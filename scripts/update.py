"""Собирает новости об ИИ из проверенных RSS-лент и пересказывает их по-русски.

Пересказ делает бесплатная модель GitHub Models (через встроенный GITHUB_TOKEN
в GitHub Actions). Лимиты Claude не используются.

Запуск: python scripts/update.py
Переменные окружения:
  GITHUB_TOKEN   — токен для GitHub Models (в Actions выдаётся автоматически)
  MODELS         — список моделей через запятую, пробуются по очереди
"""
import calendar
import email.utils
import hashlib
import html
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FEEDS_PATH = os.path.join(ROOT, "feeds.json")
DATA_PATH = os.path.join(ROOT, "data", "news.json")

ENDPOINT = "https://models.github.ai/inference/chat/completions"
MODELS = [m.strip() for m in os.environ.get("MODELS", "openai/gpt-4.1-mini,openai/gpt-4o-mini").split(",") if m.strip()]
TOKEN = os.environ.get("GITHUB_TOKEN", "")

MAX_AGE_DAYS = 7          # новые записи старше недели не берём
KEEP_DAYS = 60            # сколько дней хранить ленту
MAX_ITEMS = 600           # потолок размера ленты
PER_FEED = 15             # сколько последних записей смотреть в каждой ленте
BATCH = 6                 # записей в одном запросе к модели
MAX_REQUESTS = 3          # запросов к модели за один запуск (бесплатный лимит ~150 в сутки)

CATEGORIES = ["Модели", "Агенты", "Исследования", "Безопасность", "Железо", "Open source",
              "Регулирование", "Рынки и экономика", "Разработка", "Применение"]

AI_RE = re.compile(
    r"(\bAI\b|\bA\.I\.|artificial intelligence|machine learning|\bLLMs?\b|\bGPT|Gemini|Claude|"
    r"neural|deep learning|generative|chatbot|AI agent|agentic|inference|transformer|OpenAI|"
    r"Anthropic|DeepMind|Copilot|Llama|Mistral|robotics|humanoid|diffusion model|language model)",
    re.IGNORECASE,
)

SYSTEM_PROMPT = (
    "Ты редактор русскоязычной ленты новостей об искусственном интеллекте для обычного читателя. "
    "Для каждой новости из входных данных верни пересказ строго на основе её заголовка и анонса. "
    "Правила: не добавляй фактов, цифр, имён и выводов, которых нет во входном тексте; "
    "если анонс короткий — пиши короче, но не додумывай. Пиши простым языком, как объясняешь умному "
    "другу без технического образования; избегай жаргона, а если без термина не обойтись — "
    "объясни его в поле term. Ответ — только JSON."
)

USER_TEMPLATE = (
    "Новости (JSON-массив, у каждой поле i — номер):\n{items}\n\n"
    "Верни JSON-объект вида {{\"items\": [{{\"i\": номер, \"is_ai\": true/false, "
    "\"title_ru\": \"короткий понятный заголовок по-русски, до 110 символов\", "
    "\"simple\": \"2–3 простых предложения: что произошло и почему это может быть интересно\", "
    "\"term\": \"один сложный термин из новости и его объяснение в 1 предложении, например "
    "'Инференс — запуск уже обученной модели для получения ответов'. Пустая строка, если терминов нет\", "
    "\"category\": одно из {cats}}}]}}. "
    "is_ai=false, если новость на самом деле не про искусственный интеллект."
)


def now_iso():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def clean(text, limit=None):
    text = html.unescape(re.sub(r"<[^>]+>", " ", text or ""))
    text = re.sub(r"\s+", " ", text).strip()
    if limit and len(text) > limit:
        text = text[:limit].rsplit(" ", 1)[0] + "…"
    return text


def parse_time(value):
    value = (value or "").strip()
    if not value:
        return None
    try:  # RSS: "Tue, 13 Oct 2026 16:01:58 +0000"
        return email.utils.parsedate_to_datetime(value).timestamp()
    except (TypeError, ValueError, IndexError):
        pass
    try:  # Atom: "2026-10-13T16:01:58Z"
        return datetime.fromisoformat(value.replace("Z", "+00:00")).timestamp()
    except ValueError:
        return None


def local(tag):
    return tag.rsplit("}", 1)[-1].lower()


def child_text(node, *names):
    for child in node:
        if local(child.tag) in names:
            text = "".join(child.itertext()).strip()
            if text:
                return text
    return ""


def child_link(node):
    for child in node:
        if local(child.tag) == "link":
            href = child.get("href")
            if href and child.get("rel", "alternate") == "alternate":
                return href.strip()
            if (child.text or "").strip():
                return child.text.strip()
    return child_text(node, "guid", "id")


def read_source(url):
    if not url.startswith("http"):
        with open(url, "rb") as f:
            return f.read()
    req = urllib.request.Request(url, headers={
        "User-Agent": "Mozilla/5.0 (compatible; ai-news-feed/1.0)",
        "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml, */*"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        return resp.read()


def parse_feed(url):
    """Возвращает записи RSS или Atom: [{title, link, summary, ts}]."""
    raw = read_source(url)
    try:
        nodes = [n for n in ET.fromstring(raw).iter() if local(n.tag) in ("item", "entry")]
    except ET.ParseError:
        # лента оборвана или с ошибками — разбираем записи по отдельности
        text = raw.decode("utf-8", "replace")
        nodes = []
        for m in re.finditer(r"<(item|entry)(?:\s[^>]*)?>.*?</\1>", text, re.S):
            fragment = re.sub(r"<(/?)[A-Za-z][\w.-]*:", r"<\1", m.group(0))  # убираем префиксы пространств имён
            try:
                nodes.append(ET.fromstring(fragment))
            except ET.ParseError:
                continue
        if not nodes:
            raise
    entries = []
    for n in nodes:
        entries.append({
            "title": child_text(n, "title"),
            "link": child_link(n),
            "summary": child_text(n, "description", "summary", "content", "encoded"),
            "ts": parse_time(child_text(n, "pubdate", "published", "updated", "date")),
        })
    entries.sort(key=lambda e: e["ts"] or 0, reverse=True)  # некоторые ленты не отсортированы
    return entries


def load_data():
    try:
        with open(DATA_PATH, encoding="utf-8") as f:
            data = json.load(f)
            data.setdefault("items", [])
            return data
    except (FileNotFoundError, json.JSONDecodeError):
        return {"items": []}


def fetch_candidates(feeds, known_ids):
    cutoff = time.time() - MAX_AGE_DAYS * 86400
    found, failed = [], []
    for feed in feeds:
        try:
            entries = parse_feed(feed["url"])
        except Exception as exc:  # лента недоступна — пропускаем, покажем на сайте
            failed.append(feed["name"])
            print(f"[!] {feed['name']}: {exc}", file=sys.stderr)
            continue
        for e in entries[:PER_FEED]:
            link = (e["link"] or "").strip()
            title = clean(e["title"])
            if not link.startswith("http") or not title:
                continue
            uid = hashlib.sha1(link.encode("utf-8")).hexdigest()[:14]
            if uid in known_ids:
                continue
            ts = e["ts"]
            if ts is None or ts < cutoff or ts > time.time() + 86400:
                continue
            summary = clean(e["summary"], 700)
            if feed.get("filter") and not AI_RE.search(title + " " + summary):
                continue
            known_ids.add(uid)
            found.append({
                "id": uid,
                "date": datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "addedAt": now_iso(),
                "source": feed["name"],
                "sourceType": feed.get("type", "media"),
                "url": link,
                "title_en": title,
                "summary_en": summary,
                "pending": True,
            })
    return found, failed


def call_model(batch):
    payload_items = [{"i": n, "title": it["title_en"], "summary": it["summary_en"][:600], "source": it["source"]}
                     for n, it in enumerate(batch)]
    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": USER_TEMPLATE.format(
            items=json.dumps(payload_items, ensure_ascii=False),
            cats=json.dumps(CATEGORIES, ensure_ascii=False))},
    ]
    last_error = None
    for model in MODELS:
        body = {"model": model, "messages": messages, "temperature": 0.2,
                "response_format": {"type": "json_object"}}
        req = urllib.request.Request(
            ENDPOINT, data=json.dumps(body).encode("utf-8"), method="POST",
            headers={"Authorization": f"Bearer {TOKEN}", "Content-Type": "application/json",
                     "Accept": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=90) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            text = data["choices"][0]["message"]["content"]
            match = re.search(r"\{.*\}", text, re.S)
            return json.loads(match.group(0) if match else text).get("items", []), model
        except urllib.error.HTTPError as exc:
            last_error = f"{model}: HTTP {exc.code} {exc.read()[:200]!r}"
            if exc.code == 429:  # дневной лимит исчерпан — дальше пробовать бессмысленно
                break
        except Exception as exc:
            last_error = f"{model}: {exc}"
    raise RuntimeError(last_error or "модель недоступна")


def summarize(items):
    if not TOKEN:
        print("[i] GITHUB_TOKEN не задан — пересказ пропущен, записи остаются на английском", file=sys.stderr)
        return
    queue = sorted([it for it in items if it.get("pending")], key=lambda x: x["date"], reverse=True)
    for r in range(MAX_REQUESTS):
        batch = queue[r * BATCH:(r + 1) * BATCH]
        if not batch:
            break
        try:
            results, model = call_model(batch)
        except Exception as exc:
            print(f"[!] пересказ не удался: {exc}", file=sys.stderr)
            break
        for res in results:
            try:
                it = batch[int(res["i"])]
            except (KeyError, ValueError, IndexError, TypeError):
                continue
            if res.get("is_ai") is False:
                it["drop"] = True
                continue
            title_ru = clean(res.get("title_ru"), 160)
            simple = clean(res.get("simple"), 700)
            if not title_ru or not simple:
                continue
            it.update({"title_ru": title_ru, "simple": simple, "term": clean(res.get("term"), 300),
                       "category": res.get("category") if res.get("category") in CATEGORIES else "Применение",
                       "model": model, "pending": False})
        time.sleep(7)  # бережём поминутный лимит


def main():
    with open(FEEDS_PATH, encoding="utf-8") as f:
        feeds = json.load(f)
    data = load_data()
    items = data["items"]
    known = {it["id"] for it in items}
    new, failed = fetch_candidates(feeds, known)
    items.extend(new)
    summarize(items)

    keep_after = time.time() - KEEP_DAYS * 86400
    items = [it for it in items if not it.get("drop")
             and calendar.timegm(time.strptime(it["date"], "%Y-%m-%dT%H:%M:%SZ")) >= keep_after]
    items.sort(key=lambda x: x["date"], reverse=True)
    items = items[:MAX_ITEMS]

    out = {"updated": now_iso(), "failedSources": failed, "items": items}
    os.makedirs(os.path.dirname(DATA_PATH), exist_ok=True)
    with open(DATA_PATH, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)
    done = sum(1 for it in items if not it.get("pending"))
    print(f"Новых записей: {len(new)}; всего: {len(items)}; с пересказом: {done}; недоступные ленты: {failed or 'нет'}")


if __name__ == "__main__":
    main()
