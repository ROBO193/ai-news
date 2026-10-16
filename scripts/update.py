"""Собирает новости об ИИ из проверенных RSS-лент и пересказывает их по-русски.

Пересказ делает бесплатная модель через любой OpenAI-совместимый API
(по умолчанию Groq, бесплатный тариф без карты). Лимиты Claude не используются.

Запуск: python scripts/update.py
Переменные окружения:
  LLM_API_KEY  — ключ API (в GitHub: Settings → Secrets → Actions → LLM_API_KEY)
  LLM_API_URL  — адрес chat/completions (необязательно, по умолчанию Groq)
  LLM_MODELS   — модели через запятую, пробуются по очереди (необязательно)
"""
import calendar
import email.utils
import gzip
import hashlib
import zlib
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

ENDPOINT = os.environ.get("LLM_API_URL", "").strip() or "https://api.groq.com/openai/v1/chat/completions"
MODELS = [m.strip() for m in (os.environ.get("LLM_MODELS", "").strip()
          or "openai/gpt-oss-120b,openai/gpt-oss-20b").split(",") if m.strip()]
TOKEN = os.environ.get("LLM_API_KEY", "").strip()

MAX_AGE_DAYS = 7          # новые записи старше недели не берём
KEEP_DAYS = 60            # сколько дней хранить ленту
MAX_ITEMS = 600           # потолок размера ленты
PER_FEED = 15             # сколько последних записей смотреть в каждой ленте
BATCH = 6                 # записей в одном запросе к модели
MAX_REQUESTS = 6          # запросов к модели за один запуск (Groq бесплатно: 30 в минуту, 1000 в сутки)

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
    "объясни его в поле term. В поле use дай практичные советы, которые логично вытекают из новости, "
    "без выдуманных фактов и без финансовых обещаний. "
    "Поле money заполняй честно и строго: только если из новости следует реальный законный способ, "
    "которым обычный человек или небольшой бизнес может заработать уже сейчас — например, предложить "
    "услугу, сделать продукт, освоить востребованный навык, взять заказы на фрилансе. Не предлагай "
    "покупать акции, криптовалюту или другие инвестиции, не называй суммы дохода и не обещай результат. "
    "Если способа нет или он нужен только крупным компаниям — money = null. Таких новостей большинство, "
    "это нормально. Ответ — только JSON."
)

MONEY_TEMPLATE = (
    "\"money\": null ИЛИ {{\"idea\": \"одна фраза: на чём именно можно заработать\", "
    "\"how\": [\"3–4 конкретных шага по порядку, каждый начинается с действия\"], "
    "\"who\": \"кому подходит: какие навыки нужны\", "
    "\"effort\": одно из \"низкий\", \"средний\", \"высокий\", "
    "\"risk\": \"главный риск или ограничение в одном предложении\"}}, "
)

USER_TEMPLATE = (
    "Новости (JSON-массив, у каждой поле i — номер):\n{items}\n\n"
    "Верни JSON-объект вида {{\"items\": [{{\"i\": номер, \"is_ai\": true/false, "
    "\"title_ru\": \"короткий понятный заголовок по-русски, до 110 символов\", "
    "\"simple\": \"2–3 простых предложения: что произошло и почему это может быть интересно\", "
    "\"term\": \"один сложный термин из новости и его объяснение в 1 предложении, например "
    "'Инференс — запуск уже обученной модели для получения ответов'. Пустая строка, если терминов нет\", "
    "\"use\": [\"2–3 конкретных практических совета, как читатель может использовать эту новость: "
    "что попробовать, на что обратить внимание, что учесть в работе, учёбе, бизнесе или инвестициях. "
    "Каждый совет — одно-два коротких предложения, начинается с действия. Советы должны прямо следовать "
    "из новости и не содержать новых фактов, цифр и обещаний. Если практической пользы нет — пустой массив\"], "
    + MONEY_TEMPLATE +
    "\"category\": одно из {cats}}}]}}. "
    "is_ai=false, если новость на самом деле не про искусственный интеллект."
)

BACKFILL_DAYS = 7  # уже пересказанным новостям свежее недели дописываем недостающие поля (советы, заработок)
EFFORTS = ("низкий", "средний", "высокий")
MONEY_BAN = re.compile(r"(акци[яиюей]|криптовалют|биткоин|токен[аы]? для инвест|инвестируйте|купите доли|"
                       r"гарантирован|\$\s?\d|\d+\s?(?:\$|долл|руб|₽|евро|€))", re.IGNORECASE)


def parse_money(raw):
    """Проверяет блок «для заработка». Возвращает словарь или None."""
    if not isinstance(raw, dict):
        return None
    idea = clean(raw.get("idea"), 220)
    how = [clean(str(s), 260) for s in (raw.get("how") if isinstance(raw.get("how"), list) else []) if clean(str(s))][:4]
    if not idea or len(how) < 2:
        return None
    text = " ".join([idea, *how, clean(raw.get("who")), clean(raw.get("risk"))])
    if MONEY_BAN.search(text):  # инвестиционные советы и обещанные суммы не пропускаем
        return None
    effort = raw.get("effort") if raw.get("effort") in EFFORTS else "средний"
    return {"idea": idea, "how": how, "who": clean(raw.get("who"), 220), "effort": effort,
            "risk": clean(raw.get("risk"), 260)}


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


def decompress(raw, encoding=""):
    """Распаковывает ответ, если сервер прислал его сжатым (даже без запроса)."""
    encoding = (encoding or "").lower()
    if raw[:2] == b"\x1f\x8b" or "gzip" in encoding:
        return gzip.decompress(raw)
    if "deflate" in encoding:
        try:
            return zlib.decompress(raw)
        except zlib.error:
            return zlib.decompress(raw, -zlib.MAX_WBITS)
    return raw


def read_source(url):
    if not url.startswith("http"):
        with open(url, "rb") as f:
            raw, enc = f.read(), ""
    else:
        req = urllib.request.Request(url, headers={
            "User-Agent": "Mozilla/5.0 (compatible; ai-news-feed/1.0)",
            "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml, */*",
            "Accept-Encoding": "gzip, deflate"})
        with urllib.request.urlopen(req, timeout=30) as resp:
            raw, enc = resp.read(), resp.headers.get("Content-Encoding", "")
    raw = decompress(raw, enc)
    # убираем BOM и пробелы перед <?xml — из-за них парсер падает на первой строке
    return raw.lstrip(b"\xef\xbb\xbf").lstrip()


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
            raise ValueError(f"это не RSS/Atom; начало ответа: {raw[:80]!r}")
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
    errors = []
    for model in MODELS:
        base = {"model": model, "messages": messages, "temperature": 0.2}
        # сначала с подсказкой «только JSON», если API её не понимает — без неё
        variants = [dict(base, response_format={"type": "json_object"}), base]
        if "gpt-oss" in model:
            variants.insert(0, dict(base, response_format={"type": "json_object"}, reasoning_effort="low"))
        for body in variants:
            status, text = post_json(body)
            if status == 200:
                try:
                    content = json.loads(text)["choices"][0]["message"]["content"] or ""
                    content = re.sub(r"^```(?:json)?|```$", "", content.strip(), flags=re.M)
                    match = re.search(r"\{.*\}", content, re.S)
                    return json.loads(match.group(0) if match else content).get("items", []), model
                except Exception as exc:
                    errors.append(f"{model}: ответ не разобран ({exc}); начало: {text[:200]!r}")
                    break
            errors.append(f"{model}: HTTP {status} {text[:300]!r}")
            if status in (401, 403):
                raise RuntimeError("ключ API не подходит или не задан. " + errors[-1])
            if status == 429:  # лимит исчерпан — пробуем следующую модель
                break
            if status != 400:  # 400 — пробуем упрощённый запрос, остальное — следующую модель
                break
    raise RuntimeError(" | ".join(errors) or "модель недоступна")


def post_json(body):
    req = urllib.request.Request(
        ENDPOINT, data=json.dumps(body).encode("utf-8"), method="POST",
        headers={"Authorization": f"Bearer {TOKEN}", "Content-Type": "application/json",
                 "Accept": "application/json", "Accept-Encoding": "gzip",
                 "User-Agent": "ai-news-feed/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=120) as resp:
            raw = decompress(resp.read(), resp.headers.get("Content-Encoding", ""))
            return resp.status, raw.decode("utf-8", "replace")
    except urllib.error.HTTPError as exc:
        raw = decompress(exc.read() or b"", exc.headers.get("Content-Encoding", "") if exc.headers else "")
        return exc.code, raw.decode("utf-8", "replace")
    except Exception as exc:
        return 0, str(exc)


def summarize(items):
    if not TOKEN:
        print("[i] LLM_API_KEY не задан — пересказ пропущен, записи остаются на английском. "
              "Добавьте ключ: Settings → Secrets and variables → Actions → New repository secret", file=sys.stderr)
        return
    fresh = datetime.fromtimestamp(time.time() - BACKFILL_DAYS * 86400, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    pending = [it for it in items if it.get("pending")]
    backfill = [it for it in items if not it.get("pending") and ("use" not in it or "money" not in it)
                and it["date"] >= fresh]
    # сначала новые записи без пересказа, потом добавляем советы к уже пересказанным
    queue = sorted(pending, key=lambda x: x["date"], reverse=True) + sorted(backfill, key=lambda x: x["date"], reverse=True)
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
            raw_use = res.get("use") if isinstance(res.get("use"), list) else []
            use = [clean(str(u), 300) for u in raw_use if clean(str(u))][:3]
            it.update({"title_ru": title_ru, "simple": simple, "term": clean(res.get("term"), 300), "use": use,
                       "money": parse_money(res.get("money")),
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
