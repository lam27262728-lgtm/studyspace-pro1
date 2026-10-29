#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
StudySpace Pro v2 - Không gian tự học đỉnh cao.
Hỗ trợ quản lý file theo Môn học -> Giữa kì / Cuối kì,
Xem trước đa định dạng (PDF, Word, Markdown, Ảnh), MathJax, RAG & AI Tutor.

Chạy:      pip install flask pypdf
           python studyspace_pro.py
Mở:        http://127.0.0.1:5000
"""
import html as htmllib
import io
import json
import math
import os
import platform
import random
import re
import secrets
import shutil
import sqlite3
import subprocess
import threading
import unicodedata
import urllib.error
import urllib.request
import zipfile
from collections import Counter
from datetime import date, datetime, timedelta
from html.parser import HTMLParser
from xml.etree import ElementTree as ET

from flask import (Flask, abort, flash, g, jsonify, redirect,
                   render_template_string, request, send_file,
                   send_from_directory, session, url_for)

# --------------------------------------------------------------------------
# Cấu hình
# --------------------------------------------------------------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UPLOAD_FOLDER = os.path.join(BASE_DIR, 'uploads')
DB_PATH = os.path.join(BASE_DIR, 'studyspace.db')
KEY_PATH = os.path.join(BASE_DIR, '.secret_key')
os.makedirs(UPLOAD_FOLDER, exist_ok=True)

TEXT_EXT = {'.txt', '.md', '.py', '.html', '.htm', '.json', '.csv', '.tex'}
INDEX_EXT = TEXT_EXT | {'.docx', '.pdf'}
ALLOWED_EXT = INDEX_EXT | {'.png', '.jpg', '.jpeg', '.gif', '.webp', '.pptx', '.xlsx', '.zip'}
QUIZ_EXT = {'.txt', '.md', '.docx', '.pdf', '.tex'}

MAX_UPLOAD_MB = 100
MAX_INDEX_BYTES = 10 * 1024 * 1024
BOX_DAYS = {1: 0, 2: 1, 3: 3, 4: 7, 5: 14}

IMAGE_EXT = {'.png', '.jpg', '.jpeg', '.gif', '.webp'}
VIEW_EXT = TEXT_EXT | {'.docx', '.pdf'} | IMAGE_EXT
PERIODS = ['giua-ki', 'cuoi-ki']


def _subject(sid, name, icon, c1, c2):
    return {'id': sid, 'name': name, 'icon': icon, 'c1': c1, 'c2': c2}


SUBJECTS = [
    _subject('toan', 'Toán học', '➗', '#34d399', '#059669'),
    _subject('ngu-van', 'Ngữ văn', '📖', '#d9f99d', '#84cc16'),
    _subject('tieng-anh', 'Tiếng Anh', '🔤', '#818cf8', '#3b4fd8'),
    _subject('vat-li', 'Vật lí', '⚛️', '#7dd3fc', '#0ea5e9'),
    _subject('hoa-hoc', 'Hóa học', '🧪', '#fcd34d', '#f97316'),
    _subject('sinh-hoc', 'Sinh học', '🧬', '#a21caf', '#e879f9'),
    _subject('lich-su', 'Lịch sử', '📜', '#a16207', '#e0b88a'),
    _subject('tin-hoc', 'Tin học', '💻', '#334e8a', '#64748b'),
    _subject('dia-li', 'Địa lí', '🌏', '#4338ca', '#a78bfa'),
    _subject('cong-nghe', 'Công nghệ', '🛠️', '#fde047', '#eab308'),
    _subject('the-chat', 'GD Thể chất', '🏃', '#f472b6', '#fb923c'),
    _subject('quoc-phong', 'GD Quốc phòng và An ninh', '🛡️', '#4ade80', '#fb923c'),
    _subject('kinh-te-phap-luat', 'GD kinh tế và pháp luật', '⚖️', '#bef264', '#65a30d'),
    _subject('hdtn', 'HĐ trải nghiệm, hướng nghiệp', '🧭', '#2dd4bf', '#34d399'),
    _subject('khac', 'Khác', '📁', '#94a3b8', '#64748b'),
]
SUBJECT_BY_ID = {x['id']: x for x in SUBJECTS}

for _x in SUBJECTS:
    sub_path = os.path.join(UPLOAD_FOLDER, _x['id'])
    os.makedirs(sub_path, exist_ok=True)
    for p in PERIODS:
        os.makedirs(os.path.join(sub_path, p), exist_ok=True)

try:
    import pypdf
    HAS_PYPDF = True
except Exception:
    pypdf = None
    HAS_PYPDF = False

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = MAX_UPLOAD_MB * 1024 * 1024 * 4


def _load_secret():
    if os.path.exists(KEY_PATH):
        with open(KEY_PATH, 'r', encoding='utf-8') as f:
            key = f.read().strip()
            if key:
                return key
    key = secrets.token_hex(32)
    with open(KEY_PATH, 'w', encoding='utf-8') as f:
        f.write(key)
    try:
        os.chmod(KEY_PATH, 0o600)
    except OSError:
        pass
    return key


app.secret_key = _load_secret()
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE='Lax')


# --------------------------------------------------------------------------
# Cơ sở dữ liệu (SQLite)
# --------------------------------------------------------------------------
def get_db():
    if 'db' not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
    return g.db


@app.teardown_appcontext
def close_db(_exc):
    db = g.pop('db', None)
    if db is not None:
        db.close()


def init_db():
    with sqlite3.connect(DB_PATH) as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS notes(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            content TEXT NOT NULL, tags TEXT DEFAULT '',
            created TEXT, updated TEXT);
        CREATE TABLE IF NOT EXISTS cards(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            front TEXT NOT NULL, back TEXT NOT NULL,
            box INTEGER DEFAULT 1, due TEXT, reviews INTEGER DEFAULT 0, created TEXT);
        CREATE TABLE IF NOT EXISTS chat(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            question TEXT NOT NULL, answer TEXT NOT NULL, created TEXT);
        """)


def now_s():
    return datetime.now().isoformat(timespec='seconds')


def today_s():
    return date.today().isoformat()


# --------------------------------------------------------------------------
# Bảo vệ CSRF & Headers
# --------------------------------------------------------------------------
def csrf_token():
    if 'csrf' not in session:
        session['csrf'] = secrets.token_hex(16)
    return session['csrf']


app.jinja_env.globals['csrf_token'] = csrf_token


@app.before_request
def csrf_protect():
    if request.method == 'POST':
        expected = session.get('csrf')
        sent = request.form.get('csrf_token') or request.headers.get('X-CSRF-Token') or ''
        if not expected or not secrets.compare_digest(expected, sent):
            if request.path.startswith('/api/'):
                return jsonify(error='Phiên làm việc hết hạn. Hãy tải lại trang.'), 400
            flash('Phiên làm việc đã hết hạn. Hãy thử lại thao tác.', 'err')
            return redirect(url_for('index'))


@app.after_request
def security_headers(resp):
    resp.headers.setdefault('X-Content-Type-Options', 'nosniff')
    resp.headers.setdefault('Referrer-Policy', 'same-origin')
    return resp


@app.errorhandler(413)
def too_large(_e):
    flash(f'Tệp quá lớn (tối đa {MAX_UPLOAD_MB} MB mỗi tệp).', 'err')
    return redirect(url_for('index', _anchor='files'))


# --------------------------------------------------------------------------
# Quản lý File & Thư mục (Giữa kì / Cuối kì)
# --------------------------------------------------------------------------
def human_size(n):
    for unit in ('B', 'KB', 'MB', 'GB'):
        if n < 1024 or unit == 'GB':
            return f'{n:.0f} {unit}' if unit == 'B' else f'{n:.1f} {unit}'
        n /= 1024


def clean_filename(raw):
    name = os.path.basename((raw or '').replace('\\', '/'))
    name = unicodedata.normalize('NFC', name)
    name = re.sub(r'[\x00-\x1f<>:"/\\|?*]', '_', name).strip(' .')
    if not name:
        return None
    stem, ext = os.path.splitext(name)
    return (stem[:120] or 'tep') + ext.lower()[:12]


def subject_period_dir(subject, period):
    if subject not in SUBJECT_BY_ID or period not in PERIODS:
        return None
    return os.path.join(UPLOAD_FOLDER, subject, period)


def unique_name(subject, period, name):
    stem, ext = os.path.splitext(name)
    base = subject_period_dir(subject, period)
    candidate, i = name, 1
    while os.path.exists(os.path.join(base, candidate)):
        candidate = f'{stem} ({i}){ext}'
        i += 1
    return candidate


def safe_path(subject, period, name):
    base = subject_period_dir(subject, period)
    if not base or not name or name != os.path.basename(name) or name.startswith('.'):
        return None
    root = os.path.realpath(base)
    path = os.path.realpath(os.path.join(root, name))
    return path if os.path.dirname(path) == root else None


FILE_ICONS = {'.pdf': '📕', '.docx': '📘', '.md': '📝', '.txt': '📄', '.py': '🐍',
              '.html': '🌐', '.htm': '🌐', '.json': '🧩', '.csv': '📊', '.xlsx': '📊',
              '.pptx': '📙', '.zip': '🗜️', '.tex': '🧮'}


def list_files():
    items = []
    for sub in SUBJECTS:
        sub_id = sub['id']
        for period in PERIODS:
            base = os.path.join(UPLOAD_FOLDER, sub_id, period)
            if not os.path.isdir(base):
                continue
            for name in sorted(os.listdir(base), key=str.lower):
                path = safe_path(sub_id, period, name)
                if not path or not os.path.isfile(path):
                    continue
                st = os.stat(path)
                ext = os.path.splitext(name)[1].lower()
                items.append({
                    'name': name, 'size': st.st_size, 'mtime': st.st_mtime,
                    'size_h': human_size(st.st_size),
                    'date': datetime.fromtimestamp(st.st_mtime).strftime('%d/%m/%Y %H:%M'),
                    'icon': FILE_ICONS.get(ext, '🖼️' if ext in IMAGE_EXT else '📎'),
                    'searchable': ext in INDEX_EXT and (ext != '.pdf' or HAS_PYPDF),
                    'viewable': ext in VIEW_EXT, 'ext': ext,
                    'subject': sub_id, 'subject_name': sub['name'],
                    'period': period, 'period_name': 'Giữa kì' if period == 'giua-ki' else 'Cuối kì'
                })
    return items


def migrate_legacy_files():
    for name in os.listdir(UPLOAD_FOLDER):
        old = os.path.join(UPLOAD_FOLDER, name)
        if os.path.isfile(old) and not name.startswith('.'):
            dest_dir = os.path.join(UPLOAD_FOLDER, 'khac', 'giua-ki')
            os.makedirs(dest_dir, exist_ok=True)
            shutil.move(old, os.path.join(dest_dir, name))


# --------------------------------------------------------------------------
# Trích xuất Văn bản Đa định dạng (PDF, Word, Text...)
# --------------------------------------------------------------------------
def strip_accents(s):
    s = s.replace('đ', 'd').replace('Đ', 'D')
    return ''.join(c for c in unicodedata.normalize('NFD', s) if unicodedata.category(c) != 'Mn')


def norm(s):
    return strip_accents(s).lower()


TOKEN_RE = re.compile(r'\w+', re.UNICODE)
_STOP_RAW = ('là và của các những một có trong cho được với này đó khi thì như để không gì nào sao '
             'bao nhiêu thế tại về từ đến cũng sẽ đã đang ra vào bị bởi nên mà hay hoặc rất '
             'the a an of and is are to in on for with as by at it this that be')
STOPWORDS = {norm(w) for w in _STOP_RAW.split()}


def tokenize(text):
    return [t for t in TOKEN_RE.findall(norm(text))
            if t not in STOPWORDS and (len(t) > 1 or t.isdigit())]


def decode_text(raw):
    if raw[:2] in (b'\xff\xfe', b'\xfe\xff'):
        return raw.decode('utf-16', errors='replace')
    try:
        return raw.decode('utf-8-sig')
    except UnicodeDecodeError as e:
        if e.start >= len(raw) - 3:
            return raw[:e.start].decode('utf-8-sig', errors='replace')
        return raw.decode('cp1258', errors='replace')


class _HTMLText(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts, self._skip = [], 0

    def handle_starttag(self, tag, attrs):
        if tag in ('script', 'style'):
            self._skip += 1

    def handle_endtag(self, tag):
        if tag in ('script', 'style') and self._skip:
            self._skip -= 1
        elif tag in ('p', 'div', 'br', 'li', 'h1', 'h2', 'h3', 'tr'):
            self.parts.append('\n')

    def handle_data(self, data):
        if not self._skip:
            self.parts.append(data)


def extract_text(path):
    ext = os.path.splitext(path)[1].lower()
    try:
        if ext in TEXT_EXT:
            with open(path, 'rb') as f:
                text = decode_text(f.read(MAX_INDEX_BYTES))
            if ext in ('.html', '.htm'):
                parser = _HTMLText()
                parser.feed(text)
                text = ''.join(parser.parts)
        elif ext == '.docx':
            with zipfile.ZipFile(path) as z:
                root = ET.fromstring(z.read('word/document.xml'))
            w = '{http://schemas.openxmlformats.org/wordprocessingml/2006/main}'
            text = '\n'.join(''.join(t.text or '' for t in p.iter(w + 't')) for p in root.iter(w + 'p'))
        elif ext == '.pdf' and HAS_PYPDF:
            reader = pypdf.PdfReader(path)
            text = '\n\n'.join((page.extract_text() or '') for page in reader.pages[:500])
        else:
            return ''
        return unicodedata.normalize('NFC', text)
    except Exception:
        return ''


def split_sentences(text):
    return [s.strip() for s in re.split(r'(?<=[.!?…])\s+|\n+', text) if s.strip()]


def chunk_text(text, size=650):
    chunks, buf = [], ''
    for unit in split_sentences(text):
        if buf and len(buf) + len(unit) + 1 > size:
            chunks.append(buf)
            buf = ''
        buf = f'{buf} {unit}'.strip() if buf else unit
    if buf:
        chunks.append(buf)
    return chunks


# --------------------------------------------------------------------------
# RAG Search & AI Tutor
# --------------------------------------------------------------------------
_index = {'sig': None, 'chunks': [], 'df': Counter(), 'avgdl': 1.0}
_index_lock = threading.Lock()


def build_index(db):
    files = list_files()
    notes = db.execute('SELECT id, content, updated FROM notes').fetchall()
    sig = (tuple((f['subject'], f['period'], f['name'], f['mtime'], f['size']) for f in files),
           tuple((n['id'], n['updated']) for n in notes))
    with _index_lock:
        if sig == _index['sig']:
            return _index
        chunks = []
        for f in files:
            if f['searchable']:
                f_path = os.path.join(UPLOAD_FOLDER, f['subject'], f['period'], f['name'])
                text = extract_text(f_path)
                for c in chunk_text(text):
                    chunks.append({'source': f"{f['name']} ({f['subject_name']} - {f['period_name']})",
                                   'kind': 'file', 'ext': f['ext'], 'text': c})
        for n in notes:
            for c in chunk_text(n['content']):
                chunks.append({'source': f'Ghi chú #{n["id"]}', 'kind': 'note', 'ext': '.md', 'text': c})
        df = Counter()
        total = 0
        for ch in chunks:
            ch['tf'] = Counter(tokenize(ch['text']))
            ch['len'] = sum(ch['tf'].values()) or 1
            total += ch['len']
            df.update(ch['tf'].keys())
        _index.update(sig=sig, chunks=chunks, df=df, avgdl=(total / len(chunks)) if chunks else 1.0)
        return _index


def bm25_search(query, db, k=4):
    idx = build_index(db)
    chunks = idx['chunks']
    q_tokens = tokenize(query)
    if not q_tokens or not chunks:
        return [], q_tokens, len(chunks)
    n_docs, k1, b = len(chunks), 1.5, 0.75
    scored = []
    for ch in chunks:
        score = 0.0
        for t in set(q_tokens):
            f = ch['tf'].get(t, 0)
            if not f:
                continue
            n = idx['df'][t]
            idf = math.log(1 + (n_docs - n + 0.5) / (n + 0.5))
            score += idf * f * (k1 + 1) / (f + k1 * (1 - b + b * ch['len'] / idx['avgdl']))
        if score > 0:
            scored.append((score, ch))
    scored.sort(key=lambda x: -x[0])
    return scored[:k], q_tokens, len(chunks)


_MATH_RE = re.compile(r'(\$\$.+?\$\$|\$[^$\n]+?\$)', re.S)


def highlight(text, q_tokens):
    qs = set(q_tokens)

    def mark(segment):
        out, pos = [], 0
        for m in TOKEN_RE.finditer(segment):
            out.append(htmllib.escape(segment[pos:m.start()]))
            w = m.group(0)
            out.append(f'<mark>{htmllib.escape(w)}</mark>' if norm(w) in qs else htmllib.escape(w))
            pos = m.end()
        out.append(htmllib.escape(segment[pos:]))
        return ''.join(out)

    parts = _MATH_RE.split(text)
    return ''.join(htmllib.escape(p) if i % 2 else mark(p) for i, p in enumerate(parts))


def call_llm(question, contexts):
    key = os.environ.get('ANTHROPIC_API_KEY')
    if not key:
        return None
    ctx = '\n\n'.join(f'[{i + 1}] ({c["source"]}) {c["text"]}' for i, c in enumerate(contexts))
    prompt = ('Bạn là gia sư. Chỉ dựa vào các đoạn tài liệu dưới đây để trả lời bằng tiếng Việt, '
              'ngắn gọn, đúng trọng tâm. Nếu tài liệu không đủ thông tin, hãy nói rõ.\n\n'
              f'TÀI LIỆU:\n{ctx}\n\nCÂU HỎI: {question}')
    body = json.dumps({'model': os.environ.get('STUDYSPACE_MODEL', 'claude-sonnet-5-5'),
                       'max_tokens': 900,
                       'messages': [{'role': 'user', 'content': prompt}]}).encode('utf-8')
    req = urllib.request.Request('https://api.anthropic.com/v1/messages', data=body, headers={
        'x-api-key': key, 'anthropic-version': '2023-06-01', 'content-type': 'application/json'})
    try:
        with urllib.request.urlopen(req, timeout=45) as r:
            data = json.load(r)
        text = ''.join(b.get('text', '') for b in data.get('content', []) if b.get('type') == 'text').strip()
        return text or None
    except Exception:
        return None


def answer_question(q, db):
    hits, q_tokens, n_chunks = bm25_search(q, db)
    if not hits:
        msg = 'Không tìm thấy nội dung liên quan. Hãy tải lên tài liệu học tập hoặc thêm ghi chú.'
        return {'answer_html': htmllib.escape(msg), 'sources': [], 'mode': 'none'}

    top_score = hits[0][0]
    sources = []
    for score, ch in hits:
        text = ch['text'] if len(ch['text']) <= 600 else ch['text'][:600].rsplit(' ', 1)[0] + '…'
        sources.append({'source': ch['source'], 'kind': ch['kind'],
                        'html': highlight(text, q_tokens), 'score': round(100 * score / top_score)})

    llm = call_llm(q, [c for _, c in hits])
    if llm:
        answer_html = htmllib.escape(llm).replace('\n', '<br>')
        return {'answer_html': answer_html, 'sources': sources, 'mode': 'llm'}

    qset = set(q_tokens)
    best = max(split_sentences(hits[0][1]['text']),
               key=lambda s: len(qset & set(tokenize(s))), default=hits[0][1]['text'])
    return {'answer_html': '<strong>Câu liên quan nhất:</strong> ' + highlight(best, q_tokens),
            'sources': sources, 'mode': 'rag'}


# --------------------------------------------------------------------------
# Tạo Quiz trắc nghiệm điền khuyết
# --------------------------------------------------------------------------
def generate_quiz(db, n=5):
    idx = build_index(db)
    sentences, pool = [], {}
    for ch in idx['chunks']:
        if ch['kind'] == 'file' and ch['ext'] not in QUIZ_EXT:
            continue
        for s in split_sentences(ch['text']):
            words = [w for w in re.findall(r'[^\W\d_]{5,}', s) if norm(w) not in STOPWORDS]
            for w in words:
                pool.setdefault(norm(w), w)
            if 40 <= len(s) <= 220 and '$' not in s and '\\' not in s and words:
                sentences.append((s, ch['source'], words))
    random.shuffle(sentences)
    quiz = []
    for s, source, words in sentences:
        answer = random.choice(sorted(words, key=len, reverse=True)[:3])
        near = []
        for tolerance in (2, 4, 99):
            near = [w for key, w in pool.items()
                    if key != norm(answer) and abs(len(w) - len(answer)) <= tolerance
                    and w.lower() != answer.lower()]
            if len(near) >= 3:
                break
        if len(near) < 3:
            continue
        options = random.sample(near, 3) + [answer]
        random.shuffle(options)
        blank = re.sub(r'(?<!\w)' + re.escape(answer) + r'(?!\w)', '_____', s)
        if blank == s:
            continue
        quiz.append({'q': blank, 'options': options, 'answer': options.index(answer), 'source': source})
        if len(quiz) >= n:
            break
    return quiz


# --------------------------------------------------------------------------
# Giao diện HTML & CSS Hoàn chỉnh
# --------------------------------------------------------------------------
HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="vi">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>StudySpace Pro - Không gian tự học thông minh</title>
<script>
  window.MathJax = {
    tex: { inlineMath: [['$', '$'], ['\\(', '\\)']], displayMath: [['$$', '$$'], ['\\[', '\\]']] },
    options: { skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code'] }
  };
</script>
<script async src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-mml-chtml.js"></script>
<script src="https://cdn.jsdelivr.net/npm/marked/marked.min.js"></script>
<style>
  :root {
    --bg:#f1f5f9; --card:#ffffff; --soft:#f8fafc; --text:#334155; --strong:#0f172a; --muted:#64748b;
    --line:#e2e8f0; --brand:#4f46e5; --brand-d:#4338ca; --brand-soft:#eef2ff; --accent:#0284c7;
    --ok:#059669; --ok-soft:#d1fae5; --bad:#dc2626; --bad-soft:#fee2e2; --side:#0f172a; --side-text:#94a3b8;
    --mark:#fef08a; --shadow:0 1px 3px rgba(15,23,42,.08);
  }
  [data-theme="dark"] {
    --bg:#0b1220; --card:#121b2e; --soft:#0e1627; --text:#cbd5e1; --strong:#f1f5f9; --muted:#94a3b8;
    --line:#243049; --brand:#818cf8; --brand-d:#6366f1; --brand-soft:#1c2442; --accent:#38bdf8;
    --ok:#34d399; --ok-soft:#064e3b; --bad:#f87171; --bad-soft:#4c1d1d; --side:#070d19; --mark:#854d0e;
    --shadow:none;
  }
  * { box-sizing:border-box; margin:0; padding:0; font-family:'Segoe UI',system-ui,-apple-system,sans-serif; }
  html { scroll-behavior:smooth; }
  body { display:flex; background:var(--bg); color:var(--text); min-height:100vh; line-height:1.55; }
  :focus-visible { outline:2px solid var(--brand); outline-offset:2px; }
  mark { background:var(--mark); color:inherit; border-radius:3px; padding:0 2px; }

  .sidebar { width:260px; background:var(--side); color:#fff; padding:24px 16px; position:fixed; inset:0 auto 0 0; display:flex; flex-direction:column; gap:4px; z-index:10; }
  .brand { display:flex; align-items:center; gap:10px; font-size:19px; font-weight:700; color:#fff; padding:0 10px 20px; }
  .brand small { display:block; font-size:12px; font-weight:400; color:var(--side-text); }
  .nav { display:flex; align-items:center; gap:10px; width:100%; text-align:left; background:none; border:0; color:var(--side-text); padding:11px 12px; border-radius:8px; cursor:pointer; font-size:15px; font-weight:500; transition:background .15s,color .15s; }
  .nav:hover { background:#1e293b; color:#fff; }
  .nav[aria-current="page"] { background:var(--brand-d); color:#fff; }
  .nav .count { margin-left:auto; background:#f59e0b; color:#1f1300; border-radius:99px; font-size:12px; font-weight:700; padding:0 7px; }
  .side-foot { margin-top:auto; padding:10px; }
  .theme-btn { background:#1e293b; color:#cbd5e1; border:0; border-radius:8px; padding:8px 12px; cursor:pointer; width:100%; font-size:13px; }

  .content { margin-left:260px; flex:1; padding:36px 40px 60px; max-width:1100px; min-width:0; }
  .panel { display:none; }
  .panel.active { display:block; }
  .card { background:var(--card); border-radius:12px; box-shadow:var(--shadow); border:1px solid var(--line); padding:26px; margin-bottom:22px; }
  .card h2 { font-size:19px; color:var(--strong); margin-bottom:6px; }
  .card h3 { font-size:15px; color:var(--strong); margin:20px 0 8px; }
  .lead { color:var(--muted); font-size:14px; margin-bottom:16px; }
  h1.page { font-size:26px; color:var(--strong); margin-bottom:4px; }
  p.sub { color:var(--muted); margin-bottom:22px; }

  .btn { background:var(--brand); color:#fff; border:0; padding:10px 18px; border-radius:8px; cursor:pointer; font-weight:600; font-size:14px; transition:background .15s; text-decoration:none; display:inline-block; }
  .btn:hover { background:var(--brand-d); text-decoration:none; }
  .btn.ghost { background:var(--brand-soft); color:var(--brand); }
  .btn.ghost:hover { background:var(--line); }
  .btn.ok { background:var(--ok); } .btn.bad { background:var(--bad); }
  .btn.sm { padding:5px 11px; font-size:13px; border-radius:6px; }
  .btn:disabled { opacity:.5; cursor:not-allowed; }

  input[type=text], textarea, select { padding:11px 12px; border:1px solid var(--line); background:var(--card); color:var(--text); border-radius:8px; width:100%; margin-bottom:12px; font-size:14px; }
  input[type=text]:focus, textarea:focus, select:focus { border-color:var(--brand); outline:none; box-shadow:0 0 0 3px var(--brand-soft); }
  textarea { resize:vertical; }
  a { color:var(--accent); text-decoration:none; font-weight:500; } a:hover { text-decoration:underline; }

  .stats { display:grid; grid-template-columns:repeat(auto-fit,minmax(150px,1fr)); gap:14px; margin-bottom:22px; }
  .stat { background:var(--card); border:1px solid var(--line); border-radius:12px; padding:16px 18px; }
  .stat b { display:block; font-size:28px; color:var(--strong); line-height:1.2; }
  .stat span { color:var(--muted); font-size:13px; }
  .two { display:grid; grid-template-columns:1fr 1fr; gap:22px; }

  .drop { border:2px dashed var(--line); border-radius:12px; padding:26px; text-align:center; color:var(--muted); cursor:pointer; transition:all .15s; display:block; }
  .drop:hover, .drop.over { border-color:var(--brand); background:var(--brand-soft); color:var(--brand); }
  .drop input { display:none; }
  .list { list-style:none; margin-top:12px; }
  .row { display:flex; justify-content:space-between; align-items:center; gap:12px; padding:10px 12px; background:var(--soft); border:1px solid var(--line); margin-bottom:8px; border-radius:8px; flex-wrap:wrap; }
  .row .meta { color:var(--muted); font-size:12px; }
  .row .name { overflow:hidden; text-overflow:ellipsis; white-space:nowrap; min-width:0; flex:1 1 200px; }
  .acts { display:flex; gap:6px; align-items:center; flex-wrap:wrap; justify-content:flex-end; }
  
  .tabs { display:flex; gap:8px; border-bottom:2px solid var(--line); margin-bottom:18px; }
  .tab-btn { background:none; border:0; padding:10px 16px; font-weight:600; font-size:15px; color:var(--muted); cursor:pointer; border-bottom:2px solid transparent; margin-bottom:-2px; }
  .tab-btn.active { color:var(--brand); border-bottom-color:var(--brand); }

  .flash { position:fixed; top:16px; right:16px; z-index:50; display:flex; flex-direction:column; gap:8px; }
  .toast { padding:11px 16px; border-radius:9px; box-shadow:0 6px 20px rgba(0,0,0,.18); font-size:14px; max-width:360px; }
  .toast.ok { background:var(--ok-soft); color:var(--ok); } .toast.err { background:var(--bad-soft); color:var(--bad); }

  .subjects { display:grid; grid-template-columns:repeat(auto-fill,minmax(140px,1fr)); gap:26px 12px; margin-top:12px; }
  .subj { background:none; border:0; cursor:pointer; text-align:center; color:var(--text); font-size:15px; padding:4px; border-radius:12px; }
  .subj:hover .circle { transform:translateY(-3px); }
  .circle { position:relative; width:84px; height:84px; border-radius:50%; margin:0 auto 8px; display:grid; place-items:center; font-size:36px; background:linear-gradient(135deg,var(--c1),var(--c2)); box-shadow:0 4px 10px rgba(0,0,0,.14); transition:transform .15s; }
  .sname { display:block; line-height:1.3; }

  /* Modal xem tài liệu mạnh mẽ đa định dạng */
  .viewer-modal { display:none; position:fixed; inset:0; z-index:100; background:rgba(15,23,42,0.6); backdrop-filter:blur(4px); padding:40px; justify-content:center; align-items:center; }
  .viewer-modal.active { display:flex; }
  .viewer-content { background:var(--card); width:100%; max-width:950px; height:90vh; border-radius:16px; display:flex; flex-direction:column; box-shadow:0 20px 25px -5px rgba(0,0,0,0.3); border:1px solid var(--line); overflow:hidden; }
  .viewer-header { padding:16px 24px; border-bottom:1px solid var(--line); display:flex; justify-content:space-between; align-items:center; background:var(--soft); }
  .viewer-body { padding:24px; overflow-y:auto; flex:1; font-size:16px; line-height:1.7; }
  .viewer-body img { max-width:100%; height:auto; border-radius:8px; display:block; margin:0 auto; }

  .chat-box { background:var(--soft); border:1px solid var(--line); padding:16px; height:430px; overflow-y:auto; margin-bottom:14px; border-radius:10px; }
  .msg-user { background:var(--brand); color:#fff; padding:9px 14px; border-radius:14px 14px 3px 14px; margin:0 0 8px auto; width:fit-content; max-width:85%; word-wrap:break-word; }
  .msg-bot { background:var(--card); border:1px solid var(--line); border-radius:14px 14px 14px 3px; padding:12px 14px; margin-bottom:16px; max-width:95%; }
  .src { border-left:3px solid var(--line); padding:4px 0 4px 10px; margin-top:10px; font-size:13.5px; color:var(--muted); }
  .src b { color:var(--text); font-size:12.5px; }
  .src .score { float:right; font-size:12px; }

  .study { text-align:center; padding:24px 10px; }
  .face { font-size:18px; color:var(--strong); min-height:70px; display:flex; align-items:center; justify-content:center; white-space:pre-wrap; word-wrap:break-word; }
  .opts { display:grid; gap:10px; max-width:640px; margin:16px auto 0; }
  .opt { text-align:left; background:var(--soft); border:1px solid var(--line); color:var(--text); padding:11px 14px; border-radius:8px; cursor:pointer; font-size:15px; }
  .opt:hover:not(:disabled) { border-color:var(--brand); }
  .opt.right { background:var(--ok-soft); border-color:var(--ok); color:var(--ok); }
  .opt.wrong { background:var(--bad-soft); border-color:var(--bad); color:var(--bad); }

  .pomo { text-align:center; }
  .pomo .time { font-size:52px; font-weight:700; color:var(--strong); font-variant-numeric:tabular-nums; }
  .pomo .btns { display:flex; gap:8px; justify-content:center; margin-top:8px; }
</style>
</head>
<body data-theme="light">
  <nav class="sidebar">
    <div class="brand">
      <span>📚 StudySpace</span>
      <small>Pro v2 - Ôn thi tối thượng</small>
    </div>
    <button class="nav" onclick="go('home')" id="nav-home" aria-current="page">🏠 Tổng quan</button>
    <button class="nav" onclick="go('subjects')" id="nav-subjects">📂 Môn học & Tài liệu</button>
    <button class="nav" onclick="go('ai')" id="nav-ai">🤖 AI Trợ lý học tập</button>
    <button class="nav" onclick="go('quiz')" id="nav-quiz">📝 Kiểm tra / Quiz</button>
    <button class="nav" onclick="go('cards')" id="nav-cards">🗂️ Flashcard <span class="count" id="due-count">0</span></button>
    <button class="nav" onclick="go('notes')" id="nav-notes">📒 Ghi chú nhanh</button>
    <button class="nav" onclick="go('pomo')" id="nav-pomo">⏳ Đồng hồ Pomodoro</button>
    <div class="side-foot">
      <button class="theme-btn" onclick="toggleTheme()">🌓 Đổi giao diện</button>
    </div>
  </nav>

  <main class="content">
    {% with messages = get_flashed_messages(with_categories=true) %}
      {% if messages %}
        <div class="flash">
          {% for cat, msg in messages %}
            <div class="toast {{ 'ok' if cat == 'ok' else 'err' }}">{{ msg }}</div>
          {% endfor %}
        </div>
      {% endif %}
    {% endwith %}

    <!-- PANEL: HOME -->
    <section id="panel-home" class="panel active">
      <h1 class="page">Xin chào bạn!</h1>
      <p class="sub">Không gian tập trung tối đa cho việc học và ôn thi hiệu quả.</p>
      
      <div class="stats">
        <div class="stat"><b id="st-files">0</b><span>Tài liệu học tập</span></div>
        <div class="stat"><b id="st-notes">0</b><span>Ghi chú đã lưu</span></div>
        <div class="stat"><b id="st-cards">0</b><span>Thẻ Flashcard</span></div>
      </div>

      <div class="card">
        <h2>🚀 Thao tác nhanh</h2>
        <p class="lead">Chọn môn học để xem tài liệu Giữa kì / Cuối kì hoặc bắt đầu ôn luyện ngay.</p>
        <div class="subjects">
          {% for s in subjects %}
          <button class="subj" onclick="openSubject('{{ s.id }}')">
            <div class="circle" style="--c1:{{ s.c1 }}; --c2:{{ s.c2 }}">{{ s.icon }}</div>
            <span class="sname">{{ s.name }}</span>
          </button>
          {% endfor %}
        </div>
      </div>
    </section>

    <!-- PANEL: SUBJECTS & FILES -->
    <section id="panel-subjects" class="panel">
      <h1 class="page" id="sub-title">Quản lý Môn học & Tài liệu</h1>
      <p class="sub">Tài liệu được phân loại rõ ràng theo Giữa kì và Cuối kì để ôn tập khoa học.</p>
      
      <div id="subject-selector" class="card">
        <h2>Chọn môn học cần xem:</h2>
        <div class="subjects">
          {% for s in subjects %}
          <button class="subj" onclick="openSubject('{{ s.id }}')">
            <div class="circle" style="--c1:{{ s.c1 }}; --c2:{{ s.c2 }}">{{ s.icon }}</div>
            <span class="sname">{{ s.name }}</span>
          </button>
          {% endfor %}
        </div>
      </div>

      <div id="subject-detail" class="hidden">
        <button class="btn ghost sm" onclick="backToSubjects()" style="margin-bottom:16px;">← Quay lại danh sách môn</button>
        
        <div class="card">
          <div style="display:flex; justify-content:space-between; align-items:center; flex-wrap:wrap; gap:12px;">
            <h2 id="current-subject-name">Tên môn học</h2>
          </div>
          
          <div class="tabs" style="margin-top:16px;">
            <button class="tab-btn active" onclick="switchPeriod('giua-ki')" id="tab-btn-giua-ki">📚 Ôn tập Giữa kì</button>
            <button class="tab-btn" onclick="switchPeriod('cuoi-ki')" id="tab-btn-cuoi-ki">🏆 Ôn tập Cuối kì</button>
          </div>

          <form id="upload-form" action="{{ url_for('upload_file_route') }}" method="POST" enctype="multipart/form-data" style="margin-top:16px;">
            <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <input type="hidden" name="subject" id="form-subject" value="">
            <input type="hidden" name="period" id="form-period" value="giua-ki">
            
            <label class="drop" id="dropzone">
              <span>📤 Kéo thả tệp vào đây hoặc bấm để chọn tệp (<span id="period-label-text">Giữa kì</span>)</span>
              <input type="file" name="files" multiple onchange="this.form.submit()">
            </label>
          </form>

          <div style="margin-top:20px;">
            <h3 id="file-list-heading">Danh sách tài liệu Giữa kì</h3>
            <div id="file-container" class="list"></div>
          </div>
        </div>
      </div>
    </section>

    <!-- PANEL: AI TUTOR -->
    <section id="panel-ai" class="panel">
      <h1 class="page">🤖 AI Trợ lý học tập</h1>
      <p class="sub">Hỏi đáp trực tiếp dựa trên toàn bộ tài liệu và ghi chú của bạn.</p>
      <div class="card">
        <div class="chat-box" id="chat-box">
          <div class="msg-bot">Xin chào! Bạn cần tôi giải đáp thắc mắc về môn học nào hoặc nội dung tài liệu nào hôm nay?</div>
        </div>
        <form onsubmit="askAI(event)" style="display:flex; gap:10px;">
          <input type="text" id="ai-q" placeholder="Nhập câu hỏi của bạn (ví dụ: Công thức tính đạo hàm là gì?)..." autocomplete="off" style="margin:0;">
          <button class="btn" type="submit">Gửi hỏi</button>
        </form>
      </div>
    </section>

    <!-- PANEL: QUIZ -->
    <section id="panel-quiz" class="panel">
      <h1 class="page">📝 Kiểm tra Trắc nghiệm (Quiz)</h1>
      <p class="sub">Tự động tạo câu hỏi điền khuyết từ tài liệu học tập của bạn.</p>
      <div class="card study">
        <div id="quiz-area">
          <p class="lead">Bấm nút bên dưới để tạo bài kiểm tra ôn tập ngay.</p>
          <button class="btn" onclick="loadQuiz()">Tạo đề kiểm tra mới</button>
        </div>
      </div>
    </section>

    <!-- PANEL: CARDS -->
    <section id="panel-cards" class="panel">
      <h1 class="page">🗂️ Ôn tập Flashcard (Leitner)</h1>
      <p class="sub">Ghi nhớ kiến thức siêu tốc bằng phương pháp lặp lại ngắt quãng.</p>
      <div class="two">
        <div class="card">
          <h2>Thêm thẻ nhớ mới</h2>
          <form onsubmit="addCard(event)">
            <label>Mặt trước (Câu hỏi / Thuật ngữ):</label>
            <textarea id="card-front" rows="3" required></textarea>
            <label>Mặt sau (Đáp án / Giải thích):</label>
            <textarea id="card-back" rows="3" required></textarea>
            <button class="btn" type="submit">Lưu thẻ nhớ</button>
          </form>
        </div>
        <div class="card study">
          <h2>Ôn tập hôm nay</h2>
          <div id="flashcard-area">
            <p class="lead">Không có thẻ cần ôn hôm nay.</p>
          </div>
        </div>
      </div>
    </section>

    <!-- PANEL: NOTES -->
    <section id="panel-notes" class="panel">
      <h1 class="page">📒 Ghi chú nhanh</h1>
      <p class="sub">Lưu trữ các công thức, định nghĩa hoặc tóm tắt kiến thức.</p>
      <div class="card">
        <form onsubmit="addNote(event)">
          <textarea id="note-content" rows="4" placeholder="Nhập nội dung ghi chú..." required></textarea>
          <input type="text" id="note-tags" placeholder="Thẻ (nhãn), phân cách bằng dấu phẩy (vd: toan, cong-thuc)">
          <button class="btn" type="submit">Thêm ghi chú</button>
        </form>
      </div>
      <div id="notes-list"></div>
    </section>

    <!-- PANEL: POMODORO -->
    <section id="panel-pomo" class="panel">
      <h1 class="page">⏳ Đồng hồ Pomodoro</h1>
      <p class="sub">Tập trung cao độ 25 phút học, 5 phút nghỉ ngơi.</p>
      <div class="card pomo">
        <div class="time" id="pomo-time">25:00</div>
        <p class="lead" id="pomo-status">Thời gian tập trung</p>
        <div class="btns">
          <button class="btn" onclick="startPomo()">Bắt đầu</button>
          <button class="btn ghost" onclick="pausePomo()">Tạm dừng</button>
          <button class="btn ghost" onclick="resetPomo()">Đặt lại</button>
        </div>
      </div>
    </section>
  </main>

  <!-- MODAL XEM TÀI LIỆU MẠNH MẼ -->
  <div class="viewer-modal" id="doc-viewer-modal">
    <div class="viewer-content">
      <div class="viewer-header">
        <h3 id="viewer-title">Xem tài liệu</h3>
        <button class="btn sm ghost" onclick="closeViewer()">Đóng ✕</button>
      </div>
      <div class="viewer-body" id="viewer-body-content">
        Đang tải nội dung...
      </div>
    </div>
  </div>

<script>
  let currentSubj = '';
  let currentPeriod = 'giua-ki';
  const subjectsData = {{ subjects_json | safe }};

  function go(id) {
    document.querySelectorAll('.panel').forEach(p => p.classList.remove('active'));
    document.querySelectorAll('.sidebar button.nav').forEach(b => b.removeAttribute('aria-current'));
    document.getElementById('panel-' + id).classList.add('active');
    const nav = document.getElementById('nav-' + id);
    if(nav) nav.setAttribute('aria-current', 'page');
    if(id === 'cards') loadDueCards();
    if(id === 'notes') loadNotes();
    if(id === 'home') loadStats();
  }

  function toggleTheme() {
    const b = document.body;
    b.dataset.theme = b.dataset.theme === 'dark' ? 'light' : 'dark';
  }

  function loadStats() {
    fetch('/api/stats').then(r => r.json()).then(d => {
      document.getElementById('st-files').innerText = d.files;
      document.getElementById('st-notes').innerText = d.notes;
      document.getElementById('st-cards').innerText = d.cards;
      document.getElementById('due-count').innerText = d.due;
    });
  }

  function openSubject(sid) {
    currentSubj = sid;
    currentPeriod = 'giua-ki';
    document.getElementById('form-subject').value = sid;
    document.getElementById('form-period').value = currentPeriod;
    
    const subObj = subjectsData.find(s => s.id === sid);
    if(subObj) {
      document.getElementById('current-subject-name').innerText = subObj.icon + ' ' + subObj.name;
    }
    
    document.getElementById('subject-selector').classList.add('hidden');
    document.getElementById('subject-detail').classList.remove('hidden');
    document.getElementById('sub-title').innerText = subObj ? subObj.name : 'Môn học';
    
    updateTabUI();
    loadSubjectFiles();
    go('subjects');
  }

  function backToSubjects() {
    document.getElementById('subject-detail').classList.add('hidden');
    document.getElementById('subject-selector').classList.remove('hidden');
    document.getElementById('sub-title').innerText = 'Quản lý Môn học & Tài liệu';
  }

  function switchPeriod(period) {
    currentPeriod = period;
    document.getElementById('form-period').value = period;
    updateTabUI();
    loadSubjectFiles();
  }

  function updateTabUI() {
    const gkBtn = document.getElementById('tab-btn-giua-ki');
    const ckBtn = document.getElementById('tab-btn-cuoi-ki');
    const lbl = document.getElementById('period-label-text');
    const heading = document.getElementById('file-list-heading');

    if(currentPeriod === 'giua-ki') {
      gkBtn.classList.add('active');
      ckBtn.classList.remove('active');
      lbl.innerText = 'Giữa kì';
      heading.innerText = 'Danh sách tài liệu Ôn tập Giữa kì';
    } else {
      ckBtn.classList.add('active');
      gkBtn.classList.remove('active');
      lbl.innerText = 'Cuối kì';
      heading.innerText = 'Danh sách tài liệu Ôn tập Cuối kì';
    }
  }

  function loadSubjectFiles() {
    if(!currentSubj) return;
    fetch(`/api/files/${currentSubj}/${currentPeriod}`).then(r => r.json()).then(files => {
      const c = document.getElementById('file-container');
      if(files.length === 0) {
        c.innerHTML = `<div class="empty">Chưa có tài liệu nào trong phần này. Hãy tải lên file PDF, Word, Txt, Markdown, Ảnh...</div>`;
        return;
      }
      c.innerHTML = files.map(f => `
        <div class="row">
          <span>${f.icon}</span>
          <span class="name" title="${f.name}">${f.name}</span>
          <span class="meta">${f.size_h} • ${f.date}</span>
          <div class="acts">
            <button class="btn sm" onclick="previewDoc('${currentSubj}', '${currentPeriod}', '${f.name}', '${f.ext}')">👁️ Xem tài liệu</button>
            <a class="btn sm ghost" href="/download/${currentSubj}/${currentPeriod}/${encodeURIComponent(f.name)}">Tải xuống</a>
            <button class="btn sm bad" onclick="deleteFile('${currentSubj}', '${currentPeriod}', '${f.name}')">Xóa</button>
          </div>
        </div>
      `).join('');
    });
  }

  function previewDoc(sub, period, name, ext) {
    const modal = document.getElementById('doc-viewer-modal');
    const title = document.getElementById('viewer-title');
    const body = document.getElementById('viewer-body-content');
    
    title.innerText = 'Đang đọc: ' + name;
    body.innerHTML = 'Đang tải nội dung...';
    modal.classList.add('active');

    // Nếu là ảnh, hiển thị trực tiếp thẻ img
    const imageExts = ['.png', '.jpg', '.jpeg', '.gif', '.webp'];
    if(imageExts.includes(ext.toLowerCase())) {
      body.innerHTML = `<img src="/download/${sub}/${period}/${encodeURIComponent(name)}" alt="${name}">`;
      return;
    }

    // Nếu là PDF hoặc văn bản/Word
    fetch(`/api/preview/${sub}/${period}/${encodeURIComponent(name)}`).then(r => r.json()).then(res => {
      if(res.ok) {
        if(res.is_text) {
          body.innerHTML = marked.parse(res.content);
          if(window.MathJax) {
            MathJax.typesetPromise([body]);
          }
        } else {
          body.innerHTML = `<p class="lead">Không thể hiển thị định dạng này trực tiếp. Bạn hãy bấm tải xuống hoặc mở bằng ứng dụng trên máy.</p>`;
        }
      } else {
        body.innerHTML = `<p class="lead" style="color:var(--bad);">Không thể đọc nội dung tệp này.</p>`;
      }
    });
  }

  function closeViewer() {
    document.getElementById('doc-viewer-modal').classList.remove('active');
  }

  function deleteFile(sub, period, name) {
    if(!confirm(`Bạn có chắc chắn muốn xóa file ${name}?`)) return;
    fetch('/api/delete-file', {
      method: 'POST',
      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': '{{ csrf_token() }}'},
      body: JSON.stringify({subject: sub, period: period, name: name})
    }).then(r => r.json()).then(res => {
      if(res.ok) loadSubjectFiles();
      else alert(res.error || 'Lỗi khi xóa file.');
    });
  }

  function askAI(e) {
    e.preventDefault();
    const qInput = document.getElementById('ai-q');
    const q = qInput.value.trim();
    if(!q) return;
    qInput.value = '';

    const box = document.getElementById('chat-box');
    box.innerHTML += `<div class="msg-user">${escapeHtml(q)}</div>`;
    box.scrollTop = box.scrollHeight;

    fetch('/api/ask', {
      method: 'POST',
      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': '{{ csrf_token() }}'},
      body: JSON.stringify({question: q})
    }).then(r => r.json()).then(res => {
      let srcHtml = '';
      if(res.sources && res.sources.length > 0) {
        srcHtml = res.sources.map(s => `
          <div class="src">
            <span class="score">${s.score}% phù hợp</span>
            <b>${escapeHtml(s.source)}</b><br>${s.html}
          </div>
        `).join('');
      }
      box.innerHTML += `
        <div class="msg-bot">
          <div>${res.answer_html}</div>
          ${srcHtml}
        </div>
      `;
      box.scrollTop = box.scrollHeight;
      if(window.MathJax) MathJax.typesetPromise();
    });
  }

  function escapeHtml(text) {
    return text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }

  function loadQuiz() {
    const area = document.getElementById('quiz-area');
    area.innerHTML = '<p class="lead">Đang tạo bộ câu hỏi thông minh từ tài liệu...</p>';
    fetch('/api/quiz').then(r => r.json()).then(quiz => {
      if(!quiz || quiz.length === 0) {
        area.innerHTML = `<p class="lead">Chưa đủ tài liệu văn bản để tạo Quiz. Hãy tải lên tệp .txt, .docx, .pdf hoặc thêm ghi chú.</p><button class="btn" onclick="loadQuiz()">Thử lại</button>`;
        return;
      }
      window.quizData = quiz;
      window.quizIdx = 0;
      window.quizScore = 0;
      renderQuizQuestion();
    });
  }

  function renderQuizQuestion() {
    const qz = window.quizData;
    const i = window.quizIdx;
    const area = document.getElementById('quiz-area');
    if(i >= qz.length) {
      area.innerHTML = `
        <h2>🎉 Hoàn thành bài kiểm tra!</h2>
        <p class="lead" style="margin:16px 0;">Điểm số của bạn: <b>${window.quizScore} / ${qz.length}</b> câu đúng.</p>
        <button class="btn" onclick="loadQuiz()">Làm đề khác</button>
      `;
      return;
    }
    const item = qz[i];
    area.innerHTML = `
      <p class="meta" style="margin-bottom:8px;">Câu ${i+1} / ${qz.length} • Nguồn: ${escapeHtml(item.source)}</p>
      <div class="face" style="margin-bottom:16px;">${escapeHtml(item.q)}</div>
      <div class="opts">
        ${item.options.map((opt, idx) => `
          <button class="opt" onclick="answerQuiz(${idx}, ${item.answer})">${String.fromCharCode(65+idx)}. ${escapeHtml(opt)}</button>
        `).join('')}
      </div>
    `;
    if(window.MathJax) MathJax.typesetPromise();
  }

  function answerQuiz(selected, correct) {
    const buttons = document.querySelectorAll('.opts .opt');
    buttons.forEach((btn, idx) => {
      btn.disabled = true;
      if(idx === correct) btn.classList.add('right');
      else if(idx === selected) btn.classList.add('wrong');
    });
    if(selected === correct) window.quizScore++;
    setTimeout(() => {
      window.quizIdx++;
      renderQuizQuestion();
    }, 1400);
  }

  let currentCard = null;
  function addCard(e) {
    e.preventDefault();
    const front = document.getElementById('card-front').value;
    const back = document.getElementById('card-back').value;
    fetch('/api/cards', {
      method: 'POST',
      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': '{{ csrf_token() }}'},
      body: JSON.stringify({front, back})
    }).then(r => r.json()).then(res => {
      if(res.ok) {
        document.getElementById('card-front').value = '';
        document.getElementById('card-back').value = '';
        loadDueCards();
        loadStats();
        alert('Đã thêm thẻ nhớ thành công!');
      }
    });
  }

  function loadDueCards() {
    fetch('/api/cards/due').then(r => r.json()).then(card => {
      const area = document.getElementById('flashcard-area');
      if(!card) {
        area.innerHTML = '<p class="lead">Tuyệt vời! Bạn đã ôn tập hết thẻ hôm nay.</p>';
        currentCard = null;
        return;
      }
      currentCard = card;
      area.innerHTML = `
        <div class="face" id="card-display" onclick="flipCard()">${escapeHtml(card.front)}</div>
        <p class="meta" style="margin:10px 0;">(Bấm vào thẻ để lật xem đáp án)</p>
        <div id="card-actions" class="hidden" style="display:flex; gap:10px; justify-content:center; margin-top:14px;">
          <button class="btn bad sm" onclick="reviewCard(1)">Quên (Ôn lại sớm)</button>
          <button class="btn ok sm" onclick="reviewCard(3)">Nhớ tốt</button>
        </div>
      `;
      if(window.MathJax) MathJax.typesetPromise();
    });
  }

  function flipCard() {
    if(!currentCard) return;
    const disp = document.getElementById('card-display');
    const acts = document.getElementById('card-actions');
    if(disp.innerText === currentCard.front) {
      disp.innerText = currentCard.back;
      acts.classList.remove('hidden');
    } else {
      disp.innerText = currentCard.front;
      acts.classList.add('hidden');
    }
  }

  function reviewCard(box) {
    if(!currentCard) return;
    fetch('/api/cards/review', {
      method: 'POST',
      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': '{{ csrf_token() }}'},
      body: JSON.stringify({id: currentCard.id, box: box})
    }).then(() => {
      loadDueCards();
      loadStats();
    });
  }

  function addNote(e) {
    e.preventDefault();
    const content = document.getElementById('note-content').value;
    const tags = document.getElementById('note-tags').value;
    fetch('/api/notes', {
      method: 'POST',
      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': '{{ csrf_token() }}'},
      body: JSON.stringify({content, tags})
    }).then(r => r.json()).then(res => {
      if(res.ok) {
        document.getElementById('note-content').value = '';
        document.getElementById('note-tags').value = '';
        loadNotes();
        loadStats();
      }
    });
  }

  function loadNotes() {
    fetch('/api/notes').then(r => r.json()).then(notes => {
      const list = document.getElementById('notes-list');
      if(notes.length === 0) {
        list.innerHTML = '<div class="empty">Chưa có ghi chú nào.</div>';
        return;
      }
      list.innerHTML = notes.map(n => `
        <div class="card">
          <div class="note-body">${escapeHtml(n.content)}</div>
          <div class="note-foot">
            <span class="meta">${n.updated}</span>
            <button class="btn sm bad" onclick="deleteNote(${n.id})">Xóa</button>
          </div>
        </div>
      `).join('');
    });
  }

  function deleteNote(id) {
    if(!confirm('Xóa ghi chú này?')) return;
    fetch('/api/notes/' + id, {
      method: 'DELETE',
      headers: {'X-CSRF-Token': '{{ csrf_token() }}'}
    }).then(() => {
      loadNotes();
      loadStats();
    });
  }

  let pomoTimer = null;
  let secondsLeft = 25 * 60;
  let isRunning = false;

  function updatePomoDisplay() {
    const m = Math.floor(secondsLeft / 60);
    const s = secondsLeft % 60;
    document.getElementById('pomo-time').innerText = `${m.toString().padStart(2,'0')}:${s.toString().padStart(2,'0')}`;
  }

  function startPomo() {
    if(isRunning) return;
    isRunning = true;
    document.getElementById('pomo-status').innerText = 'Đang tập trung học tập...';
    pomoTimer = setInterval(() => {
      if(secondsLeft > 0) {
        secondsLeft--;
        updatePomoDisplay();
      } else {
        clearInterval(pomoTimer);
        isRunning = false;
        alert('Đã hết giờ học! Hãy nghỉ ngơi 5 phút nhé.');
        secondsLeft = 5 * 60;
        document.getElementById('pomo-status').innerText = 'Thời gian nghỉ ngơi';
        updatePomoDisplay();
      }
    }, 1000);
  }

  function pausePomo() {
    clearInterval(pomoTimer);
    isRunning = false;
    document.getElementById('pomo-status').innerText = 'Đã tạm dừng';
  }

  function resetPomo() {
    clearInterval(pomoTimer);
    isRunning = false;
    secondsLeft = 25 * 60;
    document.getElementById('pomo-status').innerText = 'Thời gian tập trung';
    updatePomoDisplay();
  }

  window.onload = () => {
    loadStats();
  };
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------
# Flask Routes
# --------------------------------------------------------------------------
@app.route('/')
def index():
    migrate_legacy_files()
    subjects_json = json.dumps(SUBJECTS, ensure_ascii=False)
    return render_template_string(HTML_TEMPLATE, subjects=SUBJECTS, subjects_json=subjects_json)


@app.route('/api/stats')
def api_stats():
    db = get_db()
    files = len(list_files())
    notes = db.execute('SELECT COUNT(*) FROM notes').fetchone()[0]
    cards = db.execute('SELECT COUNT(*) FROM cards').fetchone()[0]
    due = db.execute('SELECT COUNT(*) FROM cards WHERE due <= ?', (today_s(),)).fetchone()[0]
    return jsonify(files=files, notes=notes, cards=cards, due=due)


@app.route('/api/files/<subject>/<period>')
def api_files_by_period(subject, period):
    if subject not in SUBJECT_BY_ID or period not in PERIODS:
        return jsonify([])
    base = subject_period_dir(subject, period)
    if not os.path.isdir(base):
        return jsonify([])
    items = []
    for name in sorted(os.listdir(base), key=str.lower):
        path = safe_path(subject, period, name)
        if not path or not os.path.isfile(path):
            continue
        st = os.stat(path)
        ext = os.path.splitext(name)[1].lower()
        items.append({
            'name': name, 'size': st.st_size,
            'size_h': human_size(st.st_size),
            'date': datetime.fromtimestamp(st.st_mtime).strftime('%d/%m/%Y %H:%M'),
            'icon': FILE_ICONS.get(ext, '🖼️' if ext in IMAGE_EXT else '📎'),
            'ext': ext
        })
    return jsonify(items)


@app.route('/upload', methods=['POST'])
def upload_file_route():
    subject = request.form.get('subject', 'khac')
    period = request.form.get('period', 'giua-ki')
    if subject not in SUBJECT_BY_ID or period not in PERIODS:
        flash('Môn học hoặc học kì không hợp lệ.', 'err')
        return redirect(url_for('index'))

    uploaded_files = request.files.getlist('files')
    target_dir = subject_period_dir(subject, period)
    os.makedirs(target_dir, exist_ok=True)

    saved_count = 0
    for f in uploaded_files:
        if f and f.filename:
            raw_name = clean_filename(f.filename)
            if not raw_name:
                continue
            ext = os.path.splitext(raw_name)[1].lower()
            if ext not in ALLOWED_EXT:
                continue
            final_name = unique_name(subject, period, raw_name)
            f.save(os.path.join(target_dir, final_name))
            saved_count += 1

    if saved_count > 0:
        flash(f'Đã tải lên thành công {saved_count} tệp!', 'ok')
    else:
        flash('Không có tệp hợp lệ nào được tải lên.', 'err')
    return redirect(url_for('index', _anchor='subjects'))


@app.route('/download/<subject>/<period>/<name>')
def download_file(subject, period, name):
    path = safe_path(subject, period, name)
    if not path or not os.path.isfile(path):
        abort(404)
    return send_file(path, as_attachment=True)


@app.route('/api/preview/<subject>/<period>/<name>')
def api_preview_file(subject, period, name):
    path = safe_path(subject, period, name)
    if not path or not os.path.isfile(path):
        return jsonify(ok=False), 404
    
    ext = os.path.splitext(name)[1].lower()
    if ext in TEXT_EXT or ext == '.pdf' or ext == '.docx':
        content = extract_text(path)
        return jsonify(ok=True, is_text=True, content=content)
    return jsonify(ok=True, is_text=False)


@app.route('/api/delete-file', methods=['POST'])
def delete_file_api():
    data = request.get_json() or {}
    subject = data.get('subject')
    period = data.get('period')
    name = data.get('name')
    path = safe_path(subject, period, name)
    if path and os.path.isfile(path):
        os.remove(path)
        return jsonify(ok=True)
    return jsonify(error='Không tìm thấy tệp.'), 400


@app.route('/api/ask', methods=['POST'])
def api_ask():
    data = request.get_json() or {}
    q = (data.get('question') or '').strip()
    if not q:
        return jsonify(answer_html='Vui lòng nhập câu hỏi.', sources=[])
    db = get_db()
    res = answer_question(q, db)
    db.execute('INSERT INTO chat(question, answer, created) VALUES (?, ?, ?)',
               (q, res['answer_html'], now_s()))
    db.commit()
    return jsonify(res)


@app.route('/api/quiz')
def api_quiz():
    db = get_db()
    quiz = generate_quiz(db, n=5)
    return jsonify(quiz)


@app.route('/api/cards', methods=['GET', 'POST'])
def api_cards():
    db = get_db()
    if request.method == 'POST':
        data = request.get_json() or {}
        front = (data.get('front') or '').strip()
        back = (data.get('back') or '').strip()
        if front and back:
            db.execute('INSERT INTO cards(front, back, due, created) VALUES (?, ?, ?, ?)',
                       (front, back, today_s(), now_s()))
            db.commit()
            return jsonify(ok=True)
        return jsonify(error='Thiếu nội dung.'), 400
    else:
        cards = db.execute('SELECT * FROM cards ORDER BY id DESC').fetchall()
        return jsonify([dict(c) for c in cards])


@app.route('/api/cards/due')
def api_cards_due():
    db = get_db()
    card = db.execute('SELECT * FROM cards WHERE due <= ? ORDER BY reviews ASC, id ASC LIMIT 1',
                      (today_s(),)).fetchone()
    if not card:
        card = db.execute('SELECT * FROM cards ORDER BY due ASC, reviews ASC LIMIT 1').fetchone()
    return jsonify(dict(card)) if card else jsonify(None)


@app.route('/api/cards/review', methods=['POST'])
def api_cards_review():
    data = request.get_json() or {}
    cid = data.get('id')
    box = int(data.get('box', 1))
    db = get_db()
    card = db.execute('SELECT * FROM cards WHERE id = ?', (cid,)).fetchone()
    if not card:
        return jsonify(error='Không tìm thấy thẻ.'), 404
    next_box = min(5, max(1, box))
    days = BOX_DAYS.get(next_box, 1)
    due_date = (date.today() + timedelta(days=days)).isoformat()
    db.execute('UPDATE cards SET box = ?, due = ?, reviews = reviews + 1 WHERE id = ?',
               (next_box, due_date, cid))
    db.commit()
    return jsonify(ok=True)


@app.route('/api/notes', methods=['GET', 'POST'])
def api_notes():
    db = get_db()
    if request.method == 'POST':
        data = request.get_json() or {}
        content = (data.get('content') or '').strip()
        tags = (data.get('tags') or '').strip()
        if content:
            t = now_s()
            db.execute('INSERT INTO notes(content, tags, created, updated) VALUES (?, ?, ?, ?)',
                       (content, tags, t, t))
            db.commit()
            return jsonify(ok=True)
        return jsonify(error='Nội dung trống.'), 400
    else:
        notes = db.execute('SELECT * FROM notes ORDER BY id DESC').fetchall()
        return jsonify([dict(n) for n in notes])


@app.route('/api/notes/<int:nid>', methods=['DELETE'])
def api_delete_note(nid):
    db = get_db()
    db.execute('DELETE FROM notes WHERE id = ?', (nid,))
    db.commit()
    return jsonify(ok=True)


# --------------------------------------------------------------------------
# Khởi chạy ứng dụng
# --------------------------------------------------------------------------
if __name__ == '__main__':
    init_db()
    host = os.environ.get('STUDYSPACE_HOST', '127.0.0.1')
    port = int(os.environ.get('STUDYSPACE_PORT', 5000))
    debug = os.environ.get('STUDYSPACE_DEBUG', '0') == '1'
    print(f'[*] StudySpace Pro đang chạy tại: http://{host}:{port}')
    app.run(host=host, port=port, debug=debug)