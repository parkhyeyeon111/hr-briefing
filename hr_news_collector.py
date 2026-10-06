"""
HR 이슈 & 뉴스 수집 파이프라인 (보상운영 대시보드용)

흐름: 수집(구글 뉴스 RSS 키워드 검색, 구글 뉴스 site: 검색으로 정부 부처 보도, 선택: 법령 API)
      → 정규화 → 중복 제거 → 분류·태깅 → 2줄 요약 → SQLite 저장 → articles.json 내보내기

필요 패키지:  pip install requests feedparser beautifulsoup4
              (선택) pip install anthropic
API 키:       필요 없음. 키 없이 구글 뉴스 RSS만으로 전체 파이프라인이 동작합니다.
선택 환경 변수:
              LAW_OC              국가법령정보 공동활용 OC 값 (있으면 법령 공포·시행 정보 추가 수집)
              ANTHROPIC_API_KEY   (있으면 기사 설명문을 2문장으로 요약, 없으면 원문 설명·매체명 사용)
실행 주기:    매일 아침 1회 (한국시간 07:30 ~ 08:00)
              GitHub Actions(.github/workflows/collector.yml)의 cron '30 22 * * *'(UTC)로 실행합니다.
              GitHub 예약 실행은 부하에 따라 수 분~수십 분 늦게 시작될 수 있어 08:00 전후 도착을 목표로 합니다.
              로컬 실행: python hr_news_collector.py
하루 1회 수집이므로 검색 기간은 직전 실행과 겹치도록 '최근 2일'로 잡고, 겹친 기사는 중복 제거 단계에서 걸러냅니다.
"""
from __future__ import annotations

import difflib
import hashlib
import html
import json
import os
import re
import sqlite3
import sys
import time
from datetime import datetime, timedelta, timezone
from urllib.parse import urlencode

import feedparser
import requests
from bs4 import BeautifulSoup

KST = timezone(timedelta(hours=9))
DB_PATH = os.getenv("HR_DB", "data/hr_news.db")          # 워크플로가 저장소에 커밋해 다음 날 중복 제거에 재사용
EXPORT_PATH = os.getenv("HR_EXPORT", "data/articles.json")  # 대시보드가 읽는 파일
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 HR-Dashboard-Collector"}

# ─────────────────────────────────────────────────────────────
# 0. 구글 뉴스 RSS 수집 설정
# ─────────────────────────────────────────────────────────────
GNEWS_ENDPOINT = "https://news.google.com/rss/search"
GNEWS_LOCALE = {"hl": "ko", "gl": "KR", "ceid": "KR:ko"}   # 한국어 인터페이스, 한국 지역판
RECENT_DAYS = 2           # 기본 검색 기간: 최근 2일 (when:2d)
FALLBACK_DAYS = 7         # 결과가 적은 키워드는 7일로 넓혀 한 번 더 조회 (when:7d)
MIN_PER_QUERY = 5         # 이 건수보다 적으면 FALLBACK_DAYS로 재조회
MAX_PER_QUERY = 40        # 키워드당 최신순 최대 보관 건수 (RSS는 한 번에 최대 약 100건 반환)
REQUEST_INTERVAL = 1.2    # 요청 간 대기(초): 연속 요청으로 차단되지 않도록
MAX_RETRIES = 3

# ─────────────────────────────────────────────────────────────
# 1. 검색 키워드 (탭별) — 대시보드 탭 id와 동일하게 유지
#    띄어쓰기가 있는 키워드는 자동으로 "따옴표" 처리해 구문 일치로 검색합니다.
#    더 정밀한 검색식이 필요하면 QUERY_OVERRIDES에 구글 검색 연산자(OR, -, 괄호)로 적습니다.
# ─────────────────────────────────────────────────────────────
KEYWORDS: dict[str, list[str]] = {
    "hrm": ["최저임금", "통상임금", "4대보험 요율", "국민연금 보험료율", "건강보험료율",
            "연말정산", "퇴직금", "퇴직연금", "연차수당", "식대 비과세", "근로시간 단축"],
    "hrbp": ["인사평가 제도", "성과급 제도", "조직문화 진단", "리더십 개발", "직급체계 개편"],
    "talent": ["채용 시장 동향", "수시채용", "헤드헌팅", "채용 브랜딩", "공정채용"],
    "erir": ["노조법 개정", "취업규칙 불이익 변경", "부당해고 판정", "직장 내 괴롭힘", "단체교섭"],
}

QUERY_OVERRIDES: dict[str, str] = {
    "최저임금": '최저임금 (시급 OR 인상 OR 고시 OR 최저임금위원회) -알바몬 -알바천국',
    "통상임금": '통상임금 (판결 OR 대법원 OR 수당 OR 상여금)',
    "4대보험 요율": '("4대보험" OR "사회보험") (요율 OR 보험료율 OR 인상)',
    "연말정산": '연말정산 (공제 OR 간소화 OR 환급 OR 국세청)',
    "퇴직금": '퇴직금 (지급 OR 판결 OR 계산 OR 퇴직급여) -코인',
    "연차수당": '("연차수당" OR "연차휴가 수당" OR "미사용 연차")',
    "식대 비과세": '("식대 비과세" OR "식대" 비과세 한도)',
    "헤드헌팅": '(헤드헌팅 OR 서치펌) 채용',
    "단체교섭": '(단체교섭 OR 임단협 OR 임금교섭)',
}

# 정부 부처 보도: 별도 API 키 없이 구글 뉴스의 site: 검색으로 수집합니다.
# (정책브리핑 korea.kr은 부처 보도자료를 모아 게시하므로 부처명과 함께 검색)
GOV_SITE_QUERIES: list[tuple[str, str, str | None]] = [
    # (대시보드 출처 코드, 검색식, 탭 힌트)
    ("moel", "site:korea.kr 고용노동부", None),
    ("moel", "site:moel.go.kr", None),
    ("moef", "site:korea.kr 기획재정부 (소득세 OR 세법 OR 근로소득)", "hrm"),
    ("nts",  "site:korea.kr 국세청 (연말정산 OR 원천세 OR 지급명세서)", "hrm"),
    ("mw",   "최저임금위원회", "hrm"),
]

# 태그 규칙: (태그, 매칭 단어들) — 대시보드 자체 분류(HR/ER/IR)와 실무 용어 기준
TAG_RULES: list[tuple[str, list[str]]] = [
    ("최저임금", ["최저임금", "최저시급"]),
    ("통상임금", ["통상임금"]),
    ("4대보험", ["4대보험", "사회보험", "고용보험", "산재보험", "건강보험료"]),
    ("국민연금", ["국민연금"]),
    ("급여", ["급여", "임금", "수당", "상여"]),
    ("연말정산", ["연말정산", "근로소득공제", "간소화"]),
    ("비과세", ["비과세", "식대"]),
    ("퇴직금", ["퇴직금", "퇴직급여", "퇴직연금"]),
    ("근태", ["근태", "근로시간", "연장근로", "4.5일제", "유연근무"]),
    ("연차", ["연차"]),
    ("성과관리", ["성과", "평가", "KPI", "OKR"]),
    ("조직문화", ["조직문화", "조직개발", "몰입"]),
    ("채용시장", ["채용", "공채", "구직"]),
    ("헤드헌팅", ["헤드헌팅", "서치펌"]),
    ("노조법", ["노조법", "노동조합", "노란봉투"]),
    ("단체교섭", ["단체교섭", "임단협", "임금교섭"]),
    ("취업규칙", ["취업규칙"]),
    ("노동위원회", ["노동위원회", "부당해고", "구제신청"]),
    ("판례", ["대법원", "판결", "판례", "전원합의체"]),
]
HOT_TAGS = {"급여", "통상임금", "4대보험", "국민연금", "최저임금"}
LAW_TERMS = ["입법예고", "시행령", "시행규칙", "고시", "공포", "개정안", "시행"]
URGENT_TERMS = ["요율", "인상", "개정", "시행", "고시", "전원합의체", "판결"]
DOMAIN_BY_TAB = {"hrm": "HR", "hrbp": "HR", "talent": "HR", "erir": "ER"}

# ─────────────────────────────────────────────────────────────
# 2. 수집기
# ─────────────────────────────────────────────────────────────
def clean(text: str) -> str:
    text = BeautifulSoup(html.unescape(text or ""), "html.parser").get_text(" ")
    return re.sub(r"\s+", " ", text).replace("\xa0", " ").strip()


def build_query(keyword: str, days: int) -> str:
    """키워드 → 구글 뉴스 검색식. 구문 일치 + 기간 연산자(when:Nd)."""
    expr = QUERY_OVERRIDES.get(keyword)
    if expr is None:
        expr = f'"{keyword}"' if " " in keyword and not keyword.startswith("site:") else keyword
    return f"{expr} when:{days}d"


def gnews_url(query: str) -> str:
    return f"{GNEWS_ENDPOINT}?{urlencode({'q': query, **GNEWS_LOCALE})}"


def fetch_feed(url: str) -> feedparser.FeedParserDict | None:
    """재시도·백오프 포함 RSS 요청. 실패 시 None."""
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            r = requests.get(url, headers=UA, timeout=15)
            if r.status_code == 200:
                return feedparser.parse(r.content)
            if r.status_code in (429, 500, 502, 503, 504):
                time.sleep(REQUEST_INTERVAL * 2 ** attempt)
                continue
            print(f"[warn] HTTP {r.status_code}: {url}")
            return None
        except requests.RequestException as e:
            print(f"[warn] 요청 실패({attempt}/{MAX_RETRIES}): {e}")
            time.sleep(REQUEST_INTERVAL * 2 ** attempt)
    return None


def entry_date(e) -> datetime | None:
    t = e.get("published_parsed") or e.get("updated_parsed")
    return datetime(*t[:6], tzinfo=timezone.utc).astimezone(KST) if t else None


def parse_entry(e, src: str, tab: str | None) -> dict | None:
    dt = entry_date(e)
    if not dt or not e.get("link"):
        return None
    publisher = clean(e.get("source", {}).get("title", "")) if e.get("source") else ""
    title = clean(e.get("title", ""))
    if publisher and title.endswith(f" - {publisher}"):           # "제목 - 매체명" 꼬리 제거
        title = title[: -len(publisher) - 3].strip()
    elif " - " in title:
        title, publisher = title.rsplit(" - ", 1)[0].strip(), publisher or title.rsplit(" - ", 1)[1].strip()

    # 구글 뉴스 RSS 설명문은 대부분 '제목 + 매체명' 링크 묶음이라 실제 본문 요약이 없을 수 있음
    desc = clean(e.get("summary", ""))
    for noise in (title, publisher):
        desc = desc.replace(noise, " ") if noise else desc
    desc = re.sub(r"\s+", " ", desc).strip()
    has_desc = len(desc) >= 30

    return {
        "src": src, "tab_hint": tab, "title": title, "publisher": publisher,
        "summary": desc if has_desc else "", "has_desc": has_desc,
        "url": e.link, "date": dt,
    }


def collect_google_rss(keyword: str, tab: str | None, src: str = "google") -> list[dict]:
    """키워드 1개에 대해 최근 2일 기사를 최신순으로 최대 MAX_PER_QUERY건 수집.
    결과가 MIN_PER_QUERY건 미만이면 기간을 FALLBACK_DAYS로 넓혀 한 번 더 조회한다."""
    items: list[dict] = []
    for days in (RECENT_DAYS, FALLBACK_DAYS):
        feed = fetch_feed(gnews_url(build_query(keyword, days)))
        time.sleep(REQUEST_INTERVAL)
        if feed is None:
            break
        cutoff = datetime.now(KST) - timedelta(days=days, hours=6)   # when: 연산자가 놓치는 오래된 기사 2차 필터
        seen, items = set(), []
        for e in feed.entries:
            a = parse_entry(e, src, tab)
            if not a or a["date"] < cutoff:
                continue
            key = (a["title"], a["publisher"])
            if key in seen:
                continue
            seen.add(key)
            items.append(a)
        items.sort(key=lambda x: x["date"], reverse=True)
        if len(items) >= MIN_PER_QUERY:
            break
    return items[:MAX_PER_QUERY]


def collect_gov_sites() -> list[dict]:
    out = []
    for src, query, tab in GOV_SITE_QUERIES:
        out += collect_google_rss(query, tab, src=src)
    return out


WATCH_LAWS = ["근로기준법", "최저임금법", "근로자퇴직급여 보장법", "소득세법", "국민연금법",
              "국민건강보험법", "고용보험법", "노동조합 및 노동관계조정법", "남녀고용평등"]


def collect_law_api() -> list[dict]:
    """(선택) 국가법령정보 공동활용 API: LAW_OC가 있을 때만 최근 공포 법령을 '법령·고시' 카드로 변환."""
    oc = os.getenv("LAW_OC")
    if not oc:
        return []
    out = []
    since = (datetime.now(KST) - timedelta(days=14)).strftime("%Y%m%d")
    for name in WATCH_LAWS:
        r = requests.get("https://www.law.go.kr/DRF/lawSearch.do",
                         params={"OC": oc, "target": "law", "type": "JSON", "query": name, "display": 20},
                         headers=UA, timeout=10)
        if r.status_code != 200:
            continue
        laws = r.json().get("LawSearch", {}).get("law", [])
        for law in laws if isinstance(laws, list) else [laws]:
            promul = str(law.get("공포일자", ""))
            if promul < since:
                continue
            eff = str(law.get("시행일자", ""))
            out.append({
                "src": "law", "tab_hint": "erir" if "노동조합" in law.get("법령명한글", "") else "hrm",
                "title": f"{law.get('법령명한글')} {law.get('제개정구분명', '')} 공포",
                "publisher": "국가법령정보센터", "has_desc": True,
                "summary": f"공포일 {promul}, 시행일 {eff}. 급여·인사 규정 반영 여부를 확인하세요.",
                "url": "https://www.law.go.kr" + law.get("법령상세링크", ""),
                "date": datetime.strptime(promul, "%Y%m%d").replace(tzinfo=KST),
                "force_kind": "law",
            })
    return out

# ─────────────────────────────────────────────────────────────
# 3. 정규화 · 중복 제거 · 분류
# ─────────────────────────────────────────────────────────────
def norm_title(t: str) -> str:
    return re.sub(r"[^\w가-힣]", "", re.sub(r"\[.*?\]|\(.*?\)", "", t)).lower()


def make_id(a: dict) -> str:
    return hashlib.sha1(norm_title(a["title"]).encode()).hexdigest()[:16]


def dedupe(items: list[dict], recent_titles: list[str]) -> list[dict]:
    """같은 보도를 여러 매체·여러 키워드가 가져온 경우를 제목 유사도로 제거.
    정부 출처(moel 등)와 일반 뉴스가 겹치면 정부 출처를 남긴다."""
    priority = {"law": 0, "moel": 1, "moef": 1, "nts": 1, "mw": 1, "google": 2}
    seen, out = list(recent_titles), []
    for a in sorted(items, key=lambda x: (priority.get(x["src"], 3), x["date"])):
        nt = norm_title(a["title"])
        if not nt or any(difflib.SequenceMatcher(None, nt, s).ratio() > 0.85 for s in seen[-600:]):
            continue
        seen.append(nt)
        out.append(a)
    return out


def classify(a: dict) -> dict:
    text = f"{a['title']} {a['summary']}"
    tags = [tag for tag, words in TAG_RULES if any(w in text for w in words)][:4]
    scores = {tab: sum(text.count(k.split()[0]) for k in kws) for tab, kws in KEYWORDS.items()}
    tab = a.get("tab_hint") or max(scores, key=scores.get)
    kind = a.get("force_kind") or ("law" if any(t in a["title"] for t in LAW_TERMS) else "news")
    urgent = tab == "hrm" and bool(HOT_TAGS & set(tags)) and any(t in text for t in URGENT_TERMS)
    return {**a, "tab": tab, "tags": tags or ["기타"], "kind": kind, "urgent": urgent,
            "domain": "IR" if {"노조법", "단체교섭"} & set(tags) else DOMAIN_BY_TAB[tab]}


def summarize(a: dict) -> str:
    """2줄 요약.
    - 설명문이 있고 ANTHROPIC_API_KEY가 있으면 Claude로 요약
    - 설명문이 없으면(구글 뉴스 RSS에서 흔함) 제목만으로 내용을 지어내지 않고 매체명 안내문을 사용"""
    fallback = f"{a.get('publisher') or '언론'} 보도입니다. 세부 내용은 원문에서 확인하세요."
    if not a.get("has_desc"):
        return fallback
    base = a["summary"][:400]
    key = os.getenv("ANTHROPIC_API_KEY")
    if not key:
        return base[:140]
    try:
        import anthropic
        msg = anthropic.Anthropic(api_key=key).messages.create(
            model="claude-haiku-4-5-20251001", max_tokens=200,
            messages=[{"role": "user", "content":
                "다음 HR 기사 내용을 급여·노무 담당자 관점에서 한국어 2문장(총 120자 이내)으로 요약해. "
                f"추측하지 말고 내용에 있는 사실만 써.\n제목: {a['title']}\n내용: {base}"}],
        )
        return msg.content[0].text.strip()
    except Exception:
        return base[:140]

# ─────────────────────────────────────────────────────────────
# 4. 저장 · 내보내기
# ─────────────────────────────────────────────────────────────
def db() -> sqlite3.Connection:
    os.makedirs(os.path.dirname(DB_PATH) or ".", exist_ok=True)
    con = sqlite3.connect(DB_PATH)
    con.execute("""CREATE TABLE IF NOT EXISTS articles(
        id TEXT PRIMARY KEY, tab TEXT, domain TEXT, src TEXT, kind TEXT, urgent INTEGER,
        tags TEXT, title TEXT, summary TEXT, url TEXT, date TEXT, norm TEXT, created TEXT)""")
    return con


def save(con: sqlite3.Connection, items: list[dict]) -> int:
    n = 0
    for a in items:
        cur = con.execute(
            "INSERT OR IGNORE INTO articles VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (make_id(a), a["tab"], a["domain"], a["src"], a["kind"], int(a["urgent"]),
             json.dumps(a["tags"], ensure_ascii=False), a["title"], a["summary"], a["url"],
             a["date"].isoformat(), norm_title(a["title"]), datetime.now(KST).isoformat()))
        n += cur.rowcount
    con.commit()
    return n


def export(con: sqlite3.Connection, days: int = 30) -> None:
    since = (datetime.now(KST) - timedelta(days=days)).isoformat()
    rows = con.execute("SELECT id,tab,domain,src,kind,urgent,tags,title,summary,url,date "
                       "FROM articles WHERE date >= ? ORDER BY date DESC", (since,)).fetchall()
    keys = ["id", "tab", "domain", "src", "kind", "urgent", "tags", "title", "summary", "url", "date"]
    data = []
    for r in rows:
        d = dict(zip(keys, r))
        d["urgent"], d["tags"] = bool(d["urgent"]), json.loads(d["tags"])
        data.append(d)
    os.makedirs(os.path.dirname(EXPORT_PATH) or ".", exist_ok=True)
    with open(EXPORT_PATH, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)


def run_once() -> None:
    con = db()
    raw: list[dict] = []
    stats: dict[str, int] = {}

    for tab, kws in KEYWORDS.items():
        for kw in kws:
            got = collect_google_rss(kw, tab)
            stats[kw] = len(got)
            raw += got

    for name, fn in (("정부 부처(site:)", collect_gov_sites), ("법령 API", collect_law_api)):
        try:
            got = fn()
            stats[name] = len(got)
            raw += got
        except Exception as e:                       # 한 소스 실패가 전체를 멈추지 않게
            print(f"[warn] {name}: {e}")

    print("키워드별 수집 건수:", ", ".join(f"{k} {v}" for k, v in stats.items()))
    thin = [k for k, v in stats.items() if v < MIN_PER_QUERY and k in sum(KEYWORDS.values(), [])]
    if thin:
        print(f"[info] 결과가 적은 키워드 (QUERY_OVERRIDES로 검색식 보강 검토): {', '.join(thin)}")
    if not raw:
        print("[error] 수집된 기사가 없습니다. 네트워크 또는 구글 뉴스 응답을 확인하세요.")
        sys.exit(1)                                  # 워크플로를 실패로 표시해 알림을 받도록

    recent = [r[0] for r in con.execute(
        "SELECT norm FROM articles WHERE date >= ?", ((datetime.now(KST) - timedelta(days=7)).isoformat(),))]
    fresh = dedupe(raw, recent)
    items = [classify(a) for a in fresh]
    for a in items:
        a["summary"] = summarize(a)
    added = save(con, items)
    export(con)
    print(f"수집 {len(raw)}건, 중복 제거 후 {len(fresh)}건, 신규 저장 {added}건 → {EXPORT_PATH}")


if __name__ == "__main__":
    run_once()
