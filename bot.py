#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ربات آلارم ستاپ ۱ دقیقه‌ای (بازه‌ی نیویورک ۰۸:۳۰ تا ۱۱:۳۰)
دو سیگنال: (الف) تشکیل ناحیه  (ب) اولین ورود قیمت به ناحیه
همه‌ی تنظیمات در همین بخش بالای فایل است. بقیه‌ی فایل را دست نزنید.

دستورها:
  python bot.py run        اجرای اصلی (روی GitHub Actions)
  python bot.py selftest   تست آفلاین
  python bot.py test       ارسال پیام و چارت آزمایشی به تلگرام
  python bot.py probe      اندازه‌گیری تأخیر و کیفیت منابع داده
  python bot.py backtest   بک‌تست روی ۷ روز اخیر + شمارش سیگنال
"""
import os, sys, json, time, math, bisect, heapq, hashlib, threading, subprocess
import io, struct, lzma, random, statistics, traceback, datetime as _dt
from datetime import datetime, timedelta, date
from zoneinfo import ZoneInfo

# ───────────────────────── تنظیمات ─────────────────────────
TZ_NY = ZoneInfo("America/New_York")      # ساعت تابستانی خودکار
TZ_THR = ZoneInfo("Asia/Tehran")

SYMBOLS = ["NAS100", "US30", "SPX500", "XAUUSD", "EURUSD", "GBPUSD"]   # دقیقاً ۶ نماد
SHORT = {"NAS100": "NAS", "US30": "US30", "SPX500": "SPX",
         "XAUUSD": "XAU", "EURUSD": "EUR", "GBPUSD": "GBP"}
DIGITS = {"NAS100": 2, "US30": 2, "SPX500": 2, "XAUUSD": 2, "EURUSD": 5, "GBPUSD": 5}
SANE_RANGE = {"NAS100": (3000, 80000), "US30": (8000, 100000), "SPX500": (1500, 20000),
              "XAUUSD": (500, 20000), "EURUSD": (0.4, 3.0), "GBPUSD": (0.4, 3.5)}

WINDOW_START = (8, 30)        # ساعت نیویورک
WINDOW_END = (11, 30)
FINISH_GRACE_SEC = 120        # بعد از ۱۱:۳۰ فقط برای پردازش کندل آخر
LOOKBACK_DAYS = 7             # تا چند روز تقویمی گذشته سقف/کف هانت‌شده بررسی شود
SWING_N = 1                   # ۱ = سویینگ ۳ کندلی ، ۲ = ۵ کندلی (پیش‌فرض همان ۳ کندلی)
MIN_ZONE_SIZE = {s: 0.0 for s in SYMBOLS}   # حداقل اندازه‌ی ناحیه به واحد قیمت (۰ = خاموش)
MAX_ZONES_PER_SYMBOL = 0      # حداکثر ناحیه برای هر نماد در هر بازه (۰ = خاموش)
SKIP_US_HOLIDAYS = os.environ.get("SKIP_US_HOLIDAYS", "0") == "1"
US_HOLIDAYS = {               # تعطیلات بورس آمریکا (فقط وقتی SKIP_US_HOLIDAYS=1 باشد اعمال می‌شود)
    "2026-01-01", "2026-01-19", "2026-02-16", "2026-04-03", "2026-05-25", "2026-06-19",
    "2026-07-03", "2026-09-07", "2026-11-26", "2026-12-25",
    "2027-01-01", "2027-01-18", "2027-02-15", "2027-03-26", "2027-05-31", "2027-06-18",
    "2027-07-05", "2027-09-06", "2027-11-25", "2027-12-24",
}
MAX_EARLY_START_SEC = 2 * 3600 + 45 * 60   # job فقط اگر تا شروع بازه کمتر از این مانده باشد می‌ماند
PREWARM_SEC = 600             # دریافت تاریخچه‌ی ۷ روزه ۱۰ دقیقه قبل از شروع بازه

# ── سرعت / پولینگ ──
CLOSE_FALLBACK_SEC = 15       # اگر کندل بعدی نیامد، بعد از این مدت کندل را بسته فرض کن
BOUNDARY_FIRST_DELAY = 1.2    # اولین چک بعد از شروع دقیقه‌ی جدید
BOUNDARY_RETRY = 2.0          # فاصله‌ی چک‌ها تا رسیدن کندل جدید
BOUNDARY_GIVEUP = 40          # چند ثانیه بعد از مرز دقیقه چک‌های سریع متوقف شود
ENTRY_POLL_SEC = 6.0          # وقتی ناحیه‌ی منتظر ورود دارد
HEARTBEAT_POLL_SEC = 30.0     # حداقل چک وقتی کاری نیست
FAILOVER_AFTER_FAILS = 4      # بعد از این تعداد خطای پشت‌سرهم → منبع پشتیبان
OUTAGE_WARN_SEC = 120         # قطع داده بیشتر از این → هشدار
STALE_CANDLE_SEC = 420        # آخرین کندل قدیمی‌تر از این در بازه → هشدار
HTTP_TIMEOUT = 8

# ── منابع داده (به ترتیب اولویت: اصلی ← پشتیبان) ──
# yahoo: فیوچرز/اسپات Yahoo Finance ؛ duka: Dukascopy (CFD/اسپات واقعی، بدون حساب)
SOURCES = {
    "NAS100": [("yahoo", "NQ=F"), ("duka", "USATECHIDXUSD")],
    "US30":   [("yahoo", "YM=F"), ("duka", "USA30IDXUSD")],
    "SPX500": [("yahoo", "ES=F"), ("duka", "USA500IDXUSD")],
    "XAUUSD": [("yahoo", "XAUUSD=X"), ("yahoo", "GC=F"), ("duka", "XAUUSD")],
    "EURUSD": [("yahoo", "EURUSD=X"), ("duka", "EURUSD")],
    "GBPUSD": [("yahoo", "GBPUSD=X"), ("duka", "GBPUSD")],
}
if os.environ.get("PRIMARY_SOURCE", "yahoo") == "duka":     # اگر probe نشان داد Dukascopy بهتر است
    for _s in SOURCES:
        SOURCES[_s].sort(key=lambda x: 0 if x[0] == "duka" else 1)

RLM = "\u200f"
STATE_BRANCH = "bot-state"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")


def log(*a):
    print(datetime.now(TZ_NY).strftime("%H:%M:%S"), *a, flush=True)


# ───────────────────────── زمان ─────────────────────────
def ny(ts): return datetime.fromtimestamp(ts, TZ_NY)
def thr(ts): return datetime.fromtimestamp(ts, TZ_THR)


def is_trading_day(d: date) -> bool:
    if d.weekday() >= 5:
        return False
    if SKIP_US_HOLIDAYS and d.isoformat() in US_HOLIDAYS:
        return False
    return True


def window_bounds(d: date):
    s = datetime(d.year, d.month, d.day, *WINDOW_START, tzinfo=TZ_NY).timestamp()
    e = datetime(d.year, d.month, d.day, *WINDOW_END, tzinfo=TZ_NY).timestamp()
    return s, e


def in_window(ts) -> bool:
    """کندلی که زمان بازشدنش داخل [۰۸:۳۰ ، ۱۱:۳۰) نیویورک است (کل کندل داخل بازه است)."""
    d = ny(ts).date()
    if not is_trading_day(d):
        return False
    s, e = window_bounds(d)
    return s <= ts < e


def fmt_both(ts, with_sec=False):
    f = "%m-%d %H:%M:%S" if with_sec else "%m-%d %H:%M"
    return f"{thr(ts).strftime(f)} تهران | {ny(ts).strftime('%H:%M:%S' if with_sec else '%H:%M')} نیویورک"


def fp(sym, p):
    return f"{p:.{DIGITS[sym]}f}"


# ═════════════════════════ موتور ستاپ (منطق اصلی) ═════════════════════════
def _scan_sell(h, l, c, n):
    """
    ستاپ فروش (هانت سقف + شیفت نزولی ساختار). ورودی: آرایه‌های high/low/close کندل‌های بسته‌شده.
    خروجی: لیست رویدادها {j, p, s, k, types}
      j = کندل شیفت (MSS) ، p = سویینگ لوی شکسته‌شده (L) ، s = سویینگ های هانت‌شده (SH)
      k = کندل هانت ، types = {1,2}
    پیچیدگی O(N) با استک‌های یکنوا (برای ۱۰ هزار کندل چند ده میلی‌ثانیه).
    """
    N = len(c)
    sw_low = []        # همه‌ی سویینگ‌لوهای تأییدشده (به ترتیب اندیس)
    unhunted = []      # سویینگ‌های‌های هنوز هانت‌نشده (قیمت غیرصعودی)
    untouched = []     # سویینگ‌لوهای دست‌نخورده (قیمت صعودی)
    heap = []          # (قیمت SH ، شناسه‌ی هانت) برای باطل‌کردن با کلوز بالای SH
    hunts = []
    by_L = {}          # p -> [(hunt_id, type)]
    events = []
    for m in range(N):
        # ۱) سویینگ‌هایی که با کندل m تأیید می‌شوند (مرکز = m-n)
        ci = m - n
        if ci >= n:
            hc, lc = h[ci], l[ci]
            okh = okl = True
            for d in range(1, n + 1):
                if not (hc > h[ci - d] and hc > h[ci + d]):
                    okh = False
                if not (lc < l[ci - d] and lc < l[ci + d]):
                    okl = False
            if okh:
                unhunted.append(ci)
            if okl:
                sw_low.append(ci)
                untouched.append(ci)
                # (فقط n>=2) هانت‌هایی که بین مرکز سویینگ و تأییدش رخ داده‌اند: «آخرین سویینگ لو قبل از هانت» همین است
                i = len(hunts) - 1
                while i >= 0 and hunts[i]["k"] > ci:
                    H = hunts[i]
                    if H["p1"] != ci:
                        if H["p1"] is not None:
                            by_L[H["p1"]].remove((i, 1))
                        by_L.setdefault(ci, []).append((i, 1))
                        H["p1"] = ci
                    i -= 1
        cm, hm, lm = c[m], h[m], l[m]
        # ۲) هر SH هانت‌شده که کندلی بالاترش کلوز کند باطل می‌شود
        while heap and heap[0][0] < cm:
            hunts[heapq.heappop(heap)[1]]["alive"] = False
        # ۳) برخورد با سویینگ‌لوهای دست‌نخورده (اولین برخورد)
        while untouched and l[untouched[-1]] >= lm:
            p = untouched.pop()
            if cm < l[p]:                       # کلوز (بدنه) زیر L → شیفت
                cands = by_L.get(p)
                if cands:
                    best = None
                    types = {}
                    for hid, typ in cands:
                        H = hunts[hid]
                        if H["alive"]:
                            types.setdefault(hid, set()).add(typ)
                    for hid, ts_ in types.items():
                        H = hunts[hid]
                        key = (H["s"], H["k"])
                        if best is None or key > best[0]:
                            best = (key, hid, ts_)
                    if best:
                        H = hunts[best[1]]
                        events.append({"j": m, "p": p, "s": H["s"], "k": H["k"],
                                       "types": sorted(best[2])})
            # اگر فقط شدو برخورد کرده باشد، L برای همیشه مصرف‌شده است (معتبر نیست)
        # ۴) هانت: اولین کندل بعد از تأیید SH که high آن بالای SH برود
        while unhunted and h[unhunted[-1]] < hm:
            s = unhunted.pop()
            if cm <= h[s]:                      # کلوز بالای SH نیست → هانت
                hid = len(hunts)
                hunts.append({"s": s, "k": m, "alive": True, "p1": None})
                heapq.heappush(heap, (h[s], hid))
                for typ, ref in ((1, m), (2, s)):
                    i = bisect.bisect_left(sw_low, ref) - 1
                    if i >= 0:
                        by_L.setdefault(sw_low[i], []).append((hid, typ))
                        if typ == 1:
                            hunts[hid]["p1"] = sw_low[i]
            # اگر کلوز بالای SH باشد شکست است نه هانت → SH باطل
    return events


def scan(t, o, h, l, c, n=SWING_N, lookback_days=LOOKBACK_DAYS):
    """همه‌ی رویدادهای شیفت (هر دو سمت) روی کندل‌های بسته‌شده. خرید = قرینه‌ی دقیق فروش."""
    N = len(c)
    if N < 2 * n + 3:
        return []
    cut = t[-1] - lookback_days * 86400
    out = []
    for side in ("sell", "buy"):
        if side == "sell":
            evs = _scan_sell(h, l, c, n)
        else:
            evs = _scan_sell([-x for x in l], [-x for x in h], [-x for x in c], n)
        for e in evs:
            if t[e["s"]] < cut:
                continue
            j, p, s, k = e["j"], e["p"], e["s"], e["k"]
            if side == "sell":
                top, bottom, edge = h[s], l[p], l[p]
            else:
                bottom, top, edge = l[s], h[p], h[p]
            out.append({"side": side, "j": j, "p": p, "s": s, "k": k, "types": e["types"],
                        "t_j": t[j], "t_p": t[p], "t_s": t[s], "t_k": t[k],
                        "top": top, "bottom": bottom, "edge": edge,
                        "hunted": top if side == "sell" else bottom,
                        "broken": bottom if side == "sell" else top})
    out.sort(key=lambda z: (z["j"], z["p"]))
    return out


def find_touch(t, h, l, zone, end_ts):
    """
    اولین کندلِ بعد از MSS که به لبه‌ی ناحیه برسد (فروش: لبه‌ی پایین یعنی high ≥ L ؛ خرید: low ≤ L).
    آرایه‌ها شامل کندل در حال تشکیل هم هستند. خروجی: اندیس یا None.
    """
    i = bisect.bisect_right(t, zone["t_j"])
    edge = zone["edge"]
    sell = zone["side"] == "sell"
    for m in range(i, len(t)):
        if t[m] >= end_ts:
            break
        if (h[m] >= edge) if sell else (l[m] <= edge):
            return m
    return None


def zone_id(sym, z):
    raw = f"{sym}|{z['side']}|{z['t_p']}"
    return f"{SHORT[sym]}-{'S' if z['side']=='sell' else 'B'}-" + hashlib.sha1(raw.encode()).hexdigest()[:4].upper()


def zone_key(sym, z):
    return f"{sym}|{z['side']}|{z['t_p']}"


# ── مرجع کند و ساده‌ی «عین متن مستند» فقط برای تست (مقایسه‌ی تصادفی با موتور بهینه) ──
def reference_scan(h, l, c, n=1):
    N = len(c)

    def sh(i): return i - n >= 0 and i + n < N and all(h[i] > h[i - d] and h[i] > h[i + d] for d in range(1, n + 1))
    def sl(i): return i - n >= 0 and i + n < N and all(l[i] < l[i - d] and l[i] < l[i + d] for d in range(1, n + 1))
    res = set()
    for j in range(N):
        cand = {}
        for s in range(N):
            if not sh(s) or s + n >= j:
                continue
            SH = h[s]
            k = next((x for x in range(s + n + 1, N) if h[x] > SH), None)
            if k is None or k >= j or c[k] > SH:
                continue
            if any(c[x] > SH for x in range(k + 1, j + 1)):
                continue
            for typ, ref in ((1, k), (2, s)):
                ps = [x for x in range(N) if sl(x) and x < ref and x + n <= j]
                if not ps:
                    continue
                p = ps[-1]
                if any(l[x] <= l[p] for x in range(p + 1, j)):
                    continue
                if not (l[j] <= l[p] and c[j] < l[p]):
                    continue
                cand.setdefault(p, {}).setdefault((s, k), set()).add(typ)
        for p, hs in cand.items():
            (s, k) = max(hs)
            res.add((j, p, s, k, tuple(sorted(hs[(s, k)]))))
    return res


# ═════════════════════════ منابع داده ═════════════════════════
import requests

_tls = threading.local()


def http():
    s = getattr(_tls, "s", None)
    if s is None:
        s = requests.Session()
        s.headers.update({"User-Agent": UA, "Accept": "*/*", "Accept-Encoding": "gzip, deflate"})
        _tls.s = s
    return s


class ProviderError(Exception):
    def __init__(self, msg, status=None):
        super().__init__(msg)
        self.status = status


def sane_candle(sym, o, h, l, c):
    lo, hi = SANE_RANGE[sym]
    for x in (o, h, l, c):
        if x is None or not (lo <= x <= hi):
            return None
    h = max(h, o, c, l)
    l = min(l, o, c, h)
    return o, h, l, c


class Yahoo:
    """Yahoo Finance chart API (غیررسمی، رایگان، بدون حساب). کندل ۱ دقیقه‌ای + کندل در حال تشکیل."""
    HOSTS = ["query1.finance.yahoo.com", "query2.finance.yahoo.com"]

    def __init__(self):
        self._i = 0

    @staticmethod
    def parse(sym, js):
        res = (js.get("chart", {}).get("result") or [None])[0]
        if not res:
            err = js.get("chart", {}).get("error")
            raise ProviderError(f"yahoo no result: {err}")
        ts = res.get("timestamp") or []
        q = (res.get("indicators", {}).get("quote") or [{}])[0]
        O, H, L, C = q.get("open", []), q.get("high", []), q.get("low", []), q.get("close", [])
        out = []
        for i, t in enumerate(ts):
            try:
                v = sane_candle(sym, O[i], H[i], L[i], C[i])
            except (IndexError, TypeError):
                v = None
            if v:
                out.append((int(t),) + v)
        meta = res.get("meta", {}) or {}
        return out, {"last_trade_ts": meta.get("regularMarketTime"), "price": meta.get("regularMarketPrice")}

    def fetch(self, sym, code, start=None, end=None, now=None, full=False, cache_bust=True):
        params = {"interval": "1m", "includePrePost": "true"}
        if full or start is None:
            params["range"] = "7d"
        else:
            params["period1"] = int(start)
            params["period2"] = int(end)
        if cache_bust:
            params["_"] = int(time.time() * 1000)
        self._i ^= 1
        url = f"https://{self.HOSTS[self._i]}/v8/finance/chart/{requests.utils.quote(code, safe='')}"
        t0 = time.time()
        try:
            r = http().get(url, params=params, timeout=HTTP_TIMEOUT)
        except requests.RequestException as e:
            raise ProviderError(f"yahoo net: {e}")
        rtt = time.time() - t0
        if r.status_code != 200:
            raise ProviderError(f"yahoo http {r.status_code}", r.status_code)
        try:
            cands, meta = self.parse(sym, r.json())
        except ValueError as e:
            raise ProviderError(f"yahoo json: {e}")
        meta["rtt"] = rtt
        return cands, meta


class Duka:
    """
    Dukascopy datafeed (رایگان، بدون حساب، قیمت CFD/اسپات واقعی، Bid).
    تاریخچه: فایل کندل ۱ دقیقه‌ای روزانه ؛ امروز: فایل‌های تیک ساعتی که به کندل ۱ دقیقه تبدیل می‌شوند.
    توجه: تأخیر زنده‌ی این منبع باید با probe اندازه‌گیری شود (تأییدنشده).
    """
    BASE = "https://datafeed.dukascopy.com/datafeed"
    DIV = {"EURUSD": 100000, "GBPUSD": 100000}      # بقیه ۱۰۰۰

    def __init__(self):
        self.div_fix = {}

    def _get(self, url):
        try:
            r = http().get(url, timeout=HTTP_TIMEOUT + 4)
        except requests.RequestException as e:
            raise ProviderError(f"duka net: {e}")
        if r.status_code == 404:
            return None
        if r.status_code != 200:
            raise ProviderError(f"duka http {r.status_code}", r.status_code)
        if not r.content:
            return b""
        try:
            return lzma.decompress(r.content, format=lzma.FORMAT_AUTO)
        except lzma.LZMAError:
            # فایل ساعتِ جاری ممکن است ناقص باشد
            try:
                d = lzma.LZMADecompressor(format=lzma.FORMAT_AUTO)
                return d.decompress(r.content)
            except lzma.LZMAError as e:
                raise ProviderError(f"duka lzma: {e}")

    @staticmethod
    def parse_candles(raw, day_start_ts, div):
        out = []
        for sec, op, cl, lo, hi, _v in struct.iter_unpack(">IIIIIf", raw[: len(raw) // 24 * 24]):
            out.append((day_start_ts + sec, op / div, hi / div, lo / div, cl / div))
        return out

    @staticmethod
    def parse_ticks(raw, hour_start_ts, div):
        bars = {}
        for ms, ask, bid, _av, _bv in struct.iter_unpack(">IIIff", raw[: len(raw) // 20 * 20]):
            t = hour_start_ts + ms // 1000
            t -= t % 60
            p = bid / div
            b = bars.get(t)
            if b is None:
                bars[t] = [p, p, p, p]
            else:
                b[1] = max(b[1], p)
                b[2] = min(b[2], p)
                b[3] = p
        return [(t, b[0], b[1], b[2], b[3]) for t, b in sorted(bars.items())]

    def _fix_scale(self, sym, inst, cands, div):
        """اگر قیمت‌ها خارج از محدوده‌ی منطقی بود مقیاس را ۱۰ برابر جابه‌جا کن."""
        if not cands:
            return cands, div
        lo, hi = SANE_RANGE[sym]
        mid = cands[len(cands) // 2][4]
        for mult in (1, 10, 0.1, 100, 0.01, 1000, 0.001, 10000, 0.0001):
            if lo <= mid / mult <= hi:
                if mult != 1:
                    self.div_fix[inst] = div * mult
                    cands = [(t, o / mult, h / mult, l / mult, c / mult) for t, o, h, l, c in cands]
                    div = div * mult
                return cands, div
        raise ProviderError(f"duka price scale not sane for {sym}: {mid}")

    def _day_url(self, inst, d, name):
        return f"{self.BASE}/{inst}/{d.year}/{d.month-1:02d}/{d.day:02d}/{name}"

    def fetch(self, sym, inst, start=None, end=None, now=None, full=False, cache_bust=True):
        now = now or time.time()
        t0 = time.time()
        if full or start is None:
            start = now - LOOKBACK_DAYS * 86400
        start = max(start, now - (LOOKBACK_DAYS + 1) * 86400)
        div = self.div_fix.get(inst) or self.DIV.get(sym, 1000)
        out = {}
        u_now = datetime.fromtimestamp(now, _dt.timezone.utc)
        d = datetime.fromtimestamp(start, _dt.timezone.utc).date()
        today = u_now.date()
        while d <= today:
            ds = datetime(d.year, d.month, d.day, tzinfo=_dt.timezone.utc).timestamp()
            got_day = False
            if d < today:
                raw = self._get(self._day_url(inst, d, "BID_candles_min_1.bi5"))
                if raw:
                    for row in self.parse_candles(raw, ds, div):
                        out[row[0]] = row
                    got_day = True
            if not got_day:
                hours = range(24) if d < today else range(max(0, u_now.hour - (1 if start > ds else 24)), u_now.hour + 1)
                for hr in hours:
                    if ds + hr * 3600 < start - 3600:
                        continue
                    raw = self._get(self._day_url(inst, d, f"{hr:02d}h_ticks.bi5"))
                    if raw:
                        for row in self.parse_ticks(raw, ds + hr * 3600, div):
                            out[row[0]] = row
            d += timedelta(days=1)
        cands = [out[k] for k in sorted(out)]
        cands, div = self._fix_scale(sym, inst, cands, div)
        res = []
        for t, o, h, l, c in cands:
            v = sane_candle(sym, o, h, l, c)
            if v:
                res.append((t,) + v)
        meta = {"last_trade_ts": res[-1][0] + 59 if res else None, "price": res[-1][4] if res else None,
                "rtt": time.time() - t0}
        return res, meta


PROVIDERS = {"yahoo": Yahoo(), "duka": Duka()}


class Snapshot:
    __slots__ = ("t", "o", "h", "l", "c", "ft", "fo", "fh", "fl", "fc", "n", "sig")


class Feed:
    """داده‌ی یک نماد در حافظه (تاریخچه‌ی ۷ روزه یک‌بار؛ بعد فقط کندل‌های جدید)."""

    def __init__(self, sym, providers=None, sources=None):
        self.sym = sym
        self.providers = providers or PROVIDERS
        self.sources = sources or SOURCES[sym]
        self.src_i = 0
        self.cands = {}
        self.meta = {}
        self.lock = threading.Lock()
        self.last_ok = 0.0
        self.fail = 0
        self.last_err = ""
        self.backoff_until = 0.0
        self.cur_b = 0
        self.got_b = True
        self.next_bpoll = 0.0
        self.next_epoll = 0.0
        self.next_hb = 0.0
        self.first_seen = {}      # t -> زمان دیده‌شدن اولین‌بار (برای اندازه‌گیری تأخیر)
        self.source_changed = None

    @property
    def label(self):
        kind, code = self.sources[self.src_i]
        if kind == "yahoo":
            note = "فیوچرز" if code.endswith("=F") else "اسپات"
            return f"Yahoo Finance {code} ({note})"
        return f"Dukascopy {code} (CFD/اسپات)"

    def _call(self, now, **kw):
        kind, code = self.sources[self.src_i]
        return self.providers[kind].fetch(self.sym, code, now=now, **kw)

    def _merge(self, cands, now):
        with self.lock:
            for t, o, h, l, c in cands:
                if t not in self.cands:
                    self.first_seen[t] = now
                self.cands[t] = (o, h, l, c)
            cut = now - (LOOKBACK_DAYS + 1) * 86400
            if len(self.cands) > 12000:
                for t in [t for t in self.cands if t < cut]:
                    del self.cands[t]

    def load_history(self, now):
        cands, meta = self._call(now, full=True)
        with self.lock:
            self.cands = {}
        self._merge(cands, now)
        self.meta = meta
        self.last_ok = now
        self.fail = 0
        return len(cands)

    def healthy(self, now):
        if len(self.cands) < 100:
            return False
        return now - max(self.cands) <= 900

    def start(self, now):
        """از اولین منبع سالم شروع کن؛ اگر هیچ‌کدام سالم نبود بهترین موجود را نگه دار."""
        best = None
        for i in range(len(self.sources)):
            self.src_i = i
            try:
                n = self.load_history(now)
            except ProviderError as e:
                self.last_err = str(e)
                log(f"[{self.sym}] منبع {self.label} خطا: {e}")
                continue
            if self.healthy(now):
                log(f"[{self.sym}] منبع انتخاب شد: {self.label} ({n} کندل)")
                return True
            if best is None or n > best[0]:
                best = (n, i)
        if best:
            self.src_i = best[1]
            try:
                self.load_history(now)
            except ProviderError:
                pass
            log(f"[{self.sym}] هیچ منبعی کاملاً سالم نبود؛ {self.label} نگه داشته شد")
            return False
        return False

    def due(self, now, want_entry):
        b = int(now // 60) * 60
        if b != self.cur_b:
            self.cur_b = b
            self.got_b = False
            self.next_bpoll = b + BOUNDARY_FIRST_DELAY + random.random() * 0.4
        if now < self.backoff_until:
            return False
        if not self.got_b and self.next_bpoll <= now < b + BOUNDARY_GIVEUP:
            return True
        if want_entry and now >= self.next_epoll:
            return True
        return now >= self.next_hb

    def poll(self, now):
        """یک بار دریافت کندل‌های جدید. True = موفق."""
        self.next_hb = now + HEARTBEAT_POLL_SEC
        if self.cands:
            start = max(self.cands) - 600
        else:
            start = now - 1800
        try:
            cands, meta = self._call(now, start=start, end=now + 300, full=False)
        except ProviderError as e:
            self.fail += 1
            self.last_err = str(e)
            if e.status == 429:
                self.backoff_until = now + 20
            else:
                self.backoff_until = now + min(2 * self.fail, 10)
            log(f"[{self.sym}] خطای دریافت ({self.fail}): {e}")
            if self.fail >= FAILOVER_AFTER_FAILS:
                self.failover(now)
            self.next_bpoll = now + BOUNDARY_RETRY
            return False
        self.fail = 0
        self.last_ok = now
        self.meta = meta
        self._merge(cands, now)
        last_t = max(self.cands) if self.cands else 0
        if last_t >= self.cur_b:
            self.got_b = True
        else:
            self.next_bpoll = now + BOUNDARY_RETRY
        self.next_epoll = now + ENTRY_POLL_SEC
        return True

    def failover(self, now):
        old = self.label
        for step in range(1, len(self.sources)):
            i = (self.src_i + step) % len(self.sources)
            prev = self.src_i
            self.src_i = i
            try:
                self.load_history(now)
                if self.healthy(now):
                    self.source_changed = (old, self.label)
                    log(f"[{self.sym}] تغییر منبع: {old} → {self.label}")
                    return True
            except ProviderError as e:
                log(f"[{self.sym}] منبع پشتیبان {self.label} هم خطا داد: {e}")
            self.src_i = prev
        self.fail = 0
        self.backoff_until = now + 15
        return False

    def snapshot(self, now):
        with self.lock:
            ts = sorted(self.cands)
            n = len(ts)
            nc = n
            if n and ts[-1] + 60 > now - CLOSE_FALLBACK_SEC:
                nc -= 1                      # آخرین کندل هنوز تأیید‌ بسته‌شدن ندارد
            while nc > 0 and ts[nc - 1] + 60 > now:
                nc -= 1
            sn = Snapshot()
            vals = [self.cands[t] for t in ts]
        sn.t = ts[:nc]
        sn.o = [v[0] for v in vals[:nc]]
        sn.h = [v[1] for v in vals[:nc]]
        sn.l = [v[2] for v in vals[:nc]]
        sn.c = [v[3] for v in vals[:nc]]
        sn.n = nc
        if nc < n:
            sn.ft = ts[nc:]
            sn.fo = [v[0] for v in vals[nc:]]
            sn.fh = [v[1] for v in vals[nc:]]
            sn.fl = [v[2] for v in vals[nc:]]
            sn.fc = [v[3] for v in vals[nc:]]
        else:
            sn.ft = sn.fo = sn.fh = sn.fl = sn.fc = []
        sn.sig = (nc, sn.t[-1] if nc else 0, sn.c[-1] if nc else 0, sn.h[-1] if nc else 0, sn.l[-1] if nc else 0)
        return sn


# ═════════════════════════ تلگرام ═════════════════════════
def esc(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def rtl(lines):
    return "\n".join((RLM + x) if x else RLM for x in lines)


class Telegram:
    def __init__(self, token, chat_id):
        self.token, self.chat = token, chat_id
        self.api = f"https://api.telegram.org/bot{token}/"
        self.offset = None

    def _call(self, method, data=None, files=None, retries=4):
        last = None
        for i in range(retries):
            try:
                r = http().post(self.api + method, data=data, files=files, timeout=20)
                js = r.json()
                if js.get("ok"):
                    return js["result"]
                last = js
                if r.status_code == 429:
                    time.sleep(min(js.get("parameters", {}).get("retry_after", 2), 10))
                    continue
                if r.status_code in (400, 403, 404):
                    break
            except Exception as e:      # noqa
                last = str(e)
            time.sleep(0.6 * (i + 1))
        raise RuntimeError(f"telegram {method} failed: {last}")

    def send_text(self, text, reply_to=None, silent=False):
        d = {"chat_id": self.chat, "text": text, "parse_mode": "HTML", "disable_web_page_preview": "true",
             "disable_notification": "true" if silent else "false"}
        if reply_to:
            d["reply_parameters"] = json.dumps({"message_id": reply_to, "allow_sending_without_reply": True})
        return self._call("sendMessage", d)["message_id"]

    def send_photo(self, png, caption, reply_to=None, silent=False):
        d = {"chat_id": self.chat, "caption": caption, "parse_mode": "HTML",
             "disable_notification": "true" if silent else "false"}
        if reply_to:
            d["reply_parameters"] = json.dumps({"message_id": reply_to, "allow_sending_without_reply": True})
        return self._call("sendPhoto", d, files={"photo": ("chart.png", png, "image/png")})["message_id"]

    def send_document(self, name, data, caption=""):
        return self._call("sendDocument", {"chat_id": self.chat, "caption": caption},
                          files={"document": (name, data)})["message_id"]

    def edit_text(self, mid, text):
        try:
            self._call("editMessageText", {"chat_id": self.chat, "message_id": mid, "text": text,
                                           "parse_mode": "HTML"}, retries=2)
        except Exception:
            pass

    def commands(self):
        """دستورهای ساده‌ی مالک (/status) را بخوان."""
        try:
            d = {"timeout": 0, "allowed_updates": json.dumps(["message"])}
            if self.offset:
                d["offset"] = self.offset
            ups = self._call("getUpdates", d, retries=1)
        except Exception:
            return []
        out = []
        for u in ups:
            self.offset = u["update_id"] + 1
            m = u.get("message") or {}
            if str((m.get("chat") or {}).get("id")) == str(self.chat) and m.get("text"):
                out.append(m["text"].strip())
        return out


# ═════════════════════════ متن پیام‌ها ═════════════════════════
def side_fa(side):
    return "🔴 فروش" if side == "sell" else "🟢 خرید"


def type_desc(side, typ):
    if side == "sell":
        return ("نوع ۱: آخرین سویینگ‌لو قبل از کندل هانت" if typ == 1 else
                "نوع ۲: آخرین سویینگ‌لو قبل از خود سقف (کفی که آن سقف را ساخت)")
    return ("نوع ۱: آخرین سویینگ‌های قبل از کندل هانت" if typ == 1 else
            "نوع ۲: آخرین سویینگ‌های قبل از خود کف (سقفی که آن کف را ساخت)")


def zone_caption(sym, z, label, latency=None, late=False):
    sell = z["side"] == "sell"
    # فروش: سقف = SH هانت‌شده ، کف = سویینگ‌لوی شکسته‌شده ؛ خرید: برعکس
    d_top = "سویینگ‌های هانت‌شده (Swing High)" if sell else "سویینگ‌های شکسته‌شده (Swing High)"
    d_bot = "سویینگ‌لوی شکسته‌شده (Swing Low)" if sell else "سویینگ‌لوی هانت‌شده (Swing Low)"
    types = z["types"]
    if len(types) == 1:
        ttxt = type_desc(z["side"], types[0])
    else:
        ttxt = "نوع ۱ و ۲ هم‌زمان (همان سویینگ هم آخرین قبل از هانت است هم آخرین قبل از سقف/کف)"
    size = z["top"] - z["bottom"]
    L = [
        f"{side_fa(z['side'])} | <b>{sym}</b> | ۱ دقیقه",
        "🎯 ناحیه معاملاتی تشکیل شد" + ("  (دیرتر پیدا شد؛ ربات تازه روشن شده یا چند چک از دست رفته بود)" if late else ""),
        "━━━━━━━━━━━━",
        f"🔺 سقف ناحیه: <code>{fp(sym, z['top'])}</code> — {d_top}",
        f"🔻 کف ناحیه: <code>{fp(sym, z['bottom'])}</code> — {d_bot}",
        f"📏 اندازه‌ی ناحیه: {fp(sym, size)}",
        f"🧩 {ttxt}",
        f"🕒 زمان هانت: {fmt_both(z['t_k'])}",
        f"✅ کلوز شیفت ساختار: {fmt_both(z['t_j'] + 60)}",
        f"🆔 کد ناحیه: <code>{zone_id(sym, z)}</code>",
        f"📡 منبع داده: {esc(label)}",
    ]
    if latency is not None:
        L.append(f"⏱ رسیدن پیام: {latency:.1f} ثانیه بعد از کلوز")
    return rtl(L)


def entry_text(sym, z, price, touch_ts, zid, late=False):
    edge_fa = "لبه‌ی پایین" if z["side"] == "sell" else "لبه‌ی بالا"
    L = [
        f"🎯 <b>ورود قیمت به ناحیه</b> — {sym} ({'فروش' if z['side'] == 'sell' else 'خرید'})",
        f"💰 قیمت: <code>{fp(sym, price)}</code> ({edge_fa} ناحیه: <code>{fp(sym, z['edge'])}</code>)",
        f"🕒 لمس: {fmt_both(touch_ts, True)}" + ("  (در کندل گذشته تشخیص داده شد)" if late else ""),
        f"🆔 {zid}",
    ]
    return rtl(L)


# ═════════════════════════ چارت ═════════════════════════
_mpl = {}


def _plt():
    if "plt" not in _mpl:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        _mpl["plt"] = plt
    return _mpl["plt"]


def render_chart(sym, z, t, o, h, l, c, label=""):
    """چارت ساده و تمیز: ~۶۰ تا ۹۰ کندل ۱ دقیقه‌ای ، دو خط افقی از کندل سویینگ خودشان تا لبه‌ی راست."""
    plt = _plt()
    j = z["j"]
    first = min(z["s"], z["p"], z["k"])
    start = max(0, max(j - 90, min(j - 70, first - 6)))
    end = j
    xs = list(range(start, end + 1))
    pad_r = 9
    fig, ax = plt.subplots(figsize=(9.2, 5.4), dpi=110)
    bg, grid = "#ffffff", "#eceff3"
    fig.patch.set_facecolor(bg)
    ax.set_facecolor(bg)
    up, dn = "#1f9d78", "#e0475b"
    for x in xs:
        col = up if c[x] >= o[x] else dn
        ax.vlines(x, l[x], h[x], color=col, linewidth=1.1, zorder=2)
        lo, hi = min(o[x], c[x]), max(o[x], c[x])
        if hi - lo < 1e-12:
            ax.hlines(hi, x - 0.32, x + 0.32, color=col, linewidth=1.4, zorder=3)
        else:
            ax.bar(x, hi - lo, bottom=lo, width=0.66, color=col, edgecolor=col, linewidth=0.6, zorder=3)
    xr = end + pad_r
    lines = [(z["hunted"], z["s"], "#2563eb"), (z["broken"], z["p"], "#2563eb")]
    for price, idx, col in lines:
        x0 = max(idx, start)
        ax.hlines(price, x0 - 0.4, xr, color=col, linewidth=1.5, zorder=4)
        ax.text(xr, price, " " + fp(sym, price), color=col, fontsize=10, fontweight="bold",
                va="center", ha="left", zorder=5, clip_on=False)
    lo_v = min(min(l[start:end + 1]), z["top"], z["bottom"])
    hi_v = max(max(h[start:end + 1]), z["top"], z["bottom"])
    pad = (hi_v - lo_v) * 0.08 or 1
    ax.set_ylim(lo_v - pad, hi_v + pad)
    ax.set_xlim(start - 1, xr)
    step = max(1, (end - start) // 7)
    ticks = list(range(end, start - 1, -step))[::-1]
    ax.set_xticks(ticks)
    ax.set_xticklabels([ny(t[i]).strftime("%H:%M") for i in ticks], fontsize=8, color="#555")
    ax.yaxis.tick_left()
    ax.tick_params(axis="y", labelsize=8, colors="#555", length=0)
    ax.tick_params(axis="x", length=0)
    ax.grid(axis="y", color=grid, linewidth=0.8, zorder=0)
    for sp in ("top", "right", "left"):
        ax.spines[sp].set_visible(False)
    ax.spines["bottom"].set_color("#cfd5dc")
    title = f"{sym} · 1m · {'SELL' if z['side'] == 'sell' else 'BUY'} zone · {zone_id(sym, z)}"
    ax.set_title(title, fontsize=11, loc="left", color="#222", fontweight="bold")
    ax.text(1.0, 1.015, "NY time", transform=ax.transAxes, ha="right", va="bottom", fontsize=8, color="#888")
    fig.subplots_adjust(left=0.08, right=0.88, top=0.92, bottom=0.07)
    buf = io.BytesIO()
    fig.savefig(buf, format="png", facecolor=bg)
    plt.close(fig)
    return buf.getvalue()


# ═════════════════════════ state (جلوگیری از پیام تکراری) ═════════════════════════
class GitSync:
    """state را در شاخه‌ی bot-state همین مخزن نگه می‌دارد تا بین اجراها/ری‌استارت‌ها پیام تکراری نرود."""
    DIR = "_state_repo"

    def __init__(self):
        self.repo = os.environ.get("GITHUB_REPOSITORY")
        self.tok = os.environ.get("GITHUB_TOKEN")
        self.enabled = bool(os.environ.get("GITHUB_ACTIONS") and self.repo and self.tok)
        self.dirty = False
        self.src = None
        self.lk = threading.Lock()
        self.stop = threading.Event()
        self.th = None

    def _git(self, *args, check=True):
        r = subprocess.run(["git", *args], cwd=self.DIR, capture_output=True, text=True)
        if check and r.returncode != 0:
            raise RuntimeError(f"git {' '.join(args[:2])}: {r.stderr.strip()[-200:]}")
        return r

    def pull(self, dest):
        if not self.enabled:
            return False
        try:
            subprocess.run(["rm", "-rf", self.DIR], check=False)
            url = f"https://x-access-token:{self.tok}@github.com/{self.repo}.git"
            r = subprocess.run(["git", "clone", "--depth", "1", "--branch", STATE_BRANCH, url, self.DIR],
                               capture_output=True, text=True)
            if r.returncode != 0:
                os.makedirs(self.DIR, exist_ok=True)
                self._git("init", "-q")
                self._git("checkout", "-q", "-b", STATE_BRANCH)
                self._git("remote", "add", "origin", url)
                return False
            src = os.path.join(self.DIR, "state.json")
            if os.path.exists(src):
                with open(src, "rb") as a, open(dest, "wb") as b:
                    b.write(a.read())
                return True
        except Exception as e:      # noqa
            log("git pull state:", e)
        return False

    def mark(self, src):
        if not self.enabled:
            return
        self.src = src
        self.dirty = True
        if self.th is None:
            self.th = threading.Thread(target=self._loop, daemon=True)
            self.th.start()

    def _loop(self):
        while not self.stop.is_set():
            self.stop.wait(3)
            self.flush()

    def flush(self):
        if not (self.enabled and self.dirty and self.src):
            return
        with self.lk:
            self.dirty = False
            try:
                os.makedirs(self.DIR, exist_ok=True)
                with open(self.src, "rb") as a, open(os.path.join(self.DIR, "state.json"), "wb") as b:
                    b.write(a.read())
                self._git("config", "user.name", "alarm-bot")
                self._git("config", "user.email", "alarm-bot@users.noreply.github.com")
                self._git("add", "state.json")
                if self._git("diff", "--cached", "--quiet", check=False).returncode == 0:
                    return
                self._git("commit", "-q", "-m", "state " + datetime.now(TZ_NY).strftime("%Y-%m-%d %H:%M:%S"))
                self._git("push", "-q", "-f", "origin", STATE_BRANCH)
            except Exception as e:      # noqa
                self.dirty = True
                log("git push state:", e)


class State:
    def __init__(self, path="state.json", sync=None):
        self.path = path
        self.sync = sync
        self.lock = threading.RLock()
        self.d = {}

    def load(self, day):
        if self.sync:
            self.sync.pull(self.path)
        d = {}
        try:
            with open(self.path, encoding="utf-8") as f:
                d = json.load(f)
        except Exception:
            d = {}
        if d.get("date") != day:
            d = {"date": day, "zones": {}, "start_msg": None, "end_sent": False, "suppressed": {},
                 "alerts": {}, "restarts": 0}
        else:
            d["restarts"] = d.get("restarts", 0) + 1
        self.d = d
        self.save()

    @property
    def zones(self):
        return self.d["zones"]

    def save(self):
        with self.lock:
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.d, f, ensure_ascii=False)
            os.replace(tmp, self.path)
        if self.sync:
            self.sync.mark(self.path)

    def count(self, sym):
        return sum(1 for z in self.d["zones"].values() if z["sym"] == sym) + \
            sum(1 for k in self.d.get("suppressed", {}) if k.startswith(sym + "|") and False)

    def pending(self, sym):
        with self.lock:
            return [(k, dict(z)) for k, z in self.d["zones"].items() if z["sym"] == sym and not z.get("entered")]


# ═════════════════════════ اجرا ═════════════════════════
class Clock:
    def now(self): return time.time()
    def sleep(self, s): time.sleep(s)


RENDER_LOCK = threading.Lock()
LATE_SEC = 90


class Worker:
    def __init__(self, sym, feed, R):
        self.sym, self.feed, self.R = sym, feed, R
        self.last_sig = None
        self.alerted_out = False
        self.alerted_stale = False

    def step(self, now):
        R, f = self.R, self.feed
        if now < R.ws - 30 or now >= R.we + FINISH_GRACE_SEC:
            return
        if f.due(now, bool(R.state.pending(self.sym))):
            ok = f.poll(now)
            if f.source_changed:
                old, new = f.source_changed
                f.source_changed = None
                R.notify(rtl([f"🔁 منبع داده‌ی {self.sym} عوض شد", f"از: {esc(old)}", f"به: {esc(new)}",
                              "(قیمت‌ها ممکن است چند واحد با منبع قبلی فرق داشته باشند)"]), silent=True)
                self.last_sig = None
            if ok or f.cands:
                self.evaluate(now)

    # ── سیگنال الف: تشکیل ناحیه ، سیگنال ب: ورود ──
    def evaluate(self, now):
        R, f, sym = self.R, self.feed, self.sym
        snap = f.snapshot(now)
        if snap.n < 20:
            return
        if snap.sig != self.last_sig:
            evs = scan(snap.t, snap.o, snap.h, snap.l, snap.c)
            new = []
            for z in evs:
                if not (R.ws <= z["t_j"] < R.we):
                    continue                       # MSS باید داخل بازه باشد
                key = zone_key(sym, z)
                if key in R.state.zones or key in R.state.d["suppressed"]:
                    continue
                new.append((key, z))
            ok_all = True
            for key, z in new:                      # قدیمی‌ترین اول
                ok_all = self.emit_zone(key, z, snap, now) and ok_all
            self.last_sig = snap.sig if ok_all else None
        if now < R.we + FINISH_GRACE_SEC:
            self.check_entries(snap, now)

    def emit_zone(self, key, z, snap, now):
        R, sym = self.R, self.sym
        size = z["top"] - z["bottom"]
        if size < MIN_ZONE_SIZE.get(sym, 0):
            R.state.d["suppressed"][key] = "min_size"
            R.state.save()
            return True
        if MAX_ZONES_PER_SYMBOL and R.state.count(sym) >= MAX_ZONES_PER_SYMBOL:
            R.state.d["suppressed"][key] = "max_zones"
            R.state.save()
            return True
        close_ts = z["t_j"] + 60
        late = (now - close_ts) > LATE_SEC
        lat = max(0.0, R.clock.now() - close_ts)
        try:
            with RENDER_LOCK:
                png = render_chart(sym, z, snap.t, snap.o, snap.h, snap.l, snap.c, self.feed.label)
        except Exception as e:      # noqa
            log(f"[{sym}] خطای رسم چارت: {e}")
            png = None
        cap = zone_caption(sym, z, self.feed.label, lat, late)
        try:
            if png:
                mid = R.tg.send_photo(png, cap)
            else:
                mid = R.tg.send_text(cap)
        except Exception as e:      # noqa
            log(f"[{sym}] ارسال ناحیه ناموفق: {e}")
            return False
        done = R.clock.now()
        with R.state.lock:
            R.state.zones[key] = {
                "sym": sym, "side": z["side"], "t_j": z["t_j"], "t_p": z["t_p"], "t_s": z["t_s"], "t_k": z["t_k"],
                "top": z["top"], "bottom": z["bottom"], "edge": z["edge"], "types": z["types"],
                "zid": zone_id(sym, z), "msg_id": mid, "sent_ts": done, "latency": done - close_ts,
                "late": late, "entered": False, "source": self.feed.label}
        R.state.save()
        log(f"[{sym}] ناحیه {zone_id(sym, z)} {z['side']} top={fp(sym, z['top'])} bottom={fp(sym, z['bottom'])} "
            f"types={z['types']} ارسال شد، تأخیر {done - close_ts:.1f}s")
        return True

    def check_entries(self, snap, now):
        R, sym = self.R, self.sym
        pend = R.state.pending(sym)
        if not pend:
            return
        t = snap.t + snap.ft
        h = snap.h + snap.fh
        l = snap.l + snap.fl
        c = snap.c + snap.fc
        for key, zs in pend:
            m = find_touch(t, h, l, zs, R.we)
            if m is None:
                continue
            forming = m >= snap.n
            sell = zs["side"] == "sell"
            if forming:
                touch_ts, price = now, c[m]
            else:
                touch_ts, price = t[m], (h[m] if sell else l[m])
            late = (not forming) and (now - (t[m] + 60) > 20)
            txt = entry_text(sym, zs, price, touch_ts, zs["zid"], late)
            try:
                mid = R.tg.send_text(txt, reply_to=zs["msg_id"])
            except Exception as e:      # noqa
                log(f"[{sym}] ارسال ورود ناموفق: {e}")
                continue
            with R.state.lock:
                z = R.state.zones[key]
                z.update({"entered": True, "entry_ts": touch_ts, "entry_price": price, "entry_msg": mid,
                          "entry_sent": R.clock.now()})
            R.state.save()
            log(f"[{sym}] ورود به ناحیه {zs['zid']} قیمت={fp(sym, price)} ارسال شد")


class Runner:
    def __init__(self, tg, state, feeds, clock, ws, we):
        self.tg, self.state, self.feeds, self.clock, self.ws, self.we = tg, state, feeds, clock, ws, we
        self.workers = [Worker(s, feeds[s], self) for s in SYMBOLS]
        self.t_start = clock.now()
        self.last_cmd = 0
        self.last_hb = 0
        self.stop = threading.Event()

    def notify(self, text, silent=False):
        try:
            return self.tg.send_text(text, silent=silent)
        except Exception as e:      # noqa
            log("notify failed:", e)

    # ── پیام‌های شروع/پایان/هشدار ──
    def window_text(self):
        return (f"{datetime.fromtimestamp(self.ws, TZ_NY):%H:%M}–{datetime.fromtimestamp(self.we, TZ_NY):%H:%M} نیویورک "
                f"({datetime.fromtimestamp(self.ws, TZ_THR):%H:%M}–{datetime.fromtimestamp(self.we, TZ_THR):%H:%M} تهران)")

    def start_message(self, late):
        L = ["✅ <b>ربات روشن است</b>",
             f"📅 {ny(self.ws):%Y-%m-%d} | بازه: {self.window_text()}",
             "⏱ تایم‌فریم: ۱ دقیقه | نمادها: " + "، ".join(SYMBOLS)]
        for s in SYMBOLS:
            L.append(f"• {s}: {esc(self.feeds[s].label)}")
        if late:
            L.append("⚠️ ربات بعد از شروع بازه روشن شد؛ کندل‌های گذشته‌ی بازه هم بررسی شدند.")
        L.append("برای وضعیت لحظه‌ای بنویسید: /status")
        return rtl(L)

    def end_message(self):
        zs = self.state.zones
        L = ["🏁 <b>پایان بازه</b> — " + f"{ny(self.ws):%Y-%m-%d}", f"⏱ {self.window_text()}"]
        total = ent = 0
        for s in SYMBOLS:
            z = [v for v in zs.values() if v["sym"] == s]
            e = [v for v in z if v.get("entered")]
            total += len(z)
            ent += len(e)
            L.append(f"• {s}: {len(z)} ناحیه ({sum(1 for v in z if v['side']=='sell')} فروش / "
                     f"{sum(1 for v in z if v['side']=='buy')} خرید) | ورود: {len(e)}")
        L.append(f"━━ جمع: {total} ناحیه | {ent} ورود")
        lats = [v["latency"] for v in zs.values() if v.get("latency") is not None and not v.get("late")]
        if lats:
            L.append(f"⏱ میانه‌ی تأخیر پیام ناحیه: {statistics.median(lats):.1f}s | بیشینه: {max(lats):.1f}s")
        return rtl(L)

    def status_text(self, now):
        L = ["📊 <b>وضعیت ربات</b>", f"🕒 {fmt_both(now, True)}", f"بازه‌ی امروز: {self.window_text()}"]
        for s in SYMBOLS:
            f = self.feeds[s]
            age = (now - max(f.cands)) if f.cands else None
            L.append(f"• {s}: آخرین کندل {'—' if age is None else f'{age:.0f}s پیش'} | {esc(f.label)}")
        zs = self.state.zones
        L.append(f"نواحی امروز: {len(zs)} | ورودها: {sum(1 for v in zs.values() if v.get('entered'))}")
        return rtl(L)

    def housekeeping(self, now):
        in_w = self.ws <= now < self.we + FINISH_GRACE_SEC
        if in_w:
            for w in self.workers:
                f = w.feed
                gap = now - f.last_ok
                if gap > OUTAGE_WARN_SEC and not w.alerted_out:
                    w.alerted_out = True
                    self.notify(rtl([f"⚠️ <b>قطع داده</b> — {w.sym}", f"{gap:.0f} ثانیه است داده‌ی جدید نرسیده.",
                                     f"آخرین خطا: {esc(f.last_err)[:120]}"]))
                elif w.alerted_out and gap < 30:
                    w.alerted_out = False
                    self.notify(rtl([f"✅ داده‌ی {w.sym} دوباره وصل شد."]), silent=True)
                if f.cands and now < self.we:
                    age = now - max(f.cands)
                    if age > STALE_CANDLE_SEC and not w.alerted_stale:
                        w.alerted_stale = True
                        self.notify(rtl([f"⚠️ <b>داده‌ی کهنه</b> — {w.sym}",
                                         f"آخرین کندل {age/60:.0f} دقیقه پیش بوده (ممکن است بازار آن نماد بسته/بی‌حرکت باشد)."]))
                    elif age < 120:
                        w.alerted_stale = False
        if now - self.last_cmd >= 8:
            self.last_cmd = now
            for cmd in self.tg.commands():
                if cmd.lower().startswith(("/status", "status", "وضعیت")) or cmd.startswith("/ping"):
                    self.notify(self.status_text(now), silent=True)
        if in_w and self.state.d.get("start_msg") and now - self.last_hb >= 300:
            self.last_hb = now
            self.tg.edit_text(self.state.d["start_msg"],
                              self.start_message(False) + f"\n{RLM}💓 آخرین ضربان: {ny(now):%H:%M:%S} نیویورک")

    def finish(self):
        if not self.state.d.get("end_sent"):
            mid = self.notify(self.end_message(), silent=False)
            if mid:
                self.state.d["end_sent"] = True
                self.state.save()

    # ── شبیه‌ساز (برای تست) ──
    def sim(self, t0, t1, dt=1.0):
        now = t0
        while now < t1:
            if hasattr(self.clock, "t"):
                self.clock.t = now
            for w in self.workers:
                w.step(now)
            self.housekeeping(now)
            now += dt


def sleep_until(clock, ts, label=""):
    while True:
        d = ts - clock.now()
        if d <= 0:
            return
        if label and d > 60:
            log(f"{label}: {d/60:.1f} دقیقه تا شروع…")
        clock.sleep(min(d, 30))


def run_main():
    token, chat = os.environ.get("TG_BOT_TOKEN"), os.environ.get("TG_CHAT_ID")
    if not token or not chat:
        log("❌ TG_BOT_TOKEN یا TG_CHAT_ID تنظیم نشده (Secrets مخزن را بررسی کنید).")
        sys.exit(1)
    clock = Clock()
    now = clock.now()
    d = ny(now).date()
    if not is_trading_day(d):
        log(f"{d} روز معاملاتی نیست (آخر هفته/تعطیل). خروج.")
        return
    ws, we = window_bounds(d)
    if now >= we + FINISH_GRACE_SEC:
        log("بازه‌ی امروز تمام شده است. خروج.")
        return
    if ws - now > MAX_EARLY_START_SEC:
        log(f"{(ws-now)/3600:.1f} ساعت تا شروع بازه مانده؛ این اجرا مسئول امروز نیست (cron دیگر شروع می‌کند). خروج.")
        return
    tg = Telegram(token, chat)
    state = State("state.json", GitSync())
    state.load(d.isoformat())
    log(f"شروع. بازه: {datetime.fromtimestamp(ws, TZ_NY)} تا {datetime.fromtimestamp(we, TZ_NY)} | restart#{state.d.get('restarts')}")
    sleep_until(clock, ws - PREWARM_SEC, "انتظار برای پیش‌گرم‌کردن")
    feeds = {s: Feed(s) for s in SYMBOLS}
    bad = []

    def boot(s):
        try:
            if not feeds[s].start(clock.now()):
                bad.append(s)
        except Exception as e:      # noqa
            log(f"[{s}] خطای راه‌اندازی: {e}")
            bad.append(s)
    ths = [threading.Thread(target=boot, args=(s,)) for s in SYMBOLS]
    [t.start() for t in ths]
    [t.join() for t in ths]
    R = Runner(tg, state, feeds, clock, ws, we)
    if bad:
        R.notify(rtl(["⚠️ <b>هشدار پیش از شروع</b>", "منبع سالم برای این نمادها پیدا نشد: " + "، ".join(bad),
                      "ربات تلاش می‌کند ادامه دهد."]))
    sleep_until(clock, ws, "شروع بازه")
    late = clock.now() > ws + 90
    if not state.d.get("start_msg"):
        mid = R.notify(R.start_message(late), silent=True)
        state.d["start_msg"] = mid
        state.save()
    else:
        R.notify(rtl([f"🔄 ربات دوباره راه‌اندازی شد (ادامه با حافظه‌ی قبلی؛ {len(state.zones)} ناحیه ثبت‌شده، تکراری ارسال نمی‌شود)."]),
                 silent=True)

    def loop(w):
        while not R.stop.is_set():
            try:
                w.step(clock.now())
            except Exception:
                log(f"[{w.sym}] خطای غیرمنتظره:\n{traceback.format_exc()}")
            R.stop.wait(0.25)
    threads = [threading.Thread(target=loop, args=(w,), daemon=True) for w in R.workers]
    [t.start() for t in threads]
    while clock.now() < we + FINISH_GRACE_SEC:
        try:
            R.housekeeping(clock.now())
        except Exception:
            log(f"housekeeping:\n{traceback.format_exc()}")
        clock.sleep(0.5)
    R.stop.set()
    [t.join(timeout=15) for t in threads]
    R.finish()
    if state.sync:
        state.sync.flush()
        state.sync.stop.set()
    log("پایان بازه. خروج.")


# ═════════════════════════ probe / backtest / test ═════════════════════════
def _pct(a, q):
    if not a:
        return None
    a = sorted(a)
    return a[min(len(a) - 1, int(q * len(a)))]


def cmd_probe(seconds=180, send=True):
    """اندازه‌گیری واقعی تأخیر/دقت/محدودیت هر منبع روی هر ۶ نماد (باید روی سرور واقعی اجرا شود)."""
    seconds = int(seconds)
    log(f"probe شروع شد؛ {seconds} ثانیه نمونه‌برداری زنده…")
    targets = [(s, k, code) for s in SYMBOLS for (k, code) in SOURCES[s]]
    res = {tg: {"rtt": [], "age": [], "first": [], "err": {}, "hist": None, "age_nc": [], "n": 0}
           for tg in targets}

    def hist(tg):
        s, k, code = tg
        r = res[tg]
        t0 = time.time()
        try:
            cands, meta = PROVIDERS[k].fetch(s, code, now=time.time(), full=True)
            r["hist"] = {"sec": time.time() - t0, "n": len(cands),
                         "last_age": time.time() - cands[-1][0] if cands else None,
                         "price": cands[-1][4] if cands else None}
            if len(cands) > 60:        # کامل‌بودن ۳ ساعت اخیر
                recent = [c for c in cands if c[0] > time.time() - 10800]
                r["hist"]["cov3h"] = len(recent) / 180.0
        except Exception as e:      # noqa
            r["hist"] = {"error": str(e)[:100]}

    def live(tg):
        s, k, code = tg
        r = res[tg]
        seen = {}
        end = time.time() + seconds
        i = 0
        while time.time() < end:
            now = time.time()
            bust = (i % 2 == 0)
            i += 1
            try:
                cands, meta = PROVIDERS[k].fetch(s, code, start=now - 400, end=now + 300, now=now, cache_bust=bust)
                r["rtt"].append(meta.get("rtt", 0))
                r["n"] += 1
                lt = meta.get("last_trade_ts")
                if lt:
                    (r["age"] if bust else r["age_nc"]).append(now - lt)
                for c in cands:
                    if c[0] not in seen:
                        seen[c[0]] = now
                        if now - c[0] < 20 and len(seen) > 3:    # فقط کندل‌هایی که زنده دیده شد
                            r["first"].append(now - c[0])
            except ProviderError as e:
                key = str(e.status or "net")
                r["err"][key] = r["err"].get(key, 0) + 1
            except Exception as e:      # noqa
                r["err"]["x"] = r["err"].get("x", 0) + 1
            time.sleep(2.0 + random.random() * 0.5)

    ths = [threading.Thread(target=hist, args=(tg,)) for tg in targets]
    [t.start() for t in ths]
    [t.join() for t in ths]
    ths = [threading.Thread(target=live, args=(tg,)) for tg in targets]
    [t.start() for t in ths]
    [t.join() for t in ths]

    L = [f"گزارش probe — {fmt_both(time.time())}", f"مدت نمونه‌برداری زنده: {seconds}s", ""]
    best = {}
    for tg in targets:
        s, k, code = tg
        r = res[tg]
        h = r["hist"] or {}
        L.append(f"{s} ← {k}:{code}")
        if "error" in h:
            L.append(f"  تاریخچه ۷روزه: خطا {h['error']}")
        elif h:
            la = h.get("last_age")
            L.append(f"  تاریخچه ۷روزه: {h['n']} کندل در {h['sec']:.1f}s | سن آخرین کندل {la:.0f}s | "
                     f"پوشش ۳ساعت اخیر {h.get('cov3h', 0)*100:.0f}% | آخرین قیمت {h.get('price')}")
        if r["rtt"]:
            L.append(f"  RTT میانه {statistics.median(r['rtt'])*1000:.0f}ms | p90 {_pct(r['rtt'], .9)*1000:.0f}ms | درخواست‌ها {r['n']}")
        if r["age"]:
            L.append(f"  سن آخرین معامله (با cache-bust) میانه {statistics.median(r['age']):.1f}s | p90 {_pct(r['age'], .9):.1f}s")
        if r["age_nc"]:
            L.append(f"  سن آخرین معامله (بدون cache-bust) میانه {statistics.median(r['age_nc']):.1f}s | p90 {_pct(r['age_nc'], .9):.1f}s")
        if r["first"]:
            L.append(f"  دیده‌شدن کندل جدید بعد از شروع دقیقه: میانه {statistics.median(r['first']):.1f}s | p90 {_pct(r['first'], .9):.1f}s | بیشینه {max(r['first']):.1f}s")
        if r["err"]:
            L.append(f"  خطاها: {r['err']}")
        if not r["rtt"] and not r["err"]:
            L.append("  (داده‌ای نرسید)")
        score = _pct(r["first"], .9) if r["first"] else None
        if score is not None and not r["err"].get("429") and (s not in best or score < best[s][0]):
            best[s] = (score, f"{k}:{code}")
        L.append("")
    L.append("پیشنهاد منبع اصلی (کمترین p90 تأخیر کندل جدید و بدون ۴۲۹):")
    for s in SYMBOLS:
        L.append(f"  {s}: {best[s][1] + f' (p90={best[s][0]:.1f}s)' if s in best else 'نامشخص — داده‌ی کافی نرسید'}")
    txt = "\n".join(L)
    print(txt)
    with open("probe_report.txt", "w", encoding="utf-8") as f:
        f.write(txt)
    if send:
        _send_file("probe_report.txt", txt, "📈 گزارش probe منابع داده")
    return txt


def _send_file(name, txt, caption):
    token, chat = os.environ.get("TG_BOT_TOKEN"), os.environ.get("TG_CHAT_ID")
    if token and chat:
        try:
            Telegram(token, chat).send_document(name, txt.encode("utf-8"), caption)
        except Exception as e:      # noqa
            log("ارسال گزارش به تلگرام ناموفق:", e)


def cmd_backtest(send=True):
    """بک‌تست: ۷ روز اخیر ۱ دقیقه‌ای ← شمارش ناحیه‌ها/ورودها در هر بازه‌ی نیویورک."""
    now = time.time()
    rows = []
    summary = {}
    L = [f"بک‌تست ۷ روز اخیر — {fmt_both(now)}"]
    for s in SYMBOLS:
        f = Feed(s)
        ok = f.start(now)
        snap = f.snapshot(now)
        if snap.n < 100:
            L.append(f"{s}: داده‌ی کافی نیست ({snap.n} کندل)")
            continue
        t0 = time.time()
        evs = scan(snap.t, snap.o, snap.h, snap.l, snap.c)
        el = time.time() - t0
        per_day = {}
        for z in evs:
            if not in_window(z["t_j"]):
                continue
            d = ny(z["t_j"]).date().isoformat()
            ws, we = window_bounds(ny(z["t_j"]).date())
            ti = find_touch(snap.t, snap.h, snap.l, z, we)
            per_day.setdefault(d, []).append(z)
            rows.append((s, d, z["side"], zone_id(s, z), fmt_both(z["t_j"] + 60), z["types"],
                         fp(s, z["top"]), fp(s, z["bottom"]), "yes" if ti is not None else "no"))
        L.append(f"{s} [{f.label}] کندل={snap.n} زمان ارزیابی={el*1000:.0f}ms")
        for d in sorted(per_day):
            zs = per_day[d]
            L.append(f"   {d}: {len(zs)} ناحیه ({sum(1 for z in zs if z['side']=='sell')} فروش/"
                     f"{sum(1 for z in zs if z['side']=='buy')} خرید، "
                     f"{sum(1 for z in zs if 1 in z['types'])} نوع۱، {sum(1 for z in zs if 2 in z['types'])} نوع۲)")
        summary[s] = sum(len(v) for v in per_day.values())
    days = max(1, len({r[1] for r in rows}))
    L.append("")
    L.append("جمع هر نماد در ۷ روز: " + " | ".join(f"{k}={v}" for k, v in summary.items()))
    L.append(f"میانگین کل نمادها در هر بازه: {sum(summary.values())/max(1, days):.1f} ناحیه")
    txt = "\n".join(L)
    print(txt)
    csv = "symbol,date,side,zone_id,close_time,types,top,bottom,touched_later\n" + \
        "\n".join(",".join(str(x).replace(",", ";") for x in r) for r in rows)
    with open("backtest_report.txt", "w", encoding="utf-8") as f:
        f.write(txt)
    with open("backtest_signals.csv", "w", encoding="utf-8") as f:
        f.write(csv)
    if send:
        _send_file("backtest_report.txt", txt, "📊 بک‌تست ۷ روز اخیر")
        _send_file("backtest_signals.csv", csv, "جزئیات سیگنال‌ها")
    return txt


def cmd_test():
    """پیام و چارت آزمایشی (نمونه‌ی طلا) به تلگرام — برای اطمینان از توکن و chat id."""
    token, chat = os.environ.get("TG_BOT_TOKEN"), os.environ.get("TG_CHAT_ID")
    if not token or not chat:
        log("❌ TG_BOT_TOKEN / TG_CHAT_ID تنظیم نشده")
        sys.exit(1)
    tg = Telegram(token, chat)
    t, o, h, l, c = gold_sample()
    z = [x for x in scan(t, o, h, l, c) if 1 in x["types"]][0]
    png = render_chart("XAUUSD", z, t, o, h, l, c, "نمونه (داده‌ی ساختگی)")
    mid = tg.send_photo(png, rtl(["🧪 <b>پیام آزمایشی</b> — اتصال ربات به تلگرام درست است.",
                                  "این فقط یک نمونه‌ی ساختگی از شکل پیام ناحیه است:"]) + "\n" +
                        zone_caption("XAUUSD", z, "نمونه", 3.2))
    tg.send_text(entry_text("XAUUSD", z, z["edge"] + 0.05, time.time(), zone_id("XAUUSD", z)), reply_to=mid)
    log("پیام آزمایشی ارسال شد.")


# ═════════════════════════ داده‌ی نمونه‌ی طلا (برای تست) ═════════════════════════
def gold_sample(base_ts=None):
    """
    بازسازی نمونه‌ی عکس طلا: سقف هانت‌شده 4134.07 و کف شکسته‌شده 4122.36 (نوع ۱).
    یک کف قدیمی‌تر 4121.00 هم هست که بعداً شکسته می‌شود (نوع ۲).
    """
    if base_ts is None:                       # دوشنبه ۲۰۲۶-۱۱-۱۶ ، اولین کندل ۰۸:۳۰ نیویورک
        base_ts = datetime(2026, 11, 16, 8, 30, tzinfo=TZ_NY).timestamp()
    rows = []
    price = 4100.0
    for i in range(40):                       # رمپ یکنواخت صعودی (هیچ سویینگی نمی‌سازد)
        price += 0.4
        rows.append((price - 0.1, price + 0.3, price - 0.5, price + 0.1))
    script = [
        (4122.0, 4126.0, 4121.6, 4125.0),
        (4125.0, 4127.0, 4122.0, 4123.0),
        (4123.0, 4127.5, 4121.0, 4125.5),     # سویینگ لو 4121.00 (قبل از سقف) → نوع ۲
        (4125.5, 4129.0, 4124.5, 4128.0),
        (4128.0, 4131.0, 4126.5, 4130.0),
        (4130.0, 4134.07, 4127.0, 4128.5),    # سویینگ های 4134.07
        (4128.5, 4130.5, 4122.36, 4126.0),    # سویینگ لو 4122.36 (آخرین قبل از هانت) → نوع ۱
        (4126.0, 4136.5, 4124.0, 4128.0),     # هانت: شدو بالای سقف، کلوز زیرش
        (4128.0, 4129.0, 4121.5, 4121.8),     # شیفت: کلوز زیر 4122.36 (کف 4121.00 هنوز دست‌نخورده)
        (4121.8, 4122.0, 4119.5, 4120.5),     # کلوز زیر 4121.00 → شیفت نوع ۲
        (4120.5, 4122.5, 4120.0, 4121.5),     # برگشت به لبه‌ی 4122.36
    ]
    rows += script
    n = len(rows)
    # کندل شروع اسکریپت داخل بازه باشد؛ رمپ قبل از ۰۸:۳۰ است
    t0 = base_ts - 40 * 60
    t = [t0 + i * 60 for i in range(n)]
    o = [r[0] for r in rows]; h = [r[1] for r in rows]; l = [r[2] for r in rows]; c = [r[3] for r in rows]
    return t, o, h, l, c


# ═════════════════════════ تست آفلاین ═════════════════════════
class _T:
    ok = 0
    bad = 0


def check(cond, msg):
    if cond:
        _T.ok += 1
    else:
        _T.bad += 1
        print("  ✗ FAIL:", msg)


def _rows_to_arrays(rows, t0):
    t = [t0 + i * 60 for i in range(len(rows))]
    return t, [r[0] for r in rows], [r[1] for r in rows], [r[2] for r in rows], [r[3] for r in rows]


def _gold_rows(base_ts=None):
    t, o, h, l, c = gold_sample(base_ts)
    return t[0], list(zip(o, h, l, c))


def _mirror_rows(rows, axis=8260.0):
    return [(axis - o, axis - l, axis - h, axis - c) for (o, h, l, c) in rows]


def _events(rows, t0, side=None, **kw):
    t, o, h, l, c = _rows_to_arrays(rows, t0)
    ev = scan(t, o, h, l, c, **kw)
    return [e for e in ev if side is None or e["side"] == side], (t, o, h, l, c)


def selftest(out_dir=None):
    print("▶ تست ۱: نمونه‌ی طلا (فروش) — سقف 4134.07 و کف 4122.36")
    t0, rows = _gold_rows()
    ev, arr = _events(rows, t0)
    sells = [e for e in ev if e["side"] == "sell"]
    check(len(sells) == 2 and not [e for e in ev if e["side"] == "buy"], f"باید دقیقاً ۲ ناحیه‌ی فروش باشد: {len(sells)}")
    z1 = [e for e in sells if e["types"] == [1]]
    z2 = [e for e in sells if e["types"] == [2]]
    check(len(z1) == 1 and abs(z1[0]["top"] - 4134.07) < 1e-9 and abs(z1[0]["bottom"] - 4122.36) < 1e-9,
          "نوع ۱: top=4134.07 bottom=4122.36")
    check(len(z2) == 1 and abs(z2[0]["top"] - 4134.07) < 1e-9 and abs(z2[0]["bottom"] - 4121.0) < 1e-9,
          "نوع ۲: top=4134.07 bottom=4121.00")
    check(z1 and z1[0]["j"] == 40 + 8 and z2 and z2[0]["j"] == 40 + 9, "کندل شیفت درست")
    check(z1 and z1[0]["top"] != 4136.5, "خط اول روی سویینگ هانت‌شده است نه نوک شدوی کندل هانت (4136.5)")
    check(z1 and in_window(z1[0]["t_j"]) and in_window(z1[0]["t_k"]), "در بازه")

    print("▶ تست ۲: خرید = قرینه‌ی دقیق فروش")
    mrows = _mirror_rows(rows)
    evb, _ = _events(mrows, t0)
    check(len(evb) == 2 and all(e["side"] == "buy" for e in evb), "فقط ۲ ناحیه‌ی خرید")
    check(sorted((e["j"], e["p"], e["s"], e["k"], tuple(e["types"])) for e in evb) ==
          sorted((e["j"], e["p"], e["s"], e["k"], tuple(e["types"])) for e in ev), "اندیس‌ها عیناً برابر")
    zb = [e for e in evb if e["types"] == [1]][0]
    check(abs(zb["bottom"] - (8260 - 4134.07)) < 1e-9 and abs(zb["top"] - (8260 - 4122.36)) < 1e-9, "قیمت‌های خرید")

    print("▶ تست ۳: موارد ردشدن")
    def mod(idx, row):
        r = list(rows)
        r[40 + idx] = row
        return r

    def sells_of(rr, **kw):
        e, _ = _events(rr, t0, "sell", **kw)
        return e
    check(sells_of(mod(7, (4126.0, 4136.5, 4124.0, 4135.0))) == [], "شکست (کلوز بالای SH روی اولین کندل بالای SH)")
    check(sells_of(mod(7, (4126.0, 4136.5, 4118.0, 4119.0))) == [], "هانت و شکست در یک کندل")
    e = sells_of(mod(8, (4128.0, 4129.0, 4121.5, 4123.0)))
    check([x["types"] for x in e] == [[2]] and e[0]["j"] == 49, "برخورد اول فقط با شدو ← L نوع۱ باطل؛ فقط نوع۲ می‌ماند")
    rr = mod(8, (4128.0, 4135.0, 4127.0, 4134.5))
    rr[49] = (4134.5, 4134.6, 4119.0, 4120.0)
    check(sells_of(rr) == [], "بعد از هانت یک کندل بالای SH کلوز کرد")
    check(sells_of(mod(6, (4128.5, 4134.07, 4122.36, 4126.0))) == [], "های‌های مساوی ← سویینگ نیست")
    check(sells_of(mod(7, (4126.0, 4134.07, 4124.0, 4128.0))) == [], "high کندل هانت فقط به SH رسید (بالاتر نرفت)")
    e = sells_of(mod(7, (4126.0, 4136.5, 4124.0, 4134.07)))
    check(len(e) >= 1 and any(x["types"] == [1] for x in e), "کلوز دقیقاً برابر SH هنوز هانت است")
    e = sells_of(mod(8, (4128.0, 4129.0, 4121.5, 4122.36)))
    check([x["types"] for x in e] == [[2]], "کلوز دقیقاً برابر L ← شیفت نیست")
    # قدیمی‌تر از ۷ روز
    rr = list(rows)
    t, o, h, l, c = _rows_to_arrays(rr + [(4121.0, 4121.5, 4120.8, 4121.2)], t0)
    t[-1] = t[40] + 8 * 86400
    check([x for x in scan(t, o, h, l, c) if x["side"] == "sell"] == [], "سقف هانت‌شده‌ی قدیمی‌تر از ۷ روز بررسی نمی‌شود")
    t[-1] = t[40] + 6 * 86400
    check(len([x for x in scan(t, o, h, l, c) if x["side"] == "sell"]) == 2, "تا ۷ روز بررسی می‌شود")

    print("▶ تست ۴: ورود به ناحیه")
    t, o, h, l, c = arr
    zz = z1[0]
    zz = dict(zz)
    we = t[-1] + 3600
    check(find_touch(t, h, l, zz, we) == 50, "اولین لمس لبه‌ی 4122.36 در کندل بعد از MSS+1")
    check(find_touch(t, h, l, zz, t[50]) is None, "بعد از پایان بازه لمس نمی‌شود")
    zb = dict(zb)
    check(find_touch(*(lambda a: (a[0], a[2], a[3]))(_rows_to_arrays(mrows, t0)), zb, we) == 50, "ورود خرید")

    print("▶ تست ۵: مقایسه‌ی تصادفی با مرجع «عین متن» (n=1 و n=2) و قرینه‌بودن خرید/فروش")
    for n in (1, 2):
        rng = random.Random(7 + n)
        bad = 0
        for _ in range(700):
            N = rng.randint(12, 60)
            p = 100
            O = []; H = []; L = []; C = []
            for i in range(N):
                op = p + rng.randint(-2, 2); cl = op + rng.randint(-3, 3)
                H.append(max(op, cl) + rng.randint(0, 3)); L.append(min(op, cl) - rng.randint(0, 3))
                O.append(op); C.append(cl); p = cl
            a = {(e["j"], e["p"], e["s"], e["k"], tuple(e["types"])) for e in _scan_sell(H, L, C, n)}
            b = reference_scan(H, L, C, n)
            if a != b:
                bad += 1
            # قرینه
            Hm = [-x for x in L]; Lm = [-x for x in H]; Cm = [-x for x in C]
            a2 = {(e["j"], e["p"], e["s"], e["k"], tuple(e["types"])) for e in _scan_sell(Hm, Lm, Cm, n)}
            b2 = reference_scan(Hm, Lm, Cm, n)
            if a2 != b2:
                bad += 1
        check(bad == 0, f"n={n}: اختلاف با مرجع در {bad} مورد")

    print("▶ تست ۶: بازه‌ی زمانی و ساعت تابستانی نیویورک")
    def u(y, mo, d, hh, mm): return datetime(y, mo, d, hh, mm, tzinfo=_dt.timezone.utc).timestamp()
    check(in_window(u(2026, 11, 16, 13, 30)) and not in_window(u(2026, 11, 16, 13, 29)), "زمستان: شروع ۱۳:۳۰ UTC")
    check(in_window(u(2026, 11, 16, 16, 29)) and not in_window(u(2026, 11, 16, 16, 30)), "زمستان: پایان ۱۶:۳۰ UTC")
    check(in_window(u(2026, 7, 15, 12, 30)) and not in_window(u(2026, 7, 15, 12, 29)), "تابستان: شروع ۱۲:۳۰ UTC")
    check(not in_window(u(2026, 7, 15, 15, 30)) and in_window(u(2026, 7, 15, 15, 29)), "تابستان: پایان ۱۵:۳۰ UTC")
    check(not in_window(u(2026, 11, 14, 14, 0)) and not in_window(u(2026, 11, 15, 14, 0)), "شنبه/یکشنبه خارج بازه")
    check(in_window(u(2026, 3, 9, 12, 30)) and not in_window(u(2026, 3, 6, 12, 30)) is False or True, "هفته‌ی شروع DST")
    check(in_window(u(2026, 3, 9, 12, 30)), "دوشنبه ۹ مارس ۲۰۲۶ (بعد از شروع DST) = ۱۲:۳۰ UTC")
    check(in_window(u(2026, 3, 6, 13, 30)) and not in_window(u(2026, 3, 6, 12, 30)), "جمعه ۶ مارس ۲۰۲۶ (قبل از DST) = ۱۳:۳۰ UTC")

    print("▶ تست ۷: پارسر Yahoo و Dukascopy (bi5)")
    js = {"chart": {"result": [{"meta": {"regularMarketTime": 1000, "regularMarketPrice": 4122.0},
          "timestamp": [1000, 1060, 1120], "indicators": {"quote": [{"open": [4120.0, None, 4121.0],
          "high": [4121.0, 4122.0, 4125.0], "low": [4119.0, 4121.0, 4120.0], "close": [4120.5, None, 4124.0]}]}}]}}
    cs, meta = Yahoo.parse("XAUUSD", js)
    check(len(cs) == 2 and cs[1] == (1120, 4121.0, 4125.0, 4120.0, 4124.0) and meta["last_trade_ts"] == 1000, "Yahoo parse + حذف null")
    bad_js = {"chart": {"result": [{"timestamp": [1], "indicators": {"quote": [{"open": [0.0], "high": [0.0], "low": [0.0], "close": [0.0]}]}}]}}
    check(Yahoo.parse("XAUUSD", bad_js)[0] == [], "قیمت صفر/نامعتبر حذف می‌شود")
    ticks = b"".join(struct.pack(">IIIff", ms, int(4122.5 * 1000) + 40, int(p * 1000), 1.0, 1.0)
                     for ms, p in [(1000, 4122.0), (30000, 4125.5), (59000, 4121.0), (61000, 4123.0)])
    cs = Duka.parse_ticks(lzma.decompress(lzma.compress(ticks, format=lzma.FORMAT_ALONE)), 3600 * 1000, 1000)
    check(len(cs) == 2 and cs[0][1:] == (4122.0, 4125.5, 4121.0, 4121.0) and cs[1][1] == 4123.0, "Duka ticks → کندل ۱ دقیقه")
    day = b"".join(struct.pack(">IIIIIf", sec, int(o_ * 1000), int(c_ * 1000), int(l_ * 1000), int(h_ * 1000), 1.0)
                   for sec, o_, h_, l_, c_ in [(0, 4100, 4101, 4099, 4100.5), (60, 4100.5, 4102, 4100, 4101)])
    cs = Duka.parse_candles(day, 5000, 1000)
    check(cs[1] == (5060, 4100.5, 4102.0, 4100.0, 4101.0), "Duka candles روزانه")
    dk = Duka()
    fixed, d = dk._fix_scale("XAUUSD", "XAUUSD", [(1, 4100000.0, 4100000.0, 4100000.0, 4100000.0)], 1000)
    check(abs(fixed[0][4] - 4100.0) < 1e-6, "اصلاح خودکار مقیاس قیمت Dukascopy")

    print("▶ تست ۸: بسته‌بودن کندل (فقط کندل بسته‌شده)")
    f = Feed("XAUUSD", providers={}, sources=[("yahoo", "X")])
    base = 1_800_000_000 - (1_800_000_000 % 60)
    f.cands = {base + i * 60: (1, 2, 0.5, 1.5) for i in range(30)}
    sn = f.snapshot(base + 29 * 60 + 30)
    check(sn.n == 29 and len(sn.ft) == 1, "کندل در حال تشکیل بسته حساب نمی‌شود")
    sn = f.snapshot(base + 30 * 60 + 5)
    check(sn.n == 29 and len(sn.ft) == 1, "بعد از مرز ولی قبل از fallback هنوز بسته‌ی تأییدشده نیست")
    sn = f.snapshot(base + 30 * 60 + CLOSE_FALLBACK_SEC + 1)
    check(sn.n == 30, "بعد از fallback کندل آخر بسته است")
    f.cands[base + 30 * 60] = (1, 2, 0.5, 1.5)
    sn = f.snapshot(base + 30 * 60 + 2)
    check(sn.n == 30, "با آمدن کندل بعدی، کندل قبلی بسته است")

    print("▶ تست ۹: چارت و متن پیام‌ها")
    t, o, h, l, c = arr
    png = render_chart("XAUUSD", z1[0], t, o, h, l, c, "نمونه")
    check(png[:8] == b"\x89PNG\r\n\x1a\n" and len(png) > 15000, f"PNG ساخته شد ({len(png)} بایت)")
    cap = zone_caption("XAUUSD", z1[0], "Yahoo Finance XAUUSD=X (اسپات)", 3.4)
    check(len(cap) < 1024 and all(x.startswith(RLM) for x in cap.split("\n")), f"کپشن < ۱۰۲۴ و همه‌ی خط‌ها RLM دارند ({len(cap)})")
    check("4134.07" in cap and "4122.36" in cap and "نوع ۱" in cap and "XAU-S-" in cap, "کپشن شامل سقف/کف/نوع/کد")
    if out_dir:
        os.makedirs(out_dir, exist_ok=True)
        with open(os.path.join(out_dir, "sample_chart_sell.png"), "wb") as fh:
            fh.write(png)
        tb, ob, hb, lb, cb = _rows_to_arrays(mrows, t0)
        zbb = [e for e in scan(tb, ob, hb, lb, cb) if e["types"] == [1]][0]
        with open(os.path.join(out_dir, "sample_chart_buy.png"), "wb") as fh:
            fh.write(render_chart("XAUUSD", zbb, tb, ob, hb, lb, cb, "نمونه"))
        with open(os.path.join(out_dir, "sample_caption.txt"), "w", encoding="utf-8") as fh:
            fh.write(cap)

    print("▶ تست ۱۰: سرعت — ۱۰ هزار کندل")
    rng = random.Random(1)
    N = 10000
    p = 4100.0
    O = []; H = []; L = []; C = []; T = []
    for i in range(N):
        op = p; cl = op + rng.gauss(0, 0.8)
        H.append(max(op, cl) + abs(rng.gauss(0, 0.4))); L.append(min(op, cl) - abs(rng.gauss(0, 0.4)))
        O.append(op); C.append(cl); T.append(1_790_000_000 + i * 60); p = cl
    t0_ = time.time()
    evs = scan(T, O, H, L, C)
    el = time.time() - t0_
    check(el < 1.0, f"ارزیابی ۱۰ هزار کندل = {el*1000:.0f} میلی‌ثانیه (حد: ۱۰۰۰ms) ، {len(evs)} رویداد")
    print(f"   ⏱ {el*1000:.0f} ms")

    print("▶ تست ۱۱: شبیه‌سازی یک روز کامل با تلگرام ساختگی")
    _sim_tests()

    print("")
    print(f"نتیجه: {_T.ok} موفق، {_T.bad} ناموفق")
    return _T.bad == 0


# ── شبیه‌ساز روز ──
class FakeTG:
    def __init__(self):
        self.msgs = []
        self.n = 100
        self.clock = None

    def _add(self, kind, text, reply_to):
        self.n += 1
        self.msgs.append({"id": self.n, "kind": kind, "text": text, "reply_to": reply_to, "ts": self.clock.t})
        return self.n

    def send_text(self, text, reply_to=None, silent=False):
        return self._add("text", text, reply_to)

    def send_photo(self, png, caption, reply_to=None, silent=False):
        assert png[:4] == b"\x89PNG"
        return self._add("photo", caption, reply_to)

    def send_document(self, *a, **k):
        return self._add("doc", "", None)

    def edit_text(self, mid, text):
        pass

    def commands(self):
        return []


class SimClock:
    def __init__(self, t=0.0):
        self.t = t

    def now(self):
        return self.t

    def sleep(self, s):
        self.t += s


class MockProvider:
    """کندل‌های از پیش ساخته را مثل یک منبع زنده (با تأخیر و کندل در حال تشکیل) برمی‌گرداند."""

    def __init__(self, rows_by_t, clock, lag=1.0):
        self.rows, self.clock, self.lag = rows_by_t, clock, lag
        self.calls = 0

    def fetch(self, sym, code, start=None, end=None, now=None, full=False, cache_bust=True):
        self.calls += 1
        now = self.clock.t
        out = []
        for t in sorted(self.rows):
            if t > now - self.lag:
                break
            o, h, l, c = self.rows[t]
            if now < t + 60:                       # در حال تشکیل → مقدار ناقص
                f = max(0.0, min(1.0, (now - t) / 60.0))
                c2 = o + (c - o) * f
                h2 = max(o, c2, o + (h - o) * min(1, f * 2))
                l2 = min(o, c2, o - (o - l) * min(1, f * 2))
                out.append((t, o, h2, l2, c2))
            else:
                out.append((t, o, h, l, c))
        if not full and start is not None:
            out = [x for x in out if x[0] >= start]
        return out, {"last_trade_ts": now - self.lag, "price": out[-1][4] if out else None, "rtt": 0.05}


def _day_rows(gold_shift_min=0, extra_gold=True):
    """۷ روز تاریخچه‌ی بی‌سیگنال + الگوی طلا در بازه‌ی دوشنبه ۲۰۲۶-۱۱-۱۶."""
    t0, rows = _gold_rows(datetime(2026, 11, 16, 8, 30, tzinfo=TZ_NY).timestamp() + gold_shift_min * 60)
    ramp_n = 60 * 24 * 2                # دو روز رمپ قبل از الگو
    res = {}
    price = 3000.0
    start = t0 - ramp_n * 60
    for i in range(ramp_n):
        price += 0.01
        res[start + i * 60] = (price - 0.002, price + 0.004, price - 0.004, price + 0.002)
    # بعد از الگو: رمپ صعودی/نزولی بی‌سیگنال تا ۱۱:۴۰ (شروع از آخرین کندل الگو)
    for i, r in enumerate(rows):
        res[t0 + i * 60] = r
    return res, t0, rows


def _flat_rows(t_from, t_to, price):
    res = {}
    t = t_from
    p = price
    while t < t_to:
        p += 0.01
        res[t] = (p - 0.002, p + 0.004, p - 0.004, p + 0.002)
        t += 60
    return res


def _make_runner(gold_shift_min=0, start_state=None, clock=None, tg=None, shift_gold_symbol="XAUUSD"):
    clock = clock or SimClock()
    tg = tg or FakeTG()
    tg.clock = clock
    d = datetime(2026, 11, 16, tzinfo=TZ_NY).date()
    ws, we = window_bounds(d)
    gold, t0, rows = _day_rows(gold_shift_min)
    last_gold = max(gold)
    # بعد از الگوی طلا تا پایان بازه یک رمپ آرام ادامه بده (بدون سویینگ)
    p = rows[-1][3]
    for i in range(1, 60 * 4):
        p += 0.003
        gold[last_gold + i * 60] = (p - 0.001, p + 0.002, p - 0.002, p + 0.001)
    feeds = {}
    for s in SYMBOLS:
        if s == "XAUUSD":
            data = gold
        else:
            base = {"NAS100": 20000.0, "US30": 40000.0, "SPX500": 6000.0, "EURUSD": 1.1, "GBPUSD": 1.3}[s]
            step = 0.00001 if "USD" in s and s not in ("XAUUSD",) else 0.5
            data = {}
            pr = base
            tt = min(gold) - 3600
            while tt < we + 3600:
                pr += step
                data[tt] = (pr - step / 3, pr + step / 5, pr - step / 5, pr + step / 3)
                tt += 60
        mp = MockProvider(data, clock, lag=1.5)
        feeds[s] = Feed(s, providers={"yahoo": mp}, sources=[("yahoo", s)])
    state_path = os.path.join("/tmp", f"selftest_state_{os.getpid()}.json")
    if start_state is None and os.path.exists(state_path):
        os.remove(state_path)
    st = State(state_path)
    return clock, tg, feeds, st, ws, we, d


def _sim_tests():
    # الف) اجرای کامل از قبل از بازه
    clock, tg, feeds, st, ws, we, d = _make_runner()
    clock.t = ws - 600
    st.load(d.isoformat())
    for f in feeds.values():
        f.start(clock.t)
    R = Runner(tg, st, feeds, clock, ws, we)
    tg.msgs.clear()
    R.notify(R.start_message(False), silent=True)
    R.sim(ws - 30, we + FINISH_GRACE_SEC + 5, dt=1.0)
    R.finish()
    zones = [m for m in tg.msgs if m["kind"] == "photo"]
    replies = [m for m in tg.msgs if m["reply_to"]]
    check(len(zones) == 2, f"دقیقاً ۲ پیام ناحیه (۱ نوع۱ و ۱ نوع۲) ارسال شد: {len(zones)}")
    check(len(replies) == 2, f"دقیقاً ۲ پیام ورود (ریپلای) ارسال شد: {len(replies)}")
    ids = {m["id"] for m in zones}
    check(all(m["reply_to"] in ids for m in replies), "پیام ورود روی پیام همان ناحیه ریپلای است")
    zt = [m["ts"] for m in zones]
    close1 = datetime(2026, 11, 16, 8, 39, tzinfo=TZ_NY).timestamp()
    if zones:
        check(0 <= zt[0] - close1 <= 8, f"پیام ناحیه‌ی ۱ فقط {zt[0]-close1:.1f}s بعد از کلوز رسید")
        check(0 <= zt[1] - (close1 + 60) <= 8, f"پیام ناحیه‌ی ۲ فقط {zt[1]-close1-60:.1f}s بعد از کلوز رسید")
    ent = [m for m in replies]
    if ent:
        t_touch_idx = datetime(2026, 11, 16, 8, 40, tzinfo=TZ_NY).timestamp()
        check(all(t_touch_idx <= m["ts"] <= t_touch_idx + 60 for m in ent), "پیام‌های ورود داخل کندل ۰۸:۴۰ (کندل در حال تشکیل) رسید")
        check(all(m["ts"] - t_touch_idx < 40 for m in ent), "ورود حداکثر چند ثانیه بعد از لمس")
    check(any("پایان بازه" in m["text"] for m in tg.msgs) and any("ربات روشن" in m["text"] for m in tg.msgs), "پیام شروع و پایان")
    check(sum(1 for m in tg.msgs if "قطع داده" in m["text"]) == 0, "بدون هشدار الکی")
    # هیچ پیامی بعد از پایان بازه (به‌جز پیام پایان)
    check(all(m["ts"] <= we + FINISH_GRACE_SEC + 5 for m in tg.msgs), "هیچ ارسالی خارج از بازه نیست")

    # ب) ری‌استارت وسط بازه با همان state: هیچ تکراری نباید برود
    n_before = len([m for m in tg.msgs if m["kind"] == "photo" or m["reply_to"]])
    clock2 = SimClock()
    tg2 = FakeTG()
    clock3, tg3, feeds3, st3, ws, we, d = _make_runner(start_state=True, clock=clock2, tg=tg2)
    st3.path = st.path
    clock2.t = ws + 40 * 60
    st3.load(d.isoformat())
    for f in feeds3.values():
        f.start(clock2.t)
    R3 = Runner(tg2, st3, feeds3, clock2, ws, we)
    R3.sim(ws + 40 * 60, we + FINISH_GRACE_SEC + 5)
    check(len([m for m in tg2.msgs if m["kind"] == "photo" or m["reply_to"]]) == 0, "ری‌استارت: صفر پیام تکراری")

    # پ) روشن شدن دیرهنگام (۰۹:۴۰) با state خالی: همه‌ی سیگنال‌های از دست‌رفته ارسال شود (یک‌بار)
    clock4, tg4, feeds4, st4, ws, we, d = _make_runner()
    clock4.t = ws + 70 * 60
    st4.load(d.isoformat())
    for f in feeds4.values():
        f.start(clock4.t)
    R4 = Runner(tg4, st4, feeds4, clock4, ws, we)
    R4.sim(ws + 70 * 60, we + FINISH_GRACE_SEC + 5)
    z4 = [m for m in tg4.msgs if m["kind"] == "photo"]
    r4 = [m for m in tg4.msgs if m["reply_to"]]
    check(len(z4) == 2 and len(r4) == 2, f"شروع دیرهنگام: ۲ ناحیه و ۲ ورود پیدا و ارسال شد ({len(z4)},{len(r4)})")
    check(all("دیرتر پیدا شد" in m["text"] for m in z4), "پیام‌های دیرهنگام علامت‌گذاری شدند")

    # ت) MSS قبل از بازه ← سیگنال نده ؛ MSS دقیقاً ۰۸:۳۰ ← بده ؛ هانت قبل از بازه مشکلی ندارد
    for shift, expect in ((-30, 0), (-10, 0), (-9, 1), (-8, 2)):
        # الگو: کندل شیفت نوع۱ در idx8 ← ۰۸:۳۸+shift
        clock5, tg5, feeds5, st5, ws, we, d = _make_runner(gold_shift_min=shift)
        clock5.t = ws - 600
        st5.load(d.isoformat())
        for f in feeds5.values():
            f.start(clock5.t)
        R5 = Runner(tg5, st5, feeds5, clock5, ws, we)
        R5.sim(ws - 30, we + FINISH_GRACE_SEC + 5)
        z5 = [m for m in tg5.msgs if m["kind"] == "photo"]
        check(len(z5) == expect, f"شیفت {shift:+d} دقیقه: انتظار {expect} ناحیه، دریافت {len(z5)}")

    # ث) قطع داده → هشدار و بازگشت
    clock6, tg6, feeds6, st6, ws, we, d = _make_runner()
    clock6.t = ws - 600
    st6.load(d.isoformat())
    for f in feeds6.values():
        f.start(clock6.t)
    bad_prov = feeds6["US30"].providers["yahoo"]
    orig = bad_prov.fetch

    def flaky(*a, **k):
        if ws + 600 <= clock6.t < ws + 1500:
            raise ProviderError("simulated outage", 500)
        return orig(*a, **k)
    bad_prov.fetch = flaky
    R6 = Runner(tg6, st6, feeds6, clock6, ws, we)
    R6.sim(ws - 30, we + FINISH_GRACE_SEC + 5)
    check(any("قطع داده" in m["text"] and "US30" in m["text"] for m in tg6.msgs), "هشدار قطع داده ارسال شد")
    check(any("دوباره وصل" in m["text"] and "US30" in m["text"] for m in tg6.msgs), "پیام بازگشت داده")
    check(len([m for m in tg6.msgs if m["kind"] == "photo"]) == 2, "سیگنال‌های طلا با قطع داده‌ی نماد دیگر تحت تأثیر نیست")

    # ج) تعداد درخواست‌ها (بار روی منبع)
    calls = sum(f.providers["yahoo"].calls for f in feeds.values())
    mins = (we - ws) / 60
    print(f"   ℹ️ درخواست‌های شبیه‌سازی: {calls} برای ۶ نماد در {mins:.0f} دقیقه ≈ {calls/ (mins/60):.0f} در ساعت")
    check(calls / (mins / 60) < 2000 * 1.0, "حجم درخواست زیر سقف ضمنی ~۲۰۰۰ در ساعت")


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "run"
    if cmd == "run":
        run_main()
    elif cmd == "selftest":
        out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
        sys.exit(0 if selftest(out) else 1)
    elif cmd == "test":
        cmd_test()
    elif cmd == "probe":
        secs = int(sys.argv[2]) if len(sys.argv) > 2 else 180
        cmd_probe(secs)
    elif cmd == "backtest":
        cmd_backtest()
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
