#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════╗
║  BALFUND TRADING PVT. LTD.                                              ║
║  EMA Breakout Options Strategy — GUI Edition                            ║
║                                                                          ║
║  Version : 1.0 (GUI)                                                    ║
║  Date    : May 2026                                                      ║
║                                                                          ║
║  Strategy : 5-min EMA 89 (High/Low) breakout on ITM option strikes      ║
║  Mode     : Paper trade first, live-ready architecture                   ║
║  GUI      : CustomTkinter with Balfund dark branding                     ║
║  Build    : PyInstaller via GitHub Actions → Windows .exe                ║
╚══════════════════════════════════════════════════════════════════════════╝
"""

import os, sys, time, json, struct, signal, threading, csv
from datetime import datetime, timedelta, timezone
from collections import deque
from typing import Dict, Optional, Any, List, Tuple
from pathlib import Path
from queue import Queue, Empty

import requests
import pandas as pd
import pyotp
import websocket
from dotenv import load_dotenv, set_key
import customtkinter as ctk

# ══════════════════════════════════════════════════════════════════════════
# PATH — works both as .py and PyInstaller .exe
# ══════════════════════════════════════════════════════════════════════════
if getattr(sys, "frozen", False):
    BASE_DIR = Path(sys.executable).parent
else:
    BASE_DIR = Path(__file__).resolve().parent

ENV_FILE = BASE_DIR / ".env"
LOG_CSV  = BASE_DIR / "ema_breakout_trades.csv"

# ══════════════════════════════════════════════════════════════════════════
# THEME — Balfund Dark
# ══════════════════════════════════════════════════════════════════════════
DARK_BG    = "#0d1117"
PANEL_BG   = "#161b22"
CARD_BG    = "#21262d"
ACCENT     = "#238636"
ACCENT_H   = "#2ea043"
RED_COL    = "#da3633"
RED_H      = "#b91c1c"
ORANGE_COL = "#d29922"
CYAN_COL   = "#58a6ff"
GOLD_COL   = "#e3b341"
WHITE_COL  = "#e6edf3"
GREY_COL   = "#8b949e"
BORDER     = "#30363d"

F_TITLE  = ("Segoe UI", 20, "bold")
F_HEAD   = ("Segoe UI", 15, "bold")
F_LABEL  = ("Segoe UI", 13)
F_BTN    = ("Segoe UI", 13, "bold")
F_MONO   = ("Consolas", 12)
F_MONO_S = ("Consolas", 11)
F_SMALL  = ("Segoe UI", 11)
F_BIG    = ("Consolas", 28, "bold")

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("dark-blue")

# ══════════════════════════════════════════════════════════════════════════
# STRATEGY CONSTANTS
# ══════════════════════════════════════════════════════════════════════════
EMA_PERIOD = 89
CANDLE_INTERVAL_SEC = 300
TARGET_POINTS = 15.0
ITM_OFFSET = 100
NIFTY_STRIKE_GAP = 50
BANKNIFTY_STRIKE_GAP = 100

INDEX_CONFIG = {
    "NIFTY":     {"security_id": "13", "strike_gap": NIFTY_STRIKE_GAP,     "lot_size": 75},
    "BANKNIFTY": {"security_id": "25", "strike_gap": BANKNIFTY_STRIKE_GAP, "lot_size": 30},
}

BASE_URL = "https://api.dhan.co/v2"
AUTH_GENERATE_URL = "https://auth.dhan.co/app/generateAccessToken"
AUTH_RENEW_URL    = "https://api.dhan.co/v2/RenewToken"
AUTH_VERIFY_URL   = "https://api.dhan.co/v2/profile"

REQ_SUB_TICKER = 15
RESP_TICKER    = 2
EXCH_SEG_MAP   = {0: "IDX_I", 1: "NSE_EQ", 2: "NSE_FNO", 3: "NSE_CURRENCY",
                  4: "BSE_EQ", 5: "MCX_COMM", 7: "BSE_CURRENCY", 8: "BSE_FNO"}

# Runtime globals — set after token resolution
HEADERS: Dict[str, str] = {}
WS_URL: str = ""
CLIENT_ID: str = ""
ACCESS_TOKEN: str = ""


# ══════════════════════════════════════════════════════════════════════════
# ENV HELPERS
# ══════════════════════════════════════════════════════════════════════════
def _ensure_env():
    if not ENV_FILE.exists():
        ENV_FILE.write_text(
            "DHAN_CLIENT_ID=\nDHAN_PIN=\nDHAN_TOTP_SECRET=\nDHAN_ACCESS_TOKEN=\n"
        )
    load_dotenv(str(ENV_FILE), override=True)


def _save_env(key: str, value: str):
    try:
        set_key(str(ENV_FILE), key, value)
    except Exception:
        pass


def _read_env(key: str) -> str:
    _ensure_env()
    return os.getenv(key, "").strip()


# ══════════════════════════════════════════════════════════════════════════
# TIME HELPERS
# ══════════════════════════════════════════════════════════════════════════
def _normalize_dhan_epoch(ts: int) -> int:
    ts = int(ts)
    now_ts = int(time.time())
    diff = ts - now_ts
    if int(4.5 * 3600) <= diff <= int(6.5 * 3600):
        ts -= 19800
    return ts


def epoch_to_ist_str(ts, fmt="%H:%M:%S") -> str:
    if not ts:
        return "-"
    ts = _normalize_dhan_epoch(int(ts))
    ist = timezone(timedelta(hours=5, minutes=30))
    dt = datetime.fromtimestamp(ts, tz=ist)
    return dt.strftime(fmt)


def five_min_bucket(epoch_sec: int) -> int:
    epoch_sec = _normalize_dhan_epoch(int(epoch_sec))
    return epoch_sec - (epoch_sec % CANDLE_INTERVAL_SEC)


def now_ist() -> datetime:
    ist = timezone(timedelta(hours=5, minutes=30))
    return datetime.now(ist)


# ══════════════════════════════════════════════════════════════════════════
# TOKEN MANAGER
# ══════════════════════════════════════════════════════════════════════════
class DhanTokenManager:
    def __init__(self, client_id, pin, totp_secret, existing_token=""):
        self.client_id = client_id
        self.pin = pin
        self.totp_secret = totp_secret
        self.existing_token = existing_token
        self.log_lines: List[str] = []

    def _log(self, msg):
        self.log_lines.append(msg)

    def verify(self, token: str) -> bool:
        if not token:
            return False
        try:
            h = {"access-token": token, "client-id": self.client_id}
            r = requests.get(AUTH_VERIFY_URL, headers=h, timeout=10)
            return r.status_code == 200
        except Exception:
            return False

    def renew(self, token: str) -> Optional[str]:
        try:
            h = {"access-token": token, "dhanClientId": self.client_id,
                 "Content-Type": "application/json"}
            r = requests.get(AUTH_RENEW_URL, headers=h, timeout=15)
            try:
                d = r.json()
            except Exception:
                d = {}
            if "accessToken" in d:
                self._log(f"✅ Token renewed (exp: {d.get('expiryTime', '?')})")
                return d["accessToken"]
            self._log(f"Renew failed: {d.get('errorMessage', str(d)[:100])}")
            return None
        except Exception as e:
            self._log(f"Renew exception: {e}")
            return None

    def generate(self, max_retries=3) -> Optional[str]:
        for attempt in range(max_retries):
            rem = 30 - (int(time.time()) % 30)
            if attempt > 0 or rem < 10:
                self._log(f"⏳ Waiting {rem + 1}s for fresh TOTP window...")
                time.sleep(rem + 1)
            totp = pyotp.TOTP(self.totp_secret).now()
            self._log(f"Attempt {attempt + 1}: TOTP={totp}")
            try:
                params = {"dhanClientId": self.client_id,
                          "pin": self.pin, "totp": totp}
                r = requests.post(AUTH_GENERATE_URL, params=params, timeout=15)
                try:
                    d = r.json()
                except Exception:
                    d = {}
                if "accessToken" in d:
                    self._log(f"✅ Token generated (exp: {d.get('tokenExpiry', '?')})")
                    return d["accessToken"]
                err = str(d.get("errorMessage") or d.get("message") or d.get("remarks") or d)
                self._log(f"Attempt {attempt + 1} failed: {err}")
                if "totp" in err.lower() or "invalid" in err.lower():
                    continue
                return None
            except Exception as e:
                self._log(f"Exception (attempt {attempt + 1}): {e}")
                if attempt < max_retries - 1:
                    time.sleep(2)
                    continue
                return None
        return None

    def ensure_token(self) -> Optional[str]:
        existing = self.existing_token
        if existing:
            self._log("Verifying existing token...")
            if self.verify(existing):
                self._log("✅ Existing token valid")
                return existing
            self._log("Token expired — trying Renew...")
            renewed = self.renew(existing)
            if renewed:
                _save_env("DHAN_ACCESS_TOKEN", renewed)
                return renewed
            self._log("Renew failed — generating via TOTP...")
        else:
            self._log("No existing token — generating via TOTP...")
        new = self.generate()
        if new:
            _save_env("DHAN_ACCESS_TOKEN", new)
        return new


# ══════════════════════════════════════════════════════════════════════════
# REST API HELPERS
# ══════════════════════════════════════════════════════════════════════════
def api_post(endpoint, payload, retries=2):
    url = f"{BASE_URL}{endpoint}"
    for attempt in range(retries + 1):
        try:
            r = requests.post(url, headers=HEADERS, json=payload, timeout=15)
            if r.status_code == 200:
                return r.json()
        except Exception:
            pass
        if attempt < retries:
            time.sleep(1)
    return None


def fetch_expiry_list(index_name):
    cfg = INDEX_CONFIG[index_name]
    payload = {"UnderlyingScrip": int(cfg["security_id"]), "UnderlyingSeg": "IDX_I"}
    resp = api_post("/optionchain/expirylist", payload)
    if resp and resp.get("status") == "success":
        return resp.get("data", [])
    return []


def get_current_week_expiry(index_name):
    expiries = fetch_expiry_list(index_name)
    today = now_ist().date()
    dates = []
    for s in expiries:
        try:
            d = datetime.strptime(s, "%Y-%m-%d").date()
            if d >= today:
                dates.append((d, s))
        except ValueError:
            continue
    dates.sort()
    return dates[0][1] if dates else None


def fetch_option_chain(index_name, expiry):
    cfg = INDEX_CONFIG[index_name]
    payload = {"UnderlyingScrip": int(cfg["security_id"]), "UnderlyingSeg": "IDX_I", "Expiry": expiry}
    resp = api_post("/optionchain", payload)
    if resp and resp.get("status") == "success":
        data = resp["data"]
        return {"spot_price": float(data["last_price"]), "oc": data["oc"]}
    return None


def select_itm_strikes(index_name, spot_price, oc_data):
    cfg = INDEX_CONFIG[index_name]
    gap = cfg["strike_gap"]
    atm = round(spot_price / gap) * gap
    itm_ce = atm - ITM_OFFSET
    itm_pe = atm + ITM_OFFSET
    oc = oc_data["oc"]
    ce_info = pe_info = None

    for k in oc:
        try:
            if abs(float(k) - itm_ce) < 0.01 and oc[k].get("ce"):
                d = oc[k]["ce"]
                ce_info = {"strike": itm_ce, "security_id": str(d["security_id"]),
                           "last_price": float(d.get("last_price", 0)), "option_type": "CE"}
            if abs(float(k) - itm_pe) < 0.01 and oc[k].get("pe"):
                d = oc[k]["pe"]
                pe_info = {"strike": itm_pe, "security_id": str(d["security_id"]),
                           "last_price": float(d.get("last_price", 0)), "option_type": "PE"}
        except ValueError:
            continue
    return ce_info, pe_info


def fetch_historical_5min(security_id, days_back=10):
    to_date = now_ist().strftime("%Y-%m-%d")
    from_date = (now_ist() - timedelta(days=days_back)).strftime("%Y-%m-%d")
    payload = {"securityId": str(security_id), "exchangeSegment": "NSE_FNO",
               "instrument": "OPTIDX", "interval": "5",
               "fromDate": from_date, "toDate": to_date}
    resp = api_post("/charts/intraday", payload)
    if not resp or "open" not in resp or not resp["open"]:
        return None
    df = pd.DataFrame({"timestamp": resp["timestamp"],
                        "open": [float(x) for x in resp["open"]],
                        "high": [float(x) for x in resp["high"]],
                        "low": [float(x) for x in resp["low"]],
                        "close": [float(x) for x in resp["close"]],
                        "volume": resp.get("volume", [0] * len(resp["open"]))})
    df.sort_values("timestamp", inplace=True)
    df.reset_index(drop=True, inplace=True)
    return df


def fetch_lot_size(index_name):
    try:
        url = "https://images.dhan.co/api-data/api-scrip-master-detailed.csv"
        r = requests.get(url, timeout=20)
        r.raise_for_status()
        from io import StringIO
        df = pd.read_csv(StringIO(r.text),
                         usecols=["SYMBOL_NAME", "INSTRUMENT", "SEM_LOT_UNITS"],
                         low_memory=False)
        df = df[(df["INSTRUMENT"] == "OPTIDX") & (df["SYMBOL_NAME"] == index_name)]
        if not df.empty:
            lot = int(df.iloc[0]["SEM_LOT_UNITS"])
            if lot > 0:
                return lot
    except Exception:
        pass
    return INDEX_CONFIG[index_name]["lot_size"]


# ══════════════════════════════════════════════════════════════════════════
# EMA CALCULATOR — matches TradingView ta.ema() exactly
# ══════════════════════════════════════════════════════════════════════════
class EMACalculator:
    def __init__(self, period=89):
        self.period = period
        self.k = 2.0 / (period + 1.0)
        self.ema_high = None
        self.ema_low = None
        self.candle_count = 0
        self.candles = deque(maxlen=200)

    def seed_from_historical(self, df):
        self.candles.clear()
        self.ema_high = self.ema_low = None
        self.candle_count = 0
        for _, row in df.iterrows():
            self._process(int(row["timestamp"]), float(row["open"]),
                          float(row["high"]), float(row["low"]),
                          float(row["close"]), int(row.get("volume", 0)))

    def _process(self, ts, o, h, l, c, v=0):
        self.candle_count += 1
        if self.ema_high is None:
            self.ema_high = h
            self.ema_low = l
        else:
            self.ema_high = h * self.k + self.ema_high * (1.0 - self.k)
            self.ema_low  = l * self.k + self.ema_low  * (1.0 - self.k)
        self.candles.append({"ts": ts, "o": o, "h": h, "l": l, "c": c, "v": v,
                             "ema_h": self.ema_high, "ema_l": self.ema_low})

    def update_candle(self, ts, o, h, l, c, v=0):
        self._process(ts, o, h, l, c, v)

    def is_ready(self):
        return self.candle_count >= self.period and self.ema_high is not None

    def get_values(self):
        return (round(self.ema_high, 2) if self.ema_high is not None else None,
                round(self.ema_low, 2)  if self.ema_low  is not None else None)

    def last_n(self, n=5):
        return list(self.candles)[-n:]


# ══════════════════════════════════════════════════════════════════════════
# 5-MIN CANDLE ENGINE
# ══════════════════════════════════════════════════════════════════════════
class FiveMinCandleEngine:
    def __init__(self, sec_id, label, on_close=None):
        self.sec_id = sec_id
        self.label = label
        self.on_close = on_close
        self.lock = threading.Lock()
        self.current = None
        self.last_ltp = None
        self.last_ltt = None
        self.tick_count = 0

    def on_tick(self, ltp, ltt_epoch):
        ltp = float(ltp)
        ltt_epoch = _normalize_dhan_epoch(int(ltt_epoch))
        bucket = five_min_bucket(ltt_epoch)
        with self.lock:
            self.last_ltp = ltp
            self.last_ltt = ltt_epoch
            self.tick_count += 1
            if self.current is None:
                self.current = {"bucket": bucket, "open": ltp, "high": ltp,
                                "low": ltp, "close": ltp, "ticks": 1}
                return
            if bucket == self.current["bucket"]:
                self.current["high"] = max(self.current["high"], ltp)
                self.current["low"]  = min(self.current["low"],  ltp)
                self.current["close"] = ltp
                self.current["ticks"] += 1
                return
            if bucket > self.current["bucket"]:
                completed = dict(self.current)
                self.current = {"bucket": bucket, "open": ltp, "high": ltp,
                                "low": ltp, "close": ltp, "ticks": 1}
                if self.on_close:
                    threading.Thread(target=self.on_close,
                                     args=(self.sec_id, completed), daemon=True).start()

    def snapshot(self):
        with self.lock:
            return {"label": self.label, "ltp": self.last_ltp,
                    "ltt": self.last_ltt,
                    "current": dict(self.current) if self.current else None,
                    "tick_count": self.tick_count}


# ══════════════════════════════════════════════════════════════════════════
# WS BINARY PARSERS
# ══════════════════════════════════════════════════════════════════════════
def parse_header_8(msg):
    if len(msg) < 8:
        return None
    return {"resp_code": msg[0],
            "exch_seg_name": EXCH_SEG_MAP.get(msg[3], str(msg[3])),
            "security_id": str(struct.unpack_from("<I", msg, 4)[0]),
            "payload": msg[8:]}


def parse_ticker(payload):
    if len(payload) < 8:
        return None
    return {"ltp": float(struct.unpack_from("<f", payload, 0)[0]),
            "ltt_epoch": int(struct.unpack_from("<I", payload, 4)[0])}


# ══════════════════════════════════════════════════════════════════════════
# TRADE STATE
# ══════════════════════════════════════════════════════════════════════════
class Trade:
    def __init__(self, index, option_type, strike, security_id,
                 entry_price, entry_time, target, stop_loss, lot_size):
        self.index = index
        self.option_type = option_type
        self.strike = strike
        self.security_id = security_id
        self.entry_price = entry_price
        self.entry_time = entry_time
        self.target = target
        self.stop_loss = stop_loss
        self.lot_size = lot_size
        self.current_ltp = None
        self.pnl = 0.0
        self.exit_price = None
        self.exit_time = None
        self.exit_reason = None
        self.is_open = True


# ══════════════════════════════════════════════════════════════════════════
# STRATEGY ENGINE (headless — communicates via Queue)
# ══════════════════════════════════════════════════════════════════════════
class StrategyEngine:
    def __init__(self, indices, log_q: Queue):
        self.indices = indices
        self.log_q = log_q
        self.stop_event = threading.Event()

        self.expiry = {}
        self.spot_price = {}
        self.lot_sizes = {}
        self.ce_info = {}
        self.pe_info = {}
        self.ema_calcs = {}
        self.ema_label = {}
        self.candle_engines = {}
        self.spot_engines = {}

        self.trades_lock = threading.Lock()
        self.active_trades: Dict[str, Trade] = {}
        self.completed_trades: List[Trade] = []
        self.needs_refresh = {}

        self.ws = None
        self.ws_connected = threading.Event()
        self.ws_instruments = []
        self.packet_count = 0
        self.last_ws_error = None

    def log(self, msg):
        ts = now_ist().strftime("%H:%M:%S")
        self.log_q.put(f"[{ts}] {msg}")

    # ── INIT ──
    def initialize(self):
        for idx in self.indices:
            self.log(f"[{idx}] Initializing...")
            self.lot_sizes[idx] = fetch_lot_size(idx)
            self.log(f"[{idx}] Lot size: {self.lot_sizes[idx]}")

            exp = get_current_week_expiry(idx)
            if not exp:
                self.log(f"[{idx}] ❌ No expiry found")
                continue
            self.expiry[idx] = exp
            self.log(f"[{idx}] Expiry: {exp}")
            self._select_strikes(idx)

        if not self.ws_instruments:
            self.log("❌ No instruments to subscribe — cannot start.")
            return False
        return True

    def _select_strikes(self, idx):
        exp = self.expiry.get(idx)
        if not exp:
            return
        oc = fetch_option_chain(idx, exp)
        if not oc:
            self.log(f"[{idx}] ❌ Option chain failed")
            return
        spot = oc["spot_price"]
        self.spot_price[idx] = spot
        self.log(f"[{idx}] Spot: {spot:.2f}")

        ce, pe = select_itm_strikes(idx, spot, oc)
        self.ce_info[idx] = ce
        self.pe_info[idx] = pe

        if ce:
            self.log(f"[{idx}] CE: {int(ce['strike'])} | secId={ce['security_id']} | LTP={ce['last_price']:.2f}")
            self._setup_option(idx, ce, "CE")
        if pe:
            self.log(f"[{idx}] PE: {int(pe['strike'])} | secId={pe['security_id']} | LTP={pe['last_price']:.2f}")
            self._setup_option(idx, pe, "PE")
        self.needs_refresh[idx] = False

    def _setup_option(self, idx, info, opt_type):
        sec_id = info["security_id"]
        label = f"{idx} {int(info['strike'])}{opt_type}"
        self.ema_label[sec_id] = label

        self.log(f"  Fetching 5-min history for {label}...")
        df = fetch_historical_5min(sec_id, days_back=10)

        ema = EMACalculator(EMA_PERIOD)
        if df is not None and len(df) > 0:
            now_epoch = int(time.time())
            current_bucket = five_min_bucket(now_epoch)
            if len(df) > 1 and int(df.iloc[-1]["timestamp"]) >= current_bucket:
                df = df.iloc[:-1].copy()
            ema.seed_from_historical(df)
            eh, el = ema.get_values()
            self.log(f"  {label}: {len(df)} candles | EMA_H={eh} | EMA_L={el} | Ready={ema.is_ready()}")
        else:
            self.log(f"  {label}: No history — EMA will build from live")

        self.ema_calcs[sec_id] = ema
        engine = FiveMinCandleEngine(sec_id, label, on_close=self.on_candle_close)
        self.candle_engines[sec_id] = engine
        self.ws_instruments.append({"name": label, "exchange": "NSE_FNO", "security_id": sec_id})

    # ── CANDLE CLOSE → STRATEGY LOGIC ──
    def on_candle_close(self, sec_id, candle):
        ema = self.ema_calcs.get(sec_id)
        if not ema:
            return

        o, h, l, c = float(candle["open"]), float(candle["high"]), float(candle["low"]), float(candle["close"])
        ts = int(candle["bucket"])
        ema.update_candle(ts, o, h, l, c)

        if not ema.is_ready():
            return

        ema_h, ema_l = ema.get_values()
        label = self.ema_label.get(sec_id, sec_id)
        t_str = epoch_to_ist_str(ts, "%H:%M")
        self.log(f"[{t_str}] {label}  O={o:.2f} H={h:.2f} L={l:.2f} C={c:.2f} | EMA_H={ema_h} EMA_L={ema_l}")

        with self.trades_lock:
            if sec_id in self.active_trades:
                trade = self.active_trades[sec_id]
                if trade.is_open:
                    old_sl = trade.stop_loss
                    trade.stop_loss = ema_l
                    trade.current_ltp = c

                    if c >= trade.target:
                        self._close_trade(trade, c, "TARGET HIT")
                        del self.active_trades[sec_id]
                        self._flag_refresh(sec_id)
                        return
                    if c <= ema_l:
                        self._close_trade(trade, c, "SL HIT (EMA Low)")
                        del self.active_trades[sec_id]
                        self._flag_refresh(sec_id)
                        return
                    if old_sl != trade.stop_loss:
                        self.log(f"  ↳ Trailing SL: {old_sl:.2f} → {trade.stop_loss:.2f}")
                return

            # ENTRY CHECK
            if c > ema_h:
                for idx_name in self.indices:
                    ci = self.ce_info.get(idx_name)
                    pi = self.pe_info.get(idx_name)
                    info = None
                    if ci and ci["security_id"] == sec_id:
                        info = ci
                    elif pi and pi["security_id"] == sec_id:
                        info = pi
                    if info:
                        trade = Trade(
                            index=idx_name, option_type=info["option_type"],
                            strike=info["strike"], security_id=sec_id,
                            entry_price=c, entry_time=epoch_to_ist_str(ts, "%H:%M:%S"),
                            target=c + TARGET_POINTS, stop_loss=ema_l,
                            lot_size=self.lot_sizes.get(idx_name, INDEX_CONFIG[idx_name]["lot_size"]))
                        self.active_trades[sec_id] = trade
                        self.log(f"▶ ENTRY  {idx_name} {int(info['strike'])}{info['option_type']}  "
                                 f"@ ₹{c:.2f}  Target=₹{trade.target:.2f}  SL=₹{ema_l:.2f}  Qty={trade.lot_size}")
                        break

    def _close_trade(self, trade, exit_price, reason):
        trade.exit_price = exit_price
        trade.exit_time = now_ist().strftime("%H:%M:%S")
        trade.exit_reason = reason
        trade.pnl = (exit_price - trade.entry_price) * trade.lot_size
        trade.is_open = False
        self.completed_trades.append(trade)
        col = "🟢" if trade.pnl >= 0 else "🔴"
        self.log(f"◼ EXIT  {trade.index} {int(trade.strike)}{trade.option_type}  "
                 f"₹{trade.entry_price:.2f}→₹{exit_price:.2f}  "
                 f"{col} ₹{trade.pnl:+.2f}  ({reason})")
        self._save_trade_csv(trade)

    def _flag_refresh(self, sec_id):
        for idx_name in self.indices:
            ci = self.ce_info.get(idx_name)
            pi = self.pe_info.get(idx_name)
            if (ci and ci["security_id"] == sec_id) or (pi and pi["security_id"] == sec_id):
                self.needs_refresh[idx_name] = True

    def _save_trade_csv(self, t):
        exists = LOG_CSV.exists()
        try:
            with open(str(LOG_CSV), "a", newline="") as f:
                w = csv.writer(f)
                if not exists:
                    w.writerow(["Date", "Index", "Strike", "Type", "Entry", "Exit",
                                "EntryTime", "ExitTime", "PnL", "Qty", "Reason"])
                w.writerow([now_ist().strftime("%Y-%m-%d"), t.index, int(t.strike),
                            t.option_type, f"{t.entry_price:.2f}", f"{t.exit_price:.2f}",
                            t.entry_time, t.exit_time, f"{t.pnl:.2f}", t.lot_size, t.exit_reason])
        except Exception:
            pass

    def check_refresh(self):
        for idx in self.indices:
            if self.needs_refresh.get(idx):
                self.log(f"🔄 Refreshing strikes for {idx}...")
                old_ce = self.ce_info.get(idx)
                old_pe = self.pe_info.get(idx)
                old_sids = set()
                for info in [old_ce, old_pe]:
                    if info:
                        sid = info["security_id"]
                        old_sids.add(sid)
                        self.candle_engines.pop(sid, None)
                        self.ema_calcs.pop(sid, None)
                        self.ema_label.pop(sid, None)
                self.ws_instruments = [i for i in self.ws_instruments if i["security_id"] not in old_sids]
                self._select_strikes(idx)
                if self.ws and self.ws_connected.is_set():
                    new_instr = [i for i in self.ws_instruments if i["security_id"] not in old_sids]
                    if new_instr:
                        sub = {"RequestCode": REQ_SUB_TICKER,
                               "InstrumentCount": len(new_instr),
                               "InstrumentList": [{"ExchangeSegment": str(i["exchange"]),
                                                   "SecurityId": str(i["security_id"])} for i in new_instr]}
                        try:
                            self.ws.send(json.dumps(sub))
                            self.log("✅ Subscribed to new strikes")
                        except Exception as e:
                            self.log(f"WS resubscribe error: {e}")

    # ── WEBSOCKET ──
    def on_ws_open(self, ws):
        self.ws_connected.set()
        spot_instr = [{"ExchangeSegment": "IDX_I",
                       "SecurityId": INDEX_CONFIG[idx]["security_id"]}
                      for idx in self.indices]
        for idx in self.indices:
            self.spot_engines[idx] = FiveMinCandleEngine(INDEX_CONFIG[idx]["security_id"], f"{idx} SPOT")

        opt_instr = [{"ExchangeSegment": str(i["exchange"]),
                      "SecurityId": str(i["security_id"])} for i in self.ws_instruments]
        all_instr = spot_instr + opt_instr
        ws.send(json.dumps({"RequestCode": REQ_SUB_TICKER,
                            "InstrumentCount": len(all_instr),
                            "InstrumentList": all_instr}))
        self.log(f"📡 WebSocket connected — {len(all_instr)} instruments subscribed")

    def on_ws_message(self, ws, message):
        if isinstance(message, str):
            return
        msg = bytes(message)
        hdr = parse_header_8(msg)
        if not hdr:
            return
        code = int(hdr["resp_code"])
        sec_id = str(hdr["security_id"])
        self.packet_count += 1

        if code == RESP_TICKER:
            t = parse_ticker(hdr["payload"])
            if not t:
                return
            ltp = float(t["ltp"])
            ltt = int(t["ltt_epoch"])

            for idx in self.indices:
                if sec_id == INDEX_CONFIG[idx]["security_id"]:
                    self.spot_price[idx] = ltp

            if sec_id in self.candle_engines:
                self.candle_engines[sec_id].on_tick(ltp, ltt)
                with self.trades_lock:
                    if sec_id in self.active_trades:
                        trade = self.active_trades[sec_id]
                        trade.current_ltp = ltp
                        if ltp >= trade.target and trade.is_open:
                            self._close_trade(trade, ltp, "TARGET HIT (tick)")
                            del self.active_trades[sec_id]
                            self._flag_refresh(sec_id)

    def on_ws_error(self, ws, error):
        self.last_ws_error = str(error)

    def on_ws_close(self, ws, status_code, msg):
        self.ws_connected.clear()

    def run_ws(self):
        websocket.enableTrace(False)
        while not self.stop_event.is_set():
            try:
                self.ws = websocket.WebSocketApp(
                    WS_URL, on_open=self.on_ws_open, on_message=self.on_ws_message,
                    on_error=self.on_ws_error, on_close=self.on_ws_close)
                self.ws.run_forever(ping_interval=20, ping_timeout=10)
            except Exception:
                pass
            if not self.stop_event.is_set():
                time.sleep(2)

    def run(self):
        ok = self.initialize()
        if not ok:
            return
        threading.Thread(target=self.run_ws, daemon=True).start()
        self.ws_connected.wait(timeout=15)
        if not self.ws_connected.is_set():
            self.log("❌ WebSocket failed to connect")
            return
        self.log("✅ Live — monitoring for EMA breakout signals...")
        while not self.stop_event.is_set():
            try:
                self.check_refresh()
                time.sleep(1)
            except Exception as e:
                self.log(f"Loop error: {e}")
                time.sleep(1)

    def stop(self):
        self.stop_event.set()
        if self.ws:
            try:
                self.ws.close()
            except Exception:
                pass

    def get_dashboard_data(self):
        """Snapshot for GUI refresh."""
        options = []
        for sec_id, eng in self.candle_engines.items():
            snap = eng.snapshot()
            ema = self.ema_calcs.get(sec_id)
            eh, el = ema.get_values() if ema else (None, None)
            with self.trades_lock:
                in_trade = sec_id in self.active_trades
            options.append({
                "label": snap["label"], "ltp": snap["ltp"],
                "ema_h": eh, "ema_l": el,
                "ticks": snap["tick_count"], "in_trade": in_trade,
            })

        active = []
        with self.trades_lock:
            for sec_id, t in self.active_trades.items():
                ltp = t.current_ltp or t.entry_price
                unr = (ltp - t.entry_price) * t.lot_size
                active.append({
                    "label": f"{t.index} {int(t.strike)}{t.option_type}",
                    "entry": t.entry_price, "ltp": ltp,
                    "target": t.target, "sl": t.stop_loss,
                    "pnl": unr, "qty": t.lot_size,
                })

        total_pnl = sum(t.pnl for t in self.completed_trades)
        wins = sum(1 for t in self.completed_trades if t.pnl > 0)
        total = len(self.completed_trades)

        return {
            "spots": dict(self.spot_price),
            "expiries": dict(self.expiry),
            "lots": dict(self.lot_sizes),
            "options": options,
            "active": active,
            "completed": self.completed_trades[-10:],
            "total_pnl": total_pnl,
            "wins": wins, "total_trades": total,
            "packets": self.packet_count,
            "ws_connected": self.ws_connected.is_set(),
            "ws_error": self.last_ws_error,
        }


# ══════════════════════════════════════════════════════════════════════════
# GUI — TOKEN MANAGER TAB
# ══════════════════════════════════════════════════════════════════════════
class TokenTab(ctk.CTkFrame):
    def __init__(self, master, on_token_ready):
        super().__init__(master, fg_color=DARK_BG)
        self.on_token_ready = on_token_ready
        self._build()
        self._load()

    def _build(self):
        # Header
        hdr = ctk.CTkFrame(self, fg_color=PANEL_BG, corner_radius=0, height=70)
        hdr.pack(fill="x")
        hdr.pack_propagate(False)
        ctk.CTkLabel(hdr, text="🔑  Dhan Token Manager",
                     font=F_TITLE, text_color=GOLD_COL).pack(side="left", padx=20, pady=15)

        # Card
        card = ctk.CTkFrame(self, fg_color=CARD_BG, corner_radius=12)
        card.pack(padx=40, pady=30, fill="x")

        fields = [("Client ID", "client_id"), ("6-Digit PIN", "pin"),
                  ("TOTP Secret", "totp_secret")]
        self.entries = {}
        for i, (lbl, key) in enumerate(fields):
            ctk.CTkLabel(card, text=lbl, font=F_LABEL, text_color=GREY_COL).grid(
                row=i, column=0, padx=(20, 10), pady=(15, 5), sticky="w")
            e = ctk.CTkEntry(card, width=400, height=38, font=F_MONO,
                             fg_color=DARK_BG, border_color=BORDER, text_color=WHITE_COL,
                             show="*" if key == "pin" else "")
            e.grid(row=i, column=1, padx=(0, 20), pady=(15, 5), sticky="w")
            self.entries[key] = e

        # Buttons
        btn_frame = ctk.CTkFrame(card, fg_color="transparent")
        btn_frame.grid(row=len(fields), column=0, columnspan=2, pady=20, padx=20, sticky="w")

        ctk.CTkButton(btn_frame, text="💾  Save Credentials", font=F_BTN,
                      fg_color=ACCENT, hover_color=ACCENT_H, width=180, height=42,
                      command=self._save).pack(side="left", padx=(0, 10))
        ctk.CTkButton(btn_frame, text="🔐  Generate Token", font=F_BTN,
                      fg_color=CYAN_COL, hover_color="#79c0ff", text_color=DARK_BG,
                      width=180, height=42, command=self._generate).pack(side="left", padx=(0, 10))

        # Status
        self.status_var = ctk.StringVar(value="")
        ctk.CTkLabel(card, textvariable=self.status_var, font=F_SMALL,
                     text_color=GREY_COL, wraplength=500).grid(
            row=len(fields) + 1, column=0, columnspan=2, padx=20, pady=(0, 15), sticky="w")

        # Log
        self.log_box = ctk.CTkTextbox(self, height=180, font=F_MONO_S,
                                       fg_color=PANEL_BG, text_color=GREY_COL, border_color=BORDER,
                                       border_width=1, state="disabled")
        self.log_box.pack(padx=40, pady=(0, 20), fill="x")

    def _load(self):
        _ensure_env()
        self.entries["client_id"].insert(0, _read_env("DHAN_CLIENT_ID"))
        self.entries["pin"].insert(0, _read_env("DHAN_PIN"))
        self.entries["totp_secret"].insert(0, _read_env("DHAN_TOTP_SECRET"))

    def _save(self):
        cid = self.entries["client_id"].get().strip()
        pin = self.entries["pin"].get().strip()
        totp = self.entries["totp_secret"].get().strip()
        if not cid or not pin or not totp:
            self.status_var.set("❌ All fields required")
            return
        _save_env("DHAN_CLIENT_ID", cid)
        _save_env("DHAN_PIN", pin)
        _save_env("DHAN_TOTP_SECRET", totp)
        self.status_var.set("✅ Credentials saved to .env")

    def _generate(self):
        cid = self.entries["client_id"].get().strip()
        pin = self.entries["pin"].get().strip()
        totp_s = self.entries["totp_secret"].get().strip()
        existing = _read_env("DHAN_ACCESS_TOKEN")
        if not cid or not pin or not totp_s:
            self.status_var.set("❌ Save credentials first")
            return
        self.status_var.set("⏳ Authenticating...")
        self._append_log("Starting token generation...")

        def _run():
            mgr = DhanTokenManager(cid, pin, totp_s, existing)
            token = mgr.ensure_token()
            for line in mgr.log_lines:
                self._append_log(line)
            if token:
                global CLIENT_ID, ACCESS_TOKEN, HEADERS, WS_URL
                CLIENT_ID = cid
                ACCESS_TOKEN = token
                HEADERS.update({"Content-Type": "application/json", "Accept": "application/json",
                                "access-token": token, "client-id": cid})
                WS_URL = f"wss://api-feed.dhan.co?version=2&token={token}&clientId={cid}&authType=2"
                self.status_var.set("✅ Token ready — switch to Strategy tab")
                self._append_log("✅ Token ready!")
                if self.on_token_ready:
                    self.on_token_ready()
            else:
                self.status_var.set("❌ Token generation failed — check log")
                self._append_log("❌ Failed to obtain token")

        threading.Thread(target=_run, daemon=True).start()

    def _append_log(self, msg):
        try:
            self.log_box.configure(state="normal")
            self.log_box.insert("end", msg + "\n")
            self.log_box.see("end")
            self.log_box.configure(state="disabled")
        except Exception:
            pass


# ══════════════════════════════════════════════════════════════════════════
# GUI — STRATEGY DASHBOARD TAB
# ══════════════════════════════════════════════════════════════════════════
class StrategyTab(ctk.CTkFrame):
    def __init__(self, master):
        super().__init__(master, fg_color=DARK_BG)
        self.engine: Optional[StrategyEngine] = None
        self.log_q = Queue()
        self.running = False
        self._build()

    def _build(self):
        # ── TOP BAR ──
        top = ctk.CTkFrame(self, fg_color=PANEL_BG, corner_radius=0, height=70)
        top.pack(fill="x")
        top.pack_propagate(False)

        ctk.CTkLabel(top, text="📊  EMA Breakout Strategy",
                     font=F_TITLE, text_color=GOLD_COL).pack(side="left", padx=20)

        # Controls
        ctrl = ctk.CTkFrame(top, fg_color="transparent")
        ctrl.pack(side="right", padx=20)

        ctk.CTkLabel(ctrl, text="Index:", font=F_LABEL, text_color=GREY_COL).pack(side="left", padx=(0, 5))
        self.idx_var = ctk.StringVar(value="NIFTY")
        self.idx_menu = ctk.CTkOptionMenu(ctrl, variable=self.idx_var,
                                           values=["NIFTY", "BANKNIFTY", "BOTH"],
                                           font=F_LABEL, width=140, height=34,
                                           fg_color=CARD_BG, button_color=ACCENT)
        self.idx_menu.pack(side="left", padx=(0, 15))

        self.start_btn = ctk.CTkButton(ctrl, text="▶  Start", font=F_BTN,
                                        fg_color=ACCENT, hover_color=ACCENT_H,
                                        width=120, height=38, command=self._toggle)
        self.start_btn.pack(side="left")

        # ── STATUS ROW ──
        self.status_frame = ctk.CTkFrame(self, fg_color=CARD_BG, corner_radius=8, height=50)
        self.status_frame.pack(fill="x", padx=15, pady=(10, 5))
        self.status_frame.pack_propagate(False)

        self.ws_dot = ctk.CTkLabel(self.status_frame, text="●", font=("Segoe UI", 16),
                                    text_color=RED_COL)
        self.ws_dot.pack(side="left", padx=(15, 5))
        self.ws_label = ctk.CTkLabel(self.status_frame, text="Disconnected",
                                      font=F_SMALL, text_color=GREY_COL)
        self.ws_label.pack(side="left", padx=(0, 20))

        self.spot_labels = {}
        for idx in ["NIFTY", "BANKNIFTY"]:
            lbl = ctk.CTkLabel(self.status_frame, text=f"{idx}: ---",
                               font=F_LABEL, text_color=WHITE_COL)
            lbl.pack(side="left", padx=15)
            self.spot_labels[idx] = lbl

        self.pkt_label = ctk.CTkLabel(self.status_frame, text="Pkts: 0",
                                       font=F_SMALL, text_color=GREY_COL)
        self.pkt_label.pack(side="right", padx=15)

        # ── OPTION CARDS FRAME ──
        self.cards_frame = ctk.CTkFrame(self, fg_color="transparent")
        self.cards_frame.pack(fill="x", padx=15, pady=5)
        self.option_cards = {}

        # ── ACTIVE TRADE CARD ──
        self.trade_card = ctk.CTkFrame(self, fg_color=CARD_BG, corner_radius=10)
        self.trade_card.pack(fill="x", padx=15, pady=5)
        self.trade_title = ctk.CTkLabel(self.trade_card, text="  No Active Trade",
                                         font=F_HEAD, text_color=GREY_COL)
        self.trade_title.pack(anchor="w", padx=15, pady=(10, 2))
        self.trade_detail = ctk.CTkLabel(self.trade_card, text="",
                                          font=F_MONO, text_color=WHITE_COL)
        self.trade_detail.pack(anchor="w", padx=15, pady=(0, 10))

        # ── PNL SUMMARY ──
        pnl_row = ctk.CTkFrame(self, fg_color="transparent")
        pnl_row.pack(fill="x", padx=15, pady=5)

        self.pnl_card = self._make_stat_card(pnl_row, "Total P&L", "₹0.00")
        self.wins_card = self._make_stat_card(pnl_row, "Wins / Total", "0 / 0")
        self.wr_card = self._make_stat_card(pnl_row, "Win Rate", "0%")

        # ── LOG ──
        self.log_box = ctk.CTkTextbox(self, height=200, font=F_MONO_S,
                                       fg_color=PANEL_BG, text_color=GREY_COL,
                                       border_color=BORDER, border_width=1, state="disabled")
        self.log_box.pack(fill="both", expand=True, padx=15, pady=(5, 15))

    def _make_stat_card(self, parent, title, value):
        card = ctk.CTkFrame(parent, fg_color=CARD_BG, corner_radius=10, width=220, height=80)
        card.pack(side="left", padx=(0, 10), fill="x", expand=True)
        card.pack_propagate(False)
        ctk.CTkLabel(card, text=title, font=F_SMALL, text_color=GREY_COL).pack(anchor="w", padx=15, pady=(10, 0))
        lbl = ctk.CTkLabel(card, text=value, font=F_BIG, text_color=WHITE_COL)
        lbl.pack(anchor="w", padx=15)
        return lbl

    def _toggle(self):
        if not self.running:
            self._start()
        else:
            self._stop()

    def _start(self):
        if not HEADERS:
            self._log_append("❌ Generate token first (Token Manager tab)")
            return

        choice = self.idx_var.get()
        if choice == "BOTH":
            indices = ["NIFTY", "BANKNIFTY"]
        else:
            indices = [choice]

        self.engine = StrategyEngine(indices, self.log_q)
        self.running = True
        self.start_btn.configure(text="◼  Stop", fg_color=RED_COL, hover_color=RED_H)
        self.idx_menu.configure(state="disabled")

        threading.Thread(target=self.engine.run, daemon=True).start()
        self._poll_loop()

    def _stop(self):
        if self.engine:
            self.engine.stop()
        self.running = False
        self.start_btn.configure(text="▶  Start", fg_color=ACCENT, hover_color=ACCENT_H)
        self.idx_menu.configure(state="normal")

    def _poll_loop(self):
        """Poll log queue + refresh dashboard every 500ms."""
        # Drain log queue
        try:
            while True:
                msg = self.log_q.get_nowait()
                self._log_append(msg)
        except Empty:
            pass

        # Update dashboard
        if self.engine and self.running:
            try:
                data = self.engine.get_dashboard_data()
                self._update_dashboard(data)
            except Exception:
                pass

        if self.running:
            self.after(500, self._poll_loop)

    def _update_dashboard(self, data):
        # WS status
        if data["ws_connected"]:
            self.ws_dot.configure(text_color=ACCENT)
            self.ws_label.configure(text="Connected", text_color=ACCENT)
        else:
            self.ws_dot.configure(text_color=RED_COL)
            self.ws_label.configure(text="Disconnected", text_color=RED_COL)

        # Spots
        for idx in ["NIFTY", "BANKNIFTY"]:
            spot = data["spots"].get(idx)
            exp = data["expiries"].get(idx, "")
            lot = data["lots"].get(idx, "")
            if spot:
                self.spot_labels[idx].configure(text=f"{idx}: {spot:.2f}  (Exp: {exp}  Lot: {lot})")
            else:
                self.spot_labels[idx].configure(text=f"{idx}: ---")

        self.pkt_label.configure(text=f"Pkts: {data['packets']}")

        # Option cards
        for child in self.cards_frame.winfo_children():
            child.destroy()

        for opt in data["options"]:
            card = ctk.CTkFrame(self.cards_frame, fg_color=CARD_BG, corner_radius=10, height=70)
            card.pack(side="left", padx=(0, 8), fill="x", expand=True)
            card.pack_propagate(False)

            # Label
            ctk.CTkLabel(card, text=opt["label"], font=F_HEAD,
                         text_color=GOLD_COL if opt["in_trade"] else WHITE_COL).pack(
                anchor="w", padx=12, pady=(8, 0))

            ltp_s = f"₹{opt['ltp']:.2f}" if opt['ltp'] else "---"
            eh_s = f"{opt['ema_h']:.2f}" if opt['ema_h'] else "..."
            el_s = f"{opt['ema_l']:.2f}" if opt['ema_l'] else "..."

            detail = f"LTP: {ltp_s}  |  EMA_H: {eh_s}  |  EMA_L: {el_s}  |  Ticks: {opt['ticks']}"
            status_col = ACCENT if opt["in_trade"] else GREY_COL
            ctk.CTkLabel(card, text=detail, font=F_MONO_S,
                         text_color=status_col).pack(anchor="w", padx=12, pady=(0, 8))

        # Active trade
        if data["active"]:
            t = data["active"][0]
            pnl_col = ACCENT if t["pnl"] >= 0 else RED_COL
            self.trade_title.configure(
                text=f"  ▶ {t['label']}  |  Qty: {t['qty']}",
                text_color=GOLD_COL)
            self.trade_detail.configure(
                text=f"  Entry: ₹{t['entry']:.2f}   LTP: ₹{t['ltp']:.2f}   "
                     f"Target: ₹{t['target']:.2f}   SL: ₹{t['sl']:.2f}   "
                     f"P&L: ₹{t['pnl']:+.2f}",
                text_color=pnl_col)
        else:
            self.trade_title.configure(text="  No Active Trade", text_color=GREY_COL)
            self.trade_detail.configure(text="")

        # Stats
        tp = data["total_pnl"]
        pnl_col = ACCENT if tp >= 0 else RED_COL
        self.pnl_card.configure(text=f"₹{tp:+,.2f}", text_color=pnl_col)
        self.wins_card.configure(text=f"{data['wins']} / {data['total_trades']}")
        wr = (data['wins'] / data['total_trades'] * 100) if data['total_trades'] > 0 else 0
        self.wr_card.configure(text=f"{wr:.0f}%")

    def _log_append(self, msg):
        try:
            self.log_box.configure(state="normal")
            self.log_box.insert("end", msg + "\n")
            self.log_box.see("end")
            self.log_box.configure(state="disabled")
        except Exception:
            pass


# ══════════════════════════════════════════════════════════════════════════
# MAIN APP
# ══════════════════════════════════════════════════════════════════════════
class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("Balfund EMA Breakout — Paper Trader")
        self.geometry("1050x780")
        self.minsize(900, 650)
        self.configure(fg_color=DARK_BG)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        # Sidebar
        sidebar = ctk.CTkFrame(self, fg_color=PANEL_BG, width=200, corner_radius=0)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)

        # Logo area
        ctk.CTkLabel(sidebar, text="BALFUND", font=("Segoe UI", 22, "bold"),
                     text_color=GOLD_COL).pack(pady=(25, 2))
        ctk.CTkLabel(sidebar, text="TRADING PVT. LTD.", font=F_SMALL,
                     text_color=GREY_COL).pack(pady=(0, 5))
        ctk.CTkLabel(sidebar, text="EMA Breakout v1.0", font=F_SMALL,
                     text_color=GREY_COL).pack(pady=(0, 20))

        sep = ctk.CTkFrame(sidebar, fg_color=BORDER, height=1)
        sep.pack(fill="x", padx=15, pady=5)

        self.tab_btns = {}
        for name, icon in [("Token Manager", "🔑"), ("Strategy", "📊")]:
            btn = ctk.CTkButton(sidebar, text=f" {icon}  {name}", font=F_LABEL,
                                fg_color="transparent", hover_color=CARD_BG,
                                text_color=WHITE_COL, anchor="w", height=40,
                                command=lambda n=name: self._switch_tab(n))
            btn.pack(fill="x", padx=10, pady=2)
            self.tab_btns[name] = btn

        # Version footer
        ctk.CTkLabel(sidebar, text="Paper Trade Mode", font=F_SMALL,
                     text_color=ORANGE_COL).pack(side="bottom", pady=(0, 10))
        ctk.CTkLabel(sidebar, text="© 2026 Balfund Trading", font=F_SMALL,
                     text_color=GREY_COL).pack(side="bottom", pady=(0, 2))

        # Content area
        self.content = ctk.CTkFrame(self, fg_color=DARK_BG)
        self.content.pack(side="right", fill="both", expand=True)

        self.token_tab = TokenTab(self.content, on_token_ready=lambda: self._switch_tab("Strategy"))
        self.strategy_tab = StrategyTab(self.content)

        self.current_tab = None
        self._switch_tab("Token Manager")

    def _switch_tab(self, name):
        if self.current_tab:
            self.current_tab.pack_forget()

        for n, btn in self.tab_btns.items():
            if n == name:
                btn.configure(fg_color=CARD_BG, text_color=GOLD_COL)
            else:
                btn.configure(fg_color="transparent", text_color=WHITE_COL)

        if name == "Token Manager":
            self.token_tab.pack(fill="both", expand=True)
            self.current_tab = self.token_tab
        else:
            self.strategy_tab.pack(fill="both", expand=True)
            self.current_tab = self.strategy_tab

    def _on_close(self):
        if self.strategy_tab.engine:
            self.strategy_tab.engine.stop()
        self.destroy()


# ══════════════════════════════════════════════════════════════════════════
# ENTRY
# ══════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    _ensure_env()
    app = App()
    app.mainloop()
