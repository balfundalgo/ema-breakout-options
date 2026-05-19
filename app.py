#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════════╗
║  BALFUND TRADING PVT. LTD.                                                  ║
║  EMA 89 Breakout · Options Paper Trader · GUI v2.0                          ║
║                                                                              ║
║  5-min candles  ·  EMA 89(High) / EMA 89(Low)  ·  100pt ITM strikes        ║
║  Target +15 pts  ·  Trailing SL = EMA Low  ·  Auto strike refresh           ║
║  CustomTkinter  ·  Dhan API  ·  PyInstaller-ready                           ║
╚══════════════════════════════════════════════════════════════════════════════╝
"""

import os, sys, time, json, struct, threading, csv
from datetime import datetime, timedelta, timezone
from collections import deque
from typing import Dict, Optional, List, Tuple
from pathlib import Path
from queue import Queue, Empty

import requests
import pandas as pd
import pyotp
import websocket
from dotenv import load_dotenv, set_key
import customtkinter as ctk

# ─────────────────────────────────────────────────────────────────────────────
# PATH — PyInstaller + dev safe
# ─────────────────────────────────────────────────────────────────────────────
if getattr(sys, "frozen", False):
    BASE_DIR = Path(sys.executable).parent
else:
    BASE_DIR = Path(__file__).resolve().parent

ENV_FILE  = BASE_DIR / ".env"
LOG_CSV   = BASE_DIR / "ema_breakout_trades.csv"

# ─────────────────────────────────────────────────────────────────────────────
# THEME — Teal / Emerald on deep charcoal
# ─────────────────────────────────────────────────────────────────────────────
BG_DEEP     = "#111318"
BG_PANEL    = "#181b22"
BG_CARD     = "#1e222a"
BG_CARD_HI  = "#252a34"
BG_INPUT    = "#14171e"

TEAL        = "#2dd4bf"
TEAL_DIM    = "#1a9e8f"
EMERALD     = "#34d399"
EMERALD_DIM = "#059669"
MINT        = "#a7f3d0"

RED         = "#f87171"
RED_DIM     = "#dc2626"
AMBER       = "#fbbf24"
AMBER_DIM   = "#d97706"

WHITE       = "#f1f5f9"
GREY_LT     = "#94a3b8"
GREY        = "#64748b"
GREY_DK     = "#475569"
BORDER      = "#2a2f3a"

F_BRAND  = ("Segoe UI", 22, "bold")
F_TITLE  = ("Segoe UI", 17, "bold")
F_HEAD   = ("Segoe UI", 14, "bold")
F_BODY   = ("Segoe UI", 13)
F_SMALL  = ("Segoe UI", 11)
F_BTN    = ("Segoe UI", 13, "bold")
F_MONO   = ("Consolas", 12)
F_MONO_S = ("Consolas", 11)
F_BIG    = ("Consolas", 26, "bold")
F_HUGE   = ("Consolas", 34, "bold")

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("dark-blue")

# ─────────────────────────────────────────────────────────────────────────────
# STRATEGY DEFAULTS (overridable from GUI)
# ─────────────────────────────────────────────────────────────────────────────
DEFAULT_EMA_PERIOD    = 89
DEFAULT_CANDLE_TF     = 5          # minutes
DEFAULT_TARGET_POINTS = 15.0
DEFAULT_ITM_OFFSET    = 100
DEFAULT_QTY_MULT      = 1
NIFTY_STRIKE_GAP      = 50
BANKNIFTY_STRIKE_GAP  = 100

# Candle TF choices (minutes → seconds)
TF_OPTIONS = {"1": 60, "3": 180, "5": 300, "15": 900}

INDEX_CONFIG = {
    "NIFTY":     {"security_id": "13", "strike_gap": NIFTY_STRIKE_GAP,     "lot_size": 65},
    "BANKNIFTY": {"security_id": "25", "strike_gap": BANKNIFTY_STRIKE_GAP, "lot_size": 30},
}

BASE_URL          = "https://api.dhan.co/v2"
AUTH_GENERATE_URL = "https://auth.dhan.co/app/generateAccessToken"
AUTH_RENEW_URL    = "https://api.dhan.co/v2/RenewToken"
AUTH_VERIFY_URL   = "https://api.dhan.co/v2/profile"

REQ_SUB_TICKER = 15
RESP_TICKER    = 2
EXCH_SEG_MAP   = {0:"IDX_I",1:"NSE_EQ",2:"NSE_FNO",3:"NSE_CURRENCY",
                  4:"BSE_EQ",5:"MCX_COMM",7:"BSE_CURRENCY",8:"BSE_FNO"}

# Runtime globals
HEADERS: Dict[str, str] = {}
WS_URL: str = ""


# ─────────────────────────────────────────────────────────────────────────────
# ENV HELPERS
# ─────────────────────────────────────────────────────────────────────────────
def _ensure_env():
    if not ENV_FILE.exists():
        ENV_FILE.write_text(
            "DHAN_CLIENT_ID=\nDHAN_PIN=\nDHAN_TOTP_SECRET=\nDHAN_ACCESS_TOKEN=\n")
    load_dotenv(str(ENV_FILE), override=True)

def _save_env(k, v):
    try: set_key(str(ENV_FILE), k, v)
    except: pass

def _read_env(k):
    _ensure_env()
    return os.getenv(k, "").strip()


# ─────────────────────────────────────────────────────────────────────────────
# TIME HELPERS (exact copy from working version)
# ─────────────────────────────────────────────────────────────────────────────
def _normalize_dhan_epoch(ts):
    ts = int(ts); now_ts = int(time.time()); diff = ts - now_ts
    if int(4.5*3600) <= diff <= int(6.5*3600): ts -= 19800
    return ts

def epoch_to_ist_str(ts, fmt="%H:%M:%S"):
    if not ts: return "-"
    ts = _normalize_dhan_epoch(int(ts))
    ist = timezone(timedelta(hours=5, minutes=30))
    return datetime.fromtimestamp(ts, tz=ist).strftime(fmt)

def five_min_bucket(epoch_sec, interval_sec=300):
    epoch_sec = _normalize_dhan_epoch(int(epoch_sec))
    return epoch_sec - (epoch_sec % interval_sec)

def now_ist():
    return datetime.now(timezone(timedelta(hours=5, minutes=30)))


# ─────────────────────────────────────────────────────────────────────────────
# TOKEN MANAGER (exact copy from working version)
# ─────────────────────────────────────────────────────────────────────────────
class DhanTokenManager:
    def __init__(self, client_id, pin, totp_secret, existing=""):
        self.client_id = client_id; self.pin = pin
        self.totp_secret = totp_secret; self.existing_token = existing
        self.log_lines = []

    def _log(self, m): self.log_lines.append(m)

    def verify(self, token):
        if not token: return False
        try:
            r = requests.get(AUTH_VERIFY_URL,
                             headers={"access-token":token,"client-id":self.client_id}, timeout=10)
            return r.status_code == 200
        except: return False

    def renew(self, token):
        try:
            h = {"access-token":token,"dhanClientId":self.client_id,"Content-Type":"application/json"}
            r = requests.get(AUTH_RENEW_URL, headers=h, timeout=15)
            try: d = r.json()
            except: d = {}
            if "accessToken" in d:
                self._log(f"✅ Token renewed (exp: {d.get('expiryTime','?')})")
                return d["accessToken"]
            self._log(f"Renew failed: {d.get('errorMessage',str(d)[:100])}")
        except Exception as e: self._log(f"Renew error: {e}")
        return None

    def generate(self, max_retries=3):
        for attempt in range(max_retries):
            rem = 30 - (int(time.time()) % 30)
            if attempt > 0 or rem < 10:
                self._log(f"⏳ Waiting {rem+1}s for TOTP window...")
                time.sleep(rem + 1)
            totp = pyotp.TOTP(self.totp_secret).now()
            self._log(f"Attempt {attempt+1}: TOTP={totp}")
            try:
                params = {"dhanClientId":self.client_id,"pin":self.pin,"totp":totp}
                r = requests.post(AUTH_GENERATE_URL, params=params, timeout=15)
                try: d = r.json()
                except: d = {}
                if "accessToken" in d:
                    self._log(f"✅ Token generated (exp: {d.get('tokenExpiry','?')})")
                    return d["accessToken"]
                err = str(d.get("errorMessage") or d.get("message") or d.get("remarks") or d)
                self._log(f"Attempt {attempt+1} failed: {err}")
                if "totp" in err.lower() or "invalid" in err.lower(): continue
                return None
            except Exception as e:
                self._log(f"Exception: {e}")
                if attempt < max_retries - 1: time.sleep(2); continue
                return None
        return None

    def ensure_token(self):
        ex = self.existing_token
        if ex:
            self._log("Verifying existing token...")
            if self.verify(ex): self._log("✅ Token valid"); return ex
            self._log("Expired — trying Renew...")
            r = self.renew(ex)
            if r: _save_env("DHAN_ACCESS_TOKEN", r); return r
            self._log("Renew failed — generating via TOTP...")
        else:
            self._log("No token — generating via TOTP...")
        n = self.generate()
        if n: _save_env("DHAN_ACCESS_TOKEN", n)
        return n


# ─────────────────────────────────────────────────────────────────────────────
# REST API HELPERS (exact copy from working version)
# ─────────────────────────────────────────────────────────────────────────────
def api_post(endpoint, payload, retries=2):
    url = f"{BASE_URL}{endpoint}"
    for attempt in range(retries + 1):
        try:
            r = requests.post(url, headers=HEADERS, json=payload, timeout=15)
            if r.status_code == 200: return r.json()
        except: pass
        if attempt < retries: time.sleep(1)
    return None

def fetch_expiry_list(idx):
    cfg = INDEX_CONFIG[idx]
    resp = api_post("/optionchain/expirylist",
                    {"UnderlyingScrip":int(cfg["security_id"]),"UnderlyingSeg":"IDX_I"})
    return resp.get("data",[]) if resp and resp.get("status")=="success" else []

def get_current_week_expiry(idx):
    today = now_ist().date()
    dates = []
    for s in fetch_expiry_list(idx):
        try:
            d = datetime.strptime(s,"%Y-%m-%d").date()
            if d >= today: dates.append((d,s))
        except: continue
    dates.sort()
    return dates[0][1] if dates else None

def fetch_option_chain(idx, expiry):
    cfg = INDEX_CONFIG[idx]
    resp = api_post("/optionchain",
                    {"UnderlyingScrip":int(cfg["security_id"]),"UnderlyingSeg":"IDX_I","Expiry":expiry})
    if resp and resp.get("status")=="success":
        d = resp["data"]; return {"spot_price":float(d["last_price"]),"oc":d["oc"]}
    return None

def select_itm_strikes(idx, spot, oc_data, itm_offset=100):
    cfg = INDEX_CONFIG[idx]; gap = cfg["strike_gap"]
    atm = round(spot/gap)*gap; itm_ce = atm - itm_offset; itm_pe = atm + itm_offset
    oc = oc_data["oc"]; ce_info = pe_info = None
    for k in oc:
        try:
            kf = float(k)
            if abs(kf - itm_ce) < 0.01 and oc[k].get("ce"):
                d = oc[k]["ce"]
                ce_info = {"strike":itm_ce,"security_id":str(d["security_id"]),
                           "last_price":float(d.get("last_price",0)),"option_type":"CE"}
            if abs(kf - itm_pe) < 0.01 and oc[k].get("pe"):
                d = oc[k]["pe"]
                pe_info = {"strike":itm_pe,"security_id":str(d["security_id"]),
                           "last_price":float(d.get("last_price",0)),"option_type":"PE"}
        except: continue
    return ce_info, pe_info

def fetch_historical_5min(security_id, days_back=10, tf_minutes=5):
    to_d = now_ist().strftime("%Y-%m-%d")
    fr_d = (now_ist() - timedelta(days=days_back)).strftime("%Y-%m-%d")
    resp = api_post("/charts/intraday",
                    {"securityId":str(security_id),"exchangeSegment":"NSE_FNO",
                     "instrument":"OPTIDX","interval":str(tf_minutes),"fromDate":fr_d,"toDate":to_d})
    if not resp or "open" not in resp or not resp["open"]: return None
    df = pd.DataFrame({"timestamp":resp["timestamp"],
                        "open":[float(x) for x in resp["open"]],
                        "high":[float(x) for x in resp["high"]],
                        "low":[float(x) for x in resp["low"]],
                        "close":[float(x) for x in resp["close"]],
                        "volume":resp.get("volume",[0]*len(resp["open"]))})
    df.sort_values("timestamp",inplace=True); df.reset_index(drop=True,inplace=True)
    return df

def fetch_lot_size(idx):
    try:
        from io import StringIO
        r = requests.get("https://images.dhan.co/api-data/api-scrip-master-detailed.csv", timeout=20)
        r.raise_for_status()
        df = pd.read_csv(StringIO(r.text),
                         usecols=["SYMBOL_NAME","INSTRUMENT","SEM_LOT_UNITS"],low_memory=False)
        df = df[(df["INSTRUMENT"]=="OPTIDX")&(df["SYMBOL_NAME"]==idx)]
        if not df.empty:
            lot = int(df.iloc[0]["SEM_LOT_UNITS"])
            if lot > 0: return lot
    except: pass
    return INDEX_CONFIG[idx]["lot_size"]


# ─────────────────────────────────────────────────────────────────────────────
# EMA CALCULATOR — TradingView ta.ema() exact match
# ─────────────────────────────────────────────────────────────────────────────
class EMACalculator:
    def __init__(self, period=89):
        self.period = period; self.k = 2.0/(period+1.0)
        self.ema_high = None; self.ema_low = None; self.candle_count = 0
        self.candles = deque(maxlen=200)

    def seed_from_historical(self, df):
        self.candles.clear(); self.ema_high = self.ema_low = None; self.candle_count = 0
        for _,row in df.iterrows():
            self._proc(int(row["timestamp"]),float(row["open"]),float(row["high"]),
                       float(row["low"]),float(row["close"]),int(row.get("volume",0)))

    def _proc(self, ts, o, h, l, c, v=0):
        self.candle_count += 1
        if self.ema_high is None: self.ema_high = h; self.ema_low = l
        else:
            self.ema_high = h*self.k + self.ema_high*(1.0-self.k)
            self.ema_low  = l*self.k + self.ema_low*(1.0-self.k)
        self.candles.append({"ts":ts,"o":o,"h":h,"l":l,"c":c,"v":v,
                             "ema_h":self.ema_high,"ema_l":self.ema_low})

    def update_candle(self, ts, o, h, l, c, v=0): self._proc(ts,o,h,l,c,v)
    def is_ready(self): return self.candle_count >= self.period and self.ema_high is not None
    def get_values(self):
        return (round(self.ema_high,2) if self.ema_high else None,
                round(self.ema_low,2)  if self.ema_low  else None)
    def last_n(self, n=5): return list(self.candles)[-n:]


# ─────────────────────────────────────────────────────────────────────────────
# 5-MIN CANDLE ENGINE
# ─────────────────────────────────────────────────────────────────────────────
class FiveMinCandleEngine:
    def __init__(self, sec_id, label, on_close=None, interval_sec=300):
        self.sec_id=sec_id; self.label=label; self.on_close=on_close
        self.interval_sec=interval_sec
        self.lock=threading.Lock(); self.current=None
        self.last_ltp=None; self.last_ltt=None; self.tick_count=0

    def on_tick(self, ltp, ltt_epoch):
        ltp=float(ltp); ltt_epoch=_normalize_dhan_epoch(int(ltt_epoch))
        bucket=five_min_bucket(ltt_epoch, self.interval_sec)
        with self.lock:
            self.last_ltp=ltp; self.last_ltt=ltt_epoch; self.tick_count+=1
            if self.current is None:
                self.current={"bucket":bucket,"open":ltp,"high":ltp,"low":ltp,"close":ltp,"ticks":1}; return
            if bucket==self.current["bucket"]:
                self.current["high"]=max(self.current["high"],ltp)
                self.current["low"]=min(self.current["low"],ltp)
                self.current["close"]=ltp; self.current["ticks"]+=1; return
            if bucket > self.current["bucket"]:
                completed=dict(self.current)
                self.current={"bucket":bucket,"open":ltp,"high":ltp,"low":ltp,"close":ltp,"ticks":1}
                if self.on_close:
                    threading.Thread(target=self.on_close,args=(self.sec_id,completed),daemon=True).start()

    def snapshot(self):
        with self.lock:
            return {"label":self.label,"ltp":self.last_ltp,"ltt":self.last_ltt,
                    "current":dict(self.current) if self.current else None,"tick_count":self.tick_count}


# ─────────────────────────────────────────────────────────────────────────────
# WS PARSERS
# ─────────────────────────────────────────────────────────────────────────────
def parse_header_8(msg):
    if len(msg)<8: return None
    return {"resp_code":msg[0],"exch_seg_name":EXCH_SEG_MAP.get(msg[3],str(msg[3])),
            "security_id":str(struct.unpack_from("<I",msg,4)[0]),"payload":msg[8:]}

def parse_ticker(payload):
    if len(payload)<8: return None
    return {"ltp":float(struct.unpack_from("<f",payload,0)[0]),
            "ltt_epoch":int(struct.unpack_from("<I",payload,4)[0])}


# ─────────────────────────────────────────────────────────────────────────────
# TRADE
# ─────────────────────────────────────────────────────────────────────────────
class Trade:
    def __init__(self, index, option_type, strike, security_id,
                 entry_price, entry_time, target, stop_loss, lot_size):
        self.index=index; self.option_type=option_type; self.strike=strike
        self.security_id=security_id; self.entry_price=entry_price
        self.entry_time=entry_time; self.target=target; self.stop_loss=stop_loss
        self.lot_size=lot_size; self.current_ltp=None; self.pnl=0.0
        self.exit_price=None; self.exit_time=None; self.exit_reason=None; self.is_open=True


# ─────────────────────────────────────────────────────────────────────────────
# STRATEGY ENGINE (headless — talks to GUI via Queue)
# ─────────────────────────────────────────────────────────────────────────────
class StrategyEngine:
    def __init__(self, indices, log_q, params=None):
        self.indices=indices; self.log_q=log_q; self.stop_event=threading.Event()
        # User-configurable params
        p = params or {}
        self.ema_period    = p.get("ema_period", DEFAULT_EMA_PERIOD)
        self.candle_tf_min = p.get("candle_tf", DEFAULT_CANDLE_TF)
        self.candle_tf_sec = TF_OPTIONS.get(str(self.candle_tf_min), self.candle_tf_min * 60)
        self.target_points = p.get("target_points", DEFAULT_TARGET_POINTS)
        self.itm_offset    = p.get("itm_offset", DEFAULT_ITM_OFFSET)
        self.qty_mult      = p.get("qty_mult", DEFAULT_QTY_MULT)

        self.expiry={}; self.spot_price={}; self.lot_sizes={}
        self.ce_info={}; self.pe_info={}
        self.ema_calcs={}; self.ema_label={}
        self.candle_engines={}; self.spot_engines={}
        self.trades_lock=threading.Lock()
        self.active_trades: Dict[str,Trade]={}
        self.completed_trades: List[Trade]=[]
        self.needs_refresh={}
        self.ws=None; self.ws_connected=threading.Event()
        self.ws_instruments=[]; self.packet_count=0; self.last_ws_error=None

    def log(self, msg):
        ts = now_ist().strftime("%H:%M:%S")
        self.log_q.put(f"[{ts}] {msg}")

    def initialize(self):
        self.log(f"═══ Params: EMA={self.ema_period}  TF={self.candle_tf_min}m  "
                 f"Target={self.target_points}pts  ITM={self.itm_offset}  QtyMult={self.qty_mult}x ═══")
        for idx in self.indices:
            self.log(f"[{idx}] Initializing...")
            base_lot = fetch_lot_size(idx)
            self.lot_sizes[idx] = base_lot * self.qty_mult
            self.log(f"[{idx}] Lot: {base_lot} × {self.qty_mult} = {self.lot_sizes[idx]}")
            exp = get_current_week_expiry(idx)
            if not exp: self.log(f"[{idx}] ❌ No expiry"); continue
            self.expiry[idx] = exp
            self.log(f"[{idx}] Expiry: {exp}")
            self._select_strikes(idx)
        return bool(self.ws_instruments)

    def _select_strikes(self, idx):
        exp = self.expiry.get(idx)
        if not exp: return
        oc = fetch_option_chain(idx, exp)
        if not oc: self.log(f"[{idx}] ❌ Option chain failed"); return
        spot = oc["spot_price"]; self.spot_price[idx] = spot
        self.log(f"[{idx}] Spot: {spot:.2f}")
        ce, pe = select_itm_strikes(idx, spot, oc, itm_offset=self.itm_offset)
        self.ce_info[idx]=ce; self.pe_info[idx]=pe
        if ce:
            self.log(f"[{idx}] CE: {int(ce['strike'])} | secId={ce['security_id']} | LTP={ce['last_price']:.2f}")
            self._setup_option(idx,ce,"CE")
        if pe:
            self.log(f"[{idx}] PE: {int(pe['strike'])} | secId={pe['security_id']} | LTP={pe['last_price']:.2f}")
            self._setup_option(idx,pe,"PE")
        self.needs_refresh[idx] = False

    def _setup_option(self, idx, info, opt_type):
        sec_id=info["security_id"]; label=f"{idx} {int(info['strike'])}{opt_type}"
        self.ema_label[sec_id]=label
        self.log(f"  Fetching history for {label}...")
        df = fetch_historical_5min(sec_id, days_back=10, tf_minutes=self.candle_tf_min)
        ema = EMACalculator(self.ema_period)
        if df is not None and len(df)>0:
            now_epoch=int(time.time()); cb=five_min_bucket(now_epoch, self.candle_tf_sec)
            if len(df)>1 and int(df.iloc[-1]["timestamp"])>=cb:
                df=df.iloc[:-1].copy()
            ema.seed_from_historical(df)
            eh,el=ema.get_values()
            self.log(f"  {label}: {len(df)} candles | EMA_H={eh} | EMA_L={el} | Ready={ema.is_ready()}")
        else:
            self.log(f"  {label}: No history — building from live")
        self.ema_calcs[sec_id]=ema
        self.candle_engines[sec_id]=FiveMinCandleEngine(sec_id,label,
            on_close=self.on_candle_close, interval_sec=self.candle_tf_sec)
        self.ws_instruments.append({"name":label,"exchange":"NSE_FNO","security_id":sec_id})

    # ── STRATEGY LOGIC ──
    def on_candle_close(self, sec_id, candle):
        ema = self.ema_calcs.get(sec_id)
        if not ema: return
        o,h,l,c = float(candle["open"]),float(candle["high"]),float(candle["low"]),float(candle["close"])
        ts = int(candle["bucket"])
        ema.update_candle(ts,o,h,l,c)
        if not ema.is_ready(): return
        ema_h,ema_l = ema.get_values()
        label = self.ema_label.get(sec_id,sec_id)
        t_str = epoch_to_ist_str(ts,"%H:%M")
        self.log(f"[{t_str}] {label}  O={o:.2f} H={h:.2f} L={l:.2f} C={c:.2f} | EMA_H={ema_h} EMA_L={ema_l}")

        with self.trades_lock:
            if sec_id in self.active_trades:
                trade = self.active_trades[sec_id]
                if trade.is_open:
                    old_sl=trade.stop_loss; trade.stop_loss=ema_l; trade.current_ltp=c
                    if c>=trade.target:
                        self._close_trade(trade,c,"TARGET HIT"); del self.active_trades[sec_id]
                        self._flag_refresh(sec_id); return
                    if c<=ema_l:
                        self._close_trade(trade,c,"SL HIT (EMA Low)"); del self.active_trades[sec_id]
                        self._flag_refresh(sec_id); return
                    if old_sl!=trade.stop_loss:
                        self.log(f"  ↳ Trailing SL: {old_sl:.2f} → {trade.stop_loss:.2f}")
                return
            if c > ema_h:
                for idx_name in self.indices:
                    ci=self.ce_info.get(idx_name); pi=self.pe_info.get(idx_name); info=None
                    if ci and ci["security_id"]==sec_id: info=ci
                    elif pi and pi["security_id"]==sec_id: info=pi
                    if info:
                        trade=Trade(index=idx_name,option_type=info["option_type"],
                                    strike=info["strike"],security_id=sec_id,entry_price=c,
                                    entry_time=epoch_to_ist_str(ts,"%H:%M:%S"),
                                    target=c+self.target_points,stop_loss=ema_l,
                                    lot_size=self.lot_sizes.get(idx_name,INDEX_CONFIG[idx_name]["lot_size"]))
                        self.active_trades[sec_id]=trade
                        self.log(f"▶ ENTRY  {idx_name} {int(info['strike'])}{info['option_type']}  "
                                 f"@ ₹{c:.2f}  TGT=₹{trade.target:.2f}  SL=₹{ema_l:.2f}  Qty={trade.lot_size}")
                        break

    def _close_trade(self, trade, exit_price, reason):
        trade.exit_price=exit_price; trade.exit_time=now_ist().strftime("%H:%M:%S")
        trade.exit_reason=reason; trade.pnl=(exit_price-trade.entry_price)*trade.lot_size
        trade.is_open=False; self.completed_trades.append(trade)
        icon = "🟢" if trade.pnl>=0 else "🔴"
        self.log(f"◼ EXIT  {trade.index} {int(trade.strike)}{trade.option_type}  "
                 f"₹{trade.entry_price:.2f}→₹{exit_price:.2f}  {icon} ₹{trade.pnl:+.2f}  ({reason})")
        self._save_csv(trade)

    def _flag_refresh(self, sec_id):
        for idx in self.indices:
            ci=self.ce_info.get(idx); pi=self.pe_info.get(idx)
            if (ci and ci["security_id"]==sec_id) or (pi and pi["security_id"]==sec_id):
                self.needs_refresh[idx]=True

    def _save_csv(self, t):
        exists = LOG_CSV.exists()
        try:
            with open(str(LOG_CSV),"a",newline="") as f:
                w=csv.writer(f)
                if not exists: w.writerow(["Date","Index","Strike","Type","Entry","Exit",
                                           "EntryTime","ExitTime","PnL","Qty","Reason"])
                w.writerow([now_ist().strftime("%Y-%m-%d"),t.index,int(t.strike),t.option_type,
                            f"{t.entry_price:.2f}",f"{t.exit_price:.2f}",t.entry_time,t.exit_time,
                            f"{t.pnl:.2f}",t.lot_size,t.exit_reason])
        except: pass

    def check_refresh(self):
        for idx in self.indices:
            if not self.needs_refresh.get(idx): continue
            self.log(f"🔄 Refreshing strikes for {idx}...")
            old_sids=set()
            for info in [self.ce_info.get(idx),self.pe_info.get(idx)]:
                if info:
                    sid=info["security_id"]; old_sids.add(sid)
                    self.candle_engines.pop(sid,None); self.ema_calcs.pop(sid,None)
                    self.ema_label.pop(sid,None)
            self.ws_instruments=[i for i in self.ws_instruments if i["security_id"] not in old_sids]
            self._select_strikes(idx)
            if self.ws and self.ws_connected.is_set():
                new_instr=[i for i in self.ws_instruments if i["security_id"] not in old_sids]
                if new_instr:
                    sub={"RequestCode":REQ_SUB_TICKER,"InstrumentCount":len(new_instr),
                         "InstrumentList":[{"ExchangeSegment":str(i["exchange"]),
                                            "SecurityId":str(i["security_id"])} for i in new_instr]}
                    try: self.ws.send(json.dumps(sub)); self.log("✅ Subscribed new strikes")
                    except Exception as e: self.log(f"WS resub error: {e}")

    # ── WEBSOCKET ──
    def on_ws_open(self, ws):
        self.ws_connected.set()
        spot_instr=[{"ExchangeSegment":"IDX_I","SecurityId":INDEX_CONFIG[idx]["security_id"]}
                    for idx in self.indices]
        for idx in self.indices:
            self.spot_engines[idx]=FiveMinCandleEngine(INDEX_CONFIG[idx]["security_id"],f"{idx} SPOT")
        opt_instr=[{"ExchangeSegment":str(i["exchange"]),"SecurityId":str(i["security_id"])}
                   for i in self.ws_instruments]
        all_i=spot_instr+opt_instr
        ws.send(json.dumps({"RequestCode":REQ_SUB_TICKER,"InstrumentCount":len(all_i),"InstrumentList":all_i}))
        self.log(f"📡 WebSocket connected — {len(all_i)} instruments")

    def on_ws_message(self, ws, message):
        if isinstance(message,str): return
        msg=bytes(message); hdr=parse_header_8(msg)
        if not hdr: return
        code=int(hdr["resp_code"]); sec_id=str(hdr["security_id"]); self.packet_count+=1
        if code==RESP_TICKER:
            t=parse_ticker(hdr["payload"])
            if not t: return
            ltp=float(t["ltp"]); ltt=int(t["ltt_epoch"])
            for idx in self.indices:
                if sec_id==INDEX_CONFIG[idx]["security_id"]: self.spot_price[idx]=ltp
            if sec_id in self.candle_engines:
                self.candle_engines[sec_id].on_tick(ltp,ltt)
                with self.trades_lock:
                    if sec_id in self.active_trades:
                        trade=self.active_trades[sec_id]; trade.current_ltp=ltp
                        if ltp>=trade.target and trade.is_open:
                            self._close_trade(trade,ltp,"TARGET HIT (tick)")
                            del self.active_trades[sec_id]; self._flag_refresh(sec_id)

    def on_ws_error(self, ws, error): self.last_ws_error=str(error)
    def on_ws_close(self, ws, sc, msg): self.ws_connected.clear()

    def run_ws(self):
        websocket.enableTrace(False)
        while not self.stop_event.is_set():
            try:
                self.ws=websocket.WebSocketApp(WS_URL,on_open=self.on_ws_open,
                    on_message=self.on_ws_message,on_error=self.on_ws_error,on_close=self.on_ws_close)
                self.ws.run_forever(ping_interval=20,ping_timeout=10)
            except: pass
            if not self.stop_event.is_set(): time.sleep(2)

    def run(self):
        if not self.initialize(): self.log("❌ No instruments"); return
        threading.Thread(target=self.run_ws,daemon=True).start()
        self.ws_connected.wait(timeout=15)
        if not self.ws_connected.is_set(): self.log("❌ WS connect failed"); return
        self.log("✅ Live — monitoring for EMA breakout signals...")
        while not self.stop_event.is_set():
            try: self.check_refresh(); time.sleep(1)
            except Exception as e: self.log(f"Error: {e}"); time.sleep(1)

    def stop(self):
        self.stop_event.set()
        if self.ws:
            try: self.ws.close()
            except: pass

    def get_snapshot(self):
        opts=[]
        for sec_id,eng in self.candle_engines.items():
            snap=eng.snapshot(); ema=self.ema_calcs.get(sec_id)
            eh,el=ema.get_values() if ema else (None,None)
            with self.trades_lock: in_t=sec_id in self.active_trades
            opts.append({"label":snap["label"],"ltp":snap["ltp"],"ema_h":eh,"ema_l":el,
                         "ticks":snap["tick_count"],"in_trade":in_t,
                         "ready":ema.is_ready() if ema else False,
                         "candle_count":ema.candle_count if ema else 0})
        active=[]
        with self.trades_lock:
            for sid,t in self.active_trades.items():
                ltp=t.current_ltp or t.entry_price; unr=(ltp-t.entry_price)*t.lot_size
                active.append({"label":f"{t.index} {int(t.strike)}{t.option_type}",
                               "entry":t.entry_price,"ltp":ltp,"target":t.target,
                               "sl":t.stop_loss,"pnl":unr,"qty":t.lot_size,"entry_time":t.entry_time})
        total=sum(t.pnl for t in self.completed_trades)
        wins=sum(1 for t in self.completed_trades if t.pnl>0)
        return {"spots":dict(self.spot_price),"expiries":dict(self.expiry),
                "lots":dict(self.lot_sizes),"options":opts,"active":active,
                "completed":self.completed_trades[-15:],"total_pnl":total,
                "wins":wins,"total_trades":len(self.completed_trades),
                "packets":self.packet_count,"ws_ok":self.ws_connected.is_set(),
                "ws_err":self.last_ws_error,"ema_period":self.ema_period}


# ═════════════════════════════════════════════════════════════════════════════
#  GUI — HELPER WIDGETS
# ═════════════════════════════════════════════════════════════════════════════
class GlowLabel(ctk.CTkLabel):
    """Label with a coloured left border accent."""
    pass

def make_card(parent, **kw):
    return ctk.CTkFrame(parent, fg_color=BG_CARD, corner_radius=14,
                        border_width=1, border_color=BORDER, **kw)

def make_pill(parent, text, fg=TEAL, bg=BG_DEEP):
    f = ctk.CTkFrame(parent, fg_color=bg, corner_radius=12, height=28)
    ctk.CTkLabel(f, text=text, font=F_SMALL, text_color=fg).pack(padx=10, pady=2)
    return f


# ═════════════════════════════════════════════════════════════════════════════
#  TOKEN MANAGER TAB
# ═════════════════════════════════════════════════════════════════════════════
class TokenTab(ctk.CTkFrame):
    def __init__(self, master, on_ready):
        super().__init__(master, fg_color=BG_DEEP)
        self.on_ready = on_ready
        self._build()
        self._load()

    def _build(self):
        # ── header strip ──
        hdr = ctk.CTkFrame(self, fg_color=BG_PANEL, corner_radius=0, height=64)
        hdr.pack(fill="x"); hdr.pack_propagate(False)
        ctk.CTkLabel(hdr, text="  Dhan API Credentials", font=F_TITLE,
                     text_color=TEAL).pack(side="left", padx=20, pady=14)
        make_pill(hdr, "Saved locally in .env", fg=GREY, bg=BG_CARD).pack(
            side="right", padx=20, pady=18)

        # ── credential card ──
        card = make_card(self)
        card.pack(padx=40, pady=(30, 15), fill="x")

        self.entries = {}
        fields = [("Client ID", "cid", False), ("6-Digit PIN", "pin", True),
                  ("TOTP Secret", "totp", False)]
        for i, (lbl, key, hide) in enumerate(fields):
            row = ctk.CTkFrame(card, fg_color="transparent")
            row.pack(fill="x", padx=24, pady=(16 if i == 0 else 8, 0))
            ctk.CTkLabel(row, text=lbl, font=F_BODY, text_color=GREY_LT, width=140,
                         anchor="w").pack(side="left")
            e = ctk.CTkEntry(row, height=40, font=F_MONO, fg_color=BG_INPUT,
                             border_color=BORDER, text_color=WHITE, corner_radius=8,
                             show="●" if hide else "")
            e.pack(side="left", fill="x", expand=True, padx=(8, 0))
            self.entries[key] = e

        # ── buttons ──
        btn_row = ctk.CTkFrame(card, fg_color="transparent")
        btn_row.pack(fill="x", padx=24, pady=(20, 20))

        ctk.CTkButton(btn_row, text="💾  Save", font=F_BTN, width=150, height=42,
                      corner_radius=10, fg_color=EMERALD_DIM, hover_color=EMERALD,
                      text_color=WHITE, command=self._save).pack(side="left", padx=(0, 10))
        ctk.CTkButton(btn_row, text="🔐  Authenticate", font=F_BTN, width=180, height=42,
                      corner_radius=10, fg_color=TEAL_DIM, hover_color=TEAL,
                      text_color=BG_DEEP, command=self._auth).pack(side="left")
        self.status = ctk.CTkLabel(btn_row, text="", font=F_SMALL, text_color=GREY)
        self.status.pack(side="left", padx=15)

        # ── log ──
        self.log_box = ctk.CTkTextbox(self, height=180, font=F_MONO_S, fg_color=BG_PANEL,
                                       text_color=GREY, corner_radius=10,
                                       border_color=BORDER, border_width=1, state="disabled")
        self.log_box.pack(fill="x", padx=40, pady=(0, 30))

    def _load(self):
        _ensure_env()
        self.entries["cid"].insert(0, _read_env("DHAN_CLIENT_ID"))
        self.entries["pin"].insert(0, _read_env("DHAN_PIN"))
        self.entries["totp"].insert(0, _read_env("DHAN_TOTP_SECRET"))

    def _save(self):
        cid=self.entries["cid"].get().strip(); pin=self.entries["pin"].get().strip()
        totp=self.entries["totp"].get().strip()
        if not all([cid,pin,totp]):
            self.status.configure(text="❌ All fields required", text_color=RED); return
        _save_env("DHAN_CLIENT_ID",cid); _save_env("DHAN_PIN",pin); _save_env("DHAN_TOTP_SECRET",totp)
        self.status.configure(text="✅ Saved", text_color=EMERALD)

    def _auth(self):
        cid=self.entries["cid"].get().strip(); pin=self.entries["pin"].get().strip()
        totp_s=self.entries["totp"].get().strip()
        if not all([cid,pin,totp_s]):
            self.status.configure(text="❌ Save first", text_color=RED); return
        self.status.configure(text="⏳ Authenticating...", text_color=AMBER)
        self._logmsg("Starting authentication...")

        def _run():
            mgr=DhanTokenManager(cid,pin,totp_s,_read_env("DHAN_ACCESS_TOKEN"))
            token=mgr.ensure_token()
            for line in mgr.log_lines: self._logmsg(line)
            if token:
                global HEADERS, WS_URL
                HEADERS.update({"Content-Type":"application/json","Accept":"application/json",
                                "access-token":token,"client-id":cid})
                WS_URL=f"wss://api-feed.dhan.co?version=2&token={token}&clientId={cid}&authType=2"
                self.status.configure(text="✅ Token ready — go to Strategy tab", text_color=EMERALD)
                self._logmsg("✅ Authenticated!")
                if self.on_ready: self.on_ready()
            else:
                self.status.configure(text="❌ Failed — see log", text_color=RED)
                self._logmsg("❌ Auth failed")
        threading.Thread(target=_run, daemon=True).start()

    def _logmsg(self, msg):
        try:
            self.log_box.configure(state="normal")
            self.log_box.insert("end", msg+"\n"); self.log_box.see("end")
            self.log_box.configure(state="disabled")
        except: pass


# ═════════════════════════════════════════════════════════════════════════════
#  STRATEGY DASHBOARD TAB
# ═════════════════════════════════════════════════════════════════════════════
class StrategyTab(ctk.CTkFrame):
    def __init__(self, master):
        super().__init__(master, fg_color=BG_DEEP)
        self.engine = None; self.log_q = Queue(); self.running = False
        self._build()

    def _build(self):
        # ── TOP BAR ──
        top = ctk.CTkFrame(self, fg_color=BG_PANEL, corner_radius=0, height=64)
        top.pack(fill="x"); top.pack_propagate(False)

        ctk.CTkLabel(top, text="  Strategy Dashboard", font=F_TITLE,
                     text_color=TEAL).pack(side="left", padx=20)

        ctrl = ctk.CTkFrame(top, fg_color="transparent")
        ctrl.pack(side="right", padx=20)

        ctk.CTkLabel(ctrl, text="Index", font=F_SMALL, text_color=GREY).pack(side="left", padx=(0,4))
        self.idx_var = ctk.StringVar(value="NIFTY")
        ctk.CTkSegmentedButton(ctrl, values=["NIFTY","BANKNIFTY","BOTH"],
                               variable=self.idx_var, font=F_SMALL, height=32,
                               fg_color=BG_CARD, selected_color=TEAL_DIM,
                               selected_hover_color=TEAL,
                               unselected_color=BG_CARD,
                               unselected_hover_color=BG_CARD_HI,
                               text_color=WHITE).pack(side="left", padx=(0,12))
        self.start_btn = ctk.CTkButton(ctrl, text="▶  Start", font=F_BTN,
                                        width=120, height=36, corner_radius=10,
                                        fg_color=EMERALD_DIM, hover_color=EMERALD,
                                        text_color=WHITE, command=self._toggle)
        self.start_btn.pack(side="left")

        # ── SETTINGS PANEL ──
        settings = ctk.CTkFrame(self, fg_color=BG_CARD, corner_radius=12,
                                border_width=1, border_color=BORDER)
        settings.pack(fill="x", padx=12, pady=(8, 0))

        stitle = ctk.CTkFrame(settings, fg_color="transparent")
        stitle.pack(fill="x", padx=14, pady=(10, 6))
        ctk.CTkLabel(stitle, text="⚙  Parameters", font=F_HEAD,
                     text_color=GREY_LT).pack(side="left")

        sparams = ctk.CTkFrame(settings, fg_color="transparent")
        sparams.pack(fill="x", padx=14, pady=(0, 12))

        # EMA Period
        self.ema_var = ctk.StringVar(value=str(DEFAULT_EMA_PERIOD))
        self._param_field(sparams, "EMA Period", self.ema_var,
                          ["21", "50", "89", "144", "200"], 0)

        # Candle TF
        self.tf_var = ctk.StringVar(value=str(DEFAULT_CANDLE_TF))
        self._param_field(sparams, "Candle TF (min)", self.tf_var,
                          ["1", "3", "5", "15"], 1)

        # Target Points
        self.tgt_var = ctk.StringVar(value=str(int(DEFAULT_TARGET_POINTS)))
        self._param_field(sparams, "Target (pts)", self.tgt_var,
                          ["5", "10", "15", "20", "25", "30"], 2)

        # ITM Offset
        self.itm_var = ctk.StringVar(value=str(DEFAULT_ITM_OFFSET))
        self._param_field(sparams, "ITM Offset", self.itm_var,
                          ["50", "100", "150", "200", "300"], 3)

        # Qty Multiplier
        self.qty_var = ctk.StringVar(value=str(DEFAULT_QTY_MULT))
        self._param_field(sparams, "Qty Multiplier", self.qty_var,
                          ["1", "2", "3", "5", "10"], 4)

        # ── SCROLLABLE BODY ──
        body = ctk.CTkScrollableFrame(self, fg_color=BG_DEEP)
        body.pack(fill="both", expand=True, padx=12, pady=(8, 0))

        # ── STATUS ROW ──
        sr = ctk.CTkFrame(body, fg_color=BG_CARD, corner_radius=12, height=44,
                          border_width=1, border_color=BORDER)
        sr.pack(fill="x", pady=(0,8)); sr.pack_propagate(False)

        self.ws_dot = ctk.CTkLabel(sr, text="●", font=("Segoe UI",14), text_color=RED)
        self.ws_dot.pack(side="left", padx=(14,4))
        self.ws_lbl = ctk.CTkLabel(sr, text="Offline", font=F_SMALL, text_color=GREY)
        self.ws_lbl.pack(side="left", padx=(0,16))

        self.spot_lbls = {}
        for idx in ["NIFTY","BANKNIFTY"]:
            lbl = ctk.CTkLabel(sr, text=f"{idx}: —", font=F_BODY, text_color=WHITE)
            lbl.pack(side="left", padx=14)
            self.spot_lbls[idx] = lbl

        self.pkt_lbl = ctk.CTkLabel(sr, text="", font=F_SMALL, text_color=GREY_DK)
        self.pkt_lbl.pack(side="right", padx=14)

        # ── OPTION CARDS CONTAINER ──
        self.opt_frame = ctk.CTkFrame(body, fg_color="transparent")
        self.opt_frame.pack(fill="x", pady=(0,8))

        # ── ACTIVE TRADE ──
        self.trade_card = make_card(body)
        self.trade_card.pack(fill="x", pady=(0,8))
        self.trade_hdr = ctk.CTkLabel(self.trade_card, text="  No Active Trade",
                                       font=F_HEAD, text_color=GREY_DK)
        self.trade_hdr.pack(anchor="w", padx=16, pady=(12,2))
        self.trade_body = ctk.CTkLabel(self.trade_card, text="", font=F_MONO,
                                        text_color=WHITE)
        self.trade_body.pack(anchor="w", padx=16, pady=(0,12))

        # ── STATS ROW ──
        stats_row = ctk.CTkFrame(body, fg_color="transparent")
        stats_row.pack(fill="x", pady=(0,8))
        stats_row.columnconfigure((0,1,2), weight=1)

        self.pnl_lbl = self._stat_card(stats_row, "Session P&L", "₹0.00", 0)
        self.win_lbl = self._stat_card(stats_row, "Wins / Total", "0 / 0", 1)
        self.wr_lbl  = self._stat_card(stats_row, "Win Rate", "—", 2)

        # ── TRADE HISTORY ──
        hist_card = make_card(body)
        hist_card.pack(fill="x", pady=(0,8))
        ctk.CTkLabel(hist_card, text="  Recent Trades", font=F_HEAD,
                     text_color=GREY_LT).pack(anchor="w", padx=16, pady=(12,4))
        self.hist_box = ctk.CTkTextbox(hist_card, height=100, font=F_MONO_S,
                                        fg_color=BG_INPUT, text_color=GREY_LT,
                                        corner_radius=8, state="disabled")
        self.hist_box.pack(fill="x", padx=16, pady=(0,12))

        # ── LOG ──
        log_card = make_card(body)
        log_card.pack(fill="x", pady=(0,12))
        ctk.CTkLabel(log_card, text="  Event Log", font=F_HEAD,
                     text_color=GREY_LT).pack(anchor="w", padx=16, pady=(12,4))
        self.log_box = ctk.CTkTextbox(log_card, height=180, font=F_MONO_S,
                                       fg_color=BG_INPUT, text_color=GREY,
                                       corner_radius=8, state="disabled")
        self.log_box.pack(fill="x", padx=16, pady=(0,12))

    def _param_field(self, parent, label, var, options, col):
        f = ctk.CTkFrame(parent, fg_color="transparent")
        f.pack(side="left", padx=(0, 16), fill="x", expand=True)
        ctk.CTkLabel(f, text=label, font=F_SMALL, text_color=GREY).pack(anchor="w")
        ctk.CTkOptionMenu(f, variable=var, values=options, font=F_MONO,
                          width=100, height=30, fg_color=BG_INPUT,
                          button_color=TEAL_DIM, button_hover_color=TEAL,
                          dropdown_fg_color=BG_CARD, dropdown_hover_color=BG_CARD_HI,
                          text_color=WHITE, corner_radius=8).pack(anchor="w", pady=(2, 0))

    def _stat_card(self, parent, title, value, col):
        c = make_card(parent, height=85)
        c.grid(row=0, column=col, sticky="nsew", padx=(0 if col==0 else 6, 0))
        c.pack_propagate(False)
        ctk.CTkLabel(c, text=title, font=F_SMALL, text_color=GREY).pack(
            anchor="w", padx=16, pady=(12,0))
        lbl = ctk.CTkLabel(c, text=value, font=F_BIG, text_color=WHITE)
        lbl.pack(anchor="w", padx=16, pady=(2,0))
        return lbl

    def _toggle(self):
        if not self.running: self._start()
        else: self._stop()

    def _start(self):
        if not HEADERS:
            self._log("❌ Authenticate first (Credentials tab)")
            return
        choice = self.idx_var.get()
        indices = ["NIFTY","BANKNIFTY"] if choice=="BOTH" else [choice]

        # Read params from GUI
        params = {
            "ema_period":    int(self.ema_var.get()),
            "candle_tf":     int(self.tf_var.get()),
            "target_points": float(self.tgt_var.get()),
            "itm_offset":    int(self.itm_var.get()),
            "qty_mult":      int(self.qty_var.get()),
        }

        self.engine = StrategyEngine(indices, self.log_q, params=params)
        self.running = True
        self.start_btn.configure(text="◼  Stop", fg_color=RED_DIM, hover_color=RED)
        threading.Thread(target=self.engine.run, daemon=True).start()
        self._poll()

    def _stop(self):
        if self.engine: self.engine.stop()
        self.running = False
        self.start_btn.configure(text="▶  Start", fg_color=EMERALD_DIM, hover_color=EMERALD)

    def _poll(self):
        try:
            while True:
                msg = self.log_q.get_nowait()
                self._log(msg)
        except Empty: pass

        if self.engine and self.running:
            try: self._refresh(self.engine.get_snapshot())
            except: pass

        if self.running: self.after(500, self._poll)

    def _refresh(self, d):
        # WS
        if d["ws_ok"]:
            self.ws_dot.configure(text_color=EMERALD); self.ws_lbl.configure(text="Live", text_color=EMERALD)
        else:
            self.ws_dot.configure(text_color=RED); self.ws_lbl.configure(text="Offline", text_color=RED)

        # Spots
        for idx in ["NIFTY","BANKNIFTY"]:
            s=d["spots"].get(idx); exp=d["expiries"].get(idx,""); lot=d["lots"].get(idx,"")
            if s: self.spot_lbls[idx].configure(text=f"{idx}  {s:.2f}   Exp:{exp}  Lot:{lot}")
            else: self.spot_lbls[idx].configure(text=f"{idx}: —")

        self.pkt_lbl.configure(text=f"Pkts: {d['packets']:,}")

        # Option cards
        for w in self.opt_frame.winfo_children(): w.destroy()
        for opt in d["options"]:
            c = ctk.CTkFrame(self.opt_frame, fg_color=BG_CARD_HI if opt["in_trade"] else BG_CARD,
                             corner_radius=12, border_width=1,
                             border_color=TEAL if opt["in_trade"] else BORDER, height=72)
            c.pack(side="left", padx=(0,6), fill="x", expand=True)
            c.pack_propagate(False)

            # Top row: label + status pill
            top_r = ctk.CTkFrame(c, fg_color="transparent")
            top_r.pack(fill="x", padx=14, pady=(10,0))
            ctk.CTkLabel(top_r, text=opt["label"], font=F_HEAD,
                         text_color=TEAL if opt["in_trade"] else WHITE).pack(side="left")
            if opt["in_trade"]:
                make_pill(top_r, "IN TRADE", fg=BG_DEEP, bg=TEAL).pack(side="right")
            elif opt["ready"]:
                make_pill(top_r, "watching", fg=GREY, bg=BG_CARD).pack(side="right")
            else:
                make_pill(top_r, f"warmup {opt['candle_count']}/{d.get('ema_period', DEFAULT_EMA_PERIOD)}",
                         fg=AMBER, bg=BG_CARD).pack(side="right")

            # Bottom row: LTP + EMAs
            ltp_s = f"₹{opt['ltp']:.2f}" if opt['ltp'] else "—"
            eh_s = f"{opt['ema_h']:.2f}" if opt['ema_h'] else "..."
            el_s = f"{opt['ema_l']:.2f}" if opt['ema_l'] else "..."
            det = f"LTP {ltp_s}  ·  EMA↑ {eh_s}  ·  EMA↓ {el_s}  ·  {opt['ticks']} ticks"
            ctk.CTkLabel(c, text=det, font=F_MONO_S,
                         text_color=TEAL_DIM if opt["in_trade"] else GREY).pack(
                anchor="w", padx=14, pady=(2,0))

        # Active trade
        if d["active"]:
            t=d["active"][0]; pnl_col=EMERALD if t["pnl"]>=0 else RED
            self.trade_hdr.configure(text=f"  ▶  {t['label']}   Qty: {t['qty']}   Entry @ {t['entry_time']}",
                                      text_color=TEAL)
            self.trade_body.configure(
                text=f"  Entry ₹{t['entry']:.2f}   LTP ₹{t['ltp']:.2f}   "
                     f"Target ₹{t['target']:.2f}   SL ₹{t['sl']:.2f}   "
                     f"P&L ₹{t['pnl']:+.2f}", text_color=pnl_col)
        else:
            self.trade_hdr.configure(text="  No Active Trade", text_color=GREY_DK)
            self.trade_body.configure(text="")

        # Stats
        tp=d["total_pnl"]; pnl_col=EMERALD if tp>=0 else RED
        self.pnl_lbl.configure(text=f"₹{tp:+,.2f}", text_color=pnl_col)
        self.win_lbl.configure(text=f"{d['wins']} / {d['total_trades']}")
        wr=(d['wins']/d['total_trades']*100) if d['total_trades']>0 else 0
        self.wr_lbl.configure(text=f"{wr:.0f}%", text_color=EMERALD if wr>=50 else AMBER)

        # Trade history
        self.hist_box.configure(state="normal"); self.hist_box.delete("1.0","end")
        for t in reversed(d["completed"]):
            icon="🟢" if t.pnl>=0 else "🔴"
            self.hist_box.insert("end",
                f"{icon} {t.index} {int(t.strike)}{t.option_type}  "
                f"₹{t.entry_price:.2f}→₹{t.exit_price:.2f}  "
                f"₹{t.pnl:+.2f}  {t.exit_reason}  ({t.entry_time}→{t.exit_time})\n")
        self.hist_box.configure(state="disabled")

    def _log(self, msg):
        try:
            self.log_box.configure(state="normal")
            self.log_box.insert("end", msg+"\n"); self.log_box.see("end")
            self.log_box.configure(state="disabled")
        except: pass


# ═════════════════════════════════════════════════════════════════════════════
#  MAIN APP
# ═════════════════════════════════════════════════════════════════════════════
class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("Balfund — EMA Breakout Options")
        self.geometry("1120x800")
        self.minsize(960, 680)
        self.configure(fg_color=BG_DEEP)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        # ── SIDEBAR ──
        sb = ctk.CTkFrame(self, fg_color=BG_PANEL, width=210, corner_radius=0,
                          border_width=0)
        sb.pack(side="left", fill="y"); sb.pack_propagate(False)

        # Brand
        brand_frame = ctk.CTkFrame(sb, fg_color="transparent")
        brand_frame.pack(fill="x", padx=16, pady=(24,0))
        ctk.CTkLabel(brand_frame, text="BALFUND", font=F_BRAND,
                     text_color=TEAL).pack(anchor="w")
        ctk.CTkLabel(brand_frame, text="TRADING PVT. LTD.", font=F_SMALL,
                     text_color=GREY_DK).pack(anchor="w", pady=(0,2))

        # Separator
        ctk.CTkFrame(sb, fg_color=BORDER, height=1).pack(fill="x", padx=16, pady=(16,12))

        # Strategy info
        info_frame = ctk.CTkFrame(sb, fg_color=BG_CARD, corner_radius=10)
        info_frame.pack(fill="x", padx=12, pady=(0,12))
        for line in ["EMA Breakout (High/Low)", "Configurable TF & Params", "Trailing SL · Auto Refresh"]:
            ctk.CTkLabel(info_frame, text=line, font=F_SMALL,
                         text_color=GREY_LT).pack(anchor="w", padx=12, pady=(4,0))
        ctk.CTkLabel(info_frame, text="", font=F_SMALL).pack(pady=(0,6))

        # Nav buttons
        self.nav_btns = {}
        for name, icon in [("Credentials", "🔑"), ("Strategy", "📊")]:
            btn = ctk.CTkButton(sb, text=f"  {icon}   {name}", font=F_BODY,
                                fg_color="transparent", hover_color=BG_CARD,
                                text_color=WHITE, anchor="w", height=42,
                                corner_radius=10,
                                command=lambda n=name: self._switch(n))
            btn.pack(fill="x", padx=10, pady=2)
            self.nav_btns[name] = btn

        # Footer
        ctk.CTkFrame(sb, fg_color=BORDER, height=1).pack(fill="x", padx=16, pady=8, side="bottom")
        make_pill(sb, "PAPER TRADE", fg=AMBER, bg=BG_CARD).pack(side="bottom", pady=(0,12))
        ctk.CTkLabel(sb, text="© 2026 Balfund Trading", font=("Segoe UI",10),
                     text_color=GREY_DK).pack(side="bottom", pady=(0,4))
        ctk.CTkLabel(sb, text="v2.0", font=("Segoe UI",10),
                     text_color=GREY_DK).pack(side="bottom")

        # ── CONTENT AREA ──
        self.content = ctk.CTkFrame(self, fg_color=BG_DEEP, corner_radius=0)
        self.content.pack(side="right", fill="both", expand=True)

        self.token_tab = TokenTab(self.content, on_ready=lambda: self._switch("Strategy"))
        self.strategy_tab = StrategyTab(self.content)
        self.cur_tab = None
        self._switch("Credentials")

    def _switch(self, name):
        if self.cur_tab: self.cur_tab.pack_forget()
        for n, btn in self.nav_btns.items():
            if n == name:
                btn.configure(fg_color=BG_CARD, text_color=TEAL)
            else:
                btn.configure(fg_color="transparent", text_color=WHITE)
        tab = self.token_tab if name == "Credentials" else self.strategy_tab
        tab.pack(fill="both", expand=True)
        self.cur_tab = tab

    def _on_close(self):
        if self.strategy_tab.engine: self.strategy_tab.engine.stop()
        self.destroy()


# ═════════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    _ensure_env()
    App().mainloop()
