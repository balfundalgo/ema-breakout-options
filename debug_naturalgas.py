#!/usr/bin/env python3
"""
Debug NATURALGAS Option Chain — run in VS Code
Fetches expiry list, option chain, and shows all available strikes
so we can see why ITM strike matching fails.
"""

import os, requests, json
from datetime import datetime, timedelta, timezone
from dotenv import load_dotenv

load_dotenv()

CLIENT_ID = os.getenv("DHAN_CLIENT_ID", "").strip()
TOKEN = os.getenv("DHAN_ACCESS_TOKEN", "").strip()

if not CLIENT_ID or not TOKEN:
    print("❌ Missing DHAN_CLIENT_ID or DHAN_ACCESS_TOKEN in .env")
    exit(1)

BASE = "https://api.dhan.co/v2"
HEADERS = {"Content-Type": "application/json", "Accept": "application/json",
           "access-token": TOKEN, "client-id": CLIENT_ID}
SCRIP_URL = "https://images.dhan.co/api-data/api-scrip-master.csv"


def now_ist():
    return datetime.now(timezone(timedelta(hours=5, minutes=30)))


def api_post(endpoint, payload):
    r = requests.post(f"{BASE}{endpoint}", headers=HEADERS, json=payload, timeout=15)
    print(f"  POST {endpoint} → {r.status_code}")
    if r.status_code == 200:
        return r.json()
    print(f"  Response: {r.text[:500]}")
    return None


# ─────────────────────────────────────────────────────────────────────────
# Step 1: Resolve NATURALGAS near-month futures security_id
# ─────────────────────────────────────────────────────────────────────────
print("=" * 70)
print("STEP 1: Resolve NATURALGAS near-month futures from scrip master")
print("=" * 70)

import pandas as pd
from io import StringIO

print("  Downloading scrip master (~34MB)...")
r = requests.get(SCRIP_URL, timeout=60)
r.raise_for_status()
print(f"  Downloaded: {len(r.content) // (1024*1024)} MB")

cols = ["SEM_EXM_EXCH_ID", "SEM_SEGMENT", "SEM_SMST_SECURITY_ID",
        "SEM_INSTRUMENT_NAME", "SM_SYMBOL_NAME", "SEM_EXPIRY_DATE",
        "SEM_LOT_UNITS", "SEM_TRADING_SYMBOL"]
df = pd.read_csv(StringIO(r.text), usecols=cols, low_memory=False)
for c in ["SEM_EXM_EXCH_ID", "SEM_SEGMENT", "SEM_INSTRUMENT_NAME", "SM_SYMBOL_NAME"]:
    df[c] = df[c].astype(str).str.strip()

# Show all NATURALGAS rows
ng = df[(df["SEM_EXM_EXCH_ID"] == "MCX") &
        (df["SM_SYMBOL_NAME"].str.upper() == "NATURALGAS")]
print(f"\n  All NATURALGAS rows in scrip master ({len(ng)}):")
print(f"  {'Instrument':<15} {'SecId':<12} {'Expiry':<25} {'TradingSymbol':<35} {'Lot':<8} {'Segment':<12}")
print(f"  {'-'*105}")
for _, row in ng.iterrows():
    print(f"  {row['SEM_INSTRUMENT_NAME']:<15} {row['SEM_SMST_SECURITY_ID']:<12} "
          f"{str(row['SEM_EXPIRY_DATE'])[:19]:<25} {str(row['SEM_TRADING_SYMBOL']):<35} "
          f"{row['SEM_LOT_UNITS']:<8} {row['SEM_SEGMENT']:<12}")

# Find FUTCOM near-month
today_str = now_ist().strftime("%Y-%m-%d")
fut = ng[ng["SEM_INSTRUMENT_NAME"] == "FUTCOM"].copy()
fut["exp_date"] = fut["SEM_EXPIRY_DATE"].astype(str).str[:10]
fut = fut[fut["exp_date"] >= today_str].sort_values("exp_date")
if fut.empty:
    print("\n  ❌ No FUTCOM found for NATURALGAS!")
    exit(1)

near = fut.iloc[0]
fut_sec_id = str(near["SEM_SMST_SECURITY_ID"]).strip()
fut_exp = str(near["exp_date"])
print(f"\n  ✅ Near-month FUTCOM: secId={fut_sec_id}  expiry={fut_exp}")
print(f"     Trading symbol: {near['SEM_TRADING_SYMBOL']}")

# ─────────────────────────────────────────────────────────────────────────
# Step 2: Fetch expiry list for NATURALGAS options
# ─────────────────────────────────────────────────────────────────────────
print(f"\n{'=' * 70}")
print("STEP 2: Fetch option expiry list")
print("=" * 70)

resp = api_post("/optionchain/expirylist",
                {"UnderlyingScrip": int(fut_sec_id), "UnderlyingSeg": "MCX_COMM"})
if resp and resp.get("status") == "success":
    expiries = resp["data"]
    print(f"  Expiries: {expiries}")
    # Pick nearest
    today = now_ist().date()
    valid = []
    for s in expiries:
        try:
            d = datetime.strptime(s, "%Y-%m-%d").date()
            if d >= today:
                valid.append((d, s))
        except:
            continue
    valid.sort()
    if valid:
        nearest_exp = valid[0][1]
        print(f"  ✅ Nearest expiry: {nearest_exp}")
    else:
        print("  ❌ No valid future expiry found")
        exit(1)
else:
    print("  ❌ Expiry list fetch failed")
    print(f"  Raw response: {json.dumps(resp, indent=2) if resp else 'None'}")
    exit(1)

# ─────────────────────────────────────────────────────────────────────────
# Step 3: Fetch option chain
# ─────────────────────────────────────────────────────────────────────────
print(f"\n{'=' * 70}")
print(f"STEP 3: Fetch option chain (underlying={fut_sec_id}, expiry={nearest_exp})")
print("=" * 70)

resp = api_post("/optionchain",
                {"UnderlyingScrip": int(fut_sec_id), "UnderlyingSeg": "MCX_COMM",
                 "Expiry": nearest_exp})

if not resp or resp.get("status") != "success":
    print("  ❌ Option chain fetch failed")
    print(f"  Raw response: {json.dumps(resp, indent=2) if resp else 'None'}")
    exit(1)

data = resp["data"]
spot = float(data["last_price"])
oc = data["oc"]

print(f"\n  Spot price (futures LTP): {spot}")
print(f"  Total strikes in chain: {len(oc)}")

# ─────────────────────────────────────────────────────────────────────────
# Step 4: Print ALL available strikes
# ─────────────────────────────────────────────────────────────────────────
print(f"\n{'=' * 70}")
print("STEP 4: All strikes in option chain")
print("=" * 70)

strikes = []
for k in oc:
    try:
        strike_val = float(k)
    except:
        strike_val = k
    has_ce = "ce" in oc[k] and oc[k]["ce"] is not None
    has_pe = "pe" in oc[k] and oc[k]["pe"] is not None
    ce_ltp = float(oc[k]["ce"]["last_price"]) if has_ce else 0
    pe_ltp = float(oc[k]["pe"]["last_price"]) if has_pe else 0
    ce_sid = str(oc[k]["ce"]["security_id"]) if has_ce else "-"
    pe_sid = str(oc[k]["pe"]["security_id"]) if has_pe else "-"
    strikes.append((strike_val, k, has_ce, ce_ltp, ce_sid, has_pe, pe_ltp, pe_sid))

strikes.sort(key=lambda x: x[0] if isinstance(x[0], float) else 0)

print(f"\n  {'Strike Key':<18} {'Strike Val':<12} {'CE?':<5} {'CE LTP':<10} {'CE SecId':<12} "
      f"{'PE?':<5} {'PE LTP':<10} {'PE SecId':<12}")
print(f"  {'-'*95}")
for s in strikes:
    marker = " ◄ ATM" if isinstance(s[0], float) and abs(s[0] - spot) < 3 else ""
    print(f"  {s[1]:<18} {s[0]:<12} {'✅' if s[2] else '❌':<5} {s[3]:<10.2f} {s[4]:<12} "
          f"{'✅' if s[5] else '❌':<5} {s[6]:<10.2f} {s[7]:<12}{marker}")

# ─────────────────────────────────────────────────────────────────────────
# Step 5: Test ITM strike selection with different offsets
# ─────────────────────────────────────────────────────────────────────────
print(f"\n{'=' * 70}")
print("STEP 5: Test ITM strike matching")
print("=" * 70)

STRIKE_GAP = 2

for offset in [2, 4, 6, 8, 10, 20]:
    atm = round(spot / STRIKE_GAP) * STRIKE_GAP
    itm_ce = atm - offset
    itm_pe = atm + offset

    # Try to find in option chain
    ce_found = pe_found = False
    for k in oc:
        try:
            kf = float(k)
            if abs(kf - itm_ce) < 0.01 and oc[k].get("ce"):
                ce_found = True
            if abs(kf - itm_pe) < 0.01 and oc[k].get("pe"):
                pe_found = True
        except:
            continue

    print(f"  Offset={offset:>3}  ATM={atm}  CE_strike={itm_ce} {'✅' if ce_found else '❌'}  "
          f"PE_strike={itm_pe} {'✅' if pe_found else '❌'}")

# ─────────────────────────────────────────────────────────────────────────
# Step 6: Show first 5 raw strike keys for format analysis
# ─────────────────────────────────────────────────────────────────────────
print(f"\n{'=' * 70}")
print("STEP 6: Raw strike key format (first 10)")
print("=" * 70)

raw_keys = list(oc.keys())[:10]
for k in raw_keys:
    print(f"  Key: '{k}'  (type={type(k).__name__}, repr={repr(k)})")

print(f"\n{'=' * 70}")
print("DEBUG COMPLETE")
print("=" * 70)
