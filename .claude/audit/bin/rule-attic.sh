#!/usr/bin/env bash
# rule-attic.sh — move rules that haven't fired in N days into rules/attic/.
# They are disabled there and preserved for history. Reactivate by moving
# the pair back to rules/ and setting `enabled: true`.
set -euo pipefail

AUDIT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VENV_PY="${AUDIT_DIR}/venv/bin/python3"

SINCE_DAYS="${1:-90}"
DRY_RUN="${DRY_RUN:-0}"

"${VENV_PY}" <<PY
import json, os, shutil
from pathlib import Path
import yaml
AUDIT = Path("${AUDIT_DIR}")
since_days = ${SINCE_DAYS}
hist = AUDIT / "central-state" / "findings-history.ndjson"
if not hist.exists():
    # Legacy fallback.
    hist = AUDIT / "state" / "findings-history.ndjson"
seen = set()
if hist.exists():
    import datetime as dt
    cutoff = dt.datetime.utcnow() - dt.timedelta(days=since_days)
    for line in hist.read_text().splitlines():
        try:
            rec = json.loads(line)
        except Exception:
            continue
        try:
            t = dt.datetime.fromisoformat(rec.get("ts","").rstrip("Z"))
        except Exception:
            continue
        if t >= cutoff and rec.get("rule_id"):
            seen.add(rec["rule_id"])
dry = ${DRY_RUN} == 1
attic = AUDIT / "rules" / "attic"
attic.mkdir(parents=True, exist_ok=True)
moved = []
for p in sorted((AUDIT / "rules").glob("*.yaml")):
    with open(p) as f:
        r = yaml.safe_load(f) or {}
    rid = r.get("id")
    if not rid or rid in seen:
        continue
    if not r.get("enabled", True):
        continue
    md = p.with_suffix(".md")
    if dry:
        print(f"would-move {rid}")
        continue
    shutil.move(str(p), str(attic / p.name))
    if md.exists():
        shutil.move(str(md), str(attic / md.name))
    moved.append(rid)
if moved:
    print("moved:", ", ".join(moved))
else:
    print("no dead rules to archive (since_days=${SINCE_DAYS})")
PY
