#!/usr/bin/env python3
"""audit-history.py — render the rocq-audit dashboard.

Aggregates:
- `state/bypass.log` entries
- Stage 1 and Stage 2 historical findings (if `state/findings-history.ndjson`
  exists; audit.sh appends one line per finding at report time)
- `refs/notes/audit-bypass` git notes
- rule catalog metadata

Emits:
- Markdown to stdout (always)
- HTML to `.claude/audit/reports/dashboard.html` when `--format all|html`
- JSON to `.claude/audit/reports/dashboard.json` when `--format all|json`

Questions answered:
1. Top-firing rules (count, by rule_id, with title)
2. Top-offending files (count, by path)
3. Rules not fired in the last `--since` window
4. Recent bypass events (who, when, which rules would have fired)
"""
from __future__ import annotations
import argparse
import datetime as dt
import json
import os
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import yaml

ROOT = Path(os.environ.get("REPO_ROOT", subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())).resolve()
AUDIT_DIR = Path(os.environ.get("AUDIT_DIR", ROOT / ".claude" / "audit")).resolve()
# In the execroot model, AUDIT_DIR may be either the engine root (when a
# human runs /rocq-audit history from the terminal) or a run directory.
# Resolve the stable roots explicitly.
if AUDIT_DIR.parent.name == "runs":
    AUDIT_ENGINE = AUDIT_DIR.parent.parent
else:
    AUDIT_ENGINE = AUDIT_DIR
AUDIT_TEMPLATE = Path(os.environ.get("AUDIT_TEMPLATE", AUDIT_ENGINE / "template")).resolve()
AUDIT_CENTRAL = Path(os.environ.get("AUDIT_CENTRAL", AUDIT_ENGINE / "central-state")).resolve()
AUDIT_RUNS = AUDIT_ENGINE / "runs"


def load_rules() -> dict[str, dict]:
    rules: dict[str, dict] = {}
    rules_dir = AUDIT_TEMPLATE / "rules" if (AUDIT_TEMPLATE / "rules").exists() else AUDIT_DIR / "rules"
    for p in sorted(rules_dir.glob("*.yaml")):
        with open(p) as f:
            r = yaml.safe_load(f) or {}
        if r.get("id"):
            rules[r["id"]] = r
    return rules


def load_history(since_days: int) -> list[dict]:
    p = AUDIT_CENTRAL / "findings-history.ndjson"
    if not p.exists():
        return []
    cutoff = dt.datetime.utcnow() - dt.timedelta(days=since_days)
    out: list[dict] = []
    for line in p.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            rec = json.loads(line)
        except Exception:
            continue
        ts = rec.get("ts", "")
        try:
            t = dt.datetime.fromisoformat(ts.rstrip("Z"))
        except Exception:
            continue
        if t < cutoff:
            continue
        out.append(rec)
    return out


def load_bypass_entries() -> list[dict]:
    out: list[dict] = []
    bp = AUDIT_CENTRAL / "bypass.log"
    if bp.exists():
        for line in bp.read_text().splitlines():
            if line.startswith("bypass"):
                parts = line.split()
                ts = parts[1] if len(parts) > 1 else "?"
                commit = next((x.split("=", 1)[1] for x in parts if x.startswith("commit=")), "?")
                diff = next((x.split("=", 1)[1] for x in parts if x.startswith("diff=")), "?")
                out.append({"ts": ts, "commit": commit, "diff": diff, "rules": []})
            elif line.strip().startswith("rule="):
                if out:
                    rid = line.split("rule=")[1].split()[0]
                    out[-1]["rules"].append(rid)
    # Also pull from git notes.
    try:
        notes = subprocess.check_output(["git", "notes", "--ref=audit-bypass", "list"], text=True, stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        notes = ""
    for line in notes.splitlines():
        parts = line.split()
        if len(parts) >= 2:
            out.append({"ts": "(git-note)", "commit": parts[1], "diff": "?", "rules": [], "via": "git-notes"})
    return out


def render_markdown(top_rules: list[tuple[str, int, str]],
                    top_files: list[tuple[str, int]],
                    dead_rules: list[tuple[str, str]],
                    bypasses: list[dict],
                    since_days: int) -> str:
    lines = [f"# rocq-audit dashboard  (last {since_days} days)", ""]
    lines.append("## Top-firing rules")
    lines.append("")
    if top_rules:
        lines.append("| Rule | Count | Title |")
        lines.append("|---|---|---|")
        for rid, cnt, title in top_rules:
            lines.append(f"| {rid} | {cnt} | {title} |")
    else:
        lines.append("_No findings in this window._")
    lines.append("")
    lines.append("## Top-offending files")
    lines.append("")
    if top_files:
        lines.append("| File | Count |")
        lines.append("|---|---|")
        for fp, cnt in top_files:
            lines.append(f"| `{fp}` | {cnt} |")
    else:
        lines.append("_No findings in this window._")
    lines.append("")
    lines.append("## Dead rules")
    lines.append("")
    lines.append(f"Rules enabled but with zero firings in the last {since_days} days.")
    lines.append("")
    if dead_rules:
        lines.append("| Rule | Title |")
        lines.append("|---|---|")
        for rid, title in dead_rules:
            lines.append(f"| {rid} | {title} |")
    else:
        lines.append("_All enabled rules fired at least once._")
    lines.append("")
    lines.append("## Bypass events")
    lines.append("")
    if bypasses:
        lines.append("| Timestamp | Commit | Diff | Rules that would have fired |")
        lines.append("|---|---|---|---|")
        for b in bypasses:
            rules = ",".join(b.get("rules", [])) or "-"
            lines.append(f"| {b.get('ts','?')} | `{b.get('commit','?')[:8]}` | `{b.get('diff','?')[:8]}` | {rules} |")
    else:
        lines.append("_No bypass events recorded._")
    lines.append("")
    return "\n".join(lines)


def render_html(md: str) -> str:
    # Minimal self-contained HTML renderer; escape & wrap in <pre>-like layout
    # with a stylesheet so the dashboard stands alone without tooling.
    esc = (md
           .replace("&", "&amp;")
           .replace("<", "&lt;")
           .replace(">", "&gt;"))
    css = (
        "body{font-family:system-ui,sans-serif;max-width:960px;margin:2em auto;padding:0 1em;}"
        "table{border-collapse:collapse;margin:1em 0;}"
        "th,td{border:1px solid #ccc;padding:.3em .6em;}"
        "code{background:#f4f4f4;padding:.1em .3em;border-radius:.2em;}"
        "h1,h2{border-bottom:1px solid #ddd;padding-bottom:.2em;}"
    )
    return f"<!doctype html><html><head><meta charset='utf-8'><title>rocq-audit dashboard</title><style>{css}</style></head><body><pre style='white-space:pre-wrap;font-family:inherit;'>{esc}</pre></body></html>"


def read_last_run_id() -> str | None:
    p = AUDIT_CENTRAL / "last-run-id"
    if not p.exists():
        return None
    try:
        return p.read_text().strip() or None
    except Exception:
        return None


def validate() -> int:
    """Validate the run-pointer state.

    Exit codes:
      0 — bootstrap (both pointers absent) OR all pointers consistent
      2 — last-run-id names a missing directory, runs/LATEST dangles, or the
          two pointers disagree and the divergence is not a transient race
    """
    errs: list[str] = []
    last_id_path = AUDIT_CENTRAL / "last-run-id"
    latest_link = AUDIT_RUNS / "LATEST"

    last_exists = last_id_path.exists()
    latest_exists = latest_link.exists() or latest_link.is_symlink()

    if not last_exists and not latest_exists:
        print("audit-history --validate: bootstrap (no last-run-id, no runs/LATEST); OK.")
        return 0

    last_id = read_last_run_id() if last_exists else None
    if last_id:
        run_dir = AUDIT_RUNS / last_id
        if not run_dir.is_dir():
            errs.append(f"central-state/last-run-id points at missing run {last_id} ({run_dir})")

    if latest_exists:
        try:
            resolved = latest_link.resolve(strict=False)
            if not resolved.is_dir():
                errs.append(f"runs/LATEST dangles: resolves to {resolved} (not a directory)")
        except Exception as e:
            errs.append(f"runs/LATEST resolution failed: {e}")

    if last_exists and latest_exists and last_id and (AUDIT_RUNS / last_id).is_dir():
        # Compare ids: last-run-id vs the name runs/LATEST points at.
        try:
            link_target = os.readlink(latest_link)
        except OSError:
            link_target = None
        if link_target and link_target != last_id:
            # Possible transient divergence. Re-read last-run-id after 200ms.
            time.sleep(0.2)
            second = read_last_run_id()
            if second != last_id:
                print(f"audit-history --validate: transient divergence (last-run-id changed from {last_id} to {second}); a concurrent audit is in flight. OK.")
                return 0
            errs.append(f"last-run-id={last_id} disagrees with runs/LATEST={link_target}; pointers are stale")

    # Walk each run directory and check meta.json parses.
    if AUDIT_RUNS.is_dir():
        for d in sorted(AUDIT_RUNS.iterdir()):
            if not d.is_dir() or d.name in ("LATEST", "e2e-scratch"):
                continue
            meta = d / "meta.json"
            if not meta.exists():
                errs.append(f"runs/{d.name}/meta.json missing")
                continue
            try:
                json.load(open(meta))
            except Exception as e:
                errs.append(f"runs/{d.name}/meta.json fails to parse: {e}")

    if errs:
        print("audit-history --validate: FAILED", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        return 2
    print("audit-history --validate: OK.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", default="30d", help="Window, e.g. 7d, 30d, 90d.")
    ap.add_argument("--format", default="all", choices=["markdown", "html", "json", "all"])
    ap.add_argument("--validate", action="store_true",
                    help="Check run-pointer consistency (last-run-id, runs/LATEST, per-run meta.json) and exit.")
    args = ap.parse_args()

    if args.validate:
        return validate()

    m = args.since.rstrip()
    if m.endswith("d"):
        days = int(m[:-1])
    else:
        days = int(m)

    rules = load_rules()
    history = load_history(days)
    bypasses = load_bypass_entries()

    rule_counter: Counter = Counter()
    file_counter: Counter = Counter()
    for rec in history:
        rid = rec.get("rule_id")
        if rid:
            rule_counter[rid] += 1
        fp = rec.get("file")
        if fp:
            file_counter[fp] += 1

    top_rules = [(rid, cnt, rules.get(rid, {}).get("title", ""))
                 for rid, cnt in rule_counter.most_common(20)]
    top_files = file_counter.most_common(20)
    dead_rules = [(rid, r.get("title", "")) for rid, r in rules.items()
                  if r.get("enabled", True) and rid not in rule_counter]

    md = render_markdown(top_rules, top_files, dead_rules, bypasses, days)
    print(md)

    reports = AUDIT_DIR / "reports"
    reports.mkdir(parents=True, exist_ok=True)
    if args.format in ("html", "all"):
        (reports / "dashboard.html").write_text(render_html(md))
    if args.format in ("json", "all"):
        data = {
            "since_days": days,
            "top_rules": [{"rule_id": r, "count": c, "title": t} for r, c, t in top_rules],
            "top_files": [{"file": f, "count": c} for f, c in top_files],
            "dead_rules": [{"rule_id": r, "title": t} for r, t in dead_rules],
            "bypass_events": bypasses,
        }
        (reports / "dashboard.json").write_text(json.dumps(data, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
