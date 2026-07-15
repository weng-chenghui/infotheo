#!/usr/bin/env python3
"""Merge Stage 1, Stage 2, and Tier K outputs; render Markdown; compute exit
code.

Usage: report-merge.py <tier0.json> <stage1.json> <stage2.json> <tierk.json> <latest.md>

Exit code:
  0  no error-severity findings
  2  at least one error-severity finding
"""
from __future__ import annotations
import json
import os
import sys
from pathlib import Path

import yaml

ROOT = Path(os.environ.get("REPO_ROOT", ".")).resolve()
AUDIT_DIR = Path(os.environ.get("AUDIT_DIR", ROOT / ".claude" / "audit")).resolve()
AUDIT_CENTRAL = Path(os.environ.get(
    "AUDIT_CENTRAL",
    AUDIT_DIR.parent.parent / "central-state"
        if AUDIT_DIR.parent.name == "runs"
        else AUDIT_DIR / "central-state",
)).resolve()

SEVERITY_ORDER = {"error": 3, "warning": 2, "info": 1}


def _rules_dir() -> Path:
    if (AUDIT_DIR / "rules").exists():
        return AUDIT_DIR / "rules"
    if (AUDIT_DIR / "template" / "rules").exists():
        return AUDIT_DIR / "template" / "rules"
    return AUDIT_DIR / "rules"


def ranges_overlap(a_start: int, a_end: int, b_start: int, b_end: int) -> bool:
    return a_start <= b_end and b_start <= a_end


def load_rule_titles() -> dict[str, str]:
    titles: dict[str, str] = {}
    for p in sorted(_rules_dir().glob("*.yaml")):
        with open(p) as f:
            r = yaml.safe_load(f) or {}
        if r.get("id"):
            titles[r["id"]] = r.get("title", "")
    return titles


def load_rules_full() -> dict[str, dict]:
    full: dict[str, dict] = {}
    for p in sorted(_rules_dir().glob("*.yaml")):
        with open(p) as f:
            r = yaml.safe_load(f) or {}
        if r.get("id"):
            full[r["id"]] = r
    return full


def load_suppressions() -> dict:
    p = AUDIT_DIR / "suppressions.yaml"
    if not p.exists() and (AUDIT_DIR / "template" / "suppressions.yaml").exists():
        p = AUDIT_DIR / "template" / "suppressions.yaml"
    if not p.exists():
        return {"suppressions": [], "escalations": []}
    with open(p) as f:
        return yaml.safe_load(f) or {"suppressions": [], "escalations": []}


def suppressed(f: dict, suppressions: list[dict]) -> bool:
    import datetime as _dt
    import fnmatch as _fn
    today = _dt.date.today()
    for s in suppressions or []:
        if s.get("rule_id") and s["rule_id"] != f["rule_id"]:
            continue
        if s.get("path") and not _fn.fnmatch(f.get("file", ""), s["path"]):
            continue
        exp = s.get("expires")
        if exp:
            try:
                if _dt.date.fromisoformat(str(exp)) < today:
                    continue
            except Exception:
                continue
        return True
    return False


def apply_inline_pragmas(findings: list[dict]) -> list[dict]:
    """Drop findings whose lemma body contains `(* rocq-audit-disable <ID> ... *)`.
    The pragma is read from the entity body captured in Tier 0, so here we
    approximate by scanning the staged file content."""
    import re as _re
    out: list[dict] = []
    cache: dict[str, str] = {}
    for f in findings:
        fp = f.get("file", "")
        if fp not in cache:
            try:
                src = subprocess.check_output(["git", "show", f":{fp}"], cwd=ROOT, text=True, stderr=subprocess.DEVNULL)
            except Exception:
                src = ""
            cache[fp] = src
        body = cache[fp]
        pragma = _re.compile(r"\(\*\s*rocq-audit-disable\s+" + _re.escape(f["rule_id"]) + r"\b")
        if pragma.search(body):
            continue
        out.append(f)
    return out


def apply_escalations(merged: list[dict], rules: dict[str, dict]) -> list[dict]:
    """If a rule has escalation.fire_count set, count historical fires and
    promote warnings to errors when the threshold is crossed."""
    history_path = AUDIT_CENTRAL / "findings-history.ndjson"
    if not history_path.exists():
        return merged
    counts: dict[str, int] = {}
    try:
        for line in history_path.read_text().splitlines():
            try:
                rec = json.loads(line)
            except Exception:
                continue
            rid = rec.get("rule_id")
            if rid:
                counts[rid] = counts.get(rid, 0) + 1
    except Exception:
        pass
    for f in merged:
        rid = f.get("rule_id")
        rule = rules.get(rid, {})
        esc = rule.get("escalation")
        if not esc:
            continue
        if counts.get(rid, 0) >= int(esc.get("fire_count", 0)) and esc.get("promote_to") == "error":
            if f.get("severity") == "warning":
                f["severity"] = "error"
                f.setdefault("escalated_from", "warning")
    return merged


import subprocess  # used by apply_inline_pragmas


def merge_findings(stage1: list[dict], stage2: list[dict]) -> list[dict]:
    """Overlap-based merge. Two findings merge when same rule_id, same file,
    and their [line_start, line_end] intervals intersect."""
    combined = list(stage1) + list(stage2)
    combined.sort(key=lambda f: (f["rule_id"], f["file"], f["line_start"]))
    merged: list[dict] = []
    for f in combined:
        merged_into = None
        for g in merged:
            if g["rule_id"] != f["rule_id"] or g["file"] != f["file"]:
                continue
            if ranges_overlap(g["line_start"], g["line_end"], f["line_start"], f["line_end"]):
                merged_into = g
                break
        if merged_into is None:
            merged.append(dict(f, stages={f.get("stage", "unknown")}))
            continue
        # Merge ranges, severity, stages.
        merged_into["line_start"] = min(merged_into["line_start"], f["line_start"])
        merged_into["line_end"] = max(merged_into["line_end"], f["line_end"])
        if SEVERITY_ORDER.get(f["severity"], 0) > SEVERITY_ORDER.get(merged_into["severity"], 0):
            merged_into["severity"] = f["severity"]
        merged_into.setdefault("stages", set()).add(f.get("stage", "unknown"))
        if f.get("evidence_quote") and not merged_into.get("evidence_quote"):
            merged_into["evidence_quote"] = f["evidence_quote"]
        if f.get("explanation") and not merged_into.get("explanation"):
            merged_into["explanation"] = f["explanation"]
        if f.get("fix_sketch") and not merged_into.get("fix_sketch"):
            merged_into["fix_sketch"] = f["fix_sketch"]
    for g in merged:
        g["stages"] = sorted(g.get("stages", set()))
    return merged


def render(manifest: dict, merged: list[dict], titles: dict[str, str], stage1_disabled: bool, stage2_disabled: bool,
           budget: dict | None = None, fast_bypassed: bool = False,
           stage2_incomplete: bool = False,
           tier_k_unavailable: bool = False) -> str:
    lines = ["# rocq-audit report", ""]
    if fast_bypassed:
        lines.append("> **FAST BYPASS**: Stage 2 and Tier K were skipped. Only Stage 1 findings are authoritative.")
        lines.append("")
    elif stage2_incomplete:
        reason = (budget or {}).get("stop_reason", "cap_hit")
        lines.append(f"> **CAP HIT**: Stage 2 budget exhausted (reason: `{reason}`). "
                     "A CAP-HIT sentinel (S996) has been injected at error severity; "
                     "the commit is blocked until the operator addresses it.")
        lines.append("")
    elif budget and budget.get("stop_reason", "clean") not in ("clean", "fast_bypass"):
        lines.append(f"> **PARTIAL AUDIT**: Stage 2 stopped early (reason: `{budget['stop_reason']}`). "
                     f"{budget.get('deferred_chunks', 0)} chunks deferred.")
        lines.append("")
    # Tier K unavailability is a separate axis from cap-hits and fast-bypass.
    # Only render the banner when the merged findings actually carry a
    # kernel_contract claim; otherwise Tier K had nothing to verify and the
    # banner would be noise.
    if tier_k_unavailable and any(f.get("kernel_contract") for f in merged):
        lines.append("> **TIER K UNAVAILABLE**: kernel-contract rules are reported without Tier K "
                     "verification; expect possible false positives.")
        lines.append("")
    touched = manifest.get("touched_files", [])
    entities = manifest.get("entities", [])
    lines.append(f"- Touched files: {len(touched)}")
    lines.append(f"- Touched entities: {len(entities)}")
    lines.append(f"- Stage 1: {'disabled' if stage1_disabled else 'enabled'}")
    if fast_bypassed:
        stage2_state = "fast-bypassed"
    elif stage2_disabled:
        stage2_state = "disabled"
    else:
        stage2_state = "enabled"
    lines.append(f"- Stage 2: {stage2_state}")
    lines.append("")
    if budget and not fast_bypassed and budget.get("stop_reason") != "fast_bypass":
        lines.append("## Budget")
        lines.append("")
        wall_used_s = budget.get("wall_ms_used", 0) / 1000.0
        wall_cap_s = budget.get("wall_ms_cap", 0) / 1000.0
        tokens_used = budget.get("tokens_used", 0)
        tokens_cap = budget.get("tokens_cap", 0) or 1
        tok_pct = int(100 * tokens_used / tokens_cap) if tokens_cap else 0
        deferred = budget.get("deferred_chunks", 0)
        workers = budget.get("workers_used", 0)
        chunk_count = budget.get("chunk_count", 0)
        chunk_size = budget.get("chunk_size", 0)
        estimated = budget.get("estimated_usd", 0.0)
        model = budget.get("model", "sonnet")
        reason = budget.get("stop_reason", "clean")
        lines.append(f"- Entities audited: {budget.get('entity_count', 0)} ({deferred} deferred)")
        lines.append(f"- Chunks: {chunk_count} of size {chunk_size}; workers used: {workers}")
        lines.append(f"- Tokens: {tokens_used:,} of {tokens_cap:,} cap ({tok_pct}%)")
        lines.append(f"- Wall time: {wall_used_s:.1f}s of {wall_cap_s:.0f}s budget")
        lines.append(f"- Estimated cost: ${estimated:.4f} ({model})")
        lines.append(f"- Stop reason: {reason}")
        lines.append("")

    if not merged:
        lines.append("No findings.")
        lines.append("")
        return "\n".join(lines)
    err = sum(1 for f in merged if f["severity"] == "error")
    warn = sum(1 for f in merged if f["severity"] == "warning")
    info = sum(1 for f in merged if f["severity"] == "info")
    lines.append(f"**{err} error, {warn} warning, {info} info**")
    lines.append("")
    # Group by file.
    by_file: dict[str, list[dict]] = {}
    for f in merged:
        by_file.setdefault(f["file"], []).append(f)
    for fp in sorted(by_file.keys()):
        lines.append(f"## {fp}")
        lines.append("")
        rows = sorted(by_file[fp], key=lambda x: (x["line_start"], x["rule_id"]))
        for f in rows:
            rule_id = f["rule_id"]
            title = titles.get(rule_id, "")
            stages = ",".join(f.get("stages", []))
            sev = f["severity"].upper()
            lr = f"{f['line_start']}" if f["line_start"] == f["line_end"] else f"{f['line_start']}-{f['line_end']}"
            lines.append(f"### {rule_id} [{sev}] {title}  (stages: {stages})")
            lines.append(f"- **Location**: `{fp}:{lr}`")
            if f.get("lemma_name"):
                lines.append(f"- **Entity**: `{f['lemma_name']}`")
            if f.get("evidence_quote"):
                quote = f["evidence_quote"].replace("`", "\\`")
                lines.append(f"- **Evidence**: `{quote}`")
            if f.get("closeness"):
                lines.append(f"- **Closeness**: {f['closeness']}")
            if f.get("explanation"):
                lines.append(f"- **Explanation**: {f['explanation']}")
            if f.get("fix_sketch"):
                lines.append(f"- **Fix sketch**: {f['fix_sketch']}")
            lines.append("")
    return "\n".join(lines)


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser(
        description="Merge Stage 1, Stage 2, and Tier K outputs into a Markdown report."
    )
    ap.add_argument("tier0", help="Tier 0 manifest JSON")
    ap.add_argument("stage1", help="Stage 1 findings JSON")
    ap.add_argument("stage2", help="Stage 2 findings JSON")
    ap.add_argument("tierk", help="Tier K verdicts JSON")
    ap.add_argument("out_md", help="Markdown output path")
    ap.add_argument("--json", dest="json_out", default=None,
                    help="Also write merged findings plus metadata to this JSON path.")
    args = ap.parse_args()
    tier0_path, stage1_path, stage2_path, tierk_path, out_path = (
        args.tier0, args.stage1, args.stage2, args.tierk, args.out_md
    )
    with open(tier0_path) as f:
        manifest = json.load(f)
    with open(stage1_path) as f:
        stage1 = json.load(f)
    with open(stage2_path) as f:
        stage2 = json.load(f)
    with open(tierk_path) as f:
        tierk = json.load(f)
    stage1_findings = stage1.get("findings", [])
    stage2_findings = stage2.get("findings", [])
    # Drop Stage 2 findings refuted by Tier K.
    refuted = {v["finding_id"] for v in tierk.get("verdicts", []) if not v.get("confirmed", True)}
    if refuted:
        stage2_findings = [f for f in stage2_findings if f.get("id") not in refuted]
    titles = load_rule_titles()
    rules_full = load_rules_full()
    suppressions_cfg = load_suppressions()
    merged = merge_findings(stage1_findings, stage2_findings)
    merged = [f for f in merged if not suppressed(f, suppressions_cfg.get("suppressions", []))]
    merged = apply_inline_pragmas(merged)
    merged = apply_escalations(merged, rules_full)
    budget = stage2.get("budget") if isinstance(stage2, dict) else None
    fast_bypassed = bool(stage2.get("fast_bypassed")) if isinstance(stage2, dict) else False
    stage2_incomplete = bool(stage2.get("stage2_incomplete")) if isinstance(stage2, dict) else False
    tier_k_unavailable = bool(tierk.get("tier_k_unavailable")) if isinstance(tierk, dict) else False
    md = render(manifest, merged, titles,
                stage1_disabled=bool(stage1.get("disabled")),
                stage2_disabled=bool(stage2.get("disabled")),
                budget=budget,
                fast_bypassed=fast_bypassed,
                stage2_incomplete=stage2_incomplete,
                tier_k_unavailable=tier_k_unavailable)
    with open(out_path, "w") as f:
        f.write(md)
    any_error = any(x["severity"] == "error" for x in merged)
    exit_code = 2 if any_error else 0
    if args.json_out:
        json_payload = {
            "findings": merged,
            "stage2_incomplete": stage2_incomplete,
            "tier_k_unavailable": tier_k_unavailable,
            "budget": budget,
            "exit_code": exit_code,
        }
        with open(args.json_out, "w") as f:
            json.dump(json_payload, f, indent=2, ensure_ascii=False, default=list)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
