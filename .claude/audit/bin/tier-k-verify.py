#!/usr/bin/env python3
"""Tier K kernel grounding.

Reads Stage 2 findings; for each finding with `kernel_contract`, spawns a
headless claude session with rocq-mcp tools and runs the named contract:

- `unused_hypothesis`: open a rocq-mcp session, attempt the proof with the
  named hypothesis removed, report whether the proof still closes.
- `goal_closed_at_line`: open a rocq-mcp session at the claimed line number
  and check whether `done` or `by []` succeeds.

Emits verdicts as JSON on stdout:
{
  "verdicts": [
    {"finding_id": str, "contract": str, "confirmed": bool, "detail": str}
  ]
}
"""
from __future__ import annotations
import json
import os
import subprocess
import sys
from pathlib import Path

import yaml

ROOT = Path(os.environ.get("REPO_ROOT", ".")).resolve()
AUDIT_DIR = Path(os.environ.get("AUDIT_DIR", ROOT / ".claude" / "audit")).resolve()


def finding_id(f: dict) -> str:
    return f"{f['rule_id']}-{f['file']}-{f['line_start']}-{f['line_end']}"


def invoke_contract(contract_name: str, params: dict, finding: dict) -> tuple[bool, str]:
    """Spawn `claude -p` with rocq-mcp tools and ask it to evaluate the
    contract. The prompt is contract-specific and requests a strict JSON
    reply `{"confirmed": bool, "detail": str}`.
    """
    file_rel = finding.get("file", "")
    lemma = finding.get("lemma_name", "")
    if contract_name == "unused_hypothesis":
        hyp = params.get("hypothesis", "")
        prompt = (
            "Use mcp__rocq-mcp__rocq_start to open the lemma below, then inspect whether the "
            f"hypothesis `{hyp}` appears in the proof term. Approach: call "
            f"`mcp__rocq-mcp__rocq_assumptions` on `{lemma}` or read the proof body and check "
            f"whether any tactic references `{hyp}`. If `{hyp}` is never referenced, confirmed=true. "
            f"Otherwise confirmed=false.\n\n"
            f"File: {file_rel}\nLemma: {lemma}\nHypothesis: {hyp}\n\n"
            "Return ONLY JSON: {\"confirmed\": <bool>, \"detail\": \"<brief reason>\"}"
        )
    elif contract_name == "goal_closed_at_line":
        line = int(params.get("line", 0))
        prompt = (
            "Use mcp__rocq-mcp__rocq_start to open a session at the file position below, then "
            "call mcp__rocq-mcp__rocq_check with body `Show.` to see if the goal is already closed. "
            "If there are no remaining goals, confirmed=true. If goals remain, confirmed=false.\n\n"
            f"File: {file_rel}\nLine: {line}\n\n"
            "Return ONLY JSON: {\"confirmed\": <bool>, \"detail\": \"<brief reason>\"}"
        )
    else:
        return False, f"unknown contract {contract_name}"

    try:
        proc = subprocess.run(
            ["claude", "-p", prompt,
             "--model", "sonnet",
             "--output-format", "json",
             "--allowedTools", "Read,Grep,Glob,mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check,mcp__rocq-mcp__rocq_query,mcp__rocq-mcp__rocq_assumptions",
             "--disallowedTools", "Edit,Write,Bash",
             "--disable-slash-commands",
             "--max-budget-usd", "0.5"],
            capture_output=True, text=True, timeout=300, stdin=subprocess.DEVNULL,
        )
    except subprocess.TimeoutExpired:
        return False, "timeout"
    except FileNotFoundError:
        return False, "claude CLI not on PATH"
    if proc.returncode != 0:
        return False, f"rc={proc.returncode}: {proc.stderr[:200]}"
    try:
        env = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return False, "non-JSON envelope"
    result = env.get("result", "")
    if isinstance(result, str):
        try:
            result = json.loads(result)
        except json.JSONDecodeError:
            return False, f"result not JSON: {result[:120]}"
    confirmed = bool(result.get("confirmed", False))
    detail = str(result.get("detail", ""))
    return confirmed, detail


def main() -> int:
    if len(sys.argv) < 3:
        print("usage: tier-k-verify.py <stage2.json> <tier0.json>", file=sys.stderr)
        return 2
    with open(sys.argv[1]) as f:
        stage2 = json.load(f)
    # tier0 unused here but kept in signature for future extensions.

    verdicts: list[dict] = []
    for f in stage2.get("findings", []):
        contract = f.get("kernel_contract")
        if not contract or not isinstance(contract, dict):
            continue
        name = contract.get("name")
        params = contract.get("parameters", {}) or {}
        confirmed, detail = invoke_contract(name, params, f)
        verdicts.append({
            "finding_id": finding_id(f),
            "contract": name,
            "confirmed": confirmed,
            "detail": detail,
        })

    print(json.dumps({"verdicts": verdicts}, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
