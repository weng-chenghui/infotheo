#!/usr/bin/env python3
"""Catalog linter.

- Validates every `rules/<id>.yaml` against `schema/rule.schema.json`.
- Rejects banned regex features in `fast_pattern.pattern`.
- Runs Stage 1 against each rule's fixture pair and asserts that the `bad`
  fixture produces at least one finding for this rule and the `good` fixture
  produces none (for rules with stage_mode including Stage 1).
- For Stage 2 rules, runs snapshot replay. When the fingerprint matches the
  stored snapshot at `snapshots/<id>.json`, assertions use the cached agent
  verdict. Pass `--refresh-snapshots` to re-invoke the agent and update the
  snapshot file.

Usage: lint-rules.py [--refresh-snapshots] [--stage2-live]
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

import yaml
import jsonschema

# Ensure the sibling module is importable regardless of cwd.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from file_manifest import build_manifest

ROOT = Path(os.environ.get("REPO_ROOT", subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())).resolve()
AUDIT_DIR = Path(os.environ.get("AUDIT_DIR", ROOT / ".claude" / "audit")).resolve()
# In the execroot model, rules, schema, AUTHORITY.md live under template/.
# Fall back to AUDIT_DIR for the legacy flat layout.
AUDIT_TEMPLATE = Path(os.environ.get("AUDIT_TEMPLATE", AUDIT_DIR / "template")).resolve()
if not (AUDIT_TEMPLATE / "rules").exists() and (AUDIT_DIR / "rules").exists():
    AUDIT_TEMPLATE = AUDIT_DIR
AUDIT_CENTRAL = Path(os.environ.get("AUDIT_CENTRAL", AUDIT_DIR / "central-state")).resolve()

BANNED_REGEX_FEATURES = [
    (re.compile(r"\(\?="), "positive lookahead"),
    (re.compile(r"\(\?!"), "negative lookahead"),
    (re.compile(r"\(\?<="), "positive lookbehind"),
    (re.compile(r"\(\?<!"), "negative lookbehind"),
    (re.compile(r"\\[1-9]"), "backreference"),
]


def load_schema() -> dict:
    with open(AUDIT_TEMPLATE / "schema" / "rule.schema.json") as f:
        return json.load(f)


def check_pattern(pattern: str) -> list[str]:
    errs = []
    for rx, label in BANNED_REGEX_FEATURES:
        if rx.search(pattern):
            errs.append(f"banned regex feature: {label}")
    try:
        re.compile(pattern)
    except re.error as e:
        errs.append(f"invalid regex: {e}")
    return errs


def lint_one(rule_path: Path, schema: dict) -> list[str]:
    errs = []
    with open(rule_path) as f:
        rule = yaml.safe_load(f)
    try:
        jsonschema.validate(instance=rule, schema=schema)
    except jsonschema.ValidationError as e:
        errs.append(f"schema: {e.message} (path: {list(e.absolute_path)})")
    fp = (rule or {}).get("fast_pattern") or {}
    if fp.get("pattern"):
        errs.extend(check_pattern(fp["pattern"]))
    md = rule_path.with_suffix(".md")
    if md.exists() is False:
        errs.append(f"missing sibling Markdown at {md.name}")
    return errs


def run_stage1_fixture(rid: str, fixture_path: Path) -> list[dict]:
    # Manifest construction lives in the shared module `file_manifest.py`;
    # the `fallback_name` keeps the legacy "one synthetic whole-file entity
    # named fixture_<rid>" behaviour when the fixture has no declarations.
    with open(fixture_path) as f:
        content = f.read()
    manifest = build_manifest(
        file_path=fixture_path,
        repo_root=ROOT,
        content=content,
        fallback_name=f"fixture_{rid}",
    )
    tmp_path = AUDIT_CENTRAL / "lint-scratch" / f"lint-tier0-{rid}.json"
    tmp_path.parent.mkdir(parents=True, exist_ok=True)
    with open(tmp_path, "w") as f:
        json.dump(manifest, f)
    env = os.environ.copy()
    env["REPO_ROOT"] = str(ROOT)
    env["AUDIT_DIR"] = str(AUDIT_DIR)
    out = subprocess.check_output(
        [str(AUDIT_DIR / "venv" / "bin" / "python3"),
         str(AUDIT_DIR / "bin" / "stage1-regex.py"),
         str(tmp_path)],
        env=env, text=True)
    data = json.loads(out)
    tmp_path.unlink(missing_ok=True)
    return [f for f in data.get("findings", []) if f["rule_id"] == rid]


def snapshot_fingerprint(rule: dict, bad: str, good: str) -> str:
    h = hashlib.sha256()
    payload = {
        "rule": {k: rule.get(k) for k in ("id", "title", "agent_prompt", "kernel_contract", "severity")},
        "bad": bad,
        "good": good,
    }
    h.update(json.dumps(payload, sort_keys=True).encode())
    return h.hexdigest()[:16]


def stage2_snapshot_path(rid: str) -> Path:
    return AUDIT_DIR / "snapshots" / f"{rid}.json"


def stage2_call_live(rule: dict, fixture_path: Path) -> dict:
    """Call stage2-agent.py against a fixture to get a fresh verdict."""
    rid = rule["id"]
    with open(fixture_path) as f:
        content = f.read()
    rel = str(fixture_path.relative_to(ROOT))
    lines = content.splitlines()
    entity = {
        "file": rel,
        "kind": "Lemma",
        "name": f"fixture_{rid}",
        "line_start": 1,
        "line_end": max(len(lines), 1),
        "header": lines[0] if lines else "",
        "body": content,
        "touched_lines": list(range(1, len(lines) + 1)),
    }
    manifest = {"touched_files": [rel], "entities": [entity], "unanchored_hunks": []}
    tmp_tier0 = AUDIT_CENTRAL / "lint-scratch" / f"lint-stage2-tier0-{rid}.json"
    tmp_stage1 = AUDIT_CENTRAL / "lint-scratch" / f"lint-stage2-stage1-{rid}.json"
    tmp_tier0.parent.mkdir(parents=True, exist_ok=True)
    with open(tmp_tier0, "w") as f:
        json.dump(manifest, f)
    with open(tmp_stage1, "w") as f:
        json.dump({"findings": []}, f)
    env = os.environ.copy()
    env["REPO_ROOT"] = str(ROOT)
    env["AUDIT_DIR"] = str(AUDIT_DIR)
    try:
        out = subprocess.check_output(
            [str(AUDIT_DIR / "venv" / "bin" / "python3"),
             str(AUDIT_DIR / "bin" / "stage2-agent.py"),
             str(tmp_tier0), str(tmp_stage1)],
            env=env, text=True, timeout=600)
    except subprocess.CalledProcessError as e:
        return {"error": f"stage2 call failed: {e}"}
    except subprocess.TimeoutExpired:
        return {"error": "stage2 call timed out"}
    finally:
        tmp_tier0.unlink(missing_ok=True)
        tmp_stage1.unlink(missing_ok=True)
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return {"error": f"non-JSON stage2 output: {out[:200]}"}


def run_stage2_fixture_snapshot(rule: dict, bad: Path, good: Path,
                                refresh: bool, live: bool) -> list[str]:
    errs = []
    rid = rule["id"]
    snap_path = stage2_snapshot_path(rid)
    snap_path.parent.mkdir(parents=True, exist_ok=True)
    bad_text = bad.read_text() if bad.exists() else ""
    good_text = good.read_text() if good.exists() else ""
    fp = snapshot_fingerprint(rule, bad_text, good_text)

    snap: dict | None = None
    if snap_path.exists():
        try:
            snap = json.load(open(snap_path))
        except Exception:
            snap = None

    need_refresh = refresh or snap is None or snap.get("fingerprint") != fp
    if need_refresh:
        if not live and not refresh:
            errs.append(
                f"stage2 snapshot stale for {rid} (fingerprint mismatch); "
                "re-run with --refresh-snapshots to regenerate."
            )
            return errs
        bad_verdict = stage2_call_live(rule, bad) if bad.exists() else {"findings": []}
        good_verdict = stage2_call_live(rule, good) if good.exists() else {"findings": []}
        snap = {
            "fingerprint": fp,
            "bad": bad_verdict,
            "good": good_verdict,
        }
        with open(snap_path, "w") as f:
            json.dump(snap, f, indent=2)

    # Assertions from the (possibly cached) snapshot.
    bad_findings = [f for f in snap["bad"].get("findings", []) if f.get("rule_id") == rid]
    good_findings = [f for f in snap["good"].get("findings", []) if f.get("rule_id") == rid]
    if not bad_findings:
        errs.append(f"stage2 bad fixture yielded 0 findings for {rid}; expected at least 1")
    if good_findings:
        errs.append(f"stage2 good fixture yielded {len(good_findings)} findings for {rid}; expected 0")
    return errs


def run_fixture_test(rule: dict, refresh: bool, stage2_live: bool) -> list[str]:
    errs = []
    rid = rule["id"]
    bad = AUDIT_DIR / "fixtures" / "bad" / f"{rid}.v"
    good = AUDIT_DIR / "fixtures" / "good" / f"{rid}.v"
    if not bad.exists():
        errs.append(f"missing bad fixture {bad.name}")
        return errs
    if not good.exists():
        errs.append(f"missing good fixture {good.name}")
        return errs

    stage_mode = rule.get("stage_mode")
    if stage_mode == "sentinel":
        # Driver-produced rules (e.g. the S997/S998 sentinels). Fixtures
        # must exist for parity with other rules but no regex or agent pass
        # applies; the sentinel is emitted from inside stage2-agent.py.
        return errs
    if stage_mode in ("stage1_only", "both"):
        bad_hits = run_stage1_fixture(rid, bad)
        good_hits = run_stage1_fixture(rid, good)
        if not bad_hits:
            errs.append(f"stage1 bad fixture produced 0 findings; expected >=1")
        if good_hits:
            errs.append(f"stage1 good fixture produced {len(good_hits)} findings; expected 0")

    if stage_mode in ("stage2_only", "both"):
        errs.extend(run_stage2_fixture_snapshot(rule, bad, good, refresh, stage2_live))
    return errs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--refresh-snapshots", action="store_true",
                    help="Re-invoke Stage 2 and update snapshot files for rules whose fingerprint changed.")
    ap.add_argument("--stage2-live", action="store_true",
                    help="Always call Stage 2 live, bypassing the snapshot cache.")
    args = ap.parse_args()

    schema = load_schema()
    rules_dir = AUDIT_TEMPLATE / "rules"
    any_error = False
    for p in sorted(rules_dir.glob("*.yaml")):
        errs = lint_one(p, schema)
        try:
            with open(p) as f:
                rule = yaml.safe_load(f)
            fixture_errs = run_fixture_test(rule, args.refresh_snapshots, args.stage2_live)
            errs.extend(fixture_errs)
        except Exception as e:
            errs.append(f"fixture test raised: {e}")
        label = f"{p.name}"
        if errs:
            any_error = True
            print(f"FAIL {label}")
            for e in errs:
                print(f"   - {e}")
        else:
            print(f"ok   {label}")
    return 1 if any_error else 0


if __name__ == "__main__":
    sys.exit(main())
