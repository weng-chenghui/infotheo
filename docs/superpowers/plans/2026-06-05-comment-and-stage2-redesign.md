# Comment contract and Stage-2 architecture Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the LLM-graded comment rules with a deterministic Stage-1 tag contract (Phase 1), then move the kernel-decidable rules to a token-free deterministic kernel pass and scope the surviving LLM work (Phase 2).

**Architecture:** Phase 1 makes the H-series `stage1_only` regex with three tags (`@intent`, `@composes`, `@main <label>`) plus a bounded `git grep` for `@composes` resolution. Phase 2 adds a `bin/stage1_5-kernel.py` deterministic pass for D001/E001, deletes Tier-K, retires C001 to a regex stub, scopes commit-time G001 to renamed entities, and prunes the per-chunk LLM prompt.

**Tech Stack:** Python 3 (pipeline scripts under `.claude/audit/bin/`), YAML rule catalog, JSON Schema, coq-lsp / rocq-mcp for the kernel pass, git for staged-content access.

**Source spec:** `docs/superpowers/specs/2026-06-05-comment-and-stage2-redesign-design.md`

---

## Conventions used by every task

- `$A` means `.claude/audit`. `$PY` means `.claude/audit/venv/bin/python3`.
- Run the catalog linter with: `.claude/audit/bin/lint-rules.sh` (add `--full` for the e2e harness). It validates schema, checks banned regex, and runs each rule's `bad`/`good` fixture (Stage-1 rules: `bad` must yield >=1 finding for that rule, `good` must yield 0).
- A "synthetic manifest test" runs the real Stage-1 entry point on a hand-written Tier-0 JSON: `$PY .claude/audit/bin/stage1-regex.py /tmp/m.json` with env `REPO_ROOT=$(git rev-parse --show-toplevel) AUDIT_DIR=$REPO_ROOT/.claude/audit`. This is the only way to exercise `touched_header=false` branches, because the fixture harness (`file_manifest.py:107`) always sets `touched_header=true`.
- Commit note: `.claude/audit/bin/audit.sh:125` audits every staged `*.v`, so a deliberately-broken `bad` fixture would self-trip the pre-commit gate. **Task 1 adds `.claude/audit/fixtures/**` to `excluded_paths`, after which fixture commits pass.** Commits of `.py`/`.yaml`/`.md`/`.json` stage no `.v` and never trip the gate.
- Do not use `--no-verify` (forbidden by policy). If a commit must bypass for an unrelated reason, use `ROCQ_AUDIT_BYPASS=1`.

---

# PHASE 1 — Part A: comment tag contract

### Task 1: Groundwork — schema, config, fixture exclusion

**Files:**
- Modify: `.claude/audit/template/schema/rule.schema.json` (the `fast_check.kind` enum)
- Modify: `.claude/audit/template/config.yaml`

- [ ] **Step 1: Extend the `fast_check.kind` enum**

In `rule.schema.json`, change the `fast_check.properties.kind.enum` from
`["missing_preceding_comment", "naming_conformance_or_justify"]` to:

```json
"kind": { "type": "string", "enum": [
  "missing_preceding_comment",
  "naming_conformance_or_justify",
  "comment_tag_absence",
  "comment_tag_validity",
  "comment_composes_reachability"
] }
```

- [ ] **Step 2: Add config keys**

In `template/config.yaml`, under `excluded_paths` add the fixtures glob, and add the two new keys near `strict_comment_coverage`:

```yaml
excluded_paths:
- _build/**
- rocq_mcp_cache_*.v
- '**/extraction/**'
- .lia.cache
- .Makefile.d/**
- .claude/audit/fixtures/**
```

```yaml
# Allowed labels for the @main <label> comment tag (Part A).
main_purpose_labels:
  - security
  - correctness
  - architecture
  - bound
# Opt-in agent check that prose matches the claimed @main pillar (H004). Default off.
comment_semantic_check: false
```

- [ ] **Step 3: Verify the schema still validates the catalog**

Run: `.claude/audit/bin/lint-rules.sh`
Expected: every existing rule prints `ok` (no schema regressions). Snapshot-staleness warnings for stage2 rules are acceptable here; they are addressed later.

- [ ] **Step 4: Commit**

```bash
git add .claude/audit/template/schema/rule.schema.json .claude/audit/template/config.yaml
git commit -m "audit: schema+config groundwork for comment tag contract"
```

---

### Task 2: Shared tag parser and content floor in stage1-regex.py

**Files:**
- Modify: `.claude/audit/bin/stage1-regex.py` (add helpers after the imports / `load_config`)
- Create: `.claude/audit/bin/test_hseries_helpers.py` (standalone assertion script)

- [ ] **Step 1: Write the failing helper test**

Create `.claude/audit/bin/test_hseries_helpers.py`:

```python
#!/usr/bin/env python3
"""Unit checks for the H-series tag helpers in stage1-regex.py.
Run: .claude/audit/venv/bin/python3 .claude/audit/bin/test_hseries_helpers.py
"""
import importlib.util, sys
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "stage1regex", str(Path(__file__).resolve().parent / "stage1-regex.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def ok(cond, msg):
    if not cond:
        print("FAIL:", msg); sys.exit(1)

# content floor
ok(m._content_floor_ok("abelian words leak no identity", "x"), "floor: real prose passes")
ok(not m._content_floor_ok("x", "word_collapse"), "floor: one char fails")
ok(not m._content_floor_ok("TODO", "x"), "floor: TODO fails")
ok(not m._content_floor_ok("word_collapse", "word_collapse"), "floor: equals identifier fails")

# tag parsing
e = {"preceding_comment": "(** f.  @main security: hides the deck. *)"}
t = m._comment_role_tag(e)
ok(t and t["kind"] == "main" and t["labels"] == ["security"] and t["value"] == "hides the deck.", "main tag")
e = {"preceding_comment": "(** g.  @composes: foo, bar *)"}
t = m._comment_role_tag(e)
ok(t and t["kind"] == "composes" and t["targets"] == ["foo", "bar"], "composes tag")
e = {"preceding_comment": "(** d.  @intent: canonical shuffle action. *)"}
t = m._comment_role_tag(e)
ok(t and t["kind"] == "intent" and t["value"].startswith("canonical"), "intent tag")
ok(m._comment_role_tag({"preceding_comment": "(* plain comment *)"}) is None, "no tag -> None")
print("ok test_hseries_helpers")
```

- [ ] **Step 2: Run it to confirm it fails**

Run: `$PY .claude/audit/bin/test_hseries_helpers.py` (use the venv python).
Expected: FAIL with `AttributeError: module 'stage1regex' has no attribute '_content_floor_ok'`.

- [ ] **Step 3: Implement the helpers**

In `stage1-regex.py`, after `load_config()` (around line 111), add:

```python
# ---- H-series comment tag contract ----------------------------------------

_TAG_KEYWORD_RE = re.compile(r"@(intent|composes|main)\b", re.IGNORECASE)
_INTENT_RE = re.compile(r"@intent\s*:\s*(.+)", re.IGNORECASE | re.DOTALL)
_COMPOSES_RE = re.compile(r"@composes\s*:\s*([^\n*]+)", re.IGNORECASE)
_MAIN_RE = re.compile(
    r"@main\s+([A-Za-z][A-Za-z0-9_]*(?:\s*,\s*[A-Za-z][A-Za-z0-9_]*)*)\s*:\s*(.+)",
    re.IGNORECASE | re.DOTALL)
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_DEGEN_WORDS = {"todo", "fixme", "wip", "xxx", "???"}


def _strip_comment_delims(pc: str) -> str:
    s = pc
    for d in ("(**", "(*", "*)"):
        s = s.replace(d, " ")
    return s


def _content_floor_ok(text: str, identifier: str) -> bool:
    """Reused for both the @-tag value (anti-gaming) and the substantive
    legacy-comment test. Mirrors the old H001.yaml:18-27 metric."""
    t = (text or "").strip()
    if t.lower() in _DEGEN_WORDS:
        return False
    if t == identifier:
        return False
    if len(re.sub(r"\s+", "", t)) < 10:
        return False
    alpha_tokens = re.findall(r"[^\W\d_]{3,}", t, re.UNICODE)
    return len(alpha_tokens) >= 2


def _comment_role_tag(entity: dict) -> dict | None:
    """Return the single role tag found in the preceding comment, or None.
    {"kind": "intent"|"composes"|"main", "value": str,
     "labels": [str]|None, "targets": [str]|None, "multi": bool}"""
    body = _strip_comment_delims(entity.get("preceding_comment", "") or "")
    kws = [k.lower() for k in _TAG_KEYWORD_RE.findall(body)]
    if not kws:
        return None
    kind = kws[0]
    tag: dict = {"kind": kind, "multi": len(set(kws)) > 1, "labels": None, "targets": None, "value": ""}
    if kind == "intent":
        mm = _INTENT_RE.search(body)
        tag["value"] = mm.group(1).strip() if mm else ""
    elif kind == "composes":
        mm = _COMPOSES_RE.search(body)
        raw = mm.group(1).strip() if mm else ""
        tag["value"] = raw
        tag["targets"] = _IDENT_RE.findall(raw)
    elif kind == "main":
        mm = _MAIN_RE.search(body)
        if mm:
            tag["labels"] = [s.strip().lower() for s in mm.group(1).split(",")]
            tag["value"] = mm.group(2).strip()
        else:
            tag["labels"] = []
            tag["value"] = ""
    return tag


def _main_purpose_labels(cfg: dict) -> set[str]:
    return {str(s).lower() for s in (cfg.get("main_purpose_labels") or [])}


def _composes_target_exists(name: str) -> bool:
    """Bounded git grep for an exact top-level declaration of `name`.
    The decl-keyword anchor excludes `Used by:` comment mentions."""
    import subprocess
    pat = (r"^[[:space:]]*(Lemma|Theorem|Fact|Corollary|Proposition|Definition|Fixpoint)"
           r"[[:space:]]+" + re.escape(name) + r"([^A-Za-z0-9_']|$)")
    try:
        r = subprocess.run(["git", "grep", "-lE", pat, "--", "*.v"],
                           cwd=str(ROOT), capture_output=True, text=True, timeout=20)
    except Exception:
        return True  # abstain: never raise a false dangling error on tool failure
    return r.returncode == 0 and bool(r.stdout.strip())
```

- [ ] **Step 4: Run the helper test to confirm it passes**

Run: `$PY .claude/audit/bin/test_hseries_helpers.py`
Expected: `ok test_hseries_helpers`

- [ ] **Step 5: Commit**

```bash
git add .claude/audit/bin/stage1-regex.py .claude/audit/bin/test_hseries_helpers.py
git commit -m "audit: shared H-series tag parser and content floor"
```

---

### Task 3: H001 rework — tag absence and migration

**Files:**
- Modify: `.claude/audit/template/rules/H001.yaml`, `.md`
- Modify: `.claude/audit/bin/stage1-regex.py` (`apply_fast_check` dispatch)
- Rewrite: `.claude/audit/fixtures/bad/H001.v`, `.claude/audit/fixtures/good/H001.v`
- Delete: `.claude/audit/snapshots/H001.json`

- [ ] **Step 1: Rewrite the H001 fixtures (the tests)**

`fixtures/bad/H001.v` (each entity violates H001; `file_manifest` marks all `touched_header=true`, so every untagged in-scope decl is an error):

```coq
(* Fixture: triggers H001. Do NOT compile. *)

Lemma no_tag_no_comment : 0 < 1.
Proof. by []. Qed.

(* TODO *)
Lemma no_tag_degenerate_comment : 0 < 2.
Proof. by []. Qed.

(** plain prose with no role tag at all here. *)
Lemma no_role_tag : 0 < 3.
Proof. by []. Qed.
```

`fixtures/good/H001.v` (no H001 violation):

```coq
(* Fixture: no H001 violation. Do NOT compile. *)

(** zero_lt_one.  @composes: ord_pos_ge0 *)
Lemma zero_lt_one : 0 < 1.
Proof. by []. Qed.

(** commuted_add.  @main correctness: addition commutes on nat. *)
#[local] Arguments commuted_add _ _.
Lemma commuted_add (a b : nat) : a + b = b + a.
Proof. by rewrite addnC. Qed.

(** deck_index.  @intent: canonical index type for the deck. *)
Definition deck_index (n : nat) : Type := 'I_n * 'I_n.

(* Out-of-scope: single-line Definition with trivial RHS is not audited. *)
Definition x := 1.
```

- [ ] **Step 2: Rewrite H001.yaml**

```yaml
id: H001
category: formatting
title: "Declaration lacks a required role tag (@intent / @composes / @main)"
severity: error
enabled: true
stage_mode: stage1_only
authority:
  - peer-feedback-2026-04
  - coqdoc
fast_check:
  kind: comment_tag_absence
scope: changed_lemmas
fix_hint: "Add exactly one role tag in the preceding comment: `@intent: ...` for a Definition/Fixpoint, `@composes: <lemma>` for a helper, or `@main <security|correctness|architecture|bound>: ...` for a main lemma. See AUTHORITY.md."
exceptions: []
```

- [ ] **Step 3: Implement the `comment_tag_absence` branch**

In `apply_fast_check` (stage1-regex.py, the `kind ==` dispatch around line 165), add a branch. It needs config, so pass `cfg` through: change `apply_fast_check(rule, manifest, strict_comment_coverage)` callers and signature to also take `cfg` (the `main` function already has `cfg`). Then:

```python
    elif kind == "comment_tag_absence":
        for entity in manifest.get("entities", []):
            if not h_series_applies(entity):
                continue
            if not strict_comment_coverage and not _entity_touched(entity):
                continue
            tag = _comment_role_tag(entity)
            if tag is not None:
                continue  # validity handled by H002
            name = entity.get("name", "")
            present = entity.get("preceding_comment_present", False)
            if not present:
                sev_use, why = "error", "no preceding comment and no role tag"
            elif entity.get("touched_header", False):
                sev_use, why = "error", "declaration changed; a role tag is required"
            elif _content_floor_ok(_strip_comment_delims(entity.get("preceding_comment", "")), name):
                sev_use, why = "warning", "legacy comment grandfathered; add a role tag"
            else:
                sev_use, why = "error", "degenerate comment and no role tag"
            findings.append({
                "rule_id": rule["id"], "file": entity["file"],
                "line_start": entity["line_start"], "line_end": entity["line_start"],
                "lemma_name": name, "severity": sev_use,
                "evidence_quote": entity.get("header", "").strip(),
                "stage": "stage1", "reason": why,
            })
```

Add the small helper near the others:

```python
def _entity_touched(entity: dict) -> bool:
    """In commit mode an entity is in scope when any of its body lines or its
    header line changed. file_manifest sets touched_header=True for all."""
    return bool(entity.get("touched_lines")) or entity.get("touched_header", False)
```

Update the dispatch call sites: in `main()` change `apply_fast_check(rule, manifest, strict_comment)` to `apply_fast_check(rule, manifest, strict_comment, cfg)`; update the `def apply_fast_check(rule, manifest, strict_comment_coverage, cfg):` signature; pass `cfg` down to the naming branch too (ignore it there).

- [ ] **Step 4: Delete the orphaned Stage-2 snapshot**

```bash
git rm .claude/audit/snapshots/H001.json
```

- [ ] **Step 5: Run the fixture lint**

Run: `.claude/audit/bin/lint-rules.sh`
Expected: `ok H001.yaml` (bad yields >=1 H001, good yields 0). No snapshot path is exercised because H001 is now `stage1_only`.

- [ ] **Step 6: Synthetic-manifest test for the grandfather branch**

Write `/tmp/h001_grandfather.json` (a body-only change to a pre-existing decl with a substantive legacy comment and no tag → must be a WARNING, not error):

```json
{"touched_files":["pgg-smc/x.v"],"entities":[{
  "file":"pgg-smc/x.v","kind":"Lemma","name":"legacy_lemma","line_start":10,"line_end":12,
  "header":"Lemma legacy_lemma : 0 < 1.","body":"Lemma legacy_lemma : 0 < 1.\nProof. by []. Qed.",
  "touched_lines":[11],"touched_header":false,
  "preceding_comment":"(** legacy_lemma proves the base inequality used widely. *)",
  "preceding_comment_present":true}],"unanchored_hunks":[]}
```

Run:
```bash
REPO_ROOT=$(git rev-parse --show-toplevel) AUDIT_DIR=$REPO_ROOT/.claude/audit \
  .claude/audit/venv/bin/python3 .claude/audit/bin/stage1-regex.py /tmp/h001_grandfather.json
```
Expected: one H001 finding with `"severity": "warning"`. Change `touched_header` to `true` and re-run: severity becomes `error`. Change `preceding_comment` to `"(* TODO *)"` with `touched_header:false`: severity is `error` (degenerate).

- [ ] **Step 7: Commit**

```bash
git add .claude/audit/template/rules/H001.yaml .claude/audit/template/rules/H001.md \
        .claude/audit/bin/stage1-regex.py \
        .claude/audit/fixtures/bad/H001.v .claude/audit/fixtures/good/H001.v
git commit -m "audit: H001 becomes stage1 tag-absence with migration severity"
```

---

### Task 4: H002 rework — tag validity and dangling @composes

**Files:**
- Modify: `.claude/audit/template/rules/H002.yaml`, `.md`
- Modify: `.claude/audit/bin/stage1-regex.py` (`comment_tag_validity` branch)
- Rewrite: `.claude/audit/fixtures/bad/H002.v`, `.claude/audit/fixtures/good/H002.v`
- Delete: `.claude/audit/snapshots/H002.json`

- [ ] **Step 1: Rewrite the H002 fixtures**

`fixtures/bad/H002.v` (each line is a distinct validity error; `nonexistent_xyz_target` must not exist anywhere in the repo):

```coq
(* Fixture: triggers H002. Do NOT compile. *)

(** a.  @main security: x *)
Lemma empty_value_tag : 0 < 1.
Proof. by []. Qed.

(** b.  @main leakage: this label is not in the enum at all. *)
Lemma bad_label_tag : 0 < 2.
Proof. by []. Qed.

(** c.  @composes: nonexistent_xyz_target *)
Lemma dangling_composes : 0 < 3.
Proof. by []. Qed.
```

`fixtures/good/H002.v`:

```coq
(* Fixture: no H002 violation. Do NOT compile. *)

(** a.  @main security: abelian words leak no card identity. *)
Lemma well_formed_main : 0 < 1.
Proof. by []. Qed.

(** b.  @composes: well_formed_main *)
Lemma well_formed_helper : 0 < 2.
Proof. by []. Qed.
```

- [ ] **Step 2: Rewrite H002.yaml**

```yaml
id: H002
category: formatting
title: "Role tag is malformed, empty, bad-label, or names a dangling @composes target"
severity: error
enabled: true
stage_mode: stage1_only
authority:
  - peer-feedback-2026-04
fast_check:
  kind: comment_tag_validity
scope: changed_lemmas
fix_hint: "Give the tag a non-degenerate value; use a @main label from main_purpose_labels; ensure each @composes target names a real declaration; use @intent for definitions and @main/@composes for lemmas."
exceptions: []
```

- [ ] **Step 3: Implement the `comment_tag_validity` branch**

```python
    elif kind == "comment_tag_validity":
        labels = _main_purpose_labels(cfg)
        for entity in manifest.get("entities", []):
            if not h_series_applies(entity):
                continue
            if not strict_comment_coverage and not _entity_touched(entity):
                continue
            tag = _comment_role_tag(entity)
            if tag is None:
                continue  # absence handled by H001
            name = entity.get("name", "")
            kindk = entity.get("kind", "")
            problems = []
            if tag.get("multi"):
                problems.append("more than one role tag")
            # tag/kind agreement
            is_def = kindk in ("Definition", "Fixpoint")
            if is_def and tag["kind"] != "intent":
                problems.append("definitions use @intent, not @" + tag["kind"])
            if not is_def and tag["kind"] == "intent":
                problems.append("lemmas use @main or @composes, not @intent")
            # per-kind validity
            if tag["kind"] in ("intent", "main") and not _content_floor_ok(tag["value"], name):
                problems.append("empty or degenerate tag value")
            if tag["kind"] == "main":
                for lab in (tag.get("labels") or []):
                    if lab not in labels:
                        problems.append(f"@main label '{lab}' not in main_purpose_labels")
                if not tag.get("labels"):
                    problems.append("@main missing a label")
            if tag["kind"] == "composes":
                targets = tag.get("targets") or []
                if not targets:
                    problems.append("@composes names no target")
                for tgt in targets:
                    if not _composes_target_exists(tgt):
                        problems.append(f"@composes target '{tgt}' has no declaration in the repo")
            if problems:
                findings.append({
                    "rule_id": rule["id"], "file": entity["file"],
                    "line_start": entity["line_start"], "line_end": entity["line_start"],
                    "lemma_name": name, "severity": rule.get("severity", "error"),
                    "evidence_quote": (entity.get("preceding_comment", "") or "").strip()[:200],
                    "stage": "stage1", "reason": "; ".join(problems),
                })
```

- [ ] **Step 4: Delete the orphaned snapshot and run lint**

```bash
git rm .claude/audit/snapshots/H002.json
.claude/audit/bin/lint-rules.sh
```
Expected: `ok H002.yaml`. The `good` fixture's `@composes: well_formed_main` resolves because `well_formed_main` is declared in the same fixture file (git grep finds it once the fixture is committed; before commit it resolves against the working tree only if tracked). If the `good` fixture's composes target is not yet tracked, lint may report a false dangling. To avoid that ordering hazard, the `good` H002 helper composes a target that already exists in the repo at lint time. Use this instead for `good/H002.v` second entity:

```coq
(** b.  @composes: well_formed_main *)
Lemma well_formed_helper : 0 < 2.
Proof. by []. Qed.
```

and keep `well_formed_main` declared above it in the same file. Confirm `git grep -lE '^[[:space:]]*Lemma[[:space:]]+well_formed_main' -- '*.v'` finds the fixture only after it is staged/committed; run lint after `git add` of the good fixture so the working tree contains it.

- [ ] **Step 5: Commit**

```bash
git add .claude/audit/template/rules/H002.yaml .claude/audit/template/rules/H002.md \
        .claude/audit/bin/stage1-regex.py \
        .claude/audit/fixtures/bad/H002.v .claude/audit/fixtures/good/H002.v
git commit -m "audit: H002 becomes stage1 tag-validity with git-grep composes resolution"
```

---

### Task 5: H003 new — @composes reachability to a @main node

**Files:**
- Create: `.claude/audit/template/rules/H003.yaml`, `.md`
- Modify: `.claude/audit/bin/stage1-regex.py` (`comment_composes_reachability` branch)
- Create: `.claude/audit/fixtures/bad/H003.v`, `.claude/audit/fixtures/good/H003.v`

- [ ] **Step 1: Fixtures**

`fixtures/bad/H003.v` (a helper whose @composes chain never reaches a @main node within the file):

```coq
(* Fixture: triggers H003. Do NOT compile. *)

(** a.  @composes: helper_b *)
Lemma helper_a : 0 < 1.
Proof. by []. Qed.

(** b.  @composes: helper_a *)
Lemma helper_b : 0 < 2.
Proof. by []. Qed.
```

`fixtures/good/H003.v` (the chain reaches a @main node):

```coq
(* Fixture: no H003 violation. Do NOT compile. *)

(** m.  @main correctness: the headline result. *)
Lemma headline : 0 < 1.
Proof. by []. Qed.

(** a.  @composes: headline *)
Lemma reaches_main : 0 < 2.
Proof. by []. Qed.
```

- [ ] **Step 2: H003.yaml**

```yaml
id: H003
category: formatting
title: "@composes chain does not reach a @main lemma within the commit"
severity: warning
enabled: true
stage_mode: stage1_only
authority:
  - peer-feedback-2026-04
fast_check:
  kind: comment_composes_reachability
scope: changed_lemmas
fix_hint: "Point the helper's @composes (directly or transitively) at a lemma tagged @main, or retag the helper. Cross-file chains are not checked; this fires only on intra-commit chains that demonstrably dead-end."
exceptions: []
```

- [ ] **Step 3: Implement the `comment_composes_reachability` branch**

```python
    elif kind == "comment_composes_reachability":
        # Build the @composes edge graph over the manifest's entities. Mark
        # @main nodes. A helper is flagged when NO node reachable from it
        # (including via other in-manifest helpers) is @main AND every edge it
        # follows stays inside the manifest (a target outside the manifest is
        # treated as "unknown" -> not flagged, disclosed limitation).
        by_name = {}
        is_main = {}
        edges = {}
        for entity in manifest.get("entities", []):
            tag = _comment_role_tag(entity)
            nm = entity.get("name", "")
            by_name[nm] = entity
            is_main[nm] = bool(tag and tag["kind"] == "main")
            edges[nm] = list(tag["targets"]) if (tag and tag["kind"] == "composes") else []
        for entity in manifest.get("entities", []):
            if not strict_comment_coverage and not _entity_touched(entity):
                continue
            tag = _comment_role_tag(entity)
            if not tag or tag["kind"] != "composes":
                continue
            nm = entity.get("name", "")
            # BFS within the manifest.
            seen, stack, reached_main, left_manifest = set(), list(edges[nm]), False, False
            while stack:
                t = stack.pop()
                if t in seen:
                    continue
                seen.add(t)
                if t not in by_name:
                    left_manifest = True
                    continue
                if is_main.get(t):
                    reached_main = True
                    break
                stack.extend(edges.get(t, []))
            if not reached_main and not left_manifest:
                findings.append({
                    "rule_id": rule["id"], "file": entity["file"],
                    "line_start": entity["line_start"], "line_end": entity["line_start"],
                    "lemma_name": nm, "severity": "warning",
                    "evidence_quote": entity.get("header", "").strip(),
                    "stage": "stage1",
                    "reason": "@composes chain dead-ends without reaching a @main lemma",
                })
```

- [ ] **Step 4: Run lint**

Run: `.claude/audit/bin/lint-rules.sh`
Expected: `ok H003.yaml` (bad: `helper_a`/`helper_b` cycle reaches no main and never leaves the manifest -> >=1 finding; good: `reaches_main` reaches `headline` -> 0).

- [ ] **Step 5: Commit**

```bash
git add .claude/audit/template/rules/H003.yaml .claude/audit/template/rules/H003.md \
        .claude/audit/bin/stage1-regex.py \
        .claude/audit/fixtures/bad/H003.v .claude/audit/fixtures/good/H003.v
git commit -m "audit: add H003 intra-commit @composes reachability (warning)"
```

---

### Task 6: AUTHORITY.md, CLAUDE.md, full lint green

**Files:**
- Modify: `.claude/audit/template/rules/AUTHORITY.md`
- Modify: `CLAUDE.md`

- [ ] **Step 1: Replace the AUTHORITY comment-template section**

Replace the "## Comment template for lemmas, theorems, and nontrivial definitions" section with the tag contract: the three tags, the `main_purpose_labels` enum, the content floor, and the worked examples from the spec (`docs/superpowers/specs/2026-06-05-comment-and-stage2-redesign-design.md`, "The contract" and "Grammar" sections). Keep the "## Naming conformance or justification" section unchanged.

- [ ] **Step 2: Rewrite the CLAUDE.md "Comment quality (H-series)" section**

Replace it with: H001 (error) absent/degenerate/no-comment role tag; H002 (error) tag invalid (empty, bad-label, dangling @composes, malformed/wrong-kind); H003 (warning) intra-commit @composes does not reach a @main; all `stage1_only`. Note `main_purpose_labels` is configurable and the `touched_header`-based migration grandfathers substantive legacy comments.

- [ ] **Step 3: Full lint + e2e**

Run: `.claude/audit/bin/lint-rules.sh --full`
Expected: every rule `ok`, and `audit-e2e-test.sh` passes.

- [ ] **Step 4: Commit**

```bash
git add .claude/audit/template/rules/AUTHORITY.md CLAUDE.md
git commit -m "docs: AUTHORITY and CLAUDE describe the comment tag contract"
```

---

### Task 7: Real-file commit-mode integration sanity

**Files:** none modified; verification only.

- [ ] **Step 1: Stage a real edit and dry-run the audit**

Pick a real file, for example add an `@main` tag above an existing main lemma in
`pgg-smc/instances/abelian/abelian_word_collapse.v`, stage it, and run the
single-file auditor:

```bash
.claude/audit/bin/audit-file.sh --file pgg-smc/instances/abelian/abelian_word_collapse.v --stage1-only --rule H001,H002,H003 --json
```
Expected: the tagged lemma yields no H001/H002; an untagged touched lemma yields H001 error. Confirm no Python tracebacks.

- [ ] **Step 2: Confirm the grandfather path on a body-only change**

Edit only a proof body (not the header, not the comment) of a pre-existing,
substantively-commented but untagged lemma; stage it; run the same command.
Expected: H001 fires at `warning` severity (grandfathered), not error.

- [ ] **Step 3: No commit** (verification task). Revert the scratch edits.

**Phase 1 is complete and self-contained: the comment rules are deterministic Stage-1 regex, the LLM no longer grades comments, and the migration grandfathers legacy comments.**

---

# PHASE 2 — Part B: Stage-2 architecture

> Phase 2 begins only after Phase 1 is merged and green. Task 8 is a gating spike; do not implement Tasks 9-11 until its success criteria are met and recorded.

### Task 8: SPIKE — deterministic kernel driver (gating)

**Goal:** produce a written recipe (commit it to `docs/superpowers/specs/2026-06-05-kernel-driver-recipe.md`) proving the no-LLM mechanisms work, including the E001 mechanism that was not run end-to-end during design.

- [ ] **Step 1: D001 clear-replay on the known counterexample**

Using rocq-mcp against `pgg-smc/groups/free_group_ball.v`, open `letter_inv_lt`,
issue `clear Hr.` then replay the original proof script. Record that the replay
FAILS (Hr is implicitly used; must NOT be flagged). Then add a decoy unused
hypothesis to a scratch copy and confirm `clear` + replay SUCCEEDS (flagged).
Success criterion: the false positive from the old rule does not reproduce.

- [ ] **Step 2: E001 step-minus-terminator on a real proof**

Open a multi-step proof; step the script up to but not including the last
terminator; read `proof_finished`. Confirm it is `false` when the last tactic is
load-bearing (no E001) and `true` for a constructed redundant-tail proof (E001).
Record the exact rocq-mcp calls and how the "last terminator" line is identified
(handle `;`-chains and bullets: test each trailing sentence boundary).

- [ ] **Step 3: Staged-blob materialization + latency**

Write a file's staged blob (`git show :<file>`) to a same-directory hidden temp
file, open it, and confirm imports resolve. Record cold/warm open latency and
RSS, and the abstain signals (open failure, missing reference, parse error,
timeout).

- [ ] **Step 4: Commit the recipe**

```bash
git add docs/superpowers/specs/2026-06-05-kernel-driver-recipe.md
git commit -m "spec: deterministic kernel driver recipe (D001 clear-replay, E001 step)"
```

**GATE:** if Step 1 or Step 2 cannot be made deterministic, stop and revisit the design (keep D001/E001 in the pre-merge LLM `--full` run only). Do not proceed to Task 9 otherwise.

---

### Task 9: Add a `kernel` stage mode; route D001/E001

**Files:**
- Modify: `.claude/audit/template/schema/rule.schema.json` (stage_mode enum)
- Modify: `.claude/audit/template/rules/D001.yaml`, `E001.yaml`
- Modify: `.claude/audit/bin/stage2-agent.py` (skip `kernel` rules in `load_rules`)
- Modify: `.claude/audit/bin/lint-rules.py` (treat `kernel` like `sentinel`)

- [ ] **Step 1:** Add `"kernel"` to `stage_mode` enum in the schema.
- [ ] **Step 2:** Set `stage_mode: kernel` on D001 and E001; remove their `kernel_contract` blocks (the kernel pass owns the mechanism now); keep their `agent_prompt` removed so the schema's `stage2_only/both -> agent_prompt` rule does not apply.
- [ ] **Step 3:** In `stage2-agent.py` load_rules, skip rules whose `stage_mode == "kernel"`.
- [ ] **Step 4:** In `lint-rules.py` `run_fixture_test`, treat `stage_mode == "kernel"` like `sentinel` (parity fixtures must exist, but no Stage-1/Stage-2 assertion runs; the kernel is exercised by Task 16's integration test).
- [ ] **Step 5:** Run `.claude/audit/bin/lint-rules.sh`; expected `ok D001.yaml`, `ok E001.yaml`.
- [ ] **Step 6:** Commit: `git commit -m "audit: add kernel stage_mode, route D001/E001 to it"`.

---

### Task 10: Implement `bin/stage1_5-kernel.py`

**Files:**
- Create: `.claude/audit/bin/stage1_5-kernel.py`, `.claude/audit/bin/stage1_5-kernel.sh`

- [ ] **Step 1:** Implement per the Task-8 recipe: read the Tier-0 manifest; for each touched file, materialize the staged blob to a same-directory hidden temp file; open one session; for each in-scope D001 candidate run clear-replay (emit only on clean replay-break-free unused), for E001 run step-minus-terminator. Abstain (emit nothing for the file) on any open/import/parse/timeout failure; wall-clock gate via `per_commit_wall_seconds`. Emit `{"findings": [...]}` in the Stage-1 finding schema with `"stage": "stage1.5"` and `severity: warning`.
- [ ] **Step 2:** Guard the temp file with a unique hidden name and remove it in a `finally`.
- [ ] **Step 3:** Test on the real counterexample: run the script on a synthetic manifest naming `letter_inv_lt` and assert zero D001 findings; on a manifest with a genuinely unused hypothesis assert one. (This is the regression for the design bug.)
- [ ] **Step 4:** Commit.

---

### Task 11: Wire Stage 1.5 in, delete Tier-K

**Files:**
- Modify: `.claude/audit/bin/audit.sh`, `.claude/audit/bin/audit-file.sh`
- Modify: `.claude/audit/bin/report-merge.py` (only if folding requires it)
- Delete: `.claude/audit/bin/tier-k-verify.py`, `tier-k-verify.sh`

- [ ] **Step 1:** In `audit.sh`, after Stage 1, run `stage1_5-kernel.py` to `KERNEL` json, then fold into Stage 1 before merge: `jq -s '{findings: (.[0].findings + .[1].findings)}' "$STAGE1" "$KERNEL" > "$STAGE1_MERGED"` and pass `$STAGE1_MERGED` to `report-merge.py`. Remove the `tier-k-verify.sh` invocation (lines ~294-295) and pass an empty `{"verdicts": []}` for the TIERK arg.
- [ ] **Step 2:** Mirror in `audit-file.sh`: replace the `--no-tier-k`/tier-k block with the kernel pass; keep `--stage1-only` skipping both Stage 2 and the kernel.
- [ ] **Step 3:** `git rm` the two tier-k scripts.
- [ ] **Step 4:** Run `.claude/audit/bin/lint-rules.sh --full`; expected green.
- [ ] **Step 5:** Commit.

---

### Task 12: Retire C001 to a regex stub

**Files:** `.claude/audit/template/rules/C001.yaml`/`.md`, fixtures, delete `snapshots/C001.json`.

- [ ] **Step 1:** Set C001 `stage_mode: stage1_only` with `fast_pattern.pattern: '^\s*(Inductive|Record)\b[^.]*:\s*forall\s*\{'` (currently zero repo matches), `severity: warning`.
- [ ] **Step 2:** Write `bad/C001.v` with one matching header and `good/C001.v` with a plain Record. Delete the stage2 snapshot.
- [ ] **Step 3:** Lint green. Commit.

---

### Task 13: Two run modes and commit-time G001 scoping

**Files:** `.claude/audit/bin/stage2-agent.py`, `.claude/audit/bin/audit.sh` (mode flag), `.claude/audit/template/rules/G001.yaml`.

- [ ] **Step 1:** Add an env/flag `ROCQ_AUDIT_FULL` (set by `--full`). In `stage2-agent.py`, when not full, restrict the active rule set to commit-relevant rules and filter G001 candidate entities to those with `touched_header == true`. When full, keep all entities and rules.
- [ ] **Step 2:** Test: a synthetic manifest with one body-only-changed entity and one header-changed entity; assert commit mode sends only the header-changed one to G001's candidate set.
- [ ] **Step 3:** Lint/snapshot for G001 unchanged (still stage2). Commit.

---

### Task 14: Per-chunk prompt pruning

**Files:** `.claude/audit/bin/stage2-agent.py` (`build_prompt`).

- [ ] **Step 1:** Build `rule_brief` from only the rules active in the current run mode, and trim the AUTHORITY excerpt to the sections those rules cite (a small mapping `rule_id -> [section headers]`). 
- [ ] **Step 2:** Test: assert the commit-mode prompt for a G001-only run contains the G001 stanza and the "Standard suffixes"/"Lemma naming grammar" sections and excludes the H-series and D001/E001 stanzas.
- [ ] **Step 3:** Refresh affected snapshots (`lint-rules.sh --refresh-snapshots`), verify, commit.

---

### Task 15: Locality chunking

**Files:** `.claude/audit/bin/stage2-agent.py` (`chunk_entities`).

- [ ] **Step 1:** Replace the flat slice with grouping by `(file, Section)` adjacency at `chunk_size = 3`, preserving the `ROCQ_AUDIT_CHUNK_SIZE` override.
- [ ] **Step 2:** Test: two entities in the same file adjacent in source land in the same chunk; entities in different files do not share a chunk.
- [ ] **Step 3:** Refresh snapshots if fingerprints shift, verify, commit.

---

### Task 16: Phase-2 integration and regression

- [ ] **Step 1:** Regression: confirm the kernel D001 does NOT flag `letter_inv_lt` and DOES flag a constructed unused hypothesis (the design-bug regression), run from `audit-file.sh`.
- [ ] **Step 2:** `.claude/audit/bin/lint-rules.sh --full` green.
- [ ] **Step 3:** Token sanity: on a 3-entity staged commit, confirm Stage 2 makes zero agent calls unless a header changed (only then a single pruned G001 micro-call). Record observed token usage from `central-state/token-usage.json`.
- [ ] **Step 4:** Update `CLAUDE.md` "rocq-audit pre-commit pipeline" to describe Stage 1.5, the removal of Tier-K, and the two run modes. Commit.

---

## Self-Review

**Spec coverage:** Part A tags/severity/migration/scope/config/catalog -> Tasks 1-6. `@composes` git-grep -> Task 4. H003 reachability -> Task 5. Part B kernel pass -> Tasks 8-11. Delete Tier-K -> Task 11. Retire C001 -> Task 12. Commit-time G001 scoping + two modes -> Task 13. Prompt pruning -> Task 14. Locality chunking -> Task 15. Residual-risk verifications (E001 end-to-end, staged-blob, latency) -> Task 8 spike + Task 16. H004 (opt-in agent) is intentionally deferred: it is `enabled: false` by default and would force a live-agent snapshot in lint; add it only if `comment_semantic_check` is turned on.

**Placeholder scan:** no "TBD"/"handle edge cases"; each code step shows the code; Phase-2 kernel specifics are gated behind the Task-8 spike that produces the exact commands.

**Type consistency:** finding dicts use the same keys as `stage1-regex.py` emits (`rule_id`, `file`, `line_start`, `line_end`, `lemma_name`, `severity`, `evidence_quote`, `stage`, optional `reason`). Helper names (`_comment_role_tag`, `_content_floor_ok`, `_composes_target_exists`, `_entity_touched`, `_main_purpose_labels`) are referenced consistently across Tasks 2-5. The `apply_fast_check` signature gains `cfg` in Task 3 and is used in Task 4.
