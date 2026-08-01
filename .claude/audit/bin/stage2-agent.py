#!/usr/bin/env python3
"""Stage 2 agent driver.

Spawns `claude -p` with the `rocq-auditor` agent, passes it a structured
packet (Tier 0 manifest, enabled Stage 2 rules, authority, Stage 1
findings), validates the JSON response against `auditor-response.schema.json`,
chunks per `max_entities_per_invocation`, and re-runs any chunk containing a
`low`-confidence finding under the escalation model.

Invoked as: stage2-agent.py <tier0.json> <stage1.json>
Emits: combined findings on stdout.
"""
from __future__ import annotations
import concurrent.futures
import hashlib
import json
import math
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

import yaml
import jsonschema

ROOT = Path(os.environ.get("REPO_ROOT", ".")).resolve()
AUDIT_DIR = Path(os.environ.get("AUDIT_DIR", ROOT / ".claude" / "audit")).resolve()
# Central state: content-addressed caches and append-only logs that span runs.
# When AUDIT_CENTRAL is unset we fall back to `AUDIT_DIR/../../central-state`
# for compatibility with legacy callers that still pass the engine root.
AUDIT_CENTRAL = Path(os.environ.get(
    "AUDIT_CENTRAL",
    AUDIT_DIR.parent.parent / "central-state"
        if AUDIT_DIR.parent.name == "runs"
        else AUDIT_DIR / "central-state",
)).resolve()
STATE = AUDIT_DIR / "state"
CACHE_DIR = AUDIT_CENTRAL / "stage2-cache"
SNAPSHOTS = (AUDIT_DIR / "snapshots") if (AUDIT_DIR / "snapshots").exists() else (AUDIT_DIR.parent.parent / "snapshots")
def _schema_file() -> Path:
    p = AUDIT_DIR / "schema" / "auditor-response.schema.json"
    if p.exists():
        return p
    return AUDIT_DIR / "template" / "schema" / "auditor-response.schema.json"


SCHEMA_FILE = _schema_file()


def _rules_dir() -> Path:
    if (AUDIT_DIR / "rules").exists():
        return AUDIT_DIR / "rules"
    if (AUDIT_DIR / "template" / "rules").exists():
        return AUDIT_DIR / "template" / "rules"
    return AUDIT_DIR / "rules"


def _schema_dir() -> Path:
    if (AUDIT_DIR / "schema").exists():
        return AUDIT_DIR / "schema"
    if (AUDIT_DIR / "template" / "schema").exists():
        return AUDIT_DIR / "template" / "schema"
    return AUDIT_DIR / "schema"


def _config_path() -> Path:
    p = AUDIT_DIR / "config.yaml"
    if p.exists():
        return p
    q = AUDIT_DIR / "template" / "config.yaml"
    if q.exists():
        return q
    return p


def load_config() -> dict:
    with open(_config_path()) as f:
        return yaml.safe_load(f) or {}


def load_rules() -> list[dict]:
    rules = []
    for p in sorted(_rules_dir().glob("*.yaml")):
        with open(p) as f:
            r = yaml.safe_load(f) or {}
        if not r.get("enabled", True):
            continue
        if r.get("stage_mode") not in ("stage2_only", "both"):
            continue
        md = p.with_suffix(".md")
        if md.exists():
            with open(md) as f:
                r["_markdown"] = f.read()
        rules.append(r)
    return rules


COMMENT_STYLE_PREAMBLE = """
## Comment-style guidance for H002 fix_sketch

When emitting a `fix_sketch` for an H002 finding, produce a 1-8 line
(Lemma/Theorem/Fact/Corollary/Proposition), 1-15 line (non-Local
multi-line Definition/Fixpoint), or 1-25 line (Hypothesis/Variable)
PROSE comment. Do NOT produce a stacked-slot template (`Kind:` /
`Why:` / `Used by:` on separate lines). Do not restate the type
signature; do not cite plan files, plan-task tokens, or absolute
line numbers.

### Purposive framing first

The first sentence must state the entity's PURPOSE in the larger
system — pick one of:

- ROLE: what this entity does in the architecture and what other
  entities depend on it.
- RATIONALE: why this design choice exists; what invariant it
  discharges.
- ALTERNATIVE: what other choices are compatible with the type
  and why this one was selected.

Reserve proof-tactic mechanics (which lemma the proof reduces to,
which obligations collapse, which side-conditions unify) for a
second sentence — and only when the mechanics themselves carry
architectural meaning (e.g., `emptym` location set enabling
`fseparate0m` IS a design choice; "the proof is by induction on n"
usually is not).

The H002 MECHANISM_ONLY detector fires when the first 200 chars
contain a mechanism stop-phrase (`reduces to`, `by case analysis`,
`discharges`, `obligations`, `by reflexivity`, `cancellation
bijection`, ...) AND fewer than 2 architecture/purposive nouns
(`bridge`, `adversary`, `predictor`, `package`, `chain`, `game`,
`space`, `AHE`, `SSProve`, `IND-CPA`, `secrecy`, ...). Aim for
≥ 2 architecture nouns in the first sentence.

### Three-tier example: `chmsg_of_msgK`

Mechanism-only (AVOID — trips MECHANISM_ONLY):
```
(* Cancellation bijection for the message-side type bridge.
   The proof reduces directly to enum_rankK. *)
```

Purposive (preferred):
```
(* Bijection to build type bridge between AHE and SSProve. *)
```

Purposive + architecturally-informative mechanism (also preferred):
```
(* Bijection bridging the AHE-side `plain AHE` Type and the
   SSProve-side `t_msg` choice_type code. Used by every
   encryption-oracle proof to round-trip messages through the
   SSProve type-code layer. *)
```

Good fix_sketch examples:

```
(* Bijection to build type bridge between AHE and SSProve. *)
```

```
(* For every predictor in the considered class, the probability that
   the predictor correctly guesses V_2 from the leaked-ciphertext
   game is at most 1 / card_t_msg. *)
```

```
(* A stateless oracle-free adversary. When asked, samples a fresh
   uniform plaintext and returns it as its guess at V_2. *)
```

Bad fix_sketch examples (DO NOT emit):

```
(** foo - cancel law for the X bijection. Routes through eq_rect.
    Kind: cancellation.
    Why: discharges [foo] (line 130).
    Used by: T1 rebuild. *)
```

```
(** card_X - cardinality index used by Y_secrecy's residual bound
    [1 / card_X]. Set equal to card_msg.
    Kind: concrete-carrier index.
    Why: discharges abstract section parameter at concrete carriers.
    Used by: Z_random_guess. *)
```

Refer to AUTHORITY.md's "Acceptable examples" and "Unacceptable
examples" sections for the full convention.
"""


def load_authority() -> str:
    """Return AUTHORITY.md content with the prose-style comment guidance
    prepended so it sits at the top of every Stage 2 prompt.

    The preamble (COMMENT_STYLE_PREAMBLE) is the load-bearing thing for
    H002: sonnet's prior tends to bulleted/templated explanations, so
    putting the good/bad examples at the FRONT of the authority excerpt
    (rather than buried inside the rule body) gives the agent the most
    direct exposure to the target style.
    """
    p = _rules_dir() / "AUTHORITY.md"
    body = p.read_text() if p.exists() else ""
    return COMMENT_STYLE_PREAMBLE + "\n" + body


def load_schema() -> dict:
    with open(SCHEMA_FILE) as f:
        return json.load(f)


def preflight_permission_test(model: str) -> tuple[bool, str]:
    """Invoke the agent with a synthetic request that would require Edit.
    Expect refusal. Passes when the agent does NOT produce a JSON finding that
    edits a file.

    Phase 1.5 implementation: send a trivial prompt asking for a JSON envelope
    confirming tool restrictions. The agent's tool list is the real enforcer;
    this test merely confirms the invocation works.
    """
    try:
        proc = subprocess.run(
            ["claude", "-p",
             "Emit exactly the JSON: {\"passed\": true, \"findings\": [], \"tokens_used\": 0}. No other text.",
             "--agent", "rocq-auditor",
             "--model", model,
             "--output-format", "json",
             "--allowedTools", "Read,Grep,Glob",
             "--disallowedTools", "Edit,Write,Bash",
             "--disable-slash-commands",
             "--max-budget-usd", "1"],
            capture_output=True, text=True, timeout=120, stdin=subprocess.DEVNULL,
        )
    except subprocess.TimeoutExpired:
        return False, "pre-flight timed out"
    except FileNotFoundError:
        return False, "claude CLI not found on PATH"
    if proc.returncode != 0:
        return False, f"pre-flight rc={proc.returncode}: {proc.stderr[:200]}"
    return True, ""


def chunk_entities(entities: list[dict], n: int) -> list[list[dict]]:
    return [entities[i:i + n] for i in range(0, len(entities), n)] if entities else []


def build_prompt(manifest_chunk: dict, stage1_findings: list[dict], rules: list[dict],
                 authority: str, chunk_meta: dict, escalation: bool) -> str:
    """Build the stdin packet handed to the agent."""
    rule_brief = []
    for r in rules:
        rule_brief.append({
            "id": r["id"],
            "title": r["title"],
            "severity": r["severity"],
            "authority": r.get("authority", []),
            "agent_prompt": r.get("agent_prompt", ""),
            "fix_hint": r.get("fix_hint", ""),
            "kernel_contract_name": (r.get("kernel_contract") or {}).get("name"),
            "exceptions": r.get("exceptions", []),
            "markdown": r.get("_markdown", ""),
        })
    packet = {
        "authority_excerpt": authority,
        "rules": rule_brief,
        "manifest": manifest_chunk,
        "stage1_findings": stage1_findings,
        "chunk": chunk_meta,
        "escalation": escalation,
    }
    return "Audit this Rocq commit against the MathComp and Infotheo style rules. " \
           "Return JSON matching the response schema. No prose outside the JSON.\n\n" \
           "INPUT:\n" + json.dumps(packet, indent=2, ensure_ascii=False)


def call_agent(prompt: str, model: str, schema: dict, budget_usd: float = 1.0, timeout: int = 600) -> tuple[dict, str]:
    """Invoke `claude -p` and parse the response envelope. Returns (findings_obj, error_str)."""
    try:
        proc = subprocess.run(
            ["claude", "-p", prompt,
             "--agent", "rocq-auditor",
             "--model", model,
             "--output-format", "json",
             # The claude CLI's --json-schema validator rejects the
             # draft-2020-12 "$schema" reference; strip meta keys.
             "--json-schema", json.dumps(
                 {k: v for k, v in schema.items()
                  if k not in ("$schema", "$id")}),
             "--allowedTools", "Read,Grep,Glob",
             "--disallowedTools", "Edit,Write,Bash",
             "--disable-slash-commands",
             "--max-budget-usd", str(budget_usd)],
            capture_output=True, text=True, timeout=timeout, stdin=subprocess.DEVNULL,
        )
    except subprocess.TimeoutExpired:
        return {}, "agent call timed out"
    except FileNotFoundError:
        return {}, "claude CLI not found"
    if proc.returncode != 0:
        return {}, f"agent rc={proc.returncode}: {proc.stderr[:400]}"
    # claude -p --output-format json returns an envelope with 'result' field.
    try:
        envelope = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {}, f"non-JSON stdout: {proc.stdout[:200]}"
    result_str = envelope.get("result", "")
    if isinstance(result_str, dict):
        result = result_str
    else:
        try:
            result = json.loads(result_str)
        except json.JSONDecodeError:
            return {}, f"result field not JSON: {result_str[:200]}"
    try:
        jsonschema.validate(instance=result, schema=schema)
    except jsonschema.ValidationError as e:
        return {}, f"schema violation: {e.message}"
    # Pull real token usage from the envelope. The agent's own `tokens_used`
    # is unreliable because we don't instruct it to introspect cost.
    usage = envelope.get("usage") or {}
    in_tok = int(usage.get("input_tokens", 0)) + int(usage.get("cache_read_input_tokens", 0)) + int(usage.get("cache_creation_input_tokens", 0))
    out_tok = int(usage.get("output_tokens", 0))
    result["tokens_used"] = in_tok + out_tok
    result["_input_tokens"] = in_tok
    result["_output_tokens"] = out_tok
    return result, ""


def chunk_fingerprint(chunk_entities_: list[dict], rules: list[dict]) -> str:
    h = hashlib.sha256()
    payload = {
        "entities": [{"file": e["file"], "name": e.get("name"),
                      "line_start": e["line_start"], "line_end": e["line_end"],
                      "body": e["body"]} for e in chunk_entities_],
        "rules": [{"id": r["id"], "agent_prompt": r.get("agent_prompt"),
                   "markdown": r.get("_markdown", "")} for r in rules],
    }
    h.update(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8"))
    return h.hexdigest()[:16]


def cache_get(fp: str) -> dict | None:
    p = CACHE_DIR / f"stage2-cache-{fp}.json"
    if p.exists():
        try:
            with open(p) as f:
                return json.load(f)
        except Exception:
            return None
    return None


def cache_put(fp: str, result: dict) -> None:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    p = CACHE_DIR / f"stage2-cache-{fp}.json"
    with open(p, "w") as f:
        json.dump(result, f)


def token_guard_read() -> dict:
    AUDIT_CENTRAL.mkdir(parents=True, exist_ok=True)
    p = AUDIT_CENTRAL / "token-usage.json"
    if p.exists():
        try:
            return json.load(open(p))
        except Exception:
            pass
    return {"daily": {}, "monthly": {}}


def token_guard_update(used: int) -> None:
    d = token_guard_read()
    today = time.strftime("%Y-%m-%d")
    month = time.strftime("%Y-%m")
    d["daily"][today] = int(d["daily"].get(today, 0)) + int(used)
    d["monthly"][month] = int(d["monthly"].get(month, 0)) + int(used)
    # Trim old.
    d["daily"] = {k: v for k, v in d["daily"].items() if k.startswith(today[:7]) or k == today}
    AUDIT_CENTRAL.mkdir(parents=True, exist_ok=True)
    with open(AUDIT_CENTRAL / "token-usage.json", "w") as f:
        json.dump(d, f)


def main() -> int:
    if len(sys.argv) < 3:
        print("usage: stage2-agent.py <tier0.json> <stage1.json>", file=sys.stderr)
        return 2
    cfg = load_config()
    rules = load_rules()
    if not rules:
        print(json.dumps({"findings": [], "note": "no Stage 2 rules enabled"}))
        return 0
    with open(sys.argv[1]) as f:
        manifest = json.load(f)
    with open(sys.argv[2]) as f:
        stage1 = json.load(f)
    authority = load_authority()
    schema = load_schema()

    default_model = cfg.get("audit_model", "sonnet")
    escalation_model = cfg.get("escalation_model", "opus")

    # Per-rule model routing: if any enabled rule sets `model:` in its
    # YAML, promote the entire chunk to the highest-tier model among
    # the chunk's rules. Strategy chosen over per-model chunk splitting
    # to avoid doubling the agent-invocation count when multiple rules
    # share a model preference. See plan revision 2 (1.5.E) for the
    # rationale.
    MODEL_TIER = {"haiku": 0, "sonnet": 1, "opus": 2}
    candidate_models = [r.get("model") or default_model for r in rules]
    candidate_models.append(default_model)
    chunk_model = max(
        candidate_models,
        key=lambda m: MODEL_TIER.get(m, 1),
    )
    daily_cap = int(cfg.get("daily_token_cap", 2000000))
    on_failure = cfg.get("on_agent_failure", "block")
    # Env-var override: callers (typically a fix-flow subagent) can pass
    # ROCQ_AUDIT_ADVISORY=1 to downgrade block to advisory for this
    # invocation only, without editing the config file on disk.
    if os.environ.get("ROCQ_AUDIT_ADVISORY") == "1" or os.environ.get("ROCQ_AUDIT_FIX_FLOW") == "1":
        on_failure = "advisory"
    parallelism_cap = int(os.environ.get("ROCQ_AUDIT_WORKERS") or cfg.get("stage2_parallelism_cap", 8))
    wall_seconds = int(os.environ.get("ROCQ_AUDIT_WALL_SECONDS") or cfg.get("per_commit_wall_seconds", 600))

    entities = manifest.get("entities", [])
    entity_count = len(entities)

    # Adaptive chunk size: max(3, min(10, ceil(n/8))). Overridable.
    if os.environ.get("ROCQ_AUDIT_CHUNK_SIZE"):
        chunk_size = int(os.environ["ROCQ_AUDIT_CHUNK_SIZE"])
    elif entity_count <= 0:
        chunk_size = 3
    else:
        chunk_size = max(3, min(10, math.ceil(entity_count / 8)))

    # Adaptive token cap. Real runs show ~40-50k tokens per chunk because
    # each chunk carries the full rule catalog plus AUTHORITY.md. The
    # formula max(75000, 60000 * chunk_count_estimate) fits observed usage
    # with headroom; the operator can override via ROCQ_AUDIT_TOKEN_CAP or
    # the static `per_commit_token_cap` key in config.yaml.
    if os.environ.get("ROCQ_AUDIT_TOKEN_CAP"):
        per_commit_cap = int(os.environ["ROCQ_AUDIT_TOKEN_CAP"])
    elif cfg.get("per_commit_token_cap"):
        per_commit_cap = int(cfg["per_commit_token_cap"])
    else:
        est_chunks = max(1, math.ceil(max(entity_count, 1) / 5))
        per_commit_cap = max(75000, 60000 * est_chunks)

    # Cost guard (daily). Emits an error-severity S996 sentinel so that
    # `report-merge.py` blocks the commit instead of treating the empty
    # findings list as a clean verdict. Earlier versions returned `findings:
    # []` which caused the gate to exit 0 despite Stage 2 never running.
    usage = token_guard_read()
    today = time.strftime("%Y-%m-%d")
    if int(usage["daily"].get(today, 0)) >= daily_cap:
        out = {
            "findings": [{
                "rule_id": "S996",
                "file": "rocq-audit",
                "line_start": 1, "line_end": 1,
                "severity": "error",
                "evidence_quote": f"daily_token_cap {daily_cap} exceeded before any chunk ran",
                "closeness": "near",
                "explanation": (
                    "Stage 2 aborted: the daily token cap had already been "
                    "reached before the first chunk. No Stage 2 findings "
                    "were produced. The commit is blocked until the cap is "
                    "raised, the day resets, or the operator explicitly "
                    "bypasses with ROCQ_AUDIT_BYPASS=1."
                ),
                "fix_sketch": "Raise daily_token_cap in template/config.yaml, wait until UTC midnight, or bypass with ROCQ_AUDIT_BYPASS=1.",
                "confidence": "high",
                "stage": "stage2",
            }],
            "error": f"daily_token_cap {daily_cap} exceeded",
            "budget": {"stop_reason": "daily_cap", "entity_count": entity_count},
            "stage2_incomplete": True,
        }
        print(json.dumps(out))
        return 0 if on_failure == "advisory" else 2

    chunks = chunk_entities(entities, chunk_size) or [[]]
    chunk_count = len(chunks) if entities else 0
    workers = min(parallelism_cap, max(1, chunk_count)) if chunk_count else 1

    tokens_lock = threading.Lock()
    state = {
        "tokens_used": 0,
        "input_tokens": 0,
        "output_tokens": 0,
        "combined": [],
        "deferred_chunks": 0,
        "stop_reason": "clean",
        "s997_emitted": False,
    }

    def process_chunk(idx: int, ch: list[dict]) -> None:
        chunk_manifest = dict(manifest, entities=ch)
        fp = chunk_fingerprint(ch, rules)
        cached = cache_get(fp)
        if cached is not None:
            result = cached
            err = ""
        else:
            prompt = build_prompt(chunk_manifest, stage1.get("findings", []), rules,
                                  authority, {"index": idx, "total": chunk_count}, False)
            result, err = call_agent(prompt, chunk_model, schema)
            if not err:
                cache_put(fp, result)
        if err:
            with tokens_lock:
                state["combined"].append({
                    "rule_id": "S998",
                    "file": "rocq-audit",
                    "line_start": 1, "line_end": 1,
                    "severity": "warning",
                    "evidence_quote": err,
                    "closeness": "near",
                    "explanation": f"Stage 2 call failed for chunk {idx}; see logs.",
                    "fix_sketch": "Retry the commit. If repeated, check agent configuration.",
                    "confidence": "high",
                    "stage": "stage2",
                })
            return

        findings_local = result.get("findings", [])
        for f in findings_local:
            f["stage"] = "stage2"

        # Per-chunk escalation of low-confidence findings.
        low_conf = [f for f in findings_local if f.get("confidence") == "low"]
        esc_tokens = 0
        if low_conf and escalation_model != chunk_model:
            prompt = build_prompt(chunk_manifest, stage1.get("findings", []), rules,
                                  authority, {"index": idx, "total": chunk_count}, True)
            esc_result, esc_err = call_agent(prompt, escalation_model, schema)
            if not esc_err:
                esc_tokens = int(esc_result.get("tokens_used", 0))
                findings_local = esc_result.get("findings", [])
                for f in findings_local:
                    f["stage"] = "stage2"
                    f.setdefault("escalated_model", escalation_model)

        chunk_tokens = int(result.get("tokens_used", 0)) + esc_tokens
        with tokens_lock:
            state["tokens_used"] += chunk_tokens
            state["combined"].extend(findings_local)

    t0 = time.monotonic()
    wall_cap = float(wall_seconds)
    wall_soft = wall_cap * 0.8

    def elapsed() -> float:
        return time.monotonic() - t0

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures: dict[concurrent.futures.Future, int] = {}
        submitted = 0
        for idx, ch in enumerate(chunks):
            if not ch:
                continue
            # Pre-submission guard against the per-commit token cap.
            with tokens_lock:
                if state["tokens_used"] >= per_commit_cap:
                    state["deferred_chunks"] += 1
                    state["stop_reason"] = "token_cap"
                    continue
            futures[pool.submit(process_chunk, idx, ch)] = idx
            submitted += 1

        # Collect with soft/hard wall-clock awareness.
        remaining = set(futures.keys())
        while remaining:
            # Check wall-clock thresholds before blocking on the next future.
            el = elapsed()
            if el >= wall_cap:
                state["stop_reason"] = "wall_cap"
                # Do not cancel; let in-flight finish. But count any chunks
                # still unfinished beyond this point as deferred and stop
                # waiting.
                for fut in list(remaining):
                    if not fut.done():
                        state["deferred_chunks"] += 1
                break
            if not state["s997_emitted"] and el >= wall_soft:
                state["s997_emitted"] = True
                with tokens_lock:
                    state["combined"].append({
                        "rule_id": "S997",
                        "file": "rocq-audit",
                        "line_start": 1, "line_end": 1,
                        "severity": "info",
                        "evidence_quote": f"wall-clock at {int(el)}s of {int(wall_cap)}s budget",
                        "closeness": "near",
                        "explanation": "Stage 2 passed the 80% wall-clock mark; in-flight chunks continue.",
                        "fix_sketch": "If this recurs, raise per_commit_wall_seconds or split the commit.",
                        "confidence": "high",
                        "stage": "stage2",
                    })

            # Wait for any future for up to the remaining budget slice.
            slice_timeout = max(1.0, min(wall_cap - el, 5.0))
            done, _ = concurrent.futures.wait(remaining, timeout=slice_timeout,
                                              return_when=concurrent.futures.FIRST_COMPLETED)
            for fut in done:
                remaining.discard(fut)
                # Propagate exceptions.
                try:
                    fut.result()
                except Exception as e:
                    with tokens_lock:
                        state["combined"].append({
                            "rule_id": "S998",
                            "file": "rocq-audit",
                            "line_start": 1, "line_end": 1,
                            "severity": "warning",
                            "evidence_quote": f"worker exception: {e}",
                            "closeness": "near",
                            "explanation": "A Stage 2 worker raised an exception.",
                            "fix_sketch": "Retry the commit. If repeated, check agent configuration.",
                            "confidence": "high",
                            "stage": "stage2",
                        })

            # Post-iteration: check token cap in case a chunk just reported.
            with tokens_lock:
                if state["tokens_used"] >= per_commit_cap and state["stop_reason"] == "clean":
                    state["stop_reason"] = "token_cap"
                    # Remaining futures are allowed to finish to avoid
                    # partial cache entries; deferred count is 0 because
                    # nothing is unsubmitted at this point.

    # Emit an error-severity S996 sentinel if the run did not end cleanly.
    # Earlier versions emitted a warning-severity S999 here, which did not
    # block the commit because `report-merge.py` gates on error-severity
    # findings only. The cap-hit was then silently downgraded to a pass.
    # S996 at error severity forces the gate to exit 2 on any cap hit.
    if state["stop_reason"] != "clean":
        reasons = {
            "token_cap": f"per_commit_token_cap {per_commit_cap} reached",
            "wall_cap": f"per_commit_wall_seconds {int(wall_cap)} reached",
        }
        state["combined"].append({
            "rule_id": "S996",
            "file": "rocq-audit",
            "line_start": 1, "line_end": 1,
            "severity": "error",
            "evidence_quote": reasons.get(state["stop_reason"], state["stop_reason"]),
            "closeness": "near",
            "explanation": (
                f"Stage 2 halted: {state['stop_reason']} reached after partial run. "
                f"{state['deferred_chunks']} chunks deferred. Stage 1 findings "
                "still apply, but Stage 2 is incomplete; the commit is blocked "
                "so the operator raises the cap or acknowledges the gap."
            ),
            "fix_sketch": "Split the commit, raise the relevant cap, or re-run with ROCQ_AUDIT_WALL_SECONDS / ROCQ_AUDIT_TOKEN_CAP.",
            "confidence": "high",
            "stage": "stage2",
        })

    tokens_used = state["tokens_used"]
    token_guard_update(tokens_used)

    # Cost estimate using static pricing table. Input vs output split is not
    # reliably reported by the upstream envelope, so we approximate with a
    # 3:1 input:output ratio which matches observed audit workloads.
    pricing = cfg.get("pricing", {}) or {}
    in_rate = pricing.get(f"{default_model}_input_per_mtok", 3)
    out_rate = pricing.get(f"{default_model}_output_per_mtok", 15)
    approx_input = int(tokens_used * 0.75)
    approx_output = tokens_used - approx_input
    estimated_usd = round((approx_input * in_rate + approx_output * out_rate) / 1_000_000.0, 4)

    budget = {
        "entity_count": entity_count,
        "chunk_count": chunk_count,
        "chunk_size": chunk_size,
        "workers_used": workers,
        "tokens_used": tokens_used,
        "tokens_cap": per_commit_cap,
        "wall_ms_used": int(elapsed() * 1000),
        "wall_ms_cap": int(wall_cap * 1000),
        "deferred_chunks": state["deferred_chunks"],
        "stop_reason": state["stop_reason"],
        "estimated_usd": estimated_usd,
        "model": chunk_model,
    }

    # Top-level `stage2_incomplete` flag so `report-merge.py` can render the
    # CAP HIT banner without reparsing individual findings.
    stage2_incomplete = state["stop_reason"] in ("daily_cap", "token_cap", "wall_cap")
    out = {
        "findings": state["combined"],
        "tokens_used": tokens_used,
        "budget": budget,
        "stage2_incomplete": stage2_incomplete,
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
