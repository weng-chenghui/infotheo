#!/usr/bin/env bash
# Rocq audit pipeline orchestrator, execroot edition.
#
# Every invocation materialises a self-contained run directory under
# .claude/audit/runs/<run_id>/ from .claude/audit/template/. Cross-run
# state (attempts, oscillation, stage2 cache, bypass log, findings
# history, token usage) lives in .claude/audit/central-state/.
#
# See /Users/cheng-huiweng/.claude/plans/context-every-time-i-eager-crystal.md
# for the full architecture.
set -euo pipefail

# ---- Locate repo root and audit engine -----------------------------------
if ! REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"; then
  echo "rocq-audit: not inside a git worktree; skipping." >&2
  exit 0
fi
AUDIT_ROOT="${REPO_ROOT}/.claude/audit"
if [[ ! -d "${AUDIT_ROOT}" ]]; then
  exit 0
fi

AUDIT_TEMPLATE="${AUDIT_ROOT}/template"
AUDIT_CENTRAL="${AUDIT_ROOT}/central-state"
AUDIT_RUNS="${AUDIT_ROOT}/runs"
VENV_PY="${AUDIT_ROOT}/venv/bin/python3"

if [[ ! -d "${AUDIT_TEMPLATE}" ]]; then
  echo "rocq-audit: template directory missing at ${AUDIT_TEMPLATE}. Run the execroot migration or re-install." >&2
  exit 1
fi
if [[ ! -x "${VENV_PY}" ]]; then
  echo "rocq-audit: venv missing at ${AUDIT_ROOT}/venv; run 'python3 -m venv ${AUDIT_ROOT}/venv && ${AUDIT_ROOT}/venv/bin/pip install pyyaml jsonschema'." >&2
  exit 1
fi

mkdir -p "${AUDIT_CENTRAL}/attempts" "${AUDIT_CENTRAL}/oscillation" "${AUDIT_CENTRAL}/stage2-cache" "${AUDIT_RUNS}"

# ---- Parse inputs --------------------------------------------------------
MODE="${1:-}"
BYPASS="${ROCQ_AUDIT_BYPASS:-0}"
ADVISORY_OVERRIDE="${ROCQ_AUDIT_ADVISORY:-0}"
if [[ "${ROCQ_AUDIT_FIX_FLOW:-0}" == "1" ]]; then
  ADVISORY_OVERRIDE="1"
fi
case "${BYPASS}" in
  fast|FAST|Fast) BYPASS="fast" ;;
  1|true|yes) BYPASS="1" ;;
  ""|0|false|no) BYPASS="0" ;;
  *) echo "rocq-audit: ROCQ_AUDIT_BYPASS must be unset, 1, or fast; got '${BYPASS}'" >&2; exit 2 ;;
esac

validate_int_range() {
  local name="$1" val="$2" lo="$3" hi="$4"
  [[ -z "${val}" ]] && return 0
  if ! [[ "${val}" =~ ^[0-9]+$ ]]; then
    echo "rocq-audit: ${name} must be an integer, got '${val}'" >&2
    exit 2
  fi
  if (( val < lo || val > hi )); then
    echo "rocq-audit: ${name}=${val} outside allowed range [${lo}, ${hi}]" >&2
    exit 2
  fi
  return 0
}

validate_int_range ROCQ_AUDIT_WORKERS          "${ROCQ_AUDIT_WORKERS:-}"        1     16
validate_int_range ROCQ_AUDIT_CHUNK_SIZE       "${ROCQ_AUDIT_CHUNK_SIZE:-}"     1     20
validate_int_range ROCQ_AUDIT_TOKEN_CAP        "${ROCQ_AUDIT_TOKEN_CAP:-}"      10000 1000000
validate_int_range ROCQ_AUDIT_WALL_SECONDS     "${ROCQ_AUDIT_WALL_SECONDS:-}"   60    3600
validate_int_range ROCQ_AUDIT_MAX_ATTEMPTS     "${ROCQ_AUDIT_MAX_ATTEMPTS:-}"   1     10

# Git trailers override env vars.
EDITMSG="$(git rev-parse --git-path COMMIT_EDITMSG 2>/dev/null)"
if [[ -n "${EDITMSG}" && -f "${EDITMSG}" ]]; then
  parse_trailer() {
    local key="$1"
    git interpret-trailers --parse --no-divider <"${EDITMSG}" 2>/dev/null | awk -F': *' -v k="${key}" 'tolower($1)==tolower(k){print $2; exit}'
  }
  T_WORKERS=$(parse_trailer "Rocq-Audit-Workers")
  T_CHUNK=$(parse_trailer "Rocq-Audit-Chunk-Size")
  T_TOKEN=$(parse_trailer "Rocq-Audit-Token-Cap")
  T_WALL=$(parse_trailer "Rocq-Audit-Wall-Seconds")
  T_SKIP2=$(parse_trailer "Rocq-Audit-Skip-Stage2")
  for forbidden in Rocq-Audit-Skip-Stage1 Rocq-Audit-Skip-Tier0 Rocq-Audit-Skip-Attempts-Counter; do
    if [[ -n "$(parse_trailer "${forbidden}")" ]]; then
      echo "rocq-audit: trailer ${forbidden} is forbidden and cannot appear in commit messages." >&2
      exit 2
    fi
  done
  [[ -n "${T_WORKERS}" ]] && { validate_int_range "trailer Rocq-Audit-Workers" "${T_WORKERS}" 1 16; ROCQ_AUDIT_WORKERS="${T_WORKERS}"; }
  [[ -n "${T_CHUNK}" ]]   && { validate_int_range "trailer Rocq-Audit-Chunk-Size" "${T_CHUNK}" 1 20; ROCQ_AUDIT_CHUNK_SIZE="${T_CHUNK}"; }
  [[ -n "${T_TOKEN}" ]]   && { validate_int_range "trailer Rocq-Audit-Token-Cap" "${T_TOKEN}" 10000 1000000; ROCQ_AUDIT_TOKEN_CAP="${T_TOKEN}"; }
  [[ -n "${T_WALL}" ]]    && { validate_int_range "trailer Rocq-Audit-Wall-Seconds" "${T_WALL}" 60 3600; ROCQ_AUDIT_WALL_SECONDS="${T_WALL}"; }
  if [[ -n "${T_SKIP2}" ]]; then
    case "${T_SKIP2,,}" in
      true|yes|1) BYPASS="fast" ;;
      false|no|0) : ;;
      *) echo "rocq-audit: trailer Rocq-Audit-Skip-Stage2 must be true/false; got '${T_SKIP2}'" >&2; exit 2 ;;
    esac
  fi
fi

OVERRIDE_NOTES=""
[[ -n "${ROCQ_AUDIT_WORKERS:-}" ]]      && OVERRIDE_NOTES+="workers=${ROCQ_AUDIT_WORKERS} "
[[ -n "${ROCQ_AUDIT_TOKEN_CAP:-}" ]]    && OVERRIDE_NOTES+="token_cap=${ROCQ_AUDIT_TOKEN_CAP} "
[[ -n "${ROCQ_AUDIT_WALL_SECONDS:-}" ]] && OVERRIDE_NOTES+="wall_seconds=${ROCQ_AUDIT_WALL_SECONDS} "
[[ -n "${ROCQ_AUDIT_CHUNK_SIZE:-}" ]]   && OVERRIDE_NOTES+="chunk_size=${ROCQ_AUDIT_CHUNK_SIZE} "
[[ -n "${ROCQ_AUDIT_MAX_ATTEMPTS:-}" ]] && OVERRIDE_NOTES+="max_attempts=${ROCQ_AUDIT_MAX_ATTEMPTS} "

export ROCQ_AUDIT_WORKERS ROCQ_AUDIT_CHUNK_SIZE ROCQ_AUDIT_TOKEN_CAP
export ROCQ_AUDIT_WALL_SECONDS ROCQ_AUDIT_MAX_ATTEMPTS
export ROCQ_AUDIT_ADVISORY ROCQ_AUDIT_FIX_FLOW

# When ROCQ_AUDIT_E2E=1, the audit runs against a synthetic fixture tree
# spun up by audit-e2e-test.sh. Central-state writes (findings-history,
# bypass.log, git notes) are suppressed so e2e scenarios do not pollute
# the real audit history.
E2E_MODE="${ROCQ_AUDIT_E2E:-0}"
if [[ "${E2E_MODE}" == "1" ]]; then
  echo "rocq-audit: e2e mode; central-state writes suppressed" >&2
fi

# ---- Staged diff no-op -----------------------------------------------------
STAGED=$(git diff --cached --name-only --diff-filter=ACMR -- '*.v' 2>/dev/null || true)
if [[ -z "${STAGED}" ]]; then
  exit 0
fi

# ---- Compute identifiers --------------------------------------------------
BASE_COMMIT="$(git rev-parse --verify HEAD 2>/dev/null || echo none)"
DIFF_HASH="$(git diff --cached | shasum -a 256 | cut -c1-16)"
CATALOG_HASH="$(find "${AUDIT_TEMPLATE}/rules" "${AUDIT_TEMPLATE}/schema" -type f \( -name '*.yaml' -o -name '*.json' -o -name '*.md' \) -print0 | sort -z | xargs -0 shasum -a 256 | shasum -a 256 | cut -c1-16)"
STATE_KEY="$(printf '%s|%s|%s' "${BASE_COMMIT}" "${DIFF_HASH}" "${CATALOG_HASH}" | shasum -a 256 | cut -c1-16)"

RAND4="$(openssl rand -hex 2 2>/dev/null || printf '%04x' $RANDOM)"
RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)-${DIFF_HASH:0:8}-${RAND4}"
RUN_DIR="${AUDIT_RUNS}/${RUN_ID}"

# ---- Materialise execroot from template ----------------------------------
mkdir -p "${RUN_DIR}"
cp -R "${AUDIT_TEMPLATE}/." "${RUN_DIR}/"
mkdir -p "${RUN_DIR}/reports" "${RUN_DIR}/fix-plans" "${RUN_DIR}/state"

# Synthesise fix-flow config into the run copy. Canonical template/config.yaml
# stays untouched.
if [[ "${ADVISORY_OVERRIDE}" == "1" ]]; then
  "${VENV_PY}" - <<PY
import yaml
p = "${RUN_DIR}/config.yaml"
c = yaml.safe_load(open(p)) or {}
c["on_agent_failure"] = "advisory"
if "${ROCQ_AUDIT_FIX_FLOW:-0}" == "1":
    c["on_agent_failure_reason"] = "fix-flow run ${RUN_ID}"
else:
    c["on_agent_failure_reason"] = "advisory override ${RUN_ID}"
open(p, "w").write(yaml.safe_dump(c))
PY
fi

# Invariant: central-state/last-run-id is the canonical pointer. runs/LATEST
# is a best-effort human-convenience symlink, updated first; last-run-id is
# written after, so any race-reader that gets last-run-id always sees a
# valid id even if the symlink write failed or lagged.
( cd "${AUDIT_RUNS}" && rm -f LATEST.new && ln -s "${RUN_ID}" "LATEST.new" && mv -f "LATEST.new" "LATEST" ) || {
  echo "rocq-audit: WARNING runs/LATEST symlink not updated; consumers should read central-state/last-run-id" >&2
}

# Write last-run-id as a text pointer for code that needs strict atomicity.
printf '%s\n' "${RUN_ID}" > "${AUDIT_CENTRAL}/last-run-id.new" && \
  mv -f "${AUDIT_CENTRAL}/last-run-id.new" "${AUDIT_CENTRAL}/last-run-id"

# ---- Export run-local paths -----------------------------------------------
AUDIT_DIR="${RUN_DIR}"
export AUDIT_DIR AUDIT_TEMPLATE AUDIT_CENTRAL REPO_ROOT

# Age-based reap of orphan central-state oscillation logs.
OSC_TTL_DAYS=$("${VENV_PY}" -c "import yaml; c=yaml.safe_load(open('${AUDIT_TEMPLATE}/config.yaml')); print(c.get('oscillation_log_ttl_days', 7))" 2>/dev/null || echo 7)
find "${AUDIT_CENTRAL}/oscillation" -maxdepth 1 -name '*.log' -type f -mtime "+${OSC_TTL_DAYS}" -delete 2>/dev/null || true

# ---- Attempt counter (central, keyed) -------------------------------------
ATTEMPT_FILE="${AUDIT_CENTRAL}/attempts/${STATE_KEY}"
if [[ -n "${ROCQ_AUDIT_MAX_ATTEMPTS:-}" ]]; then
  MAX_ATTEMPTS="${ROCQ_AUDIT_MAX_ATTEMPTS}"
else
  MAX_ATTEMPTS=$("${VENV_PY}" -c "import yaml; c=yaml.safe_load(open('${AUDIT_DIR}/config.yaml')); print(c.get('max_attempts_per_diff', 3))" 2>/dev/null || echo 3)
fi
ATTEMPT=0
FIRST_ATTEMPT=true
if [[ -f "${ATTEMPT_FILE}" ]]; then
  ATTEMPT=$(cat "${ATTEMPT_FILE}")
  FIRST_ATTEMPT=false
fi
ATTEMPT=$((ATTEMPT + 1))
echo "${ATTEMPT}" > "${ATTEMPT_FILE}"

OSC_LOG="${AUDIT_CENTRAL}/oscillation/${STATE_KEY}.log"
if [[ "${FIRST_ATTEMPT}" == "true" ]]; then
  : > "${OSC_LOG}" 2>/dev/null || true
fi

# Write initial meta.json
"${VENV_PY}" - <<PY
import json
meta = {
    "run_id": "${RUN_ID}",
    "started_at_utc": "$(date -u +%FT%TZ)",
    "ended_at_utc": None,
    "commit_sha_pre": "${BASE_COMMIT}",
    "commit_sha_post": None,
    "diff_hash": "${DIFF_HASH}",
    "catalog_hash": "${CATALOG_HASH}",
    "state_key": "${STATE_KEY}",
    "attempt": ${ATTEMPT},
    "max_attempts": ${MAX_ATTEMPTS},
    "fix_flow": "${ROCQ_AUDIT_FIX_FLOW:-0}" == "1",
    "advisory": "${ADVISORY_OVERRIDE}" == "1",
    "bypass": "${BYPASS}" if "${BYPASS}" != "0" else None,
    "overrides": "${OVERRIDE_NOTES}".strip() or None,
    "result": "in_progress",
}
open("${RUN_DIR}/meta.json", "w").write(json.dumps(meta, indent=2) + "\n")
PY

set_meta_result() {
  local result="$1"
  "${VENV_PY}" - <<PY
import json
p = "${RUN_DIR}/meta.json"
m = json.load(open(p))
m["ended_at_utc"] = "$(date -u +%FT%TZ)"
m["commit_sha_post"] = None  # filled by git post-commit hook if needed
m["result"] = "${result}"
open(p, "w").write(json.dumps(m, indent=2) + "\n")
PY
}

if [[ "${ATTEMPT}" -gt "${MAX_ATTEMPTS}" ]]; then
  echo "" >&2
  echo "COMMIT HALTED by rocq-audit: attempt ${ATTEMPT} on the same diff exceeds max_attempts_per_diff=${MAX_ATTEMPTS}." >&2
  echo "The fixer has been invoked repeatedly without converging. Review the diff manually or bypass with ROCQ_AUDIT_BYPASS=1." >&2
  echo "State key: ${STATE_KEY}" >&2
  set_meta_result "halted_attempts_exceeded"
  exit 2
fi

# ---- Pipeline paths ------------------------------------------------------
STAGE="${AUDIT_DIR}/reports/stage"
TIER0="${STAGE}-tier0.json"
STAGE1="${STAGE}-stage1.json"
STAGE2="${STAGE}-stage2.json"
TIERK="${STAGE}-tierk.json"
LATEST="${AUDIT_DIR}/reports/latest.md"
SENTINEL="${AUDIT_DIR}/reports/sentinel"

# Also keep a stable-path convenience symlink for external consumers.
mkdir -p "${AUDIT_RUNS}/LATEST/reports" 2>/dev/null || true

# ---- Tier 0 --------------------------------------------------------------
"${VENV_PY}" "${AUDIT_ROOT}/bin/tier0-extract.py" > "${TIER0}"

STAGE1_ENABLED=$("${VENV_PY}" -c "import yaml; c=yaml.safe_load(open('${AUDIT_DIR}/config.yaml')); print('1' if c.get('stage1_enabled', True) else '0')")
STAGE2_ENABLED=$("${VENV_PY}" -c "import yaml; c=yaml.safe_load(open('${AUDIT_DIR}/config.yaml')); print('1' if c.get('stage2_enabled', False) else '0')")
# Env-var override: for deterministic e2e runs and debugging, disable Stage 2
# without the bypass semantics (fast-bypass forces exit 0, which is wrong for
# testing Stage-1 gating).
if [[ "${ROCQ_AUDIT_STAGE2_DISABLED:-0}" == "1" ]]; then
  STAGE2_ENABLED=0
fi

# ---- Stage 1 -------------------------------------------------------------
if [[ "${STAGE1_ENABLED}" == "1" ]]; then
  "${VENV_PY}" "${AUDIT_ROOT}/bin/stage1-regex.py" "${TIER0}" > "${STAGE1}"
else
  echo '{"findings": [], "disabled": true}' > "${STAGE1}"
fi

# ---- Stage 2 and Tier K --------------------------------------------------
if [[ "${BYPASS}" == "fast" ]]; then
  echo '{"findings": [], "fast_bypassed": true, "budget": {"stop_reason": "fast_bypass"}}' > "${STAGE2}"
  echo '{"verdicts": [], "fast_bypassed": true}' > "${TIERK}"
elif [[ "${STAGE2_ENABLED}" == "1" ]]; then
  if [[ -x "${AUDIT_ROOT}/bin/stage2-agent.sh" ]]; then
    "${AUDIT_ROOT}/bin/stage2-agent.sh" "${TIER0}" "${STAGE1}" > "${STAGE2}" || true
  else
    echo '{"findings": [], "error": "stage2-agent.sh not yet installed"}' > "${STAGE2}"
  fi
else
  echo '{"findings": [], "disabled": true}' > "${STAGE2}"
fi

if [[ "${BYPASS}" == "fast" ]]; then
  :
elif [[ "${STAGE2_ENABLED}" == "1" && -x "${AUDIT_ROOT}/bin/tier-k-verify.sh" ]]; then
  "${AUDIT_ROOT}/bin/tier-k-verify.sh" "${STAGE2}" "${TIER0}" > "${TIERK}" 2>/dev/null || echo '{"verdicts": [], "error": "tier-k failed"}' > "${TIERK}"
else
  echo '{"verdicts": [], "disabled": true}' > "${TIERK}"
fi

# ---- Merge and render ----------------------------------------------------
set +e
"${VENV_PY}" "${AUDIT_ROOT}/bin/report-merge.py" "${TIER0}" "${STAGE1}" "${STAGE2}" "${TIERK}" "${LATEST}"
MERGE_RC=$?
set -e

echo "${LATEST}" > "${SENTINEL}"

# ---- Append trails to central state --------------------------------------
if [[ "${E2E_MODE}" != "1" ]]; then
  if [[ -n "${OVERRIDE_NOTES:-}" && "${BYPASS}" == "0" ]]; then
    echo "override $(date -u +%FT%TZ) run=${RUN_ID} commit=${BASE_COMMIT} diff=${DIFF_HASH} ${OVERRIDE_NOTES}" \
      >> "${AUDIT_CENTRAL}/bypass.log" 2>/dev/null || true
  fi
  if [[ "${ADVISORY_OVERRIDE}" == "1" ]]; then
    echo "advisory $(date -u +%FT%TZ) run=${RUN_ID} commit=${BASE_COMMIT} diff=${DIFF_HASH} fix_flow=${ROCQ_AUDIT_FIX_FLOW:-0}" \
      >> "${AUDIT_CENTRAL}/bypass.log" 2>/dev/null || true
  fi

  # Append findings to the central history log, tagged with run_id.
  export TS="$(date -u +%FT%TZ)"
  export _RUN_ID="${RUN_ID}"
  export _STAGE1="${STAGE1}"
  export _STAGE2="${STAGE2}"
  "${VENV_PY}" - <<PY 2>/dev/null || true
import json, os
ts = os.environ["TS"]
rid = os.environ["_RUN_ID"]
hpath = os.path.join(os.environ["AUDIT_CENTRAL"], "findings-history.ndjson")
out = []
for p in [os.environ.get("_STAGE1"), os.environ.get("_STAGE2")]:
    try:
        with open(p) as f: d = json.load(f)
    except Exception:
        continue
    for rec in d.get("findings", []):
        rec = dict(rec)
        rec["ts"] = ts
        rec["run_id"] = rid
        out.append(rec)
if out:
    with open(hpath, "a") as f:
        for rec in out:
            f.write(json.dumps(rec) + "\n")
PY
fi

# ---- Oscillation detection -----------------------------------------------
REPORT_FP=$(shasum -a 256 "${LATEST}" 2>/dev/null | cut -c1-16)
if [[ -n "${REPORT_FP}" ]]; then
  if [[ -f "${OSC_LOG}" ]] && grep -qF "${REPORT_FP}" "${OSC_LOG}" 2>/dev/null; then
    echo "" >&2
    echo "rocq-audit: OSCILLATION DETECTED. Report fingerprint ${REPORT_FP} has already been seen for this diff." >&2
    echo "The fixer appears to be flipping between two states. Halting." >&2
    set_meta_result "oscillation_halt"
    exit 2
  fi
  echo "${REPORT_FP}" >> "${OSC_LOG}"
  tail -n 5 "${OSC_LOG}" > "${OSC_LOG}.tmp" && mv "${OSC_LOG}.tmp" "${OSC_LOG}"
fi

# ---- Bypass handling -----------------------------------------------------
if [[ "${BYPASS}" == "fast" ]] || [[ "${MERGE_RC}" != "0" && "${BYPASS}" == "1" ]]; then
  COMMIT_SHA="$(git rev-parse --verify HEAD 2>/dev/null || echo '(none)')"
  if [[ "${E2E_MODE}" != "1" ]]; then
    {
      echo "bypass $(date -u +%FT%TZ) run=${RUN_ID} mode=${BYPASS} commit=${COMMIT_SHA} diff=${DIFF_HASH} overrides=${OVERRIDE_NOTES:-none}"
      # Iterate BOTH Stage 1 and Stage 2 findings so an S996 cap-hit
      # sentinel is preserved in the bypass audit trail, not just Stage 1.
      for p in "${STAGE1}" "${STAGE2}"; do
        "${VENV_PY}" -c "import json,sys; r=json.load(open(sys.argv[1])); [print('  rule=', f['rule_id'], 'file=', f['file'], 'line=', f['line_start']) for f in r.get('findings',[])]" "${p}" 2>/dev/null || true
      done
    } >> "${AUDIT_CENTRAL}/bypass.log" 2>/dev/null
    if git notes --ref=audit-bypass list "${COMMIT_SHA}" >/dev/null 2>&1; then
      git notes --ref=audit-bypass append -m "$(cat ${LATEST})" "${COMMIT_SHA}" || true
    else
      git notes --ref=audit-bypass add -f -m "$(cat ${LATEST})" "${COMMIT_SHA}" || true
    fi
  fi
  if [[ "${BYPASS}" == "fast" ]]; then
    echo "rocq-audit: FAST BYPASS (Stage 2 skipped). Report at ${LATEST}." >&2
    set_meta_result "fast_bypassed"
  else
    echo "rocq-audit: BYPASSED via ROCQ_AUDIT_BYPASS=1. Report at ${LATEST}." >&2
    set_meta_result "bypassed"
  fi
  rm -f "${ATTEMPT_FILE}" "${OSC_LOG:-}" 2>/dev/null || true
  exit 0
fi

if [[ "${MERGE_RC}" != "0" ]]; then
  echo "" >&2
  echo "COMMIT BLOCKED by rocq-audit." >&2
  echo "Report: ${LATEST}" >&2
  echo "Attempt: ${ATTEMPT} of ${MAX_ATTEMPTS}" >&2
  echo "Next: run /rocq-fix-plan, review the plan, approve, then run /rocq-apply-fixes and retry." >&2
  echo "Bypass: ROCQ_AUDIT_BYPASS=1 git commit -m '...'   (logged to refs/notes/audit-bypass)" >&2
  set_meta_result "failed"
  exit 2
fi

# Clean up per-state-key trackers when the diff passes.
rm -f "${ATTEMPT_FILE}" "${OSC_LOG}" 2>/dev/null || true
set_meta_result "passed"
exit 0
