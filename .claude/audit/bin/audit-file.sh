#!/usr/bin/env bash
# audit-file.sh — single-file / single-entity rocq-audit CLI.
#
# Unlike audit.sh (which reads `git diff --cached`), this script builds a
# Tier 0 manifest directly from a file on disk, then pipes it through the
# existing Stage 1, Stage 2, Tier K, and merge stages. Useful for ad-hoc
# rule checks outside the commit flow.
#
# Usage:
#   audit-file.sh --file <path>
#                 [--entity PAT1,PAT2,...]
#                 [--lines START-END]
#                 [--rule ID1,ID2,...]
#                 [--stage1-only]
#                 [--no-tier-k]
#                 [--advisory]
#                 [--json]
#                 [--output PATH]
#                 [--keep-workdir]
#
# Exit codes:
#   0  no error-severity findings
#   1  usage error (missing --file, mutual exclusion, malformed --lines,
#      file outside repo, .claude/audit missing, ...)
#   2  at least one error-severity finding
#   3  selector (--entity / --lines) matched zero entities
#
# Notes:
# - `--entity` and `--lines` are mutually exclusive.
# - `--entity` patterns are shell globs via Python fnmatch. Quote them to
#   prevent shell expansion: --entity 'pose_*'
# - Stage 2 defaults ON, same gate semantics audit.sh uses. --stage1-only
#   skips Stage 2 entirely. --stage2-only is deliberately NOT offered;
#   Stage 2 rules read Stage 1 findings as context, and stubbing that
#   context would weaken Stage 2 silently.
# - `ROCQ_AUDIT_FIX_FLOW` and `ROCQ_AUDIT_ADVISORY` are unset unless
#   --advisory is passed; file audits should not silently downgrade to
#   advisory just because the calling shell was a fix-flow subagent.
# - No run id, no meta.json, no findings-history append, no bypass log.
#   Only central-state write is stage2-agent.py's token-usage.json
#   increment.

set -euo pipefail

# ---- Locate the audit engine --------------------------------------------
if ! REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"; then
  echo "audit-file.sh: not inside a git worktree." >&2
  exit 1
fi
AUDIT_ROOT="${REPO_ROOT}/.claude/audit"
if [[ ! -d "${AUDIT_ROOT}" ]]; then
  echo "audit-file.sh: rocq-audit not installed in this repo (.claude/audit missing)." >&2
  exit 1
fi
AUDIT_TEMPLATE="${AUDIT_ROOT}/template"
AUDIT_CENTRAL="${AUDIT_ROOT}/central-state"
VENV_PY="${AUDIT_ROOT}/venv/bin/python3"
if [[ ! -x "${VENV_PY}" ]]; then
  echo "audit-file.sh: venv missing at ${AUDIT_ROOT}/venv." >&2
  exit 1
fi

# ---- Parse flags ---------------------------------------------------------
FILE=""
ENTITY=""
LINES=""
RULE=""
STAGE1_ONLY=0
NO_TIER_K=0
ADVISORY=0
JSON_OUT=0
OUTPUT=""
KEEP_WORKDIR=0

usage_err() {
  echo "audit-file.sh: $1" >&2
  echo "Usage: audit-file.sh --file <path> [--entity PAT,...|--lines N-M] [--rule ID,...] [--stage1-only] [--no-tier-k] [--advisory] [--json] [--output PATH] [--keep-workdir]" >&2
  exit 1
}

while (( $# > 0 )); do
  case "$1" in
    --file)          FILE="${2:-}"; shift 2 ;;
    --file=*)        FILE="${1#--file=}"; shift ;;
    --entity)        ENTITY="${2:-}"; shift 2 ;;
    --entity=*)      ENTITY="${1#--entity=}"; shift ;;
    --lines)         LINES="${2:-}"; shift 2 ;;
    --lines=*)       LINES="${1#--lines=}"; shift ;;
    --rule)          RULE="${2:-}"; shift 2 ;;
    --rule=*)        RULE="${1#--rule=}"; shift ;;
    --stage1-only)   STAGE1_ONLY=1; shift ;;
    --no-tier-k)     NO_TIER_K=1; shift ;;
    --advisory)      ADVISORY=1; shift ;;
    --json)          JSON_OUT=1; shift ;;
    --output)        OUTPUT="${2:-}"; shift 2 ;;
    --output=*)      OUTPUT="${1#--output=}"; shift ;;
    --keep-workdir)  KEEP_WORKDIR=1; shift ;;
    -h|--help)
      grep -E '^# ( +|[A-Z])' "$0" | sed 's/^# //' >&2
      exit 0
      ;;
    *) usage_err "unknown flag: $1" ;;
  esac
done

[[ -z "${FILE}" ]] && usage_err "--file is required"
if [[ -n "${ENTITY}" && -n "${LINES}" ]]; then
  usage_err "--entity and --lines are mutually exclusive"
fi

# Validate --lines format: two positive integers, first <= second.
LINE_LO=""
LINE_HI=""
if [[ -n "${LINES}" ]]; then
  if ! [[ "${LINES}" =~ ^([0-9]+)-([0-9]+)$ ]]; then
    usage_err "--lines must be START-END (two integers); got '${LINES}'"
  fi
  LINE_LO="${BASH_REMATCH[1]}"
  LINE_HI="${BASH_REMATCH[2]}"
  if (( LINE_LO < 1 )) || (( LINE_HI < LINE_LO )); then
    usage_err "--lines range invalid: ${LINES}"
  fi
fi

# Resolve file to absolute path and verify membership in REPO_ROOT.
FILE_ABS="$("${VENV_PY}" -c "
import sys, pathlib
try:
    p = pathlib.Path(sys.argv[1]).resolve(strict=True)
    print(str(p))
except (FileNotFoundError, OSError) as e:
    print('err:' + str(e), file=sys.stderr)
    sys.exit(2)
" "${FILE}" 2>&1)" || { echo "audit-file.sh: file not found: ${FILE}" >&2; exit 1; }

REPO_ABS="$("${VENV_PY}" -c "import sys, pathlib; print(str(pathlib.Path(sys.argv[1]).resolve()))" "${REPO_ROOT}")"
case "${FILE_ABS}" in
  "${REPO_ABS}"/*) : ;;
  *) usage_err "file must be inside the repository: ${FILE_ABS}" ;;
esac
if [[ ! -r "${FILE_ABS}" ]]; then
  usage_err "file not readable: ${FILE_ABS}"
fi

# ---- Workdir + cleanup ---------------------------------------------------
WORKDIR="$(mktemp -d -t rocq-audit-file.XXXXXX)"
cleanup() {
  local rc=$?
  if (( KEEP_WORKDIR == 1 )); then
    echo "audit-file.sh: workdir preserved at ${WORKDIR}" >&2
  else
    rm -rf "${WORKDIR}"
  fi
  exit "${rc}"
}
trap cleanup EXIT INT TERM

# ---- Env setup -----------------------------------------------------------
export REPO_ROOT
export AUDIT_DIR="${AUDIT_ROOT}"
export AUDIT_TEMPLATE
export AUDIT_CENTRAL

if (( ADVISORY == 0 )); then
  unset ROCQ_AUDIT_FIX_FLOW ROCQ_AUDIT_ADVISORY
fi

# ---- Build Tier 0 from the file -----------------------------------------
ENTITY_NAMES_JSON="null"
if [[ -n "${ENTITY}" ]]; then
  # Translate CSV into a JSON list for the Python shim.
  ENTITY_NAMES_JSON="$("${VENV_PY}" -c "
import json, sys
items = [s for s in sys.argv[1].split(',') if s]
print(json.dumps(items))
" "${ENTITY}")"
fi
LINE_RANGE_JSON="null"
if [[ -n "${LINES}" ]]; then
  LINE_RANGE_JSON="[${LINE_LO}, ${LINE_HI}]"
fi

"${VENV_PY}" - "${AUDIT_ROOT}" "${FILE_ABS}" "${REPO_ABS}" "${ENTITY_NAMES_JSON}" "${LINE_RANGE_JSON}" <<'PY' > "${WORKDIR}/tier0.json"
import json, sys
audit_root, file_abs, repo_abs, entity_json, line_json = sys.argv[1:6]
sys.path.insert(0, f"{audit_root}/bin")
from file_manifest import build_manifest
entity_names = json.loads(entity_json)
line_range_raw = json.loads(line_json)
line_range = tuple(line_range_raw) if line_range_raw is not None else None
manifest = build_manifest(
    file_path=file_abs,
    repo_root=repo_abs,
    entity_names=entity_names,
    line_range=line_range,
    fallback_name=None,
)
json.dump(manifest, sys.stdout, indent=2, ensure_ascii=False)
PY

# If a selector was active but matched nothing, exit 3.
SELECTOR_ACTIVE=0
[[ -n "${ENTITY}" || -n "${LINES}" ]] && SELECTOR_ACTIVE=1
ENTITY_COUNT="$("${VENV_PY}" -c "
import json, sys
d = json.load(open(sys.argv[1]))
print(len(d.get('entities', [])))
" "${WORKDIR}/tier0.json")"
if (( SELECTOR_ACTIVE == 1 )) && [[ "${ENTITY_COUNT}" == "0" ]]; then
  if [[ -n "${ENTITY}" ]]; then
    echo "audit-file.sh: --entity filter matched no entities in ${FILE_ABS}" >&2
  else
    echo "audit-file.sh: --lines filter matched no entities in ${FILE_ABS}" >&2
  fi
  exit 3
fi

# ---- Stage 1 -------------------------------------------------------------
"${VENV_PY}" "${AUDIT_ROOT}/bin/stage1-regex.py" "${WORKDIR}/tier0.json" \
  > "${WORKDIR}/stage1.json"

# ---- Stage 2 -------------------------------------------------------------
if (( STAGE1_ONLY == 1 )); then
  echo '{"findings": [], "disabled": true}' > "${WORKDIR}/stage2.json"
else
  # stage2-agent.sh delegates to stage2-agent.py and exits 0 on cap-hit
  # in advisory mode, 2 in block mode. Use `|| true` to keep going; the
  # gate is report-merge.py's exit code.
  "${AUDIT_ROOT}/bin/stage2-agent.sh" \
    "${WORKDIR}/tier0.json" "${WORKDIR}/stage1.json" \
    > "${WORKDIR}/stage2.json" || true
fi

# ---- Tier K --------------------------------------------------------------
TIER_K_UNAVAILABLE=0
if (( STAGE1_ONLY == 1 )) || (( NO_TIER_K == 1 )); then
  echo '{"verdicts": [], "disabled": true}' > "${WORKDIR}/tierk.json"
else
  if [[ -x "${AUDIT_ROOT}/bin/tier-k-verify.sh" ]]; then
    if ! "${AUDIT_ROOT}/bin/tier-k-verify.sh" \
         "${WORKDIR}/stage2.json" "${WORKDIR}/tier0.json" \
         > "${WORKDIR}/tierk.json" 2>/dev/null; then
      echo '{"verdicts": [], "tier_k_unavailable": true}' > "${WORKDIR}/tierk.json"
      TIER_K_UNAVAILABLE=1
    fi
  else
    echo '{"verdicts": [], "tier_k_unavailable": true}' > "${WORKDIR}/tierk.json"
    TIER_K_UNAVAILABLE=1
  fi
fi

# ---- --rule post-filter --------------------------------------------------
# Filter BOTH stage1 and stage2 findings to only the requested rule IDs.
# Done before merge so the report is accurate without further plumbing.
if [[ -n "${RULE}" ]]; then
  for p in "${WORKDIR}/stage1.json" "${WORKDIR}/stage2.json"; do
    "${VENV_PY}" - "${p}" "${RULE}" <<'PY'
import json, sys, fnmatch
path, csv = sys.argv[1], sys.argv[2]
patterns = [s for s in csv.split(',') if s]
d = json.load(open(path))
kept = [f for f in d.get("findings", [])
        if any(fnmatch.fnmatchcase(f.get("rule_id",""), pat) for pat in patterns)]
d["findings"] = kept
json.dump(d, open(path, "w"), indent=2, ensure_ascii=False)
PY
  done
fi

# ---- Merge + render ------------------------------------------------------
JSON_FLAG=()
if (( JSON_OUT == 1 )); then
  JSON_FLAG=(--json "${WORKDIR}/merge.json")
fi
set +e
"${VENV_PY}" "${AUDIT_ROOT}/bin/report-merge.py" \
  "${WORKDIR}/tier0.json" "${WORKDIR}/stage1.json" \
  "${WORKDIR}/stage2.json" "${WORKDIR}/tierk.json" \
  "${WORKDIR}/report.md" \
  ${JSON_FLAG[@]+"${JSON_FLAG[@]}"}
MERGE_RC=$?
set -e

# ---- Emit ---------------------------------------------------------------
if (( JSON_OUT == 1 )); then
  if [[ -n "${OUTPUT}" ]]; then
    cp "${WORKDIR}/merge.json" "${OUTPUT}"
  else
    cat "${WORKDIR}/merge.json"
  fi
else
  if [[ -n "${OUTPUT}" ]]; then
    cp "${WORKDIR}/report.md" "${OUTPUT}"
  else
    cat "${WORKDIR}/report.md"
  fi
fi

exit "${MERGE_RC}"
