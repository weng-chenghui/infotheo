#!/usr/bin/env bash
# audit_batch.sh — batch driver around .claude/audit/bin/audit-file.sh for pgg-smc/.
#
# Reads pgg-smc/audit-inventory/scope.txt, iterates in-scope files in a
# priority order (staged → lib → protocol → groups → security →
# reconstruct → instances/{abelian,denboer1989,kim2025,s5,s5x5}), chunks
# files above --chunk-threshold by decl-index, and writes per-file
# JSON + MD reports plus a resume-friendly manifest.tsv.
#
# Design notes:
# - No audit-engine source is modified. The driver uses engine-supplied
#   env knobs (ROCQ_AUDIT_TOKEN_CAP, ROCQ_AUDIT_WORKERS) and flags
#   (--stage1-only, --no-tier-k, --lines, --json, --output).
# - Resume: on subsequent runs, files whose last manifest row shows
#   exit_code == 0 are skipped by default. exit_code == 2 (error
#   findings present) is re-audited so post-/rocq-apply-fixes state is
#   not stale. --retry-failed forces re-audit of exit 0 rows too.
# - S996 (Stage 2 token cap sentinel): halts the run, exit 0. The file
#   that hit the sentinel is NOT marked complete.
# - Soft cap: after each call the driver reads token-usage.json; if
#   today's usage exceeds --soft-cap, pause and exit 0.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
SCOPE_FILE="${REPO_ROOT}/pgg-smc/audit-inventory/scope.txt"
AUDIT_SH="${REPO_ROOT}/.claude/audit/bin/audit-file.sh"
TOKEN_USAGE="${REPO_ROOT}/.claude/audit/central-state/token-usage.json"
PY="${REPO_ROOT}/.claude/audit/venv/bin/python3"

# ---- Defaults ------------------------------------------------------------
DATE="$(date -u +%F)"
ONLY=""
SKIP=""
CHUNK_THRESHOLD=40
CHUNK_SIZE=25
STAGE1_ONLY=0
DRY_RUN=0
RESUME=1
RETRY_FAILED=0
SOFT_CAP=8000000
TOKEN_CAP=10000000
FORCE=0

usage() {
  cat <<EOF
Usage: audit_batch.sh [options]

  --date YYYY-MM-DD         Override run-directory date stamp (default: today UTC).
  --only GLOB               Only audit files whose scope-relative path matches GLOB.
  --skip GLOB               Skip files whose scope-relative path matches GLOB.
  --chunk-threshold N       Decl count above which a file is chunked (default 40).
  --chunk-size M            Decls per chunk (default 25).
  --stage1-only             Skip Stage 2 (pass-through to audit-file.sh).
  --dry-run                 Print the planned audit-file.sh invocations; do not execute.
  --resume                  Skip files already marked exit 0 in manifest.tsv (default on).
  --no-resume               Disable resume; re-audit every file.
  --retry-failed            Also re-audit files previously marked exit 0.
  --soft-cap N              Halt if daily token usage exceeds N after a call (default 8000000).
  --token-cap N             Export ROCQ_AUDIT_TOKEN_CAP=N (default 10000000).
  --force                   Bypass the rocqworker/pet concurrency guard.
  -h, --help                Show this.
EOF
}

while (( $# > 0 )); do
  case "$1" in
    --date)             DATE="$2"; shift 2 ;;
    --only)             ONLY="$2"; shift 2 ;;
    --skip)             SKIP="$2"; shift 2 ;;
    --chunk-threshold)  CHUNK_THRESHOLD="$2"; shift 2 ;;
    --chunk-size)       CHUNK_SIZE="$2"; shift 2 ;;
    --stage1-only)      STAGE1_ONLY=1; shift ;;
    --dry-run)          DRY_RUN=1; shift ;;
    --resume)           RESUME=1; shift ;;
    --no-resume)        RESUME=0; shift ;;
    --retry-failed)     RETRY_FAILED=1; shift ;;
    --soft-cap)         SOFT_CAP="$2"; shift 2 ;;
    --token-cap)        TOKEN_CAP="$2"; shift 2 ;;
    --force)            FORCE=1; shift ;;
    -h|--help)          usage; exit 0 ;;
    *) echo "audit_batch.sh: unknown flag: $1" >&2; usage >&2; exit 1 ;;
  esac
done

USAGE_KEY="$(date -u +%F)"
RUN_DIR="${REPO_ROOT}/.claude/audit/file-audits/${DATE}"
MANIFEST="${RUN_DIR}/manifest.tsv"
mkdir -p "${RUN_DIR}"
if [[ ! -f "${MANIFEST}" ]]; then
  printf "timestamp\tfile\tchunk\tlines\texit_code\terrors\twarnings\tduration_s\tnote\n" > "${MANIFEST}"
fi

# ---- Safety: no concurrent rocqworker / pet processes --------------------
# pgrep -x matches the exact process name, avoiding false positives on
# processes that merely contain "pet" in their command line (spotlight,
# petanque-setup-agent, etc.).
if (( FORCE == 0 )); then
  if pgrep -x rocqworker >/dev/null 2>&1; then
    echo "audit_batch.sh: rocqworker process is running; refusing to start (see CLAUDE.md compile safety). Re-run with --force to override." >&2
    exit 1
  fi
  if pgrep -x pet >/dev/null 2>&1; then
    echo "audit_batch.sh: pet process is running (likely rocq-mcp holding a worker); close it first, or re-run with --force to override." >&2
    exit 1
  fi
else
  echo "audit_batch.sh: --force set; skipping rocqworker/pet concurrency guard." >&2
fi

# ---- Engine env knobs ----------------------------------------------------
export ROCQ_AUDIT_WORKERS="${ROCQ_AUDIT_WORKERS:-4}"
export ROCQ_AUDIT_WALL_SECONDS="${ROCQ_AUDIT_WALL_SECONDS:-1800}"
export ROCQ_AUDIT_TOKEN_CAP="${TOKEN_CAP}"

# ---- Helpers -------------------------------------------------------------
py_read_scope() {
  "${PY}" - "${SCOPE_FILE}" <<'PY'
import sys
path = sys.argv[1]
for raw in open(path):
    s = raw.rstrip("\n")
    if not s.strip() or s.strip().startswith("#"):
        continue
    fragile = "fragile:no-tier-k" in s
    name = s.split("#", 1)[0].strip()
    if name:
        print(f"{name}\t{1 if fragile else 0}")
PY
}

py_decl_count() {
  # $1 = absolute path to .v file
  grep -cE "^(Theorem|Lemma|Fact|Corollary|Proposition)[[:space:]]" "$1" || true
}

py_chunk_ranges() {
  # $1 = relative path (pgg-smc/...), $2 = CHUNK_SIZE
  "${PY}" - "${REPO_ROOT}" "$1" "$2" <<'PY'
import sys, pathlib
repo, rel, chunk_size = sys.argv[1], sys.argv[2], int(sys.argv[3])
sys.path.insert(0, f"{repo}/.claude/audit/bin")
from file_manifest import build_manifest
src = pathlib.Path(f"{repo}/pgg-smc/{rel}").read_text().splitlines()
eof = len(src)
m = build_manifest(file_path=f"{repo}/pgg-smc/{rel}", repo_root=repo,
                   entity_names=None, line_range=None, fallback_name=None)
KINDS = {"Theorem","Lemma","Fact","Corollary","Proposition"}
# Filter out phantom entities where line_start is inside (* ... *).
def in_comment(lines):
    src_full = "\n".join(lines)
    inside=set(); depth=0; line=1; i=0
    while i<len(src_full):
        two=src_full[i:i+2]
        if two=="(*":
            depth+=1
            if depth==1: inside.add(line)
            i+=2; continue
        if two=="*)" and depth>0:
            if depth==1: inside.add(line)
            depth-=1; i+=2; continue
        if depth>0: inside.add(line)
        if src_full[i]=="\n": line+=1
        i+=1
    return inside
bad = in_comment(src)
decls = sorted(
    [e["line_start"] for e in m["entities"]
     if e["kind"] in KINDS and e["line_start"] not in bad
     and (e["line_start"]-1 < len(src))
     and src[e["line_start"]-1].lstrip().startswith(e["kind"]+" ")]
)
if not decls:
    sys.exit(0)
n = len(decls)
for i in range(0, n, chunk_size):
    lo = decls[i]
    j = i + chunk_size
    hi = decls[j] - 1 if j < n else eof
    print(f"{lo}\t{hi}")
PY
}

py_read_json_findings() {
  # $1 = path to audit JSON; prints "errors\twarnings\ts996"
  "${PY}" - "$1" <<'PY'
import json, sys
try:
    d = json.load(open(sys.argv[1]))
except Exception:
    print("0\t0\t0"); sys.exit(0)
errs = warns = s996 = 0
for f in d.get("findings", []):
    sev = (f.get("severity") or "").lower()
    if sev == "error": errs += 1
    elif sev in {"warning","warn"}: warns += 1
    if f.get("rule_id") == "S996": s996 = 1
print(f"{errs}\t{warns}\t{s996}")
PY
}

py_daily_usage() {
  "${PY}" - "${TOKEN_USAGE}" "${USAGE_KEY}" <<'PY'
import json, sys
try:
    d = json.load(open(sys.argv[1]))
except Exception:
    print(0); sys.exit(0)
print(d.get("daily", {}).get(sys.argv[2], 0))
PY
}

# Emit ordered path\tfragile rows.
order_files() {
  local staged
  staged=$(git -C "${REPO_ROOT}" diff --cached --name-only -- '*.v' 2>/dev/null | sed 's|^pgg-smc/||' || true)
  py_read_scope | while IFS=$'\t' read -r path fragile; do
    # Apply --only / --skip globs; match against scope-relative path.
    if [[ -n "${ONLY}" ]]; then
      case "${path}" in ${ONLY}) : ;; *) continue ;; esac
    fi
    if [[ -n "${SKIP}" ]]; then
      case "${path}" in ${SKIP}) continue ;; esac
    fi
    local count dirprio
    count=$(py_decl_count "${REPO_ROOT}/pgg-smc/${path}")
    case "${path}" in
      lib/*)                   dirprio=2 ;;
      protocol/*)              dirprio=3 ;;
      groups/*)                dirprio=4 ;;
      security/*)              dirprio=5 ;;
      reconstruct/*)           dirprio=6 ;;
      instances/abelian/*)     dirprio=7 ;;
      instances/denboer1989/*) dirprio=8 ;;
      instances/kim2025/*)     dirprio=9 ;;
      instances/s5/*)          dirprio=10 ;;
      instances/s5x5/*)        dirprio=11 ;;
      *)                       dirprio=99 ;;
    esac
    if echo "${staged}" | grep -Fxq "${path}"; then
      dirprio=1
    fi
    printf "%d\t%04d\t%s\t%d\n" "${dirprio}" "${count}" "${path}" "${fragile}"
  done | sort -t$'\t' -k1,1n -k2,2n -k3,3 | cut -f3,4
}

# Resume check: last exit code for this file/chunk in manifest.
last_exit_for() {
  local key="$1"
  awk -F'\t' -v k="${key}" 'BEGIN{last=""} $2==k {last=$5} END{print last}' "${MANIFEST}"
}

should_skip() {
  local file="$1"
  (( RESUME == 0 )) && return 1
  local last
  last=$(last_exit_for "${file}")
  [[ -z "${last}" ]] && return 1
  if [[ "${last}" == "0" ]] && (( RETRY_FAILED == 0 )); then
    return 0
  fi
  return 1
}

# Invoke audit-file.sh once and record the result.
run_one() {
  local path="$1" fragile="$2" chunk="$3" lines="$4"
  local out_json out_md note=""
  local rel_out
  if [[ -n "${chunk}" ]]; then
    rel_out="${path%.v}.chunk-${chunk}"
  else
    rel_out="${path%.v}"
  fi
  out_json="${RUN_DIR}/${rel_out}.json"
  out_md="${RUN_DIR}/${rel_out}.md"
  mkdir -p "$(dirname "${out_json}")"

  local -a flags
  flags=( --file "pgg-smc/${path}" --json --output "${out_json}" )
  if [[ -n "${lines}" ]]; then
    flags+=( --lines "${lines}" )
  fi
  if (( STAGE1_ONLY == 1 )); then
    flags+=( --stage1-only )
  fi
  if [[ "${fragile}" == "1" ]]; then
    flags+=( --no-tier-k )
    note="fragile-no-tier-k"
  fi

  local ts start_ns end_ns dur_s rc=0
  ts="$(date -u +%FT%TZ)"
  if (( DRY_RUN == 1 )); then
    echo "DRY ${AUDIT_SH} ${flags[*]}"
    printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
      "${ts}" "${path}" "${chunk}" "${lines}" "DRY" "0" "0" "0" "${note}" >> "${MANIFEST}"
    return 0
  fi

  start_ns="$(date +%s)"
  set +e
  "${AUDIT_SH}" "${flags[@]}" >"${out_md}" 2>&1
  rc=$?
  set -e
  end_ns="$(date +%s)"
  dur_s=$(( end_ns - start_ns ))

  local errs=0 warns=0 s996=0
  if [[ -s "${out_json}" ]]; then
    IFS=$'\t' read -r errs warns s996 < <(py_read_json_findings "${out_json}")
  fi
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
    "${ts}" "${path}" "${chunk}" "${lines}" "${rc}" "${errs}" "${warns}" "${dur_s}" "${note}" >> "${MANIFEST}"

  if [[ "${s996}" == "1" ]]; then
    echo "audit_batch.sh: Stage 2 token cap hit (S996) while auditing ${path}${chunk:+ chunk ${chunk}}. Halting. Re-run with --resume once the cap resets." >&2
    exit 0
  fi

  # Soft cap check: if today's usage exceeds SOFT_CAP, pause.
  local used
  used=$(py_daily_usage)
  if (( used > SOFT_CAP )); then
    echo "audit_batch.sh: daily soft cap reached (${used} > ${SOFT_CAP}). Halting. Re-run with --resume tomorrow or raise --soft-cap." >&2
    exit 0
  fi
}

# ---- Main loop -----------------------------------------------------------
total=0
skipped=0
order_files | while IFS=$'\t' read -r path fragile; do
  total=$(( total + 1 ))
  if should_skip "${path}"; then
    skipped=$(( skipped + 1 ))
    printf "resumed: skipping %s\n" "${path}"
    continue
  fi
  count=$(py_decl_count "${REPO_ROOT}/pgg-smc/${path}")
  if (( count <= CHUNK_THRESHOLD )); then
    run_one "${path}" "${fragile}" "" ""
  else
    chunk_idx=0
    while IFS=$'\t' read -r lo hi; do
      run_one "${path}" "${fragile}" "${chunk_idx}" "${lo}-${hi}"
      chunk_idx=$(( chunk_idx + 1 ))
    done < <(py_chunk_ranges "${path}" "${CHUNK_SIZE}")
  fi
done

echo "audit_batch.sh: done. manifest at ${MANIFEST}"
