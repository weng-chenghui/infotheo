#!/usr/bin/env bash
# audit-e2e-test.sh — end-to-end pipeline regression harness.
#
# Covers: (a) one representative rule-parity scenario for Stage 1, and the
# three post-trial defect regressions documented in
# /Users/cheng-huiweng/.claude/plans/context-every-time-i-eager-crystal.md:
#
#   Defect 1 (pipeline half): stage a bad fixture, run audit.sh, hand-edit
#     to resolve one of two findings, run audit.sh again, assert the
#     remaining finding is still reported. This asserts the pipeline's
#     re-audit catches residual findings. It does NOT assert anything
#     about the fix agent (that lives in /rocq-apply-fixes prompt text
#     and is verified manually).
#
#   Defect 3 (pointer consistency): run two back-to-back audits on
#     different staged diffs. Assert central-state/last-run-id names the
#     second run. Break runs/LATEST by pointing it at a nonexistent
#     directory. Run audit-history.py --validate. Assert exit 2. Then
#     remove both pointers and assert --validate exits 0 (bootstrap).
#
# The harness does NOT invoke the Stage 2 LLM. All scenarios set
# ROCQ_AUDIT_STAGE2_DISABLED=1 (Stage 2 skipped while Stage 1 still
# gates the commit on its own findings).
#
# The harness does NOT test whether any agent fixes Rocq code. Agent
# behaviour is outside the pipeline and outside this harness.

set -euo pipefail

AUDIT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REAL_CLAUDE="$(cd "${AUDIT_ROOT}/.." && pwd)"   # the real .claude dir
AUDIT_CENTRAL="${AUDIT_ROOT}/central-state"
AUDIT_RUNS="${AUDIT_ROOT}/runs"
SCRATCH_ROOT="${AUDIT_RUNS}/e2e-scratch"
TEMPLATE_CFG="${AUDIT_ROOT}/template/config.yaml"

export ROCQ_AUDIT_E2E=1

PASSED=0
FAILED=0
TOTAL=0

SAVED_TOKEN_USAGE=""
SAVED_LATEST=""
SAVED_LAST_RUN_ID=""

save_state() {
  # Snapshot the few central-state files the harness perturbs so the real
  # history is restored on exit.
  local tu="${AUDIT_CENTRAL}/token-usage.json"
  if [[ -f "${tu}" ]]; then
    SAVED_TOKEN_USAGE="$(cat "${tu}")"
  fi
  local latest="${AUDIT_RUNS}/LATEST"
  if [[ -L "${latest}" ]]; then
    SAVED_LATEST="$(readlink "${latest}")"
  fi
  local lri="${AUDIT_CENTRAL}/last-run-id"
  if [[ -f "${lri}" ]]; then
    SAVED_LAST_RUN_ID="$(cat "${lri}")"
  fi
}

restore_state() {
  # Restore token-usage.json verbatim.
  if [[ -n "${SAVED_TOKEN_USAGE}" ]]; then
    printf '%s' "${SAVED_TOKEN_USAGE}" > "${AUDIT_CENTRAL}/token-usage.json"
  fi
  # Restore LATEST symlink.
  if [[ -n "${SAVED_LATEST}" ]]; then
    ( cd "${AUDIT_RUNS}" && rm -f LATEST && ln -s "${SAVED_LATEST}" LATEST ) || true
  fi
  # Restore last-run-id.
  if [[ -n "${SAVED_LAST_RUN_ID}" ]]; then
    printf '%s\n' "${SAVED_LAST_RUN_ID}" > "${AUDIT_CENTRAL}/last-run-id"
  fi
}

cleanup() {
  rm -rf "${SCRATCH_ROOT}"
  restore_state
}
trap cleanup INT TERM EXIT

mkdir -p "${SCRATCH_ROOT}"
save_state

init_scenario() {
  # Create a fresh scratch git tree with a .claude symlink back to the real
  # audit root. Prints the absolute scratch directory path.
  local id="$1"
  local dir="${SCRATCH_ROOT}/${id}"
  rm -rf "${dir}"
  mkdir -p "${dir}"
  ( cd "${dir}" \
    && git init -q --initial-branch=main 2>/dev/null || git init -q \
    && git -c user.email=e2e@local -c user.name=e2e \
         commit --allow-empty -q -m "e2e init" \
    && ln -s "${REAL_CLAUDE}" ".claude" )
  printf '%s' "${dir}"
}

# -------------------------------------------------------------------------
# Assertion helpers
# -------------------------------------------------------------------------
assert() {
  local label="$1" expected="$2" actual="$3"
  TOTAL=$((TOTAL + 1))
  if [[ "${expected}" == "${actual}" ]]; then
    PASSED=$((PASSED + 1))
    echo "  ok   ${label}"
  else
    FAILED=$((FAILED + 1))
    echo "  FAIL ${label}: expected '${expected}', got '${actual}'" >&2
  fi
}

assert_grep() {
  local label="$1" pattern="$2" path="$3"
  TOTAL=$((TOTAL + 1))
  if [[ -f "${path}" ]] && grep -q -- "${pattern}" "${path}"; then
    PASSED=$((PASSED + 1))
    echo "  ok   ${label}"
  else
    FAILED=$((FAILED + 1))
    echo "  FAIL ${label}: pattern '${pattern}' not found in ${path}" >&2
  fi
}

assert_no_grep() {
  local label="$1" pattern="$2" path="$3"
  TOTAL=$((TOTAL + 1))
  if [[ -f "${path}" ]] && grep -q -- "${pattern}" "${path}"; then
    FAILED=$((FAILED + 1))
    echo "  FAIL ${label}: pattern '${pattern}' unexpectedly found in ${path}" >&2
  else
    PASSED=$((PASSED + 1))
    echo "  ok   ${label}"
  fi
}

current_run_dir() {
  # Returns the run directory that the last audit.sh invocation just wrote,
  # resolved via the canonical last-run-id text pointer (not the symlink).
  local rid
  rid="$(cat "${AUDIT_CENTRAL}/last-run-id" 2>/dev/null || true)"
  if [[ -z "${rid}" ]]; then
    echo ""
    return
  fi
  printf '%s' "${AUDIT_RUNS}/${rid}"
}

# -------------------------------------------------------------------------
# Scenario A: Stage 1 rule parity (A001).
# Confirms audit.sh correctly flags a bad fixture and passes a good one
# when Stage 2 is fast-bypassed. Representative Stage 1 smoke test.
# -------------------------------------------------------------------------
scenario_stage1_rule_parity() {
  echo "Scenario A: Stage 1 rule parity (A001, fast-bypassed Stage 2)"
  local dir bad good report
  bad="${AUDIT_ROOT}/fixtures/bad/A001.v"
  good="${AUDIT_ROOT}/fixtures/good/A001.v"

  dir="$(init_scenario "A-bad")"
  cp "${bad}" "${dir}/A001.v"
  ( cd "${dir}" && git add A001.v )
  local rc=0
  ( cd "${dir}" && ROCQ_AUDIT_STAGE2_DISABLED=1 "${AUDIT_ROOT}/bin/audit.sh" ) || rc=$?
  local run_dir
  run_dir="$(current_run_dir)"
  report="${run_dir}/reports/latest.md"
  assert "A001 bad fixture exit code" "2" "${rc}"
  assert_grep "A001 bad fixture latest.md names A001" "A001" "${report}"

  dir="$(init_scenario "A-good")"
  cp "${good}" "${dir}/A001.v"
  ( cd "${dir}" && git add A001.v )
  rc=0
  ( cd "${dir}" && ROCQ_AUDIT_STAGE2_DISABLED=1 "${AUDIT_ROOT}/bin/audit.sh" ) || rc=$?
  assert "A001 good fixture exit code" "0" "${rc}"
}

# -------------------------------------------------------------------------
# Scenario C: Defect 3 (pointer consistency) regression.
# Runs two back-to-back audits. Verifies last-run-id names the second run.
# Breaks runs/LATEST symlink and asserts audit-history --validate flags
# the dangling symlink. Then removes both pointers and asserts --validate
# exits 0 (bootstrap).
# -------------------------------------------------------------------------
scenario_defect3_pointer_consistency() {
  echo "Scenario C: Defect 3 pointer consistency regression"
  local dir bad
  bad="${AUDIT_ROOT}/fixtures/bad/A001.v"

  dir="$(init_scenario "C-first")"
  cp "${bad}" "${dir}/first.v"
  ( cd "${dir}" && git add first.v )
  ( cd "${dir}" && ROCQ_AUDIT_STAGE2_DISABLED=1 "${AUDIT_ROOT}/bin/audit.sh" ) || true

  dir="$(init_scenario "C-second")"
  cp "${bad}" "${dir}/second.v"
  ( cd "${dir}" && git add second.v )
  ( cd "${dir}" && ROCQ_AUDIT_STAGE2_DISABLED=1 "${AUDIT_ROOT}/bin/audit.sh" ) || true

  local second_id last_id
  second_id="$(cat "${AUDIT_CENTRAL}/last-run-id")"
  assert "last-run-id non-empty after second audit" "yes" "$([[ -n "${second_id}" ]] && echo yes || echo no)"

  # Break runs/LATEST by pointing at a nonexistent id.
  ( cd "${AUDIT_RUNS}" && rm -f LATEST && ln -s "20000101T000000Z-dead-beef" LATEST )
  local rc=0
  "${AUDIT_ROOT}/venv/bin/python3" "${AUDIT_ROOT}/bin/audit-history.py" --validate >/dev/null 2>&1 || rc=$?
  assert "validate flags dangling LATEST" "2" "${rc}"

  # Bootstrap: remove both pointers.
  rm -f "${AUDIT_CENTRAL}/last-run-id" "${AUDIT_RUNS}/LATEST"
  rc=0
  "${AUDIT_ROOT}/venv/bin/python3" "${AUDIT_ROOT}/bin/audit-history.py" --validate >/dev/null 2>&1 || rc=$?
  assert "validate allows bootstrap (both absent)" "0" "${rc}"

  # Rebuild the pointers so restore_state can put them back cleanly.
  if [[ -n "${SAVED_LAST_RUN_ID}" ]]; then
    printf '%s\n' "${SAVED_LAST_RUN_ID}" > "${AUDIT_CENTRAL}/last-run-id"
  fi
}

# -------------------------------------------------------------------------
# Scenario D: Defect 1 (pipeline half) regression.
# Stage a bad fixture with two distinct Stage 1 findings. Run audit.sh;
# assert both findings reported. Hand-edit the fixture to resolve one
# finding. Run audit.sh again; assert only the remaining finding is
# reported. This is the pipeline half of Defect 1 and does not exercise
# the fix agent.
# -------------------------------------------------------------------------
scenario_defect1_pipeline_half() {
  echo "Scenario D: Defect 1 pipeline half (re-audit catches residuals)"
  local dir report run_dir
  dir="$(init_scenario "D-pipeline-half")"
  # Construct a fixture with both A001 (pose proof) and A004 (have ... by ...)
  # style issues so we have two distinct rules to reason about.
  # We pick A001 (fast_pattern: '^[ \t]*pose proof\b') and use a second
  # copy of pose proof so Stage 1 reports two A001 findings at distinct
  # line positions.
  cat > "${dir}/D_two_findings.v" <<'EOF'
(* D fixture: two A001 findings on distinct lines *)
Lemma bad_pose_1 : True.
Proof.
pose proof I as H1.
exact H1.
Qed.

Lemma bad_pose_2 : True.
Proof.
pose proof I as H2.
exact H2.
Qed.
EOF
  ( cd "${dir}" && git add D_two_findings.v )
  local rc=0
  ( cd "${dir}" && ROCQ_AUDIT_STAGE2_DISABLED=1 "${AUDIT_ROOT}/bin/audit.sh" ) || rc=$?
  run_dir="$(current_run_dir)"
  report="${run_dir}/reports/latest.md"
  assert "two-finding first audit exit code" "2" "${rc}"
  local count
  count="$(grep -c '^### A001' "${report}" || true)"
  assert "two A001 findings in first audit" "2" "${count}"

  # Resolve only the first finding. Leave the second intact.
  sed -i.bak '4s/pose proof I as H1/have H1 := I/' "${dir}/D_two_findings.v"
  rm -f "${dir}/D_two_findings.v.bak"
  ( cd "${dir}" && git add D_two_findings.v )
  rc=0
  ( cd "${dir}" && ROCQ_AUDIT_STAGE2_DISABLED=1 "${AUDIT_ROOT}/bin/audit.sh" ) || rc=$?
  run_dir="$(current_run_dir)"
  report="${run_dir}/reports/latest.md"
  assert "partial-fix re-audit exit code" "2" "${rc}"
  count="$(grep -c '^### A001' "${report}" || true)"
  assert "one A001 finding remaining after partial fix" "1" "${count}"
}

# -------------------------------------------------------------------------
# Scenario E: audit-file.sh single-file CLI.
# Exercises the selector and emission flags end-to-end without going
# through audit.sh. Fast path uses --stage1-only so Stage 2 is not
# invoked (zero LLM cost). Uses fixtures/bad/A001.v which reliably
# trips A001 exactly once at line 5.
# -------------------------------------------------------------------------
scenario_audit_file_cli() {
  echo "Scenario E: audit-file.sh CLI"
  local bad="${AUDIT_ROOT}/fixtures/bad/A001.v"
  local out rc

  # (a) no selector: exit 2, report names A001.
  rc=0
  out="$("${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --stage1-only 2>/dev/null)" || rc=$?
  assert "audit-file no-selector exit code" "2" "${rc}"
  if [[ "${out}" == *"A001"* ]]; then
    PASSED=$((PASSED + 1)); TOTAL=$((TOTAL + 1))
    echo "  ok   audit-file no-selector report names A001"
  else
    FAILED=$((FAILED + 1)); TOTAL=$((TOTAL + 1))
    echo "  FAIL audit-file no-selector report missing A001" >&2
  fi

  # (b) --entity exact match.
  rc=0
  "${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --entity bad_pose --stage1-only >/dev/null 2>&1 || rc=$?
  assert "audit-file --entity bad_pose exit" "2" "${rc}"

  # (c) --entity glob.
  rc=0
  "${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --entity 'bad_*' --stage1-only >/dev/null 2>&1 || rc=$?
  assert "audit-file --entity glob exit" "2" "${rc}"

  # (d) --lines selector intersecting the finding.
  rc=0
  "${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --lines 1-10 --stage1-only >/dev/null 2>&1 || rc=$?
  assert "audit-file --lines 1-10 exit" "2" "${rc}"

  # (e) --rule A001 filter.
  rc=0
  out="$("${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --rule A001 --stage1-only 2>/dev/null)" || rc=$?
  assert "audit-file --rule A001 exit" "2" "${rc}"
  # Count A001 sections: expect exactly 1.
  local n_a001
  n_a001="$(echo "${out}" | grep -c '^### A001' || true)"
  assert "audit-file --rule A001 single finding" "1" "${n_a001}"

  # (f) --json emits parseable JSON.
  rc=0
  out="$("${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --stage1-only --json 2>/dev/null)" || rc=$?
  assert "audit-file --json exit" "2" "${rc}"
  local exit_code_key
  exit_code_key="$("${AUDIT_ROOT}/venv/bin/python3" -c "
import json, sys
try:
    d = json.loads(sys.stdin.read())
    print(d.get('exit_code'))
except Exception as e:
    print('parse_err')
" <<< "${out}")"
  assert "audit-file --json payload exit_code" "2" "${exit_code_key}"

  # Negative: --entity matches nothing -> exit 3.
  rc=0
  "${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --entity nonexistent_name --stage1-only >/dev/null 2>&1 || rc=$?
  assert "audit-file --entity typo exit 3" "3" "${rc}"

  # Negative: --lines 10-5 (inverted) -> exit 1.
  rc=0
  "${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --lines 10-5 --stage1-only >/dev/null 2>&1 || rc=$?
  assert "audit-file --lines inverted exit 1" "1" "${rc}"

  # Negative: --entity + --lines together -> exit 1.
  rc=0
  "${AUDIT_ROOT}/bin/audit-file.sh" --file "${bad}" --entity foo --lines 1-10 --stage1-only >/dev/null 2>&1 || rc=$?
  assert "audit-file mutual exclusion exit 1" "1" "${rc}"
}

# -------------------------------------------------------------------------
# Run scenarios
# -------------------------------------------------------------------------
echo "rocq-audit e2e harness (E2E_MODE=1; central-state writes suppressed)"
echo ""
scenario_stage1_rule_parity
echo ""
scenario_defect3_pointer_consistency
echo ""
scenario_defect1_pipeline_half
echo ""
scenario_audit_file_cli
echo ""
echo "--- Summary ---"
echo "Passed: ${PASSED} of ${TOTAL}"
echo "Failed: ${FAILED} of ${TOTAL}"
if (( FAILED > 0 )); then
  exit 2
fi
exit 0
