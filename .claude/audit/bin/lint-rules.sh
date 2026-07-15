#!/usr/bin/env bash
# lint-rules.sh — invoke the catalog linter via the bundled venv.
# In the execroot model, rules and fixtures live under template/.
#
# With --full, also runs the end-to-end pipeline regression harness at
# audit-e2e-test.sh after the normal lint pass succeeds.
set -euo pipefail
AUDIT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REPO_ROOT="$(git -C "${AUDIT_ROOT}" rev-parse --show-toplevel 2>/dev/null || echo "${AUDIT_ROOT}/../..")"
AUDIT_TEMPLATE="${AUDIT_ROOT}/template"
AUDIT_CENTRAL="${AUDIT_ROOT}/central-state"
export AUDIT_DIR="${AUDIT_ROOT}" AUDIT_TEMPLATE AUDIT_CENTRAL REPO_ROOT

FULL=0
PASSTHROUGH=()
for arg in "$@"; do
  case "${arg}" in
    --full) FULL=1 ;;
    *) PASSTHROUGH+=("${arg}") ;;
  esac
done

"${AUDIT_ROOT}/venv/bin/python3" "${AUDIT_ROOT}/bin/lint-rules.py" "${PASSTHROUGH[@]:+${PASSTHROUGH[@]}}"
LINT_RC=$?
if (( LINT_RC != 0 )); then
  exit ${LINT_RC}
fi

if (( FULL == 1 )); then
  exec "${AUDIT_ROOT}/bin/audit-e2e-test.sh"
fi

exit 0
