#!/usr/bin/env bash
# Tier K verifier. For each Stage 2 finding that carries a kernel_contract,
# spawn a headless claude session with rocq-mcp tools and evaluate the
# contract against the real proof state. Emit verdicts JSON.
set -euo pipefail

AUDIT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VENV_PY="${AUDIT_DIR}/venv/bin/python3"

STAGE2="${1:-}"
TIER0="${2:-}"
if [[ -z "${STAGE2}" || -z "${TIER0}" ]]; then
  echo "usage: $0 <stage2.json> <tier0.json>" >&2
  exit 2
fi
exec "${VENV_PY}" "${AUDIT_DIR}/bin/tier-k-verify.py" "${STAGE2}" "${TIER0}"
