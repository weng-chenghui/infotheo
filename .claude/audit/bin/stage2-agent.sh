#!/usr/bin/env bash
# Stage 2 agent driver. Thin wrapper that delegates to the Python driver so
# that schema validation, chunking, and escalation can share PyYAML and the
# jsonschema validator.
set -euo pipefail

AUDIT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VENV_PY="${AUDIT_DIR}/venv/bin/python3"

TIER0="${1:-}"
STAGE1="${2:-}"

if [[ -z "${TIER0}" || -z "${STAGE1}" ]]; then
  echo "usage: $0 <tier0.json> <stage1.json>" >&2
  exit 2
fi

exec "${VENV_PY}" "${AUDIT_DIR}/bin/stage2-agent.py" "${TIER0}" "${STAGE1}"
