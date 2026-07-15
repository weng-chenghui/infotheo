#!/usr/bin/env bash
# audit-history.sh — aggregate the audit state into a dashboard.
set -euo pipefail

AUDIT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VENV_PY="${AUDIT_DIR}/venv/bin/python3"

exec "${VENV_PY}" "${AUDIT_DIR}/bin/audit-history.py" "$@"
