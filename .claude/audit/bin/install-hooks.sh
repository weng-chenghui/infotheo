#!/usr/bin/env bash
# Install the native git pre-commit shim into every worktree of this repo.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
SHIM="${REPO_ROOT}/.claude/audit/git-hooks/pre-commit"

if [[ ! -x "${SHIM}" ]]; then
  chmod +x "${SHIM}" 2>/dev/null || true
fi

install_into() {
  local target_hooks_dir="$1"
  if [[ ! -d "${target_hooks_dir}" ]]; then
    return 0
  fi
  local dest="${target_hooks_dir}/pre-commit"
  if [[ -L "${dest}" ]]; then
    local current="$(readlink "${dest}")"
    if [[ "${current}" == "${SHIM}" ]]; then
      echo "up-to-date: ${dest}"
      return 0
    fi
  fi
  if [[ -e "${dest}" && ! -L "${dest}" ]]; then
    echo "backup: ${dest} -> ${dest}.pre-rocq-audit.$(date +%s)"
    mv "${dest}" "${dest}.pre-rocq-audit.$(date +%s)"
  fi
  ln -sf "${SHIM}" "${dest}"
  echo "installed: ${dest} -> ${SHIM}"
}

# Main worktree.
install_into "$(git rev-parse --git-path hooks 2>/dev/null || echo "${REPO_ROOT}/.git/hooks")"

# Additional worktrees.
while IFS= read -r wt; do
  [[ -z "${wt}" ]] && continue
  [[ "${wt}" == "${REPO_ROOT}" ]] && continue
  git_dir="$(git -C "${wt}" rev-parse --git-path hooks 2>/dev/null || true)"
  [[ -n "${git_dir}" ]] && install_into "${git_dir}"
done < <(git worktree list --porcelain | awk '/^worktree /{print $2}')

# Verify toolchain.
missing=()
"${REPO_ROOT}/.claude/audit/venv/bin/python3" -c "import yaml, jsonschema" 2>/dev/null || missing+=("venv/python+pyyaml+jsonschema")
command -v git >/dev/null || missing+=("git")
command -v shasum >/dev/null || missing+=("shasum")
if (( ${#missing[@]} > 0 )); then
  echo "WARNING: missing tools: ${missing[*]}" >&2
fi

echo "done."
