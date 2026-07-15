#!/usr/bin/env bash
# new-rule.sh — interactive scaffolder for a new audit rule.
#
# Usage: new-rule.sh <RULE_ID>
# Example: new-rule.sh A005
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <RULE_ID>   (e.g. A005, G002, D002)" >&2
  exit 1
fi

RULE_ID="$1"
if ! [[ "${RULE_ID}" =~ ^[A-Z][0-9]{3}$ ]]; then
  echo "rule id must match ^[A-Z][0-9]{3}$ (e.g. A005)" >&2
  exit 1
fi

AUDIT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
AUDIT_TEMPLATE="${AUDIT_ROOT}/template"
YAML="${AUDIT_TEMPLATE}/rules/${RULE_ID}.yaml"
MD="${AUDIT_TEMPLATE}/rules/${RULE_ID}.md"
BAD="${AUDIT_ROOT}/fixtures/bad/${RULE_ID}.v"
GOOD="${AUDIT_ROOT}/fixtures/good/${RULE_ID}.v"

for f in "${YAML}" "${MD}" "${BAD}" "${GOOD}"; do
  if [[ -e "${f}" ]]; then
    echo "refusing to overwrite ${f}" >&2
    exit 1
  fi
done

echo "category (deprecated_tactics|verbose_idioms|opaque_signatures|unused_hypotheses|overlong_proofs|naming|mathcomp_suffix|formatting):"
read -r CATEGORY
echo "severity (error|warning|info):"
read -r SEVERITY
echo "stage_mode (stage1_only|stage2_only|both):"
read -r STAGE_MODE
echo "one-line title:"
read -r TITLE

cat > "${YAML}" <<YAML
id: ${RULE_ID}
category: ${CATEGORY}
title: "${TITLE}"
severity: ${SEVERITY}
enabled: true
stage_mode: ${STAGE_MODE}
authority:
  - mathcomp-CONTRIBUTING
fast_pattern:
  pattern: 'TODO'
  ignore_in_comments: true
  file_glob: '*.v'
# agent_prompt: |
#   Describe to the agent what idiomatic and non-idiomatic look like and
#   what evidence to report.
scope: changed_hunks
fix_hint: "TODO: short guidance for the fixer."
exceptions: []
YAML

cat > "${MD}" <<MD
# ${RULE_ID} — ${TITLE}

## Rationale

TODO.

## Stages

- Stage: ${STAGE_MODE}

## Bad

\`\`\`coq
TODO
\`\`\`

## Good

\`\`\`coq
TODO
\`\`\`

## Known false-positive patterns

- TODO
MD

cat > "${BAD}" <<COQ
(* Fixture: triggers ${RULE_ID}. Do NOT compile. *)
(* TODO: violating snippet *)
COQ

cat > "${GOOD}" <<COQ
(* Fixture: no ${RULE_ID} violation. Do NOT compile. *)
(* TODO: clean snippet *)
COQ

echo "scaffolded ${RULE_ID}:"
echo "  ${YAML}"
echo "  ${MD}"
echo "  ${BAD}"
echo "  ${GOOD}"
echo
echo "Next: edit the files, then run 'make rocq-audit-lint' (or bin/lint-rules.py directly) to verify the fixture pair."
