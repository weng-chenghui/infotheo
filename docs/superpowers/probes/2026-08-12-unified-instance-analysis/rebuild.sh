#!/bin/sh
# Compile one probe file with the project's include flags, one worker.
# Usage: sh rebuild.sh probe_s5_plugs.v
# Exit code is the compiler's own (the filter runs on a captured log so a
# red compile cannot be masked by the grep pipe).
set -e
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg
D=docs/superpowers/probes/2026-08-12-unified-instance-analysis
LOG=$(mktemp)
status=0
rocq compile -q \
  -R . infotheo \
  -R pgg-smc/lib pgg_smc -R pgg-smc/protocol pgg_smc \
  -R pgg-smc/groups pgg_smc -R pgg-smc/security pgg_smc \
  -R pgg-smc/reconstruct pgg_reconstruct \
  -R pgg-smc/instances/pgl27 pgg_smc \
  -R pgg-smc/instances/kim2025 pgg_smc \
  -R pgg-smc/instances/denboer1989 pgg_smc \
  -R pgg-smc/instances/s5 pgg_smc \
  -R pgg-smc/instances/s5x5 pgg_smc \
  -R pgg-smc/instances/abelian pgg_smc \
  -R pgg-smc/instances/cyclic pgg_smc \
  -R pgg-smc/manifest pgg_smc \
  -R docs/superpowers/probes/2026-08-12-unified-instance-analysis uia_probe \
  "$D/$1" >"$LOG" 2>&1 || status=$?
grep -v -e 'notation-overridden' -e 'already used in scope' \
        -e 'ambiguous-paths' -e 'coercion path' -e '^Warning:$' \
        -e 'is ambiguous with existing' -e 'deprecated-library-file' \
        -e 'notation-incompatible-prefix' "$LOG" || true
rm -f "$LOG"
exit $status
