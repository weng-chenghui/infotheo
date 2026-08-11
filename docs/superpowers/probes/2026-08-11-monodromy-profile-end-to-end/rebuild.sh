#!/bin/sh
# Compile one probe file with the project's include flags, one worker.
# Usage: sh rebuild.sh probe_a_sufficiency.v
set -e
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg
D=docs/superpowers/probes/2026-08-11-monodromy-profile-end-to-end
rocq compile -q \
  -R . infotheo \
  -R pgg-smc/lib pgg_smc -R pgg-smc/protocol pgg_smc \
  -R pgg-smc/groups pgg_smc -R pgg-smc/security pgg_smc \
  -R pgg-smc/reconstruct pgg_reconstruct \
  -R pgg-smc/instances/pgl27 pgg_smc \
  -R pgg-smc/instances/kim2025 pgg_smc \
  -R pgg-smc/instances/denboer1989 pgg_smc \
  "$D/$1" 2>&1 \
  | grep -v -e 'notation-overridden' -e 'already used in scope' \
            -e 'ambiguous-paths' -e 'coercion path' -e '^Warning:$' \
            -e 'is ambiguous with existing'
