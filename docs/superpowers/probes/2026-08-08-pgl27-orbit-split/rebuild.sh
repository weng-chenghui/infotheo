#!/bin/sh
# Rebuild probe B = pgl27_orbit.v + block.v, then compile it with the
# project's include flags, one worker.
set -e
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg
D=docs/superpowers/probes/2026-08-08-pgl27-orbit-split
cat pgg-smc/instances/pgl27/pgl27_orbit.v "$D/block.v" > "$D/probe_b_pgl27_orbit.v"
rocq compile -q \
  -R . infotheo \
  -R pgg-smc/lib pgg_smc -R pgg-smc/protocol pgg_smc \
  -R pgg-smc/groups pgg_smc -R pgg-smc/security pgg_smc \
  -R pgg-smc/reconstruct pgg_reconstruct \
  -R pgg-smc/instances/pgl27 pgg_smc \
  "$D/probe_b_pgl27_orbit.v" 2>&1 \
  | grep -v -e 'notation-overridden' -e 'already used in scope' \
            -e 'ambiguous-paths' -e 'coercion path' -e '^Warning:$' \
            -e 'is ambiguous with existing'
