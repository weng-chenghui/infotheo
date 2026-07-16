#!/usr/bin/env bash
# Build the DSDP derivation-chain blueprint: the HTML + dependency graph, plus
# the coqdoc API pages the \rocq{...} node links point at (the \dochome target).
set -euo pipefail

BP="$(cd "$(dirname "$0")" && pwd)"          # .../dumas2017dual/blueprint
REPO="$(cd "$BP/../.." && pwd)"              # repo root (has _CoqProject, -R . infotheo)
PLASTEX="$BP/.venv/bin/plastex"

# Modules the blueprint references via \rocq{...}; coqdoc needs their .glob
# (present after a normal build of the project).
MODULES=(
  dumas2017dual/dsdp/symbolic_game/dsdp_symbolic_exec.v
  dumas2017dual/dsdp/symbolic_game/dsdp_game_derivation.v
  dumas2017dual/dsdp/symbolic_game/dsdp_game_code.v
  dumas2017dual/dsdp/indcpa_hopping/dsdp_indcpa_advantage.v
  homomorphic_encryption/indcpa_ror.v
  # Modules cited green by Part II (it_bound_bridge.tex): the Infotheo fiber
  # facts and the full output-channel chain: the derivation extension, the
  # S-exposing games + 2*epsilon_cpa, the guessing layer + connector, and the
  # information-theoretic bound + composition (footprint frame, sample fdist, the
  # output-determined guess kernel + guess _|_ V2 | S, the route-F fiber bound,
  # and the triangle composition).  Every Part II node is green.
  dumas2017dual/dsdp/counting/dsdp_entropy.v
  dumas2017dual/entropy_fiber/entropy_fiber_zpq.v
  dumas2017dual/dsdp/indcpa_hopping/dsdp_guess_fiber.v
  dumas2017dual/lib/extra_proba.v
  # The main-results file: every headline theorem, with its full proof.
  dumas2017dual/dsdp/dsdp_main.v
  # The simulation axis: the ideal functionality, the simulator, and the
  # factorization the simulation-security chapter (security.tex) cites.
  dumas2017dual/dsdp/simulation/dsdp_simulator.v
  # The SSProve<->Infotheo connector: the footprint-frame lemmas the
  # output-secrecy chain (it_bound_bridge.tex) cites.
  dumas2017dual/dsdp/convert/dsdp_convert.v
)

echo "[1/3] blueprint HTML + dependency graph (plastex)"
rm -rf "$BP/web"
( cd "$BP/src" && "$PLASTEX" -c plastex.cfg web.tex )

echo "[2/3] coqdoc API pages -> web/coqdoc (the \\dochome target)"
mkdir -p "$BP/web/coqdoc"
( cd "$REPO" && coqdoc --html --no-externals --utf8 -R . infotheo \
    -d "$BP/web/coqdoc" "${MODULES[@]}" )

echo "[3/3] static dependency-graph image (web/dep_graph.png)"
if command -v dot >/dev/null 2>&1; then
  grep -oE 'digraph[^`]*' "$BP/web/dep_graph_document.html" > "$BP/web/dep_graph.gv" || true
  dot -Tpng "$BP/web/dep_graph.gv" -o "$BP/web/dep_graph.png" 2>/dev/null || true
fi

echo "Done. Serve with:  (cd '$BP/web' && python3 -m http.server 8000)"
echo "Then open http://127.0.0.1:8000/  and click 'Dependency graph'."
