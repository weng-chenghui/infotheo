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
  dumas2017dual/dsdp/dsdp_symbolic.v
  dumas2017dual/dsdp/dsdp_game_symbolic.v
  dumas2017dual/dsdp/dsdp_game_code.v
  dumas2017dual/dsdp/dsdp_indcpa_security.v
  homomorphic_encryption/indcpa_ror.v
  # Modules cited green by Part II (it_bound_bridge.tex): the Infotheo fiber
  # facts and the committed output-channel chain (derivation extension, the
  # S-exposing games + 2*epsilon_cpa, the guessing layer + connector).  The
  # remaining option-B construction nodes (footprint, sample fdist, identities,
  # fiber bound, composition) are blue (no \rocq link yet).
  dumas2017dual/dsdp/dsdp_entropy.v
  dumas2017dual/entropy_fiber/entropy_fiber_zpq.v
  dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v
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
