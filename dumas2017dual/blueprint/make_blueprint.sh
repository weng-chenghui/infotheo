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
  # The library facts the "Reused Infotheo facts" section cites: the fiber
  # counting and conditional-uniformity lemmas, and the diagonal bound.
  dumas2017dual/dsdp/counting/dsdp_entropy.v
  dumas2017dual/entropy_fiber/entropy_fiber_zpq.v
  dumas2017dual/lib/extra_proba.v
  # The information-theoretic headline theorems, with their full proofs.
  dumas2017dual/dsdp/dsdp_main.v
  # The computational leg: the two-hop ladder over the corrupted-Alice
  # experiment, its two reductions, the guessing / unpredictability / simulation
  # bounds, and their transfer to the executed piSMC trace.
  dumas2017dual/dsdp/fdist_hopping/dsdp_alice_fdist_secrecy.v
  dumas2017dual/dsdp/fdist_hopping/dsdp_alice_trace_link.v
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
