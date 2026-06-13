#!/usr/bin/env bash
# Build the PGG framework blueprint: the HTML + dependency graph, plus the
# coqdoc API pages the \rocq{...} node links point at (the \dochome target).
set -euo pipefail

BP="$(cd "$(dirname "$0")" && pwd)"          # .../pgg-smc/blueprint
REPO="$(cd "$BP/../.." && pwd)"              # repo root (has _CoqProject)

# Reuse the rocqblueprint/plasTeX install from the dumas2017dual blueprint venv
# (document-agnostic). Override with PLASTEX=... if it lives elsewhere.
PLASTEX="${PLASTEX:-/Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/blueprint/.venv/bin/plastex}"

# -R mappings matching _CoqProject so coqdoc emits pgg_reconstruct.<mod>.html
# and pgg_smc.<mod>.html, the filenames the \rocq{...} links resolve to.
RFLAGS=(-R . infotheo
  -R pgg-smc/lib pgg_smc -R pgg-smc/protocol pgg_smc -R pgg-smc/groups pgg_smc
  -R pgg-smc/security pgg_smc -R pgg-smc/reconstruct pgg_reconstruct
  -R pgg-smc/instances/denboer1989 pgg_smc -R pgg-smc/instances/kim2025 pgg_smc
  -R pgg-smc/instances/s5 pgg_smc -R pgg-smc/instances/s5x5 pgg_smc)

# Modules referenced by \rocq{...} in content.tex (their .glob is present after
# a normal project build).
MODULES=(
  pgg-smc/protocol/pgg_interface.v
  pgg-smc/protocol/pgg_monodromy_profile.v
  pgg-smc/protocol/card_exchange_pismc.v
  pgg-smc/protocol/pgg_input_commitment.v
  pgg-smc/reconstruct/pgg_sharing_framework.v
  pgg-smc/reconstruct/covering_scheme.v
  pgg-smc/reconstruct/input_encoding.v
  pgg-smc/reconstruct/algebraic_rigidity.v
  pgg-smc/reconstruct/cover_tradeoff.v
  pgg-smc/reconstruct/s5_nogo.v
  pgg-smc/reconstruct/invariant_profiler.v
  pgg-smc/reconstruct/gap_dimension.v
  pgg-smc/reconstruct/cover_genus0.v
  pgg-smc/reconstruct/cover_genus1.v
  pgg-smc/reconstruct/cover_genus2.v
  pgg-smc/reconstruct/combinatorial_rigidity.v
  pgg-smc/instances/denboer1989/five_card_scheme_I5.v
  pgg-smc/instances/denboer1989/den_boer_encoding.v
  pgg-smc/instances/denboer1989/den_boer_run.v
  pgg-smc/instances/denboer1989/den_boer_profile.v
  pgg-smc/instances/denboer1989/five_card_leakage.v
  pgg-smc/instances/kim2025/five_card_kim.v
  pgg-smc/instances/kim2025/five_card_family.v
  pgg-smc/instances/kim2025/rigidity_kim_instance.v
  pgg-smc/instances/s5/rigidity_s5_instance.v
  pgg-smc/instances/s5/s5_mixing.v
  pgg-smc/instances/s5x5/rigidity_s5x5_instance.v
  pgg-smc/instances/s5x5/s5x5_pile.v
)

echo "[1/3] blueprint HTML + dependency graph (plastex)"
rm -rf "$BP/web"
( cd "$BP/src" && "$PLASTEX" -c plastex.cfg web.tex )

echo "[2/3] coqdoc API pages -> web/coqdoc (the \\dochome target)"
mkdir -p "$BP/web/coqdoc"
( cd "$REPO" && coqdoc --html --no-externals --utf8 "${RFLAGS[@]}" \
    -d "$BP/web/coqdoc" "${MODULES[@]}" )

echo "[3/3] static dependency-graph image (web/dep_graph.png)"
if command -v dot >/dev/null 2>&1; then
  grep -oE 'digraph[^`]*' "$BP/web/dep_graph_document.html" > "$BP/web/dep_graph.gv" || true
  dot -Tpng "$BP/web/dep_graph.gv" -o "$BP/web/dep_graph.png" 2>/dev/null || true
fi

echo "Done. Serve with:  (cd '$BP/web' && python3 -m http.server 8000)"
echo "Then open http://127.0.0.1:8000/  and click 'Dependency graph'."
