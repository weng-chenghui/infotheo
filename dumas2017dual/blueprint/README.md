# DSDP security blueprint

A `rocqblueprint` (a Rocq port of Patrick Massot's `leanblueprint`) presentation
of the machine-checked security analysis of SMC-DSDP against one semi-honest
corrupted party: the corrupted-Alice output and ciphertext channels, and the
corrupted-relay channels.

## What is here

- `src/web.tex`, `src/plastex.cfg`, `src/macros/*`, `src/security.tex` — the
  blueprint source. `security.tex` is the whole document: a Foundations part (the
  message flow, party views, correctness), a Corrupted Alice part (the
  conditional-entropy residual of the plaintext channel, the reused Infotheo
  fiber facts, the two-hop ladder that bounds the ciphertext channel, the
  simulation bound, the transfer of all three bounds to the executed piSMC
  trace, and the degenerate-query tightness boundary), and a Corrupted relay
  part (the one-time-pad secrecy of each relay's view). Each node carries
  `\rocq{<full Rocq name>}` (the formal declaration), `\rocqok` (formalized),
  and `\uses{...}` (dependency edges).
- The computational leg is SSProve-free. Every `\varepsilon` in it is the
  real-or-zero advantage `indcpa_fdist_epsilon` of a reduction constructed in
  `dsdp/fdist_hopping/dsdp_alice_fdist_secrecy.v`, so the blueprint states no
  cryptographic assumption as an axiom.
- `make_blueprint.sh` — one-command build: the blueprint HTML + dependency graph,
  the coqdoc API pages the `\rocq{...}` links point at, and the static graph PNG.
- `web/` (gitignored) — the generated site: `index.html`, the per-chapter
  `sect*.html`, `dep_graph_document.html`, `dep_graph.png`, and `web/coqdoc/`
  (the coqdoc pages).
- `.venv/` (gitignored) — local Python environment with rocqblueprint installed.

## Build

    dumas2017dual/blueprint/make_blueprint.sh
    (cd dumas2017dual/blueprint/web && python3 -m http.server 8000)
    # open http://127.0.0.1:8000/  and click "Dependency graph"

View through `http://`, not by double-clicking a file: the graph is drawn by an
in-browser WASM graphviz that does not load over `file://`.

The build has two halves, both in `make_blueprint.sh`:

1. **Blueprint HTML + graph** via plasTeX. The `rocqblueprint` CLI assumes the
   blueprint lives at the git root (`<root>/blueprint`); this one lives under
   `dumas2017dual/`, so the script calls `plastex -c plastex.cfg web.tex`
   directly (exactly what `rocqblueprint web` runs internally).
2. **coqdoc API pages** for the referenced modules into `web/coqdoc/`. The
   `\rocq{M.decl}` links resolve to `coqdoc/M.html#decl` because `web.tex` sets
   `\dochome{coqdoc}`. coqdoc needs each module's `.glob`, which a normal project
   build produces. The coqdoc file naming (`infotheo.<path>.<module>.html`) and
   anchors (`#<decl>`) match the blueprint URL scheme exactly.

To re-create the venv from scratch (graphviz required: `brew install graphviz`):

    python3 -m venv .venv
    GVP=$(brew --prefix graphviz)
    .venv/bin/pip install \
      --config-settings=--global-option=build_ext \
      --config-settings=--global-option="-I$GVP/include/" \
      --config-settings=--global-option="-L$GVP/lib/" pygraphviz
    .venv/bin/pip install rocqblueprint

## Status

The dependency graph renders the analysis with proof-status coloring:
definitions light green ("defined"), proved lemmas/theorems dark green ("fully
proved"), and the one open statement (worst-case simulation) as a blue dashed
node ("can state, not yet formalized"). Every node's "Rocq" link opens the
corresponding coqdoc declaration. The only cosmetic note is that `dvisvgm` is
absent, so inline math uses plasTeX's fallback raster imager.

`check_coverage.py` is the ratchet that keeps the node set and the `MODULES`
scope in step; see `COVERAGE.md`.
