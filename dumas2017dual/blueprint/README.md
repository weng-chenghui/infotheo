# DSDP derivation-chain blueprint

A `rocqblueprint` (a Rocq port of Patrick Massot's `leanblueprint`) presentation
of the DSDP corrupted-Alice IND-CPA secrecy auto-derivation chain: from the one
protocol program and the one control record to the final `2*epsilon_cpa` bound,
with the deferred information-theoretic and composition legs shown as targets.

## What is here

- `src/web.tex`, `src/plastex.cfg`, `src/macros/*`, `src/content.tex` — the
  blueprint source. `content.tex` holds the full chain as ~38 nodes across eight
  chapters (symbolic model, corrupted view, lowering, denotation, IND-CPA hybrid
  bound, control record + generic theorem, DSDP instance, deferred legs). Each
  node carries `\rocq{<full Rocq name>}` (the formal declaration), `\rocqok`
  (formalized), and `\uses{...}` (dependency edges).
- `make_blueprint.sh` — one-command build: the blueprint HTML + dependency graph,
  the coqdoc API pages the `\rocq{...}` links point at, and the static graph PNG.
- `web/` (gitignored) — the generated site: `index.html`, `sect0001..8.html`,
  `dep_graph_document.html`, `dep_graph.png`, and `web/coqdoc/` (the coqdoc pages).
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
2. **coqdoc API pages** for the five referenced modules into `web/coqdoc/`. The
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

The build succeeds end to end. The dependency graph renders the full chain with
proof-status coloring: definitions light green ("defined"), proved
lemmas/theorems dark green ("fully proved"), and the two deferred legs as blue
dashed nodes ("can state, not yet formalized"). Every node's "Rocq" link opens
the corresponding coqdoc declaration (HTTP 200). The only cosmetic note is that
`dvisvgm` is absent, so inline math uses plasTeX's fallback raster imager.
