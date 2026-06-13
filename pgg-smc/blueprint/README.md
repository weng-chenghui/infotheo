# PGG framework blueprint

A `rocqblueprint` (a Rocq port of Patrick Massot's `leanblueprint`) presentation
of the PGG monodromy-MPC framework's modularity and its den Boer instantiation:
Part I is the framework (interfaces + generic theorems, no instance named),
Part II is instantiation (den Boer end-to-end, the Kim five-card family, and the
S5 / S5xS5 AG-code no-go), closing with a modularity ledger.

## What is here

- `src/web.tex`, `src/plastex.cfg`, `src/blueprint.sty`, `src/macros/*`,
  `src/content.tex` — the blueprint source. `content.tex` holds the story as
  ~30 nodes across eleven chapters. Each node carries `\rocq{<full Rocq name>}`
  (the formal declaration, post the 2026-06-13 naming rename), `\rocqok`
  (proved/defined, green), and `\uses{...}` (dependency edges). The six justified
  axioms (S5 / S5xS5 group orders and geometric realizations) carry no `\rocqok`
  and render blue-dashed (assumed).
- `make_blueprint.sh` — one-command build: the blueprint HTML + dependency graph,
  the coqdoc API pages the `\rocq{...}` links point at, and the static graph PNG.
- `web/` (gitignored) — the generated site: `index.html`, `sect00NN.html`,
  `dep_graph_document.html`, `dep_graph.png`, `images/img-0001.png` (the
  architecture diagram, Figure 1), and `web/coqdoc/` (the coqdoc pages).

## Build

    pgg-smc/blueprint/make_blueprint.sh
    (cd pgg-smc/blueprint/web && python3 -m http.server 8000)
    # open http://127.0.0.1:8000/  and click "Dependency graph"

View through `http://`, not by double-clicking a file: the graph is drawn by an
in-browser WASM graphviz that does not load over `file://`.

The build has two halves, both in `make_blueprint.sh`:

1. **Blueprint HTML + graph** via plasTeX. The script reuses the `rocqblueprint`
   install from the `dumas2017dual/blueprint/.venv` (document-agnostic);
   override with `PLASTEX=/path/to/plastex`. It calls `plastex -c plastex.cfg
   web.tex` directly (what `rocqblueprint web` runs internally), since the
   project is not at the git root.
2. **coqdoc API pages** for the referenced modules into `web/coqdoc/`. The
   `\rocq{M.decl}` links resolve to `coqdoc/M.html#decl` because `web.tex` sets
   `\dochome{coqdoc}`. coqdoc needs each module's `.glob`, which a normal project
   build produces; the `-R` mappings emit `pgg_reconstruct.<mod>.html` and
   `pgg_smc.<mod>.html`, matching the blueprint URL scheme.

## Status

The build succeeds end to end. The dependency graph renders the framework and
den Boer chains green (defined/proved), with the six S5 / S5xS5 axioms as
blue-dashed assumed nodes. Every node's "Rocq" link opens the corresponding
coqdoc declaration. `dvisvgm` is absent, so inline math and the TikZ figure use
plasTeX's raster imager (pdflatex), which is why `src/blueprint.sty` is kept
locally for the imager.
