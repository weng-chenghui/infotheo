# Update plan: reflect the one-record facade in the thesis overview chapter and the shared architecture diagram

Date: 2026-06-09
Status: PLAN ONLY (not executed). Awaiting go-ahead.

## Why

The `obs_of_procs` + one-record facade work (commits `82adb46`, `d9a670e`,
`3b5ffbb`, `14f8c7c`, `9d25580`, `d8a4505`) changed two things that the thesis
chapter `aplas2024-poster/thesis/chapters/derived-overview.tex` and the shared
architecture figure do not yet reflect:

1. **The derived/declared boundary moved.** Before, only the wire ciphertexts and
   the homomorphic combine terms were derived; sample typing, hop sites, and the
   leak set were declared configuration. Now `obs_of_procs` derives the WHOLE
   corrupted-view trace: the sample set and first-appearance order, the hop
   reception observations (the party and secret read off each declared
   ciphertext's `HE_enc` shape), and the combines. What stays declared is a short
   list of record fields: the corrupt party's program, the received hop
   ciphertext stream, the challenge secret, the leak ORDER, and the two
   cardinalities. (For DSDP the challenge is not a free choice: `dsdp_problem`
   fixes it to Bob's secret name `dsdp_v2_name`, the cell the trace writes.)
2. **The declared part is reified as one record.** Those declared fields, plus the
   concrete scheme and its marshalling, are the fields of
   `dsdp_indcpa_secrecy_problem`. From one record the corrupted view, the real
   game, the all-zero game, and the hop count are all projections, and a generic
   theorem `dsdp_indcpa_secrecy` bounds advantage by `count * epsilon_cpa`. The
   DSDP corollary `dsdp_problem_secure` reads off `2 * epsilon_cpa`.

The architecture (one program, two readings, two halves meeting at the reified
game, `advantage_le` giving `k * epsilon_cpa`) is still accurate. Only the
config/scope is understated.

## Part A — Thesis chapter `derived-overview.tex` (prose)

Targeted edits, paragraph by paragraph:

- **Scope paragraph (current lines 35-46), rewrite the derived/declared split.**
  Derived now = the whole observation trace: the sampled scalars and randomness,
  the reception observations read off each declared ciphertext's shape, and the
  homomorphic combinations. Declared now = the record fields (corrupt party
  program, received hop ciphertext stream, challenge secret, leak order, two
  cardinalities). Keep the closing "the generality lives in the back end"
  sentence.
- **Add the facade.** One short paragraph after the scope paragraph: the declared
  fields plus the scheme and marshalling form one record; the corrupted view, the
  two games, and the hop count are projections of it; one generic theorem gives
  `count * epsilon_cpa`, and the DSDP instance fills the record, its challenge
  fixed to Bob's secret and its hop count two, and reads off `2 * epsilon_cpa`.
  Sidenotes: `\coqin{dsdp_indcpa_secrecy_problem}` and
  `\coqin{dsdp_indcpa_secrecy}` in `dsdp/dsdp_game_symbolic.v`,
  `\coqin{dsdp_problem_secure}` in `dsdp/dsdp_indcpa_security.v`.
- **Symbolic-reading paragraph (lines 13-23).** Light touch: it currently says the
  symbolic run "exposes the homomorphic expressions that party sends as ordinary
  data." Extend to "exposes the corrupted party's whole view as ordinary data:
  what it samples, receives, assembles, and leaks," so it matches `obs_of_procs`.
- **Closing roadmap paragraph (lines 99-109).** The phrase "the schema by which a
  k-hop protocol instantiates that bound" becomes "the one record by which a
  protocol instance fixes the corrupted view and the generic bound specialises to
  `k * epsilon_cpa`."
- **Bracket with `/thesis-review`** per the standing convention: commit the chapter
  edit, run `/thesis-review` on `derived-overview.tex`, apply fixes, commit.

## Part B — The architecture figure (TikZ), applied to BOTH copies

The figure exists in two copies that must stay in sync. They are NOT
byte-identical today: the bodies already diverge in two macros, and any edit must
preserve that per-copy split.
- thesis: `aplas2024-poster/thesis/chapters/derived-overview.tex`,
  `\label{fig:derived:architecture}`. The bound node spells
  `\varepsilon_{\mathrm{cpa}}`; the caption uses `\ssprove{}`.
- blueprint: `infotheo .../dumas2017dual/blueprint/src/content.tex`,
  `\label{fig:bp:architecture}`. The bound node spells `\epscpa` (defined in
  `macros/common.tex`); the caption uses the plain text "SSProve".
Everything else (the other twelve nodes, all edges, the dashed divider, the two
italic labels) is byte-identical.

### Node/edge changes (concrete, no placeholders)

1. Rename `cfg` box text
   `Declared security-model configuration`
   -> `Control record: corrupt party, received hops, challenge, leak order, cardinalities`
   and keep it as the single declared source. (Listing "received hops" here is
   what keeps the figure honest: the received-ciphertext stream is the declared
   field `sp_received_hop_ciphertexts`.)
2. Rename `comb` box text
   `Derived combine terms`
   -> `Derived trace: samples, receptions, combines`
   The symbolic run now yields the whole trace, not only the combines. Read at two
   levels: `cfg` supplies the received-ciphertext stream as a declared field, and
   the walk derives the reception OBSERVATIONS by reading the party and secret off
   each one. So "receptions" in this box are derived; the stream they read sits in
   the `cfg` box.
3. Re-wire edges into `trace` so the record and the symbolic run both feed it:
   keep `run -> comb -> trace`; keep `cfg -> trace`. Optionally add `cfg -> run`
   to show the record's symbolic fields drive the walk (decide when editing; the
   minimal change keeps the existing two in-edges).
4. Rename the final `bound` box text `Advantage $\le k\,...$`, spelling the
   per-copy macro (this is the second of the two divergence points above):
   - thesis copy: `Generic bound $k\,\varepsilon_{\mathrm{cpa}}$; DSDP $2\,\varepsilon_{\mathrm{cpa}}$`
   - blueprint copy: `Generic bound $k\,\epscpa$; DSDP $2\,\epscpa$`
   so the generic-theorem / instance split shows.
5. Keep the front-end / back-end dashed divider and the two italic labels
   unchanged.

### Resulting top-of-center column (for reference)

```
   Protocol procedures (one program) over the protocol interface
        /                                              \
  Concrete instance                              Symbolic instance
        |                                              |
  Correctness, termination,                Symbolic run of the corrupted party
  duality preserved                                    |
                                            Derived trace: samples, receptions, combines
   Control record: corrupt party, received  -------->  |
   hops, challenge, leak order, cardinalities  \       |
                                              -> Observation trace
                                                       |
   ---- front end | back end ----            Reified game
                                                       |
                                            Denotation into SSProve
                                                       |
                                              SSProve game
                                                       |
                                            Hybrid ladder, k IND-CPA hops
                                                       |
                            Generic bound k*eps_cpa; DSDP 2*eps_cpa
```

## Sequencing and verification

1. **Blueprint figure first** (cheap iteration): edit `content.tex`, run
   `dumas2017dual/blueprint/make_blueprint.sh`, eyeball `web/images/img-0001.png`.
2. **Port the TikZ to the thesis** figure (preserving the two per-copy macros:
   `\varepsilon_{\mathrm{cpa}}` in the bound node, `\ssprove{}` in the caption),
   then build the thesis with its Makefile: `make` / `make all`, which runs
   `latexmk -pdf -interaction=nonstopmode -halt-on-error main`. Confirm it
   compiles and the `\ref` resolves.
3. **Thesis prose edits** (Part A), then `/thesis-review` bracketed by commits.
4. Keep the two figure bodies in sync except the two known per-copy macros: the
   bound node (`\varepsilon_{\mathrm{cpa}}` thesis vs `\epscpa` blueprint) and the
   caption (`\ssprove{}` thesis vs plain "SSProve" blueprint). If anything else
   drifts, note it at both `\label`s.

## Out of scope

- No Coq changes; the facade code is complete and green.
- No edits to other thesis chapters or to the blueprint node content (only the
  figure and, in the thesis, the overview prose).
- Surfacing the GitHub branch link as a visible header button (separate cosmetic
  task; the `\github`/`\home` config already points at the branch).
