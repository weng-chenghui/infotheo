# Design: TikZ derived-game figures in the concrete DSDP chapter

Date: 2026-06-09
Status: DESIGN ONLY (awaiting review). No thesis edits yet.

## Goal

Add TikZ versions of the two concrete-term derivation diagrams (the architecture
branch and the `obs_of_procs` flow, currently ASCII in
`notes/20260605-symbolic-to-game-architecture.md` and
`notes/20260608-obs-of-procs-facade-design.md`) to the concrete DSDP chapter
`chapters/dsdp.tex`, as a coda to the computational line. The figures show that
the four-game chain the chapter analyses is auto-derived from the single DSDP
program, and that `dsdp_faithful` checks the derived game equals the hand-written
fixture `gc_dsdp`.

## Decisions (from the brainstorm)

1. **Placement: `dsdp.tex` (Part V case study), both figures.** Part IV
   (`part:derived`) is abstract by design (`derived-overview.tex:117`) and already
   carries the *abstract* architecture figure `fig:derived:architecture`. The two
   diagrams use concrete DSDP terms, so by the abstract/concrete split they belong
   in the concrete chapter. This also discharges the overview's promise
   (`derived-overview.tex:118`) that Part V "carries it out on a concrete protocol
   ... the derived game checked against the hand-written one".
2. **Insertion: a coda subsection after `§subsec:dsdp:triangle`** (≈ line 753),
   before `§subsec:dsdp:bridge`. Present the hand-written chain first (as the
   chapter already does), then reveal it is derived and that `dsdp_faithful`
   checks derived = `gc_dsdp`. `dsdp_faithful` literally reads "derived =
   hand-written", which lands best once the hand-written chain is on the table.
3. **Full figures, no slimming.** Figure 1 keeps the full IT-line branch (the
   corrected `Standard → IT-line → 1/m` split). The author may shrink or
   restructure later; the deliverable is the full version.

## Correctness invariant established this session (must hold in the figures)

The computational facade does **not** use `Standard_DSDP_Interface`. The control
record `dsdp_indcpa_secrecy_problem` carries `sp_enc_scheme : AHEncType` directly
(`dsdp_game_symbolic.v:457-477`), filled by a raw section-variable `AHE`
(`dsdp_indcpa_security.v:57,77`). `Standard_DSDP_Interface` appears only in the
IT-line / concrete-proc files (`dsdp_correctness.v`, `dsdp_entropy_trace.v`,
`dsdp_pismc.v`, `dsdp_program.v`, `dsdp_interface.v`), never in
`dsdp_game_symbolic.v` / `dsdp_indcpa_security.v` / `dsdp_game_code.v` /
`dsdp_symbolic.v`. So in Figure 1:

- the concrete (`Standard`) branch flows to correctness/termination/duality and
  the information-theoretic line (`Pr_zero ≤ 1/m`), NOT to the record;
- the record takes scheme `E` as a **direct leaf input** (an `AHEncType`), not via
  the concrete interface.

## A. The coda subsection

- **File:** `chapters/dsdp.tex`, inserted between the triangle subsection
  (ends ≈ 753) and `\subsection{The interpreter--game bridge}` (≈ 755).
- **Title / label:** `\subsection{The game chain, derived from the protocol
  program}\label{subsec:dsdp:derived}`.
- **Prose (one short paragraph):**
  - the four-game chain just analysed is not hand-written: the framework of
    Part~\ref{part:derived} produces it from the single symbolic run of Alice's
    program;
  - `dsdp_faithful` machine-checks that the derived game equals the fixture
    `gc_dsdp` this section's bound was computed on (so the `2ε_cpa` bound transports
    to the derived game verbatim);
  - one honest-scope sentence: the homomorphic combines (`a₁,a₂`) and the sample
    set are derived from the program; the security-model configuration (corrupt
    party = Alice, which receptions are hops, the leak order, the two sample
    cardinalities) is declared;
  - closing clause: the *distributional* interpreter–game question is separate and
    is the subject of the next subsection (`§subsec:dsdp:bridge`), so the reader is
    not led to conflate symbolic-run derivation with the erase-translate bridge.
- **Cross-refs:** `\ref{part:derived}` / `\ref{ch:derived-overview}`,
  `\ref{fig:derived:architecture}` (the abstract original), forward
  `\ref{subsec:dsdp:bridge}`.
- **Sidenotes (`\coqin{}`):** `dsdp_faithful`, `gc_dsdp`,
  `dsdp_indcpa_secrecy_problem`, `dsdp_problem`, `dsdp_problem_secure`.

## B. Figure 1 — concrete derivation architecture

- **Label / caption:** `\label{fig:dsdp:derived-architecture}`. Caption opens
  "The concrete instance of Figure~\ref{fig:derived:architecture}…" and routes all
  code identifiers through `\coqin{}` (as `fig:dsdp:reduction` does).
- **Style:** reuse the `box`/arrow `tikzpicture` style of
  `fig:derived:architecture` so the two read as siblings; the IT vs computational
  colouring may borrow `DarkBlue`/`DarkRed` from `fig:dsdp:two-paths` if it helps.
- **Nodes (concept phrases; full IT line per decision 3):**
  - top: *Alice / Bob / Charlie programs (one protocol interface)*
  - left: *Concrete instance* → *correctness, termination, duality (preserved)* →
    *information-theoretic line* → `Pr_zero ≤ 1/m`
  - right: *Symbolic instance* → *symbolic run of Alice's program* → *derived
    combines $a_1,a_2$ + declared fields (received hops, challenge $V_2$, leak
    order, sample cardinalities)*
  - leaf into the record: *concrete AHE scheme $E$ + choice-type marshalling*
    (annotated "supplied directly, not via the concrete instance")
  - centre: *Control record* (declared fields + scheme $E$)
  - down the centre: *corrupted view* → *reified game* → *denote into \ssprove{}*
    → *\ssprove{} game* → `≤ 2\varepsilon_{\mathrm{cpa}}`
- **Concept ↔ code map (code goes in the caption, not the nodes):**
  | figure node | code identifier (caption) |
  |---|---|
  | Concrete instance | `Standard_DSDP_Interface` |
  | Symbolic instance | `Symbolic_DSDP_Interface` |
  | symbolic run of Alice's program | `palice_sym`, `obs_of_procs` |
  | Control record | `dsdp_indcpa_secrecy_problem` / `dsdp_problem` |
  | concrete AHE scheme $E$ | `sp_enc_scheme : AHEncType` |
  | reified game | `game_of_trace` → `game_code` |
  | denote into \ssprove{} | `denote_game` |
  | `≤ 2ε_cpa` | `dsdp_problem_secure` |

## C. Figure 2 — the derived trace (`obs_of_procs` flow)

- **Label / caption:** `\label{fig:dsdp:derived-trace}`. Caption: "Detail of the
  *symbolic run → corrupted view* step of
  Figure~\ref{fig:dsdp:derived-architecture}", code identifiers in `\coqin{}`.
- **Flow (concept phrases + chapter math):**
  - *Bob & Charlie first sends* → *received hop ciphertexts* `[c_2, c_3]`
  - *walk Alice's symbolic program*: each reception → a *hop*; each send → a
    *combine*; halt at the first unanswered reception (the decrypt-receive)
  - *walk output* = `[hop c_2; hop c_3; combine a_1; combine a_2]`
  - *collect sampled names* → values $V_2,V_3,U_2,U_3,R_2,R_3$; randomness
    $ra_1,ra_2$
  - *assemble* `samples ++ put(V_2) ++ walk ++ leak` → *corrupted view*
  - → *reified game* (links to Figure 1's reified-game node)
- **Concept ↔ code map (caption):** `walk_obs`, `collect_samples`,
  `AO_recv_hop`/`AO_combine`/`AO_put`/`AO_leak`, `corrupted_view`,
  `dsdp_received_hop_ciphertexts`.
- **Notation reconciliation (implementation must verify):** the symbolic trace
  samples `v2,v3,u2,u3,r2,r3`; the chapter's random variables are
  $V_i,U_i,R_i$ (`§subsec:dsdp:traces`). Figure 2 uses the chapter's RV notation;
  confirm the sampled-name set and order against `corrupted_view dsdp_problem`
  (and the `c_m`/`c_r` split) so the figure matches the code, not just the prose.

## D. Pen-and-paper rule

Figure bodies carry concept phrases and chapter math only (`c_2=\Enc(pk_b,V_2)`,
`a_1,a_2`, `2\varepsilon_{\mathrm{cpa}}`, `\View_{\text{Alice}}`). Every Rocq
identifier appears only in the caption through `\coqin{}`. Operators go through the
existing thesis macros (`\Enc`, `\Emul`, `\Epow`, `\ssprove`, `\dsdp`, `\pismc`,
`\View`, `\game{...}`). Bound macro is `\varepsilon_{\mathrm{cpa}}` (thesis side of
the established sync convention with the blueprint's `\epscpa`).

## E. Single-source / sync

The two TikZ figures must stay consistent with (a) the corrected ASCII diagrams in
`notes/20260605-…` and `notes/20260608-…`, and (b) the abstract
`fig:derived:architecture`. If any of the three changes, update the others. Record
this as a comment in the figure source.

## F. Verification

1. Build with the thesis `make` (latexmk `-pdf -halt-on-error`); both figures must
   compile with no undefined macro and no overfull `\hbox` past the kaobook text
   column (scale with `\scalebox` / `\resizebox` as `fig:dsdp:reduction` does if
   needed).
2. Confirm `\ref` to `fig:dsdp:derived-architecture`, `fig:dsdp:derived-trace`,
   `fig:derived:architecture`, `subsec:dsdp:bridge`, `part:derived` all resolve
   (no `??`).
3. Grep the figure bodies: no Rocq identifier outside a `\coqin{}` (caption only).
4. `/thesis-review` on the new subsection, bracketed by commits (before review /
   after fixes), per the dated-notes + review convention.

## Out of scope

- No change to the abstract `fig:derived:architecture` or the Part IV chapters.
- No change to the existing `dsdp.tex` figures (`fig:dsdp:two-paths`,
  `fig:dsdp:reduction`, `fig:dsdp:bridge`) or to the hand-written-chain prose.
- No new Rocq; the figures cite existing identifiers only.
