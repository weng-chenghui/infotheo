# dealt_key_leak + biased_key + rerouted_key: axes of Lindell's joint comparison

Date: 2026-08-02 (rev 2 after audits).  Workflow: /rocq-probe-first-spec.
Probe: `smc/security_models/.scratch/probe_dealt_key.v` (+ mutations
`probe_dealt_key_mutA/B/C.v`; extension `probe_dealt_key_ext.v`, pending).
SUPERSEDES [[20260802-masked-share-leak-refactor-design]] (the masked echo
was rejected: its leaking step is functionally unnecessary, so a peer can
dismiss it by deletion; the dealt shared key makes the step irreducible —
the functionality's delivery space demands the key, so a protocol can only
re-route it).  Predecessor instance:
[[20260802-share-leak-sfe-counterexample-design]].

## Purpose

Lindell's joint equation
`(S(x_A, f_A(x)), f(x)) ~ (view, output^pi)` asserts three orthogonal
facts: the view marginal (privacy triangle), the OUTPUT marginal (the real
delivered joint law equals the prescription — delivery-law correctness,
stateable only through nu_Y since the correctness square fixes the
aggregate alone), and the coupling (output consistency + output
independence).  The refactor replaces the verbatim-echo example with a
functionality family carrying one protocol per failing axis, each with the
other axes machine-checked to HOLD:

1. `dealt_key_leak` (the thesis example): party one deals the shared key —
   fails output independence ONLY.  Attribution (A1): this ISOLATES THE
   COUPLING COMPONENT of Lindell's randomized-functionality counterexample
   (Lindell2017 Sec. 4.2, ECCC TR17-112: a functionality prescribing an
   INDEPENDENT random sample to each party, realized by a protocol that
   outputs the SAME sample to both — that protocol fails the output
   marginal AND the coupling at once).  Our construction keeps the output
   marginal exact (`delivery_law_holds` is by construction) and fails the
   coupling alone; it is a cleaner, single-axis descendant, NOT Lindell's
   protocol re-modeled.  Never quote Lindell as "party 1 chooses r and
   sends it" — no such sentence exists in the source.
2. `biased_key`: party two samples the key with bias 3/4 and routes it
   securely — fails delivery-law correctness ONLY (and the correctness
   square cannot even state the failure).
3. Triangle axis: machine-checked by masking_verdicts' no-mask verdict
   (view = input; deterministic functionality).  Row-3 positive cells and
   the Joint refutation gain named lemmas in the probe extension (A6).
4. `rerouted_key` (NEW, from audit A2/F-19): party two deals a uniform
   key — the secure baseline; every check holds, including the positive
   joint equality `real_ideal_pair_eq`.  Promoted from mutA to a landed
   module because the thesis table's baseline row must cite identifiers
   that exist in landed code.

## Common functionality (carrier pinned; Context {R : realType})

- `F2 := 'F_2`; inputs `X3 := (F2 * F2 * F2)%type`, party i holds x_i,
  f_sum x = x_1 + x_2 + x_3; prior `mu` uniform (full support).
- Delivered outputs: party one Y_1; party two (Y_2, r); party three
  (Y_3, r) — additive shares of f_sum plus a SHARED uniform key r for the
  two honest parties (correlated delivered randomness, the commodity-server
  pattern; du2002's server-honesty assumption is the real-world echo).
- `Yfull := ((F2 * (F2 * F2)) * (F2 * F2))%type`, tuple
  `((Y1, (Y2, r)), (Y3, r))`; `proj_ya s = s.1.1`;
  `proj_yh s = (s.1.2, s.2)` — honest pair ((Y2, r), (Y3, r)).
- `functionality x := fdistmap (fun w : (F2 * F2) * F2 =>
     ((w.1.1, (w.1.2, w.2)),
      (f_sum x - w.1.1 - w.1.2, w.2))) <uniform coins>`.
- Coin naming (A9/F-13, probe names are canonical): each module's own
  execution coins are `P_Omega` (uniform in dealt_key_leak and
  rerouted_key; biased in biased_key).  Only biased_key carries a second
  object `P_Omega_unif` for the prescribed uniform coins the functionality
  draws from.  There is no `P_Omega_biased` anywhere.
- `agg s := s.1.1 + s.1.2.1 + s.2.1` (ignores both key slots);
  compat = `fdist1 (f_sum x)`.

## Landing rename map (naming audit, all accepted)

Every statement lands verbatim from the probe EXCEPT these renames; the
ledgers below already use the landing names.

| probe name | landing name | finding |
|---|---|---|
| `sim'`, `functionality_compat'`, `sim_consistent'`, `triangle_holds'`, `perfect_privacy_holds'` | unprimed (module scope already disambiguates) | F-01 BLOCKER |
| `cond2_rv` and the `_cond2`/`cond2` cascade (8 names) | `cond_key_rv`, `_cond_key` throughout | F-02 BLOCKER |
| `lindell_pair`, `lindell_pair_zero`, `lindell_pair_val` | `real_pair`, `real_pair_zero`, `real_pair_val` (Lindell attribution moves to the statement comment) | F-03 |
| `not_lindell_pair`, `not_lindell_pair_at` | `real_ideal_pair_neq`, `real_ideal_pair_neq_at` (`_neq` = `<>`, `not_` = `~`, per file convention) | F-04 |
| `delivery_law_pred_ok` / `not_delivery_law` | `delivery_law_holds` / `not_delivery_law_holds` (file's `_holds` = instance proof of the named predicate; also removes the entropy_link shadowing risk F-14) | F-05 |
| `delivery_cond` | `outputs_cond_real_law` (view_cond_sim scheme: conditional law named after what it equals) | F-06 |
| `joint_vcond_honest_recode`, `law_vcond_recode` | `joint_view_cond_honest_recode`, `law_view_cond_recode` | F-08 |
| `prob34`, `p34` | `Let key_bias_subproof`, `key_bias : {prob R}` | F-09 |
| `marg_fst_biased`, `marg_fst_unif` | `fst_marginal_biasedE`, `fst_marginal_unifE` | F-10 |
| inline `[% y2_rv, key_rv]` + `y2key` names (7) | `Definition party2_out_rv := [% y2_rv, key_rv]` (party two's delivered output); `card_preim_party2_out`, `pfwd1_party2_out`, `party2_out_lawE`, `joint_party2_out_cond`, `centropy_party2_out_cond`, `card_preim_party2_out_cond`, `pfwd1_party2_out_cond` | F-11 |
| `recode_view`, `recode_cond2` (+`_inj`) | `recode_view_cond_honest`, `recode_view_cond` (+`_inj`) | F-12 |

Also at landing: add `allow_rv := [% adv_input_rv, y1_rv]` to biased_key
with a comment that the view coincides with the allowed information
(F-15); move `unif4` beside `unif2` (F-17); port the 14 applicable
`Naming:` notes from the share_leak twins and author new ones for
`outputs_cond_real_law` and `cpr_y2_view_unif` (F-07, F-20); module names
`dealt_key_leak` / `biased_key` / `rerouted_key` stand (F-16).

## Module 1: dealt_key_leak (thesis example; fails output independence only)

- Coins `P_Omega` uniform; exec_law = tensor mu P_Omega, 64 points.
- Protocol: run delivers the shares and the key; party ONE samples r and
  deals it to both honest parties.  View `V = (x1, Y1, r)`, space
  ((F2*F2)*F2); `out_adv v = v.1.2`; readoff.
- Simulator `sim a := tensor (fdist1 a) unif2` (fresh uniform key slot).
- cond = (X, Y_1).  Given cond the honest pair has two free bits (w2, r);
  the view knows r: `H(honest | cond) = log 4`,
  `H(honest | view, cond) = log 2` (recode routes: party2_out given cond;
  y2 given (view, cond) since r sits in the view).
- By-construction note (A12): this module DEFINES `functionality x` as the
  pushforward of the run, so the predicate-form `delivery_law_holds` is
  `by []`.  Non-vacuous but definitional; the derived content is the
  conditional form `delivery_law_ok`.
- Ledger (A8: one identifier per row, landing names):

| # | identifier | claim |
|---|---|---|
| D1 | `exec_lawE` (+ counting support `card_F2`, `card_X3`, `pfwd1_cardE`, `card_preim_*`, `pfwd1_*` families) | 64-point law, every mass 64^-1, preimage counting |
| D2 | `functionality_compat` | fdistmap agg (functionality x) = fdist1 (f_sum x) |
| D3 | `sim_consistent` | simulator consistency shape |
| D4 | `view_cond_sim` | conditional view law = sim at (x, s) |
| D5 | `view_factorization` | `p_ view = `p_ allow >>= sim |
| D6 | `delivery_law_holds` | predicate form, by construction (A12) |
| D7 | `delivery_law_ok` | conditional form at every input |
| D8 | `not_cinde_honest` | ~ cinde at witness x0=(0,0,0), s=0, r=0 |
| D9 | `centropy_honest_cond` | = log 4 |
| D10 | `centropy_view_honest` | = log 2 |
| D11 | `centropy_view_honest_neq` | log 2 <> log 4 |
| D12 | `cpr_y2_view_unif` | share component marginally uniform given view |
| D13 | `not_output_det` | exec-guard refutation, witnesses differ in r |
| D14 | `not_output_determined` | curried variant |
| D15 | `run_correct` | agg (run e) = f_sum e.1 |
| D16 | `triangle_holds` | chapter triangle shape |
| D17 | `perfect_privacy_holds` | chapter perfect-privacy shape |
| D18 | `centropy_chapter_neq` | chapter-conditioner entropy gap (carries the every-simulator claim via perfect_privacy_centropyP; A3) |
| D19 | `real_pair`, `ideal_pair` defs + `real_pair_zero`, `ideal_pair_val` | the two joint laws and their values at (v0, y0): 0 vs 16^-1 |
| D20 | `real_ideal_pair_neq_at` | pointwise difference at positive ideal mass |
| D21 | `real_ideal_pair_neq` | the pair laws differ at x0 |
| D22 | axioms | boolp trio on every target (VERIFIED by both audits) |

## Module 2: biased_key (fails delivery-law correctness only)

- Coins `P_Omega := tensor (tensor unif2 unif2) biased2` with
  `biased2 := (fdist1 0 <| key_bias |> fdist1 1)` (mass 3/4 at 0; conv
  construction as biased3 in this file); prescribed coins `P_Omega_unif`.
- Protocol: party two samples the biased key and sends it to party three
  (secure routing).  View `V = (x1, Y1)` ONLY, space (F2*F2);
  simulator `sim a := fdist1 a` (the view IS the allowed information;
  `allow_rv` added at landing, F-15).
- Positive certificates: `triangle_holds` (Dirac simulator; degenerate
  route noted in the thesis caption, A13), `sim_consistent`,
  `functionality_compat` (compat is about the PRESCRIPTION, which draws
  from P_Omega_unif), `cinde_honest_holds` + `output_independent_holds`
  (the view is a function of (X, Y_1)), `run_correct` (the correctness
  square holds at every execution regardless of the key's bias).
- Negative certificates: `not_delivery_law_ok` (conditional form; premise
  discharged by `pfwd1_input_neq0`) and `not_delivery_law_holds`
  (predicate form).  Witness values (A7, corrected): at x0, y0 the real
  law gives `4^-1 * (3/4) = 3/16` and the prescription `8^-1 = 1/8`.
  This is the axis only nu_Y can state: the correctness square holds
  while the delivered joint law is wrong.
- Ledger (A8):

| # | identifier | claim |
|---|---|---|
| B1 | `biased2` + `biased2_0`, `biased2_1`, `key_bias` | the biased coin, masses 3/4 and 1/4 |
| B2 | `exec_lawE` (+ `P_OmegaE`, `P_Omega_unifE`) | e ↦ 32^-1 * biased2 e.2.2 |
| B3 | `run_correct` | correctness square |
| B4 | `functionality_compat` | aggregate compat with the prescription |
| B5 | `sim_consistent` | Dirac simulator consistency |
| B6 | `cinde_honest_holds` | output independence HOLDS |
| B7 | `output_independent_holds` | entropy_link predicate form |
| B8 | `fst_marginal_biasedE`, `fst_marginal_unifE` | first-share marginal uniform under both coin laws |
| B9 | `triangle_holds` | view marginal ideal |
| B10 | `perfect_privacy_holds` | chapter shape |
| B11 | `pfwd1_input_neq0` | full-support premise for the conditional refutation |
| B12 | `outputs_cond_real_law` | Pr[outputs = y | input = x] = real_law x y |
| B13 | `not_delivery_law_ok` | conditional-form refutation at positive mass |
| B14 | `not_delivery_law_holds` | predicate-form refutation |
| B15 | `real_pair_val`, `ideal_pair_val` | 3/16 vs 1/8 at (v0, y0) |
| B16 | `real_ideal_pair_neq_at` | pointwise difference |
| B17 | `real_ideal_pair_neq` | pair laws differ at x0 (the named simulator) |
| B18 | `not_exists_ideal_pair` (NEW, probe extension; A3) | ~ (exists S, real_pair x0 = ideal_pair_of S x0) — for ANY simulator the ideal pair's output marginal is `functionality x0`, the real pair's is `real_law x0`, and `not_delivery_law_holds` separates them |
| B19 | axioms | boolp trio |

`ideal_pair_of` (probe extension): S-parameterized form
`ideal_pair_of S x := functionality x >>= (fun y =>
(S (proj_xa x, proj_ya y)) `x (fdist1 y))`, with
`ideal_pair := ideal_pair_of sim`.  Reason (A3): row 2's Joint cell
asserts rejection for EVERY simulator, and the row-1 route through
`perfect_privacy_centropyP` is unavailable here because that lemma
requires `delivery_law_ok` — exactly what this module refutes.

## Module 3: rerouted_key (NEW; the secure baseline row)

Construction = mutA's (view drops r: `V = (x1, Y1)`, party two deals the
uniform key to party three), promoted to a landed module (F-19/A2: the
baseline row of the thesis table must cite landed identifiers; mutA stays
in .scratch/ as the mutation record).  Ledger (probe extension):

| # | identifier | claim |
|---|---|---|
| R1 | carrier + `exec_lawE` | uniform 64-point law (shared with module 1) |
| R2 | `functionality_compat` | Square column |
| R3 | `sim_consistent` | Dirac simulator |
| R4 | `run_correct` | correctness square at every execution |
| R5 | `delivery_law_ok` (+ `delivery_law_holds`) | Delivery column |
| R6 | `cinde_honest_holds` | Independence column (from mutA) |
| R7 | `output_independent_holds` | entropy_link predicate form |
| R8 | `triangle_holds` | Triangle column |
| R9 | `perfect_privacy_holds` | chapter shape |
| R10 | `real_ideal_pair_eq` | POSITIVE Joint cell: `real_pair x = ideal_pair x` for every x (A2: fdistmap_comp + eq_fdistmap route) |
| R11 | axioms | boolp trio |

## Row 3 supplements (masking_verdicts; probe extension)

- Triangle "fails" witness PINNED (A6): `masking_verdicts.insecurity_no_mask`
  — already the every-simulator form `~ (exists S, perfect_privacy ...)`.
- NEW positive cells: `delivery_law_ok` and an output-independence
  positive at the trivial output `'I_1` (names follow the module's local
  vocabulary; deviations recorded at probe time).
- NEW Joint refutation `not_exists_ideal_pair`: the output space is a
  singleton, so the pair equality collapses to the view-marginal equality
  and the refutation reduces to `insecurity_no_mask`.  Decision (A6):
  formalize directly rather than downgrade the "Joint witnesses are
  direct" rule.

## The joint pair, formalized (footnotes for the Joint column)

Every "fails" cell of the thesis table carries a machine-checked witness.
Both flawed modules define the two joint laws and refute their equality
pointwise; the baseline module proves the equality.

- `real_pair x := fdistmap (fun w => (view_at (x, w), run (x, w)))
  P_Omega` — the REAL joint law of (view, delivered outputs) at x (with
  the module's own exec coins); Lindell attribution lives in the
  statement comment (F-03);
- `ideal_pair x := functionality x >>= (fun y =>
  (sim (proj_xa x, proj_ya y)) `x (fdist1 y))` — the simulated view
  coupled with the SAME functionality draw;
- D20/D21 `real_ideal_pair_neq_at` / `real_ideal_pair_neq`
  (dealt_key_leak): the real pair carries the dealt key in BOTH
  components, the ideal pair gives mismatched keys positive mass
  (`real_pair_zero` = 0 vs `ideal_pair_val` = 16^-1 — refutation at
  positive ideal mass, vacuity-checked by the soundness audit);
- B16/B17/B18 (biased_key): pointwise 3/16 vs 1/8, plus the
  every-simulator form through the output marginal;
- R10 `real_ideal_pair_eq` (rerouted_key): the positive equality.

Quantifier layering in the thesis footnotes (A3): row 1's every-simulator
claim is carried by `centropy_chapter_neq` (via perfect_privacy_centropyP,
whose `delivery_law_ok` hypothesis module 1 satisfies), with
`real_ideal_pair_neq` as the direct pointwise instance; row 2 and row 3
carry `not_exists_ideal_pair` directly.

## Mutations (each must FAIL; falsity/positivity certificates kept)

- mutA (module 1): re-route the key — view drops r (V = (x1, Y1)).
  not_cinde_honest must FAIL, and the companion file PROVES the positive
  cinde — the domain-of-validity certificate for "who samples matters".
  Promoted content lands as Module rerouted_key; the scratch file stays
  as the mutation record.
- mutB (module 1): agg reads a key slot — functionality_compat fails
  (certificate `not_functionality_compat` at 1/2 vs 1).
- mutC (module 2): key sampled uniformly — not_delivery_law_ok must fail
  (delivery-law correctness is restored), and the row collapses to the
  secure protocol.
- Cross-mutation for R10: `real_ideal_pair_eq` fails at the dealt
  routing — witnessed by module 1's `real_ideal_pair_neq` itself; no
  separate mutation file needed.

## Soundness invariants

- No new axiom; boolp trio everywhere (36 Print Assumptions targets
  verified by the soundness audit).
- SFE scope: aggregate deterministic (agg ignores the key slots);
  delivered outputs randomized as def:smc:functionality allows; the shared
  key is correlated delivered randomness, precedented by the commodity
  server's outputs in the correctness walkthrough.
- Necessity (A10, corrected): the key component is a modelling consequence
  of the functionality's delivery space, machine-checked through
  `functionality_compat` + `delivery_law_ok` AT that space; mutA/R6
  certify re-routability alone.  There is no delete-the-Deal-step
  mutation, because deleting the step changes the functionality's type.
- Orthogonality honesty: each flawed row's PASSING axes are machine-checked
  positively, not asserted; rows 2 and 4 route the view securely, so
  their triangle holds with the Dirac simulator (A13 — acknowledged in
  the thesis caption, not presented as a substantive privacy proof).
- English-statement checks: "the share component stays marginally uniform"
  = cpr_y2_view_unif; "the dealer knows the key it dealt" = the view
  containing r verbatim; log 4 vs log 2 = the two centropy lemmas.
- Entropy readings are NOT conflated (A11): log 4 / log 2 are at
  conditioner (X, Y_1) with variable honest_rv; `centropy_chapter_neq` is
  at the chapter conditioner (x_1, Y_1) with variable (x_h, Y_h) and is
  derived from `not_cinde_honest`, not from the two log values.  The
  thesis presents them as two readings, never one as an instance of the
  other.
- Quantifiers: existence witnesses for pointwise refutations; the Joint
  column's every-simulator claims carried exactly as the quantifier
  layering above states.

## Module policy (decided)

ADD `Module dealt_key_leak`, `Module biased_key`, `Module rerouted_key`
to examples_f3.v; EXTEND `Module masking_verdicts` with the row-3
supplement lemmas; KEEP `share_leak` and `coin_leak` (kept-variants
precedent; the thesis cites only the new modules and masking_verdicts).
Header table gains one row per new module (F-18; landing agent enforces
the file's exact 80-column format: name right-aligned to col 25, `==` at
27-28, description from col 30):

- `dealt_key_leak` == adversary deals the honest parties' shared key;
  only output independence fails
- `biased_key` == honest dealer, biased key; only delivery-law
  correctness fails
- `rerouted_key` == honest dealer, uniform key; every check holds (the
  table's secure baseline)

File intro paragraph gains two sentences naming the three-axes family and
its role as the thesis table's witness set.

## Thesis touchpoints (after the modules land)

security-models.tex, ex:smc:share-leak replaced by the dealt-key example:
- PRESERVED from 95ee955: the example opens by defining the parties'
  inputs and the displayed ideal function f before use (SPP pattern), and
  states the ideal=real layering.  ADAPTED: the excess-step sentence is
  REVERSED — the functionality itself demands the key; only its routing is
  the protocol's choice ("computing f and delivering the key are both the
  functionality's demands; the routing of the key is the protocol's").
- Attribution (A1, corrected): the example isolates the coupling
  component of Lindell's counterexample; suggested sentence: "the example
  isolates the coupling failure behind Lindell's randomized-functionality
  counterexample~\cite[\S4.2]{Lindell2017}, whose protocol fails the
  output law and the coupling at once; here the delivered law is exact
  and only the coupling fails."  The commodity-server tie-in sentence
  cites the correctness walkthrough (and du2002's server-honesty
  assumption where the chapter already cites it).
- Steps in the trace format: \emph{Share.} (traces [x1,Y1], [x2,Y2],
  [x3,Y3]); \emph{Deal.} party one samples r, sends to both honest
  parties (traces [x1,Y1,r], [x2,Y2,r], [x3,Y3,r]); \emph{Output.}
  Secure re-routing (party two samples, sends to party three) shown as
  the one-line foil, now citable as \coqin{rerouted_key}.
- Entropy display: H(Y_h | X, Y_A) = log 4 vs H(Y_h | V, X, Y_A) = log 2,
  presented as the (X, Y_A) reading; the chapter proposition's
  \coqin{centropy_chapter_neq} is the (x_1, Y_1) reading (A11 — two
  readings, stated as such in the sidenote).
- THE CHECKS TABLE (user requirements 2026-08-02; placement decided):
  PLACEMENT: immediately AFTER the three-condition itemize list and
  BEFORE "The execution context makes these statements precise" — the
  list names the conditions, the table shows each is non-redundant, then
  the formal development delivers them.  Row one is the example the
  reader has just finished, so the table sits adjacent to it.
  INTRO PARAGRAPH (A4, rewritten: names the four TABLE axes, and says
  explicitly why output consistency has no row):

    "Lindell's equation compares one pair of joint distributions.
    Table~\ref{tab:smc:joint-checks} separates its content along the
    checks this section develops: the correctness square, the
    view-marginal triangle, delivery-law correctness, and output
    independence.  Each flawed row passes every check except its own
    axis, so no condition in the list above is redundant: dropping one
    admits a protocol that the joint comparison rejects.  The first two
    rows agree with the secure baseline on the correctness square and
    the triangle; the distance between those classical checks and
    Lindell's equation is exactly the two output-side conditions.
    Output consistency has no row of its own: it disciplines the
    simulator rather than the protocol, and the read-off comparison
    (\cref{def:smc:output-consistency}) already forces it for every
    simulator in the table."

  TABLE: four rows (P1 dealt key = the example; P2 biased key; P3 the
  unmasked view, witnessed by masking_verdicts; P4 = rerouted_key, the
  secure baseline), five check columns with SHORT heads (refs live in
  the caption; kaobook width discipline):

    \begin{table}[htbp]
      \centering
      \caption{One protocol per axis of Lindell's joint comparison.
        Rows one, two and four share the key-delivering functionality of
        \cref{ex:smc:share-leak}; row three is the masking instance of
        Figure~\ref{fig:smc:privacy-instance} over $\F_3$, whose output
        is trivial (A5).  Every simulator in the table is
        output-consistent; rows two and four route the view securely, so
        their triangle holds with the Dirac simulator (A13).  The column
        heads expand to Eq.~\eqref{eq:smc:correctness},
        \cref{def:smc:perfect-privacy}, \cref{def:smc:delivery-law},
        \cref{def:smc:output-independence}, and Lindell's comparison
        (\cref{prop:smc:entropy-characterization}).}
      \label{tab:smc:joint-checks}
      \begin{tabular}{@{}lccccc@{}}
      \toprule
      Protocol & Square & Triangle & Delivery & Independence & Joint \\
      \midrule
      Party one deals the key        & holds & holds & holds & fails & fails \\
      Party two samples a biased key & holds & holds & fails & holds & fails \\
      View shows an input (no mask)  & holds & fails & holds & holds & fails \\
      Party two deals a uniform key  & holds & holds & holds & holds & holds \\
      \bottomrule
      \end{tabular}
    \end{table}

  FOOTNOTED FAILS CELLS (user requirement 2026-08-02; landing names):
  every "fails" cell carries a superscript letter expanded below the
  table (plain $^{a}$ in the cell + a caption-footer legend line; no
  extra package), each naming the Rocq witness:
  - (row 1, Independence): \coqin{dealt_key_leak.not_cinde_honest}
  - (row 1, Joint): \coqin{dealt_key_leak.real_ideal_pair_neq} (direct
    pointwise refutation); \coqin{centropy_chapter_neq} carries the
    every-simulator claim (A3)
  - (row 2, Delivery): \coqin{biased_key.not_delivery_law_ok}
  - (row 2, Joint): \coqin{biased_key.not_exists_ideal_pair} (every
    simulator, via the output marginal); \coqin{real_ideal_pair_neq}
    the named-simulator pointwise instance
  - (row 3, Triangle): \coqin{masking_verdicts.insecurity_no_mask}
    (already the every-simulator form)
  - (row 3, Joint): \coqin{masking_verdicts.not_exists_ideal_pair}
    (singleton output: the pair collapses to the view marginal)
  Passing cells cited collectively in one sidenote:
  dealt_key_leak.{triangle_holds, delivery_law_ok, functionality_compat};
  biased_key.{triangle_holds, cinde_honest_holds, functionality_compat,
  run_correct}; masking_verdicts.{delivery_law_ok + the independence
  positive}; rerouted_key.{functionality_compat, triangle_holds,
  delivery_law_ok, cinde_honest_holds, real_ideal_pair_eq} for the
  baseline row — all landed identifiers, none from .scratch/ (F-19).
- The hygiene remark (0db2939 lineage) survives in adapted form: masking
  discussion stays as prose; the pad-undelivered/secure-routing validity
  statement now points at \coqin{rerouted_key} (landed), not at mutA.
- Minimality sentence replaced by the routing sentence (three parties are
  needed for a key SHARED between honest parties; with one honest party
  there is no second recipient).
- eps-bound paragraph wording updated (the dealt key, one bit of honest
  output known to the view).

## Plan (one atomic task per commit)

1. PROBE EXTENSION (rocq-prover, model Opus; .scratch/probe_dealt_key_ext.v):
   B18 `ideal_pair_of` + `not_exists_ideal_pair`; the rerouted_key
   positive set R1-R10 (building on mutA; A2's route for R10:
   fdistmap_comp + eq_fdistmap); the masking_verdicts row-3 supplements
   (positives + `not_exists_ideal_pair`).  Zero Admitted/Abort/Axiom;
   Print Assumptions per target; compile against the local switch.
2. Land the three modules + masking_verdicts extension in examples_f3.v
   (statements verbatim from the probes MODULO the rename map above;
   Naming: notes ported per F-07; header rows + intro sentences per
   F-18); compile; golf (bodies only); axioms; gate UNBYPASSED; commit.
3. Thesis example rewrite + checks table + intro paragraph; build with
   the project Makefile; commit (blob-staged against in-flight user
   edits).

## Deviations / findings folded back

Naming audit (NO-GO -> resolved): F-01..F-15 accepted as the rename map
above; F-16 module names kept; F-17 placement; F-18 header rows drafted;
F-19 resolved by promoting rerouted_key to a landed module; F-20 keep
with a new Naming: note.

Soundness audit (NO-GO -> resolved): A1 attribution corrected (fabricated
quotation deleted; "isolates the coupling component" framing); A2
baseline positives + R10 added; A3 quantifier layering + B18/row-3
`not_exists_ideal_pair`; A4 intro paragraph rewritten around the four
table axes with the consistency-has-no-row sentence; A5 caption
corrected; A6 row-3 witnesses formalized (insecurity_no_mask pinned);
A7 3/16 vs 1/8; A8 ledgers renumbered one identifier per row; A9 probe
coin names adopted; A10 necessity wording corrected; A11 entropy
readings separated; A12 by-construction note; A13 Dirac-simulator
acknowledgment in the caption.
