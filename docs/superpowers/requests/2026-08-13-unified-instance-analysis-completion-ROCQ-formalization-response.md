# Completion response: unified instance analysis contract

Date: 2026-08-13

Status: PARTIAL. Work package A is NO-GO because its pinned executed
theorems are mathematically false for the deterministic encoders; work
packages B and C are delivered in full. Per section 12 of the request the
status is not COMPLETE, since acceptance criteria 1, 2, 4, 5 and 6 cannot
pass.

Request: `docs/superpowers/requests/2026-08-13-unified-instance-analysis-completion-ROCQ-formalization-request.md`

## 1. Commits (section 12 item 1)

- Baseline: `51f8192661440576abd8274d051cf5e366b6ec87` (as expected by the
  request).
- Code commits, in order:
  - `e1b11396` rename KernelClosed to BaselineClassicalOnly (package C)
  - `ffebab0b` typed model-family vocabulary (package B, section 5.1)
  - `89220316` ten typed model families + facade aliases (package B, 5.2)
  - `9cceb246` dependent model slot in the manifest rows (package B, 5.1/5.3)
  - `0d925262` manifest file-legend alignment (audit fix-forward)
- Final commit: the commit adding this response document.

## 2. Verdicts (section 12 item 2)

| Package | Verdict |
|---|---|
| S5 executed endpoints (4.1) | NO-GO: the requested statement is false; compiled counterexample below |
| S5xS5 executed endpoints (4.2) | NO-GO: items 1-3 false (compiled counterexamples); items 4-7 true only by support confinement, excluded to avoid mislabeling (section 5 below) |
| Typed manifest (5) | GO: delivered, except 5.3 check 5 and the fourth mutation case, both contingent on package A and recorded unmet |
| Assumption-status correction (6) | GO: delivered in full |
| Repository contract (7) | GO with one A-contingent gap: the client reaches every new model family and the revised typed fields; there is no executed finite-word theorem family to reach |

## 3. Work package A: the obstruction (section 12 items 3, 5; request 4.1/4.2 NO-GO protocol)

### 3.1 Why the executed upper bounds are false

The deterministic plugs deal the canonical threshold encoding, and that
encoding is degenerate:

- `sum_mod_encode s = mktuple (fun i => if i == ord_max then s else ord0)`,
  i.e. `[0,0,0,0,s]` (`pgg-smc/reconstruct/pgg_sharing_framework.v:191`),
  the `ts_encode` of `s5_scheme = @sum_mod_scheme 3 4`
  (`pgg-smc/instances/s5/s5_run.v:39`).
- The interpreter-executed seat endpoint of the deterministic S5 plug is
  `s5_content_obs s (w0, i) = tnth (ts_encode s5_scheme s) (pgg_rho w0 i)`
  (`s5_exec.v:139-143`, cut-generic seat equation `s5_exec_seat_endpointE`
  at `s5_exec.v:295`), with `pgg_rho` the identity inclusion
  (`pgg_interface.v:536-545`) and `pi_starts = ord_tuple 5`
  (`s5_profile.v:37-38`).

So the executed endpoint at seat `i`, secret `s` and cut `w0` is
`if w0 i == ord_max then s else ord0`: the cut-level theorems bound the
distribution of the position `w0 i`, while `sa_seat_dist` is that position
pushed through the non-injective content map `q |-> tnth (encode s) q`.
The two observers agree only for an encoder injective per secret;
`sum_mod_encode` collapses four of five positions to `ord0`.

For S5xS5, `product_encode` (`product_threshold.v:220-227`) composes two
sum-mod encoders pile-wise with `embed_pile1` value-preserving and
`embed_pile2 = +5` (`product_threshold.v:126-148`); at secret `ord0` the
content tuple is `[0,0,0,0,0,5,5,5,5,5]`, the action is pile-preserving at
word_eval images (`word_eval_pile1`, `s5x5_mixing.v:616-635`), and
`pi_starts = ord_tuple 10` (`rigidity_s5x5_instance.v:520-521`).

### 3.2 The exact attempted types and their compiled refutations

The refutation probe (session scratchpad, twelve statements, all `Qed`,
zero `Admitted`/`Abort`/`Axiom`, 5.0 s compile, exit 0) proves for every
`R : realType`:

Executed seat distributions at the point-mass prior, for every length and
seat:

```coq
Lemma refute_s5_seat_dist (L : nat) (i : 'I_(pi_T' (mp_PI mpS)).+1) :
  @sa_seat_dist R mpS s5_exec_plug (s5_word_sample (fdist1 ord0) L) 0 i
  = fdist1 ord0.
```

with the S5xS5 analogues at seats `widen5to10 s` (value `fdist1 ord0`) and
`rshift5to10 s` (value `fdist1 (Ordinal 5)`). Full-L1 distances:
`var_dist (fdist1 v) (fdist_uniform (card_ord n.+1)) = 2 * (1 - 1/n.+1)`,
i.e. 8/5 against `fdist_uniform (card_ord 5)`, `fdist_uniform_pile1` and
`fdist_uniform_pile2`, and 9/5 against `fdist_uniform (card_ord 10)`.
Numeric gates: `sqrt 5 * (s5_alpha_R R)^+17 < 8/5` (via
`alpha = 181/200 <= 381/400 = lazy` and `s5x5_lazy_sqrt17`),
`sqrt 5 * (s5_lazy_alpha_R R)^+17 < 8/5`, and
`1 + sqrt 5 * (s5_lazy_alpha_R R)^+34 < 9/5` (via `s5x5_lazy_pow34` and
`sqrt 5 <= 3`). Hence the four negations, quoted with the exact attempted
statement under the negation:

```coq
Lemma refute_s5_requested :
  ~ (forall (secretP : R.-fdist 'I_5) (L : nat)
       (i : 'I_(pi_T' (mp_PI mpS)).+1),
       var_dist
         (@sa_seat_dist R mpS s5_exec_plug (s5_word_sample secretP L) 0 i)
         (fdist_uniform (card_ord 5))
       <= Num.sqrt 5%:R * (s5_alpha_R R) ^+ 17).   (* section 4.1 shape *)

Lemma refute_s5x5_pile1_requested :  (* section 4.2 item 1 shape *)
  ~ (forall (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
       var_dist
         (@sa_seat_dist R mpX s5x5_exec_plug (s5x5_word_sample secretP L) 0
            (widen5to10 s : 'I_(pi_T' (mp_PI mpX)).+1))
         (fdist_uniform_pile1 R)
       <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L).

Lemma refute_s5x5_pile2_requested :  (* item 2, rshift5to10 / pile2 *)
Lemma refute_s5x5_seat_requested :   (* item 3, uniform (card_ord 10) *)
```

(the last two elided here have exactly the item-2 and item-3 shapes of
request section 4.2; all four are `Qed` in the probe). Statement integrity:
every statement compiled byte-identical to the planned form; the seat
ascriptions `(widen5to10 s : 'I_(pi_T' (mp_PI mpX)).+1)` elaborate because
`pi_T' s5x5_PI` is the literal 9.

Probe assumption lists (`Print Assumptions`): each refutation carries the
boolp trio plus only the relevant group-order assumption
(`s5_group_order_eq` for S5, `s5x5_group_order_eq` for S5xS5), which enters
through the profile's plug; nothing else, and nothing from the `lra`
side-condition tactic used in the numeric gates.

Mutation checks on the probe: replacing the point-mass prior by the uniform
prior breaks the seat-distribution equality at its first step, and lowering
the numeric gate's exponent to 0 breaks the gate (the bound is vacuous at
small L, not false), confirming the probe tests what it claims.

### 3.3 Adversarial verification of the NO-GO

Two independent read-only audits were dispatched before implementation:

- A mathematical audit attacked every step (observer semantics of P_idx,
  plug content, rho, the 8/5 computation in the un-halved convention, pile
  preservation, alternative readings, vacuity regimes) and returned
  REFUTATION-CONFIRMED. Strengthenings it established: the minimal
  refuting lengths are L = 4 (S5), L = 7 (both pile bounds), L = 22
  (global seat bound); and the S5 failure is prior-independent, since
  `P(endpoint = ord0) >= 4/5 - sqrt 5 * alpha^L` for every prior (the
  uniform prior gives asymptotic distance 32/25), so no quantifier repair
  exists within the pinned deterministic plug.
- A requirements audit confirmed that no implementable reading of package
  A exists inside the request's pins (observer, ideals, constants,
  sections 3.5/3.8, the no-substitution rule of 4.2), and that the
  request's NO-GO protocol is package-scoped, prescribing delivery of
  packages B and C with A reported NO-GO.

### 3.4 Old cut-level theorems and their executed counterparts (section 12 item 3)

| Cut-level theorem (kept, unchanged) | Executed counterpart |
|---|---|
| `s5_word_endpoint_bound` (s5_models.v:295) | NO-GO, false; attempted type in 3.2 |
| `s5x5_word_pile1_bound` (s5x5_models.v:703) | NO-GO, false |
| `s5x5_word_pile2_bound` (s5x5_models.v:720) | NO-GO, false |
| `s5x5_word_seat_bound` (s5x5_models.v:738) | NO-GO, false |
| `s5x5_word_pile1_floor` (s5x5_models.v:757) | type true, NOT delivered (see below) |
| `s5x5_word_pile2_floor` (s5x5_models.v:787) | type true, NOT delivered |
| `s5x5_word_pile1_floor_gt0` (s5x5_models.v:817) | type true, NOT delivered |
| `s5x5_word_pile2_floor_gt0` (s5x5_models.v:837) | type true, NOT delivered |

Why the true floor types were not delivered: at the executed observer the
floors hold with the unconditional constant 1, for every length and every
word distribution, purely because the deterministic encoder confines a
pile seat's executed content to at most five of ten values. Nothing is
transported from the spectral floor; the `1 - sqrt 5 * lazy^L` slack and
the `17 <= L` regime would be decoration. Delivering them under section
4.3's `AnalysisBridged / NegativeTransfer` semantics ("a theorem
transporting an obstruction to the path's observer",
`pgg_analysis_status.v`) would present a support-confinement artifact as a
transported mixing limitation, contradicting section 3.2's preserved claim
that these are negative mixing results and the manifest's own row prose.
This is the same class of substitution section 4.2 forbids without
approval, so the whole package is NO-GO rather than 4/7 delivered.

### 3.5 Consequence for section 4.3

The status table of section 4.3 is conditioned on the executed theorems
existing and is NOT applied. The word and limitation rows keep their
honest cut-level statuses: `s5_row_word`, `s5x5_row_pile1_word`,
`s5x5_row_pile2_word` at `Sampled / NoModelComparison`,
`s5x5_row_pile1_limitation`, `s5x5_row_pile2_limitation` at
`Sampled / NegativeTransfer` (the transported obstruction being at the
cut-level observer, as their prose states).

## 4. Work package B as delivered (section 12 items 4, 5, 6)

### 4.1 New public types (in `pgg-smc/manifest/pgg_analysis_status.v`)

```coq
Record AnalysisModelFamily (observed : OE.ObservedExecution) :=
  MkAnalysisModelFamily {
    amf_index  : realType -> Type ;
    amf_sample : forall R : realType,
                   amf_index R
                   -> @SampleAdapter R _ (OE.oe_execution observed) ;
  }.
Arguments amf_sample {observed} f R x : rename.

Definition AnalysisModelSlot (observed : OE.ObservedExecution)
    (c : CompletionLevel) : Type :=
  match c with
  | Sampled | AnalysisBridged => AnalysisModelFamily observed
  | Algebraic | Executable | Observed => option (AnalysisModelFamily observed)
  end.
```

The row record's slot is now
`apr_model : AnalysisModelSlot apr_observed apr_completion` (field order
observed, completion, model, transfer, assumptions), so a `Sampled` or
`AnalysisBridged` row without a typed family witness is a type error, and
a family over another row's execution is a type error against the slot
type itself. The vocabulary file now imports the protocol layer it is
typed against and still imports no instance, facade or manifest file (no
cycle; its header records the new boundary).

### 4.2 Model families and facade aliases (section 5.2 table as landed)

| Family (instance constant) | Facade alias | Index at R | Row(s) |
|---|---|---|---|
| `pgl27_exact_family` | `PGL27Analysis.exact_family` | `unit` | 1 |
| `pgl27_word_family` | `PGL27Analysis.word_family` | `R.-fdist bool` | 2 |
| `five_card_uniform_family` | `FiveCardAnalysis.uniform_family` | `unit` | 3 |
| `kim_biased_family` | `FiveCardAnalysis.biased_family` | `unit` (the fixed 1/100 member) | 4 |
| `kim_centi_family` | `FiveCardAnalysis.centi_family` | `unit` | 5 |
| `s5_rand_family` | `S5Analysis.rand_family` | `unit` | 7 |
| `s5_word_family` | `S5Analysis.word_family` | `(R.-fdist 'I_5 * nat)%type` | 8 |
| `s5x5_rand_family` | `S5x5Analysis.rand_family` | `unit` | 10 |
| `s5x5_word_family` | `S5x5Analysis.word_family` | `(R.-fdist 'I_10 * nat)%type` | 11, 12, 13, 14 (one shared value) |
| `abel_word_family` | `AbelianAnalysis.word_family` | `nat` | 17 |

The abelian limitation row now carries the actual length-indexed word
model as its typed evidence; the ideal model remains the facade Models
alias `AbelianAnalysis.ideal_sample`. No underlying model was duplicated.
No other facade alias was changed.

### 4.3 The seventeen rows (section 12 item 4)

| # | Row | Family index at R | Completion | Transfer | Assumptions |
|---|---|---|---|---|---|
| 1 | `pgl27_row_exact` | `unit` | AnalysisBridged | StaticExecutedOnly | BaselineClassicalOnly |
| 2 | `pgl27_row_word` | `R.-fdist bool` | AnalysisBridged | IdealFinite | BaselineClassicalOnly |
| 3 | `five_card_row_uniform` | `unit` | AnalysisBridged | StaticExecutedOnly | BaselineClassicalOnly |
| 4 | `five_card_row_biased` | `unit` | AnalysisBridged | StaticExecutedOnly | BaselineClassicalOnly |
| 5 | `five_card_row_repeated` | `unit` | Sampled | NoModelComparison | BaselineClassicalOnly |
| 6 | `s5_row_det` | empty optional slot | Observed | NoModelComparison | AcceptsAxioms [:: AxS5GroupOrder] |
| 7 | `s5_row_rand` | `unit` | AnalysisBridged | StaticExecutedOnly | AcceptsAxioms [:: AxS5GroupOrder] |
| 8 | `s5_row_word` | `R.-fdist 'I_5 * nat` | Sampled | NoModelComparison | AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R] |
| 9 | `s5x5_row_det` | empty optional slot | Observed | NoModelComparison | AcceptsAxioms [:: AxS5x5GroupOrder] |
| 10 | `s5x5_row_rand` | `unit` | AnalysisBridged | StaticExecutedOnly | AcceptsAxioms [:: AxS5x5GroupOrder] |
| 11 | `s5x5_row_pile1_word` | `R.-fdist 'I_10 * nat` | Sampled | NoModelComparison | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 12 | `s5x5_row_pile2_word` | `R.-fdist 'I_10 * nat` | Sampled | NoModelComparison | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 13 | `s5x5_row_pile1_limitation` | `R.-fdist 'I_10 * nat` | Sampled | NegativeTransfer | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 14 | `s5x5_row_pile2_limitation` | `R.-fdist 'I_10 * nat` | Sampled | NegativeTransfer | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |
| 15 | `abel_row_recovery` | empty optional slot | Observed | NoModelComparison | BaselineClassicalOnly |
| 16 | `abel_row_identity` | empty optional slot | Observed | NoModelComparison | BaselineClassicalOnly |
| 17 | `abel_row_limitation` | `nat` | AnalysisBridged | NegativeTransfer | BaselineClassicalOnly |

Every completion, transfer and assumption status is unchanged from the
baseline; only the model evidence became typed.

### 4.4 Manifest checks and mutation guards (section 5.3)

- Check 1 (witness required at Sampled/AnalysisBridged): enforced by the
  slot type itself, and one `Timeout 60 Check (apr_model <row> : ...)` per
  row pins the mandatory or optional form.
- Check 2 (adapter over the row's own execution): the family record's
  `amf_sample` codomain is literally
  `SampleAdapter R (OE.oe_execution observed)`, and a generic spelled
  check in the manifest exhibits it for every row and family.
- Check 3 (status constructors): the 51 existing erefl pins retained
  (renamed constructor).
- Check 4 (theorems at spelled types): the 203 existing spelled-type
  checks retained unchanged.
- Check 5 (executed aliases named by word rows): UNMET, contingent on
  package A.
- Index-type pins: one application per parameterized family at its
  section 5.2 index type, plus one at `tt` for a unit family.
- Mutation guards, inline `Fail Check` in the manifest (each verified to
  fail for the intended reason; probe error messages below):
  1. `Sampled` row with `None` — rejected: "The term None has type
     option ?A while it is expected to have type AnalysisModelSlot ...
     Sampled".
  2. `Sampled` row with a `tt` stub — rejected analogously.
  3. `AnalysisBridged` row with `None` — rejected analogously.
  4. A family over the wrong execution (`s5x5_word_family` in an S5 row) —
     rejected against `AnalysisModelSlot S5Analysis.observed Sampled`,
     i.e. by the slot's dependency on the row's own observed execution.
  The request's fourth case (executed alias reverted to cut-level type) is
  UNMET, contingent on package A.
- The profile-facade checker is untouched: `profile_facade_check.sh` exits
  0 (six profiles, all represented) and all 18 cases of
  `profile_facade_check_test.py` pass.

### 4.5 Client

`pgg_analysis_client.v` keeps exactly one `Require`. It now also reaches:
`AnalysisModelFamily`, `AnalysisModelSlot`, `amf_index`, `amf_sample`,
`BaselineClassicalOnly`, `AcceptsAxioms`, `apr_model`, and all ten family
aliases across the five facades.

## 5. Work package C as delivered (section 6)

`KernelClosed` renamed to `BaselineClassicalOnly` with the required
meanings stated at the constructor:

- `BaselineClassicalOnly` = no accepted assumption beyond the repository's
  documented boolp classical trio;
- `AcceptsAxioms xs` = the trio plus exactly the named assumptions in xs.

The boolp trio was not added to `PggAxiom`. All 8 row definitions, 8 erefl
pins and 9 prose comments updated; no facade or client occurrence existed.
This response never describes a trio-dependent result as kernel-closed.

## 6. Changed files by work package (section 12 item 7)

- Package C: `pgg-smc/manifest/pgg_analysis_status.v`,
  `pgg-smc/manifest/pgg_analysis_manifest.v` (commit e1b11396).
- Package B: `pgg-smc/manifest/pgg_analysis_status.v` (ffebab0b);
  `pgg-smc/instances/s5/{s5_models,s5_analysis}.v`,
  `pgg-smc/instances/s5x5/{s5x5_models,s5x5_analysis}.v`,
  `pgg-smc/instances/pgl27/{pgl27_models,pgl27_analysis}.v`,
  `pgg-smc/instances/kim2025/{five_card_models,five_card_analysis}.v`,
  `pgg-smc/instances/abelian/{abelian_models,abelian_analysis}.v`
  (89220316); `pgg-smc/manifest/{pgg_analysis_manifest,pgg_analysis_client}.v`
  (9cceb246); `pgg-smc/manifest/pgg_analysis_manifest.v` (0d925262).
- Package A: no production file (NO-GO; refutation probes stayed in the
  session scratchpad and are quoted in 3.2, per the request's rule against
  permanent probe files).
- No new production `.v` file, so `_CoqProject` is unchanged. No paper,
  slide, bibliography or older formalization response was touched (the
  pre-existing uncommitted working-tree modification of
  `pgg-smc/paper-wadt2026/main.tex` was left strictly alone and never
  staged).

## 7. Builds, tests, audits (section 12 items 8, 9)

All builds via `opam exec --switch=/Users/cheng-huiweng/Projects/coq --
make -j1 <targets>`; Rocq 9.0.0 / OCaml 5.2.1; every one exit 0:

| Step | Targets | Wall time |
|---|---|---|
| C rename | status.vo, manifest.vo, client.vo | 29.7 s |
| B vocabulary | status.vo | 4.4 s; dependent cone (manifest.vo, client.vo + facades) 31.0 s |
| B families | five instance models .vo | 3.5-4.5 s each; five facades .vo 18.6 s |
| B manifest | manifest.vo, client.vo | 11.1 s |
| Forced client rebuild + full serial repository build | `rm client.vo; make -j1` | 10 min 17 s, exit 0 |

Warnings: no new warning class. The pre-existing classes
(notation-overridden, ambiguous coercion paths, deprecated-library-file,
notation-incompatible-prefix) now also appear when compiling
`pgg_analysis_status.v`, as a mechanical consequence of its new
protocol-layer imports; nothing else changed.

Scans: `Axiom|Parameter|Admitted|admit|Abort` over all 13 touched
production files: none found.

Audits: the pre-commit gate ran on every commit (Stage 1 green; Stage 2
remains the known S998 silent no-op), compensated by direct rocq-auditor
dispatches: e1b11396 passed (its one real finding, fourteen lines pushed
past 80 columns by the longer constructor name, was fixed in 9cceb246,
verified zero over-80 lines); 89220316 + 9cceb246 passed with one
info-severity finding (file-legend drift), fixed forward in 0d925262.
Probe compiles (scratchpad, project flags, single worker): refutation
probe 5.0 s exit 0; model-slot probe 6.8 s exit 0.

## 8. Print Assumptions (section 12 item 10)

Per new public value (families are definitions; package B adds no
theorem):

- boolp trio only (`propositional_extensionality`,
  `functional_extensionality_dep`, `constructive_indefinite_description`):
  `pgl27_exact_family`, `pgl27_word_family`, `five_card_uniform_family`,
  `kim_biased_family`, `kim_centi_family`, `abel_word_family`, and the
  rows `pgl27_row_exact`, `abel_row_limitation`.
- trio + `s5_group_order_eq`: `s5_rand_family`, `s5_word_family`, the
  facade alias `S5Analysis.word_family`, the row `s5_row_word`.
- trio + `s5x5_group_order_eq`: `s5x5_rand_family`, `s5x5_word_family`.

These match the rows' declared assumption statuses. `s5_rayleigh_Q2_R`
appears in no new value: it enters only through the (unchanged) cut-level
theorems, which is what the `AcceptsAxioms` entries of rows 8 and 11-14
record.

## 9. Boundary confirmations (section 12 items 11-13)

- Item 11: `s5_rayleigh_Q2_R` was retained, not eliminated, unfolded,
  reproven or expanded. Every theorem depending on it remains explicitly
  conditional; the refutation probe reuses only the lazy-coefficient
  numeric chain built on it.
- Item 12, strongest repository-facing claim after this work: the landed
  cut-level finite-word endpoint bounds, randomized executed secrecy
  theorems and the Abelian executed distance-one limitation stand
  unchanged; on top of them, the manifest's model evidence is now typed —
  no Sampled or AnalysisBridged path can exist without a model-family
  witness over its own observed execution — and the assumption vocabulary
  states its true boundary. Newly established knowledge: the
  interpreter-executed endpoint observer of the deterministic S5/S5xS5
  plugs has encoder-image ideals; its distance to the uniform ideals is
  bounded below by 8/5 (pile carriers) and 9/5 (global carrier) at
  point-mass priors, at every word length, which refutes any uniform-ideal
  executed upper bound for these plugs.
- Item 13, nearby claims that remain false: the section 4.1/4.2 executed
  uniform-ideal upper bounds (compiled refutations in 3.2); any privacy,
  secrecy, indistinguishability, coalition or leakage reading of any
  finite-word endpoint result, executed or cut-level; any ideal-to-finite
  transfer for S5 or S5xS5 (the full-carrier premise remains absent, and
  for group-uniform ideals unsatisfiable); and the reading of the
  would-be executed floors as transported mixing limitations (they hold
  only by encoder support confinement, with constant 1, at every length).

## 10. Acceptance ledger (section 11) and repair options

Unmet: 1, 2, 4, 5, 6 (package A), the A-contingent parts of 3 (no
executed counterparts exist; the cut-level theorems are unchanged and
distinguished), 9 (no executed theorem family to reach) and 11 (three of
four mutation classes delivered). Met: 7, 8, 10, 12, 13, 14, and the
remainder of 3, 9, 11.

Paths that would make an executed-endpoint package true, all requiring
approval because they change a pinned element:

1. Re-pin the executed ideals to the encoder images: per fixed secret the
   executed reader factors through the cut, so the data processing
   inequality gives
   `var_dist (sa_seat_dist ...) (fdistmap (content map) ideal) <= sqrt 5 *
   alpha^L` per secret, and a mixture argument extends it to any prior.
2. Randomize the deterministic encoder (the randomized plugs already deal
   uniform share tapes); an executed uniform-ideal statement then becomes
   plausible, as a new artifact.
3. Accept the floors as support-confinement limitations under a new,
   honest transfer label (not `NegativeTransfer` as currently defined).
