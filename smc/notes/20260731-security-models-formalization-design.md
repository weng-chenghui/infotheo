# Security-models chapter formalization: design spec

Date: 2026-07-31
Branch base: `itp2026-dumas2017dual`
Status: DRAFT under probe-first-spec; core probes P1-P5 all GO; probes D1
(entropy miniature) and D4+D2 ('F_3 examples, log API) in flight; adversarial
audits pending.

## 1. Goal and scope

Give every rendered, numbered definition, proposition, and example of
`phd-thesis/chapters/security-models.tex` (plus its main displayed equations) a
corresponding Rocq artifact under `smc/security_models/`, and extend the thesis
repo's structure map
(`docs/notes/20260731-2237-security-models-pre-game-structure-map.md`) to the
whole chapter with a per-block "Rocq artifact" column.

Boundary decisions (user-confirmed in the brainstorming session):

- IN: the Iwamoto direction of `eq:smc:entropy` (perfect privacy implies the
  conditional-entropy equality), scoped as decided in §6.
- IN: the T-relativized unpredictability-entropy composition display.
- OUT: the hidden `\iffalse` sufficiency subsection (not rendered).
- OUT: standalone threat-model formalization. Adversary classes stay abstract:
  an arbitrary `T : {set tester}` parameter, per the settled reduction-form
  convention (`dumas2017dual/notes/20260728-reduction-form-security-statements.md`);
  no concrete "efficient" class is ever defined (the rejected design is
  recorded in `20260728-resource-bounded-adversary-class.md`).
- Examples: the 'F_3 matrix examples are self-contained; the SPP instance
  bridges to `du2002/spp_simulator.v`, reusing its Qed lemmas (no rebuild, no
  edits to du2002).

Not SSProve: no packages, no state, no code interpretation. Everything is
`R.-fdist` over finTypes on the local infotheo fork.

## 2. Architecture: two layers

The chapter itself is two-layered: the observation-diagram section uses
per-party structure; the simulation and game sections manipulate only the
spaces `E`, `B_A`, `X_A x Y_A` and arrows between them. The formalization
mirrors this:

- privacy kernel (abstract spaces + maps): carries all simulation/game-side
  definitions and propositions.
- party structure (n-party dependent families): carries the
  observation-diagram section and instantiates the kernel
  (`party_to_kernel`).
- SPP enters at the kernel level (its nested-tuple view space is just a
  kernel `Bv`), avoiding any dffun isomorphism layer.

Files (each listed in `_CoqProject`; `spp_bridge.v` after the du2002 block):

| file | content |
|---|---|
| `smc/security_models/finstoch.v` | stochastic maps, dirac, composition, laws, tensor + the four transport helpers |
| `smc/security_models/statdist.v` | TV distance, testers, max-advantage, `class_adv` |
| `smc/security_models/privacy_kernel.v` | draw, view law, allow, simulator, privacy triangle, insecurity, game equivalences, hybrid bound |
| `smc/security_models/party_structure.v` | n-party diagram, view, read-off square, revelation, `party_to_kernel` |
| `smc/security_models/entropy_link.v` | Iwamoto direction (scope per §6) |
| `smc/security_models/unpredictability.v` | T-relative H_unp composition |
| `smc/security_models/examples_f3.v` | 'F_3 matrix examples + three-verdict toy |
| `smc/security_models/spp_bridge.v` | SPP corrupted-Bob instance via `cond_law_to_bind` |

Conventions: snake_case identifiers; ASCII notation only; `R : realType`
section variable; `Local Open Scope fdist_scope` (load-bearing, probe P3
finding 1); `Import Order.Theory` last so bigmax lemmas resolve to the
order-theoretic versions (probe P2 finding 4).

## 3. Chapter-item mapping

### finstoch.v (probe P1, all GO)

| chapter | artifact |
|---|---|
| def:smc:stochastic-map | `stoch A B := A -> R.-fdist B`; matrix reading via `stoch_compE` |
| def:smc:dirac | `dirac g := fun a => fdist1 (g a)` |
| def:smc:finstoch (composition) | `stoch_comp g f := fun a => f a >>= g` |
| prop:smc:finstoch-laws | `stoch_compA`, `stoch_comp_idl`, `stoch_comp_idr` |
| prop:smc:transport-commutes | `dirac_comp`, plus identity law above |
| def:smc:transport | no standalone object: transport is arrow-wise `dirac`; its content is `dirac_comp` + the identity law (recorded as such in the map) |
| def:smc:tensor | `tensor p q := (p `x q)%fdist`; `tensorE` by `fdist_prodE` |
| (idiom bridge) | `stoch_comp_dirac_fdistmap`: deterministic post-composition is `fdistmap` |
| (supports) | `eq_fdistmap`, `fdistmap_cst`, `fdistmap_cst_eq`, `tensor_fdist1` (probe P1 finding 2; no funext needed) |

Probe fact folded in: `` `x `` is `` `X (fun _ => q) `` — the kernel product
`` `X `` is primitive (`fdist.v:1071`); `fdist_prodE ab = P ab.1 * W ab.1 ab.2`.

### statdist.v (probe P2, 12/12 GO)

| chapter | artifact |
|---|---|
| def:smc:tv-distance | `statdist p q := 2%:R^-1 * \sum_b `\|p b - q b\|`; `statdist_ge0/sym/triangle`; max-over-events form optional (see ledger R-ev) |
| distinguisher (game section) | `tester := {ffun B -> bool}`; `accept D p := Pr p [set b \| D b]`; `adv D p q` |
| prop:smc:max-advantage | `statdist_test_le`, `statdist_test_max` (optimal tester `[ffun b => q b < p b]`) |
| Delta_T (composition section) | `class_adv (T : {set tester}) p q := \big[Num.max/0]_(D in T) adv D p q` |
| prop:smc:composition | `class_adv_ge0/sym/xx/triangle/sub`; `class_adv_all` ties to `statdist` |
| (separation, for testP) | `statdist_eq0 : (statdist p q == 0) = (p == q)` |

Port note: the deleted `{distr}` development (`git show
2bbc1714:smc/ssprove_ext_statdist.v`, copy at
`.scratch/reference_statdist_distr_source.txt`) collapses: 15 pointwise
lemmas become 3 local helpers (`sum_diff_complement`, `sum_diff_le`,
`statdist_pos_part`); all summability obligations vanish.

### privacy_kernel.v (probes P1 + P5, all GO)

Section parameters: finTypes `X Yfull Y Xa Ya Bv Omega`; `f : X -> Y`;
`agg : Yfull -> Y`; `proj_xa`; `proj_ya`; `F : X -> R.-fdist Yfull` with
`F_compat : forall x, fdistmap agg (F x) = fdist1 (f x)`;
`P_Omega : R.-fdist Omega`; `view_at : X * Omega -> Bv`;
`run : X * Omega -> Yfull` with `run_correct : forall e, agg (run e) = f e.1`.

| chapter | artifact |
|---|---|
| def:smc:ancilla-distribution | the `P_Omega` parameter |
| def:smc:ancilla-draw | `draw x := tensor (fdist1 x) P_Omega` |
| def:smc:law / def:smc:view-rv | `fdistmap` as law; `view_at (x, .)`; connected by `view_lawE` |
| def:smc:view-law | `view_law x := fdistmap view_at (draw x)`; unpacking `view_lawE` |
| def:smc:functionality | the `F` parameter + `F_compat` (deterministic case: `F = dirac F0`) |
| def:smc:allowed-info | `allow x := fdistmap (fun xy => (proj_xa xy.1, proj_ya xy.2)) (tensor (fdist1 x) (F x))`; `allowE : allow x = tensor (fdist1 (proj_xa x)) (f_a x)`; `f_a x := fdistmap proj_ya (F x)` |
| def:smc:sim / def:smc:simulator | `simulator := Xa * Ya -> R.-fdist Bv` (one definition, two chapter readings) |
| def:smc:factors-through | `factors_through h g := exists s, h =1 stoch_comp s g` |
| def:smc:perfect-privacy | `perfect_privacy S := view_law =1 sim_view S`, `sim_view S x := allow x >>= S` (single-S quantifier order preserved by `=1`) |
| eq:smc:simulation / def:smc:epsilon-privacy | `eps_privacy S eps := forall x, statdist (view_law x) (sim_view S x) <= eps` |
| prop:smc:insecurity | `insecurity : allow x = allow x' -> view_law x != view_law x' -> ~ (exists S, perfect_privacy S)` |
| prop:smc:worlds-compute-f | `real_route_f` (via `run_correct`), `ideal_route_f` (via `F_compat`) |
| eq:smc:test-advantage | `test_adv D S := \big[Num.max/0]_x adv D (view_law x) (sim_view S x)` |
| perfect/eps <-> forall D | `perfect_privacy_testP`, `eps_privacy_testP` (P5: consumed supports recorded; no extra hypotheses needed) |
| def:smc:hybrid | `hybrid_bound` (triangle-inequality instance; the hybrid law itself is instance-level data) |

### party_structure.v (probe P3, all GO)

Parameters: `n`; families `Xi Si Yi : 'I_n -> finType`; `Y`; `Omega`,
`P_Omega`; `trace_map : exec_ctx -> s_all`; per-party `out_i`, `in_i`;
`agg`; `f`; `correctness`; `trace_records_inputs`; adversary
`A : {set 'I_n}`.

| chapter | artifact |
|---|---|
| E, joint trace, delivery space | `exec_ctx := (x_all * Omega)%type`, `s_all`, `y_all` as `{dffun forall i, _ i}` |
| B_A, proj_A, def:smc:view | `view_space := {dffun forall i : {i \| i \in A}, Si (val i)}`, `proj_adv`, `view := proj_adv \o trace_map` |
| out_A, eq:smc:readoff-square | `out_adv`; `readoff_square` by `ffunP` ("commutes by construction") |
| in_A + glossary identity | `in_adv`; `in_adv_records` |
| eq:smc:reveal-criterion | `reveals_output p := forall y, p (proj_y_adv y) = agg y` |
| revelation chain | `reveal_chain` |
| kernel instantiation | `party_to_kernel` (probe: elaborates; record-projection form `r.(field)` required) |

Probe facts folded in: the sig-indexed dffun finType is canonical
(`fintype.v:1509`, `[Finite of {x | P x} by <:]`); the extensionality lemma
is `ffunP` (there is no `dffunP`).

### entropy_link.v (probe D1 in flight; scope decision §6)

Kernel extended (sub-section) with honest-side projections `Xh Yh`,
`proj_xh`, `proj_yh`, input prior `mu : R.-fdist X`, joint prior
`d := mu `x P_Omega`, RVs `view_rv`, `input_rv`, `allow_rv` (spelling
`{RV d -> _}` required for `pfwd1` inference, probe P4 finding 4).
Target (deterministic functionality):

- `triangle_cinde : d |= view_rv _|_ input_rv | allow_rv` from the per-input
  triangle;
- `cinde_centropy_eq :` H(honest | view, allowed) = H(honest | allowed) in the
  repo's centropy notation.

Missing library lemmas found by D1 become planned implementation work.

### unpredictability.v (probe D2 in flight)

T-relative form only. `sec : X -> Sec`; `predictor := {ffun Bv -> Sec}`;
`pred_success` under the joint prior; `ideal_guess` from allowed information;
composition lemma `pred_success <= ideal_guess + e_game + e_sim` via
`class_adv` triangle + membership of induced testers in `T`; then
`unp_entropy_ge` by log monotonicity (log identifier pinned by D2).

### examples_f3.v (probe D4 in flight)

| chapter | artifact |
|---|---|
| ex:smc:dirac-matrix | `dirac_shiftE` on 'F_3 |
| ex:smc:mask-matrix | `mask_chan`; `mask_chan_uniform_hides`; biased (1/2,1/4,1/4) `biased3`; `mask_chan_biased_leaks` |
| ex:smc:ancilla-matrix | `draw_add_mask : fdistmap add (tensor (fdist1 x) m) = mask_chan m x` |
| tab:smc:privacy-laws / fig:smc:privacy-instance | three-verdict toy: one masking kernel instance; uniform => `perfect_privacy`; biased => `eps_privacy` with eps = 6^-1 (D4c pins the value); no mask => `insecurity` witness |

### spp_bridge.v (probe P4 GO)

Bridge point: `bob_view_cond_sim_xy` (conditioning on Bob's own `(x2, y2)`,
i.e. exactly the allowed information) + `cond_law_to_bind` (probe P4, Qed, 6
lines) give the RV-form factorization

    `p_ BobView = `p_ [% x2, y2] >>= (fun '(b, y) => bob_simulator b y)

as the machine-checked nu = Sim o allow (marginal form); the per-input form is
`bob_view_cond_sim` itself. Both are recorded in the map. No du2002 file is
edited; scratch is never imported (`.scratch` has no logical name — permanent
files restate probe code verbatim).

## 4. Claim ledger

Library objects:

| # | claim | status | evidence |
|---|---|---|---|
| L1 | fdistbind + fdist1bind/fdistbind1/fdistbindA | GO | fdist.v:317-363; used in P1 |
| L2 | fdistmap + _comp/_1/E | GO | fdist.v:377-402; P1 |
| L3 | fdist1 + fdist1E/fdist1xx | GO | P1 |
| L4 | `` `x `` binary product | GO (resolved) | `` `x `` = `` `X `` at constant kernel, fdist.v:1071; `fdist_prodE`; P1 finding 1 |
| L5 | `Pr E = \sum_(a in E) P a` | GO | proba.v:217; P2 |
| L6 | fdist_ext | GO | fdist.v:234; P1/P2 |
| L8 | tester finType + bigmax API | GO | P2: bigmax_le/bigmax_sup/sub_bigmax/bigmax_ge_id + bigmax_eq_id/le_bigmax (P5); Import Order.Theory order load-bearing |
| L9 | sig-indexed dffun finType + extensionality | GO | canonical via fintype.v:1509; ffunP (no dffunP); P3 |
| L10 | lra at realType with these imports | GO | P2 finding 1 (all_ssreflect deprecation warning only) |
| L11 | cpr_eqE / pfwd1_domin_RV1 / fst_RV2 conditional API | GO | proba.v:2061/1127/932; P4 |

Proof shapes: S1-S13 all GO (P1: S1-S6; P2: S7-S9; P3: S10-S11; P4: S12 with
the `{RV P -> B}` spelling correction; P5: S13, no added hypotheses).
Pending: D1 (CI + centropy route), D2 (log API), D4 (biased fdist
construction, eps = 6^-1 computation).

Probe files (kept, never imported):
`smc/security_models/.scratch/probe_finstoch_kernel.v`,
`probe_statdist_maxadv.v`, `probe_party_dffun.v`, `probe_spp_bridge_shape.v`,
`probe_kernel_decomposition.v`, `probe_examples_f3.v`,
`probe_entropy_link_mini.v`, plus mutation copies `*_mutN.v` and the port
reference `reference_statdist_distr_source.txt`.

Notable probe findings already folded in:

- P2 finding 7: for mass-1 laws the wrong-side optimal tester also attains the
  max; statement-level mutation would not catch it (proof-level mutation is
  the standard here).
- P4 mut3: dropping the nonzero-mass guard in `cond_law_to_bind` is refuted by
  a Qed two-point counterexample (strongest mutation form).
- P1 finding 7 / P3: axiom criterion is "zero axioms beyond the boolp trio
  baseline" (propositional_extensionality, functional_extensionality_dep,
  constructive_indefinite_description) — "closed under the global context" is
  unattainable for any `forall R : realType` statement.
- P5 finding 2: headline-consumed supports are exactly statdist_eq0 /
  statdist_test_le / statdist_test_max / adv_triangle; statdist_triangle and
  adv_ge0 are kept for prop:smc:composition itself, not for the headlines.
- Pre-commit gate dry run on the probe set: all 145 errors are H001
  (statement comments) and F001/I001 (naming grammar) on scratch files —
  style rules aimed at permanent code. Fold-in: the flagged names
  (`statdist_test_le`, `statdist_test_max`, `perfect_privacy_testP`,
  `eps_privacy_testP`, `cond_law_to_bind`, `stoch_comp_dirac_fdistmap`,
  `c_in_adv_records`) are explicit inputs to the naming audit, which must
  either bless them with a `Naming:` justification or rename them before
  they enter permanent files. Statement comments are mandatory in the
  permanent files (terse mathematical style per the statement-comment
  rule); probes stay comment-light. The probe commit itself is bypassed
  (logged), since the same content re-enters the unbypassed gate when the
  permanent files land.

## 5. Soundness invariants

- No new axiom or assumed constant; per-lemma criterion: zero axioms beyond
  the boolp trio baseline.
- No distributional-equality claim where only computational
  indistinguishability is available: computational content appears only as
  reduction-form, adversary-indexed epsilons; `Delta_eff` is never
  concretized; only the abstract `class_adv T`.
- Quantifier order: `perfect_privacy` fixes ONE simulator for all inputs
  (`=1`); the per-input constant simulator does not satisfy the definition.
- Degenerate regimes recorded honestly: `class_adv set0 _ _ = 0` (empty
  tester class certifies nothing); eps-privacy with eps >= 1 is vacuous;
  the three-verdict toy exhibits non-vacuity concretely.
- Hypothesis-set satisfiability: probe P1's vacuity section discharges the
  kernel hypotheses at a concrete instance and proves a perfect-privacy
  consequence; probe P3's concrete section does the same for the party layer.
- English-statement fidelity: each artifact row in §3 names its chapter
  label; the thesis-repo map extension cross-links both directions.

## 6. Open decision (user): scope of the Iwamoto direction

For randomized functionalities the view-only triangle does NOT imply
`eq:smc:entropy` with `Y_{bar A}` on the left (the view correlates with
honest outputs through the ancilla); Lindell/Iwamoto handle randomized F
with a JOINT (view, output) simulation notion. Recommendation (in force
unless the user overrides): formalize the direction for deterministic `F`
(covers DSDP; coincides with the joint notion there), and flag the
randomized case as a candidate prose caveat for the chapter (soundness
audit to double-check against Iwamoto Thm 5.6 as cited). Alternative:
strengthen the kernel's perfect privacy to the joint form — bigger surface,
not needed by any current instance.

## 7. Deliverable in the thesis repo

Extend `docs/notes/20260731-2237-security-models-pre-game-structure-map.md`:
add the game-section and examples-section blocks (lines 1776-2571, same table
format) and a "Rocq artifact" column on ALL blocks (existing artifacts such as
`bob_ext_ok`, `fdist`, centropy files named directly; new rows use the
identifiers of §3; prose-only rows get a dash).

## 8. Process

Implementation only after: D probes land, two adversarial audits (soundness +
naming, parallel, compile-capable agents) return GO, findings folded here,
user reviews this spec. Then superpowers:writing-plans; one atomic task per
commit; each file compiles before the next starts; probe code copied verbatim
with the probe path cited per task; golf pass on proof bodies only; audit
gate unbypassed on substantive commits.
