# Security-models chapter formalization: design spec

Date: 2026-07-31
Branch base: `itp2026-dumas2017dual`
Status: PROBED AND AUDITED. All seven probes (P1-P5, D1, D4+D2) GO, exit 0,
zero axioms beyond the boolp baseline. Naming audit NO-GO resolved in-place;
soundness audit GO with all blocking findings folded. Awaiting user review,
then superpowers:writing-plans.

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
| `smc/security_models/spp_bridge.v` | SPP corrupted-Bob instance via `dist_of_RV_bind` |

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
| def:smc:tv-distance | `statdist p q := 2%:R^-1 * \sum_b `\|p b - q b\|`; `statdist_ge0/sym/triangle`; the definition's embedded max-over-events equality is `statdist_test_max` modulo tester-event identification (map cell says so) |
| distinguisher (game section) | `tester := {ffun B -> bool}`; `accept D p := Pr p [set b \| D b]`; `adv D p q` |
| prop:smc:max-advantage | `statdist_test_le`, `statdist_test_max` (optimal tester `[ffun b => q b < p b]`) |
| Delta_T (composition section) | `class_adv (T : {set tester}) p q := \big[Num.max/0]_(D in T) adv D p q` |
| prop:smc:composition | `class_adv_ge0/sym/xx/triangle/sub`; `class_adv_all` ties to `statdist` |
| (separation, for testP) | `statdist_eq0 : (statdist p q == 0) = (p == q)` |
| (headline supports) | `adv_ge0`, `adv_triangle` (one-liners via `normr_ge0` / `ler_distD`; consumed by the testP headlines and hybrid_bound) |
| (live sibling) | `statdist_var_dist : statdist p q = 2^-1 * var_dist p q` — `var_dist` EXISTS at `probability/variation_dist.v:33` with `symmetric_var_dist`/`pos_var_dist`/`def_var_dist`/`leq_var_dist` (:37-:55); the equality is definitional (`by []`). statdist.v cites it and derives the overlapping support lemmas from it where shapes allow, instead of duplicating |

Section plumbing (naming-audit finding 13): statdist.v declares
`Variable B : finType` (explicit), NOT probe P2's `Context {B}` — with an
implicit `B`, `tester` cannot be applied at `Bv` from privacy_kernel.v.
This is the one recorded deviation from the verbatim-copy rule.

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
| prop:smc:worlds-compute-f | `real_route_f` (via `run_correct`), `ideal_route_f` (via `F_compat`), `ideal_route_projx_f` (the second ideal route through `proj_X`, eq:smc:ideal-route-f's first equality; same `tensor_fdist1` + `fdistmap_comp` machinery) |
| eq:smc:test-advantage | `test_adv D S := \big[Num.max/0]_x adv D (view_law x) (sim_view S x)` |
| perfect/eps <-> forall D | `perfect_privacy_testP`; `eps_privacy_testP` carries the necessary side condition `0 <= eps` (empty-X + negative-eps makes the untested direction false; the chapter states no such condition, the formal statement must) |
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

### entropy_link.v (probe D1: both targets GO; scope decision §6)

Kernel extended (sub-section) with honest-side projections `Xh Yh`,
`proj_xh`, `proj_yh`, input prior `mu : R.-fdist X`, joint prior
`d := mu `x P_Omega`, RVs `view_rv`, `input_rv`, `allow_rv` (spelling
`{RV d -> _}` required for `pfwd1` inference, probe P4 finding 4).
Target (deterministic functionality):

- `triangle_cinde : d |= view_rv _|_ input_rv | allow_rv` from the per-input
  triangle;
- `cinde_centropy_eq :` H(honest | view, allowed) = H(honest | allowed) in the
  repo's centropy notation.

Headline names (naming-audit finding 11; amended by design B+ 2026-08-01):
the entropy_link headline is the arbitrary-F iff, candidate name
`perfect_privacy_centropyP` (final name passes the naming gate); the
forward direction and the triangle-form intermediate keep
`perfect_privacy_centropy_eq` / `triangle_centropy_eq` — NOT
`cinde_centropy_eq`, which would shadow the upstreamed generic lemma of
that name. Corollaries: deterministic-F and output-determined-F discharge
lemmas, plus the DSDP simulator-existence derivation.

Probe D1 outcome (`probe_entropy_link_mini.v`, Qed at abstract finTypes):
`triangle_cinde` via `cinde_RV_factor` + two pfwd1 helpers;
the centropy equality is a one-liner because the CI-to-centropy link
ALREADY EXISTS: `cinde_centropy_eq` at `dumas2017dual/lib/extra_entropy.v:126`
(routed through `cinde_cond_mutual_info0`, same file line 73). Modern
names: `cinde_RV` (proba.v; `cinde_rv` deprecated), `centropy_RV` with
`` `H( Y | X ) `` in entropy_scope (`cond_entropy` deprecated); the file
must `Local Open Scope entropy_scope`.

Dependency-direction decision: `smc/security_models/` must not import the
case-study directory `dumas2017dual/`. The plan therefore UPSTREAMS the
route's case-study-local lemmas into a root-level shared location
(target: `lib/` or `information_theory/`, fixed in the plan), with their
current file re-exporting or its clients re-pointed:
(naming-audit finding 12 fixes the targets, and the dependency closure is
four objects, not two):
- `cinde_cond_mutual_info0` + `cinde_centropy_eq`
  (`dumas2017dual/lib/extra_entropy.v:73/:126`) move to
  `information_theory/entropy.v` after the `cond_mutual_info` section
  (:1086), adding `Require Import graphoid` (legal: graphoid precedes
  entropy in `_CoqProject`);
- `cinde_RV_factor` (`dumas2017dual/lib/extra_proba.v:529`) with its
  dependencies `marg_out_Y`/`marg_out_X`/`marg_Z_X` (:494/:516), plus
  `cinde_RV_comp` (:465) and `fdist_proj23_RV3` (:239), move to
  `probability/proba.v` beside `fdist_proj13_RV3` (:955);
- `logr_eq1` (`dumas2017dual/lib/extra_algebra.v:37`) moves to
  `lib/realType_ln.v`;
- the `extra_entropy.v` copies are DELETED (grep: zero clients outside
  the file itself); root `lib/` was rejected as target (no probability
  content there).
Reason: all are generic information theory / probability; keeping them
in the case-study lib would invert the infra-to-case-study dependency
direction.

Two further D1 refinements adopted:
- The statements hold for an ARBITRARY joint prior
  `d : R.-fdist (X * Omega)` — the product form `mu `x P_Omega` is
  never used by the proofs. `entropy_link.v` states the lemmas at an
  arbitrary `d`, with the product-prior form as the corollary the
  chapter narrates.
- The sole genuinely-new supporting statement is `pfwd1_pair_det`
  (joint law of an RV with a deterministic function of it; 6 lines,
  Qed in the probe; `pfwd1_diag` at `proba.v:988` covers only `id`).
  It is generic and joins the upstreamed lemmas rather than staying
  private to `entropy_link.v`.
- Honest-projection step (soundness-audit finding 2, LOCALIZED open
  risk): probe D1 proves the FULL-INPUT form
  (CI of view vs `input_rv` given allowed). The chapter's
  eq:smc:entropy puts the honest pair (X_h, Y_h) on the left; under
  deterministic F both honest coordinates are functions of the full
  input, so the headline `perfect_privacy_centropy_eq` derives the
  honest form from the full-input form via graphoid `symmetry` +
  `cinde_RV_comp` (`extra_proba.v:465`, X ⊥ Y | Z implies
  f(X,Z) ⊥ Y | Z at `f x a := (proj_xh x, proj_yh (F0 x))`). This one
  step is unprobed at the carrier — the exact lemma, file, and
  composite are pinned here, and the implementation task probes it
  before the headline lands.

### unpredictability.v (probe D2 GO)

T-relative form only. `sec : X -> Sec`; `predictor := {ffun Bv -> Sec}`;
`pred_success` under the joint prior; `ideal_guess` from allowed information;
composition lemma `pred_success <= ideal_guess + e_game + e_sim` via
`class_adv` triangle + membership of induced testers in `T`; then
`unp_entropy_ge` by log monotonicity. D2 pinned: the base-2 log is
literally `log` (`lib/realType_ln.v:177`, `:= Log 2`); monotonicity is
`ler_log` (`{in Num.pos &, {mono log : x y / x <= y}}`); the bare
implication forms `log_le_probe` / `log_neg_probe` are Qed in
`probe_examples_f3.v`.

ACCEPTED UNPROBED SHAPE (soundness-audit finding 10; the one §3 item with
no compiled miniature): the composition lemma itself — per-input induced
testers `D_x := [pred b | pred_map b == sec x]`, the hypothesis that BOTH
hops' induced testers lie in `T`, and the weighted-sum assembly under the
joint prior — plus the positivity side condition
`0 < p_ideal + e_game + e_sim` that `ler_log`'s `Num.pos` domain forces
on `unp_entropy_ge`. These hypotheses are spelled here so the plan states
them verbatim; the unpredictability.v task begins with a shape probe
before the permanent statement lands.

### examples_f3.v (probe D4: all GO)

| chapter | artifact |
|---|---|
| ex:smc:dirac-matrix | `dirac_shiftE` on 'F_3 |
| ex:smc:mask-matrix | `mask_chan`; `mask_chan_uniform_hides`; biased (1/2,1/4,1/4) `biased3`; `mask_chan_biased_leaks` |
| ex:smc:ancilla-matrix | `draw_add_mask : fdistmap add (tensor (fdist1 x) m) = mask_chan m x` |
| tab:smc:privacy-laws / fig:smc:privacy-instance | three-verdict toy, an 'F_3 ANALOGUE of the chapter's 'F_29 instance (chapter: 1/2-at-0, 1/56-else, eps = 27/58; toy: (1/2,1/4,1/4), eps = 6^-1 — both are 1/2 - 1/#|F|; the map cell is labeled "F_3 analogue"): uniform => `perfect_privacy`; biased => `eps_privacy` (D4c: 6^-1 confirmed TRUE, mutation with 4^-1 fails); no mask => `insecurity` witness |

D4 construction facts folded in: `biased3` is nested binary `fdist_conv`
(`p <| w |> q`, `fdist.v:880-894`) over `fdist1`s — NOT `fdist_convn`
(which needs a weight fdist on 'I_3, the same problem one level down);
the weight literal `(2^-1 : R)%:pr` needs no side proof (`{i01 R}`
canonicals, `realType_ext.v:225`). `#|'F_3| = 3` by `card_ord` (no
`card_Fp` needed). Channel evaluation via a `mask_chanE` read-off lemma;
`tensor_dirac_l : tensor (fdist1 x) m = fdistmap (pair x) m` makes
`draw_add_mask` one `fdistmap_comp`.

### spp_bridge.v (probe P4 GO)

Bridge point: `bob_view_cond_sim_xy` (conditioning on Bob's own `(x2, y2)`,
i.e. exactly the allowed information) + the probe-P4 lemma (Qed, 6 lines) —
permanent name `dist_of_RV_bind` per naming-audit finding 3 (`_to_` is this
development's conversion-FUNCTION idiom, cf. `party_to_kernel`; the
conclusion's mainSymbols are `` `p_ `` = `dist_of_RV` and `>>=`) — give the
RV-form factorization

    `p_ BobView = `p_ [% x2, y2] >>= (fun '(b, y) => bob_simulator b y)

as the machine-checked nu = Sim o allow (marginal form); the per-input form is
`bob_view_cond_sim` itself. Both are recorded in the map. No du2002 file is
edited; scratch is never imported (`.scratch` has no logical name — permanent
files restate probe code verbatim).

Build caveat (naming-audit finding 16): `du2002/spp_simulator.vo` is
currently stale ("inconsistent assumptions over infotheo.smc.smc_interpreter");
the spp_bridge task rebuilds the du2002 chain before compiling.

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
D probes: D1 GO (CI + centropy route; upstreaming decision recorded in
§3), D2 GO (`log` / `ler_log`), D4 GO (nested `fdist_conv` construction;
eps = 6^-1 confirmed).

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
- P4 mut3 (wording per soundness-audit finding 4): demanding the
  conditional-law hypothesis at a SINGLE fibre only is refuted by a Qed
  two-point counterexample (strongest mutation form); the guard-flip
  variant is mut2, a compile-failure check.
- P1 finding 7 / P3: axiom criterion is "zero axioms beyond the boolp trio
  baseline" (propositional_extensionality, functional_extensionality_dep,
  constructive_indefinite_description) — "closed under the global context" is
  unattainable for any `forall R : realType` statement.
- P5 finding 2: headline-consumed supports are exactly statdist_eq0 /
  statdist_test_le / statdist_test_max / adv_triangle; statdist_triangle and
  adv_ge0 are kept for prop:smc:composition itself, not for the headlines.
- Pre-commit gate dry run on the probe set: all 145 errors are H001
  (statement comments) and F001/I001 (naming grammar) on scratch files —
  style rules aimed at permanent code. Statement comments are mandatory in
  the permanent files (terse mathematical style per the statement-comment
  rule); probes stay comment-light. The probe commit itself is bypassed
  (logged), since the same content re-enters the unbypassed gate when the
  permanent files land.

Naming-audit resolutions (VERDICT was NO-GO; all five blocking findings
folded here, none invalidates a probe result):

| name | resolution |
|---|---|
| `statdist_test_le` / `statdist_test_max` | keep, one `Naming:` note on the pair (subject is `adv`; pair-naming groups both halves of prop:smc:max-advantage; port continuity with 2bbc1714) |
| `perfect_privacy_testP` / `eps_privacy_testP` | keep, `Naming:` note (`P` = iff characterization, `ffunP`/`setP` precedent; `eps_` has repo precedent) |
| `stoch_comp_dirac_fdistmap` | keep, `Naming:` note (LHS-shape-then-RHS-symbol, same pattern as `fdist1bind`) |
| `cond_law_to_bind` | RENAMED `dist_of_RV_bind` |
| entropy_link headline | RENAMED `perfect_privacy_centropy_eq` (avoid shadowing the upstreamed `cinde_centropy_eq`) |
| `c_*` / `vac_*` instance families | RENAMED via named Modules (`Module identity_protocol` style) in the permanent files; bare prefixes are semantic-stripping |
| `statdist` vs `var_dist` | acknowledged live sibling; bridging lemma mandatory (see statdist.v rows) |
| `dirac` | no collision in the import closure today; `Naming:` note warns about mathcomp-analysis measure-theory `dirac` if imports ever widen |
| `probe_p3_statdist.v` names | no collision (file not in `_CoqProject`, no logical path) |

All other precedent line numbers verified live by the audit (one nit: the
`fdist_conv` span is 880-895).

Audit outcomes (both audits' evidence files kept in `.scratch/`):

- Naming/precedent audit: NO-GO with five blocking findings, all folded
  above (`audit_nam_scope.v`, `audit_nam_cross_section.v`).
- Soundness audit: GO with three blocking findings, all folded above
  (upstream closure completed with the marg helpers and `cinde_RV_comp`;
  honest-projection step recorded as a localized probe obligation;
  unpredictability composition recorded as the accepted unprobed shape
  with its hypotheses spelled out). Tautology probes: `tensorE`,
  `view_lawE`, `allowE`, `statdist_test_max`, `biased_uniform_eps` all
  non-trivial (`audit_snd_tautology.v`). Quantifier-order and insecurity
  non-vacuity compiled (`audit_snd_quantifier.v`). Randomized-F negative
  certificate compiled (`audit_snd_randomized_F.v`). Statement-match
  restatements checked against the chapter for every headline; the two
  mismatches found (worlds-compute-f second route, 'F_29 vs 'F_3
  example) are folded in section 3.

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
  consequence; probe P3's concrete section does the same for the party
  layer. Both instances degenerate the probabilistic layer (Omega = 'I_1);
  the non-degenerate witnesses are `audit_snd_quantifier.v` (per-input
  simulability without a single simulator, plus a satisfiable
  insecurity-hypothesis pair — prop:smc:insecurity is non-vacuous) and
  `audit_snd_randomized_F.v`.
- English-statement fidelity: each artifact row in §3 names its chapter
  label; the thesis-repo map extension cross-links both directions.

## 6. Scope of the Iwamoto direction (machine-checked; user may override)

For randomized functionalities the view-only triangle does NOT imply
`eq:smc:entropy` with the honest pair on the left. This is now
MACHINE-CHECKED, not a conjecture: `audit_snd_randomized_F.v` (Qed, exit
0) exhibits a randomized F whose per-input view-only triangle holds
(`view_only_triangle`) while CI fails (`not_cinde_honest`) and
`H(honest | view, allowed) = 0` (via `centropy_RV_comp0`,
`entropy.v:498`) against `H(honest | allowed) = log 2`. The chapter's own
definitions (def:smc:sim, eq:smc:simulation at security-models.tex:517-519)
are view-only, while Iwamoto Def 5.2/(25) conditions on ALL parties'
inputs-and-outputs (verbatim-verified against the KB slice, pp. 366-367)
— a jointly-conditioned notion — and the chapter states the equivalence
unrestricted while its own SPP functionality is randomized.

Decisions (SUPERSEDED 2026-08-01 by design B+, agreed with the user after
the Broadbent-Karvonen reading; companion spec:
`phd-thesis/docs/notes/20260801-security-models-output-independence-fix-design.md`):
- Rocq side: `entropy_link.v` states the characterization at ARBITRARY `F`
  as an iff (candidate name `perfect_privacy_centropyP`, `_testP` iff
  precedent), with two explicit hypotheses replacing the deterministic-F
  scope: simulator consistency (`out_A o Sim(a,y)` reads off `y`) and the
  output-independence condition as a `cinde_RV` clause
  (`view _|_ Y_h | (X, Y_A)`). Deterministic `F` (DSDP) and
  output-determined `F` (SPP, `y_a = f(x) - y_b`) become corollaries that
  discharge the condition structurally. NEW derived artifact: for DSDP the
  converse direction turns the mechanized counting results into simulator
  existence. New probe obligations before implementation: (a) mixture
  conditioning under out_A-disjoint supports selects the component;
  (b) the converse-direction Sim construction, including the off-support
  consistency decision (support-restricted consistency vs an out_A
  section). The audit counterexample file remains the negative certificate
  showing the condition is not free.
- Thesis side: the B+ fix (five touchpoints: condition + consistency +
  iff theorem + corollaries into the IT-characterization block; matrix
  example; BK citation correction at 1362-1372 — Thm 4.9 collapses the
  adversary quantifier, not the honest wire; BK typing remark; Lindell
  joint-pair sidenote). Detailed in the companion spec.

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
