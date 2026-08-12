# Probe ledger: layered protocol packing (§15 gate)

Request: `docs/superpowers/requests/2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`.
HEAD at probe time: `995e2a39`. Build command for every probe:
`sh docs/superpowers/probes/2026-08-12-layered-protocol-packing/rebuild.sh <file>.v`
(one worker; exit code preserved). Probe files cannot `Require` each other
(the directory name is not a legal logical path component); shared modules are
copied per file.

## Unit A — §15.1 profile split + §15.3 computational cache: GREEN

Files: `probe_a_profile_split.v` (830 lines), `probe_a_mutation.v` (219),
`probe_a_vmcompute.v` (278). Exit 0 each; 5 s / 5 s / 35 s (30 s of which is
the deliberate Timeout guard). Zero Admitted/Abort/Axiom.

- Revised records elaborate with NO realType in the program layer:
  `MonodromyProfile` 5→4 fields (mp_security dropped), `ExecutionPlug` 8→7
  (ep_cards_bridge dropped), smart constructors lose R + cards_bridge.
- Both instance profiles become CLOSED TERMS: `pgl27_profileP`,
  `five_card_profileP` (no R, eps, hypotheses, or L);
  `den_boer_profileP = five_card_profileP` by `by []`.
- Process lists recovered by definitional equality at both carriers
  (`pgl27_exec_procsPE`, `five_card_exec_procsPE`, both `by []`).
- Full correctness chains transported at BOTH carriers
  (`..._terminatesP/_endpointsP/_decodeEP/_reconP/_recoversP/_correctP`).
- §7.8 verifier twin landed: `exec_verifier_trace` +
  `exec_endpoints_verifier_traceE` (`by []`).
- Print Assumptions on the five key results: **Closed under the global
  context** (stronger than the boolp-trio prediction — dropping mp_security
  removes every fdist dependency from the correctness cone).
- Mutation file: five-card profile with the PGL ReconPlug fails by type
  mismatch (`ReconPlug FiveCardKim_M bool` expected); errors harvested
  verbatim in-file.
- §15.3 cache: concrete `pgl27_players` 0.022 s, record-field `ep_players`
  0.016 s, `enum 'I_8` stuck (385 KB normal form, `Finite.enum` + `idP`
  leaves; Timeout-30 guard fires; `size (enum 'I_8)` case: vm completes to a
  stuck term and `reflexivity` fails). Verdict: keep `ep_players`/`ep_playersE`.
- API table: 54 explicit `@exec_*` sites change arity (24 pgl27_exec.v,
  30 five_card_exec.v — line lists in the unit-A report/section 3);
  23 `@sa_*` sites change ONLY the type of their mp argument, not arity
  (SampleAdapter keeps its own R).
- Deviations: probe files copy module PS instead of Require (path
  constraint); `PS.exec_procs` needs the @-form after discharge (e not
  inferable — matches production shape); pgl27 recovery smoke test included
  (nothing deferred).

## Unit B — §15.2 witness split: GREEN

Files: `probe_b_witness_split.v` (615 lines, 26 Qed), `probe_b_mutation.v`
(284 lines, 4 Fail + 4 Qed). Exit 0; 8.3 s / 5.5 s. Zero Admitted/Abort/Axiom;
Print Assumptions = boolp trio exactly, on all 19 anchors.

- `bound_of_witness` / `bundle_of_witness` typecheck with NO cast — the
  sw_rho_dist carrier is convertible by iota, so ALL 19 producers migrate
  mechanically (4 buckets exercised directly: s5 fiber BOUND, s5-schreier
  ASYM incl. tactic-mode s5x5 via cr_security, pgl27 EXACT, Kim BOTH incl.
  kim_security_bundle_centiB built directly).
- FORCED ADJUSTMENT (plan must carry verbatim): `Set Implicit Arguments`
  demotes the first field of dependent constructors, so
  `Arguments MkShuffleMarginalBound {R M} _ _ _ _.` and
  `Arguments MkShuffleCertificateBundle {R M} _ _ _.` plus
  `clear implicits` on both records are required; without them
  shuffle_bundle_of_bound as written in the request does not compile.
- Consumer patterns all elaborate: AlgebraicRigidityB (bound + asym values),
  CombinatorialRigidityB (from s5x5 projections, no re-proof),
  SecurityProfileB (sp_at_Lstar stays erefl), CertifiedSolutionB
  (cs_L_eq stays erefl), dealer-bridge Let-L, dealer_words_epsilon_bound
  (`exact: sw_bound` through scb_bound), security_per_position,
  kim_deal_centi_lt (unfold list gains /bundle_of_witness /bound_of_witness).
- Five witness ties restated against separate bound values: profile_eps_pgl27B
  (`by []`), den_boer_perfectB (proof unchanged), pgl27_sample_cut_distEB
  (product equation restated, tail byte-identical), den_boer_witness_rotationEB
  (/den_boer_profile -> /den_boer_marginal_boundB /bound_of_witness),
  den_boer_sample_cut_witnessEB (unchanged).
- Usage audits: `five_card_witness_cut_dist` zero external refs -> DELETE;
  `pgl27_witness_cut_dist` one same-file consumer -> inline away.
- Mutations: M1a same-group different-rho (L=2 exact onto L=1 bound) red;
  M1b cross-instance red; M2/M3 emptied-slot equations red with passing
  positive controls; errors harvested verbatim in-file.
- API facts for the plan: `scb_exact b != None` ill-typed (option not an
  eqType) — state Some-shape facts via isSome or = Some/None; files that
  receive the eps side conditions need `Import Num.Theory` (ltr0n not in
  scope from a bare algebraic_rigidity import block); certified_from_bound
  keeps the landed argument-demotion behavior (call with @).

## Unit C — §15.4 ObservedExecution: GREEN

Files: `probe_c_observed_execution.v` (1240 lines), `probe_c_mutation.v`
(609 lines, 5 Fail + 3 positive controls). Exit 0; 5.3 s / 34.9 s. Zero
Admitted/Abort/Axiom; Print Assumptions on all 8 anchors (both record
values, both recovery/correct corollaries, both static-recon discharges):
**Closed under the global context**.

- Record lands with the §9 skeleton exactly (dependency order, quantifiers,
  group membership only on oe_static_recon), in `Module OE` with
  **`Unset Implicit Arguments`** — the demotion is wider than unit B's:
  the three proof-field projections AND all nine derived declarations
  demote their record/oe argument; per-constant `Arguments` would need 14
  lines, the module flag needs 1. PS.exec_* occurrences use @-form.
- All five §9 derivations are pure one-line gluing (exec_endpoints_size,
  exec_run_recovers, exec_run_correct, exec_seat_endpointE,
  exec_coalition_endpointsE applied to record fields); no proof body
  duplicated. Five raw-row extractors are definitions with no equation.
- pgl27_observed: proof fields are probe A's lemmas verbatim.
  five_card_observed: one `case: x => a b` per field. Both closed terms;
  `Print five_card_observed` confirms no R/eps/hypotheses/L anywhere;
  `den_boer_observed := five_card_observed` with `by []` core equality.
- Mutations: ObservedExecutionNoEp (7 fields) — size proof unbuildable
  (M1a) and recovery gluing fails with a Hep hole (M1b), with positive
  controls isolating exactly the endpoint half. Generic semantic raw-row
  equation: readout form UNSTATABLE (unresolved implicit — committed list
  not a package field, M2a); static form statable but `by []` fails (M2b)
  and vm_compute DIVERGES on the generic goal (M2c) — an unguarded compile
  was killed at 10 minutes; `timeout 30 (vm_compute; reflexivity)` guard is
  mandatory; per-instance positive control (denboer_abs_p0) shows the shape
  is provable concretely.
- Tooling: Fail catches Timeout at command level, not tactic level;
  rocq_start cannot open a file whose body contains a 30 s command (harvest
  from a session on the other file).

## Unit D1 — §15.5 five-card half + §15.7 vacuity: GREEN

Files: `probe_d1_five_card_models.v` (547 lines), `probe_d1_mutation.v`
(444 lines, 7 Fail + positive controls). Exit 0; 10.1 s / 7.5 s. Zero
Admitted/Abort/Axiom; Print Assumptions on all 15 anchors = boolp trio only.

- Four sample models land at the fixed carriers: uniform (landed, cited),
  single biased (Omega, kim_input_dist, rotation cut), repeated biased
  ((bool*bool) x L.-tuple 'I_5, uniform-pairs x word_weighted, word_eval cut),
  concrete centi (repeated at 1/100, L=7). MkSampleAdapter's plug argument
  cannot be `_` (ep_inputT projection blocks unification) — pin e explicitly.
- Cut identities: kim_single_cut_distE (= rotation image of kim_weight_dist),
  kim_repeated_cut_distE (= rho_from_words_weighted at fc_kim_sigmas),
  kim_centi_witness_rhoE (`by []`) + kim_centi_cut_distE. Proof order trap:
  unfold the product/rho FIRST, marginal chain second, fdistmap_comp last.
- COLOUR READER (NEEDS-PROBE resolved): compiled orientation is
  `cut = fc_sigma ^+ k` (positive exponent); the whole bridge already exists
  in denboer_trace.v (denboer_player_trace_shape + denboer_player_trace_ok);
  failed orientation's error harvested. Pointwise five_card_colour_viewE,
  RV equality to kim_view (definitionally ViewA), duplicate-order instance
  [::1;3;1] and out-of-range instance [::0;7] (false default agrees on both
  sides). decode_bool s := (s == inord 1) is STUCK under vm_compute (idP
  opacity) even on the static side — close concrete values by transporting
  to the ViewA side first, then plain conversion.
- kim_input_private BRIDGE HYPOTHESES (item 16): request CONFIRMED — third
  section hypothesis eps_small : 0 < 5^-1 - `|eps| at kim_input_privacy.v:420
  is required (enters via kim_div_bound; not implied by Hlt+Hgt, witness
  eps = -1/2). Transported corollary five_card_colour_view_leak_bound
  consumes Hlt, Hgt, Hspec, L, Hsmall — Hspec/L ONLY because the executed
  reader is stated over the eps-indexed plug; stage A's parameterless plug
  sheds them.
- sa_seat_distE instantiates at the repeated + centi models in one line
  (five_card_exec_endpoints discharges Hep at every cut).
- §15.7 vacuity: full hypothesis table at eps=0 and eps=1/100 incl. the two
  new smallbias lemmas; fc_kim_security_bound (five_card_kim.v:568)
  instantiated at both biases; per-theorem consumption table in-file.
- Mutations: bias (Fail + SEMANTIC disequality kim_single_cut_dist_neq_uniform
  Qed'd via rho_from_words_weighted1/kim_var_dist_exact route), constant cut,
  constant decoder (general + concrete-with-heart), missing-Hsmall (two
  forms) — all rejected with harvested errors and positive controls.
- New standing rules: `exact: erefl` is the discriminating closer for fdist
  equalities (by [] gives uninformative "No applicable tactic"); NEVER let a
  bare `//` or nth_default side goal see `size (exec_endpoints ...)` (it
  evaluates run_interp by conversion — latent bomb found and defused);
  qualified kim_input_privacy.card_bool2 is in the cone (the local
  five_card_card_bool2 copy is only needed by five_card_exec.v itself).

## Unit D2 — §15.5 PGL half: GREEN

Files: `probe_d2_pgl27_models.v` (387 lines, 11 Qed), `probe_d2_mutation.v`
(322 lines, 5 Fail + 5 Qed). Exit 0; 7.9 s / 7.4 s. Zero Admitted/Abort/Axiom;
Print Assumptions = boolp trio exactly, on all 15 anchors.

- Both fixed-secret models elaborate. `[the finType of pgg_gT pgl27_M]` FAILS
  ("has type finType while it is expected to have type finGroupType"); the
  working carrier form is `(pgg_gT pgl27_M : finType)`. The tuple carrier
  takes `[the finType of (200.-tuple 'I_5)%type]` as written. As in D1 the
  plug argument of `MkSampleAdapter` must be pinned, not `_`.
- Cut identities: `pgl27_fixed_cut_distE` = `U pgl27_G_pos (fdistmap_id;
  `exact: erefl` is REJECTED here because the map is `idfun`, not a
  conversion identity), `pgl27_fixed_word_cut_distE` = rho_word after
  `/rho_from_words_weighted /pgl27_word_wordP` (unfold first, as in D1).
- FINITE CONTENT READER (NEEDS-PROBE resolved): the direct
  `[ffun i : 'I_8 => ...]` form typechecks with NO seat-type transport
  (`(pi_T' (mp_PI mpP)).+1` is 'I_8 by iota, `pgl27_exec_seat_countE` is
  `by []`). Route to the landed trace: `pgl27_exec_rowE` (fold to
  `pgl27_exec_player_raw_trace` by `exact: erefl`, then the landed
  `pgl27_exec_raw_traceE`) then `/pgl27_player_trace`.
- NEW LATENT BOMB: an unscoped `rewrite ffunE` (also `!ffunE`, `2!ffunE`)
  TIMES OUT on a goal whose finfun body mentions `exec_participant_trace` —
  the occurrence search evaluates the interpreter. `rewrite [LHS]ffunE
  [RHS]ffunE` fires in milliseconds. Same class as the D1 `//` bomb.
- SECOND LATENT BOMB: `exact:`/`apply:` of `pgl27_exec_raw_traceE` on the
  UNFOLDED row equation diverges — ssreflect fills the leading realType
  argument as an evar and the unifier falls into `run_interp`. Fold first
  (`have -> : ... = pgl27_exec_player_raw_trace (R:=R) s w0 i by exact:
  erefl`), then apply with `@` and R pinned. `rewrite -/(...)` to fold also
  diverges; only `exact: erefl` on the fold is cheap.
- Static view route: `pgl27_exec_coalition_endpointsE` then
  `tnth_ord_tuple` (the profile's starts are `ord_tuple 8`, so seat i's start
  is i). `ts_encode orbit_scheme` needs NO bridge lemma — it is
  `orbit_encode` by primitive projection and `/=` discharges it.
- Distribution equalities: coalition (4.1), content-trace twin (4.2) and the
  arbitrary-prior joint (4.3) all go through `boolp.funext` + explicitly
  instantiated `-(fdistmap_comp f g)`. Bare `rewrite fdistmap_comp` fires the
  WRONG way (it unfolds `pgl27_word_wordP` to `fdistmap tuple_of_row (W `^
  200)` and merges), so both function arguments must be supplied.
- 4.3 pair orientation is (view, secret), matching `pgl27_view_mixing`; the
  executed side factors as `(fun v => (pgl27_view C v, pgl27_secret v)) \o
  (fun u => (u.1, word_eval u.2))` and the inner map is definitionally
  `sa_joint_dist (sa_arg (pgl27_word_sample secretP))`, closed by
  `rewrite /sa_joint_dist` after `-(pgl27_word_sample_joint_distE secretP)`.
- API arity facts for the plan: `pgl27_word_wordP R` and `rho_word R` take R
  EXPLICIT, but `pgl27_word_sampleP`, `pgl27_word_sample` and
  `pgl27_word_sample_joint_distE` take it IMPLICIT (`@pgl27_word_sampleP R
  secretP`); `pgl27_view_indep R (C:=C) HC` has R explicit and C implicit.
- Two 2^-39 miniatures land in three lines each over the landed
  `pgl27_word_view_indist` / `pgl27_word_trace_indist`; the exact-model
  bridge is `pgl27_exact_coalition_distE` plus the product corollary
  `pgl27_exec_exact_view_indep` (via `inde_dist_of_RV2`). `` `x `` binds
  tighter than application, so the right factor needs its own parentheses.
- Mutations: constant cut (two closers), dropped coalition guard (Fail plus
  SEMANTIC disequality `mu2_content_trace_neq` Qed'd at C = [set ord0],
  secret true, identity cut, differing at seat one), arbitrary-prior model in
  the fixed-secret slot (miniature proof and the distribution identity it
  rewrites by) — all rejected with harvested errors and positive controls.
  `mu3_same_secret` is the degeneracy control: at s = s' the bound reduces to
  `0 <= 2^-39` with no reference to the shuffle.
- Import edge added beyond the pgl27_exec cone: `pgl27_trace` (for
  `content_of`, `pgl27_player_trace`, `pgl27_coalition_trace`). Acyclic —
  `pgl27_trace` does not import `pgl27_exec`, and both probe files are
  leaves.

## Unit E — §15.6 generic transfer: GREEN

Files: `probe_e_transfer.v` (174 lines), `probe_e_mutation.v` (204 lines).
Exit 0 both, first compile each; 5.2 s / 7.1 s. Zero Admitted/Abort/Axiom;
all 9 Print Assumptions anchors = boolp trio (nothing closed — realType/fdist
drag boolp unconditionally).

- Generic lemma landed as `var_dist_fdistmap_transfer` (head-symbol
  conformance with the var_dist family; the suggested fdistmap_pair_transfer
  rejected — no pair in the statement). Proof: le_trans over var_dist_triangle
  through fdistmap fx Q, lerD, var_dist_fdistmap on each half,
  symmetric_var_dist internal. Discharged signature: both hypotheses are the
  only explicit arguments — `exact: (var_dist_fdistmap_transfer H1 H2)`.
- LIBRARY LOCATION FINDING: var_dist_triangle and var_dist_fdistmap are NOT
  in infotheo's variation_dist.v — they live in
  pgg-smc/security/pgg_collusion_bound.v:44/:73; the generic bound needs that
  import. `var_dist_refl` (var_dist P P = 0) does not exist anywhere — probe
  proves it (big1/subrr/normr0); upstreaming candidate.
- PGL instantiation `pgl27_word_view_indist_via_transfer` at delta = 2^-40,
  constant stays 2^-39 via the copied pow2_split; pgl27_word_mixing needs NO
  reorientation (already var_dist real ideal); pgl27_view_law_const takes C
  implicitly — call form (pgl27_view_law_const _ s s' HC). Statement
  agreement with the landed theorem is machine-checked by type ascription.
- Mutation M1: script without Hideal fails two ways (variable not found;
  le_trans/var_dist_fdistmap cannot match mixed readers) with an
  ltac-delivery control. M2 SEMANTIC: at P = Q = fdist1 true, fx = idfun,
  fy = negb, delta = 0 — HPQ holds, Hideal provably fails, and
  `transfer_needs_ideal` Qed's that the conclusion is FALSE
  (var_dist computes to 2). fdist1/fdistmap1/big_bool are the constructors;
  no Bernoulli needed.
- Traps: Order.TotalTheory.ltNge must be qualified and applied after
  apply/negP; lerNgt does not exist.



## Unit F — §15.8 facade + manifest: GREEN

Files: `probe_f_pgl27_facade.v` (313), `probe_f_five_card_facade.v` (398),
`probe_f_manifest.v` (308), `probe_f_client.v` (105), `probe_f_mutation.v`
(253). Exit 0 all; rebuild.sh gained ONE line
(`-R <probe-dir> lpp_probe`) enabling real import edges; earlier probes
recompile green under it (probe_b spot-checked). Zero Admitted/Abort/Axiom;
Print Assumptions on 10 anchors = boolp trio (aliases of the LANDED profiles
still drag fdist via mp_security; the closed-context result returns only
after the migration).

- Seven-section order works with no dependency cycle; 43 aliases
  (21 PGL + 22 five-card), every alias `Definition fa_x := @landed` retaining
  the exact type; five-card Transfer section intentionally empty with the
  H1-required documentation; endpoint bounds live in a `bound` sub-block.
- Manifest: Require Export of both facades; 5-row table (PGL exact,
  PGL word, five-card uniform/single-biased/repeated+centi) with honest
  levels — ONLY PGL finite-word is Security-bridged, and only "at the
  static-view layer" (fa_pgl27_transfer derives 2^-39 at rho_word, the
  sample's own cut distribution); observed-execution column ABSENT on all
  rows (OE is post-migration); rows 1/3/4 stay Sampled with capabilities.
  Checker: 33 Timeout-60 `Check (alias : type)` lines.
- Client visibility (machine-checked): Require is transitive in LOADING not
  IMPORTING — one import reaches all facade aliases + exported vocabulary by
  short name; instance constants only by qualified name (Fail Check passes
  on bare names). Production split: Require Export framework/type
  vocabulary, Require Import instance cone.
- Mutations: kim_deal_centi_lt cannot inhabit the coalition-bridge type
  (three defects shown: no coalition quantifier, no secret pair, different
  constant/strictness; errors harvested); deleted-alias and retyped-alias
  checker failures demonstrated; positive controls pass
  (fa_pgl27_transfer DOES inhabit the landed bridge type).
- H2 inventory (cross-checked = migration-inventory.md exactly): 5 direct
  profiles + den_boer wrapper (live) + kim_profile (ORPHANED); 14 grep false
  positives classified; order: five-card fold-in first, then s5/s5x5
  (Algebraic-only facades), abelian recorded-not-facaded (out of instance
  scope), oc/monster/cyclic/star not facade-eligible (no profile; star
  unbuilt + Admitted).
- THIRD LAZY-EVAL BOMB VARIANT: `Check (erefl : fa_x = landed_x)` diverges
  when the alias body reaches the interpreter (unifier evaluates run_interp;
  10-minute kill observed). Value-level retention checks only for
  program-layer aliases; everything else via alias_same_type (common-type
  forcing) under Timeout 60. Spelled type ascriptions are safe.
- Tooling: macOS has no timeout(1) — use perl alarm; batch rocq compile
  never echoes Fail messages (harvest unwrapped in scratch); rocq-mcp cannot
  see lpp_probe (flags come from _CoqProject) — compiler-only feedback for
  cross-probe imports.

## GATE SUMMARY

All seven units (A, B, C, D1, D2, E, F) GREEN at HEAD 995e2a39.
17 probe .v files; every public probe result Qed with Print Assumptions =
boolp trio or closed; every §15 mutation check red with harvested errors;
zero Admitted/Abort/Axiom anywhere. The §16 audits run next on this ledger,
the probe files, and the amended request.

## §16 RE-AUDIT OUTCOME (2026-08-12)

Soundness audit: VERDICT: GO (21 findings — 4 MAJOR all in Section 13's
new-scope manifest level/capability discipline, folded into request §16.4
items 1; probe-gate integrity independently confirmed by 5 recompiles and a
17-file Admitted/Abort/Axiom sweep; every §16.1 checklist item evidenced).
API/naming audit: VERDICT: GO (24 findings + complete per-file migration
table; MAJORs folded as request §16.4 items 2-4). All accepted findings
recorded in request §16.4; implementation planning is now authorized.
