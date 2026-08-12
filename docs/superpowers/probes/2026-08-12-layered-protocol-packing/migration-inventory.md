# Migration inventory (Section 5.3 raw material)

Swept 2026-08-12 at HEAD `995e2a39` by a read-only repository agent. This file
is the evidence base for the Section 5.3 migration matrix of
`docs/superpowers/requests/2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`.

## Record parameters (verbatim sources)

- `SecurityWitness` — `reconstruct/algebraic_rigidity.v:147-157`, section vars
  `R : realType`, `M : MonodromyReprWithGeneratorType`; post-section
  `Arguments SecurityWitness R M : clear implicits` (:196). Fields: sw_L,
  sw_bound_eps, sw_rho_dist, sw_bound, sw_exact (option (SecurityExact
  sw_rho_dist)), sw_asymptotic (option SecurityAsymptotic). There is NO sw_eps.
- `SecurityExact` — :90-96, `Arguments {R} {M} rho` (:194). Fields se_eps, se_exact.
- `SecurityAsymptotic` — :122-134, `Arguments {R} {M}` (:195). Fields sa_spectral_gap,
  sa_eps_inf, sa_gap_pos, sa_gap_le1, sa_eps_inf_ge0, sa_rho_L, sa_convergence.
  HAZARD: `sa_*` prefix collides with SampleAdapter's `sa_*` (both loaded
  together in pgg_sample_adapter.v already; new bundle fields use scb_*).
- `MonodromyProfile (R)` — `protocol/pgg_monodromy_profile.v:49-55`;
  `mp_security` is the ONLY field mentioning R.
- `ExecutionPlug (R) (mp)` — `protocol/pgg_execution_plug.v:57-72`; R needed
  only to type mp; no field mentions R; no Arguments directive.
- `SampleAdapter (R) (mp) (e)` — `security/pgg_sample_adapter.v:114-121`;
  R genuinely used (`sa_sampleP : R.-fdist _`); keeps R after migration.
- `AlgebraicRigidity` — :187-190 { ar_security : SecurityWitness; ar_threshold :
  ThresholdWitness }. `ThresholdWitness` (:181-185) already R-free.
- `CombinatorialRigidity` — `reconstruct/combinatorial_rigidity.v:42-47`
  { cr_security : SecurityWitness R M ; cr_covering; cr_genus_gt0; cr_klein_lt_card }.
- `SecurityProfile` — algebraic_rigidity.v:475-480 { sp_Lstar; sp_witness :
  SecurityWitness R M; sp_at_Lstar : sw_L sp_witness = sp_Lstar; sp_nontrivial :
  sw_bound_eps sp_witness < 2 }.
- `CertifiedSolution` — :514-521 { cs_params : SecurityParams; cs_witness :
  SecurityWitness R M; cs_L_eq; cs_denom_pos; cs_eps_le }.

## SecurityWitness producers (19 build-tree) and their bundle bucket

Bucket key: BOUND = returns ShuffleMarginalBound; EXACT = bundle with
scb_exact = Some; ASYM = bundle with scb_asymptotic = Some; BOTH = both Some.

Generic:
| name | site | optionals | bucket |
|---|---|---|---|
| security_witness_fiber | algebraic_rigidity.v:223 | None,None | BOUND |
| security_witness_endpoint_inj | algebraic_rigidity.v:261 | None,None | BOUND |
| security_witness_from_bound | algebraic_rigidity.v:297 | None,None | BOUND (ORPHANED) |
| security_witness_with_exact | algebraic_rigidity.v:311 | Some,None | EXACT (ORPHANED) |
| security_witness_schreier | pgg_schreier.v:351 | None,Some | ASYM |
| security_witness_from_entropy | pgg_entropy_security.v:579 | None,None | BOUND |
| uniform_security_witness | pgg_uniform_security.v:186 | Some,None | EXACT (ORPHANED) |
| discovery_to_certification | pgg_protocol_landscape.v:469 | delegates schreier | ASYM |
| certified_from_witness | algebraic_rigidity.v:554 | consumes sw_L/sw_bound_eps | takes BOUND |
| ar_security_profile | algebraic_rigidity.v:483 | consumes sw_L/sw_bound_eps | takes bundle→bound (ORPHANED) |

Instance:
| name | site | optionals | bucket |
|---|---|---|---|
| abel_security_witness_direct_1 | abelian/rigidity_abelian_instance.v:145 | None,None | BOUND |
| ncycle_security_witness_direct_1 | cyclic/rigidity_cyclic_instance.v:87 | None,None | BOUND |
| monster_security_witness_Lstar | monster/rigidity_monster_instance.v:138 | None,None | BOUND |
| monster_security_witness_schreier | monster/rigidity_monster_instance.v:265 | None,Some | ASYM (ORPHANED) |
| oc_security_witness_2 | oc/rigidity_oc_instance.v:125 | None,None | BOUND |
| oc_security_witness_schreier | oc/rigidity_oc_instance.v:180 | None,Some | ASYM |
| s5_security_witness_1 | s5/rigidity_s5_instance.v:154 | None,None | BOUND |
| s5_security_witness_schreier | s5/rigidity_s5_instance.v:200 | None,Some | ASYM |
| s5x5_security_witness_1 | s5x5/rigidity_s5x5_instance.v:204 | None,None | BOUND |
| s5x5_security_witness_schreier | s5x5/rigidity_s5x5_instance.v:275 (tactic, Defined) | None,Some | ASYM |
| star_security_witness_1 | star/rigidity_star_instance.v:107 (NOT BUILT; file has Admitted:103) | None,None | BOUND |
| fc_kim_security_witness | kim2025/five_card_kim.v:507 | Some,Some | BOTH (only both-Some in build) |
| kim_security_witness_centi | kim2025/five_card_kim.v:630 | inherits both | BOTH |
| pgl27_security | pgl27/pgl27_profile.v:98 | Some,None | EXACT |
| monster_security_from_entropy | pgg_entropy_security_demo.v:64 | None,None | BOUND |
| monster_security_short_L | pgg_entropy_security_demo.v:119 | None,None | BOUND (ORPHANED) |
| oc_security_from_entropy | pgg_entropy_security_demo.v:211 | None,None | BOUND |
| oc_security_from_entropy_L | pgg_entropy_security_demo.v:259 | None,None | BOUND |

SecurityAsymptotic producers: security_witness_schreier_asymptotic
(pgg_schreier.v:334), fc_kim_asymptotic (five_card_kim.v:480/496),
oc_asymptotic (:168), s5_asymptotic (:186), s5x5_asymptotic (:252, only
sa_eps_inf <> 0).

## MonodromyProfile values (complete)

| # | name | site | mp_security arg | liveness |
|---|---|---|---|---|
| 1 | abel_profile R | abelian/abel_profile.v:69-71 | abel_security_witness_direct_1 R | near-orphan (profile_k_abel only) |
| 2 | five_card_profile R eps Hlt Hgt Hspec L | kim2025/five_card_family.v:164-168 | fc_kim_security_witness Hlt Hgt Hspec L | LIVE hub |
| 3 | pgl27_profile R | pgl27/pgl27_profile.v:105-106 | pgl27_security | LIVE |
| 4 | s5_profile R | s5/s5_profile.v:51-53 | s5_security_witness_schreier R 286 | near-orphan (profile_k_s5) |
| 5 | s5x5_profile R | s5x5/s5x5_profile.v:42-44 | s5x5_security_witness_1 R | near-orphan (profile_k_s5x5) |
| 6 | den_boer_profile R (wrapper) | denboer1989/den_boer_profile.v:76-78 = five_card_profile 0 ... 1 | inherited | LIVE |
| 7 | kim_profile L (wrapper) | kim2025/rigidity_kim_instance.v:66-67 | inherited | ORPHANED (0 refs) |

No monster/oc/cyclic/star/wreath MonodromyProfile exists (those stop at
AlgebraicRigidity). Rigidity values to migrate (contain a SecurityWitness):
abel_rigidity, ncycle_rigidity, monster_rigidity, oc_rigidity,
oc_rigidity_cryptographically_secure, s5_rigidity,
s5_rigidity_cryptographically_secure, s5x5_rigidity,
s5x5_rigidity_cryptographically_secure, s5x5_combinatorial_rigidity (only
CombinatorialRigidity value), star_rigidity + star_certified_1 (unbuilt).

## mp_security consumers (all sites)

| site | decl | migration |
|---|---|---|
| pgg_monodromy_profile.v:87 | profile_eps | delete; only consumer is profile_eps_pgl27 |
| pgg_monodromy_profile.v:96 | profile_anonymous | delete; ZERO external consumers |
| den_boer_profile.v:87 | den_boer_perfect | restate over fc_kim_security_witness ... 1 (cf five_card_family.v:183 five_card_eps0_eq0, already mp_security-free) |
| pgl27_profile.v:119 | profile_eps_pgl27 | restate over pgl27_security's bound |
| pgl27_exec.v:373 | pgl27_witness_cut_dist | re-source sw_rho_dist from separate PGL bound value |
| pgl27_exec.v:381 | pgl27_sample_witness_prodE | same |
| five_card_exec.v:492 | five_card_witness_cut_dist | re-source (NOTE: no consumer outside own decl; removal candidate per request 5.2) |
| five_card_exec.v:858 | den_boer_witness_rotationE | re-source from den Boer bound value (proof unfolds /den_boer_profile at :862) |
| five_card_exec.v:877 | den_boer_sample_cut_witnessE | same |

## SecurityWitness consumers by file (beyond producers)

- pgg_dealer_bridge.v: :38 Let L := sw_L (ar_security ar); :79-84
  dealer_words_epsilon_bound consumes sw_rho_dist/sw_bound_eps/sw_bound.
- pgg_protocol_landscape.v: security_per_position (:124-127),
  protocol_correct_unbundled (:314, pure signature slot),
  ar_security_per_position (:365-370), entropy sections :496/:501/:584,
  ar_covering_decomposition (:589-595), ar_genus0_shamir (:599-607),
  discovery_to_certification (:469-472).
- pgg_landscape_demo.v (NOT in request's file list but real consumer):
  monster_security_demo :81-85, monster_entropy_gap_demo :139-142,
  monster_pinsker_demo :148-150, oc_security_demo :211-215.
- pgg_entropy_security_demo.v: eps lemmas at :68-74, :175-176, :217-229,
  :263-270, :287-305.
- five_card_kim.v: kim_deal_centi_lt :635-644 (sw_rho_dist, sw_bound,
  /sw_bound_eps unfold).
- five_card_family.v: five_card_eps0_eq0 :180-184 (sw_bound_eps of the
  witness directly, mp_security-free — survives as-is modulo rename).
- star: star_eps_rational :199-205 (unfolds /security_witness_fiber),
  star_certified_1 :207-212 (only certified_from_witness call site).
- pgg_collusion_bound.v and pgg_security_solver.v: COMMENT-ONLY, no code
  dependency.
- pgl27_group.v:97-100: comment — pgl27_M must stay a Notation (ascription
  would seal HB hasGenerators needed by the witness downstream); same
  constraint holds for ShuffleMarginalBound (same statement shape).

## ep_cards_bridge / exec_content_from_plug

- ep_cards_bridge consumer: ONLY exec_content_from_plug
  (pgg_execution_plug.v:246-250). Producers pass erefl at both instance call
  sites (pgl27_exec.v:104, five_card_exec.v:139).
- exec_content_from_plug consumers: ZERO repo-wide (only its own definition
  :242/:246). Removal of both is a closed edit inside pgg_execution_plug.v
  plus a dropped argument at 4 constructor sites (2 smart constructors x 2
  instance calls).

## Explicit-R application sites whose arity changes

- pgl27_exec.v: 33 sites (listed by line in the run log; plug ctor :104,
  exec_* :130-281, MkSampleAdapter :312/:432, sa_* :319-499).
- five_card_exec.v: 34 sites (plug ctor :139, exec_* :175-378, :690,
  cross-profile biasE :790/:793, MkSampleAdapter :430, sa_* :438-515).
- pgg_sample_adapter.v: 5 generic-section sites (:141,:150,:158,:231,:232).
- pgg_execution_plug.v: :88,:107 (MkExecutionPlug in smart constructors);
  :291,:305,:348 are @-for-Hsz only, R not passed.
- pgl27_run.v: :220 @run_recover R (pgl27_profile R); :232 @run_party R.
- pgl27_profile.v: :119 @profile_eps R (whole lemma restated).
- No (R := ...) named-argument form anywhere.

## Other findings

- five_card_exec_procs_biasE (five_card_exec.v:784-796) exists precisely
  because the witness is invisible to processes; after stage A the two
  profiles are literally the same value and the lemma degenerates —
  restate/retire per plan.
- kim_profile is orphaned; den_boer_profile is live.
- profile_anonymous dead; profile_eps one consumer.
- star instance not in _CoqProject and carries an Admitted.
- pgg-smc/groups/pgg_cycle.v untracked yet listed in _CoqProject:173 (clean
  clone cannot build) — pre-existing, unrelated to this request.
