# Section 5.3 migration matrix: SecurityWitness -> ShuffleMarginalBound / ShuffleCertificateBundle

Derived 2026-08-12 from `migration-inventory.md` (HEAD `995e2a39`). Status:
DRAFT-FOR-PROBE — probe unit B elaborates every row; the implementation plan
copies the probed rows verbatim. Bucket key: BOUND = `ShuffleMarginalBound R M`;
EXACT / ASYM / BOTH = `ShuffleCertificateBundle R M` with the named optional(s)
`Some`.

## New record layer (target, request 5.2 verbatim shapes)

```coq
Record ShuffleMarginalBound (R : realType) (M : MonodromyReprWithGeneratorType)
  := MkShuffleMarginalBound {
  sw_L : nat;
  sw_bound_eps : R;
  sw_rho_dist : R.-fdist {perm 'I_(pgg_N' M).+1};
  sw_bound : forall s,
    var_dist (fdistmap (fun sigma => sigma s) sw_rho_dist)
             (fdist_uniform (card_ord (pgg_N' M).+1)) <= sw_bound_eps }.

Record ShuffleCertificateBundle (R : realType)
    (M : MonodromyReprWithGeneratorType) := MkShuffleCertificateBundle {
  scb_bound : ShuffleMarginalBound R M;
  scb_exact : option (SecurityExact (sw_rho_dist scb_bound));
  scb_asymptotic : option (@SecurityAsymptotic R M) }.

Definition shuffle_bundle_of_bound R M (b : ShuffleMarginalBound R M)
  : ShuffleCertificateBundle R M := MkShuffleCertificateBundle b None None.
```

`SecurityExact` and `SecurityAsymptotic` are preserved unchanged. The old
`SecurityWitness` record and `MkSecurityWitness` are deleted in the same
commit (atomic migration; a type alias cannot preserve the 6-argument
constructor arity). Field names `sw_*` are reused deliberately: the old
projections are deleted in the same commit, so no collision survives.

## Core records

| decl | old | target | constructor change | compat path |
|---|---|---|---|---|
| MonodromyProfile | (R : realType), 5 fields incl. mp_security | no R, 4 fields | MkMonodromyProfile drops R + witness arg | none (atomic); witness moves to named per-instance bound/bundle values |
| ExecutionPlug | (R) (mp : MonodromyProfile R), 8 fields incl. ep_cards_bridge | (mp : MonodromyProfile), 7 fields | MkExecutionPlug drops R + cards_bridge | none; both instance call sites passed erefl |
| dealer_secret_plug / committed_input_plug | take R + cards_bridge | drop both | 4 call-site updates | none |
| exec_content_from_plug | consumes ep_cards_bridge | DELETED | — | zero consumers repo-wide |
| SampleAdapter | (R) (mp : MonodromyProfile R) (e) | (R) (mp : MonodromyProfile) (e) | unchanged arity, mp/e re-typed | none |
| AlgebraicRigidity.ar_security | SecurityWitness | ShuffleCertificateBundle R M | MkAlgebraicRigidity arg becomes bundle | consumers project scb_bound before sw_* |
| CombinatorialRigidity.cr_security | SecurityWitness R M | ShuffleCertificateBundle R M | same | same |
| SecurityProfile.sp_witness | SecurityWitness R M | ShuffleMarginalBound R M | sp_at_Lstar / sp_nontrivial read sw_L / sw_bound_eps of the bound directly | none |
| CertifiedSolution.cs_witness | SecurityWitness R M | ShuffleMarginalBound R M | cs_L_eq / cs_eps_le read the bound directly | none |
| profile_eps / profile_anonymous | read mp_security | DELETED from pgg_monodromy_profile.v | — | profile_eps_pgl27 restated over the PGL bound value; profile_anonymous has zero consumers |

## Generic smart constructors

| decl (site) | old return | target return | bucket |
|---|---|---|---|
| security_witness_fiber (algebraic_rigidity.v:223) | SecurityWitness | ShuffleMarginalBound | BOUND |
| security_witness_endpoint_inj (:261) | SecurityWitness | ShuffleMarginalBound | BOUND |
| security_witness_from_bound (:297, orphaned) | SecurityWitness | ShuffleMarginalBound (canonical bound-only ctor) | BOUND |
| security_witness_with_exact (:311, orphaned) | SecurityWitness | ShuffleCertificateBundle | EXACT |
| security_witness_schreier (pgg_schreier.v:351) | SecurityWitness | ShuffleCertificateBundle | ASYM |
| security_witness_from_entropy (pgg_entropy_security.v:579) | SecurityWitness | ShuffleMarginalBound | BOUND |
| uniform_security_witness (pgg_uniform_security.v:186, orphaned) | SecurityWitness | ShuffleCertificateBundle | EXACT |
| discovery_to_certification (pgg_protocol_landscape.v:469) | SecurityWitness | ShuffleCertificateBundle (delegates schreier) | ASYM |
| shuffle_bundle_of_bound (NEW, algebraic_rigidity.v) | — | ShuffleCertificateBundle | maps BOUND into bundle, both None |
| certified_from_witness (:554) | takes SecurityWitness | takes ShuffleMarginalBound | consumer |
| ar_security_profile (:483, orphaned) | SecurityProfile from AlgebraicRigidity | projects scb_bound (ar_security ar) | consumer |

## Direct MkSecurityWitness instance sites

| decl (site) | optionals | target |
|---|---|---|
| pgl27_security (pgl27_profile.v:98) | Some exact, None | split: `pgl27_marginal_bound : ShuffleMarginalBound R pgl27_M` (L=0, eps=0, pgl27_rho_dist, pgl27_sw_bound) + `pgl27_security_bundle : ShuffleCertificateBundle` with scb_exact = Some (MkSecurityExact ... pgl27_se_exact); name per request: pgl27_marginal_bound replaces pgl27_security |
| fc_kim_security_witness (five_card_kim.v:507) | Some, Some | `fc_kim_security_bundle` : bundle with BOTH attachments; its bound projection is the family marginal bound |
| kim_security_witness_centi (five_card_kim.v:630) | inherits both | `kim_security_bundle_centi` |
| oc_security_witness_schreier (oc:180) | None, Some | bundle ASYM |
| s5_security_witness_schreier (s5:200) | None, Some | bundle ASYM |
| s5x5_security_witness_schreier (s5x5:275, tactic/Defined) | None, Some | bundle ASYM |
| monster_security_witness_schreier (monster:265, orphaned) | None, Some | bundle ASYM |
| fiber/endpoint_inj/entropy family (abel:145, cyclic:87, monster:138, oc:125, s5:154, s5x5:204, star:107 unbuilt, entropy_demo x4) | None, None | ShuffleMarginalBound via migrated generic constructors |

New den Boer name (request 5.2): `den_boer_marginal_bound` := the bound
projection of the unbiased one-letter bundle
(`scb_bound (fc_kim_security_bundle @ eps=0, L=1)` up to the den Boer
eps0 hypothesis pack).

## Rigidity / profile values

| value (site) | old field arg | target |
|---|---|---|
| abel_rigidity, ncycle_rigidity, monster_rigidity, oc_rigidity, oc_rigidity_cryptographically_secure, s5_rigidity, s5_rigidity_cryptographically_secure, s5x5_rigidity, s5x5_rigidity_cryptographically_secure | ar_security := witness | ar_security := bundle (shuffle_bundle_of_bound for BOUND-bucket witnesses; the schreier bundles directly for ASYM) |
| s5x5_combinatorial_rigidity | cr_security := witness | cr_security := bundle |
| star_rigidity, star_certified_1 (NOT BUILT) | — | migrate opportunistically, not gating |
| abel_profile / five_card_profile / pgl27_profile / s5_profile / s5x5_profile | mp_security := witness | field deleted; profiles lose R (five_card also loses eps/Hlt/Hgt/Hspec/L); witnesses survive as the named bound/bundle values above |
| den_boer_profile (wrapper) | five_card_profile @ eps=0 L=1 | := five_card_profile (now the same parameterless core value) |
| kim_profile (wrapper, ORPHANED) | five_card_profile @ eps | delete or keep as alias := five_card_profile; decision at naming audit |

## Consumer re-plumbing

| site | old | target |
|---|---|---|
| pgg_dealer_bridge.v:38,79-84 | sw_* (ar_security ar) | sw_* (scb_bound (ar_security ar)) |
| pgg_protocol_landscape.v:124-127 security_per_position | (sw : SecurityWitness R M) | (sw : ShuffleMarginalBound R M) |
| pgg_protocol_landscape.v:314 protocol_correct_unbundled | signature slot, never projected | ShuffleMarginalBound (weakest sufficient) |
| pgg_protocol_landscape.v:365-370, :496, :501, :584, :589-607 | sw_* (ar_security ar) | project scb_bound first |
| pgg_landscape_demo.v:81-85,139-150,211-215 | sw_* (ar_security ar) | project scb_bound first |
| pgg_entropy_security_demo.v eps lemmas | sw_bound_eps of BOUND-bucket values | unchanged shape (values become ShuffleMarginalBound) |
| five_card_kim.v:635-644 kim_deal_centi_lt | sw_* kim_security_witness_centi | sw_* (scb_bound kim_security_bundle_centi) |
| five_card_family.v:180-184 five_card_eps0_eq0 | sw_bound_eps (fc_kim_security_witness ...) | sw_bound_eps (scb_bound (fc_kim_security_bundle ...)) |
| den_boer_profile.v:86-88 den_boer_perfect | sw_bound_eps (mp_security (den_boer_profile R)) | sw_bound_eps den_boer_marginal_bound (same 0 constant) |
| pgl27_profile.v:115-120 profile_eps_pgl27 | @profile_eps R (pgl27_profile R) | sw_bound_eps pgl27_marginal_bound = 0 (compatibility corollary) |
| pgl27_exec.v:372-393 witness_cut_dist / _prodE / _cut_distE | sw_rho_dist (mp_security mpP) | sw_rho_dist pgl27_marginal_bound |
| five_card_exec.v:491-492 five_card_witness_cut_dist | sw_rho_dist (mp_security mpF) | REMOVAL CANDIDATE (no consumer outside own decl; underlying Kim bound value preserved) — final call after repeated usage audit in probe B |
| five_card_exec.v:857-878 den_boer_witness_rotationE / den_boer_sample_cut_witnessE | sw_rho_dist (mp_security (den_boer_profile R)) | sw_rho_dist den_boer_marginal_bound |
| star_eps_rational / star_certified_1 (unbuilt) | fiber witness | bound value |
| pgg_collusion_bound.v, pgg_security_solver.v | comment-only | comment updates only |

## Exact/asymptotic attachment preservation ledger (invariant 13)

| producer | attachment | preserved as |
|---|---|---|
| pgl27_security | exact (se_eps = 0) | scb_exact of pgl27_security_bundle |
| uniform_security_witness | exact (0, endpoint_exact) | scb_exact (orphaned producer migrated, not deleted) |
| security_witness_with_exact | exact (param) | scb_exact |
| fc_kim_security_witness / kim_security_witness_centi | exact + asymptotic | both scb slots of fc_kim_security_bundle / kim_security_bundle_centi |
| schreier family (generic, s5, s5x5, oc, monster) | asymptotic | scb_asymptotic |
