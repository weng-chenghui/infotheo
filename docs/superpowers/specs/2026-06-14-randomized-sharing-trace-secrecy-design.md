# Randomized additive sharing: machine-checked view-level secrecy for the four PGG instances

Created: 2026-06-14. Revised: 2026-06-15 after an adversarial audit (see Audit record below).

Companion to the literature foundation
`docs/superpowers/specs/2026-06-14T125931Z-randomized-additive-sharing-literature.md`,
which records the construction and the verified citation backbone. This document is the
implementation design.

## Problem

The PGG sum-mod sharing deals the deterministic canonical representative
`sum_mod_encode s = [0; ...; 0; s]`. It is a valid sharing and reconstruction recovers it,
but the last shareholder holds the secret in the clear, so a sub-threshold coalition of size
one already learns the secret. We want a machine-checked, distributional secrecy theorem: once
the encode is randomized, a sub-threshold coalition's view carries zero information about the
secret, for all four in-scope instances. This is the distributional upgrade of the existing
combinatorial `ts_private` field, from "an alternative sharing exists" to `I(Secret; view) = 0`.

This plan stops at the view level. Tying the view to the executed `run_interp` trace (the
operational layer) is deferred; see Non-goals.

## Scope

All four in-scope instances: s5, s5x5, denboer1989, kim2025. Out of scope by standing project
policy: abelian, cyclic, monster, oc, star, wreath.

## Feasibility basis (established, not assumed)

Three Rocq probes settled feasibility before this design; the first two were temporary and
deleted, the third is retained as a seed.

1. The existing `run_interp` endpoint trace is the verifier's reconstruction view and
   determines the secret (`s5_run_recovers` proves `ts_recon(endpoints) = s`). It is the wrong
   object for a secrecy statement. The secrecy object is a sub-threshold coalition view.

2. The randomized additive sampler typechecks as a pushforward fdist over tuples of `'Z_N`,
   reconstruction equals the symmetric sum, and a sub-threshold marginal is secret-independent.

3. `du2002/_probe_c_pgg_secrecy.v` proves, with no custom axiom, that under the randomized
   encode's guarantees (`Mask` uniform, `Mask` independent of `Secret`), the player-1 share
   `sh1 = Secret - Mask` satisfies `P |= sh1 _|_ Secret`, hence `I(Secret; sh1) = 0` and
   `H(Secret | sh1) = H(Secret)`. The proof reuses du2002's `lemma_3_5'`, the one-time-pad engine
   from the scalar-product proof. This is the T = 2 single-mask case; the general T-of-T coalition
   statement is the main new proof of this plan (see Risks).

## Two families

The four instances split into two families with different randomization mechanisms.

| Instance | Secret | Randomization | View-level secrecy today | Uses `RandomizedSharing` |
|---|---|---|---|---|
| s5 | position `'I_5` | additive mask | to build (generalize the seed) | yes |
| s5x5 | product of two sum-mod | additive masks | to build | yes |
| den Boer | bool `a && b` | uniform cyclic cut | proven (`leak_k1`, `five_card_leakage.v`) | no |
| kim | bool | cyclic cut `<[fc_sigma]>` | to build (adapt the den Boer counting) | no |

The mechanisms are genuinely different: a one-time-pad additive mask versus a uniform cyclic
cut. They share the generic tail and the family wrapper.

## Architecture

Naming follows the local idiom: unprefixed CamelCase records, `Mk<Name>` constructors,
lowercase-initial field prefixes. The structure mirrors `AlgebraicRigidity`
(`algebraic_rigidity.v:187`), a wrapper over sub-witnesses with smart constructors. The record
shapes below are the forms a shape audit confirmed typecheck against the live codebase.

### Records and the family wrapper

`RandomizedSharing` carries the additive-family randomness assumptions, the local rendering of
SPP's `scalar_product_random_inputs`. The mask-independence field is the bundle form: each mask
is independent of the pair (secret, whole mask family), which is what the T-of-T one-time-pad
argument needs.

    Record RandomizedSharing (P : R.-fdist U) := MkRandomizedSharing {
      rsh_secret     : {RV P -> 'Z_N} ;
      rsh_mask       : 'I_(T-1) -> {RV P -> 'Z_N} ;
      rsh_mask_unif  : forall j, `p_ (rsh_mask j) = fdist_uniform card_ZN ;
      rsh_mask_indep : forall j,
        P |= rsh_mask j _|_ [% rsh_secret,
                                (fun u => [ffun i => rsh_mask i u] : {RV P -> {ffun 'I_(T-1) -> 'Z_N}})] }.

`LeakageWitness` is the interface the generic tail consumes. It is type-packed: `secretT` and
`viewT` are fields, not parameters, because a flat parameterized record cannot hold both the
additive (`'Z_N` secret) and card (`bool` secret) witnesses, which a single dispatch must return.
It is parameterized by the probability space `P`, which differs per instance. Named to avoid
collision with the existing `SecurityWitness` (the unrelated monodromy var-dist bound).

    Record LeakageWitness (P : R.-fdist U) := MkLeakageWitness {
      lw_secretT : finType ;
      lw_viewT   : finType ;
      lw_secret  : {RV P -> lw_secretT} ;
      lw_view    : {RV P -> lw_viewT} ;
      lw_indep   : P |= lw_view _|_ lw_secret }.

`SharingMechanism` is the family marker, parameterized by `P`. Each instance is exactly one
family, so a variant is the natural wrapper.

    Variant SharingMechanism (P : R.-fdist U) :=
      | Additive  of RandomizedSharing P
      | CyclicCut of CyclicCutData P.

    Definition mechanism_leakage (P : R.-fdist U) : SharingMechanism P -> LeakageWitness P :=
      fun m => match m with
        | Additive rs  => additive_leakage rs       (* via the T-of-T head *)
        | CyclicCut cc => cyclic_cut_leakage cc      (* via counting *)
      end.

`CyclicCutData` is thin: the cut group, its uniformity, and the proven `view _|_ Secret`. For den
Boer it wraps the existing `leak_k1`.

### Theorem chain

Family-specific head, the only place the families differ. It produces `P |= view _|_ Secret`.

    additive_view_indep   : from RandomizedSharing, any coalition of m < T shares
                            jointly independent of Secret                       (* s5, s5x5 *)
    cyclic_cut_view_indep : from cyclic-cut uniformity
                            (den Boer reuses leak_k1; kim new)

Generic tail, family-agnostic, polymorphic over abstract finTypes. Already closed to `Qed` by the
shape audit over abstract types, lifting the seed's proof.

    leakage_of_view_indep : P |= view _|_ Secret ->
                            `I(Secret; view) = 0 /\ `H(Secret | view) = `H `p_ Secret.

Per-instance final theorem, same shape for all four, obtained by feeding the instance's
`SharingMechanism` value through `mechanism_leakage` into the tail.

    <inst>_view_secrecy : `I(Secret; view) = 0 /\ `H(Secret | view) = `H `p_ Secret.

## File layout

Imports are infotheo plus `spp_proba`/`spp_entropy` (and `five_card_leakage` for den Boer). No
interpreter import is needed, since the executed trace is out of scope.

| File | Contents |
|---|---|
| `pgg-smc/security/pgg_randomized_sharing.v` | `RandomizedSharing`, `additive_view_indep` (T-of-T), `additive_leakage`. Promoted from the Probe C seed and generalized. |
| `pgg-smc/security/pgg_leakage_witness.v` | `LeakageWitness`, `SharingMechanism`, `mechanism_leakage`, `leakage_of_view_indep`, `CyclicCutData`, `cyclic_cut_leakage`. |
| `pgg-smc/instances/<inst>/<inst>_secrecy.v` (x4) | the instance's `SharingMechanism` value and `<inst>_view_secrecy`. |

The Probe C seed `du2002/_probe_c_pgg_secrecy.v` is underscore-prefixed and excluded from the
build manifest. Its content moves into the tracked `pgg_randomized_sharing.v` and the `du2002`
copy is deleted in the first implementation step.

## Per-instance instantiation

- s5: `Additive` over `sum_mod_scheme 3 4`. Build `RandomizedSharing`, apply `additive_view_indep`
  at the sub-threshold coalition, conclude `s5_view_secrecy`.
- s5x5: `Additive` over `product_scheme (sum_mod_scheme 3 4) (sum_mod_scheme 3 4)`. Instantiate
  `RandomizedSharing` on each of the two sum-mod components and combine through the existing
  `product_scheme` structure. A coalition below the product threshold `min(k1, k2)` is sub-threshold
  on each component, which supplies a one-time pad on each.
- den Boer: `CyclicCut` wrapping the existing `leak_k1` as the `LeakageWitness`, then conclude
  `denboer_view_secrecy`. No new view-level proof.
- kim: `CyclicCut`. New `cyclic_cut_view_indep` for kim's cut group `<[fc_sigma]>`, adapting the
  den Boer counting argument, then conclude `kim_view_secrecy`.

## Risks and mitigations

1. Additive T-of-T head, the main new proof. Generalize the proven T = 2 single-mask case to any
   coalition of `m < T` shares jointly independent of the secret. This is genuine work, an induction
   over the mask vector or a joint-uniformity lemma, not a one-liner from `lemma_3_5'` (which has a
   single mask `Z`). Mitigation: the bundle-form `rsh_mask_indep` supplies the joint hypothesis; the
   unseen coordinate of a sub-threshold coalition is the one-time pad.
2. kim cyclic-cut head. New counting over kim's five-rotation cut. Mitigation: the den Boer `leak_k1`
   proof is the template; kim's cut group is `<[fc_sigma]>`.
3. finType discipline. The entropy and mutual-info layer requires `finType` codomains. The packed
   `lw_secretT`/`lw_viewT` stay at `finType`; both families satisfy this (`'Z_N`, `bool`).
4. Threshold degeneracy. `'I_(T-1)` is empty at `T = 1`, so the mask family is vacuous there. Correct
   (no masks at threshold one) but to be aware of when instantiating small thresholds.
5. Correctness is untouched. Randomized shares still reconstruct because the sum is word-independent,
   so existing `*_run_recovers` proofs are not disturbed; secrecy is purely additive on top.

## Verification criteria

- All new lemmas reach `Qed` with no `Admitted`, no custom axiom beyond the standard `boolp`
  classical axioms already pervasive in the codebase.
- Records parity: each of the four instances carries its `SharingMechanism` value and its
  `<inst>_view_secrecy` theorem in a persisted, build-manifest file, matching siblings.
- The headline `<inst>_view_secrecy : I(Secret; view) = 0 /\ H(Secret | view) = H(Secret)` holds for
  all four instances through the single generic `leakage_of_view_indep`.

## Non-goals

- The executed-trace operational layer (the trace bridge) is deferred. It requires lifting
  `run_interp` to a probability space, which does not exist today, following SPP's
  `scalar_product_RV` construction; `leak_k1` lives over a standalone card-colour space, not a
  trace projection; the operational observer must be a single sub-threshold player. Recorded in the
  project memory `project_trace_bridge_deferred`.
- No change to the existing correctness or reconstruction proofs.
- No general representation-theoretic G-invariant secret-sharing theorem; the design assembles the
  additive linearity results and the cyclic-cut counting separately.
- No partial-erasure or dropout decoder; reconstruction still consumes the full share tuple.

## Audit record

The 2026-06-14 draft was reviewed by two adversarial agents (a codebase-claims auditor and a
rocq-mcp shape auditor). Confirmed sound: `lemma_3_5'` and the spp helpers, `leak_k1`/`leak_k5`,
`s5_run_recovers`, the scheme types, `product_scheme`'s `min(k1,k2)` threshold, the naming idiom,
the assumption-record legitimacy, and the generic tail (closed to `Qed`). Folded-in corrections:
the trace bridge is deferred as the operational lift it actually is; `LeakageWitness` is type-packed;
`rsh_mask_indep` is the bundle form; the additive head is scoped as genuine T-of-T work, not a
one-liner.
