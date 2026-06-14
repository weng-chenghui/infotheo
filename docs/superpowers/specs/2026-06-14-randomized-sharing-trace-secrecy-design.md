# Randomized additive sharing: machine-checked trace secrecy for the four PGG instances

Date: 2026-06-14

Companion to the literature foundation
`docs/superpowers/specs/2026-06-14T125931Z-randomized-additive-sharing-literature.md`,
which records the construction and the verified citation backbone. This document is the
implementation design.

## Problem

The PGG sum-mod sharing deals the deterministic canonical representative
`sum_mod_encode s = [0; ...; 0; s]`. It is a valid sharing and reconstruction recovers
it, but the last shareholder holds the secret in the clear, so a sub-threshold coalition
of size one already learns the secret. We want a machine-checked proof that, once the
encode is randomized, a sub-threshold observer's executed `run_interp` trace carries zero
information about the dealt secret, for all four in-scope instances.

The target is the information-theoretic shape of the Du-Atallah scalar-product proof,
`scalar_product_is_leakage_free` (`du2002/spp_proof.v:220`):
`H(Secret | observer_trace) = H(Secret)`.

## Feasibility basis (established, not assumed)

Three Rocq probes settled feasibility before this design; the first two were temporary and
deleted, the third is retained as a seed.

1. The existing `run_interp` endpoint trace is the verifier's reconstruction view and
   determines the secret (`s5_run_recovers` proves `ts_recon(endpoints) = s`). Lifting it as
   the random variable `V` forces `H(Secret | V) = 0`, the authorized-reconstruction case,
   not secrecy. The repo already carries this as `leak_k5`. Conclusion: the secrecy object
   is a sub-threshold observer view, never the verifier's full endpoint set.

2. The randomized additive sampler typechecks as a pushforward fdist over tuples of `'Z_N`,
   reconstruction equals the symmetric sum, and a sub-threshold marginal is secret-independent.

3. `du2002/_probe_c_pgg_secrecy.v` proves, with no custom axiom, that under the randomized
   encode's guarantees (`Mask` uniform, `Mask` independent of `Secret`), the player-1 share
   `sh1 = Secret - Mask` satisfies `P |= sh1 _|_ Secret`, hence `I(Secret; sh1) = 0` and
   `H(Secret | sh1) = H(Secret)`. The proof reuses du2002's `lemma_3_5'`, the same one-time-pad
   engine that proves SPP's `x2' = x2 + s2` secret-independent.

Why SPP succeeds where the existing PGG trace fails, and how this design fixes it: SPP
protects a party's input against the other party's view and injects uniform masks. The
existing PGG trace is the verifier's reconstruction view and the encode is deterministic.
The randomized sampler is the missing mask; a sub-threshold observer trace is the missing
object.

## Scope

All four in-scope instances: s5, s5x5, denboer1989, kim2025. Out of scope by standing
project policy: abelian, cyclic, monster, oc, star, wreath.

## Two families

The four instances split into two families with different randomization mechanisms and a
shared secrecy spine.

| Instance | Secret | Randomization | View-level secrecy today | Uses `RandomizedSharing` |
|---|---|---|---|---|
| s5 | position `'I_5` | additive mask | to build | yes |
| s5x5 | product of two sum-mod | additive masks | to build | yes |
| den Boer | bool `a && b` | uniform cyclic cut | proven (`five_card_leakage.v`) | no |
| kim | bool | cyclic cut `<[fc_sigma]>` | to build | no |

The mechanisms are genuinely different: a one-time-pad additive mask versus a uniform
cyclic cut. They share only the trace bridge.

## Architecture

Naming follows the local idiom: unprefixed CamelCase records, `Mk<Name>` constructors,
lowercase-initial field prefixes. The structure mirrors `AlgebraicRigidity`
(`algebraic_rigidity.v:187`), a wrapper record over sub-witnesses with smart constructors.

### Records and the family wrapper

`RandomizedSharing` carries the additive-family randomness assumptions, the local rendering
of SPP's `scalar_product_random_inputs`.

    Record RandomizedSharing := MkRandomizedSharing {
      rsh_secret     : {RV P -> 'Z_N} ;
      rsh_mask       : 'I_(T-1) -> {RV P -> 'Z_N} ;
      rsh_mask_unif  : forall j, `p_ (rsh_mask j) = fdist_uniform card_ZN ;
      rsh_mask_indep : (* each mask independent of the secret and the other masks *) }.

`LeakageWitness` is the common interface the trace bridge consumes. It is named to avoid
collision with the existing `SecurityWitness`, which is the unrelated monodromy var-dist
bound.

    Record LeakageWitness := MkLeakageWitness {
      lw_secret : {RV P -> secretT} ;
      lw_view   : {RV P -> viewT} ;
      lw_indep  : P |= lw_view _|_ lw_secret }.

`SharingMechanism` is the family marker. Each instance is exactly one family, so a variant
is the natural wrapper.

    Variant SharingMechanism :=
      | Additive  of RandomizedSharing
      | CyclicCut of CyclicCutData.

    Definition mechanism_leakage : SharingMechanism -> LeakageWitness :=
      fun m => match m with
        | Additive rs  => additive_leakage rs
        | CyclicCut cc => cyclic_cut_leakage cc end.

`CyclicCutData` is thin: the cut group, its uniformity, and the proven `ViewA _|_ Secret`.
For den Boer it wraps the existing `leak_k1`.

### Theorem chain

The chain factors into a family-specific head and a generic tail.

Head, family-specific, the only place the families differ. It produces `P |= view _|_ Secret`.

    additive_view_indep   : from RandomizedSharing via lemma_3_5'   (* s5, s5x5 *)
    cyclic_cut_view_indep : from cyclic-cut uniformity              (* den Boer reuses leak_k1; kim new *)

Tail, generic, identical statements for all four.

    leakage_of_view_indep : P |= view _|_ Secret ->
                            `I(Secret; view) = 0 /\ `H(Secret | view) = `H `p_ Secret.

    trace_secrecy : (trace = f `o view) -> P |= view _|_ Secret ->
                    `H(Secret | trace) = `H `p_ Secret.

Per-instance final theorem, same shape for all four.

    <inst>_trace_secrecy : `H(Secret | observer_trace) = `H `p_ Secret.

`leakage_of_view_indep` is the family-agnostic `leak_k1` template (chain_rule_RV,
joint_entropy_RVC, inde_RV_joint_entropyE, mutual_info_RVE). `trace_secrecy` is the SPP
`alice_traces_entropy` transport via `centropy_RV_contraction`.

### Trace bridge

`run_interp` returns per-party traces; `player_idx i = i.+2`. The observer trace is a
sub-threshold projection `nth ... (run_interp ...).2 (player_idx i)`, the analogue of SPP's
`alice_traces = (fun t => tnth t 0) `o ...`. The per-instance trace-ok lemma states the
projected trace equals a function of the sub-threshold view:

    <inst>_trace_ok : observer_trace = trace_of `o view.

It is established by running `interp` symbolically, the technique already used by
`s5_run_recovers` and SPP's `smc_scalar_product_traces_ok`, abstracting explosive leaves
(perms, enum, decode) into variables so reduction stays atomic.

For the card family the observer view must stay sub-threshold: the full reveal determines
the secret (`leak_k5`), so the bridge connects to a single-player or sub-threshold-coalition
view, where `leak_k1` gives independence.

## File layout

| File | Contents |
|---|---|
| `pgg-smc/security/pgg_randomized_sharing.v` | `RandomizedSharing`, `additive_view_indep` (T-of-T), `additive_leakage`. Imports infotheo plus `spp_proba`, `spp_entropy`. |
| `pgg-smc/security/pgg_leakage_bridge.v` | `LeakageWitness`, `SharingMechanism`, `mechanism_leakage`, `leakage_of_view_indep`, `trace_secrecy`. Imports follow `spp_proof.v` (interpreter plus entropy). |
| `pgg-smc/instances/<inst>/<inst>_secrecy.v` (x4) | the instance's `SharingMechanism` value, its trace-ok lemma, and `<inst>_trace_secrecy`. |

The retained seed `du2002/_probe_c_pgg_secrecy.v` is the basis for `additive_view_indep`; its
content moves into `pgg_randomized_sharing.v` and the `du2002` copy is deleted in the first
implementation step.

## Per-instance instantiation

- s5: `Additive` over `sum_mod_scheme 3 4`. Build `RandomizedSharing`, apply
  `additive_view_indep` at the sub-threshold coalition, prove `s5_trace_ok`, conclude.
- s5x5: `Additive` over `product_scheme (sum_mod_scheme 3 4) (sum_mod_scheme 3 4)`.
  Instantiate `RandomizedSharing` on each of the two sum-mod components and combine through
  the existing `product_scheme` structure, so the product reuses the component head rather
  than reproving independence at the product level. A coalition below the product threshold
  `min(k1, k2)` is sub-threshold on each component, which supplies a one-time pad on each.
- den Boer: `CyclicCut` wrapping the existing `leak_k1` as the `LeakageWitness`, then prove
  `denboer_trace_ok` and conclude. No new view-level proof.
- kim: `CyclicCut`. New `cyclic_cut_view_indep` for kim's cut group `<[fc_sigma]>`, adapting
  the den Boer counting argument, then `kim_trace_ok` and conclude.

## Risks and mitigations

1. Additive head T-of-T generalization. The unseen coordinate of a coalition with `|C| < T`
   is the one-time pad. Mitigation: `lemma_3_5'` applies with the unseen coordinate as `Z`,
   structurally identical to the proven T = 2 case.
2. kim cyclic-cut head. New counting over kim's five-rotation cut. Mitigation: the den Boer
   `leak_k1` proof is the template; kim's cut group is `<[fc_sigma]>`.
3. Symbolic `interp` in the trace-ok lemmas. Mitigation: precedent in `s5_run_recovers` and
   `smc_scalar_product_traces_ok`; abstract explosive leaves into variables.
4. Import combination of interpreter and entropy. Mitigation: `spp_proof.v` already combines
   them; mirror its import set.
5. Correctness is untouched. Randomized shares still reconstruct because the sum is
   word-independent, so existing `*_run_recovers` proofs are not disturbed; secrecy is purely
   additive on top.

## Verification criteria

- All new lemmas reach `Qed` with no `Admitted`, no custom axiom beyond the standard `boolp`
  classical axioms already pervasive in the codebase.
- Records parity: each of the four instances carries its `SharingMechanism` value and its
  `<inst>_trace_secrecy` theorem in a persisted file, matching siblings.
- The headline `<inst>_trace_secrecy : H(Secret | observer_trace) = H(Secret)` holds for all
  four instances through the single generic `trace_secrecy`.

## Non-goals

- No change to the existing correctness or reconstruction proofs.
- No general representation-theoretic G-invariant secret-sharing theorem; the design assembles
  the additive linearity results and the cyclic-cut counting separately, as the literature note
  records.
- No partial-erasure or dropout decoder; reconstruction still consumes the full share tuple.
