# Concrete additive sampler: an inhabitation witness for RandomizedSharing

Date: 2026-06-15

Follow-on to `docs/superpowers/specs/2026-06-14-randomized-sharing-trace-secrecy-design.md`
and its landed implementation (commits fb2e749..a3ac34a). This is item 1 of the post-landing
backlog.

## Problem

The s5 and s5x5 instance theorems (`s5_view_secrecy`, `s5x5_view_secrecy`) are parameterized
by an abstract `RandomizedSharing` record. Nothing yet proves the record is inhabited, so the
secrecy theorems, while true, are not known to be non-vacuous: a contradictory set of assumed
independences would make `additive_view_indep` vacuously provable. We build one concrete
inhabitant. This discharges the assumptions from an actual distribution, and it lets s5 and
s5x5 state secrecy unconditionally.

This is beyond what the Du-Atallah scalar-product proof does. Its `scalar_product_random_inputs`
is also an assumed record over an abstract distribution, never inhabited. The added value here
is the consistency witness.

## Feasibility basis (established)

A throwaway probe (`pgg-smc/security/_probe_sampler.v`, retained as a seed) proved, with no
custom axiom, all three record fields at `T' = 2` over the iid uniform tape `'rV['Z_N]_3`,
including the hard field: a middle coordinate is independent of the bundle of the other two.
The mechanism is three reusable facts plus a transposition:

- the iid product is invariant under any coordinate permutation,
- the head coordinate is independent of the tail vector,
- independence is preserved when both random variables are precomposed with a coordinate
  permutation,

so coordinate `k` is independent of the rest by transposing `k` into the head. The remaining
work is generalizing the size-3 proofs to `'rV_(T'.+1)` and expressing the field bundles as
the complementary coordinates. This is index and ffun bookkeeping, not a feasibility risk.

## Scope

Build a concrete inhabitant for general `T'` and wire it into s5 and s5x5. If the general-`T'`
bookkeeping unexpectedly fights, fall back to a fixed `T' = 4` inhabitant, which still covers
both instances (both use `sum_mod_scheme 3 4`).

## Architecture

### File 1: `pgg-smc/security/pgg_fdist_rV_indep.v`

Coordinate-independence facts for the iid product distribution `P ^ n` (infotheo `fdist_rV`),
generalizing the seed lemmas. Names follow infotheo's `prod_dist_inde_RV_rV` / `fdist_nth` /
`fdist_perm` / `inde_RV` / `col_perm` family.

    fdist_perm_rV  : forall (s : {perm 'I_n}), fdist_perm (P0 `^ n) s = P0 `^ n.
    inde_RV_head_rV : P0 `^ n.+1 |= (g1 `o head) _|_ (g2 `o tail).
    inde_RV_col_perm : P0 `^ n |= A _|_ B ->
                       P0 `^ n |= (A `o col_perm s) _|_ (B `o col_perm s).
    inde_RV_nth_rV : P0 `^ n |= (nth-coordinate i) _|_ (post-processing of the other coordinates).
    fdist_nth_unif : fdist_nth (P0 `^ n) i = P0.

`inde_RV_head_rV` generalizes infotheo's `prod_dist_inde_RV_rV` to arbitrary post-processing
on both sides. `inde_RV_nth_rV` is derived from `fdist_perm_rV` + `inde_RV_col_perm` +
`inde_RV_head_rV` by transposing coordinate `i` to the head.

### File 2: `pgg-smc/security/pgg_canonical_sharing.v`

The concrete inhabitant over the uniform iid tape.

    Let N := N'.+2.  Let card_ZN : #|'Z_N| = N'.+1.+1 := card_ord _.
    Let P0 := fdist_uniform card_ZN.
    Let P  := P0 `^ T'.+1.                       (* Omega = 'rV['Z_N]_(T'.+1) *)
    Definition unif_secret : {RV P -> 'Z_N} := fun v => v ord0 ord0.
    Definition unif_mask (k : 'I_T') : {RV P -> 'Z_N} := fun v => v ord0 (lift ord0 k).
    Definition unif_randomized_sharing : RandomizedSharing P N' T' :=
      MkRandomizedSharing unif_secret unif_mask
        unif_mask_unif unif_masks_indep unif_mask_indep.

The three field obligations `unif_mask_unif`, `unif_masks_indep`, `unif_mask_indep` are
discharged as:

- `rsh_mask_unif k` from `fdist_nth_unif` (mask `k` is coordinate `lift ord0 k`).
- `rsh_masks_indep` from `inde_RV_head_rV` (the secret is the head, the mask vector is a
  function of the tail).
- `rsh_mask_indep k` from `inde_RV_nth_rV` at coordinate `lift ord0 k` (the bundle
  `[secret, othermasks k]` is a post-processing of the complementary coordinates).

### Edits: `s5_secrecy.v`, `s5x5_secrecy.v`

Add unconditional concrete theorems using `unif_randomized_sharing`, keeping the existing
abstract versions. Each has the same conjunction shape as its existing `<inst>_view_secrecy`
(`I(Secret; view) = 0` and `H(Secret | view) = H(Secret)`), with the abstract `rs` replaced by
`unif_randomized_sharing` at the instance dimensions, so no `RandomizedSharing` hypothesis remains.

    s5_view_secrecy_concrete   : forall (C : {set 'I_5}) (HC : (#|C| < 5)%N),
      <conjunction> for (mechanism_leakage (Additive (unif_randomized_sharing (N':=3) (T':=4)) HC)).
    s5x5_view_secrecy_concrete : the same conjunction on each of two unif_randomized_sharing
      components, matching the per-component shape of the existing s5x5_view_secrecy.

## Component boundaries

`pgg_fdist_rV_indep.v` depends only on infotheo (`fdist`, `proba`, plus `matrix`, `perm` for
`col_perm`, `ssralg_ext` for `rbehead`). It is generic, with no PGG or `'Z_N` specifics.
`pgg_canonical_sharing.v` instantiates it at `'Z_N` and packages the record. The instance
edits depend on both plus the existing `pgg_sharing_mechanism.v`.

## Risks and mitigations

1. General-`T'` index arithmetic (`lift ord0 k`, transposition `tperm ord0 (lift ord0 k)`).
   Mitigation: the seed proves the mechanism; generalize coordinate by coordinate. Fallback:
   fixed `T' = 4`.
2. Expressing `othermasks k` (an ffun over `'I_T'` zeroed at `k`) as a post-processing of the
   complementary tape coordinates. Mitigation: the seed's `bundle_premap` does this for the
   pair case; the general case is the same construction over the ffun.
3. `'Z_N` and `fdist_rV` interaction. The probe confirmed `zmodp` plays well with `P ^ n` and
   `prod_dist_inde_RV_rV`.

## Verification criteria

- All lemmas reach `Qed` with no `Admitted`, no custom axiom beyond the standard `boolp`
  classical axioms.
- `unif_randomized_sharing : RandomizedSharing (P0 `^ T'.+1) N' T'` typechecks with all three
  fields proven, confirming `RandomizedSharing` is non-vacuous.
- `s5_view_secrecy_concrete` and `s5x5_view_secrecy_concrete` are unconditional (no abstract
  `RandomizedSharing` hypothesis) and compile, with `Print Assumptions` clean.

## Non-goals

- The executed-trace bridge stays deferred (`project_trace_bridge_deferred`).
- s5x5 joint product secrecy (combined view independent of the joint secret) stays out;
  s5x5 remains per-component.
- No change to `additive_view_indep` or the existing instance theorems; the concrete versions
  are added alongside.
