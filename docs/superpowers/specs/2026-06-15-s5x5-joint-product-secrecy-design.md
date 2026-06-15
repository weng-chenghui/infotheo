# s5x5 joint product secrecy

Date: 2026-06-15

Follow-on to the view-secrecy framework and the concrete additive sampler (item 1). This is
item 2 of the post-landing backlog: the s5x5 joint product secrecy.

## Problem

The current `s5x5_view_secrecy_concrete` is per-component: each 5-of-5 component's sub-threshold
view is independent of that component's own secret. It does not state that the COMBINED view
(across both components) is independent of the JOINT secret `(s1, s2)`. The per-component form is
also degenerate for the joint, since it uses the same sampler twice, which would force `s1 = s2`.
We want the unconditional joint statement: the combined coalition view reveals nothing about the
pair of secrets.

## Feasibility basis (established)

A throwaway probe proved the combinator, axiom-clean, via a direct pointwise (`pfwd1`) route:

    joint_view_indep : P |= V1 _|_ S1 -> P |= V2 _|_ S2 ->
                       P |= [% V1, S1] _|_ [% V2, S2] ->
                       P |= [% V1, V2] _|_ [% S1, S2].

The third hypothesis is the defining property of a product scheme: the two components run on
independent randomness. The graphoid route structurally cycles back to the goal; the pointwise
route (transpose the preimage `((v1,v2),(s1,s2))` to `((v1,s1),(v2,s2))`, factor by the three
hypotheses and the derived `V1 _|_ V2`, `S1 _|_ S2`, recombine with `mulrACA`) closes it.

The two product-distribution helpers are standard infotheo facts: `Pr_fdist_prod` (proba.v:453)
gives event-level fst-vs-snd independence over `P1 `x P2`, and `Pr_fdist_fst` / `fdist_prod1` give
the marginal transport. The sampler probe's `headtail_inde` is already the fst-vs-snd pattern.

## Scope

The unconditional concrete joint for s5x5. The two components run on independent uniform tapes,
realized as the two factors of a product distribution `P1 `x P2`.

## Architecture

### File: `pgg-smc/security/pgg_leakage_product.v`

Three lemmas and a combinator. Imports infotheo (`fdist`, `proba`, `graphoid`), `spp_proba` for
`inde_RV_comp`, and `pgg_leakage_witness`.

    (* the proven combinator core *)
    joint_view_indep : P |= V1 _|_ S1 -> P |= V2 _|_ S2 ->
                       P |= [% V1, S1] _|_ [% V2, S2] -> P |= [% V1, V2] _|_ [% S1, S2].

    (* helper (a): a function of fst is independent of a function of snd over a product *)
    inde_RV_fst_snd (f : A -> TB1) (g : B -> TB2) :
      (P1 `x P2) |= ((fun ab => f ab.1) : {RV _ -> TB1}) _|_ ((fun ab => g ab.2) : {RV _ -> TB2}).

    (* helper (b): independence transports along the fst (and snd) projection *)
    inde_RV_fst (X : {RV P1 -> TB1}) (Y : {RV P1 -> TB2}) :
      P1 |= X _|_ Y ->
      (P1 `x P2) |= ((fun ab => X ab.1) : {RV _ -> TB1}) _|_ ((fun ab => Y ab.1) : {RV _ -> TB2}).
    inde_RV_snd (X : {RV P2 -> TB1}) (Y : {RV P2 -> TB2}) :
      P2 |= X _|_ Y ->
      (P1 `x P2) |= ((fun ab => X ab.2) : {RV _ -> TB1}) _|_ ((fun ab => Y ab.2) : {RV _ -> TB2}).

    (* the LeakageWitness-level product, baking in the construction *)
    leakage_product (lw1 : LeakageWitness P1) (lw2 : LeakageWitness P2) : LeakageWitness (P1 `x P2).

`leakage_product`'s witness has secret `[% lw_secret lw1 `o fst, lw_secret lw2 `o snd]` and view
`[% lw_view lw1 `o fst, lw_view lw2 `o snd]`. Its independence field is `joint_view_indep` applied
to: `lw_indep lw1` transported by `inde_RV_fst`, `lw_indep lw2` transported by `inde_RV_snd`, and
the cross-independence `[%V1,S1] `o fst _|_ [%V2,S2] `o snd` from `inde_RV_fst_snd`.

### Edit: `pgg-smc/instances/s5x5/s5x5_secrecy.v`

    s5x5_joint_view_secrecy : forall (C1 C2 : {set 'I_5}) (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N),
      let lw := leakage_product (mechanism_leakage (Additive (unif_randomized_sharing) HC1))
                                (mechanism_leakage (Additive (unif_randomized_sharing) HC2)) in
      `I( lw_secret lw ; lw_view lw ) = 0 /\ `H( lw_secret lw | lw_view lw ) = `H `p_ (lw_secret lw).

Proof: `apply: leakage_of_view_indep; exact: lw_indep _`. The two components are the same uniform
sampler placed on the two independent factors of the product, so their secrets are genuinely
distinct random variables.

## Component boundaries

`pgg_leakage_product.v` is generic over any two `LeakageWitness`es; it has no s5x5 or `'Z_N`
specifics. The s5x5 edit instantiates it with the concrete uniform sampler. `joint_view_indep`,
`inde_RV_fst_snd`, `inde_RV_fst`/`inde_RV_snd` are independently reusable.

## Risks and mitigations

1. `inde_RV_fst_snd`. Mitigation: adapt the sampler probe's `headtail_inde` proof
   (`Pr_fdist_prod_of_rV1/2` becomes `Pr_fdist_fst`/`Pr_fdist_snd`; the `setX = _ `*T :&: T`* _`
   rewrite and `Pr_fdist_prod` finish are identical).
2. `inde_RV_fst`/`inde_RV_snd`. Mitigation: `[%X,Y] `o fst` has the same law over `P1 `x P2` as
   `[%X,Y]` over `P1` because `(P1 `x P2)`1 = P1` (`fdist_prod1`); push `pfwd1` through `Pr_fdist_fst`.
3. `leakage_product` constructor unification (the `LeakageWitness` heterogeneous-type packing).
   Mitigation: destructure both witnesses (`let: MkLeakageWitness .. := lw1 in ...`) as the
   `cyclic_cut_leakage` definition does, to avoid the projection metavar.

## Verification criteria

- All lemmas reach `Qed` with no `Admitted`, no custom axiom beyond the standard `boolp` axioms.
- `s5x5_joint_view_secrecy` is unconditional (no `Hcross` hypothesis), with `Print Assumptions` clean.
- The joint secret `[% s1, s2]` is a genuine pair of distinct random variables (the two factors),
  not a degenerate `[% s, s]`.

## Non-goals

- The executed-trace bridge stays deferred.
- No general n-fold product, only the two-component s5x5 joint.
- `joint_view_indep` and the product helpers are stated for two components; no associativity or
  general-arity combinator.
