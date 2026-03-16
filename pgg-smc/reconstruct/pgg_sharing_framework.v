(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG-SMC: Abstract Secret Sharing Framework                                 *)
(*                                                                            *)
(* The PGG-SMC framework has two orthogonal layers: security (monodromy walk) *)
(* and threshold (secret sharing). This file makes the threshold layer        *)
(* abstract via a ThresholdScheme interface and a compatibility predicate that *)
(* links it to the monodromy representation.                                  *)
(*                                                                            *)
(* Design rationale — why axiomatize:                                         *)
(*   The reconstruction correctness theorem and the security-threshold        *)
(*   tradeoff (in cover_tradeoff.v) depend only on three properties of the   *)
(*   sharing scheme: correctness (ts_correct), privacy (ts_private), and     *)
(*   compatibility with monodromy (ts_perm_compatible). These properties     *)
(*   hold for any AG code on any curve of any genus, so the proofs are       *)
(*   parametric in ThresholdScheme. Concrete curve arithmetic is unnecessary.*)
(*                                                                            *)
(* Section 1 -- Abstract interface:                                           *)
(*   ThresholdScheme secretT shareT == record bundling:                       *)
(*     - T parties, k threshold                                               *)
(*     - validity predicate, reconstruction function                          *)
(*     - correctness and privacy axioms                                        *)
(*                                                                            *)
(* Section 2 -- Compatibility:                                                *)
(*   ts_perm_compatible perm ts == reordering shares by perm g preserves     *)
(*     reconstruction. Satisfiable for monodromy groups (coordinate perm).   *)
(*                                                                            *)
(* Section 3 -- Sum-mod-N instance:                                           *)
(*   sum_mod_scheme N' T' == ThresholdScheme wrapping existing sum-mod-N      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sum_mod.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Abstract Secret Sharing Scheme                              *)
(******************************************************************************)

Record ThresholdScheme (secretT shareT : Type) := MkThresholdScheme {
  ts_T' : nat ;
  ts_k' : nat ;
  ts_valid : secretT -> ts_T'.+1.-tuple shareT -> Prop ;
  ts_recon : ts_T'.+1.-tuple shareT -> secretT ;
  ts_correct : forall (s : secretT) (shares : ts_T'.+1.-tuple shareT),
    ts_valid s shares ->
    ts_recon shares = s ;
  ts_private : forall (s1 s2 : secretT) (shares : ts_T'.+1.-tuple shareT)
    (C : {set 'I_ts_T'.+1}),
    #|C| < ts_k'.+1 ->
    ts_valid s1 shares ->
    exists shares' : ts_T'.+1.-tuple shareT,
      ts_valid s2 shares' /\
      (forall i : 'I_ts_T'.+1, i \in C -> tnth shares' i = tnth shares i) ;
}.

Arguments ts_T' {secretT shareT}.
Arguments ts_k' {secretT shareT}.
Arguments ts_valid {secretT shareT}.
Arguments ts_recon {secretT shareT}.
Arguments ts_correct {secretT shareT}.
Arguments ts_private {secretT shareT}.

Definition ts_T {sT shT : Type} (ts : ThresholdScheme sT shT) : nat :=
  (ts_T' ts).+1.

Definition ts_k {sT shT : Type} (ts : ThresholdScheme sT shT) : nat :=
  (ts_k' ts).+1.

(******************************************************************************)
(*     Section 2: Coordinate-Permutation Compatibility                        *)
(******************************************************************************)

Section compatibility.

Variables (gT : finGroupType) (G : {group gT}).
Variables (secretT shareT : Type).
Variable ts : ThresholdScheme secretT shareT.

Let T := (ts_T' ts).+1.

(* Coordinate-permutation compatibility: reordering shares by perm g
   preserves reconstruction. This IS satisfiable for monodromy groups,
   unlike value-transformation compatibility (which is not). *)
Definition ts_perm_compatible (perm : gT -> {perm 'I_T}) : Prop :=
  forall (g : gT) (s : secretT) (shares : T.-tuple shareT),
    g \in G ->
    ts_valid ts s shares ->
    ts_recon ts [tuple tnth shares (perm g i) | i < T] = s.

End compatibility.

Arguments ts_perm_compatible {gT G secretT shareT}.

(******************************************************************************)
(*     Section 3: Sum-mod-N Instance                                          *)
(******************************************************************************)

Section sum_mod_instance.

Variable N' : nat.
Let N := N'.+2.

Variable T' : nat.
Let T := T'.+1.

(* Reconstruction: compute the sum of all share values mod N *)
Definition sum_mod_recon (shares : T.-tuple 'I_N) : 'I_N :=
  Ordinal (ltn_pmod (\sum_(i < T) (tnth shares i : nat)) (isT : 0 < N)).

(* Validity: the sum of share values mod N equals the secret *)
Definition sum_mod_valid_pred (s : 'I_N) (shares : T.-tuple 'I_N) : Prop :=
  (\sum_(i < T) (tnth shares i : nat)) %% N = s :> nat.

Lemma sum_mod_scheme_correct (s : 'I_N) (shares : T.-tuple 'I_N) :
  sum_mod_valid_pred s shares ->
  sum_mod_recon shares = s.
Proof.
rewrite /sum_mod_valid_pred /sum_mod_recon => Hvalid.
by apply: val_inj.
Qed.

Lemma sum_mod_scheme_private (s1 s2 : 'I_N)
    (shares : T.-tuple 'I_N) (C : {set 'I_T}) :
  #|C| < T ->
  sum_mod_valid_pred s1 shares ->
  exists shares' : T.-tuple 'I_N,
    sum_mod_valid_pred s2 shares' /\
    (forall i : 'I_T, i \in C -> tnth shares' i = tnth shares i).
Proof.
move=> HC Hvalid.
have Hpsni := @partial_sum_no_info N' T' shares (1 : {perm 'I_N}) C s1 s2 HC.
have Hvalid' : sum_mod_valid shares s1 by rewrite /sum_mod_valid /sheets_sum.
have [shares' [Hv' [Hagree _]]] := Hpsni Hvalid'.
exists shares'; split; last exact: Hagree.
by rewrite /sum_mod_valid_pred /sheets_sum.
Qed.

Definition sum_mod_scheme : ThresholdScheme 'I_N 'I_N :=
  @MkThresholdScheme 'I_N 'I_N T' T'
    sum_mod_valid_pred
    sum_mod_recon
    sum_mod_scheme_correct
    sum_mod_scheme_private.

End sum_mod_instance.

Arguments sum_mod_scheme {N' T'}.

(******************************************************************************)
(*     Section 4: Protocol Integration                                        *)
(******************************************************************************)

(* Helper: cast a tuple when the size index changes *)
Definition cast_tuple {A : Type} {n m : nat} (H : n = m)
    (t : n.-tuple A) : m.-tuple A :=
  eq_rect n (fun k => k.-tuple A) t m H.

Lemma tnth_cast_tuple {A : Type} {n m : nat} (H : n = m)
    (t : n.-tuple A) (i : 'I_m) :
  tnth (cast_tuple H t) i = tnth t (cast_ord (esym H) i).
Proof.
subst m.
by rewrite /cast_tuple /= cast_ord_id.
Qed.

Section pgg_protocol_secret.

Variable M : MonodromyReprType.
Variable PI : PGGInterface M.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.

Variable ts : ThresholdScheme 'I_N 'I_N.
Hypothesis HT : ts_T' ts = pi_T' PI.

Let sT := (ts_T' ts).+1.

(* Cast endpoints to the scheme's tuple type *)
Definition pgg_recon (eps : T.-tuple 'I_N) : 'I_N :=
  ts_recon ts (cast_tuple (esym (congr1 S HT)) eps).

(* The secret reconstructed from endpoints *)
Definition pgg_recon_endpoints (P : gT) : 'I_N :=
  pgg_recon [tuple rho P (tnth starts i) | i < T].

(* Main theorem: coordinate-permutation compatible scheme + G-stable starts
   + valid starting shares ⟹ reconstruction of endpoints recovers the secret *)
Lemma pgg_secret_invariant_perm (s : 'I_N) (P : gT)
    (perm : gT -> {perm 'I_sT})
    (G_stable : forall g, g \in pgg_G M ->
       forall i : 'I_sT, rho g (tnth (cast_tuple (esym (congr1 S HT)) starts) i) =
                          tnth (cast_tuple (esym (congr1 S HT)) starts) (perm g i)) :
  P \in pgg_G M ->
  ts_valid ts s (cast_tuple (esym (congr1 S HT)) starts) ->
  @ts_perm_compatible gT (pgg_G M) _ _ ts perm ->
  pgg_recon_endpoints P = s.
Proof.
move=> PG Hvalid Hperm.
rewrite /pgg_recon_endpoints /pgg_recon.
have -> : cast_tuple (esym (congr1 S HT))
            [tuple rho P (tnth starts i) | i < T] =
          [tuple tnth (cast_tuple (esym (congr1 S HT)) starts) (perm P i) | i < sT].
  apply: eq_from_tnth => i.
  rewrite tnth_cast_tuple !tnth_mktuple.
  rewrite -(G_stable P PG i).
  congr (rho P _).
  by rewrite tnth_cast_tuple.
exact: Hperm PG Hvalid.
Qed.

End pgg_protocol_secret.
