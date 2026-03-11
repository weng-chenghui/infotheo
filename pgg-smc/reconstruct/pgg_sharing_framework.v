(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG-SMC: Abstract Secret Sharing Framework                                 *)
(*                                                                            *)
(* The PGG-SMC framework has two orthogonal layers: security (monodromy walk) *)
(* and threshold (secret sharing). This file makes the threshold layer        *)
(* abstract via a SharingScheme interface and a compatibility predicate that   *)
(* links it to the monodromy representation.                                  *)
(*                                                                            *)
(* Section 1 -- Abstract interface:                                           *)
(*   SharingScheme secretT shareT == record bundling:                         *)
(*     - T parties, k threshold                                               *)
(*     - validity predicate, reconstruction function                          *)
(*     - correctness and privacy axioms                                        *)
(*                                                                            *)
(* Section 2 -- Compatibility:                                                *)
(*   rss_compatible act rss == a group action on shares is compatible with    *)
(*     sharing scheme: acting on shares preserves reconstruction              *)
(*                                                                            *)
(* Section 3 -- Sum-mod-N instance:                                           *)
(*   sum_mod_scheme N' T' == SharingScheme wrapping existing sum-mod-N        *)
(*   sum_mod_compatible == preserves_sum_mod implies compatibility            *)
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

Record SharingScheme (secretT shareT : Type) := MkSharingScheme {
  sharing_T' : nat ;
  sharing_k' : nat ;
  sharing_valid : secretT -> sharing_T'.+1.-tuple shareT -> Prop ;
  sharing_reconstruct_all : sharing_T'.+1.-tuple shareT -> secretT ;
  sharing_correct : forall (s : secretT) (shares : sharing_T'.+1.-tuple shareT),
    sharing_valid s shares ->
    sharing_reconstruct_all shares = s ;
  sharing_private : forall (s1 s2 : secretT) (shares : sharing_T'.+1.-tuple shareT)
    (C : {set 'I_sharing_T'.+1}),
    #|C| < sharing_k'.+1 ->
    sharing_valid s1 shares ->
    exists shares' : sharing_T'.+1.-tuple shareT,
      sharing_valid s2 shares' /\
      (forall i : 'I_sharing_T'.+1, i \in C -> tnth shares' i = tnth shares i) ;
}.

Arguments sharing_T' {secretT shareT}.
Arguments sharing_k' {secretT shareT}.
Arguments sharing_valid {secretT shareT}.
Arguments sharing_reconstruct_all {secretT shareT}.
Arguments sharing_correct {secretT shareT}.
Arguments sharing_private {secretT shareT}.

Definition sharing_T {sT shT : Type} (rss : SharingScheme sT shT) : nat :=
  (sharing_T' rss).+1.

Definition sharing_k {sT shT : Type} (rss : SharingScheme sT shT) : nat :=
  (sharing_k' rss).+1.

(******************************************************************************)
(*     Section 2: Compatibility with a Group Action                           *)
(******************************************************************************)

Section compatibility.

Variables (gT : finGroupType) (G : {group gT}).
Variables (secretT shareT : Type).
Variable rss : SharingScheme secretT shareT.

Let T := (sharing_T' rss).+1.

(* A group action on shares is compatible with the sharing scheme if
   applying any g in G to each share preserves reconstruction. *)
Definition rss_compatible (act : gT -> shareT -> shareT) : Prop :=
  forall (g : gT) (s : secretT) (shares : T.-tuple shareT),
    g \in G ->
    sharing_valid rss s shares ->
    sharing_reconstruct_all rss
      [tuple act g (tnth shares i) | i < T] = s.

(* Compatibility with identity action is trivially satisfied *)
Lemma rss_compatible_id :
  rss_compatible (fun _ x => x).
Proof.
move=> g s shares gG Hvalid.
have -> : [tuple (fun (_ : gT) (x : shareT) => x) g (tnth shares i) | i < T] = shares.
  apply: eq_from_tnth => i.
  by rewrite tnth_mktuple.
exact: sharing_correct Hvalid.
Qed.

End compatibility.

Arguments rss_compatible {gT G secretT shareT}.

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

Definition sum_mod_scheme : SharingScheme 'I_N 'I_N :=
  @MkSharingScheme 'I_N 'I_N T' T'
    sum_mod_valid_pred
    sum_mod_recon
    sum_mod_scheme_correct
    sum_mod_scheme_private.

End sum_mod_instance.

Arguments sum_mod_scheme {N' T'}.

(******************************************************************************)
(*     Section 4: Sum-mod-N Compatibility                                     *)
(******************************************************************************)

Section sum_mod_compatibility.

Variable N' : nat.
Let N := N'.+2.

Variable T' : nat.
Let T := T'.+1.

(* If a permutation preserves sum mod N, then applying it to shares
   is compatible with the sum-mod-N scheme *)
Lemma sum_mod_compatible (gT : finGroupType) (G : {group gT})
    (act : gT -> 'I_N -> 'I_N) :
  (forall g : gT, g \in G ->
    forall (s : T.-tuple 'I_N),
      (\sum_(i < T) (act g (tnth s i) : nat)) %% N =
      (\sum_(i < T) (tnth s i : nat)) %% N) ->
  @rss_compatible gT G _ _ (@sum_mod_scheme N' T') act.
Proof.
move=> Hpres g s shares gG Hvalid.
rewrite /= /sum_mod_recon.
apply: val_inj => /=.
have -> : \sum_(i < T) (tnth [tuple act g (tnth shares i) | i < T] i : nat) =
          \sum_(i < T) (act g (tnth shares i) : nat).
  by apply: eq_bigr => i _; rewrite tnth_mktuple.
by rewrite Hpres.
Qed.

End sum_mod_compatibility.

(******************************************************************************)
(*     Section 5: Integration with PGG Monodromy                              *)
(******************************************************************************)

Section pgg_compatibility.

Variable N' : nat.
Let N := N'.+2.

Variable T' : nat.
Let T := T'.+1.

Variable M : MonodromyReprType.
Hypothesis HN : (pgg_N' M).+1 = N.

Let gT := pgg_gT M.
Let G := pgg_G M.
Let rho := @pgg_rho M.

(* The monodromy action on 'I_N, cast from 'I_(pgg_N' M).+1 *)
Definition rho_act (g : gT) (x : 'I_N) : 'I_N :=
  cast_ord HN (rho g (cast_ord (esym HN) x)).

Lemma rho_act_val (g : gT) (x : 'I_N) :
  val (rho_act g x) = val (rho g (cast_ord (esym HN) x)).
Proof. by []. Qed.

(* If rho preserves sum mod N, the sum-mod-N scheme is compatible *)
Lemma pgg_sum_mod_compatible :
  (forall g : gT, g \in G ->
    forall (s : T.-tuple 'I_N),
      (\sum_(i < T) (rho_act g (tnth s i) : nat)) %% N =
      (\sum_(i < T) (tnth s i : nat)) %% N) ->
  @rss_compatible gT G _ _ (@sum_mod_scheme N' T') rho_act.
Proof. exact: sum_mod_compatible. Qed.

End pgg_compatibility.
