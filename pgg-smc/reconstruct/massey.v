(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Massey's Secret Sharing from Linear Codes                                  *)
(*                                                                            *)
(* Reference:                                                                 *)
(*   J. L. Massey, "Minimal codewords and secret sharing,"                    *)
(*   in Proc. 6th Joint Swedish-Russian Int. Workshop on Inf. Theory,         *)
(*   Mölle, Sweden, Aug. 1993, pp. 276-279.                                   *)
(*                                                                            *)
(* Given an [n, k, d] linear code C over F_q, Massey's construction defines  *)
(* a secret sharing scheme: for codeword c = (c_0, c_1, ..., c_{n-1}),       *)
(* the secret is c_0 and the shares are (c_1, ..., c_{n-1}).                  *)
(*                                                                            *)
(*   massey_codeword s shares == full codeword from secret s and shares       *)
(*   massey_reconstruct shares == recover secret from all shares (via pick)   *)
(*   massey_secret_unique == d >= 2 implies secret is determined by shares    *)
(*   massey_valid_tuple == validity predicate (full vector is a codeword)     *)
(*   massey_scheme == SharingScheme instance parameterized by dual distance   *)
(*   privacy_surj == surjectivity hypothesis (from dual distance d_perp)     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_reconstruct Require Import pgg_sharing_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Tuple <-> Row Vector Utilities                              *)
(******************************************************************************)

Section tuple_rV.
Variables (F : ringType) (m : nat).

Definition tuple_to_rV (t : m.-tuple F) : 'rV[F]_m :=
  \row_(i < m) tnth t i.

Definition rV_to_tuple (v : 'rV[F]_m) : m.-tuple F :=
  [tuple v ord0 i | i < m].

Lemma rV_to_tupleK (v : 'rV[F]_m) : tuple_to_rV (rV_to_tuple v) = v.
Proof. by apply/rowP => i; rewrite mxE tnth_mktuple. Qed.

Lemma tuple_to_rVK (t : m.-tuple F) : rV_to_tuple (tuple_to_rV t) = t.
Proof.
apply: eq_from_tnth => i.
by rewrite tnth_mktuple mxE.
Qed.

Lemma tuple_to_rV_tnth (t : m.-tuple F) (i : 'I_m) :
  (tuple_to_rV t) ord0 i = tnth t i.
Proof. by rewrite mxE. Qed.

End tuple_rV.

(******************************************************************************)
(*     Section 2: Massey's Secret Sharing Construction                        *)
(******************************************************************************)

Section massey.

Variable F : finFieldType.
Variable n' : nat.
Let n := n'.+2.   (* n >= 3: at least secret + 2 shares *)

Variable C : Lcode0.t F n.
Hypothesis C_not_trivial : not_trivial C.

Let d := min_dist C_not_trivial.
Hypothesis Hd2 : 1 < d.

(* Build the full codeword from secret (position 0) and shares (positions 1..n-1).
   Defined pointwise to avoid row_mx type inference issues. *)
Definition massey_codeword (s : F) (shares : 'rV[F]_n'.+1) : 'rV[F]_n :=
  \row_(i < n) if (i : nat) == 0%N then s else shares ord0 (inord i.-1).

Lemma massey_codeword0 (s : F) (shares : 'rV[F]_n'.+1) :
  (massey_codeword s shares) ord0 ord0 = s.
Proof. by rewrite mxE /=. Qed.

(* Ordinal helper: lift ord0 (inord i.-1) = i when i != 0 *)
Lemma lift_inord (i : 'I_n) : (i : nat) != 0%N ->
  lift (ord0 : 'I_n) (@inord n' i.-1) = i.
Proof.
move=> Hi; apply/val_inj => /=.
rewrite /bump leq0n add1n inordK.
  by rewrite prednK //; case: (val i) Hi.
by case: (val i) Hi (ltn_ord i) => //= k _ /ltnW.
Qed.

Lemma massey_codewordS (s : F) (shares : 'rV[F]_n'.+1) (j : 'I_n'.+1) :
  (massey_codeword s shares) ord0 (lift ord0 j) = shares ord0 j.
Proof.
rewrite mxE /=.
by congr (shares ord0 _); apply/val_inj => /=; rewrite add0n inordK // ltn_ord.
Qed.

(* Any row vector decomposes as massey_codeword of its parts *)
Lemma massey_codeword_decompose (v : 'rV[F]_n) :
  v = massey_codeword (v ord0 ord0) (\row_(j < n'.+1) v ord0 (lift ord0 j)).
Proof.
apply/rowP => i; rewrite mxE.
case Hi : ((i : nat) == 0%N).
- by congr (v ord0 _); apply/val_inj; exact/eqP.
- by rewrite mxE; congr (v ord0 _); rewrite lift_inord // Hi.
Qed.

(* Key uniqueness: if d >= 2, the secret is determined by the shares *)
Lemma massey_secret_unique (s1 s2 : F) (shares : 'rV[F]_n'.+1) :
  massey_codeword s1 shares \in C ->
  massey_codeword s2 shares \in C ->
  s1 = s2.
Proof.
move=> Hc1 Hc2.
set diff := massey_codeword s1 shares - massey_codeword s2 shares.
have HdiffC : diff \in C by rewrite /diff; exact: memvB.
have Hsupp : forall i : 'I_n, (i : nat) != 0%N -> diff ord0 i = 0.
  move=> i Hi; rewrite /diff !mxE (negbTE Hi); exact: subrr.
have HwH1 : wH diff <= 1.
  rewrite -card_wH_supp -(cards1 (ord0 : 'I_n)).
  apply: subset_leq_card; apply/subsetP => i.
  rewrite !inE => Hi.
  case Hi0 : ((i : nat) == 0%N).
    by apply/eqP/val_inj; exact/eqP.
  by exfalso; move/negP: Hi; apply; rewrite Hsupp ?eqxx // Hi0.
have /eqP Hdiff0 : diff == 0.
  apply/negPn/negP => Hne0.
  have : d <= 1 :=
    leq_trans (min_dist_is_min C_not_trivial HdiffC Hne0) HwH1.
  by rewrite leqNgt Hd2.
have := congr1 (fun v : 'rV[F]_n => v ord0 ord0) Hdiff0.
rewrite /diff !mxE /=.
by move/eqP; rewrite subr_eq0 => /eqP.
Qed.

(* Reconstruction: find s0 such that (s0, shares) is a codeword *)
Definition massey_reconstruct (shares : 'rV[F]_n'.+1) : F :=
  odflt 0 [pick s0 : F | massey_codeword s0 shares \in C].

Lemma massey_reconstruct_correct (s : F) (shares : 'rV[F]_n'.+1) :
  massey_codeword s shares \in C ->
  massey_reconstruct shares = s.
Proof.
move=> HC.
rewrite /massey_reconstruct.
case: pickP => [s0 Hs0 | Habs].
- exact: massey_secret_unique Hs0 HC.
- by move: (Habs s); rewrite HC.
Qed.

(******************************************************************************)
(*     Section 3: Privacy from Dual Distance                                  *)
(******************************************************************************)

Section massey_privacy.

Variable d_perp' : nat.
Let d_perp := d_perp'.+2.  (* dual distance >= 2 *)

(* Key privacy hypothesis: for any set S with |S| < d_perp, the coordinate
   projection from C onto S is surjective. This is the content of Massey's
   Theorem 1, derived from the dual code's minimum distance. *)
Hypothesis privacy_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < d_perp ->
    exists c : 'rV[F]_n, c \in C /\ vproj c S = vproj target S.

(* Helper: extract coordinates from vproj equality *)
Lemma vproj_coord_eq (c target : 'rV[F]_n) (S : {set 'I_n}) (i : 'I_n) :
  vproj c S = vproj target S -> i \in S -> c ord0 i = target ord0 i.
Proof.
move=> Hvproj Hi.
have := congr1 (fun v : 'rV[F]_n => v ord0 i) Hvproj.
by rewrite !mxE Hi.
Qed.

(* Index mapping: share position j to codeword position *)
Definition lift_share (j : 'I_n'.+1) : 'I_n := lift ord0 j.

Definition lift_coalition (coal : {set 'I_n'.+1}) : {set 'I_n} :=
  [set lift_share j | j in coal].

Lemma lift_share_inj : injective lift_share.
Proof. exact: lift_inj. Qed.

Lemma lift_coalition_card (coal : {set 'I_n'.+1}) :
  #|lift_coalition coal| = #|coal|.
Proof. by rewrite card_imset //; exact: lift_share_inj. Qed.

Lemma ord0_notin_lift (coal : {set 'I_n'.+1}) :
  (ord0 : 'I_n) \notin lift_coalition coal.
Proof.
apply/negP => /imsetP [j _].
rewrite /lift_share => Habs.
by move/negP: (neq_lift ord0 j); apply; rewrite -Habs.
Qed.

Lemma card_S_bound (coal : {set 'I_n'.+1}) :
  #|coal| < d_perp'.+1 ->
  #|[set ord0 : 'I_n] :|: lift_coalition coal| < d_perp.
Proof.
move=> Hcoal.
rewrite cardsU1 (negbTE (ord0_notin_lift coal)) add1n lift_coalition_card.
by rewrite /d_perp ltnS.
Qed.

(* Main privacy lemma *)
Lemma massey_private (s1 s2 : F) (shares : 'rV[F]_n'.+1)
    (coal : {set 'I_n'.+1}) :
  #|coal| < d_perp'.+1 ->
  massey_codeword s1 shares \in C ->
  exists shares' : 'rV[F]_n'.+1,
    massey_codeword s2 shares' \in C /\
    (forall j : 'I_n'.+1, j \in coal -> shares' ord0 j = shares ord0 j).
Proof.
move=> Hcoal Hvalid.
set S := [set ord0 : 'I_n] :|: lift_coalition coal.
set target := massey_codeword s2 shares.
have HS : #|S| < d_perp by exact: card_S_bound.
have [c [HcC Hvproj]] := privacy_surj target HS.
(* c has s2 at position 0 *)
have Hc0 : c ord0 ord0 = s2.
  have Hord0S : (ord0 : 'I_n) \in S by rewrite /S in_setU1 eqxx.
  by rewrite (vproj_coord_eq Hvproj Hord0S) massey_codeword0.
(* Build shares' from c's tail *)
set shares' : 'rV[F]_n'.+1 := \row_(j < n'.+1) c ord0 (lift ord0 j).
(* c = massey_codeword s2 shares' via decomposition *)
have HcEq : c = massey_codeword s2 shares'.
  rewrite {1}(massey_codeword_decompose c) Hc0 /shares' //.
exists shares'; split.
- by rewrite -HcEq.
- move=> j Hj.
  have HjS : lift_share j \in S.
    rewrite /S in_setU1; apply/orP; right.
    by apply/imsetP; exists j.
  rewrite mxE (vproj_coord_eq Hvproj HjS).
  by rewrite /target massey_codewordS.
Qed.

(******************************************************************************)
(*     Section 4: SharingScheme Instance                                      *)
(******************************************************************************)

Definition massey_valid_tuple (s : F) (shares : n'.+1.-tuple F) : Prop :=
  massey_codeword s (tuple_to_rV shares) \in C.

Definition massey_recon_tuple (shares : n'.+1.-tuple F) : F :=
  massey_reconstruct (tuple_to_rV shares).

Lemma massey_correct_tuple (s : F) (shares : n'.+1.-tuple F) :
  massey_valid_tuple s shares ->
  massey_recon_tuple shares = s.
Proof. exact: massey_reconstruct_correct. Qed.

Lemma massey_private_tuple (s1 s2 : F) (shares : n'.+1.-tuple F)
    (coal : {set 'I_n'.+1}) :
  #|coal| < d_perp'.+1 ->
  massey_valid_tuple s1 shares ->
  exists shares' : n'.+1.-tuple F,
    massey_valid_tuple s2 shares' /\
    (forall i : 'I_n'.+1, i \in coal -> tnth shares' i = tnth shares i).
Proof.
move=> Hcoal Hvalid.
have [shares_rV [HvC Hagree]] := massey_private s2 Hcoal Hvalid.
exists (rV_to_tuple shares_rV); split.
- rewrite /massey_valid_tuple rV_to_tupleK; exact: HvC.
- move=> i Hi.
  rewrite tnth_mktuple -(tuple_to_rV_tnth shares i).
  exact: Hagree.
Qed.

Definition massey_scheme : SharingScheme F F :=
  @MkSharingScheme F F n' d_perp'
    massey_valid_tuple
    massey_recon_tuple
    massey_correct_tuple
    massey_private_tuple.

End massey_privacy.

(******************************************************************************)
(*     Section 5: MDS Specialization                                          *)
(******************************************************************************)

Section massey_mds.

Hypothesis HMDS : maximum_distance_separable C_not_trivial.

Let k := \dim C.

(* For MDS codes: d = n - k + 1 (Singleton bound with equality).
   The dual of an MDS code is MDS with d_perp = k + 1.
   Proving d_perp = k + 1 from HMDS requires the dual code theory
   (currently WIP in linearcode.v). *)

Lemma mds_min_dist_eq : d = (n - k + 1)%N.
Proof. by move/eqP: HMDS. Qed.

End massey_mds.

End massey.

Arguments massey_scheme {F n' C} C_not_trivial Hd2 {d_perp'} privacy_surj.
