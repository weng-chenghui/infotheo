(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Coordinate-Permutation Compatibility for Massey Secret Sharing             *)
(*                                                                            *)
(*   coord_perm_compatible C sigma == column permutation preserves code       *)
(*   restrict_perm0_val sigma Hfix == induced perm on share positions         *)
(*   massey_codeword_col_perm == col_perm sigma on codeword = codeword with  *)
(*     permuted shares                                                        *)
(*   massey_recon_col_perm == code auto + fix-0 => recon of permuted = secret*)
(*   massey_perm_compatible == derives ts_perm_compatible for massey_scheme   *)
(*   transport_perm_compatible == ts_perm_compatible lifts thru transport     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg finalg zmodp.
From mathcomp Require Import fingroup perm matrix mxalgebra vector.
Require Import ssr_ext ssralg_ext hamming linearcode.
From pgg_reconstruct Require Import pgg_sharing_framework massey
  rs_massey_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(*     Section 1: Code Automorphism                                           *)
(******************************************************************************)

Section coord_perm_compat_def.

Variable F : finFieldType.
Variable n : nat.
Variable C : Lcode0.t F n.

Definition coord_perm_compatible (sigma : {perm 'I_n}) : Prop :=
  forall c : 'rV[F]_n, c \in C -> col_perm sigma c \in C.

End coord_perm_compat_def.

Arguments coord_perm_compatible {F n} C sigma.

(******************************************************************************)
(*     Section 2: Restricting a Permutation that Fixes Position 0             *)
(******************************************************************************)

Section restrict_perm0.

Variable n' : nat.
Let n := n'.+2.

Variable sigma : {perm 'I_n}.
Hypothesis Hfix0 : sigma ord0 = ord0.

Lemma sigma_lift_neq0 (j : 'I_n'.+1) : sigma (lift ord0 j) != ord0.
Proof.
apply/eqP => Habs.
have Hlj0 : lift ord0 j = ord0 by exact: (perm_inj (etrans Habs (esym Hfix0))).
have := congr1 val Hlj0.
by rewrite /= /bump leq0n add1n.
Qed.

Definition restrict_perm0_fun (j : 'I_n'.+1) : 'I_n'.+1 :=
  odflt j (unlift ord0 (sigma (lift ord0 j))).

Lemma restrict_perm0_funE (j : 'I_n'.+1) :
  lift ord0 (restrict_perm0_fun j) = sigma (lift ord0 j).
Proof.
rewrite /restrict_perm0_fun.
case: (unliftP ord0 (sigma (lift ord0 j))) => [k Hk | Habs].
- by rewrite /= Hk.
- by exfalso; move/eqP: (sigma_lift_neq0 j); rewrite Habs.
Qed.

Lemma restrict_perm0_inj : injective restrict_perm0_fun.
Proof.
move=> j1 j2 Heq.
have : lift ord0 (restrict_perm0_fun j1) = lift ord0 (restrict_perm0_fun j2).
  by rewrite Heq.
rewrite !restrict_perm0_funE => /perm_inj.
exact: lift_inj.
Qed.

Definition restrict_perm0_val : {perm 'I_n'.+1} :=
  perm restrict_perm0_inj.

Lemma restrict_perm0_valE (j : 'I_n'.+1) :
  lift ord0 (restrict_perm0_val j) = sigma (lift ord0 j).
Proof. by rewrite permE restrict_perm0_funE. Qed.

End restrict_perm0.

Arguments restrict_perm0_val {n'} sigma Hfix0.

(******************************************************************************)
(*     Section 3: Massey Codeword + Column Permutation                        *)
(******************************************************************************)

Section massey_col_perm.

Variable F : finFieldType.
Variable n' : nat.
Let n := n'.+2.

Variable C : Lcode0.t F n.
Hypothesis C_nt : not_trivial C.
Let d := min_dist C_nt.
Hypothesis Hd2 : 1 < d.

Variable sigma : {perm 'I_n}.
Hypothesis Hfix0 : sigma ord0 = ord0.

Let sigma_sh := restrict_perm0_val sigma Hfix0.

Lemma massey_codeword_col_perm (s : F) (shares : 'rV[F]_n'.+1) :
  col_perm sigma (massey_codeword s shares) =
  massey_codeword s (col_perm sigma_sh shares).
Proof.
apply/rowP => i.
rewrite /col_perm mxE /massey_codeword mxE mxE.
case: (unliftP ord0 i) => [j -> | ->]; last by rewrite Hfix0 eqxx.
have Hneq0 : (lift ord0 j : nat) != 0%N by rewrite /=.
rewrite (negbTE Hneq0).
have Hneq0s : (sigma (lift ord0 j) : nat) != 0%N.
  by have := sigma_lift_neq0 Hfix0 j; rewrite -val_eqE /=.
rewrite (negbTE Hneq0s) mxE.
have lift_inord : forall (k : 'I_n), (k : nat) != 0%N ->
    lift ord0 (@inord n' k.-1) = k.
  move=> k Hk; apply/val_inj => /=.
  rewrite /bump leq0n add1n inordK; first by rewrite prednK //; case: (val k) Hk.
  by case: (val k) Hk (ltn_ord k) => //= m _ /ltnW.
congr (shares ord0 _).
suff Hlift : lift ord0 (inord (sigma (lift ord0 j)).-1) =
             lift ord0 (sigma_sh (inord (lift ord0 j).-1)).
  exact: lift_inj Hlift.
by rewrite restrict_perm0_valE lift_inord // lift_inord //.
Qed.

Lemma massey_recon_col_perm (s : F) (shares : 'rV[F]_n'.+1) :
  coord_perm_compatible C sigma ->
  massey_codeword s shares \in C ->
  massey_reconstruct C (col_perm sigma_sh shares) = s.
Proof.
move=> Hauto HmemC.
apply: (massey_reconstruct_correct Hd2).
rewrite -massey_codeword_col_perm.
exact: Hauto.
Qed.

End massey_col_perm.

(******************************************************************************)
(*     Section 4: ts_perm_compatible for massey_scheme                        *)
(******************************************************************************)

Section massey_perm_compat.

Variable F : finFieldType.
Variable n' : nat.
Let n := n'.+2.

Variable C : Lcode0.t F n.
Hypothesis C_nt : not_trivial C.
Let d := min_dist C_nt.
Hypothesis Hd2 : 1 < d.

Variable d_perp' : nat.
Hypothesis priv_surj :
  forall (S : {set 'I_n}) (target : 'rV[F]_n),
    #|S| < d_perp'.+2 ->
    exists c : 'rV[F]_n, c \in C /\ vproj c S = vproj target S.

Variable gT : finGroupType.
Variable G : {group gT}.

Variable sigma_code : gT -> {perm 'I_n}.

Hypothesis sigma_fix0 :
  forall g, g \in G -> sigma_code g ord0 = ord0.

Hypothesis code_auto :
  forall g, g \in G -> coord_perm_compatible C (sigma_code g).

Definition massey_share_perm (g : gT) : {perm 'I_n'.+1} :=
  if Sumbool.sumbool_of_bool (g \in G) is left hg then
    restrict_perm0_val (sigma_code g) (sigma_fix0 hg)
  else 1%g.

Lemma massey_share_permE (g : gT) (gG : g \in G) :
  massey_share_perm g = restrict_perm0_val (sigma_code g) (sigma_fix0 gG).
Proof.
rewrite /massey_share_perm.
case: (Sumbool.sumbool_of_bool _) => [hg | /negP]; last by rewrite gG.
by congr (restrict_perm0_val _ _); exact: eq_irrelevance.
Qed.

Lemma massey_perm_compatible :
  @ts_perm_compatible gT G _ _
    (massey_scheme C_nt Hd2 priv_surj)
    massey_share_perm.
Proof.
move=> g s shares gG Hvalid /=.
rewrite /= /massey_recon_tuple massey_share_permE.
have Heq : tuple_to_rV [tuple tnth shares (restrict_perm0_val (sigma_code g) (sigma_fix0 gG) i) | i < n'.+1] =
           col_perm (restrict_perm0_val (sigma_code g) (sigma_fix0 gG)) (tuple_to_rV shares).
  apply/rowP => j.
  by rewrite mxE tnth_mktuple mxE mxE.
rewrite Heq.
apply: massey_recon_col_perm => //.
exact: code_auto.
Qed.

End massey_perm_compat.

(******************************************************************************)
(*     Section 5: ts_perm_compatible lifts through transport_scheme           *)
(******************************************************************************)

Section transport_perm_compat.

Variables (A B : Type).
Variable (f : A -> B) (g_inv : B -> A).
Hypothesis Hgi : cancel g_inv f.
Hypothesis Hfg : cancel f g_inv.

Variable ts : ThresholdScheme A A.

Variable gT : finGroupType.
Variable G : {group gT}.

Let T := (ts_T' ts).+1.

Variable perm_A : gT -> {perm 'I_T}.

Lemma transport_perm_compatible :
  @ts_perm_compatible gT G _ _ ts perm_A ->
  @ts_perm_compatible gT G _ _ (transport_scheme Hgi Hfg ts) perm_A.
Proof.
move=> Hperm g s shares gG.
change (ts_valid ts (g_inv s) [tuple g_inv (tnth shares i) | i < T] ->
  f (ts_recon ts
    [tuple g_inv (tnth [tuple tnth shares (perm_A g i0) | i0 < T] i)
    | i < T]) = s).
move=> Hvalid.
have Heq : [tuple g_inv (tnth [tuple tnth shares (perm_A g i0) | i0 < T] i)
            | i < T] =
           [tuple tnth [tuple g_inv (tnth shares i0) | i0 < T] (perm_A g i)
            | i < T].
  apply: eq_from_tnth => i; by rewrite !tnth_mktuple.
rewrite Heq.
have Hc := Hperm g (g_inv s)
  [tuple g_inv (tnth shares i0) | i0 < T] gG Hvalid.
by rewrite Hc Hgi.
Qed.

End transport_perm_compat.

Arguments transport_perm_compatible {A B f g_inv} Hgi Hfg {ts gT G} perm_A.
