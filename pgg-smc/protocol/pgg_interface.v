(* infotheo (c) AIST and Tohoku University. License: GPL-3.0-or-later. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.

(******************************************************************************)
(* PGG-SMC: Monodromy Representation Interface                               *)
(*                                                                            *)
(* Layer 1 -- HB mixin (like HETypes + isEncDec):                             *)
(*   PGGTypes  == record bundling group type, sheet count, and group          *)
(*   isMonodromyRepr == mixin providing the representation rho : G -> S_N     *)
(*   MonodromyReprType == HB structure packaging PGGTypes + isMonodromyRepr   *)
(*                                                                            *)
(* Derived operations:                                                        *)
(*   endpoint M g s == rho(g)(s), monodromy evaluation                        *)
(*   start_sheet PI i == starting sheet of party i                            *)
(*   share PI W i == party i's column of the permutation table                *)
(*   compute PI P i == endpoint for party i under word P                      *)
(*   endpoints PI P == T-tuple of all party endpoints                         *)
(*                                                                            *)
(* Layer 2 -- PGG_Interface record (like DSDP_Interface):                     *)
(*   pgg_dtype  == session data type kind (DT_Sheet | DT_Share | DT_Idx)      *)
(*   pgg_data N == protocol data: sheet index, share, or word index           *)
(*   PGG_Interface M == protocol configuration (T parties, starting sheets)   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Layer 1: HB mixin -- Monodromy Representation                              *)
(* ========================================================================== *)

Record PGGTypes := MkPGG {
  pgg_gT : finGroupType ;
  pgg_N' : nat ;
  pgg_G  : {group pgg_gT} ;
}.

HB.mixin Record isMonodromyRepr (T : PGGTypes) := {
  pgg_rho : {morphism (pgg_G T) >-> {perm 'I_(pgg_N' T).+1}} ;
}.

#[short(type=MonodromyReprType)]
HB.structure Definition MonodromyRepr := { T of isMonodromyRepr T }.

(* ========================================================================== *)
(* Derived operations from monodromy representation                           *)
(* ========================================================================== *)

Section monodromy_ops.

Variable M : MonodromyReprType.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let G := pgg_G M.
Let rho := @pgg_rho M.

Definition endpoint (g : gT) (s : 'I_N) : 'I_N := rho g s.

Lemma endpointM (g h : gT) (s : 'I_N) :
  g \in G -> h \in G ->
  endpoint (g * h) s = endpoint h (endpoint g s).
Proof. by move=> gG hG; rewrite /endpoint morphM //= permM. Qed.

Lemma endpoint1 (s : 'I_N) : endpoint 1 s = s.
Proof. by rewrite /endpoint morph1 perm1. Qed.

Lemma endpoint_inj (g : gT) : injective (endpoint g).
Proof. by move=> s1 s2; rewrite /endpoint; exact: perm_inj. Qed.

Lemma endpointV (g : gT) (s : 'I_N) :
  g \in G -> endpoint g^-1 (endpoint g s) = s.
Proof.
move=> gG; rewrite -endpointM ?groupV // mulgV.
exact: endpoint1.
Qed.

End monodromy_ops.

Arguments endpoint {M}.

(* ========================================================================== *)
(* Session Data Type Kind                                                     *)
(* ========================================================================== *)

Inductive pgg_dtype : Type := DT_Sheet | DT_Share | DT_Idx.

Definition pgg_dtype_eqb (d1 d2 : pgg_dtype) : bool :=
  match d1, d2 with
  | DT_Sheet, DT_Sheet => true
  | DT_Share, DT_Share => true
  | DT_Idx, DT_Idx => true
  | _, _ => false
  end.

Lemma pgg_dtype_eqP : Equality.axiom pgg_dtype_eqb.
Proof. by move=> [] []; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build pgg_dtype pgg_dtype_eqP.

(* ========================================================================== *)
(* Protocol Data Type                                                         *)
(* ========================================================================== *)

Inductive pgg_data (N : nat) : Type :=
  | PGG_sheet (i : 'I_N)
  | PGG_share (s : seq ('I_N))
  | PGG_idx (n : nat).

Arguments PGG_sheet {N}.
Arguments PGG_share {N}.
Arguments PGG_idx {N}.

Definition pgg_data_dtype {N} (d : pgg_data N) : pgg_dtype :=
  match d with
  | PGG_sheet _ => DT_Sheet
  | PGG_share _ => DT_Share
  | PGG_idx _ => DT_Idx
  end.

Definition from_sheet {N} (d : pgg_data N) : option ('I_N) :=
  if d is PGG_sheet i then Some i else None.

Definition from_share {N} (d : pgg_data N) : option (seq ('I_N)) :=
  if d is PGG_share s then Some s else None.

Definition from_idx {N} (d : pgg_data N) : option nat :=
  if d is PGG_idx n then Some n else None.

Lemma from_sheet_PGG_sheet {N} (i : 'I_N) :
  from_sheet (PGG_sheet i) = Some i.
Proof. by []. Qed.

Lemma from_share_PGG_share {N} (s : seq ('I_N)) :
  from_share (PGG_share s) = Some s.
Proof. by []. Qed.

Lemma from_idx_PGG_idx {N} (n : nat) :
  from_idx (@PGG_idx N n) = Some n.
Proof. by []. Qed.

(* ========================================================================== *)
(* Layer 2: PGG_Interface -- Protocol Configuration                           *)
(* ========================================================================== *)

Record PGG_Interface (M : MonodromyReprType) := MkPGGI {
  pi_T' : nat ;
  pi_starts : pi_T'.+1.-tuple 'I_(pgg_N' M).+1 ;
  pi_starts_uniq : uniq pi_starts ;
}.

Arguments pi_T' {M} _.
Arguments pi_starts {M} _.
Arguments pi_starts_uniq {M} _.

(* ========================================================================== *)
(* Protocol Operations                                                        *)
(* ========================================================================== *)

Section pgg_protocol_ops.

Variable M : MonodromyReprType.
Variable PI : PGG_Interface M.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.

Definition start_sheet (i : 'I_T) : 'I_N := tnth starts i.

Let x0 := tnth starts ord0.

Lemma start_sheet_inj : injective start_sheet.
Proof.
move=> i j; rewrite /start_sheet => eq_ij.
have Hi : (i < size starts)%N by rewrite size_tuple.
have Hj : (j < size starts)%N by rewrite size_tuple.
have := @nth_uniq _ x0 starts i j Hi Hj (pi_starts_uniq PI).
have -> : nth x0 starts i = tnth starts i by rewrite (tnth_nth x0).
have -> : nth x0 starts j = tnth starts j by rewrite (tnth_nth x0).
rewrite eq_ij eqxx => /esym/eqP. exact: ord_inj.
Qed.

Definition start_sheets : {set 'I_N} :=
  [set tnth starts i | i : 'I_T].

Lemma card_start_sheets : #|start_sheets| = T.
Proof.
rewrite card_imset; first by rewrite card_ord.
exact: start_sheet_inj.
Qed.

Definition perm_table (W : seq gT) : seq {perm 'I_N} :=
  [seq rho w | w <- W].

Definition share (W : seq gT) (i : 'I_T) : seq ('I_N) :=
  [seq rho w (tnth starts i) | w <- W].

Definition compute (P : gT) (i : 'I_T) : 'I_N :=
  rho P (tnth starts i).

Definition endpoints (P : gT) : T.-tuple 'I_N :=
  [tuple compute P i | i < T].

Lemma compute_in_share (W : seq gT) (P : gT) (i : 'I_T) :
  P \in W -> compute P i \in share W i.
Proof.
move=> PW; rewrite /share /compute.
by apply/mapP; exists P.
Qed.

Lemma endpointsE (P : gT) (i : 'I_T) :
  tnth (endpoints P) i = rho P (tnth starts i).
Proof. by rewrite tnth_mktuple. Qed.

Lemma endpoint_starts_uniq (g : gT) :
  uniq (map (rho g) starts).
Proof.
rewrite map_inj_uniq; [exact: (pi_starts_uniq PI) | exact: perm_inj].
Qed.

End pgg_protocol_ops.

Arguments start_sheet {M} PI.
Arguments start_sheets {M} PI.
Arguments share {M} PI.
Arguments compute {M} PI.
Arguments endpoints {M} PI.
