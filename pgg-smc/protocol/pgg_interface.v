(* infotheo (c) AIST and Tohoku University. License: GPL-3.0-or-later. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism bigop.

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

HB.mixin Record hasGenerators (T : PGGTypes) := {
  pgg_ngens' : nat ;
  pgg_sigmas : pgg_ngens'.+1.-tuple (pgg_gT T) ;
  pgg_sigmas_gen : <<[set tnth pgg_sigmas i | i : 'I_pgg_ngens'.+1]>>%G = pgg_G T ;
}.

#[short(type=GeneratedMonodromyReprType)]
HB.structure Definition GeneratedMonodromyRepr :=
  { T of isMonodromyRepr T & hasGenerators T }.

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
(* Search space definitions from generators                                   *)
(* ========================================================================== *)

Section search_space_ops.

Variable M : GeneratedMonodromyReprType.

Let gT := pgg_gT M.
Let G := pgg_G M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

(* A word of length L: sequence of generator indices *)
Definition pgg_word (L : nat) := L.-tuple 'I_Tg.

(* Evaluate a word by folding group multiplication *)
Definition word_eval (L : nat) (w : pgg_word L) : gT :=
  (\prod_(i < L) tnth sigmas (tnth w i))%g.

(* Set of achievable group elements from words of length L *)
Definition achievable (L : nat) : {set gT} :=
  [set word_eval w | w : pgg_word L].

(* Search space size *)
Definition search_space (L : nat) : nat :=
  #|achievable L|.

(* Upper bound: achievable ⊆ G *)
Lemma sigmas_in_G (i : 'I_Tg) : tnth sigmas i \in G.
Proof.
have HgenG := @pgg_sigmas_gen M.
suff : tnth sigmas i \in <<[set tnth sigmas j | j : 'I_Tg]>>%G.
  by rewrite HgenG.
by apply: mem_gen; apply/imsetP; exists i.
Qed.

Lemma achievable_sub (L : nat) : achievable L \subset G.
Proof.
apply/subsetP => g /imsetP [w _ ->].
rewrite /word_eval; apply: group_prod => i _ /=.
exact: sigmas_in_G.
Qed.

(* Upper bound: search space ≤ |G| *)
Lemma search_space_leG (L : nat) : search_space L <= #|G|.
Proof.
rewrite /search_space.
exact: (subset_leq_card (achievable_sub L)).
Qed.

(* Upper bound: search space ≤ T^L (number of words) *)
Lemma search_space_le_words (L : nat) : search_space L <= Tg ^ L.
Proof.
rewrite /search_space /achievable.
apply: leq_trans (leq_imset_card _ _) _.
by rewrite card_tuple card_ord.
Qed.

(* L-freeness: word evaluation is injective on L-words *)
Definition lfree (L : nat) : Prop :=
  injective (word_eval (L:=L)).

(* L-free generators achieve the maximal search space T^L *)
Lemma lfree_search_space (L : nat) :
  lfree L -> search_space L = Tg ^ L.
Proof.
move=> Hinj; rewrite /search_space /achievable.
rewrite card_imset; last exact: Hinj.
by rewrite card_tuple card_ord.
Qed.

Definition lfreeB (L : nat) : bool :=
  injectiveb (word_eval (L:=L)).

Lemma lfreeP (L : nat) : reflect (lfree L) (lfreeB L).
Proof. exact: injectiveP. Qed.

End search_space_ops.

(* ========================================================================== *)
(* Generic results from generator injectivity                                 *)
(* ========================================================================== *)

Section gen_inj_theory.

Variable M : GeneratedMonodromyReprType.

Let gT := pgg_gT M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

Lemma gen_inj_lfree1 :
  injective (fun i : 'I_Tg => tnth sigmas i) ->
  @lfree M 1.
Proof.
move=> Hinj w1 w2 Heval.
apply: eq_from_tnth => i.
have -> : i = ord0 by apply: val_inj; case: i => -[].
apply: Hinj.
by move: Heval; rewrite /word_eval !big_ord_recl !big_ord0 !mulg1.
Qed.

Lemma gen_inj_search_space_1 :
  injective (fun i : 'I_Tg => tnth sigmas i) ->
  @search_space M 1 = Tg.
Proof. by move/gen_inj_lfree1/lfree_search_space. Qed.

End gen_inj_theory.

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

(* ========================================================================== *)
(* Parameterized multi-generator instance                                     *)
(* ========================================================================== *)

Section generated_instance.

Variable m : nat.
Variable n : nat.
Let T := m.+1.
Let N := n.+2.
Let gT : finGroupType := {perm 'I_N}.

Variable sigmas : T.-tuple gT.

Let gen_set : {set gT} := [set tnth sigmas i | i : 'I_T].
Let G : {group gT} := <<gen_set>>%G.

(* Inclusion morphism: identity on the subgroup *)
Lemma gen_incl_morphM : {in G &, {morph (@id gT) : x y / (x * y)%g}}.
Proof. by []. Qed.

Definition gen_incl_morph : {morphism G >-> {perm 'I_N}} :=
  Morphism gen_incl_morphM.

Definition Gen_PGGTypes := @MkPGG gT N.-1 G.

HB.instance Definition Gen_isMonodromyRepr :=
  @isMonodromyRepr.Build Gen_PGGTypes gen_incl_morph.

Lemma gen_sigmas_gen :
  <<[set tnth sigmas i | i : 'I_T]>>%G = G.
Proof. by []. Qed.

HB.instance Definition Gen_hasGenerators :=
  @hasGenerators.Build Gen_PGGTypes m sigmas gen_sigmas_gen.

Let M : MonodromyReprType := Gen_PGGTypes.

Definition gen_starts_2 : 2.-tuple 'I_N :=
  [tuple @Ordinal N 0 isT; @Ordinal N 1 isT].

Lemma gen_starts_2_uniq : uniq gen_starts_2.
Proof. by vm_compute. Qed.

Definition Gen_PGG_2 : PGG_Interface M :=
  @MkPGGI M 1 gen_starts_2 gen_starts_2_uniq.

End generated_instance.

(* ========================================================================== *)
(* Generic tuple construction from a generator function                       *)
(* ========================================================================== *)

Section gen_tuple_construction.

Variable T : nat.
Variable gT : finGroupType.
Variable gen : 'I_T.+1 -> gT.

Lemma gen_map_size : size (map gen (enum 'I_T.+1)) == T.+1.
Proof. by rewrite size_map size_enum_ord. Qed.

Definition gen_tuple_of : T.+1.-tuple gT := Tuple gen_map_size.

Lemma gen_tuple_ofE (i : 'I_T.+1) : tnth gen_tuple_of i = gen i.
Proof.
rewrite (tnth_nth (gen ord0)) /= (nth_map ord0) ?size_enum_ord //.
by congr gen; rewrite nth_ord_enum.
Qed.

End gen_tuple_construction.

(* ========================================================================== *)
(* Permutation utilities for RAAG instances                                   *)
(* ========================================================================== *)

Local Lemma neqS {fT : eqType} {a b : fT} : a != b -> b != a.
Proof. by rewrite eq_sym. Qed.

Lemma tperm_disjoint_comm (fT : finType) (a b c d : fT) :
  a != c -> a != d -> b != c -> b != d ->
  (tperm a b * tperm c d = tperm c d * tperm a b)%g.
Proof.
move=> Hac Had Hbc Hbd.
have Hca := neqS Hac; have Hda := neqS Had.
have Hcb := neqS Hbc; have Hdb := neqS Hbd.
apply/permP => x; rewrite !permM.
have [->|Hxa] := eqVneq x a.
  by rewrite tpermL (tpermD Hca Hda) (tpermD Hcb Hdb) tpermL.
have [->|Hxb] := eqVneq x b.
  by rewrite tpermR (tpermD Hca Hda) (tpermD Hcb Hdb) tpermR.
have [->|Hxc] := eqVneq x c.
  by rewrite (tpermD Hac Hbc) !tpermL (tpermD Had Hbd).
have [->|Hxd] := eqVneq x d.
  by rewrite (tpermD Had Hbd) !tpermR (tpermD Hac Hbc).
by rewrite !(tpermD _ _) // 1?eq_sym.
Qed.

(* Non-abelianity from a non-commuting generator pair *)
Lemma gen_nonabelian (M : GeneratedMonodromyReprType)
    (i j : 'I_(@pgg_ngens' M).+1) :
  i != j ->
  (tnth (@pgg_sigmas M) i * tnth (@pgg_sigmas M) j !=
   tnth (@pgg_sigmas M) j * tnth (@pgg_sigmas M) i)%g ->
  ~~ abelian (pgg_G M).
Proof.
move=> Hij Hnc.
rewrite -(pgg_sigmas_gen (s:=M)) abelian_gen.
apply/negP => /centsP Habel.
have Hi : tnth (@pgg_sigmas M) i \in
          [set tnth (@pgg_sigmas M) k | k : 'I_(@pgg_ngens' M).+1]
  by apply/imsetP; exists i.
have Hj : tnth (@pgg_sigmas M) j \in
          [set tnth (@pgg_sigmas M) k | k : 'I_(@pgg_ngens' M).+1]
  by apply/imsetP; exists j.
by move: Hnc; rewrite (Habel _ Hi _ Hj) eqxx.
Qed.
