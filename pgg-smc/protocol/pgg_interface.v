(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism bigop.
From mathcomp Require Import boolp reals.
From infotheo Require Import fdist.

(******************************************************************************)
(* PGG: Monodromy Representation Interface                                    *)
(*                                                                            *)
(* Layer 1 -- HB mixin (like HETypes + isEncDec):                             *)
(*   PGGTypes  == record bundling group type, card position count, and group  *)
(*   isMonodromyRepr == mixin providing the representation rho : G -> S_N     *)
(*   MonodromyReprType == HB structure packaging PGGTypes + isMonodromyRepr   *)
(*                                                                            *)
(* Derived operations:                                                        *)
(*   endpoint M g s == rho(g)(s), monodromy evaluation                        *)
(*   start_sheet PI i == starting card position of player i                   *)
(*   dealt_hand PI W i == player i's column of the permutation table          *)
(*   compute PI P i == endpoint for player i under word P                     *)
(*   endpoints PI P == T-tuple of all player endpoints                        *)
(*                                                                            *)
(* Layer 2 -- PGGInterface record (like DSDP_Interface):                     *)
(*   pgg_dtype  == session data type kind (DT_Sheet | DT_Hand | DT_Idx)       *)
(*   pgg_data N == protocol data: card position, dealt hand, or word index   *)
(*   PGGInterface M == protocol config (T players, starting card positions)  *)
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

(* [pgg_rho] is the permutation representation realising the abstract
   group [pgg_G] on a deck of [pgg_N'.+1] physical card positions.
   In MathComp, [{perm 'I_n}] is the symmetric group S_n on the finite
   type 'I_n = {0,...,n-1}, so [pgg_rho] is literally a morphism
   G -> S_n. The target S_n is not a restriction but a mathematical
   necessity: any action on n fixed card positions is by definition a
   homomorphism into S_n. The generality of the framework instead
   lives in the source [pgg_gT : finGroupType], which is an arbitrary
   finite group type -- instantiated in this development as cyclic,
   abelian, Coxeter A_4 (RAAG for S_5), star, or monster groups, each
   specified by its own presentation rather than as a pre-chosen
   subgroup of S_n. *)
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

(** endpoint — monodromy evaluation: applies the permutation [rho g] to card position [s].
    Kind: interface.
    Why: single-line accessor that the whole protocol is built on.
*)
Definition endpoint (g : gT) (s : 'I_N) : 'I_N := rho g s.

(** endpointM — multiplicative law for endpoint: [endpoint (g*h) s = endpoint h (endpoint g s)].
    Kind: main.
*)
Lemma endpointM (g h : gT) (s : 'I_N) :
  g \in G -> h \in G ->
  endpoint (g * h) s = endpoint h (endpoint g s).
Proof. by move=> gG hG; rewrite /endpoint morphM //= permM. Qed.

(** endpoint1 — identity element fixes every starting sheet.
    Kind: main.
*)
Lemma endpoint1 (s : 'I_N) : endpoint 1 s = s.
Proof. by rewrite /endpoint morph1 perm1. Qed.

(** endpoint_inj — [endpoint g] is injective on card positions.
    Kind: main.
    Why: used downstream to show distinctness of player endpoints under any shuffle.
*)
Lemma endpoint_inj (g : gT) : injective (endpoint g).
Proof. by move=> s1 s2; rewrite /endpoint; exact: perm_inj. Qed.

(** endpointV — inverse cancellation: applying [endpoint g^-1] undoes [endpoint g].
    Kind: main.
*)
Lemma endpointV (g : gT) (s : 'I_N) :
  g \in G -> endpoint g^-1 (endpoint g s) = s.
Proof.
move=> gG; rewrite -endpointM ?groupV // mulgV.
exact: endpoint1.
Qed.

End monodromy_ops.

Arguments endpoint {M}.

(* The endpoint at sheet s under permutation sigma.
   Analogous to endpoint g s = rho g s but takes a permutation
   directly, bypassing the monodromy morphism rho.
   Used in fiber counting and security analysis. *)
Section perm_endpoint_def.

Variable N' : nat.
Let N := N'.+1.

(** perm_endpoint — endpoint of sheet [s] under a raw permutation [sigma].
    Kind: interface.
    Why: bypasses the monodromy morphism [rho] so fiber counting and security
    analyses can quantify directly over [{perm 'I_N}].
*)
Definition perm_endpoint (sigma : {perm 'I_N}) (s : 'I_N) : 'I_N :=
  sigma s.

End perm_endpoint_def.

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

(** achievable_sub — words of length [L] produce elements inside [G].
    Kind: helper.
    Why: upper-bound step relating the word-search space to the ambient group.
    Used by: search_space_leG.
*)
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

(* Word-eval injectivity: word evaluation is injective on L-words *)
Definition weval_inj (L : nat) : Prop :=
  injective (word_eval (L:=L)).

(* Word-eval injective generators achieve the maximal search space T^L *)
Lemma weval_inj_search_space (L : nat) :
  weval_inj L -> search_space L = Tg ^ L.
Proof.
move=> Hinj; rewrite /search_space /achievable.
rewrite card_imset; last exact: Hinj.
by rewrite card_tuple card_ord.
Qed.

(** weval_injB — boolean reflect of [weval_inj] via MathComp [injectiveb].
    Kind: canonical.
*)
Definition weval_injB (L : nat) : bool :=
  injectiveb (word_eval (L:=L)).

(** weval_injP — reflection between [weval_inj] and [weval_injB].
    Kind: canonical.
*)
Lemma weval_injP (L : nat) : reflect (weval_inj L) (weval_injB L).
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

(** gen_inj_weval_inj1 — injective generators force word evaluation at length 1 to be injective.
    Kind: helper.
    Why: bridges the simple hypothesis on generators to the general [weval_inj] predicate.
    Used by: gen_inj_weval_inj1_search_space.
*)
Lemma gen_inj_weval_inj1 :
  injective (fun i : 'I_Tg => tnth sigmas i) ->
  @weval_inj M 1.
Proof.
move=> Hinj w1 w2 Heval.
apply: eq_from_tnth => i.
have -> : i = ord0 by apply: val_inj; case: i => -[].
apply: Hinj.
by move: Heval; rewrite /word_eval !big_ord_recl !big_ord0 !mulg1.
Qed.

(** gen_inj_weval_inj1_search_space — injective generators give a length-1 search space of size [Tg].
    Kind: main.
    Why: specialises the generic upper bound to the concrete length-1 maximum.
    Naming: the name concatenates three canonical witnesses (injective generators,
    word-eval injectivity at length 1, and the resulting search-space cardinality)
    because it is the composition gen_inj -> weval_inj1 -> search_space = Tg;
    splitting it would lose that chain of implications at the call site.
*)
Lemma gen_inj_weval_inj1_search_space :
  injective (fun i : 'I_Tg => tnth sigmas i) ->
  @search_space M 1 = Tg.
Proof. by move/gen_inj_weval_inj1/weval_inj_search_space. Qed.

End gen_inj_theory.

(* ========================================================================== *)
(* Session Data Type Kind                                                     *)
(* ========================================================================== *)

Inductive pgg_dtype : Type := DT_Sheet | DT_Hand | DT_Idx.

(** pgg_dtype_eqb — boolean decidable equality on the three session data tags.
    Kind: canonical.
*)
Definition pgg_dtype_eqb (d1 d2 : pgg_dtype) : bool :=
  match d1, d2 with
  | DT_Sheet, DT_Sheet => true
  | DT_Hand, DT_Hand => true
  | DT_Idx, DT_Idx => true
  | _, _ => false
  end.

(** pgg_dtype_eqP — reflection lemma witnessing that [pgg_dtype_eqb] is an equality axiom.
    Kind: canonical.
*)
Lemma pgg_dtype_eqP : Equality.axiom pgg_dtype_eqb.
Proof. by move=> [] []; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build pgg_dtype pgg_dtype_eqP.

(* ========================================================================== *)
(* Protocol Data Type                                                         *)
(* ========================================================================== *)

Inductive pgg_data (N : nat) : Type :=
  | PGG_sheet (i : 'I_N)
  | PGG_hand (s : seq ('I_N))
  | PGG_idx (n : nat).

Arguments PGG_sheet {N}.
Arguments PGG_hand {N}.
Arguments PGG_idx {N}.

(** pgg_data_dtype — tag function mapping a [pgg_data] payload to its [pgg_dtype].
    Kind: interface.
    Why: session types project protocol data through this tag.
*)
Definition pgg_data_dtype {N} (d : pgg_data N) : pgg_dtype :=
  match d with
  | PGG_sheet _ => DT_Sheet
  | PGG_hand _ => DT_Hand
  | PGG_idx _ => DT_Idx
  end.

(** from_sheet — partial projection recovering the card position from a [PGG_sheet] payload.
    Kind: interface.
    Why: session wrappers use this to pattern-match received data of type [DT_Sheet].
*)
Definition from_sheet {N} (d : pgg_data N) : option ('I_N) :=
  if d is PGG_sheet i then Some i else None.

(** from_hand — partial projection recovering the dealt hand from a [PGG_hand] payload.
    Kind: interface.
*)
Definition from_hand {N} (d : pgg_data N) : option (seq ('I_N)) :=
  if d is PGG_hand s then Some s else None.

(** from_idx — partial projection recovering the index from a [PGG_idx] payload.
    Kind: interface.
*)
Definition from_idx {N} (d : pgg_data N) : option nat :=
  if d is PGG_idx n then Some n else None.

(** from_sheet_PGG_sheet — round-trip: [from_sheet] recovers the stored card position.
    Kind: helper.
    Why: rewrite the [option]-projection to clear [match] noise in session proofs.
    Used by: card-exchange protocol programs and their duality checks.
*)
Lemma from_sheet_PGG_sheet {N} (i : 'I_N) :
  from_sheet (PGG_sheet i) = Some i.
Proof. by []. Qed.

(** from_hand_PGG_hand — round-trip: [from_hand] recovers the stored hand.
    Kind: helper.
    Why: as for [from_sheet_PGG_sheet], but on the [DT_Hand] branch.
    Used by: card-exchange protocol programs and their duality checks.
*)
Lemma from_hand_PGG_hand {N} (s : seq ('I_N)) :
  from_hand (PGG_hand s) = Some s.
Proof. by []. Qed.

(** from_idx_PGG_idx — round-trip: [from_idx] recovers the stored natural index.
    Kind: helper.
    Why: as for [from_sheet_PGG_sheet], but on the [DT_Idx] branch.
    Used by: card-exchange protocol programs and their duality checks.
*)
Lemma from_idx_PGG_idx {N} (n : nat) :
  from_idx (@PGG_idx N n) = Some n.
Proof. by []. Qed.

(* ========================================================================== *)
(* Layer 2: PGGInterface -- Protocol Configuration                           *)
(* ========================================================================== *)

Record PGGInterface (M : MonodromyReprType) := MkPGGI {
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
Variable PI : PGGInterface M.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.

Definition start_sheet (i : 'I_T) : 'I_N := tnth starts i.

Let x0 := tnth starts ord0.

(** start_sheet_inj — starting card positions are distinct across players.
    Kind: helper.
    Why: needed to convert cardinality of [start_sheets] to [T] via [card_imset].
    Used by: card_start_sheets.
*)
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

(** start_sheets — the set of all starting card positions of the [T] players.
    Kind: interface.
    Why: used in security and fiber analyses to range over starting deck positions.
*)
Definition start_sheets : {set 'I_N} :=
  [set tnth starts i | i : 'I_T].

(** card_start_sheets — there are exactly [T] starting card positions.
    Kind: main.
    Why: equates abstract interface cardinality with the player count; used in
    uniform-fiber counting and entropy analyses.
*)
Lemma card_start_sheets : #|start_sheets| = T.
Proof.
rewrite card_imset; first by rewrite card_ord.
exact: start_sheet_inj.
Qed.

(** perm_table — list of permutations obtained by applying [rho] to a word sequence.
    Kind: interface.
    Why: intermediate abstraction bridging abstract group words and permutation effects.
*)
Definition perm_table (W : seq gT) : seq {perm 'I_N} :=
  [seq rho w | w <- W].

(** dealt_hand — player [i]'s column of the permutation table: the sequence of
    card positions visited from [start_sheet i] under each word in [W].
    Kind: interface.
    Why: central protocol datum dealt to each player in the card-exchange program.
*)
Definition dealt_hand (W : seq gT) (i : 'I_T) : seq ('I_N) :=
  [seq rho w (tnth starts i) | w <- W].

(** compute — endpoint of player [i]'s starting card position under a fixed word [P].
    Kind: interface.
    Why: the single card position each player reveals to the verifier.
*)
Definition compute (P : gT) (i : 'I_T) : 'I_N :=
  rho P (tnth starts i).

(** endpoints — tuple of all player endpoints under a shared shuffle [P].
    Kind: interface.
    Why: full verifier-side observation across all [T] players for a given shuffle.
*)
Definition endpoints (P : gT) : T.-tuple 'I_N :=
  [tuple compute P i | i < T].

(** compute_in_dealt_hand — if [P] appears in [W], player [i]'s computed
    endpoint under [P] lies in the hand dealt to [i].
    Kind: helper.
    Why: correctness link between [compute] and [dealt_hand] used by the player program.
    Used by: card-exchange player correctness proofs.
*)
Lemma compute_in_dealt_hand (W : seq gT) (P : gT) (i : 'I_T) :
  P \in W -> compute P i \in dealt_hand W i.
Proof.
move=> PW; rewrite /dealt_hand /compute.
by apply/mapP; exists P.
Qed.

(** endpointsE — component-wise evaluation of [endpoints] reduces to [rho P (start i)].
    Kind: main.
*)
Lemma endpointsE (P : gT) (i : 'I_T) :
  tnth (endpoints P) i = rho P (tnth starts i).
Proof. by rewrite tnth_mktuple. Qed.

(** endpoint_starts_uniq — all endpoints under a fixed shuffle [g] remain distinct.
    Kind: main.
    Why: distinctness of starting card positions is preserved by any permutation,
    underpinning security/reconstruction arguments at the verifier.
*)
Lemma endpoint_starts_uniq (g : gT) :
  uniq (map (rho g) starts).
Proof.
rewrite map_inj_uniq; [exact: (pi_starts_uniq PI) | exact: perm_inj].
Qed.

End pgg_protocol_ops.

Arguments start_sheet {M} PI.
Arguments start_sheets {M} PI.
Arguments dealt_hand {M} PI.
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

(** gen_incl_morph — identity inclusion [G >-> {perm 'I_N}] as a group morphism.
    Kind: instance.
    Why: supplies [pgg_rho] for the generic template instance [Gen_PGGTypes].
*)
Definition gen_incl_morph : {morphism G >-> {perm 'I_N}} :=
  Morphism gen_incl_morphM.

(** Gen_PGGTypes — generic PGG types instance built from a tuple of generators.
    Kind: instance.
    Why: template reused by every concrete group family (Star, OC, Monster, ...).
*)
Definition Gen_PGGTypes := @MkPGG gT N.-1 G.

HB.instance Definition Gen_isMonodromyRepr :=
  @isMonodromyRepr.Build Gen_PGGTypes gen_incl_morph.

(** gen_sigmas_gen — the generator set spans the carrier group [G].
    Kind: helper.
    Why: discharges [pgg_sigmas_gen] when registering the [hasGenerators] instance.
    Used by: Gen_hasGenerators.
*)
Lemma gen_sigmas_gen :
  <<[set tnth sigmas i | i : 'I_T]>>%G = G.
Proof. by []. Qed.

HB.instance Definition Gen_hasGenerators :=
  @hasGenerators.Build Gen_PGGTypes m sigmas gen_sigmas_gen.

Let M : MonodromyReprType := Gen_PGGTypes.

(** gen_starts_2 — canonical two-player starting tuple [[0; 1]].
    Kind: instance.
    Why: minimal interface for native-compute duality checks at [T=2].
*)
Definition gen_starts_2 : 2.-tuple 'I_N :=
  [tuple @Ordinal N 0 isT; @Ordinal N 1 isT].

(** gen_starts_2_uniq — the two-player starts tuple has distinct entries.
    Kind: helper.
    Why: discharges the [pi_starts_uniq] obligation for [Gen_PGG_2].
    Used by: Gen_PGG_2.
*)
Lemma gen_starts_2_uniq : uniq gen_starts_2.
Proof. by vm_compute. Qed.

(** Gen_PGG_2 — two-player PGG interface over [Gen_PGGTypes].
    Kind: instance.
    Why: smallest concrete interface used for protocol duality verification.
*)
Definition Gen_PGG_2 : PGGInterface M :=
  @MkPGGI M 1 gen_starts_2 gen_starts_2_uniq.

End generated_instance.

(* ========================================================================== *)
(* T-party interface for any T <= N                                           *)
(* ========================================================================== *)

Section gen_pgg_T.

Variable M : MonodromyReprType.
Variable T' : nat.
Let T := T'.+1.
Let N := (pgg_N' M).+1.
Hypothesis HT : T <= N.

(** gen_starts_T_size — the generic [T]-player start tuple has size [T].
    Kind: helper.
    Why: discharges the size side-condition for the dependent [Tuple] constructor.
    Used by: gen_starts_T.
*)
Lemma gen_starts_T_size : size (map (widen_ord HT) (enum 'I_T)) == T.
Proof. by rewrite size_map size_enum_ord. Qed.

(** gen_starts_T — the tuple of the first [T] card positions, used as starts.
    Kind: instance.
    Why: provides the canonical start tuple for the [T]-player interface [Gen_PGG_T].
*)
Definition gen_starts_T : T.-tuple 'I_N := Tuple gen_starts_T_size.

(** gen_starts_T_uniq — the first [T] card positions are distinct.
    Kind: helper.
    Why: discharges [pi_starts_uniq] for [Gen_PGG_T].
    Used by: Gen_PGG_T.
*)
Lemma gen_starts_T_uniq : uniq gen_starts_T.
Proof.
rewrite /gen_starts_T /= map_inj_uniq ?enum_uniq //.
by move=> x y Heq; apply: val_inj; have := congr1 val Heq.
Qed.

(** Gen_PGG_T — [T]-player PGG interface using the first [T] card positions as starts.
    Kind: instance.
    Why: uniform interface used by every multi-player concrete protocol instance.
*)
Definition Gen_PGG_T : PGGInterface M :=
  @MkPGGI M T' gen_starts_T gen_starts_T_uniq.

End gen_pgg_T.

(* ========================================================================== *)
(* Generic tuple construction from a generator function                       *)
(* ========================================================================== *)

Section gen_tuple_construction.

Variable T : nat.
Variable gT : finGroupType.
Variable gen : 'I_T.+1 -> gT.

(** gen_map_size — [map gen (enum 'I_T.+1)] has size [T.+1].
    Kind: helper.
    Why: discharges the size obligation of the dependent [Tuple] constructor.
    Used by: gen_tuple_of.
*)
Lemma gen_map_size : size (map gen (enum 'I_T.+1)) == T.+1.
Proof. by rewrite size_map size_enum_ord. Qed.

(** gen_tuple_of — packages a function [gen : 'I_T.+1 -> gT] as a [T.+1]-tuple.
    Kind: interface.
    Why: lifts a generator-by-index function to the tuple expected by [Gen_PGGTypes].
*)
Definition gen_tuple_of : T.+1.-tuple gT := Tuple gen_map_size.

(** gen_tuple_ofE — component access on [gen_tuple_of] recovers the generator function.
    Kind: main.
    Why: rewriting lemma that removes the [Tuple]/[nth_map] scaffolding at use sites.
*)
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

(** tperm_disjoint_comm — disjoint transpositions [(a b)] and [(c d)] commute.
    Kind: main.
    Why: reusable permutation identity that underpins commutativity witnesses
    for abelian and star-type RAAG presentations.
*)
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

(******************************************************************************)
(*  Weighted generator distribution                                           *)
(******************************************************************************)

Local Open Scope fdist_scope.

HB.mixin Record hasWeights (R : realType) (T : PGGTypes)
    of GeneratedMonodromyRepr T := {
  pgg_gen_weights : R.-fdist 'I_(@pgg_ngens' T).+1 ;
}.

#[short(type=WeightedPGGType)]
HB.structure Definition WeightedPGG (R : realType) :=
  { T of isMonodromyRepr T & hasGenerators T & hasWeights R T }.
