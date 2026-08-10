(* Probe: object elaboration at the pinned carrier.                           *)
(* Spec: docs/superpowers/specs/                                              *)
(*   2026-08-10-five-card-all-reveal-cases-design.md                          *)
(* Ledger rows: L1, L3, L4, L5, L6, L8, L13.                                  *)
(* Rules: final state has ZERO Admitted/Abort/Axiom; statements may be        *)
(* adjusted syntactically (ordinal-literal encodings, tuple coercions) but    *)
(* never semantically; never imported by a permanent file.                    *)

(* IMPORT ADJUSTMENT (recorded): five_card_leakage.v does not import          *)
(* mathcomp's div, so the notation "_ %% _" is not in scope there.  succ5 and *)
(* nth_rot5 both need it, so div is added below.  Probe finding: adding div   *)
(* breaks no scope or notation used by the carrier (this file compiles).      *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program.
From mathcomp Require Import lra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section probe_objects.

Variable R : realType.

Local Open Scope ring_scope.

(* ---- carrier, replicated verbatim from five_card_leakage.v ---- *)

Definition Omega : finType := [the finType of (bool * bool * 'I_5)%type].

Lemma card_Omega20 : #|Omega| = 19.+1.
Proof. by rewrite !card_prod card_bool card_ord. Qed.

Definition P : R.-fdist Omega := fdist_uniform card_Omega20.

Definition arr (w : Omega) : seq bool :=
  let: (a, b, k) := w in fc_shuffle k (fc_arrange a b).

Definition Secret : {RV P -> bool} := fun w => let: (a, b, _) := w in a && b.

Definition ViewA (A : seq nat) : {RV P -> (size A).-tuple bool} :=
  fun w => map_tuple (fun i => nth false (arr w) i) (in_tuple A).

(* ---- L4: position-tuple view ---- *)

Definition succ5 (i : 'I_5) : 'I_5 := inord (i.+1 %% 5).

Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

(* ---- L1: the file's MI toolkit elaborates at ViewT ---- *)

Lemma probe_mi_toolkit (t : 3.-tuple 'I_5) :
  `I( Secret ; ViewT t ) = `H `p_Secret - `H( Secret | ViewT t ).
Proof. by rewrite mutual_info_RVE. Qed.

(* ---- L3: enum-as-tuple for {set 'I_5} ---- *)
(* RESOLUTION (recorded): mathcomp's fintype/tuple machinery does provide the *)
(* canonical enumerating tuple, enum_tuple : forall (A : {pred T}),           *)
(* #|A|.-tuple T (mathcomp.boot.tuple, line 427), and it typechecks at the    *)
(* declared type #|A|.-tuple 'I_5 with no cast.  So the "Tuple + cardE"       *)
(* fallback is not needed.                                                    *)
(*                                                                            *)
(* PROBE FINDING (important for the implementation plan): set_tuple does NOT  *)
(* reduce to a literal tuple by computation.  enum 'I_5 goes through          *)
(* ord_enum = pmap insub (iota 0 5) and insub is blocked on idP, which is     *)
(* Qed-opaque; vm_compute leaves a stuck "match idP with ..." term.  The same *)
(* blocks #|A| and inord.  The reduction therefore has to be done by rewriting*)
(* through val_enum_ord, which is what enum_val5 and card_val5 below package: *)
(* both #|A| and map val (enum A) reduce to closed nat computations on        *)
(* iota 0 5 once membership in A is expressed as a predicate on val.          *)

Definition set_tuple (A : {set 'I_5}) : #|A|.-tuple 'I_5 := enum_tuple A.

(* enum_val5 — the ascending enumeration of a subset of 'I_5, read off at the
   nat level: if membership in A is the nat predicate q on the ordinal value,
   then the values of enum A are the elements of iota 0 5 satisfying q. *)
Lemma enum_val5 (A : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in A) = q (val x)) ->
  map val (enum A) = filter q (iota 0 5).
Proof.
move=> H; rewrite -val_enum_ord filter_map; congr (map _ _).
by rewrite {1}/enum_mem -enumT; apply: eq_filter => x /=; exact: H.
Qed.

(* card_val5 — the cardinality of a subset of 'I_5 as a nat computation. *)
Lemma card_val5 (A : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in A) = q (val x)) -> #|A| = size (filter q (iota 0 5)).
Proof. by move=> H; rewrite cardE -(size_map val) (enum_val5 H). Qed.

(* succ5_val — the value of the successor position. *)
Lemma succ5_val (i : 'I_5) : val (succ5 i) = (i.+1 %% 5)%N.
Proof. by rewrite /succ5 /= inordK // ltn_pmod. Qed.

Lemma set_tuple_013 :
  val (set_tuple [set inord 0; inord 1; inord 3]) =
  [:: inord 0; inord 1; (inord 3 : 'I_5)].
Proof.
apply: (inj_map val_inj).
rewrite (enum_val5 (A := [set inord 0; inord 1; (inord 3 : 'I_5)])
  (q := fun n => (n == 0%N) || (n == 1%N) || (n == 3%N))); last first.
  by move=> x; rewrite !inE -!val_eqE /= !inordK.
by rewrite /= !inordK.
Qed.

(* ---- L5: fc_adjacent computes on literals ---- *)

Definition fc_adjacent (A : {set 'I_5}) : bool :=
  [exists i : 'I_5, A == [set i; succ5 i]].

Lemma fc_adjacent_01 : fc_adjacent [set inord 0; inord 1] = true.
Proof.
apply/existsP; exists (inord 0 : 'I_5); apply/eqP.
by apply/setP => x; rewrite !inE -!val_eqE /= succ5_val !inordK.
Qed.

Lemma fc_adjacent_02 : fc_adjacent [set inord 0; inord 2] = false.
Proof.
apply/negbTE/existsPn => i; apply/negP => /eqP/setP hm.
have h0 := hm (inord 0). have h1 := hm (inord 1). have h2 := hm (inord 2).
have h3 := hm (inord 3). have h4 := hm (inord 4).
clear hm; move: h0 h1 h2 h3 h4.
rewrite !inE -!val_eqE /= !inordK //.
  by case: i => [[|[|[|[|[|m]]]]] Hm].
by rewrite ltn_pmod.
Qed.

(* wrap-around adjacency: {4,0} is adjacent *)
Lemma fc_adjacent_40 : fc_adjacent [set inord 4; inord 0] = true.
Proof.
apply/existsP; exists (inord 4 : 'I_5); apply/eqP.
by apply/setP => x; rewrite !inE -!val_eqE /= succ5_val !inordK.
Qed.

(* ---- L6: fc_leak compiles under ring_scope and reduces on literals ---- *)

Definition fc_leak (A : {set 'I_5}) : R :=
  match #|A| with
  | 0 => 0
  | 1 => 0
  | 2 => if fc_adjacent A
         then 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R
         else 5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
              - (7%:R / 20%:R) * log 7%:R
  | 3 => 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R
  | _ => 2%:R - (3%:R / 4%:R) * log 3%:R
  end.

Lemma fc_leak_singleton : fc_leak [set (inord 0 : 'I_5)] = 0.
Proof. by rewrite /fc_leak cards1. Qed.

Lemma fc_leak_2adj :
  fc_leak [set inord 0; inord 1] =
  27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R.
Proof.
rewrite /fc_leak fc_adjacent_01.
have -> : #|[set (inord 0 : 'I_5); inord 1]| = 2%N.
  rewrite (card_val5 (q := fun n => (n == 0%N) || (n == 1%N))) //.
  by move=> x; rewrite !inE -!val_eqE /= !inordK.
by [].
Qed.

Lemma fc_leak_3gap :
  fc_leak [set inord 0; inord 1; inord 3] =
  6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Proof.
rewrite /fc_leak.
have -> : #|[set (inord 0 : 'I_5); inord 1; inord 3]| = 3%N.
  rewrite (card_val5 (q := fun n => (n == 0%N) || (n == 1%N) || (n == 3%N))) //.
  by move=> x; rewrite !inE -!val_eqE /= !inordK.
by [].
Qed.

(* ---- L8: nth-of-rot at size 5 ---- *)

Lemma nth_rot5 (s : seq bool) (i k : nat) :
  size s = 5%N -> (i < 5)%N -> (k < 5)%N ->
  nth false (rot k s) i = nth false s ((i + k) %% 5)%N.
Proof.
move=> Hs Hi Hk.
move: Hs; case: s => [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 l]]]]]] //= _.
by case: i Hi => [|[|[|[|[|i]]]]] //= _; case: k Hk => [|[|[|[|[|k]]]]] //=.
Qed.

(* ---- L13: spot-check the {0,1,3} fibre tables ---- *)
(* Ground truth (five_card_leak_enum.py): view FTT has nv = 4;               *)
(* joint (true, FTT) has count 1. Template: cardV3/cardJ3 in                 *)
(* five_card_leakage.v lines 452-483.                                        *)

(* stepBB, stepO — the two reindexing steps of the enumeration template,
   replicated from five_card_leakage.v lines 145-157. *)
Lemma stepBB (G : bool * bool -> nat) :
  (\sum_(ab : bool * bool) G ab)%N
    = (\sum_(a : bool) \sum_(b : bool) G (a, b))%N.
Proof. by rewrite pair_bigA /=; apply: eq_big => // i _; case: i. Qed.

Lemma stepO (G : Omega -> nat) :
  (\sum_(i : Omega) G i)%N
    = (\sum_(ab : bool * bool) \sum_(k : 'I_5) G (ab, k))%N.
Proof. by rewrite pair_bigA /=; apply: eq_big => // i _; case: i. Qed.

Lemma cardV013_FTT :
  #|preim (ViewA [:: 0; 1; 3]%N) (pred1 [tuple of [:: false; true; true]])|
  = 4%N.
Proof.
rewrite -sum1_card (eq_bigl (fun w : Omega =>
   (nth false (arr w) 0 == false) && (nth false (arr w) 1 == true)
     && (nth false (arr w) 3 == true))); last first.
  move=> w /=.
  by rewrite /ViewA inE /= -val_eqE /= !eqseq_cons andbT andbA.
rewrite big_mkcond /= stepO.
under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
by rewrite stepBB !big_bool /=.
Qed.

Lemma cardJ013_true_FTT :
  #|preim [% Secret, ViewA [:: 0; 1; 3]%N]
          (pred1 (true, [tuple of [:: false; true; true]]))| = 1%N.
Proof.
rewrite -sum1_card (eq_bigl (fun w : Omega =>
    (let: (a, b, _) := w in (a && b) == true)
      && ((nth false (arr w) 0 == false) && ((nth false (arr w) 1 == true)
          && (nth false (arr w) 3 == true))))); last first.
  move=> w /=; rewrite inE /=.
  rewrite xpair_eqE /Secret /ViewA /=.
  by case: w => [[a b] k] /=; rewrite -val_eqE /= !eqseq_cons andbT.
rewrite big_mkcond /= stepO.
under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
by rewrite stepBB !big_bool /=.
Qed.

End probe_objects.
