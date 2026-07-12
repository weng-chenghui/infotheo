(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_group: the PGL(2,7) monodromy on the eight-point projective line     *)
(*                                                                            *)
(* The projective line P^1(F_7) is identified with 'I_8: point 7 is the       *)
(* point at infinity, points 0..6 are the field elements of 'F_7. The three   *)
(* PGL(2,7) generators are given as explicit permutation tables of 'I_8:      *)
(*                                                                            *)
(*   tr_perm  == z |-> z + 1    (translation, tr_tbl  = [1;2;3;4;5;6;0;7])    *)
(*   sc_perm  == z |-> 3 z       (scaling,     sc_tbl  = [0;3;6;2;5;1;4;7])   *)
(*   inv_perm == z |-> -1 / z    (inversion,   inv_tbl = [7;6;3;2;5;4;1;0])   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_gens == the three generators as a 3.-tuple {perm 'I_8}             *)
(*   pgl27_M    == the MonodromyReprType [@Gen_PGGTypes 2 6 pgl27_gens]       *)
(*                 (a Notation, so HB keeps the hasGenerators structure)      *)
(*   moebius a b c d == the Moebius map z |-> (a z + b)/(c z + d) on 'I_8     *)
(*                                                                            *)
(* Key results:                                                               *)
(*   tr_moebius, sc_moebius, inv_moebius == Moebius maps z+1, 3z, -1/z        *)
(*   moebius_id             == the identity matrix induces the identity map   *)
(*   pgl27_3transitive      == the group acts 3-transitively on 'I_8         *)
(*   pgl27_rho_im           == rho's image is the generated group itself      *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order matrix mxalgebra.
From mathcomp Require Import finalg finfield zmodp.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgl_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------------- *)
(* The three generators as explicit permutation tables of 'I_8.               *)
(* -------------------------------------------------------------------------- *)

(* Ordinal in 'I_8 from a natural number, by reduction modulo 8. *)
Local Definition Imod (k : nat) : 'I_8 := Ordinal (ltn_pmod k (ltn0Sn 7)).

Local Definition tr_tbl  : seq nat := [:: 1; 2; 3; 4; 5; 6; 0; 7].
Local Definition sc_tbl  : seq nat := [:: 0; 3; 6; 2; 5; 1; 4; 7].
Local Definition inv_tbl : seq nat := [:: 7; 6; 3; 2; 5; 4; 1; 0].

(* Inverse tables of translation and scaling, used as cancellation witnesses. *)
Local Definition tr_inv_tbl : seq nat := [:: 6; 0; 1; 2; 3; 4; 5; 7].
Local Definition sc_inv_tbl : seq nat := [:: 0; 5; 3; 1; 6; 4; 2; 7].

(* The 'I_8 -> 'I_8 function read off a table by position. *)
Local Definition tbl_fun (tbl : seq nat) (i : 'I_8) : 'I_8 :=
  Imod (nth 0 tbl i).

(** tr_inj — the translation table defines an injective self-map of 'I_8.
    @composes: pgl27_gens *)
Lemma tr_inj : injective (tbl_fun tr_tbl).
Proof.
apply: (can_inj (g := tbl_fun tr_inv_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|?]]]]]]]] ?.
Qed.

(** sc_inj — the scaling table defines an injective self-map of 'I_8.
    @composes: pgl27_gens *)
Lemma sc_inj : injective (tbl_fun sc_tbl).
Proof.
apply: (can_inj (g := tbl_fun sc_inv_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|?]]]]]]]] ?.
Qed.

(** inv_inj — the inversion table is an involution, hence injective.
    @composes: pgl27_gens *)
Lemma inv_inj : injective (tbl_fun inv_tbl).
Proof.
apply: (can_inj (g := tbl_fun inv_tbl)).
by move=> x; apply: val_inj; case: x => -[|[|[|[|[|[|[|[|?]]]]]]]] ?.
Qed.

Local Definition tr_perm  : {perm 'I_8} := perm tr_inj.
Local Definition sc_perm  : {perm 'I_8} := perm sc_inj.
Local Definition inv_perm : {perm 'I_8} := perm inv_inj.

(** pgl27_gens — the three PGL(2,7) generators translation, scaling and
    inversion, packaged as the generator tuple of the monodromy.
    @intent: the generator tuple driving [pgl27_M]. *)
Definition pgl27_gens : 3.-tuple {perm 'I_8} :=
  [tuple tr_perm; sc_perm; inv_perm].

(* [pgl27_M] must be a Notation (not a Definition with a MonodromyReprType
   ascription): the ascription would seal the HB hasGenerators structure that
   SecurityWitness needs downstream. *)
Notation pgl27_M := (@Gen_PGGTypes 2 6 pgl27_gens).

(** pgl27_N' — the deck of [pgl27_M] has eight card positions ('I_8).
    @composes: pgl27_gens *)
Lemma pgl27_N' : pgg_N' pgl27_M = 7.
Proof. by []. Qed.

(* -------------------------------------------------------------------------- *)
(* The Moebius map layer on P^1(F_7) = 'I_8 (plain functions, no group        *)
(* quotients and no HB actions).                                              *)
(* -------------------------------------------------------------------------- *)

(* The point at infinity of P^1(F_7). *)
Local Definition inf_pt : 'I_8 := ord_max.

(* Field coordinate of a finite point; embedding a field element on the deck. *)
Local Definition to_F7 (i : 'I_8) : 'F_7 := (val i)%:R.
Local Definition of_F7 (x : 'F_7) : 'I_8 := widen_ord (isT : (7 <= 8)%N) x.

(** moebius — the Moebius map z |-> (a z + b) / (c z + d) on P^1(F_7),
    total via the infinity case split.
    @intent: the matrix-parameterised action of PGL(2,7) on the deck. *)
Definition moebius (a b c d : 'F_7) (z : 'I_8) : 'I_8 :=
  if z == inf_pt then (if c == 0 then inf_pt else of_F7 (a / c))
  else let x := to_F7 z in let den := c * x + d in
       if den == 0 then inf_pt else of_F7 ((a * x + b) / den).

(** moebius_id — the identity matrix induces the identity map on the deck.
    @composes: tr_moebius *)
Lemma moebius_id : moebius 1 0 0 1 =1 id.
Proof.
by move=> i; apply/val_inj; case: i => -[|[|[|[|[|[|[|[|?]]]]]]]] ?; vm_compute.
Qed.

(** tr_moebius — the translation generator is the Moebius map z |-> z + 1.
    @main architecture: identifies the first generator with a PGL(2,7) map. *)
Lemma tr_moebius : tr_perm =1 moebius 1 1 0 1.
Proof.
by move=> i; rewrite permE; apply/val_inj;
   case: i => -[|[|[|[|[|[|[|[|?]]]]]]]] ?; vm_compute.
Qed.

(** sc_moebius — the scaling generator is the Moebius map z |-> 3 z.
    @main architecture: identifies the second generator with a PGL(2,7) map. *)
Lemma sc_moebius : sc_perm =1 moebius (3%:R) 0 0 1.
Proof.
by move=> i; rewrite permE; apply/val_inj;
   case: i => -[|[|[|[|[|[|[|[|?]]]]]]]] ?; vm_compute.
Qed.

(** inv_moebius — the inversion generator is the Moebius map z |-> -1/z.
    @main architecture: identifies the third generator with a PGL(2,7) map. *)
Lemma inv_moebius : inv_perm =1 moebius 0 (-1) 1 0.
Proof.
by move=> i; rewrite permE; apply/val_inj;
   case: i => -[|[|[|[|[|[|[|[|?]]]]]]]] ?; vm_compute.
Qed.

(** pgl27_pgl2_order — the abstract PGL(2,7) quotient has order
    336 = 7*(7^2-1) = 8*7*6, the order of the action on P^1(F_7).
    @main bound: the machine-checked |PGL(2,7)| = 336. *)
Lemma pgl27_pgl2_order : #|pgl2 'F_7| = 336.
Proof. by rewrite card_pgl2 card_Fp. Qed.

(* ---------------------------------------------------------------------- *)
(* In-kernel 3-transitivity: nat-level word search.                        *)
(* A word is a seq of generator indices (0 = translation, 1 = scaling,     *)
(* 2 = inversion). A fueled BFS from the base triple [:: 0; 1; 2] finds,   *)
(* for each of the 336 ordered distinct code triples, a word carrying the  *)
(* base triple to it; the checker re-verifies every entry by computation.  *)
(* ---------------------------------------------------------------------- *)

(* The nat-level action of generator i on a code position. *)
Local Definition wgenn (i : nat) : nat -> nat :=
  if i == 0 then (fun a => nth 0 tr_tbl a)
  else if i == 1 then (fun a => nth 0 sc_tbl a)
  else (fun a => nth 0 inv_tbl a).

(* Application of a word (right-to-left generator composition) to a position. *)
Local Definition papply (w : seq nat) (a : nat) : nat :=
  foldl (fun x i => wgenn i x) a w.

(* One generator step applied coordinatewise to a code triple. *)
Local Definition wstep (i : nat) (t : seq nat) : seq nat := map (wgenn i) t.

(* Application of a word coordinatewise to a code triple. *)
Local Definition wapply (w : seq nat) (t : seq nat) : seq nat :=
  foldl (fun acc i => wstep i acc) t w.

(* Fueled word search, keeping one word per reached triple. *)
Local Fixpoint word_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | S f =>
    let nxt := flatten
      [seq [seq (wstep i tw.1, rcons tw.2 i)
             | i <- [:: 0; 1; 2]] | tw <- seen] in
    let add := foldl (fun acc tw =>
      if has (fun sw : seq nat * seq nat => sw.1 == tw.1) (seen ++ acc)
      then acc else rcons acc tw) [::] nxt in
    if size add == 0 then seen else word_bfs f (seen ++ add)
  end.

(* Reached triples paired with a carrying word, from the base triple. *)
Local Definition word_table : seq (seq nat * seq nat) :=
  word_bfs 12 [:: ([:: 0; 1; 2], [::])].

(* Every distinct code triple has a table word carrying the base to it. *)
Local Definition word_table_ok : bool :=
  all (fun a => all (fun b => all (fun c =>
    (a != b) && (a != c) && (b != c) ==>
    has (fun sw : seq nat * seq nat =>
      (sw.1 == [:: a; b; c]) && (wapply sw.2 [:: 0; 1; 2] == [:: a; b; c]))
      word_table)
    (iota 0 8)) (iota 0 8)) (iota 0 8).

(* Every word in the table re-verifies against every distinct code triple. *)
Local Lemma word_table_okT : word_table_ok.
Proof. by vm_compute. Qed.

(* Word application on a triple is coordinatewise scalar application. *)
Local Lemma wapply_map (w : seq nat) (a b c : nat) :
  wapply w [:: a; b; c] = [:: papply w a; papply w b; papply w c].
Proof. by elim: w a b c => [|i w IH] a b c //=. Qed.

(* The perm-level generator selected by a word index. *)
Local Definition gen_of (i : nat) : {perm 'I_8} :=
  if i == 0 then tr_perm else if i == 1 then sc_perm else inv_perm.

(* A word folded into the composite shuffle permutation. *)
Local Definition word_perm (w : seq nat) : {perm 'I_8} :=
  foldl (fun g i => (g * gen_of i)%g) 1%g w.

(* Each generator lies in the generated shuffle group. *)
Local Lemma gen_of_mem (i : nat) : gen_of i \in pgg_G pgl27_M.
Proof.
apply: mem_gen; apply/imsetP; rewrite /gen_of.
case: (i == 0); first by exists (@Ordinal 3 0 isT).
case: (i == 1); first by exists (@Ordinal 3 1 isT).
by exists (@Ordinal 3 2 isT).
Qed.

(* A composite word permutation lies in the generated shuffle group. *)
Local Lemma word_perm_mem (w : seq nat) : word_perm w \in pgg_G pgl27_M.
Proof.
rewrite /word_perm.
have g1 : 1%g \in pgg_G pgl27_M by exact: group1.
elim: w (1%g) g1 => [|i w IH] g gG //=.
by apply: IH; apply: groupM => //; exact: gen_of_mem.
Qed.

(* The perm-level generator agrees with the nat-level table action. *)
Local Lemma gen_of_val (i : nat) (x : 'I_8) :
  val (gen_of i x) = wgenn i (val x).
Proof.
rewrite /gen_of /wgenn; case: (i == 0); last case: (i == 1).
- by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE.
- by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE.
- by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE.
Qed.

(* The composite word permutation agrees with nat-level word application. *)
Local Lemma word_perm_val (w : seq nat) (x : 'I_8) :
  val (word_perm w x) = papply w (val x).
Proof.
rewrite /word_perm /papply.
have H : forall (w' : seq nat) (g : {perm 'I_8}) (y : 'I_8),
    val (foldl (fun h i => (h * gen_of i)%g) g w' y)
    = foldl (fun a i => wgenn i a) (val (g y)) w'.
  by elim=> [|i w' IH] g y //=; rewrite IH permM gen_of_val.
by rewrite H perm1.
Qed.

(* For every ordered distinct triple the BFS table exhibits a carrying word. *)
Local Lemma triple_word (x y z : 'I_8) :
  x != y -> x != z -> y != z ->
  exists w : seq nat,
    [/\ papply w 0 = val x, papply w 1 = val y & papply w 2 = val z].
Proof.
move=> nxy nxz nyz.
have Hin : forall n : 'I_8, val n \in iota 0 8.
  by move=> n; rewrite mem_iota; case: n.
have Hd : (val x != val y) && (val x != val z) && (val y != val z).
  by rewrite !val_eqE nxy nxz nyz.
move: word_table_okT.
move=> /allP/(_ _ (Hin x))/allP/(_ _ (Hin y))/allP/(_ _ (Hin z)).
move=> /implyP/(_ Hd)/hasP[[t w] /= _ /andP[_ /eqP Hw]].
exists w; move: Hw; rewrite wapply_map.
by case=> -> -> ->.
Qed.

(** pgl27_rho_im — the permutation image of the monodromy morphism is the
    generated shuffle group itself.
    @composes: pgl27_3transitive *)
Lemma pgl27_rho_im :
  (@pgg_rho pgl27_M @* pgg_G pgl27_M)%g = pgg_G pgl27_M.
Proof. by rewrite morphimEdom imset_id. Qed.

(* -------------------------------------------------------------------------- *)
(* Sharp 3-transitivity, in-kernel: for every ordered distinct triple the     *)
(* BFS word table exhibits a generator word carrying the base triple (0,1,2)  *)
(* to it; the orbit of the base triple is therefore all of 3.-dtuple.         *)
(* -------------------------------------------------------------------------- *)

(** pgl27_3transitive — the PGL(2,7) monodromy group acts 3-transitively on
    the eight projective points.
    @main security: the transitivity feeding every coalition-privacy result
    of the pgl27 instance. *)
Lemma pgl27_3transitive :
  ntransitive 3 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P.
Proof.
rewrite /ntransitive pgl27_rho_im.
pose t0 : 3.-tuple 'I_8 :=
  [tuple (@Ordinal 8 0 isT); (@Ordinal 8 1 isT); (@Ordinal 8 2 isT)].
have Ht0 : t0 \in 3.-dtuple([set: 'I_8]).
  by rewrite inE; apply/andP; split=> //; apply/subsetP => u _; rewrite inE.
apply/imsetP; exists t0 => //.
apply/setP => u; apply/idP/idP => [Hu | /orbitP[a aG <-]]; last first.
  apply: n_act_dtuple => //.
  by apply/astabsP => v; rewrite !inE.
case/tupleP: u Hu => x u; case/tupleP: u => y u; case/tupleP: u => z u.
rewrite tuple0 inE => /andP[Huniq _].
have [nxy nxz nyz] : [/\ x != y, x != z & y != z].
  by move: Huniq; rewrite /= !inE !negb_or => /andP[/andP[-> ->] /andP[-> _]].
have [w [Hx Hy Hz]] := triple_word nxy nxz nyz.
apply/orbitP; exists (word_perm w); first exact: word_perm_mem.
apply: eq_from_tnth => j.
rewrite tnth_map.
case: j => -[|[|[|//]]] Hj; apply: val_inj => /=.
- by rewrite [tnth t0 _]/= word_perm_val Hx.
- by rewrite [tnth t0 _]/= word_perm_val Hy.
- by rewrite [tnth t0 _]/= word_perm_val Hz.
Qed.
