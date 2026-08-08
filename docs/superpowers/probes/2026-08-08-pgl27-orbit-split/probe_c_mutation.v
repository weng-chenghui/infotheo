(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_orbit: the orbit-class secret of the eight-card PGL(2,7) scheme      *)
(*                                                                            *)
(* A deck is an eight-position arrangement [sh : 8.-tuple 'I_8] of the cards  *)
(* 'I_8; a heart is a card with code below four. The heart positions form a   *)
(* four-subset of the projective line P^1(F_7) = 'I_8 (point 7 is infinity)   *)
(* and its PGL(2,7) orbit is read off by the cross-ratio: a distinct four-    *)
(* tuple is equianharmonic when its cross-ratio lands in {3,5}. Arithmetic    *)
(* runs on the 'I_8 codes as nat mod 7 (inversion by the table               *)
(* [0;1;4;5;2;3;6]) so every ground check is [vm_compute]-safe; no 'F_7       *)
(* field inversion is used.                                                   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   is_heart c     == the card c is a heart (code below four)                *)
(*   deck_ok sh     == the arrangement sh has distinct cards                  *)
(*   heart_set sh   == the set of positions holding a heart                   *)
(*   cross_ratio    == cross-ratio of four points, valued in nat mod 7        *)
(*   subset_class S == equianharmonic verdict of a four-subset of positions   *)
(*   orbit_class sh == the orbit class of the heart four-subset of sh         *)
(*   orbit_encode b == a distinct-card deck of orbit class b                  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   orbit_class_invariant == orbit_class is invariant under the coordinate   *)
(*                            action of any shuffle-group element             *)
(*   deck_stable           == the coordinate action preserves distinctness    *)
(*   orbit_populated       == both orbit classes occur among distinct decks   *)
(*   orbit_encodeK         == orbit_encode is a section of orbit_class        *)
(*   orbit_class_split     == 28 of the 70 four-subsets are equianharmonic,   *)
(*                            42 are harmonic (the two PGL(2,7) orbit sizes) *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group.

(* -------------------------------------------------------------------------- *)
(* Cross-ratio on P^1(F_7), as nat-mod-7 table arithmetic on the 'I_8 codes.  *)
(* -------------------------------------------------------------------------- *)

(* Modular inverse of a residue mod 7, read off the table [0;1;4;5;2;3;6]. *)
Local Definition inv7 (a : nat) : nat := nth 0 [:: 0; 1; 4; 5; 2; 3; 6] a.
Local Definition sub7 (a b : nat) : nat := (a + 7 - b) %% 7.
Local Definition mul7 (a b : nat) : nat := (a * b) %% 7.
Local Definition div7 (a b : nat) : nat := mul7 a (inv7 b).

(* nat-mod-7 cross-ratio of four codes, with the four infinity case splits. *)
Local Definition crn (x1 x2 x3 x4 : nat) : nat :=
  if x1 == 7 then div7 (sub7 x2 x4) (sub7 x2 x3)
  else if x2 == 7 then div7 (sub7 x1 x3) (sub7 x1 x4)
  else if x3 == 7 then div7 (sub7 x2 x4) (sub7 x1 x4)
  else if x4 == 7 then div7 (sub7 x1 x3) (sub7 x2 x3)
  else div7 (mul7 (sub7 x1 x3) (sub7 x2 x4)) (mul7 (sub7 x1 x4) (sub7 x2 x3)).

(** cross_ratio — cross-ratio of four points of P^1(F_7) = 'I_8, point 7 the
    point at infinity, valued in nat mod 7.
    @intent: the PGL(2,7)-invariant of an ordered distinct quadruple. *)
Definition cross_ratio (x1 x2 x3 x4 : 'I_8) : nat :=
  crn (val x1) (val x2) (val x3) (val x4).

(** equianharmonic — a cross-ratio value lies in the equianharmonic orbit.
    @intent: the two-valued orbit predicate {3,5} on distinct cross-ratios. *)
Definition equianharmonic (l : nat) : bool := (l == 3) || (l == 5).

(* Verdict of a code list: equianharmonic cross-ratio of the sorted codes. *)
Local Definition nclass (L : seq nat) : bool :=
  match sort leq L with
  | [:: a; b; c; d] => equianharmonic (crn a b c d)
  | _ => false
  end.

(* -------------------------------------------------------------------------- *)
(* Deck, hearts and the orbit classifier.                                     *)
(* -------------------------------------------------------------------------- *)

(** is_heart — the card c is a heart, i.e. carries a code below four.
    @intent: the colour predicate splitting the deck into hearts and others. *)
Definition is_heart (c : 'I_8) : bool := (val c < 4)%N.

(** deck_ok — the arrangement sh deals eight distinct cards.
    @intent: the valid-deck predicate of the eight-card scheme. *)
Definition deck_ok (sh : 8.-tuple 'I_8) : bool := uniq sh.

(** heart_set — the set of positions of sh holding a heart.
    @intent: the four-subset of P^1(F_7) carrying the secret. *)
Definition heart_set (sh : 8.-tuple 'I_8) : {set 'I_8} :=
  [set i | is_heart (tnth sh i)].

(** subset_class — the equianharmonic verdict of the cross-ratio read on the
    four positions of a subset in increasing order.
    @intent: the PGL(2,7) orbit class of a four-subset of the deck. *)
Definition subset_class (S : {set 'I_8}) : bool :=
  match sort (fun i j : 'I_8 => (val i <= val j)%N) (enum S) with
  | [:: a; b; c; d] => equianharmonic (cross_ratio a b c d)
  | _ => false
  end.

(** orbit_class — the orbit class of the heart four-subset of a deck.
    @intent: the one-bit secret dealt by the eight-card PGL(2,7) scheme. *)
Definition orbit_class (sh : 8.-tuple 'I_8) : bool :=
  subset_class (heart_set sh).

(* -------------------------------------------------------------------------- *)
(* Bridge from the set classifier to the nat verdict, and perm-invariance.    *)
(* -------------------------------------------------------------------------- *)

(* subset_class factors through the code verdict of the subset's elements. *)
Local Lemma subset_classE (S : {set 'I_8}) :
  subset_class S = nclass (map val (enum S)).
Proof.
rewrite /subset_class /nclass.
have -> : sort leq [seq val i | i <- enum S]
        = map val (sort (fun i j : 'I_8 => (val i <= val j)%N) (enum S)).
  by rewrite sort_map.
by case: (sort _ (enum S)) => [|a [|b [|c [|d [|? ?]]]]].
Qed.

(* The verdict depends only on the multiset of codes. *)
Local Lemma nclass_perm (L1 L2 : seq nat) :
  perm_eq L1 L2 -> nclass L1 = nclass L2.
Proof.
by move=> /(perm_sortP leq_total leq_trans anti_leq) Hs; rewrite /nclass Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* The three generators act on the codes by their nat permutation tables.     *)
(* -------------------------------------------------------------------------- *)

Local Definition trn (a : nat) : nat := nth 0 [:: 1; 2; 3; 4; 5; 6; 0; 7] a.
Local Definition scn (a : nat) : nat := nth 0 [:: 0; 3; 6; 2; 5; 1; 4; 7] a.
Local Definition invn (a : nat) : nat := nth 0 [:: 7; 6; 3; 2; 5; 4; 1; 0] a.

Local Lemma gen0_val (i : 'I_8) :
  val ((tnth pgl27_gens (@Ordinal 3 0 isT)) i) = trn (val i).
Proof. by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE. Qed.

Local Lemma gen1_val (i : 'I_8) :
  val ((tnth pgl27_gens (@Ordinal 3 1 isT)) i) = scn (val i).
Proof. by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE. Qed.

Local Lemma gen2_val (i : 'I_8) :
  val ((tnth pgl27_gens (@Ordinal 3 2 isT)) i) = invn (val i).
Proof. by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE. Qed.

(* The enumeration of an injective image permutes the mapped enumeration. *)
Local Lemma enum_imset_perm (f : 'I_8 -> 'I_8) (S : {set 'I_8}) :
  injective f -> perm_eq (enum (f @: S)) (map f (enum S)).
Proof.
move=> finj; apply: uniq_perm; first exact: enum_uniq.
  by rewrite map_inj_uniq // enum_uniq.
move=> x; rewrite mem_enum; apply/imsetP/mapP => [[y yS ->]|[y]].
  by exists y => //; rewrite mem_enum.
by rewrite mem_enum => yS ->; exists y.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ground Moebius-invariance of the verdict, one exhaustive check per table.  *)
(* -------------------------------------------------------------------------- *)

Local Definition distinct4 (a b c d : nat) : bool :=
  (a != b) && (a != c) && (a != d) && (b != c) && (b != d) && (c != d).

(* For every distinct code quadruple, the table image has the same verdict. *)
Local Definition gen_ok (g : nat -> nat) : bool :=
  all (fun a => all (fun b => all (fun c => all (fun d =>
    distinct4 a b c d ==>
    (nclass [:: g a; g b; g c; g d] == nclass [:: a; b; c; d]))
    (iota 0 8)) (iota 0 8)) (iota 0 8)) (iota 0 8).

Local Lemma gen_ok_trn : gen_ok trn. Proof. by vm_compute. Qed.
Local Lemma gen_ok_scn : gen_ok scn. Proof. by vm_compute. Qed.
Local Lemma gen_ok_invn : gen_ok invn. Proof. by vm_compute. Qed.

(* Read the ground check off at a specific in-range distinct quadruple. *)
Local Lemma gen_class (g : nat -> nat) (a b c d : nat) :
  gen_ok g -> (a < 8)%N -> (b < 8)%N -> (c < 8)%N -> (d < 8)%N ->
  distinct4 a b c d -> nclass [:: g a; g b; g c; g d] = nclass [:: a; b; c; d].
Proof.
have Hin : forall x, (x < 8)%N -> x \in iota 0 8.
  by move=> x Hx; rewrite mem_iota.
move=> gok Ha Hb Hc Hd Hdist.
move: gok => /allP/(_ _ (Hin _ Ha))/allP/(_ _ (Hin _ Hb)).
move=> /allP/(_ _ (Hin _ Hc))/allP/(_ _ (Hin _ Hd)).
by move=> /implyP/(_ Hdist)/eqP.
Qed.

(* A list without exactly four elements has verdict false. *)
Local Lemma nclass_neq4 (M : seq nat) : size M != 4 -> nclass M = false.
Proof.
rewrite /nclass => Hne; move: (size_sort leq M) => Hsz.
case E: (sort leq M) Hsz => [|a [|b [|c [|d [|e l]]]]] //= Hsz.
by move: Hne; rewrite -Hsz eqxx.
Qed.

(* Mapping a distinct in-range code list through a table keeps the verdict. *)
Local Lemma nclass_map_gen (g : nat -> nat) (M : seq nat) :
  gen_ok g -> uniq M -> all (fun x => (x < 8)%N) M ->
  nclass (map g M) = nclass M.
Proof.
move=> gok uM aM.
have [H4|Hn4] := altP (size M =P 4); last first.
  by rewrite nclass_neq4 ?size_map // nclass_neq4.
move: uM aM; case: M H4 => [|a [|b [|c [|d [|e l]]]]] //= _ uM aM.
case/and5P: aM => Ha Hb Hc Hd _.
apply: (@gen_class g a b c d gok Ha Hb Hc Hd).
move: uM; rewrite /distinct4 !inE !negb_or.
by move=> /and4P[/and3P[-> -> ->] /andP[-> ->] -> _].
Qed.

(* A generator perm preserves the subset classifier. *)
Local Lemma subset_class_gen (g0 : {perm 'I_8}) (g0n : nat -> nat) :
  gen_ok g0n -> (forall i, val (g0 i) = g0n (val i)) ->
  forall S : {set 'I_8}, subset_class (g0 @: S) = subset_class S.
Proof.
move=> gok Hval S; rewrite !subset_classE.
transitivity (nclass (map val (map g0 (enum S)))).
  apply: nclass_perm; apply: perm_map.
  by apply: enum_imset_perm; exact: perm_inj.
have -> : map val (map g0 (enum S)) = map g0n (map val (enum S)).
  by rewrite -!map_comp; apply: eq_map => i /=; exact: Hval.
apply: nclass_map_gen => //.
  by rewrite map_inj_uniq ?enum_uniq //; exact: val_inj.
by apply/allP => x /mapP[i _ ->]; exact: ltn_ord.
Qed.

(* -------------------------------------------------------------------------- *)
(* Lift from the generators to the whole shuffle group via a stabiliser.      *)
(* -------------------------------------------------------------------------- *)

(* Perms preserving subset_class on every subset. *)
Local Definition stabp : {set {perm 'I_8}} :=
  [set g : {perm 'I_8} |
     [forall S : {set 'I_8}, subset_class (g @: S) == subset_class S]].

Local Lemma stabpP (g : {perm 'I_8}) :
  reflect (forall S : {set 'I_8}, subset_class (g @: S) = subset_class S)
          (g \in stabp).
Proof.
rewrite inE; apply: (iffP forallP) => H S; by [apply/eqP | apply/eqP].
Qed.

Local Lemma group_set_stabp : group_set stabp.
Proof.
apply/group_setP; split.
  apply/stabpP => S; congr subset_class.
  apply/setP => x; apply/imsetP/idP => [[y yS ->]|xS].
    by rewrite perm1.
  by exists x => //; rewrite perm1.
move=> g h /stabpP Hg /stabpP Hh; apply/stabpP => S.
have -> : ((g * h)%g) @: S = h @: (g @: S).
  by rewrite -imset_comp; apply: eq_imset => x; rewrite permM.
by rewrite Hh Hg.
Qed.

Local Lemma gens_sub_stabp :
  [set tnth pgl27_gens i | i : 'I_3] \subset stabp.
Proof.
apply/subsetP => x /imsetP[i _ ->]; apply/stabpP => S.
case: i => -[|[|[|//]]] Hlt.
- exact: (@subset_class_gen _ trn gen_ok_trn gen0_val S).
- exact: (@subset_class_gen _ scn gen_ok_scn gen1_val S).
- exact: (@subset_class_gen _ invn gen_ok_invn gen2_val S).
Qed.

Local Canonical stabp_group := Group group_set_stabp.

Local Lemma G_sub_stabp : pgg_G pgl27_M \subset stabp.
Proof. by rewrite gen_subG; exact: gens_sub_stabp. Qed.

(* -------------------------------------------------------------------------- *)
(* Invariance of the classifier and stability of the deck.                    *)
(* -------------------------------------------------------------------------- *)

(** orbit_class_invariant — the orbit classifier is invariant under the
    coordinate action of any element of the shuffle group.
    @main security: privacy rests on the shuffle not moving the orbit class. *)
Lemma orbit_class_invariant (g : pgg_gT pgl27_M) (sh : 8.-tuple 'I_8) :
  g \in pgg_G pgl27_M ->
  orbit_class [tuple tnth sh (@pgg_rho pgl27_M g i) | i < 8] = orbit_class sh.
Proof.
move=> gG; rewrite /orbit_class.
have Hheart : heart_set [tuple tnth sh (@pgg_rho pgl27_M g i) | i < 8]
            = (g^-1)%g @: heart_set sh.
  apply/setP => x; rewrite inE tnth_mktuple.
  apply/idP/imsetP => [Hx | [y]].
    by exists (g x); [rewrite inE | rewrite permK].
  by rewrite inE => Hy ->; rewrite permKV.
rewrite Hheart.
have gV : (g^-1)%g \in pgg_G pgl27_M by rewrite groupV.
have /stabpP Hstab : (g^-1)%g \in stabp by exact: (subsetP G_sub_stabp).
by rewrite Hstab.
Qed.

(** deck_stable — the coordinate action of a shuffle keeps cards distinct.
    @main correctness: a re-dealt arrangement is again a valid deck. *)
Lemma deck_stable (g : pgg_gT pgl27_M) (sh : 8.-tuple 'I_8) :
  g \in pgg_G pgl27_M ->
  deck_ok [tuple tnth sh (@pgg_rho pgl27_M g i) | i < 8] = deck_ok sh.
Proof.
move=> _; rewrite /deck_ok; apply: perm_uniq.
rewrite (_ : [tuple tnth sh (@pgg_rho pgl27_M g i) | i < 8]
           = [seq tnth sh (g i) | i <- enum 'I_8] :> seq _); last first.
  by apply: eq_map => i.
rewrite (map_comp (tnth sh) g (enum 'I_8)).
rewrite -[X in perm_eq _ X](map_tnth_enum sh).
apply: perm_map; apply: uniq_perm.
- by rewrite map_inj_uniq ?enum_uniq //; exact: perm_inj.
- exact: enum_uniq.
- move=> x; rewrite mem_enum inE; apply/mapP.
  by exists ((g^-1)%g x); [rewrite mem_enum inE | rewrite permKV].
Qed.

(* -------------------------------------------------------------------------- *)
(* Population of both orbit classes by explicit distinct-card decks.          *)
(* -------------------------------------------------------------------------- *)

Local Definition ord8_enum : seq 'I_8 :=
  [:: @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT; @Ordinal 8 3 isT;
      @Ordinal 8 4 isT; @Ordinal 8 5 isT; @Ordinal 8 6 isT; @Ordinal 8 7 isT].

Local Lemma enum_ord8 : enum 'I_8 = ord8_enum.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(* Ground form of orbit_class: verdict of the heart codes filtered by place. *)
Local Lemma orbit_classE (sh : 8.-tuple 'I_8) :
  orbit_class sh
  = nclass (map val [seq i <- ord8_enum | is_heart (tnth sh i)]).
Proof.
rewrite /orbit_class subset_classE; apply: nclass_perm; apply: perm_map.
apply: uniq_perm; first exact: enum_uniq.
  by rewrite filter_uniq // -enum_ord8 enum_uniq.
by move=> x; rewrite mem_enum inE mem_filter -enum_ord8 mem_enum inE andbT.
Qed.

(** orbit_encode — a distinct-card deck whose heart four-subset has class b.
    @intent: the encoder dealing a chosen one-bit secret. *)
Definition orbit_encode (b : bool) : 8.-tuple 'I_8 :=
  if b then [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
                   @Ordinal 8 4 isT; @Ordinal 8 3 isT; @Ordinal 8 5 isT;
                   @Ordinal 8 6 isT; @Ordinal 8 7 isT]
  else [tuple @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT;
              @Ordinal 8 3 isT; @Ordinal 8 4 isT; @Ordinal 8 5 isT;
              @Ordinal 8 6 isT; @Ordinal 8 7 isT].

(** orbit_encodeK — orbit_encode is a section of orbit_class.
    @main correctness: the encoder deals exactly the requested secret. *)
Lemma orbit_encodeK (s : bool) : orbit_class (orbit_encode s) = s.
Proof. by case: s; rewrite orbit_classE; vm_compute. Qed.

(** orbit_encode_deck — every encoded arrangement is a valid deck.
    @main correctness: the encoder outputs distinct cards. *)
Lemma orbit_encode_deck (s : bool) : deck_ok (orbit_encode s).
Proof. by case: s; vm_compute. Qed.

(** orbit_populated — both orbit classes occur among distinct-card decks.
    @main correctness: the secret space is covered by valid arrangements. *)
Lemma orbit_populated (b : bool) :
  exists sh : 8.-tuple 'I_8, deck_ok sh /\ orbit_class sh = b.
Proof.
exists (orbit_encode b); split.
- exact: orbit_encode_deck.
- exact: orbit_encodeK.
Qed.

(* -------------------------------------------------------------------------- *)
(* The forty-two / twenty-eight split of the seventy four-subsets.            *)
(* -------------------------------------------------------------------------- *)

(* The four-subset of positions whose codes occur in a code list. *)
Local Definition list_to_set (L : seq nat) : {set 'I_8} :=
  [set i : 'I_8 | val i \in L].

(* A strictly ascending four-list of codes below eight. *)
Local Definition asc4 (L : seq nat) : bool :=
  [&& sorted ltn L, all (fun n => (n < 8)%N) L & size L == 4].

(* The seventy strictly ascending four-lists of codes below eight. *)
Local Definition sorted4 : seq (seq nat) :=
  flatten [seq flatten [seq flatten [seq [seq [:: a; b; c; d]
    | d <- iota c.+1 (8 - c.+1)]
    | c <- iota b.+1 (8 - b.+1)]
    | b <- iota a.+1 (8 - a.+1)]
    | a <- iota 0 8].

(* sorted4 lists no code quadruple twice. @composes: orbit_class_split *)
Local Lemma sorted4_uniq : uniq sorted4.
Proof. by vm_compute. Qed.

(* Every element of sorted4 is a strictly ascending four-list below eight. *)
Local Lemma sorted4_asc : all asc4 sorted4.
Proof. by vm_compute. Qed.

(* sorted4 enumerates every strictly ascending four-list below eight. *)
Local Lemma sorted4_complete (L : seq nat) : asc4 L -> L \in sorted4.
Proof.
case: L => [|a [|b [|c [|d [|e l]]]]] A //.
all: try by case/and3P: A => _ _ /eqP.
case/and3P: A => Hsort Hall _.
move: Hsort; rewrite /= => /andP[Hab /andP[Hbc Hcd]].
move: Hall => /= /andP[Ha /andP[Hb /andP[Hc /andP[Hd _]]]].
move: Hcd; rewrite andbT => Hcd.
apply/flatten_mapP; exists a; first by rewrite mem_iota add0n Ha.
apply/flatten_mapP; exists b; first by rewrite mem_iota (subnKC Ha) Hab Hb.
apply/flatten_mapP; exists c; first by rewrite mem_iota (subnKC Hb) Hbc Hc.
apply/mapP; exists d; first by rewrite mem_iota (subnKC Hc) Hcd Hd.
by [].
Qed.

(* The code list of a subset's enumeration is strictly ascending. *)
Local Lemma sorted_val_enum (S : {set 'I_8}) : sorted ltn (map val (enum S)).
Proof.
rewrite sorted_map.
have He : enum S = [seq x <- enum 'I_8 | x \in S]
  by rewrite enumT -deprecated_filter_index_enum.
rewrite He; apply: sorted_filter.
  by move=> y x z; apply: ltn_trans.
by rewrite -sorted_map val_enum_ord; exact: iota_ltn_sorted.
Qed.

(* list_to_set is a section of the code list of the enumeration. *)
Local Lemma list_to_setK (S : {set 'I_8}) :
  list_to_set (map val (enum S)) = S.
Proof.
by apply/setP => i; rewrite /list_to_set inE (mem_map val_inj) mem_enum.
Qed.

(* The code list of list_to_set L is a permutation of L for ascending L. *)
Local Lemma perm_list_to_set (L : seq nat) :
  asc4 L -> perm_eq (map val (enum (list_to_set L))) L.
Proof.
move=> /and3P[Hsort Hall _].
apply: uniq_perm.
- rewrite (map_inj_uniq val_inj); exact: enum_uniq.
- exact: (sorted_uniq ltn_trans ltnn Hsort).
- move=> n; apply/mapP/idP => [[i Hi ->]|Hn];
    first by move: Hi; rewrite mem_enum inE.
  have Hn8 : (n < 8)%N by move/allP: Hall => /(_ n Hn).
  by exists (Ordinal Hn8); [rewrite mem_enum inE|].
Qed.

(* An ascending four-list codes a four-element position subset. *)
Local Lemma card_list_to_set (L : seq nat) : asc4 L -> #|list_to_set L| = 4.
Proof.
move=> A; rewrite cardE -(size_map val (enum (list_to_set L)))
  (perm_size (@perm_list_to_set L A)).
by move: A => /and3P[_ _ /eqP ->].
Qed.

(* The subset classifier of list_to_set L is the code verdict of L. *)
Local Lemma subset_class_list_to_set (L : seq nat) :
  asc4 L -> subset_class (list_to_set L) = nclass L.
Proof.
by move=> A; rewrite subset_classE; apply: nclass_perm;
   exact: perm_list_to_set.
Qed.

(* list_to_set is injective on strictly ascending four-lists. *)
Local Lemma list_to_set_inj (L1 L2 : seq nat) :
  asc4 L1 -> asc4 L2 -> list_to_set L1 = list_to_set L2 -> L1 = L2.
Proof.
move=> A1 A2 Heq; apply: (irr_sorted_eq ltn_trans ltnn).
- by case/and3P: A1.
- by case/and3P: A2.
- move=> n; rewrite -(perm_mem (@perm_list_to_set L1 A1)) Heq.
  by rewrite (perm_mem (@perm_list_to_set L2 A2)).
Qed.

(* A four-subset class count equals the code-level count over sorted4. *)
(* @composes: orbit_class_split *)
Local Lemma class_count (p : {set 'I_8} -> bool) (pn : seq nat -> bool) :
  (forall L, asc4 L -> p (list_to_set L) = pn L) ->
  #|[set S : {set 'I_8} | (#|S| == 4) && p S]| = count pn sorted4.
Proof.
move=> Hp.
have key : forall S : {set 'I_8}, #|S| = 4 -> asc4 (map val (enum S)).
  move=> S HcS; rewrite /asc4 sorted_val_enum /=; apply/andP; split.
    by apply/allP => n /mapP[i _ ->]; exact: ltn_ord.
  by rewrite size_map -cardE HcS.
have Huniq : uniq [seq list_to_set L | L <- filter pn sorted4].
  rewrite map_inj_in_uniq; last first.
    move=> L1 L2; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].
    by apply: list_to_set_inj; apply: (allP sorted4_asc).
  by rewrite filter_uniq // sorted4_uniq.
have Hmem : [set S : {set 'I_8} | (#|S| == 4) && p S]
              =i [seq list_to_set L | L <- filter pn sorted4].
  move=> S; rewrite inE; apply/idP/idP.
    move=> /andP[/eqP HcS HpS]; apply/mapP.
    exists (map val (enum S)); last by rewrite list_to_setK.
    rewrite mem_filter (@sorted4_complete (map val (enum S)) (key S HcS)) andbT.
    by rewrite -(Hp _ (key S HcS)) list_to_setK.
  move=> /mapP[L]; rewrite mem_filter => /andP[HpnL HinL] ->.
  have AL : asc4 L by apply: (allP sorted4_asc).
  by rewrite (@card_list_to_set L AL) eqxx (Hp _ AL).
rewrite (eq_card Hmem).
transitivity (size [seq list_to_set L | L <- filter pn sorted4]).
  by apply/card_uniqP.
by rewrite size_map size_filter.
Qed.

(** orbit_class_split — twenty-eight of the seventy four-subsets of the
    projective line are equianharmonic.
    @main architecture: the classifier splits the seventy four-subsets into
    forty-two harmonic and twenty-eight equianharmonic, identifying the two
    secret classes with the two PGL(2,7) orbit sizes on four-subsets. *)
Lemma orbit_class_split :
  #|[set S : {set 'I_8} | (#|S| == 4) && subset_class S]| = 28.
Proof.
rewrite (@class_count subset_class nclass subset_class_list_to_set).
by vm_compute.
Qed.

(** orbit_class_split_complement — forty-two of the seventy four-subsets of
    the projective line are harmonic.
    @main architecture: the harmonic orbit has size forty-two, the complement
    of the twenty-eight equianharmonic four-subsets. *)
Lemma orbit_class_split_complement :
  #|[set S : {set 'I_8} | (#|S| == 4) && ~~ subset_class S]| = 42.
Proof.
have Hneg : forall L, asc4 L -> ~~ subset_class (list_to_set L) = ~~ nclass L
  by move=> L AL; rewrite (@subset_class_list_to_set L AL).
by rewrite (@class_count (fun S => ~~ subset_class S)
             (fun L => ~~ nclass L) Hneg);
  vm_compute.
Qed.

(* -------------------------------------------------------------------------- *)
(* Each Boolean fiber of the classifier is one orbit of the shuffle group.    *)
(* -------------------------------------------------------------------------- *)

(** subset_class_invariant — the four-subset classifier is invariant under
    the image action of a shuffle-group element.
    @main security: the shuffle moves a four-subset without moving its
    orbit class. *)
Lemma subset_class_invariant (g : pgg_gT pgl27_M) (S : {set 'I_8}) :
  g \in pgg_G pgl27_M -> subset_class (g @: S) = subset_class S.
Proof. by move=> gG; move/stabpP: (subsetP G_sub_stabp _ gG); apply. Qed.

(* The word layer: generator indices act on codes by the tables above. *)
Local Definition wgenn (i : nat) : nat -> nat :=
  if i == 0 then trn else if i == 1 then scn else invn.

(* Application of a word, left to right, to a single code. *)
Local Definition papply (w : seq nat) (a : nat) : nat :=
  foldl (fun x i => wgenn i x) a w.

(* The generator perm selected by a word index. *)
Local Definition gen_of (i : nat) : {perm 'I_8} :=
  tnth pgl27_gens (if i == 0 then @Ordinal 3 0 isT
                   else if i == 1 then @Ordinal 3 1 isT
                   else @Ordinal 3 2 isT).

(* A word folded into the composite shuffle permutation. *)
Local Definition word_perm (w : seq nat) : {perm 'I_8} :=
  foldl (fun g i => (g * gen_of i)%g) 1%g w.

Local Lemma gen_of_val (i : nat) (x : 'I_8) :
  val (gen_of i x) = wgenn i (val x).
Proof.
rewrite /gen_of /wgenn; case: (i == 0); first exact: gen0_val.
by case: (i == 1); [exact: gen1_val | exact: gen2_val].
Qed.

Local Lemma gen_of_mem (i : nat) : gen_of i \in pgg_G pgl27_M.
Proof.
apply: mem_gen; apply/imsetP; rewrite /gen_of.
case: (i == 0); first by exists (@Ordinal 3 0 isT).
case: (i == 1); first by exists (@Ordinal 3 1 isT).
by exists (@Ordinal 3 2 isT).
Qed.

Local Lemma word_perm_mem (w : seq nat) : word_perm w \in pgg_G pgl27_M.
Proof.
rewrite /word_perm.
have g1 : 1%g \in pgg_G pgl27_M by exact: group1.
elim: w (1%g) g1 => [|i w IH] g gG //=.
by apply: IH; apply: groupM => //; exact: gen_of_mem.
Qed.

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

(* -------------------------------------------------------------------------- *)
(* Finite reachability certificate: a fueled BFS over four-subsets.           *)
(* -------------------------------------------------------------------------- *)

(* One generator step on a four-subset, in ascending canonical form. *)
Local Definition sstep (i : nat) (L : seq nat) : seq nat :=
  sort leq (map (wgenn i) L).

(* Fueled BFS over four-subsets, one carrying word per reached subset. *)
Local Fixpoint set_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | S f =>
    let nxt := flatten
      [seq [seq (sstep i Lw.1, rcons Lw.2 i)
             | i <- [:: 0; 1; 2]] | Lw <- seen] in
    let add := foldl (fun acc Lw =>
      if has (fun sw : seq nat * seq nat => sw.1 == Lw.1) (seen ++ acc)
      then acc else rcons acc Lw) [::] nxt in
    if size add == 0 then seen else set_bfs f (seen ++ add)
  end.

(* The representative four-subset of each Boolean class, as a code list. *)
Local Definition rep_list (b : bool) : seq nat :=
  if b then [:: 0; 1; 2; 4] else [:: 0; 1; 2; 3].

Local Definition set_table (b : bool) : seq (seq nat * seq nat) :=
  set_bfs 12 [:: (rep_list b, [::])].

(* Every ascending four-list of verdict b carries a word from rep_list b.
   The check recomputes each word from scratch, so a BFS bookkeeping error
   cannot make it true. *)
Local Definition set_table_ok (b : bool) : bool :=
  all (fun L => (nclass L == b) ==>
         has (fun sw : seq nat * seq nat =>
                sort leq (map (papply sw.2) (rep_list b)) == L)
             (set_table b))
      sorted4.

Local Lemma set_table_okT : set_table_ok true. Proof. by vm_compute. Qed.
Local Lemma set_table_okF : set_table_ok false. Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* From the code-level certificate to subsets of the projective line.         *)
(* -------------------------------------------------------------------------- *)

(* The image of a code-coded subset is coded by the word applied codewise. *)
Local Lemma word_perm_imset (w : seq nat) (L : seq nat) :
  all (fun n => (n < 8)%N) L ->
  word_perm w @: list_to_set L = list_to_set (map (papply w) L).
Proof.
move=> HL; apply/setP => x; apply/imsetP/idP => [[y]|Hx].
  rewrite inE => yL ->; rewrite inE; apply/mapP.
  by exists (val y); rewrite // word_perm_val.
move: Hx; rewrite inE => /mapP[a aL Ha].
have Ha8 : (a < 8)%N by move/allP: HL => /(_ a aL).
exists (Ordinal Ha8); first by rewrite inE.
by apply/val_inj; rewrite word_perm_val.
Qed.

(* list_to_set reads membership only, so sorting the code list is invisible. *)
Local Lemma list_to_set_sort (L : seq nat) :
  list_to_set (sort leq L) = list_to_set L.
Proof. by apply/setP => i; rewrite !inE mem_sort. Qed.

(* The code list of a four-subset's enumeration is an ascending four-list. *)
Local Lemma asc4_val_enum (S : {set 'I_8}) :
  #|S| = 4 -> asc4 (map val (enum S)).
Proof.
move=> HcS; rewrite /asc4 sorted_val_enum /=; apply/andP; split.
  by apply/allP => n /mapP[i _ ->]; exact: ltn_ord.
by rewrite size_map -cardE HcS.
Qed.

(* Every four-subset is a shuffle image of the representative of its class. *)
Local Lemma subset_class_reach (S : {set 'I_8}) :
  #|S| = 4 ->
  exists w : seq nat,
    S = word_perm w @: list_to_set (rep_list (subset_class S)).
Proof.
move=> HcS.
have AL : asc4 (map val (enum S)) by exact: asc4_val_enum.
have Hcl : nclass (map val (enum S)) = subset_class S by rewrite subset_classE.
have Hmem := sorted4_complete _ AL.
have Hok : set_table_ok (subset_class S).
  by case: (subset_class S); [exact: set_table_okT | exact: set_table_okF].
have H8 : all (fun n => (n < 8)%N) (rep_list (subset_class S))
  by case: (subset_class S).
move: Hok => /allP/(_ _ Hmem)/implyP.
rewrite Hcl eqxx => /(_ isT)/hasP[[L w] /= _ /eqP Hw].
exists w; rewrite (word_perm_imset w _ H8).
by rewrite -list_to_set_sort Hw list_to_setK.
Qed.

(* -------------------------------------------------------------------------- *)
(* The orbit split.                                                           *)
(* -------------------------------------------------------------------------- *)

(* A product of shuffles acts by successive images. *)
Local Lemma imsetM (g h : {perm 'I_8}) (A : {set 'I_8}) :
  (g * h)%g @: A = h @: (g @: A).
Proof. by rewrite -imset_comp; apply: eq_imset => x; rewrite permM. Qed.

(* The inverse shuffle undoes the image of a shuffle. *)
Local Lemma perm_imsetK (g : {perm 'I_8}) (A : {set 'I_8}) :
  (g^-1)%g @: (g @: A) = A.
Proof.
apply/setP => x; apply/imsetP/idP => [[y /imsetP[z zA ->] ->]|xA].
  by rewrite permK.
by exists (g x); [apply/imsetP; exists x | rewrite permK].
Qed.

(** subset_class_orbit — two four-subsets of the projective line carry the
    same classifier value exactly when one is the shuffle image of the other.
    @main architecture: each Boolean fiber of the classifier is a single
    orbit of the PGL(2,7) shuffle group on four-subsets. *)
Lemma subset_class_orbit (S T : {set 'I_8}) :
  #|S| = 4 -> #|T| = 4 ->
  (subset_class S = subset_class T <->
   exists g : pgg_gT pgl27_M, g \in pgg_G pgl27_M /\ T = g @: S).
Proof.
move=> HcS HcT; split => [Hcl|[g [gG ->]]]; last first.
  by rewrite (subset_class_invariant _ _ gG).
have [w1 Hw1] := subset_class_reach _ HcS.
have [w2 Hw2] := subset_class_reach _ HcT.
rewrite Hcl in Hw1.
exists ((word_perm w1)^-1 * word_perm w2)%g; split.
  by apply: groupM; [rewrite groupV|]; exact: word_perm_mem.
by rewrite Hw2 Hw1 imsetM perm_imsetK.
Qed.

(** subset_class_orbitE — the orbit of a four-subset under the shuffle group
    is the classifier fiber it belongs to.
    @main architecture: the equianharmonic fiber and the harmonic fiber are
    the two orbits of the PGL(2,7) shuffle group on four-subsets. *)
Lemma subset_class_orbitE (S : {set 'I_8}) :
  #|S| = 4 ->
  orbit 'P^* (pgg_G pgl27_M) S
  = [set T : {set 'I_8} | (#|T| == 4) && (subset_class T == subset_class S)].
Proof.
move=> HcS; apply/setP => T; rewrite inE.
apply/orbitP/andP => [[g gG <-]|[/eqP HcT /eqP Hcl]].
  have ginj : injective g by exact: perm_inj.
  rewrite (card_imset _ ginj) HcS eqxx /=; split=> //; apply/eqP.
  exact: (subset_class_invariant g S gG).
have [g [gG ->]] : exists g : pgg_gT pgl27_M,
    g \in pgg_G pgl27_M /\ T = g @: S
  by apply/(subset_class_orbit S T HcS HcT); exact: (esym Hcl).
by exists g.
Qed.

(* -------------------------------------------------------------------------- *)
(* Probe-only checks, spec sections 6.5 and 6.6.                              *)
(* -------------------------------------------------------------------------- *)

(* 6.5: the two chosen representatives are four-subsets of the projective
   line, and they carry opposite classifier values. *)
Lemma rep_card_class :
  [/\ #|list_to_set [:: 0; 1; 2; 4]| = 4,
      #|list_to_set [:: 0; 1; 2; 3]| = 4,
      subset_class (list_to_set [:: 0; 1; 2; 4]) = true &
      subset_class (list_to_set [:: 0; 1; 2; 3]) = false].
Proof.
have A1 : asc4 [:: 0; 1; 2; 4] by vm_compute.
have A2 : asc4 [:: 0; 1; 2; 3] by vm_compute.
split.
- exact: (card_list_to_set _ A1).
- exact: (card_list_to_set _ A2).
- by rewrite (subset_class_list_to_set _ A1); vm_compute.
- by rewrite (subset_class_list_to_set _ A2); vm_compute.
Qed.

(* 6.6, at the level of the theorem rather than the certificate: the two
   representatives are not shuffle-related.  The forward implication of
   subset_class_orbit is therefore not vacuous, and the two fibers are two
   distinct orbits rather than one. *)
Lemma orbit_mutation_check :
  ~ (exists g : pgg_gT pgl27_M,
       g \in pgg_G pgl27_M /\
       list_to_set [:: 0; 1; 2; 4] = g @: list_to_set [:: 0; 1; 2; 3]).
Proof.
case=> g [gG Heq].
have A1 : asc4 [:: 0; 1; 2; 4] by vm_compute.
have A2 : asc4 [:: 0; 1; 2; 3] by vm_compute.
have Hinv := subset_class_invariant g (list_to_set [:: 0; 1; 2; 3]) gG.
rewrite -Heq (subset_class_list_to_set _ A1) in Hinv.
rewrite (subset_class_list_to_set _ A2) in Hinv.
by move: Hinv; vm_compute.
Qed.

Print Assumptions subset_class_invariant.
Print Assumptions subset_class_orbit.
Print Assumptions subset_class_orbitE.
Print Assumptions orbit_mutation_check.
