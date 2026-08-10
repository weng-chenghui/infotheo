(* Probe round 2: the five-card all-reveal-cases formal core, elaborated at   *)
(* the real imported carrier of five_card_leakage.v.  Ledger rows R1-R5.      *)
(* Spec: docs/superpowers/specs/                                              *)
(*   2026-08-10-five-card-all-reveal-cases-design.md                          *)
(*                                                                            *)
(* Probe bookkeeping, collected here so every declaration below carries only  *)
(* a declarative statement comment:                                           *)
(* - mathcomp's div supplies "_ %% _" for val_fc_sigma_fun and for the       *)
(*   rotation arithmetic inside ViewT_sigma; five_card_group supplies         *)
(*   fc_sigma_fun, fc_sigma_inv and fc_sigmaK.  The name fc_sigma_funE is     *)
(*   already taken by five_card_program.v:128 for a different equation, so    *)
(*   the value computation is val_fc_sigma_fun.                               *)
(* - five_card_leakage's section is discharged over R, so Omega, arr,         *)
(*   card_Omega20 and count_pr carry no explicit R while P, Secret and ViewA  *)
(*   take one; those three are pinned by Local Notation.                      *)
(* - fc_sigmaKV is the inverse-direction cancel, absent from five_card_group  *)
(*   (which states only fc_sigmaK), so it is proved here.                     *)
(* - leak_k3_gap is the only Admitted declaration; its fibre tables are in    *)
(*   the spec and it is discharged from the leak_k3 template at              *)
(*   transcription.  The probe's leak_view_rest escape hatch is absent: all   *)
(*   32 branches of leak_view_set are real chains.                            *)
(* - map_tnth, exists_ord5, setb5_eq and the leakE<n> read-off lemmas are     *)
(*   local infrastructure introduced by this round.                           *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program five_card_leakage five_card_group.
From mathcomp Require Import lra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section probe_round2.

Variable R : realType.

Local Open Scope ring_scope.

Local Notation P := (P R).
Local Notation Secret := (Secret R).
Local Notation ViewA := (ViewA R).

Local Notation p0 := (Ordinal (isT : (0 < 5)%N)).
Local Notation p1 := (Ordinal (isT : (1 < 5)%N)).
Local Notation p2 := (Ordinal (isT : (2 < 5)%N)).
Local Notation p3 := (Ordinal (isT : (3 < 5)%N)).
Local Notation p4 := (Ordinal (isT : (4 < 5)%N)).

(* ---- views indexed by a position tuple and by a position set ---- *)

(* ViewT t reads the card colours of the dealt row at the positions listed
   by t, as a tuple of bits of the same length. *)
Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

(* ViewS S is the view at the positions of S, listed in ascending order by
   the canonical enumeration tuple of S. *)
Definition ViewS (S : {set 'I_5}) : {RV P -> #|S|.-tuple bool} :=
  ViewT (enum_tuple S).

(* adjacent S holds when S is a pair of positions at cyclic distance one,
   that is a pair {i, sigma i} for the five-cycle shift sigma. *)
Definition adjacent (S : {set 'I_5}) : bool :=
  [exists i : 'I_5, S == [set i; fc_sigma_fun i]].

(* leak S is the exact mutual information, in bits, between the den Boer
   secret and the view at S: zero below two revealed cards, two distinct
   positive values at two cards according to adjacency, 6/5 - (9/20) log 3
   at three cards, and the full secret entropy from four cards on. *)
Definition leak (S : {set 'I_5}) : R :=
  match #|S| with
  | 0 => 0
  | 1 => 0
  | 2 => if adjacent S
         then 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R
         else 5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
              - (7%:R / 20%:R) * log 7%:R
  | 3 => 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R
  | _ => 2%:R - (3%:R / 4%:R) * log 3%:R  (* #|S| >= 4 determines the secret *)
  end.

(* ---- subsets of 'I_5 presented by their five membership bits ---- *)

(* setb5 b0 b1 b2 b3 b4 is the subset of 'I_5 whose membership vector is
   the bit list [b0; b1; b2; b3; b4]. *)
Definition setb5 (b0 b1 b2 b3 b4 : bool) : {set 'I_5} :=
  [set i : 'I_5 | nth false [:: b0; b1; b2; b3; b4] (val i)].

(* Membership in setb5 is the bit at the position's index. *)
Lemma mem_setb5 (b0 b1 b2 b3 b4 : bool) (x : 'I_5) :
  (x \in setb5 b0 b1 b2 b3 b4) = nth false [:: b0; b1; b2; b3; b4] (val x).
Proof. by rewrite inE. Qed.

(* An existential quantifier over 'I_5 is the disjunction of its five
   instances. *)
Lemma exists_ord5 (q : pred 'I_5) :
  [exists i : 'I_5, q i] = [|| q p0, q p1, q p2, q p3 | q p4].
Proof.
have cases5 (i : 'I_5) : [|| i == p0, i == p1, i == p2, i == p3 | i == p4].
  by rewrite -!val_eqE; case: i => [[|[|[|[|[|m]]]]] Hm].
apply/existsP/idP => [[i qi]|].
  move: qi; case/orP: (cases5 i) => [|/orP[|/orP[|/orP[]]]] /eqP -> qi.
  - by rewrite qi.
  - by rewrite qi ?orbT.
  - by rewrite qi ?orbT.
  - by rewrite qi ?orbT.
  - by rewrite qi ?orbT.
by case/orP => [H|/orP[H|/orP[H|/orP[H|H]]]];
  [exists p0|exists p1|exists p2|exists p3|exists p4].
Qed.

(* Two bit-presented subsets are equal exactly when their bit vectors are. *)
Lemma setb5_eq (b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : bool) :
  (setb5 b0 b1 b2 b3 b4 == setb5 c0 c1 c2 c3 c4)
  = [&& b0 == c0, b1 == c1, b2 == c2, b3 == c3 & b4 == c4].
Proof.
apply/eqP/idP => [/setP hS|].
  move: (hS p0) (hS p1) (hS p2) (hS p3) (hS p4).
  rewrite !mem_setb5 /= => -> -> -> -> ->.
  by rewrite !eqxx.
by case/and5P => /eqP-> /eqP-> /eqP-> /eqP-> /eqP->.
Qed.

(* Adjacency of a bit-presented subset is the boolean condition that exactly
   two bits are set at cyclically consecutive positions. *)
Lemma adjacentE (b0 b1 b2 b3 b4 : bool) :
  adjacent (setb5 b0 b1 b2 b3 b4)
  = [|| [&& b0, b1, ~~ b2, ~~ b3 & ~~ b4],
        [&& ~~ b0, b1, b2, ~~ b3 & ~~ b4],
        [&& ~~ b0, ~~ b1, b2, b3 & ~~ b4],
        [&& ~~ b0, ~~ b1, ~~ b2, b3 & b4]
      | [&& b0, ~~ b1, ~~ b2, ~~ b3 & b4]].
Proof.
rewrite /adjacent exists_ord5.
have e0 : [set p0; fc_sigma_fun p0] = setb5 true true false false false.
  by apply/setP => x; rewrite mem_setb5 !inE -!val_eqE;
     case: x => [[|[|[|[|[|m]]]]] Hm].
have e1 : [set p1; fc_sigma_fun p1] = setb5 false true true false false.
  by apply/setP => x; rewrite mem_setb5 !inE -!val_eqE;
     case: x => [[|[|[|[|[|m]]]]] Hm].
have e2 : [set p2; fc_sigma_fun p2] = setb5 false false true true false.
  by apply/setP => x; rewrite mem_setb5 !inE -!val_eqE;
     case: x => [[|[|[|[|[|m]]]]] Hm].
have e3 : [set p3; fc_sigma_fun p3] = setb5 false false false true true.
  by apply/setP => x; rewrite mem_setb5 !inE -!val_eqE;
     case: x => [[|[|[|[|[|m]]]]] Hm].
have e4 : [set p4; fc_sigma_fun p4] = setb5 true false false false true.
  by apply/setP => x; rewrite mem_setb5 !inE -!val_eqE;
     case: x => [[|[|[|[|[|m]]]]] Hm].
rewrite e0 e1 e2 e3 e4 !setb5_eq.
by case: b0; case: b1; case: b2; case: b3; case: b4.
Qed.

(* Every subset of 'I_5 is bit-presented. *)
Lemma setb5_onto (S : {set 'I_5}) :
  exists b0 b1 b2 b3 b4 : bool, S = setb5 b0 b1 b2 b3 b4.
Proof.
exists (p0 \in S), (p1 \in S), (p2 \in S), (p3 \in S), (p4 \in S).
apply/setP => x; rewrite mem_setb5.
by case: x => [[|[|[|[|[|m]]]]] Hm] //=; congr (_ \in S); apply: val_inj.
Qed.

(* The indices enumerating a subset of 'I_5 described by a predicate on
   nat are that predicate's filter of the first five naturals. *)
Lemma enum_val5 (S : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in S) = q (val x)) ->
  map val (enum S) = filter q (iota 0 5).
Proof.
move=> hq; rewrite -val_enum_ord filter_map; congr (map _ _).
by rewrite {1}/enum_mem -enumT; apply: eq_filter => x /=; exact: hq.
Qed.

(* The cardinality of such a subset is the length of that filter. *)
Lemma card_val5 (S : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in S) = q (val x)) -> #|S| = size (filter q (iota 0 5)).
Proof. by move=> hq; rewrite cardE -(size_map val) (enum_val5 hq). Qed.

(* The cardinality of a bit-presented subset counts its set bits. *)
Lemma card_setb5 (b0 b1 b2 b3 b4 : bool) :
  #|setb5 b0 b1 b2 b3 b4|
  = size (filter (fun n => nth false [:: b0; b1; b2; b3; b4] n) (iota 0 5)).
Proof. by apply: card_val5 => x; exact: mem_setb5. Qed.

(* The enumeration indices of a bit-presented subset are the indices of its
   set bits, in increasing order. *)
Lemma enum_setb5 (b0 b1 b2 b3 b4 : bool) :
  map val (enum (setb5 b0 b1 b2 b3 b4))
  = filter (fun n => nth false [:: b0; b1; b2; b3; b4] n) (iota 0 5).
Proof. by apply: enum_val5 => x; exact: mem_setb5. Qed.

(* ---- leak read off from a cardinality and an adjacency ---- *)

Lemma leakE0 (S : {set 'I_5}) : #|S| = 0%N -> leak S = 0.
Proof. by rewrite /leak => ->. Qed.

Lemma leakE1 (S : {set 'I_5}) : #|S| = 1%N -> leak S = 0.
Proof. by rewrite /leak => ->. Qed.

Lemma leakE2adj (S : {set 'I_5}) : #|S| = 2%N -> adjacent S ->
  leak S = 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R.
Proof. by rewrite /leak => -> ->. Qed.

Lemma leakE2dist2 (S : {set 'I_5}) : #|S| = 2%N -> ~~ adjacent S ->
  leak S = 5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
           - (7%:R / 20%:R) * log 7%:R.
Proof. by rewrite /leak => -> /negbTE ->. Qed.

Lemma leakE3 (S : {set 'I_5}) : #|S| = 3%N ->
  leak S = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Proof. by rewrite /leak => ->. Qed.

Lemma leakE4 (S : {set 'I_5}) : #|S| = 4%N ->
  leak S = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof. by rewrite /leak => ->. Qed.

Lemma leakE5 (S : {set 'I_5}) : #|S| = 5%N ->
  leak S = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof. by rewrite /leak => ->. Qed.

(* ---- mutual information under an injective relabeling of the view ---- *)

(* Relabeling the alphabet of a random variable by an injection leaves its
   mutual information with any other random variable unchanged.  Upstream
   candidate, next to infotheo's injective_joint_entropy. *)
Lemma injective_mutual_info_RV (T' T U : finType) (X : {RV P -> T'})
    (Y : {RV P -> T}) (g : T -> U) :
  injective g -> `I( X ; g `o Y ) = `I( X ; Y ).
Proof.
move=> gi.
rewrite !mutual_info_RVE; congr (_ - _).
apply: cPr_centropy_RV_comp => x y Hy.
rewrite !cpr_eqE (pfwd1_comp Y y gi); congr (_ / _).
have hinj : injective (fun p : T' * T => (p.1, g p.2)).
  by move=> [a1 b1] [a2 b2] [] -> /gi ->.
by rewrite -(pfwd1_comp [% X, Y] (x, y) hinj).
Qed.

(* Cyclic rotation of a tuple is injective. *)
Lemma rot_tuple_inj (T : Type) k n :
  injective (fun t : k.-tuple T => rot_tuple n t).
Proof. by move=> x y /(congr1 val) /= /rot_inj /val_inj. Qed.

(* The view at a position tuple is the row read pointwise along that tuple. *)
Lemma ViewTE k (t : k.-tuple 'I_5) (w : Omega) :
  ViewT t w = map_tuple (fun j : 'I_5 => nth false (arr w) (val j)) t.
Proof. by apply: eq_from_tnth => i; rewrite /ViewT tnth_mktuple tnth_map. Qed.

(* Rotating the position tuple rotates the view tuple. *)
Lemma ViewT_rot k n (t : k.-tuple 'I_5) :
  ViewT (rot_tuple n t) = (fun x : k.-tuple bool => rot_tuple n x) `o ViewT t.
Proof.
apply: boolp.funext => w; rewrite /comp_RV !ViewTE; apply: val_inj => /=.
exact: map_rot.
Qed.

(* Rotating the position tuple leaves the leakage unchanged. *)
Lemma mutual_info_ViewT_rot k n (t : k.-tuple 'I_5) :
  `I( Secret ; ViewT (rot_tuple n t) ) = `I( Secret ; ViewT t ).
Proof.
by rewrite ViewT_rot; apply: injective_mutual_info_RV; exact: rot_tuple_inj.
Qed.

(* The set-indexed view equals the tuple-indexed view at any position tuple
   of the same length and the same ascending values. *)
Lemma mutual_info_ViewS_ViewT (S : {set 'I_5}) k (t : k.-tuple 'I_5)
    (e : #|S| = k) :
  map val (val (enum_tuple S)) = map val (val t) ->
  `I( Secret ; ViewS S ) = `I( Secret ; ViewT t ).
Proof.
by move: t; case: k / e => t hv; rewrite /ViewS (val_inj (inj_map val_inj hv)).
Qed.

(* ---- the cyclic cut shift and its transport of mutual information ---- *)

(* The five-cycle shift sends a position to its successor modulo five. *)
Lemma val_fc_sigma_fun (i : 'I_5) : val (fc_sigma_fun i) = (i.+1 %% 5)%N.
Proof. by case: i => [[|[|[|[|[|m]]]]] Hm]. Qed.

(* fc_sigma_fun cancels fc_sigma_inv, the direction not stated in
   five_card_group. *)
Lemma fc_sigmaKV : cancel fc_sigma_inv fc_sigma_fun.
Proof. by move=> x; apply: val_inj; case: x => [[|[|[|[|[|m]]]]] Hm]. Qed.

(* cut_sigma advances the cut of an outcome by one position. *)
Definition cut_sigma (w : Omega) : Omega :=
  let: (a, b, k) := w in (a, b, fc_sigma_fun k).

(* cut_sigma_inv retracts the cut of an outcome by one position. *)
Definition cut_sigma_inv (w : Omega) : Omega :=
  let: (a, b, k) := w in (a, b, fc_sigma_inv k).

Lemma cut_sigmaK : cancel cut_sigma cut_sigma_inv.
Proof. by move=> [[a b] k]; rewrite /= fc_sigmaK. Qed.

Lemma cut_sigmaKV : cancel cut_sigma_inv cut_sigma.
Proof. by move=> [[a b] k]; rewrite /= fc_sigmaKV. Qed.

(* The uniform distribution on the sample space is invariant under the cut
   shift. *)
Lemma fdistmap_cut_sigma : fdistmap cut_sigma P = P.
Proof.
apply/fdist_ext => w; rewrite fdistmapE.
rewrite (big_pred1 (cut_sigma_inv w)); last first.
  by move=> i; rewrite !inE /=; apply/idP/idP => [/eqP <-|/eqP ->];
     rewrite ?cut_sigmaK ?cut_sigmaKV.
by rewrite /P !fdist_uniformE.
Qed.

(* Reading the shifted positions of an outcome is reading the original
   positions of the shifted outcome. *)
Lemma ViewT_sigma k (t : k.-tuple 'I_5) (w : Omega) :
  ViewT (map_tuple fc_sigma_fun t) w = ViewT t (cut_sigma w).
Proof.
apply: eq_from_tnth => i.
rewrite /ViewT !tnth_mktuple tnth_map val_fc_sigma_fun.
case: w => [[a b] kk] /=; rewrite /arr /fc_shuffle.
have nr5 (s : seq bool) (m n : nat) : size s = 5%N -> (m < 5)%N ->
    (n < 5)%N -> nth false (rot n s) m = nth false s ((m + n) %% 5)%N.
  move=> hs hm hn.
  move: hs; case: s => [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 l]]]]]] //= _.
  by case: m hm => [|[|[|[|[|m']]]]] //= _; case: n hn => [|[|[|[|[|n']]]]] //=.
rewrite (nr5 _ _ _ (fc_arrange_size a b) (@ltn_pmod (tnth t i).+1 5 isT)
  (ltn_ord kk)).
rewrite (nr5 _ _ _ (fc_arrange_size a b) (ltn_ord (tnth t i))
  (ltn_ord (fc_sigma_fun kk))).
rewrite val_fc_sigma_fun modnDml modnDmr.
by rewrite addSnnS.
Qed.

(* Shifting every position of the tuple by the five-cycle leaves the leakage
   unchanged. *)
Lemma mutual_info_ViewT_sigma k (t : k.-tuple 'I_5) :
  `I( Secret ; ViewT (map_tuple fc_sigma_fun t) ) = `I( Secret ; ViewT t ).
Proof.
rewrite /mutual_info_RV; congr (mutual_info _).
have -> : [% Secret, ViewT (map_tuple fc_sigma_fun t)]
        = [% Secret, ViewT t] \o cut_sigma.
  apply: boolp.funext => w; rewrite /RV2 /=.
  by rewrite ViewT_sigma; case: w => [[a b] kk].
by rewrite /dist_of_RV -fdistmap_comp fdistmap_cut_sigma.
Qed.

(* ---- the bridge to the published position-list views ---- *)

(* Mapping a function along the components of a tuple is mapping it along
   the tuple's underlying sequence. *)
Lemma map_tnth (T1 T2 : Type) n (t : n.-tuple T1) (f : T1 -> T2) :
  [seq f (tnth t i) | i <- enum 'I_n] = [seq f j | j <- val t].
Proof.
have e : [seq f (tnth t i) | i <- enum 'I_n] = [seq f j | j <- tval t].
  by rewrite -(map_tnth_enum t) -[RHS]map_comp.
exact: e.
Qed.

(* The tuple-indexed view at t is the position-list view at the list of
   values of t. *)
Lemma ViewT_ViewA (A : seq nat) (t : (size A).-tuple 'I_5) :
  map val (val t) = A -> ViewT t = ViewA A.
Proof.
move=> hA; apply: boolp.funext => w; apply: val_inj.
rewrite /ViewT /ViewA /=.
rewrite (map_tnth t (fun j : 'I_5 => nth false (arr w) (val j))).
have -> : [seq nth false (arr w) (val j) | j <- val t]
        = [seq nth false (arr w) i | i <- [seq val j | j <- val t]].
  by rewrite -[RHS]map_comp.
by rewrite hA.
Qed.

(* ---- the two endpoints of the leak_k<n> family ---- *)

(* Revealing no card leaks nothing about the secret. *)
Lemma leak_k0 : `I( Secret ; ViewT ([tuple] : 0.-tuple 'I_5) ) = 0.
Proof.
have hind : P |= Secret _|_ (ViewT ([tuple] : 0.-tuple 'I_5)).
  rewrite /inde_RV => s c; rewrite (tuple0 c) !count_pr.
  have -> : #|preim (ViewT ([tuple] : 0.-tuple 'I_5)) (pred1 [tuple])| = 20%N.
    rewrite -card_Omega20; apply: eq_card => w.
    by rewrite !inE /=; apply/eqP; exact: tuple0.
  have -> : #|preim [% Secret, ViewT ([tuple] : 0.-tuple 'I_5)]
                    (pred1 (s, [tuple]))| = #|preim Secret (pred1 s)|.
    apply: eq_card => w; rewrite !inE /= xpair_eqE.
    have -> : (ViewT ([tuple] : 0.-tuple 'I_5) w == [tuple]) = true.
      by apply/eqP; exact: tuple0.
    by rewrite andbT.
  by rewrite divff ?mulr1 // pnatr_eq0.
rewrite mutual_info_RVE.
have hcond : `H( Secret | ViewT ([tuple] : 0.-tuple 'I_5)) = `H `p_Secret.
  have := chain_rule_RV (ViewT ([tuple] : 0.-tuple 'I_5)) Secret.
  rewrite -joint_entropy_RVC (inde_RV_joint_entropyE hind) => h1.
  have : `H `p_(ViewT ([tuple] : 0.-tuple 'I_5))
         + `H( Secret | ViewT ([tuple] : 0.-tuple 'I_5))
       = `H `p_(ViewT ([tuple] : 0.-tuple 'I_5)) + `H `p_Secret.
    by rewrite -h1 addrC.
  by move/addrI.
by rewrite hcond subrr.
Qed.

(* Revealing the gapped triple of positions {0, 1, 3} leaks
   6/5 - (9/20) log 3 bits about the secret. *)
Lemma leak_k3_gap :
  `I( Secret ; ViewA [:: 0; 1; 3]%N ) = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Admitted.

(* ---- the master theorem ---- *)

(* The mutual information between the den Boer secret and the view at any
   subset of the five row positions is the closed form leak S. *)
Theorem leak_view_set (S : {set 'I_5}) : `I( Secret ; ViewS S ) = leak S.
Proof.
case: (setb5_onto S) => b0 [b1 [b2 [b3 [b4 ->]]]].
case: b0; case: b1; case: b2; case: b3; case: b4.
(* {0, 1, 2, 3, 4} *)
- rewrite (leakE5 (card_setb5 true true true true true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1; p2; p3; p4])
    (card_setb5 true true true true true)); last by rewrite enum_setb5.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2; 3; 4]%N)
    (t := [tuple p0; p1; p2; p3; p4]) erefl)
     leak_k5.
(* {0, 1, 2, 3} *)
- rewrite (leakE4 (card_setb5 true true true true false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1; p2; p3])
    (card_setb5 true true true true false)); last by rewrite enum_setb5.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2; 3]%N)
    (t := [tuple p0; p1; p2; p3]) erefl)
     leak_k4.
(* {0, 1, 2, 4} *)
- rewrite (leakE4 (card_setb5 true true true false true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1; p2; p4])
    (card_setb5 true true true false true)); last by rewrite enum_setb5.
  have e : [tuple p0; p1; p2; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      rot_tuple 1 [tuple p0; p1; p2; p3])))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2; 3]%N)
    (t := [tuple p0; p1; p2; p3]) erefl)
     leak_k4.
(* {0, 1, 2} *)
- rewrite (leakE3 (card_setb5 true true true false false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1; p2])
    (card_setb5 true true true false false)); last by rewrite enum_setb5.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2]%N)
    (t := [tuple p0; p1; p2]) erefl)
     leak_k3.
(* {0, 1, 3, 4} *)
- rewrite (leakE4 (card_setb5 true true false true true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1; p3; p4])
    (card_setb5 true true false true true)); last by rewrite enum_setb5.
  have e : [tuple p0; p1; p3; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (rot_tuple 2 [tuple p0; p1; p2; p3]))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2; 3]%N)
    (t := [tuple p0; p1; p2; p3]) erefl)
     leak_k4.
(* {0, 1, 3} *)
- rewrite (leakE3 (card_setb5 true true false true false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1; p3])
    (card_setb5 true true false true false)); last by rewrite enum_setb5.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 3]%N)
    (t := [tuple p0; p1; p3]) erefl)
     leak_k3_gap.
(* {0, 1, 4} *)
- rewrite (leakE3 (card_setb5 true true false false true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1; p4])
    (card_setb5 true true false false true)); last by rewrite enum_setb5.
  have e : [tuple p0; p1; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      rot_tuple 1 [tuple p0; p1; p2])))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2]%N)
    (t := [tuple p0; p1; p2]) erefl)
     leak_k3.
(* {0, 1} *)
- rewrite (leakE2adj (card_setb5 true true false false false));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p1])
    (card_setb5 true true false false false)); last by rewrite enum_setb5.
  by rewrite (ViewT_ViewA (A := [:: 0; 1]%N) (t := [tuple p0; p1]) erefl)
     leak_k2_adj.
(* {0, 2, 3, 4} *)
- rewrite (leakE4 (card_setb5 true false true true true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p2; p3; p4])
    (card_setb5 true false true true true)); last by rewrite enum_setb5.
  have e : [tuple p0; p2; p3; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      rot_tuple 3 [tuple p0; p1; p2; p3])).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2; 3]%N)
    (t := [tuple p0; p1; p2; p3]) erefl)
     leak_k4.
(* {0, 2, 3} *)
- rewrite (leakE3 (card_setb5 true false true true false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p2; p3])
    (card_setb5 true false true true false)); last by rewrite enum_setb5.
  have e : [tuple p0; p2; p3]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      rot_tuple 2 [tuple p0; p1; p3])).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 3]%N)
    (t := [tuple p0; p1; p3]) erefl)
     leak_k3_gap.
(* {0, 2, 4} *)
- rewrite (leakE3 (card_setb5 true false true false true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p2; p4])
    (card_setb5 true false true false true)); last by rewrite enum_setb5.
  have e : [tuple p0; p2; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      rot_tuple 1 [tuple p0; p1; p3])))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 3]%N)
    (t := [tuple p0; p1; p3]) erefl)
     leak_k3_gap.
(* {0, 2} *)
- rewrite (leakE2dist2 (card_setb5 true false true false false));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p2])
    (card_setb5 true false true false false)); last by rewrite enum_setb5.
  by rewrite (ViewT_ViewA (A := [:: 0; 2]%N) (t := [tuple p0; p2]) erefl)
     leak_k2_dist2.
(* {0, 3, 4} *)
- rewrite (leakE3 (card_setb5 true false false true true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p3; p4])
    (card_setb5 true false false true true)); last by rewrite enum_setb5.
  have e : [tuple p0; p3; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (rot_tuple 2 [tuple p0; p1; p2]))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2]%N)
    (t := [tuple p0; p1; p2]) erefl)
     leak_k3.
(* {0, 3} *)
- rewrite (leakE2dist2 (card_setb5 true false false true false));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p3])
    (card_setb5 true false false true false)); last by rewrite enum_setb5.
  have e : [tuple p0; p3]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (rot_tuple 1 [tuple p0; p2]))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 2]%N) (t := [tuple p0; p2]) erefl)
     leak_k2_dist2.
(* {0, 4} *)
- rewrite (leakE2adj (card_setb5 true false false false true));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0; p4])
    (card_setb5 true false false false true)); last by rewrite enum_setb5.
  have e : [tuple p0; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      rot_tuple 1 [tuple p0; p1])))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1]%N) (t := [tuple p0; p1]) erefl)
     leak_k2_adj.
(* {0} *)
- rewrite (leakE1 (card_setb5 true false false false false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p0])
    (card_setb5 true false false false false)); last by rewrite enum_setb5.
  by rewrite (ViewT_ViewA (A := [:: 0]%N) (t := [tuple p0]) erefl)
     leak_k1.
(* {1, 2, 3, 4} *)
- rewrite (leakE4 (card_setb5 false true true true true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1; p2; p3; p4])
    (card_setb5 false true true true true)); last by rewrite enum_setb5.
  have e : [tuple p1; p2; p3; p4]
    = map_tuple fc_sigma_fun ([tuple p0; p1; p2; p3]).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2; 3]%N)
    (t := [tuple p0; p1; p2; p3]) erefl)
     leak_k4.
(* {1, 2, 3} *)
- rewrite (leakE3 (card_setb5 false true true true false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1; p2; p3])
    (card_setb5 false true true true false)); last by rewrite enum_setb5.
  have e : [tuple p1; p2; p3] = map_tuple fc_sigma_fun ([tuple p0; p1; p2]).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2]%N)
    (t := [tuple p0; p1; p2]) erefl)
     leak_k3.
(* {1, 2, 4} *)
- rewrite (leakE3 (card_setb5 false true true false true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1; p2; p4])
    (card_setb5 false true true false true)); last by rewrite enum_setb5.
  have e : [tuple p1; p2; p4] = map_tuple fc_sigma_fun ([tuple p0; p1; p3]).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 3]%N)
    (t := [tuple p0; p1; p3]) erefl)
     leak_k3_gap.
(* {1, 2} *)
- rewrite (leakE2adj (card_setb5 false true true false false));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1; p2])
    (card_setb5 false true true false false)); last by rewrite enum_setb5.
  have e : [tuple p1; p2] = map_tuple fc_sigma_fun ([tuple p0; p1]).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 1]%N) (t := [tuple p0; p1]) erefl)
     leak_k2_adj.
(* {1, 3, 4} *)
- rewrite (leakE3 (card_setb5 false true false true true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1; p3; p4])
    (card_setb5 false true false true true)); last by rewrite enum_setb5.
  have e : [tuple p1; p3; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (rot_tuple 2 [tuple p0; p1; p3]))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 3]%N)
    (t := [tuple p0; p1; p3]) erefl)
     leak_k3_gap.
(* {1, 3} *)
- rewrite (leakE2dist2 (card_setb5 false true false true false));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1; p3])
    (card_setb5 false true false true false)); last by rewrite enum_setb5.
  have e : [tuple p1; p3] = map_tuple fc_sigma_fun ([tuple p0; p2]).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 2]%N) (t := [tuple p0; p2]) erefl)
     leak_k2_dist2.
(* {1, 4} *)
- rewrite (leakE2dist2 (card_setb5 false true false false true));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1; p4])
    (card_setb5 false true false false true)); last by rewrite enum_setb5.
  have e : [tuple p1; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      rot_tuple 1 [tuple p0; p2])))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma mutual_info_ViewT_rot.
  by rewrite (ViewT_ViewA (A := [:: 0; 2]%N) (t := [tuple p0; p2]) erefl)
     leak_k2_dist2.
(* {1} *)
- rewrite (leakE1 (card_setb5 false true false false false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p1])
    (card_setb5 false true false false false)); last by rewrite enum_setb5.
  have e : [tuple p1] = map_tuple fc_sigma_fun ([tuple p0]).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0]%N) (t := [tuple p0]) erefl)
     leak_k1.
(* {2, 3, 4} *)
- rewrite (leakE3 (card_setb5 false false true true true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p2; p3; p4])
    (card_setb5 false false true true true)); last by rewrite enum_setb5.
  have e : [tuple p2; p3; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun ([tuple p0; p1; p2])).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 1; 2]%N)
    (t := [tuple p0; p1; p2]) erefl)
     leak_k3.
(* {2, 3} *)
- rewrite (leakE2adj (card_setb5 false false true true false));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p2; p3])
    (card_setb5 false false true true false)); last by rewrite enum_setb5.
  have e : [tuple p2; p3]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun ([tuple p0; p1])).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 1]%N) (t := [tuple p0; p1]) erefl)
     leak_k2_adj.
(* {2, 4} *)
- rewrite (leakE2dist2 (card_setb5 false false true false true));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p2; p4])
    (card_setb5 false false true false true)); last by rewrite enum_setb5.
  have e : [tuple p2; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun ([tuple p0; p2])).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 2]%N) (t := [tuple p0; p2]) erefl)
     leak_k2_dist2.
(* {2} *)
- rewrite (leakE1 (card_setb5 false false true false false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p2])
    (card_setb5 false false true false false)); last by rewrite enum_setb5.
  have e : [tuple p2]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun ([tuple p0])).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0]%N) (t := [tuple p0]) erefl)
     leak_k1.
(* {3, 4} *)
- rewrite (leakE2adj (card_setb5 false false false true true));
    last by rewrite adjacentE.
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p3; p4])
    (card_setb5 false false false true true)); last by rewrite enum_setb5.
  have e : [tuple p3; p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun ([tuple p0; p1]))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0; 1]%N) (t := [tuple p0; p1]) erefl)
     leak_k2_adj.
(* {3} *)
- rewrite (leakE1 (card_setb5 false false false true false)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p3])
    (card_setb5 false false false true false)); last by rewrite enum_setb5.
  have e : [tuple p3]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun ([tuple p0]))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0]%N) (t := [tuple p0]) erefl)
     leak_k1.
(* {4} *)
- rewrite (leakE1 (card_setb5 false false false false true)).
  rewrite (mutual_info_ViewS_ViewT (t := [tuple p4])
    (card_setb5 false false false false true)); last by rewrite enum_setb5.
  have e : [tuple p4]
    = map_tuple fc_sigma_fun (map_tuple fc_sigma_fun (
      map_tuple fc_sigma_fun (map_tuple fc_sigma_fun ([tuple p0])))).
    by apply: val_inj.
  rewrite e !mutual_info_ViewT_sigma.
  by rewrite (ViewT_ViewA (A := [:: 0]%N) (t := [tuple p0]) erefl)
     leak_k1.
(* set0 *)
- rewrite (leakE0 (card_setb5 false false false false false)).
  rewrite (mutual_info_ViewS_ViewT (t := ([tuple] : 0.-tuple 'I_5))
    (card_setb5 false false false false false)); last by rewrite enum_setb5.
  exact: leak_k0.
Qed.

End probe_round2.
