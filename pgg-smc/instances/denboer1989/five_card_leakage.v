(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Den Boer's Five-Card Trick: Partial-View Leakage                           *)
(*                                                                            *)
(* Quantifies, as Shannon mutual information in bits, the information a        *)
(* partial reveal of the dealt five-card row carries about the den Boer        *)
(* secret a && b, under the realistic uniform prior on (a, b, cut).            *)
(*                                                                            *)
(* Sample space: (a, b, k) uniform over bool * bool * 'I_5 (20 outcomes).      *)
(* Since a and b are fair coins, a && b is true with probability 1/4, the      *)
(* prior built into the model. arr w is the dealt, cut five-card row (hearts   *)
(* = true), Secret w = a && b (equal to fc_three_consec (arr w) by fc_correct).*)
(* A view at a fixed position list A reads the card colours at A as a          *)
(* (size A)-tuple of bits; its leakage about the secret is the mutual          *)
(* information `I( Secret ; ViewA A ).                                         *)
(*                                                                            *)
(* The closed forms (log = log base 2) are computed exactly for k = 1..5:      *)
(* one card leaks nothing; two adjacent and two distance-2 cards leak          *)
(* distinct positive amounts; three cards leak 6/5 - (9/20) log 3; and four    *)
(* or five cards leak the full secret entropy H(1/4) = 2 - (3/4) log 3.        *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype tuple finfun finset bigop.
From mathcomp Require Import ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import five_card_program five_card_group.
From mathcomp Require Import lra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section five_card_leakage.

Variable R : realType.

Local Open Scope ring_scope.

(** Omega — the sample space of the den Boer trick.
    @intent: the product finite type of the two input bits and the cyclic cut,
    bool * bool * 'I_5, with 20 equally likely outcomes. *)
Definition Omega : finType := [the finType of (bool * bool * 'I_5)%type].

(** card_Omega20 — the sample space has 20 outcomes.
    Casts #|Omega| into n.+1 form so the uniform distribution fdist_uniform
    can be built on Omega.
    @composes: P. *)
Lemma card_Omega20 : #|Omega| = 19.+1.
Proof. by rewrite !card_prod card_bool card_ord. Qed.

(** P — the uniform distribution on the sample space.
    @intent: fdist_uniform over Omega; each of the 20 outcomes (a, b, k) has
    probability 1/20, so a && b is true with the realistic prior 1/4. *)
Definition P : R.-fdist Omega := fdist_uniform card_Omega20.

(** arr — the dealt, cut five-card row of an outcome.
    @intent: applies the cyclic cut sigma^k to the den Boer arrangement of the
    two input bits, fc_shuffle k (fc_arrange a b); hearts = true, size 5. *)
Definition arr (w : Omega) : seq bool :=
  let: (a, b, k) := w in fc_shuffle k (fc_arrange a b).

(** Secret — the den Boer secret of an outcome.
    @intent: the conjunction a && b of the two input bits, equal to
    fc_three_consec (arr w) by fc_correct. *)
Definition Secret : {RV P -> bool} := fun w => let: (a, b, _) := w in a && b.

(** ViewA — the partial view at a fixed list of card positions.
    @intent: reads the card colours of arr w at the positions in A as a
    (size A)-tuple of bits, the finite-type-valued random variable whose
    leakage about Secret is measured. *)
Definition ViewA (A : seq nat) : {RV P -> (size A).-tuple bool} :=
  fun w => map_tuple (fun i => nth false (arr w) i) (in_tuple A).

(** H_secret — the entropy of the den Boer secret is H(1/4) = 2 - (3/4) log 3.
    The Shannon entropy of a && b under the uniform prior, the leakage that
    leak_k4 and leak_k5 attain at full reveal.
    @composes: leak_k4. *)
Lemma H_secret : `H `p_Secret = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof.
have val : forall c : bool,
    `p_ Secret c = #|preim Secret (pred1 c)|%:R / 20%:R :> R.
  move=> c; rewrite /dist_of_RV fdistmapE.
  under eq_bigr do rewrite fdist_uniformE.
  rewrite big_const GRing.iter_addr_0 card_Omega20.
  by rewrite -[20^-1 *+ _]mulr_natl mulrC.
have Ht : `p_ Secret true = 4%:R^-1 :> R.
  rewrite val.
  have -> : #|preim Secret (pred1 true)| = 5%N.
    rewrite (@eq_card _ _ [predX [pred ab : bool * bool | ab.1 && ab.2] & 'I_5])
      ?cardX.
      rewrite card_ord (eq_card (B := pred1 (true, true))) ?card1 //.
      by move=> [a b]; rewrite !inE; case: a; case: b.
    by move=> [[a b] k]; rewrite !inE /=; case: a; case: b.
  have e20 : (20%:R : R) = 5%:R * 4%:R by rewrite -natrM.
  by rewrite e20 invfM mulrA -[5%:R / 5%:R]/(5%:R / 5%:R) divff ?mul1r// pnatr_eq0.
have Hf : `p_ Secret false = 3%:R / 4%:R :> R.
  rewrite val.
  have -> : #|preim Secret (pred1 false)| = 15%N.
    rewrite (@eq_card _ _
      [predX [pred ab : bool * bool | ~~ (ab.1 && ab.2)] & 'I_5]) ?cardX.
      rewrite card_ord (eq_card (B := [pred ab : bool * bool | ab != (true, true)])).
        by rewrite cardC1 card_prod !card_bool.
      by move=> [a b]; rewrite !inE; case: a; case: b.
    by move=> [[a b] k]; rewrite !inE /=; case: a; case: b.
  have e20 : (20%:R : R) = 4%:R * 5%:R by rewrite -natrM.
  have e15 : (15%:R : R) = 3%:R * 5%:R by rewrite -natrM.
  by rewrite {1}e15 {1}e20 invfM mulrA mulrAC mulfK ?pnatr_eq0.
rewrite /entropy big_bool /= Ht Hf.
rewrite logV ?ltr0n// log4 logDiv ?ltr0n// log4.
set L := log 3%:R; rewrite !mulrBr opprD mulrN opprK -mulNr.
rewrite opprD addrA addrAC; congr (_ - _).
rewrite mulNr opprK -mulrDl.
have -> : (4%:R^-1 + 3%:R / 4%:R : R) = 1.
  rewrite [3%:R / 4%:R]mulrC -{1}[4%:R^-1]mulr1 -mulrDr.
  have -> : (1 + 3%:R : R) = 4%:R by rewrite -[1]/(1%:R) -natrD.
  by rewrite mulVf ?pnatr_eq0.
by rewrite mul1r.
Qed.

(** count_pr — the law of any random variable under the uniform prior is its
    fibre cardinality divided by 20. The pushforward probability pfwd1 X x
    equals #|preim X (pred1 x)| / 20, since P is uniform on the 20 outcomes.
    @composes: condent_ratio. *)
Lemma count_pr (A : finType) (X : {RV P -> A}) (x : A) :
  pfwd1 X x = #|preim X (pred1 x)|%:R / 20%:R :> R.
Proof.
rewrite -dist_of_RVE /dist_of_RV fdistmapE.
under eq_bigr do rewrite fdist_uniformE.
rewrite big_const GRing.iter_addr_0 card_Omega20.
by rewrite -[20^-1 *+ _]mulr_natl mulrC.
Qed.

(** stepBB — a sum over bool * bool expands into the four constituent cells.
    Reindexes \sum_(ab : bool * bool) into the nested \sum_a \sum_b form for
    explicit cell enumeration.
    @composes: condent_ratio. *)
Lemma stepBB (G : bool * bool -> nat) :
  (\sum_(ab : bool * bool) G ab)%N
    = (\sum_(a : bool) \sum_(b : bool) G (a, b))%N.
Proof. by rewrite pair_bigA /=; apply: eq_big => // i _; case: i. Qed.

(** stepO — a sum over Omega expands into a sum over (bool * bool) then 'I_5.
    Reindexes \sum_(i : Omega) into \sum_ab \sum_k, the shape on which the
    card enumerations operate.
    @composes: condent_ratio. *)
Lemma stepO (G : Omega -> nat) :
  (\sum_(i : Omega) G i)%N
    = (\sum_(ab : bool * bool) \sum_(k : 'I_5) G (ab, k))%N.
Proof. by rewrite pair_bigA /=; apply: eq_big => // i _; case: i. Qed.

(** binent_1_4 — the binary entropy at 1/4 in closed form.
    -1/4 log(1/4) - 3/4 log(3/4) = 2 - 3/4 log 3.
    @composes: leak_k3. *)
Lemma binent_1_4 :
  - (1%:R / 4%:R) * log (1%:R / 4%:R) - (3%:R / 4%:R) * log (3%:R / 4%:R)
  = 2%:R - 3%:R / 4%:R * log 3%:R :> R.
Proof. rewrite logDiv ?ltr0n// logDiv ?ltr0n// log1 log4. lra. Qed.

(** binent_1_7 — the binary entropy at 1/7 in closed form.
    -1/7 log(1/7) - 6/7 log(6/7) = log 7 - 6/7 - 6/7 log 3.
    @composes: leak_k2_adj. *)
Lemma binent_1_7 :
  - (1%:R / 7%:R) * log (1%:R / 7%:R) - (6%:R / 7%:R) * log (6%:R / 7%:R)
  = log 7%:R - 6%:R / 7%:R - 6%:R / 7%:R * log 3%:R :> R.
Proof.
have l6 : log (6%:R : R) = 1 + log 3%:R.
  by rewrite (_ : 6%:R = 2%:R * 3%:R) ?logM ?ltr0n ?log2 // -natrM.
rewrite logDiv ?ltr0n// log1 logDiv ?ltr0n// l6. lra.
Qed.

(** binent_2_5 — the binary entropy at 2/5 in closed form.
    -2/5 log(2/5) - 3/5 log(3/5) = log 5 - 2/5 - 3/5 log 3.
    @composes: leak_k2_dist2. *)
Lemma binent_2_5 :
  - (2%:R / 5%:R) * log (2%:R / 5%:R) - (3%:R / 5%:R) * log (3%:R / 5%:R)
  = log 5%:R - 2%:R / 5%:R - 3%:R / 5%:R * log 3%:R :> R.
Proof. rewrite logDiv ?ltr0n// log2 logDiv ?ltr0n//. lra. Qed.

(** binent_det0 — a view whose secret is determined false carries no entropy.
    The binary entropy of the ratios (0/nv, nv/nv) is 0.
    @composes: leak_k3. *)
Lemma binent_det0 (nv : nat) : (0 < nv)%N ->
  - (0%:R / nv%:R) * log (0%:R / nv%:R)
  - (nv%:R / nv%:R) * log (nv%:R / nv%:R) = 0 :> R.
Proof.
move=> Hnv.
have nvn0 : nv%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite mul0r !divff // log1. lra.
Qed.

(** binent_det1 — a view whose secret is determined true carries no entropy.
    The binary entropy of the ratios (nv/nv, 0/nv) is 0.
    @composes: leak_k3. *)
Lemma binent_det1 (nv : nat) : (0 < nv)%N ->
  - (nv%:R / nv%:R) * log (nv%:R / nv%:R)
  - (0%:R / nv%:R) * log (0%:R / nv%:R) = 0 :> R.
Proof.
move=> Hnv.
have nvn0 : nv%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite mul0r !divff // log1. lra.
Qed.

(** condent_ratio — the conditional entropy of the secret given a fixed view
    value is the binary entropy of its true/false fibre ratios. For a view
    value a with view count nv > 0 and joint counts nt (secret true) and nf
    (secret false), H[Secret | View = a] equals -(nt/nv) log(nt/nv) -
    (nf/nv) log(nf/nv).
    @composes: leak_k3. *)
Lemma condent_ratio (A : seq nat) (a : (size A).-tuple bool) (nv nt nf : nat) :
  #|preim (ViewA A) (pred1 a)| = nv ->
  #|preim [% Secret, ViewA A] (pred1 (true, a))| = nt ->
  #|preim [% Secret, ViewA A] (pred1 (false, a))| = nf ->
  (0 < nv)%N ->
  centropy1_RV (ViewA A) Secret a =
    - (nt%:R / nv%:R) * log (nt%:R / nv%:R)
    - (nf%:R / nv%:R) * log (nf%:R / nv%:R) :> R.
Proof.
move=> Hnv Hnt Hnf Hpos.
have Hmarg : (`p_ [% ViewA A, Secret])`1 a != 0 :> R.
  rewrite fst_RV2 dist_of_RVE count_pr Hnv.
  by rewrite mulf_eq0 negb_or invr_eq0 !pnatr_eq0 -!lt0n Hpos /=.
rewrite (centropy1_RVE Hmarg).
have Hd : forall b : bool,
    jfdist_cond.jfdist_cond `p_ [% ViewA A, Secret] a b =
    #|preim [% Secret, ViewA A] (pred1 (b, a))|%:R / nv%:R :> R.
  move=> b.
  rewrite jfdist_cond.jfdist_condE // fdistX_RV2 jfdist_cond.jPr_Pr.
  rewrite cpr_in1 cpr_eqE !count_pr Hnv.
  by rewrite invf_div mulrA divfK ?pnatr_eq0 //.
rewrite /entropy big_bool /= !Hd Hnt Hnf.
by rewrite opprD mulNr.
Qed.

(** leak_k1 — revealing one card leaks nothing about a && b.
    @main security: the mutual information between the secret and a single
    revealed card position is 0. *)
Lemma leak_k1 : `I( Secret ; ViewA [:: 0%N] ) = 0.
Proof.
have Hinde : P |= Secret _|_ (ViewA [:: 0%N]).
  rewrite /inde_RV => s c.
  have count_pr : forall (A : finType) (X : {RV P -> A}) (x : A),
      pfwd1 X x = #|preim X (pred1 x)|%:R / 20%:R :> R.
    move=> A X x; rewrite -dist_of_RVE /dist_of_RV fdistmapE.
    under eq_bigr do rewrite fdist_uniformE.
    rewrite big_const GRing.iter_addr_0 card_Omega20.
    by rewrite -[20^-1 *+ _]mulr_natl mulrC.
  have stepBB : forall G : bool * bool -> nat,
      (\sum_(ab : bool * bool) G ab)%N
        = (\sum_(a : bool) \sum_(b : bool) G (a, b))%N.
    by move=> G; rewrite pair_bigA /=; apply: eq_big => // i _; case: i.
  have stepO : forall G : Omega -> nat,
      (\sum_(i : Omega) G i)%N
        = (\sum_(ab : bool * bool) \sum_(k : 'I_5) G (ab, k))%N.
    by move=> G; rewrite pair_bigA /=; apply: eq_big => // i _; case: i.
  have card_view : forall d0 : bool,
      #|preim (ViewA [:: 0%N]) (pred1 [tuple d0])| = (if d0 then 12 else 8)%N.
    move=> d0.
    rewrite -sum1_card (eq_bigl (fun w : Omega => nth false (arr w) 0 == d0));
      last first.
      by move=> w /=; rewrite /ViewA inE /= -val_eqE /= eqseq_cons andbT.
    rewrite big_mkcond /= stepO.
    under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
    by rewrite stepBB !big_bool /=; case: d0.
  have card_secret : forall s0 : bool,
      #|preim Secret (pred1 s0)| = (if s0 then 5 else 15)%N.
    move=> s0.
    rewrite -sum1_card
      (eq_bigl (fun w : Omega => let: (a, b, _) := w in (a && b) == s0));
      last first.
      by move=> w /=; rewrite inE /Secret /=; case: w => [[a b] k].
    rewrite big_mkcond /= stepO.
    under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
    by rewrite stepBB !big_bool /=; case: s0.
  have card_joint : forall (s0 d0 : bool),
      #|preim [% Secret, ViewA [:: 0%N]] (pred1 (s0, [tuple d0]))| =
        (if s0 then (if d0 then 3 else 2) else (if d0 then 9 else 6))%N.
    move=> s0 d0.
    rewrite -sum1_card (eq_bigl (fun w : Omega =>
        (let: (a, b, _) := w in (a && b) == s0)
          && (nth false (arr w) 0 == d0))); last first.
      move=> w /=; rewrite inE /=.
      rewrite xpair_eqE /Secret /ViewA /=.
      by case: w => [[a b] k] /=; rewrite -val_eqE /= eqseq_cons andbT.
    rewrite big_mkcond /= stepO.
    under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
    by rewrite stepBB !big_bool /=; case: s0; case: d0.
  case/tupleP : c => c0 c'.
  rewrite (tuple0 c') /= !count_pr.
  have -> : [tuple of c0 :: [tuple]] = [tuple c0] by apply: val_inj.
  rewrite card_secret card_view card_joint.
  apply/eqP; rewrite mulrACA -invfM -!natrM.
  have -> : (20 * 20 = 400)%N by [].
  by rewrite eqr_div ?pnatr_eq0 // -!natrM eqr_nat; case: s; case: c0.
rewrite mutual_info_RVE.
have HcondE : `H( Secret | ViewA [:: 0%N]) = `H `p_Secret.
  have := chain_rule_RV (ViewA [:: 0%N]) Secret.
  rewrite -joint_entropy_RVC (inde_RV_joint_entropyE Hinde) => H1.
  have : `H `p_(ViewA [:: 0%N]) + `H( Secret | ViewA [:: 0%N])
       = `H `p_(ViewA [:: 0%N]) + `H `p_Secret.
    by rewrite -H1 addrC.
  by move/addrI.
by rewrite HcondE subrr.
Qed.

(** leak_k2_adj — two adjacent cards leak 27/10 - (1/4) log 5 - (7/10) log 7
    bits about a && b.
    @main security: the mutual information between the secret and the colours
    at the adjacent positions {0, 1}. *)
Lemma leak_k2_adj :
  `I( Secret ; ViewA [:: 0; 1]%N ) =
    27%:R / 10%:R - (4%:R^-1) * log 5%:R - (7%:R / 10%:R) * log 7%:R.
Proof.
rewrite mutual_info_RVE H_secret centropy_RVE'.
have cardV2 : forall a0 a1 : bool,
  #|preim (ViewA [:: 0; 1]%N) (pred1 [tuple of [:: a0; a1]])| =
  (if a0 then (if a1 then 5 else 7) else (if a1 then 7 else 1))%N.
  move=> a0 a1.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
     (nth false (arr w) 0 == a0) && (nth false (arr w) 1 == a1))); last first.
    move=> w /=.
    by rewrite /ViewA inE /= -val_eqE /= !eqseq_cons andbT.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: a0; case: a1.
have cardJ2 : forall (s a0 a1 : bool),
  #|preim [% Secret, ViewA [:: 0; 1]%N] (pred1 (s, [tuple of [:: a0; a1]]))| =
  (if s then (if a0 then (if a1 then 2 else 1) else (if a1 then 1 else 1))
        else (if a0 then (if a1 then 3 else 6) else (if a1 then 6 else 0)))%N.
  move=> s a0 a1.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
      (let: (a, b, _) := w in (a && b) == s)
        && ((nth false (arr w) 0 == a0) && (nth false (arr w) 1 == a1))));
    last first.
    move=> w /=; rewrite inE /=.
    rewrite xpair_eqE /Secret /ViewA /=.
    by case: w => [[a b] k] /=; rewrite -val_eqE /= !eqseq_cons andbT.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: s; case: a0; case: a1.
have hterm : forall (t : (size [:: 0; 1]%N).-tuple bool) (nv nt nf : nat),
   #|preim (ViewA [:: 0; 1]%N) (pred1 t)| = nv ->
   #|preim [% Secret, ViewA [:: 0; 1]%N] (pred1 (true, t))| = nt ->
   #|preim [% Secret, ViewA [:: 0; 1]%N] (pred1 (false, t))| = nf ->
   (0 < nv)%N ->
   pfwd1 (ViewA [:: 0; 1]%N) t * centropy1_RV (ViewA [:: 0; 1]%N) Secret t =
   nv%:R / 20%:R *
   (- (nt%:R / nv%:R) * log (nt%:R / nv%:R) - (nf%:R / nv%:R) * log (nf%:R / nv%:R)).
  move=> t nv nt nf Hv Ht Hf Hpos.
  by rewrite count_pr Hv (condent_ratio Hv Ht Hf Hpos).
rewrite (bigD1 [tuple of [:: false; true]]) //=.
rewrite (bigD1 [tuple of [:: true; false]]) //=.
rewrite (bigD1 [tuple of [:: true; true]]) //=.
rewrite big1; last first.
  move=> i; case/tupleP: i => a0 /tupleP[a1 a2]; rewrite (tuple0 a2) /=.
  case: a0; case: a1 => //=.
  move=> _; rewrite (hterm [tuple false; false] 1 1 0 (cardV2 false false)
    (cardJ2 true false false) (cardJ2 false false false) (ltn0Sn _))
    (binent_det1 (ltn0Sn _)) mulr0 //.
rewrite (hterm [tuple false; true] 7 1 6 (cardV2 false true)
  (cardJ2 true false true) (cardJ2 false false true) (ltn0Sn _)).
rewrite (hterm [tuple true; false] 7 1 6 (cardV2 true false)
  (cardJ2 true true false) (cardJ2 false true false) (ltn0Sn _)).
rewrite (hterm [tuple true; true] 5 2 3 (cardV2 true true)
  (cardJ2 true true true) (cardJ2 false true true) (ltn0Sn _)).
rewrite !binent_1_7 binent_2_5 addr0.
lra.
Qed.

(** leak_k2_dist2 — two distance-2 cards leak
    5/2 - (3/20) log 3 - (1/2) log 5 - (7/20) log 7 bits about a && b.
    @main security: the mutual information between the secret and the colours
    at the distance-2 positions {0, 2}. *)
Lemma leak_k2_dist2 :
  `I( Secret ; ViewA [:: 0; 2]%N ) =
    5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - (2%:R^-1) * log 5%:R
      - (7%:R / 20%:R) * log 7%:R.
Proof.
rewrite mutual_info_RVE H_secret centropy_RVE'.
have cardV2 : forall a0 a1 : bool,
  #|preim (ViewA [:: 0; 2]%N) (pred1 [tuple of [:: a0; a1]])| =
  (if a0 then (if a1 then 7 else 5) else (if a1 then 5 else 3))%N.
  move=> a0 a1.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
     (nth false (arr w) 0 == a0) && (nth false (arr w) 2 == a1))); last first.
    move=> w /=.
    by rewrite /ViewA inE /= -val_eqE /= !eqseq_cons andbT.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: a0; case: a1.
have cardJ2 : forall (s a0 a1 : bool),
  #|preim [% Secret, ViewA [:: 0; 2]%N] (pred1 (s, [tuple of [:: a0; a1]]))| =
  (if s then (if a0 then (if a1 then 1 else 2) else (if a1 then 2 else 0))
        else (if a0 then (if a1 then 6 else 3) else (if a1 then 3 else 3)))%N.
  move=> s a0 a1.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
      (let: (a, b, _) := w in (a && b) == s)
        && ((nth false (arr w) 0 == a0) && (nth false (arr w) 2 == a1)))); last first.
    move=> w /=; rewrite inE /=.
    rewrite xpair_eqE /Secret /ViewA /=.
    by case: w => [[a b] k] /=; rewrite -val_eqE /= !eqseq_cons andbT.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: s; case: a0; case: a1.
have hterm : forall (t : (size [:: 0; 2]%N).-tuple bool) (nv nt nf : nat),
   #|preim (ViewA [:: 0; 2]%N) (pred1 t)| = nv ->
   #|preim [% Secret, ViewA [:: 0; 2]%N] (pred1 (true, t))| = nt ->
   #|preim [% Secret, ViewA [:: 0; 2]%N] (pred1 (false, t))| = nf ->
   (0 < nv)%N ->
   pfwd1 (ViewA [:: 0; 2]%N) t * centropy1_RV (ViewA [:: 0; 2]%N) Secret t =
   nv%:R / 20%:R *
   (- (nt%:R / nv%:R) * log (nt%:R / nv%:R) - (nf%:R / nv%:R) * log (nf%:R / nv%:R)).
  move=> t nv nt nf Hv Ht Hf Hpos.
  by rewrite count_pr Hv (condent_ratio Hv Ht Hf Hpos).
rewrite (bigD1 [tuple of [:: false; true]]) //=.
rewrite (bigD1 [tuple of [:: true; false]]) //=.
rewrite (bigD1 [tuple of [:: true; true]]) //=.
rewrite big1; last first.
  move=> i; case/tupleP: i => a0 /tupleP[a1 a2]; rewrite (tuple0 a2) /=.
  case: a0; case: a1 => //=.
  move=> _; rewrite (hterm [tuple false; false] 3 0 3 (cardV2 false false)
    (cardJ2 true false false) (cardJ2 false false false) (ltn0Sn _))
    (binent_det0 (ltn0Sn _)) mulr0 //.
rewrite (hterm [tuple false; true] 5 2 3 (cardV2 false true)
  (cardJ2 true false true) (cardJ2 false false true) (ltn0Sn _)).
rewrite (hterm [tuple true; false] 5 2 3 (cardV2 true false)
  (cardJ2 true true false) (cardJ2 false true false) (ltn0Sn _)).
rewrite (hterm [tuple true; true] 7 1 6 (cardV2 true true)
  (cardJ2 true true true) (cardJ2 false true true) (ltn0Sn _)).
rewrite !binent_2_5 binent_1_7 addr0.
lra.
Qed.

(** leak_k3 — three cards leak 6/5 - (9/20) log 3 bits about a && b.
    @main security: the mutual information between the secret and the colours
    at positions {0, 1, 2}. *)
Lemma leak_k3 :
  `I( Secret ; ViewA [:: 0; 1; 2]%N ) = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Proof.
rewrite mutual_info_RVE H_secret centropy_RVE'.
have cardV3 : forall a0 a1 a2 : bool,
  #|preim (ViewA [:: 0; 1; 2]%N) (pred1 [tuple of [:: a0; a1; a2]])| =
  (if a0 then (if a1 then (if a2 then 1 else 4) else (if a2 then 6 else 1))
         else (if a1 then (if a2 then 4 else 3) else (if a2 then 1 else 0)))%N.
  move=> a0 a1 a2.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
     (nth false (arr w) 0 == a0) && (nth false (arr w) 1 == a1)
       && (nth false (arr w) 2 == a2))); last first.
    move=> w /=.
    by rewrite /ViewA inE /= -val_eqE /= !eqseq_cons andbT andbA.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: a0; case: a1; case: a2.
have cardJ3 : forall (s a0 a1 a2 : bool),
  #|preim [% Secret, ViewA [:: 0; 1; 2]%N] (pred1 (s, [tuple of [:: a0; a1; a2]]))| =
  (if s then (if a0 then (if a1 then (if a2 then 1 else 1) else (if a2 then 0 else 1))
                     else (if a1 then (if a2 then 1 else 0) else (if a2 then 1 else 0)))
        else (if a0 then (if a1 then (if a2 then 0 else 3) else (if a2 then 6 else 0))
                     else (if a1 then (if a2 then 3 else 3) else (if a2 then 0 else 0))))%N.
  move=> s a0 a1 a2.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
      (let: (a, b, _) := w in (a && b) == s)
        && ((nth false (arr w) 0 == a0) && ((nth false (arr w) 1 == a1)
            && (nth false (arr w) 2 == a2))))); last first.
    move=> w /=; rewrite inE /=.
    rewrite xpair_eqE /Secret /ViewA /=.
    by case: w => [[a b] k] /=; rewrite -val_eqE /= !eqseq_cons andbT.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: s; case: a0; case: a1; case: a2.
have hterm : forall (t : (size [:: 0; 1; 2]%N).-tuple bool) (nv nt nf : nat),
   #|preim (ViewA [:: 0; 1; 2]%N) (pred1 t)| = nv ->
   #|preim [% Secret, ViewA [:: 0; 1; 2]%N] (pred1 (true, t))| = nt ->
   #|preim [% Secret, ViewA [:: 0; 1; 2]%N] (pred1 (false, t))| = nf ->
   (0 < nv)%N ->
   pfwd1 (ViewA [:: 0; 1; 2]%N) t * centropy1_RV (ViewA [:: 0; 1; 2]%N) Secret t =
   nv%:R / 20%:R *
   (- (nt%:R / nv%:R) * log (nt%:R / nv%:R) - (nf%:R / nv%:R) * log (nf%:R / nv%:R)).
  move=> t nv nt nf Hv Ht Hf Hpos.
  by rewrite count_pr Hv (condent_ratio Hv Ht Hf Hpos).
rewrite (bigD1 [tuple of [:: false; true; true]]) //=.
rewrite (bigD1 [tuple of [:: true; true; false]]) //=.
rewrite big1; last first.
  move=> i; case/tupleP: i => a0 /tupleP[a1 /tupleP[a2 a3]].
  rewrite (tuple0 a3) /=.
  case: a0; case: a1; case: a2 => //=.
  - move=> _; rewrite (hterm [tuple true; true; true] 1 1 0 (cardV3 true true true)
      (cardJ3 true true true true) (cardJ3 false true true true) (ltn0Sn _))
      (binent_det1 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple true; false; true] 6 0 6 (cardV3 true false true)
      (cardJ3 true true false true) (cardJ3 false true false true) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple true; false; false] 1 1 0 (cardV3 true false false)
      (cardJ3 true true false false) (cardJ3 false true false false) (ltn0Sn _))
      (binent_det1 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple false; true; false] 3 0 3 (cardV3 false true false)
      (cardJ3 true false true false) (cardJ3 false false true false) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple false; false; true] 1 1 0 (cardV3 false false true)
      (cardJ3 true false false true) (cardJ3 false false false true) (ltn0Sn _))
      (binent_det1 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite count_pr (cardV3 false false false) /= !mul0r //.
rewrite (hterm [tuple false; true; true] 4 1 3 (cardV3 false true true)
  (cardJ3 true false true true) (cardJ3 false false true true) (ltn0Sn _)).
rewrite (hterm [tuple true; true; false] 4 1 3 (cardV3 true true false)
  (cardJ3 true true true false) (cardJ3 false true true false) (ltn0Sn _)).
rewrite !binent_1_4 addr0.
lra.
Qed.

(** leak_k3_gap — the gapped three cards {0, 1, 3} leak 6/5 - (9/20) log 3
    bits about a && b, the same value as the consecutive triple {0, 1, 2}.
    @main security: the mutual information between the secret and the colours
    at positions {0, 1, 3}. *)
Lemma leak_k3_gap :
  `I( Secret ; ViewA [:: 0; 1; 3]%N ) = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Proof.
rewrite mutual_info_RVE H_secret centropy_RVE'.
have cardV3 : forall a0 a1 a2 : bool,
  #|preim (ViewA [:: 0; 1; 3]%N) (pred1 [tuple of [:: a0; a1; a2]])| =
  (if a0 then (if a1 then (if a2 then 3 else 2) else (if a2 then 4 else 3))
         else (if a1 then (if a2 then 4 else 3) else (if a2 then 1 else 0)))%N.
  move=> a0 a1 a2.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
     (nth false (arr w) 0 == a0) && (nth false (arr w) 1 == a1)
       && (nth false (arr w) 3 == a2))); last first.
    move=> w /=.
    by rewrite /ViewA inE /= -val_eqE /= !eqseq_cons andbT andbA.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: a0; case: a1; case: a2.
have cardJ3 : forall (s a0 a1 a2 : bool),
  #|preim [% Secret, ViewA [:: 0; 1; 3]%N]
      (pred1 (s, [tuple of [:: a0; a1; a2]]))| =
  (if s
   then (if a0 then (if a1 then (if a2 then 0 else 2) else (if a2 then 1 else 0))
               else (if a1 then (if a2 then 1 else 0) else (if a2 then 1 else 0)))
   else (if a0 then (if a1 then (if a2 then 3 else 0) else (if a2 then 3 else 3))
               else (if a1 then (if a2 then 3 else 3) else (if a2 then 0 else 0))))%N.
  move=> s a0 a1 a2.
  rewrite -sum1_card (eq_bigl (fun w : Omega =>
      (let: (a, b, _) := w in (a && b) == s)
        && ((nth false (arr w) 0 == a0) && ((nth false (arr w) 1 == a1)
            && (nth false (arr w) 3 == a2))))); last first.
    move=> w /=; rewrite inE /=.
    rewrite xpair_eqE /Secret /ViewA /=.
    by case: w => [[a b] k] /=; rewrite -val_eqE /= !eqseq_cons andbT.
  rewrite big_mkcond /= stepO.
  under eq_bigr=> ab _ do rewrite !big_ord_recl big_ord0 addn0 /=.
  rewrite stepBB !big_bool /=.
  by case: s; case: a0; case: a1; case: a2.
have hterm : forall (t : (size [:: 0; 1; 3]%N).-tuple bool) (nv nt nf : nat),
   #|preim (ViewA [:: 0; 1; 3]%N) (pred1 t)| = nv ->
   #|preim [% Secret, ViewA [:: 0; 1; 3]%N] (pred1 (true, t))| = nt ->
   #|preim [% Secret, ViewA [:: 0; 1; 3]%N] (pred1 (false, t))| = nf ->
   (0 < nv)%N ->
   pfwd1 (ViewA [:: 0; 1; 3]%N) t * centropy1_RV (ViewA [:: 0; 1; 3]%N) Secret t =
   nv%:R / 20%:R *
   (- (nt%:R / nv%:R) * log (nt%:R / nv%:R)
    - (nf%:R / nv%:R) * log (nf%:R / nv%:R)).
  move=> t nv nt nf Hv Ht Hf Hpos.
  by rewrite count_pr Hv (condent_ratio Hv Ht Hf Hpos).
rewrite (bigD1 [tuple of [:: false; true; true]]) //=.
rewrite (bigD1 [tuple of [:: true; false; true]]) //=.
rewrite big1; last first.
  move=> i; case/tupleP: i => a0 /tupleP[a1 /tupleP[a2 a3]].
  rewrite (tuple0 a3) /=.
  case: a0; case: a1; case: a2 => //=.
  - move=> _; rewrite (hterm [tuple true; true; true] 3 0 3 (cardV3 true true true)
      (cardJ3 true true true true) (cardJ3 false true true true) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple true; true; false] 2 2 0 (cardV3 true true false)
      (cardJ3 true true true false) (cardJ3 false true true false) (ltn0Sn _))
      (binent_det1 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple true; false; false] 3 0 3 (cardV3 true false false)
      (cardJ3 true true false false) (cardJ3 false true false false) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple false; true; false] 3 0 3 (cardV3 false true false)
      (cardJ3 true false true false) (cardJ3 false false true false) (ltn0Sn _))
      (binent_det0 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite (hterm [tuple false; false; true] 1 1 0 (cardV3 false false true)
      (cardJ3 true false false true) (cardJ3 false false false true) (ltn0Sn _))
      (binent_det1 (ltn0Sn _)) mulr0 //.
  - move=> _; rewrite count_pr (cardV3 false false false) /= !mul0r //.
rewrite (hterm [tuple false; true; true] 4 1 3 (cardV3 false true true)
  (cardJ3 true false true true) (cardJ3 false false true true) (ltn0Sn _)).
rewrite (hterm [tuple true; false; true] 4 1 3 (cardV3 true false true)
  (cardJ3 true true false true) (cardJ3 false true false true) (ltn0Sn _)).
rewrite !binent_1_4 addr0.
lra.
Qed.

(** leak_k4 — four cards leak the full secret entropy 2 - (3/4) log 3 bits.
    @main security: the mutual information between the secret and the colours
    at positions {0, 1, 2, 3} equals H(Secret), so the secret is determined. *)
Lemma leak_k4 :
  `I( Secret ; ViewA [:: 0; 1; 2; 3]%N ) = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof.
have HV4 : forall w : Omega, val (ViewA [:: 0%N; 1; 2; 3] w) =
    [:: nth false (arr w) 0; nth false (arr w) 1;
        nth false (arr w) 2; nth false (arr w) 3].
  by move=> w; rewrite /ViewA /=.
pose g4 : (size [:: 0%N; 1; 2; 3]).-tuple bool -> bool :=
  fun t => fc_three_consec (val t ++ [:: count id (val t) == 2%N]).
have HSec : Secret = g4 `o (ViewA [:: 0%N; 1; 2; 3]).
  apply: boolp.funext => w; rewrite /comp_RV /g4 HV4.
  case: w => [[a b] k]; rewrite /Secret /arr /fc_shuffle.
  by case: a; case: b; case: k => -[|[|[|[|[|m]]]]] Hk //=.
by rewrite mutual_info_RVE {2}HSec centropy_RV_comp0 subr0 H_secret.
Qed.

(** leak_k5 — all five cards leak the full secret entropy 2 - (3/4) log 3 bits.
    @main security: the mutual information between the secret and the colours
    at all positions {0, 1, 2, 3, 4} equals H(Secret). *)
Lemma leak_k5 :
  `I( Secret ; ViewA [:: 0; 1; 2; 3; 4]%N ) = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof.
pose g5 : (size [:: 0%N; 1; 2; 3; 4]).-tuple bool -> bool :=
  fun t => fc_three_consec (val t).
have HV : forall w : Omega, val (ViewA [:: 0%N; 1; 2; 3; 4] w) = arr w.
  move=> w; rewrite /ViewA /=.
  have Hsz : size (arr w) = 5.
    by case: w => [[a b] k] /=; rewrite /fc_shuffle size_rot fc_arrange_size.
  by move: Hsz; case E: (arr w) => [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 l]]]]]] //= _.
have HSec : Secret = g5 `o (ViewA [:: 0%N; 1; 2; 3; 4]).
  apply: boolp.funext => w; rewrite /comp_RV /g5 HV.
  by case: w => [[a b] k]; rewrite /Secret /arr (esym (fc_correct a b (ltn_ord k))).
by rewrite mutual_info_RVE {2}HSec centropy_RV_comp0 subr0 H_secret.
Qed.

Local Notation p0 := (Ordinal (isT : (0 < 5)%N)).
Local Notation p1 := (Ordinal (isT : (1 < 5)%N)).
Local Notation p2 := (Ordinal (isT : (2 < 5)%N)).
Local Notation p3 := (Ordinal (isT : (3 < 5)%N)).
Local Notation p4 := (Ordinal (isT : (4 < 5)%N)).

(** ViewT — the view at a tuple of card positions.
    @intent: the partial view at a tuple of positions; component i reads the
    colour of arr w at position tnth t i. *)
Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

(** ViewS — the view at a set of card positions.
    @intent: the partial view at a set of positions, read in ascending
    enumeration order via enum_tuple. *)
Definition ViewS (S : {set 'I_5}) : {RV P -> #|S|.-tuple bool} :=
  ViewT (enum_tuple S).

(** adjacent — cyclic adjacency of a two-element set of positions.
    @intent: the two elements of a 2-set lie at cyclic distance 1, i.e.
    S = {i, sigma i} for some i. *)
Definition adjacent (S : {set 'I_5}) : bool :=
  [exists i : 'I_5, S == [set i; fc_sigma_fun i]].

(** leak — the exact mutual information, in bits, between the den Boer secret
    and the view at S.
    @intent: the closed-form leakage of a reveal pattern, classified by
    cardinality with the adjacency split at two cards. *)
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

(** setb5 — a subset of 'I_5 presented by five membership bits.
    @intent: the subset of 'I_5 whose membership vector is the five given
    bits. *)
Definition setb5 (b0 b1 b2 b3 b4 : bool) : {set 'I_5} :=
  [set i : 'I_5 | nth false [:: b0; b1; b2; b3; b4] (val i)].

(** mem_setb5 — membership in setb5 is the bit at the position's index.
    @composes: card_setb5 *)
Lemma mem_setb5 (b0 b1 b2 b3 b4 : bool) (x : 'I_5) :
  (x \in setb5 b0 b1 b2 b3 b4) = nth false [:: b0; b1; b2; b3; b4] (val x).
Proof. by rewrite inE. Qed.

(** exists_ord5 — an existential quantifier over 'I_5 is the disjunction of its
    five instances.
    @composes: adjacentE *)
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

(** setb5_eq — two bit-presented subsets are equal exactly when their bit
    vectors are.
    @composes: adjacentE *)
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

(** adjacentE — adjacency of a bit-presented subset is the boolean condition
    that exactly two bits are set at cyclically consecutive positions.
    @composes: leak_view_set *)
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

(** setb5_onto — every subset of 'I_5 is bit-presented.
    @composes: leak_view_set *)
Lemma setb5_onto (S : {set 'I_5}) :
  exists b0 b1 b2 b3 b4 : bool, S = setb5 b0 b1 b2 b3 b4.
Proof.
exists (p0 \in S), (p1 \in S), (p2 \in S), (p3 \in S), (p4 \in S).
apply/setP => x; rewrite mem_setb5.
by case: x => [[|[|[|[|[|m]]]]] Hm] //=; congr (_ \in S); apply: val_inj.
Qed.

(** enum_val5 — the indices enumerating a subset of 'I_5 described by a
    predicate on nat are that predicate's filter of the first five naturals.
    @composes: enum_setb5 *)
Lemma enum_val5 (S : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in S) = q (val x)) ->
  map val (enum S) = filter q (iota 0 5).
Proof.
move=> hq; rewrite -val_enum_ord filter_map; congr (map _ _).
by rewrite {1}/enum_mem -enumT; apply: eq_filter => x /=; exact: hq.
Qed.

(** card_val5 — the cardinality of a subset of 'I_5 described by a predicate on
    nat is the length of that predicate's filter of the first five naturals.
    @composes: card_setb5 *)
Lemma card_val5 (S : {set 'I_5}) (q : pred nat) :
  (forall x : 'I_5, (x \in S) = q (val x)) -> #|S| = size (filter q (iota 0 5)).
Proof. by move=> hq; rewrite cardE -(size_map val) (enum_val5 hq). Qed.

(** card_setb5 — the cardinality of a bit-presented subset counts its set
    bits.
    @composes: leak_view_set *)
Lemma card_setb5 (b0 b1 b2 b3 b4 : bool) :
  #|setb5 b0 b1 b2 b3 b4|
  = size (filter (fun n => nth false [:: b0; b1; b2; b3; b4] n) (iota 0 5)).
Proof. by apply: card_val5 => x; exact: mem_setb5. Qed.

(** enum_setb5 — the enumeration indices of a bit-presented subset are the
    indices of its set bits, in increasing order.
    @composes: leak_view_set *)
Lemma enum_setb5 (b0 b1 b2 b3 b4 : bool) :
  map val (enum (setb5 b0 b1 b2 b3 b4))
  = filter (fun n => nth false [:: b0; b1; b2; b3; b4] n) (iota 0 5).
Proof. by apply: enum_val5 => x; exact: mem_setb5. Qed.

(** leakE0 — a reveal pattern of no card has leak zero.
    @composes: leak_view_set *)
Lemma leakE0 (S : {set 'I_5}) : #|S| = 0%N -> leak S = 0.
Proof. by rewrite /leak => ->. Qed.

(** leakE1 — a reveal pattern of one card has leak zero.
    @composes: leak_view_set *)
Lemma leakE1 (S : {set 'I_5}) : #|S| = 1%N -> leak S = 0.
Proof. by rewrite /leak => ->. Qed.

(** leakE2adj — a reveal pattern of two adjacent cards has leak
    27/10 - (1/4) log 5 - (7/10) log 7.
    @composes: leak_view_set *)
Lemma leakE2adj (S : {set 'I_5}) : #|S| = 2%N -> adjacent S ->
  leak S = 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R.
Proof. by rewrite /leak => -> ->. Qed.

(** leakE2dist2 — a reveal pattern of two non-adjacent cards has leak
    5/2 - (3/20) log 3 - (1/2) log 5 - (7/20) log 7.
    @composes: leak_view_set *)
Lemma leakE2dist2 (S : {set 'I_5}) : #|S| = 2%N -> ~~ adjacent S ->
  leak S = 5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
           - (7%:R / 20%:R) * log 7%:R.
Proof. by rewrite /leak => -> /negbTE ->. Qed.

(** leakE3 — a reveal pattern of three cards has leak 6/5 - (9/20) log 3.
    @composes: leak_view_set *)
Lemma leakE3 (S : {set 'I_5}) : #|S| = 3%N ->
  leak S = 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R.
Proof. by rewrite /leak => ->. Qed.

(** leakE4 — a reveal pattern of four cards has leak 2 - (3/4) log 3.
    @composes: leak_view_set *)
Lemma leakE4 (S : {set 'I_5}) : #|S| = 4%N ->
  leak S = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof. by rewrite /leak => ->. Qed.

(** leakE5 — a reveal pattern of five cards has leak 2 - (3/4) log 3.
    @composes: leak_view_set *)
Lemma leakE5 (S : {set 'I_5}) : #|S| = 5%N ->
  leak S = 2%:R - (3%:R / 4%:R) * log 3%:R.
Proof. by rewrite /leak => ->. Qed.

(** injective_mutual_info_RV — relabeling the alphabet of a random variable by
    an injection leaves its mutual information with any other random variable
    unchanged, an upstream candidate next to infotheo's
    injective_joint_entropy.
    @composes: mutual_info_ViewT_rot *)
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

(** rot_tuple_inj — cyclic rotation of a tuple is injective.
    @composes: mutual_info_ViewT_rot *)
Lemma rot_tuple_inj (T : Type) k n :
  injective (fun t : k.-tuple T => rot_tuple n t).
Proof. by move=> x y /(congr1 val) /= /rot_inj /val_inj. Qed.

(** ViewTE — the view at a position tuple is the row read pointwise along that
    tuple.
    @composes: ViewT_rot *)
Lemma ViewTE k (t : k.-tuple 'I_5) (w : Omega) :
  ViewT t w = map_tuple (fun j : 'I_5 => nth false (arr w) (val j)) t.
Proof. by apply: eq_from_tnth => i; rewrite /ViewT tnth_mktuple tnth_map. Qed.

(** ViewT_rot — rotating the position tuple rotates the view tuple.
    @composes: mutual_info_ViewT_rot *)
Lemma ViewT_rot k n (t : k.-tuple 'I_5) :
  ViewT (rot_tuple n t) = (fun x : k.-tuple bool => rot_tuple n x) `o ViewT t.
Proof.
apply: boolp.funext => w; rewrite /comp_RV !ViewTE; apply: val_inj => /=.
exact: map_rot.
Qed.

(** mutual_info_ViewT_rot — rotating the position tuple leaves the leakage
    unchanged.
    @composes: leak_view_set *)
Lemma mutual_info_ViewT_rot k n (t : k.-tuple 'I_5) :
  `I( Secret ; ViewT (rot_tuple n t) ) = `I( Secret ; ViewT t ).
Proof.
by rewrite ViewT_rot; apply: injective_mutual_info_RV; exact: rot_tuple_inj.
Qed.

(** mutual_info_ViewS_ViewT — the set-indexed view has the leakage of the
    tuple-indexed view at any position tuple of the same length and the same
    ascending values.
    @composes: leak_view_set *)
Lemma mutual_info_ViewS_ViewT (S : {set 'I_5}) k (t : k.-tuple 'I_5)
    (e : #|S| = k) :
  map val (val (enum_tuple S)) = map val (val t) ->
  `I( Secret ; ViewS S ) = `I( Secret ; ViewT t ).
Proof.
by move: t; case: k / e => t hv; rewrite /ViewS (val_inj (inj_map val_inj hv)).
Qed.

(** val_fc_sigma_fun — the five-cycle shift sends a position to its successor
    modulo five.
    @composes: ViewT_sigma *)
Lemma val_fc_sigma_fun (i : 'I_5) : val (fc_sigma_fun i) = (i.+1 %% 5)%N.
Proof. by case: i => [[|[|[|[|[|m]]]]] Hm]. Qed.

(** fc_sigmaKV — fc_sigma_fun cancels fc_sigma_inv.
    @composes: cut_sigmaKV *)
Lemma fc_sigmaKV : cancel fc_sigma_inv fc_sigma_fun.
Proof. by move=> x; apply: val_inj; case: x => [[|[|[|[|[|m]]]]] Hm]. Qed.

(** cut_sigma — the cut advance on the sample space.
    @intent: the sample-space map advancing the cut by one cyclic shift,
    identity on the two input bits. *)
Definition cut_sigma (w : Omega) : Omega :=
  let: (a, b, k) := w in (a, b, fc_sigma_fun k).

(** cut_sigma_inv — the cut retraction on the sample space.
    @intent: the sample-space map retracting the cut by one cyclic shift. *)
Definition cut_sigma_inv (w : Omega) : Omega :=
  let: (a, b, k) := w in (a, b, fc_sigma_inv k).

(** cut_sigmaK — cut_sigma_inv cancels cut_sigma.
    @composes: fdistmap_cut_sigma *)
Lemma cut_sigmaK : cancel cut_sigma cut_sigma_inv.
Proof. by move=> [[a b] k]; rewrite /= fc_sigmaK. Qed.

(** cut_sigmaKV — cut_sigma cancels cut_sigma_inv.
    @composes: fdistmap_cut_sigma *)
Lemma cut_sigmaKV : cancel cut_sigma_inv cut_sigma.
Proof. by move=> [[a b] k]; rewrite /= fc_sigmaKV. Qed.

(** fdistmap_cut_sigma — the uniform distribution on the sample space is
    invariant under the cut shift.
    @composes: mutual_info_ViewT_sigma *)
Lemma fdistmap_cut_sigma : fdistmap cut_sigma P = P.
Proof.
apply/fdist_ext => w; rewrite fdistmapE.
rewrite (big_pred1 (cut_sigma_inv w)); last first.
  by move=> i; rewrite !inE /=; apply/idP/idP => [/eqP <-|/eqP ->];
     rewrite ?cut_sigmaK ?cut_sigmaKV.
by rewrite /P !fdist_uniformE.
Qed.

(** ViewT_sigma — reading the shifted positions of an outcome is reading the
    original positions of the shifted outcome.
    @composes: mutual_info_ViewT_sigma *)
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

(** mutual_info_ViewT_sigma — shifting every position of the tuple by the
    five-cycle leaves the leakage unchanged.
    @composes: leak_view_set *)
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

(** map_tnth — mapping a function along the components of a tuple is mapping it
    along the tuple's underlying sequence.
    @composes: ViewT_ViewA *)
Lemma map_tnth (T1 T2 : Type) n (t : n.-tuple T1) (f : T1 -> T2) :
  [seq f (tnth t i) | i <- enum 'I_n] = [seq f j | j <- val t].
Proof.
have e : [seq f (tnth t i) | i <- enum 'I_n] = [seq f j | j <- tval t].
  by rewrite -(map_tnth_enum t) -[RHS]map_comp.
exact: e.
Qed.

(** ViewT_ViewA — the tuple-indexed view at t is the position-list view at the
    list of values of t.
    @composes: leak_view_set *)
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

(** leak_k0 — revealing no card leaks nothing about a && b.
    @main security: the empty reveal carries no information about the
    secret. *)
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

(** leak_view_set — the mutual information between the den Boer secret and the
    view at any subset of the five row positions is the closed form leak S.
    @main security: for every subset of the five positions, the mutual
    information between the secret and the revealed colours equals the closed
    form leak; all thirty-two reveal patterns in one statement. *)
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

End five_card_leakage.
