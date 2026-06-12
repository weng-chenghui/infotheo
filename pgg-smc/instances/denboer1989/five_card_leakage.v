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

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
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
    @composes: leak_k2_d2. *)
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

(** leak_k2_d2 — two distance-2 cards leak
    5/2 - (3/20) log 3 - (1/2) log 5 - (7/20) log 7 bits about a && b.
    @main security: the mutual information between the secret and the colours
    at the distance-2 positions {0, 2}. *)
Lemma leak_k2_d2 :
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

End five_card_leakage.
