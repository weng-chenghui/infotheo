From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_tactics.
Require Import spp_proba homomorphic_encryption entropy_fiber.
Require Import entropy_fiber_zpq.  (* General entropy framework for Z/pqZ *)
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program.
Require Import linear_fiber_zpq.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

(*
  CRT Reconstruction Section
  ==========================
  
  This section formalizes the DSDP protocol over composite modulus Z/pqZ
  instead of prime field F_m. The key insight from CRT is:
  
    Z/pqZ ≅ Z/pZ × Z/qZ  (when gcd(p,q) = 1)
  
  For the constraint u2*v2 + u3*v3 = target:
    - 1 equation, 2 unknowns → 1 degree of freedom
    - Over Z/p: p solutions
    - Over Z/q: q solutions  
    - Over Z/pq: p × q = pq solutions (via CRT product rule)
  
  Security condition: U3 < min(p,q) ensures U3 is invertible in both
  Z/p and Z/q (since it can't be divisible by either prime).
*)
Section dsdp_entropy.

Context {R : realType}.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q)%N.
(* Use Zp ring structure for composite modulus arithmetic *)
Local Notation msg := 'Z_m.

(* Fiber from full constraint: s - u1*v1 = u2*v2 + u3*v3.
   Uses linear_fiber_2d from linear_fiber_zpq.v for the generic 2D linear fiber. *)
Definition dsdp_fiber (u1 u2 u3 v1 s : msg) : {set msg * msg} :=
  linear_fiber_2d u2 u3 (s - u1 * v1)%R.

Variable T : finType.
Variable P : R.-fdist T.
Variables (V1 V2 V3 U1 U2 U3 S : {RV P -> msg}).
Let CondRV : {RV P -> (msg * msg * msg * msg * msg)} :=
  [% V1, U1, U2, U3, S].
Let VarRV : {RV P -> (msg * msg)} := [%V2, V3].

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Let card_msg_pair : #|((msg * msg)%type : finType)| = (m ^ 2)%N.
Proof. by rewrite card_prod !card_msg expnS expn1. Qed.

Definition dsdp_constraint (cond : msg * msg * msg * msg * msg)
  (var : msg * msg) : bool :=
  let '(v1, u1, u2, u3, s) := cond in
  let '(v2, v3) := var in
  (s - u1 * v1 == u2 * v2 + u3 * v3)%R.

(* The constraint on explicit components, so a caller can rewrite with it
   instead of unfolding the definition. *)
Lemma dsdp_constraintE (v1 u1 u2 u3 s v2 v3 : msg) :
  dsdp_constraint (v1, u1, u2, u3, s) (v2, v3)
  = (s - u1 * v1 == u2 * v2 + u3 * v3)%R.
Proof. by []. Qed.

Hypothesis constraint_holds :
  forall t, dsdp_constraint (CondRV t) (VarRV t).

(* Cryptographic assumptions for DSDP security:
   1. VarRV = (V2, V3) is uniformly distributed over msg × msg
   2. VarRV is independent of the inputs (V1, U1, U2, U3)
   These are standard assumptions in secure multi-party computation. *)
Hypothesis VarRV_uniform : `p_ VarRV = fdist_uniform card_msg_pair.
Hypothesis VarRV_indep_inputs : P |= [%V1, U1, U2, U3] _|_ VarRV.

(* ========================================================================= *)
(*    Instantiation of entropy_fiber_zpq for DSDP constraint structure       *)
(* ========================================================================= *)

(* Abbreviation for [%V1, U1, U2, U3] - the inputs independent of VarRV *)
Let InputRV : {RV P -> (msg * msg * msg * msg)} := [%V1, U1, U2, U3].

(* DSDP fiber function: maps condition tuple to fiber set *)
Let dsdp_fiber_fn (cond : msg * msg * msg * msg * msg) : {set msg * msg} :=
  let '(v1, u1, u2, u3, s) := cond in dsdp_fiber u1 u2 u3 v1 s.

(* DSDP projection: extracts input part from condition *)
Let dsdp_proj_input (cond : msg * msg * msg * msg * msg) : msg * msg * msg * msg :=
  let '(v1, u1, u2, u3, _) := cond in (v1, u1, u2, u3).

(* Prerequisite 1: VarRV is always in the fiber of CondRV *)
Let constraint_fiber_dsdp : forall t, VarRV t \in dsdp_fiber_fn (CondRV t).
Proof.
move=> t.
rewrite /dsdp_fiber_fn /dsdp_fiber /linear_fiber_2d inE /=.
apply/eqP.
move: (constraint_holds t).
by rewrite /dsdp_constraint /CondRV /VarRV /= => /eqP.
Qed.

(* Prerequisite 2: InputRV is the projection of CondRV *)
Let InputRV_proj_dsdp : forall t, InputRV t = dsdp_proj_input (CondRV t).
Proof. by move=> t. Qed.

(* Prerequisite 3: Joint probability relation - DSDP-specific.
   The joint [%VarRV, CondRV] probability equals [%VarRV, InputRV]
   when (v2,v3) is in the fiber (constraint is satisfied).
   This captures that S is determined by the constraint. *)
Let joint_eq_input_dsdp :
  forall (cond : msg * msg * msg * msg * msg) (var : msg * msg),
    var \in dsdp_fiber_fn cond ->
    `Pr[[%VarRV, CondRV] = (var, cond)] =
    `Pr[[%VarRV, InputRV] = (var, dsdp_proj_input cond)].
Proof.
move=> [[[[v1 u1] u2] u3] s] [v2 v3] /= Hin_fiber.
(* Both sides count the same events because S is determined by the constraint *)
rewrite !pfwd1E.
congr Pr.
apply/setP => t0.
rewrite !inE /= !xpair_eqE.
apply/idP/idP => H.
- (* LHS -> RHS: drop S and rearrange *)
  move/and3P: H => [Hvar Hinput Hs].
  move/andP: Hinput => [Hinput3 Hu3].
  move/andP: Hinput3 => [Hinput2 Hu2].
  move/andP: Hinput2 => [Hv1 Hu1].
  apply/and3P.
  split => //.
  by rewrite Hv1 Hu1 Hu2.
- (* RHS -> LHS: derive S=s from constraint *)
  move/and3P: H => [Hvar Hinput3 Hu3].
  move/andP: Hinput3 => [Hinput2 Hu2].
  move/andP: Hinput2 => [Hv1 Hu1].
  apply/and3P.
  split => //.
  + by rewrite Hv1 Hu1 Hu2 Hu3.
  + (* S t0 = s follows from the constraint *)
    move/andP: Hvar => [/eqP Hv2_eq /eqP Hv3_eq].
    move/eqP: Hv1 => Hv1_eq.
    move/eqP: Hu1 => Hu1_eq.
    move/eqP: Hu2 => Hu2_eq.
    move/eqP: Hu3 => Hu3_eq.
    move: (constraint_holds t0).
    rewrite /dsdp_constraint /CondRV /VarRV /=.
    rewrite Hv1_eq Hu1_eq Hu2_eq Hu3_eq Hv2_eq Hv3_eq.
    move=> /eqP Hconstr.
    move: Hin_fiber.
    rewrite /dsdp_fiber_fn /dsdp_fiber /linear_fiber_2d inE /=.
    move=> /eqP Hfiber_eq.
    apply/eqP.
    have Heq: S t0 - u1 * v1 = s - u1 * v1.
      by rewrite Hconstr Hfiber_eq.
    by move: Heq => /(f_equal (fun x => x + u1 * v1)); rewrite !subrK.
Qed.

(* The number of input pairs consistent with one fixed value of Alice's view
   data.  It is m whenever her trust weight on Charlie lies strictly between
   0 and both primes, since such a weight is divisible by neither and is
   therefore invertible.  What the bound buys is uniformity rather than size:
   the count is m for every view value alike, and that is what turns it into
   a conditional entropy of log m.  A weight sharing a factor with the
   modulus does not simply shrink the count, it makes the count depend on the
   view, leaving some views impossible and others with more candidates than
   m.  The weight is a public protocol parameter, so this is a condition on
   how the protocol is configured rather than an assumption about an
   adversary. *)
Lemma dsdp_fiber_card (u1 u2 u3 v1 s : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|dsdp_fiber u1 u2 u3 v1 s| = m.
Proof.
move=> Hu3_pos Hu3_lt.
rewrite /dsdp_fiber /linear_fiber_2d.
exact: (linear_fiber_2d_card prime_p prime_q).
Qed.

(* Non-solutions have zero probability *)
Lemma Pr_dsdp_nosol_eq0 (u1 u2 u3 v1 s : msg) (v2 v3 : msg) :
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  (v2, v3) \notin dsdp_fiber u1 u2 u3 v1 s ->
  `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] = 0.
Proof.
move=> Hcond_pos Hnot_solution.
(* Define constraint as fiber membership *)
set constraint := fun (conds : msg * msg * msg * msg * msg)
  (vals : msg * msg) =>
  let '(v1, u1, u2, u3, s) := conds in
  let '(v2, v3) := vals in
  (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s.
have Hconstraint: forall t, constraint (CondRV t) (VarRV t).
  move=> t.
  rewrite /constraint /=.
  rewrite /dsdp_fiber /linear_fiber_2d inE /=.
  apply/eqP.
  (* constraint_holds gives: s - u1*v1 = u2*v2 + u3*v3 *)
  (* We need: u2*v2 + u3*v3 = s - u1*v1 *)
  move: (constraint_holds t).
  rewrite /dsdp_constraint /CondRV /VarRV /=.
  by move=> /eqP ->.
by rewrite (cond_prob_zero_outside_constraint Hconstraint Hcond_pos).
Qed.

(* Solutions have uniform probability.
   Instantiates cPr_uniform_fiber from entropy_fiber_zpq.v with DSDP structure. *)
Lemma Pr_dsdp_sol_uniform (u1 u2 u3 v1 s : msg) (v2 v3 : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s ->
  `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] = m%:R^-1.
Proof.
move=> Hu3_pos Hu3_lt Hcond_pos Hin.
(* Fiber cardinality = m *)
have Hcard: #|dsdp_fiber u1 u2 u3 v1 s| = m.
  by apply: dsdp_fiber_card.
(* Apply cPr_uniform_fiber from entropy_fiber_zpq.v.
   The card_msg_pair parameter is now implicit and accepts any proof. *)
have Hcpr := @cPr_uniform_fiber R p_minus_2 q_minus_2
               T P VarRV (msg * msg * msg * msg)%type InputRV
               (msg * msg * msg * msg * msg)%type CondRV
               dsdp_fiber_fn dsdp_proj_input
               constraint_fiber_dsdp InputRV_proj_dsdp
               card_msg_pair VarRV_uniform VarRV_indep_inputs
               joint_eq_input_dsdp
               (v1, u1, u2, u3, s) (v2, v3) Hcond_pos Hin.
by rewrite Hcpr /= Hcard.
Qed.

(* Helper: Each conditioning value gives entropy log(m).
   Uses centropy1_uniform_over_set directly with DSDP-specific probability lemmas. *)
Lemma dsdp_centropy1_uniform (v1 u1 u2 u3 s : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  `H[ VarRV | CondRV = (v1, u1, u2, u3, s) ] = log (m%:R : R).
Proof.
move=> Hu3_pos Hu3_lt Hcond_pos.
(* Fiber cardinality = m *)
have card_m : #|dsdp_fiber u1 u2 u3 v1 s| = m.
  by apply: dsdp_fiber_card.
(* Build uniform hypothesis using Pr_dsdp_sol_uniform *)
have Hsol_unif: forall pair : msg * msg,
    pair \in dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)] = 
    #|dsdp_fiber u1 u2 u3 v1 s|%:R^-1.
  move=> [v2 v3] Hin.
  by rewrite (Pr_dsdp_sol_uniform Hu3_pos Hu3_lt Hcond_pos Hin) card_m.
(* Build zero-outside hypothesis using Pr_dsdp_nosol_eq0 *)
have Hnonsol_zero: forall pair : msg * msg,
    pair \notin dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)] = 0.
  move=> [v2 v3] Hnotin.
  exact: Pr_dsdp_nosol_eq0.
(* Apply general lemma *)
rewrite (@centropy1_uniform_over_set R T P _ _ VarRV CondRV
           (dsdp_fiber u1 u2 u3 v1 s) (v1, u1, u2, u3, s)
           Hcond_pos Hsol_unif Hnonsol_zero); first by rewrite card_m.
(* Prove fiber cardinality is positive: m = p*q > 0 since p, q are primes *)
by rewrite card_m muln_gt0 prime_gt0 // prime_gt0.
Qed.

(* The constraint function g for centropy_jcond_determined_fibers:
   given a value (v2,v3) of VarRV and a value (v1,u1,u2,u3) of InputRV,
   produces the value of S that satisfies the DSDP constraint. *)
Definition dsdp_g (var : msg * msg) (inp : msg * msg * msg * msg) : msg :=
  let '(v2, v3) := var in
  let '(v1, u1, u2, u3) := inp in
  (u1 * v1 + u2 * v2 + u3 * v3)%R.

(* Bridge: the DSDP fiber matches the abstract fiber set of dsdp_g. *)
Lemma dsdp_fiber_eq_abstract (v1 u1 u2 u3 s : msg) :
  dsdp_fiber u1 u2 u3 v1 s =
  [set x' : msg * msg | dsdp_g x' (v1, u1, u2, u3) == s].
Proof.
apply/setP => [[v2 v3]].
rewrite /dsdp_fiber /linear_fiber_2d !inE /dsdp_g /=.
apply/eqP/eqP => H.
- by rewrite -addrA H addrC subrK.
- by rewrite -H; ring.
Qed.

(* S is functionally determined by VarRV and InputRV through dsdp_g. *)
Lemma S_determined : S = (fun t => dsdp_g (VarRV t) (InputRV t)).
Proof.
apply: boolp.funext => t.
move: (constraint_holds t).
rewrite /dsdp_constraint /CondRV /VarRV /InputRV /dsdp_g /=.
move=> Heq.
move: Heq; rewrite subr_eq addrC => /eqP ->.
by rewrite addrA.
Qed.

(* Conditioned on Alice's inputs and the output (V1, U1, U2, U3, S), the relay
   private inputs (V2, V3) retain log m bits of uncertainty.  Same statement
   and same hypotheses as dsdp_centropy_uniform of dsdp_main.v, reached by a
   different route: here the conditional entropy is expanded into its
   per-point sum and each term is closed by dsdp_centropy1_uniform, where the
   apex proof instead factors through the generic fiber argument of
   centropy_jcond_determined_fibers.  The bound therefore has two independent
   derivations, one counting solutions point by point and one quotienting by
   the fibers of dsdp_g.  [3-party] *)
Theorem dsdp_centropy_uniform_direct :
  (forall t, (0 < U3 t)%N) ->
  (forall t, (U3 t < minn p q)%N) ->
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
move=> HU3_pos HU3_lt.
rewrite centropy_RVE' /=.
transitivity (\sum_(a : msg * msg * msg * msg * msg)
               `Pr[ CondRV = a ] * log (m%:R : R)).
  apply: eq_bigr => [] [] [] [] [] v1 u1 u2 u3 s H.
  have [->|Hcond_pos] := eqVneq (`Pr[CondRV = (v1, u1, u2, u3, s)]) 0.
    by rewrite !mul0r.
  have Hu3_pos: (0 < u3)%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
    by rewrite -HU3t; apply: HU3_pos.
  have Hu3_lt: (u3 < minn p q)%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
    by rewrite -HU3t; apply: HU3_lt.
  by rewrite (dsdp_centropy1_uniform Hu3_pos Hu3_lt Hcond_pos).
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.

Section dsdp_var_entropy.

(* m = p * q > 1 since p, q >= 2 *)
Let m_gt1 : (1 < m)%N.
Proof.
(* p >= 2, q >= 2, so p * q >= 4 > 1 *)
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

(* card_msg and card_msg_pair are inherited from outer section *)

(* Unconditional entropy of private inputs (V2, V3) when uniformly distributed.
   
   Since V2, V3 are private inputs from Bob and Charlie respectively,
   assuming uniform distribution gives H(V2,V3) = log(m²) = 2*log(m).
   
   Combined with the conditional entropy result H(V2,V3 | view) = log(m),
   this shows DSDP leaks log(m) bits but preserves log(m) bits of entropy.
   
   The security argument (joint_centropy_reduction at end of file) shows
   that H(V2,V3 | AliceView) = H(V2 | AliceView), i.e., knowing V3 given
   the constraint adds no information beyond knowing V2. *)
Lemma dsdp_var_entropy :
  `p_VarRV = fdist_uniform card_msg_pair ->
  `H `p_VarRV = log (m%:R * m%:R : R).
Proof.
move->.
rewrite entropy_uniform card_prod !card_msg.
by rewrite natrM.
Qed.

End dsdp_var_entropy.

End dsdp_entropy.

(* ========================================================================== *)
(* Ring-generic siblings of dsdp_fiber_card and Pr_dsdp_sol_uniform           *)
(* ========================================================================== *)

Section dsdp_entropy_ring.

Context {R_real : realType}.
Variable R : finComNzRingType.

(* Ring-generic fiber: solutions to u2*v2 + u3*v3 = s - u1*v1 in R*R. *)
Definition dsdp_fiber_ring (u1 u2 u3 v1 s : R) : {set R * R} :=
  [set vv : R * R | (u2 * vv.1 + u3 * vv.2 == s - u1 * v1)%R].

(* Ring-generic fiber cardinality: when u3 is left-regular, so that
   multiplication by it is injective, the fiber has #|R| solutions. *)
Lemma dsdp_fiber_card_ring (u1 u2 u3 v1 s : R) :
  GRing.lreg u3 ->
  #|dsdp_fiber_ring u1 u2 u3 v1 s| = #|R|.
Proof.
move=> Hinj.
have Hbij : bijective (fun v : R => u3 * v) by apply: (inj_card_bij Hinj).
case: Hbij => g Hg1 Hg2.
pose f := fun v2 : R => (v2, g (s - u1 * v1 - u2 * v2)).
have Hf_inj : injective f by move=> a b /=; case.
have Hf_image : [set f v2 | v2 : R] = dsdp_fiber_ring u1 u2 u3 v1 s.
  apply/setP => [[v2 v3]]; rewrite /dsdp_fiber_ring !inE.
  apply/imsetP/eqP.
  - by move=> [v2' _ [H1 H2]]; subst v2 v3; rewrite Hg2 addrC subrK.
  - move=> Heq; exists v2 => //=; congr pair.
    have Hv3 : u3 * v3 = s - u1 * v1 - u2 * v2 by rewrite -Heq addrC addKr.
    by rewrite -Hv3 Hg1.
by rewrite -Hf_image card_imset.
Qed.

Variable T : finType.
Variable P : R_real.-fdist T.
Variables (V1 V2 V3 U1 U2 U3 S : {RV P -> R}).

Let CondRV_r : {RV P -> (R * R * R * R * R)} := [%V1, U1, U2, U3, S].
Let VarRV_r : {RV P -> (R * R)} := [%V2, V3].
Let InputRV_r : {RV P -> (R * R * R * R)} := [%V1, U1, U2, U3].

Let card_R_gt0 : (0 < #|R|)%N.
Proof. by apply/card_gt0P; exists 0; rewrite inE. Qed.

Let card_RR_pair :
  #|((R * R)%type : finType)| = (#|R| * #|R|).-1.+1.
Proof.
rewrite card_prod prednK //.
by rewrite muln_gt0; apply/andP; split.
Qed.

(* dsdp_constraint_ring — the ring-generic DSDP linear constraint: for conditions
   (v1, u1, u2, u3, s) and variables (v2, v3), s - u1 * v1 = u2 * v2 + u3 * v3. *)
Definition dsdp_constraint_ring (cond : R * R * R * R * R)
  (var : R * R) : bool :=
  let '(v1, u1, u2, u3, s) := cond in
  let '(v2, v3) := var in
  (s - u1 * v1 == u2 * v2 + u3 * v3)%R.

(* The ring-generic constraint on explicit components. *)
Lemma dsdp_constraint_ringE (v1 u1 u2 u3 s v2 v3 : R) :
  dsdp_constraint_ring (v1, u1, u2, u3, s) (v2, v3)
  = (s - u1 * v1 == u2 * v2 + u3 * v3)%R.
Proof. by []. Qed.

Hypothesis constraint_holds_r :
  forall t, dsdp_constraint_ring (CondRV_r t) (VarRV_r t).

Hypothesis VarRV_uniform_r : `p_ VarRV_r = fdist_uniform card_RR_pair.
Hypothesis VarRV_indep_inputs_r : P |= InputRV_r _|_ VarRV_r.

Let dsdp_fiber_fn_r (cond : R * R * R * R * R) : {set R * R} :=
  let '(v1, u1, u2, u3, s) := cond in dsdp_fiber_ring u1 u2 u3 v1 s.

Let dsdp_proj_input_r (cond : R * R * R * R * R) : R * R * R * R :=
  let '(v1, u1, u2, u3, _) := cond in (v1, u1, u2, u3).

Let constraint_fiber_r :
  forall t, VarRV_r t \in dsdp_fiber_fn_r (CondRV_r t).
Proof.
move=> t.
rewrite /dsdp_fiber_fn_r /dsdp_fiber_ring /CondRV_r /VarRV_r /=.
rewrite inE /=.
apply/eqP.
move: (constraint_holds_r t).
by rewrite /dsdp_constraint_ring /CondRV_r /VarRV_r /= => /eqP.
Qed.

Let InputRV_proj_r :
  forall t, InputRV_r t = dsdp_proj_input_r (CondRV_r t).
Proof. by move=> t. Qed.

Let joint_eq_input_r :
  forall (cond : R * R * R * R * R) (var : R * R),
    var \in dsdp_fiber_fn_r cond ->
    `Pr[[%VarRV_r, CondRV_r] = (var, cond)] =
    `Pr[[%VarRV_r, InputRV_r] = (var, dsdp_proj_input_r cond)].
Proof.
move=> [[[[v1 u1] u2] u3] s] [v2 v3] /= Hin_fiber.
rewrite !pfwd1E.
congr Pr.
apply/setP => t0.
rewrite !inE /= !xpair_eqE.
apply/idP/idP => H.
- move/and3P: H => [Hvar Hinput Hs].
  move/andP: Hinput => [Hinput3 Hu3].
  move/andP: Hinput3 => [Hinput2 Hu2].
  move/andP: Hinput2 => [Hv1 Hu1].
  apply/and3P.
  split => //.
  by rewrite Hv1 Hu1 Hu2.
- move/and3P: H => [Hvar Hinput3 Hu3].
  move/andP: Hinput3 => [Hinput2 Hu2].
  move/andP: Hinput2 => [Hv1 Hu1].
  apply/and3P.
  split => //.
  + by rewrite Hv1 Hu1 Hu2 Hu3.
  + move/andP: Hvar => [/eqP Hv2_eq /eqP Hv3_eq].
    move/eqP: Hv1 => Hv1_eq.
    move/eqP: Hu1 => Hu1_eq.
    move/eqP: Hu2 => Hu2_eq.
    move/eqP: Hu3 => Hu3_eq.
    move: (constraint_holds_r t0).
    rewrite /dsdp_constraint_ring /CondRV_r /VarRV_r /=.
    rewrite Hv1_eq Hu1_eq Hu2_eq Hu3_eq Hv2_eq Hv3_eq.
    move=> /eqP Hconstr.
    move: Hin_fiber.
    rewrite /dsdp_fiber_fn_r /dsdp_fiber_ring inE /=.
    move=> /eqP Hfiber_eq.
    apply/eqP.
    have Heq: S t0 - u1 * v1 = s - u1 * v1.
      by rewrite Hconstr Hfiber_eq.
    by move: Heq => /eqP; rewrite -subr_eq0 opprB addrA subrK subr_eq0 => /eqP.
Qed.

(* Ring-generic conditional uniformity: when u3 is left-regular, (v2, v3) is
   uniform on the fiber given the conditioning view. *)
Lemma Pr_dsdp_sol_uniform_ring (u1 u2 u3 v1 s v2 v3 : R) :
  GRing.lreg u3 ->
  `Pr[CondRV_r = (v1, u1, u2, u3, s)] != 0 ->
  (v2, v3) \in dsdp_fiber_ring u1 u2 u3 v1 s ->
  `Pr[ VarRV_r = (v2, v3) | CondRV_r = (v1, u1, u2, u3, s) ] = #|R|%:R^-1.
Proof.
move=> Hu3 Hcond_pos Hin.
have Hcard: #|dsdp_fiber_ring u1 u2 u3 v1 s| = #|R|
  by apply: dsdp_fiber_card_ring.
have Hcpr := @gen_cPr_uniform_fiber R_real T P
               ((R * R)%type : finType) _ card_RR_pair
               VarRV_r ((R * R * R * R)%type : finType) InputRV_r
               ((R * R * R * R * R)%type : finType) CondRV_r
               dsdp_fiber_fn_r dsdp_proj_input_r
               constraint_fiber_r InputRV_proj_r
               VarRV_uniform_r VarRV_indep_inputs_r
               joint_eq_input_r
               (v1, u1, u2, u3, s) (v2, v3) Hcond_pos Hin.
by rewrite Hcpr /= Hcard.
Qed.

End dsdp_entropy_ring.

(* ========================================================================== *)
(* N-party entropy analysis                                                    *)
(* ========================================================================== *)

(* Generalization of the 3-party entropy result to N parties.

   For n_relay.+2 total parties (Alice + n_relay.+1 relays):
   - VarRV : {RV P -> {ffun 'I_n_relay.+1 -> msg}} — relay inputs
   - CondRV : (v0, u0, u_relay_vec, s) — constraint parameters
   - Fiber: \sum u_i * v_i = s - u0*v0  (n_relay.+1 unknowns, 1 equation)
   - |fiber| = m^n_relay  (n_relay free variables)
   - H[VarRV | CondRV = c] = n_relay * log m, for each conditioning value c
*)

Section dsdp_entropy_n.

Context {R : realType}.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q)%N.
Local Notation msg := 'Z_m.

Variable n_relay : nat.

Variable T : finType.
Variable P : R.-fdist T.

Let m_gt0 : (0 < m)%N.
Proof. by rewrite muln_gt0 prime_gt0 // prime_gt0. Qed.

Let card_ffun_msg : #|{ffun 'I_n_relay.+1 -> msg}| = (m ^ n_relay.+1).-1.+1.
Proof. by rewrite prednK ?expn_gt0 ?m_gt0 // card_ffun !card_ord Zp_cast. Qed.

(* Fiber for N-party constraint:
   s - u0*v0 = \sum_(i < n_relay.+1) u_rel(i) * v_rel(i) *)
Definition dsdp_fiber_n (u_rel : {ffun 'I_n_relay.+1 -> msg}) (target : msg)
    : {set {ffun 'I_n_relay.+1 -> msg}} :=
  @linear_fiber_nd p_minus_2 q_minus_2 n_relay u_rel target.

(* Condition type: (v0, u0, u_relay_vector, s) *)
Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
(* Input type: everything except s (which is determined by constraint) *)
Let InputT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg})%type.

Variable VarRV : {RV P -> {ffun 'I_n_relay.+1 -> msg}}.
Variable CondRV : {RV P -> CondT_n}.
Variable InputRV : {RV P -> InputT_n}.

Let dsdp_fiber_fn_n (cond : CondT_n) : {set {ffun 'I_n_relay.+1 -> msg}} :=
  let '(v0, u0, u_rel, s) := cond in
  dsdp_fiber_n u_rel (s - u0 * v0).

Let dsdp_proj_input_n (cond : CondT_n) : InputT_n :=
  let '(v0, u0, u_rel, _) := cond in (v0, u0, u_rel).

Hypothesis constraint_fiber_n :
  forall t, VarRV t \in dsdp_fiber_fn_n (CondRV t).

Hypothesis InputRV_proj_n :
  forall t, InputRV t = dsdp_proj_input_n (CondRV t).

Hypothesis VarRV_uniform_n :
  `p_ VarRV = fdist_uniform card_ffun_msg.

Hypothesis VarRV_indep_inputs_n :
  P |= InputRV _|_ VarRV.

Hypothesis joint_eq_input_n :
  forall (cond : CondT_n) (var : {ffun 'I_n_relay.+1 -> msg}),
    var \in dsdp_fiber_fn_n cond ->
    `Pr[[%VarRV, CondRV] = (var, cond)] =
    `Pr[[%VarRV, InputRV] = (var, dsdp_proj_input_n cond)].

(* The N-party fiber count.  The numeric interval on the last relay weight
   is the protocol-checkable specialization of the coprimality condition
   linear_fiber_nd_card takes, discharged here by lt_minpq_coprime. *)
Lemma dsdp_fiber_card_n (v0 u0 s : msg)
    (u_rel : {ffun 'I_n_relay.+1 -> msg}) :
  (0 < val (u_rel ord_max))%N ->
  (val (u_rel ord_max) < minn p q)%N ->
  #|dsdp_fiber_fn_n (v0, u0, u_rel, s)| = (m ^ n_relay)%N.
Proof.
move=> Hu_pos Hu_lt.
rewrite /dsdp_fiber_fn_n /dsdp_fiber_n.
have Heta : linear_fiber_nd u_rel (s - u0 * v0) =
            @linear_fiber_nd p_minus_2 q_minus_2 n_relay
              (fun i => u_rel i) (s - u0 * v0) by [].
rewrite Heta.
apply: (linear_fiber_nd_card prime_p).
exact: (lt_minpq_coprime prime_p prime_q).
Qed.

(* Per-conditioning-value entropy *)
Lemma dsdp_centropy1_uniform_n (v0 u0 s : msg)
    (u_rel : {ffun 'I_n_relay.+1 -> msg}) :
  (0 < val (u_rel ord_max))%N ->
  (val (u_rel ord_max) < minn p q)%N ->
  `Pr[CondRV = (v0, u0, u_rel, s)] != 0 ->
  `H[ VarRV | CondRV = (v0, u0, u_rel, s) ] = log ((m ^ n_relay)%:R : R).
Proof.
move=> Hu_pos Hu_lt Hcond_pos.
have Hcard := @dsdp_fiber_card_n v0 u0 s u_rel Hu_pos Hu_lt.
(* Build uniform hypothesis using gen_cPr_uniform_fiber *)
have Hsol_unif: forall w : {ffun 'I_n_relay.+1 -> msg},
    w \in dsdp_fiber_fn_n (v0, u0, u_rel, s) ->
    `Pr[VarRV = w | CondRV = (v0, u0, u_rel, s)] =
    #|dsdp_fiber_fn_n (v0, u0, u_rel, s)|%:R^-1.
  move=> w Hin.
  have Hcpr := @gen_cPr_uniform_fiber R T P
                 ({ffun 'I_n_relay.+1 -> msg} : finType) _ card_ffun_msg
                 VarRV InputT_n InputRV CondT_n CondRV
                 dsdp_fiber_fn_n dsdp_proj_input_n
                 constraint_fiber_n InputRV_proj_n
                 VarRV_uniform_n VarRV_indep_inputs_n
                 joint_eq_input_n
                 (v0, u0, u_rel, s) w Hcond_pos Hin.
  by [].
(* Build zero-outside hypothesis *)
have Hnonsol_zero: forall w : {ffun 'I_n_relay.+1 -> msg},
    w \notin dsdp_fiber_fn_n (v0, u0, u_rel, s) ->
    `Pr[VarRV = w | CondRV = (v0, u0, u_rel, s)] = 0.
  move=> w Hnotin.
  set constraint := fun c v => v \in dsdp_fiber_fn_n c.
  exact: (cond_prob_zero_outside_constraint
            (constraint := constraint) constraint_fiber_n Hcond_pos Hnotin).
rewrite (@centropy1_uniform_over_set R T P _ _ VarRV CondRV
           (dsdp_fiber_fn_n (v0, u0, u_rel, s)) (v0, u0, u_rel, s)
           Hcond_pos Hsol_unif Hnonsol_zero); first by rewrite Hcard.
by rewrite Hcard expn_gt0 m_gt0.
Qed.

(* Extract relay coefficient vector from condition tuple *)
Let u_of_cond (c : CondT_n) : {ffun 'I_n_relay.+1 -> msg} :=
  let '(_, _, u_rel, _) := c in u_rel.

End dsdp_entropy_n.



