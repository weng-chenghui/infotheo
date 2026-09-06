From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix.
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

(******************************************************************************)
(* The fiber count of dsdp_fiber_card is m only when Alice's weight on        *)
(* Charlie is invertible modulo m.  A weight sharing a factor with the        *)
(* modulus makes the count depend on the view, leaving some views impossible  *)
(* and others with more candidates than m.                                    *)
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
(* The plaintext ring at the composite modulus m = p * q. *)
Local Notation msg := 'Z_m.

(* The set of relay input pairs (v2, v3) with u2 * v2 + u3 * v3 equal to
   s - u1 * v1.  These are the pairs consistent with one value of Alice's
   plaintext view. *)
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

(* Alice's own input and her three query weights, the part of her view
   that is independent of the relay inputs. *)
Let InputRV : {RV P -> (msg * msg * msg * msg)} := [%V1, U1, U2, U3].

(* The fiber of a conditioning tuple, read as a function of that
   tuple. *)
Let dsdp_fiber_fn (cond : msg * msg * msg * msg * msg) : {set msg * msg} :=
  let '(v1, u1, u2, u3, s) := cond in dsdp_fiber u1 u2 u3 v1 s.

(* The conditioning tuple with the output dropped, leaving Alice's input
   and her three weights. *)
Let dsdp_proj_input (cond : msg * msg * msg * msg * msg) :
    msg * msg * msg * msg :=
  let '(v1, u1, u2, u3, _) := cond in (v1, u1, u2, u3).

(* The relay inputs of a sample always lie in the fiber of that sample's
   conditioning tuple. *)
Let constraint_fiber_dsdp : forall t, VarRV t \in dsdp_fiber_fn (CondRV t).
Proof.
move=> t.
rewrite /dsdp_fiber_fn /dsdp_fiber /linear_fiber_2d inE /=.
apply/eqP.
move: (constraint_holds t).
by rewrite /dsdp_constraint /CondRV /VarRV /= => /eqP.
Qed.

(* Alice's input and weights are the projection of the conditioning tuple
   that drops the output. *)
Let InputRV_proj_dsdp : forall t, InputRV t = dsdp_proj_input (CondRV t).
Proof. by move=> t. Qed.

(* On the fiber, the joint law of the relay inputs with the conditioning
   tuple agrees with their joint law with Alice's input and weights.  The
   output adds nothing there, since the constraint already determines
   it. *)
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

(* The fiber holds m input pairs whenever Alice's weight on Charlie lies
   strictly between 0 and both primes, since such a weight is invertible
   modulo m.  The count is the same m at every view value, which is what
   turns it into a conditional entropy of log m, and the weight is a
   public protocol parameter, so this is a condition on how the protocol
   is configured. *)
Lemma dsdp_fiber_card (u1 u2 u3 v1 s : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|dsdp_fiber u1 u2 u3 v1 s| = m.
Proof.
move=> Hu3_pos Hu3_lt.
rewrite /dsdp_fiber /linear_fiber_2d.
exact: (linear_fiber_2d_card prime_p prime_q).
Qed.

(* An input pair outside the fiber has conditional probability zero given
   the view value. *)
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

(* An input pair inside the fiber has conditional probability 1 / m given
   the view value, so the relay inputs are uniform on the fiber. *)
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

(* At one value of Alice's plaintext view, the relay inputs keep log m
   bits of uncertainty.  The value is the same at every view value of
   positive probability. *)
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

(* The protocol output as a function of the relay inputs and of Alice's
   input and weights: u1 * v1 + u2 * v2 + u3 * v3. *)
Definition dsdp_g (var : msg * msg) (inp : msg * msg * msg * msg) : msg :=
  let '(v2, v3) := var in
  let '(v1, u1, u2, u3) := inp in
  (u1 * v1 + u2 * v2 + u3 * v3)%R.

(* The fiber of the DSDP constraint is the set of relay input pairs that
   dsdp_g sends to the output value s. *)
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

(* Conditioning on Alice's input, her three weights and the output, the
   plaintext part of her view, the relay inputs keep log m bits of
   uncertainty.  The counting axis bounds the plaintexts, while her key,
   her masks and the ciphertexts are bounded on the hopping axis.
   [3-party] *)
Theorem dsdp_centropy_uniform :
  (forall t, (0 < U3 t)%N) ->
  (forall t, (U3 t < minn p q)%N) ->
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
(* S is a function of (V2, V3) and the inputs through dsdp_g, so
   centropy_jcond_determined_fibers quotients the conditional entropy by the
   fibers of that function, and dsdp_fiber_card supplies the m solutions each
   fiber holds. *)
move=> HU3_pos HU3_lt.
have Hm_pos : (0 < m)%N by rewrite muln_gt0 prime_gt0 // prime_gt0.
apply: (@centropy_jcond_determined_fibers R T P
          (msg * msg)%type (msg * msg * msg * msg)%type msg
          VarRV InputRV S dsdp_g S_determined _ m _ Hm_pos).
  move=> [[[v1 u1] u2] u3] s [v2 v3] /= Hcond_pos Hin.
  move/pfwd1_neq0: (Hcond_pos) => [t [Ht _]].
  move: Ht; rewrite inE => /eqP Ht.
  have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
  have Hu3_pos : (0 < u3)%N by rewrite -HU3t; apply: HU3_pos.
  have Hu3_lt : (u3 < minn p q)%N by rewrite -HU3t; apply: HU3_lt.
  rewrite -dsdp_fiber_eq_abstract in Hin *.
  rewrite (dsdp_fiber_card u1 u2 v1 s Hu3_pos Hu3_lt).
  exact: (Pr_dsdp_sol_uniform Hu3_pos Hu3_lt Hcond_pos Hin).
move=> [[[v1 u1] u2] u3] s Hcond_pos.
rewrite -dsdp_fiber_eq_abstract.
move/pfwd1_neq0: (Hcond_pos) => [t [Ht _]].
move: Ht; rewrite inE => /eqP Ht.
have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
apply: dsdp_fiber_card.
  by rewrite -HU3t; apply: HU3_pos.
by rewrite -HU3t; apply: HU3_lt.
Qed.

Section dsdp_var_entropy.

(* The modulus m = p * q exceeds 1, since both primes are at least 2. *)
Let m_gt1 : (1 < m)%N.
Proof.
(* p >= 2, q >= 2, so p * q >= 4 > 1 *)
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

(* card_msg and card_msg_pair are inherited from outer section *)

(* The relay inputs are uniform on a space of size m ^ 2 before any
   conditioning, so their joint entropy is log (m * m).  Against
   dsdp_centropy_uniform, which leaves log m given Alice's plaintext
   view, this says the run reveals exactly half of that joint entropy. *)
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

(* The DSDP linear constraint over a finite commutative ring: for the
   conditioning tuple (v1, u1, u2, u3, s) and the pair (v2, v3),
   s - u1 * v1 = u2 * v2 + u3 * v3. *)
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

(* When u3 is left-regular, an input pair inside the fiber has
   conditional probability 1 / #|R| given the view value, so the relay
   inputs are uniform on the fiber. *)
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
(* N-party entropy analysis                                                   *)
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

(* The set of relay input vectors whose weighted sum equals the target
   s - u0 * v0, the N-party form of dsdp_fiber. *)
Definition dsdp_fiber_n (u_rel : {ffun 'I_n_relay.+1 -> msg}) (target : msg)
    : {set {ffun 'I_n_relay.+1 -> msg}} :=
  @linear_fiber_nd p_minus_2 q_minus_2 n_relay u_rel target.

(* The conditioning tuple of the N-party run: Alice's input, her own
   weight, the vector of relay weights, and the output. *)
Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
(* The conditioning tuple with the output dropped, which the constraint
   already determines from the rest. *)
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

(* The fiber holds m ^ n_relay input vectors whenever the last relay
   weight lies strictly between 0 and both primes.  That numeric interval
   is the protocol-checkable form of the coprimality condition
   linear_fiber_nd_card takes. *)
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

(* At one value of the N-party view, the relay inputs keep
   log (m ^ n_relay) bits of uncertainty. *)
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

(* The vector of relay weights, read off the conditioning tuple. *)
Let u_of_cond (c : CondT_n) : {ffun 'I_n_relay.+1 -> msg} :=
  let '(_, _, u_rel, _) := c in u_rel.

(* The last relay's weight, read off the conditioning tuple.  Held
   strictly between 0 and min(p, q) it is invertible modulo m, and that
   is what leaves the relay inputs uniform given the view. *)
Definition last_relay_weight (c : CondT_n) : msg :=
  (let '(_, _, u_rel, _) := c in u_rel) ord_max.

(* Conditioning on the N-party view, Alice's input and weight, the vector
   of relay weights and the output, the relay inputs keep
   log (m ^ n_relay) bits of uncertainty, one coordinate less than their
   joint entropy whatever the number of relays.  The 3-party
   dsdp_centropy_uniform is this statement at n_relay = 1.  [N-party] *)
Theorem dsdp_centropy_uniform_n :
  (forall t, (0 < val (last_relay_weight (CondRV t)))%N) ->
  (forall t, (val (last_relay_weight (CondRV t)) < minn p q)%N) ->
  `H(VarRV | CondRV) = log ((m ^ n_relay)%:R : R).
Proof.
move=> HU_pos HU_lt.
rewrite centropy_RVE' /=.
transitivity (\sum_(a : CondT_n)
               `Pr[ CondRV = a ] * log ((m ^ n_relay)%:R : R)).
  apply: eq_bigr => [] [[[v0 u0] u_rel] s] _.
  have [->|Hcond_pos] := eqVneq (`Pr[CondRV = (v0, u0, u_rel, s)]) 0.
    by rewrite !mul0r.
  have Hu_pos : (0 < val (u_rel ord_max))%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    by have := HU_pos t; rewrite Ht.
  have Hu_lt : (val (u_rel ord_max) < minn p q)%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    by have := HU_lt t; rewrite Ht.
  by rewrite (dsdp_centropy1_uniform_n Hu_pos Hu_lt Hcond_pos).
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.

End dsdp_entropy_n.



