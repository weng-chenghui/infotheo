From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption residuosity_game.
Require Import idealized_ahe paillier_fdist_instance.
Require Import negligible epshop epshop_family.
Require Import indcpa_game idealized_indcpa_scheme.
Require Import paillier_indcpa_scheme benaloh_indcpa_scheme.
Require Import dsdp_instance.
Require Import dsdp_alice_hop_secrecy dsdp_alice_trace_link.
Require Import dsdp_alice_main.

(**md**************************************************************************)
(* # Concrete readings of DSDP corrupted-Alice secrecy                       *)
(*                                                                            *)
(* The abstract Alice bounds are instantiated at the idealized, Paillier and *)
(* Benaloh IND-CPA schemes.                                                   *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope proc_scope.
Local Open Scope sproc_scope.

(* The vacuity question the abstract bounds leave open, answered on the
   idealized scheme of idealized_ahe.v: a sequence of instances that
   discharges every hypothesis of the guessing headline at once, where the
   assumed advantage is zero at every k and the whole content of the bound is
   its information-theoretic term. *)
Section idealized.
Context {R : realType}.


(* The witness instance at k, over a plaintext space of cardinality
   (k+2)^(k+2).  Its guessing probability is 1/#|plain| rather than 0, so the
   bound has content. *)
Definition idealized_instance (k : nat) : dsdp_instance := {|
  inst_scheme       := idealized_indcpa_scheme 'Z_((k.+2) ^ k.+2) ;
  inst_v1 := 0 ; inst_u1 := 0 ; inst_u2 := 0 ; inst_u3 := 1 ;
  inst_u3_unit      := GRing.unitr1 _ ;
  inst_dk_a := 0 ; inst_dk_b := 0 ; inst_dk_c := 0 ;
  inst_rb2 := ord0 ; inst_rc2 := ord0 |}.

(* The witness plaintext space at k has cardinality (k+2)^(k+2). *)
Let card_plain_idealized (k : nat) :
  #|plain (scheme_AHE (idealized_instance k))| = ((k.+2) ^ k.+2)%N.
Proof. by rewrite card_ord Zp_cast // -{1}(expn0 k.+2) ltn_exp2l. Qed.

(* The unconditional term of every bound along the witness sequence.  Its
   plaintext spaces grow as (k+2)^(k+2), so the term falls below every inverse
   polynomial. *)
Let idealized_size_negligible :
  negligible_fun (fun k =>
    (#|plain (scheme_AHE (idealized_instance k))|%:R : R)^-1).
Proof.
apply: negligible_fun_le negligible_fun_inv_expnn => k.
by rewrite card_plain_idealized.
Qed.

(* The witness sequence: the idealized instances above, under the
   cipher-constant assumption of indcpa_game.v at each k. *)
Definition idealized_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := idealized_instance ;
  sequence_assumption := fun k =>
    cipher_constant_assumption (idealized_instance k) |}.

(* The two negligibility facts about the witness sequence, discharged rather
   than assumed.  Its assumed advantage is zero at every k, leaving only the
   1/#|plain| term. *)
Definition idealized_asymptotic :
    dsdp_asymptotic idealized_instance_sequence :=
  @Build_dsdp_asymptotic R idealized_instance_sequence
    idealized_size_negligible negligible_fun_cst0.

(* The constant predictor's distinguisher reads only the state slot.  Its
   Bob-key reduction ignores the challenge ciphertext, so the cipher-constant
   class admits it. *)
Lemma idealized_bob_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (idealized_instance k))
    (bob_trace_adversary (R:=R) (I:=idealized_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of idealized_bob_cipher_constant. *)
Lemma idealized_charlie_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (idealized_instance k))
    (charlie_trace_adversary (R:=R) (I:=idealized_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* The hypotheses of alice_trace_guess_V2_negligible hold together at least
   once, on the idealized sequence.  The constant predictor's two reductions
   are in the cipher-constant class at every k. *)
Corollary alice_trace_guess_V2_idealized_negligible :
  negligible_fun (fun k =>
    alice_trace_guess_V2_pr (R:=R) (I:=idealized_instance k) (fun _ => 0)).
Proof.
apply: (alice_trace_guess_V2_negligible (Q := idealized_instance_sequence)
          (predict := fun k => fun _ => 0) _ _ idealized_asymptotic).
- exact: idealized_bob_cipher_constant.
- exact: idealized_charlie_cipher_constant.
Qed.

End idealized.

(* The Paillier reading of the corrupted-Alice bounds: a sequence of moduli
   p k q k, the DSDP instance the Paillier IND-CPA scheme of
   paillier_indcpa_scheme.v carries at each of them, and the decisional
   composite residuosity record the computational term of every bound below
   is stated in.  Everything DSDP, the four weights, the three keys and the
   two hop coins, is declared here; the scheme file carries the packaging,
   the coin type and coin map, and the derived assumption alone.  At this
   scheme both terms of the abstract bound have number-theoretic values:
   1/(p k * q k) for the plaintext count, and twice the residuosity epsilon
   for the assumed advantage. *)
Section paillier.
Context {R : realType}.
Variables p q : nat -> nat.
Hypothesis p_gt1 : forall k, (1 < p k)%N.
Hypothesis q_gt1 : forall k, (1 < q k)%N.

(* The Paillier IND-CPA instance of paillier_indcpa_scheme.v at the k-th
   modulus, pinned once under the name that file exports it by. *)
Local Notation AHE k := (Paillier_AHEnc (pq_gt1 (p_gt1 k) (q_gt1 k))).

Variables (v1 u1 u2 u3 : forall k, plain (AHE k)).

(* Charlie's weight is invertible.  This is what makes the DSDP solution
   fiber a bijective image of the plaintext space, and so what turns the
   leaked output into the 1/(p k * q k) term of the bounds below rather than
   into a determination of Bob's input. *)
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.

Variables (dk_a dk_b dk_c : forall k, priv_key (AHE k)).
Variables (rb2 rc2 : forall k, renc_paillier (p k) (q k)).

(* The plaintext space at k has cardinality p k * q k, the form the
   composite-modulus DSDP bounds consume. *)
Let card_plain_pq k : #|plain (AHE k)| = (p k * q k)%N.
Proof. exact: card_plain_paillier_pq. Qed.

(* The inverse plaintext cardinality at the composite modulus. *)
Let inv_pq_cardE k : ((p k * q k)%N%:R : R)^-1 = (#|plain (AHE k)|%:R : R)^-1.
Proof. by rewrite card_plain_pq. Qed.

(* The DSDP instance at k on the Paillier IND-CPA scheme, with the weights,
   keys and coins supplied as sequences.  Everything number-theoretic about
   the moduli beyond 1 < p, q stays assumed. *)
Definition paillier_instance (k : nat) : dsdp_instance := {|
  inst_scheme       := paillier_indcpa_scheme (p_gt1 k) (q_gt1 k) ;
  inst_v1 := v1 k ; inst_u1 := u1 k ; inst_u2 := u2 k ;
  inst_u3 := u3 k ; inst_u3_unit := u3_unit k ;
  inst_dk_a := dk_a k ; inst_dk_b := dk_b k ; inst_dk_c := dk_c k ;
  inst_rb2 := rb2 k ; inst_rc2 := rc2 k |}.

(* A decisional composite residuosity record at each modulus p k q k, the
   only computational premise the Paillier bounds are read at.  The IND-CPA
   assumption at k is derived from it by paillier_indcpa_assumption, so those
   bounds are stated in residuosity epsilons rather than in an advantage left
   free. *)
Variable dcr : forall k, dcr_assumption (R:=R) (p k) (q k).

(* The Paillier instance sequence: the instances above, with the IND-CPA
   assumption derived at each k from dcr k.  It is the sequence
   alice_trace_guess_V2_negligible is applied at below. *)
Definition paillier_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := paillier_instance ;
  sequence_assumption := fun k =>
    paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (dcr k) |}.

(* The assumption at k is the one paillier_indcpa_scheme.v derives from dcr k.
   The equation holds by unfolding, so the identification is a conversion. *)
Lemma paillier_assumption_at_dcrE k :
  sequence_assumption paillier_instance_sequence k
  = paillier_indcpa_assumption (p_gt1 k) (q_gt1 k) (dcr k).
Proof. by []. Qed.

(* The epsilon at k is twice the residuosity epsilon, one call per hop.  It
   restates a Paillier bound in decisional composite residuosity epsilons. *)
Lemma paillier_epsilon_at_dcrE k :
  indcpa_assumption_epsilon (sequence_assumption paillier_instance_sequence k)
  = 2 * dcr_epsilon (dcr k).
Proof. by []. Qed.

(* A predictor of Bob's input reading Alice's executed trace, one at each
   security parameter, with the two class premises every trace bound below is
   conditional on: the class the residuosity record induces at k admits the
   two reduction adversaries the k-th predictor induces.  The restriction
   lands on those two adversaries and never on the predictor itself, which is
   what leaves the trace-decrypting predictor outside the bounds rather than
   inside them. *)
Variable predict : forall k, predictor (paillier_instance k)
    (alice_traceT (paillier_instance k)).
Arguments predict : clear implicits.

Hypothesis bob_admissible : forall k,
  indcpa_admissible (sequence_assumption paillier_instance_sequence k)
    (bob_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (predict k))).

Hypothesis charlie_admissible : forall k,
  indcpa_admissible (sequence_assumption paillier_instance_sequence k)
    (charlie_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (predict k))).

(* The trace guessing bound at k: 1/#|plain| plus 4 residuosity epsilons, two
   calls per key.  The first summand is unconditional, the second conditional
   on the residuosity record. *)
Corollary paillier_trace_guess_V2_admissible_le k :
  alice_trace_guess_V2_pr (I:=paillier_instance k) (predict k)
  <= (#|plain (AHE k)|%:R : R)^-1 + 4 * dcr_epsilon (dcr k).
Proof.
have := alice_trace_guess_V2_admissible_le (I:=paillier_instance k)
          (bob_admissible k) (charlie_admissible k).
by rewrite paillier_epsilon_at_dcrE mulrA -(natrM R 2 2).
Qed.

(* The same bound with its unconditional summand written 1/(p k * q k), the
   plaintext count at the Paillier modulus. *)
Corollary paillier_trace_guess_V2_admissible_pq_le k :
  alice_trace_guess_V2_pr (I:=paillier_instance k) (predict k)
  <= ((p k * q k)%N%:R : R)^-1 + 4 * dcr_epsilon (dcr k).
Proof.
rewrite inv_pq_cardE; exact: paillier_trace_guess_V2_admissible_le.
Qed.

(* The constant predictor's Bob-key reduction is in the class the residuosity
   record induces.  Its epsilon is zero, so the class premises of the bounds
   above are satisfiable. *)
Lemma paillier_bob_decide_constant_admissible k :
  paillier_dcr_admissible
    (decide_constant_assumption (R:=R) 'Z_((p k * q k) * (p k * q k))
       (p k * q k) (card_renc_paillier (p k) (q k)))
    (bob_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: paillier_dcr_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of paillier_bob_decide_constant_admissible, so
   that both class premises hold at the same record and the same predictor. *)
Lemma paillier_charlie_decide_constant_admissible k :
  paillier_dcr_admissible
    (decide_constant_assumption (R:=R) 'Z_((p k * q k) * (p k * q k))
       (p k * q k) (card_renc_paillier (p k) (q k)))
    (charlie_trace_adversary (I:=paillier_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: paillier_dcr_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* Supplies the unconditional summand of the bound
   Pr_k <= 1/(p k * q k) + 2 * eps k, through f_size_paillier_negligible,
   which reads the plaintext cardinality at k as the modulus p k * q k.

   The summand 1/(p k * q k) is the guessing probability the leaked
   output Sout concedes: at Paillier #|plain| is the modulus p k * q k,
   and Sout confines the uniform V2 to a fiber of that size.  Negligible
   is the acceptance criterion of the asymptotic reading: the concrete
   analysis already treats this residue as the acceptable leak, and this
   hypothesis states that acceptability uniformly in k, the residue
   falling below every inverse polynomial. *)
Hypothesis f_pq_negligible : negligible_fun (f_pq (R:=R) p q).

(* The residuosity advantage the assumption sequence assumes is negligible:
   the asymptotic form of decisional composite residuosity along the moduli
   p k q k, and the only computational hypothesis the sequence makes. *)
Hypothesis f_dcr_negligible : negligible_fun (f_dcr_paillier dcr).

(* The two negligibility facts about the Paillier sequence.  The unconditional
   one is read at the modulus, the other from the residuosity hypothesis. *)
Definition paillier_asymptotic :
    dsdp_asymptotic paillier_instance_sequence :=
  @Build_dsdp_asymptotic R paillier_instance_sequence
    (f_size_paillier_negligible p_gt1 q_gt1 f_pq_negligible)
    (f_adv_paillier_negligible p_gt1 q_gt1 f_dcr_negligible).

(* Past some security parameter the derived class admits the decrypting
   predictor's Bob-key reduction adversary at no k.  The two negligibility
   facts above exclude the predictor whose guessing probability is 1. *)
Corollary paillier_decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (sequence_assumption paillier_instance_sequence k)
      (bob_trace_adversary (I:=paillier_instance k)
         (distinguisher_of_predictor
            (bob_decrypt_predictor (I:=paillier_instance k))))
    = false.
Proof.
exact: (decrypt_reduction_admissible_eventuallyF paillier_asymptotic).
Qed.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=paillier_instance_sequence) predict).

(* The k-th predictor's guessing probability at the k-th Paillier instance is
   negligible in k.  Its whole computational content is decisional composite
   residuosity along the moduli p k q k. *)
Corollary paillier_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
(* At each k the two class premises yield the bound of
   alice_trace_guess_V2_admissible_le, Pr_k <= 1/(p k * q k) + 2 * eps k,
   with eps k the advantage dcr k assumes.  The two fields of
   paillier_asymptotic make f_size and f_adv negligible, f_size through the
   scheme-side reading of modulus growth as plaintext growth.  Those two are
   the loss terms the three labels of the program carry, so the terminal over
   the security parameter reads the bound off the label list and transfers
   negligibility to f_guess_V2. *)
exact: (alice_trace_guess_V2_negligible (Q := paillier_instance_sequence)
          bob_admissible charlie_admissible paillier_asymptotic).
Qed.

End paillier.

(* The Benaloh reading of the corrupted-Alice bounds: a sequence of moduli
   n k with block sizes r k, the DSDP instance the Benaloh IND-CPA scheme of
   benaloh_indcpa_scheme.v carries at each of them, and the r-th residuosity
   record the computational term of every bound below is stated in.  The
   plaintext count here is the block size r k and not the modulus n k, which
   sizes the ciphertext space, so the information-theoretic term reads 1/r k;
   the assumed advantage is twice the residuosity epsilon. *)
Section benaloh.
Context {R : realType}.
Variables n r : nat -> nat.
Hypothesis n_gt1 : forall k, (1 < n k)%N.
Hypothesis r_gt1 : forall k, (1 < r k)%N.

(* The Benaloh IND-CPA scheme at the k-th modulus and block size.  It is
   pinned once, under the name benaloh_indcpa_scheme.v exports it by. *)
Local Notation AHE k := (Benaloh_AHEnc (n k) (r_gt1 k)).

Variables (v1 u1 u2 u3 : forall k, plain (AHE k)).

(* Charlie's weight is invertible in Z/rZ.  This is what makes the DSDP
   solution fiber a bijective image of the plaintext space, and so what turns
   the leaked output into the 1/r k term of the bounds below rather than into
   a determination of Bob's input. *)
Hypothesis u3_unit : forall k, u3 k \is a GRing.unit.

Variables (dk_a dk_b dk_c : forall k, priv_key (AHE k)).
Variables (rb2 rc2 : forall k, renc_benaloh (n k)).

(* The plaintext space at k is Z/(r k)Z, so its cardinality is the block size
   r k.  The unconditional term below is read off r k, where n k sizes the
   ciphertext space. *)
Let card_plain_r k : #|plain (AHE k)| = r k.
Proof. by rewrite card_ord (Zp_cast (r_gt1 k)). Qed.

(* The inverse plaintext cardinality at the Benaloh block size. *)
Let inv_r_cardE k : ((r k)%:R : R)^-1 = (#|plain (AHE k)|%:R : R)^-1.
Proof. by rewrite card_plain_r. Qed.

(* The DSDP instance at k on the Benaloh IND-CPA scheme, with the weights,
   keys and coins supplied as sequences.  Everything number-theoretic about
   the modulus and the block size beyond 1 < n, r stays assumed. *)
Definition benaloh_instance (k : nat) : dsdp_instance := {|
  inst_scheme       := benaloh_indcpa_scheme (n k) (r_gt1 k) ;
  inst_v1 := v1 k ; inst_u1 := u1 k ; inst_u2 := u2 k ;
  inst_u3 := u3 k ; inst_u3_unit := u3_unit k ;
  inst_dk_a := dk_a k ; inst_dk_b := dk_b k ; inst_dk_c := dk_c k ;
  inst_rb2 := rb2 k ; inst_rc2 := rc2 k |}.

(* An r-th residuosity record at each modulus n k and exponent r k, the only
   computational premise the Benaloh bounds are read at.  The IND-CPA
   assumption at k is derived from it by benaloh_indcpa_assumption, so those
   bounds are stated in residuosity epsilons rather than in an advantage left
   free. *)
Variable residuosity :
  forall k, benaloh_residuosity_assumption (R:=R) (n k) (r k).

(* The Benaloh instance sequence: the instances above, with the IND-CPA
   assumption derived at each k from residuosity k.  It is the sequence
   alice_trace_guess_V2_negligible is applied at below. *)
Definition benaloh_instance_sequence : dsdp_instance_sequence R := {|
  sequence_instance := benaloh_instance ;
  sequence_assumption := fun k =>
    benaloh_indcpa_assumption (r_gt1 k) (residuosity k) |}.

(* The assumption at k is the one benaloh_indcpa_scheme.v derives from
   residuosity k.  The equation holds by unfolding, so the identification is a
   conversion. *)
Lemma benaloh_assumption_at_residuosityE k :
  sequence_assumption benaloh_instance_sequence k
  = benaloh_indcpa_assumption (r_gt1 k) (residuosity k).
Proof. by []. Qed.

(* The epsilon at k is twice the residuosity epsilon, one call per hop.  It
   restates a Benaloh bound in r-th residuosity epsilons. *)
Lemma benaloh_epsilon_at_residuosityE k :
  indcpa_assumption_epsilon (sequence_assumption benaloh_instance_sequence k)
  = 2 * benaloh_residuosity_epsilon (residuosity k).
Proof. by []. Qed.

(* A predictor of Bob's input reading Alice's executed trace, one at each
   security parameter, with the two class premises every trace bound below is
   conditional on: the class the residuosity record induces at k admits the
   two reduction adversaries the k-th predictor induces.  The restriction
   lands on those two adversaries and never on the predictor itself, which is
   what leaves the trace-decrypting predictor outside the bounds rather than
   inside them. *)
Variable predict : forall k, predictor (benaloh_instance k)
    (alice_traceT (benaloh_instance k)).
Arguments predict : clear implicits.

Hypothesis bob_admissible : forall k,
  indcpa_admissible (sequence_assumption benaloh_instance_sequence k)
    (bob_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (predict k))).

Hypothesis charlie_admissible : forall k,
  indcpa_admissible (sequence_assumption benaloh_instance_sequence k)
    (charlie_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (predict k))).

(* The trace guessing bound at k: 1/#|plain| plus 4 residuosity epsilons, two
   calls per key.  The first summand is unconditional, the second conditional
   on the residuosity record. *)
Corollary benaloh_trace_guess_V2_admissible_le k :
  alice_trace_guess_V2_pr (I:=benaloh_instance k) (predict k)
  <= (#|plain (AHE k)|%:R : R)^-1
     + 4 * benaloh_residuosity_epsilon (residuosity k).
Proof.
have := alice_trace_guess_V2_admissible_le (I:=benaloh_instance k)
          (bob_admissible k) (charlie_admissible k).
by rewrite benaloh_epsilon_at_residuosityE mulrA -(natrM R 2 2).
Qed.

(* The same bound at a block size written as a product p * q.  The hypothesis
   r k = p * q is the only link between the two readings. *)
Corollary benaloh_trace_guess_V2_admissible_pq_le k (p q : nat)
    (r_pq : r k = (p * q)%N) :
  alice_trace_guess_V2_pr (I:=benaloh_instance k) (predict k)
  <= ((p * q)%N%:R : R)^-1
     + 4 * benaloh_residuosity_epsilon (residuosity k).
Proof.
rewrite -r_pq inv_r_cardE; exact: benaloh_trace_guess_V2_admissible_le.
Qed.

(* The constant predictor's Bob-key reduction is in the class the residuosity
   record induces.  Its epsilon is zero, so the class premises of the bounds
   above are satisfiable. *)
Lemma benaloh_bob_decide_constant_admissible k :
  benaloh_residuosity_admissible
    (decide_constant_assumption (R:=R) 'Z_(n k) (r k)
       (card_renc_benaloh (n k)))
    (bob_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: benaloh_residuosity_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of benaloh_bob_decide_constant_admissible, so
   that both class premises hold at the same record and the same predictor. *)
Lemma benaloh_charlie_decide_constant_admissible k :
  benaloh_residuosity_admissible
    (decide_constant_assumption (R:=R) 'Z_(n k) (r k)
       (card_renc_benaloh (n k)))
    (charlie_trace_adversary (I:=benaloh_instance k)
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply: benaloh_residuosity_admissible_cipher_constant.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* Supplies the unconditional summand of the bound
   Pr_k <= 1/(r k) + 2 * eps k, through f_size_benaloh_negligible, which
   reads the plaintext cardinality at k as the block size r k.

   The summand 1/(r k) is the guessing probability the leaked output
   Sout concedes: at Benaloh #|plain| is the block size r k, and Sout
   confines the uniform V2 to a fiber of that size.  Negligible is the
   acceptance criterion of the asymptotic reading: the concrete analysis
   already treats this residue as the acceptable leak, and this
   hypothesis states that acceptability uniformly in k, the residue
   falling below every inverse polynomial. *)
Hypothesis f_r_negligible : negligible_fun (f_r (R:=R) r).

(* The residuosity advantage the assumption sequence assumes is negligible:
   the asymptotic form of r-th residuosity along the moduli n k, and the only
   computational hypothesis the sequence makes. *)
Hypothesis f_residuosity_negligible :
  negligible_fun (f_residuosity_benaloh residuosity).

(* The two negligibility facts about the Benaloh sequence.  The unconditional
   one is read at the block size, the other from the residuosity
   hypothesis. *)
Definition benaloh_asymptotic :
    dsdp_asymptotic benaloh_instance_sequence :=
  @Build_dsdp_asymptotic R benaloh_instance_sequence
    (f_size_benaloh_negligible n r_gt1 f_r_negligible)
    (f_adv_benaloh_negligible r_gt1 f_residuosity_negligible).

(* Past some security parameter the derived class admits the decrypting
   predictor's Bob-key reduction adversary at no k.  The two negligibility
   facts above exclude the predictor whose guessing probability is 1. *)
Corollary benaloh_decrypt_reduction_admissible_eventuallyF :
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (sequence_assumption benaloh_instance_sequence k)
      (bob_trace_adversary (I:=benaloh_instance k)
         (distinguisher_of_predictor
            (bob_decrypt_predictor (I:=benaloh_instance k))))
    = false.
Proof.
exact: (decrypt_reduction_admissible_eventuallyF benaloh_asymptotic).
Qed.

Local Notation f_guess_V2 :=
  (f_guess_V2 (R:=R) (Q:=benaloh_instance_sequence) predict).

(* The k-th predictor's guessing probability at the k-th Benaloh instance is
   negligible in k.  Its whole computational content is r-th residuosity along
   the moduli n k. *)
Corollary benaloh_trace_guess_V2_negligible : negligible_fun f_guess_V2.
Proof.
(* At each k the two class premises yield the bound of
   alice_trace_guess_V2_admissible_le, Pr_k <= 1/(r k) + 2 * eps k, with
   eps k the advantage residuosity k assumes.  The two fields of
   benaloh_asymptotic make f_size and f_adv negligible, f_size through the
   scheme-side reading of block-size growth as plaintext growth.  Those two
   are the loss terms the three labels of the program carry, so the terminal
   over the security parameter reads the bound off the label list and transfers
   negligibility to f_guess_V2. *)
exact: (alice_trace_guess_V2_negligible (Q := benaloh_instance_sequence)
          bob_admissible charlie_admissible benaloh_asymptotic).
Qed.

End benaloh.
