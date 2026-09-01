From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import zmodp ring boolp reals.
Require Import realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist_extra proba.
Require Import homomorphic_encryption.
Require Import idealized_ahe.
Require Import indcpa_game dsdp_alice_fdist_secrecy dsdp_alice_trace_link.

(**md**************************************************************************)
(* # A security-parameter-indexed family of DSDP executions                   *)
(*                                                                            *)
(* Every corrupted-Alice bound of dsdp_alice_trace_link.v is stated at one    *)
(* fixed instance: one AHEncType, one coin type, three private keys, four     *)
(* weights, one real epsilon.  negligible_fun of indcpa_game.v speaks about   *)
(* families indexed by a security parameter.  This file supplies the object   *)
(* that joins them, a record holding exactly the section variables of that    *)
(* development, and reads the concrete class-conditional guessing bound off   *)
(* at every k of a family of such records.                                    *)
(*                                                                            *)
(* The class restriction lands on the two reduction adversaries a predictor   *)
(* induces, never on the predictor itself.  That is what separates the        *)
(* headline from the predictor that decrypts Bob's ciphertext off the trace,  *)
(* whose guessing probability is 1: the companion corollary shows that the    *)
(* same two negligibility hypotheses eventually reject that predictor's       *)
(* reduction adversary.  The witness section answers the vacuity question     *)
(* from the other side, discharging every hypothesis of the headline at once  *)
(* on the identity scheme of idealized_ahe.v.                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*              dsdp_instance == one instance of the family, the section      *)
(*                               variables of the corrupted-Alice trace       *)
(*                               development packed as one record             *)
(*          expnn_gt_monomial == (k+2)^(k+2) exceeds every monomial k^c past  *)
(*                               c                                            *)
(*   negligible_fun_inv_expnn == the inverse of (k+2)^(k+2) is negligible     *)
(* negligible_fun_inv_ge_expnn == a sequence dominating (k+2)^(k+2) has a     *)
(*                               negligible inverse                           *)
(*        negligible_fun_cst0 == the zero family is negligible                *)
(*     bob_trace_adversary_at == the Bob-key reduction adversary at k         *)
(* charlie_trace_adversary_at == the Charlie-key reduction adversary at k     *)
(* alice_trace_guess_V2_pr_at == the trace guessing probability at k          *)
(* alice_trace_guess_V2_admissible_negligible ==                              *)
(*                               the trace guessing family is negligible      *)
(*                               under the two class premises and the two     *)
(*                               negligibility hypotheses                     *)
(* decrypt_reduction_admissible_eventuallyF ==                                *)
(*                               those same hypotheses eventually reject the  *)
(*                               decrypting predictor's reduction adversary   *)
(*             card_renc_ord1 == the one-element coin space, in successor     *)
(*                               form                                         *)
(*           trivial_instance == the identity-scheme witness family           *)
(* trivial_bob_cipher_constant == the witness Bob reduction ignores the       *)
(*                               challenge ciphertext                         *)
(* trivial_charlie_cipher_constant ==                                         *)
(*                               its Charlie counterpart                      *)
(* trivial_instance_guess_V2_negligible ==                                    *)
(*                               the witness discharges every hypothesis of   *)
(*                               the headline                                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

(* One instance of a security-parameter-indexed family of DSDP executions: the
   scheme, its coin index type with a pinned nonemptiness proof, the coin
   map, the four weights with Charlie's weight invertible, the three private
   keys, and the two hop coins.  These are exactly the section variables of
   the corrupted-Alice trace development (dsdp_alice_trace_link.v), so every
   concrete trace bound applies at each k unchanged.  The real field
   stays outside: a family lives over one R, which only the assumption
   record and the probabilities mention. *)
Record dsdp_instance := {
  inst_AHE          : AHEncType ;
  inst_renc         : finType ;
  inst_card_renc    : #|inst_renc| = #|inst_renc|.-1.+1 ;
  inst_rand_of_renc : inst_renc -> rand inst_AHE ;
  inst_v1           : plain inst_AHE ;
  inst_u1           : plain inst_AHE ;
  inst_u2           : plain inst_AHE ;
  inst_u3           : plain inst_AHE ;
  inst_u3_unit      : inst_u3 \is a GRing.unit ;
  inst_dk_a         : priv_key inst_AHE ;
  inst_dk_b         : priv_key inst_AHE ;
  inst_dk_c         : priv_key inst_AHE ;
  inst_rb2          : inst_renc ;
  inst_rc2          : inst_renc }.

(* Superpolynomial growth of (k+2)^(k+2): past c the sequence dominates
   every monomial k^c, by base and exponent monotonicity alone. *)
Lemma expnn_gt_monomial (c n : nat) : (c < n)%N -> (n ^ c < n.+2 ^ n.+2)%N.
Proof.
move=> Hcn; apply: leq_ltn_trans (_ : (n.+2) ^ c < _)%N; last first.
  by rewrite ltn_exp2l //; exact: (leq_trans Hcn (leqW (leqnSn n))).
move: Hcn; case: c => [_|c _]; first by rewrite !expn0.
by rewrite leq_exp2r //; exact: (leqW (leqnSn n)).
Qed.

Section negligible_helpers.
Context {R : realType}.

(* The inverse of (k+2)^(k+2) falls below every inverse polynomial: the
   growth rate the witness family's plaintext spaces follow. *)
Lemma negligible_fun_inv_expnn :
  negligible_fun (fun k : nat => (((k.+2) ^ k.+2)%N%:R : R)^-1).
Proof.
move=> c; exists c => n Hn.
have Hn0 : (0 < n)%N by apply: leq_ltn_trans Hn.
rewrite -natrX ltf_pV2 ?ltr_nat ?expnn_gt_monomial //.
  by rewrite posrE ltr0n expn_gt0.
by rewrite posrE ltr0n expn_gt0 Hn0.
Qed.

(* A sequence dominating (k+2)^(k+2) has negligible inverse.  The checkable
   modulus-growth condition of the scheme families: a Paillier or Benaloh
   family whose modulus (block size) grows at least this fast satisfies the
   information-theoretic negligibility hypothesis. *)
Lemma negligible_fun_inv_ge_expnn (f : nat -> nat) :
  (forall k, ((k.+2) ^ k.+2 <= f k)%N) ->
  negligible_fun (fun k => ((f k)%:R : R)^-1).
Proof.
move=> Hf; apply: negligible_fun_le negligible_fun_inv_expnn => k.
rewrite lef_pV2 ?ler_nat //.
  by rewrite posrE ltr0n (leq_trans _ (Hf k)) // expn_gt0.
by rewrite posrE ltr0n expn_gt0.
Qed.

(* The zero family is negligible: what the cipher-constant assumption family
   contributes to the witness. *)
Lemma negligible_fun_cst0 : negligible_fun (fun _ : nat => 0 : R).
Proof. by move=> c; exists 0 => n Hn; rewrite invr_gt0 exprn_gt0 // ltr0n. Qed.

End negligible_helpers.

Section dsdp_instance_family.
Context {R : realType}.
Variable I : nat -> dsdp_instance.
Variable A : forall k, indcpa_epsilon_assumption (R:=R)
                         (inst_card_renc (I k)) (@inst_rand_of_renc (I k)).
Variable predict : forall k,
    predictor (inst_AHE (I k)) (dsdp_traceT (inst_AHE (I k))).
Arguments predict : clear implicits.

(* The Bob-key reduction adversary at k: the concrete constant applied
   at the record fields of I k.  Family plumbing; the mathematics is in the
   constant it applies. *)
Definition bob_trace_adversary_at k
    (D : distinguisher (trace_jointT (inst_AHE (I k)))) :=
  bob_trace_adversary (R:=R) (inst_card_renc (I k))
    (@inst_rand_of_renc (I k))
    (inst_v1 (I k)) (inst_u1 (I k)) (inst_u2 (I k)) (inst_u3 (I k))
    (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
    (inst_rc2 (I k)) D.

(* The Charlie-key counterpart of bob_trace_adversary_at. *)
Definition charlie_trace_adversary_at k
    (D : distinguisher (trace_jointT (inst_AHE (I k)))) :=
  charlie_trace_adversary (R:=R) (inst_card_renc (I k))
    (@inst_rand_of_renc (I k))
    (inst_v1 (I k)) (inst_u1 (I k)) (inst_u2 (I k)) (inst_u3 (I k))
    (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
    (inst_rc2 (I k)) D.

(* The probability that a predictor reading Alice's executed trace at k
   returns Bob's input.  The two hop coins enter here and not in the two
   reduction adversaries, which fix Bob's coin by the challenge. *)
Definition alice_trace_guess_V2_pr_at k
    (p : predictor (inst_AHE (I k)) (dsdp_traceT (inst_AHE (I k)))) : R :=
  alice_trace_guess_V2_pr (inst_card_renc (I k)) (@inst_rand_of_renc (I k))
    (inst_v1 (I k)) (inst_u1 (I k)) (inst_u2 (I k)) (inst_u3 (I k))
    (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
    (inst_rb2 (I k)) (inst_rc2 (I k)) p.

(* A family of predictors reading Alice's executed traces along a family of
   DSDP instances matches Bob's input with negligible probability, provided
   the inverse plaintext cardinalities and the assumed advantages are
   negligible families and the two reduction adversaries at each k are
   admitted by the class at that k.  The class restriction lands on the
   reduction adversaries, not on the predictor, and it is what separates
   this statement from the decrypting counterexample: decrypt_guess_prE
   puts the guessing probability at 1 for the predictor that decrypts
   Bob's ciphertext off the trace, and
   decrypt_reduction_admissible_eventuallyF below shows these same
   negligibility hypotheses eventually force that predictor's reduction
   adversary out of the class.  Every currency is hypothesis-conditional,
   priced at each k as in the concrete bound. *)
Theorem alice_trace_guess_V2_admissible_negligible :
  (forall k, indcpa_admissible (A k)
     (bob_trace_adversary_at (distinguisher_of_predictor (predict k)))) ->
  (forall k, indcpa_admissible (A k)
     (charlie_trace_adversary_at (distinguisher_of_predictor (predict k)))) ->
  negligible_fun (fun k => (#|plain (inst_AHE (I k))|%:R : R)^-1) ->
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)) ->
  negligible_fun (fun k => alice_trace_guess_V2_pr_at (predict k)).
Proof.
move=> HB HC Hinv Heps.
apply: negligible_fun_le (negligible_fun_predictor_bound Hinv Heps) => k.
exact: (alice_trace_guess_V2_admissible_le
          (inst_u3_unit (I k)) (inst_rb2 (I k)) (HB k) (HC k)).
Qed.

(* Under the same two negligibility hypotheses, the decrypting predictor's
   Bob-side reduction adversary is eventually outside the class: the
   parallel-track counterexample is excluded by the hypotheses themselves,
   not by the information-theoretic term. *)
Corollary decrypt_reduction_admissible_eventuallyF :
  negligible_fun (fun k => (#|plain (inst_AHE (I k))|%:R : R)^-1) ->
  negligible_fun (fun k => indcpa_assumption_epsilon (A k)) ->
  exists K, forall k, (K < k)%N ->
    indcpa_admissible (A k)
      (bob_trace_adversary_at (distinguisher_of_predictor
         (bob_trace_decrypt_predictor (@inst_rand_of_renc (I k))
            (inst_dk_a (I k)) (inst_dk_b (I k)) (inst_dk_c (I k))
            (inst_rc2 (I k))))) = false.
Proof.
move=> Hinv Heps.
have [N1 HN1] := Hinv 1%N; have [N2 HN2] := Heps 1%N.
exists (maxn (maxn N1 N2) 1) => k.
rewrite !gtn_max => /andP[/andP[Hk1 Hk2] Hk3].
have Hk0 : (0 < k%:R :> R) by rewrite ltr0n ltnW.
move: (HN1 k Hk1) (HN2 k Hk2); rewrite !expr1 => Hinv' Heps'.
have Hhalf : (k%:R : R)^-1 <= 1 - (k%:R : R)^-1.
  rewrite lerBrDr -div1r -mulrDl ler_pdivrMr // mul1r -(natrD R 1 1).
  by rewrite ler_nat.
apply: (decrypt_reduction_admissibleF (inst_v1 (I k)) (inst_u1 (I k))
          (inst_u2 (I k)) (inst_u3_unit (I k)) (inst_dk_a (I k))
          (inst_dk_b (I k)) (inst_dk_c (I k)) (inst_rb2 (I k))
          (inst_rc2 (I k))).
apply: lt_le_trans Heps' _; apply: le_trans Hhalf _.
by rewrite lerD2l lerN2 ltW.
Qed.

End dsdp_instance_family.

Section trivial_witness.
Context {R : realType}.

(* The one-element coin space, in the successor form the uniform coin of the
   abstract development takes. *)
Fact card_renc_ord1 : #|'I_1| = #|'I_1|.-1.+1.
Proof. by rewrite card_ord. Qed.

(* The witness family: the identity scheme of idealized_ahe.v over
   plaintext spaces of cardinality (k+2)^(k+2), trivial coins and keys.
   It hides nothing; its role is exactly that the headline's hypotheses
   are jointly satisfiable, and on it the guessing probability is
   1/#|plain|, not 0, so the conclusion has content here. *)
Definition trivial_instance (k : nat) : dsdp_instance := {|
  inst_AHE          := Idealized_HETypes 'Z_((k.+2) ^ k.+2) ;
  inst_renc         := 'I_1 ;
  inst_card_renc    := card_renc_ord1 ;
  inst_rand_of_renc := fun _ => 0 ;
  inst_v1 := 0 ; inst_u1 := 0 ; inst_u2 := 0 ; inst_u3 := 1 ;
  inst_u3_unit      := GRing.unitr1 _ ;
  inst_dk_a := 0 ; inst_dk_b := 0 ; inst_dk_c := 0 ;
  inst_rb2 := ord0 ; inst_rc2 := ord0 |}.

(* The witness plaintext space at k has cardinality (k+2)^(k+2). *)
Let card_plain_trivial (k : nat) :
  #|plain (inst_AHE (trivial_instance k))| = ((k.+2) ^ k.+2)%N.
Proof. by rewrite card_ord Zp_cast // -{1}(expn0 k.+2) ltn_exp2l. Qed.

(* The constant predictor's distinguisher reads only the state slot, so the
   Bob-key reduction adversary ignores the challenge ciphertext and the
   cipher-constant class admits it. *)
Lemma trivial_bob_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (inst_card_renc (trivial_instance k))
       (@inst_rand_of_renc (trivial_instance k)))
    (bob_trace_adversary (R:=R) (inst_card_renc (trivial_instance k))
       (@inst_rand_of_renc (trivial_instance k))
       (inst_v1 (trivial_instance k)) (inst_u1 (trivial_instance k))
       (inst_u2 (trivial_instance k)) (inst_u3 (trivial_instance k))
       (inst_dk_a (trivial_instance k)) (inst_dk_b (trivial_instance k))
       (inst_dk_c (trivial_instance k)) (inst_rc2 (trivial_instance k))
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] rho3].
Qed.

(* The Charlie-key counterpart of trivial_bob_cipher_constant. *)
Lemma trivial_charlie_cipher_constant (k : nat) :
  indcpa_admissible
    (cipher_constant_assumption (R:=R) (inst_card_renc (trivial_instance k))
       (@inst_rand_of_renc (trivial_instance k)))
    (charlie_trace_adversary (R:=R) (inst_card_renc (trivial_instance k))
       (@inst_rand_of_renc (trivial_instance k))
       (inst_v1 (trivial_instance k)) (inst_u1 (trivial_instance k))
       (inst_u2 (trivial_instance k)) (inst_u3 (trivial_instance k))
       (inst_dk_a (trivial_instance k)) (inst_dk_b (trivial_instance k))
       (inst_dk_c (trivial_instance k)) (inst_rc2 (trivial_instance k))
       (distinguisher_of_predictor (fun _ => 0))).
Proof.
apply/forallP => c; apply/forallP => ch1; apply/forallP => ch2.
by case: c => [[[vv ms] ra] c2zero].
Qed.

(* The headline's hypotheses hold together at least once: the witness
   discharges every one of them end-to-end. *)
Corollary trivial_instance_guess_V2_negligible :
  negligible_fun (fun k =>
    alice_trace_guess_V2_pr (R:=R) (inst_card_renc (trivial_instance k))
      (@inst_rand_of_renc (trivial_instance k))
      (inst_v1 (trivial_instance k)) (inst_u1 (trivial_instance k))
      (inst_u2 (trivial_instance k)) (inst_u3 (trivial_instance k))
      (inst_dk_a (trivial_instance k)) (inst_dk_b (trivial_instance k))
      (inst_dk_c (trivial_instance k)) (inst_rb2 (trivial_instance k))
      (inst_rc2 (trivial_instance k)) (fun _ => 0)).
Proof.
apply: (alice_trace_guess_V2_admissible_negligible
          (I := trivial_instance)
          (A := fun k => cipher_constant_assumption
                  (inst_card_renc (trivial_instance k))
                  (@inst_rand_of_renc (trivial_instance k)))
          (predict := fun k => fun _ => 0)).
- exact: trivial_bob_cipher_constant.
- exact: trivial_charlie_cipher_constant.
- apply: negligible_fun_le negligible_fun_inv_expnn => k.
  by rewrite card_plain_trivial.
- exact: negligible_fun_cst0.
Qed.

End trivial_witness.
