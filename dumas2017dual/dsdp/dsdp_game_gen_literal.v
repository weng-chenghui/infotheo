(* dsdp_game_gen_literal.v — the LITERAL (hand-spelled) form of the auto-derived
   corrupted-Alice SSProve program.  [gen_literal_zeroE] / [gen_literal_realE]
   certify that the legible programs below are exactly the denotations
   [drun seed gc] / [drun seed gc_real] the generator emits for the
   output-exposing all-zero / real endpoint games, with the scalar-product output
   S written by name into [Sout_cell].  The reflection scaffolding (the seven
   [denote_run] unfold lemmas, [gc_eq], [output_term], [denote_output_termE]) is
   re-established here, standalone, so this file sits upstream of and independent
   from dsdp_security_indcpa_fiber.v. *)

From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".
From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code.
Require Import dsdp_symbolic.
Require Import dsdp_game_symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Section dsdp_game_gen_literal.
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable seed : denv AHE.
Hypothesis card_renc_neq : card_renc != card_msg.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis seed_wu1 : as_plain (de_val_nth seed 0) = w_u1.
Hypothesis seed_wu2 : as_plain (de_val_nth seed 1) = w_u2.
Hypothesis seed_wu3 : as_plain (de_val_nth seed 2) = w_u3.
Hypothesis seed_wv1 : as_plain (de_val_nth seed 3) = w_v1.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher) (in custom pack_type at level 2).

Set Warnings "-notation-overridden".
Notation "u *h w" := (Emul u w) (at level 40).
Notation "u ^h w" := (Epow u w) (at level 40).
Notation "'E<' p ',' s '>(|' m '|)'" :=
  (enc (pkey_of_party p) m (rand_of_renc (sample_to_renc renc_card s)))
  (at level 10, p constr at level 0, s constr at level 0, m constr at level 200,
   format "'E<' p ',' s '>(|'  m  '|)'").
Notation "'m[' i ']'" := (msg_of_idx i) (at level 0).
Notation "'<[' c ']>'" := (chcipher_of_cipher c) (at level 0).
Set Warnings "notation-overridden".

(* The seeded output-exposing games (identical RHS to zero_game_leak_S /
   real_game_leak_S run oracles). *)
Let gc      := all_zero (game_of_trace_seeded dsdp_weight_names
                 (dsdp_alice_obs_leak_S_seeded card_msg card_renc)).
Let gc_real := all_real (game_of_trace_seeded dsdp_weight_names
                 (dsdp_alice_obs_leak_S_seeded card_msg card_renc)).
Let drun := denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
              pkey_of_party msg_of_idx rand0.
Let dhe := denote_he pkey_of_party rand0.

(* A card_msg sample node draws a uniform message index and pushes its plaintext. *)
Lemma denote_run_sample_msg (e:denv AHE) k : drun e (GC_sample card_msg k) = (x ← sample uniform card_msg ;; drun (push_val (Gplain (msg_of_idx x)) e) k).
Proof. by rewrite /drun /denote_run -/denote_run eqxx. Qed.
(* A card_renc sample node draws a uniform index and pushes its encryption randomness. *)
Lemma denote_run_sample_renc (e:denv AHE) k : drun e (GC_sample card_renc k) = (x ← sample uniform card_renc ;; drun (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k).
Proof. by rewrite /drun /denote_run -/denote_run (negbTE card_renc_neq) eqxx. Qed.
(* A put node writes the denoted term into V_2_cell. *)
Lemma denote_run_put (e:denv AHE) t k : drun e (GC_put t k) = (#put (V_2_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;; drun e k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
(* A put_output node writes the denoted scalar-product output into Sout_cell. *)
Lemma denote_run_put_output (e:denv AHE) t k : drun e (GC_put_output t k) = (#put (Sout_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;; drun e k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
(* A let node pushes the denoted term as a new value binding. *)
Lemma denote_run_let (e:denv AHE) t k : drun e (GC_let t k) = drun (push_val (dhe e t) e) k.
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
(* An enc_hop node draws fresh randomness and pushes the encryption of the denoted secret to the hop party. *)
Lemma denote_run_enc_hop (e:denv AHE) pk secret k : drun e (GC_enc_hop pk secret k) = (ir ← sample uniform card_renc ;; drun (push_val (Gcipher (enc (pkey_of_party (nat_to_party_id pk)) (as_plain (dhe e secret)) (rand_of_renc (sample_to_renc renc_card ir)))) e) k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
(* A ret node returns the leaked ciphertexts, each denoted and marshalled to the wire type. *)
Lemma denote_run_ret (e:denv AHE) outs : drun e (GC_ret outs) = ret ([seq chcipher_of_cipher (as_cipher (dhe e o)) | o <- outs] : cipher_list t_cipher).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.

(* The explicit AST of the seeded all-zero output-exposing game.
   Naming: kept as [gc_eq] (the defining equation of [gc]) to mirror [gc_eq] in
   dsdp_security_indcpa_fiber.v. *)
Lemma gc_eq : gc = GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_renc (GC_sample card_renc (GC_put (HE_var 3) (GC_enc_hop 1 (HE_const 0) (GC_enc_hop 2 (HE_const 0) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 7)) (HE_enc 1 (HE_var 3) 1)) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 9)) (HE_enc 2 (HE_var 3) 0)) (GC_put_output (HE_add (HE_add (HE_mul (HE_var 8) (HE_var 11)) (HE_mul (HE_var 9) (HE_var 7))) (HE_mul (HE_var 10) (HE_var 6))) (GC_ret [:: HE_var 1; HE_var 0; HE_var 3; HE_var 2])))))))))))).
Proof. by rewrite /gc; vm_compute. Qed.

(* The explicit AST of the seeded real output-exposing game; the two hops carry
   the real secrets rather than 0.
   Naming: kept as [gc_real_eq] to mirror the [gc_eq] convention above. *)
Lemma gc_real_eq : gc_real = GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_renc (GC_sample card_renc (GC_put (HE_var 3) (GC_enc_hop 1 (HE_var 3) (GC_enc_hop 2 (HE_var 3) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 7)) (HE_enc 1 (HE_var 3) 1)) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 9)) (HE_enc 2 (HE_var 3) 0)) (GC_put_output (HE_add (HE_add (HE_mul (HE_var 8) (HE_var 11)) (HE_mul (HE_var 9) (HE_var 7))) (HE_mul (HE_var 10) (HE_var 6))) (GC_ret [:: HE_var 1; HE_var 0; HE_var 3; HE_var 2])))))))))))).
Proof. by rewrite /gc_real; vm_compute. Qed.

(* output_term — the GC_put_output he_term (scalar product over the put_output
   env indices v1=11, u1=8, u2=9, u3=10, v2=7, v3=6). *)
Notation output_term :=
  (HE_add (HE_add (HE_mul (HE_var 8) (HE_var 11)) (HE_mul (HE_var 9) (HE_var 7)))
          (HE_mul (HE_var 10) (HE_var 6))).

(* The leaked output term denotes to the scalar-product spec [dsdp_output] of the
   env values at the put_output indices. *)
Lemma denote_output_termE (e : denv AHE) :
  as_plain (dhe e output_term)
  = dsdp_output (as_plain (de_val_nth e 11)) (as_plain (de_val_nth e 8))
                (as_plain (de_val_nth e 9)) (as_plain (de_val_nth e 10))
                (as_plain (de_val_nth e 7)) (as_plain (de_val_nth e 6)).
Proof. by rewrite /dhe /dsdp_output /=. Qed.

(* ---- the legible programs (transcribed from the reduced normal form) ------- *)

(* The all-zero output-exposing game: four scalar samples [x x0 x1 x2], two
   encryption-randomness samples [x5 x6], V_2 := m[x], two hops encrypting 0 with
   inline randomness [ir ir0], the scalar-product output [Sout] put by name into
   [Sout_cell], and the leaked combines/hops [a2 ; a3 ; bob_hop ; charlie_hop]. *)
Definition gen_literal_zero : raw_code (cipher_list t_cipher) :=
  (x  ← sample uniform card_msg ;;
   x0 ← sample uniform card_msg ;;
   x1 ← sample uniform card_msg ;;
   x2 ← sample uniform card_msg ;;
   x5 ← sample uniform card_renc ;;
   x6 ← sample uniform card_renc ;;
   #put (V_2_cell t_msg) := Some (chmsg_of_msg m[ x ]) ;;
   ir  ← sample uniform card_renc ;;
   ir0 ← sample uniform card_renc ;;
   let Sout := dsdp_output w_v1 w_u1 w_u2 w_u3 m[ x ] m[ x0 ] in
   #put (Sout_cell t_msg) := Some (chmsg_of_msg Sout) ;;
   ret ([:: <[ (E<Bob, ir>(| 0%:R |) ^h w_u2) *h E<Bob, x5>(| m[ x1 ] |) ]> ;
            <[ (E<Charlie, ir0>(| 0%:R |) ^h w_u3) *h E<Charlie, x6>(| m[ x2 ] |) ]> ;
            <[ E<Bob, ir>(| 0%:R |) ]> ;
            <[ E<Charlie, ir0>(| 0%:R |) ]> ] : cipher_list t_cipher)).

(* The real output-exposing game: identical to [gen_literal_zero] except the two
   hops encrypt the true plaintexts m[x] (Bob) and m[x0] (Charlie). *)
Definition gen_literal_real : raw_code (cipher_list t_cipher) :=
  (x  ← sample uniform card_msg ;;
   x0 ← sample uniform card_msg ;;
   x1 ← sample uniform card_msg ;;
   x2 ← sample uniform card_msg ;;
   x5 ← sample uniform card_renc ;;
   x6 ← sample uniform card_renc ;;
   #put (V_2_cell t_msg) := Some (chmsg_of_msg m[ x ]) ;;
   ir  ← sample uniform card_renc ;;
   ir0 ← sample uniform card_renc ;;
   let Sout := dsdp_output w_v1 w_u1 w_u2 w_u3 m[ x ] m[ x0 ] in
   #put (Sout_cell t_msg) := Some (chmsg_of_msg Sout) ;;
   ret ([:: <[ (E<Bob, ir>(| m[ x ] |) ^h w_u2) *h E<Bob, x5>(| m[ x1 ] |) ]> ;
            <[ (E<Charlie, ir0>(| m[ x0 ] |) ^h w_u3) *h E<Charlie, x6>(| m[ x2 ] |) ]> ;
            <[ E<Bob, ir>(| m[ x ] |) ]> ;
            <[ E<Charlie, ir0>(| m[ x0 ] |) ]> ] : cipher_list t_cipher)).

(* The legible all-zero program equals the generator's denotation of the seeded
   all-zero output-exposing game. *)
Lemma gen_literal_zeroE : gen_literal_zero = drun seed gc.
Proof.
rewrite /gen_literal_zero gc_eq.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x0.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x1.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x2.
rewrite denote_run_sample_renc; congr sampler; apply: boolp.funext => x5.
rewrite denote_run_sample_renc; congr sampler; apply: boolp.funext => x6.
rewrite denote_run_put; congr putr.
rewrite denote_run_enc_hop; congr sampler; apply: boolp.funext => ir.
rewrite denote_run_enc_hop; congr sampler; apply: boolp.funext => ir0.
rewrite denote_run_let denote_run_let denote_run_put_output; congr putr.
1: by rewrite denote_output_termE seed_wv1 seed_wu1 seed_wu2 seed_wu3.
rewrite denote_run_ret /=.
rewrite /de_val_nth /de_rand_nth /push_val /push_rand /de_val /de_rand /=.
rewrite -![nth (Gplain 0) (de_val seed) _]/(de_val_nth seed _).
by rewrite seed_wu2 seed_wu3.
Qed.

(* The legible real program equals the generator's denotation of the seeded real
   output-exposing game. *)
Lemma gen_literal_realE : gen_literal_real = drun seed gc_real.
Proof.
rewrite /gen_literal_real gc_real_eq.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x0.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x1.
rewrite denote_run_sample_msg; congr sampler; apply: boolp.funext => x2.
rewrite denote_run_sample_renc; congr sampler; apply: boolp.funext => x5.
rewrite denote_run_sample_renc; congr sampler; apply: boolp.funext => x6.
rewrite denote_run_put; congr putr.
rewrite denote_run_enc_hop; congr sampler; apply: boolp.funext => ir.
rewrite denote_run_enc_hop; congr sampler; apply: boolp.funext => ir0.
rewrite denote_run_let denote_run_let denote_run_put_output; congr putr.
1: by rewrite denote_output_termE seed_wv1 seed_wu1 seed_wu2 seed_wu3.
rewrite denote_run_ret /=.
rewrite /de_val_nth /de_rand_nth /push_val /push_rand /de_val /de_rand /=.
rewrite -![nth (Gplain 0) (de_val seed) _]/(de_val_nth seed _).
by rewrite seed_wu2 seed_wu3.
Qed.

End dsdp_game_gen_literal.
