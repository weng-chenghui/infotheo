(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy at the executed piSMC trace                 *)
(*                                                                            *)
(* Documentation table completed in the final task.                           *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption dsdp_interface dsdp_program dsdp_pismc.
Require Import dsdp_alice_infotheo_secrecy.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section dsdp_alice_trace_link.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType)
          (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE).
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* Every party's public key is the one associated with its private key, so
   [dec_correct] fires by conversion and no key hypothesis is needed. *)
Definition pkey_of_dk (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

Let DI := Standard_DSDP_Interface AHE.

(* The finite image of the interpreter's data carrier: plaintexts kept,
   ciphertexts marshalled, both key sorts erased to marks.  Summand order
   mirrors [std_data]'s msgT + encT + privT + pubT. *)
Definition dsdp_trace_dataT : finType :=
  ((plain AHE + t_cipher) + unit + unit)%type.

Definition trace_data_of_di_data (x : di_data DI) : dsdp_trace_dataT :=
  match x with
  | inl (inl (inl m)) => inl (inl (inl m))
  | inl (inl (inr c)) => inl (inl (inr (chcipher_of_cipher c)))
  | inl (inr _) => inl (inr tt)
  | inr _ => inr tt
  end.

(* The single qualified reference in this file: the piSMC programs, not the
   same-named ones of dsdp_program.v. *)
Let decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.

End dsdp_alice_trace_link.
