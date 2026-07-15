From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import smc_interpreter pismc.
Require Import smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types.
Require Import idealized_ahe.

Local Open Scope ring_scope.

(* Procs over ABSTRACT DI *)
Section abstract.
Variable DI : DSDP_Interface.
Variable decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI).
Variable ek : party_id -> di_pub_keyT DI.

Let data := di_data DI.
Let e := di_data_of_cipher DI.
Let k := di_data_of_priv_key DI.
Let dd := di_data_of_plain DI.
Let Emul := di_emul DI.
Let Epow := di_epow DI.

Definition alice_idx : nat := 0.
Definition bob_idx : nat := 1.
Definition charlie_idx : nat := 2.
Coercion nat_to_party_id : nat >-> party_id.

Definition tenc (p : party_id) (m : di_msgT DI) (r : di_randT DI) : di_cipherT DI :=
  di_encrypt DI (ek p) m r.

Definition tpbob (dk : di_priv_keyT DI)(v2 : di_msgT DI)(rb1 rb2 : di_randT DI) :
  @sproc dsdp_dtype data bob_idx _ _ :=
  DInit (k dk) (
  DInit (dd v2) (
  DSend (charlie_idx) (e (tenc bob_idx v2 rb1)) (
  DRecv_dec decode (alice_idx) dk (fun d2 =>
  DRecv_enc (alice_idx) (fun a3 =>
    DSend (alice_idx) (e (Emul a3 (tenc charlie_idx d2 rb2))) (
  DFinish)))))).

End abstract.

(* Instantiate at Standard with Idealized AHE *)
Section concrete.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'F_m.
Local Definition AHE0 : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      (@Idealized_isEncDec msg) (@Idealized_isAHEnc msg)).
Let DI0 := Standard_DSDP_Interface AHE0.
Let decode0 : di_priv_keyT DI0 -> di_cipherT DI0 -> option (di_msgT DI0) := @dec AHE0.
Variables (kb : priv_key AHE0) (v2 : plain AHE0).
Let ek0 (p : party_id) : pub_key AHE0 := pub_of_priv kb.
Let runit : rand AHE0 := 1.

Definition apb := mk_aproc (@tpbob DI0 decode0 ek0 kb v2 runit runit).

(* Can we native_compute something about this abstract-DI proc at concrete? *)
Lemma test_compute : [> [:: apb] ] = 7.
Proof. reflexivity. Qed.

End concrete.
