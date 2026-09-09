From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring.
Require Import smc_interpreter pismc.
Require Import smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program dsdp_pismc.
Require Import idealized_ahe.

(**md**************************************************************************)
(* # Idealized executions of the DSDP piSMC programs                         *)
(*                                                                            *)
(* Idealized three-, four- and five-party programs terminate without failure. *)
(*                                                                            *)
(* The statements hold at every m: the plaintext carrier 'F_m is 'Z_(pdiv m), *)
(* which at m at most one is Z/2Z.                                            *)
(******************************************************************************)

Local Open Scope pismc_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(** * Session environment convergence for the idealized DSDP instance         *)
(******************************************************************************)

(* This section instantiates DSDP with the Idealized AHEncType, where
   enc/dec have concrete computable definitions. This enables native_compute
   proofs for termination properties. *)

Section dsdp_idealized_termination.

Variable m : nat.
Local Notation msg := 'F_m.

(* Build the Idealized AHEncType *)
Local Definition Idealized_EncDec_instance :=
  @Idealized_isEncDec msg.

Local Definition Idealized_AHEnc_instance :=
  @Idealized_isAHEnc msg.

Local Definition Idealized_EncDec_local : EncDecType :=
  @EncDec.Pack (Idealized_HETypes msg)
    (@EncDec.Class (Idealized_HETypes msg) Idealized_EncDec_instance).

Local Definition Idealized_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      Idealized_EncDec_instance Idealized_AHEnc_instance).

Let AHE : AHEncType := Idealized_AHEnc_local.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

(* Party definitions *)
Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.
Let pn : party_id -> nat := party_id_to_nat.

(* Program variables *)
Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).
Let runit : rand AHE := 1.

(* Private keys are just msg values in idealized *)
Let dk_a : priv_key AHE := k_a.
Let dk_b : priv_key AHE := k_b.
Let dk_c : priv_key AHE := k_c.

(* Public keys derived from private keys via pub_of_priv *)
Let ek (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

(* Instantiate programs from dsdp_program.v *)
Let palice_inst :=
  @dsdp_program.palice AHE bob charlie pn ek dk_a v1 u1 u2 u3 r2 r3 runit runit.
Let pbob_inst :=
  @dsdp_program.pbob AHE alice bob charlie pn ek dk_b v2 runit runit.
Let pcharlie_inst :=
  @dsdp_program.pcharlie AHE alice bob charlie pn ek dk_c v3 runit runit.

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Session-typed processes *)
Definition dsdp_ideal_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice_inst; pbob_inst; pcharlie_inst].

Definition dsdp_ideal_procs : seq (proc data) :=
  erase_aprocs dsdp_ideal_saprocs.

(* Fuel bound *)
Lemma dsdp_ideal_max_fuel_ok : [> dsdp_ideal_saprocs] = 27.
Proof. reflexivity. Qed.

(* DSDP (Idealized): after interpretation, all processes are terminal. *)
Lemma dsdp_ideal_terminates traces :
  all_terminated (interp [> dsdp_ideal_saprocs] dsdp_ideal_procs traces).1.
Proof. by native_compute. Qed.

(* DSDP (Idealized): after interpretation, no process is Fail. *)
Lemma dsdp_ideal_no_fail traces :
  all_nonfail (interp [> dsdp_ideal_saprocs] dsdp_ideal_procs traces).1.
Proof. by native_compute. Qed.

(* Main theorem: DSDP (Idealized) session environment converges to empty. *)
Theorem dsdp_ideal_senv_zero traces :
  exists aps' : seq (aproc dsdp_dtype data),
    erase_aprocs aps' =
      (interp [> dsdp_ideal_saprocs] dsdp_ideal_procs traces).1 /\
    aprocs_senv_depth aps' = 0.
Proof.
have [aps' [Hsz [Herase Hsenv]]] :=
  @senv_bounded _ _ [:: 0; 1; 2] [> dsdp_ideal_saprocs]
    dsdp_ideal_saprocs traces (leqnn _).
exists aps'.
split; first exact: Herase.
apply: terminated_nonfail_senv_zero.
- by rewrite Herase; exact: dsdp_ideal_terminates.
- by rewrite Herase; exact: dsdp_ideal_no_fail.
Qed.

End dsdp_idealized_termination.

(******************************************************************************)
(** * Four-party session compatibility at the idealized instance              *)
(******************************************************************************)

Section dsdp_n4_idealized_duality.

Variable m : nat.
Local Notation msg := 'F_m.

(* Idealized AHE setup *)
Local Definition N4_EncDec_instance :=
  @Idealized_isEncDec msg.

Local Definition N4_AHEnc_instance :=
  @Idealized_isAHEnc msg.

Local Definition N4_EncDec_local : EncDecType :=
  @EncDec.Pack (Idealized_HETypes msg)
    (@EncDec.Class (Idealized_HETypes msg) N4_EncDec_instance).

Local Definition N4_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      N4_EncDec_instance N4_AHEnc_instance).

Let AHE : AHEncType := N4_AHEnc_local.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

(* Per-instance decoder for the pismc procs' recv-and-decrypt.
   At the Standard interface this is the scheme's [dec]. *)
Let decode :
    di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.

(* Party keys *)
Variables (k0 k1 k2 k3 : msg).
Let dk0 : priv_key AHE := k0.
Let dk1 : priv_key AHE := k1.
Let dk2 : priv_key AHE := k2.
Let dk3 : priv_key AHE := k3.
Let runit : rand AHE := 1.

(* Public key mapping for 4 parties (party 3 = NoParty) *)
Let ek4 (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk0
  | Bob => pub_of_priv dk1
  | Charlie => pub_of_priv dk2
  | NoParty => pub_of_priv dk3
  end.

(* Program variables *)
Variables (v0 v1 v2 v3 : msg).
Variables (u0' u1' u2' u3' : msg).
Variables (r0' r1' r2' : msg).

(* Index functions for palice_n *)
Let u4 : 'I_4 -> msg := fun i =>
  match val i with 0 => u0' | 1 => u1' | 2 => u2' | _ => u3' end.
Let r4_3 : 'I_3 -> msg := fun i =>
  match val i with 0 => r0' | 1 => r1' | _ => r2' end.
Let rand4_3 : 'I_3 -> rand AHE := fun _ => runit.

(* 4-party programs: Alice + first relay + intermediate + last relay *)
Let palice_4 := @palice_n DI decode ek4 2
  [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT]
  dk0 v0 u4 r4_3 rand4_3.
Let pfirst_4 := @DParty_first DI decode ek4 1 2 dk1 v1 runit runit.
Let pinter_4 := @DParty_intermediate DI decode ek4 2 0 1 3 dk2 v2 runit runit.
Let plast_4 := @DParty_last DI decode ek4 3 2 dk3 v3 runit runit.

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Wrap as aprocs for duality checking *)
Definition ap_alice_n4 := mk_aproc palice_4.
Definition ap_first_n4 := mk_aproc pfirst_4.
Definition ap_inter_n4 := mk_aproc pinter_4.
Definition ap_last_n4 := mk_aproc plast_4.

(* 4-party compatibility verification *)
Lemma dsdp_compat_n4 :
  aprocs_compat [:: ap_alice_n4; ap_first_n4; ap_inter_n4; ap_last_n4].
Proof. by []. Qed.

(* Cross-check: generic builder produces same erased procs as hand-written *)
Let dk_relay_4 : 'I_3 -> priv_key AHE := fun i =>
  match val i with 0 => dk1 | 1 => dk2 | _ => dk3 end.
Let v_relay_4 : 'I_3 -> plain AHE := fun i =>
  match val i with 0 => v1 | 1 => v2 | _ => v3 end.
Let r1_relay_4 : 'I_3 -> rand AHE := fun _ => runit.
Let r2_relay_4 : 'I_3 -> rand AHE := fun _ => runit.

Lemma dsdp_n4_builder_correct :
  @dsdp_n_procs DI decode ek4 2
    [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT]
    dk0 v0 u4 r4_3 rand4_3 dk_relay_4 v_relay_4 r1_relay_4 r2_relay_4 =
  erase_aprocs [aprocs palice_4; pfirst_4; pinter_4; plast_4].
Proof. by native_compute. Qed.

(* 4-party saprocs for interpreter integration *)
Definition dsdp_n4_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice_4; pfirst_4; pinter_4; plast_4].

Definition dsdp_n4_procs : seq (proc data) :=
  erase_aprocs dsdp_n4_saprocs.

Lemma dsdp_n4_max_fuel_ok : [> dsdp_n4_saprocs] = 31.
Proof. reflexivity. Qed.

(* 4-party termination: after interpretation, all processes are terminal *)
Lemma dsdp_n4_terminates traces :
  all_terminated (interp [> dsdp_n4_saprocs] dsdp_n4_procs traces).1.
Proof. by native_compute. Qed.

(* 4-party no-fail: after interpretation, no process is Fail *)
Lemma dsdp_n4_no_fail traces :
  all_nonfail (interp [> dsdp_n4_saprocs] dsdp_n4_procs traces).1.
Proof. by native_compute. Qed.

(* 4-party session environment convergence *)
Theorem dsdp_n4_senv_zero traces :
  exists aps' : seq (aproc dsdp_dtype data),
    erase_aprocs aps' =
      (interp [> dsdp_n4_saprocs] dsdp_n4_procs traces).1 /\
    aprocs_senv_depth aps' = 0.
Proof.
have [aps' [Hsz [Herase Hsenv]]] :=
  @senv_bounded _ _ [:: 0; 1; 2; 3] [> dsdp_n4_saprocs]
    dsdp_n4_saprocs traces (leqnn _).
exists aps'.
split; first exact: Herase.
apply: terminated_nonfail_senv_zero.
- by rewrite Herase; exact: dsdp_n4_terminates.
- by rewrite Herase; exact: dsdp_n4_no_fail.
Qed.

End dsdp_n4_idealized_duality.

(******************************************************************************)
(** * Five-party session compatibility at the idealized instance              *)
(******************************************************************************)

Section dsdp_n5_idealized_duality.

Variable m : nat.
Local Notation msg := 'F_m.

(* Idealized AHE setup *)
Local Definition N5_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      (@Idealized_isEncDec msg) (@Idealized_isAHEnc msg)).

Let AHE : AHEncType := N5_AHEnc_local.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

(* Per-instance decoder for the pismc procs' recv-and-decrypt.
   At the Standard interface this is the scheme's [dec]. *)
Let decode :
    di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.

(* Party keys (parties 3 and 4 both map to NoParty via nat_to_party_id) *)
Variables (k0 k1 k2 k3 k4 : msg).
Let dk0 : priv_key AHE := k0.
Let dk1 : priv_key AHE := k1.
Let dk2 : priv_key AHE := k2.
Let dk3 : priv_key AHE := k3.
Let dk4 : priv_key AHE := k4.
Let runit : rand AHE := 1.

(* Public key mapping for 5 parties
   (parties 3,4 share NoParty — values don't affect duality) *)
Let ek5 (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk0
  | Bob => pub_of_priv dk1
  | Charlie => pub_of_priv dk2
  | NoParty => pub_of_priv dk3
  end.

Variables (v0 v1 v2 v3 v4 : msg).
Variables (u0' u1' u2' u3' u4' : msg).
Variables (r0' r1' r2' r3' : msg).

Let u5 : 'I_5 -> msg := fun i =>
  match val i with 0 => u0' | 1 => u1' | 2 => u2' | 3 => u3' | _ => u4' end.
Let r5_4 : 'I_4 -> msg := fun i =>
  match val i with 0 => r0' | 1 => r1' | 2 => r2' | _ => r3' end.
Let rand5_4 : 'I_4 -> rand AHE := fun _ => runit.

(* 5-party programs *)
Let palice_5 := @palice_n DI decode ek5 3
  [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT]
  dk0 v0 u5 r5_4 rand5_4.
Let pfirst_5 := @DParty_first DI decode ek5 1 2 dk1 v1 runit runit.
Let pinter2_5 := @DParty_intermediate DI decode ek5 2 0 1 3 dk2 v2 runit runit.
Let pinter3_5 := @DParty_intermediate DI decode ek5 3 0 2 4 dk3 v3 runit runit.
Let plast_5 := @DParty_last DI decode ek5 4 3 dk4 v4 runit runit.

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

Definition ap_alice_n5 := mk_aproc palice_5.
Definition ap_first_n5 := mk_aproc pfirst_5.
Definition ap_inter2_n5 := mk_aproc pinter2_5.
Definition ap_inter3_n5 := mk_aproc pinter3_5.
Definition ap_last_n5 := mk_aproc plast_5.

(* 5-party compatibility *)
Lemma dsdp_compat_n5 : aprocs_compat
    [:: ap_alice_n5; ap_first_n5; ap_inter2_n5; ap_inter3_n5; ap_last_n5].
Proof. by []. Qed.

(* 5-party saprocs and termination *)
Definition dsdp_n5_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice_5; pfirst_5; pinter2_5; pinter3_5; plast_5].

Definition dsdp_n5_procs : seq (proc data) :=
  erase_aprocs dsdp_n5_saprocs.

Lemma dsdp_n5_terminates traces :
  all_terminated (interp [> dsdp_n5_saprocs] dsdp_n5_procs traces).1.
Proof. by native_compute. Qed.

Lemma dsdp_n5_no_fail traces :
  all_nonfail (interp [> dsdp_n5_saprocs] dsdp_n5_procs traces).1.
Proof. by native_compute. Qed.

End dsdp_n5_idealized_duality.
