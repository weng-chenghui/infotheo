(* Test script for dsdp_inv_no_orphan — explore goals *)
(* Run: coqc -R . infotheo scripts/test_no_orphan.v 2>&1 | tail -60 *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types smc_deadlock.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc dsdp_nofail.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.

Section test.
Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.
Variable dk : priv_key AHE.
Variable dk_relay : 'I_n_relay.+1 -> priv_key AHE.
Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek j.+1 = pub_of_priv (dk_relay j).
Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Hypothesis Hrelays_id : forall k : 'I_n_relay.+1, nth ord0 relays k = k.
Variable v0 : plain AHE.
Variable u : 'I_n_relay.+2 -> plain AHE.
Variable r : 'I_n_relay.+1 -> plain AHE.
Variable rand_a : 'I_n_relay.+1 -> rand AHE.
Variable v_relay : 'I_n_relay.+1 -> plain AHE.
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).

(* Copy needed definitions from dsdp_progress.v *)
Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.
Let saprocs := @dsdp_n_saprocs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Definition mk_tup (ps : seq (proc data)) (Hsz : size ps = n_relay.+2) :
  (n_relay.+2).-tuple (proc data) := Tuple (introT eqP Hsz).

(* Test: what does the no_orphan goal look like after case split? *)
Goal forall ps (Hsz : size ps = n_relay.+2),
  dsdp_inv AHE ek n_relay Hn_relay dk dk_relay dec_total key_alice key_relay
    relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay ps ->
  forall i : 'I_n_relay.+2, is_stuck (@mk_tup ps Hsz) i ->
    forall j : 'I_n_relay.+2, wait_for (@mk_tup ps Hsz) i j ->
      ~~ is_final (tnth (@mk_tup ps Hsz) j).
Proof.
move=> ps Hsz Hinv i Hi j.
rewrite /wait_for /= Hi /= => /eqP Htgt.
(* Bridge to seq/nat *)
rewrite (tnth_nth (default_proc data)) /mk_tup /=.
(* Now goal: ~~ is_final (nth ... ps (nat_of_ord j)) *)
(* Htgt : wait_target (tnth (mk_tup ps Hsz) i) = Some (nat_of_ord j) *)
(* Need to also bridge Htgt to seq/nat *)
rewrite (tnth_nth (default_proc data)) /mk_tup /= in Htgt.
(* Now Htgt : wait_target (nth ... ps (nat_of_ord i)) = Some (nat_of_ord j) *)
move: Htgt Hsz Hi; case: Hinv.
(* Inv_tail — simplest, test first *)
{ move=> ps0 Hsz0 Hwf [v Hsend] Halice Hfin Htgt Hsz Hi.
  (* nat_of_ord i determines the position *)
  case Hi0 : (nat_of_ord i) => [|i'].
  - (* i=0: Alice = Recv n_relay.+1 f. wait_target = Some n_relay.+1 *)
    (* j = n_relay.+1. ps[j] = Send 0 v Finish. is_final(Send ...) = false. *)
    rewrite Halice alice_foldr_at_tail in Htgt.
    case: (alice_tail_is_recv AHE n_relay dk v0 u r) => f' Htail.
    rewrite Htail /= in Htgt.
    case: Htgt => Hjeq.
    rewrite -Hjeq Hsend. done.
  - (* i=i'+1: relay position *)
    (* If i'+1 < n_relay: ps[i'+1] = Finish. But Finish is final, contradicts is_stuck *)
    Show.
    admit.
}
Abort.

End test.
