(* Audit probe: do Bob/Charlie corrupted traces have nonzero IND-CPA hops?
   walk_obs emits AO_recv_hop ONLY when a received response has the bare shape
   HE_enc party (HE_var secret) _. Bob/Charlie receive homomorphic combos and
   decrypt-receives, so this probe checks their hop counts. *)
From mathcomp Require Import all_boot.
Require Import smc_interpreter.
Require Import dsdp_game_code dsdp_symbolic_exec dsdp_game_derivation.

Set Implicit Arguments.
Unset Strict Implicit.

(* Bob receives Alice's two sends to Bob: the homomorphic combos a1, a2. *)
Definition bob_recv_stream : seq symbolic_data :=
  [:: SD_cipher a1_observed ; SD_cipher a2_observed ].

(* Charlie receives ONLY Bob's send addressed to Charlie. Bob's sends in order
   are [head-send Enc(Bob,v2) to Alice ; combo to Charlie]; Charlie receives the
   second only (behead drops Bob's head send to Alice). *)
Definition charlie_recv_stream : seq symbolic_data :=
  [seq SD_cipher c | c <- behead (pmap symbolic_get_cipher
                              (sent_payloads pbob_sym bob_recv_stream))].

(* What Bob actually sends (to confirm the derivation is non-empty / faithful). *)
Definition bob_sends : seq he_term :=
  pmap symbolic_get_cipher (sent_payloads pbob_sym bob_recv_stream).

Definition charlie_sends : seq he_term :=
  pmap symbolic_get_cipher (sent_payloads pcharlie_sym charlie_recv_stream).

Definition bob_walk := walk_obs pbob_sym bob_recv_stream 100.
Definition charlie_walk := walk_obs pcharlie_sym charlie_recv_stream 100.

Definition bob_hops := count_obs_hops bob_walk.
Definition charlie_hops := count_obs_hops charlie_walk.

(* Full obs_of_procs traces (sample synthesis + put + walk + leak). *)
Definition bob_obs :=
  obs_of_procs pbob_sym bob_recv_stream 11 (fun a b => a ++ b) 7 7.
Definition charlie_obs :=
  obs_of_procs pcharlie_sym charlie_recv_stream 10 (fun a b => a ++ b) 7 7.

Goal True.
  idtac "=== Bob sends (forwarded to Charlie) ===".
  let x := eval compute in bob_sends in idtac x.
  idtac "=== Charlie receives ===".
  let x := eval compute in charlie_recv_stream in idtac x.
  idtac "=== Bob walk trace ===".
  let x := eval compute in bob_walk in idtac x.
  idtac "=== Bob hop count ===".
  let x := eval compute in bob_hops in idtac x.
  idtac "=== Charlie walk trace ===".
  let x := eval compute in charlie_walk in idtac x.
  idtac "=== Charlie hop count ===".
  let x := eval compute in charlie_hops in idtac x.
  idtac "=== Bob obs_of_procs full trace ===".
  let x := eval compute in bob_obs in idtac x.
  idtac "=== Bob obs_of_procs hop count ===".
  let x := eval compute in (count_obs_hops bob_obs) in idtac x.
  idtac "=== Charlie obs_of_procs hop count ===".
  let x := eval compute in (count_obs_hops charlie_obs) in idtac x.
  exact I.
Qed.
