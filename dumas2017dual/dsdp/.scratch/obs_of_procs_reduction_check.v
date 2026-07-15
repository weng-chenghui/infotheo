(* Feasibility check for the obs_of_procs derivation. Scratch only; do not commit. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code.
Require Import dsdp_symbolic.
Require Import dsdp_game_symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ================================================================= *)
(* Task A — senders' symbolic runs and the structured hop stream.    *)
(* ================================================================= *)

Definition pbob_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pbob Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 10) 22 23).

Definition pcharlie_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pcharlie Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 11) 24 25).

Fixpoint first_send (p : proc symbolic_data) : option symbolic_data :=
  match p with
  | smc_interpreter.Init _ k => first_send k
  | smc_interpreter.Send _ d _ => Some d
  | _ => None
  end.

Definition dsdp_received_hop_ciphertexts : seq symbolic_data :=
  pmap first_send [:: pbob_sym ; pcharlie_sym].

(* ================================================================= *)
(* Task B1 — walk_obs.                                               *)
(* ================================================================= *)

Fixpoint walk_obs (p : proc symbolic_data) (resp : seq symbolic_data) (next : nat)
  : seq alice_obs :=
  match p with
  | smc_interpreter.Init _ k => walk_obs k resp next
  | smc_interpreter.Recv _ f =>
      match resp with
      | [::] => [::]
      | r :: rs =>
          match symbolic_get_cipher r with
          | Some (HE_enc party (HE_var secret) _) =>
              AO_recv_hop party secret next
                :: walk_obs (f (SD_cipher (HE_var next))) rs next.+1
          | _ => [::]
          end
      end
  | smc_interpreter.Send _ d k =>
      match symbolic_get_cipher d with
      | Some c => AO_combine next c :: walk_obs k resp next.+1
      | None => walk_obs k resp next
      end
  | smc_interpreter.Ret _ => [::]
  | smc_interpreter.Finish => [::]
  | smc_interpreter.Fail => [::]
  end.

(* ================================================================= *)
(* Task B3 — collect_samples (and helpers).                          *)
(* ================================================================= *)

(* result names that are BOUND by hops/combines (must NOT become samples). *)
Definition bound_names (w : seq alice_obs) : seq nat :=
  foldr (fun o acc =>
    match o with
    | AO_recv_hop _ _ result => result :: acc
    | AO_combine result _ => result :: acc
    | _ => acc
    end) [::] w.

(* free HE_var value names of a term, in first-appearance (left-to-right) order. *)
Fixpoint term_value_names (t : he_term) : seq nat :=
  match t with
  | HE_var x => [:: x]
  | HE_const _ => [::]
  | HE_enc _ m _ => term_value_names m
  | HE_dec _ c => term_value_names c
  | HE_emul a b => term_value_names a ++ term_value_names b
  | HE_epow a b => term_value_names a ++ term_value_names b
  | HE_add a b => term_value_names a ++ term_value_names b
  | HE_sub a b => term_value_names a ++ term_value_names b
  | HE_mul a b => term_value_names a ++ term_value_names b
  end.

(* free HE_enc randomness-slot names of a term, in first-appearance order. *)
Fixpoint term_rnd_names (t : he_term) : seq nat :=
  match t with
  | HE_var _ => [::]
  | HE_const _ => [::]
  | HE_enc _ m r => term_rnd_names m ++ [:: r]
  | HE_dec _ c => term_rnd_names c
  | HE_emul a b => term_rnd_names a ++ term_rnd_names b
  | HE_epow a b => term_rnd_names a ++ term_rnd_names b
  | HE_add a b => term_rnd_names a ++ term_rnd_names b
  | HE_sub a b => term_rnd_names a ++ term_rnd_names b
  | HE_mul a b => term_rnd_names a ++ term_rnd_names b
  end.

(* value names contributed by one observation step. *)
Definition obs_value_names (o : alice_obs) : seq nat :=
  match o with
  | AO_recv_hop _ secret _ => [:: secret]
  | AO_combine _ expr => term_value_names expr
  | _ => [::]
  end.

(* randomness names contributed by one observation step. *)
Definition obs_rnd_names (o : alice_obs) : seq nat :=
  match o with
  | AO_combine _ expr => term_rnd_names expr
  | _ => [::]
  end.

(* dedup preserving first appearance; undup over the concatenation does that. *)
Definition collect_samples (card_msg card_renc : nat) (w : seq alice_obs)
  : seq alice_obs :=
  let bound := bound_names w in
  let vals  := undup (flatten [seq obs_value_names o | o <- w]) in
  let rnds  := undup (flatten [seq obs_rnd_names o | o <- w]) in
  let vals' := [seq x <- vals | x \notin bound] in
  let rnds' := [seq x <- rnds | x \notin bound] in
  [seq AO_sample_val card_msg x | x <- vals']
    ++ [seq AO_sample_rnd card_renc x | x <- rnds'].

(* ================================================================= *)
(* Task B4 — obs_of_procs (and the name helpers).                    *)
(* ================================================================= *)

Definition combine_names (w : seq alice_obs) : seq nat :=
  pmap (fun o => match o with AO_combine result _ => Some result | _ => None end) w.

Definition recv_names (w : seq alice_obs) : seq nat :=
  pmap (fun o => match o with AO_recv_hop _ _ result => Some result | _ => None end) w.

Definition obs_of_procs (corrupt : proc symbolic_data)
    (hop_sends : seq symbolic_data) (challenge : nat)
    (leak : seq nat -> seq nat -> seq nat) (card_msg card_renc : nat)
  : seq alice_obs :=
  let w := walk_obs corrupt hop_sends 100 in
  collect_samples card_msg card_renc w
    ++ [:: AO_put challenge]
    ++ w
    ++ [:: AO_leak (leak (combine_names w) (recv_names w)) ].

(* ================================================================= *)
(* Task C1 — gc_dsdp_rebuilt (local copy with two index edits).      *)
(* ================================================================= *)

Definition gc_dsdp_rebuilt (card_renc card_msg : nat) : game_code :=
  GC_sample card_msg (GC_sample card_msg (GC_sample card_msg
  (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg
  (GC_sample card_renc (GC_sample card_renc
  (GC_put (HE_var 5)
  (GC_enc_hop 1 (HE_var 5)
  (GC_enc_hop 2 (HE_var 5)
  (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 5)) (HE_enc 1 (HE_var 4) 1))
  (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 4)) (HE_enc 2 (HE_var 3) 0))
  (GC_ret [:: HE_var 1 ; HE_var 0 ; HE_var 3 ; HE_var 2 ])
  )))))))))))).

(* probe theorem to anchor an interactive session *)
Lemma reduction_check_probe : True.
Proof. exact: I. Qed.

(* C-D headline faithfulness, as a real lemma, to check assumptions. *)
Lemma reduction_check_faithful (cm cr : nat) :
  game_of_trace
    (obs_of_procs palice_sym dsdp_received_hop_ciphertexts 10
       (fun c r => c ++ r) cm cr)
  = gc_dsdp_rebuilt cr cm.
Proof. by []. Qed.
