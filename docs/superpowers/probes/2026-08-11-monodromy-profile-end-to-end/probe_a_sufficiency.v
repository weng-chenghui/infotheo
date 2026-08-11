(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-A: sufficiency of MonodromyProfile for an end-to-end run           *)
(*                                                                            *)
(* Section generic_sufficiency builds, from a generic mp : MonodromyProfile R *)
(* and a register of section Variables, the eight objects of request 7.1:     *)
(* dealer, participant list, verifier, session-typed process list, erased     *)
(* process list, run_interp result, one participant trace, verifier           *)
(* endpoints. Every Variable tagged REGISTER is a value the profile does not  *)
(* determine. The two instantiation sections fill the register at             *)
(* pgl27_profile and at five_card_profile with bias 0.                        *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The generic run and its register                                       *)
(******************************************************************************)

Section generic_sufficiency.

Variable R : realType.
Variable mp : MonodromyProfile R.

Let M  := mp_M mp.
Let PI := mp_PI mp.
Let N  := (pgg_N' M).+1.
Let T  := (pi_T' PI).+1.

(* REGISTER: the dealt content readout. The profile's rp_content is a fixed
   endomorphism of 'I_N, so it cannot depend on a dealt secret or on committed
   inputs; the share readout tnth (ts_encode (rp_scheme (mp_plug mp)) s) lives
   on 'I_(ts_T' (rp_scheme (mp_plug mp))).+1, a different index type. *)
Variable content_of : seq 'I_N -> ('I_N -> 'I_N).

(* REGISTER: the dealt deck. mp_security carries a word length sw_L and a
   distribution sw_rho_dist on {perm 'I_N}, never a concrete seq (pgg_gT M). *)
Variable W : seq (pgg_gT M).

(* REGISTER: the committing input parties. MonodromyProfile has no input-mode
   field, so the processes that send the committed cards are outside it. *)
Variable input_procs : seq (aproc pgg_dtype (pgg_data N)).

(* REGISTER: the party identifiers the dealer's prologue receives from. *)
Variable inputs : seq nat.

(* REGISTER: the announced index into the deck W. *)
Variable P_idx : nat.

(* REGISTER: the interpreter fuel. *)
Variable fuel : nat.

(** gen_players — the participant list of the run.
    @intent: the enumeration of the pi_T'.+1 seats of mp_PI; derived from the
    profile alone. *)
Definition gen_players : seq 'I_T := enum 'I_T.

(** gen_dealer — the dealer of the run.
    @intent: dealer_with_input_encoding at mp_PI with the register's content
    readout, deck, input identifiers and announced index. *)
Definition gen_dealer :=
  dealer_with_input_encoding PI content_of W inputs gen_players P_idx.

(** gen_verifier — the verifier of the run.
    @intent: exchange_verifier at mp_PI over gen_players; derived from the
    profile alone. *)
Definition gen_verifier := exchange_verifier PI gen_players.

(** gen_saprocs — the session-typed process list of the run.
    @intent: dealer, verifier, one player per seat, then the register's input
    parties, in process-identifier order. *)
Definition gen_saprocs : seq (aproc pgg_dtype (pgg_data N)) :=
  mk_aproc gen_dealer :: mk_aproc gen_verifier
    :: [seq mk_aproc (exchange_player PI i) | i <- gen_players] ++ input_procs.

(** gen_procs — the erased process list.
    @intent: the plain-proc image of gen_saprocs. *)
Definition gen_procs := erase_aprocs gen_saprocs.

(** gen_run — the interpreter result.
    @intent: run_interp at the register's fuel on gen_procs, a pair of the
    final process states and the per-process traces. *)
Definition gen_run := run_interp fuel gen_procs.

(** gen_participant_trace — the executed trace of the seat-i player.
    @intent: entry 2 + i of gen_run.2, the player processes following the
    dealer and the verifier. *)
Definition gen_participant_trace (i : 'I_T) := nth [::] gen_run.2 (2 + i).

(** gen_endpoints — the verifier's collected endpoints.
    @intent: endpoints_of_trace of the verifier's executed trace, entry 1 of
    gen_run.2. *)
Definition gen_endpoints := endpoints_of_trace (nth [::] gen_run.2 1).

(** gen_input_ids — the party identifiers of the input parties under the
    positional convention.
    @intent: the input parties occupy process identifiers T.+2 onwards, so
    their identifiers are iota T.+2 (size input_procs). *)
Definition gen_input_ids : seq nat := iota T.+2 (size input_procs).

(** gen_content_plug_fixed — the content readout the plug does supply.
    @intent: rp_content of mp_plug, an endomorphism of 'I_N constant in the
    committed inputs and in the dealt secret. *)
Definition gen_content_plug_fixed : seq 'I_N -> ('I_N -> 'I_N) :=
  fun _ => rp_content (mp_plug mp).

(** gen_content_plug_cast — the share readout of a dealt secret, given an
    equality between the card count and the share count.
    @intent: tnth (ts_encode (rp_scheme (mp_plug mp)) s) transported along
    N = (ts_T' (rp_scheme (mp_plug mp))).+1. *)
Definition gen_content_plug_cast
    (Hcard : N = (ts_T' (rp_scheme (mp_plug mp))).+1) (s : mp_secretT mp)
    : seq 'I_N -> ('I_N -> 'I_N) :=
  fun _ i => tnth (ts_encode (rp_scheme (mp_plug mp)) s) (cast_ord Hcard i).

(* Counter-probe: without Hcard the share readout does not elaborate. The
   rejected command records the constraint verbatim:
     The term "tnth (ts_encode (rp_scheme (mp_plug mp)) s)" has type
      "'I_(ts_T' (rp_scheme (mp_plug mp))).+1 -> 'I_(pgg_N' (mp_M mp)).+1"
     while it is expected to have type "'I_N -> 'I_N" (cannot unify "'I_N"
     and "'I_(ts_T' (rp_scheme (mp_plug mp))).+1"). *)
Fail Definition gen_content_of_plug (s : mp_secretT mp)
    : seq 'I_N -> ('I_N -> 'I_N) :=
  fun _ => tnth (ts_encode (rp_scheme (mp_plug mp)) s).

(** gen_players_size — the participant list has one entry per seat.
    @main architecture: size (enum 'I_T) = T. *)
Lemma gen_players_size : size gen_players = T.
Proof. by rewrite /gen_players size_enum_ord. Qed.

(** gen_procs_size — the run has one process per seat plus the dealer, the
    verifier and the input parties.
    @main architecture: size gen_procs = T.+2 + size input_procs. *)
Lemma gen_procs_size : size gen_procs = T.+2 + size input_procs.
Proof.
rewrite /gen_procs /erase_aprocs size_map /gen_saprocs.
rewrite -[size (_ :: _ :: _)]/((size
  ([seq mk_aproc (exchange_player PI i) | i <- gen_players]
     ++ input_procs)).+2).
by rewrite size_cat size_map gen_players_size.
Qed.

(* Obligations, not data: termination of gen_run at fuel, the count bridge
   pi_T' PI = ts_T' (rp_scheme (mp_plug mp)) that types the endpoint tuple fed
   to run_recover, and the endpoint equation. None is a field of
   MonodromyProfile and none is provable for a generic mp. *)

End generic_sufficiency.

(******************************************************************************)
(*     Register filled at pgl27_profile                                       *)
(******************************************************************************)

Section pgl27_register.

Variable R : realType.
Variable s : bool.
Variable w0 : pgg_gT pgl27_M.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** pgl_content — the PGL(2,7) content readout.
    @intent: the shares ts_encode orbit_scheme s of the dealt orbit secret,
    read at a card position; the eight cards and the eight shares share an
    index type. *)
Definition pgl_content : seq 'I_(pgg_N' (mp_M mpP)).+1 ->
    ('I_(pgg_N' (mp_M mpP)).+1 -> 'I_(pgg_N' (mp_M mpP)).+1) :=
  fun _ => tnth (ts_encode orbit_scheme s).

(** pgl_input_procs — the PGL(2,7) input parties.
    @intent: none; the position-model run commits no inputs. *)
Definition pgl_input_procs
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mpP)).+1)) := [::].

(** pgl_dealer — the PGL(2,7) dealer of the generic run. @intent: gen_dealer
    at the cut [:: w0], no committed inputs, announced index 0. *)
Definition pgl_dealer := @gen_dealer R mpP pgl_content [:: w0] [::] 0.

(** pgl_players — the eight PGL(2,7) seats. @intent: gen_players at mpP. *)
Definition pgl_players := @gen_players R mpP.

(** pgl_verifier — the PGL(2,7) verifier. @intent: gen_verifier at mpP. *)
Definition pgl_verifier := @gen_verifier R mpP.

(** pgl_saprocs — the ten session-typed processes. @intent: gen_saprocs at the
    filled register. *)
Definition pgl_saprocs :=
  @gen_saprocs R mpP pgl_content [:: w0] pgl_input_procs [::] 0.

(** pgl_procs — the erased ten-process list. @intent: gen_procs at the filled
    register. *)
Definition pgl_procs :=
  @gen_procs R mpP pgl_content [:: w0] pgl_input_procs [::] 0.

(** pgl_run — the PGL(2,7) interpreter result. @intent: gen_run at fuel
    pgl27_fuel. *)
Definition pgl_run :=
  @gen_run R mpP pgl_content [:: w0] pgl_input_procs [::] 0 pgl27_fuel.

(** pgl_trace — the executed trace of one PGL(2,7) participant.
    @intent: gen_participant_trace at seat i. *)
Definition pgl_trace (i : 'I_(pi_T' (mp_PI mpP)).+1) :=
  @gen_participant_trace R mpP pgl_content [:: w0] pgl_input_procs [::] 0
    pgl27_fuel i.

(** pgl_endpoints — the PGL(2,7) verifier endpoints. @intent: gen_endpoints at
    the filled register. *)
Definition pgl_endpoints :=
  @gen_endpoints R mpP pgl_content [:: w0] pgl_input_procs [::] 0 pgl27_fuel.

(** pgl_procs_size — the PGL(2,7) run has ten processes.
    @main architecture: size pgl_procs = 10, the dealer, the verifier and the
    eight seats. *)
Lemma pgl_procs_size : size pgl_procs = 10.
Proof. exact: gen_procs_size. Qed.

(** pgl_input_ids — the PGL(2,7) run commits no inputs.
    @main architecture: the positional identifiers of the input parties are
    empty, matching the empty prologue of pgl27_dealer_run. *)
Lemma pgl_input_ids : @gen_input_ids R mpP pgl_input_procs = [::].
Proof. by []. Qed.

End pgl27_register.

(******************************************************************************)
(*     Register filled at five_card_profile with bias 0 (den Boer)            *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section fivecard_register.

Variable R : realType.
Variable a b : bool.
Variable w0 : pgg_gT FiveCardKim_M.
Variable P_idx : nat.
Variable L : nat.

(** fc_lt0 — the bias 0 is below 5%:R^-1.
    @main bound: the first Kim positivity constraint at bias 0. *)
Lemma fc_lt0 : (0:R) < 5%:R^-1.
Proof. by rewrite invr_gt0 ltr0n. Qed.

(** fc_gt0 — the bias 0 is above - (4%:R * 5%:R^-1).
    @main bound: the second Kim positivity constraint at bias 0. *)
Lemma fc_gt0 : - (4%:R * 5%:R^-1) < (0:R).
Proof. by rewrite oppr_lt0 mulr_gt0 // ?ltr0n // invr_gt0 ltr0n. Qed.

(** fc_spec0 — the bias 0 satisfies the spectral-gap constraint.
    @main bound: `|0| < 4%:R / 5%:R. *)
Lemma fc_spec0 : `|(0:R)| < 4%:R / 5%:R.
Proof. by rewrite normr0 divr_gt0 // ltr0n. Qed.

Let mpD : MonodromyProfile R := @five_card_profile R 0 fc_lt0 fc_gt0 fc_spec0 L.

(** db_content — the den Boer content readout.
    @intent: the layout den_boer_layout of the two committed bits, read at a
    card position. *)
Definition db_content : seq 'I_(pgg_N' (mp_M mpD)).+1 ->
    ('I_(pgg_N' (mp_M mpD)).+1 -> 'I_(pgg_N' (mp_M mpD)).+1) :=
  fun committed => tnth (den_boer_layout (den_boer_decode committed)).

(** db_input_procs — the two den Boer input parties.
    @intent: the parties 7 and 8 sending the card encodings of a and b. *)
Definition db_input_procs
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mpD)).+1)) :=
  [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool a))
    ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool b))].

(** db_dealer — the den Boer dealer of the generic run. @intent: gen_dealer at
    the cut [:: w0] with the commit prologue over parties 7 and 8. *)
Definition db_dealer := @gen_dealer R mpD db_content [:: w0] [:: 7; 8] P_idx.

(** db_players — the five den Boer seats. @intent: gen_players at mpD. *)
Definition db_players := @gen_players R mpD.

(** db_verifier — the den Boer verifier. @intent: gen_verifier at mpD. *)
Definition db_verifier := @gen_verifier R mpD.

(** db_saprocs — the nine session-typed processes. @intent: gen_saprocs at the
    filled register. *)
Definition db_saprocs :=
  @gen_saprocs R mpD db_content [:: w0] db_input_procs [:: 7; 8] P_idx.

(** db_procs — the erased nine-process list. @intent: gen_procs at the filled
    register. *)
Definition db_procs :=
  @gen_procs R mpD db_content [:: w0] db_input_procs [:: 7; 8] P_idx.

(** db_run — the den Boer interpreter result. @intent: gen_run at fuel 100. *)
Definition db_run :=
  @gen_run R mpD db_content [:: w0] db_input_procs [:: 7; 8] P_idx 100.

(** db_trace — the executed trace of one den Boer participant.
    @intent: gen_participant_trace at seat i. *)
Definition db_trace (i : 'I_(pi_T' (mp_PI mpD)).+1) :=
  @gen_participant_trace R mpD db_content [:: w0] db_input_procs [:: 7; 8]
    P_idx 100 i.

(** db_endpoints — the den Boer verifier endpoints. @intent: gen_endpoints at
    the filled register. *)
Definition db_endpoints :=
  @gen_endpoints R mpD db_content [:: w0] db_input_procs [:: 7; 8] P_idx 100.

(** db_procs_size — the den Boer run has nine processes.
    @main architecture: size db_procs = 9, the dealer, the verifier, the five
    seats and the two input parties. *)
Lemma db_procs_size : size db_procs = 9.
Proof. exact: gen_procs_size. Qed.

(** db_input_ids — the den Boer input identifiers are positional.
    @main architecture: iota T.+2 2 = [:: 7; 8], the identifiers
    den_boer_dealer_run passes to the commit prologue. *)
Lemma db_input_ids : @gen_input_ids R mpD db_input_procs = [:: 7; 8].
Proof. by []. Qed.

End fivecard_register.

(* Audit fold (2026-08-11, soundness finding 10): in-file assumption checks. *)
Print Assumptions gen_players_size.
Print Assumptions gen_procs_size.
Print Assumptions pgl_procs_size.
Print Assumptions pgl_input_ids.
Print Assumptions fc_lt0.
Print Assumptions fc_gt0.
Print Assumptions fc_spec0.
Print Assumptions db_procs_size.
Print Assumptions db_input_ids.
