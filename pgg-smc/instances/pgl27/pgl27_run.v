(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGL(2,7) operational realization (position model)                          *)
(*                                                                            *)
(* The dealer deals the shares ts_encode orbit_scheme s of a bool orbit       *)
(* secret s, with the cut w0 and starts = ord_tuple 8. The verifier collects  *)
(* the eight endpoints; reconstruction returns s. This is the eight-card      *)
(* analogue of s5_run, with an empty input prologue and ten processes.        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_fuel       == the interpreter fuel driving the ten-process run     *)
(*   pgl27_players    == the eight explicit player ordinals of 'I_8           *)
(*   pgl27_dealer_run == the dealer dealing the encoded shares of s at cut w0 *)
(*   pgl27_saprocs    == the ten session-typed processes of one run           *)
(*   pgl27_procs      == the erased ten-process list fed to the interpreter   *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_endpoints     == the collected endpoints are the dealt shares      *)
(*   pgl27_run_recovers  == the executed run reconstructs the dealt secret    *)
(*                                                                            *)
(* The implemented decoder reads all eight endpoints; seven already determine *)
(* the class and six never do (pgl27_recovery.v). The secrecy statements of   *)
(* the companion files concern the pre-reveal execution: after the public     *)
(* reveal every player learns the secret by design.                           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** pgl27_fuel — the interpreter fuel bound driving the ten-process run to
    completion.
    @intent: the fixed fuel at which every process of the eight-card run
    reaches Finish; the interpreter halts early once no process advances, so
    this value only needs to exceed the number of communication rounds. *)
Definition pgl27_fuel : nat := 220.

(** pgl27_players — the eight-player list for the PGL(2,7) dealing phase.
    @intent: the explicit eight-element list of 'I_8 player ordinals; a
    concrete list (rather than enum 'I_8) lets the dealer's fold_senv reduce
    under vm_compute. *)
Definition pgl27_players : seq 'I_(pi_T' pgl27_PI).+1 :=
  [:: @Ordinal 8 0 isT; @Ordinal 8 1 isT; @Ordinal 8 2 isT; @Ordinal 8 3 isT;
      @Ordinal 8 4 isT; @Ordinal 8 5 isT; @Ordinal 8 6 isT; @Ordinal 8 7 isT].

(** pgl27_dealer_run — the PGL(2,7) dealer via the generic input-encoding
    dealer (cut w0, empty input prologue, position-model content reading the
    shares ts_encode orbit_scheme s of the dealt secret s).
    @intent: deals the encoded shares of the orbit secret s; the empty prologue
    [::] makes this a pure position-model dealer. *)
Definition pgl27_dealer_run (s : bool) (w0 : pgg_gT pgl27_M) :=
  dealer_with_input_encoding pgl27_PI
    (fun _ => tnth (ts_encode orbit_scheme s))
    [:: w0] [::] pgl27_players 0.

(** pgl27_saprocs — dealer ++ verifier ++ eight players, ordered by process id
    (0..9).
    @intent: the ten session-typed processes of one PGL(2,7) run. *)
Definition pgl27_saprocs (s : bool) (w0 : pgg_gT pgl27_M) :=
  [:: mk_aproc (pgl27_dealer_run s w0)
    ; mk_aproc (exchange_verifier pgl27_PI pgl27_players)
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 0 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 1 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 2 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 3 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 4 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 5 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 6 isT))
    ; mk_aproc (exchange_player pgl27_PI (@Ordinal 8 7 isT))].

(** pgl27_procs — the erased ten-process list fed to the interpreter.
    @intent: the plain-proc image of pgl27_saprocs driving run_interp. *)
Definition pgl27_procs (s : bool) (w0 : pgg_gT pgl27_M) :=
  erase_aprocs (pgl27_saprocs s w0).

(** pgl27_run_terminates — every process reaches Finish (ten procs), for any
    cut w0.
    @composes: pgl27_run_recovers *)
Lemma pgl27_run_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (run_interp pgl27_fuel (pgl27_procs s w0)).1 = nseq 10 Finish.
Proof. by vm_compute. Qed.

(** pgl27_verifier_endpoints — the verifier's executed endpoints are the dealt
    content readout at the deck cut and starts, one per player.
    @composes: pgl27_endpoints *)
Lemma pgl27_verifier_endpoints
    (g : seq 'I_(pgg_N' pgl27_M).+1 -> ('I_8 -> 'I_8))
    (w0 : pgg_gT pgl27_M)
    (st : 8.-tuple 'I_8) (Hst : uniq st) :
  let PI' := @MkPGGI pgl27_M 7 st Hst in
  endpoints_of_trace (nth [::] (run_interp pgl27_fuel (erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer PI' (g committed) pgl27_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier PI' pgl27_players)
      ; mk_aproc (exchange_player PI' (@Ordinal 8 0 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 8 1 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 8 2 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 8 3 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 8 4 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 8 5 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 8 6 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 8 7 isT))])).2 1)
  = [seq g [::] (@pgg_rho pgl27_M w0 (tnth st i)) | i <- pgl27_players].
Proof. move=> PI'; rewrite /PI'; vm_compute; reflexivity. Qed.

(** pgl27_endpoints — the verifier's collected endpoints are the dealt shares
    of the orbit secret s (cut w0, ord_tuple starts).
    @composes: pgl27_run_recovers *)
Lemma pgl27_endpoints (s : bool) (w0 : pgg_gT pgl27_M) :
  endpoints_of_trace (nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 1)
  = [seq tnth (ts_encode orbit_scheme s)
        (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) i))
     | i <- enum 'I_(pi_T' pgl27_PI).+1].
Proof.
rewrite /pgl27_procs /pgl27_saprocs /pgl27_dealer_run
  /dealer_with_input_encoding /identity_deck.
rewrite (@pgl27_verifier_endpoints (fun=> tnth (ts_encode orbit_scheme s))
  w0 (ord_tuple 8) pgl27_starts_uniq).
have Hde : pgl27_players = enum 'I_8.
  by apply: (inj_map val_inj); rewrite val_enum_ord.
by rewrite Hde.
Qed.

(** pgl27_endpoints_size — the verifier collects exactly ts_T'.+1 endpoints.
    @composes: pgl27_run_recovers *)
Lemma pgl27_endpoints_size (s : bool) (w0 : pgg_gT pgl27_M) :
  size (endpoints_of_trace
          (nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 1))
  = (ts_T' orbit_scheme).+1.
Proof. by rewrite pgl27_endpoints size_map size_enum_ord. Qed.

(** pgl27_run_recovers — reconstructing the verifier's executed endpoints
    returns the dealt orbit secret s, for any cut w0 in the group.
    @main correctness: the running PGL(2,7) protocol recovers the dealt orbit
    secret s : bool from the verifier's cut-permuted endpoints, via the
    scheme's reconstruction perm-invariance (orbit_recon_invariant) at w0. *)
Lemma pgl27_run_recovers (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  ts_recon orbit_scheme
    (tcast (pgl27_endpoints_size s w0)
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 1))))
  = s.
Proof.
move=> Hw0.
have Hgoal : forall (ep : seq 'I_(pgg_N' pgl27_M).+1)
    (Hsz : size ep = (ts_T' orbit_scheme).+1),
    ep = [seq tnth (ts_encode orbit_scheme s)
              (@pgg_rho pgl27_M w0 (tnth (pi_starts pgl27_PI) i))
            | i <- enum 'I_(pi_T' pgl27_PI).+1] ->
    ts_recon orbit_scheme (tcast Hsz (in_tuple ep)) = s.
  move=> ep Hsz Hep.
  rewrite -[s](@orbit_recon_invariant w0 s (ts_encode orbit_scheme s) Hw0
                 (ts_encode_valid orbit_scheme s)).
  congr (ts_recon _ _).
  apply: eq_from_tnth => i.
  rewrite tcastE tnth_mktuple.
  rewrite (tnth_nth ord0) /= Hep.
  rewrite (nth_map i) ?nth_ord_enum ?tnth_ord_tuple;
    last by rewrite size_enum_ord ltn_ord.
  by [].
apply: Hgoal.
exact: pgl27_endpoints.
Qed.
