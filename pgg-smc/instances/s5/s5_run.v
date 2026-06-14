(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 operational realization (position model)                               *)
(*                                                                            *)
(* The dealer deals the shares ts_encode s5_scheme s of a secret position     *)
(* s : 'I_5, with the identity cut and starts = ord_tuple 5. The verifier     *)
(* collects the five endpoints; reconstruction returns s. This is the         *)
(* position-model analogue of den_boer_run, with an empty input prologue.     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
Require Import pgg_interface.
From pgg_smc Require Import pgg_raag_s5 s5_profile pgg_raag_path.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** s5_M — the S_5 adjacent-transposition monodromy template (N = 5).
    @intent: a notation for the Gen_PGGTypes form s5_PI and s5_plug carry, so
    the run definitions share their type. s5_M is a section-local Let in the
    rigidity instance, hence not exported; spelled out here. *)
Local Notation s5_M := (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

(** s5_scheme — the S_5 sum-mod sharing scheme on 'I_5, convertible to
    rp_scheme s5_plug.
    @intent: the threshold scheme the dealer shares and the verifier
    reconstructs; the five-party sum-mod scheme. Named directly (rather than
    rp_scheme s5_plug) so the operational lemmas stay closed under the global
    context: s5_plug bundles the genus gap field, whose proof uses the
    justified Bring-curve facts, which are never exercised by the run. *)
Definition s5_scheme : ThresholdScheme 'I_5 'I_5 := @sum_mod_scheme 3 4.

(** s5_scheme_plug — s5_scheme is the scheme dealt by the s5 plug.
    @composes: s5_endpoints. *)
Lemma s5_scheme_plug : rp_scheme s5_plug = s5_scheme.
Proof. by []. Qed.

(** s5_players — the five-player list for the S_5 dealing phase.
    @intent: the explicit five-element list of 'I_5 player ordinals; a concrete
    list (rather than enum 'I_5) lets the dealer's fold_senv reduce under
    vm_compute. Used-by: s5_dealer_run, s5_saprocs. *)
Definition s5_players : seq 'I_(pi_T' s5_PI).+1 :=
  [:: @Ordinal 5 0 isT; @Ordinal 5 1 isT; @Ordinal 5 2 isT;
      @Ordinal 5 3 isT; @Ordinal 5 4 isT].

(** s5_dealer_run — the S_5 dealer via the generic input-encoding dealer
    (identity cut, empty input prologue, position-model content reading the
    shares ts_encode s5_scheme s of the dealt secret s).
    @intent: deals the encoded shares of the secret position s; the empty
    prologue [::] makes this a pure position-model dealer. Used-by:
    s5_saprocs. *)
Definition s5_dealer_run (s : 'I_5) :=
  dealer_with_input_encoding s5_PI
    (fun _ => tnth (ts_encode s5_scheme s))
    [::] s5_players 0.

(** s5_saprocs — dealer ++ verifier ++ five players, ordered by process id
    (0..6). @intent: the seven session-typed processes of one S_5 run.
    Used-by: s5_procs. *)
Definition s5_saprocs (s : 'I_5) :=
  [:: mk_aproc (s5_dealer_run s)
    ; mk_aproc (exchange_verifier s5_PI s5_players)
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 0 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 1 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 2 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 3 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 4 isT))].

(** s5_procs — the erased process list fed to the interpreter. *)
Definition s5_procs (s : 'I_5) := erase_aprocs (s5_saprocs s).

(** s5_run_terminates — every process reaches Finish (7 procs). *)
Lemma s5_run_terminates (s : 'I_5) :
  (run_interp 150 (s5_procs s)).1 = nseq 7 Finish.
Proof. by vm_compute. Qed.

(** s5_verifier_endpoints — the verifier's executed endpoints are the dealt
    content readout at the deck cut and starts, one per player.
    @composes: s5_endpoints. *)
Lemma s5_verifier_endpoints
    (g : seq 'I_(pgg_N' s5_M).+1 -> ('I_5 -> 'I_5))
    (w0 : pgg_gT s5_M)
    (st : 5.-tuple 'I_5) (Hst : uniq st) :
  let PI' := @MkPGGI s5_M 4 st Hst in
  endpoints_of_trace (nth [::] (run_interp 150 (erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer PI' (g committed) s5_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier PI' s5_players)
      ; mk_aproc (exchange_player PI' (@Ordinal 5 0 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 5 1 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 5 2 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 5 3 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 5 4 isT))])).2 1)
  = [seq g [::] (@pgg_rho s5_M w0 (tnth st i)) | i <- s5_players].
Proof. move=> PI'; rewrite /PI'; vm_compute; reflexivity. Qed.

(** s5_endpoints — the verifier's collected endpoints are the dealt shares of
    the secret position s (identity cut, ord_tuple starts).
    @composes: s5_run_recovers. *)
Lemma s5_endpoints (s : 'I_5) :
  endpoints_of_trace (nth [::] (run_interp 150 (s5_procs s)).2 1)
  = val (ts_encode s5_scheme s).
Proof.
rewrite /s5_procs /s5_saprocs /s5_dealer_run
        /dealer_with_input_encoding /identity_deck.
rewrite (@s5_verifier_endpoints
          (fun=> tnth (ts_encode s5_scheme s))
          1%g (ord_tuple 5) s5_starts_uniq).
under eq_map => i do rewrite morph1 perm1 tnth_ord_tuple.
have Hde : s5_players = enum 'I_5
  by apply: (inj_map val_inj); rewrite val_enum_ord.
by rewrite Hde map_tnth_enum.
Qed.

(** s5_endpoints_size — the verifier collects exactly ts_T'.+1 endpoints.
    @composes: s5_run_recovers. *)
Lemma s5_endpoints_size (s : 'I_5) :
  size (endpoints_of_trace (nth [::] (run_interp 150 (s5_procs s)).2 1))
  = (ts_T' s5_scheme).+1.
Proof. by rewrite s5_endpoints size_tuple. Qed.

(** s5_run_recovers — reconstructing the verifier's executed endpoints returns
    the dealt secret position s.
    @main correctness: the running S_5 protocol recovers the dealt secret
    position s : 'I_5 from the verifier's collected endpoints, reshaped to the
    scheme's ts_T'.+1-tuple via the size equality s5_endpoints_size. *)
Lemma s5_run_recovers (s : 'I_5) :
  ts_recon s5_scheme
    (tcast (s5_endpoints_size s)
       (in_tuple (endpoints_of_trace (nth [::] (run_interp 150 (s5_procs s)).2 1))))
  = s.
Proof.
have Heq : tcast (s5_endpoints_size s)
             (in_tuple (endpoints_of_trace (nth [::] (run_interp 150 (s5_procs s)).2 1)))
         = ts_encode s5_scheme s.
  apply: val_inj; rewrite [LHS]val_tcast in_tupleE; exact: s5_endpoints.
rewrite Heq.
exact: ts_correct (ts_encode_valid s5_scheme s).
Qed.
