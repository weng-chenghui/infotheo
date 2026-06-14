(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* S_5 x S_5 operational realization (position model)                         *)
(*                                                                            *)
(* The dealer deals the shares ts_encode s5x5_scheme s of a secret            *)
(* position s : 'I_10, with the identity cut and starts = ord_tuple 10. The   *)
(* verifier collects the ten endpoints; reconstruction returns s. This is the *)
(* position-model analogue of den_boer_run, with an empty input prologue.     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
Require Import pgg_interface.
From pgg_smc Require Import pgg_s5x5 s5x5_profile rigidity_s5x5_instance.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.
From pgg_reconstruct Require Import product_threshold.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** s5x5_scheme — the S_5 x S_5 product sum-mod sharing scheme on 'I_10,
    convertible to rp_scheme s5x5_plug.
    @intent: the threshold scheme the dealer shares and the verifier
    reconstructs; the two-pile product of the five-party sum-mod scheme. Named
    directly (rather than rp_scheme s5x5_plug) so the operational lemmas stay
    closed under the global context: s5x5_plug bundles the genus gap field
    s5x5_cs_gap, whose proof uses the justified group-order fact
    s5x5_group_order_eq, which is never exercised by the run. *)
Definition s5x5_scheme : ThresholdScheme 'I_10 'I_10 :=
  @product_scheme 3 3 (@sum_mod_scheme 3 4) (@sum_mod_scheme 3 4).

(** s5x5_scheme_plug — s5x5_scheme is the scheme dealt by the s5x5 plug.
    @composes: s5x5_endpoints. *)
Lemma s5x5_scheme_plug : rp_scheme s5x5_plug = s5x5_scheme.
Proof. by []. Qed.

(** s5x5_players — the ten-player list for the S_5 x S_5 dealing phase.
    @intent: the explicit ten-element list of 'I_10 player ordinals; a concrete
    list (rather than enum 'I_10) lets the dealer's fold_senv reduce under
    vm_compute. Used-by: s5x5_dealer_run, s5x5_saprocs. *)
Definition s5x5_players : seq 'I_(pi_T' s5x5_PI).+1 :=
  [:: @Ordinal 10 0 isT; @Ordinal 10 1 isT; @Ordinal 10 2 isT;
      @Ordinal 10 3 isT; @Ordinal 10 4 isT; @Ordinal 10 5 isT;
      @Ordinal 10 6 isT; @Ordinal 10 7 isT; @Ordinal 10 8 isT;
      @Ordinal 10 9 isT].

(** s5x5_dealer_run — the S_5 x S_5 dealer via the generic input-encoding dealer
    (identity cut, empty input prologue, position-model content reading the
    shares ts_encode s5x5_scheme s of the dealt secret s).
    @intent: deals the encoded shares of the secret position s; the empty
    prologue [::] makes this a pure position-model dealer. Used-by:
    s5x5_saprocs. *)
Definition s5x5_dealer_run (s : 'I_10) :=
  dealer_with_input_encoding s5x5_PI
    (fun _ => tnth (ts_encode s5x5_scheme s))
    [::] s5x5_players 0.

(** s5x5_saprocs — dealer ++ verifier ++ ten players, ordered by process id
    (0..11). @intent: the twelve session-typed processes of one S_5 x S_5 run.
    Used-by: s5x5_procs. *)
Definition s5x5_saprocs (s : 'I_10) :=
  [:: mk_aproc (s5x5_dealer_run s)
    ; mk_aproc (exchange_verifier s5x5_PI s5x5_players)
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 0 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 1 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 2 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 3 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 4 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 5 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 6 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 7 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 8 isT))
    ; mk_aproc (exchange_player s5x5_PI (@Ordinal 10 9 isT))].

(** s5x5_procs — the erased process list fed to the interpreter. *)
Definition s5x5_procs (s : 'I_10) := erase_aprocs (s5x5_saprocs s).

(** s5x5_run_terminates — every process reaches Finish (12 procs). *)
Lemma s5x5_run_terminates (s : 'I_10) :
  (run_interp 300 (s5x5_procs s)).1 = nseq 12 Finish.
Proof. by vm_compute. Qed.

(** s5x5_verifier_endpoints — the verifier's executed endpoints are the dealt
    content readout at the deck cut and starts, one per player.
    @composes: s5x5_endpoints. *)
Lemma s5x5_verifier_endpoints
    (g : seq 'I_(pgg_N' s5x5_M).+1 -> ('I_10 -> 'I_10))
    (w0 : pgg_gT s5x5_M)
    (st : 10.-tuple 'I_10) (Hst : uniq st) :
  let PI' := @MkPGGI s5x5_M 9 st Hst in
  endpoints_of_trace (nth [::] (run_interp 300 (erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer PI' (g committed) s5x5_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier PI' s5x5_players)
      ; mk_aproc (exchange_player PI' (@Ordinal 10 0 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 1 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 2 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 3 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 4 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 5 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 6 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 7 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 8 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 10 9 isT))])).2 1)
  = [seq g [::] (@pgg_rho s5x5_M w0 (tnth st i)) | i <- s5x5_players].
Proof. move=> PI'; rewrite /PI'; vm_compute; reflexivity. Qed.

(** s5x5_endpoints — the verifier's collected endpoints are the dealt shares of
    the secret position s (identity cut, ord_tuple starts).
    @composes: s5x5_run_recovers. *)
Lemma s5x5_endpoints (s : 'I_10) :
  endpoints_of_trace (nth [::] (run_interp 300 (s5x5_procs s)).2 1)
  = val (ts_encode s5x5_scheme s).
Proof.
rewrite /s5x5_procs /s5x5_saprocs /s5x5_dealer_run
        /dealer_with_input_encoding /identity_deck.
rewrite (@s5x5_verifier_endpoints
          (fun=> tnth (ts_encode s5x5_scheme s))
          1%g (ord_tuple 10) s5x5_starts_uniq).
under eq_map => i do rewrite morph1 perm1 tnth_ord_tuple.
have Hde : s5x5_players = enum 'I_10
  by apply: (inj_map val_inj); rewrite val_enum_ord.
by rewrite Hde map_tnth_enum.
Qed.

(** s5x5_endpoints_size — the verifier collects exactly ts_T'.+1 endpoints.
    @composes: s5x5_run_recovers. *)
Lemma s5x5_endpoints_size (s : 'I_10) :
  size (endpoints_of_trace (nth [::] (run_interp 300 (s5x5_procs s)).2 1))
  = (ts_T' s5x5_scheme).+1.
Proof. by rewrite s5x5_endpoints size_tuple. Qed.

(** s5x5_run_recovers — reconstructing the verifier's executed endpoints returns
    the dealt secret position s.
    @main correctness: the running S_5 x S_5 protocol recovers the dealt secret
    position s : 'I_10 from the verifier's collected endpoints, reshaped to the
    scheme's ts_T'.+1-tuple via the size equality s5x5_endpoints_size. *)
Lemma s5x5_run_recovers (s : 'I_10) :
  ts_recon s5x5_scheme
    (tcast (s5x5_endpoints_size s)
       (in_tuple (endpoints_of_trace (nth [::] (run_interp 300 (s5x5_procs s)).2 1))))
  = s.
Proof.
have Heq : tcast (s5x5_endpoints_size s)
             (in_tuple (endpoints_of_trace (nth [::] (run_interp 300 (s5x5_procs s)).2 1)))
         = ts_encode s5x5_scheme s.
  apply: val_inj; rewrite [LHS]val_tcast in_tupleE; exact: s5x5_endpoints.
rewrite Heq.
exact: ts_correct (ts_encode_valid s5x5_scheme s).
Qed.
