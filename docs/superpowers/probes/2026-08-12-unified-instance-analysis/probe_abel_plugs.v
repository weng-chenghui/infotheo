(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_abel_plugs: the two abelian ExecutionPlugs and their observations    *)
(*                                                                            *)
(* Phase 0 probe for the unified-instance-analysis request, sections 6.3,     *)
(* 6.4, 9.2 and 9.3, over the revised profile abel_profileP of                *)
(* probe_abel_profile.v. Two plugs share the four-seat program flow: the      *)
(* secret-recovery plug deals ts_encode abel_ts s and recovers s, the         *)
(* shuffle-analysis plug deals identity content over a trivial run input and  *)
(* recovers the constant 2 : 'I_4 for every cut permutation.                  *)
(*                                                                            *)
(* Probe claims:                                                              *)
(*   abel_verifier_endpoints  == the six-process run's endpoint equation      *)
(*   abel_det_plug            == the secret-recovery plug, fuel 150           *)
(*   abel_det_recon           == recovery of every s : 'I_4 at every group cut*)
(*   abel_shuffle_plug        == the identity-content plug, fuel 150          *)
(*   abel_identity_recon_value== the constant 2 : 'I_4 it reconstructs        *)
(*   abel_reader              == the complete four-endpoint vector observer   *)
(*   abel_reader_inj          == that observer is globally injective          *)
(*   abel_det_observed        == the secret-recovery ObservedExecution        *)
(*   abel_shuffle_observed    == the shuffle-analysis ObservedExecution       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From infotheo Require Import variation_dist.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance abelian_word_collapse.
From pgg_smc Require Import abel_profile.
From uia_probe Require Import probe_abel_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The shared four-seat program flow                                      *)
(******************************************************************************)

(** abel_players — the four-seat participant list.
    @intent: the explicit four-element list of 'I_4 seat ordinals; a concrete
    list rather than enum 'I_4 lets the dealer's fold_senv reduce under
    vm_compute. *)
Definition abel_players : seq 'I_4 :=
  [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT].

(** abel_players_enumE — the participant list is the seat enumeration.
    @composes: abel_det_plug *)
Lemma abel_players_enumE :
  abel_players = enum 'I_(pi_T' (mp_PI abel_profileP)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** abel_verifier_endpoints — the verifier's executed endpoints of the
    six-process abelian run are the dealt content readout at the cut and the
    four starts.
    @composes: abel_det_endpoints, abel_shuffle_endpoints *)
Lemma abel_verifier_endpoints
    (g : seq 'I_(pgg_N' abel_M).+1 -> ('I_4 -> 'I_4))
    (w0 : pgg_gT abel_M)
    (st : 4.-tuple 'I_4) (Hst : uniq st) :
  let PI' := @MkPGGI abel_M 3 st Hst in
  endpoints_of_trace (nth [::] (run_interp 150 (erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer PI' (g committed) abel_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier PI' abel_players)
      ; mk_aproc (exchange_player PI' (@Ordinal 4 0 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 4 1 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 4 2 isT))
      ; mk_aproc (exchange_player PI' (@Ordinal 4 3 isT))])).2 1)
  = [seq g [::] (@pgg_rho abel_M w0 (tnth st i)) | i <- abel_players].
Proof. move=> PI'; rewrite /PI'; vm_compute; reflexivity. Qed.

(** abel_rhoE — the abelian monodromy is the identity inclusion.
    @composes: abel_shuffle_recon *)
Lemma abel_rhoE (w0 : pgg_gT abel_M) (x : 'I_4) : @pgg_rho abel_M w0 x = w0 x.
Proof. by []. Qed.

(** abel_static_tnth — entry i of the transported static observation is the
    observation at seat i's start.
    @composes: abel_det_recon, abel_shuffle_recon *)
Lemma abel_static_tnth (e : ExecutionPlug abel_profileP)
    (obs : ep_inputT e -> pgg_gT (mp_M abel_profileP)
             * 'I_(pgg_N' (mp_M abel_profileP)).+1
             -> 'I_(pgg_N' (mp_M abel_profileP)).+1)
    (x : ep_inputT e) (w0 : pgg_gT abel_M)
    (H : size (@exec_static_endpoints abel_profileP e obs x w0) = 4)
    (i : 'I_4) :
  tnth (tcast H (in_tuple (@exec_static_endpoints abel_profileP e obs x w0))) i
  = obs x (w0, tnth (pi_starts abel_PI) i).
Proof.
rewrite tcastE (tnth_nth ord0) /= /exec_static_endpoints (ep_playersE e).
by rewrite (nth_map i) ?nth_ord_enum // size_enum_ord ltn_ord.
Qed.

(** abel_decodeE — the plugs' decoder is the sum-mod reconstruction.
    @composes: abel_det_recon, abel_shuffle_recon *)
Lemma abel_decodeE (e : ExecutionPlug abel_profileP) (ep : seq 'I_4)
    (Hsz : size ep = (pi_T' (mp_PI abel_profileP)).+1)
    (Hsz' : size ep = (ts_T' abel_ts).+1) :
  @exec_decode abel_profileP e ep Hsz
  = ts_recon abel_ts (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(******************************************************************************)
(*     The secret-recovery plug                                               *)
(******************************************************************************)

(** abel_det_plug — the abelian secret-recovery execution plug.
    @intent: the execution layer over abel_profileP with run argument 'I_4,
    the seat/share bridge erefl at four seats and four shares, participant
    list abel_players, content the shares ts_encode abel_ts s of the dealt
    secret s and fuel 150. *)
Definition abel_det_plug : ExecutionPlug abel_profileP :=
  @dealer_secret_plug abel_profileP 'I_4 erefl abel_players abel_players_enumE
    (fun s _ => tnth (ts_encode abel_ts s)) 150.

(** abel_content_obs — the secret-recovery static observation.
    @intent: the share of the secret s at the cut image of a starting
    position, namely tnth (ts_encode abel_ts s) (pgg_rho w0 p). *)
Definition abel_content_obs (s : 'I_4)
    (p : pgg_gT (mp_M abel_profileP) * 'I_(pgg_N' (mp_M abel_profileP)).+1)
    : 'I_(pgg_N' (mp_M abel_profileP)).+1 :=
  tnth (ts_encode abel_ts s) (@pgg_rho (mp_M abel_profileP) p.1 p.2).

(** abel_det_procs_size — the derived run has six processes.
    @composes: abel_det_terminates *)
Lemma abel_det_procs_size (s : 'I_4) (w0 : pgg_gT abel_M) :
  size (@exec_procs abel_profileP abel_det_plug s w0 0) = 6.
Proof. by []. Qed.

(** abel_det_terminates — every process of the derived run reaches Finish.
    @composes: abel_det_observed *)
Lemma abel_det_terminates (s : 'I_4) (w0 : pgg_gT abel_M) :
  (@exec_run abel_profileP abel_det_plug s w0 0).1
  = nseq (size (@exec_procs abel_profileP abel_det_plug s w0 0)) Finish.
Proof. rewrite abel_det_procs_size; vm_compute; reflexivity. Qed.

(** abel_det_endpoints — the derived verifier endpoints are the static
    observation over the four seats.
    @composes: abel_det_observed *)
Lemma abel_det_endpoints (s : 'I_4) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profileP abel_det_plug s w0 0
  = @exec_static_endpoints abel_profileP abel_det_plug abel_content_obs s w0.
Proof.
have E : @exec_procs abel_profileP abel_det_plug s w0 0
  = erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer abel_PI
             ((fun _ => tnth (ts_encode abel_ts s)) committed)
             abel_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier abel_PI abel_players)
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 0 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 1 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 2 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 3 isT))] by [].
rewrite /exec_endpoints /exec_run E /exec_verifier_id.
rewrite (@abel_verifier_endpoints (fun _ => tnth (ts_encode abel_ts s))
           w0 (ord_tuple 4) abel_starts_uniq).
by [].
Qed.

(** abel_det_recon — decoding the static observation returns the dealt secret,
    for every secret and every cut in the group.
    @composes: abel_det_observed *)
Lemma abel_det_recon (s : 'I_4) (w0 : pgg_gT abel_M) :
  w0 \in pgg_G abel_M ->
  forall Hsz : size (@exec_static_endpoints abel_profileP abel_det_plug
                       abel_content_obs s w0) = (pi_T' (mp_PI abel_profileP)).+1,
  @exec_decode abel_profileP abel_det_plug
    (@exec_static_endpoints abel_profileP abel_det_plug abel_content_obs s w0)
    Hsz = s.
Proof.
move=> Hw0 Hsz.
rewrite (abel_decodeE abel_det_plug Hsz Hsz).
rewrite -[RHS](abel_sum_mod_perm_compatible Hw0 (ts_encode_valid abel_ts s)).
congr (ts_recon _ _); apply: eq_from_tnth => i.
by rewrite abel_static_tnth tnth_mktuple /abel_content_obs /= tnth_ord_tuple.
Qed.

(** abel_det_observed — the abelian secret-recovery observed execution.
    @intent: abel_profileP with plug abel_det_plug at process offset 0, static
    observation abel_content_obs and expected value the dealt secret. *)
Definition abel_det_observed : OE.ObservedExecution :=
  OE.MkObservedExecution abel_profileP abel_det_plug 0
    abel_content_obs (fun s : 'I_4 => s)
    abel_det_terminates abel_det_endpoints (@abel_det_recon).

(** abel_det_correct — termination, endpoint count and arbitrary-secret
    recovery of the executed secret-recovery run.
    @main correctness: the run of abel_det_plug reaches Finish at each of its
    six processes, collects one endpoint per seat, and decodes to the dealt
    secret s, for every s : 'I_4 and every cut w0 in the group. *)
Theorem abel_det_correct (s : 'I_4) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  [/\ (@exec_run abel_profileP abel_det_plug s w0 0).1
        = nseq (size (@exec_procs abel_profileP abel_det_plug s w0 0)) Finish,
      size (@exec_endpoints abel_profileP abel_det_plug s w0 0)
        = (pi_T' (mp_PI abel_profileP)).+1 &
      @exec_decode abel_profileP abel_det_plug
        (@exec_endpoints abel_profileP abel_det_plug s w0 0)
        (exec_endpoints_size (abel_det_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct abel_profileP abel_det_plug abel_content_obs
          (fun s : 'I_4 => s) s w0 0 (abel_det_terminates s w0)
          (abel_det_endpoints s w0) (abel_det_recon Hw0)).
Qed.

(******************************************************************************)
(*     The shuffle-analysis plug                                              *)
(******************************************************************************)

(** abel_shuffle_plug — the abelian shuffle-analysis execution plug.
    @intent: the execution layer over abel_profileP with trivial run argument
    unit, identity card content, participant list abel_players and fuel 150;
    its endpoints therefore record the cut permutation itself. *)
Definition abel_shuffle_plug : ExecutionPlug abel_profileP :=
  @dealer_secret_plug abel_profileP unit erefl abel_players abel_players_enumE
    (fun _ _ => idfun) 150.

(** abel_id_obs — the shuffle-analysis static observation.
    @intent: the cut image of a starting position, pgg_rho w0 p, with no
    dependence on the run argument. *)
Definition abel_id_obs (x : unit)
    (p : pgg_gT (mp_M abel_profileP) * 'I_(pgg_N' (mp_M abel_profileP)).+1)
    : 'I_(pgg_N' (mp_M abel_profileP)).+1 :=
  @pgg_rho (mp_M abel_profileP) p.1 p.2.

(** abel_identity_recon_value — the constant the identity-content run
    reconstructs.
    @intent: the ordinal 2 : 'I_4, the residue of 0 + 1 + 2 + 3 modulo 4. *)
Definition abel_identity_recon_value : 'I_4 := @Ordinal 4 2 isT.

(** abel_shuffle_procs_size — the derived run has six processes.
    @composes: abel_shuffle_terminates *)
Lemma abel_shuffle_procs_size (x : unit) (w0 : pgg_gT abel_M) :
  size (@exec_procs abel_profileP abel_shuffle_plug x w0 0) = 6.
Proof. by []. Qed.

(** abel_shuffle_terminates — every process of the derived run reaches Finish.
    @composes: abel_shuffle_observed *)
Lemma abel_shuffle_terminates (x : unit) (w0 : pgg_gT abel_M) :
  (@exec_run abel_profileP abel_shuffle_plug x w0 0).1
  = nseq (size (@exec_procs abel_profileP abel_shuffle_plug x w0 0)) Finish.
Proof. rewrite abel_shuffle_procs_size; vm_compute; reflexivity. Qed.

(** abel_shuffle_endpoints — the derived verifier endpoints are the cut images
    of the four starts.
    @composes: abel_shuffle_observed *)
Lemma abel_shuffle_endpoints (x : unit) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profileP abel_shuffle_plug x w0 0
  = @exec_static_endpoints abel_profileP abel_shuffle_plug abel_id_obs x w0.
Proof.
have E : @exec_procs abel_profileP abel_shuffle_plug x w0 0
  = erase_aprocs
    [:: mk_aproc (pgg_commit_prologue (fun committed =>
           exchange_dealer abel_PI ((fun _ => @idfun 'I_4) committed)
             abel_players [:: w0] 0) [::] [::])
      ; mk_aproc (exchange_verifier abel_PI abel_players)
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 0 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 1 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 2 isT))
      ; mk_aproc (exchange_player abel_PI (@Ordinal 4 3 isT))] by [].
rewrite /exec_endpoints /exec_run E /exec_verifier_id.
rewrite (@abel_verifier_endpoints (fun _ => @idfun 'I_4)
           w0 (ord_tuple 4) abel_starts_uniq).
by [].
Qed.

(** abel_shuffle_recon — decoding the identity-content static observation
    returns the constant 2 : 'I_4, for every cut in the group.
    @composes: abel_shuffle_observed *)
Lemma abel_shuffle_recon (x : unit) (w0 : pgg_gT abel_M) :
  w0 \in pgg_G abel_M ->
  forall Hsz : size (@exec_static_endpoints abel_profileP abel_shuffle_plug
                       abel_id_obs x w0) = (pi_T' (mp_PI abel_profileP)).+1,
  @exec_decode abel_profileP abel_shuffle_plug
    (@exec_static_endpoints abel_profileP abel_shuffle_plug abel_id_obs x w0)
    Hsz = abel_identity_recon_value.
Proof.
move=> Hw0 Hsz; rewrite (abel_decodeE abel_shuffle_plug Hsz Hsz).
apply: val_inj => /=.
under eq_bigr do rewrite (abel_static_tnth (e:=abel_shuffle_plug)).
under eq_bigr do rewrite /abel_id_obs /= tnth_ord_tuple abel_rhoE.
have E : (\sum_(i < 4) (w0 i : nat)) = \sum_(i < 4) (i : nat).
  by rewrite [RHS](reindex_perm w0).
by rewrite E !big_ord_recl big_ord0.
Qed.

(** abel_shuffle_observed — the abelian shuffle-analysis observed execution.
    @intent: abel_profileP with plug abel_shuffle_plug at process offset 0,
    static observation abel_id_obs and expected value the constant
    abel_identity_recon_value. *)
Definition abel_shuffle_observed : OE.ObservedExecution :=
  OE.MkObservedExecution abel_profileP abel_shuffle_plug 0
    abel_id_obs (fun _ : unit => abel_identity_recon_value)
    abel_shuffle_terminates abel_shuffle_endpoints (@abel_shuffle_recon).

(** abel_shuffle_correct — termination, endpoint count and constant recovery
    of the executed identity-content run.
    @main correctness: the run of abel_shuffle_plug reaches Finish at each of
    its six processes, collects one endpoint per seat, and decodes to
    abel_identity_recon_value for every cut w0 in the group. *)
Theorem abel_shuffle_correct (x : unit) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  [/\ (@exec_run abel_profileP abel_shuffle_plug x w0 0).1
        = nseq (size (@exec_procs abel_profileP abel_shuffle_plug x w0 0))
                Finish,
      size (@exec_endpoints abel_profileP abel_shuffle_plug x w0 0)
        = (pi_T' (mp_PI abel_profileP)).+1 &
      @exec_decode abel_profileP abel_shuffle_plug
        (@exec_endpoints abel_profileP abel_shuffle_plug x w0 0)
        (exec_endpoints_size (abel_shuffle_endpoints x w0))
      = abel_identity_recon_value].
Proof.
exact: (@exec_run_correct abel_profileP abel_shuffle_plug abel_id_obs
          (fun _ : unit => abel_identity_recon_value) x w0 0
          (abel_shuffle_terminates x w0) (abel_shuffle_endpoints x w0)
          (abel_shuffle_recon Hw0)).
Qed.

(******************************************************************************)
(*     The complete four-endpoint observer                                    *)
(******************************************************************************)

(** abel_reader — the complete four-endpoint vector of a cut.
    @intent: the tuple of the images of the four starting positions under a
    permutation, the finite observation the negative mixing result ends at. *)
Definition abel_reader (sigma : {perm 'I_4}) : 4.-tuple 'I_4 :=
  [tuple sigma (tnth (pi_starts abel_PI) i) | i < 4].

(** abel_reader_inj — the complete four-endpoint vector determines the cut.
    @main architecture: injective abel_reader, on all of {perm 'I_4} and not
    only on the generated group; a permutation of four sheets is determined by
    its images on all four starts. *)
Lemma abel_reader_inj : injective abel_reader.
Proof.
move=> x y H; apply/permP => z.
have := congr1 (fun t : 4.-tuple 'I_4 => tnth t z) H.
by rewrite /abel_reader !tnth_mktuple tnth_ord_tuple.
Qed.

(** abel_shuffle_static_readerE — the shuffle-analysis static observation is
    the complete four-endpoint vector of the cut.
    @composes: abel_shuffle_executed_readerE *)
Lemma abel_shuffle_static_readerE (x : unit) (w0 : pgg_gT abel_M) :
  @exec_static_endpoints abel_profileP abel_shuffle_plug abel_id_obs x w0
  = val (abel_reader w0).
Proof.
rewrite /exec_static_endpoints /abel_reader (ep_playersE abel_shuffle_plug).
by rewrite /=; apply: eq_map => i; rewrite tnth_ord_tuple.
Qed.

(** abel_shuffle_executed_readerE — the executed endpoints of the
    shuffle-analysis run are the complete four-endpoint vector of the cut.
    @main architecture: exec_endpoints abel_shuffle_plug x w0 0 =
    val (abel_reader w0), the equality connecting the static reader to the
    executed one. *)
Lemma abel_shuffle_executed_readerE (x : unit) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profileP abel_shuffle_plug x w0 0 = val (abel_reader w0).
Proof. by rewrite abel_shuffle_endpoints abel_shuffle_static_readerE. Qed.

(******************************************************************************)
(*     The remaining observer types read off the two plugs                    *)
(******************************************************************************)

(** abel_det_seat_endpointE — seat i's endpoint of the secret-recovery run is
    the share at the cut image of seat i's start.
    @main correctness: exec_seat_endpoint abel_det_plug s w0 0 i =
    abel_content_obs s (w0, tnth (pi_starts abel_PI) i). *)
Lemma abel_det_seat_endpointE (s : 'I_4) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profileP)).+1) :
  @exec_seat_endpoint abel_profileP abel_det_plug s w0 0 i
  = abel_content_obs s (w0, tnth (pi_starts (mp_PI abel_profileP)) i).
Proof. exact: (exec_seat_endpointE (abel_det_endpoints s w0) i). Qed.

(** abel_shuffle_seat_endpointE — seat i's endpoint of the shuffle-analysis
    run is the cut image of seat i's start.
    @main correctness: exec_seat_endpoint abel_shuffle_plug x w0 0 i =
    pgg_rho w0 (tnth (pi_starts abel_PI) i). *)
Lemma abel_shuffle_seat_endpointE (x : unit) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profileP)).+1) :
  @exec_seat_endpoint abel_profileP abel_shuffle_plug x w0 0 i
  = abel_id_obs x (w0, tnth (pi_starts (mp_PI abel_profileP)) i).
Proof. exact: (exec_seat_endpointE (abel_shuffle_endpoints x w0) i). Qed.

(** abel_det_coalition_endpointsE — a coalition's endpoint readings of the
    secret-recovery run are the shares at the cut images of its seats.
    @main correctness: the finfun sends a seat in C to the share of s at the
    cut image of that seat's start, and every seat outside C to ord0. *)
Lemma abel_det_coalition_endpointsE (s : 'I_4) (w0 : pgg_gT abel_M)
    (C : {set 'I_(pi_T' (mp_PI abel_profileP)).+1}) :
  @exec_coalition_endpoints abel_profileP abel_det_plug s w0 0 C
  = [ffun i => if i \in C
               then abel_content_obs s (w0, tnth (pi_starts (mp_PI abel_profileP)) i)
               else ord0].
Proof. exact: (exec_coalition_endpointsE (abel_det_endpoints s w0) C). Qed.

(** abel_det_verifier_traceE — the derived verifier row of the secret-recovery
    run is process row 1 of the interpreter output.
    @main architecture: exec_verifier_trace abel_det_plug s w0 0 = nth [::]
    (exec_run abel_det_plug s w0 0).2 1. *)
Lemma abel_det_verifier_traceE (s : 'I_4) (w0 : pgg_gT abel_M) :
  @exec_verifier_trace abel_profileP abel_det_plug s w0 0
  = nth [::] (@exec_run abel_profileP abel_det_plug s w0 0).2 1.
Proof. by []. Qed.

(** abel_shuffle_verifier_traceE — the derived verifier row of the
    shuffle-analysis run is process row 1 of the interpreter output.
    @main architecture: exec_verifier_trace abel_shuffle_plug x w0 0 =
    nth [::] (exec_run abel_shuffle_plug x w0 0).2 1. *)
Lemma abel_shuffle_verifier_traceE (x : unit) (w0 : pgg_gT abel_M) :
  @exec_verifier_trace abel_profileP abel_shuffle_plug x w0 0
  = nth [::] (@exec_run abel_profileP abel_shuffle_plug x w0 0).2 1.
Proof. by []. Qed.

(** abel_shuffle_raw_traceE — the derived raw seat row of the
    shuffle-analysis run is process row 2 + i of the interpreter output.
    @main architecture: exec_participant_trace abel_shuffle_plug x w0 0 i =
    nth [::] (exec_run abel_shuffle_plug x w0 0).2 (2 + i). *)
Lemma abel_shuffle_raw_traceE (x : unit) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profileP)).+1) :
  @exec_participant_trace abel_profileP abel_shuffle_plug x w0 0 i
  = nth [::] (@exec_run abel_profileP abel_shuffle_plug x w0 0).2 (2 + i).
Proof. by []. Qed.

(** abel_seat_countE — the revised profile's seat index type is 'I_4.
    @main architecture: (pi_T' (mp_PI abel_profileP)).+1 = 4. *)
Lemma abel_seat_countE : (pi_T' (mp_PI abel_profileP)).+1 = 4.
Proof. by []. Qed.

Print Assumptions abel_det_correct.
Print Assumptions abel_shuffle_correct.
Print Assumptions abel_det_observed.
Print Assumptions abel_shuffle_observed.
Print Assumptions abel_reader_inj.
Print Assumptions abel_shuffle_executed_readerE.
