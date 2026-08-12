(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* abelian_exec: the two ExecutionPlug values of the abelian instance         *)
(*                                                                            *)
(* The four-seat abelian instance carries two execution plugs over the same   *)
(* profile abel_profile. The secret-recovery plug takes the dealt secret 'I_4 *)
(* as its run argument and reads the shares ts_encode abel_ts of that secret; *)
(* the shuffle-analysis plug takes the unit as its run argument and reads the *)
(* identity content, so its endpoints record the cut permutation itself on   *)
(* all four starting positions. Both use the participant list abel_players    *)
(* and fuel 150.                                                             *)
(*                                                                            *)
(* The identity-content plug has no dealt secret, so it has no arbitrary-     *)
(* secret recovery statement. What it recovers is the constant                *)
(* abel_identity_recon_value, the sum-mod reconstruction of the identity      *)
(* layout, and that constant is the same for every cut permutation.           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   abel_players        == the four seat ordinals as an explicit list        *)
(*   abel_exec_plug      == the secret-recovery execution plug                *)
(*   abel_content_obs    == the secret-recovery static observation: the share *)
(*                          of the dealt secret at the cut image of a        *)
(*                          starting position                                *)
(*   abel_det_observed   == the ObservedExecution packing the secret-recovery *)
(*                          plug, its static observation and its three run    *)
(*                          facts at process offset 0                         *)
(*   abel_shuffle_plug   == the identity-content execution plug               *)
(*   abel_id_obs         == the identity-content static observation: the cut  *)
(*                          image of a starting position                      *)
(*   abel_identity_recon_value == the constant 2 : 'I_4 it reconstructs       *)
(*   abel_shuffle_observed == the ObservedExecution of the identity-content   *)
(*                          plug                                              *)
(*   abel_reader         == the complete four-endpoint vector of a cut        *)
(*                                                                            *)
(* Key results, one entry per @main declaration:                              *)
(*   abel_exec_endpoint_count == the secret-recovery run collects four        *)
(*                          endpoints                                         *)
(*   abel_exec_recovers  == the secret-recovery run decodes to the dealt      *)
(*                          secret                                            *)
(*   abel_exec_correct   == termination, endpoint count and recovery of the   *)
(*                          secret-recovery run                               *)
(*   abel_observed_recovers == the same recovery through the packaged         *)
(*                          observed execution                                *)
(*   abel_shuffle_endpoint_count == the identity-content run collects four    *)
(*                          endpoints                                         *)
(*   abel_shuffle_recovers == the identity-content run decodes to that        *)
(*                          constant                                          *)
(*   abel_shuffle_correct == termination, endpoint count and constant        *)
(*                          recovery of the identity-content run             *)
(*   abel_shuffle_observed_recovers == the same constant recovery through the *)
(*                          packaged observed execution                       *)
(*   abel_reader_inj     == the complete four-endpoint vector determines the  *)
(*                          cut                                               *)
(*   abel_shuffle_executed_readerE == the identity-content executed endpoints *)
(*                          are that vector                                   *)
(*   abel_exec_seat_endpointE == seat i's endpoint is the share at the cut    *)
(*                          image of seat i's start                           *)
(*   abel_shuffle_seat_endpointE == seat i's identity-content endpoint is the *)
(*                          cut image of seat i's start                       *)
(*   abel_exec_coalition_endpointsE == a coalition's endpoint readings are    *)
(*                          the shares at the cut images of its seats         *)
(*   abel_exec_verifier_traceE, abel_shuffle_verifier_traceE == the derived   *)
(*                          verifier rows are process row 1 of the run        *)
(*   abel_shuffle_raw_traceE == the derived raw seat row is process row 2 + i *)
(*   abel_seat_countE    == the profile's seat index type is 'I_4             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import rigidity_abelian_instance abel_profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* abel_M — the abelian two-generator monodromy template at N = 4, the
   Gen_PGGTypes form abel_profile is built over. *)
Local Notation abel_M := (@Gen_PGGTypes 1 2 abel_sigmas).

(******************************************************************************)
(*     The shared four-seat program flow                                      *)
(******************************************************************************)

(** abel_players — the four-seat participant list.
    @intent: the explicit four-element list of 'I_4 seat ordinals. It is a
    reduction cache: written this way rather than as enum 'I_4, the dealer's
    fold_senv reduces under vm_compute, which is what the interpreter facts
    below are proved by. *)
Definition abel_players : seq 'I_4 :=
  [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT].

(** abel_players_enumE — the participant list is the seat enumeration.
    @composes: abel_exec_plug, abel_shuffle_plug *)
Lemma abel_players_enumE :
  abel_players = enum 'I_(pi_T' (mp_PI abel_profile)).+1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

(** abel_verifier_endpoints — the verifier's executed endpoints of the
    six-process abelian run are the dealt content readout at the cut images of
    the starting positions.
    @composes: abel_exec_endpoints, abel_shuffle_endpoints *)
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
    @composes: abel_exec_recon, abel_shuffle_recon *)
Lemma abel_static_tnth (e : ExecutionPlug abel_profile)
    (obs : ep_inputT e -> pgg_gT (mp_M abel_profile)
             * 'I_(pgg_N' (mp_M abel_profile)).+1
             -> 'I_(pgg_N' (mp_M abel_profile)).+1)
    (x : ep_inputT e) (w0 : pgg_gT abel_M)
    (H : size (@exec_static_endpoints abel_profile e obs x w0) = 4)
    (i : 'I_4) :
  tnth (tcast H (in_tuple (@exec_static_endpoints abel_profile e obs x w0))) i
  = obs x (w0, tnth (pi_starts abel_PI) i).
Proof.
rewrite tcastE (tnth_nth ord0) /= /exec_static_endpoints (ep_playersE e).
by rewrite (nth_map i) ?nth_ord_enum // size_enum_ord ltn_ord.
Qed.

(** abel_decodeE — the plugs' decoder is the sum-mod reconstruction.
    @composes: abel_exec_recon, abel_shuffle_recon *)
Lemma abel_decodeE (e : ExecutionPlug abel_profile) (ep : seq 'I_4)
    (Hsz : size ep = (pi_T' (mp_PI abel_profile)).+1)
    (Hsz' : size ep = (ts_T' abel_ts).+1) :
  @exec_decode abel_profile e ep Hsz
  = ts_recon abel_ts (tcast Hsz' (in_tuple ep)).
Proof.
by rewrite /exec_decode /run_recover (eq_irrelevance (etrans Hsz _) Hsz').
Qed.

(******************************************************************************)
(*     The secret-recovery plug                                               *)
(******************************************************************************)

(** abel_exec_plug — the abelian secret-recovery execution plug.
    @intent: the execution layer over abel_profile with run argument 'I_4, the
    seat/share bridge erefl at four seats and four shares, participant list
    abel_players, content the shares ts_encode abel_ts s of the dealt secret s
    and fuel 150. The fuel is retained at 150 because the termination and
    endpoint facts below are computed at that fuel. *)
Definition abel_exec_plug : ExecutionPlug abel_profile :=
  @dealer_secret_plug abel_profile 'I_4 erefl abel_players abel_players_enumE
    (fun s _ => tnth (ts_encode abel_ts s)) 150.

(** abel_content_obs — the secret-recovery static observation.
    @intent: the share of the secret s at the cut image of a starting
    position, namely tnth (ts_encode abel_ts s) (pgg_rho w0 p). *)
Definition abel_content_obs (s : 'I_4)
    (p : pgg_gT (mp_M abel_profile) * 'I_(pgg_N' (mp_M abel_profile)).+1)
    : 'I_(pgg_N' (mp_M abel_profile)).+1 :=
  tnth (ts_encode abel_ts s) (@pgg_rho (mp_M abel_profile) p.1 p.2).

(** abel_exec_procs_size — the derived run has six processes.
    @composes: abel_exec_terminates *)
Lemma abel_exec_procs_size (s : 'I_4) (w0 : pgg_gT abel_M) :
  size (@exec_procs abel_profile abel_exec_plug s w0 0) = 6.
Proof. by []. Qed.

(** abel_exec_terminates — every process of the derived run reaches Finish.
    @composes: abel_det_observed, abel_exec_correct *)
Lemma abel_exec_terminates (s : 'I_4) (w0 : pgg_gT abel_M) :
  (@exec_run abel_profile abel_exec_plug s w0 0).1
  = nseq (size (@exec_procs abel_profile abel_exec_plug s w0 0)) Finish.
Proof. rewrite abel_exec_procs_size; vm_compute; reflexivity. Qed.

(** abel_exec_endpoints — the derived verifier endpoints are the static
    observation over the four seats.
    @composes: abel_det_observed, abel_exec_correct *)
Lemma abel_exec_endpoints (s : 'I_4) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profile abel_exec_plug s w0 0
  = @exec_static_endpoints abel_profile abel_exec_plug abel_content_obs s w0.
Proof.
have E : @exec_procs abel_profile abel_exec_plug s w0 0
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

(** abel_exec_endpoint_count — the secret-recovery run collects four endpoints.
    @main correctness: size (exec_endpoints abel_exec_plug s w0 0) = 4. *)
Lemma abel_exec_endpoint_count (s : 'I_4) (w0 : pgg_gT abel_M) :
  size (@exec_endpoints abel_profile abel_exec_plug s w0 0) = 4.
Proof. by rewrite (exec_endpoints_size (abel_exec_endpoints s w0)). Qed.

(** abel_exec_recon — decoding the static observation returns the dealt secret,
    for every secret and every cut in the group.
    @composes: abel_det_observed, abel_exec_recovers *)
Lemma abel_exec_recon (s : 'I_4) (w0 : pgg_gT abel_M) :
  w0 \in pgg_G abel_M ->
  forall Hsz : size (@exec_static_endpoints abel_profile abel_exec_plug
                       abel_content_obs s w0) = (pi_T' (mp_PI abel_profile)).+1,
  @exec_decode abel_profile abel_exec_plug
    (@exec_static_endpoints abel_profile abel_exec_plug abel_content_obs s w0)
    Hsz = s.
Proof.
move=> Hw0 Hsz.
rewrite (abel_decodeE abel_exec_plug Hsz Hsz).
rewrite -[RHS](abel_sum_mod_perm_compatible Hw0 (ts_encode_valid abel_ts s)).
congr (ts_recon _ _); apply: eq_from_tnth => i.
by rewrite abel_static_tnth tnth_mktuple /abel_content_obs /= tnth_ord_tuple.
Qed.

(** abel_exec_recovers — the secret-recovery run decodes to the dealt secret.
    @main correctness: exec_decode of the executed endpoints of the run of
    abel_exec_plug at secret s and cut w0 is s, for every s : 'I_4 and every
    cut w0 in the group. *)
Theorem abel_exec_recovers (s : 'I_4) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_exec_plug
    (@exec_endpoints abel_profile abel_exec_plug s w0 0)
    (exec_endpoints_size (abel_exec_endpoints s w0)) = s.
Proof.
exact: (@exec_run_recovers abel_profile abel_exec_plug abel_content_obs
          (fun s : 'I_4 => s) s w0 0 (abel_exec_endpoints s w0)
          (abel_exec_recon Hw0)).
Qed.

(** abel_exec_correct — termination, endpoint count and arbitrary-secret
    recovery of the executed secret-recovery run.
    @main correctness: the run of abel_exec_plug reaches Finish at each of its
    six processes, collects one endpoint per seat, and decodes to the dealt
    secret s, for every s : 'I_4 and every cut w0 in the group. *)
Theorem abel_exec_correct (s : 'I_4) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  [/\ (@exec_run abel_profile abel_exec_plug s w0 0).1
        = nseq (size (@exec_procs abel_profile abel_exec_plug s w0 0)) Finish,
      size (@exec_endpoints abel_profile abel_exec_plug s w0 0)
        = (pi_T' (mp_PI abel_profile)).+1 &
      @exec_decode abel_profile abel_exec_plug
        (@exec_endpoints abel_profile abel_exec_plug s w0 0)
        (exec_endpoints_size (abel_exec_endpoints s w0)) = s].
Proof.
exact: (@exec_run_correct abel_profile abel_exec_plug abel_content_obs
          (fun s : 'I_4 => s) s w0 0 (abel_exec_terminates s w0)
          (abel_exec_endpoints s w0) (abel_exec_recon Hw0)).
Qed.

(** abel_det_observed — the abelian secret-recovery observed execution.
    @intent: abel_profile with plug abel_exec_plug at process offset 0, static
    observation abel_content_obs and expected value the dealt secret; the three
    run facts are abel_exec_terminates, abel_exec_endpoints and
    abel_exec_recon. *)
Definition abel_det_observed : OE.ObservedExecution :=
  OE.MkObservedExecution abel_profile abel_exec_plug 0
    abel_content_obs (fun s : 'I_4 => s)
    abel_exec_terminates abel_exec_endpoints (@abel_exec_recon).

(** abel_observed_recovers — the packaged secret-recovery run decodes to the
    dealt secret.
    @main correctness: exec_decode of the executed endpoints of
    abel_det_observed at secret s and cut w0 is s, for every cut w0 in the
    group. *)
Theorem abel_observed_recovers (s : 'I_4) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_exec_plug
    (@exec_endpoints abel_profile abel_exec_plug s w0 0)
    (OE.oe_endpoints_size abel_det_observed s w0) = s.
Proof. exact: (OE.oe_run_recovers abel_det_observed s w0 Hw0). Qed.

(******************************************************************************)
(*     The shuffle-analysis plug                                              *)
(******************************************************************************)

(** abel_shuffle_plug — the abelian shuffle-analysis execution plug.
    @intent: the execution layer over abel_profile with trivial run argument
    unit, identity card content, participant list abel_players and fuel 150;
    its endpoints therefore record the cut permutation itself. The fuel is
    retained at 150 because the termination and endpoint facts below are
    computed at that fuel. *)
Definition abel_shuffle_plug : ExecutionPlug abel_profile :=
  @dealer_secret_plug abel_profile unit erefl abel_players abel_players_enumE
    (fun _ _ => idfun) 150.

(** abel_id_obs — the shuffle-analysis static observation.
    @intent: the cut image of a starting position, pgg_rho w0 p, with no
    dependence on the run argument. *)
Definition abel_id_obs (x : unit)
    (p : pgg_gT (mp_M abel_profile) * 'I_(pgg_N' (mp_M abel_profile)).+1)
    : 'I_(pgg_N' (mp_M abel_profile)).+1 :=
  @pgg_rho (mp_M abel_profile) p.1 p.2.

(** abel_identity_recon_value — the constant the identity-content run
    reconstructs.
    @intent: the ordinal 2 : 'I_4, the residue of 0 + 1 + 2 + 3 modulo 4, that
    being the sum-mod reconstruction of the identity layout. *)
Definition abel_identity_recon_value : 'I_4 := @Ordinal 4 2 isT.

(** abel_shuffle_procs_size — the derived run has six processes.
    @composes: abel_shuffle_terminates *)
Lemma abel_shuffle_procs_size (x : unit) (w0 : pgg_gT abel_M) :
  size (@exec_procs abel_profile abel_shuffle_plug x w0 0) = 6.
Proof. by []. Qed.

(** abel_shuffle_terminates — every process of the derived run reaches Finish.
    @composes: abel_shuffle_observed, abel_shuffle_correct *)
Lemma abel_shuffle_terminates (x : unit) (w0 : pgg_gT abel_M) :
  (@exec_run abel_profile abel_shuffle_plug x w0 0).1
  = nseq (size (@exec_procs abel_profile abel_shuffle_plug x w0 0)) Finish.
Proof. rewrite abel_shuffle_procs_size; vm_compute; reflexivity. Qed.

(** abel_shuffle_endpoints — the derived verifier endpoints are the cut images
    of the four starts.
    @composes: abel_shuffle_observed, abel_shuffle_correct *)
Lemma abel_shuffle_endpoints (x : unit) (w0 : pgg_gT abel_M) :
  @exec_endpoints abel_profile abel_shuffle_plug x w0 0
  = @exec_static_endpoints abel_profile abel_shuffle_plug abel_id_obs x w0.
Proof.
have E : @exec_procs abel_profile abel_shuffle_plug x w0 0
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

(** abel_shuffle_endpoint_count — the identity-content run collects four
    endpoints.
    @main correctness: size (exec_endpoints abel_shuffle_plug x w0 0) = 4. *)
Lemma abel_shuffle_endpoint_count (x : unit) (w0 : pgg_gT abel_M) :
  size (@exec_endpoints abel_profile abel_shuffle_plug x w0 0) = 4.
Proof. by rewrite (exec_endpoints_size (abel_shuffle_endpoints x w0)). Qed.

(** abel_shuffle_recon — decoding the identity-content static observation
    returns the constant 2 : 'I_4, for every cut in the group.
    @composes: abel_shuffle_observed, abel_shuffle_recovers *)
Lemma abel_shuffle_recon (x : unit) (w0 : pgg_gT abel_M) :
  w0 \in pgg_G abel_M ->
  forall Hsz : size (@exec_static_endpoints abel_profile abel_shuffle_plug
                       abel_id_obs x w0) = (pi_T' (mp_PI abel_profile)).+1,
  @exec_decode abel_profile abel_shuffle_plug
    (@exec_static_endpoints abel_profile abel_shuffle_plug abel_id_obs x w0)
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

(** abel_shuffle_recovers — the identity-content run decodes to the constant
    abel_identity_recon_value.
    @main correctness: exec_decode of the executed endpoints of the run of
    abel_shuffle_plug at cut w0 is abel_identity_recon_value, for every cut w0
    in the group; the identity-content plug deals no secret, so this is a
    constant recovery statement and not an arbitrary-secret one. *)
Theorem abel_shuffle_recovers (x : unit) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_shuffle_plug
    (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
    (exec_endpoints_size (abel_shuffle_endpoints x w0))
  = abel_identity_recon_value.
Proof.
exact: (@exec_run_recovers abel_profile abel_shuffle_plug abel_id_obs
          (fun _ : unit => abel_identity_recon_value) x w0 0
          (abel_shuffle_endpoints x w0) (abel_shuffle_recon Hw0)).
Qed.

(** abel_shuffle_correct — termination, endpoint count and constant recovery
    of the executed identity-content run.
    @main correctness: the run of abel_shuffle_plug reaches Finish at each of
    its six processes, collects one endpoint per seat, and decodes to
    abel_identity_recon_value for every cut w0 in the group. *)
Theorem abel_shuffle_correct (x : unit) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  [/\ (@exec_run abel_profile abel_shuffle_plug x w0 0).1
        = nseq (size (@exec_procs abel_profile abel_shuffle_plug x w0 0))
                Finish,
      size (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
        = (pi_T' (mp_PI abel_profile)).+1 &
      @exec_decode abel_profile abel_shuffle_plug
        (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
        (exec_endpoints_size (abel_shuffle_endpoints x w0))
      = abel_identity_recon_value].
Proof.
exact: (@exec_run_correct abel_profile abel_shuffle_plug abel_id_obs
          (fun _ : unit => abel_identity_recon_value) x w0 0
          (abel_shuffle_terminates x w0) (abel_shuffle_endpoints x w0)
          (abel_shuffle_recon Hw0)).
Qed.

(** abel_shuffle_observed — the abelian shuffle-analysis observed execution.
    @intent: abel_profile with plug abel_shuffle_plug at process offset 0,
    static observation abel_id_obs and expected value the constant
    abel_identity_recon_value; the three run facts are
    abel_shuffle_terminates, abel_shuffle_endpoints and abel_shuffle_recon. *)
Definition abel_shuffle_observed : OE.ObservedExecution :=
  OE.MkObservedExecution abel_profile abel_shuffle_plug 0
    abel_id_obs (fun _ : unit => abel_identity_recon_value)
    abel_shuffle_terminates abel_shuffle_endpoints (@abel_shuffle_recon).

(** abel_shuffle_observed_recovers — the packaged identity-content run decodes
    to the constant abel_identity_recon_value.
    @main correctness: exec_decode of the executed endpoints of
    abel_shuffle_observed at cut w0 is abel_identity_recon_value, for every cut
    w0 in the group. *)
Theorem abel_shuffle_observed_recovers (x : unit) (w0 : pgg_gT abel_M)
    (Hw0 : w0 \in pgg_G abel_M) :
  @exec_decode abel_profile abel_shuffle_plug
    (@exec_endpoints abel_profile abel_shuffle_plug x w0 0)
    (OE.oe_endpoints_size abel_shuffle_observed x w0)
  = abel_identity_recon_value.
Proof. exact: (OE.oe_run_recovers abel_shuffle_observed x w0 Hw0). Qed.

(******************************************************************************)
(*     The complete four-endpoint observer                                    *)
(******************************************************************************)

(** abel_reader — the complete four-endpoint vector of a cut.
    @intent: the tuple of the images of the four starting positions under a
    permutation, with carrier 4.-tuple 'I_4; the finite observation the
    abelian mixing statements are read at. *)
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
  @exec_static_endpoints abel_profile abel_shuffle_plug abel_id_obs x w0
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
  @exec_endpoints abel_profile abel_shuffle_plug x w0 0 = val (abel_reader w0).
Proof. by rewrite abel_shuffle_endpoints abel_shuffle_static_readerE. Qed.

(******************************************************************************)
(*     The remaining observer types read off the two plugs                    *)
(******************************************************************************)

(** abel_exec_seat_endpointE — seat i's endpoint of the secret-recovery run is
    the share at the cut image of seat i's start.
    @main correctness: exec_seat_endpoint abel_exec_plug s w0 0 i =
    abel_content_obs s (w0, tnth (pi_starts abel_PI) i). *)
Lemma abel_exec_seat_endpointE (s : 'I_4) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profile)).+1) :
  @exec_seat_endpoint abel_profile abel_exec_plug s w0 0 i
  = abel_content_obs s (w0, tnth (pi_starts (mp_PI abel_profile)) i).
Proof. exact: (exec_seat_endpointE (abel_exec_endpoints s w0) i). Qed.

(** abel_shuffle_seat_endpointE — seat i's endpoint of the shuffle-analysis
    run is the cut image of seat i's start.
    @main correctness: exec_seat_endpoint abel_shuffle_plug x w0 0 i =
    pgg_rho w0 (tnth (pi_starts abel_PI) i). *)
Lemma abel_shuffle_seat_endpointE (x : unit) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profile)).+1) :
  @exec_seat_endpoint abel_profile abel_shuffle_plug x w0 0 i
  = abel_id_obs x (w0, tnth (pi_starts (mp_PI abel_profile)) i).
Proof. exact: (exec_seat_endpointE (abel_shuffle_endpoints x w0) i). Qed.

(** abel_exec_coalition_endpointsE — a coalition's endpoint readings of the
    secret-recovery run are the shares at the cut images of its seats.
    @main correctness: the finfun sends a seat in C to the share of s at the
    cut image of that seat's start, and every seat outside C to ord0. *)
Lemma abel_exec_coalition_endpointsE (s : 'I_4) (w0 : pgg_gT abel_M)
    (C : {set 'I_(pi_T' (mp_PI abel_profile)).+1}) :
  @exec_coalition_endpoints abel_profile abel_exec_plug s w0 0 C
  = [ffun i => if i \in C
               then abel_content_obs s
                      (w0, tnth (pi_starts (mp_PI abel_profile)) i)
               else ord0].
Proof. exact: (exec_coalition_endpointsE (abel_exec_endpoints s w0) C). Qed.

(** abel_exec_verifier_traceE — the derived verifier row of the
    secret-recovery run is process row 1 of the interpreter output. The row is
    a message list and is navigation only: it is not a finite random variable.
    @main architecture: exec_verifier_trace abel_exec_plug s w0 0 = nth [::]
    (exec_run abel_exec_plug s w0 0).2 1. *)
Lemma abel_exec_verifier_traceE (s : 'I_4) (w0 : pgg_gT abel_M) :
  @exec_verifier_trace abel_profile abel_exec_plug s w0 0
  = nth [::] (@exec_run abel_profile abel_exec_plug s w0 0).2 1.
Proof. by []. Qed.

(** abel_shuffle_verifier_traceE — the derived verifier row of the
    shuffle-analysis run is process row 1 of the interpreter output. The row is
    a message list and is navigation only: it is not a finite random variable.
    @main architecture: exec_verifier_trace abel_shuffle_plug x w0 0 =
    nth [::] (exec_run abel_shuffle_plug x w0 0).2 1. *)
Lemma abel_shuffle_verifier_traceE (x : unit) (w0 : pgg_gT abel_M) :
  @exec_verifier_trace abel_profile abel_shuffle_plug x w0 0
  = nth [::] (@exec_run abel_profile abel_shuffle_plug x w0 0).2 1.
Proof. by []. Qed.

(** abel_shuffle_raw_traceE — the derived raw seat row of the
    shuffle-analysis run is process row 2 + i of the interpreter output. The
    row is a message list and is navigation only: it is not a finite random
    variable.
    @main architecture: exec_participant_trace abel_shuffle_plug x w0 0 i =
    nth [::] (exec_run abel_shuffle_plug x w0 0).2 (2 + i). *)
Lemma abel_shuffle_raw_traceE (x : unit) (w0 : pgg_gT abel_M)
    (i : 'I_(pi_T' (mp_PI abel_profile)).+1) :
  @exec_participant_trace abel_profile abel_shuffle_plug x w0 0 i
  = nth [::] (@exec_run abel_profile abel_shuffle_plug x w0 0).2 (2 + i).
Proof. by []. Qed.

(** abel_seat_countE — the profile's seat index type is 'I_4.
    @main architecture: (pi_T' (mp_PI abel_profile)).+1 = 4. *)
Lemma abel_seat_countE : (pi_T' (mp_PI abel_profile)).+1 = 4.
Proof. by []. Qed.
