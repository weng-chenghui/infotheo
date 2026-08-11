(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-G (computation half): vm_compute over the generic participant      *)
(* enumeration                                                                *)
(*                                                                            *)
(* The EPP record and the derived section are those of probe_c_pgl27_exec.v   *)
(* and probe_d_fivecard_exec.v, trimmed to the run (players, input            *)
(* identifiers, dealer, process lists, run) and extended by one family:       *)
(* epp_saprocs_at / epp_procs_at / epp_run_at take the participant list as an *)
(* argument, so the same generic assembly can be run at enum 'I_T.+1 and at   *)
(* an instance's concrete list. epp_run_atE shows epp_run is the _at family   *)
(* at epp_players, by conversion.                                            *)
(*                                                                            *)
(* Measured (numbers in the timing block at the end of the file):             *)
(*                                                                            *)
(*  1. ENUM-DIRECT TERMINATION DOES NOT REDUCE. Both direct proofs, at the    *)
(*     PGL carrier and at the five-card carrier, were attempted as            *)
(*     Proof. by vm_compute. Qed. over epp_run (that is, over epp_players =   *)
(*     enum 'I_T.+1) and both were killed. They are not in this file; the     *)
(*     attempted statements are recorded verbatim in the block "Attempted and *)
(*     killed" below.                                                         *)
(*                                                                            *)
(*  2. THE BLOCKER IS THE ENUMERATION, NOT THE ASSEMBLY, THE FUEL OR THE      *)
(*     PARTY INDEX. Eval vm_compute in (enum 'I_8) returns a STUCK term of    *)
(*     385088 characters: the head is Finite.enum applied to the ordinal      *)
(*     Finite class record, and its leaves are match idP with ReflectT ... ,  *)
(*     idP being Qed-opaque. size (enum 'I_8) is stuck the same way (387979   *)
(*     characters), so the VM cannot even learn the LENGTH of the participant *)
(*     list, hence not the length of the process list. run_interp then walks  *)
(*     a list whose tail is a 385 KB stuck term at fuel 220 (PGL) and 100     *)
(*     (five-card).                                                          *)
(*                                                                            *)
(*  3. THE SAME GENERIC ASSEMBLY AT A CONCRETE LIST REDUCES. Replacing only   *)
(*     the participant list, epp_run_at pgl27_players and epp_run_at          *)
(*     den_boer_players, leaves the enum the single changed token, and both   *)
(*     pgl_concrete_terminates and fc_concrete_terminates close by            *)
(*     vm_compute in about a tenth of a second. The generic dealer, the       *)
(*     generic verifier, the mapped players, the appended commit prologue and *)
(*     the record projection ep_fuel all reduce.                              *)
(*                                                                            *)
(*  4. ASYMMETRY BETWEEN THE TWO INPUT MODES. The empty-input PGL attempt hit *)
(*     the 70 s session limit and was killed by timeout; the committed-input  *)
(*     five-card attempt killed the PET process outright (no response) inside *)
(*     the same window, at the friendlier literal P_idx = 0 and at the        *)
(*     smaller fuel 100. The commit prologue is appended AFTER the stuck      *)
(*     mapped-player segment, so the interpreter's process table is stuck in  *)
(*     the middle and the two committing parties are reached only through it. *)
(*     Committed input is therefore the worse of the two under a stuck        *)
(*     participant list, not the better.                                      *)
(*                                                                            *)
(*  5. P_idx IS NOT INVOLVED. fc_concrete_terminates quantifies P_idx and     *)
(*     still reduces, while the killed five-card attempt used the literal 0.  *)
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
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The execution adapter (probe_c_pgl27_exec.v, probe_d_fivecard_exec.v)  *)
(******************************************************************************)

(** EPP — the execution adapter over a MonodromyProfile.
    Kind: interface.
    A value of this type carries the run argument type ep_inputT, the seat/share
    bridge ep_players_bridge, the card/share bridge ep_cards_bridge, the content
    readout ep_content, the input processes ep_input_procs and the interpreter
    fuel ep_fuel. *)
Record EPP (R : realType) (mp : MonodromyProfile R) := MkEPP {
  ep_inputT         : Type ;
  ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ;
  ep_cards_bridge   : (pgg_N' (mp_M mp)).+1
                        = (ts_T' (rp_scheme (mp_plug mp))).+1 ;
  ep_content        : ep_inputT -> seq 'I_(pgg_N' (mp_M mp)).+1
                        -> ('I_(pgg_N' (mp_M mp)).+1
                            -> 'I_(pgg_N' (mp_M mp)).+1) ;
  ep_input_procs    : ep_inputT
                        -> seq (aproc pgg_dtype
                                  (pgg_data (pgg_N' (mp_M mp)).+1)) ;
  ep_fuel           : nat ;
}.

(******************************************************************************)
(*     The run derived from the adapter                                       *)
(******************************************************************************)

Section execution_of_profile.

Variable R : realType.
Variable mp : MonodromyProfile R.
Variable e : EPP mp.

(** epp_players — the participant list of the run.
    @intent: the enumeration of the (pi_T' (mp_PI mp)).+1 seats. *)
Definition epp_players : seq 'I_(pi_T' (mp_PI mp)).+1 :=
  enum 'I_(pi_T' (mp_PI mp)).+1.

(** epp_input_ids — the party identifiers of the input processes.
    @intent: iota (pi_T' (mp_PI mp)).+3 (size (ep_input_procs e x)), the
    identifiers following the dealer, the verifier and the seats. *)
Definition epp_input_ids (x : ep_inputT e) : seq nat :=
  iota (pi_T' (mp_PI mp)).+3 (size (e.(ep_input_procs) x)).

(* The _at family below is the measurement instrument: it is the assembly of
   epp_saprocs with the participant list abstracted, so that enum 'I_T.+1 and
   an instance's concrete list differ by one token and nothing else. *)

(** epp_saprocs_at — the session-typed process list of the run over a given
    participant list.
    @intent: dealer, verifier, one player per entry of ps, then the input
    processes, in process-identifier order. *)
Definition epp_saprocs_at (ps : seq 'I_(pi_T' (mp_PI mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) :=
  mk_aproc (dealer_with_input_encoding (mp_PI mp) (e.(ep_content) x) [:: w0]
              (epp_input_ids x) ps P_idx)
    :: mk_aproc (exchange_verifier (mp_PI mp) ps)
    :: [seq mk_aproc (exchange_player (mp_PI mp) i) | i <- ps]
       ++ e.(ep_input_procs) x.

(** epp_procs_at — the erased process list over a given participant list.
    @intent: the plain-proc image of epp_saprocs_at. *)
Definition epp_procs_at (ps : seq 'I_(pi_T' (mp_PI mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  erase_aprocs (epp_saprocs_at ps x w0 P_idx).

(** epp_run_at — the interpreter result over a given participant list.
    @intent: run_interp at ep_fuel e on epp_procs_at. *)
Definition epp_run_at (ps : seq 'I_(pi_T' (mp_PI mp)).+1)
    (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (epp_procs_at ps x w0 P_idx).

(** epp_dealer — the dealer of the run.
    @intent: dealer_with_input_encoding at mp_PI mp with the adapter's content
    readout, the singleton deck [:: w0], the input identifiers and the seats. *)
Definition epp_dealer (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  dealer_with_input_encoding (mp_PI mp) (e.(ep_content) x) [:: w0]
    (epp_input_ids x) epp_players P_idx.

(** epp_saprocs — the session-typed process list of the run.
    @intent: dealer, verifier, one player per seat, then the input processes, in
    process-identifier order. *)
Definition epp_saprocs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' (mp_M mp)).+1)) :=
  mk_aproc (epp_dealer x w0 P_idx)
    :: mk_aproc (exchange_verifier (mp_PI mp) epp_players)
    :: [seq mk_aproc (exchange_player (mp_PI mp) i) | i <- epp_players]
       ++ e.(ep_input_procs) x.

(** epp_procs — the erased process list.
    @intent: the plain-proc image of epp_saprocs. *)
Definition epp_procs (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  erase_aprocs (epp_saprocs x w0 P_idx).

(** epp_run — the interpreter result.
    @intent: run_interp at ep_fuel e on epp_procs, a pair of the final process
    states and the per-process traces. *)
Definition epp_run (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :=
  run_interp e.(ep_fuel) (epp_procs x w0 P_idx).

(** epp_run_atE — the run is the participant-list-indexed run at epp_players.
    @main architecture: epp_run x w0 P_idx = epp_run_at epp_players x w0 P_idx,
    by conversion; the two paths compared in this file differ only in the
    participant list supplied to epp_run_at. *)
Lemma epp_run_atE (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) (P_idx : nat) :
  epp_run x w0 P_idx = epp_run_at epp_players x w0 P_idx.
Proof. by []. Qed.

End execution_of_profile.

(******************************************************************************)
(*     The adapter filled at pgl27_profile (empty input)                      *)
(******************************************************************************)

Section pgl27_execution.

Variable R : realType.

Let mpP : MonodromyProfile R := pgl27_profile R.

(** pgl_epp — the PGL(2,7) execution adapter.
    @intent: run argument bool, both bridges erefl at 7 seats, 7 shares and 8
    cards, content the shares ts_encode orbit_scheme s of the dealt orbit
    secret, no input processes, fuel pgl27_fuel. *)
Definition pgl_epp : EPP mpP :=
  @MkEPP R mpP bool erefl erefl
    (fun s _ => tnth (ts_encode orbit_scheme s))
    (fun _ => [::]) pgl27_fuel.

(** pgl_epp_playersE — the derived participant list is the instance's list.
    @composes: pgl_epp_procsE *)
Lemma pgl_epp_playersE : @epp_players R mpP = pgl27_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(** pgl_epp_fuelE — the adapter's fuel is the instance's fuel.
    @composes: pgl_transport_terminates *)
Lemma pgl_epp_fuelE : @ep_fuel R mpP pgl_epp = pgl27_fuel.
Proof. by []. Qed.

(** pgl_epp_procsE — the derived process list is the instance's process list.
    @composes: pgl_transport_terminates *)
Lemma pgl_epp_procsE (s : bool) (w0 : pgg_gT pgl27_M) :
  @epp_procs R mpP pgl_epp s w0 0 = pgl27_procs s w0.
Proof.
rewrite /epp_procs /pgl27_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /pgl27_saprocs /pgl27_dealer_run.
by rewrite pgl_epp_playersE.
Qed.

(** pgl_concrete_terminates — every process of the generic assembly at the
    instance's participant list reaches Finish.
    @main correctness: (epp_run_at pgl_epp pgl27_players s w0 0).1 =
    nseq 10 Finish, for any cut w0, closed by vm_compute with no appeal to a
    landed lemma. *)
Lemma pgl_concrete_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@epp_run_at R mpP pgl_epp pgl27_players s w0 0).1 = nseq 10 Finish.
Proof. Time by vm_compute. Qed.

(** pgl_transport_terminates — every process of the derived run reaches
    Finish.
    @main correctness: (epp_run pgl_epp s w0 0).1 = nseq 10 Finish, for any cut
    w0, obtained from pgl27_run_terminates along the process equality. *)
Lemma pgl_transport_terminates (s : bool) (w0 : pgg_gT pgl27_M) :
  (@epp_run R mpP pgl_epp s w0 0).1 = nseq 10 Finish.
Proof.
Time (rewrite /epp_run pgl_epp_fuelE pgl_epp_procsE;
      exact: pgl27_run_terminates).
Qed.

End pgl27_execution.

(******************************************************************************)
(*     The adapter filled at five_card_profile (committed input)              *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section fivecard_execution.

Variable R : realType.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

Let mpF : MonodromyProfile R := @five_card_profile R eps Hlt Hgt Hspec L.

(** fc_epp — the five-card execution adapter at bias eps.
    @intent: run argument the committed pair (a, b) : bool * bool, both bridges
    erefl at 5 seats, 5 shares and 5 cards, content the den Boer layout of the
    decoded committed cards, input processes the two committing parties 7 and 8,
    fuel 100. *)
Definition fc_epp : EPP mpF :=
  @MkEPP R mpF (bool * bool)%type erefl erefl
    (fun _ committed => tnth (den_boer_layout (den_boer_decode committed)))
    (fun ab => [:: mk_aproc (@pgg_commit FiveCardKim_M 7 (encode_bool ab.1))
                 ; mk_aproc (@pgg_commit FiveCardKim_M 8 (encode_bool ab.2))])
    100.

(** fc_epp_playersE — the derived participant list is the instance's list.
    @composes: fc_epp_procsE *)
Lemma fc_epp_playersE : @epp_players R mpF = den_boer_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(** fc_epp_fuelE — the adapter's fuel is the instance's fuel.
    @composes: fc_transport_terminates *)
Lemma fc_epp_fuelE : @ep_fuel R mpF fc_epp = 100.
Proof. by []. Qed.

(** fc_epp_procsE — the derived process list is the instance's process list.
    @composes: fc_transport_terminates *)
Lemma fc_epp_procsE (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  @epp_procs R mpF fc_epp (a, b) w0 P_idx = den_boer_procs a b w0 P_idx.
Proof.
rewrite /epp_procs /den_boer_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /den_boer_saprocs /den_boer_dealer_run.
by rewrite fc_epp_playersE.
Qed.

(** fc_concrete_terminates — every process of the generic assembly at the
    instance's participant list reaches Finish.
    @main correctness: (epp_run_at fc_epp den_boer_players (a, b) w0 P_idx).1 =
    nseq 9 Finish, for any cut w0 and any party index P_idx, closed by
    vm_compute with no appeal to a landed lemma. *)
Lemma fc_concrete_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M)
    (P_idx : nat) :
  (@epp_run_at R mpF fc_epp den_boer_players (a, b) w0 P_idx).1 = nseq 9 Finish.
Proof. Time by vm_compute. Qed.

(** fc_transport_terminates — every process of the derived run reaches Finish.
    @main correctness: (epp_run fc_epp (a, b) w0 0).1 = nseq 9 Finish, for any
    cut w0, obtained from den_boer_run_terminates along the process equality. *)
Lemma fc_transport_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  (@epp_run R mpF fc_epp (a, b) w0 0).1 = nseq 9 Finish.
Proof.
Time (rewrite /epp_run fc_epp_fuelE fc_epp_procsE;
      exact: den_boer_run_terminates).
Qed.

End fivecard_execution.

Print Assumptions pgl_concrete_terminates.
Print Assumptions pgl_transport_terminates.
Print Assumptions fc_concrete_terminates.
Print Assumptions fc_transport_terminates.

(******************************************************************************)
(*     Attempted and killed                                                   *)
(*                                                                            *)
(* The two enum-direct termination proofs below were run under rocq-mcp       *)
(* against the state holding every declaration of this file. Neither is in    *)
(* the file: neither returned.                                                *)
(*                                                                            *)
(* Lemma pgl_direct_terminates (s : bool) (w0 : pgg_gT pgl27_M) :             *)
(*   (@epp_run R mpP pgl_epp s w0 0).1 = nseq 10 Finish.                      *)
(* Proof. Time by vm_compute. Qed.                                           *)
(*   -> killed by the 70 s session limit, goal untouched.                     *)
(*                                                                            *)
(* Lemma fc_direct_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M) :      *)
(*   (@epp_run R mpF fc_epp (a, b) w0 0).1 = nseq 9 Finish.                   *)
(* Proof. Time by vm_compute. Qed.                                           *)
(*   -> killed the PET process (no response) inside the same 70 s window.     *)
(*                                                                            *)
(* The isolating variation was the participant list alone: epp_run x w0 P is  *)
(* epp_run_at epp_players x w0 P by conversion (epp_run_atE), and replacing   *)
(* epp_players by the instance's concrete list gives pgl_concrete_terminates  *)
(* and fc_concrete_terminates, both of which close by vm_compute.             *)
(******************************************************************************)

(******************************************************************************)
(*     Timing block                                                           *)
(*                                                                            *)
(* Machine: darwin 25.5.0, rocq 9, one worker. Session numbers are rocq-mcp   *)
(* rocq_check wall time for the quoted call; file numbers are the Time        *)
(* vernacular of the compile run of this file.                                *)
(*                                                                            *)
(* Termination proofs                                                         *)
(*                                                                            *)
(*   carrier    participant list           route        session       file    *)
(*   -------    ----------------           -----        -------       ----    *)
(*   PGL        enum 'I_8   (epp_players)  vm_compute   KILLED 70 s   absent  *)
(*   PGL        pgl27_players              vm_compute   0.295 s [1]   0.023 s *)
(*   PGL        pgl27_players              transport    0.009 s [2]   0.000 s *)
(*   five-card  enum 'I_5   (epp_players)  vm_compute   PET DIED      absent  *)
(*   five-card  den_boer_players           vm_compute   0.116 s [3]   0.036 s *)
(*   five-card  den_boer_players           transport    0.051 s [4]   0.001 s *)
(*                                                                            *)
(*   The file column is stable across the two compile runs of this text:      *)
(*   0.024 / 0. / 0.036 / 0.001 then 0.023 / 0. / 0.036 / 0.001.              *)
(*                                                                            *)
(*   [1] one rocq_check of 5 commands: the definition, the statement, Time    *)
(*       vm_compute, Qed.                                                     *)
(*   [2] one rocq_check of 4 commands: statement, Proof, tactic, Qed.         *)
(*   [3] one rocq_check of 4 commands, at ABSTRACT P_idx.                     *)
(*   [4] one rocq_check of 30 commands: the whole five-card section up to     *)
(*       and including this proof; the proof alone is below that figure.      *)
(*                                                                            *)
(*   The file column is the Time vernacular of the compile run and is the     *)
(*   figure to compare; the session column carries the enclosing rocq_check   *)
(*   and is an upper bound.                                                   *)
(*                                                                            *)
(* Enumeration reduction                                                      *)
(*                                                                            *)
(*   Eval vm_compute in (enum 'I_8)         stuck, 385088 chars of normal form*)
(*   Eval vm_compute in (size (enum 'I_8))  stuck, 387979 chars               *)
(*   head of both normal forms: Finite.enum applied to the ordinal Finite     *)
(*   class record; leaves: match idP with @ReflectT _ x0 => Some (Ordinal ..) *)
(*                                                                            *)
(* Whole file                                                                 *)
(*                                                                            *)
(*   compile wall time (time sh rebuild.sh probe_g_vmcompute.v)   5.862 s     *)
(*   probe_g_vmcompute.vo                                         100258 B    *)
(*                                                                            *)
(*   Both figures are those of the code-identical run preceding this          *)
(*   paragraph. The compile is dominated by the import closure: the four      *)
(*   proofs together account for 0.06 s of the 5.862 s.                       *)
(*                                                                            *)
(* Verdict against the plan thresholds: the enum-direct path is not within 3x *)
(* of the concrete path, it exceeds the 60 s kill threshold at both carriers  *)
(* while the concrete path costs about 0.1 s, so the ratio is not finite as   *)
(* measured. A new instance cannot prove termination on the enum-based        *)
(* process list; the adapter needs a concrete participant-list field together *)
(* with its equation against enum (pgl_epp_playersE, fc_epp_playersE), which  *)
(* is exactly the design already documented at pgl27_run.v:53-56.             *)
(******************************************************************************)
