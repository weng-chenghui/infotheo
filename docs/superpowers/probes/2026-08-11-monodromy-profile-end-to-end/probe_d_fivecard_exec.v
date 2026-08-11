(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Probe P-D: the execution adapter at five_card_profile, arbitrary bias      *)
(*                                                                            *)
(* The EPP record and the generic section execution_of_profile are the ones   *)
(* of probe_c_pgl27_exec.v (the probe directory has no -R mapping, so they    *)
(* are copied rather than required). Section fivecard_execution fills the     *)
(* record at five_card_profile over ARBITRARY bias eps, with the two          *)
(* committing input parties in ep_input_procs, and proves the derived process *)
(* list equal to the landed den_boer_procs. The four landed end-to-end facts  *)
(* (termination, verifier endpoints, the endpoint decoder, executed AND       *)
(* recovery) transport along that equality.                                   *)
(*                                                                            *)
(* Findings, not statements (design record for P-E and P-H):                  *)
(*                                                                            *)
(*  1. OFF-BY-ONE IN THE COPIED epp_input_ids. probe_c_pgl27_exec.v starts    *)
(*     the input identifiers at (pi_T' (mp_PI mp)).+2. Process identifiers    *)
(*     are 0 for the dealer, 1 for the verifier and 2 .. (pi_T' _).+2 for the *)
(*     seats, so the first free identifier is (pi_T' (mp_PI mp)).+3. At the   *)
(*     five-card carrier pi_T' = 4, and the P-C offset yields [:: 6; 7] where *)
(*     den_boer_dealer_run passes [:: 7; 8] (fc_input_ids_offsetE against     *)
(*     fc_epp_input_idsE). The identifier list is an argument of the dealer,  *)
(*     so at the P-C offset the process equality against the landed dealer is *)
(*     false, not merely unprovable. One token of the copied generic section  *)
(*     is therefore changed, .+2 to .+3, which is the P-A convention          *)
(*     (gen_input_ids = iota T.+2 _ with T = (pi_T' PI).+1). The change is    *)
(*     invisible to P-C: pgl_epp has ep_input_procs = fun _ => [::], and      *)
(*     epp_input_ids0 shows iota _ 0 = [::] at every offset, so               *)
(*     pgl_epp_procsE is unaffected.                                          *)
(*                                                                            *)
(*  2. The process ORDER of the generic epp_saprocs (dealer, verifier, seats, *)
(*     then input parties) is already den_boer_saprocs's order; nothing else  *)
(*     in the generic section was touched.                                    *)
(*                                                                            *)
(*  3. ep_content is constant in the run argument: the committed bits reach   *)
(*     the dealt layout through the parties in ep_input_procs and the commit  *)
(*     prologue, never through the content readout. The readout is den Boer's *)
(*     uncast tnth (den_boer_layout (den_boer_decode committed)), so the      *)
(*     process equality stays a conversion after the one players rewrite.     *)
(*                                                                            *)
(*  4. Fuel is pinned by fc_epp_fuelE before every transport, per the P-C     *)
(*     divergence note. Each transported proof runs in tens of milliseconds.  *)
(*                                                                            *)
(*  5. The bias enters no process term: fc_epp_procs_biasE holds by           *)
(*     conversion, so the two five-card family members share one program.     *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The execution adapter (probe_c_pgl27_exec.v)                           *)
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

(* The offset is .+3, not the .+2 of probe_c_pgl27_exec.v: the seats occupy the
   identifiers 2 .. (pi_T' (mp_PI mp)).+2, so the first free identifier is
   (pi_T' (mp_PI mp)).+3. See finding 1 in the file header. *)

(** epp_input_ids — the party identifiers of the input processes.
    @intent: iota (pi_T' (mp_PI mp)).+3 (size (ep_input_procs e x)), the
    identifiers following the dealer, the verifier and the seats. *)
Definition epp_input_ids (x : ep_inputT e) : seq nat :=
  iota (pi_T' (mp_PI mp)).+3 (size (e.(ep_input_procs) x)).

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

(** epp_endpoints — the verifier's collected endpoints.
    @intent: endpoints_of_trace of entry 1 of epp_run.2. *)
Definition epp_endpoints (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) :=
  endpoints_of_trace (nth [::] (epp_run x w0 P_idx).2 1).

(** epp_participant_trace — the executed trace of the seat-i player.
    @intent: entry 2 + i of epp_run.2. *)
Definition epp_participant_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp))
    (P_idx : nat) (i : 'I_(pi_T' (mp_PI mp)).+1) :=
  nth [::] (epp_run x w0 P_idx).2 (2 + i).

(** epp_seat_share_count — the seat/share bridge in successor form.
    @composes: fc_epp_run_recovers *)
Lemma epp_seat_share_count :
  (pi_T' (mp_PI mp)).+1 = (ts_T' (rp_scheme (mp_plug mp))).+1.
Proof. by rewrite e.(ep_players_bridge). Qed.

(** epp_decode — the endpoint decoder of the adapter.
    @intent: an endpoint list of one card per seat, transported along the
    seat/share bridge into the argument type of run_recover and reconstructed
    there. *)
Definition epp_decode (ep : seq 'I_(pgg_N' (mp_M mp)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mp)).+1) : mp_secretT mp :=
  run_recover (tcast (etrans Hsz epp_seat_share_count) (in_tuple ep)).

(** epp_content_from_plug — the share readout derived from the card/share
    bridge.
    @intent: tnth (ts_encode (rp_scheme (mp_plug mp)) s) at a card position,
    transported along ep_cards_bridge. *)
Definition epp_content_from_plug (s : mp_secretT mp)
    : seq 'I_(pgg_N' (mp_M mp)).+1
      -> ('I_(pgg_N' (mp_M mp)).+1 -> 'I_(pgg_N' (mp_M mp)).+1) :=
  fun _ i => tnth (ts_encode (rp_scheme (mp_plug mp)) s)
               (cast_ord e.(ep_cards_bridge) i).

End execution_of_profile.

(** epp_input_ids0 — an adapter with no input processes has no input
    identifiers, at any offset.
    @main architecture: ep_input_procs e x = [::] implies epp_input_ids x =
    [::], so the offset correction of finding 1 leaves every input-free
    instantiation, probe_c_pgl27_exec.v's pgl_epp among them, unchanged. *)
Lemma epp_input_ids0 (R : realType) (mp : MonodromyProfile R) (e : EPP mp)
    (x : ep_inputT e) :
  e.(ep_input_procs) x = [::] -> @epp_input_ids R mp e x = [::].
Proof. by rewrite /epp_input_ids => ->. Qed.

(******************************************************************************)
(*     The adapter filled at five_card_profile, arbitrary bias                *)
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

(** fc_epp_contentE — the content readout ignores the run argument.
    @main architecture: ep_content fc_epp x = ep_content fc_epp y for all x, y;
    the committed bits reach the dealt layout through the input parties and the
    commit prologue, not through the readout. *)
Lemma fc_epp_contentE (x y : bool * bool) :
  fc_epp.(ep_content) x = fc_epp.(ep_content) y.
Proof. by []. Qed.

(** fc_epp_playersE — the derived participant list is the instance's list.
    @composes: fc_epp_procsE *)
Lemma fc_epp_playersE : @epp_players R mpF = den_boer_players.
Proof.
rewrite /epp_players; apply: (inj_map val_inj); rewrite val_enum_ord.
by [].
Qed.

(** fc_epp_input_idsE — the derived input identifiers are the instance's.
    @composes: fc_epp_procsE *)
Lemma fc_epp_input_idsE (ab : bool * bool) :
  @epp_input_ids R mpF fc_epp ab = [:: 7; 8].
Proof. by []. Qed.

(** fc_input_ids_offsetE — the identifier list at the probe_c_pgl27_exec.v
    offset.
    @main architecture: iota (pi_T' FiveCardKim_PI).+2 2 = [:: 6; 7], the two
    identifiers that offset produces where den_boer_dealer_run passes
    [:: 7; 8]; the witness of finding 1. *)
Lemma fc_input_ids_offsetE : iota (pi_T' FiveCardKim_PI).+2 2 = [:: 6; 7].
Proof. by []. Qed.

(** fc_epp_procsE — the derived process list is the instance's process list.
    @main architecture: epp_procs fc_epp (a, b) w0 P_idx = den_boer_procs a b w0
    P_idx, at every bias eps. *)
Lemma fc_epp_procsE (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  @epp_procs R mpF fc_epp (a, b) w0 P_idx = den_boer_procs a b w0 P_idx.
Proof.
rewrite /epp_procs /den_boer_procs; congr erase_aprocs.
rewrite /epp_saprocs /epp_dealer /den_boer_saprocs /den_boer_dealer_run.
by rewrite fc_epp_playersE.
Qed.

(** fc_epp_fuelE — the adapter's fuel is the instance's fuel.
    @composes: fc_epp_terminates *)
Lemma fc_epp_fuelE : @ep_fuel R mpF fc_epp = 100.
Proof. by []. Qed.

(** fc_epp_terminates — every process of the derived run reaches Finish.
    @main correctness: (epp_run fc_epp (a, b) w0 P_idx).1 = nseq 9 Finish, for
    any cut w0. *)
Lemma fc_epp_terminates (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  (@epp_run R mpF fc_epp (a, b) w0 P_idx).1 = nseq 9 Finish.
Proof.
rewrite /epp_run fc_epp_fuelE fc_epp_procsE; exact: den_boer_run_terminates.
Qed.

(** fc_epp_endpoints — the derived verifier endpoints are the dealt layout at
    the cut.
    @main correctness: epp_endpoints fc_epp (a, b) w0 0 is the layout of the
    committed pair read at the cut image of each starting position, one per
    seat. *)
Lemma fc_epp_endpoints (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  @epp_endpoints R mpF fc_epp (a, b) w0 0
  = [seq tnth (den_boer_layout (a, b))
        (@pgg_rho (mp_M mpF) w0 (tnth (pi_starts (mp_PI mpF)) i))
     | i <- @epp_players R mpF].
Proof.
rewrite /epp_endpoints /epp_run fc_epp_fuelE fc_epp_procsE.
exact: den_boer_endpoints.
Qed.

(** fc_epp_endpoints_size — the derived run collects one endpoint per seat.
    @composes: fc_epp_run_recovers *)
Lemma fc_epp_endpoints_size (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  size (@epp_endpoints R mpF fc_epp (a, b) w0 0) = (pi_T' (mp_PI mpF)).+1.
Proof. by rewrite fc_epp_endpoints size_map /epp_players size_enum_ord. Qed.

(** fc_epp_decodeE — the adapter's decoder is the instance's reconstruction.
    @composes: fc_epp_decode_seqE *)
Lemma fc_epp_decodeE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1)
    (Hsz' : size ep = (ts_T' fcI_scheme).+1) :
  @epp_decode R mpF fc_epp ep Hsz
  = ts_recon fcI_scheme (tcast Hsz' (in_tuple ep)).
Proof.
rewrite /epp_decode /run_recover.
by rewrite (eq_irrelevance (etrans Hsz (@epp_seat_share_count R mpF fc_epp))
                          Hsz').
Qed.

(** fc_epp_decode_seqE — the adapter's decoder at the sequence level.
    @composes: fc_epp_run_recovers
    epp_decode fc_epp ep Hsz = fc_three_consec [seq decode_bool x | x <- ep],
    the reconstruction shape of den_boer_run_recovers; the tuple cast is
    transparent on the underlying sequence. *)
Lemma fc_epp_decode_seqE (ep : seq 'I_(pgg_N' (mp_M mpF)).+1)
    (Hsz : size ep = (pi_T' (mp_PI mpF)).+1) :
  @epp_decode R mpF fc_epp ep Hsz
  = fc_three_consec [seq decode_bool x | x <- ep].
Proof.
rewrite (fc_epp_decodeE Hsz Hsz).
by rewrite /ts_recon /fcI_scheme /fcI_recon val_tcast.
Qed.

(** fc_epp_run_recovers — the derived run reconstructs the committed
    conjunction.
    @main correctness: decoding the executed endpoints of epp_run fc_epp through
    epp_decode returns a && b, the conjunction of the two bits committed by the
    input parties, for any cut w0 in the group. *)
Lemma fc_epp_run_recovers (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  w0 \in pgg_G FiveCardKim_M ->
  @epp_decode R mpF fc_epp (@epp_endpoints R mpF fc_epp (a, b) w0 0)
    (fc_epp_endpoints_size a b w0) = a && b.
Proof.
move=> Hw0.
rewrite fc_epp_decode_seqE /epp_endpoints /epp_run fc_epp_fuelE fc_epp_procsE.
exact: den_boer_run_recovers.
Qed.

End fivecard_execution.

(******************************************************************************)
(*     Invariance of the program in the shuffle witness                       *)
(******************************************************************************)

(** fc_epp_procs_biasE — the executed program does not depend on the bias.
    @main architecture: the process lists of the adapters at two biases eps1 and
    eps2, with their own Kim constraint packs and word lengths, are equal; the
    security witness of five_card_profile enters no process term, so a new bias
    needs no new process definition. *)
Lemma fc_epp_procs_biasE (R : realType) (eps1 eps2 : R)
    (Hlt1 : eps1 < 5%:R^-1) (Hgt1 : - (4%:R * 5%:R^-1) < eps1)
    (Hspec1 : `|eps1| < 4%:R / 5%:R)
    (Hlt2 : eps2 < 5%:R^-1) (Hgt2 : - (4%:R * 5%:R^-1) < eps2)
    (Hspec2 : `|eps2| < 4%:R / 5%:R)
    (L1 L2 : nat) (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat) :
  @epp_procs R (@five_card_profile R eps1 Hlt1 Hgt1 Hspec1 L1)
               (@fc_epp R eps1 Hlt1 Hgt1 Hspec1 L1) (a, b) w0 P_idx
  = @epp_procs R (@five_card_profile R eps2 Hlt2 Hgt2 Hspec2 L2)
               (@fc_epp R eps2 Hlt2 Hgt2 Hspec2 L2) (a, b) w0 P_idx.
Proof. by []. Qed.

Print Assumptions fc_epp_procsE.
Print Assumptions fc_epp_run_recovers.
Print Assumptions fc_epp_procs_biasE.
