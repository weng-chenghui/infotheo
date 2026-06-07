(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface pgg_session_types card_exchange_pismc.

(******************************************************************************)
(* PGG: Input-Commitment Stage                                                *)
(*                                                                            *)
(* A pre-protocol stage in which M input parties each commit one card value   *)
(* (a position in 'I_N) to the dealer before the dealing phase begins. The    *)
(* committed values are assembled into the dealer's word table and the        *)
(* unchanged exchange_dealer body runs as before; players and the verifier    *)
(* see exactly the same wire as without the prologue.                         *)
(*                                                                            *)
(* GATE 2 (see the protocol-merge plan): the den Boer commit primitives       *)
(* FCCommit/FCRecvCommit are typed over fc_dtype/fc_data and CANNOT be        *)
(* spliced into pgg_dtype/pgg_data. These wrappers are NEW, built over the    *)
(* existing pgg_dtype/pgg_data; the committed payload reuses PGG_sheet, so     *)
(* the dealer/player/verifier wire of the dealing phase is unchanged and      *)
(* only the dealer gains a prologue.                                          *)
(*                                                                            *)
(*   pgg_commit i v               == input party i sends PGG_sheet v to       *)
(*                                   the dealer, then finishes                 *)
(*   pgg_recv_commit from         == dealer receives one PGG_sheet from        *)
(*                                   [from], then finishes (dual of commit)    *)
(*   pgg_commit_prologue cont acc inputs                                       *)
(*                                == dealer receives one PGG_sheet from each    *)
(*                                   party in [inputs], accumulating the        *)
(*                                   committed values, then runs cont          *)
(*   exchange_dealer_with_commit PI inputs assemble content players P_idx      *)
(*                                == the dealer prologue (one recv per input    *)
(*                                   party) followed by the existing            *)
(*                                   exchange_dealer body, with the word table  *)
(*                                   built from the committed values           *)
(*                                                                            *)
(* The empty prologue degenerates definitionally to the plain dealer          *)
(* (exchange_dealer_with_commit_nil), so the position-model instances that     *)
(* take no committed inputs are unaffected.                                   *)
(*                                                                            *)
(* Session-type duality between the committed dealer and every counterpart     *)
(* (each input party, every player, the verifier) is verified by              *)
(* native_compute for a concrete two-input instance in the idealized section. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_input_commitment.

Variable M : MonodromyReprType.

Let N := (pgg_N' M).+1.
Let data := pgg_data N.

(** pgg_commit — an input party's commit send: deliver one card value as a
    PGG_sheet to the dealer, then finish.
    Kind: interface.
    What: SSend dealer_idx DT_Sheet (PGG_sheet v) SFinish, as the input party
    [i]. Why: GATE 2 forbids reusing the fc_dtype FCCommit; the committed
    payload is a PGG_sheet so the wire reuses the existing dealing alphabet.
    Used-by: the idealized duality demo; an input party of the committed
    protocol. *)
Definition pgg_commit (i : nat) (v : 'I_N)
    : @sproc pgg_dtype data i 2 (senv_send senv_end dealer_idx DT_Sheet) :=
  SSend dealer_idx DT_Sheet (PGG_sheet v) SFinish.

(** pgg_recv_commit — the dealer's standalone commit receive: receive one
    PGG_sheet from party [from], then finish.
    Kind: interface.
    What: SRecv from DT_Sheet matched through from_sheet, finishing on a valid
    sheet and failing on a malformed payload. Why: the session dual of
    pgg_commit, used to certify the commit/recv pair is well typed before it is
    threaded into the dealer prologue. Used-by: the idealized duality demo
    (commit/recv pair). *)
Definition pgg_recv_commit (from : nat)
    : @sproc pgg_dtype data dealer_idx 2 (senv_recv senv_end from DT_Sheet) :=
  SRecv from DT_Sheet (fun d =>
    match from_sheet d with
    | Some _ => SFinish
    | None => SFail
    end).

(** pgg_commit_prologue — the dealer's commit-collection prologue: receive one
    PGG_sheet from each party in [inputs], accumulate the committed values, and
    hand the collected list to the continuation.
    Kind: interface.
    What: a value-capturing fold of SRecv over [inputs]; the fuel and session
    environment of the result are the continuation's, prepended with one
    senv_recv layer per input party. Why: the dealing-phase body (exchange_dealer)
    has a fixed session type; the prologue prepends the committed receives while
    threading the dependent session environment by computation. Used-by:
    exchange_dealer_with_commit. *)
Fixpoint pgg_commit_prologue {dn : nat} {denv : senv pgg_dtype}
    (cont : seq 'I_N -> @sproc pgg_dtype data dealer_idx dn denv)
    (acc : seq 'I_N) (inputs : seq nat) {struct inputs}
    : @sproc pgg_dtype data dealer_idx
        (iter (size inputs) succn dn)
        (fold_senv (fun from e => senv_recv e from DT_Sheet) inputs denv) :=
  match inputs return
    @sproc pgg_dtype data dealer_idx
      (iter (size inputs) succn dn)
      (fold_senv (fun from e => senv_recv e from DT_Sheet) inputs denv)
  with
  | [::] => cont acc
  | from :: rest =>
      SRecv from DT_Sheet (fun d =>
        match from_sheet d with
        | Some v => pgg_commit_prologue cont (acc ++ [:: v]) rest
        | None => SFail
        end)
  end.

(** exchange_dealer_with_commit — the dealer program with an input-commitment
    prologue: collect one committed card value from each party in [inputs],
    assemble them into the word table, then run the existing dealing body.
    Kind: interface.
    What: pgg_commit_prologue feeding [fun committed => exchange_dealer PI
    content players (assemble committed) P_idx]. Why: routes committed inputs
    into the dealing phase without changing the dealer/player/verifier wire of
    that phase; the prologue is the only addition. Used-by: the den Boer M=2
    input-commitment instance; the idealized two-input duality demo. *)
Definition exchange_dealer_with_commit
    (PI : PGGInterface M) (inputs : seq nat)
    (assemble : seq 'I_N -> seq (pgg_gT M))
    (content : 'I_N -> 'I_N)
    (players : seq 'I_(pi_T' PI).+1) (P_idx : nat)
    : @sproc pgg_dtype data dealer_idx _ _ :=
  pgg_commit_prologue
    (fun committed => exchange_dealer PI content players (assemble committed) P_idx)
    [::] inputs.

(** exchange_dealer_with_commit_nil — the empty prologue degenerates to the
    plain dealer.
    Kind: main.
    What: with no input parties the committed dealer is the plain
    exchange_dealer on the assembled-from-nothing word table, holding by
    computation (pgg_commit_prologue matches on [::]). Why: the position-model
    instances commit no inputs, so they keep the unchanged dealing program and
    every existing duality proof. Used-by: the M = 0 degeneration check of the
    protocol-merge plan. *)
Lemma exchange_dealer_with_commit_nil
    (PI : PGGInterface M)
    (assemble : seq 'I_N -> seq (pgg_gT M))
    (content : 'I_N -> 'I_N)
    (players : seq 'I_(pi_T' PI).+1) (P_idx : nat) :
  exchange_dealer_with_commit [::] assemble content players P_idx
  = exchange_dealer PI content players (assemble [::]) P_idx.
Proof. by []. Qed.

End pgg_input_commitment.

Arguments pgg_commit {M}.
Arguments pgg_recv_commit {M}.
Arguments pgg_commit_prologue {M dn denv}.
Arguments exchange_dealer_with_commit {M} PI.

(******************************************************************************)
(** * Two-Input Duality Verification (Idealized)                              *)
(*                                                                            *)
(* Concrete check that the dealer-with-commit prologue is dual to each input  *)
(* party's commit AND that the dealing phase stays dual to every player and   *)
(* the verifier. Reuses the idealized fully symmetric S_N instance from        *)
(* card_exchange_pismc.v (two players, T = 2). Two input parties commit at     *)
(* process ids 4 and 5 (above dealer 0, verifier 1, players 2 and 3).         *)
(******************************************************************************)

Section pgg_commit_idealized_duality.

Variable n : nat.
Let N := n.+2.
Let M := Idealized_MonodromyRepr n.
Let PI := Test_PGG_2 n.
Let data := pgg_data (pgg_N' M).+1.

(* Concrete player list for the T = 2 idealized instance *)
Let players_2 : seq 'I_2 :=
  [:: @Ordinal 2 0 isT; @Ordinal 2 1 isT].

(* The two input parties commit at process ids 4 and 5 *)
Let input_ids : seq nat := [:: 4; 5].

Variables (W : seq {perm 'I_N}) (P_idx : nat).

Local Open Scope sproc_scope.

(** ap_dealer_commit_2 — the two-input committed dealer as an aproc.
    Kind: example.
    Why: the dealer side of the two-input duality check. The assemble map is
    constant (the committed values do not change the dealing-phase session type,
    only the word payloads), so the duality is exercised on the prologue
    structure. Used-by: the dwc_* duality lemmas. *)
Definition ap_dealer_commit_2 :=
  mk_aproc (exchange_dealer_with_commit PI input_ids
    (fun _ => W) id players_2 P_idx).

(** ap_input0_commit — input party 0 (process id 4) commit as an aproc.
    Kind: example. *)
Definition ap_input0_commit :=
  mk_aproc (pgg_commit 4 (@Ordinal (pgg_N' M).+1 0 isT)).

(** ap_input1_commit — input party 1 (process id 5) commit as an aproc.
    Kind: example. *)
Definition ap_input1_commit :=
  mk_aproc (pgg_commit 5 (@Ordinal (pgg_N' M).+1 0 isT)).

(** ap_recv_commit_2 — the dealer's standalone single-commit receive (from
    party 4) as an aproc.
    Kind: example. *)
Definition ap_recv_commit_2 := mk_aproc (@pgg_recv_commit M 4).

(** commit_recv_dual_2 — the standalone commit/recv-commit pair is dual.
    Kind: main.
    Why: certifies pgg_commit and pgg_recv_commit are session duals
    independently of the prologue. *)
Lemma commit_recv_dual_2 : channels_dual ap_recv_commit_2 ap_input0_commit.
Proof. by native_compute. Qed.

(** dealer_commit_input0_dual_2 — the committed dealer is dual to input party 0.
    Kind: main.
    Why: the prologue's first receive is dual to the first input party's commit
    send; this is the HIGH-risk dependent-senv threading discharged for a
    concrete two-input instance. *)
Lemma dealer_commit_input0_dual_2 :
  channels_dual ap_dealer_commit_2 ap_input0_commit.
Proof. by native_compute. Qed.

(** dealer_commit_input1_dual_2 — the committed dealer is dual to input party 1.
    Kind: main. *)
Lemma dealer_commit_input1_dual_2 :
  channels_dual ap_dealer_commit_2 ap_input1_commit.
Proof. by native_compute. Qed.

(** dealer_commit_player0_dual_2 — the committed dealer stays dual to player 0.
    Kind: main.
    Why: the prologue does not disturb the dealing-phase sends, so the dealer's
    session with each player is unchanged. *)
Lemma dealer_commit_player0_dual_2 :
  channels_dual ap_dealer_commit_2 (ap_player0_2 n).
Proof. by native_compute. Qed.

(** dealer_commit_player1_dual_2 — the committed dealer stays dual to player 1.
    Kind: main. *)
Lemma dealer_commit_player1_dual_2 :
  channels_dual ap_dealer_commit_2 (ap_player1_2 n).
Proof. by native_compute. Qed.

(** dealer_commit_verifier_dual_2 — the committed dealer stays dual to the
    verifier.
    Kind: main. *)
Lemma dealer_commit_verifier_dual_2 :
  channels_dual ap_dealer_commit_2 (ap_verifier_2 n).
Proof. by native_compute. Qed.

End pgg_commit_idealized_duality.

