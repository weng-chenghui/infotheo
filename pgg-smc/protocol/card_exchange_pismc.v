(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
From mathcomp Require Import boolp reals.
Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface pgg_session_types.
Require Import pgg_weval_inj.
From pgg_smc Require Import pgg_security_solver.
From pgg_reconstruct Require Import algebraic_rigidity.

(******************************************************************************)
(* Card Exchange Phase Protocol                                               *)
(*                                                                            *)
(* Based on: Weng, Affeldt, Garrigue, Saikawa,                               *)
(*   "An Approach to Formalize Information-Theoretic Security of              *)
(*    Multiparty Computation Protocols," FORTE 2025.                          *)
(*                                                                            *)
(* In the exchange phase, the dealer applies a sequence of card exchanges.    *)
(* In each round, one of Tg exchange operations (generators) is selected     *)
(* and applied to all card positions simultaneously. After L rounds, the     *)
(* composition sigma_{w_0} * sigma_{w_1} * ... * sigma_{w_{L-1}} determines  *)
(* the final card positions. Security converges as L grows, controlled by    *)
(* the spectral gap of the Schreier graph on the generators.                 *)
(*                                                                            *)
(* Types involved:                                                            *)
(*   generator index ('I_Tg) -- selects one of Tg exchange operations        *)
(*   word (L.-tuple 'I_Tg)  -- a sequence of L exchange selections           *)
(*   group element (gT)      -- word_eval(w), the composed exchange           *)
(*   card position ('I_N)    -- a position in {0,..,N-1}                     *)
(*   endpoint : 'I_N         -- rho(g)(s), the card position after exchange  *)
(*   outcome                 -- ts_recon(endpoints), recovered by threshold  *)
(*                              scheme from k collected card positions        *)
(*                                                                            *)
(* The dealer samples a random word w uniformly from Tg^L choices,           *)
(* evaluates word_eval(w) to get a shuffle permutation, and distributes      *)
(* each player's card position (a coordinate). The verifier collects         *)
(* k card positions and applies ts_recon to recover the hidden value.        *)
(* What the hidden value is depends on the threshold scheme:                  *)
(*   - Genus 0 (RS code): a field element via polynomial interpolation       *)
(*   - Genus g (AG codes): determined by AG code decoding                     *)
(*   - Sum-mod-N: (sum of card positions) mod N                               *)
(*                                                                            *)
(* How the hidden value is determined:                                        *)
(* 1. The dealer encodes hidden value s as starting card positions: ts_encode(s).    *)
(* 2. The word w scrambles these sheets: word_eval(w) applies a coordinate   *)
(*    permutation (invisible to reconstruction by ts_recon_perm_invariant).       *)
(* 3. The verifier collects card positions and recovers s via ts_recon.      *)
(* The hidden value is fixed by the starting card positions, not by the shuffle.     *)
(* ts_encode_valid guarantees ts_valid(s, ts_encode(s)), so the dealer       *)
(* always produces a valid configuration. dealer_encode_correct              *)
(* (pgg_dealer_bridge.v) is the end-to-end theorem.                          *)
(*                                                                            *)
(* Example: recovering the number 39 with the Monster group (N ~ 10^20).     *)
(* The starting card positions [s_0, ..., s_{T-1}] are chosen so that               *)
(* ts_valid(39, starts) holds for the threshold scheme. The dealer samples   *)
(* w : 67.-tuple 'I_2 (67 binary shuffle choices). word_eval(w) is a        *)
(* permutation on ~10^20 card positions, e.g.,                                *)
(*   {0 -> 47283..., 1 -> 91847..., 2 -> 39, ...}                           *)
(* Each player i observes rho(word_eval(w))(s_i) — a shuffled coordinate.   *)
(* The verifier collects k shuffled coordinates and recovers 39:             *)
(*   - RS code (genus 0): interpolate a polynomial through k points          *)
(*     (s_i, endpoint_i), evaluate at a hidden point -> 39                   *)
(*   - AG code (genus g): decode the AG codeword from k coordinates -> 39    *)
(*   - Sum-mod-N: (endpoint_0 + ... + endpoint_{T-1}) mod N = 39            *)
(* The shuffle determines WHICH scrambling is applied, not the hidden value. *)
(*                                                                            *)
(* The dealer evaluates words into group elements, producing a lookup table  *)
(* W : seq gT = [g_0, ..., g_{|W|-1}], and picks a selection index P_idx.   *)
(* For each player i (starting at sheet s_i), the dealer deals the hand      *)
(* [rho(g_0)(s_i), ..., rho(g_{|W|-1})(s_i)] -- a list of card positions,   *)
(* one per table entry -- together with P_idx.  Player i looks up entry      *)
(* P_idx to get the card position rho(g_{P_idx})(s_i) and reveals it to the *)
(* verifier, who collects T card positions (coordinates).                     *)
(*                                                                            *)
(* Security (pgg_collusion_bound.v, pgg_entropy_security.v,                  *)
(*           pgg_schreier.v):                                                 *)
(*   - Information-theoretic, no computational assumptions.                  *)
(*   - Collusion bound: d_TV(adversary, uniform) <= eps + 2(T-1)/N.         *)
(*   - eps measures how far the card position distribution is from uniform.  *)
(*   - Spectral bound: eps(L) <= sqrt(N) * (1-gap)^L (monotone envelope).   *)
(*   - The exact eps(L) is NOT monotonic (identity enters achievable at L=2  *)
(*     for transposition generators, causing a spike). See pgg_schreier.v.   *)
(*   - Requires non-abelian G (abelian => eps floor, see Section D below).   *)
(*   - Transitive actions drive eps -> 0 as L grows; non-transitive (Star)   *)
(*     have permanent eps floors on some orbits.                             *)
(*                                                                            *)
(* Protocol phases (card protocol actions):                                   *)
(*   1. Dealer: for each player i, deal hand(W, i) and announce P_idx       *)
(*   2. Player i: receive hand, look up entry P_idx, reveal card pos        *)
(*   3. Verifier: observe T card positions, apply ts_recon                   *)
(*                                                                            *)
(* Session-typed protocol programs using \pi{...} notation:                   *)
(*   exchange_dealer players W P_idx == dealer deals hands and announces selection   *)
(*   exchange_player i               == player i computes and reveals card position  *)
(*   exchange_verifier players       == verifier observes card positions             *)
(*                                                                            *)
(* Action notation markers (inside custom pismc):                             *)
(*   Deal<p> #x      deals hand x as DT_Hand                                *)
(*   Reveal<p> &x    reveals card position x as DT_Sheet                     *)
(*   Announce<p> $x  announces selection index x as DT_Idx                   *)
(*   Receive<p> #x   receives DT_Hand, binds x : seq ('I_N)                 *)
(*   Observe<p> &x   receives DT_Sheet, binds x : 'I_N                      *)
(*   Receive<p> $x   receives DT_Idx, binds x : nat                         *)
(*                                                                            *)
(* Cross-equality with pgg_program.v and interpreter integration are          *)
(* verified in pgg_correctness.v (not in this file).                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope pismc_scope.

Section pgg_pismc.

Variable M : MonodromyReprType.
Variable PI : PGGInterface M.

Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let gT := pgg_gT M.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.
Let data := pgg_data N.

(* Player index convention: mirrors DSDP's alice_idx/bob_idx/charlie_idx.
   dealer  = 0: deals hands and announces selection
   verifier = 1: observes card positions and reconstructs
   player i = i+2: compute players (one per starting sheet) *)
Definition dealer_idx : nat := 0.
Definition verifier_idx : nat := 1.
(** player_idx — maps logical player ordinal [i : 'I_T] to its process index [i+2].
    Kind: interface.
    Why: players occupy process ids [2, 3, ...] after dealer (0) and verifier (1).
*)
Definition player_idx (i : 'I_T) : nat := i.+2.

(* Make sproc type annotations concise *)
Arguments sproc dtype data party {_} {_}.

(* Card protocol action aliases — one per dtype *)
Let Reveal_pos {party n env} := @PGGReveal_pos M party n env.
Let Deal_hand {party n env} := @PGGDeal_hand M party n env.
Let Announce_idx {party n env} := @PGGAnnounce_idx M party n env.
Let Observe_pos {party n env} := @PGGObserve_pos M party n env.
Let Receive_hand {party n env} := @PGGReceive_hand M party n env.
Let Receive_idx {party n env} := @PGGReceive_idx M party n env.

(** * Card protocol action notations *)

Notation "'Reveal<' p '>' '&' x ; P" := (Reveal_pos p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

Notation "'Deal<' p '>' '#' x ; P" := (Deal_hand p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

Notation "'Announce<' p '>' '$' x ; P" := (Announce_idx p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

(** * Observation/receive notations *)

Local Notation "'Observe<' p '>' '&' x '=>' P" :=
  (Observe_pos p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Local Notation "'Receive<' p '>' '#' x '=>' P" :=
  (Receive_hand p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Local Notation "'Receive<' p '>' '$' x '=>' P" :=
  (Receive_idx p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

(******************************************************************************)
(** * Environment Step Functions for ForList                                  *)
(******************************************************************************)

Let dealer_hand_env (j : 'I_T) (env : senv pgg_dtype) :=
  senv_send env (player_idx j) DT_Hand.

Let dealer_idx_env (j : 'I_T) (env : senv pgg_dtype) :=
  senv_send env (player_idx j) DT_Idx.

Let verifier_env_step (j : 'I_T) (env : senv pgg_dtype) :=
  senv_recv env (player_idx j) DT_Sheet.

(** dealt_hand_content — the dealer's column after the fixed content readout:
    [seq content (rho w (start i)) | w <- W]. Kind: helper. What: bakes the plug's
    face/id readout into the wire so the revealed values are faces, not identities,
    while the wire stays 'I_N. Used-by: exchange_dealer. *)
Definition dealt_hand_content (content : 'I_N -> 'I_N) (W : seq gT) (i : 'I_T)
    : seq 'I_N :=
  [seq content (rho w (tnth starts i)) | w <- W].

(** dealt_hand_content_id — with the identity readout the content dealing is the
    plain [dealt_hand]. Kind: helper. What: dealt_hand_content id = dealt_hand.
    Why: position-model instances (content=id) reuse every existing dealt_hand
    fact and duality proof. Used-by: exchange_dealer id re-exports. *)
Lemma dealt_hand_content_id (W : seq gT) (i : 'I_T) :
  dealt_hand_content id W i = dealt_hand PI W i.
Proof. by rewrite /dealt_hand_content /dealt_hand. Qed.

(******************************************************************************)
(** * PGG Protocol Programs                                                   *)
(******************************************************************************)

(* Dealer program for T players.
   Phase 1 (ForList): deal hand(W, j) = [rho(w)(s_j) | w in W] to player j.
   Phase 2 (ForList): announce selection index P_idx to all players.
   The two ForList loops separate hand dealing (DT_Hand) from
   index announcement (DT_Idx) to keep session types uniform per loop. *)
Definition exchange_dealer (content : 'I_N -> 'I_N)
    (players : seq 'I_T) (W : seq gT) (P_idx : nat)
    : sproc pgg_dtype data dealer_idx :=
  \pi{ Init (@PGG_idx N P_idx) ;
     ForList players step S enstep dealer_hand_env as j cont k =>
       Deal<(player_idx j)> #(dealt_hand_content content W j) ;
       k
     end ;
     ForList players step S enstep dealer_idx_env as j cont k =>
       Announce<(player_idx j)> $(P_idx) ;
       k
     end ;
     Finish }.

(* Player i: receive dealt hand and selection index from dealer.
   Look up entry P_idx in hand to get card position rho(w_{P_idx})(s_i).
   Reveal this single card position to the verifier.
   nth ord0 is the default for out-of-bounds (never hit if P_idx < |W|). *)
Definition exchange_player (i : 'I_T)
    : sproc pgg_dtype data (player_idx i) :=
  \pi{ Receive<dealer_idx> #my_hand =>
     Receive<dealer_idx> $shuffle_idx =>
     Reveal<verifier_idx> &(nth ord0 my_hand shuffle_idx) ;
     Finish }.

(* Verifier: observe card position from each player into the Init buffer.
   After the loop, the buffer contains [rho(w)(s_0), ..., rho(w)(s_{T-1})].
   Reconstruction (applying recon to these T values) happens outside piSMC. *)
Definition exchange_verifier (players : seq 'I_T)
    : sproc pgg_dtype data verifier_idx :=
  \pi{ ForList players step (fun k => k.+2) enstep verifier_env_step as j cont k =>
       Observe<(player_idx j)> &ep =>
       Init (PGG_sheet ep) ;
       k
     end ;
     Finish }.

End pgg_pismc.

Arguments exchange_dealer {M} PI.
Arguments exchange_player {M} PI.
Arguments exchange_verifier {M} PI.

(******************************************************************************)
(** * Dealer from Words: Type-Safe Word-to-Protocol Bridge                    *)
(*                                                                            *)
(* exchange_dealer_from_words wraps exchange_dealer with word evaluation. The dealer samples   *)
(* w : L.-tuple 'I_Tg uniformly (offline/setup phase), evaluates word_eval w *)
(* to get a shuffle permutation, and feeds it to exchange_dealer for dealing.         *)
(******************************************************************************)

Section exchange_dealer_from_words.

Variable M : MonodromyReprWithGeneratorType.
Variable PI : PGGInterface M.

Let T := (pi_T' PI).+1.
Let Tg := (@pgg_ngens' M).+1.

(** exchange_dealer_from_words — dealer program taking a word-tuple and evaluating it.
    Kind: interface.
    Why: bridges the word-sampling layer (used in security analysis) to the
    permutation-level [exchange_dealer] program.
*)
Definition exchange_dealer_from_words (L : nat)
    (players : seq 'I_T) (w : L.-tuple 'I_Tg) (P_idx : nat) :=
  exchange_dealer PI id players [:: @word_eval M L w] P_idx.

End exchange_dealer_from_words.

Arguments exchange_dealer_from_words {M} PI.

(******************************************************************************)
(** * Session Type Duality Verification (Idealized, 2-party)                  *)
(******************************************************************************)

Section pgg_idealized_duality.

(* Idealized instance: full symmetric group S_N with identity representation.
   This makes all definitions concrete so native_compute can verify session
   type duality for all player pairs. We test the 2-player (T=2) case. *)
Variable n : nat.
Let N := n.+2.
Let gT : finGroupType := {perm 'I_N}.
Let G : {group gT} := [set: gT].

(* Identity morphism on permutation group *)
Lemma id_perm_morphM :
  {in G &, {morph (@id gT) : x y / (x * y)%g}}.
Proof. by []. Qed.

(** id_perm_morph — identity morphism on the full permutation group [G = [set: {perm 'I_N}]].
    Kind: instance.
    Why: provides [pgg_rho] for the idealized, fully symmetric instance used in
    [native_compute]-based duality verification.
*)
Definition id_perm_morph : {morphism G >-> {perm 'I_N}} :=
  Morphism id_perm_morphM.

(** Idealized_PGGTypes — PGG types record for the fully symmetric group [S_N].
    Kind: instance.
*)
Definition Idealized_PGGTypes := @MkPGG gT N.-1 G.

(** Idealized_isMonodromyRepr — monodromy mixin for [Idealized_PGGTypes] via identity.
    Kind: instance.
*)
Definition Idealized_isMonodromyRepr : isMonodromyRepr Idealized_PGGTypes.
Proof.
constructor.
rewrite /Idealized_PGGTypes /=.
exact: id_perm_morph.
Defined.

(** Idealized_MonodromyRepr — packaged [MonodromyReprType] for the idealized instance.
    Kind: instance.
*)
Definition Idealized_MonodromyRepr : MonodromyReprType :=
  @MonodromyRepr.Pack Idealized_PGGTypes
    (@MonodromyRepr.Class Idealized_PGGTypes Idealized_isMonodromyRepr).

(* 2-player interface: starts = [0, 1] *)
Let M := Idealized_MonodromyRepr.

(** test_starts_2 — two-player starting tuple [[0; 1]] for the idealized test instance.
    Kind: example.
*)
Definition test_starts_2 : 2.-tuple 'I_N :=
  [tuple @Ordinal N 0 isT; @Ordinal N 1 isT].

(** test_starts_2_uniq — the two test starts are distinct.
    Kind: helper.
    Why: discharges [pi_starts_uniq] for [Test_PGG_2].
    Used by: Test_PGG_2.
*)
Lemma test_starts_2_uniq : uniq test_starts_2.
Proof. by native_compute. Qed.

(** Test_PGG_2 — two-player idealized PGG interface for native-compute duality.
    Kind: example.
*)
Definition Test_PGG_2 : PGGInterface M :=
  @MkPGGI M 1 test_starts_2 test_starts_2_uniq.

Let PI := Test_PGG_2.
Let data := pgg_data (pgg_N' M).+1.

(* Concrete player list *)
Let players_2 : seq 'I_2 :=
  [:: @Ordinal 2 0 isT; @Ordinal 2 1 isT].

(* Variable data for programs *)
Variables (W : seq {perm 'I_N}) (P_idx : nat).

Local Open Scope sproc_scope.

(* Wrap as aprocs for duality checking *)
Definition ap_dealer_2 :=
  mk_aproc (exchange_dealer PI id players_2 W P_idx).
(** ap_player0_2 — player-0 program as an [aproc] for duality checking.
    Kind: example.
*)
Definition ap_player0_2 :=
  mk_aproc (exchange_player PI (@Ordinal 2 0 isT)).

(** ap_player1_2 — player-1 program as an [aproc] for duality checking.
    Kind: example.
*)
Definition ap_player1_2 :=
  mk_aproc (exchange_player PI (@Ordinal 2 1 isT)).

(** ap_verifier_2 — verifier program as an [aproc] for duality checking.
    Kind: example.
*)
Definition ap_verifier_2 :=
  mk_aproc (exchange_verifier PI players_2).

(* 4-process duality: all 6 pairs *)

(** dealer_player0_dual_2 — session duality between dealer and player 0 (idealized, T=2).
    Kind: main.
*)
Lemma dealer_player0_dual_2 : channels_dual ap_dealer_2 ap_player0_2.
Proof. by native_compute. Qed.

(** dealer_player1_dual_2 — session duality between dealer and player 1 (idealized, T=2).
    Kind: main.
*)
Lemma dealer_player1_dual_2 : channels_dual ap_dealer_2 ap_player1_2.
Proof. by native_compute. Qed.

(** dealer_verifier_dual_2 — session duality between dealer and verifier (idealized, T=2).
    Kind: main.
*)
Lemma dealer_verifier_dual_2 : channels_dual ap_dealer_2 ap_verifier_2.
Proof. by native_compute. Qed.

(** player0_player1_dual_2 — session duality between the two players (idealized, T=2).
    Kind: main.
*)
Lemma player0_player1_dual_2 : channels_dual ap_player0_2 ap_player1_2.
Proof. by native_compute. Qed.

(** player0_verifier_dual_2 — session duality between player 0 and verifier (idealized, T=2).
    Kind: main.
*)
Lemma player0_verifier_dual_2 : channels_dual ap_player0_2 ap_verifier_2.
Proof. by native_compute. Qed.

(** player1_verifier_dual_2 — session duality between player 1 and verifier (idealized, T=2).
    Kind: main.
*)
Lemma player1_verifier_dual_2 : channels_dual ap_player1_2 ap_verifier_2.
Proof. by native_compute. Qed.

End pgg_idealized_duality.

(******************************************************************************)
(** * Generic Duality via Gen_PGGTypes (parameterized N)                      *)
(******************************************************************************)

Section pgg_generated_duality.
(* Generic duality for ANY monodromy group via Gen_PGGTypes template.
   Parameterized by generator count (m+1) and card position count (n+2).
   Session type duality depends only on the player structure (T=2),
   not on N or the specific shuffle generators — this single verification
   covers all concrete instances:
   - OC(k, p):  m=k-1, n=k+p-3, overlapping p-cycles, N=k+p-1
                 e.g. OC(128, 3) gives N=130, practical encoding space
   - S_5:       m=3, n=3, adjacent transpositions, N=5
   - Star(m):   m=m, n=m+1, star-graph RAAG, N=m+3
   - Monster:   m=1, n=monster_n, axiomatized, N ~ 10^20             *)

Variable m n : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n.+2}.
Variables (W : seq {perm 'I_n.+2}) (P_idx : nat).

Let M_gen := Gen_PGGTypes sigmas.
Let PI_gen := Gen_PGG_2 sigmas.
Let players_2 : seq 'I_2 := [:: @Ordinal 2 0 isT; @Ordinal 2 1 isT].

Local Open Scope sproc_scope.

(** ap_dealer_gen — generic dealer program as an [aproc] for duality checking.
    Kind: instance.
*)
Definition ap_dealer_gen := mk_aproc (exchange_dealer PI_gen id players_2 W P_idx).
(** ap_player0_gen — generic player-0 program as an [aproc] for duality checking.
    Kind: instance.
*)
Definition ap_player0_gen := mk_aproc (exchange_player PI_gen (@Ordinal 2 0 isT)).
(** ap_player1_gen — generic player-1 program as an [aproc] for duality checking.
    Kind: instance.
*)
Definition ap_player1_gen := mk_aproc (exchange_player PI_gen (@Ordinal 2 1 isT)).
(** ap_verifier_gen — generic verifier program as an [aproc] for duality checking.
    Kind: instance.
*)
Definition ap_verifier_gen := mk_aproc (exchange_verifier PI_gen players_2).

(** dealer_player0_dual_gen — generic duality (parametric [m], [n]): dealer vs player 0.
    Kind: main.
*)
Lemma dealer_player0_dual_gen : channels_dual ap_dealer_gen ap_player0_gen.
Proof. by native_compute. Qed.

(** dealer_player1_dual_gen — generic duality: dealer vs player 1.
    Kind: main.
*)
Lemma dealer_player1_dual_gen : channels_dual ap_dealer_gen ap_player1_gen.
Proof. by native_compute. Qed.

(** dealer_verifier_dual_gen — generic duality: dealer vs verifier.
    Kind: main.
*)
Lemma dealer_verifier_dual_gen : channels_dual ap_dealer_gen ap_verifier_gen.
Proof. by native_compute. Qed.

(** player0_player1_dual_gen — generic duality: player 0 vs player 1.
    Kind: main.
*)
Lemma player0_player1_dual_gen : channels_dual ap_player0_gen ap_player1_gen.
Proof. by native_compute. Qed.

(** player0_verifier_dual_gen — generic duality: player 0 vs verifier.
    Kind: main.
*)
Lemma player0_verifier_dual_gen : channels_dual ap_player0_gen ap_verifier_gen.
Proof. by native_compute. Qed.

(** player1_verifier_dual_gen — generic duality: player 1 vs verifier.
    Kind: main.
*)
Lemma player1_verifier_dual_gen : channels_dual ap_player1_gen ap_verifier_gen.
Proof. by native_compute. Qed.

End pgg_generated_duality.
