(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism.
From mathcomp Require Import boolp reals.
Require Import smc_interpreter pismc smc_session_types.
Require Import pgg_interface pgg_session_types.
Require Import pgg_weval_inj.
Require Import pgg_raag_star.
Require Import pgg_oc_param.
Require Import pgg_abelian.
From pgg_smc Require Import pgg_security_solver.
From pgg_reconstruct Require Import algebraic_rigidity.
From pgg_reconstruct Require Import rigidity_monster_instance.
From pgg_reconstruct Require Import rigidity_abelian_instance.

(******************************************************************************)
(* PGG: piSMC Protocol Programs                                               *)
(*                                                                            *)
(* Types involved:                                                            *)
(*   generator index ('I_Tg) -- a "shuffle type": picks one of Tg shuffles   *)
(*   word (L.-tuple 'I_Tg)  -- a sequence of L shuffle selections            *)
(*   group element (gT)      -- word_eval(w) = sigma_{w_0} * ... * sigma_{w_{L-1}} *)
(*                              a permutation in G <= S_N                    *)
(*   card position ('I_N)    -- a position in {0,..,N-1} that perms act on   *)
(*   endpoint : 'I_N         -- rho(g)(s), the card position after shuffle g *)
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
(*    permutation (invisible to reconstruction by ts_perm_compatible).       *)
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
(*   pdealer players W P_idx == dealer deals hands and announces selection   *)
(*   pplayer i               == player i computes and reveals card position  *)
(*   pverifier players       == verifier observes card positions             *)
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

(******************************************************************************)
(** * PGG Protocol Programs                                                   *)
(******************************************************************************)

(* Dealer program for T players.
   Phase 1 (ForList): deal hand(W, j) = [rho(w)(s_j) | w in W] to player j.
   Phase 2 (ForList): announce selection index P_idx to all players.
   The two ForList loops separate hand dealing (DT_Hand) from
   index announcement (DT_Idx) to keep session types uniform per loop. *)
Definition pdealer (players : seq 'I_T) (W : seq gT) (P_idx : nat)
    : sproc pgg_dtype data dealer_idx :=
  \pi{ Init (@PGG_idx N P_idx) ;
     ForList players step S enstep dealer_hand_env as j cont k =>
       Deal<(player_idx j)> #(dealt_hand PI W j) ;
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
Definition pplayer (i : 'I_T)
    : sproc pgg_dtype data (player_idx i) :=
  \pi{ Receive<dealer_idx> #my_hand =>
     Receive<dealer_idx> $shuffle_idx =>
     Reveal<verifier_idx> &(nth ord0 my_hand shuffle_idx) ;
     Finish }.

(* Verifier: observe card position from each player into the Init buffer.
   After the loop, the buffer contains [rho(w)(s_0), ..., rho(w)(s_{T-1})].
   Reconstruction (applying recon to these T values) happens outside piSMC. *)
Definition pverifier (players : seq 'I_T)
    : sproc pgg_dtype data verifier_idx :=
  \pi{ ForList players step (fun k => k.+2) enstep verifier_env_step as j cont k =>
       Observe<(player_idx j)> &ep =>
       Init (PGG_sheet ep) ;
       k
     end ;
     Finish }.

End pgg_pismc.

Arguments pdealer {M} PI.
Arguments pplayer {M} PI.
Arguments pverifier {M} PI.

(******************************************************************************)
(** * Dealer from Words: Type-Safe Word-to-Protocol Bridge                    *)
(*                                                                            *)
(* dealer_from_words wraps pdealer with word evaluation. The dealer samples   *)
(* w : L.-tuple 'I_Tg uniformly (offline/setup phase), evaluates word_eval w *)
(* to get a shuffle permutation, and feeds it to pdealer for dealing.         *)
(******************************************************************************)

Section dealer_from_words.

Variable M : GeneratedMonodromyReprType.
Variable PI : PGGInterface M.

Let T := (pi_T' PI).+1.
Let Tg := (@pgg_ngens' M).+1.

Definition dealer_from_words (L : nat)
    (players : seq 'I_T) (w : L.-tuple 'I_Tg) (P_idx : nat) :=
  pdealer PI players [:: @word_eval M L w] P_idx.

End dealer_from_words.

Arguments dealer_from_words {M} PI.

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

Definition id_perm_morph : {morphism G >-> {perm 'I_N}} :=
  Morphism id_perm_morphM.

Definition Idealized_PGGTypes := @MkPGG gT N.-1 G.

Definition Idealized_isMonodromyRepr : isMonodromyRepr Idealized_PGGTypes.
Proof.
constructor.
rewrite /Idealized_PGGTypes /=.
exact: id_perm_morph.
Defined.

Definition Idealized_MonodromyRepr : MonodromyReprType :=
  @MonodromyRepr.Pack Idealized_PGGTypes
    (@MonodromyRepr.Class Idealized_PGGTypes Idealized_isMonodromyRepr).

(* 2-player interface: starts = [0, 1] *)
Let M := Idealized_MonodromyRepr.

Definition test_starts_2 : 2.-tuple 'I_N :=
  [tuple @Ordinal N 0 isT; @Ordinal N 1 isT].

Lemma test_starts_2_uniq : uniq test_starts_2.
Proof. by native_compute. Qed.

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
  mk_aproc (pdealer PI players_2 W P_idx).
Definition ap_player0_2 :=
  mk_aproc (pplayer PI (@Ordinal 2 0 isT)).
Definition ap_player1_2 :=
  mk_aproc (pplayer PI (@Ordinal 2 1 isT)).
Definition ap_verifier_2 :=
  mk_aproc (pverifier PI players_2).

(* 4-process duality: all 6 pairs *)
Lemma dealer_player0_dual_2 : channels_dual ap_dealer_2 ap_player0_2.
Proof. by native_compute. Qed.

Lemma dealer_player1_dual_2 : channels_dual ap_dealer_2 ap_player1_2.
Proof. by native_compute. Qed.

Lemma dealer_verifier_dual_2 : channels_dual ap_dealer_2 ap_verifier_2.
Proof. by native_compute. Qed.

Lemma player0_player1_dual_2 : channels_dual ap_player0_2 ap_player1_2.
Proof. by native_compute. Qed.

Lemma player0_verifier_dual_2 : channels_dual ap_player0_2 ap_verifier_2.
Proof. by native_compute. Qed.

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

Definition ap_dealer_gen := mk_aproc (pdealer PI_gen players_2 W P_idx).
Definition ap_player0_gen := mk_aproc (pplayer PI_gen (@Ordinal 2 0 isT)).
Definition ap_player1_gen := mk_aproc (pplayer PI_gen (@Ordinal 2 1 isT)).
Definition ap_verifier_gen := mk_aproc (pverifier PI_gen players_2).

Lemma dealer_player0_dual_gen : channels_dual ap_dealer_gen ap_player0_gen.
Proof. by native_compute. Qed.

Lemma dealer_player1_dual_gen : channels_dual ap_dealer_gen ap_player1_gen.
Proof. by native_compute. Qed.

Lemma dealer_verifier_dual_gen : channels_dual ap_dealer_gen ap_verifier_gen.
Proof. by native_compute. Qed.

Lemma player0_player1_dual_gen : channels_dual ap_player0_gen ap_player1_gen.
Proof. by native_compute. Qed.

Lemma player0_verifier_dual_gen : channels_dual ap_player0_gen ap_verifier_gen.
Proof. by native_compute. Qed.

Lemma player1_verifier_dual_gen : channels_dual ap_player1_gen ap_verifier_gen.
Proof. by native_compute. Qed.

End pgg_generated_duality.

(******************************************************************************)
(** * Monster Group Duality (N ~ 10^20 card positions)                        *)
(******************************************************************************)

Section pgg_monster_duality.
(* Monster group M: N ~ 10^20 card positions — large encoding space.
   Instantiates generic duality with axiomatized generators.
   No native_compute needed — the generic proof already covers this case.
   Shows PGG scales to arbitrarily large card decks. *)

Variables (W : seq {perm 'I_monster_n.+2}) (P_idx : nat).

Definition dealer_player0_dual_mon :=
  @dealer_player0_dual_gen 1 monster_n monster_sigmas W P_idx.

Definition dealer_player1_dual_mon :=
  @dealer_player1_dual_gen 1 monster_n monster_sigmas W P_idx.

Definition dealer_verifier_dual_mon :=
  @dealer_verifier_dual_gen 1 monster_n monster_sigmas W P_idx.

Definition player0_player1_dual_mon :=
  @player0_player1_dual_gen 1 monster_n monster_sigmas.

Definition player0_verifier_dual_mon :=
  @player0_verifier_dual_gen 1 monster_n monster_sigmas.

Definition player1_verifier_dual_mon :=
  @player1_verifier_dual_gen 1 monster_n monster_sigmas.

End pgg_monster_duality.

(******************************************************************************)
(** * Concrete Group Instances, T=4 Players via CertifiedSolution             *)
(*                                                                            *)
(*   Star(m)    : N=m+3,       Tg=m+1,  RAAG with commuting leaves          *)
(*   OC(k,p)    : N=k+p+3,    Tg=k+1,  overlapping (p+3)-cycles            *)
(*   Monster    : N~10^20,    Tg=2,    axiomatized 2-generated              *)
(*   Abelian(m) : N=2*(m+1),  Tg=m+1,  disjoint transpositions (insecure)  *)
(* Each parameterized by CertifiedSolution cs: solver determines L, eps.    *)
(******************************************************************************)

(* --- Section A: Star(m) — RAAG, N=m+3, T=4 --- *)

Section pgg_star_protocol.

Variable R : realType.
Variable m : nat.
Hypothesis Hm : (1 <= m)%N.

Let R_star : GeneratedMonodromyReprType := Gen_PGGTypes (star_gen_tuple m).
Variable cs : CertifiedSolution R R_star.
Let L := sp_L (cs_params cs).

Lemma star_4_le_N : 4 <= m.+3.
Proof. by rewrite -[4]/(1).+3 ltnS. Qed.

Let star_PI := @Gen_PGG_T R_star 3 star_4_le_N.
Let players := enum 'I_4.
Variable P_idx : nat.

Definition star4_dealer (w : L.-tuple 'I_m.+1) :=
  dealer_from_words star_PI L players w P_idx.
Definition star4_player (i : 'I_4) := pplayer star_PI i.
Definition star4_verifier := pverifier star_PI players.

End pgg_star_protocol.

(* --- Section B: OC(k,p) — parametric overlapping cycles, N=k+p+3, T=4 --- *)

Section pgg_oc_protocol.

Variable R : realType.
Variable k p : nat.
Hypothesis Hkp : (1 <= k + p)%N.

(* OC tuple cast: k + p.+3 = (k+p).+3 = ((k+p).+1).+2 to match Gen_PGGTypes *)
Let oc_param_tuple' : k.+1.-tuple {perm 'I_(k+p).+3}.
Proof. by rewrite -addnS -addnS -addnS; exact: oc_param_tuple k p. Defined.

Let R_oc : GeneratedMonodromyReprType :=
  @Gen_PGGTypes k (k + p).+1 oc_param_tuple'.
Variable cs : CertifiedSolution R R_oc.
Let L := sp_L (cs_params cs).

Lemma oc_4_le_N : 4 <= (k + p).+3.
Proof. by []. Qed.

Let oc_PI := @Gen_PGG_T R_oc 3 oc_4_le_N.
Let players := enum 'I_4.
Variable P_idx : nat.

Definition oc4_dealer (w : L.-tuple 'I_k.+1) :=
  dealer_from_words oc_PI L players w P_idx.
Definition oc4_player (i : 'I_4) := pplayer oc_PI i.
Definition oc4_verifier := pverifier oc_PI players.

End pgg_oc_protocol.

(* --- Section C: Monster — N ~ 10^20, T=4 --- *)

Section pgg_monster_protocol.

Variable R : realType.
Hypothesis Hmon : (4 <= monster_n.+2)%N.

Let R_mon : GeneratedMonodromyReprType := Gen_PGGTypes monster_sigmas.
Variable cs : CertifiedSolution R R_mon.
Let L := sp_L (cs_params cs).

Let mon_PI := @Gen_PGG_T R_mon 3 Hmon.
Let players := enum 'I_4.
Variable P_idx : nat.

Definition mon4_dealer (w : L.-tuple 'I_2) :=
  dealer_from_words mon_PI L players w P_idx.
Definition mon4_player (i : 'I_4) := pplayer mon_PI i.
Definition mon4_verifier := pverifier mon_PI players.

End pgg_monster_protocol.

(* --- Section D: Abelian(m) — disjoint transpositions, insecure --- *)

Section pgg_abelian_protocol.
(* Abelian instance: m+1 disjoint transpositions, N = 2*(m+1), T = 4.
   Demonstrates protocol-level INSECURITY: abelian groups have
   linear trace growth (n_traces ~ 2L+1), so epsilon stays large
   regardless of shuffle count L. *)

Variable R : realType.
Variable m : nat.
Hypothesis Hm : (1 <= m)%N.

Let R_abel : GeneratedMonodromyReprType := Gen_PGGTypes (dt_gen_tuple m).
Variable cs : CertifiedSolution R R_abel.
Let L := sp_L (cs_params cs).

Lemma abel_4_le_N : 4 <= m.+1.*2.
Proof. by rewrite -[4]/(1.+1.*2) leq_double. Qed.

Let abel_PI := @Gen_PGG_T R_abel 3 abel_4_le_N.
Let players := enum 'I_4.
Variable P_idx : nat.

Definition abel4_dealer (w : L.-tuple 'I_m.+1) :=
  dealer_from_words abel_PI L players w P_idx.
Definition abel4_player (i : 'I_4) := pplayer abel_PI i.
Definition abel4_verifier := pverifier abel_PI players.

End pgg_abelian_protocol.
