(******************************************************************************)
(* Probe B (red) for the spec                                                 *)
(* docs/superpowers/plans/2026-08-12-s5-w45-sample-law-input-trace-spec.md.    *)
(*                                                                            *)
(* Every mutation of a probe-A claim is either refuted by a proved lemma or   *)
(* wrapped in Fail, so this file compiles exactly when each mutation is       *)
(* rejected. A mutation that started to succeed would break the compile.      *)
(*                                                                            *)
(* M1  C4 with the two factors of the product swapped                         *)
(* M2  C6 at the participant row 2 + i                                        *)
(* M3  C8(a) with the two committed sheets swapped                            *)
(* M4  C7 with the conditional entropy replaced by 0                          *)
(* M5  C8(b) with the conditional entropy replaced by the secret's entropy    *)
(* T3, T4, T5  the tautology probes on C3, C4, C5                             *)
(*                                                                            *)
(* M1, M4 and M5 are refuted positively, by a proved negation of the mutated  *)
(* claim. M2 and M3 are Fail-guarded proof attempts.                          *)
(*                                                                            *)
(* Probe file. Never Require Import-ed by a permanent file; edits no landed    *)
(* file.                                                                      *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext realType_ln fdist proba.
From infotheo Require Import variation_dist entropy.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_weighted_words.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    algebraic_rigidity input_encoding.
From pgg_smc Require Import pgl27_group pgl27_scheme pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_word_privacy pgl27_exec.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_scheme_I5 five_card_kim five_card_family.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_trace five_card_exec.
(* Probe A, the green file of this directory: its compiled claims C4, C7 and
   C8(b) are the targets of the mutations M1, M4 and M5 below. *)
Require Import probe_a_laws.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Section probe_b_mutations.

Variable R : realType.
Variable secretP : R.-fdist bool.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

(******************************************************************************)
(*     M1: C4 with the two factors of the product swapped                     *)
(******************************************************************************)

(* The swapped shape typechecks once both factors carry the same finite type:
   the map sends A * A to A * A and both sides are laws on A * A. Probe A's C4,
   the compiled form of its proof script, does not close it, and it is not a
   definitional identity either. *)
Goal forall (A : finType) (Pa Q : R.-fdist A) (g : A -> A),
  fdistmap (fun ab : A * A => (ab.1, g ab.2)) (Pa `x Q)
  = ((fdistmap g Q) `x Pa)%fdist.
move=> A Pa Q g.
Fail exact: probe_fdistmap_prodr.
Fail by [].
Abort.

(** mut_C4_swap_false — the swapped product shape fails at the two Dirac laws
    on bool.
    @main architecture: ~ (forall A Pa Q g, fdistmap (fun ab => (ab.1, g ab.2))
    (Pa `x Q) = fdistmap g Q `x Pa). *)
Lemma mut_C4_swap_false :
  ~ (forall (A : finType) (Pa Q : R.-fdist A) (g : A -> A),
       fdistmap (fun ab : A * A => (ab.1, g ab.2)) (Pa `x Q)
       = ((fdistmap g Q) `x Pa)%fdist).
Proof.
move=> /(_ _ (fdist1 true) (fdist1 false) idfun).
rewrite probe_fdistmap_prodr fdistmap1 /= => Heq.
have : ((fdist1 true) `x (fdist1 false)) (true, false)
     = ((fdist1 false) `x (fdist1 true)) (true, false) :> R by rewrite Heq.
rewrite !fdist_prodE !fdist1E /= mulr1 mul0r.
by move/eqP; rewrite oner_eq0.
Qed.

(******************************************************************************)
(*     M2: C6 at the participant row 2 + i                                    *)
(******************************************************************************)

(** mut_C6_row_size — seat 0's executed row has two entries.
    @main correctness: size (five_card_exec_player_raw_trace (a, b) w0 ord0)
    = 2. *)
Lemma mut_C6_row_size (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  size (@five_card_exec_player_raw_trace R eps Hlt Hgt Hspec L (a, b) w0 ord0)
  = 2.
Proof.
by rewrite five_card_exec_raw_traceE /den_boer_procs; vm_compute.
Qed.

(* The emptiness claim of C6 is false at a participant row: the same
   unfold-then-vm_compute that closes the committing rows 7 and 8 leaves a
   two-entry row here. *)
Goal forall (a b : bool) (w0 : pgg_gT FiveCardKim_M),
  @five_card_exec_player_raw_trace R eps Hlt Hgt Hspec L (a, b) w0 ord0 = [::].
move=> a b w0; rewrite five_card_exec_raw_traceE /den_boer_procs.
Fail (vm_compute; reflexivity).
Abort.

(******************************************************************************)
(*     M3: C8(a) with the two committed sheets swapped                        *)
(******************************************************************************)

(* The dealer's row conses the receives, so the party-8 sheet (bit b) heads the
   two sheets; the a-then-b order is rejected. *)
Goal forall (a b : bool) (w0 : pgg_gT FiveCardKim_M),
  nth [::] (run_interp 100 (den_boer_procs a b w0 0)).2 0
  = [:: PGG_idx 0; PGG_sheet (encode_bool a); PGG_sheet (encode_bool b)].
move=> a b w0; rewrite /den_boer_procs.
Fail (vm_compute; reflexivity).
Abort.

(******************************************************************************)
(*     M4, M5: the two conditional entropies of C7 and C8(b)                  *)
(******************************************************************************)

(** mut_secret_entropy_gt0 — the den Boer secret has positive entropy, since
    log 3 < log 4 = 2 bounds the value 2 - (3/4) log 3 of H_secret below by
    1/2.
    @composes: mut_C7_zero_false *)
Lemma mut_secret_entropy_gt0 : 0 < `H `p_ (Secret R).
Proof.
have Hlog3 : log (3%:R : R) < 2.
  by rewrite -log4; apply: ltr_log; rewrite ?ltr0n ?ltr_nat.
rewrite H_secret subr_gt0.
apply: (@lt_le_trans _ _ (3%:R / 4%:R * 2%:R)).
  by rewrite ltr_pM2l ?Hlog3// divr_gt0 ?ltr0n.
by rewrite mulrAC -natrM ler_pdivrMr ?ltr0n// -natrM ler_nat.
Qed.

(** mut_C7_zero_false — the input-row conditional entropy of C7 is not zero,
    at every j: the mutation of C7 to = 0 would collapse the secret's entropy.
    @main security: `H( Secret | probe_input_view j ) != 0. *)
Lemma mut_C7_zero_false (j : nat) :
  `H( Secret R | probe_input_view Hlt Hgt Hspec L j ) != 0.
Proof.
by rewrite probe_C7; apply: lt0r_neq0; exact: mut_secret_entropy_gt0.
Qed.

(** mut_C8b_neq_entropy — the dealer-row conditional entropy of C8(b) is not
    the secret's entropy: the mutation of C8(b) to = `H `p_ Secret would make
    that entropy zero.
    @main security: `H( Secret | probe_dealer_view ) <> `H `p_ Secret. *)
Lemma mut_C8b_neq_entropy :
  `H( Secret R | probe_dealer_view Hlt Hgt Hspec L ) <> `H `p_ (Secret R).
Proof.
by rewrite probe_C8b => H0; move: mut_secret_entropy_gt0; rewrite -H0 ltxx.
Qed.

(******************************************************************************)
(*     T3, T4, T5: the tautology probes                                       *)
(******************************************************************************)

Section tautology_C4.
Variables (A B C : finType).
Variables (Pa : R.-fdist A) (Q : R.-fdist B) (g : B -> C).

(* T4: C4 is not a definitional tautology. *)
Goal fdistmap (fun ab : A * B => (ab.1, g ab.2)) (Pa `x Q)
  = (Pa `x (fdistmap g Q))%fdist.
Fail by [].
Abort.

End tautology_C4.

(* T3: C3 is not a definitional tautology. *)
Goal five_card_sample_cut_dist Hlt Hgt Hspec L
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)).
Fail by [].
Abort.

(* T5: C5 is not a definitional tautology. *)
Goal fdistmap (fun u : pgl27_word_sampleT => (u.1, pgl27_word_cut R u))
    (pgl27_word_sampleP secretP)
  = pgl27P_word_gen secretP.
Fail by [].
Abort.

End probe_b_mutations.

Print Assumptions mut_C4_swap_false.
Print Assumptions mut_secret_entropy_gt0.
Print Assumptions mut_C7_zero_false.
Print Assumptions mut_C8b_neq_entropy.
