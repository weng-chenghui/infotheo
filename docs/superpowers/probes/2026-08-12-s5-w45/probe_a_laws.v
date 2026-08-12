(******************************************************************************)
(* Probe A (green) for the spec                                               *)
(* docs/superpowers/plans/2026-08-12-s5-w45-sample-law-input-trace-spec.md:    *)
(* claims C1-C8 stated at the pinned carriers and driven to Qed.              *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section probe_s5_w45.

Variable R : realType.
Variable secretP : R.-fdist bool.
Variable eps : R.
Hypothesis Hlt : eps < 5%:R^-1.
Hypothesis Hgt : - (4%:R * 5%:R^-1) < eps.
Hypothesis Hspec : `|eps| < 4%:R / 5%:R.
Variable L : nat.

(******************************************************************************)
(*     C1 (W4): the word-space coalition law                                  *)
(******************************************************************************)

(** probe_C1 — the executed coalition law under the word shuffle is the law of
    the orbit shares at the evaluated word's images of the coalition's starts.
    @main architecture: pgl27_word_sample_coalition_dist C = fdistmap
    (sa_static_coalition_view pgl27_word_sample pgl27_content_obs C)
    pgl27_word_sampleP. *)
Lemma probe_C1 (C : {set 'I_(pi_T' (mp_PI (pgl27_profile R))).+1}) :
  pgl27_word_sample_coalition_dist secretP C
  = fdistmap (@sa_static_coalition_view R (pgl27_profile R) (pgl27_exec_plug R)
                (pgl27_word_sample secretP) (@pgl27_content_obs R) C)
      (pgl27_word_sampleP secretP).
Proof. by apply: sa_coalition_distE => u; exact: pgl27_exec_endpoints. Qed.

(******************************************************************************)
(*     C2 (W5, witness tie): the exact sample's cut law                       *)
(******************************************************************************)

(** probe_C2 — the exact sample space's cut law is the profile's own shuffle
    distribution.
    @main architecture: sa_cut_dist pgl27_sample = pgl27_witness_cut_dist. *)
Lemma probe_C2 :
  @sa_cut_dist R (pgl27_profile R) (pgl27_exec_plug R) (pgl27_sample R)
  = pgl27_witness_cut_dist R.
Proof.
rewrite /sa_cut_dist /pgl27_witness_cut_dist /pgl27_sample /=.
rewrite pgl27_sample_witness_prodE.
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(******************************************************************************)
(*     C3 (W5, rotation tie): the five-card sample's cut law                  *)
(******************************************************************************)

(** probe_card_bool2 — the pair of committed bits has four values.
    @composes: probe_omega_prodE *)
Lemma probe_card_bool2 : #|{: bool * bool}| = 3.+1.
Proof. by rewrite card_prod card_bool. Qed.

(** probe_omega_prodE — the den Boer leakage law is the product of the uniform
    law on the committed pair with the uniform law on the rotation.
    @composes: probe_omega_snd_uniform *)
Lemma probe_omega_prodE :
  five_card_leakage.P R
  = ((fdist_uniform probe_card_bool2) `x (fdist_uniform (card_ord 5)))%fdist.
Proof.
apply/fdist_ext => -[ab k].
rewrite fdist_prodE /five_card_leakage.P !fdist_uniformE.
rewrite card_Omega20 probe_card_bool2 card_ord.
by rewrite -invfM -natrM.
Qed.

(** probe_omega_snd_uniform — the rotation marginal of the den Boer leakage law
    is uniform on 'I_5.
    @composes: probe_C3 *)
Lemma probe_omega_snd_uniform :
  fdistmap (fun u : five_card_leakage.Omega => u.2) (five_card_leakage.P R)
  = fdist_uniform (card_ord 5).
Proof.
rewrite probe_omega_prodE.
by rewrite -/(fdist_snd _) -fdistX_prod fdistX2 fdist_prod1.
Qed.

(** probe_C3 — the five-card sample space's cut law is the image of the uniform
    rotation law under k |-> fc_sigma ^+ k.
    @main architecture: five_card_sample_cut_dist = fdistmap
    (fun k : 'I_5 => (fc_sigma ^+ k)%g) (fdist_uniform (card_ord 5)). *)
Lemma probe_C3 :
  five_card_sample_cut_dist Hlt Hgt Hspec L
  = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
      (fdist_uniform (card_ord 5)).
Proof.
rewrite /five_card_sample_cut_dist /sa_cut_dist /five_card_sample /=.
rewrite /five_card_sample_cut -probe_omega_snd_uniform.
by rewrite fdistmap_comp.
Qed.

(******************************************************************************)
(*     C4 (S5-1, generic): the product map on the second component            *)
(******************************************************************************)

(** probe_fdistmap_prodr — mapping the second component of a product law is the
    product with the mapped second factor.
    @main architecture: fdistmap (fun ab => (ab.1, g ab.2)) (P `x Q) =
    P `x fdistmap g Q. *)
Lemma probe_fdistmap_prodr (A B C : finType)
    (Pa : R.-fdist A) (Q : R.-fdist B) (g : B -> C) :
  fdistmap (fun ab : A * B => (ab.1, g ab.2)) (Pa `x Q)
  = (Pa `x (fdistmap g Q))%fdist.
Proof.
apply/fdist_ext => -[a c].
rewrite fdistmapE fdist_prodE fdistmapE.
rewrite (eq_big (fun a0 : A * B => (a0.1 == a) && (g a0.2 == c))
                (fun a0 : A * B => Pa a0.1 * Q a0.2)); first last.
- by move=> i _; rewrite fdist_prodE.
- by case=> x y; rewrite !inE.
rewrite (reindex_onto (fun b : B => (a, b)) snd) /=;
  last by case=> x y /andP[] /= /eqP -> _.
rewrite big_distrr /=; apply: eq_bigl => j.
by rewrite !eqxx andbT andTb.
Qed.

(******************************************************************************)
(*     C5 (S5-1, instance): the word sample's joint law                       *)
(******************************************************************************)

(** probe_C5 — the joint law of the word sample's secret and evaluated cut is
    the generic word-shuffle sample law.
    @main architecture: fdistmap (fun u => (u.1, pgl27_word_cut u))
    pgl27_word_sampleP = pgl27P_word_gen secretP. *)
Lemma probe_C5 :
  fdistmap (fun u : pgl27_word_sampleT => (u.1, pgl27_word_cut R u))
    (pgl27_word_sampleP secretP)
  = pgl27P_word_gen secretP.
Proof.
rewrite /pgl27_word_sampleP /pgl27P_word_gen /pgl27_word_cut /rho_word.
rewrite /rho_from_words_weighted /pgl27_word_wordP.
exact: probe_fdistmap_prodr.
Qed.

(** probe_C5_sa — the same identity written through the adapter's own argument
    and cut projections.
    @main architecture: fdistmap (fun u => (sa_arg u, sa_cut u)) sa_sampleP =
    pgl27P_word_gen secretP at pgl27_word_sample. *)
Lemma probe_C5_sa :
  fdistmap (fun u : sa_sampleT (pgl27_word_sample secretP) =>
              ((pgl27_word_sample secretP).(sa_arg) u,
               (pgl27_word_sample secretP).(sa_cut) u))
    ((pgl27_word_sample secretP).(sa_sampleP))
  = pgl27P_word_gen secretP.
Proof.
rewrite /pgl27_word_sample /= /pgl27_word_sampleP /pgl27P_word_gen.
rewrite /pgl27_word_cut /rho_word /rho_from_words_weighted /pgl27_word_wordP.
exact: probe_fdistmap_prodr.
Qed.

(******************************************************************************)
(*     C6 (S5-2): the committing parties' rows are empty                      *)
(******************************************************************************)

(* Honest scope: the rows are empty because in this interpreter model a Send
   logs nothing to the sender's own trace (smc_interpreter.v, step); the
   committing parties are pure senders (pgg_input_commitment.v, pgg_commit).
   Rows past the process count are empty by the nth default. This is a
   statement about the committing parties' own executed rows, not about
   commitment privacy: the committed payloads travel to the dealer's row, which
   probe_C8a and probe_C8b_fun show determines both bits. *)

(** probe_run_traces_size — the den Boer run has nine trace rows.
    @composes: probe_C6 *)
Lemma probe_run_traces_size (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  size (run_interp 100 (den_boer_procs a b w0 0)).2 = 9.
Proof. rewrite /den_boer_procs; vm_compute; reflexivity. Qed.

(** probe_C6 — committing party j's executed row is empty, at every j.
    @main security: five_card_exec_input_raw_trace (a, b) w0 j = [::]. *)
Lemma probe_C6 (a b : bool) (w0 : pgg_gT FiveCardKim_M) (j : nat) :
  five_card_exec_input_raw_trace Hlt Hgt Hspec L (a, b) w0 j = [::].
Proof.
rewrite /five_card_exec_input_raw_trace /exec_input_trace /exec_input_id
        /exec_run five_card_exec_fuelE five_card_exec_procsE.
case: j => [|[|j]].
- by rewrite /den_boer_procs; vm_compute.
- by rewrite /den_boer_procs; vm_compute.
- by apply: nth_default; rewrite probe_run_traces_size.
Qed.

(******************************************************************************)
(*     C7 (S5-2): the input-row observable leaks nothing                      *)
(******************************************************************************)

(** probe_input_view — committing party j's executed-row content as a random
    variable on the den Boer leakage space.
    @intent: content_of of five_card_exec_input_raw_trace at the committed pair
    (w.1.1, w.1.2) and the cut fc_sigma ^+ w.2. *)
Definition probe_input_view (j : nat) : {RV (five_card_leakage.P R) -> 'I_5} :=
  fun w => content_of (five_card_exec_input_raw_trace Hlt Hgt Hspec L
                         (w.1.1, w.1.2) (five_card_group.fc_sigma ^+ w.2)%g j).

(** probe_C7 — conditioning the secret on committing party j's executed-row
    observable leaves its entropy unchanged, at every j.
    @main security: `H( Secret | probe_input_view j ) = `H `p_ Secret. *)
Lemma probe_C7 (j : nat) :
  `H( Secret R | probe_input_view j ) = `H `p_ (Secret R).
Proof.
have Hc : probe_input_view j
        = (fun _ : unit => ord0) `o (unit_RV (five_card_leakage.P R)).
  apply: funext => w.
  by rewrite /probe_input_view /comp_RV probe_C6.
rewrite Hc; apply: extra_entropy.inde_cond_entropy.
apply: pgg_trace_secrecy.inde_RV_comp; exact: spp_proba.inde_unit_RV.
Qed.

(******************************************************************************)
(*     C8 (S5-2): the dealer's row determines both committed bits             *)
(******************************************************************************)

(** probe_exec_dealer_trace — the dealer's executed row.
    @intent: entry exec_dealer_id of exec_run.2 at five_card_exec_plug and
    process offset 0. *)
Definition probe_exec_dealer_trace (x : bool * bool) (w0 : pgg_gT FiveCardKim_M) :=
  nth [::] (@exec_run R (five_card_profile Hlt Hgt Hspec L)
              (five_card_exec_plug Hlt Hgt Hspec L) x w0 0).2 exec_dealer_id.

(** probe_C8a — the dealer's executed row is the deck index followed by the two
    committed sheets, the later receive at the head.
    @main architecture: probe_exec_dealer_trace (a, b) w0 = [:: PGG_idx 0;
    PGG_sheet (encode_bool b); PGG_sheet (encode_bool a)]. *)
Lemma probe_C8a (a b : bool) (w0 : pgg_gT FiveCardKim_M) :
  probe_exec_dealer_trace (a, b) w0
  = [:: PGG_idx 0; PGG_sheet (encode_bool b); PGG_sheet (encode_bool a)].
Proof.
rewrite /probe_exec_dealer_trace /exec_dealer_id /exec_run
        five_card_exec_fuelE five_card_exec_procsE.
rewrite /den_boer_procs; vm_compute; reflexivity.
Qed.

(** probe_dealer_readout — the committed pair decoded from a dealer row.
    @intent: decode_bool of the two sheets of a three-entry row, the second bit
    at the head, and (false, false) elsewhere. *)
Definition probe_dealer_readout
    (tr : seq (pgg_data (pgg_N' FiveCardKim_M).+1)) : (bool * bool)%type :=
  if tr is [:: _ ; PGG_sheet y ; PGG_sheet x] then (decode_bool x, decode_bool y)
  else (false, false).

(** probe_dealer_view — the dealer's executed row decoded as a random variable
    on the den Boer leakage space.
    @intent: probe_dealer_readout of probe_exec_dealer_trace at the committed
    pair (w.1.1, w.1.2) and the cut fc_sigma ^+ w.2. *)
Definition probe_dealer_view : {RV (five_card_leakage.P R) -> (bool * bool)%type} :=
  fun w => probe_dealer_readout (probe_exec_dealer_trace (w.1.1, w.1.2)
             (five_card_group.fc_sigma ^+ w.2)%g).

(** probe_C8b_fun — the dealer's decoded row is the sampled committed pair.
    @main security: probe_dealer_view = fun w => (w.1.1, w.1.2). *)
Lemma probe_C8b_fun : probe_dealer_view = fun w => (w.1.1, w.1.2).
Proof.
apply: funext => w.
by rewrite /probe_dealer_view probe_C8a /probe_dealer_readout /= !decode_encode_bool.
Qed.

(** probe_C8b — the dealer's decoded row determines the secret.
    @main security: `H( Secret | probe_dealer_view ) = 0. *)
Lemma probe_C8b : `H( Secret R | probe_dealer_view ) = 0.
Proof.
have -> : Secret R = (fun p : bool * bool => p.1 && p.2) `o probe_dealer_view.
  apply: funext => w; rewrite /comp_RV probe_C8b_fun /=.
  by case: w => -[a b] k.
exact: centropy_RV_comp0.
Qed.

End probe_s5_w45.

(** probe_five_card_hypotheses_at_zero — the three five-card side conditions
    hold at eps = 0.
    @main correctness: 0 < 5^-1, - (4 * 5^-1) < 0 and `|0| < 4 / 5. *)
Example probe_five_card_hypotheses_at_zero (R : realType) :
  (0 : R) < 5%:R^-1 /\ - (4%:R * 5%:R^-1) < (0 : R) /\ `|(0 : R)| < 4%:R / 5%:R.
Proof.
split; [exact: den_boer_eps0_lt |].
by split; [exact: den_boer_eps0_gt | exact: den_boer_eps0_spectral].
Qed.

Print Assumptions probe_C1.
Print Assumptions probe_C2.
Print Assumptions probe_C3.
Print Assumptions probe_fdistmap_prodr.
Print Assumptions probe_C5.
Print Assumptions probe_C5_sa.
Print Assumptions probe_C6.
Print Assumptions probe_C7.
Print Assumptions probe_C8a.
Print Assumptions probe_C8b_fun.
Print Assumptions probe_C8b.
Print Assumptions probe_five_card_hypotheses_at_zero.

(** probe_C6_at_zero — committing party j's executed row is empty at the
    eps = 0 witnesses of the den Boer family and L = 1.
    @main security: five_card_exec_input_raw_trace (den_boer_eps0_lt R)
    (den_boer_eps0_gt R) (den_boer_eps0_spectral R) 1 (a, b) w0 j = [::]. *)
Example probe_C6_at_zero (R : realType) (a b : bool)
    (w0 : pgg_gT FiveCardKim_M) (j : nat) :
  five_card_exec_input_raw_trace (den_boer_eps0_lt R) (den_boer_eps0_gt R)
    (den_boer_eps0_spectral R) 1%N (a, b) w0 j = [::].
Proof. exact: probe_C6. Qed.

Print Assumptions probe_C6_at_zero.
