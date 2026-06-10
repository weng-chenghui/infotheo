(* DSDP output-channel secrecy: the guessing experiment on the derived
   output-exposing endpoint game and the SSProve-to-Infotheo probability
   connector.

   The output-exposing endpoint games real_game_leak_S / zero_game_leak_S
   (dsdp_indcpa_security) expose Alice's view together with the scalar-product
   output S.  This file builds the absolute-probability guessing layer on those
   games: a predictor reads (view, S) and names a guess, the challenger tests
   guess = V_2, and the closed experiment's success probability is rewritten as
   an Infotheo distribution probability.  That rewrite (the connector
   guess_success_sdistr_eq_fdist) is the single identity through which the
   information-theoretic fiber bound 1/m, proved Infotheo-side, transfers to the
   SSProve-side absolute probability. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
From SSProve.Crypt Require Import HybridArgument.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code.
Require Import dsdp_symbolic.
Require Import dsdp_game_symbolic.
Require Import dsdp_indcpa_security.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(* Pin SSProve's real type as the ambient realType for this file. *)
Notation R := SSProve.Crypt.Axioms.R.

Section dsdp_security_indcpa_fiber.
(* The concrete scheme and marshalling fixed by the output-exposing endpoint
   games (same parameters as dsdp_advantage_derived_leak_S). *)
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (msg_of_chmsg : t_msg -> plain AHE) (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (cipher_of_chcipher : t_cipher -> cipher AHE)
  (chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg)
  (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher) (in custom pack_type at level 2).

(* id_guess — the predictor's operation identifier (the game oracles
   id_game_run/id_v2_get/id_s_get take 0/2/3, so 1 is free). *)
Definition id_guess : nat := 1%N.

(* guesser_export — the predictor's export interface: one operation reading the
   pair (Alice's ciphertext view, the output S) and returning a guess. *)
Definition guesser_export : Interface :=
  [interface #val #[ id_guess ] : (ciphers × msg) → msg ].

(* predictor_guesser — a closed predictor: imports nothing, exports the guess
   oracle on (view, S). *)
Definition predictor_guesser : Type :=
  package [interface] guesser_export.

(* guessing_challenger — the V_2-aware boolean indicator.  It runs the game,
   reads the output S, hands the predictor the pair (view, S), reads V_2, and
   returns the equality guess = V_2.  The predictor sees the view and S but
   never V_2. *)
Definition guessing_challenger :
  package (unionm (game_iface_leak_S t_msg t_cipher) guesser_export) A_export :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : 'bool
    {
      #import {sig #[ id_game_run ] : 'unit → ciphers } as call_run ;;
      #import {sig #[ id_s_get    ] : 'unit → msg     } as call_s_get ;;
      #import {sig #[ id_guess     ] : (ciphers × msg) → msg } as call_pred ;;
      #import {sig #[ id_v2_get    ] : 'unit → msg     } as call_v2 ;;
      view  ← call_run tt ;;
      s     ← call_s_get tt ;;
      guess ← call_pred (view, s) ;;
      v2    ← call_v2 tt ;;
      ret (guess == v2 : 'bool)
    }
  ].

(* guessing_experiment — the closed bool-output experiment: the challenger fed
   by the predictor and the game in parallel, so the challenger's game oracles
   (id_game_run, id_s_get, id_v2_get) resolve against the game and id_guess
   against the predictor. *)
Definition guessing_experiment
    (predictor : predictor_guesser)
    (game : raw_package)
    : raw_package :=
  guessing_challenger ∘ par predictor game.

End dsdp_security_indcpa_fiber.

(* sdistr_to_fdist — the SSProve subdistribution to Infotheo fdist bridge: a
   mass-1 subdistribution over a finType is an Infotheo distribution, sharing
   the same realType R as SSProve.  The mass-1 side condition is discharged by
   LosslessCode resolution on the closed experiment's sample code. *)
Section sdistr_to_fdist.
Variable U : finType.
Variable mu : distr.distr R U.
Hypothesis Hmass : psum (distr.mu mu) = 1.

Let f : {ffun U -> R} := [ffun u => distr.mu mu u].
Let f0 u : (0 <= f u)%R. Proof. by rewrite ffunE; exact: distr.ge0_mu. Qed.
Let f1 : (\sum_(u in U) f u = 1)%R.
Proof.
under eq_bigr do rewrite ffunE.
rewrite -Hmass psum_fin; apply: eq_bigr => u _.
by rewrite ger0_norm //; exact: distr.ge0_mu.
Qed.

(* sdistr_to_fdist — the bridged Infotheo distribution. *)
Definition sdistr_to_fdist : FDist.t R U := FDist.make f0 f1.

(* sdistr_to_fdistE — the bridged distribution evaluates to the subdistribution. *)
Lemma sdistr_to_fdistE u : sdistr_to_fdist u = distr.mu mu u.
Proof. by rewrite /sdistr_to_fdist /= /f ffunE. Qed.

(* Pr_sdistr_to_fdist — the bridged distribution's set-probability is the
   subdistribution probability of the same event. *)
Lemma Pr_sdistr_to_fdist (E : {set U}) :
  Pr sdistr_to_fdist E = distr.pr mu (mem E).
Proof.
rewrite /Pr /distr.pr psum_fin.
rewrite [RHS](bigID (fun a => a \in E)) /=.
rewrite [X in _ + X]big1; last by move=> a /negbTE ->; rewrite mul0r normr0.
rewrite addr0; apply: eq_bigr => a aE.
rewrite aE mul1r ger0_norm; last exact: distr.ge0_mu.
by rewrite sdistr_to_fdistE.
Qed.

End sdistr_to_fdist.

(* dmargin_comp — pushforward composition: applying [g] then [h] to a
   subdistribution is the pushforward along [h \o g]. *)
Lemma dmargin_comp {T U V : choiceType} (g : T -> U) (h : U -> V)
    (mu : distr.distr R T) :
  distr.dmargin h (distr.dmargin g mu) = distr.dmargin (h \o g) mu.
Proof.
apply: SubDistr.distr_ext => y.
rewrite distr.dmarginE distr.dmarginE distr.dmarginE dlet_dlet_ext.
by apply: dlet_f_equal => z; rewrite dlet_unit_ext.
Qed.

(* Pr_fst_map — post-composing a closed computation with a pure return is a
   pushforward of its first-projection subdistribution; holds for stateful [c]
   since it threads through [Pr_code]. *)
Lemma Pr_fst_map {A B : choiceType} (c : raw_code A) (f : A -> B) :
  Pr_fst (x ← c ;; ret (f x)) = distr.dmargin f (Pr_fst c).
Proof.
rewrite /Pr_fst Pr_code_bind.
rewrite (eq_dlet (f := fun y0 : (A * heap)%type => Pr_code (ret (f y0.1)) y0.2)
                 (g := fun y0 => distr.dunit (f y0.1, y0.2)));
  last by move=> z; rewrite Pr_code_ret.
rewrite dmargin_comp dfst_dlet_commut distr.dmarginE.
apply: SubDistr.distr_ext => y; apply: dlet_f_equal => z.
by apply: SubDistr.distr_ext => w; rewrite distr.dmargin_dunit /=.
Qed.

(* Pr_fst_agree_locs — footprint/frame property: the value-marginal of valid
   import-free code with locations [L] depends only on the heap restricted to
   [L].  Heaps agreeing on [L] yield equal value-marginals, so the code cannot
   observe state outside its own locations. *)
Lemma Pr_fst_agree_locs {A : choice_type} (L : Locations) (c : raw_code A) :
  ValidCode L [interface] c ->
  forall h h', (forall l, fhas L l -> get_heap h l = get_heap h' l) ->
  distr.dmargin fst (Pr_code c h) = distr.dmargin fst (Pr_code c h').
Proof.
induction 1 as [x | o x k Hin IH | l k Hin IH | l v Hin IH | op k IH]; intros h h' Hagree.
1: rewrite !Pr_code_ret; apply: SubDistr.distr_ext => w; rewrite 2!distr.dmargin_dunit //.
1: exfalso; eapply fhas_empty; eassumption.
1: rewrite !Pr_code_get (Hagree l Hin); apply: H; exact: Hagree.
1: rewrite !Pr_code_put; apply: IHvalid_code => l0 Hl0.
1: case: (eqVneq l0.1 l.1) => [Heq | Hneq].
1: by rewrite /get_heap /set_heap !setmE Heq eqxx.
1: by rewrite !get_set_heap_neq // Hagree.
rewrite !Pr_code_sample !distr.dmarginE !dlet_dlet_ext; apply: eq_dlet => y.
rewrite -!distr.dmarginE; exact: (H y h h' Hagree).
Qed.

(* Pr_fst_closed — the [L = emptym] case of Pr_fst_agree_locs: import-free,
   location-free code has a heap-independent value-marginal equal to Pr_fst c. *)
Lemma Pr_fst_closed {A : choice_type} (c : raw_code A) :
  ValidCode emptym [interface] c ->
  forall h, distr.dmargin fst (Pr_code c h) = Pr_fst c.
Proof.
move=> Hc h; rewrite /Pr_fst.
apply: (Pr_fst_agree_locs Hc) => l /fhas_empty [].
Qed.

Section dsdp_guess_distribution.
(* Same scheme and marshalling as the output-exposing endpoint games.  [Mfin]
   is the finite carrier on which the guess and V_2 are observed, with
   [msg_to_fin] the (injective) message-to-carrier encoding. *)
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable predictor : predictor_guesser t_msg t_cipher.
Variable Mfin : finType.
Variable msg_to_fin : t_msg -> Mfin.
Variable fin_to_msg : Mfin -> t_msg.
Hypothesis msg_to_finK : cancel msg_to_fin fin_to_msg.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher) (in custom pack_type at level 2).

(* zero_game_leak_S instantiated at this section's parameters. *)
Let game : raw_package :=
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0.

(* guess_pair_challenger — the pair-returning analogue of [guessing_challenger]:
   it runs the game, reads S, queries the predictor, reads V_2, and returns the
   pair (guess, V_2) instead of the equality bit. *)
Definition guess_pair_challenger :
  package (unionm (game_iface_leak_S t_msg t_cipher) (guesser_export t_msg t_cipher))
    [interface #val #[ 0%N ] : 'unit → msg × msg ] :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : msg × msg
    {
      #import {sig #[ id_game_run ] : 'unit → ciphers } as call_run ;;
      #import {sig #[ id_s_get    ] : 'unit → msg     } as call_s_get ;;
      #import {sig #[ id_guess     ] : (ciphers × msg) → msg } as call_pred ;;
      #import {sig #[ id_v2_get    ] : 'unit → msg     } as call_v2 ;;
      view  ← call_run tt ;;
      s     ← call_s_get tt ;;
      guess ← call_pred (view, s) ;;
      v2    ← call_v2 tt ;;
      ret (guess, v2)
    }
  ].

(* guess_op — the operation signature reading [guess_pair_challenger]'s pair
   output (parallel to SSProve's bool-locked [RUN]). *)
Definition guess_op : opsig := (0%N, (chUnit, chProd t_msg t_msg)).

(* guess_resolved — the closed pair-returning experiment over [t_msg]:
   the pair challenger fed by the predictor and the game in parallel. *)
Definition guess_resolved : raw_code (t_msg * t_msg)%type :=
  resolve (guess_pair_challenger ∘ par predictor game) guess_op tt.

(* guess_joint_code — the experiment's (guess, V_2) pair pushed into the finite
   carrier [Mfin] for the Infotheo distribution. *)
Definition guess_joint_code : raw_code (Mfin * Mfin)%type :=
  gv ← guess_resolved ;; ret (msg_to_fin gv.1, msg_to_fin gv.2).

(* guess_resolve_eq — the bool-output guessing experiment is the pair
   experiment post-composed with the equality test; both resolve the same
   oracle prefix and differ only in the final return. *)
Lemma guess_resolve_eq :
  resolve (guessing_experiment predictor game) RUN tt
  = (gv ← guess_resolved ;; ret (gv.1 == gv.2 : 'bool)).
Proof.
rewrite /guess_resolved /guessing_experiment resolve_link resolve_link.
have body_eq : resolve (guessing_challenger t_msg t_cipher) RUN tt
   = (gv ← resolve guess_pair_challenger guess_op tt ;;
      ret (gv.1 == gv.2 : 'bool)).
{ rewrite /resolve /guessing_challenger /guess_pair_challenger /=.
  by rewrite !coerce_kleisliE /=. }
by rewrite body_eq code_link_bind.
Qed.

(* Hypothesis guess_lossless — the closed pair experiment terminates with
   probability one (mass-1).  SSProve's [LosslessCode] is the [Pr_fst]-based
   closed-state class; the experiment's stateful game oracles place it outside
   the [LosslessOp_bind] closure, so the standard guessing-adversary assumption
   that the experiment always returns a guess pair is taken directly on the
   resolved code.  The predictor is the only non-terminating component (the
   challenger and the concrete game are total), making this exactly the
   predictor-losslessness hypothesis for the guessing layer. *)
Hypothesis guess_lossless : psum (distr.mu (Pr_fst guess_joint_code)) = 1.

(* guess_joint_fdist — the Infotheo distribution of the observed pair
   (guess, V_2). *)
Definition guess_joint_fdist := sdistr_to_fdist guess_lossless.

(* guess_sdistr_success — the SSProve-side success probability: the true-mass
   of the guessing game's output subdistribution (sdistr). *)
Definition guess_sdistr_success : R :=
  distr.mu (pkg_advantage.Pr (guessing_experiment predictor game)) true.

(* guess_fdist_success — the Infotheo-side success probability: the diagonal
   mass of the bridged fdist.  Same real as guess_sdistr_success; the connector
   below is this experiment's instance of sdistr_to_fdist. *)
Definition guess_fdist_success : R :=
  Pr guess_joint_fdist [set gv | gv.1 == gv.2].

(* guess_success_sdistr_eq_fdist — the SSProve-to-Infotheo connector: the
   guessing experiment's success probability on the all-zero output-exposing
   game equals the probability that the observed guess equals V_2 under
   [guess_joint_fdist].  Heap-free: pushforward [Pr_fst_map] plus the
   subdistribution-probability identities. *)
Lemma guess_success_sdistr_eq_fdist :
  guess_sdistr_success = guess_fdist_success.
Proof.
rewrite /guess_sdistr_success /guess_fdist_success.
rewrite Pr_Pr_fst guess_resolve_eq Pr_fst_map.
rewrite /guess_joint_fdist Pr_sdistr_to_fdist.
rewrite /guess_joint_code Pr_fst_map distr.pr_dmargin.
rewrite distr.dmargin_psumE /distr.pr.
apply: eq_psum => gv /=.
congr (_ * _).
rewrite eqb_id inE /=.
by rewrite (inj_eq (can_inj msg_to_finK)).
Qed.

(* ===== Reflection infrastructure (option B, risk R1) =====
   Reflect guess_joint_code into an explicit sample distribution.
   - card_renc_neq routes the GC_sample branches: the plaintext space (pq) and
     the encryption-randomness space differ, so the two sample cardinalities are
     distinct.  Harmless, discharged at instantiation.
   - predictor_locs_disj keeps the predictor's own state separate from the
     protocol cells; it is what makes the predictor blind to V_2 (the footprint
     lemma Pr_fst_agree_locs frames its output off V_2_cell). *)
Hypothesis card_renc_neq : card_renc != card_msg.
Hypothesis predictor_locs_disj : fseparate (locs predictor) (protocol_state t_msg).

Let gc := all_zero (game_of_trace (dsdp_alice_obs_leak_S card_msg card_renc)).
Let drun := denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx rand0.
Let dhe := denote_he pkey_of_party rand0.

(* denote_run per-constructor unfold lemmas. *)
Lemma drun_sample_msg (e:denv AHE) k : drun e (GC_sample card_msg k) = (x ← sample uniform card_msg ;; drun (push_val (Gplain (msg_of_idx x)) e) k).
Proof. by rewrite /drun /denote_run -/denote_run eqxx. Qed.
Lemma drun_sample_renc (e:denv AHE) k : drun e (GC_sample card_renc k) = (x ← sample uniform card_renc ;; drun (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k).
Proof. by rewrite /drun /denote_run -/denote_run (negbTE card_renc_neq) eqxx. Qed.
Lemma drun_put (e:denv AHE) t k : drun e (GC_put t k) = (#put (V_2_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;; drun e k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_put_output (e:denv AHE) t k : drun e (GC_put_output t k) = (#put (S_output_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;; drun e k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_let (e:denv AHE) t k : drun e (GC_let t k) = drun (push_val (dhe e t) e) k.
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_enc_hop (e:denv AHE) pk secret k : drun e (GC_enc_hop pk secret k) = (ir ← sample uniform card_renc ;; drun (push_val (Gcipher (enc (pkey_of_party (nat_to_party_id pk)) (as_plain (dhe e secret)) (rand_of_renc (sample_to_renc renc_card ir)))) e) k).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.
Lemma drun_ret (e:denv AHE) outs : drun e (GC_ret outs) = ret ([seq chcipher_of_cipher (as_cipher (dhe e o)) | o <- outs] : cipher_list t_cipher).
Proof. by rewrite /drun /dhe /denote_run -/denote_run. Qed.

(* gc_eq — the concrete output-exposing all-zero game body (14 constructors). *)
Lemma gc_eq : gc = GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_renc (GC_sample card_renc (GC_put (HE_var 5) (GC_enc_hop 1 (HE_const 0) (GC_enc_hop 2 (HE_const 0) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 5)) (HE_enc 1 (HE_var 4) 1)) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 4)) (HE_enc 2 (HE_var 3) 0)) (GC_put_output (HE_add (HE_sub (HE_sub (HE_dec 0 (HE_var 10)) (HE_var 6)) (HE_var 4)) (HE_mul (HE_var 10) (HE_var 10))) (GC_ret [:: HE_var 1; HE_var 0; HE_var 3; HE_var 2])))))))))))))).
Proof. by rewrite /gc; vm_compute. Qed.

(* denote_run_distr — the explicit Pr_code reflection of denote_run: samples
   become dlet over uniforms threading the env; puts update the heap. *)
Fixpoint denote_run_distr (e : denv AHE) (gc0 : game_code) (h : heap) {struct gc0}
  : distr.distr R (cipher_list t_cipher * heap)%type :=
  match gc0 with
  | GC_sample n k =>
      if n == card_msg then
        distr.dlet (fun x => denote_run_distr (push_val (Gplain (msg_of_idx x)) e) k h) (projT2 (uniform card_msg))
      else if n == card_renc then
        distr.dlet (fun x => denote_run_distr (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k h) (projT2 (uniform card_renc))
      else
        distr.dlet (fun x : Arit (uniform n) => denote_run_distr e k h) (projT2 (uniform n))
  | GC_put t k =>
      denote_run_distr e k (set_heap h (V_2_cell t_msg) (Some (chmsg_of_msg (as_plain (dhe e t)))))
  | GC_put_output t k =>
      denote_run_distr e k (set_heap h (S_output_cell t_msg) (Some (chmsg_of_msg (as_plain (dhe e t)))))
  | GC_let t k =>
      denote_run_distr (push_val (dhe e t) e) k h
  | GC_enc_hop pk secret k =>
      distr.dlet (fun ir => denote_run_distr (push_val (Gcipher (enc (pkey_of_party (nat_to_party_id pk)) (as_plain (dhe e secret)) (rand_of_renc (sample_to_renc renc_card ir)))) e) k h) (projT2 (uniform card_renc))
  | GC_ret outs =>
      distr.dunit (([seq chcipher_of_cipher (as_cipher (dhe e o)) | o <- outs] : cipher_list t_cipher), h)
  end.

(* denote_run_distrE — the run reflects to denote_run_distr (generic induction). *)
Lemma denote_run_distrE (gc0 : game_code) (e : denv AHE) (h : heap) :
  Pr_code (drun e gc0) h = denote_run_distr e gc0 h.
Proof.
elim: gc0 e h => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e h /=.
- rewrite /drun /denote_run -/denote_run.
  case: (n == card_msg).
  + rewrite Pr_code_sample; apply: eq_dlet => x; exact: IH.
  + case: (n == card_renc); rewrite Pr_code_sample; apply: eq_dlet => x; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_put; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_put; exact: IH.
- rewrite /drun /denote_run -/denote_run; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_sample; apply: eq_dlet => ir; exact: IH.
- rewrite /drun /denote_run -/denote_run Pr_code_ret //.
Qed.

End dsdp_guess_distribution.
