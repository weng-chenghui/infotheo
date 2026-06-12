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
Require Import spp_entropy extra_proba.
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

(* Pr_fst_put_invariant — the value-marginal of import-free code [c] is
   invariant under the value written to a cell outside [c]'s locations [L]:
   [c] cannot observe [cell].  Specializes Pr_fst_agree_locs to a put; it is
   what frames the guessing predictor's output off the V_2 cell. *)
Lemma Pr_fst_put_invariant {A : choice_type} (cell : Location) (L : Locations)
    (c : raw_code A) (h : heap) (x y : cell) :
  ValidCode L [interface] c -> cell.1 \notin domm L ->
  distr.dmargin fst (Pr_code (#put cell := x ;; c) h)
  = distr.dmargin fst (Pr_code (#put cell := y ;; c) h).
Proof.
move=> Hv Hcell.
rewrite !Pr_code_put.
apply: (Pr_fst_agree_locs Hv) => l Hl.
have Hne : l.1 != cell.1
  by apply: contra Hcell => /eqP <-; exact: fhas_in L l Hl.
by rewrite !get_set_heap_neq.
Qed.

(* eq_in_dlet — dlet congruence on the support: bodies that agree on the support
   of [mu] give equal [dlet] (mass outside the support is zero). *)
Lemma eq_in_dlet {T U : choiceType} (f g : T -> distr.distr R U) (mu : distr.distr R T) :
  (forall x, x \in distr.dinsupp mu -> f x = g x) -> distr.dlet f mu = distr.dlet g mu.
Proof.
move=> Hfg; apply: SubDistr.distr_ext => y; rewrite 2!distr.dletE.
apply: eq_psum => x; case: (boolP (x \in distr.dinsupp mu)) => Hx.
- by rewrite (Hfg _ Hx).
- by move/distr.dinsuppPn: Hx => ->; rewrite !mul0r.
Qed.

(* dlet_const_unit — a bind into a constant [dunit v] kernel collapses to [dunit v]
   once the base subdistribution carries unit mass (the [dweight] is 1). *)
Lemma dlet_const_unit {T U : choiceType} (D : distr.distr R T) (v : U) :
  psum (distr.mu D) = 1 ->
  distr.dlet (fun=> distr.dunit v) D = distr.dunit v.
Proof.
move=> HD; apply: SubDistr.distr_ext => y.
by rewrite distr.dletC distr.pr_predT HD mul1r.
Qed.

(* dmargin_fst_const — the first-component marginal of a subdistribution whose
   support has constant first component [v] is the constant-[v] bind. *)
Lemma dmargin_fst_const {T U : choiceType} (D : distr.distr R (U * T)%type) (v : U) :
  (forall p, p \in distr.dinsupp D -> p.1 = v) ->
  distr.dmargin fst D = distr.dlet (fun=> distr.dunit v) D.
Proof.
move=> Hsupp; rewrite distr.dmarginE.
by apply: eq_in_dlet => p Hp; rewrite (Hsupp p Hp).
Qed.

(* Pr_code_preserves — valid code with locations [L] leaves cells outside [L]
   unchanged: every heap in the support of [Pr_code c h] agrees with [h] at [l].
   The heap-level frame property (companion to the marginal frame
   Pr_fst_agree_locs); it is what makes the post-predictor V_2 read return the
   value the run wrote. *)
Lemma Pr_code_preserves {A : choice_type} (L : Locations) (c : raw_code A) (l : Location) :
  ValidCode L [interface] c -> l.1 \notin domm L ->
  forall h ah, ah \in distr.dinsupp (Pr_code c h) -> get_heap ah.2 l = get_heap h l.
Proof.
move=> Hc Hl; elim: Hc => [x|o x k Hin _ IH|l' k Hin _ IH|l' v k Hin _ IH|op k _ IH] h ah Hah.
- by move: Hah; rewrite Pr_code_ret => /distr.in_dunit ->.
- by exfalso; eapply fhas_empty; eassumption.
- by move: Hah; rewrite Pr_code_get => Hah; exact: (IH _ _ _ Hah).
- by move: Hah; rewrite Pr_code_put => Hah; rewrite (IH _ _ Hah);
     apply: get_set_heap_neq; apply: contraNneq Hl => ->; exact: fhas_in Hin.
- by move: Hah; rewrite Pr_code_sample => /distr.dinsupp_dlet [x _];
     rewrite -distr.in_dinsupp => Hah; exact: (IH x _ _ Hah).
Qed.

(* General fdist/distr helpers for the (V_2, V_3) marginal.  Stated with the
   default goal selector so the multi-goal proofs read without strict-mode
   bracketing; strict mode is restored afterwards. *)
Set Default Goal Selector "1".
Set Bullet Behavior "None".

(* fdistmap_bij_unif — a bijection carries a uniform distribution to the uniform
   distribution on the (equicardinal) codomain. *)
Lemma fdistmap_bij_unif (A B : finType) (f : A -> B) (nA nB : nat)
    (cardA : #|A| = nA.+1) (cardB : #|B| = nB.+1) :
  bijective f ->
  fdistmap f (fdist_uniform cardA) = fdist_uniform cardB :> FDist.t R B.
Proof.
move=> [g fg gf].
apply: fdist_ext => b.
rewrite fdistmapE fdist_uniformE.
rewrite (eq_bigl (pred1 (g b))); last first.
  by move=> a; rewrite inE /=; apply/eqP/eqP => [Hf|->]; [rewrite -Hf fg|exact: gf].
rewrite big_pred1_eq fdist_uniformE.
have <- : #|A| = #|B| by apply: (bij_eq_card (f := f)); exists g.
by [].
Qed.

(* mean1_eq1 — a weight [w] bounded in [[0,1]] whose [D]-mean is 1 (with [D]
   mass 1) equals 1 on the support of [D].  Normalizes the lossless predictor's
   mass out of the value-marginal. *)
Lemma mean1_eq1 (T : choiceType) (D : distr.distr R T) (w : T -> R) :
  (forall x, 0 <= w x <= 1) -> psum (distr.mu D) = 1 ->
  psum (fun x => w x * distr.mu D x) = 1 ->
  forall x, x \in distr.dinsupp D -> w x = 1.
Proof.
move=> Hw HD Hwsum x Hx.
have Hsm1 : summable (fun y => (1 - w y) * distr.mu D y).
  apply: (@le_summable _ _ _ (distr.mu D)); last exact: distr.summable_mu.
  move=> y; case/andP: (Hw y) => Hw0 Hw1.
  rewrite mulr_ge0 ?subr_ge0 //=.
  by rewrite ler_piMl ?distr.ge0_mu // ?subr_ge0 // lerBlDr lerDl.
have Hsm2 : summable (fun y => w y * distr.mu D y).
  apply: (@le_summable _ _ _ (distr.mu D)); last exact: distr.summable_mu.
  move=> y; case/andP: (Hw y) => Hw0 Hw1.
  by rewrite mulr_ge0 //= ler_piMl ?distr.ge0_mu.
have Hsum0 : psum (fun y => (1 - w y) * distr.mu D y) = 0.
  have Hsplit : (distr.mu D) =1
     (fun y => (1 - w y) * distr.mu D y + w y * distr.mu D y)
    by move=> y; rewrite -mulrDl addrNK mul1r.
  have H1 : psum (distr.mu D)
     = psum (fun y => (1 - w y) * distr.mu D y)
     + psum (fun y => w y * distr.mu D y).
    rewrite (eq_psum Hsplit); apply: psumD => //.
    - move=> y; apply: mulr_ge0; last exact: distr.ge0_mu.
      by rewrite subr_ge0; case/andP: (Hw y).
    - move=> y; apply: mulr_ge0; last exact: distr.ge0_mu.
      by case/andP: (Hw y).
  by move: H1; rewrite HD Hwsum => /eqP; rewrite eq_sym -subr_eq0 addrK => /eqP.
have Hzero : (1 - w x) * distr.mu D x = 0 by apply: (eq0_psum Hsm1 Hsum0).
move: Hx => /distr.dinsuppP /eqP Hmu.
move: Hzero => /eqP.
rewrite mulf_eq0 (negbTE Hmu) orbF subr_eq0 eq_sym.
by move=> /eqP ->.
Qed.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

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
(* seed — initial env carrying the fixed input-weight parameters (Task 7 gives it
   structure; here the run/resolve lemmas thread it abstractly). *)
Variable seed : denv AHE.
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
    pkey_of_party msg_of_idx rand0 seed.

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

(* resolve_predictor_valid — resolving the closed predictor package at its guess
   oracle yields import-free code over the predictor's own locations.  Vanilla
   [eapply valid_resolve] avoids the raw_package delta-unfolding blowup. *)
Lemma resolve_predictor_valid (cl : cipher_list t_cipher) (sread : t_msg) :
  ValidCode (locs predictor) [interface]
    (resolve (pack predictor)
       (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg)) (cl, sread)).
Proof.
eapply valid_resolve; first exact: (pack_valid predictor).
exact: fhas_set.
Qed.

Let gc := all_zero (game_of_trace_seeded dsdp_weight_names
                      (dsdp_alice_obs_leak_S_seeded card_msg card_renc)).
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

(* gc_eq — the concrete output-exposing all-zero seeded game body: 6 samples
   (secrets v2,v3, masks r2,r3, two hop randomness), the V_2 write, two zeroed
   hops, the two homomorphic combines, and the scalar-product output S
   (u1*v1 + u2*v2 + u3*v3, weights from the seed). *)
Lemma gc_eq : gc = GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_msg (GC_sample card_renc (GC_sample card_renc (GC_put (HE_var 3) (GC_enc_hop 1 (HE_const 0) (GC_enc_hop 2 (HE_const 0) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 7)) (HE_enc 1 (HE_var 3) 1)) (GC_let (HE_emul (HE_epow (HE_var 1) (HE_var 9)) (HE_enc 2 (HE_var 3) 0)) (GC_put_output (HE_add (HE_add (HE_mul (HE_var 8) (HE_var 11)) (HE_mul (HE_var 9) (HE_var 7))) (HE_mul (HE_var 10) (HE_var 6))) (GC_ret [:: HE_var 1; HE_var 0; HE_var 3; HE_var 2])))))))))))).
Proof. by rewrite /gc; vm_compute. Qed.

(* output_term — the seeded all-zero game's GC_put_output he_term (from gc_eq):
   the scalar product over the put_output env indices (v1=11, u1=8, u2=9, u3=10,
   v2=7, v3=6). *)
Notation output_term :=
  (HE_add (HE_add (HE_mul (HE_var 8) (HE_var 11)) (HE_mul (HE_var 9) (HE_var 7)))
          (HE_mul (HE_var 10) (HE_var 6))).

(* denote_output_termE — the leaked output term denotes (via denote_he) to the
   shared scalar-product spec dsdp_output of the env values at the put_output
   indices; the bridge by which the recomposed game's S meets the entropy-side
   constraint.  Definitional. *)
Lemma denote_output_termE (e : denv AHE) :
  as_plain (dhe e output_term)
  = dsdp_output (as_plain (de_val_nth e 11)) (as_plain (de_val_nth e 8))
                (as_plain (de_val_nth e 9)) (as_plain (de_val_nth e 10))
                (as_plain (de_val_nth e 7)) (as_plain (de_val_nth e 6)).
Proof. by rewrite /dhe /dsdp_output /=. Qed.

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

(* guess_resolved_par — the challenger body distributed over the parallel game:
   the four oracle calls (run, read S, predict, read V_2) resolve against
   [par predictor game] in sequence. *)
Lemma guess_resolved_par :
  guess_resolved =
  (view ← resolve (par predictor game) (id_game_run, (chUnit, cipher_list t_cipher)) tt ;;
   s    ← resolve (par predictor game) (id_s_get, (chUnit, t_msg)) tt ;;
   guess ← resolve (par predictor game) (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg)) (view, s) ;;
   v2   ← resolve (par predictor game) (id_v2_get, (chUnit, t_msg)) tt ;;
   ret (guess, v2)).
Proof.
rewrite /guess_resolved resolve_link /resolve /guess_pair_challenger /=.
rewrite coerce_kleisliE.
cbn [code_link].
reflexivity.
Qed.

(* resolve_game_run / _sget / _v2get — the game's three oracles resolve to the
   run denotation and the two cell-read bodies (getm_def lookup in the raw map). *)
Lemma resolve_game_run :
  resolve game (id_game_run, ('unit, cipher_list t_cipher)) tt = drun seed gc.
Proof.
rewrite /resolve /game /zero_game_leak_S -/gc /denote_game_leak_S /denote_game_leak_S_raw mkfmapE /id_game_run /id_v2_get /id_s_get /fst.
cbn [getm_def]; cbn [fst snd].
by rewrite eqxx /mkdef coerce_kleisliE /drun.
Qed.

Lemma resolve_game_sget :
  resolve game (id_s_get, ('unit, t_msg)) tt = denote_s_get_body chmsg_of_msg.
Proof.
rewrite /resolve /game /zero_game_leak_S -/gc /denote_game_leak_S /denote_game_leak_S_raw mkfmapE /id_game_run /id_v2_get /id_s_get /fst.
cbn [getm_def]; cbn [fst snd].
by rewrite -[(3 == 0)%N]/false -[(3 == 2)%N]/false eqxx /mkdef coerce_kleisliE.
Qed.

Lemma resolve_game_v2get :
  resolve game (id_v2_get, ('unit, t_msg)) tt = denote_v2_get_body chmsg_of_msg.
Proof.
rewrite /resolve /game /zero_game_leak_S -/gc /denote_game_leak_S /denote_game_leak_S_raw mkfmapE /id_game_run /id_v2_get /id_s_get /fst.
cbn [getm_def]; cbn [fst snd].
by rewrite -[(2 == 0)%N]/false eqxx /mkdef coerce_kleisliE.
Qed.

(* guess_resolved_oracles — resolve the four oracle calls: the game's run / S /
   V_2 oracles route to the game (not in the predictor's domm), the guess oracle
   to the predictor. *)
Lemma guess_resolved_oracles :
  guess_resolved =
  (view ← drun seed gc ;;
   s    ← denote_s_get_body chmsg_of_msg ;;
   guess ← resolve (pack predictor) (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg)) (view, s) ;;
   v2   ← denote_v2_get_body chmsg_of_msg ;;
   ret (guess, v2)).
Proof.
rewrite guess_resolved_par !resolve_par.
have Hpred_none : forall id : nat, (id == id_guess) = false -> isSome (pack predictor id) = false by (move=> id Hid; rewrite -mem_domm -(valid_domm (pack_valid predictor)) /guesser_export domm_set domm0 fsetU0 in_fset1 Hid).
cbn [fst].
rewrite (Hpred_none id_game_run erefl) (Hpred_none id_s_get erefl) (Hpred_none id_v2_get erefl).
have Hguess : isSome (pack predictor id_guess) = true by (rewrite -mem_domm -(valid_domm (pack_valid predictor)) /guesser_export domm_set domm0 fsetU0 in_fset1 eqxx).
rewrite resolve_game_run resolve_game_sget resolve_game_v2get.
have Hpar_guess : forall x, resolve (par predictor game) (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg)) x = resolve predictor (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg)) x by (move=> x; rewrite resolve_par; cbn [fst]; rewrite Hguess).
setoid_rewrite Hpar_guess.
by [].
Qed.

(* denote_run_caps — the run denotation that, at the output point, also
   returns the seven plaintext env values (v1,u1,u2,u3,v2,v3,S) at the given de
   Bruijn indices and the accumulated hop encryption-randomness [irs] (the
   samples that determine the all-zero [view]); the finite handle on [view]. *)
Fixpoint denote_run_caps (iv1 iu1 iu2 iu3 iv2 iv3 : nat)
  (irs : seq 'I_card_renc) (e : denv AHE) (gc0 : game_code) {struct gc0}
  : raw_code (cipher_list t_cipher *
       (plain AHE * plain AHE * plain AHE * plain AHE * plain AHE * plain AHE
        * plain AHE) * seq 'I_card_renc)%type :=
  match gc0 with
  | GC_sample n k =>
      if n == card_msg then
        x ← sample uniform card_msg ;;
        denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs
          (push_val (Gplain (msg_of_idx x)) e) k
      else if n == card_renc then
        x ← sample uniform card_renc ;;
        denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs
          (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k
      else
        x ← sample uniform n ;;
        denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e k
  | GC_put t k =>
      #put (V_2_cell t_msg) :=
        Some (chmsg_of_msg (as_plain (denote_he pkey_of_party rand0 e t))) ;;
      denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e k
  | GC_put_output t k =>
      #put (S_output_cell t_msg) :=
        Some (chmsg_of_msg (as_plain (denote_he pkey_of_party rand0 e t))) ;;
      cl ← denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
             pkey_of_party msg_of_idx rand0 e k ;;
      ret (cl, (as_plain (de_val_nth e iv1), as_plain (de_val_nth e iu1),
                as_plain (de_val_nth e iu2), as_plain (de_val_nth e iu3),
                as_plain (de_val_nth e iv2), as_plain (de_val_nth e iv3),
                as_plain (denote_he pkey_of_party rand0 e t)), irs)
  | GC_let t k =>
      denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs
        (push_val (denote_he pkey_of_party rand0 e t) e) k
  | GC_enc_hop pk secret k =>
      ir ← sample uniform card_renc ;;
      denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 (rcons irs ir)
        (push_val
           (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                         (as_plain (denote_he pkey_of_party rand0 e secret))
                         (rand_of_renc (sample_to_renc renc_card ir)))) e) k
  | GC_ret outs =>
      ret (([seq
           chcipher_of_cipher (as_cipher (denote_he pkey_of_party rand0 e o))
             | o <- outs] : cipher_list t_cipher),
           (0%R, 0%R, 0%R, 0%R, 0%R, 0%R, 0%R), irs)
  end.

(* denote_run_caps_fst — forgetting the captured plaintext tuple and hop
   randomness recovers the plain run; the rich run is faithful on the
   cipher-list channel. *)
Lemma denote_run_caps_fst iv1 iu1 iu2 iu3 iv2 iv3 irs (e : denv AHE)
    (gc0 : game_code) :
  (xy ← denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e gc0 ;; ret xy.1.1)
  = denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
      pkey_of_party msg_of_idx rand0 e gc0.
Proof.
elim: gc0 e irs => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e irs /=.
- case: (n == card_msg); [|case: (n == card_renc)]; cbn [bind]; congr sampler;
    apply: boolp.funext => x; exact: IH.
- cbn [bind]; congr putr; exact: IH.
- by rewrite bind_assoc; cbn [bind]; rewrite bind_ret.
- exact: IH.
- cbn [bind]; congr sampler; apply: boolp.funext => x; exact: IH.
- by [].
Qed.

(* denote_run_caps per-constructor unfold lemmas (rich-run analogues of the
   drun_* lemmas), used to peel the run inside the (V_2, V_3) reflection. *)
Lemma drc_sample_msg iv1 iu1 iu2 iu3 iv2 iv3 irs (e : denv AHE) k :
  denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e (GC_sample card_msg k)
  = (x ← sample uniform card_msg ;;
     denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs (push_val (Gplain (msg_of_idx x)) e) k).
Proof. by rewrite /denote_run_caps -/denote_run_caps eqxx. Qed.

Lemma drc_sample_renc iv1 iu1 iu2 iu3 iv2 iv3 irs (e : denv AHE) k :
  denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e (GC_sample card_renc k)
  = (x ← sample uniform card_renc ;;
     denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs
       (push_rand (rand_of_renc (sample_to_renc renc_card x)) e) k).
Proof. by rewrite /denote_run_caps -/denote_run_caps (negbTE card_renc_neq) eqxx. Qed.

Lemma drc_put iv1 iu1 iu2 iu3 iv2 iv3 irs (e : denv AHE) t k :
  denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e (GC_put t k)
  = (#put (V_2_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;;
     denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e k).
Proof. by rewrite /denote_run_caps -/denote_run_caps. Qed.

Lemma drc_let iv1 iu1 iu2 iu3 iv2 iv3 irs (e : denv AHE) t k :
  denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e (GC_let t k)
  = denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs (push_val (dhe e t) e) k.
Proof. by rewrite /denote_run_caps -/denote_run_caps. Qed.

Lemma drc_hop iv1 iu1 iu2 iu3 iv2 iv3 irs (e : denv AHE) pk secret k :
  denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e (GC_enc_hop pk secret k)
  = (ir ← sample uniform card_renc ;;
     denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 (rcons irs ir)
       (push_val (Gcipher (enc (pkey_of_party (nat_to_party_id pk))
                               (as_plain (dhe e secret))
                               (rand_of_renc (sample_to_renc renc_card ir)))) e) k).
Proof. by rewrite /denote_run_caps -/denote_run_caps. Qed.

Lemma drc_putout iv1 iu1 iu2 iu3 iv2 iv3 irs (e : denv AHE) t k :
  denote_run_caps iv1 iu1 iu2 iu3 iv2 iv3 irs e (GC_put_output t k)
  = (#put (S_output_cell t_msg) := Some (chmsg_of_msg (as_plain (dhe e t))) ;;
     cl ← drun e k ;;
     ret (cl, (as_plain (de_val_nth e iv1), as_plain (de_val_nth e iu1),
               as_plain (de_val_nth e iu2), as_plain (de_val_nth e iu3),
               as_plain (de_val_nth e iv2), as_plain (de_val_nth e iv3),
               as_plain (dhe e t)), irs)).
Proof. by rewrite /denote_run_caps -/denote_run_caps /drun /dhe. Qed.

(* guess_resolved_caps — rich pair experiment: the capturing run exposes the
   output-point env values and hop randomness, then S / guess / V_2 are read as
   in [guess_resolved_oracles]; returns the eight observed values and [irs]. *)
Definition guess_resolved_caps :
  raw_code (t_msg * t_msg *
            (plain AHE * plain AHE * plain AHE * plain AHE * plain AHE *
             plain AHE * plain AHE) * seq 'I_card_renc)%type :=
  vt ← denote_run_caps 11 8 9 10 7 6 [::] seed gc ;;
  s     ← denote_s_get_body chmsg_of_msg ;;
  guess ← resolve (pack predictor)
            (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg))
            (vt.1.1, s) ;;
  v2    ← denote_v2_get_body chmsg_of_msg ;;
  ret (guess, v2, vt.1.2, vt.2).

(* guess_full_code — the rich observed tuple in the finite carrier
   [Mfin^4 * (option 'I_card_renc)^2]: (guess, V2, V3, S, ir1, ir2), where
   ir1, ir2 are the finite handle on the predictor's [view]. *)
Definition guess_full_code :
  raw_code (Mfin * Mfin * Mfin * Mfin *
            (option 'I_card_renc) * (option 'I_card_renc))%type :=
  gv ← guess_resolved_caps ;;
  let '(guess, v2, (v1, u1, u2, u3, v2', v3, s), irs) := gv in
  ret (msg_to_fin guess, msg_to_fin v2,
       msg_to_fin (chmsg_of_msg v3), msg_to_fin (chmsg_of_msg s),
       onth irs 0, onth irs 1).

(* msg_of_chmsg / chmsg_of_msgK — the plaintext-channel encoding [chmsg_of_msg]
   has a left inverse, so the finite carrier values cross back to [plain AHE].
   Hmsg_bij — the message-index encoding is a bijection (uniform sampling is
   faithful: #|plain AHE| = card_msg and V_2 is uniform on plain AHE). *)
Variable msg_of_chmsg : t_msg -> plain AHE.
Hypothesis chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg.
Hypothesis Hmsg_bij : bijective msg_of_idx.

(* guess_full_lossless — the rich experiment terminates with probability one
   (the predictor-losslessness hypothesis for the rich-trace layer). *)
Hypothesis guess_full_lossless : psum (distr.mu (Pr_fst guess_full_code)) = 1.

(* guess_sample_fdist — the Infotheo distribution over the rich observed tuple
   (guess, V2, V3, S, ir1, ir2). *)
Definition guess_sample_fdist := sdistr_to_fdist guess_full_lossless.

(* fin_to_plain — recover the plaintext from a finite-carrier message. *)
Definition fin_to_plain (m : Mfin) : plain AHE := msg_of_chmsg (fin_to_msg m).

(* guess_full_proj_code — the (guess, V_2)-projection of the rich carrier code
   is the bridged pair code [guess_joint_code]. *)
Lemma guess_full_proj_code :
  (gv ← guess_full_code ;; ret (gv.1.1.1.1.1, gv.1.1.1.1.2)) = guess_joint_code.
Proof.
rewrite /guess_full_code /guess_joint_code bind_assoc.
rewrite guess_resolved_oracles.
transitivity (vt ← denote_run_caps 11 8 9 10 7 6 [::] seed gc ;;
  s ← denote_s_get_body chmsg_of_msg ;;
  guess ← resolve predictor
            (id_guess, (cipher_list t_cipher × t_msg, t_msg)) (vt.1.1, s) ;;
  v2 ← denote_v2_get_body chmsg_of_msg ;;
  ret (msg_to_fin guess, msg_to_fin v2)).
- rewrite /guess_resolved_caps !bind_assoc.
  apply: bind_cong => //; apply: boolp.funext => vt.
  rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => s.
  rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => guess.
  rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => v2.
  by case: (vt.1.2) => [[[[[[a b] c] d] e] f] g]; cbn [bind].
- rewrite /drun -(denote_run_caps_fst 11 8 9 10 7 6 [::] seed gc) !bind_assoc.
  apply: bind_cong => //; apply: boolp.funext => vt.
  cbn [bind].
  rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => s.
  rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => guess.
  by rewrite !bind_assoc; apply: bind_cong => //; apply: boolp.funext => v2.
Qed.

(* guess_joint_fdist_marginal — the bridged pair distribution is the
   (guess, V_2)-marginal of the rich sample distribution. *)
Lemma guess_joint_fdist_marginal :
  guess_joint_fdist
  = fdistmap (fun t : (Mfin * Mfin * Mfin * Mfin *
                       (option 'I_card_renc) * (option 'I_card_renc))%type
              => (t.1.1.1.1.1, t.1.1.1.1.2)) guess_sample_fdist.
Proof.
have Hbridge : Pr_fst guess_joint_code
  = distr.dmargin (fun t : Mfin * Mfin * Mfin * Mfin * option 'I_card_renc *
                          option 'I_card_renc => (t.1.1.1.1.1, t.1.1.1.1.2))
      (Pr_fst guess_full_code).
{ by rewrite -guess_full_proj_code Pr_fst_map. }
apply: fdist_ext => y.
rewrite /guess_joint_fdist /guess_sample_fdist sdistr_to_fdistE.
rewrite Hbridge fdistmapE.
under eq_bigr do rewrite sdistr_to_fdistE.
rewrite distr.dmargin_psumE psum_fin.
rewrite [RHS]big_mkcond /=.
apply: eq_bigr => x _.
rewrite inE /= ger0_norm;
  last by rewrite mulr_ge0 // ?ler0n//; exact: distr.ge0_mu.
by case: (_ == y); rewrite ?mul1r ?mul0r.
Qed.

Local Open Scope proba_scope.

(* cpr_eq_drop_indep — a conditioning coordinate independent of the numerator
   pair drops out of the conditioning view: if [W] is independent of [%X,Y], then
   [`Pr[X = a | [%W,Y] = (w,y)] = `Pr[X = a | Y = y]].  General; placed here for
   the open [proba_scope] (the [{RV _ -> _}] notation). *)
Lemma cpr_eq_drop_indep {Rr : realType} {U : finType} {P : FDist.t Rr U}
  {A B C : finType} (X : {RV P -> A}) (Y : {RV P -> B}) (W : {RV P -> C})
  (a : A) (y : B) (w : C) :
  `Pr[ W = w ] != 0 ->
  P |= W _|_ [% X, Y] ->
  `Pr[ X = a | [% W, Y] = (w, y) ] = `Pr[ X = a | Y = y ].
Proof.
move=> Hw Hindep.
rewrite !cpr_eqE.
have HWY : P |= W _|_ Y by exact: (inde_RV_comp idfun snd Hindep).
rewrite (pfwd1_pairCA X W Y a w y) (Hindep w (a, y)) (HWY w y).
by rewrite invfM mulrACA (mulfV Hw) mul1r.
Qed.

(* The four protocol weights Alice holds (seeded constants). *)
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).

(* Projection random variables from the rich carrier (named as in
   dsdp_entropy_ring); inputs are constants, the secrets and guess cross to
   [plain AHE] via [fin_to_plain]. *)
Definition guess_rv : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.1.
Definition V2 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.1.2.
Definition V3 : {RV guess_sample_fdist -> plain AHE} :=
  fun t => fin_to_plain t.1.1.1.2.
Definition V1 : {RV guess_sample_fdist -> plain AHE} := const_RV _ w_v1.
Definition U1 : {RV guess_sample_fdist -> plain AHE} := const_RV _ w_u1.
Definition U2 : {RV guess_sample_fdist -> plain AHE} := const_RV _ w_u2.
Definition U3 : {RV guess_sample_fdist -> plain AHE} := const_RV _ w_u3.
Definition ir1_rv : {RV guess_sample_fdist -> option 'I_card_renc} :=
  fun t => t.1.2.
Definition ir2_rv : {RV guess_sample_fdist -> option 'I_card_renc} :=
  fun t => t.2.

(* Sout — the leaked output as the scalar product of the inputs and secrets. *)
Definition Sout : {RV guess_sample_fdist -> plain AHE} :=
  fun t => dsdp_output w_v1 w_u1 w_u2 w_u3 (V2 t) (V3 t).

(* guess_S_determined — the leaked output is the scalar-product spec of the
   inputs and secrets; the fiber-side instance of [S_determined]. *)
Lemma guess_S_determined :
  Sout = (fun t => dsdp_output (V1 t) (U1 t) (U2 t) (U3 t) (V2 t) (V3 t)).
Proof. by []. Qed.

(* guess_inputs_indep — the protocol inputs (seeded constants) are independent of
   the secret samples: a constant random variable is independent of every RV. *)
Lemma guess_inputs_indep :
  guess_sample_fdist |= [% V1, U1, U2, U3] _|_ [% V2, V3].
Proof.
have Hc : [% V1, U1, U2, U3]
    = const_RV guess_sample_fdist (w_v1, w_u1, w_u2, w_u3)
  by apply: boolp.funext => t; rewrite /V1 /U1 /U2 /U3 !const_RVE.
by rewrite Hc; exact: inde_const_RV.
Qed.

(* Zcond — the conditioning view: the hop randomness (determining the cipher
   view the predictor sees) and the leaked output S. *)
Definition Zcond : {RV guess_sample_fdist ->
    (option 'I_card_renc * option 'I_card_renc * plain AHE)} :=
  [% ir1_rv, ir2_rv, Sout].

(* Lenient goal/bullet selectors for the multi-have marginal reflection. *)
Set Default Goal Selector "1".
Set Bullet Behavior "None".

(* cardpp — the plaintext-pair carrier is non-empty, so its cardinality is a
   successor (the shape [fdist_uniform] demands). *)
Lemma cardpp :
  #|((plain AHE * plain AHE)%type : finType)|
  = (#|plain AHE| * #|plain AHE|).-1.+1.
Proof.
rewrite card_prod prednK //; rewrite muln_gt0; apply/andP; split.
all: by apply/card_gt0P; exists 0%R; rewrite inE.
Qed.

(* Htail2_abs — the post-run tail collapse, abstracted over the predictor code
   [pc] (a variable) so its rewrite matches without unfolding the giant resolved
   predictor term.  The predictor never writes the V_2 cell (Pr_code_preserves +
   predictor_locs_disj), so the read returns the value the run stored, and the
   tail's value-marginal is the constant [(msg_of_chmsg cv, v3val)] scaled by the
   predictor mass. *)
Lemma Htail2_abs (h : heap) (pc : raw_code t_msg) (cv : t_msg)
    (v3val : plain AHE) :
  ValidCode (locs predictor) [interface] pc ->
  get_heap h (V_2_cell t_msg) = Some cv ->
  distr.dmargin fst (Pr_code
    (guess ← pc ;;
     v2 ← denote_v2_get_body chmsg_of_msg ;;
     ret (msg_of_chmsg v2, v3val)) h)
  = distr.dlet (fun _ : (t_msg * heap)%type =>
       distr.dunit (msg_of_chmsg cv, v3val)) (Pr_code pc h).
Proof.
move=> Hpc Hcv.
rewrite Pr_code_bind dfst_dlet_commut.
apply: eq_in_dlet => -[g hg] Hg.
have Hpres : get_heap hg (V_2_cell t_msg) = Some cv.
  rewrite -Hcv.
  apply: (Pr_code_preserves (L := locs predictor) (l := V_2_cell t_msg) _ _ Hg).
  apply: (@notin_has_separate _ _ (protocol_state t_msg) (locs predictor)
            (V_2_cell t_msg)).
  exact: fhas_set.
  exact: fseparateC predictor_locs_disj.
rewrite /denote_v2_get_body Pr_code_get Hpres Pr_code_ret.
by apply: SubDistr.distr_ext => w; rewrite distr.dmargin_dunit.
Qed.

(* guess_VarRV_uniform — the two secret samples (V_2, V_3) are jointly uniform on
   the plaintext space: they are msg_of_idx of two independent uniform index
   samples, and msg_of_idx is a bijection. *)
Lemma guess_VarRV_uniform : `p_[% V2, V3] = fdist_uniform cardpp.
Proof.
rewrite /dist_of_RV.
pose proj := (fun t : (Mfin * Mfin * Mfin * Mfin * option 'I_card_renc *
                      option 'I_card_renc)%type
              => (fin_to_plain t.1.1.1.1.2, fin_to_plain t.1.1.1.2)).
have HVproj : [% V2, V3] = proj.
  by apply: boolp.funext => t.
rewrite HVproj.
have Hproj_lossless :
    psum (distr.mu (Pr_fst (gv ← guess_full_code ;; ret (proj gv)))) = 1.
  rewrite Pr_fst_map -distr.pr_predT distr.pr_dmargin.
  rewrite (distr.eq_pr (B := predT)); last by [].
  by rewrite distr.pr_predT.
have Hbridge_sd :
    fdistmap proj guess_sample_fdist = sdistr_to_fdist Hproj_lossless.
  apply: fdist_ext => u.
  rewrite fdistmapE sdistr_to_fdistE Pr_fst_map distr.dmargin_psumE psum_fin
    big_mkcond /=.
  apply: eq_bigr => i _.
  rewrite ffunE !inE /=.
  case: (proj i == u); rewrite ?mul1r ?mul0r ?normr0 //.
  by rewrite ger0_norm //; exact: distr.ge0_mu.
rewrite Hbridge_sd.
pose pairmap := (fun p : ('I_card_msg * 'I_card_msg)%type =>
                   (msg_of_idx p.1, msg_of_idx p.2)).
pose two_idx_code : raw_code ('I_card_msg * 'I_card_msg)%type :=
  (x0 ← sample uniform card_msg ;; x1 ← sample uniform card_msg ;; ret (x0, x1)).
have card_pair :
    #|('I_card_msg * 'I_card_msg : finType)%type| = (card_msg * card_msg).-1.+1.
  rewrite card_prod !card_ord prednK //.
  rewrite muln_gt0; apply/andP; split; rewrite -(card_ord card_msg);
    apply/card_gt0P; by have [x _ _] := Hmsg_bij; exists (x 0%R); rewrite inE.
have Hpairbij : bijective pairmap.
  have [gm cgm gcm] := Hmsg_bij.
  exists (fun q : (plain AHE * plain AHE)%type => (gm q.1, gm q.2)).
    by move=> [a b]; rewrite /pairmap /= !cgm.
  by move=> [a b]; rewrite /pairmap /= !gcm.
have Hcard0 : (0 < card_msg)%N.
  have [gm _ _] := Hmsg_bij.
  by rewrite -[card_msg]card_ord; apply/card_gt0P; exists (gm 0%R).
have Hbody :
    (gv ← guess_full_code ;; ret (proj gv))
    = (vt ← denote_run_caps 11 8 9 10 7 6 [::] seed gc ;;
       s ← denote_s_get_body chmsg_of_msg ;;
       guess ← resolve (pack predictor)
                 (id_guess, (chProd (cipher_list t_cipher) t_msg, t_msg))
                 (vt.1.1, s) ;;
       v2 ← denote_v2_get_body chmsg_of_msg ;;
       ret (msg_of_chmsg v2, vt.1.2.1.2)).
  rewrite /guess_full_code /guess_resolved_caps !bind_assoc.
  apply: bind_cong=>//; apply: boolp.funext=>vt.
  rewrite !bind_assoc; apply: bind_cong=>//; apply: boolp.funext=>s.
  rewrite !bind_assoc; apply: bind_cong=>//; apply: boolp.funext=>guess.
  rewrite !bind_assoc; apply: bind_cong=>//; apply: boolp.funext=>v2.
  case: (vt.1.2) => [[[[[[a b] c] d] e] f] g] /=.
  by rewrite /proj /fin_to_plain /= !msg_to_finK !chmsg_of_msgK.
have Hcore :
    Pr_fst (gv ← guess_full_code ;; ret (proj gv))
    = distr.dmargin pairmap (Pr_fst two_idx_code).
  have HRHS : distr.dmargin pairmap (Pr_fst two_idx_code)
      = distr.dlet (fun x0 => distr.dlet (fun x1 =>
          distr.dunit (msg_of_idx x0, msg_of_idx x1)) (projT2 (uniform card_msg)))
          (projT2 (uniform card_msg)).
    rewrite /two_idx_code /Pr_fst /pairmap Pr_code_sample dfst_dlet_commut
      /distr.dmargin dlet_dlet_ext.
    apply: eq_dlet => x0.
    rewrite Pr_code_sample !dlet_dlet_ext.
    apply: eq_dlet => x1.
    by rewrite Pr_code_ret !dlet_unit_ext.
  rewrite HRHS Hbody /Pr_fst gc_eq.
  (* Peel the six leading samples (4 plaintext, 2 encryption-randomness). *)
  rewrite drc_sample_msg; cbn [bind]; rewrite Pr_code_sample dfst_dlet_commut.
  apply: eq_dlet => x0.
  rewrite drc_sample_msg; cbn [bind]; rewrite Pr_code_sample dfst_dlet_commut.
  apply: eq_dlet => x1.
  (* After peeling x0, x1: the inner experiment INNER has a constant value-marginal
     [(msg_of_idx x0, msg_of_idx x1)] (the predictor never touches V_2, V_3), so the
     marginal is [dunit VAL] scaled by INNER's total mass, which is 1 (losslessness).
     [dmargin_fst_const] discharges the constant-value side via the run-support facts
     [Hrun]; [dlet_const_unit] reduces to the mass obligation. *)
  set INNER := (X in distr.dmargin fst (Pr_code X emptym)).
  rewrite (dmargin_fst_const (v := (msg_of_idx x0, msg_of_idx x1))); last first.
    move=> [val h] /=; rewrite /INNER Pr_code_bind.
    move/distr.dinsupp_dlet => [y Hy Hval].
    have Hrun : forall z : (cipher_list t_cipher *
        (plain AHE * plain AHE * plain AHE * plain AHE * plain AHE * plain AHE
         * plain AHE) * seq 'I_card_renc)%type * heap,
        z \in distr.dinsupp (Pr_code (denote_run_caps 11 8 9 10 7 6 [::]
            (push_val (Gplain (msg_of_idx x1))
               (push_val (Gplain (msg_of_idx x0)) seed))
            (GC_sample card_msg (GC_sample card_msg (GC_sample card_renc
              (GC_sample card_renc (GC_put (HE_var 3) (GC_enc_hop 1 (HE_const 0)
              (GC_enc_hop 2 (HE_const 0) (GC_let (HE_emul (HE_epow (HE_var 1)
              (HE_var 7)) (HE_enc 1 (HE_var 3) 1)) (GC_let (HE_emul (HE_epow
              (HE_var 1) (HE_var 9)) (HE_enc 2 (HE_var 3) 0)) (GC_put_output
              output_term (GC_ret [:: HE_var 1; HE_var 0; HE_var 3;
              HE_var 2])))))))))))) emptym) ->
        z.1.1.2.1.2 = msg_of_idx x1
        /\ get_heap z.2 (V_2_cell t_msg) = Some (chmsg_of_msg (msg_of_idx x0)).
      move=> [zv zh] Hin.
      move: Hin; rewrite drc_sample_msg Pr_code_sample
        => /distr.dinsupp_dlet [a0 _ Hin].
      move: Hin; rewrite drc_sample_msg Pr_code_sample
        => /distr.dinsupp_dlet [a1 _ Hin].
      move: Hin; rewrite drc_sample_renc Pr_code_sample
        => /distr.dinsupp_dlet [b0 _ Hin].
      move: Hin; rewrite drc_sample_renc Pr_code_sample
        => /distr.dinsupp_dlet [b1 _ Hin].
      move: Hin; rewrite drc_put Pr_code_put drc_hop Pr_code_sample
        => /distr.dinsupp_dlet [c0 _ Hin].
      move: Hin; rewrite drc_hop Pr_code_sample
        => /distr.dinsupp_dlet [c1 _ Hin].
      move: Hin; rewrite drc_let drc_let drc_putout Pr_code_put Pr_code_bind
        drun_ret Pr_code_ret dlet_unit_ext Pr_code_ret
        => /distr.in_dunit [= -> ->].
      split; [by [] | by rewrite get_set_heap_neq // get_set_heap_eq].
    case: (Hrun y Hy) => Hcap Hheap.
    have Hsget : Pr_code (denote_s_get_body chmsg_of_msg) y.2
        = distr.dunit (match get_heap y.2 (S_output_cell t_msg) with
                       | Some v => v | None => chmsg_of_msg 0%R end, y.2).
      by rewrite /denote_s_get_body Pr_code_get;
         case: (get_heap y.2 (S_output_cell t_msg)) => [sv|]; rewrite Pr_code_ret.
    have Hmarg : distr.dmargin fst (Pr_code
        (s ← denote_s_get_body chmsg_of_msg ;;
         resolve predictor (id_guess, (cipher_list t_cipher × t_msg, t_msg))
           (y.1.1.1, s) ;;
         v2 ← denote_v2_get_body chmsg_of_msg ;;
         ret (msg_of_chmsg v2, y.1.1.2.1.2)) y.2)
        = distr.dlet (fun=> distr.dunit (msg_of_idx x0, msg_of_idx x1))
            (Pr_code (resolve predictor
               (id_guess, (cipher_list t_cipher × t_msg, t_msg))
               (y.1.1.1, match get_heap y.2 (S_output_cell t_msg) with
                         | Some v => v | None => chmsg_of_msg 0%R end)) y.2).
      rewrite Pr_code_bind Hsget dlet_unit_ext.
      transitivity (distr.dlet
          (fun=> distr.dunit (msg_of_chmsg (chmsg_of_msg (msg_of_idx x0)),
                              y.1.1.2.1.2))
          (Pr_code (resolve predictor
             (id_guess, (cipher_list t_cipher × t_msg, t_msg))
             (y.1.1.1, match get_heap y.2 (S_output_cell t_msg) with
                       | Some v => v | None => chmsg_of_msg 0%R end)) y.2));
        first by apply: Htail2_abs;
          [exact: resolve_predictor_valid | exact: Hheap].
      by rewrite chmsg_of_msgK Hcap.
    have Hvs : val \in distr.dinsupp (distr.dmargin fst (Pr_code
        (s ← denote_s_get_body chmsg_of_msg ;;
         resolve predictor (id_guess, (cipher_list t_cipher × t_msg, t_msg))
           (y.1.1.1, s) ;;
         v2 ← denote_v2_get_body chmsg_of_msg ;;
         ret (msg_of_chmsg v2, y.1.1.2.1.2)) y.2)).
      by rewrite distr.dmarginE; apply: (distr.dlet_dinsupp (x := (val, h)));
        [exact: Hval | rewrite distr.dunit1E eqxx; exact: oner_neq0].
    move: Hvs; rewrite Hmarg => /distr.dinsupp_dlet [q _ Hq];
      by move: Hq => /distr.in_dunit ->.
  apply: dlet_const_unit.
  (* INNER's total mass is 1: the predictor mass averages to 1 over the secrets
     (guess_full_lossless) and is bounded by 1, so it is 1 on the full uniform
     support (mean1_eq1). *)
  pose INNERf := fun a b : 'I_card_msg =>
    (vt ← denote_run_caps 11 8 9 10 7 6 [::]
        (push_val (Gplain (msg_of_idx b))
           (push_val (Gplain (msg_of_idx a)) seed))
        (GC_sample card_msg (GC_sample card_msg (GC_sample card_renc
          (GC_sample card_renc (GC_put (HE_var 3) (GC_enc_hop 1 (HE_const 0)
          (GC_enc_hop 2 (HE_const 0) (GC_let (HE_emul (HE_epow (HE_var 1)
          (HE_var 7)) (HE_enc 1 (HE_var 3) 1)) (GC_let (HE_emul (HE_epow
          (HE_var 1) (HE_var 9)) (HE_enc 2 (HE_var 3) 0)) (GC_put_output
          output_term (GC_ret [:: HE_var 1; HE_var 0; HE_var 3;
          HE_var 2]))))))))))) ;;
     s ← denote_s_get_body chmsg_of_msg ;;
     resolve predictor (id_guess, (cipher_list t_cipher × t_msg, t_msg))
       (vt.1.1, s) ;;
     v2 ← denote_v2_get_body chmsg_of_msg ;;
     ret (msg_of_chmsg v2, vt.1.2.1.2)).
  have Hpd : forall (U V : choiceType) (f : U -> V) (D : distr.distr R U),
      psum (distr.mu (distr.dmargin f D)) = psum (distr.mu D).
    move=> U V f D; rewrite -[LHS]distr.pr_predT distr.pr_dmargin -[RHS]distr.pr_predT.
    by apply: distr.eq_pr => z; rewrite !inE.
  have mass_dlet : forall (U : finType) (V : choiceType)
      (f : U -> distr.distr R V) (mu0 : distr.distr R U),
      psum (distr.mu (distr.dlet f mu0))
      = psum (fun x => psum (distr.mu (f x)) * distr.mu mu0 x).
    move=> U V f mu0.
    transitivity (psum (fun y : V =>
        \sum_(x : U) distr.mu mu0 x * distr.mu (f x) y)).
      apply: eq_psum => y; rewrite distr.dletE psum_fin.
      by apply: eq_bigr => x _; rewrite ger0_norm //;
         apply: mulr_ge0; exact: distr.ge0_mu.
    rewrite -psum_bigop;
      [ | by move=> x y; apply: mulr_ge0; exact: distr.ge0_mu
        | by move=> x; apply: summableZ; exact: distr.summable_mu ].
    rewrite psum_fin; apply: eq_bigr => x _.
    rewrite ger0_norm; last by apply: mulr_ge0; [exact: ge0_psum | exact: distr.ge0_mu].
    by rewrite psumZ ?distr.ge0_mu // mulrC.
  have HDmass : psum (distr.mu (Pr_fst two_idx_code)) = 1.
    rewrite /two_idx_code.
    apply: Lossless_sample; first by apply: LosslessOp_uniform; exact: Hcard0.
    by move=> a; apply: Lossless_sample;
       first by apply: LosslessOp_uniform; exact: Hcard0.
  have HbodyEq : (x ← two_idx_code ;; INNERf x.1 x.2)
      = (gv ← guess_full_code ;; ret (proj gv)).
    have sba : forall (A B : choiceType) (op : Op) (k : Arit op -> raw_code A)
        (f : A -> raw_code B),
        (vt ← (x ← sample op ;; k x) ;; f vt)
        = (x ← sample op ;; vt ← k x ;; f vt) by [].
    rewrite Hbody gc_eq /two_idx_code drc_sample_msg
      [in X in _ = X]sba [in X in X = _]sba.
    apply: f_equal; apply: boolp.funext => a.
    rewrite drc_sample_msg [in X in _ = X]sba [in X in X = _]sba.
    apply: f_equal; apply: boolp.funext => b.
    by rewrite /INNERf.
  have HmeanD : psum (fun p : ('I_card_msg * 'I_card_msg)%type =>
      psum (distr.mu (Pr_code (INNERf p.1 p.2) emptym))
      * distr.mu (Pr_fst two_idx_code) p) = 1.
    under eq_psum => p do
      rewrite -(Hpd _ _ fst (Pr_code (INNERf p.1 p.2) emptym)).
    rewrite -mass_dlet.
    have Hvc : ValidCode emptym [interface] two_idx_code
      by rewrite /two_idx_code; ssprove_valid.
    rewrite -(Pr_fst_bind Hvc).
    by rewrite HbodyEq.
  have Hbound : forall p : ('I_card_msg * 'I_card_msg)%type,
      0 <= psum (distr.mu (Pr_code (INNERf p.1 p.2) emptym)) <= 1.
    by move=> p; rewrite ge0_psum distr.le1_mu.
  suff HM : forall p : ('I_card_msg * 'I_card_msg)%type,
      psum (distr.mu (Pr_code (INNERf p.1 p.2) emptym)) = 1.
    by rewrite /INNER; exact: (HM (x0, x1)).
  move=> p; apply: (mean1_eq1 Hbound HDmass HmeanD).
  rewrite /two_idx_code Pr_fst_sample.
  apply: (distr.dlet_dinsupp (x := p.1));
    first by rewrite distr.in_dinsupp distr.mkdistrE /UniformDistrLemmas.r
                     card_ord div1r invr_eq0 pnatr_eq0 -lt0n.
  rewrite Pr_fst_sample.
  apply: (distr.dlet_dinsupp (x := p.2));
    first by rewrite distr.in_dinsupp distr.mkdistrE /UniformDistrLemmas.r
                     card_ord div1r invr_eq0 pnatr_eq0 -lt0n.
  by rewrite Pr_fst_ret distr.dunit1E; case: p => a b; rewrite eqxx oner_neq0.
have Htwo : Pr_fst two_idx_code
    = distr.dlet (fun x0 => distr.dlet (fun x1 => distr.dunit (x0, x1))
        (projT2 (uniform card_msg))) (projT2 (uniform card_msg)).
  rewrite /two_idx_code Pr_fst_sample.
  apply: eq_dlet => x0; rewrite Pr_fst_sample.
  by apply: eq_dlet => x1; rewrite Pr_fst_ret.
have inner_sum : forall (x0 a b : 'I_card_msg),
    (\sum_(i < card_msg)
       ((x0, i) == (a, b) :> ('I_card_msg * 'I_card_msg)%type)%:R) = (x0 == a)%:R :> R.
  move=> x0 a b.
  rewrite (eq_bigr (fun i => (x0 == a)%:R * (i == b)%:R));
    last by move=> i _; rewrite xpair_eqE -natrM mulnb.
  rewrite (bigD1 b) //= eqxx mulr1 big1 ?addr0 // => i Hib.
  by rewrite (negbTE Hib) mulr0.
have Htwoval : forall p : ('I_card_msg * 'I_card_msg)%type,
    distr.mu (distr.dlet (fun x0 => distr.dlet (fun x1 => distr.dunit (x0, x1))
      (projT2 (uniform card_msg))) (projT2 (uniform card_msg))) p
    = ((card_msg * card_msg)%:R)^-1 :> R.
  move=> [a b].
  rewrite (dlet_uniform (Hlt := Hcard0)).
  under eq_bigr => x0 _.
    rewrite (dlet_uniform (Hlt := Hcard0)).
    under eq_bigr => x1 _ do rewrite distr.dunit1E.
    rewrite inner_sum.
    over.
  under eq_bigr => x0 _ do rewrite mulrC.
  rewrite -big_distrr /= (bigD1 a) //= eqxx big1 ?addr0;
    last by move=> i Hia; rewrite (negbTE Hia).
  by rewrite mulr1 -invfM -natrM.
rewrite -(fdistmap_bij_unif card_pair cardpp Hpairbij).
apply: fdist_ext => u.
rewrite sdistr_to_fdistE Hcore distr.dmargin_psumE fdistmapE Htwo.
under eq_psum => x do rewrite Htwoval.
rewrite psum_fin [RHS]big_mkcond /= [LHS]big_mkcond /=.
apply: eq_bigr => x _.
rewrite fdist_uniformE card_pair inE /=.
case: (pairmap x == u); rewrite ?mul1r ?mul0r ?normr0 //.
rewrite ger0_norm //.
  by rewrite prednK // muln_gt0 Hcard0.
by rewrite invr_ge0 ler0n.
Qed.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(* guess_VarRV_cond_uniform — the fiber-file instance of the entropy-side
   ring-generic conditional uniformity [Pr_dsdp_sol_uniform_ring]: conditioned on
   the inputs and the leaked output S, the secret pair (V2, V3) is uniform on the
   solution fiber, with mass 1/#|plain AHE|. *)
Lemma guess_VarRV_cond_uniform (s v2 v3 : plain AHE) :
  injective (fun v : plain AHE => w_u3 * v) ->
  `Pr[ [% V1, U1, U2, U3, Sout] = (w_v1, w_u1, w_u2, w_u3, s) ] != 0 ->
  (v2, v3) \in dsdp_fiber_ring w_u1 w_u2 w_u3 w_v1 s ->
  `Pr[ [% V2, V3] = (v2, v3)
     | [% V1, U1, U2, U3, Sout] = (w_v1, w_u1, w_u2, w_u3, s) ]
  = #|plain AHE|%:R^-1.
Proof.
move=> Hinj Hcond Hin.
apply: (@Pr_dsdp_sol_uniform_ring _ (plain AHE) _ guess_sample_fdist
          V1 V2 V3 U1 U2 U3 Sout).
- by move=> t; rewrite /dsdp_constraint_ring /Sout /dsdp_output /V1 /U1 /U2 /U3 /=
       !const_RVE; ring.
- by rewrite guess_VarRV_uniform; apply: fdist_ext => x; rewrite !fdist_uniformE.
- exact: guess_inputs_indep.
- exact: Hinj.
- exact: Hcond.
- exact: Hin.
Qed.

(* guess_V2_cond_Sout — conditioned on the leaked output S alone, the secret V2 is
   uniform on the plaintext space: marginalizing V3 out of [guess_VarRV_cond_uniform]
   over the single fiber solution (u3 injective) and dropping the constant inputs. *)
Lemma guess_V2_cond_Sout (a s : plain AHE) :
  injective (fun v : plain AHE => w_u3 * v) ->
  `Pr[ Sout = s ] != 0 ->
  `Pr[ V2 = a | Sout = s ] = #|plain AHE|%:R^-1.
Proof.
move=> Hinj Hs.
have Hbij : bijective (fun v : plain AHE => w_u3 * v) by apply: inj_card_bij.
case: Hbij => g Hg1 Hg2.
pose v3star := g (s - w_u1 * w_v1 - w_u2 * a).
have Hfib : (a, v3star) \in dsdp_fiber_ring w_u1 w_u2 w_u3 w_v1 s
  by rewrite inE /=; apply/eqP; rewrite /v3star Hg2; ring.
have Hnum : pfwd1 [% V2, Sout] (a, s)
          = pfwd1 [% [% V2, V3], Sout] ((a, v3star), s).
{ rewrite !pfwd1E; congr (Pr _ _).
  apply/setP => t; rewrite !inE /= !xpair_eqE.
  case Hva: (V2 t == a) => //=.
  move/eqP: Hva => Hva.
  have HsEq : (Sout t == s) = (V3 t == v3star).
  { rewrite /Sout /dsdp_output Hva.
    have -> : s = w_u1 * w_v1 + w_u2 * a + w_u3 * v3star
      by rewrite /v3star Hg2; ring.
    by rewrite (inj_eq (addrI _)) (inj_eq Hinj). }
  by rewrite HsEq andbb. }
have Hcst : [% V1, U1, U2, U3]
    = const_RV guess_sample_fdist (w_v1, w_u1, w_u2, w_u3)
  by apply: boolp.funext => t; rewrite /V1 /U1 /U2 /U3 !const_RVE.
have HcwN : `Pr[ [% V1, U1, U2, U3] = (w_v1, w_u1, w_u2, w_u3) ] != 0.
{ rewrite Hcst pfwd1E.
  have -> : finset (preim (const_RV guess_sample_fdist (w_v1, w_u1, w_u2, w_u3))
                     (pred1 (w_v1, w_u1, w_u2, w_u3))) = [set: _].
  { by apply/setP => t; rewrite !inE /= const_RVE eqxx. }
  by rewrite Pr_setT oner_neq0. }
have Hind : guess_sample_fdist |= [% V1, U1, U2, U3] _|_ [% [% V2, V3], Sout]
  by rewrite Hcst; exact: inde_const_RV.
have Hcond_eq : `Pr[ [% V1, U1, U2, U3, Sout] = (w_v1, w_u1, w_u2, w_u3, s) ]
              = `Pr[ Sout = s ].
{ rewrite Hcst !pfwd1E; congr (Pr _ _).
  by apply/setP => t; rewrite !inE /= !xpair_eqE !eqxx. }
rewrite cpr_eqE Hnum -cpr_eqE.
rewrite -(@cpr_eq_drop_indep _ _ guess_sample_fdist _ _ _ [% V2, V3] Sout
            [% V1, U1, U2, U3] (a, v3star) s (w_v1, w_u1, w_u2, w_u3) HcwN Hind).
apply: guess_VarRV_cond_uniform.
- exact: Hinj.
- by rewrite Hcond_eq.
- exact: Hfib.
Qed.

End dsdp_guess_distribution.
