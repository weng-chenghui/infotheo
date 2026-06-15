(* dsdp_convert — generic bridge between SSProve subdistributions / Pr_code and
   Infotheo fdist / Pr.  The SDist<->fdist conversion plus the value-marginal
   framing lemmas (footprint, write-invariance, pushforward composition,
   bijection-carries-uniform, lossless-mean normalization) used to read an
   SSProve game's value marginal as an Infotheo distribution.  Consumed by
   indcpa_hopping/dsdp_guess_fiber. *)

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
Require Import smc.ssprove_ext_lossless.

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

(* dlet_dmargin_eq — a bind over a pushforward reindexes the kernel: binding [g]
   over [dmargin f mu] is binding [g \o f] over [mu].  Keeps [dmargin] folded
   (unlike unfolding to [dlet] then [dlet_dlet_ext], which exposes the monad
   internals). *)
Lemma dlet_dmargin_eq {T U V : choiceType} (g : U -> distr.distr R V)
    (f : T -> U) (mu : distr.distr R T) :
  distr.dlet g (distr.dmargin f mu) = distr.dlet (fun x => g (f x)) mu.
Proof.
rewrite distr.dmarginE dlet_dlet_ext.
by apply: eq_dlet => x; rewrite dlet_unit_ext.
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
