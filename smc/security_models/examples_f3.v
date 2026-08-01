(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Require Import realType_ext realType_ln fdist proba variation_dist entropy.
Require Import finstoch statdist privacy_kernel.

(**md**************************************************************************)
(* # Worked examples of the privacy kernel                                    *)
(*                                                                            *)
(* The additive mask on the three-element field is the smallest instance of   *)
(* the privacy kernel that separates the three verdicts: a uniform mask sends *)
(* every input to the uniform law, the biased mask (1/2, 1/4, 1/4) keeps the  *)
(* view within statistical distance 6^-1 of that law, and with no mask the    *)
(* view is the input itself, which two inputs with the same allowed           *)
(* information tell apart.  A second instance, a uniform coin that the        *)
(* protocol both delivers to the honest party and shows to the adversary,     *)
(* carries a view-only simulator while the view and the honest output are     *)
(* conditionally dependent, so the conditional entropy of the honest output   *)
(* drops from log 2 to 0 once the view joins the conditioning.                *)
(*                                                                            *)
(* ```                                                                        *)
(*                card_F3 == the three-element field has three points         *)
(*                  unif3 == the uniform law on the three-element field       *)
(*          mask_chan m x == the law of the input x shifted by a mask drawn   *)
(*                           from m                                           *)
(*             mask_chanE == the mask channel reads the mask law at the       *)
(*                           shifted point                                    *)
(*         mask_chan_unif3 == a uniform mask sends every input to the uniform *)
(*                            law                                             *)
(*  mask_chan_uniform_hides == the uniform mask channel is the same law at    *)
(*                             every input                                    *)
(*                biased3 == the mask law with masses 1/2, 1/4, 1/4           *)
(*     biased3_0, biased3_1, biased3_2 == the three masses of biased3         *)
(*  mask_chan_biased_leaks == the biased mask channel is a different law at   *)
(*                            two inputs                                      *)
(*     biased_uniform_eps == the statistical distance between biased3 and     *)
(*                           unif3 is 6^-1                                    *)
(*      statdist_mask_chan == shifting a mask law leaves its distance to the  *)
(*                            uniform law unchanged                           *)
(*            dirac_shiftE == the point mass at a shift is the corresponding  *)
(*                            entry of the permutation matrix                 *)
(*           draw_add_mask == adding the ancilla to the input transports the  *)
(*                            ancilla draw to the mask channel                *)
(*       masking_verdicts == the additive mask on the three-element field,    *)
(*                           perfectly private under a uniform mask,          *)
(*                           6^-1-private under the biased mask and insecure  *)
(*                           with no mask                                     *)
(*              coin_leak == a delivered-and-shown uniform coin, an instance  *)
(*                           carrying a view-only simulator at which the view *)
(*                           and the honest output are conditionally          *)
(*                           dependent and the conditional entropy of the     *)
(*                           honest output drops from log 2 to 0              *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section f3_examples.
Context {R : realType}.
Let F3 : finType := 'F_3.

(* ex:smc:mask-matrix *)
(* The three-element field has three points. *)
Lemma card_F3 : #|F3| = 3.
Proof. by rewrite card_ord. Qed.

(* ex:smc:mask-matrix *)
(* The uniform law on the three-element field. *)
Definition unif3 : R.-fdist F3 := fdist_uniform card_F3.

(* ex:smc:mask-matrix *)
(* The mask channel at an input is the transport of the mask law along the
   shift by that input. *)
Definition mask_chan (m : R.-fdist F3) (x : F3) : R.-fdist F3 :=
  fdistmap (fun s => x + s) m.

(* ex:smc:mask-matrix *)
(* The mask channel reads the mask law at the shifted point. *)
Lemma mask_chanE (m : R.-fdist F3) (x b : F3) :
  mask_chan m x b = m (- x + b).
Proof.
rewrite /mask_chan fdistmapE (big_pred1 (- x + b)) //.
by move=> a; rewrite /= !inE (can2_eq (addKr x) (addNKr x)).
Qed.

(* ex:smc:mask-matrix *)
(* A uniform mask sends every input to the uniform law. *)
Lemma mask_chan_unif3 (x : F3) : mask_chan unif3 x = unif3.
Proof.
by apply/fdist_ext => b; rewrite mask_chanE /unif3 !fdist_uniformE.
Qed.

(* ex:smc:mask-matrix *)
(* The uniform mask channel is the same law at every input.
   Naming: mask_chan_<mask>_<verdict> is the intentional convention of this
   examples file, naming each channel lemma after its mask and its verdict. *)
Lemma mask_chan_uniform_hides (x x' : F3) :
  mask_chan unif3 x = mask_chan unif3 x'.
Proof. by rewrite !mask_chan_unif3. Qed.

(* ex:smc:mask-matrix *)
(* The biased mask law puts 1/2 on zero and splits the remaining half evenly
   over the other two points. *)
Definition biased3 : R.-fdist F3 :=
  (fdist1 0 <| (2^-1 : R)%:pr |>
     (fdist1 1 <| (2^-1 : R)%:pr |> fdist1 (1 + 1)))%fdist.

(* ex:smc:mask-matrix *)
(* The biased mask law gives one half to zero. *)
Lemma biased3_0 : biased3 0 = 2^-1.
Proof. by rewrite /biased3 !fdist_convE !fdist1E /= onemE; lra. Qed.

(* ex:smc:mask-matrix *)
(* The biased mask law gives one quarter to one. *)
Lemma biased3_1 : biased3 1 = 4^-1.
Proof. by rewrite /biased3 !fdist_convE !fdist1E /= onemE; lra. Qed.

(* ex:smc:mask-matrix *)
(* The biased mask law gives one quarter to two. *)
Lemma biased3_2 : biased3 (1 + 1) = 4^-1.
Proof. by rewrite /biased3 !fdist_convE !fdist1E /= onemE; lra. Qed.

(* ex:smc:mask-matrix *)
(* The biased mask channel is a different law at the inputs zero and one.
   Naming: mask_chan_<mask>_<verdict> is the intentional convention of this
   examples file, naming each channel lemma after its mask and its verdict. *)
Lemma mask_chan_biased_leaks :
  mask_chan biased3 0 <> mask_chan biased3 1.
Proof.
move=> h.
have h1 : mask_chan biased3 0 1 = mask_chan biased3 1 1 :> R by rewrite h.
by move: h1; rewrite !mask_chanE oppr0 add0r addNr biased3_0 biased3_1; lra.
Qed.

(* tab:smc:privacy-laws *)
(* The statistical distance between the biased mask law and the uniform law is
   one sixth.
   Naming: eps is intentional, the privacy-epsilon vocabulary of
   tab:smc:privacy-laws whose approximate row this value instantiates. *)
Lemma biased_uniform_eps : statdist biased3 unif3 = 6%:R^-1.
Proof.
rewrite /statdist /var_dist /unif3.
under eq_bigr do rewrite fdist_uniformE card_F3.
rewrite !big_ord_recl big_ord0.
rewrite (_ : lift ord0 (lift ord0 ord0) = 1 + 1 :> F3); last exact/val_inj.
rewrite (_ : lift ord0 ord0 = 1 :> F3); last exact/val_inj.
rewrite biased3_0 biased3_1 biased3_2.
by rewrite ger0_norm ?ler0_norm; lra.
Qed.

(* tab:smc:privacy-laws *)
(* Shifting a mask law leaves its statistical distance to the uniform law
   unchanged. *)
Lemma statdist_mask_chan (m : R.-fdist F3) (x : F3) :
  statdist (mask_chan m x) unif3 = statdist m unif3.
Proof.
rewrite /statdist /var_dist; congr (_ * _).
rewrite (reindex_inj (addrI x)) /=.
by apply: eq_bigr => b _; rewrite mask_chanE addKr /unif3 !fdist_uniformE.
Qed.

(* ex:smc:dirac-matrix *)
(* The point mass at a shift is the corresponding entry of the permutation
   matrix. *)
Lemma dirac_shiftE (x y : F3) :
  fdist1 (x + 1) y = (y == x + 1)%:R :> R.
Proof. by rewrite fdist1E eq_sym. Qed.

(* ex:smc:ancilla-matrix *)
(* Adding the ancilla to the input transports the ancilla draw to the mask
   channel.
   Naming: draw_add_mask is intentional, reading the three cells of
   ex:smc:ancilla-matrix in the order the diagram composes them. *)
Lemma draw_add_mask (m : R.-fdist F3) (x : F3) :
  fdistmap (fun e : F3 * F3 => e.1 + e.2) (tensor (fdist1 x) m)
  = mask_chan m x.
Proof. by rewrite tensor_fdist1 fdistmap_comp. Qed.

End f3_examples.

(* The additive mask on the three-element field, the 'F_3 analogue of the
   chapter's 'F_29 instance: the adversary sees the input shifted by the
   ancilla, the ideal functionality delivers a one-point output and the
   adversary has no input, so the allowed information is the same at every
   input.  The three ancilla laws give the three verdicts of
   tab:smc:privacy-laws. *)
Module masking_verdicts.
Section instance.
Context {R : realType}.

(* The ideal functionality delivers the one-point output. *)
Definition functionality (x : 'F_3) : R.-fdist 'I_1 := fdist1 ord0.

(* The function the protocol computes is the one-point constant. *)
Definition outcome (x : 'F_3) : 'I_1 := ord0.

(* The adversary has no input. *)
Definition proj_adv_input (x : 'F_3) : 'I_1 := ord0.

(* The run delivers the one-point output. *)
Definition deliver (e : 'F_3 * 'F_3) : 'I_1 := ord0.

(* The adversary observes the input shifted by the ancilla. *)
Definition mask_view (e : 'F_3 * 'F_3) : 'F_3 := e.1 + e.2.

(* The uniform ancilla law. *)
Definition uniform_mask : R.-fdist 'F_3 := unif3.

(* The biased ancilla law. *)
Definition biased_mask : R.-fdist 'F_3 := biased3.

(* The one-point ancilla law. *)
Definition no_mask : R.-fdist 'I_1 := fdist1 ord0.

(* With a one-point ancilla the adversary observes the input itself. *)
Definition plain_view (e : 'F_3 * 'I_1) : 'F_3 := e.1.

(* The simulator answers the uniform law. *)
Definition sim_mask : simulator (R := R) 'I_1 'I_1 'F_3 := fun=> uniform_mask.

(* The identity aggregation of the ideal functionality is the point mass at the
   value of the outcome. *)
Lemma functionality_compat (x : 'F_3) :
  fdistmap id (functionality x) = fdist1 (outcome x).
Proof. by rewrite /functionality fdistmap_id. Qed.

(* The run of the execution context computes the outcome. *)
Lemma run_correct (e : 'F_3 * 'F_3) : id (deliver e) = outcome e.1.
Proof. by []. Qed.

(* prop:smc:worlds-compute-f *)
(* The ideal route computes the outcome at this instance. *)
Lemma ideal_route (x : 'F_3) :
  fdistmap (fun xy : 'F_3 * 'I_1 => id xy.2)
           (tensor (fdist1 x) (functionality x)) = fdist1 (outcome x).
Proof. exact: (ideal_route_f functionality_compat x). Qed.

(* prop:smc:worlds-compute-f *)
(* The real route computes the outcome at this instance. *)
Lemma real_route (x : 'F_3) :
  fdistmap (fun e : 'F_3 * 'F_3 => id (deliver e)) (draw uniform_mask x)
  = fdist1 (outcome x).
Proof. exact: (real_route_f uniform_mask run_correct x). Qed.

(* The allowed information is the same at every input. *)
Lemma allow_const (x x' : 'F_3) :
  allow proj_adv_input id functionality x
  = allow proj_adv_input id functionality x'.
Proof. by rewrite !allowE. Qed.

(* The view law of the additive mask is the mask channel. *)
Lemma view_law_maskE (m : R.-fdist 'F_3) (x : 'F_3) :
  view_law m mask_view x = mask_chan m x.
Proof. by rewrite view_lawE. Qed.

(* The simulated view law is the uniform law at every input. *)
Lemma sim_view_maskE (x : 'F_3) :
  sim_view proj_adv_input id functionality sim_mask x = uniform_mask.
Proof.
by rewrite /sim_view allowE /f_a /functionality tensor_fdist1 !fdistmap1
           fdist1bind.
Qed.

(* tab:smc:privacy-laws, perfect row *)
(* Under a uniform mask the instance is perfectly private. *)
Lemma perfect_privacy_uniform :
  perfect_privacy proj_adv_input id functionality uniform_mask mask_view
                  sim_mask.
Proof.
move=> x; rewrite view_law_maskE sim_view_maskE /uniform_mask.
exact: mask_chan_unif3.
Qed.

(* tab:smc:privacy-laws, approximate row *)
(* Under the biased mask the instance is private up to one sixth. *)
Lemma eps_privacy_biased :
  eps_privacy proj_adv_input id functionality biased_mask mask_view sim_mask
              6%:R^-1.
Proof.
move=> x; rewrite view_law_maskE sim_view_maskE statdist_mask_chan.
by rewrite /biased_mask /uniform_mask biased_uniform_eps.
Qed.

(* With no mask the view law is the point mass at the input. *)
Lemma view_law_plainE (x : 'F_3) : view_law no_mask plain_view x = fdist1 x.
Proof. by rewrite view_lawE /no_mask fdistmap1. Qed.

(* tab:smc:privacy-laws, insecure row *)
(* With no mask the inputs zero and one have the same allowed information and
   different view laws, so no simulator achieves perfect privacy. *)
Lemma insecurity_no_mask :
  ~ (exists S : simulator 'I_1 'I_1 'F_3,
       perfect_privacy proj_adv_input id functionality no_mask plain_view S).
Proof.
apply: (insecurity (x := 0) (x' := 1)); first exact: allow_const.
rewrite !view_law_plainE; apply/eqP => /fdist1_inj /eqP.
by rewrite eq_sym oner_eq0.
Qed.

End instance.
End masking_verdicts.

(* A uniform coin that the protocol delivers to the honest party and also shows
   to the adversary, over a one-point input space with trivial allowed
   information.  The view-only privacy triangle holds at this instance, yet the
   view and the honest output are conditionally dependent given the allowed
   information, and the conditional entropy of the honest output is log 2
   given the allowed information alone and 0 once the view joins it. *)
Module coin_leak.
Section instance.
Context {R : realType}.

(* The ancilla is a uniform coin. *)
Definition coin : R.-fdist 'I_2 := fdist_uniform (card_ord 2).

(* The execution context pairs the one-point input with the coin. *)
Definition exec_law : R.-fdist ('I_1 * 'I_2)%type := tensor (fdist1 ord0) coin.

(* The adversary observes the coin. *)
Definition view_rv : {RV exec_law -> 'I_2} := snd.

(* The honest party is delivered the coin. *)
Definition honest_rv : {RV exec_law -> 'I_2} := snd.

(* The input of the execution. *)
Definition input_rv : {RV exec_law -> 'I_1} := fst.

(* The allowed information is trivial. *)
Definition allow_rv : {RV exec_law -> 'I_1} := fst.

(* The allowed information at an input is that input. *)
Definition allow_info (x : 'I_1) : 'I_1 := x.

(* The simulator answers the coin law. *)
Definition sim (a : 'I_1) : R.-fdist 'I_2 := coin.

(* Every execution has mass one half. *)
Lemma exec_lawE u : exec_law u = 2%:R^-1.
Proof.
case: u => a b; rewrite /exec_law tensorE (ord1 a) fdist1xx mul1r.
by rewrite /coin fdist_uniformE card_ord.
Qed.

(* A one-point-valued variable takes its unique value almost surely. *)
Lemma pfwd1_ord1 (Z : {RV exec_law -> 'I_1}) (t : 'I_1) : `Pr[ Z = t ] = 1.
Proof.
rewrite pfwd1E.
suff -> : finset (Z @^-1 t) = [set: ('I_1 * 'I_2)%type] by rewrite Pr_setT.
by apply/setP => u; rewrite !inE (ord1 (Z u)) (ord1 t) eqxx.
Qed.

(* The view and the input take each joint value with probability one half. *)
Lemma pfwd1_view_input (v : 'I_2) (x : 'I_1) :
  `Pr[ [% view_rv, input_rv] = (v, x) ] = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% view_rv, input_rv] @^-1 (v, x))
          = [set (ord0, v) : 'I_1 * 'I_2] by rewrite Pr_set1 exec_lawE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /view_rv /input_rv /=.
by rewrite (ord1 a) (ord1 x) !eqxx andbT.
Qed.

(* The view and the allowed information are jointly zero with probability one
   half. *)
Lemma pfwd1_view_allow :
  `Pr[ [% view_rv, allow_rv] = (ord0, ord0) ] = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% view_rv, allow_rv] @^-1 (ord0, ord0))
          = [set (ord0, ord0) : 'I_1 * 'I_2] by rewrite Pr_set1 exec_lawE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /view_rv /allow_rv /=.
by rewrite (ord1 a) !eqxx andbT.
Qed.

(* The honest output and the allowed information are jointly zero with
   probability one half. *)
Lemma pfwd1_honest_allow :
  `Pr[ [% honest_rv, allow_rv] = (ord0, ord0) ] = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% honest_rv, allow_rv] @^-1 (ord0, ord0))
          = [set (ord0, ord0) : 'I_1 * 'I_2] by rewrite Pr_set1 exec_lawE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /honest_rv /allow_rv /=.
by rewrite (ord1 a) !eqxx andbT.
Qed.

(* The view, the honest output and the allowed information are jointly zero
   with probability one half.
   Naming: pfwd1_<variable tuple>, the intentional three-variable extension of
   pfwd1_view_allow and pfwd1_honest_allow. *)
Lemma pfwd1_view_honest_allow :
  `Pr[ [% [% view_rv, honest_rv], allow_rv] = ((ord0, ord0), ord0) ]
  = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% [% view_rv, honest_rv], allow_rv]
                    @^-1 ((ord0, ord0), ord0))
          = [set (ord0, ord0) : 'I_1 * 'I_2] by rewrite Pr_set1 exec_lawE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /view_rv /honest_rv /allow_rv /=.
by rewrite (ord1 a) !eqxx andbb andbT.
Qed.

(* def:smc:perfect-privacy *)
(* The view law conditioned on an input is the simulator at the allowed
   information of that input. *)
Lemma view_only_triangle (x : 'I_1) : `Pr[ input_rv = x ] != 0 ->
  forall v : 'I_2, `Pr[ view_rv = v | input_rv = x ] = sim (allow_info x) v.
Proof.
move=> _ v; rewrite cpr_eqE pfwd1_ord1 divr1 pfwd1_view_input.
by rewrite /sim /coin fdist_uniformE card_ord.
Qed.

(* The view and the honest output are conditionally dependent given the allowed
   information. *)
Lemma not_cinde_honest : ~ (exec_law |= view_rv _|_ honest_rv | allow_rv).
Proof.
move=> h; have := h ord0 ord0 ord0.
rewrite !cpr_eqE !pfwd1_ord1 !divr1.
rewrite pfwd1_view_honest_allow pfwd1_view_allow ?pfwd1_honest_allow.
by move=> h1; lra.
Qed.

(* eq:smc:entropy, left side *)
(* The view determines the honest output, so their conditional entropy given
   the view and the allowed information vanishes. *)
Lemma centropy_view_honest0 :
  `H( honest_rv | [% view_rv, allow_rv] ) = 0.
Proof. exact: (centropy_RV_comp0 [% view_rv, allow_rv] fst). Qed.

(* The law of the honest output is the coin law. *)
Lemma honest_lawE : `p_ honest_rv = coin.
Proof.
apply/fdist_ext => b; rewrite dist_of_RVE pfwd1E.
suff -> : finset (honest_rv @^-1 b) = [set (ord0, b) : 'I_1 * 'I_2].
  by rewrite Pr_set1 exec_lawE /coin fdist_uniformE card_ord.
by apply/setP => -[a c]; rewrite !inE /honest_rv/= xpair_eqE (ord1 a) eqxx.
Qed.

(* The honest output and the allowed information are independent. *)
Lemma joint_honest_allow :
  `p_ [% honest_rv, allow_rv] = (`p_ honest_rv `x `p_ allow_rv)%fdist.
Proof.
apply/fdist_ext => -[b a]; rewrite fdist_prodE !dist_of_RVE.
rewrite pfwd1_ord1 mulr1 !pfwd1E; congr Pr; apply/setP => -[c d].
by rewrite !inE /honest_rv /allow_rv/= xpair_eqE (ord1 c) (ord1 a) eqxx andbT.
Qed.

(* eq:smc:entropy, right side *)
(* Given the allowed information alone the honest output has conditional
   entropy log 2. *)
Lemma centropy_honest_allow : `H( honest_rv | allow_rv ) = log 2%:R :> R.
Proof.
have H1 : `p_ [% honest_rv, allow_rv]
  = ((`p_ [% honest_rv, allow_rv])`1 `x (`p_ [% honest_rv, allow_rv])`2)%fdist.
  by rewrite fst_RV2 snd_RV2 joint_honest_allow.
rewrite /centropy_RV (centropy_indep H1) fst_RV2 honest_lawE.
by rewrite /coin entropy_uniform card_ord.
Qed.

(* eq:smc:entropy *)
(* The conditional entropy of the honest output given the allowed information
   changes when the view joins the conditioning.
   Naming: centropy_<conditioner joined>_<conditioned>_neq is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_view_honest_neq :
  `H( honest_rv | [% view_rv, allow_rv] ) <> `H( honest_rv | allow_rv ).
Proof.
rewrite centropy_view_honest0 centropy_honest_allow log2.
by move/eqP; rewrite eq_sym oner_eq0.
Qed.

End instance.
End coin_leak.
