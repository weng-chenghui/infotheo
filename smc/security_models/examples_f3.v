(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Require Import realType_ext realType_ln fdist proba variation_dist entropy.
Require Import finstoch statdist privacy_kernel entropy_link.

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
(* drops from log 2 to 0 once the view joins the conditioning.  A third       *)
(* instance shares the sum of three private bits among three parties and      *)
(* echoes one honest share into the view: the compatibility square, the       *)
(* delivery law and an output-consistent privacy triangle hold, while the     *)
(* view and the honest shares are conditionally dependent and the same        *)
(* entropy drop occurs.                                                       *)
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
(*             share_leak == a three-party additive sharing of the sum of     *)
(*                           three private bits whose protocol echoes one     *)
(*                           honest share into the view, an instance          *)
(*                           satisfying the compatibility square, the         *)
(*                           delivery law and the privacy triangle at which   *)
(*                           the view and the honest shares are               *)
(*                           conditionally dependent and the conditional      *)
(*                           entropy of the honest shares drops from log 2    *)
(*                           to 0                                             *)
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

(* ex:smc:share-leak *)
(* Three parties additively share the sum of three private bits over the
   two-element field and the protocol shows the adversary, party one, the
   share delivered to party two.  The compatibility square, the delivery law
   and an output-consistent privacy triangle hold, while the view and the
   honest shares are conditionally dependent given the input and the
   adversary's share, and the conditional entropy of the honest shares drops
   from log 2 to 0 once the view joins the conditioning.  The ideal
   functionality is the standard three-party additive sharing, uniform on the
   first two shares with the third completing the sum, fixed independently of
   the leaking protocol.  Three parties are the minimum, since with two the
   honest share is determined by the input and the adversary's share, the
   hypothesis of output_independent_determined. *)
Module share_leak.
Section instance.
Context {R : realType}.

(* The two-element field. *)
Let F2 : finType := 'F_2.

(* The two-element field has two points. *)
Lemma card_F2 : #|F2| = 2.
Proof. by rewrite card_ord. Qed.

(* The uniform law on the two-element field. *)
Definition unif2 : R.-fdist F2 := fdist_uniform card_F2.

(* The input space gives one private bit to each of the three parties. *)
Let X3 := (F2 * F2 * F2)%type.

(* The input space has eight points. *)
Lemma card_X3 : #|(X3 : finType)| = 8.
Proof. by rewrite !card_prod !card_F2. Qed.

(* The prior on the input space is uniform.
   Naming: mu is intentional, the thesis notation $\mu$ for the prior on the
   input space. *)
Definition mu : R.-fdist X3 := fdist_uniform card_X3.

(* The ancilla law draws the two free shares as independent uniform bits. *)
Definition P_Omega : R.-fdist (F2 * F2)%type := tensor unif2 unif2.

(* The execution context pairs an input with the ancilla. *)
Definition exec_law : R.-fdist (X3 * (F2 * F2))%type := tensor mu P_Omega.

(* The function the protocol computes is the sum of the three private bits. *)
Definition f_sum (x : X3) : F2 := x.1.1 + x.1.2 + x.2.

(* The input of the execution. *)
Definition input_rv : {RV exec_law -> X3} := fst.

(* The private bit of the adversary, party one. *)
Definition adv_input_rv : {RV exec_law -> F2} := fun e => e.1.1.1.

(* The share delivered to the adversary. *)
Definition y1_rv : {RV exec_law -> F2} := fun e => e.2.1.

(* The share delivered to party two. *)
Definition y2_rv : {RV exec_law -> F2} := fun e => e.2.2.

(* The share delivered to party three completes the sum. *)
Definition y3_rv : {RV exec_law -> F2} :=
  fun e => f_sum e.1 - e.2.1 - e.2.2.

(* The adversary observes its own bit, its own share and the share delivered
   to party two. *)
Definition view_rv := [% adv_input_rv, y1_rv, y2_rv].

(* The shares delivered to the two honest parties. *)
Definition honest_rv := [% y2_rv, y3_rv].

(* The allowed information is the adversary's bit and its delivered share. *)
Definition allow_rv := [% adv_input_rv, y1_rv].

(* The conditioner is the input and the adversary's delivered share. *)
Definition cond_rv := [% input_rv, y1_rv].

(* The three delivered shares. *)
Definition shares_rv := [% y1_rv, y2_rv, y3_rv].

(* The simulator answers the allowed information together with a uniform bit
   in the echoed slot. *)
Definition sim : simulator (R := R) F2 F2 ((F2 * F2) * F2)%type :=
  fun a => tensor (fdist1 a) unif2.

(* The share map sends an ancilla to the two free shares and the share that
   completes the sum at an input. *)
Definition share_map (x : X3) (w : F2 * F2) : (F2 * F2) * F2 :=
  ((w.1, w.2), f_sum x - w.1 - w.2).

(* The ideal functionality at an input is the transport of the ancilla law
   along the share map. *)
Definition functionality (x : X3) : R.-fdist ((F2 * F2) * F2)%type :=
  fdistmap (share_map x) P_Omega.

(* The aggregation of three shares is their sum. *)
Definition agg (s : (F2 * F2) * F2) : F2 := s.1.1 + s.1.2 + s.2.

(* Every execution has mass one over thirty-two. *)
Lemma exec_lawE u : exec_law u = 32%:R^-1.
Proof.
case: u => x [s t]; rewrite /exec_law /P_Omega !tensorE !fdist_uniformE.
by rewrite card_X3 card_F2 -!invfM -!natrM.
Qed.

(* Every execution has positive mass. *)
Let exec_law_neq0 (e : X3 * (F2 * F2)%type) : exec_law e != 0.
Proof. by rewrite exec_lawE invr_eq0 pnatr_eq0. Qed.

(* The probability of a value of a variable is the cardinality of the preimage
   of that value over thirty-two. *)
Lemma pfwd1_cardE (T' : finType) (Z : {RV exec_law -> T'}) (z : T') :
  `Pr[ Z = z ] = #|finset (Z @^-1 z)|%:R * 32%:R^-1.
Proof.
rewrite pfwd1E /Pr; under eq_bigr do rewrite exec_lawE.
by rewrite big_const iter_addr addr0 mulr_natl.
Qed.

(* A set of n points out of thirty-two has mass k^-1 when n times k is
   thirty-two. *)
Let count_mass (n k : nat) : (n * k)%N = 32%N -> n != 0%N ->
  n%:R * 32%:R^-1 = (k%:R^-1 : R).
Proof.
by move=> <- n0; rewrite natrM invfM mulrA mulfV ?pnatr_eq0// mul1r.
Qed.

(* The conditioner has two preimage points at every value. *)
Lemma card_preim_cond (x : X3) (s : F2) :
  #|finset (cond_rv @^-1 (x, s))| = 2.
Proof.
have -> : finset (cond_rv @^-1 (x, s)) = setX [set x] (setX [set s] [set: F2]).
  apply/setP => -[x' [s' t']].
  by rewrite !inE !xpair_eqE /cond_rv /input_rv /y1_rv /= andbT.
by rewrite !cardsX !cards1 cardsT card_F2.
Qed.

(* The view has four preimage points at every value. *)
Lemma card_preim_view (v : (F2 * F2) * F2) :
  #|finset (view_rv @^-1 v)| = 4.
Proof.
case: v => -[a s] t.
have -> : finset (view_rv @^-1 ((a, s), t))
        = setX (setX (setX [set a] [set: F2]) [set: F2]) (setX [set s] [set t]).
  apply/setP => -[[[x1 x2] x3] [s' t']].
  rewrite !inE !xpair_eqE /view_rv /adv_input_rv /y1_rv /y2_rv /=.
  by rewrite !andbT andbA.
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The allowed information has eight preimage points at every value. *)
Lemma card_preim_allow (a s : F2) :
  #|finset (allow_rv @^-1 (a, s))| = 8.
Proof.
have -> : finset (allow_rv @^-1 (a, s))
        = setX (setX (setX [set a] [set: F2]) [set: F2])
               (setX [set s] [set: F2]).
  apply/setP => -[[[x1 x2] x3] [s' t']].
  by rewrite !inE !xpair_eqE /allow_rv /adv_input_rv /y1_rv /= !andbT.
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The input has four preimage points at every value. *)
Lemma card_preim_input (x : X3) :
  #|finset (input_rv @^-1 x)| = 4.
Proof.
have -> : finset (input_rv @^-1 x) = setX [set x] [set: (F2 * F2)%type].
  by apply/setP => -[x' w]; rewrite !inE /input_rv /= andbT.
by rewrite cardsX cards1 cardsT card_prod card_F2.
Qed.

(* The share delivered to party two has sixteen preimage points at every
   value. *)
Lemma card_preim_y2 (t : F2) : #|finset (y2_rv @^-1 t)| = 16.
Proof.
have -> : finset (y2_rv @^-1 t) = setX [set: X3] (setX [set: F2] [set t]).
  by apply/setP => -[x [s' t']]; rewrite !inE /y2_rv /=.
by rewrite !cardsX cards1 !cardsT card_X3 card_F2.
Qed.

(* The share delivered to party two and the conditioner have one preimage
   point at every joint value. *)
Lemma card_preim_y2_cond (t : F2) (x : X3) (s : F2) :
  #|finset ([% y2_rv, cond_rv] @^-1 (t, (x, s)))| = 1.
Proof.
have -> : finset ([% y2_rv, cond_rv] @^-1 (t, (x, s))) = [set (x, (s, t))].
  apply/setP => -[x' [s' t']].
  by rewrite !inE !xpair_eqE /y2_rv /cond_rv /input_rv /y1_rv /= andbC andbA.
by rewrite cards1.
Qed.

(* The conditioner takes each value with probability one over sixteen. *)
Lemma pfwd1_cond (x : X3) (s : F2) :
  `Pr[ cond_rv = (x, s) ] = 16%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_cond; apply: count_mass. Qed.

(* The view takes each value with probability one eighth. *)
Lemma pfwd1_view (v : (F2 * F2) * F2) : `Pr[ view_rv = v ] = 8%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_view; apply: count_mass. Qed.

(* The allowed information takes each value with probability one quarter. *)
Lemma pfwd1_allow (a s : F2) : `Pr[ allow_rv = (a, s) ] = 4%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_allow; apply: count_mass. Qed.

(* The input takes each value with probability one eighth. *)
Lemma pfwd1_input (x : X3) : `Pr[ input_rv = x ] = 8%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_input; apply: count_mass. Qed.

(* The share delivered to party two takes each value with probability one
   half. *)
Lemma pfwd1_y2 (t : F2) : `Pr[ y2_rv = t ] = 2%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_y2; apply: count_mass. Qed.

(* The share delivered to party two and the conditioner take each joint value
   with probability one over thirty-two. *)
Lemma pfwd1_y2_cond (t : F2) (x : X3) (s : F2) :
  `Pr[ [% y2_rv, cond_rv] = (t, (x, s)) ] = 32%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_y2_cond mul1r. Qed.

(* The all-zero input. *)
Let x0 : X3 := (0, 0, 0).

(* The execution at the all-zero input and the all-zero ancilla. *)
Let pt0 : X3 * (F2 * F2)%type := (x0, (0, 0)).

(* The sum of the all-zero input is zero. *)
Let f_sum_x0 : f_sum x0 = 0.
Proof. by rewrite /f_sum /= !addr0. Qed.

(* The view, the honest shares and the conditioner have one preimage point at
   the all-zero joint value. *)
Let card_vh_cond :
  #|finset ([% [% view_rv, honest_rv], cond_rv]
              @^-1 ((((0, 0), 0), (0, 0)), (x0, 0)))| = 1.
Proof.
have -> : finset ([% [% view_rv, honest_rv], cond_rv]
                    @^-1 ((((0, 0), 0), (0, 0)), (x0, 0))) = [set pt0].
  apply/setP => -[x' [s' t']].
  rewrite !inE !xpair_eqE /view_rv /honest_rv /cond_rv /adv_input_rv
          /y1_rv /y2_rv /y3_rv /input_rv /=.
  case: (eqVneq x' x0) => [->|xne]/=; last by rewrite andbF.
  by case: (eqVneq s' 0) => [->|sne]//=; case: (eqVneq t' 0) => [->|tne]//=.
by rewrite cards1.
Qed.

(* The view and the conditioner have one preimage point at the all-zero joint
   value. *)
Let card_v_cond :
  #|finset ([% view_rv, cond_rv] @^-1 ((((0, 0), 0)), (x0, 0)))| = 1.
Proof.
have -> : finset ([% view_rv, cond_rv] @^-1 ((((0, 0), 0)), (x0, 0)))
        = [set pt0].
  apply/setP => -[x' [s' t']].
  rewrite !inE !xpair_eqE /view_rv /cond_rv /adv_input_rv /y1_rv /y2_rv /=.
  case: (eqVneq x' x0) => [->|xne]/=; last by rewrite andbF.
  by rewrite andbAC andbb.
by rewrite cards1.
Qed.

(* The honest shares and the conditioner have one preimage point at the
   all-zero joint value. *)
Let card_h_cond :
  #|finset ([% honest_rv, cond_rv] @^-1 ((0, 0), (x0, 0)))| = 1.
Proof.
have -> : finset ([% honest_rv, cond_rv] @^-1 ((0, 0), (x0, 0))) = [set pt0].
  apply/setP => -[x' [s' t']].
  rewrite !inE !xpair_eqE /honest_rv /cond_rv /y2_rv /y3_rv /y1_rv /=.
  case: (eqVneq x' x0) => [->|xne]/=; last by rewrite andbF.
  rewrite f_sum_x0; case: (eqVneq s' 0) => [->|sne]/=; last by rewrite andbF.
  by case: (eqVneq t' 0) => [->|tne]//=.
by rewrite cards1.
Qed.

(* eq:smc:functionality-compat *)
(* The aggregation of the ideal functionality is the point mass at the value
   of the function. *)
Lemma functionality_compat (x : X3) :
  fdistmap agg (functionality x) = fdist1 (f_sum x).
Proof.
rewrite /functionality fdistmap_comp; apply: eq_fdistmap_cst => w /=.
by rewrite /agg /share_map /= addrCA addrK subrK.
Qed.

(* The output read off a simulated view is the point mass at the delivered
   share the simulator was handed. *)
Lemma sim_consistent (a : F2 * F2) :
  fdistmap (fun v : (F2 * F2) * F2 => v.1.2) (sim a) = fdist1 a.2.
Proof. by rewrite /sim tensor_fdist1 fdistmap_comp; apply: eq_fdistmap_cst. Qed.

(* On every positive-mass fibre of the conditioner the view law is the
   simulator at the allowed information.
   Naming: view_cond_sim mirrors bob_view_cond_sim_xy of the scalar-product
   bridge, naming a conditional view law after the simulator it equals. *)
Lemma view_cond_sim (x : X3) (s : F2) :
  `Pr[ cond_rv = (x, s) ] != 0 ->
  forall v, `Pr[ view_rv = v | cond_rv = (x, s) ] = sim (x.1.1, s) v.
Proof.
move=> _ [[a s'] t]; rewrite cpr_eqE pfwd1_cond invrK pfwd1_cardE.
rewrite /sim tensorE fdist1E xpair_eqE fdist_uniformE card_F2.
have -> : finset ([% view_rv, cond_rv] @^-1 (((a, s'), t), (x, s)))
        = if (a == x.1.1) && (s' == s) then [set (x, (s, t))] else set0.
  apply/setP => -[x' [s'' t']].
  rewrite !inE !xpair_eqE /view_rv /cond_rv /adv_input_rv /y1_rv /y2_rv /=.
  case: (eqVneq x' x) => [->|xne]/=; last first.
    by rewrite andbF; case: ifP => _; rewrite !inE ?xpair_eqE ?(negbTE xne)//.
  case: (eqVneq s'' s) => [->|sne]/=; last first.
    by rewrite !andbF; case: ifP => _;
      rewrite !inE ?xpair_eqE ?(negbTE sne) ?andbF//.
  rewrite andbT; case: (eqVneq a x.1.1) => [ea|ane]/=; last by rewrite inE.
  case: (eqVneq s' s) => [es|s'ne]/=; last by rewrite inE.
  by rewrite !inE !xpair_eqE !eqxx.
case: ifP => _; last by rewrite cards0 !mul0r.
by rewrite cards1 mul1r mulrC div1r; apply: count_mass.
Qed.

(* The view law is the allowed-information law bound through the simulator.
   Naming: _factorization names the >>= decomposition, mirroring
   spp_bob_factorization of the scalar-product bridge. *)
Lemma view_factorization :
  `p_ view_rv = `p_ allow_rv >>= sim.
Proof.
apply/fdist_ext => -[[a s] t]; rewrite dist_of_RVE [RHS]fdistbindE pfwd1_view.
rewrite (bigD1 (a, s))//= big1 ?addr0; last first.
  move=> a' ane; rewrite /sim tensorE fdist1E.
  by rewrite eq_sym (negbTE ane) mul0r mulr0.
rewrite dist_of_RVE pfwd1_allow /sim tensorE fdist1E eqxx/=.
by rewrite mul1r /unif2 fdist_uniformE card_F2 -invfM -natrM.
Qed.

(* On every positive-mass input the delivered shares follow the ideal
   functionality.
   Naming: the _ok suffix carries over from the delivery-law condition
   delivery_law_ok of entropy_link.v, stated here in conditional form. *)
Lemma delivery_law_ok (x : X3) :
  `Pr[ input_rv = x ] != 0 ->
  forall y, `Pr[ shares_rv = y | input_rv = x ] = functionality x y.
Proof.
move=> _ [[s t] u]; rewrite cpr_eqE pfwd1_input invrK pfwd1_cardE.
rewrite /functionality fdistmapE.
have -> : finset ([% shares_rv, input_rv] @^-1 (((s, t), u), x))
        = if u == f_sum x - s - t then [set (x, (s, t))] else set0.
  apply/setP => -[x' [s' t']].
  rewrite !inE !xpair_eqE /shares_rv /input_rv /y1_rv /y2_rv /y3_rv /=.
  case: (eqVneq x' x) => [->|xne]/=; last first.
    by rewrite andbF; case: ifP => _; rewrite !inE ?xpair_eqE ?(negbTE xne)//.
  rewrite andbT; case: (eqVneq s' s) => [->|sne]/=; last first.
    by case: ifP => _; rewrite !inE ?xpair_eqE ?(negbTE sne) ?andbF//.
  case: (eqVneq t' t) => [->|tne]/=; last first.
    by case: ifP => _; rewrite !inE ?xpair_eqE ?(negbTE tne) ?andbF//.
  by rewrite eq_sym; case: ifP => _; rewrite !inE ?xpair_eqE ?eqxx//.
case: (eqVneq u (f_sum x - s - t)) => [->|une]/=; last first.
  rewrite cards0 !mul0r; apply/esym/big_pred0 => -[w1 w2].
  rewrite !inE /share_map !xpair_eqE /=; apply/negbTE.
  by apply: contra une => /andP[/andP[/eqP-> /eqP->] h]; rewrite eq_sym.
rewrite cards1 (big_pred1 (s, t)); last first.
  move=> -[w1 w2]; rewrite !inE /share_map !xpair_eqE /=.
  by case: (eqVneq w1 s) => [->|?]//=; case: (eqVneq w2 t) => [->|?]//=;
    rewrite eqxx.
by rewrite mul1r mulrC /P_Omega tensorE /unif2 !fdist_uniformE card_F2
  -invfM -natrM; apply: count_mass.
Qed.

(* The view and the honest shares are conditionally dependent given the
   conditioner. *)
Lemma not_cinde_honest : ~ (exec_law |= view_rv _|_ honest_rv | cond_rv).
Proof.
move=> h; have := h ((0, 0), 0) (0, 0) (x0, 0); rewrite !cpr_eqE pfwd1_cond.
rewrite (pfwd1_cardE [% view_rv, honest_rv, cond_rv]) card_vh_cond.
rewrite (pfwd1_cardE [% view_rv, cond_rv]) card_v_cond.
by rewrite (pfwd1_cardE [% honest_rv, cond_rv]) card_h_cond => h1; lra.
Qed.

(* def:smc:output-independence *)
(* The view and the conditioner together determine the honest shares, so the
   conditional entropy of the honest shares given both vanishes. *)
Lemma centropy_view_honest0 :
  `H( honest_rv | [% view_rv, cond_rv] ) = 0.
Proof.
exact: (centropy_RV_comp0 [% view_rv, cond_rv]
  (fun p => (p.1.2, f_sum p.2.1 - p.2.2 - p.1.2))).
Qed.

(* The recoding sends the conditioner and the share of party two to the
   conditioner and the honest shares. *)
Definition recode (p : (X3 * F2) * F2) : (X3 * F2) * (F2 * F2) :=
  (p.1, (p.2, f_sum p.1.1 - p.1.2 - p.2)).

(* The recoding is injective. *)
Lemma recode_inj : injective recode.
Proof. by move=> [c t] [c' t'] [-> -> _]. Qed.

(* The joint law of the conditioner and the honest shares is the transport
   along the recoding of the joint law of the conditioner and the share of
   party two.
   Naming: joint_<variables>_<map> is intentional, the variables-first order
   of this file, naming the joint law before the map that carries it. *)
Lemma joint_cond_honest_recode :
  `p_ [% cond_rv, honest_rv] = fdistmap recode (`p_ [% cond_rv, y2_rv]).
Proof.
by rewrite /dist_of_RV fdistmap_comp.
Qed.

(* The law of the share delivered to party two is uniform. *)
Lemma y2_lawE : `p_ y2_rv = unif2.
Proof.
by apply/fdist_ext => t; rewrite dist_of_RVE pfwd1_y2 fdist_uniformE card_F2.
Qed.

(* The share delivered to party two and the conditioner are independent. *)
Lemma joint_y2_cond :
  `p_ [% y2_rv, cond_rv] = (`p_ y2_rv `x `p_ cond_rv)%fdist.
Proof.
apply/fdist_ext => -[t [x s]]; rewrite fdist_prodE !dist_of_RVE pfwd1_y2_cond.
by rewrite pfwd1_y2 pfwd1_cond -invfM -natrM.
Qed.

(* Given the conditioner the share delivered to party two has conditional
   entropy log 2. *)
Lemma centropy_y2_cond : `H( y2_rv | cond_rv ) = log 2%:R :> R.
Proof.
have Hprod : `p_ [% y2_rv, cond_rv]
  = ((`p_ [% y2_rv, cond_rv])`1 `x (`p_ [% y2_rv, cond_rv])`2)%fdist.
  by rewrite fst_RV2 snd_RV2 joint_y2_cond.
rewrite /centropy_RV (centropy_indep Hprod) fst_RV2 y2_lawE.
by rewrite entropy_uniform card_F2.
Qed.

(* def:smc:output-independence *)
(* Given the conditioner alone the honest shares have conditional entropy
   log 2.
   Naming: centropy_<conditioned>_<conditioner> is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_honest_cond : `H( honest_rv | cond_rv ) = log 2%:R :> R.
Proof.
have hjoint : `H(cond_rv, honest_rv) = `H(cond_rv, y2_rv).
  rewrite /joint_entropy_RV /joint_entropy joint_cond_honest_recode.
  by rewrite (entropy_fdistmap _ recode_inj).
move: (chain_rule_RV cond_rv honest_rv); rewrite hjoint.
by rewrite (chain_rule_RV cond_rv y2_rv) => /addrI <-; exact: centropy_y2_cond.
Qed.

(* def:smc:output-independence *)
(* The conditional entropy of the honest shares given the conditioner changes
   when the view joins the conditioning.
   Naming: centropy_<conditioner joined>_<conditioned>_neq is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_view_honest_neq :
  `H( honest_rv | [% view_rv, cond_rv] ) <> `H( honest_rv | cond_rv ).
Proof.
rewrite centropy_view_honest0 centropy_honest_cond log2.
by move/eqP; rewrite eq_sym oner_eq0.
Qed.

(* The adversary's part of an input. *)
Let proj_xa (x : X3) : F2 := x.1.1.

(* The honest parties' part of an input. *)
Let proj_xh (x : X3) : (F2 * F2)%type := (x.1.2, x.2).

(* The adversary's part of the delivered shares. *)
Let proj_ya (s : (F2 * F2) * F2) : F2 := s.1.1.

(* The honest parties' part of the delivered shares. *)
Let proj_yh (s : (F2 * F2) * F2) : (F2 * F2)%type := (s.1.2, s.2).

(* The run of an execution delivers the three shares. *)
Let run (e : X3 * (F2 * F2)%type) : (F2 * F2) * F2 := share_map e.1 e.2.

(* The view at an execution. *)
Let view_at (e : X3 * (F2 * F2)%type) : (F2 * F2) * F2 :=
  ((e.1.1.1, e.2.1), e.2.2).

(* The adversary's delivered share read off a view. *)
Let out_adv (v : (F2 * F2) * F2) : F2 := v.1.2.

(* The aggregation of the run recovers the function at every execution.
   Naming: _correct marks agreement with the specified function, the
   file's convention for specification-conformance statements. *)
Lemma run_correct (e : X3 * (F2 * F2)%type) : agg (run e) = f_sum e.1.
Proof.
by case: e => x [w1 w2]; rewrite /agg /run /share_map/= addrCA addrK subrK.
Qed.

(* Every ancilla has mass one quarter. *)
Let P_OmegaE (w : F2 * F2) : P_Omega w = 4%:R^-1.
Proof.
by case: w => w1 w2; rewrite /P_Omega tensorE /unif2 !fdist_uniformE card_F2
  -invfM -natrM.
Qed.

(* The view kernel at an input is the ancilla law on the two shares the
   adversary sees, at its own bit. *)
Lemma view_kernelE (c a s t : F2) :
  fdistmap (fun w : F2 * F2 => ((c, w.1), w.2)) P_Omega ((a, s), t)
  = (c == a)%:R * 4%:R^-1.
Proof.
rewrite fdistmapE; case: (eqVneq c a) => [->|cne]/=; last first.
  rewrite mul0r; apply: big_pred0 => -[w1 w2].
  by rewrite !inE !xpair_eqE/= (negbTE cne).
rewrite mul1r (big_pred1 (s, t)); first exact: P_OmegaE.
by move=> -[w1 w2]; rewrite !inE !xpair_eqE/= eqxx.
Qed.

(* The allowed-information kernel at an input is the uniform law on the
   adversary's share, at its own bit. *)
Lemma allow_kernelE (c a s : F2) :
  fdistmap (fun w : F2 * F2 => (c, w.1)) P_Omega (a, s) = (c == a)%:R * 2%:R^-1.
Proof.
have -> : fdistmap (fun w : F2 * F2 => (c, w.1)) P_Omega
        = tensor (fdist1 c) unif2.
  have <- : P_Omega`1 = unif2 by rewrite /P_Omega /tensor fdist_prod1.
  by rewrite tensor_fdist1 /fdist_fst fdistmap_comp.
by rewrite tensorE fdist1E eq_sym /unif2 fdist_uniformE card_F2.
Qed.

(* def:smc:perfect-privacy *)
(* The view law at an input is the allowed-information law of that input bound
   through the simulator.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma triangle_holds :
  triangle proj_xa proj_ya functionality P_Omega view_at sim.
Proof.
move=> x; apply/fdist_ext => -[[a s] t].
have -> : fdistmap (fun yl => (proj_xa x, proj_ya yl)) (functionality x)
        = fdistmap (fun w : F2 * F2 => (proj_xa x, w.1)) P_Omega.
  by rewrite /functionality fdistmap_comp; apply: eq_fdistmap.
rewrite [LHS]view_kernelE fdistbindE (bigD1 (a, s))//= big1 ?addr0; last first.
  by move=> b bne; rewrite /sim tensorE fdist1E eq_sym (negbTE bne) mul0r mulr0.
rewrite allow_kernelE /sim tensorE fdist1E eqxx mul1r.
by rewrite /unif2 fdist_uniformE card_F2 -mulrA -invfM -natrM.
Qed.

(* The simulator achieves perfect privacy.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma perfect_privacy_holds :
  perfect_privacy proj_xa proj_ya functionality P_Omega view_at sim.
Proof. exact/triangle_perfect_privacyP/triangle_holds. Qed.

(* The execution at the all-zero input and the ancilla with a one in the
   second slot. *)
Let pt1 : X3 * (F2 * F2)%type := (x0, (0, 1)).

(* Two executions sharing an input and an adversary share deliver different
   honest shares. *)
Let yh_differs : proj_yh (run pt0) <> proj_yh (run pt1).
Proof.
rewrite /proj_yh /run /share_map /pt0 /pt1 /=; apply/eqP.
by rewrite xpair_eqE eq_sym oner_eq0.
Qed.

(* No function of the input alone gives the honest shares at every execution of
   positive mass. *)
Lemma not_output_det :
  ~ (exists g : X3 -> (F2 * F2)%type,
       forall e, exec_law e != 0 -> proj_yh (run e) = g e.1).
Proof.
by case=> g hg; apply: yh_differs;
   rewrite (hg pt0 (exec_law_neq0 _)) (hg pt1 (exec_law_neq0 _)).
Qed.

(* No function of the input and the adversary's delivered share gives the
   honest shares at every execution of positive mass. *)
Lemma not_output_determined :
  ~ (exists g : X3 -> F2 -> (F2 * F2)%type,
       forall e, exec_law e != 0 ->
         proj_yh (run e) = g e.1 (proj_ya (run e))).
Proof.
by case=> g hg; apply: yh_differs;
   rewrite (hg pt0 (exec_law_neq0 _)) (hg pt1 (exec_law_neq0 _)).
Qed.

(* The output read off the view of an execution is the adversary's delivered
   share. *)
Let readoff (e : X3 * (F2 * F2)%type) : out_adv (view_at e) = proj_ya (run e).
Proof. by []. Qed.

(* The prior has full support. *)
Let mu_full (x : X3) : mu x != 0.
Proof. by rewrite fdist_uniformE card_X3 invr_eq0 pnatr_eq0. Qed.

(* The split of an input into the adversary's and the honest parties' parts is
   injective. *)
Let split_inj : injective (fun x => (proj_xa x, proj_xh x)).
Proof.
by move=> [[a b] c] [[a' b'] c']; rewrite /proj_xa /proj_xh /= => -[-> -> ->].
Qed.

(* The honest parties' part of the input. *)
Let xh_rv : {RV exec_law -> (F2 * F2)%type} := proj_xh \o fst.

(* The honest parties' part of the delivered shares. *)
Let yh_rv : {RV exec_law -> (F2 * F2)%type} := fun e => proj_yh (run e).

(* The adversary's part of the input. *)
Let xa_rv : {RV exec_law -> F2} := proj_xa \o fst.

(* The adversary's part of the delivered shares. *)
Let ya_rv : {RV exec_law -> F2} := fun e => proj_ya (run e).

(* The adversary's view. *)
Let v_rv : {RV exec_law -> ((F2 * F2) * F2)%type} := view_at.

(* eq:smc:entropy *)
(* The conditional entropy of the honest parties' inputs and delivered shares
   given the adversary's own changes when the view joins the conditioning.
   Naming: chapter names the thesis equality eq:smc:entropy whose two sides
   this lemma separates; the conditioned pair and the conditioner follow
   that statement rather than the file's variable convention. *)
Lemma centropy_chapter_neq :
  `H( [% xh_rv, yh_rv] | [% v_rv, [% xa_rv, ya_rv]] )
  <> `H( [% xh_rv, yh_rv] | [% xa_rv, ya_rv] ).
Proof.
move=> heq.
have [Sim [_ _ hoi]] :=
  centropy_to_sim readoff mu_full split_inj (fun=> erefl) heq.
exact: not_cinde_honest hoi.
Qed.

End instance.
End share_leak.
