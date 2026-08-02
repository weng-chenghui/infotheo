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
(* A three-axes family over the two-element field shares the sum of three     *)
(* private bits among three parties and delivers a shared key to the two      *)
(* honest parties: party one deals the key, party two deals a key biased to   *)
(* three quarters, and party two deals a uniform key.  Output independence    *)
(* fails at the first, delivery-law correctness at the second, every check    *)
(* holds at the third, and the view-marginal triangle fails at the no-mask    *)
(* instance above, so the four instances witness one axis each of Lindell's   *)
(* joint comparison.                                                          *)
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
(*         dealt_key_leak == adversary deals the honest parties' shared key;  *)
(*                           only output independence fails                   *)
(*             biased_key == honest dealer, biased key; only delivery-law     *)
(*                           correctness fails                                *)
(*           rerouted_key == honest dealer, uniform key; every check holds    *)
(*                           (the table's secure baseline)                    *)
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

(* The prior on the input space is uniform.
   Naming: prior is intentional, the thesis notation for the law the execution
   context draws the input from. *)
Definition prior : R.-fdist 'F_3 := unif3.

(* With a one-point ancilla the run delivers the one-point output. *)
Definition plain_deliver (e : 'F_3 * 'I_1) : 'I_1 := ord0.

(* The run of the execution context with a one-point ancilla computes the
   outcome.
   Naming: _correct marks agreement with the specified function, the
   file's convention for specification-conformance statements. *)
Lemma run_correct_no_mask (e : 'F_3 * 'I_1) :
  id (plain_deliver e) = outcome e.1.
Proof. by []. Qed.

(* The real delivered outputs have the law the ideal functionality prescribes
   at every input.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma delivery_law_holds_no_mask :
  delivery_law_ok functionality no_mask plain_deliver.
Proof. by move=> x; apply: eq_fdistmap_cst => w /=. Qed.

(* The view and the honest delivered output are conditionally independent
   given the input and the adversary's delivered output.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma output_independent_holds_no_mask :
  output_independent id id no_mask plain_view plain_deliver prior.
Proof.
by apply: (@output_independent_det R _ _ _ _ _ _ id id _
  plain_view plain_deliver prior (fun=> ord0)) => e _.
Qed.

(* The real joint law of the view and the delivered outputs at an input.
   This is the right-hand side of Lindell's joint comparison. *)
Definition real_pair (x : 'F_3) : R.-fdist ('F_3 * 'I_1)%type :=
  fdistmap (fun w : 'I_1 => (plain_view (x, w), plain_deliver (x, w))) no_mask.

(* The view a simulator produces coupled with the functionality draw it was
   handed. *)
Definition ideal_pair_of (S : simulator (R := R) 'I_1 'I_1 'F_3) (x : 'F_3)
    : R.-fdist ('F_3 * 'I_1)%type :=
  functionality x >>= (fun y => tensor (S (proj_adv_input x, id y)) (fdist1 y)).

(* The view marginal of the real pair is the point mass at the input. *)
Lemma fst_marginal_real_pairE (x : 'F_3) :
  fdistmap fst (real_pair x) = fdist1 x.
Proof. by rewrite /real_pair fdistmap_comp; apply: eq_fdistmap_cst => w /=. Qed.

(* The view marginal of the ideal pair is the simulator at the one-point
   allowed information. *)
Lemma fst_marginal_ideal_pairE (S : simulator (R := R) 'I_1 'I_1 'F_3)
    (x : 'F_3) : fdistmap fst (ideal_pair_of S x) = S (ord0, ord0).
Proof.
rewrite /ideal_pair_of /functionality fdist1bind.
by rewrite tensor_fdist1r fdistmap_comp -[RHS]fdistmap_id; apply: eq_fdistmap.
Qed.

(* The simulated view law is the simulator at the one-point allowed
   information, at every input. *)
Lemma sim_view_constE (S : simulator (R := R) 'I_1 'I_1 'F_3) (x : 'F_3) :
  sim_view proj_adv_input id functionality S x = S (ord0, ord0).
Proof.
by rewrite /sim_view allowE /f_a /functionality tensor_fdist1 !fdistmap1
   fdist1bind.
Qed.

(* No simulator makes the ideal pair the real pair at every input.
   Naming: not_ marks the negation of the existential the statement refutes,
   and _no_mask the ancilla law this module names its verdicts after. *)
Lemma not_exists_ideal_pair_no_mask :
  ~ (exists S : simulator (R := R) 'I_1 'I_1 'F_3,
       forall x, real_pair x = ideal_pair_of S x).
Proof.
case=> S hS; apply: insecurity_no_mask; exists S => x.
rewrite view_law_plainE sim_view_constE.
by rewrite -fst_marginal_real_pairE -(fst_marginal_ideal_pairE S x) (hS x).
Qed.

(* At a single input a simulator does make the ideal pair the real pair, so
   the input quantifier of not_exists_ideal_pair_no_mask is load-bearing.
   Naming: _at_one_input spells the quantifier this statement weakens
   not_exists_ideal_pair_no_mask to, ahead of the _no_mask ancilla suffix. *)
Lemma exists_ideal_pair_at_one_input_no_mask (x : 'F_3) :
  exists S : simulator (R := R) 'I_1 'I_1 'F_3,
    real_pair x = ideal_pair_of S x.
Proof.
exists (fun=> fdist1 x); rewrite /real_pair /ideal_pair_of.
rewrite /no_mask /functionality.
by rewrite fdistmap1 fdist1bind tensor_fdist1 fdistmap1.
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

(* Three parties additively share the sum of three private bits over the
   two-element field and the two honest parties are delivered a shared key
   that party one, the adversary, samples and deals to both.  The
   compatibility square, the delivery law and an output-consistent privacy
   triangle hold, while the view and the honest outputs are conditionally
   dependent given the input and the adversary's share, and the conditional
   entropy of the honest outputs drops from log 4 to log 2 once the view joins
   the conditioning.  The ideal functionality is the transport of the uniform
   coins along the delivery map, so the delivered joint law is the prescribed
   one and the coupling of the view with the outputs is the single component
   of Lindell's joint comparison that fails. *)
Module dealt_key_leak.
Section instance.
Context {R : realType}.

(* The two-element field. *)
Let F2 : finType := 'F_2.

(* The two-element field has two points. *)
Lemma card_F2 : #|F2| = 2.
Proof. by rewrite card_ord. Qed.

(* The uniform law on the two-element field. *)
Definition unif2 : R.-fdist F2 := fdist_uniform card_F2.

(* A pair of bits has four values. *)
Let card_F2F2 : #|((F2 * F2)%type : finType)| = 4.
Proof. by rewrite card_prod !card_F2. Qed.

(* The uniform law on pairs of bits. *)
Definition unif4 : R.-fdist (F2 * F2)%type := fdist_uniform card_F2F2.

(* The input space gives one private bit to each of the three parties. *)
Let X3 := (F2 * F2 * F2)%type.

(* The input space has eight points. *)
Lemma card_X3 : #|(X3 : finType)| = 8.
Proof. by rewrite !card_prod !card_F2. Qed.

(* The prior on the input space is uniform.
   Naming: mu is intentional, the thesis notation $\mu$ for the prior on the
   input space. *)
Definition mu : R.-fdist X3 := fdist_uniform card_X3.

(* A coin triple carries the two free shares and the key. *)
Let Om := ((F2 * F2) * F2)%type.

(* The coins draw the two free shares and the key as independent uniform
   bits. *)
Definition P_Omega : R.-fdist Om := tensor (tensor unif2 unif2) unif2.

(* The execution context pairs an input with the coins. *)
Definition exec_law : R.-fdist (X3 * Om)%type := tensor mu P_Omega.

(* The function the protocol computes is the sum of the three private
   bits. *)
Definition f_sum (x : X3) : F2 := x.1.1 + x.1.2 + x.2.

(* The delivered outputs are the share of party one, the share of party two
   with the key, and the share of party three with the same key. *)
Let Yfull := ((F2 * (F2 * F2)) * (F2 * F2))%type.

(* The delivery map sends an input and coins to the three shares and the two
   copies of the key. *)
Definition deliver (x : X3) (w : Om) : Yfull :=
  ((w.1.1, (w.1.2, w.2)), (f_sum x - w.1.1 - w.1.2, w.2)).

(* The ideal functionality at an input is the transport of the uniform coins
   along the delivery map. *)
Definition functionality (x : X3) : R.-fdist Yfull :=
  fdistmap (deliver x) P_Omega.

(* The aggregation of the delivered outputs is the sum of the three shares. *)
Definition agg (s : Yfull) : F2 := s.1.1 + s.1.2.1 + s.2.1.

(* Every execution has mass one over sixty-four. *)
Lemma exec_lawE u : exec_law u = 64%:R^-1.
Proof.
case: u => x [[s t] r]; rewrite /exec_law /P_Omega !tensorE !fdist_uniformE.
by rewrite card_X3 card_F2 -!invfM -!natrM.
Qed.

(* The input of the execution. *)
Definition input_rv : {RV exec_law -> X3} := fst.

(* The private bit of the adversary, party one. *)
Definition adv_input_rv : {RV exec_law -> F2} := fun e => e.1.1.1.

(* The share delivered to the adversary. *)
Definition y1_rv : {RV exec_law -> F2} := fun e => e.2.1.1.

(* The share delivered to party two. *)
Definition y2_rv : {RV exec_law -> F2} := fun e => e.2.1.2.

(* The key delivered to both honest parties. *)
Definition key_rv : {RV exec_law -> F2} := fun e => e.2.2.

(* The share delivered to party three completes the sum. *)
Definition y3_rv : {RV exec_law -> F2} :=
  fun e => f_sum e.1 - e.2.1.1 - e.2.1.2.

(* The output delivered to party two is its share together with the key. *)
Definition party2_out_rv := [% y2_rv, key_rv].

(* The adversary observes its own bit, its own share and the key it deals. *)
Definition view_rv := [% [% adv_input_rv, y1_rv], key_rv].

(* The outputs delivered to the two honest parties. *)
Definition honest_rv := [% [% y2_rv, key_rv], [% y3_rv, key_rv]].

(* The allowed information is the adversary's bit and its delivered share. *)
Definition allow_rv := [% adv_input_rv, y1_rv].

(* The conditioner is the input and the adversary's delivered share. *)
Definition cond_rv := [% input_rv, y1_rv].

(* The conditioner extended by the key. *)
Definition cond_key_rv := [% cond_rv, key_rv].

(* The delivered outputs of the execution. *)
Definition outputs_rv : {RV exec_law -> Yfull} := fun e => deliver e.1 e.2.

(* The simulator answers the allowed information together with a fresh
   uniform key slot. *)
Definition sim : simulator (R := R) F2 F2 ((F2 * F2) * F2)%type :=
  fun a => tensor (fdist1 a) unif2.

(* Every execution has positive mass. *)
Let exec_law_neq0 (e : X3 * Om) : exec_law e != 0.
Proof. by rewrite exec_lawE invr_eq0 pnatr_eq0. Qed.

(* The probability of a value of a variable is the cardinality of the
   preimage of that value over sixty-four. *)
Lemma pfwd1_cardE (T' : finType) (Z : {RV exec_law -> T'}) (z : T') :
  `Pr[ Z = z ] = #|finset (Z @^-1 z)|%:R * 64%:R^-1.
Proof.
rewrite pfwd1E /Pr; under eq_bigr do rewrite exec_lawE.
by rewrite big_const iter_addr addr0 mulr_natl.
Qed.

(* A set of n points out of sixty-four has mass k^-1 when n times k is
   sixty-four. *)
Let count_mass (n k : nat) : (n * k)%N = 64%N -> n != 0%N ->
  n%:R * 64%:R^-1 = (k%:R^-1 : R).
Proof.
by move=> <- n0; rewrite natrM invfM mulrA mulfV ?pnatr_eq0// mul1r.
Qed.

(* The conditioner has four preimage points at every value. *)
Lemma card_preim_cond (x : X3) (s : F2) :
  #|finset (cond_rv @^-1 (x, s))| = 4.
Proof.
have -> : finset (cond_rv @^-1 (x, s))
        = setX [set x] (setX (setX [set s] [set: F2]) [set: F2]).
  apply/setP => -[x' [[w1 w2] r]].
  by rewrite !inE !xpair_eqE /cond_rv /input_rv /y1_rv /= !andbT.
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The view has eight preimage points at every value. *)
Lemma card_preim_view (v : (F2 * F2) * F2) :
  #|finset (view_rv @^-1 v)| = 8.
Proof.
case: v => -[a s] r.
have -> : finset (view_rv @^-1 ((a, s), r))
        = setX (setX (setX [set a] [set: F2]) [set: F2])
               (setX (setX [set s] [set: F2]) [set r]).
  apply/setP => -[[[x1 x2] x3] [[w1 w2] r']].
  rewrite !inE !xpair_eqE /view_rv /adv_input_rv /y1_rv /key_rv /=.
  by rewrite !andbT andbA.
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The allowed information has sixteen preimage points at every value. *)
Lemma card_preim_allow (a s : F2) :
  #|finset (allow_rv @^-1 (a, s))| = 16.
Proof.
have -> : finset (allow_rv @^-1 (a, s))
        = setX (setX (setX [set a] [set: F2]) [set: F2])
               (setX (setX [set s] [set: F2]) [set: F2]).
  apply/setP => -[[[x1 x2] x3] [[w1 w2] r']].
  by rewrite !inE !xpair_eqE /allow_rv /adv_input_rv /y1_rv /= !andbT.
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The input has eight preimage points at every value. *)
Lemma card_preim_input (x : X3) :
  #|finset (input_rv @^-1 x)| = 8.
Proof.
have -> : finset (input_rv @^-1 x) = setX [set x] [set: Om].
  by apply/setP => -[x' w]; rewrite !inE /input_rv /= andbT.
by rewrite cardsX cards1 !cardsT !card_prod !card_F2.
Qed.

(* The share delivered to party two has thirty-two preimage points at every
   value. *)
Lemma card_preim_y2 (t : F2) : #|finset (y2_rv @^-1 t)| = 32.
Proof.
have -> : finset (y2_rv @^-1 t)
        = setX [set: X3] (setX (setX [set: F2] [set t]) [set: F2]).
  by apply/setP => -[x [[w1 w2] r]]; rewrite !inE /y2_rv /= !andbT.
by rewrite !cardsX cards1 !cardsT card_X3 !card_F2.
Qed.

(* The output delivered to party two has sixteen preimage points at every
   value. *)
Lemma card_preim_party2_out (t r : F2) :
  #|finset (party2_out_rv @^-1 (t, r))| = 16.
Proof.
have -> : finset (party2_out_rv @^-1 (t, r))
        = setX [set: X3] (setX (setX [set: F2] [set t]) [set r]).
  apply/setP => -[x [[w1 w2] r']].
  by rewrite !inE !xpair_eqE /party2_out_rv /y2_rv /key_rv /=.
by rewrite !cardsX !cards1 !cardsT card_X3 !card_F2.
Qed.

(* The extended conditioner has two preimage points at every value. *)
Lemma card_preim_cond_key (x : X3) (s r : F2) :
  #|finset (cond_key_rv @^-1 ((x, s), r))| = 2.
Proof.
have -> : finset (cond_key_rv @^-1 ((x, s), r))
        = setX [set x] (setX (setX [set s] [set: F2]) [set r]).
  apply/setP => -[x' [[w1 w2] r']].
  rewrite !inE !xpair_eqE /cond_key_rv /cond_rv /input_rv /y1_rv /key_rv /=.
  by rewrite andbT andbA.
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The output delivered to party two and the conditioner have one preimage
   point at every joint value.
   Naming: card_preim_<variables> is intentional, the convention of this file
   naming a preimage count after the variables it counts the fibre of. *)
Lemma card_preim_party2_out_cond (t r : F2) (x : X3) (s : F2) :
  #|finset ([% party2_out_rv, cond_rv] @^-1 ((t, r), (x, s)))| = 1.
Proof.
have -> : finset ([% party2_out_rv, cond_rv] @^-1 ((t, r), (x, s)))
        = [set (x, ((s, t), r))].
  apply/setP => -[x' [[w1 w2] r']].
  rewrite !inE !xpair_eqE /party2_out_rv /y2_rv /key_rv /cond_rv /input_rv
          /y1_rv /=.
  by case: (x' == x); case: (w1 == s); case: (w2 == t); case: (r' == r).
by rewrite cards1.
Qed.

(* The share of party two and the extended conditioner have one preimage
   point at every joint value.
   Naming: card_preim_<variables> is intentional, the convention of this file
   naming a preimage count after the variables it counts the fibre of. *)
Lemma card_preim_y2_cond_key (t : F2) (x : X3) (s r : F2) :
  #|finset ([% y2_rv, cond_key_rv] @^-1 (t, ((x, s), r)))| = 1.
Proof.
have -> : finset ([% y2_rv, cond_key_rv] @^-1 (t, ((x, s), r)))
        = [set (x, ((s, t), r))].
  apply/setP => -[x' [[w1 w2] r']].
  rewrite !inE !xpair_eqE /y2_rv /cond_key_rv /cond_rv /input_rv /y1_rv
          /key_rv /=.
  by case: (x' == x); case: (w1 == s); case: (w2 == t); case: (r' == r).
by rewrite cards1.
Qed.

(* The share of party two and the view have four preimage points at every
   joint value. *)
Lemma card_preim_y2_view (t : F2) (v : (F2 * F2) * F2) :
  #|finset ([% y2_rv, view_rv] @^-1 (t, v))| = 4.
Proof.
case: v => -[a s] r.
have -> : finset ([% y2_rv, view_rv] @^-1 (t, ((a, s), r)))
        = setX (setX (setX [set a] [set: F2]) [set: F2])
               (setX (setX [set s] [set t]) [set r]).
  apply/setP => -[[[x1 x2] x3] [[w1 w2] r']].
  rewrite !inE !xpair_eqE /y2_rv /view_rv /adv_input_rv /y1_rv /key_rv /=.
  by case: (x1 == a); case: (w1 == s); case: (w2 == t); case: (r' == r).
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The conditioner takes each value with probability one over sixteen. *)
Lemma pfwd1_cond (x : X3) (s : F2) : `Pr[ cond_rv = (x, s) ] = 16%:R^-1.
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

(* The output delivered to party two takes each value with probability one
   quarter. *)
Lemma pfwd1_party2_out (t r : F2) :
  `Pr[ party2_out_rv = (t, r) ] = 4%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_party2_out; apply: count_mass. Qed.

(* The extended conditioner takes each value with probability one over
   thirty-two. *)
Lemma pfwd1_cond_key (x : X3) (s r : F2) :
  `Pr[ cond_key_rv = ((x, s), r) ] = 32%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_cond_key; apply: count_mass. Qed.

(* The output delivered to party two and the conditioner take each joint
   value with probability one over sixty-four. *)
Lemma pfwd1_party2_out_cond (t r : F2) (x : X3) (s : F2) :
  `Pr[ [% party2_out_rv, cond_rv] = ((t, r), (x, s)) ] = 64%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_party2_out_cond mul1r. Qed.

(* The share of party two and the extended conditioner take each joint value
   with probability one over sixty-four. *)
Lemma pfwd1_y2_cond_key (t : F2) (x : X3) (s r : F2) :
  `Pr[ [% y2_rv, cond_key_rv] = (t, ((x, s), r)) ] = 64%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_y2_cond_key mul1r. Qed.

(* The share of party two and the view take each joint value with probability
   one over sixteen. *)
Lemma pfwd1_y2_view (t : F2) (v : (F2 * F2) * F2) :
  `Pr[ [% y2_rv, view_rv] = (t, v) ] = 16%:R^-1.
Proof. by rewrite pfwd1_cardE card_preim_y2_view; apply: count_mass. Qed.

(* Given the view the share delivered to party two is still uniform.
   Naming: cpr_ names the conditional probability the statement evaluates,
   the vocabulary of cpr_eq of proba.v, and _unif the law that value is the
   mass of. *)
Lemma cpr_y2_view_unif (t : F2) (v : (F2 * F2) * F2) :
  `Pr[ y2_rv = t | view_rv = v ] = 2%:R^-1.
Proof. by rewrite cpr_eqE pfwd1_y2_view pfwd1_view invrK; lra. Qed.

(* The all-zero input. *)
Let x0 : X3 := (0, 0, 0).

(* The execution at the all-zero input and the all-zero coins. *)
Let pt0 : X3 * Om := (x0, ((0, 0), 0)).

(* The sum of the all-zero input is zero. *)
Let f_sum_x0 : f_sum x0 = 0.
Proof. by rewrite /f_sum /= !addr0. Qed.

(* The view, the honest outputs and the conditioner have one preimage point
   at the all-zero joint value. *)
Let card_vh_cond :
  #|finset ([% [% view_rv, honest_rv], cond_rv]
       @^-1 ((((0, 0), 0), ((0, 0), (0, 0))), (x0, 0)))| = 1.
Proof.
have -> : finset ([% [% view_rv, honest_rv], cond_rv]
       @^-1 ((((0, 0), 0), ((0, 0), (0, 0))), (x0, 0))) = [set pt0].
  apply/setP => -[x' [[w1 w2] r]].
  rewrite !inE !xpair_eqE /view_rv /honest_rv /cond_rv /adv_input_rv
          /y1_rv /y2_rv /y3_rv /key_rv /input_rv /=.
  case: (eqVneq x' x0) => [->|xne]/=; last by rewrite !andbF.
  rewrite f_sum_x0.
  by case: (eqVneq w1 0) => [->|?]//=; case: (eqVneq w2 0) => [->|?]//=;
     rewrite ?subr0 ?eqxx/=; case: (r == 0).
by rewrite cards1.
Qed.

(* The view and the conditioner have two preimage points at the all-zero
   joint value. *)
Let card_v_cond :
  #|finset ([% view_rv, cond_rv] @^-1 (((0, 0), 0), (x0, 0)))| = 2.
Proof.
have -> : finset ([% view_rv, cond_rv] @^-1 (((0, 0), 0), (x0, 0)))
        = setX [set x0] (setX (setX [set 0] [set: F2]) [set 0]).
  apply/setP => -[x' [[w1 w2] r]].
  rewrite !inE !xpair_eqE /view_rv /cond_rv /adv_input_rv /y1_rv /key_rv
          /input_rv /=.
  case: (eqVneq x' x0) => [->|xne]/=; last by rewrite !andbF.
  by rewrite andbT andbAC andbb.
by rewrite !cardsX !cards1 !cardsT !card_F2.
Qed.

(* The honest outputs and the conditioner have one preimage point at the
   all-zero joint value. *)
Let card_h_cond :
  #|finset ([% honest_rv, cond_rv] @^-1 (((0, 0), (0, 0)), (x0, 0)))| = 1.
Proof.
have -> : finset ([% honest_rv, cond_rv] @^-1 (((0, 0), (0, 0)), (x0, 0)))
        = [set pt0].
  apply/setP => -[x' [[w1 w2] r]].
  rewrite !inE !xpair_eqE /honest_rv /cond_rv /y2_rv /y3_rv /y1_rv /key_rv
          /input_rv /=.
  case: (eqVneq x' x0) => [->|xne]/=; last by rewrite !andbF.
  rewrite f_sum_x0 andbC.
  by case: (eqVneq w1 0) => [->|?]//=; case: (eqVneq w2 0) => [->|?]//=;
     rewrite ?subr0 ?eqxx/=; case: (r == 0).
by rewrite cards1.
Qed.

(* def:smc:output-independence *)
(* The view and the honest outputs are conditionally dependent given the
   conditioner. *)
Lemma not_cinde_honest : ~ (exec_law |= view_rv _|_ honest_rv | cond_rv).
Proof.
move=> h; have := h ((0, 0), 0) ((0, 0), (0, 0)) (x0, 0).
rewrite !cpr_eqE pfwd1_cond.
rewrite (pfwd1_cardE [% [% view_rv, honest_rv], cond_rv]) card_vh_cond.
rewrite (pfwd1_cardE [% view_rv, cond_rv]) card_v_cond.
by rewrite (pfwd1_cardE [% honest_rv, cond_rv]) card_h_cond => h1; lra.
Qed.

(* eq:smc:functionality-compat *)
(* The aggregation of the ideal functionality is the point mass at the value
   of the function. *)
Lemma functionality_compat (x : X3) :
  fdistmap agg (functionality x) = fdist1 (f_sum x).
Proof.
rewrite /functionality fdistmap_comp; apply: eq_fdistmap_cst => w /=.
by rewrite /agg /deliver /= addrCA addrK subrK.
Qed.

(* The output read off a simulated view is the point mass at the delivered
   share the simulator was handed. *)
Lemma sim_consistent (a : F2 * F2) :
  fdistmap (fun v : (F2 * F2) * F2 => v.1.2) (sim a) = fdist1 a.2.
Proof. by rewrite /sim tensor_fdist1 fdistmap_comp; apply: eq_fdistmap_cst. Qed.

(* The joint law of the input and the delivered outputs is the prior times the
   ideal functionality. *)
Lemma pfwd1_input_outputs (x : X3) (y : Yfull) :
  `Pr[ [% input_rv, outputs_rv] = (x, y) ] = mu x * functionality x y.
Proof. exact: (pfwd1_input_pair P_Omega mu outputs_rv x y). Qed.

(* The real delivered outputs have the law the ideal functionality prescribes
   at every input.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma delivery_law_holds :
  delivery_law_ok functionality P_Omega (fun e : X3 * Om => deliver e.1 e.2).
Proof. by []. Qed.

(* On every positive-mass input the delivered outputs follow the ideal
   functionality.
   Naming: the _ok suffix carries over from the delivery-law condition
   delivery_law_ok of entropy_link.v, stated here in conditional form. *)
Lemma delivery_law_ok (x : X3) :
  `Pr[ input_rv = x ] != 0 ->
  forall y, `Pr[ outputs_rv = y | input_rv = x ] = functionality x y.
Proof.
move=> _ y; rewrite cpr_eqE pfwd1_input invrK.
have -> : `Pr[ [% outputs_rv, input_rv] = (y, x) ]
        = `Pr[ [% input_rv, outputs_rv] = (x, y) ].
  rewrite !pfwd1E; congr (Pr _ _); apply/setP => u.
  by rewrite !inE !xpair_eqE andbC.
rewrite pfwd1_input_outputs /mu fdist_uniformE card_X3.
by rewrite mulrAC mulVf ?pnatr_eq0// mul1r.
Qed.

(* The view and the conditioner have two preimage points at a compatible
   joint value and none otherwise. *)
Lemma card_preim_view_cond (a s' r : F2) (x : X3) (s : F2) :
  #|finset ([% view_rv, cond_rv] @^-1 (((a, s'), r), (x, s)))|
  = if (a == x.1.1) && (s' == s) then 2 else 0.
Proof.
have -> : finset ([% view_rv, cond_rv] @^-1 (((a, s'), r), (x, s)))
        = if (a == x.1.1) && (s' == s)
          then setX [set x] (setX (setX [set s] [set: F2]) [set r]) else set0.
  apply/setP => -[x' [[w1 w2] r']].
  rewrite !inE !xpair_eqE /view_rv /cond_rv /adv_input_rv /y1_rv /key_rv
          /input_rv /=.
  case: (eqVneq x' x) => [->|xne]/=; last first.
    by rewrite !andbF; case: ifP => _; rewrite !inE ?xpair_eqE ?(negbTE xne)//.
  case: (eqVneq x.1.1 a) => [xa|ane]/=; last by rewrite inE.
  case: (eqVneq s' s) => [->|sne]/=; last first.
    rewrite inE; case: (eqVneq w1 s') => [->|]//=.
    by rewrite (negbTE sne) andbF.
  by rewrite !inE eqxx/= andbT andbAC andbb.
case: ifP => _; last exact: cards0.
by rewrite !cardsX !cards1 !cardsT card_F2.
Qed.

(* def:smc:perfect-privacy *)
(* On every positive-mass fibre of the conditioner the view law is the
   simulator at the allowed information.
   Naming: view_cond_sim mirrors bob_view_cond_sim_xy of the scalar-product
   bridge, naming a conditional view law after the simulator it equals. *)
Lemma view_cond_sim (x : X3) (s : F2) :
  `Pr[ cond_rv = (x, s) ] != 0 ->
  forall v, `Pr[ view_rv = v | cond_rv = (x, s) ] = sim (x.1.1, s) v.
Proof.
move=> _ [[a s'] r]; rewrite cpr_eqE pfwd1_cond invrK pfwd1_cardE.
rewrite card_preim_view_cond /sim tensorE fdist1E xpair_eqE fdist_uniformE.
by rewrite card_F2; case: ifP => _; rewrite ?mul0r ?mul1r//; lra.
Qed.

(* The view law is the allowed-information law bound through the simulator.
   Naming: _factorization names the >>= decomposition, mirroring
   spp_bob_factorization of the scalar-product bridge. *)
Lemma view_factorization : `p_ view_rv = `p_ allow_rv >>= sim.
Proof.
apply/fdist_ext => -[[a s] r]; rewrite dist_of_RVE [RHS]fdistbindE pfwd1_view.
rewrite (bigD1 (a, s))//= big1 ?addr0; last first.
  move=> b bne; rewrite /sim tensorE fdist1E.
  by rewrite eq_sym (negbTE bne) mul0r mulr0.
rewrite dist_of_RVE pfwd1_allow /sim tensorE fdist1E eqxx/=.
by rewrite mul1r /unif2 fdist_uniformE card_F2 -invfM -natrM.
Qed.

(* The law of the share delivered to party two is uniform. *)
Lemma y2_lawE : `p_ y2_rv = unif2.
Proof.
by apply/fdist_ext => t; rewrite dist_of_RVE pfwd1_y2 fdist_uniformE card_F2.
Qed.

(* The law of the output delivered to party two is uniform. *)
Lemma party2_out_lawE : `p_ party2_out_rv = unif4.
Proof.
apply/fdist_ext => -[t r]; rewrite dist_of_RVE pfwd1_party2_out.
by rewrite fdist_uniformE card_F2F2.
Qed.

(* The output delivered to party two is independent of the conditioner.
   Naming: joint_<variables> is intentional, the variables-first order of this
   file, naming the joint law after the variables it relates. *)
Lemma joint_party2_out_cond :
  `p_ [% party2_out_rv, cond_rv]
  = (`p_ party2_out_rv `x `p_ cond_rv)%fdist.
Proof.
apply/fdist_ext => -[[t r] [x s]]; rewrite fdist_prodE !dist_of_RVE.
by rewrite pfwd1_party2_out_cond pfwd1_party2_out pfwd1_cond -invfM -natrM.
Qed.

(* The share of party two is independent of the extended conditioner.
   Naming: joint_<variables> is intentional, the variables-first order of this
   file, naming the joint law after the variables it relates. *)
Lemma joint_y2_cond_key :
  `p_ [% y2_rv, cond_key_rv] = (`p_ y2_rv `x `p_ cond_key_rv)%fdist.
Proof.
apply/fdist_ext => -[t [[x s] r]]; rewrite fdist_prodE !dist_of_RVE.
by rewrite pfwd1_y2_cond_key pfwd1_y2 pfwd1_cond_key -invfM -natrM.
Qed.

(* Given the conditioner the output delivered to party two has conditional
   entropy log 4.
   Naming: centropy_<conditioned>_<conditioner> is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_party2_out_cond :
  `H( party2_out_rv | cond_rv ) = log 4%:R :> R.
Proof.
have Hprod : `p_ [% party2_out_rv, cond_rv]
  = ((`p_ [% party2_out_rv, cond_rv])`1
     `x (`p_ [% party2_out_rv, cond_rv])`2)%fdist.
  by rewrite fst_RV2 snd_RV2 joint_party2_out_cond.
rewrite /centropy_RV (centropy_indep Hprod) fst_RV2 party2_out_lawE.
by rewrite entropy_uniform card_F2F2.
Qed.

(* Given the extended conditioner the share of party two has conditional
   entropy log 2.
   Naming: centropy_<conditioned>_<conditioner> is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_y2_cond_key : `H( y2_rv | cond_key_rv ) = log 2%:R :> R.
Proof.
have Hprod : `p_ [% y2_rv, cond_key_rv]
  = ((`p_ [% y2_rv, cond_key_rv])`1 `x (`p_ [% y2_rv, cond_key_rv])`2)%fdist.
  by rewrite fst_RV2 snd_RV2 joint_y2_cond_key.
rewrite /centropy_RV (centropy_indep Hprod) fst_RV2 y2_lawE.
by rewrite entropy_uniform card_F2.
Qed.

(* The recoding sends the conditioner with the share of party two and the key
   to the conditioner with the honest outputs. *)
Definition recode (p : (X3 * F2) * (F2 * F2))
  : (X3 * F2) * ((F2 * F2) * (F2 * F2)) :=
  (p.1, ((p.2.1, p.2.2), (f_sum p.1.1 - p.1.2 - p.2.1, p.2.2))).

(* The recoding is injective. *)
Lemma recode_inj : injective recode.
Proof. by move=> [c [t r]] [c' [t' r']] [] -> -> -> _ _. Qed.

(* The joint law of the conditioner and the honest outputs is the transport
   along the recoding.
   Naming: joint_<variables>_<map> is intentional, the variables-first order
   of this file, naming the joint law before the map that carries it. *)
Lemma joint_cond_honest_recode :
  `p_ [% cond_rv, honest_rv]
  = fdistmap recode (`p_ [% cond_rv, party2_out_rv]).
Proof. by rewrite /dist_of_RV fdistmap_comp. Qed.

(* def:smc:output-independence *)
(* Given the conditioner alone the honest outputs have conditional entropy
   log 4.
   Naming: centropy_<conditioned>_<conditioner> is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_honest_cond : `H( honest_rv | cond_rv ) = log 4%:R :> R.
Proof.
have hjoint : `H(cond_rv, honest_rv) = `H(cond_rv, party2_out_rv).
  rewrite /joint_entropy_RV /joint_entropy joint_cond_honest_recode.
  by rewrite (entropy_fdistmap _ recode_inj).
move: (chain_rule_RV cond_rv honest_rv); rewrite hjoint.
rewrite (chain_rule_RV cond_rv party2_out_rv) => /addrI <-.
exact: centropy_party2_out_cond.
Qed.

(* The recoding sends the extended conditioner with the share of party two to
   the view and the conditioner with the honest outputs. *)
Definition recode_view_cond_honest (p : ((X3 * F2) * F2) * F2)
  : (((F2 * F2) * F2) * (X3 * F2)) * ((F2 * F2) * (F2 * F2)) :=
  ((((p.1.1.1.1.1, p.1.1.2), p.1.2), p.1.1),
   ((p.2, p.1.2), (f_sum p.1.1.1 - p.1.1.2 - p.2, p.1.2))).

(* The recoding is injective. *)
Lemma recode_view_cond_honest_inj : injective recode_view_cond_honest.
Proof.
apply: (can_inj (g := fun q => ((q.1.2, q.1.1.2), q.2.1.1))).
by move=> -[[[x s] r] t].
Qed.

(* The recoding sends the extended conditioner to the view with the
   conditioner. *)
Definition recode_view_cond (p : (X3 * F2) * F2)
  : ((F2 * F2) * F2) * (X3 * F2) :=
  (((p.1.1.1.1, p.1.2), p.2), p.1).

(* The recoding is injective. *)
Lemma recode_view_cond_inj : injective recode_view_cond.
Proof. by apply: (can_inj (g := fun q => (q.2, q.1.2))) => -[[x s] r]. Qed.

(* The joint law of the view with the conditioner and the honest outputs is
   the transport along the recoding.
   Naming: joint_<variables>_<map> is intentional, the variables-first order
   of this file, naming the joint law before the map that carries it. *)
Lemma joint_view_cond_honest_recode :
  `p_ [% [% view_rv, cond_rv], honest_rv]
  = fdistmap recode_view_cond_honest (`p_ [% cond_key_rv, y2_rv]).
Proof. by rewrite /dist_of_RV fdistmap_comp. Qed.

(* The joint law of the view and the conditioner is the transport along the
   recoding of the law of the extended conditioner.
   Naming: law_<variables>_<map> is intentional, the variables-first order of
   this file, naming the law before the map that carries it. *)
Lemma law_view_cond_recode :
  `p_ [% view_rv, cond_rv] = fdistmap recode_view_cond (`p_ cond_key_rv).
Proof. by rewrite /dist_of_RV fdistmap_comp. Qed.

(* def:smc:output-independence *)
(* Given the view and the conditioner the honest outputs have conditional
   entropy log 2.
   Naming: centropy_<conditioner joined>_<conditioned> is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_view_honest :
  `H( honest_rv | [% view_rv, cond_rv] ) = log 2%:R :> R.
Proof.
have hjoint : `H([% view_rv, cond_rv], honest_rv) = `H(cond_key_rv, y2_rv).
  rewrite /joint_entropy_RV /joint_entropy joint_view_cond_honest_recode.
  by rewrite (entropy_fdistmap _ recode_view_cond_honest_inj).
have hmarg : `H `p_ [% view_rv, cond_rv] = `H `p_ cond_key_rv.
  by rewrite law_view_cond_recode (entropy_fdistmap _ recode_view_cond_inj).
move: (chain_rule_RV [% view_rv, cond_rv] honest_rv); rewrite hjoint hmarg.
rewrite (chain_rule_RV cond_key_rv y2_rv) => /addrI <-.
exact: centropy_y2_cond_key.
Qed.

(* def:smc:output-independence *)
(* The conditional entropy of the honest outputs given the conditioner
   changes when the view joins the conditioning.
   Naming: centropy_<conditioner joined>_<conditioned>_neq is intentional, the
   convention of this file naming a lemma after the variables it relates. *)
Lemma centropy_view_honest_neq :
  `H( honest_rv | [% view_rv, cond_rv] ) <> `H( honest_rv | cond_rv ).
Proof.
rewrite centropy_view_honest centropy_honest_cond.
have -> : (4%:R : R) = 2%:R * 2%:R by rewrite -natrM.
by rewrite logM ?ltr0n// log2 => h; move: h; lra.
Qed.

(* The adversary's part of an input. *)
Let proj_xa (x : X3) : F2 := x.1.1.

(* The honest parties' part of an input. *)
Let proj_xh (x : X3) : (F2 * F2)%type := (x.1.2, x.2).

(* The adversary's part of the delivered outputs. *)
Let proj_ya (s : Yfull) : F2 := s.1.1.

(* The honest parties' part of the delivered outputs. *)
Let proj_yh (s : Yfull) : ((F2 * F2) * (F2 * F2))%type := (s.1.2, s.2).

(* The run of an execution delivers the shares and the key. *)
Let run (e : X3 * Om) : Yfull := deliver e.1 e.2.

(* The view at an execution. *)
Let view_at (e : X3 * Om) : (F2 * F2) * F2 := ((e.1.1.1, e.2.1.1), e.2.2).

(* The adversary's delivered share read off a view. *)
Let out_adv (v : (F2 * F2) * F2) : F2 := v.1.2.

(* The aggregation of the run recovers the function at every execution.
   Naming: _correct marks agreement with the specified function, the
   file's convention for specification-conformance statements. *)
Lemma run_correct (e : X3 * Om) : agg (run e) = f_sum e.1.
Proof.
by case: e => x [[w1 w2] r]; rewrite /agg /run /deliver/= addrCA addrK subrK.
Qed.

(* Every coin triple has mass one eighth. *)
Let P_OmegaE (w : Om) : P_Omega w = 8%:R^-1.
Proof.
case: w => -[w1 w2] r; rewrite /P_Omega !tensorE /unif2 !fdist_uniformE.
by rewrite card_F2 -!invfM -!natrM.
Qed.

(* The view kernel at an input is the coin law on the share and the key the
   adversary sees, at its own bit. *)
Lemma view_kernelE (c a s t : F2) :
  fdistmap (fun w : Om => ((c, w.1.1), w.2)) P_Omega ((a, s), t)
  = (c == a)%:R * 4%:R^-1.
Proof.
rewrite fdistmapE; under eq_bigr do rewrite P_OmegaE.
rewrite big_const iter_addr addr0 mulr_natl -cardsE.
have -> : [set w in preim (fun w : Om => ((c, w.1.1), w.2)) (pred1 ((a, s), t))]
        = if c == a then setX (setX [set s] [set: F2]) [set t] else set0.
  apply/setP => -[[w1 w2] r]; rewrite !inE !xpair_eqE/=.
  by case: (c == a); rewrite !inE ?andbT.
case: (c == a); last by rewrite cards0 !mulr0n.
by rewrite !cardsX !cards1 cardsT card_F2 !mulr1n mulr2n; lra.
Qed.

(* The allowed-information kernel at an input is the uniform law on the
   adversary's share, at its own bit. *)
Lemma allow_kernelE (c a s : F2) :
  fdistmap (fun w : Om => (c, w.1.1)) P_Omega (a, s) = (c == a)%:R * 2%:R^-1.
Proof.
rewrite fdistmapE; under eq_bigr do rewrite P_OmegaE.
rewrite big_const iter_addr addr0 mulr_natl -cardsE.
have -> : [set w in preim (fun w : Om => (c, w.1.1)) (pred1 (a, s))]
        = if c == a then setX (setX [set s] [set: F2]) [set: F2] else set0.
  apply/setP => -[[w1 w2] r]; rewrite !inE !xpair_eqE/=.
  by case: (c == a); rewrite !inE ?andbT.
case: (c == a); last by rewrite cards0 !mulr0n.
rewrite !cardsX cards1 !cardsT card_F2 mulr1n.
by rewrite -mulr_natl; lra.
Qed.

(* def:smc:perfect-privacy *)
(* The view law at an input is the allowed-information law of that input
   bound through the simulator.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma triangle_holds :
  triangle proj_xa proj_ya functionality P_Omega view_at sim.
Proof.
move=> x; apply/fdist_ext => -[[a s] t].
have -> : fdistmap (fun yl => (proj_xa x, proj_ya yl)) (functionality x)
        = fdistmap (fun w : Om => (proj_xa x, w.1.1)) P_Omega.
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

(* The execution at the all-zero input and the coins with a one in the key
   slot. *)
Let pt1 : X3 * Om := (x0, ((0, 0), 1)).

(* Two executions sharing an input and an adversary share deliver different
   honest outputs. *)
Let yh_differs : proj_yh (run pt0) <> proj_yh (run pt1).
Proof.
rewrite /proj_yh /run /deliver /pt0 /pt1 /=; apply/eqP.
by rewrite !xpair_eqE eq_sym oner_eq0 !andbF.
Qed.

(* No function of the input alone gives the honest outputs at every execution
   of positive mass. *)
Lemma not_output_det :
  ~ (exists g : X3 -> ((F2 * F2) * (F2 * F2))%type,
       forall e, exec_law e != 0 -> proj_yh (run e) = g e.1).
Proof.
by case=> g hg; apply: yh_differs;
   rewrite (hg pt0 (exec_law_neq0 _)) (hg pt1 (exec_law_neq0 _)).
Qed.

(* No function of the input and the adversary's delivered share gives the
   honest outputs at every execution of positive mass. *)
Lemma not_output_determined :
  ~ (exists g : X3 -> F2 -> ((F2 * F2) * (F2 * F2))%type,
       forall e, exec_law e != 0 -> proj_yh (run e) = g e.1 (proj_ya (run e))).
Proof.
by case=> g hg; apply: yh_differs;
   rewrite (hg pt0 (exec_law_neq0 _)) (hg pt1 (exec_law_neq0 _)).
Qed.

(* The output read off the view of an execution is the adversary's delivered
   share. *)
Let readoff (e : X3 * Om) : out_adv (view_at e) = proj_ya (run e).
Proof. by []. Qed.

(* The prior has full support. *)
Let mu_full (x : X3) : mu x != 0.
Proof. by rewrite fdist_uniformE card_X3 invr_eq0 pnatr_eq0. Qed.

(* The split of an input into the adversary's and the honest parties' parts
   is injective. *)
Let split_inj : injective (fun x => (proj_xa x, proj_xh x)).
Proof.
by move=> [[a b] c] [[a' b'] c']; rewrite /proj_xa /proj_xh /= => -[-> -> ->].
Qed.

(* The honest parties' part of the input. *)
Let xh_rv : {RV exec_law -> (F2 * F2)%type} := proj_xh \o fst.

(* The honest parties' part of the delivered outputs. *)
Let yh_rv : {RV exec_law -> ((F2 * F2) * (F2 * F2))%type} :=
  fun e => proj_yh (run e).

(* The adversary's part of the input. *)
Let xa_rv : {RV exec_law -> F2} := proj_xa \o fst.

(* The adversary's part of the delivered outputs. *)
Let ya_rv : {RV exec_law -> F2} := fun e => proj_ya (run e).

(* The adversary's view. *)
Let v_rv : {RV exec_law -> ((F2 * F2) * F2)%type} := view_at.

(* eq:smc:entropy *)
(* The conditional entropy of the honest parties' inputs and delivered
   outputs given the adversary's own changes when the view joins the
   conditioning.
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

(* The real joint law of the view and the delivered outputs at an input.
   This is the right-hand side of Lindell's joint comparison. *)
Definition real_pair (x : X3) : R.-fdist (((F2 * F2) * F2) * Yfull)%type :=
  fdistmap (fun w : Om => (view_at (x, w), run (x, w))) P_Omega.

(* The simulated view coupled with the same functionality draw. *)
Definition ideal_pair (x : X3) : R.-fdist (((F2 * F2) * F2) * Yfull)%type :=
  functionality x >>= (fun y => tensor (sim (proj_xa x, proj_ya y)) (fdist1 y)).

(* The all-zero delivered outputs. *)
Let y0 : Yfull := ((0, (0, 0)), (0, 0)).

(* The view whose key slot is one. *)
Let v0 : ((F2 * F2) * F2)%type := ((0, 0), 1).

(* The ideal functionality at the all-zero input gives the all-zero outputs
   mass one eighth. *)
Let functionality_x0 : functionality x0 y0 = 8%:R^-1.
Proof.
rewrite /functionality fdistmapE (big_pred1 (((0, 0), 0) : Om));
  first exact: P_OmegaE.
move=> [[w1 w2] r]; rewrite !inE !xpair_eqE /deliver /y0 f_sum_x0 /=.
by case: (eqVneq w1 0) => [->|?]//=; case: (eqVneq w2 0) => [->|?]//=;
   rewrite ?subr0 ?eqxx/=; case: (r == 0).
Qed.

(* The real pair carries the dealt key in both components, so a mismatched
   key has mass zero. *)
Lemma real_pair_zero : real_pair x0 (v0, y0) = 0.
Proof.
rewrite /real_pair fdistmapE big_pred0// => -[[w1 w2] r].
rewrite !inE !xpair_eqE /view_at /run /deliver /v0 /y0 f_sum_x0 /=.
by case: (eqVneq r 0) => [->|?]; rewrite ?andbF// eq_sym oner_eq0 !andbF.
Qed.

(* The ideal pair draws the simulated key afresh, so a mismatched key has
   mass one over sixteen. *)
Lemma ideal_pair_val : ideal_pair x0 (v0, y0) = 16%:R^-1.
Proof.
rewrite /ideal_pair fdistbindE (bigD1 y0)//= big1 ?addr0; last first.
  by move=> y yne; rewrite tensorE fdist1E eq_sym (negbTE yne) mulr0 mulr0.
rewrite functionality_x0 tensorE fdist1E eqxx mulr1 /sim tensorE fdist1E /=.
by rewrite mul1r /unif2 fdist_uniformE card_F2 -invfM -natrM.
Qed.

(* The two joint laws differ at a mismatched-key point.
   Naming: _neq marks a <> statement and _at the pointwise instance of the
   law-level real_ideal_pair_neq. *)
Lemma real_ideal_pair_neq_at : real_pair x0 (v0, y0) <> ideal_pair x0 (v0, y0).
Proof.
rewrite real_pair_zero ideal_pair_val => /esym/eqP.
by rewrite invr_eq0 pnatr_eq0.
Qed.

(* The two joint laws of Lindell's comparison differ at the all-zero input. *)
Lemma real_ideal_pair_neq : real_pair x0 <> ideal_pair x0.
Proof. by move=> h; apply: real_ideal_pair_neq_at; rewrite h. Qed.

End instance.
End dealt_key_leak.

(* Three parties additively share the sum of three private bits over the
   two-element field and the two honest parties are delivered a shared key
   that party two samples with mass three quarters at zero and routes to
   party three.  The compatibility square, the privacy triangle and output
   independence hold, while the delivered joint law differs from the one the
   ideal functionality prescribes and no simulator couples the view with the
   prescribed outputs. *)
Module biased_key.
Section instance.
Context {R : realType}.

(* The two-element field. *)
Let F2 : finType := 'F_2.

(* The two-element field has two points. *)
Lemma card_F2 : #|F2| = 2.
Proof. by rewrite card_ord. Qed.

(* The uniform law on the two-element field. *)
Definition unif2 : R.-fdist F2 := fdist_uniform card_F2.

(* Three quarters lies in the unit interval. *)
Let key_bias_subproof : (0 <= (3 / 4 : R) <= 1)%O.
Proof. by apply/andP; split; lra. Qed.

(* The weight three quarters as a probability. *)
Definition key_bias : {prob R} := Prob.mk key_bias_subproof.

(* The biased key law puts three quarters on zero. *)
Definition biased2 : R.-fdist F2 := (fdist1 0 <| key_bias |> fdist1 1)%fdist.

(* The biased key law gives three quarters to zero. *)
Lemma biased2_0 : biased2 0 = 3 / 4.
Proof. by rewrite /biased2 !fdist_convE !fdist1E /= onemE; lra. Qed.

(* The biased key law gives one quarter to one. *)
Lemma biased2_1 : biased2 1 = 4%:R^-1.
Proof. by rewrite /biased2 !fdist_convE !fdist1E /= onemE; lra. Qed.

(* The input space gives one private bit to each of the three parties. *)
Let X3 := (F2 * F2 * F2)%type.

(* The input space has eight points. *)
Lemma card_X3 : #|(X3 : finType)| = 8.
Proof. by rewrite !card_prod !card_F2. Qed.

(* The prior on the input space is uniform.
   Naming: mu is intentional, the thesis notation $\mu$ for the prior on the
   input space. *)
Definition mu : R.-fdist X3 := fdist_uniform card_X3.

(* A coin triple carries the two free shares and the key. *)
Let Om := ((F2 * F2) * F2)%type.

(* The coins the ideal functionality prescribes draw the key uniformly. *)
Definition P_Omega_unif : R.-fdist Om := tensor (tensor unif2 unif2) unif2.

(* The coins the protocol executes on draw the key with bias three
   quarters. *)
Definition P_Omega : R.-fdist Om := tensor (tensor unif2 unif2) biased2.

(* The execution context pairs an input with the biased coins. *)
Definition exec_law : R.-fdist (X3 * Om)%type := tensor mu P_Omega.

(* The function the protocol computes is the sum of the three private
   bits. *)
Definition f_sum (x : X3) : F2 := x.1.1 + x.1.2 + x.2.

(* The delivered outputs are the share of party one, the share of party two
   with the key, and the share of party three with the same key. *)
Let Yfull := ((F2 * (F2 * F2)) * (F2 * F2))%type.

(* The delivery map sends an input and coins to the three shares and the two
   copies of the key. *)
Definition deliver (x : X3) (w : Om) : Yfull :=
  ((w.1.1, (w.1.2, w.2)), (f_sum x - w.1.1 - w.1.2, w.2)).

(* The ideal functionality at an input is the transport of the uniform coins
   along the delivery map. *)
Definition functionality (x : X3) : R.-fdist Yfull :=
  fdistmap (deliver x) P_Omega_unif.

(* The real delivered law at an input is the transport of the biased coins
   along the delivery map. *)
Definition real_law (x : X3) : R.-fdist Yfull := fdistmap (deliver x) P_Omega.

(* The aggregation of the delivered outputs is the sum of the three shares. *)
Definition agg (s : Yfull) : F2 := s.1.1 + s.1.2.1 + s.2.1.

(* A coin triple has the mass of its key over four. *)
Lemma P_OmegaE (w : Om) : P_Omega w = 4%:R^-1 * biased2 w.2.
Proof.
case: w => -[w1 w2] r; rewrite /P_Omega !tensorE /unif2 !fdist_uniformE.
by rewrite card_F2 -invfM -natrM.
Qed.

(* Every prescribed coin triple has mass one eighth. *)
Lemma P_Omega_unifE (w : Om) : P_Omega_unif w = 8%:R^-1.
Proof.
case: w => -[w1 w2] r; rewrite /P_Omega_unif !tensorE /unif2 !fdist_uniformE.
by rewrite card_F2 -!invfM -!natrM.
Qed.

(* Every execution has the mass of its key over thirty-two. *)
Lemma exec_lawE (e : X3 * Om) : exec_law e = 32%:R^-1 * biased2 e.2.2.
Proof.
case: e => x w; rewrite /exec_law tensorE P_OmegaE /mu fdist_uniformE card_X3.
by rewrite mulrA -invfM -natrM.
Qed.

(* The input of the execution. *)
Definition input_rv : {RV exec_law -> X3} := fst.

(* The private bit of the adversary, party one. *)
Definition adv_input_rv : {RV exec_law -> F2} := fun e => e.1.1.1.

(* The share delivered to the adversary. *)
Definition y1_rv : {RV exec_law -> F2} := fun e => e.2.1.1.

(* The share delivered to party two. *)
Definition y2_rv : {RV exec_law -> F2} := fun e => e.2.1.2.

(* The key delivered to both honest parties. *)
Definition key_rv : {RV exec_law -> F2} := fun e => e.2.2.

(* The share delivered to party three completes the sum. *)
Definition y3_rv : {RV exec_law -> F2} :=
  fun e => f_sum e.1 - e.2.1.1 - e.2.1.2.

(* The adversary observes its own bit and its own share. *)
Definition view_rv := [% adv_input_rv, y1_rv].

(* The outputs delivered to the two honest parties. *)
Definition honest_rv := [% [% y2_rv, key_rv], [% y3_rv, key_rv]].

(* The allowed information is the adversary's bit and its delivered share,
   which is the view itself. *)
Definition allow_rv := [% adv_input_rv, y1_rv].

(* The conditioner is the input and the adversary's delivered share. *)
Definition cond_rv := [% input_rv, y1_rv].

(* The delivered outputs of the execution. *)
Definition outputs_rv : {RV exec_law -> Yfull} := fun e => deliver e.1 e.2.

(* The simulator answers the allowed information. *)
Definition sim : simulator (R := R) F2 F2 (F2 * F2)%type := fun a => fdist1 a.

(* The adversary's part of an input. *)
Let proj_xa (x : X3) : F2 := x.1.1.

(* The honest parties' part of an input. *)
Let proj_xh (x : X3) : (F2 * F2)%type := (x.1.2, x.2).

(* The adversary's part of the delivered outputs. *)
Let proj_ya (s : Yfull) : F2 := s.1.1.

(* The honest parties' part of the delivered outputs. *)
Let proj_yh (s : Yfull) : ((F2 * F2) * (F2 * F2))%type := (s.1.2, s.2).

(* The run of an execution delivers the shares and the key. *)
Let run (e : X3 * Om) : Yfull := deliver e.1 e.2.

(* The view at an execution. *)
Let view_at (e : X3 * Om) : (F2 * F2)%type := (e.1.1.1, e.2.1.1).

(* The adversary's delivered share read off a view. *)
Let out_adv (v : (F2 * F2)%type) : F2 := v.2.

(* The aggregation of the run recovers the function at every execution.
   Naming: _correct marks agreement with the specified function, the
   file's convention for specification-conformance statements. *)
Lemma run_correct (e : X3 * Om) : agg (run e) = f_sum e.1.
Proof.
by case: e => x [[w1 w2] r]; rewrite /agg /run /deliver/= addrCA addrK subrK.
Qed.

(* eq:smc:functionality-compat *)
(* The aggregation of the ideal functionality is the point mass at the value
   of the function. *)
Lemma functionality_compat (x : X3) :
  fdistmap agg (functionality x) = fdist1 (f_sum x).
Proof.
rewrite /functionality fdistmap_comp; apply: eq_fdistmap_cst => w /=.
by rewrite /agg /deliver /= addrCA addrK subrK.
Qed.

(* The output read off a simulated view is the point mass at the delivered
   share the simulator was handed. *)
Lemma sim_consistent (a : F2 * F2) :
  fdistmap (fun v : (F2 * F2)%type => v.2) (sim a) = fdist1 a.2.
Proof. by rewrite /sim fdistmap1. Qed.

(* def:smc:output-independence *)
(* The view and the honest outputs are conditionally independent given the
   conditioner.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma cinde_honest_holds : exec_law |= view_rv _|_ honest_rv | cond_rv.
Proof.
apply: graphoid.symmetry.
by apply: (cinde_RV_fun_conditioner honest_rv
  (h := fun c : (X3 * F2)%type => (c.1.1.1, c.2))).
Qed.

(* def:smc:output-independence *)
(* Output independence holds.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma output_independent_holds :
  output_independent proj_ya proj_yh P_Omega view_at run mu.
Proof. exact: cinde_honest_holds. Qed.

(* The share delivered to the adversary is uniform under the biased coins. *)
Lemma fst_marginal_biasedE : fdistmap (fun w : Om => w.1.1) P_Omega = unif2.
Proof.
have -> : fdistmap (fun w : Om => w.1.1) P_Omega = ((P_Omega)`1)`1.
  by rewrite /fdist_fst fdistmap_comp.
by rewrite /P_Omega /tensor !fdist_prod1.
Qed.

(* The share delivered to the adversary is uniform under the prescribed
   coins. *)
Lemma fst_marginal_unifE :
  fdistmap (fun w : Om => w.1.1) P_Omega_unif = unif2.
Proof.
have -> : fdistmap (fun w : Om => w.1.1) P_Omega_unif = ((P_Omega_unif)`1)`1.
  by rewrite /fdist_fst fdistmap_comp.
by rewrite /P_Omega_unif /tensor !fdist_prod1.
Qed.

(* The allowed-information kernel at an input is the uniform law on the
   adversary's share, at its own bit, under any coins with uniform first
   marginal. *)
Lemma allow_kernelE (P : R.-fdist Om)
    (hP : fdistmap (fun w : Om => w.1.1) P = unif2) (c a s : F2) :
  fdistmap (fun w : Om => (c, w.1.1)) P (a, s) = (c == a)%:R * 2%:R^-1.
Proof.
have -> : fdistmap (fun w : Om => (c, w.1.1)) P
        = fdistmap (fun q : F2 => (c, q)) (fdistmap (fun w : Om => w.1.1) P).
  by rewrite fdistmap_comp.
by rewrite hP -tensor_fdist1 tensorE fdist1E eq_sym /unif2 fdist_uniformE
   card_F2.
Qed.

(* def:smc:perfect-privacy *)
(* The view law at an input is the allowed-information law of that input
   bound through the simulator.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma triangle_holds :
  triangle proj_xa proj_ya functionality P_Omega view_at sim.
Proof.
move=> x; apply/fdist_ext => -[a s].
have -> : fdistmap (fun yl => (proj_xa x, proj_ya yl)) (functionality x)
        = fdistmap (fun w : Om => (proj_xa x, w.1.1)) P_Omega_unif.
  by rewrite /functionality fdistmap_comp; apply: eq_fdistmap.
rewrite fdistbindE (bigD1 (a, s))//= big1 ?addr0; last first.
  by move=> b bne; rewrite /sim fdist1E eq_sym (negbTE bne) mulr0.
rewrite /sim fdist1E eqxx mulr1 (allow_kernelE fst_marginal_unifE).
by rewrite [LHS](allow_kernelE fst_marginal_biasedE).
Qed.

(* The simulator achieves perfect privacy.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma perfect_privacy_holds :
  perfect_privacy proj_xa proj_ya functionality P_Omega view_at sim.
Proof. exact/triangle_perfect_privacyP/triangle_holds. Qed.

(* The all-zero input. *)
Let x0 : X3 := (0, 0, 0).

(* The all-zero delivered outputs. *)
Let y0 : Yfull := ((0, (0, 0)), (0, 0)).

(* The sum of the all-zero input is zero. *)
Let f_sum_x0 : f_sum x0 = 0.
Proof. by rewrite /f_sum /= !addr0. Qed.

(* The all-zero outputs are delivered exactly at the all-zero coins. *)
Let deliver_x0_pred (w : Om) : (deliver x0 w == y0) = (w == (((0, 0), 0) : Om)).
Proof.
case: w => -[w1 w2] r; rewrite !xpair_eqE /deliver /y0 f_sum_x0 /=.
by case: (eqVneq w1 0) => [->|?]//=; case: (eqVneq w2 0) => [->|?]//=;
   rewrite ?subr0 ?eqxx/=; case: (r == 0).
Qed.

(* The real delivered law gives the all-zero outputs mass three sixteenths. *)
Let real_law_x0 : real_law x0 y0 = 4%:R^-1 * (3 / 4).
Proof.
rewrite /real_law fdistmapE (big_pred1 (((0, 0), 0) : Om)); last first.
  by move=> w; rewrite !inE deliver_x0_pred.
by rewrite P_OmegaE /= biased2_0.
Qed.

(* The ideal functionality gives the all-zero outputs mass one eighth. *)
Let functionality_x0 : functionality x0 y0 = 8%:R^-1.
Proof.
rewrite /functionality fdistmapE (big_pred1 (((0, 0), 0) : Om)); last first.
  by move=> w; rewrite !inE deliver_x0_pred.
exact: P_Omega_unifE.
Qed.

(* The input takes each value with the prior's mass. *)
Lemma pfwd1_input (x : X3) : `Pr[ input_rv = x ] = mu x.
Proof.
rewrite -dist_of_RVE /dist_of_RV /input_rv -/(fdist_fst exec_law).
by rewrite /exec_law /tensor fdist_prod1.
Qed.

(* Every input has positive mass. *)
Lemma pfwd1_input_neq0 (x : X3) : `Pr[ input_rv = x ] != 0.
Proof. by rewrite pfwd1_input fdist_uniformE card_X3 invr_eq0 pnatr_eq0. Qed.

(* On every input the delivered outputs follow the real delivered law.
   Naming: outputs_cond_real_law follows view_cond_sim, naming a conditional
   law after the law it equals. *)
Lemma outputs_cond_real_law (x : X3) (y : Yfull) :
  `Pr[ outputs_rv = y | input_rv = x ] = real_law x y.
Proof.
rewrite cpr_eqE pfwd1_input.
have -> : `Pr[ [% outputs_rv, input_rv] = (y, x) ]
        = `Pr[ [% input_rv, outputs_rv] = (x, y) ].
  rewrite !pfwd1E; congr (Pr _ _); apply/setP => u.
  by rewrite !inE !xpair_eqE andbC.
rewrite (pfwd1_input_pair P_Omega mu outputs_rv x y) mulrAC mulfV ?mul1r//.
by rewrite /mu fdist_uniformE card_X3 invr_eq0 pnatr_eq0.
Qed.

(* The delivered outputs do not follow the ideal functionality on every
   positive-mass input. *)
Lemma not_delivery_law_ok :
  ~ (forall x : X3, `Pr[ input_rv = x ] != 0 ->
       forall y, `Pr[ outputs_rv = y | input_rv = x ] = functionality x y).
Proof.
move=> h; move: (h x0 (pfwd1_input_neq0 x0) y0).
by rewrite outputs_cond_real_law real_law_x0 functionality_x0 => hEq; lra.
Qed.

(* The real delivered outputs do not have the law the ideal functionality
   prescribes. *)
Lemma not_delivery_law_holds :
  ~ delivery_law_ok functionality P_Omega (fun e : X3 * Om => deliver e.1 e.2).
Proof.
move=> h; have h1 : real_law x0 y0 = functionality x0 y0.
  by rewrite /real_law (h x0).
by move: h1; rewrite real_law_x0 functionality_x0 => hEq; lra.
Qed.

(* The real joint law of the view and the delivered outputs at an input.
   This is the right-hand side of Lindell's joint comparison. *)
Definition real_pair (x : X3) : R.-fdist ((F2 * F2) * Yfull)%type :=
  fdistmap (fun w : Om => (view_at (x, w), run (x, w))) P_Omega.

(* The view a simulator produces coupled with the functionality draw it was
   handed. *)
Definition ideal_pair_of (S : simulator (R := R) F2 F2 (F2 * F2)%type)
    (x : X3) : R.-fdist ((F2 * F2) * Yfull)%type :=
  functionality x >>= (fun y => tensor (S (proj_xa x, proj_ya y)) (fdist1 y)).

(* The ideal pair at the module's simulator. *)
Definition ideal_pair := ideal_pair_of sim.

(* The parameterized ideal pair at the module's simulator is the simulated
   view coupled with the same functionality draw. *)
Lemma ideal_pairE (x : X3) :
  ideal_pair x
  = functionality x
      >>= (fun y => tensor (sim (proj_xa x, proj_ya y)) (fdist1 y)).
Proof. by []. Qed.

(* The all-zero view. *)
Let v0 : (F2 * F2)%type := (0, 0).

(* The real pair gives the all-zero point the biased key's mass. *)
Lemma real_pair_val : real_pair x0 (v0, y0) = 4%:R^-1 * (3 / 4).
Proof.
rewrite /real_pair fdistmapE (big_pred1 (((0, 0), 0) : Om)); last first.
  move=> w; rewrite !inE !xpair_eqE /view_at /run /v0 /=.
  case: w => -[w1 w2] r; rewrite f_sum_x0 !xpair_eqE /=.
  by case: (eqVneq w1 0) => [->|?]//=; case: (eqVneq w2 0) => [->|?]//=;
     rewrite ?subr0 ?eqxx/=; case: (r == 0).
by rewrite P_OmegaE /= biased2_0.
Qed.

(* The ideal pair gives the all-zero point the prescribed uniform key's
   mass. *)
Lemma ideal_pair_val : ideal_pair x0 (v0, y0) = 8%:R^-1.
Proof.
rewrite /ideal_pair /ideal_pair_of fdistbindE (bigD1 y0)//= big1 ?addr0;
  last first.
  move=> y yne; rewrite tensorE fdist1E.
  by rewrite fdist1E [(y0 == y)]eq_sym (negbTE yne) mulr0 mulr0.
by rewrite functionality_x0 tensorE /sim !fdist1E /= mulr1 mulr1.
Qed.

(* The two joint laws differ at the all-zero point.
   Naming: _neq marks a <> statement and _at the pointwise instance of the
   law-level real_ideal_pair_neq. *)
Lemma real_ideal_pair_neq_at : real_pair x0 (v0, y0) <> ideal_pair x0 (v0, y0).
Proof. by rewrite real_pair_val ideal_pair_val => hEq; lra. Qed.

(* The two joint laws of Lindell's comparison differ at the all-zero
   input. *)
Lemma real_ideal_pair_neq : real_pair x0 <> ideal_pair x0.
Proof. by move=> h; apply: real_ideal_pair_neq_at; rewrite h. Qed.

(* The output marginal of the real pair is the real delivered law. *)
Lemma snd_marginal_real_pairE (x : X3) :
  fdistmap snd (real_pair x) = real_law x.
Proof. by rewrite /real_pair /real_law fdistmap_comp; apply: eq_fdistmap. Qed.

(* The output marginal of the ideal pair is the ideal functionality, at every
   simulator. *)
Lemma snd_marginal_ideal_pairE (S : simulator (R := R) F2 F2 (F2 * F2)%type)
    (x : X3) : fdistmap snd (ideal_pair_of S x) = functionality x.
Proof.
rewrite /ideal_pair_of fdistmap_bind -[RHS]fdistbind1.
congr (fdistbind _ _); apply/boolp.funext => y.
by rewrite tensor_fdist1r fdistmap_comp; apply: eq_fdistmap_cst.
Qed.

(* No simulator makes the ideal pair the real pair at the all-zero input. *)
Lemma not_exists_ideal_pair :
  ~ (exists S : simulator (R := R) F2 F2 (F2 * F2)%type,
       real_pair x0 = ideal_pair_of S x0).
Proof.
have hsep : real_law x0 y0 <> functionality x0 y0.
  by rewrite real_law_x0 functionality_x0 => hEq; lra.
case=> S hS; apply: hsep.
by rewrite -snd_marginal_real_pairE -(snd_marginal_ideal_pairE S) hS.
Qed.

End instance.
End biased_key.

(* Three parties additively share the sum of three private bits and the two
   honest parties are delivered a shared uniform key that party two samples
   and routes to party three.  The compatibility square, the delivery law, the
   privacy triangle, output independence and Lindell's joint equality all
   hold. *)
Module rerouted_key.
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

(* A coin triple carries the two free shares and the key. *)
Let Om := ((F2 * F2) * F2)%type.

(* The coins draw the two free shares and the key as independent uniform
   bits. *)
Definition P_Omega : R.-fdist Om := tensor (tensor unif2 unif2) unif2.

(* The execution context pairs an input with the coins. *)
Definition exec_law : R.-fdist (X3 * Om)%type := tensor mu P_Omega.

(* The function the protocol computes is the sum of the three private
   bits. *)
Definition f_sum (x : X3) : F2 := x.1.1 + x.1.2 + x.2.

(* The delivered outputs are the share of party one, the share of party two
   with the key, and the share of party three with the same key. *)
Let Yfull := ((F2 * (F2 * F2)) * (F2 * F2))%type.

(* The delivery map sends an input and coins to the three shares and the two
   copies of the key. *)
Definition deliver (x : X3) (w : Om) : Yfull :=
  ((w.1.1, (w.1.2, w.2)), (f_sum x - w.1.1 - w.1.2, w.2)).

(* The ideal functionality at an input is the transport of the uniform coins
   along the delivery map. *)
Definition functionality (x : X3) : R.-fdist Yfull :=
  fdistmap (deliver x) P_Omega.

(* The aggregation of the delivered outputs is the sum of the three shares. *)
Definition agg (s : Yfull) : F2 := s.1.1 + s.1.2.1 + s.2.1.

(* Every execution has mass one over sixty-four. *)
Lemma exec_lawE u : exec_law u = 64%:R^-1.
Proof.
case: u => x [[s t] r]; rewrite /exec_law /P_Omega !tensorE !fdist_uniformE.
by rewrite card_X3 card_F2 -!invfM -!natrM.
Qed.

(* The input of the execution. *)
Definition input_rv : {RV exec_law -> X3} := fst.

(* The private bit of the adversary, party one. *)
Definition adv_input_rv : {RV exec_law -> F2} := fun e => e.1.1.1.

(* The share delivered to the adversary. *)
Definition y1_rv : {RV exec_law -> F2} := fun e => e.2.1.1.

(* The share delivered to party two. *)
Definition y2_rv : {RV exec_law -> F2} := fun e => e.2.1.2.

(* The key delivered to both honest parties. *)
Definition key_rv : {RV exec_law -> F2} := fun e => e.2.2.

(* The share delivered to party three completes the sum. *)
Definition y3_rv : {RV exec_law -> F2} :=
  fun e => f_sum e.1 - e.2.1.1 - e.2.1.2.

(* The re-routed view: the adversary observes its own bit and its own share
   only. *)
Definition view_rv := [% adv_input_rv, y1_rv].

(* The outputs delivered to the two honest parties. *)
Definition honest_rv := [% [% y2_rv, key_rv], [% y3_rv, key_rv]].

(* The conditioner is the input and the adversary's delivered share. *)
Definition cond_rv := [% input_rv, y1_rv].

(* The delivered outputs of the execution. *)
Definition outputs_rv : {RV exec_law -> Yfull} := fun e => deliver e.1 e.2.

(* The simulator answers the allowed information. *)
Definition sim : simulator (R := R) F2 F2 (F2 * F2)%type := fun a => fdist1 a.

(* The adversary's part of an input. *)
Let proj_xa (x : X3) : F2 := x.1.1.

(* The adversary's part of the delivered outputs. *)
Let proj_ya (s : Yfull) : F2 := s.1.1.

(* The honest parties' part of the delivered outputs. *)
Let proj_yh (s : Yfull) : ((F2 * F2) * (F2 * F2))%type := (s.1.2, s.2).

(* The run of an execution delivers the shares and the key. *)
Let run (e : X3 * Om) : Yfull := deliver e.1 e.2.

(* The view at an execution. *)
Let view_at (e : X3 * Om) : (F2 * F2)%type := (e.1.1.1, e.2.1.1).

(* The aggregation of the run recovers the function at every execution.
   Naming: _correct marks agreement with the specified function, the
   file's convention for specification-conformance statements. *)
Lemma run_correct (e : X3 * Om) : agg (run e) = f_sum e.1.
Proof.
by case: e => x [[w1 w2] r]; rewrite /agg /run /deliver/= addrCA addrK subrK.
Qed.

(* eq:smc:functionality-compat *)
(* The aggregation of the ideal functionality is the point mass at the value
   of the function. *)
Lemma functionality_compat (x : X3) :
  fdistmap agg (functionality x) = fdist1 (f_sum x).
Proof.
rewrite /functionality fdistmap_comp; apply: eq_fdistmap_cst => w /=.
by rewrite /agg /deliver /= addrCA addrK subrK.
Qed.

(* The output read off a simulated view is the point mass at the delivered
   share the simulator was handed. *)
Lemma sim_consistent (a : F2 * F2) :
  fdistmap (fun v : (F2 * F2)%type => v.2) (sim a) = fdist1 a.2.
Proof. by rewrite /sim fdistmap1. Qed.

(* The real delivered outputs have the law the ideal functionality prescribes
   at every input.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma delivery_law_holds :
  delivery_law_ok functionality P_Omega (fun e : X3 * Om => deliver e.1 e.2).
Proof. by []. Qed.

(* The input takes each value with the prior's mass. *)
Lemma pfwd1_input (x : X3) : `Pr[ input_rv = x ] = mu x.
Proof.
rewrite -dist_of_RVE /dist_of_RV /input_rv -/(fdist_fst exec_law).
by rewrite /exec_law /tensor fdist_prod1.
Qed.

(* On every positive-mass input the delivered outputs follow the ideal
   functionality.
   Naming: the _ok suffix carries over from the delivery-law condition
   delivery_law_ok of entropy_link.v, stated here in conditional form. *)
Lemma delivery_law_ok (x : X3) :
  `Pr[ input_rv = x ] != 0 ->
  forall y, `Pr[ outputs_rv = y | input_rv = x ] = functionality x y.
Proof.
move=> _ y; rewrite cpr_eqE pfwd1_input.
have -> : `Pr[ [% outputs_rv, input_rv] = (y, x) ]
        = `Pr[ [% input_rv, outputs_rv] = (x, y) ].
  rewrite !pfwd1E; congr (Pr _ _); apply/setP => u.
  by rewrite !inE !xpair_eqE andbC.
rewrite (pfwd1_input_pair P_Omega mu outputs_rv x y) mulrAC mulfV ?mul1r//.
by rewrite /mu fdist_uniformE card_X3 invr_eq0 pnatr_eq0.
Qed.

(* def:smc:output-independence *)
(* The view and the honest outputs are conditionally independent given the
   conditioner.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma cinde_honest_holds : exec_law |= view_rv _|_ honest_rv | cond_rv.
Proof.
apply: graphoid.symmetry.
by apply: (cinde_RV_fun_conditioner honest_rv
  (h := fun c : (X3 * F2)%type => (c.1.1.1, c.2))).
Qed.

(* def:smc:output-independence *)
(* Output independence holds.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma output_independent_holds :
  output_independent proj_ya proj_yh P_Omega view_at run mu.
Proof. exact: cinde_honest_holds. Qed.

(* def:smc:perfect-privacy *)
(* The view law at an input is the allowed-information law of that input
   bound through the simulator.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma triangle_holds :
  triangle proj_xa proj_ya functionality P_Omega view_at sim.
Proof.
move=> x; rewrite /sim fdistbind1 /functionality fdistmap_comp.
by apply: eq_fdistmap.
Qed.

(* The simulator achieves perfect privacy.
   Naming: _holds marks an instance proof of the named predicate; no
   canonical suffix covers a Prop-valued instance lemma. *)
Lemma perfect_privacy_holds :
  perfect_privacy proj_xa proj_ya functionality P_Omega view_at sim.
Proof. exact/triangle_perfect_privacyP/triangle_holds. Qed.

(* The real joint law of the view and the delivered outputs at an input.
   This is the right-hand side of Lindell's joint comparison. *)
Definition real_pair (x : X3) : R.-fdist ((F2 * F2) * Yfull)%type :=
  fdistmap (fun w : Om => (view_at (x, w), run (x, w))) P_Omega.

(* The simulated view coupled with the same functionality draw. *)
Definition ideal_pair (x : X3) : R.-fdist ((F2 * F2) * Yfull)%type :=
  functionality x >>= (fun y => tensor (sim (proj_xa x, proj_ya y)) (fdist1 y)).

(* The two joint laws agree at every input. *)
Lemma real_ideal_pair_eq (x : X3) : real_pair x = ideal_pair x.
Proof.
have -> : ideal_pair x
        = fdistmap (fun y : Yfull => ((proj_xa x, proj_ya y), y))
                   (functionality x).
  rewrite /ideal_pair /fdistmap; congr (fdistbind _ _).
  by apply/boolp.funext => y; rewrite /sim tensor_fdist1 fdistmap1.
by rewrite /functionality fdistmap_comp /real_pair; apply: eq_fdistmap.
Qed.

End instance.
End rerouted_key.
