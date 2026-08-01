(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_boot all_order ssralg ssrnum reals.
Require Import fdist finstoch statdist.

(**md**************************************************************************)
(* # The privacy kernel                                                       *)
(*                                                                            *)
(* A protocol is presented by an ideal functionality F on the inputs X, an    *)
(* ancilla law P_Omega, an observation view_at and a run map on the           *)
(* execution context X * Omega.  The view law at an input is the law of the   *)
(* observation of a run at that input, and the allowed information is the     *)
(* law of the adversary's input projection paired with its delivered          *)
(* outputs.  A simulator is a stochastic map from the allowed information to  *)
(* the view space; privacy is the factorization of the view law through a     *)
(* simulator, exactly for perfect privacy and up to a statistical distance    *)
(* eps for eps-privacy.  Each factorization holds exactly when every tester   *)
(* on the view space is tied, respectively eps-bounded, and a hybrid law      *)
(* splits a tester's advantage into a game edge and a simulation edge.        *)
(*                                                                            *)
(* ```                                                                        *)
(*                  draw x == the law on the execution context that keeps x   *)
(*                            and draws the ancilla from P_Omega              *)
(*              view_law x == the law of the adversary's observation of a     *)
(*                            run at the input x                              *)
(*               view_lawE == the view law is the transport of the ancilla    *)
(*                            law along the observation at a fixed input      *)
(*                   f_a x == the law of the outputs delivered to the         *)
(*                            adversary at the input x                        *)
(*                 allow x == the law of the adversary's inputs paired with   *)
(*                            its delivered outputs at the input x            *)
(*                  allowE == the allowed information is the tensor of the    *)
(*                            adversary's input with its delivered outputs    *)
(*            real_route_f == the aggregated run computes f                   *)
(*           ideal_route_f == the aggregated ideal outputs compute f          *)
(*     ideal_route_projx_f == the input projection through the pair space     *)
(*                            computes f                                      *)
(*               simulator == the type (Xa * Ya) -> R.-fdist Bv of            *)
(*                            simulators                                      *)
(*            sim_view S x == the simulated view law at the input x           *)
(*     factors_through h g == h is the composite of g with some stochastic    *)
(*                            map, the factorization witness                  *)
(*       perfect_privacy S == the view law is the simulated view law          *)
(*        perfect_privacyP == the view law factors through the allowed        *)
(*                            information exactly when some simulator         *)
(*                            achieves perfect privacy                        *)
(*              insecurity == inputs with equal allowed information and       *)
(*                            distinct view laws admit no simulator           *)
(*       eps_privacy S eps == the view law is within eps of the simulated     *)
(*                            view law at every input                         *)
(*            test_adv D S == the largest gap the tester D opens between the  *)
(*                            two view laws over the inputs                   *)
(*   perfect_privacy_testP == perfect privacy holds exactly when every        *)
(*                            tester has advantage 0                          *)
(*       eps_privacy_testP == eps-privacy holds exactly when every tester     *)
(*                            has advantage at most eps                       *)
(*            hybrid_bound == a tester's advantage is at most the sum of its  *)
(*                            game edge and its simulation edge at a hybrid   *)
(*                            law                                             *)
(*       identity_protocol == the identity protocol on a two-point input      *)
(*                            space, a perfectly private instance             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section kernel.
Context {R : realType}.
Variables X Yfull Y Xa Ya Bv Omega : finType.
Variable f : X -> Y.
Variable agg : Yfull -> Y.
Variable proj_xa : X -> Xa.
Variable proj_ya : Yfull -> Ya.
Variable F : X -> R.-fdist Yfull.
Hypothesis F_compat : forall x, fdistmap agg (F x) = fdist1 (f x).
Variable P_Omega : R.-fdist Omega.
Variable view_at : X * Omega -> Bv.
Variable run : X * Omega -> Yfull.
Hypothesis run_correct : forall e, agg (run e) = f e.1.

(* def:smc:ancilla-draw *)
(* The ancilla draw at an input is the tensor of the point mass at that input
   with the ancilla law. *)
Definition draw (x : X) : R.-fdist (X * Omega)%type :=
  tensor (fdist1 x) P_Omega.

(* def:smc:view-law *)
(* The view law at an input is the transport of the ancilla draw along the
   adversary's observation. *)
Definition view_law (x : X) : R.-fdist Bv := fdistmap view_at (draw x).

(* def:smc:view-law *)
(* The view law at an input is the transport of the ancilla law along the
   observation with that input fixed. *)
Lemma view_lawE (x : X) :
  view_law x = fdistmap (fun w => view_at (x, w)) P_Omega.
Proof. by rewrite /view_law /draw tensor_fdist1 fdistmap_comp. Qed.

(* def:smc:allowed-info *)
(* The delivered-output law at an input is the transport of the ideal
   functionality along the adversary's output projection. *)
Definition f_a (x : X) : R.-fdist Ya := fdistmap proj_ya (F x).

(* def:smc:allowed-info *)
(* The allowed information at an input is the transport of the input paired
   with the ideal outputs along the two adversary projections. *)
Definition allow (x : X) : R.-fdist (Xa * Ya)%type :=
  fdistmap (fun xy : X * Yfull => (proj_xa xy.1, proj_ya xy.2))
           (tensor (fdist1 x) (F x)).

(* def:smc:allowed-info *)
(* The allowed information is the tensor of the point mass at the adversary's
   input with its delivered-output law. *)
Lemma allowE (x : X) : allow x = tensor (fdist1 (proj_xa x)) (f_a x).
Proof. by rewrite /allow /f_a !tensor_fdist1 !fdistmap_comp. Qed.

(* prop:smc:worlds-compute-f *)
(* The aggregated run of the ancilla draw is the point mass at the value of
   the function. *)
Lemma real_route_f (x : X) :
  fdistmap (fun e => agg (run e)) (draw x) = fdist1 (f x).
Proof.
rewrite /draw tensor_fdist1 fdistmap_comp.
by apply: fdistmap_cst_eq => w /=; exact: run_correct.
Qed.

(* prop:smc:worlds-compute-f *)
(* The aggregated ideal outputs of the pair space are the point mass at the
   value of the function. *)
Lemma ideal_route_f (x : X) :
  fdistmap (fun xy : X * Yfull => agg xy.2) (tensor (fdist1 x) (F x))
  = fdist1 (f x).
Proof.
by rewrite tensor_fdist1 fdistmap_comp -F_compat; apply: eq_fdistmap.
Qed.

(* prop:smc:worlds-compute-f, eq:smc:ideal-route-f input-projection route *)
(* The input-projection route through the pair space computes the function. *)
Lemma ideal_route_projx_f (x : X) :
  fdistmap (fun xy : X * Yfull => f xy.1) (tensor (fdist1 x) (F x))
  = fdist1 (f x).
Proof. by rewrite tensor_fdist1 fdistmap_comp; apply: fdistmap_cst_eq. Qed.

(* def:smc:sim, def:smc:simulator *)
(* The two chapter readings are the same map: a function into distributions
   over the view space, and a stochastic map out of the allowed information. *)
(* A simulator sends the adversary's inputs and delivered outputs to a law on
   its view space. *)
Definition simulator := (Xa * Ya)%type -> R.-fdist Bv.

(* def:smc:perfect-privacy *)
(* The simulated view law at an input is the simulator run on the allowed
   information at that input. *)
Definition sim_view (S : simulator) (x : X) : R.-fdist Bv :=
  allow x >>= S.

(* def:smc:factors-through *)
(* A stochastic map h factors through a stochastic map g when some stochastic
   map, the factorization witness, composes with g to give h. *)
Definition factors_through (A B C : finType)
    (h : stoch (R := R) A C) (g : stoch (R := R) A B) : Prop :=
  exists s : stoch (R := R) B C, h =1 stoch_comp s g.

(* def:smc:perfect-privacy *)
(* A simulator achieves perfect privacy when the view law is the simulated
   view law at every input. *)
Definition perfect_privacy (S : simulator) := view_law =1 sim_view S.

(* def:smc:perfect-privacy *)
(* The view law factors through the allowed information exactly when some
   simulator achieves perfect privacy, the witness being that simulator.
   Naming: P = iff characterization, ffunP/setP precedent. *)
Lemma perfect_privacyP :
  factors_through view_law allow <-> exists S, perfect_privacy S.
Proof. by split=> -[S hS]; exists S. Qed.

(* prop:smc:insecurity *)
(* Two inputs with the same allowed information and distinct view laws admit
   no perfectly private simulator. *)
Lemma insecurity (x x' : X) :
  allow x = allow x' -> view_law x != view_law x' ->
  ~ (exists S : simulator, perfect_privacy S).
Proof.
move=> ha /eqP hv [S hS]; apply: hv.
by rewrite (hS x) (hS x') /sim_view ha.
Qed.

(* def:smc:epsilon-privacy, eq:smc:simulation *)
(* A simulator achieves eps-privacy when the statistical distance between the
   view law and the simulated view law is at most eps at every input. *)
Definition eps_privacy (S : simulator) (eps : R) :=
  forall x, statdist (view_law x) (sim_view S x) <= eps.

(* eq:smc:test-advantage *)
(* The advantage of a tester is the largest gap it opens between the view law
   and the simulated view law over the inputs. *)
Definition test_adv (D : tester Bv) (S : simulator) : R :=
  \big[Num.max/0]_x adv D (view_law x) (sim_view S x).

(* sec:smc:enriched-testing, first display row *)
(* Perfect privacy holds exactly when every tester has advantage 0.
   Naming: P = iff characterization in terms of testers, ffunP/setP
   precedent. *)
Lemma perfect_privacy_testP (S : simulator) :
  perfect_privacy S <-> (forall D : tester Bv, test_adv D S = 0).
Proof.
split=> [hS D|hD x].
  rewrite /test_adv; apply: bigmax_eq_id => y _.
  by rewrite /adv hS subrr normr0.
apply/eqP; rewrite -statdist_eq0 -statdist_test_max; apply/eqP.
apply: bigmax_eq_id => D _.
by rewrite -(hD D) /test_adv; exact: le_bigmax.
Qed.

(* sec:smc:enriched-testing, second display row *)
(* eps-privacy holds exactly when every tester has advantage at most eps.
   Naming: P = iff characterization in terms of testers, ffunP/setP
   precedent. *)
Lemma eps_privacy_testP (S : simulator) (eps : R) : 0 <= eps ->
  eps_privacy S eps <-> (forall D : tester Bv, test_adv D S <= eps).
Proof.
move=> eps0; split=> [hS D|hD x].
  rewrite /test_adv; apply: bigmax_le; first exact: eps0.
  by move=> y _; exact: le_trans (statdist_test_le _ _ _) (hS y).
rewrite -statdist_test_max; apply: bigmax_le; first exact: eps0.
move=> D _; apply: (le_trans _ (hD D)).
by rewrite /test_adv; exact: le_bigmax.
Qed.

(* def:smc:hybrid *)
(* A tester's advantage between the view law and the simulated view law is at
   most the sum of its game edge and its simulation edge at a hybrid law. *)
Lemma hybrid_bound (S : simulator) (H : X -> R.-fdist Bv)
    (D : tester Bv) (e_game e_sim : R) :
  (forall x, adv D (view_law x) (H x) <= e_game) ->
  (forall x, adv D (H x) (sim_view S x) <= e_sim) ->
  forall x, adv D (view_law x) (sim_view S x) <= e_game + e_sim.
Proof.
move=> h_game h_sim x.
apply: le_trans (adv_triangle _ _ _ (H x)) _.
by apply: lerD; [exact: h_game|exact: h_sim].
Qed.

End kernel.

(* The identity protocol on a two-point input space: the ideal functionality
   delivers the input, the ancilla space is a point, and the adversary sees
   the input. *)
Module identity_protocol.
Section instance.
Context {R : realType}.

(* The ideal functionality delivers the input unchanged. *)
Definition functionality (x : 'I_2) : R.-fdist 'I_2 := fdist1 x.

(* The ancilla law is the point mass on the one-point ancilla space. *)
Definition ancilla : R.-fdist 'I_1 := fdist1 ord0.

(* The simulator returns the point mass at the adversary's input. *)
Definition sim : simulator (R := R) 'I_2 'I_2 'I_2 := fun p => fdist1 p.1.

(* The identity aggregation of the ideal functionality is the point mass at
   the value of the identity function. *)
Lemma functionality_compat (x : 'I_2) :
  fdistmap id (functionality x) = fdist1 (id x).
Proof. by rewrite /functionality fdistmap_id. Qed.

(* The first projection of the execution context computes the identity. *)
Lemma run_correct (e : 'I_2 * 'I_1) : id (fst e) = id e.1.
Proof. by []. Qed.

(* prop:smc:worlds-compute-f *)
(* The ideal route computes the identity at this instance. *)
Lemma ideal_route (x : 'I_2) :
  fdistmap (fun xy : 'I_2 * 'I_2 => id xy.2)
           (tensor (fdist1 x) (functionality x)) = fdist1 (id x).
Proof. exact: (ideal_route_f functionality_compat x). Qed.

(* prop:smc:worlds-compute-f *)
(* The real route computes the identity at this instance. *)
Lemma real_route (x : 'I_2) :
  fdistmap (fun e : 'I_2 * 'I_1 => id (fst e)) (draw ancilla x)
  = fdist1 (id x).
Proof. exact: (real_route_f ancilla run_correct x). Qed.

(* def:smc:perfect-privacy *)
(* The identity protocol is perfectly private for the simulator sim. *)
Lemma perfect_privacy_holds :
  perfect_privacy id id functionality ancilla fst sim.
Proof.
move=> x; rewrite /view_law /draw /sim_view /allow.
rewrite /sim /functionality /ancilla.
by rewrite !tensor_fdist1 !fdistmap_comp !fdistmap1 fdist1bind.
Qed.

End instance.
End identity_protocol.
