(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Entropy Security                                                       *)
(*                                                                            *)
(* Pipeline position:                                                         *)
(*   pgg_interface.v -- word_eval, achievable, endpoint, perm_endpoint        *)
(*   pgg_collusion_bound.v -- rho_from_words, var_dist bounds                 *)
(*   algebraic_rigidity.v -- ShuffleMarginalBound (fiber + endpoint_inj)      *)
(*   THIS FILE -- fiber_entropy, EntropyWitness, Pinsker bridge              *)
(*   pgg_security_solver.v -- check_perm_endpoint_inj, fiber_entropy_summary  *)
(*   pgg_schreier.v -- Schreier spectral gap, convergence rate               *)
(*                                                                            *)
(* All definitions are generic over MonodromyReprWithGeneratorType.               *)
(*                                                                            *)
(* Security model:                                                            *)
(*   The dealer samples word w uniformly from Tg^L possible L-tuples.        *)
(*   Each player i observes endpoint sigma_w(s_i), where sigma_w =          *)
(*   word_eval(w). The hidden value is ts_recon(endpoints) -- a value       *)
(*   computed from k endpoints by the threshold scheme. Fewer than k        *)
(*   endpoints reveal nothing about the hidden value (privacy).              *)
(*                                                                            *)
(*   Security = endpoint distribution P_s close to uniform over 'I_N.       *)
(*   collusion_bound (pgg_collusion_bound.v) gives:                          *)
(*     var_dist(adversary_marginal, uniform) <= eps + 2(T-1)/N               *)
(*   eps measures how far P_s is from uniform. When eps ~ 0, each           *)
(*   endpoint is nearly uniform, so observing it reveals little about        *)
(*   the hidden value.                                                       *)
(*                                                                            *)
(* Entropy approach:                                                          *)
(*   The word distribution is uniform by construction. The endpoint          *)
(*   distribution P_s is its pushforward through w |-> word_eval(w)(s).     *)
(*   entropy_fdistmap_uniform_supp gives a closed-form entropy formula:     *)
(*     H(P_s) = log(Tg^L) - (1/Tg^L) sum c_x log(c_x)                     *)
(*   where c_x = |{w in Tg^L : word_eval(w)(s) = x}| are word fibers.     *)
(*   D(P_s || U_N) = log N - H(P_s) measures leakage in bits.              *)
(*   Pinsker's inequality gives var_dist <= sqrt(2*D).                      *)
(*                                                                            *)
(* Full pipeline:                                                             *)
(*   entropy_fdistmap_uniform_supp -> H(P_s) from word fibers               *)
(*   -> EntropyWitness (entropy_witness_from_rho)                             *)
(*   -> ShuffleMarginalBound (security_witness_from_entropy, via Pinsker)     *)
(*   -> collusion_bound (pgg_collusion_bound.v)                               *)
(*                                                                            *)
(* Specializations (stronger hypotheses, simpler formulas):                   *)
(*   weval_inj: word fibers factor as achievable fibers                      *)
(*     c_x = |{sigma in achievable : sigma(s) = x}|                          *)
(*     (fiber_entropy_general)                                                *)
(*   weval_inj + pe_inj: all c_x in {0,1}, H = log(Tg^L)                   *)
(*     (fiber_entropy_injective)                                              *)
(*   weval_inj + pe_inj + Tg^L = N: H = log N, perfect security             *)
(*     (fiber_entropy_perfect)                                                *)
(*                                                                            *)
(* Marginal vs conditional:                                                   *)
(*   H(P_s) measures marginal entropy of one party's endpoint.               *)
(*   A conditional analysis H(s_target | s_0,..,s_{T-2}) would be tighter.  *)
(*   The +2(T-1)/N slack in collusion_bound covers the gap.                  *)
(*                                                                            *)
(* Example A -- Monster at L* = 67 (perfect security):                       *)
(*   Tg=2, N~10^20. Tg^L = 2^67 = N.                                        *)
(*   P_s is uniform over 'I_N (each endpoint equally likely).               *)
(*   H = log N. D = 0. eps = 0.                                              *)
(*   (rigidity_monster_instance.v: monster_security_witness_Lstar)           *)
(*                                                                            *)
(* Example B -- Monster at L = 10 (quantified leakage):                      *)
(*   Tg=2, N~10^20. Tg^L = 1024 << N.                                       *)
(*   P_s is concentrated on 1024 of ~10^20 endpoints.                       *)
(*   H = 10 log 2. D ~ 56 bits. eps <= sqrt(112) ~ 10.6.                   *)
(*   Pinsker bound exceeds 1: L is too short. Combinatorial eps or          *)
(*   larger L needed.                                                        *)
(*                                                                            *)
(* Example C -- OC(2,3) at L=2 (uneven fibers):                              *)
(*   Tg=2, N=4, Tg^L=4. Sheet s=1 has uneven word fibers (2,0,0,2).        *)
(*   P_s concentrates on 2 of 4 endpoints. H = log 2. D = log 2.           *)
(*   eps <= sqrt(2 log 2) ~ 1.18. Combinatorial eps = 1 is tighter.         *)
(*                                                                            *)
(* Example D -- OC(2,N-1) at large L (asymptotic security):                  *)
(*   OC is transitive: the group acts on all N sheets.                       *)
(*   As L grows, the achievable permutations cover 'I_N more evenly,        *)
(*   so P_s converges to uniform. H -> log N, D -> 0, eps -> 0.             *)
(*   e.g., OC(2,2^64+1) at L=128: 2^128 >> 2^64. Secure.                   *)
(*   Transitive groups always converge; non-transitive groups (Star)         *)
(*   have an eps floor regardless of L.                                      *)
(*                                                                            *)
(* Security metric comparison:                                                *)
(*   var_dist (eps): statistical distance, eps = 2(N-|img_s|)/N upper bound *)
(*     Star(m) L=1: eps = 2(m+1)/(m+3) (rigidity_star_instance.v)           *)
(*     S5 L=1:      eps = 6/5          (rigidity_s5_instance.v)              *)
(*     OC(2,3) L=2: eps = 1            (rigidity_oc_instance.v)              *)
(*   entropy (H): information-theoretic leakage in bits                     *)
(*     H = log(Tg^L) - (1/Tg^L) sum c_x log c_x                            *)
(*     D = log N - H (leakage). var_dist <= sqrt(2*D) (Pinsker).            *)
(*   Both metrics derive from the same word fiber counts c_x.               *)
(*                                                                            *)
(* Theorems:                                                                  *)
(*   entropy_fdistmap_uniform_supp                                            *)
(*     H(fdistmap f (uniform_supp C)) = log|C| - (1/|C|) sum c log c        *)
(*     Closed-form entropy for pushforward of uniform distribution.          *)
(*   fiber_entropy_general    H = log|C| - (1/|C|) sum c log c  [weval_inj] *)
(*     Specialization to achievable fibers when word_eval is injective.      *)
(*   fiber_entropy_injective  H(P_s) = log(Tg^L)  [weval_inj + pe_inj]      *)
(*     All fibers have size 1. H = log of search space.                     *)
(*   fiber_entropy_perfect    H(P_s) = log N       [above + Tg^L = N]       *)
(*     Maximum entropy -- zero leakage.                                      *)
(*   fiber_entropy_gap        D(P_s || U_N) = log N - H(P_s)                *)
(*     Entropy deficit equals KL divergence.                                 *)
(*   var_dist_from_fiber_entropy                                              *)
(*     var_dist <= sqrt(2 * (log N - H))  [Pinsker bridge]                   *)
(*   security_witness_from_entropy                                            *)
(*     EntropyWitness -> ShuffleMarginalBound via Pinsker                    *)
(*                                                                            *)
(* Sections:                                                                  *)
(*   1. entropy_uniform_supp -- H(uniform_supp C) = log |C|                  *)
(*   2. entropy_fdistmap_uniform_supp -- H of pushforward through any map    *)
(*   3. fiber_entropy -- H of endpoint distribution + key lemmas             *)
(*   4. entropy_divergence -- D(P_s || U_N) = log N - H(P_s)                *)
(*   4b. entropy_var_dist_bridge -- Pinsker bridge: H -> var_dist            *)
(*   5. protocol_rvs -- Endpoint_RV random variable                          *)
(*   6. entropy_witness -- EntropyWitness record                              *)
(*   7. security_from_entropy -- EntropyWitness -> ShuffleMarginalBound       *)
(*   8. entropy_witness_injective -- constructor for pe_inj groups           *)
(*   9. joint_entropy -- T-party joint endpoint entropy + bounds             *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From mathcomp Require Import boolp reals.
From mathcomp Require Import reals exp.
From infotheo Require Import realType_ext realType_ln fdist proba variation_dist.
From infotheo Require Import divergence entropy pinsker entropy_convex.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj.
From pgg_smc Require Import pgg_collusion_bound.
From pgg_reconstruct Require Import algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Section 1: Entropy of uniform_supp                                        *)
(*                                                                            *)
(*  H(uniform_supp C) = log |C|.                                              *)
(*  Derivable from entropy_uniform via the fact that uniform_supp C is        *)
(*  the uniform distribution on |C| elements restricted to the ambient type.  *)
(******************************************************************************)

Section entropy_uniform_supp.

Context {R : realType}.
Variable A : finType.
Variable C : {set A}.
Hypothesis HC : (0 < #|C|)%N.

(** entropy_uniform_supp — Shannon entropy of a uniform-on-support distribution equals log |C|.
    Kind: helper.
    Why: provides the closed-form entropy value used by the entropy-gap security arguments.
    Used by: entropy_fdistmap_uniform_supp and security_witness_from_entropy.
*)
Lemma entropy_uniform_supp :
  `H (@fdist_uniform_supp R A C HC) = log #|C|%:R :> R.
Proof.
rewrite /entropy fdist_uniform_supp_restrict.
have -> : \sum_(t in C) (`U HC) t * log ((`U HC) t) =
          \sum_(t in C) #|C|%:R^-1 * log (#|C|%:R^-1 : R).
  apply: eq_bigr => i Hi. by rewrite fdist_uniform_supp_in.
rewrite big_const iter_addr addr0 logV; last by rewrite ltr0n.
rewrite -mulNrn mulrN opprK -mulrnAr -(mulr_natr (log _) #|C|) mulrCA.
by rewrite mulVf ?mulr1 // pnatr_eq0 -lt0n.
Qed.

End entropy_uniform_supp.

(******************************************************************************)
(*  Section 2: Entropy of pushforward through arbitrary map                   *)
(*                                                                            *)
(*  H(fdistmap f (uniform_supp C)) = log|C| - (1/|C|) sum_{y in img} c_y log c_y *)
(*  where c_y = |{a in C : f(a) = y}| is the fiber size at y.                *)
(*  Subsumes entropy_uniform_supp (f = id, all c_y = 1).                      *)
(******************************************************************************)

Section entropy_fdistmap_uniform_supp.

Context {R : realType}.
Variables (A B : finType).
Variable C : {set A}.
Hypothesis HC : (0 < #|C|)%N.
Variable f : A -> B.

Let img := f @: C.
Let fiber_at (b : B) := [set a in C | f a == b].

(** entropy_fdistmap_uniform_supp — entropy of pushforward-of-uniform-on-support expressed as log |C| minus a fiber-weighted correction.
    Kind: helper.
    Why: exposes the fiber-decomposition form of post-pushforward entropy needed for entropy-gap arguments.
    Used by: var_dist_from_fiber_entropy and security_witness_from_entropy.
*)
Lemma entropy_fdistmap_uniform_supp :
  `H (fdistmap f (@fdist_uniform_supp R A C HC)) =
  log #|C|%:R -
  #|C|%:R^-1 *
  \sum_(b in img) #|fiber_at b|%:R * log #|fiber_at b|%:R.
Proof.
rewrite /entropy.
set P := fdistmap f (`U HC).
have P0 : forall y, y \notin img -> P y = 0.
  move=> y Hy; rewrite /P fdistmapE big1 // => a.
  rewrite inE => /eqP Hfa; apply: fdist_uniform_supp_notin.
  apply/negP => aC; move/negP: Hy; apply; apply/imsetP; by exists a.
have Pval : forall y : B, P y = #|fiber_at y|%:R * #|C|%:R^-1.
  move=> y; rewrite /P fdistmapE.
  transitivity (\sum_(a in fiber_at y) (`U HC) a : R).
    rewrite (bigID (fun a => a \in C)) /=.
    rewrite [X in _ + X]big1 ?addr0; last first.
      by move=> a /andP [Ha HaC]; rewrite fdist_uniform_supp_notin.
    by apply: eq_bigl => a; rewrite /fiber_at !inE andbC.
  rewrite (eq_bigr (fun _ => #|C|%:R^-1 : R)); last first.
    by move=> a Ha; rewrite fdist_uniform_supp_in //;
       move: Ha; rewrite /fiber_at inE => /andP [].
  by rewrite big_const iter_addr addr0 -mulr_natl mulr1 mulrC -[LHS]mulr_natr.
have -> : \sum_(a in B) P a * log (P a) = \sum_(a in img) P a * log (P a).
  rewrite [LHS](bigID (fun a => a \in img)) /=.
  rewrite [X in _ + X]big1 ?addr0 //.
  by move=> b Hb; rewrite P0 ?mul0r.
have fiber_pos : forall b, b \in img -> (0 < #|fiber_at b|)%N.
  move=> b /imsetP [a aC ->]; apply/card_gt0P; exists a.
  by rewrite /fiber_at inE aC eqxx.
have C_pos : 0 < #|C|%:R :> R by rewrite ltr0n.
under eq_bigr do rewrite Pval.
under eq_bigr => b Hb do rewrite logDiv ?ltr0n ?fiber_pos //.
under eq_bigr do rewrite mulrBr.
rewrite big_split /= opprD sumrN opprK.
have Psum1 : \sum_(i in img) (P i) = 1.
  have := FDist.f1 P.
  rewrite (bigID (fun a => a \in img)) /=.
  rewrite [X in _ + X = _]big1; last by move=> b Hb; rewrite P0.
  by rewrite addr0.
have -> : \sum_(i in img) #|fiber_at i|%:R / #|C|%:R * log #|C|%:R =
          (\sum_(i in img) P i) * log #|C|%:R.
  by rewrite mulr_suml; apply: eq_bigr => b _; rewrite Pval mulrC.
rewrite Psum1 mul1r addrC; congr (log _ - _).
rewrite mulr_sumr; apply: eq_bigr => b _.
by set c := #|fiber_at b|%:R; set n := #|C|%:R; rewrite [c / n]mulrC -mulrA.
Qed.

End entropy_fdistmap_uniform_supp.

(******************************************************************************)
(*  Section 3: Fiber Entropy                                                  *)
(*                                                                            *)
(*  fiber_entropy s = H(fdistmap (sigma |-> sigma(s)) rho_from_words)         *)
(*  The Shannon entropy of the endpoint distribution at sheet s when the      *)
(*  protocol word is sampled uniformly. Works for ANY group described by       *)
(*  generators, not RAAG-specific.                                            *)
(*                                                                            *)
(*  Key lemmas:                                                               *)
(*  - fiber_entropy_general: when weval_inj holds (no pe_inj needed),         *)
(*    H(P_s) = log(Tg^L) - (Tg^L)^{-1} sum_{x in img} c_x log c_x.         *)
(*    Works for ALL groups with weval_inj. Subsumes fiber_entropy_injective.  *)
(*  - fiber_entropy_injective: when weval_inj AND perm_endpoint injective     *)
(*    on achievable(L), H(P_s) = log(Tg^L). The chain:                       *)
(*      weval_inj -> rho_from_words = uniform_supp(achievable)               *)
(*      pe_inj    -> fdistmap pe (uniform_supp A) = uniform_supp(pe(A))      *)
(*      => H = log |achievable| = log(Tg^L).                                 *)
(*    Applies to: Cyclic, Abelian/Disjoint, Monster.                          *)
(*  - fiber_entropy_perfect: when additionally Tg^L = N, H = log N           *)
(*    (maximum entropy = zero leakage). Applies to Disjoint at critical L,    *)
(*    Monster at L* = 67.                                                     *)
(******************************************************************************)

Section fiber_entropy.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

(* Fiber entropy at sheet s: H of the endpoint distribution.
   P_s(x) = Pr[sigma(s) = x] where sigma ~ rho_from_words (uniform over
   achievable permutations when weval_inj holds, uniform over all words
   otherwise). *)
Definition fiber_entropy (s : 'I_N) : R :=
  `H (fdistmap (fun sigma : {perm 'I_N} => sigma s)
               (rho_from_words (R:=R) L sigmas)).

(* General fiber entropy formula (works for ALL groups with weval_inj):
   H(P_s) = log(Tg^L) - (Tg^L)^{-1} sum_{x in img_s} c_x log c_x
   where c_x = |{sigma in achievable : sigma(s) = x}|.
   Injective case: all c_x in {0,1} -> sum = 0 -> H = log(Tg^L).
   Balanced case: all c_x = k -> sum = |img|*k*log k -> H = log|img|.
   Unbalanced: H < log|img| (additional loss from fiber unevenness). *)
Lemma fiber_entropy_general (s : 'I_N)
    (Hlfree : @weval_inj M L) :
  let img_s := (fun sigma : {perm 'I_N} => sigma s) @: @achievable M L in
  let fiber_s x := [set sigma in @achievable M L | sigma s == x] in
  fiber_entropy s =
  log (Tg ^ L)%:R -
  (Tg ^ L)%:R^-1 *
  \sum_(x in img_s) #|fiber_s x|%:R * log #|fiber_s x|%:R.
Proof.
move=> img_s fiber_s.
rewrite /fiber_entropy (rho_from_words_uniform_supp Hlfree).
rewrite entropy_fdistmap_uniform_supp.
have -> : #|@achievable M L| = (Tg ^ L)%N.
  by have -> : #|@achievable M L| = @search_space M L by [];
     exact: (weval_inj_search_space Hlfree).
by rewrite /img_s /fiber_s.
Qed.

(* When weval_inj AND perm_endpoint is injective on achievable(L):
   H(P_s) = log(Tg^L).
   Proof sketch: weval_inj -> rho_from_words = uniform_supp(achievable),
   pe_inj -> pushforward is uniform_supp(image), H = log|image| = log(Tg^L).
   Applies to: Cyclic (trivially), Abelian/Disjoint, Monster (axiom). *)
Lemma fiber_entropy_injective (s : 'I_N)
    (Hlfree : @weval_inj M L)
    (Hinj_s : {in @achievable M L &,
               injective (fun sigma : {perm 'I_N} => sigma s)}) :
  fiber_entropy s = log (Tg ^ L)%:R.
Proof.
rewrite /fiber_entropy (rho_from_words_uniform_supp Hlfree).
rewrite (fdistmap_uniform_supp_inj _ Hinj_s) entropy_uniform_supp.
congr (log _%:R).
rewrite card_in_imset //.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space.
Qed.

(* Perfect security: H(P_s) = log N (maximum entropy, zero leakage).
   Requires weval_inj + pe_inj + the saturation condition Tg^L = N.
   When Tg^L = N, the achievable permutations cover all N sheets
   injectively, so the endpoint distribution is uniform on 'I_N. *)
Lemma fiber_entropy_perfect (s : 'I_N)
    (Hlfree : @weval_inj M L)
    (Hinj_s : {in @achievable M L &,
               injective (fun sigma : {perm 'I_N} => sigma s)})
    (Hbal : (Tg ^ L = N)%N) :
  fiber_entropy s = log N%:R.
Proof. by rewrite fiber_entropy_injective // Hbal. Qed.

(* Upper bound: H(P_s) <= log N always holds (entropy_max). *)
Lemma fiber_entropy_le_logN (s : 'I_N) :
  fiber_entropy s <= log N%:R.
Proof.
rewrite /fiber_entropy.
have Hcard : #|'I_N| = N by rewrite card_ord.
have -> : log N%:R = log #|'I_N|%:R :> R by rewrite Hcard.
exact: entropy_max.
Qed.

End fiber_entropy.

(******************************************************************************)
(*  Section 4: Entropy-Divergence Identity                                    *)
(*                                                                            *)
(*  fiber_entropy_gap: D(P_s || U_N) = log N - H(P_s).                       *)
(*  Converts the entropy deficit into KL divergence (information leakage      *)
(*  in bits). When Q is uniform, D(P||Q) = log|support(Q)| - H(P), so        *)
(*  the gap directly measures how far P_s is from uniform.                    *)
(*                                                                            *)
(*  Combined with fiber_entropy_injective:                                    *)
(*    D = log N - log(Tg^L) = log(N / Tg^L) for pe_inj groups.              *)
(*  At L* where Tg^{L*} = N: D = 0 (perfect security).                      *)
(******************************************************************************)

Section entropy_divergence.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Let P_s (s : 'I_N) : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s)
           (rho_from_words (R:=R) L sigmas).

(* Fundamental identity: the entropy gap equals the KL divergence from
   the uniform distribution. This is the standard D(P||U) = log|X| - H(P)
   identity, specialized to the endpoint distribution P_s. *)
Lemma fiber_entropy_gap (s : 'I_N) :
  log N%:R - fiber_entropy (R:=R) L sigmas s =
  D(P_s s || fdist_uniform (card_ord N)).
Proof.
rewrite /fiber_entropy /entropy /div opprK.
have -> : log N%:R = \sum_(a in 'I_N) P_s s a * log N%:R.
  by rewrite -mulr_suml FDist.f1 mul1r.
rewrite -big_split /=.
apply: eq_bigr => a _.
rewrite addrC -mulrDr fdist_uniformE card_ord.
have [->|Hpos] := eqVneq (P_s s a) 0.
  by rewrite mul0r mul0r.
congr (_ * _).
have Hgt : (0 < P_s s a) by rewrite lt0r Hpos FDist.ge0.
rewrite logDiv ?Hgt ?invr_gt0 ?ltr0n //.
rewrite logV ?ltr0n //.
by rewrite opprK.
Qed.

End entropy_divergence.

(******************************************************************************)
(*  Section 4b: Entropy-to-var_dist bridge via Pinsker                        *)
(*                                                                            *)
(*  Connects entropy analysis to the var_dist-based ShuffleMarginalBound      *)
(*  via Pinsker's inequality: var_dist(P,Q) <= sqrt(2 * D(P||Q)).            *)
(*  Combined with fiber_entropy_gap: D = log N - H(P_s), this gives          *)
(*  var_dist <= sqrt(2 * (log N - H)).                                        *)
(*                                                                            *)
(*  This makes EntropyWitness useful: high entropy -> small var_dist ->       *)
(*  ShuffleMarginalBound -> coalition security via collusion_bound.           *)
(******************************************************************************)

Section entropy_var_dist_bridge.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Let P_s (s : 'I_N) : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s)
           (rho_from_words (R:=R) L sigmas).

(* Pinsker bridge: entropy bound -> var_dist bound.
   Combines fiber_entropy_gap (D = log N - H) with Pinsker's inequality
   (var_dist <= sqrt(2*D)) to get var_dist <= sqrt(2*(log N - H)). *)
(** var_dist_from_fiber_entropy — Pinsker-style TV bound derived from the fiber entropy gap.
    Kind: helper.
    Why: the entropy-to-TV bridge that Pinsker's inequality provides in the fiber-decomposition form.
    Used by: security_witness_from_entropy and downstream security-from-entropy consumers.
    Naming: five components record the direction of the conversion (var_dist FROM fiber_entropy); shortening loses the source/target distinction.
*)
Lemma var_dist_from_fiber_entropy (s : 'I_N) :
  var_dist (P_s s) (fdist_uniform (card_ord N)) <=
  Num.sqrt (2%:R * (log N%:R - fiber_entropy (R:=R) L sigmas s)).
Proof.
rewrite fiber_entropy_gap.
exact: (Pinsker_inequality_weak (dom_by_uniform (P_s s) (card_ord N))).
Qed.

End entropy_var_dist_bridge.

(******************************************************************************)
(*  Section 5: Protocol Random Variables                                      *)
(*                                                                            *)
(*  Endpoint_RV s : the random variable mapping a word w to the endpoint      *)
(*  that party at sheet s observes, i.e., endpoint(word_eval(w), s).          *)
(*  This bridges protocol-level word sampling with information-theoretic      *)
(*  entropy: H(Endpoint_RV s) = fiber_entropy s.                              *)
(******************************************************************************)

Section protocol_rvs.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Hypothesis Hlfree : @weval_inj M L.

Let card_word_L' : #|{: L.-tuple 'I_Tg}| = (Tg ^ L).-1.+1.
Proof. by rewrite card_tuple card_ord prednK // expn_gt0. Qed.

Let w_uniform : R.-fdist (L.-tuple 'I_Tg) :=
  fdist_uniform card_word_L'.

(* Endpoint_RV: the random variable "word w |-> endpoint(word_eval(w), s)".
   Defined over the word space L.-tuple 'I_Tg, with the uniform distribution
   w_uniform. Its entropy measures how much information a party at sheet s
   learns about the word from observing its endpoint. *)
Definition Endpoint_RV (s : 'I_N) : L.-tuple 'I_Tg -> 'I_N :=
  fun w => @endpoint M (@word_eval M L w) s.

(* The entropy of Endpoint_RV equals fiber_entropy: both compute
   H(fdistmap (sigma |-> sigma(s)) rho_from_words), just via different
   factorizations of the word -> permutation -> endpoint pipeline. *)
Lemma Endpoint_RV_entropy (s : 'I_N) :
  `H (fdistmap (Endpoint_RV s) w_uniform) =
  fiber_entropy (R:=R) L sigmas s.
Proof.
rewrite /fiber_entropy /rho_from_words fdistmap_comp.
congr (`H (fdistmap _ _)).
rewrite /w_uniform /word_uniform.
congr (fdist_uniform _).
exact: eq_irrelevance.
Qed.

End protocol_rvs.

(******************************************************************************)
(*  Section 6: EntropyWitness Record                                          *)
(*                                                                            *)
(*  Packages a min-entropy lower bound for ALL sheets into a single record.   *)
(*  Generic over M : MonodromyReprWithGeneratorType (not RAAG-specific).          *)
(*                                                                            *)
(*  Fields:                                                                    *)
(*    ew_L             : word length                                           *)
(*    ew_min_entropy   : lower bound H_min on entropy at every sheet           *)
(*    ew_rho_dist      : the permutation distribution used                     *)
(*    ew_entropy_bound : forall s, H_min <= H(fdistmap (sigma |-> sigma(s))    *)
(*                                           ew_rho_dist)                      *)
(******************************************************************************)

Section entropy_witness.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.

Record EntropyWitness := MkEntropyWitness {
  ew_L : nat;
  ew_min_entropy : R;
  ew_rho_dist : R.-fdist {perm 'I_N'.+1};
  ew_entropy_bound :
    forall (s : 'I_N'.+1),
    (ew_min_entropy <= `H (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s)
                                    ew_rho_dist))%O
}.

(* Construct EntropyWitness from a rho_dist + entropy bound -- ANY group.
   When used with a ShuffleMarginalBound, pass sw_L and sw_rho_dist
   directly. *)
Definition entropy_witness_from_rho
    (L : nat)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (H_min : R)
    (Hbound : forall s : 'I_N'.+1,
      (H_min <= `H (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s)
                             rho_dist))%O)
    : EntropyWitness :=
  @MkEntropyWitness L H_min rho_dist Hbound.

End entropy_witness.

Arguments MkEntropyWitness {R M}.
Arguments entropy_witness_from_rho {R M}.

(* Derive a ShuffleMarginalBound from an EntropyWitness via Pinsker.
   eps = sqrt(2 * (log N - ew_min_entropy)). *)
Section security_from_entropy.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.

(** security_witness_from_entropy — the marginal bound of an EntropyWitness
    via Pinsker.
    Kind: main.
    Why: materialises the entropy-to-TV conversion path (EntropyWitness ->
    Pinsker -> ShuffleMarginalBound) as a named construction.
*)
Definition security_witness_from_entropy
    (ew : EntropyWitness R M) : ShuffleMarginalBound R M.
Proof.
refine (@MkShuffleMarginalBound R M (ew_L ew)
  (Num.sqrt (2%:R * (log N'.+1%:R - ew_min_entropy ew)))
  (ew_rho_dist ew) _).
move=> s.
set P := fdistmap _ _.
apply: (Order.POrderTheory.le_trans
  (Pinsker_inequality_weak (dom_by_uniform P (card_ord N'.+1)))).
rewrite ler_wsqrtr // ler_pM2l // ?(ltr0n _ 2) //.
have Helog := @entropy_log_div R _ P _ (card_ord N'.+1).
rewrite card_ord in Helog.
have HD : D(P || fdist_uniform (card_ord N'.+1)) =
          log N'.+1%:R - `H P.
  by rewrite Helog opprB addrCA subrr addr0.
rewrite HD lerD2l lerNl opprK.
exact: ew_entropy_bound.
Defined.

End security_from_entropy.

(******************************************************************************)
(*  Section 7: Injective-perm_endpoint EntropyWitness constructor             *)
(*                                                                            *)
(*  entropy_witness_inj uses fiber_entropy_injective (pe_inj hypothesis).     *)
(*  For non-pe_inj groups, use fiber_entropy_general + entropy_witness_from_rho *)
(*  to construct EntropyWitness with the exact H from fiber counts.           *)
(*                                                                            *)
(*  Applicable to:                                                            *)
(*    Cyclic  (Tg=1, pe_inj trivially -- singleton achievable)                *)
(*    Abelian (Tg=2, N=4, pe_inj on achievable(1) by case analysis)          *)
(*    Monster (Tg=2, pe_inj on achievable(Lstar) by axiom)                   *)
(*  NOT applicable to: Star, S5, OC (pe_inj fails -- use var_dist instead)   *)
(******************************************************************************)

Section entropy_witness_injective.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

(* Construct EntropyWitness for pe_inj groups.
   Given weval_inj and perm_endpoint injectivity on achievable(L) for all s,
   sets ew_min_entropy = log(Tg^L) and ew_rho_dist = rho_from_words. *)
Definition entropy_witness_inj (L : nat)
    (Hlfree : @weval_inj M L)
    (Hinj_s : forall s : 'I_n'.+2,
      {in @achievable M L &,
       injective (fun sigma : {perm 'I_n'.+2} => sigma s)})
    : EntropyWitness R M.
Proof.
refine (@MkEntropyWitness R M L (log (m.+1 ^ L)%:R)
         (rho_from_words (R:=R) L sigmas) _).
move=> s.
rewrite -(fiber_entropy_injective (R:=R) (N'':=n') (sigmas:=sigmas) Hlfree
          (Hinj_s s)).
exact: Order.POrderTheory.lexx.
Defined.

End entropy_witness_injective.

(******************************************************************************)
(*  Section 9: Joint Entropy — Multi-Party Collusion Analysis                *)
(*                                                                            *)
(*  Extends single-party fiber_entropy to T-party joint entropy.              *)
(*  The joint endpoint distribution maps a word w to the T-tuple of          *)
(*  endpoints (σ_w(s_0), ..., σ_w(s_{T-1})).                                *)
(*                                                                            *)
(*  Key results:                                                               *)
(*    joint_endpoint_dist   : the T-fold joint distribution                   *)
(*    joint_fiber_entropy   : H of the joint distribution                     *)
(*    joint_entropy_le_log_words : H ≤ log(Tg^L) — at most Tg^L outcomes   *)
(*    joint_entropy_le_T_logN : H ≤ T * log N — trivial product bound       *)
(*    joint_entropy_single  : T=1 recovers fiber_entropy                     *)
(*    joint_entropy_full    : H = log(Tg^L) when weval_inj AND              *)
(*                            T-fold endpoint injectivity (both required)    *)
(*                                                                            *)
(*  Mathematical context:                                                     *)
(*    The joint entropy measures how much information T colluding parties    *)
(*    can extract from their combined observations. The bound H ≤ log(Tg^L) *)
(*    says the joint observation cannot extract more information than the    *)
(*    word itself contains. The bound H ≤ T * log N is the independence     *)
(*    upper bound (each party sees at most log N bits).                      *)
(*    When weval_inj holds AND the T-fold endpoint map is injective, the    *)
(*    joint distribution is uniform on Tg^L outcomes, giving maximum        *)
(*    entropy. Both conditions are required: weval_inj alone does not        *)
(*    guarantee joint injectivity (multiple words can produce the same       *)
(*    T-tuple of endpoints even if they produce distinct permutations).     *)
(******************************************************************************)

Section joint_entropy.

Context {R : realType}.
Variable N'' : nat.
Let N' := N''.+1.
Let N := N'.+1.

Variable m : nat.
Let Tg := m.+1.
Variable L : nat.
Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.

Variable T' : nat.
Let T := T'.+1.
Variable parties : T.-tuple 'I_N.

(* Joint endpoint extraction: given a permutation sigma, extract the
   T-tuple of endpoints at the party sheets. *)
Definition joint_endpoint (sigma : {perm 'I_N}) : T.-tuple 'I_N :=
  [tuple sigma (tnth parties i) | i < T].

(* Joint endpoint distribution: pushforward of rho_from_words through
   the joint endpoint extraction map. *)
Definition joint_endpoint_dist : R.-fdist (T.-tuple 'I_N) :=
  fdistmap joint_endpoint (rho_from_words (R:=R) L sigmas).

(* Joint fiber entropy: Shannon entropy of the joint distribution. *)
Definition joint_fiber_entropy : R := `H joint_endpoint_dist.

(* Upper bound: H(joint) <= log(Tg^L).
   The joint distribution is a pushforward of a distribution on Tg^L words,
   so its support has at most Tg^L elements. *)
(** joint_entropy_le_log_words — joint fiber entropy is bounded by log of the total word count.
    Kind: helper.
    Why: the joint distribution is a pushforward of a uniform on L-tuples, bounding its Shannon entropy.
    Used by: joint entropy bounds for multi-sheet adversaries.
    Naming: five components record "H(joint) <= log(words)" as a compound phrase; shortening collides with joint_entropy_le without the word-count qualifier.
*)
Lemma joint_entropy_le_log_words :
  joint_fiber_entropy <= log (Tg ^ L)%:R.
Proof.
rewrite /joint_fiber_entropy /joint_endpoint_dist /rho_from_words fdistmap_comp.
rewrite /word_uniform.
have HC : (0 < #|[set: L.-tuple 'I_Tg]|)%N by rewrite cardsT card_word_L.
have Hbridge : fdist_uniform (card_word_L m L) = @fdist_uniform_supp R _ _ HC.
  by apply: fdist_ext => x;
     rewrite fdist_uniformE fdist_uniform_supp_in ?inE // cardsT.
rewrite Hbridge entropy_fdistmap_uniform_supp.
rewrite cardsT card_word_L prednK ?expn_gt0 //.
change pgg_ngens'.+1 with Tg.
rewrite gerBl.
apply: mulr_ge0.
  by rewrite invr_ge0; exact: ler0n.
apply: sumr_ge0 => b /imsetP [a _ ->].
have Hfib_pos :
  (0 < #|[set a0 in [set: L.-tuple 'I_Tg]
        | (joint_endpoint \o @word_eval M L) a0
          == (joint_endpoint \o @word_eval M L) a]|)%N.
  by apply/card_gt0P; exists a; rewrite !inE eqxx.
apply: mulr_ge0; first exact: ler0n.
rewrite -[0]log1 ler_log; first by rewrite ler1n.
  by rewrite posrE ltr01.
by rewrite posrE ltr0n.
Qed.

(* Trivial upper bound: H(joint) <= T * log N.
   Each coordinate has entropy at most log N, and H(X_1,...,X_T) <= sum H(X_i)
   by subadditivity. *)
Lemma joint_entropy_le_T_logN :
  joint_fiber_entropy <= T%:R * log N%:R.
Proof.
rewrite /joint_fiber_entropy /joint_endpoint_dist.
have H1 := @entropy_max R _ (fdistmap joint_endpoint (rho_from_words (R:=R) L sigmas)).
apply: (Order.POrderTheory.le_trans H1).
by rewrite card_tuple card_ord -log_pow_natmul.
Qed.

(* Single-party consistency: when T = 1, joint_fiber_entropy reduces to
   fiber_entropy at the single party's sheet. *)
Lemma joint_entropy_single (HT1 : T' = 0) :
  joint_fiber_entropy =
  fiber_entropy (R:=R) L sigmas (tnth parties (Ordinal (ltn0Sn T'))).
Proof.
rewrite /joint_fiber_entropy /joint_endpoint_dist /fiber_entropy.
suff : forall (T' : nat) (parties : T'.+1.-tuple 'I_N), T' = 0 ->
  `H (fdistmap (fun sigma : {perm 'I_N} =>
    [tuple sigma (tnth parties i) | i < T'.+1])
    (rho_from_words (R:=R) L sigmas)) =
  `H (fdistmap (fun sigma : {perm 'I_N} =>
    sigma (tnth parties (Ordinal (ltn0Sn T'))))
    (rho_from_words (R:=R) L sigmas)).
  by move=> H; exact: H.
case=> // parties0 _.
set P := rho_from_words _ _.
set s := tnth parties0 ord0.
have -> : (fun sigma : {perm 'I_N} =>
  [tuple sigma (tnth parties0 i) | i < 1]) =
  (fun x : 'I_N => mktuple (fun _ : 'I_1 => x)) \o
  (fun sigma : {perm 'I_N} => sigma s).
  apply: boolp.funext => sigma /=.
  apply: eq_from_tnth => i.
  by rewrite tnth_mktuple tnth_mktuple (ord1 i).
rewrite -fdistmap_comp.
apply: entropy_fdistmap.
move=> x y Hxy.
have := congr1 (fun t => tnth t ord0) Hxy.
by rewrite tnth_mktuple tnth_mktuple.
Qed.

(* Maximum entropy: H = log(Tg^L) when weval_inj AND T-fold endpoint
   injectivity both hold.
   - weval_inj ensures rho_from_words = uniform on achievable (Tg^L elements)
   - T-fold injectivity ensures joint_endpoint is injective on achievable
   Both are required. Without T-fold injectivity, multiple achievable
   permutations can produce the same T-tuple of endpoints. *)
Lemma joint_entropy_full
    (Hlfree : @weval_inj M L)
    (Hjoint_inj : {in @achievable M L &,
                   injective joint_endpoint}) :
  joint_fiber_entropy = log (Tg ^ L)%:R.
Proof.
rewrite /joint_fiber_entropy /joint_endpoint_dist.
rewrite (rho_from_words_uniform_supp Hlfree).
rewrite (fdistmap_uniform_supp_inj _ Hjoint_inj).
rewrite entropy_uniform_supp.
congr (log _%:R).
rewrite card_in_imset //.
have -> : #|@achievable M L| = @search_space M L by [].
by rewrite weval_inj_search_space.
Qed.

End joint_entropy.
