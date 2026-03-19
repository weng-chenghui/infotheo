(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Entropy Security                                                       *)
(*                                                                            *)
(* Pipeline position:                                                         *)
(*   pgg_interface.v -- word_eval, achievable, endpoint, perm_endpoint        *)
(*   pgg_collusion_bound.v -- rho_from_words, var_dist bounds                 *)
(*   algebraic_rigidity.v -- SecurityWitness (fiber + endpoint_inj)           *)
(*   THIS FILE -- fiber_entropy, EntropyWitness, Pinsker bridge              *)
(*   pgg_security_solver.v -- check_perm_endpoint_inj, fiber_entropy_summary  *)
(*                                                                            *)
(* All definitions are generic over GeneratedMonodromyReprType.               *)
(*                                                                            *)
(* Key insight: var_dist and entropy are BOTH functions of the same fiber      *)
(* distribution. Given fiber counts c_x = |{s in achievable : s(s) = x}|:    *)
(*   var_dist = 2*(N - |{x : c_x > 0}|) / N    [image coverage]             *)
(*   H(P_s)   = log(Tg^L) - (1/Tg^L) sum c_x log(c_x)  [fiber unevenness]  *)
(* When perm_endpoint is injective: all c_x in {0,1}, both simplify.         *)
(*                                                                            *)
(* How PGG security works:                                                    *)
(*   The dealer samples word w uniformly from Tg^L possible L-tuples.        *)
(*   Each party i observes one coordinate: endpoint sigma_w(s_i), where      *)
(*   sigma_w = word_eval(w). The secret is ts_recon(coordinates) -- a value  *)
(*   computed from k endpoints by the threshold scheme (field element for     *)
(*   Shamir/RS, codeword for AG codes). Fewer than k coordinates reveal      *)
(*   nothing about the secret (privacy).                                     *)
(*                                                                            *)
(*   Security guarantee (collusion_bound, pgg_collusion_bound.v):            *)
(*     var_dist(adversary_marginal, uniform) <= eps + 2(T-1)/N               *)
(*   where adversary_marginal = distribution of unobserved party's           *)
(*   endpoint given the coalition's observations.                            *)
(*                                                                            *)
(*   eps depends on how close the per-sheet endpoint distribution is to      *)
(*   uniform. When eps ~ 0, observing endpoints reveals almost nothing       *)
(*   about the unobserved party's coordinate.                                *)
(*                                                                            *)
(*   Entropy measures the same closeness in bits:                            *)
(*     H(P_s) = entropy of endpoint distribution at sheet s                  *)
(*     D(P_s || U_N) = log N - H(P_s) = leakage in bits                    *)
(*     var_dist <= sqrt(2*D) (Pinsker, probability/pinsker.v)                *)
(*   So high entropy <-> small var_dist <-> low leakage.                     *)
(*                                                                            *)
(* Abbreviations:                                                             *)
(*   weval_inj = word-eval injective: distinct length-L words produce        *)
(*     distinct group elements (the group is L-free).                        *)
(*   pe_inj = perm_endpoint injective on achievable(L): sigma |-> sigma(s)   *)
(*     is injective, meaning every achievable perm maps s to a distinct      *)
(*     endpoint. All fibers have size 1.                                     *)
(*                                                                            *)
(* Example A -- Monster at L* = 67 (secure, pe_inj):                         *)
(*   Tg=2, N~10^20. weval_inj + pe_inj (axioms). Tg^L = 2^67 >= N.         *)
(*   fiber_entropy_injective -> H = log(Tg^L) = 67 log 2.                   *)
(*   fiber_entropy_perfect (Tg^L = N) -> H = log N. D = 0.                  *)
(*   (rigidity_monster_instance.v: monster_security_witness_Lstar)           *)
(*                                                                            *)
(* Example B -- Monster at L = 10 (quantified, pe_inj):                      *)
(*   Same axioms, but Tg^L = 2^10 = 1024 << N ~ 10^20.                      *)
(*   fiber_entropy_injective -> H = log 1024 = 10 log 2.                    *)
(*   fiber_entropy_gap -> D = log N - 10 log 2 ~ 56 bits.                   *)
(*   Endpoint narrows ~10^20 sheets to 1024 possibilities.                   *)
(*                                                                            *)
(* Example C -- OC(2,3) at L=2 (quantified, non-pe_inj):                    *)
(*   Tg=2, N=4, Tg^L=4=N. weval_inj (proved). pe_inj fails at s=1.        *)
(*   Sheets 0,2,3: fibers (1,1,1,1), pe_inj -> H = log 4 = log N. D = 0.  *)
(*   Sheet 1: fibers (2,0,0,2). fiber_entropy_general ->                     *)
(*     H = log 4 - (1/4)(2 log 2 + 2 log 2) = log 2. D = log 2 ~ 1 bit.  *)
(*   var_dist: eps = 2(4-2)/4 = 1 (rigidity_oc_instance.v).                 *)
(*                                                                            *)
(* Example D -- OC(2,N-1) at large L (secure, convergence):                  *)
(*   OC is transitive, so eps -> 0 as L grows (protocol summary Table 1).   *)
(*   For ANY N: Tg=2, take L such that 2^L >> N.                             *)
(*   weval_inj gives 2^L distinct achievable permutations on N sheets.       *)
(*   Each sheet has ~2^L/N achievable perms mapping to it (average).         *)
(*   fiber_entropy_general -> H ~ log N (correction term -> 0).              *)
(*   e.g., OC(2,2^64+1) at L=128: Tg^L=2^128 >> N~2^64. Secure.            *)
(*   pe_inj failure is a small-L phenomenon; transitive groups converge.    *)
(*   (Non-transitive groups like Star are stuck at eps floor regardless.)   *)
(*                                                                            *)
(* Security metric comparison:                                                *)
(*   var_dist (eps) : always computable, eps = 2(N-|img_s|)/N upper bound.  *)
(*     Star(m) L=1: eps = 2(m+1)/(m+3) (rigidity_star_instance.v)           *)
(*     S5 L=1:      eps = 6/5          (rigidity_s5_instance.v)              *)
(*     OC(2,3) L=2: eps = 1            (rigidity_oc_instance.v)              *)
(*   entropy (H) : always computable via fiber_entropy_general.              *)
(*     H = log(Tg^L) - (1/Tg^L) sum c_x log c_x.                           *)
(*     Leakage in bits: D = log N - H.                                      *)
(*   Both compute from the same fiber sizes c_x. var_dist gives             *)
(*   statistical distance; entropy gives information-theoretic bits.        *)
(*                                                                            *)
(* Theorems:                                                                  *)
(*   entropy_fdistmap_uniform_supp                                            *)
(*     H(fdistmap f (uniform_supp C)) = log|C| - (1/|C|) sum c log c        *)
(*     General formula for pushforward entropy. No injectivity needed.       *)
(*   fiber_entropy_general    H = log|C| - (1/|C|) sum c log c  [weval_inj] *)
(*     General formula for arbitrary fibers. Subsumes injective case.        *)
(*   fiber_entropy_injective  H(P_s) = log(Tg^L)  [weval_inj + pe_inj]      *)
(*     Pins entropy to log of search space. No fiber collisions.             *)
(*   fiber_entropy_perfect    H(P_s) = log N       [above + Tg^L = N]       *)
(*     Maximum entropy -- zero leakage.                                      *)
(*   fiber_entropy_gap        D(P_s || U_N) = log N - H(P_s)                *)
(*     Converts entropy deficit to KL divergence (leakage in bits).          *)
(*   var_dist_from_fiber_entropy                                              *)
(*     var_dist <= sqrt(2 * (log N - H))  [Pinsker bridge]                   *)
(*   security_witness_from_entropy                                            *)
(*     EntropyWitness -> SecurityWitness via Pinsker                         *)
(*                                                                            *)
(* Sections:                                                                  *)
(*   1. entropy_uniform_supp -- H(uniform_supp C) = log |C|                  *)
(*   2. entropy_fdistmap_uniform_supp -- H of pushforward through any map    *)
(*   3. fiber_entropy -- H of endpoint distribution + key lemmas             *)
(*   4. entropy_divergence -- D(P_s || U_N) = log N - H(P_s)                *)
(*   4b. entropy_var_dist_bridge -- Pinsker bridge: H -> var_dist            *)
(*   5. protocol_rvs -- Endpoint_RV random variable                          *)
(*   6. entropy_witness -- EntropyWitness record                              *)
(*   7. entropy_witness_injective -- constructor for pe_inj groups           *)
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
(*  Connects entropy analysis to the var_dist-based SecurityWitness           *)
(*  via Pinsker's inequality: var_dist(P,Q) <= sqrt(2 * D(P||Q)).            *)
(*  Combined with fiber_entropy_gap: D = log N - H(P_s), this gives          *)
(*  var_dist <= sqrt(2 * (log N - H)).                                        *)
(*                                                                            *)
(*  This makes EntropyWitness useful: high entropy -> small var_dist ->       *)
(*  SecurityWitness -> coalition security via collusion_bound.                *)
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
(*  Generic over M : GeneratedMonodromyReprType (not RAAG-specific).          *)
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
Variable M : GeneratedMonodromyReprType.
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
   When used with SecurityWitness, pass sw_L and sw_rho_dist directly. *)
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

(* Derive SecurityWitness from EntropyWitness via Pinsker.
   eps = sqrt(2 * (log N - ew_min_entropy)). *)
Section security_from_entropy.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Let N' := pgg_N' M.

Definition security_witness_from_entropy
    (ew : EntropyWitness R M) : SecurityWitness R M.
Proof.
refine (@MkSecurityWitness R M (ew_L ew)
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
