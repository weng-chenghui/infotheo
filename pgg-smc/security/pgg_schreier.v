(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Schreier Graph Spectral Infrastructure for PGG Security Convergence        *)
(*                                                                            *)
(* == Pipeline position ==                                                    *)
(*                                                                            *)
(*   pgg_interface.v -- word_eval, achievable, endpoint, perm_endpoint        *)
(*   pgg_collusion_bound.v -- rho_from_words, var_dist bounds                 *)
(*   algebraic_rigidity.v -- SecurityWitness (fiber + endpoint_inj)           *)
(*   pgg_entropy_security.v -- fiber_entropy, Pinsker bridge                  *)
(*   THIS FILE -- Schreier transition matrix, spectral gap, convergence rate  *)
(*   rigidity_*_instance.v -- per-family SchreierCertificate axioms           *)
(*                                                                            *)
(* == Why Schreier instead of Cayley? ==                                      *)
(*                                                                            *)
(* A Cayley-graph approach would bound endpoint convergence via the           *)
(* Cayley graph of G (|G| vertices), then projected to 'I_N using the        *)
(* data processing inequality (DPI, var_dist_fdistmap in pgg_collusion_bound) *)
(* (var_dist_fdistmap). This is unnecessarily loose:                          *)
(*   - The sqrt(|G|) prefactor is huge (Monster: sqrt(|G|) ~ 10^26)          *)
(*   - DPI discards all fiber/injectivity structure                           *)
(*   - The projection step is where tightness is lost                         *)
(*                                                                            *)
(* The Schreier graph of the action G -> Sym('I_N) works directly on 'I_N:   *)
(*   - N vertices (sheets) instead of |G| vertices (group elements)           *)
(*   - eps(L) <= sqrt(N) * (1 - gap_schreier)^L -- no DPI needed             *)
(*   - gap(Schreier) >= gap(Cayley) -- Schreier eigenvalues are a SUBSET     *)
(*     of Cayley eigenvalues (Ceccherini-Silberstein et al. 2008, Thm 5.5.3) *)
(*   - Prefactor improvement: sqrt(N) vs sqrt(|G|) (Monster: 10^10 vs 10^26) *)
(*                                                                            *)
(* The Schreier walk Q^L(s,x) = Pr[sigma_w(s) = x] holds directly --        *)
(* no need to go through G. The weval_inj hypothesis is dropped from the     *)
(* spectral bound (it was an artifact of going through the Cayley graph).    *)
(* weval_inj is still needed downstream for SecurityWitness construction.    *)
(*                                                                            *)
(* == Contents ==                                                             *)
(*                                                                            *)
(* Schreier graph transition matrix:                                          *)
(*   schreier_gen_count x y == #{i : sigma_i(x) = y}, generator count        *)
(*   schreier_transition == N x N row-stochastic matrix over R                *)
(*     Q(x,y) = schreier_gen_count(x,y) / Tg                                 *)
(*   schreier_transition_entry_ge0 == all entries are >= 0                    *)
(*   schreier_transition_stochastic == each row sums to 1 (proved)           *)
(*                                                                            *)
(* Spectral gap:                                                              *)
(*   spectral_gap lam == 1 - lam, distance of second eigenvalue from 1       *)
(*                                                                            *)
(* Schreier certificate (axiom pattern for per-family instantiation):         *)
(*   SchreierCertificate R m n' sigmas == record packaging:                   *)
(*     sc_lambda_gap   : spectral gap value (0 < gap <= 1)                    *)
(*     sc_convergence  : var_dist <= sqrt(N) * (1 - gap)^L for all L, s      *)
(*       NOTE: no weval_inj hypothesis -- Schreier walk convergence is a      *)
(*       property of the Markov chain, independent of word-eval injectivity   *)
(*   convergence_rate sc == 1 - sc_lambda_gap sc, decay factor per step       *)
(*   schreier_epsilon sc L == sqrt(N) * (1-gap)^L, the epsilon bound         *)
(*   security_witness_schreier sc L == SecurityWitness from certificate       *)
(*   schreier_epsilon_decreasing == eps(L2) <= eps(L1) when L1 <= L2         *)
(*   security_monotone == var_dist at L2 bounded by eps(L1) when L1 <= L2    *)
(*                                                                            *)
(* Bridge to rho_from_words:                                                  *)
(*   schreier_walk_eq_endpoint == Q^L(s,x) = Pr[sigma_w(s) = x] (axiom)     *)
(*     The Schreier walk starting at sheet s gives the same distribution      *)
(*     as the endpoint distribution from rho_from_words.                      *)
(*                                                                            *)
(* == Relationship to Cayley graph ==                                         *)
(*                                                                            *)
(* The Schreier graph eigenvalues are a subset of the Cayley graph            *)
(* eigenvalues (Ceccherini-Silberstein, Scarabotti, Tolli 2008, Ch. 5,       *)
(* Theorem 5.5.3). Specifically, the Schreier graph of G acting on G/H       *)
(* has eigenvalues corresponding to the representations of G containing       *)
(* H-fixed vectors (the permutation representation decomposes as a           *)
(* subrepresentation of the regular representation).                          *)
(*                                                                            *)
(* Consequence: gap(Schreier) >= gap(Cayley). The second-largest              *)
(* eigenvalue of the Schreier graph is at most the second-largest             *)
(* eigenvalue of the Cayley graph (since fewer eigenvalues to maximize over). *)
(*                                                                            *)
(* References:                                                                *)
(*   - Ceccherini-Silberstein, Scarabotti, Tolli (2008),                      *)
(*     "Harmonic Analysis on Finite Groups," Ch. 5, Thm 5.5.3               *)
(*   - Lubotzky (2012), "Expander Graphs in Pure and Applied Mathematics,"   *)
(*     Theorem 4.2 — spectral gap comparison for transitive actions           *)
(*   - Kassabov-Lubotzky-Nikolov (2006), "Finite simple groups as            *)
(*     expanders" — expander property transfers to transitive actions         *)
(*                                                                            *)
(* == Literature ==                                                           *)
(*                                                                            *)
(* - Diaconis (1988), Group Representations in Probability and Statistics     *)
(*     Ch. 3B Proposition 2: upper bound lemma (sqrt|Omega| prefactor)       *)
(* - Saloff-Coste (1997), Lectures on Finite Markov Chains, Theorem 2.6     *)
(*     L2 to total variation conversion for reversible chains                *)
(* - Caputo-Liggett-Richthammer (2010), proof of Aldous' spectral gap        *)
(*     conjecture: transposition Cayley graphs on S_n, gap = 1/C(n,2)       *)
(* - Kassabov-Lubotzky-Nikolov (2006), finite simple groups are expanders    *)
(*     All non-abelian finite simple groups have uniformly bounded gap        *)
(* - Chung (1997), Spectral Graph Theory                                     *)
(*     Star graph spectrum, eigenvalues of specific Cayley graphs            *)
(*                                                                            *)
(* == Card Shuffle Interpretation ==                                          *)
(*                                                                            *)
(* The Schreier walk models multi-round card game shuffling:                  *)
(*   - N sheets = N card positions in a deck                                  *)
(*   - Generator sigma_i = one shuffle type (riffle, cut, transposition)      *)
(*   - Word of length L = L consecutive shuffles applied to the deck          *)
(*   - Q^L(s,x) = Pr[card at position s ends at position x after L shuffles] *)
(*                                                                            *)
(* Diaconis (1988) proved the upper bound lemma for single-observer fairness. *)
(* Diaconis-Bayer (1992) applied it to riffle shuffles: 7 shuffles suffice    *)
(* for a 52-card deck. PGG generalizes this in three ways:                    *)
(*   1. Schreier graph (N vertices) replaces Cayley graph (|G| vertices)      *)
(*   2. k-coalition resistance (pgg_collusion_bound.v): not just 1 observer   *)
(*   3. Any permutation group with generators (not just riffle shuffles)      *)
(*                                                                            *)
(* Multi-shuffle card protocols (den Boer 1989, Mizuki-Sone 2009) are the     *)
(* standard model in card-based cryptography (1989-2019). Shinagawa-Nuida     *)
(* (2019) proved a single shuffle suffices at the cost of more cards.         *)
(* PGG's spectral analysis applies to the multi-shuffle regime, answering:    *)
(* "How many shuffles are needed for k-coalition fairness?"                   *)
(*                                                                            *)
(* Closest prior work on adversarial shuffle analysis:                        *)
(*   Lorek-Kulis-Zagorski (2017), "Leakage-Resilient Riffle Shuffle"          *)
(*   (different adversary model: leaked random bits vs dealt card hands)       *)
(*                                                                            *)
(* The orbit-fiber connection: card protocols use orbit analysis (exact        *)
(* security via orbit-stabilizer theorem when mu = uniform on G). PGG uses    *)
(* fiber analysis (approximate security via Schreier spectral convergence     *)
(* when mu_L = random walk distribution). The orbit-stabilizer theorem is     *)
(* the L -> infinity limit of the spectral convergence analysis.              *)
(*                                                                            *)
(* References:                                                                *)
(*   - Diaconis-Bayer (1992), "Trailing the Dovetail Shuffle to its Lair,"    *)
(*     Annals of Applied Probability                                          *)
(*   - Lorek-Kulis-Zagorski (2017), "Leakage-Resilient Riffle Shuffle," LNCS  *)
(*   - den Boer (1989), "The Five Card Trick," EUROCRYPT                      *)
(*   - Shinagawa-Nuida (2019), "A Single Shuffle Is Enough," DAM             *)
(*   - Dvorak-Koucky (2021), "Barrington Plays Cards," STACS                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import matrix.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj
                            pgg_collusion_bound.
From pgg_reconstruct Require Import algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     Section 1: Schreier Graph Transition Matrix                            *)
(******************************************************************************)

Section schreier_transition.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.

(* Count how many generators map x to y: #{i : sigma_i(x) = y} *)
Definition schreier_gen_count (x y : 'I_N) : nat :=
  #|[set i : 'I_Tg | tnth sigmas i x == y]|.

(* The transition matrix: Q(x,y) = schreier_gen_count(x,y) / Tg *)
Definition schreier_transition : 'M[R]_(N, N) :=
  \matrix_(i, j) ((schreier_gen_count i j)%:R / Tg%:R).

(* All entries are non-negative *)
Lemma schreier_transition_entry_ge0 (i j : 'I_N) :
  0 <= schreier_transition i j.
Proof.
rewrite mxE; apply: divr_ge0; first by rewrite ler0n.
by rewrite ler0n.
Qed.

(* Each row sums to 1 (row-stochastic).
   Proof: for each generator sigma_k and sheet x, there is exactly one y
   such that sigma_k(x) = y (namely y = sigma_k(x)). So the total
   count across all y is Tg. *)
Lemma schreier_transition_stochastic (i : 'I_N) :
  \sum_j schreier_transition i j = 1.
Proof.
rewrite /schreier_transition.
under eq_bigr do rewrite mxE.
rewrite -mulr_suml /schreier_gen_count.
have -> : \sum_(j : 'I_N)
    #|[set k : 'I_Tg | tnth sigmas k i == j]|%:R
  = Tg%:R :> R.
  rewrite -natr_sum; congr _%:R.
  under eq_bigr do rewrite -sum1dep_card.
  rewrite (exchange_big_dep predT) //=.
  rewrite -[RHS]card_ord -sum1_card.
  apply: eq_bigr => k _.
  rewrite sum1dep_card.
  rewrite (_ : [set _ | _] = [set tnth sigmas k i]); first by rewrite cards1.
  apply/setP => x; rewrite !inE.
  by apply/eqP/eqP => [-> | ->].
by rewrite divff // pnatr_eq0.
Qed.

End schreier_transition.

(******************************************************************************)
(*     Section 2: Spectral Gap Definition                                     *)
(*                                                                            *)
(* The spectral gap of the Schreier transition matrix governs the mixing      *)
(* rate. We define it as 1 - lambda where lambda is the second-largest        *)
(* eigenvalue modulus. The definition is parameterized by the bound value;    *)
(* each instance provides its own bound backed by literature.                 *)
(******************************************************************************)

Section spectral_gap_def.

Variable R : realType.

(* The spectral gap: 1 - lam, where lam bounds non-trivial eigenvalues *)
Definition spectral_gap (lam : R) : R := 1 - lam.

End spectral_gap_def.

(******************************************************************************)
(*     Section 3: Schreier Certificate                                        *)
(*                                                                            *)
(* A SchreierCertificate packages the spectral gap value and the convergence  *)
(* bound for a specific group action (given by sigmas on 'I_N). The          *)
(* convergence bound is axiomatized per family (same pattern as the old       *)
(* SpectralCertificate), with mathematical justification from the literature. *)
(*                                                                            *)
(* Key difference from SpectralCertificate:                                   *)
(*   - Prefactor is sqrt(N), not sqrt(|G|)                                    *)
(*   - No weval_inj hypothesis in sc_convergence                              *)
(*   - State space is 'I_N directly (Schreier graph), not G (Cayley graph)   *)
(*                                                                            *)
(* The standard upper bound lemma (Diaconis 1988, Ch. 3B Proposition 2):     *)
(*   d_TV(Q^L(s, .), uniform_N) <= sqrt(N) * (1 - lambda_gap)^L             *)
(* where Q is the Schreier transition matrix and lambda_gap is its spectral  *)
(* gap. This requires the chain to be doubly stochastic (uniform stationary  *)
(* distribution), which holds for symmetric generator sets (S = S^{-1}).     *)
(* Each instance axiomatizes the bound and justifies it per-family.          *)
(*                                                                            *)
(* Per-family axioms (backed by cited mathematical results):                  *)
(*   Monster: Kassabov-Lubotzky-Nikolov 2006 (finite simple groups are       *)
(*     expanders). Expander property transfers to transitive Schreier graphs. *)
(*   Star(m): Chung 1997, Spectral Graph Theory. Star graph St(m+2) has      *)
(*     known eigenvalues; lambda_gap = 1/(m+1).                               *)
(*   OC(k,p): explicit computation of Schreier graph spectrum.               *)
(******************************************************************************)

Section schreier_certificate.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.
Let M := Gen_PGGTypes sigmas.
Let G := pgg_G M.

(* Schreier certificate: axiomatized spectral gap + convergence bound *)
Record SchreierCertificate := MkSchreierCertificate {
  (* The spectral gap value lambda_gap in (0, 1] *)
  sc_lambda_gap : R ;
  sc_lambda_pos : 0 < sc_lambda_gap ;
  sc_lambda_le1 : sc_lambda_gap <= 1 ;

  (* The convergence bound: var_dist at each sheet bounded by
     sqrt(N) * (1 - lambda_gap)^L.

     NOTE: no weval_inj hypothesis. The Schreier walk convergence
     Q^L(s, .) -> uniform is a property of the Markov chain on 'I_N,
     independent of word-eval injectivity on the group G. The LHS still
     uses fdistmap through rho_from_words because that IS the endpoint
     distribution (the bridge lemma establishes the equality).

     Mathematical source:
       Diaconis (1988), Ch. 3B Proposition 2 (upper bound lemma)
       Saloff-Coste (1997), Theorem 2.6 (L2 to TV conversion)
     Applied to the Schreier graph (N vertices) instead of the
     Cayley graph (|G| vertices), giving prefactor sqrt(N). *)
  sc_convergence : forall (L : nat) (s : 'I_N),
    var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                       (rho_from_words L sigmas))
             (fdist_uniform (card_ord N))
    <= Num.sqrt (N%:R) * (1 - sc_lambda_gap) ^+ L
}.

(* The convergence rate: 1 - lambda_gap, in [0, 1) *)
Definition convergence_rate (sc : SchreierCertificate) : R :=
  1 - sc_lambda_gap sc.

Lemma convergence_rate_ge0 (sc : SchreierCertificate) :
  0 <= convergence_rate sc.
Proof.
rewrite /convergence_rate subr_ge0.
exact: (sc_lambda_le1 sc).
Qed.

Lemma convergence_rate_lt1 (sc : SchreierCertificate) :
  convergence_rate sc < 1.
Proof.
rewrite /convergence_rate ltrBlDr addrC -ltrBlDr subrr.
exact: (sc_lambda_pos sc).
Qed.

(* SecurityWitness from Schreier certificate at any L.
   NOTE: weval_inj IS needed here -- it is required by SecurityWitness
   (to ensure rho_from_words is a valid distribution over achievable
   permutations). The Schreier spectral bound itself doesn't need it,
   but the downstream SecurityWitness construction does. *)
Definition security_witness_schreier (sc : SchreierCertificate)
    (L : nat) (Hlfree : @weval_inj M L) : SecurityWitness R M :=
  @MkSecurityWitness R M L
    (Num.sqrt (N%:R) * (1 - sc_lambda_gap sc) ^+ L)
    (rho_from_words L sigmas)
    (sc_convergence sc L).

(* Epsilon from Schreier certificate *)
Definition schreier_epsilon (sc : SchreierCertificate) (L : nat) : R :=
  Num.sqrt (N%:R) * (1 - sc_lambda_gap sc) ^+ L.

(* Epsilon is non-negative *)
Lemma schreier_epsilon_ge0 (sc : SchreierCertificate) (L : nat) :
  0 <= schreier_epsilon sc L.
Proof.
apply: mulr_ge0; first exact: sqrtr_ge0.
apply: exprn_ge0.
exact: convergence_rate_ge0.
Qed.

(* The UPPER BOUND schreier_epsilon is monotonically decreasing in L.
   sqrt(N) * r^L2 <= sqrt(N) * r^L1 when 0 <= r < 1, L1 <= L2.
   Follows from r^(a+b) = r^a * r^b and r^b <= 1 for 0 <= r <= 1.

   IMPORTANT: the actual var_dist (exact variational distance) is NOT
   monotonic in L. For example, with transposition generators, at L=2
   the identity enters the achievable set (sigma^2 = id), concentrating
   mass on the diagonal and spiking var_dist above its L=1 value:
     exact var_dist: 0.8  1.2  0.6  0.3  0.1  ...  (non-monotone)
     spectral bound: 3.0  2.4  1.9  1.5  1.2  ...  (monotone envelope)
   This lemma is about the envelope, not the exact value. The envelope
   is eventually tight (both converge to 0 geometrically). *)
Lemma schreier_epsilon_decreasing (sc : SchreierCertificate) (L1 L2 : nat) :
  (L1 <= L2)%N -> schreier_epsilon sc L2 <= schreier_epsilon sc L1.
Proof.
move=> HL; rewrite /schreier_epsilon.
apply: ler_wpM2l; first exact: sqrtr_ge0.
rewrite -(subnK HL) exprD.
apply: ler_piMl.
- by apply: exprn_ge0; exact: convergence_rate_ge0.
- apply: exprn_ile1; first exact: convergence_rate_ge0.
  rewrite /convergence_rate lerBlDr lerDl.
  exact: Order.POrderTheory.ltW (sc_lambda_pos sc).
Qed.

(* Monotone security: if secure at L1, at least as secure at L2 >= L1 *)
Lemma security_monotone (sc : SchreierCertificate)
    (L1 L2 : nat)
    (HL : (L1 <= L2)%N) :
  forall (s : 'I_N),
  var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                     (rho_from_words L2 sigmas))
           (fdist_uniform (card_ord N))
  <= schreier_epsilon sc L1.
Proof.
move=> s.
apply: (Order.POrderTheory.le_trans (sc_convergence sc L2 s)).
exact: schreier_epsilon_decreasing.
Qed.

End schreier_certificate.

Arguments SchreierCertificate R m n' sigmas : clear implicits.
Arguments MkSchreierCertificate {R m n' sigmas}.

(******************************************************************************)
(*     Section 4: Bridge — Schreier Walk and Endpoint Distribution            *)
(*                                                                            *)
(* The L-step random walk on the Schreier graph starting from sheet s         *)
(* produces a random sheet y = sigma_w(s) where w is a uniform L-word         *)
(* over the generators:                                                       *)
(*   Q^L(s, y) = Pr[sigma_w(s) = y]   where w ~ Uniform(Tg^L)              *)
(*                                                                            *)
(* The LHS is a matrix power on an N x N matrix; the RHS is the endpoint     *)
(* distribution from rho_from_words. The equality holds by definition of      *)
(* the Schreier walk: each step applies a uniformly random generator to       *)
(* the current sheet, which is exactly what word_eval does coordinate-wise.   *)
(*                                                                            *)
(* Note: this does NOT require weval_inj. The Schreier walk is well-defined  *)
(* regardless of whether different words produce the same group element.      *)
(******************************************************************************)

Section schreier_endpoint_bridge.

Variable R : realType.
Variable m n' : nat.
Let Tg := m.+1.
Let N := n'.+2.

Variable sigmas : Tg.-tuple {perm 'I_N}.

(* Bridge: the Schreier matrix power Q^L starting at sheet s gives the
   same distribution as the endpoint distribution from rho_from_words.

   Formally: for all sheets s, x in 'I_N,
     (schreier_transition^+L)_{s, x} = fdistmap (sigma |-> sigma(s)) (rho_from_words L) (x)

   Both sides operate on the same state space 'I_N, so no projection
   through G is needed (unlike a Cayley-graph approach which would
   require DPI to go from |G| vertices down to N).

   Axiomatized because the proof requires matrix-distribution
   correspondence infrastructure (matrix power = convolution power of
   the step distribution, then induction on L). Standard result;
   see Diaconis 1988, Chapter 3A. *)
Axiom schreier_walk_eq_endpoint : forall (L : nat)
    (s x : 'I_N),
  (schreier_transition R sigmas ^+ L) s x =
  fdistmap (fun sigma : {perm 'I_N} => sigma s)
           (@rho_from_words R _ m L sigmas) x.

End schreier_endpoint_bridge.

(******************************************************************************)
(*     Section 5: Relationship to Cayley Graph (Documentation)               *)
(*                                                                            *)
(* The Schreier graph eigenvalues are a subset of the Cayley graph            *)
(* eigenvalues. This means:                                                   *)
(*   gap(Schreier) >= gap(Cayley)                                             *)
(* (fewer eigenvalues to maximize over, so the second-largest is at most      *)
(* as large). Combined with the smaller prefactor (sqrt(N) vs sqrt(|G|)),    *)
(* the Schreier bound is strictly tighter than the Cayley bound.             *)
(*                                                                            *)
(* Mathematical justification:                                                *)
(* Let pi be the permutation representation of G on 'I_N = G/H. Then        *)
(* pi decomposes into irreducibles that are a SUBSET of those appearing      *)
(* in the regular representation (which governs the Cayley graph). The       *)
(* eigenvalues of the Schreier transition matrix are exactly the             *)
(* eigenvalues of the Cayley transition matrix restricted to this subset     *)
(* of representations.                                                        *)
(*                                                                            *)
(* References:                                                                *)
(*   - Ceccherini-Silberstein, Scarabotti, Tolli (2008),                      *)
(*     "Harmonic Analysis on Finite Groups," Theorem 5.5.3                   *)
(*   - Lubotzky (2012), "Expander Graphs in Pure and Applied Mathematics,"   *)
(*     Theorem 4.2                                                            *)
(*   - Kassabov-Lubotzky-Nikolov (2006) — the expander property of finite    *)
(*     simple groups transfers to ALL transitive actions, not just the        *)
(*     regular representation                                                 *)
(*                                                                            *)
(* No code is needed here — the SchreierCertificate record axiomatizes       *)
(* the bound per instance, and the mathematical justification is per-family. *)
(******************************************************************************)
