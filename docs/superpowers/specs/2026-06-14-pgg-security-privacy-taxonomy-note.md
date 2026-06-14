# PGG security and privacy analyses: a full taxonomy note

Date: 2026-06-14
Scope: den Boer, Kim, S5, S5xS5 (the four in-scope instances). Every fact below is
quoted from the built codebase with file:line. Axiom footprints were checked with
Print Assumptions.

## 0. Orientation: four different security notions

These instances carry up to four distinct security or privacy properties. They are
easy to conflate because they all involve a random permutation, but they have
different observables, different distributions, and different theorems.

1. **Correctness.** The verifier reconstructs the intended secret from the dealt
   shares. Quantified over the cut, holds for every cut. Operational (runs the
   interpreter). This is the trace bridge.
2. **Anonymity / mixing.** The applied shuffle is close to uniform, measured by
   variation distance, bounded by the spectral gap of a random walk on the group.
   Distributional over the dealer's random word. Abstract (no interpreter).
3. **Threshold privacy.** Fewer than k of the shares are independent of the secret.
   Standard secret-sharing privacy. Abstract.
4. **Input leakage.** The verifier's partial view leaks nothing about the individual
   inputs beyond the computed output, measured by conditional mutual information or
   per-view Shannon mutual information. Distributional over the cut. Abstract.

A fifth axis is **operational vs abstract**. "Operational" means the statement is
about the executed interpreter trace. "Abstract" means the statement is about the
permuted layout or the share distribution directly, assuming the permutation acts,
without running the interpreter. Today only correctness is operational. Anonymity,
threshold privacy, and input leakage are all abstract.

## 1. Framework records

In `reconstruct/algebraic_rigidity.v`, the anonymity observable is always
`var_dist (fdistmap (fun sigma => sigma s) rho_dist) (fdist_uniform (card_ord N))`,
the variation distance between the law of the endpoint of sheet `s` under the random
permutation and the uniform law, for every sheet `s : 'I_N`.

- `SecurityWitness` (`:147`): fields `sw_L` (word length), `sw_bound_eps` (the eps),
  `sw_rho_dist` (the distribution), `sw_bound` (`:151`, the `var_dist <= sw_bound_eps`
  inequality for all `s`), optional `sw_exact` and `sw_asymptotic`.
- `SecurityExact` (`:90`): exact equality `var_dist ... = se_eps` for all `s`.
- `SecurityAsymptotic` (`:122`): a spectral gap `sa_spectral_gap`, a floor
  `sa_eps_inf`, and `sa_convergence` (`:129`):
  `var_dist (... (sa_rho_L L)) uniform <= sa_eps_inf + sqrt(N) * (1 - gap)^L`.
- `SecurityProfile` (`:475`): a witness plus a turning length and a nontriviality
  certificate `sw_bound_eps < 2`.

In `protocol/pgg_monodromy_profile.v`, a `MonodromyProfile` exposes three guarantees:

- `run_anonymous` (`:105`) = `sw_bound (mp_security mp)`: for all `s`,
  `var_dist(law of sigma s, uniform) <= run_eps`, where `run_eps = sw_bound_eps`.
- `run_private` (`:110`) = `ts_private (rp_scheme plug)`: the threshold privacy below.
- `run_recovers` (`:116`): `run_recover (ts_encode (rp_scheme plug) s) = s`, the
  scheme-level correctness, via `ts_correct (ts_encode_valid ...)`.

In `reconstruct/pgg_sharing_framework.v`, the `ThresholdScheme` record (`:47`) carries
`ts_correct` (`:53`, any valid sharing reconstructs the secret), `ts_private` (`:56`,
for any coalition `C` with `#|C| < ts_k`, any two secrets are matchable on `C` by valid
sharings, i.e. perfect privacy below k), and `ts_encode_valid` (`:63`).

## 2. den Boer (C5, one cyclic cut, secret = AND of two bits)

### 2.1 Correctness (operational, trace bridge)
`den_boer_run_recovers (a b w0) (w0 \in pgg_G FiveCardKim_M)`: the executed verifier
endpoints reconstruct `a && b`, for any cut `w0` in C5. Qed, axiom-free beyond the
three standard boolp axioms. The run is parametric over the cut.

### 2.2 Anonymity (abstract): perfect
`den_boer_perfect` (`den_boer_profile.v:86`): `sw_bound_eps (mp_security (den_boer_profile R)) = 0`.
den Boer is the eps=0, L=1 member of the Kim family (`den_boer_profile := five_card_profile 0 ... 1`).
The bound `sqrt 5 * kim_lambda2 ^+ 1` collapses because `kim_lambda2 0 = 0`
(`kim_security_at_zero`). So one uniform cut on C5 is perfectly uniform: variation
distance exactly 0. `den_boer_run_k` (`:94`) = 2 (threshold k).

### 2.3 Input leakage (abstract): perfect, and the full ramp
`den_boer_input_private` (`den_boer_encoding.v:343`):
`cond_mutual_info (p_[% Inputs, ViewA A, Secret]) = 0` for any position list `A`. The
conditional mutual information of the inputs and the view given the secret is zero, so
the view leaks nothing about the inputs beyond the AND. Proved via `den_boer_cinde`
(`:227`, conditional independence) which reduces to `den_boer_view_count_eq` (`:143`,
equal-output inputs deal equal-count views) and the orbit fact `den_boer_orbit` (`:44`,
the three `a&&b=false` inputs are one cyclic rotation orbit). `den_boer_cinde` is
"Closed under the global context" (zero axioms).

The quantitative ramp is in `five_card_leakage.v` (uniform prior on 20 outcomes,
`Secret = a && b`, `H_secret = 2 - (3/4) log 3` bits, all Qed, only boolp axioms):

| k positions | result | mutual info `I(Secret; ViewA A)` |
|---|---|---|
| {0} | `leak_k1` (`:245`) | 0 |
| {0,1} adjacent | `leak_k2_adj` (`:317`) | 27/10 - (1/4)log5 - (7/10)log7 |
| {0,2} distance-2 | `leak_k2_dist2` (`:383`) | 5/2 - (3/20)log3 - (1/2)log5 - (7/20)log7 |
| {0,1,2} | `leak_k3` (`:448`) | 6/5 - (9/20)log3 |
| {0,1,2,3} | `leak_k4` (`:527`) | 2 - (3/4)log3 = H(Secret) |
| all five | `leak_k5` (`:546`) | 2 - (3/4)log3 = H(Secret) |

One card leaks nothing. Two cards already leak, and adjacent vs distance-2 leak
different amounts. Four cards already reveal the full secret entropy. The load-bearing
lemma is `condent_ratio` (`:217`), the per-view binary entropy of the true/false fibre
ratio, with closed-form `binent_*` values closed by `lra`.

## 3. Kim (C5, biased cyclic cut, multi-round)

### 3.1 Correctness (operational)
`kim_run_recovers`: same as den Boer, since Kim shares `FiveCardKim_M` and the layout.
Qed, axiom-free beyond boolp.

### 3.2 Anonymity / mixing (abstract): biased spectral gap, L rounds
The biased cut puts weight `1/5 - eps` on the identity and `1/5 + eps/4` on each
nontrivial rotation (`kim_weight_fun` `five_card_kim.v:158`). The second eigenvalue is
`kim_lambda2 = (5/4)|eps|` (`:370`) and the spectral gap is `1 - (5/4)|eps|` (`:396`).

- `kim_spectral_convergence` (`:420`):
  `var_dist (endpoint_dist_weighted L fc_kim_sigmas W s) uniform <= sqrt(5) * kim_lambda2 ^+ L`.
- `kim_var_dist_exact` (`:466`): the exact value `(8/5) * kim_lambda2 ^+ L`.
- `fc_kim_asymptotic` (`:492`): a `SecurityAsymptotic` with gap `kim_spectral_gap`.
- `fc_kim_security_witness (L)` (`:505`): the witness `five_card_profile` consumes.
- `kim_security_at_zero` (`:537`): at eps=0 the bound is 0 (this is what makes den Boer
  perfect). `five_card_eps0_eq0` (`five_card_family.v:180`) lifts it to the profile.

So Kim trades bias for mixing: more bias (larger eps) means slower mixing (larger
`kim_lambda2`), and over L rounds the distance to uniform decays as `kim_lambda2^L`.

### 3.3 Input leakage
Not separately quantified for the biased prior. The `five_card_leakage` ramp above is
stated for the uniform prior, which is the den Boer (eps=0) member. See the gaps below.

## 4. S5 (path on 5 sheets, 4 adjacent transpositions, secret = position)

### 4.1 Correctness (operational)
`s5_run_recovers (s w0) (w0 \in pgg_G s5_M)`: the executed verifier endpoints
reconstruct the dealt position `s : 'I_5`, for any cut, via the scheme's perm
invariance. Qed, axiom-free beyond boolp.

### 4.2 Anonymity / mixing (abstract): mixes to 0
- L=1 fiber witness `s5_security_witness_1` (`rigidity_s5_instance.v:154`): eps = 6/5
  by fiber counting. Axiom-free.
- Multi-round `s5_spectral_convergence_proved` (`s5_mixing.v:202`):
  `var_dist <= sqrt(5) * (181/200)^L`. The spectral gap is `19/200 = 0.095`.
- `s5_asymptotic` (`rigidity_s5_instance.v:186`): `SecurityAsymptotic` with gap 19/200
  and floor `eps_inf = 0`. The walk is a single connected orbit on all five sheets, so
  it mixes all the way to uniform. `s5_security_witness_schreier (L)` (`:200`) packages
  the L-dependent bound. Calibration: L=285 gives `< 2^-40`, L=893 gives `< 2^-128`.
- Complexity: `s5_complexity (L)` (`:441`): `search_space <= |G| = 120`. `s5_search_chain (L)`
  (`:451`): `n_traces <= 4^L` (4 generators). Both axiom-free.

### 4.3 Threshold privacy
`run_private` from the sum-mod scheme: below k shares, the position is hidden. Abstract.

### 4.4 Input leakage
No mutual-information leakage ramp for the position-model views (unlike den Boer). See
the gaps below.

## 5. S5xS5 (two piles of five, 8 transpositions, 10 sheets, secret = position)

### 5.1 Correctness (operational)
`s5x5_run_recovers (s w0) (w0 \in pgg_G s5x5_M)`: the executed endpoints reconstruct
`s : 'I_10`, for any cut, via the axiom-free `s5x5_perm_compatible` invariance. Qed.

### 5.2 Anonymity / mixing (abstract): mixes to a floor, not to 0
This is the important structural point. S5xS5 acts block-diagonally: pile-1 generators
fix pile-2 and vice versa, so a sheet never leaves its pile. The walk is reducible, and
the distance to uniform on all ten sheets saturates at a floor.

- L=1 fiber witness `s5x5_security_witness_1` (`rigidity_s5x5_instance.v:204`): eps = 8/5,
  fiber counting, axiom-free.
- The walk on one pile reduces to a lazy walk on 'I_5 (4 transpositions plus 4
  identities), with `lazy_alpha = (1 + 181/200)/2 = 381/400` and per-pile gap
  `19/400`. `s5_lazy_TV_bound (L)` (`s5x5_mixing.v:585`): per-pile
  `var_dist <= sqrt(5) * (381/400)^L`. `s5x5_pile1_TV_bound`/`s5x5_pile2_TV_bound`
  (`:1075`, `:1094`) lift it to the two piles.
- Master multi-round bound `s5x5_spectral_TV_bound (L)` (`:1113`):
  `var_dist(law of sigma s, uniform_10) <= 1 + sqrt(5) * (381/400)^L`.
- `s5x5_asymptotic` (`rigidity_s5x5_instance.v:252`): gap `19/400`, floor
  `eps_inf = 1`. `s5x5_security_witness_schreier (L)` (`:275`):
  `1 + sqrt(10) * (381/400)^L`. Calibration: L=591 drives the decaying term to `2^-40`,
  L=1838 to `2^-128`. The floor of 1 is the orbit-vs-global gap, which more rounds
  never close.
- Complexity `s5x5_complexity (L)` (`:435`): `search_space <= |G| = 14400`. Axiom-free.

So S5xS5 mixes each pile internally but cannot move the position across piles. The
within-pile shuffle is hidden, but the pile membership is not, which is exactly the
`eps_inf = 1` floor.

### 5.3 Threshold privacy
`run_private` from the product sum-mod scheme, k = 5. Abstract.

## 6. What we cannot claim today, and roughly how to get it

1. **Operational privacy (privacy from the executed trace).** All anonymity,
   threshold, and input-leakage results above are abstract: they reason about the
   permuted layout or the share distribution, not the interpreter trace. To make
   privacy operational, define the cut as a random variable `K : {RV P -> perm}` from
   the relevant weight fdist (uniform for den Boer, `kim_weight_dist` for Kim), lift the
   verifier's executed trace to `{RV P -> trace}` as a function of `K`, and connect it
   to the existing `var_dist` and `cond_mutual_info` lemmas. This is the DSDP pattern
   (trace lifted to random variables for leakage freedom) on the PGG side. Estimated
   work: a trace-to-RV bridge plus a substitution into the existing entropy lemmas.

2. **A single concrete random-cut distribution end to end.** The trace bridge is
   parametric over one cut `w0` (universally quantified). To talk about the random cut
   operationally, compose `fdistmap` of the cut distribution with the run, so the run's
   output is a distribution, then read the existing `run_anonymous` bound off the
   executed trace rather than off the abstract `rho_dist`. This is item 1 specialized
   to anonymity.

3. **Kim biased input leakage.** The `five_card_leakage` ramp uses the uniform prior
   (the den Boer member). Redo the ramp with `kim_weight_dist` to quantify how the bias
   changes the per-view mutual information. Estimated work: re-derive `condent_ratio`
   and the per-view cardinalities under the biased prior, then the same `lra` closes.

4. **Position-model input leakage (S5, S5xS5).** These carry threshold privacy and
   anonymity but no Shannon mutual-information leakage ramp for the verifier's partial
   views. One could add a leakage analysis analogous to den Boer's `leak_k*`, bounding
   `I(secret position ; partial view)` as the number of observed sheets grows. Estimated
   work: a per-view enumeration over the sum-mod scheme, similar in shape to
   `five_card_leakage`.

5. **Eliminate the `s5_rayleigh_Q2_R` axiom.** Every L>1 mixing result for S5 and S5xS5
   rests on one custom axiom, `s5_rayleigh_Q2_R` (`s5_mixing.v:188`), the Rayleigh
   bound `<v, Q^2 v> <= alpha^2 <v,v>` for the S5 Schreier transition, certified
   externally by a rational sum-of-squares LDL decomposition in
   `s5_spectral_certificate.py`. The rational witness data is already partly in Rocq
   (`s5_sos_lower_triangular`, `s5_sos_diagonal`, `s5_sos_diagonal_nonneg`); only the
   sum-of-squares to Rayleigh implication stays axiomatic. To remove it, prove that
   implication in kernel from the committed LDL data. Estimated work: a finite linear
   algebra argument over the explicit 5-by-5 rational decomposition.

6. **Full cross-pile mixing for S5xS5.** The floor `eps_inf = 1` is inherent to the
   block-diagonal S5xS5 action and cannot be removed by more rounds. To mix the position
   across both piles you need a connecting generator (a pile swap), which is the wreath
   construction; that instance was retired. This is a structural limit to state, not a
   bug to fix. If full mixing on ten sheets is wanted, it requires a different, transitive
   monodromy.

7. **Active or malicious adversaries.** The interpreter models deterministic honest
   execution. No active-deviation or malicious model exists. This needs a different
   adversary model, not an extension of the present proofs.

## 7. Axiom ledger

| Layer | den Boer | Kim | S5 | S5xS5 |
|---|---|---|---|---|
| Correctness trace bridge | boolp only | boolp only | boolp only | boolp only |
| Anonymity L=1 (fiber) | boolp only (eps=0) | boolp only | boolp only (eps=6/5) | boolp only (eps=8/5) |
| Anonymity L>1 (spectral) | n/a (L=1) | boolp only | `s5_rayleigh_Q2_R` | `s5_rayleigh_Q2_R` |
| Threshold privacy | boolp only | boolp only | boolp only | boolp only |
| Input leakage | boolp only | not done | not done | not done |

Notes. "boolp only" means the three standard MathComp-Analysis classical axioms
(`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`), the same baseline as infotheo, with no custom
axiom. The only custom axiom in any security layer is `s5_rayleigh_Q2_R`, which both S5
and S5xS5 L>1 mixing depend on (S5xS5 reuses it through the lazy reduction; `s5x5_mixing.v`
adds no axiom of its own). The rigidity and covering side carries separate axioms
(`s5_group_order_eq`, `s5x5_group_order_eq`, and the `realised_by_curve` geometry
markers) that the security and trace-bridge layers do not touch; the trace bridge was
specifically routed around them to stay axiom-free.
