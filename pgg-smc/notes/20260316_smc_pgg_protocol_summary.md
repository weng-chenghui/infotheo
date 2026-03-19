# SMC-PGG Protocol Summary (Meeting Brief)

*2026-03-16*

## What is SMC-PGG?

**SMC-PGG** stands for **Secure Multi-Party Computation via Parametric Geometry Groups**.

**Problem.** Given a monodromy group G acting on N sheets via generators σ₁, ..., σ_Tg, how do the algebraic properties of G constrain what threshold schemes are achievable, and at what security cost? SMC-PGG answers this by connecting the group's algebraic structure — via covering spaces and Riemann-Hurwitz — to concrete (k, T)-threshold parameters and security bounds, yielding a framework where **one algebraic choice (G + generators) simultaneously determines security, threshold gap, and round complexity**.

SMC-PGG is a **covering-space-based secure multi-party computation** protocol for functions in the complexity class NC^1 (polylog-depth Boolean circuits). Instead of encoding computation as Boolean circuits (like Yao/GMW/SPDZ), it uses a **monodromy representation** `rho: G -> S_N` — a group homomorphism mapping group elements to permutations on N "sheets." Security comes from the ambiguity in which word (over generators) produced a given observed endpoint — the adversary cannot determine which of the many possible words was used.

**Coordinates and secrets.** Each party i's endpoint `rho(w)(s_i)` is a **coordinate** — one component of the secret, not the secret itself. The framework is parametric over `ThresholdScheme` (`pgg_sharing_framework.v`): the reconstructor collects k coordinates and applies `ts_recon` to recover the secret. What "the secret" is depends on the threshold scheme:

- **Genus 0 (Shamir / Reed-Solomon)**: The secret is a field element recovered by polynomial interpolation from k evaluation points. Constructed by `genus0_covering` (used by star and S_5 instances). Gap = 0 (ideal: k = T).
- **Genus g > 0 (AG codes)**: The secret is determined by decoding the AG code on the covering curve. Gap ≤ 2g.
- **Sum-mod-N**: The secret is `(Σ endpoints) mod N` — the simplest instance, giving (T, T)-threshold (no fault tolerance: all T shares needed).

**Plug-able architecture:**

```
Group choice (G, σ₁...σ_Tg)
    │
    ├── Monodromy representation ρ: G → S_N
    │       │
    │       └── Endpoints: ρ(w)(s_i) per party  ← coordinates
    │
    └── Threshold scheme (plug-able)
            │
            ├── Genus 0: Shamir / Reed-Solomon  (gap = 0)
            ├── Genus g: AG code on curve C      (gap ≤ 2g)
            └── Sum-mod-N                        (T,T)-threshold
                    │
                    └── Secret: ts_recon(coordinates)
```

**Dealer-requires-epsilon architecture:** The dealer chooses word length L to achieve a target epsilon (security parameter). The `CertifiedSolution` record bridges the computable solver (`dealer_solve` in `pgg_security_solver.v`, which finds L via `vm_compute`) to the proof-level `SecurityWitness`. The generic constructor `certified_from_witness` (`algebraic_rigidity.v`) works for ANY `GeneratedMonodromyReprType` — it pairs a `SecurityWitness` with rational epsilon bounds to produce a `CertifiedSolution`. The star instance demonstrates this concretely via `star_certified_1`.

### Contributions

**(i) Concrete group instances formalized:**

The "Threshold" column refers to the covering scheme's genus and threshold gap. **PGL(2,N)** is the **projective general linear group** — the group of Möbius transformations of the projective line P^1, with |PGL(2,N)| = N(N²−1). Genus 0 (ideal threshold, gap = 0) requires |G| ≤ |PGL(2,N)|; groups exceeding this bound are forced to higher genus.

| Instance | Group | N | Tg | Threshold (genus → gap) | Best security eps (via `vm_compute`) | File |
|----------|-------|---|-----|------------------------|--------------------------------------|------|
| **Monster** | M (largest sporadic) | ~10^20 | 2 | genus >0, gap >0 (\|G\| >> PGL) | **0** at L\*=67 (2^67 > N, perfect); ~2 at L=1 | `rigidity_monster_instance.v` |
| **OC(2,3)** | `oc_sigmas` (3-cycles) ≤ S_4 | 4 | 2 | genus 0, gap 0 (\|G\| ≤ PGL) | **0** at L=2 (achievable = \|G\| = 12, perfect) | `rigidity_oc_instance.v` |
| **NCycle** | Z/NZ (N-cycle) | n+2 | 1 | genus 0, gap 0 (\|G\| ≤ PGL) | **0** at L=\|G\| (e.g. L=5 for N=5; perfect) | `rigidity_cyclic_instance.v` |
| **S_5** | `path_gen_tuple 3` = S_5 | 5 | 4 | genus 0, gap 0 (\|G\| ≤ PGL) | **8/295 ≈ 0.03** at L=8, → 0 (transitive) | `rigidity_s5_instance.v` |
| **Star** | `star_gen_tuple m` ≤ S_{m+3} | m+3 | m+1 | genus 0, gap 0 (\|G\| ≤ PGL) | 2(m+1)/(m+3) floor (non-transitive) | `rigidity_star_instance.v` |
| **Abelian** | Z/2Z × Z/2Z (disjoint tperms) | 4 | 2 | genus 0, gap 0 (\|G\| ≤ PGL) | 1 floor (non-transitive) | `rigidity_abelian_instance.v` |

The eps values are computed by **fiber counting** — enumerating all Tg^L words, grouping by endpoint (the "fiber" of each sheet value), and measuring the worst-case variational distance from uniform. This is generic for any group with generators, not RAAG-specific: the proof-level constructor `security_witness_fiber` (`algebraic_rigidity.v`) works for any `GeneratedMonodromyReprType`; the computable function `raag_fiber_eps_nat` (`pgg_security_solver.v`) takes an `RAAGDesc` for `vm_compute` but does not use RAAG commutation — the `raag_` prefix is a naming artifact. For transitive groups where the achievable set saturates to |G|, the direct endpoint bound (`security_witness_endpoint_inj`) gives eps = 0 — **perfect** information-theoretic security. OC(2,3) at L=2 and NCycle at L=|G| achieve this.

Key observations:
- **Transitive** groups (S_5, OC, NCycle) have eps → 0 as L grows: the achievable set eventually covers all of S_N, making the endpoint distribution uniform. **Non-transitive** groups (Star, Abelian) are stuck at a positive eps floor — orbit partitions force a constant variational distance regardless of L.
- **CertifiedSolution** bridges: Star has `star_certified_1` (concrete). Monster can use `certified_from_witness` (generic). Other instances can be bridged similarly.
- All instances except Monster have **0 global Axioms** (only Section Hypotheses). Star additionally has `star_protocol_correct` (end-to-end protocol correctness via `ar_protocol_correct`) and `star_dealer` (type-safe word→protocol demo via `dealer_from_words`).

**(ii) Covering scheme constructors (plug-able):**

The covering scheme determines the threshold — it is a **plug-able choice**, independent of the security bound. Four constructors are available, each producing a `CoveringScheme M`:

| Constructor | Genus | Gap | Curve | Fault tolerance | PGL constraint | Key file |
|-------------|-------|-----|-------|-----------------|----------------|----------|
| `genus0_covering` | 0 | 0 | P^1 (= Shamir/RS) | 0 | \|G\| ≤ PGL(2,N) required | `cover_genus0.v` |
| `genus1_covering` | 1 | ≤ 2 | Elliptic y²=f(x), deg(f)=3 | up to 2 | None | `cover_genus1.v` |
| `genus2_covering` | 2 | ≤ 4 | Hyperelliptic y²=f(x), deg(f)=5 | up to 4 | None | `cover_genus2.v` |
| `higher_genus_covering` | g | ≤ 2g | Generic | up to 2g | None | `cover_genus1.v` |

All five small instances currently use `genus0_covering` because they all satisfy |G| ≤ PGL(2,N), making genus 0 optimal (gap = 0, no wasted shares). But any instance could **switch** to a higher-genus constructor to gain fault tolerance at the cost of threshold gap — the security bound (eps) is unaffected by this choice. For example, OC(2,3) with `genus1_covering` would get (2,4)-threshold tolerating 2 party failures while keeping eps = 0.

Monster has |G| >> |PGL(2,N)|, so `genus0_covering` is unavailable — genus > 0 is forced by the tradeoff theorem. Its covering is axiomatized (`monster_covering`).

**(iii) The security/threshold tradeoff** (`cover_tradeoff.v`):
- Either genus = 0, |G| ≤ PGL(2,N), gap = 0
- Or genus > 0, gap ≤ 2g

This is the core result linking algebraic structure to threshold parameters.

## Protocol and adversary model

### What the protocol computes

A **covering** of the Riemann sphere assigns N **sheets** (indexed by `'I_N`) to each point. The **monodromy group** G ≤ S_N is the group of sheet permutations induced by analytic continuation around branch points. Each branch point contributes a **generator** σ_i ∈ G.

The protocol computes a **word** w = (w_0, ..., w_{L-1}) — a tuple of Tg generator **indices** (`w : L.-tuple 'I_Tg` in the code, where Tg is the number of generators). The group element is the product of generators looked up by index:

```
word_eval w := tnth(sigmas, w_0) · tnth(sigmas, w_1) · ... · tnth(sigmas, w_{L-1})   ∈ G
```

Each party i starts on sheet `start_sheet(i)` and **actively computes** their endpoint:

1. **Receives** their **share** — a partial permutation lookup table: `[rho(w)(s_i) | w ∈ W]` (via secret channel)
2. **Receives** the public **word index** `P_idx` (via public channel)
3. **Looks up** their endpoint: `nth ord0 my_share P_idx` (see `pparty` in `pgg_pismc.v`)
4. **Sends** the endpoint `rho(word_eval w)(s_i) ∈ 'I_N` to the reconstructor

The reconstructor collects k endpoints (coordinates) and applies `ts_recon` from the threshold scheme to recover the secret.

### Adversary model

The adversary is a **passive (semi-honest) coalition** of k parties out of N total. Each coalition member observes their own endpoint honestly (follows protocol but tries to learn more).

**General case** (`collusion_bound_k`, Section 7 of `pgg_collusion_bound.v`): A coalition of k parties observes k endpoints out of N. With a (k, T)-threshold scheme, coalitions of fewer than k learn nothing (privacy); k shares suffice for reconstruction. The T - k extra shares beyond reconstruction threshold constitute the "gap" governed by genus.

**Special case** (T-1 coalition, `collusion_bound`, Section 4): The original bound for T-1 out of T parties, where the **target** is the single unobserved party `ord_max`:

**Security guarantee** (`pgg_collusion_bound.v`):
```
var_dist(adversary_marginal, uniform) ≤ ε + 2(T-1)/N
```
where `adversary_marginal` is the distribution of `rho(g)(s_target)` induced by the protocol's word sampling, and ε is the endpoint-level variational distance bound: `∀ s, var_dist(fdistmap eval_s rho_dist, uniform(I_N)) ≤ ε`. (Before commit 41be0f0, ε measured the permutation-level distance from uniform over S_N; the refactoring moved to the tighter endpoint-level bound directly.)

**DPI vs. Direct endpoint epsilon** (`pgg_collusion_bound.v`, Sections 6 and 10):

| Method | Formula | Denominator | Available when |
|--------|---------|-------------|----------------|
| DPI (data processing inequality) | ε = 2·(N! − Tg^L) / N! | N! | Always (any weval_inj group) |
| Direct endpoint | ε = 2·(N − Tg^L) / N | N | eval_s injective on achievable(L) |

The DPI bound is always ≈ 2 (vacuous for security) since Tg^L ≪ N!. The direct endpoint bound has denominator N instead of N!, giving meaningful security:

| Instance | DPI ε | Direct ε | Improvement |
|----------|-------|----------|-------------|
| NCycle (Tg=1, N=4) | 1.92 | 1.50 | 22% |
| Abelian (Tg=2, N=4) | 1.83 | 1.00 | 45% |
| OC (Tg=2, N=4, L=2) | 1.67 | 0.00 | perfect |

The direct bound requires `eval_s` (sigma ↦ sigma(s)) to be injective on achievable(L). This holds for NCycle (trivially: singleton achievable set) and Abelian (disjoint transpositions), proved via `security_witness_endpoint_inj` in `algebraic_rigidity.v`. The `pgg_security_solver.v` file provides computable `epsilon_endpoint_rat Tg N L` for parameter exploration.

**SecurityProfile** (`algebraic_rigidity.v`): wraps a SecurityWitness with L* and nontriviality (ε < 2), confirming the security bound is strictly better than trivial.

**Orbit transitivity and epsilon convergence** (`pgg_security_demo.v`):

The endpoint epsilon's long-run behavior is determined by whether the group acts transitively on sheets:

| Family | Transitive? | Orbits | eps at L=1 | eps limit (L→∞) |
|--------|------------|--------|-----------|-----------------|
| Star(m) | No | {0,1}, {2,...,m+2} | 2(m+1)/(m+3) | stuck at floor |
| Abelian (disjoint) | No | {0,1}, {2,3} | 1 | stuck at 1 |
| Path(3) = S_5 | Yes | {0,...,4} | 6/5 | → 0 |
| OC(2,3) | Yes | {0,...,3} | 1 | → 0 |
| NCycle(N) | Yes | {0,...,N-1} | 2(N-1)/N | → 0 |
| Monster | (axiomatic) | — | ~2 | (axiomatic) |

**Non-transitive** groups have orbit partitions that prevent the endpoint distribution from approaching uniform — eps is stuck at a positive floor regardless of word length L. **Transitive** groups have eps → 0 as the achievable set grows toward |G|, but the convergence is **not monotonic**: at L=2, identity enters the achievable set (since σ² = id for transpositions), creating an eps spike.

**Best secure instances** (combining low eps with fault-tolerant threshold):

| Instance | L | eps | |achievable| | Genus | Threshold (k,T) | Fault tolerance |
|----------|---|-----|-------------|-------|-----------------|-----------------|
| **OC(2,3), genus=1** | **2** | **0** | **12 = \|G\|** | **1** | **(2, 4)** | **2** |
| OC(2,3), genus=0 | 2 | 0 | 12 = \|G\| | 0 | (4, 4) | 0 |
| Path(3), genus=1 | 5+ | → 0 | → 120 (=\|S_5\|) | 1 | (3, 5) | 2 |
| Path(3), genus=0 | 5+ | → 0 | → 120 | 0 | (5, 5) | 0 |

**OC(2,3) at genus=1** is the standout: **perfect security** (eps = 0) at just L=2 rounds, with (2,4)-threshold tolerating 2 party failures. This is the best combination of security and fault tolerance in the framework — achieved by a small group (\|G\|=12) with overlapping 3-cycles that saturate all permutations in 2 steps.

More generally, any transitive group achieving eps ≈ 0 can trade genus 0 (ideal threshold, no fault tolerance) for genus 1 ((k, k+2)-threshold with 2 fault tolerance) by choosing a higher-genus covering. The security bound is independent of the covering choice — only the threshold changes.

### Search space (adversary's brute-force cost)

Given the adversary model above, the **search space** at word length L is the number of distinct group elements achievable by any word:
```
search_space(L) := |{ word_eval(w) | w ∈ Tg^L }| = |achievable(L)|
```

This counts how many distinct permutations the adversary must consider when trying to determine the unobserved endpoint. Key bounds (all proved):

- `search_space(L) ≤ |G|` — can never exceed the group order
- `search_space(L) ≤ Tg^L` — can never exceed the word count
- When L-free (word_eval injective on `L.-tuple 'I_Tg`): `search_space(L) = Tg^L`
- RAAG chain: `search_space(L) ≤ n_traces(L) ≤ Tg^L`

Larger search space → harder for adversary → increases the upper bound on brute-force cost. But the code only proves the contrapositive constraint: if |G| > PGL(2,N), then genus > 0 (see tradeoff below). It does NOT prove that larger |G| monotonically increases genus.

### Round complexity

A **round** is one application of a generator σ_{w_j} to all parties' current sheets in parallel. A word of length L requires L sequential rounds. With RAAG structure (commutation relation on generators), letters in the same **Foata factor** can be applied simultaneously, giving an upper bound on round count equal to the **Foata normal form depth** — the number of maximal blocks of pairwise-commuting letters when the word is greedily factored left-to-right.

| RAAG graph | Rounds for word of length L | Intuition |
|------------|---------------------------|-----------|
| Fully disconnected | L (no parallelism) | No generators commute |
| Star (m leaves) | Between 1 and L | Center commutes with leaves |
| Complete (clique) | Foata depth (≤ L; = 1 only when all generator indices in the word are distinct, since `comm` is irreflexive) | All generators commute |

### Threshold and threshold gap

A **(T, k)-threshold scheme** (`ThresholdScheme` in `pgg_sharing_framework.v`) distributes a secret into T shares such that:
- **Correctness** (`ts_correct`): any k shares suffice to reconstruct the secret
- **Privacy** (`ts_private`): any coalition of fewer than k parties learns nothing about the secret

The **threshold gap** is T - k: how many shares beyond the reconstruction threshold are distributed. Ideally gap = 0 (every share is useful). The covering genus forces a gap:

```
ts_T ≤ ts_k + 2 · genus(covering curve)
```

| Genus | Gap bound | Meaning |
|-------|-----------|---------|
| 0 (rational curve, P^1) | 0 | Ideal: k = T, every share reconstructs |
| 1 (elliptic curve) | 2 | At most 2 extra shares wasted |
| g ≥ 1 | 2g | Gap grows linearly with genus |

For genus 0, the additional constraint is `|G| ≤ PGL(2,N)` (automorphisms of P^1 are Möbius transformations). This follows an **interface-implementation pattern**: each instance provides its own proof or hypothesis via `ThresholdWitness.tw_genus0_pgl` (see `algebraic_rigidity.v`). No global axiom — the star and S_5 instances use Section Hypotheses; the Monster axiomatizes it as `monster_genus0_pgl`. This appears as one arm of the `security_threshold_tradeoff` disjunction (see below).

### The security/threshold tradeoff

This is the core tension formalized by `AlgebraicRigidity`. The proved theorem (`security_threshold_tradeoff` in `cover_tradeoff.v`) is a **disjunction**:

- **Either** genus = 0, |G| ≤ PGL(2,N), and gap = 0 (ideal threshold, bounded group size)
- **Or** genus > 0, and gap ≤ 2 × genus (non-trivial threshold gap)

You cannot have both a large group (exceeding PGL(2,N)) AND genus-0 (ideal threshold). The contrapositive (`large_group_forces_gap`): if |G| > PGL(2,N), then genus > 0. Note this is NOT a monotone relationship — genus depends jointly on |G|, ramification, and base genus via Riemann-Hurwitz.

One algebraic choice (G, ρ, σ₁...σ_Tg) determines search space, security bound, threshold gap, and round complexity simultaneously — the four properties formalized in the `AlgebraicRigidity` record (which bundles `SecurityWitness`, `ThresholdWitness`, and `RoundComplexityWitness`). Word length L and sampling distribution remain free parameters within `SecurityWitness`. Round complexity is L for any group; RAAG refinement to Foata depth gives a tighter `rc_depth` bound.

### Formalization architecture: three connected pipelines

The formalization has three pipelines that are now connected end-to-end:

```
Pipeline 1 — Protocol:
  w : L.-tuple 'I_Tg ──→ dealer_from_words ──→ pdealer / pparty / precon
  (external randomness)    (pgg_pismc.v)         ──→ channel duality proofs
                                                           │
Pipeline 2 — Solver:                                       │
  RAAGDesc ──→ dealer_solve ──→ SecurityParams ──╮         │
                                                  │         │
Pipeline 3 — Security proofs:                     │         │
  SecurityWitness ──→ certified_from_witness ─────╯         │
       │                    │                               │
       │              CertifiedSolution                     │
       │                                                    │
       ╰──→ AlgebraicRigidity ──→ dealer_words_correct ─────╯
                  │                (pgg_dealer_bridge.v)
  ThresholdWitness ──╯
```

**Bridge points (now instantiated):**

| Bridge | Generic? | Concrete instance | File |
|--------|----------|-------------------|------|
| `certified_from_witness` | Yes — any `GeneratedMonodromyReprType` | `star_certified_1` | `algebraic_rigidity.v` |
| `ar_protocol_correct` | Yes — any `GeneratedMonodromyReprType` | `star_protocol_correct` | `rigidity_star_instance.v` |
| `dealer_words_correct` | Yes — any `GeneratedMonodromyReprType` | `star_dealer` | `pgg_dealer_bridge.v` |
| `dealer_from_words` | Yes — any `GeneratedMonodromyReprType` | `star_dealer` | `pgg_pismc.v` |
| `G_stable` | No — instance-specific (relates code automorphism to monodromy) | Section Hypothesis in star | `rigidity_star_instance.v` |

**Layer 1 (Computable — RAAG only):**
`RAAGDesc` → `dealer_solve` → `SecurityParams` via `vm_compute`. NOT available for Monster (axiomatized group data).

**Layer 2 (Proof-level — ANY GeneratedMonodromyReprType):**
`SecurityWitness` → `certified_from_witness` → `CertifiedSolution`. Works for Monster, Star, OC, Cyclic, etc.

**Layer 3 (End-to-end — requires G_stable):**
`AlgebraicRigidity` + `PGGInterface` + `G_stable` → `ar_protocol_correct`. Works for any instance that proves G_stable.

The **security track** depends on the group G, its generators, word combinatorics, and fiber distributions. It produces a `SecurityWitness` (variational distance bound).

The **reconstruction track** depends on the AG code, its automorphisms, and how monodromy acts as a coordinate permutation on shares. It produces a `ThresholdWitness` (covering scheme + PGL hypothesis).

The two tracks share the same group G but are otherwise independent — the security proofs never reference the threshold scheme, and the threshold proofs never reference word distributions. `AlgebraicRigidity` bundles both witnesses; `certified_from_witness` bridges the computable solver to proofs; `ar_protocol_correct` connects everything to the protocol.

## What distinguishes it from circuit-based MPC?

**One algebraic design choice (group G + generators) determines four formalized properties (search space, security, threshold, round complexity):**

| Property | Determined by | Generality | Circuit MPC comparison |
|----------|--------------|------------|----------------------|
| **Computational power** | Group variety (Barrington-Therien) -> NC^1 (polylog-depth, poly-size Boolean circuits) | Any G | Circuits compute all of P |
| **Adversary search space** | Fiber count: words of length L evaluating distinctly, bounded by \|G\| | Any GeneratedMonodromyReprType | No structural bound |
| **Threshold gap** | Riemann-Hurwitz genus -> Goppa code bound: gap <= 2*genus | Any GeneratedMonodromyReprType | Shamir = genus-0 AG code (no gap) |
| **Round complexity** | General: L rounds (one per generator). RAAG refines via independence graph -> Foata depth (abelian = 1, L-free = L, partial = intermediate) | General bound: any G. Foata upper bound: RAAG | O(1) for Yao, O(depth) for GMW |

The `AlgebraicRigidity` record in `pgg-smc/reconstruct/algebraic_rigidity.v` bundles security and threshold into a single formal witness parameterized by `GeneratedMonodromyReprType` (group G + generators). Round complexity is L for any group; RAAG trace counts refine this to Foata depth as a separate derived property.

## Two-View Security Model

PGG security is best understood through two complementary views:

### View 1 — Ideal-world perfect security (already formalized)

Under `uniform_{S_N}`, the conditional endpoint distribution is exactly uniform over remaining values. Proved by `perm_cond_uniform` (`perm_uniform.v`):

```
cPr[σ(s_new) = a | σ prescribed at s_1,...,s_k] = 1/(N-k)
```

This is **perfect** (epsilon = 0) information-theoretic security in the ideal world. The adversary learns nothing beyond what is logically forced by the observed values.

### View 2 — Real-vs-ideal gap (SecurityWitness captures this)

The real protocol samples from `rho_from_words` (uniform over Tg^L words), not `uniform_{S_N}`. The SecurityWitness epsilon measures how far the real **endpoint** distribution deviates from uniform:

```
∀ s : 'I_N,  var_dist(fdistmap eval_s rho, uniform_{I_N}) ≤ epsilon
```

This is a direct bound on what the adversary learns about ANY single endpoint, without going through the permutation-level distribution. The DPI gives a generic bound `epsilon ≤ 2*(N!-Tg^L)/N!`, but instances with group-theoretic structure (e.g., transitive action) can provide much tighter bounds by direct computation.

With enough generators and long words (`Tg^L >> N`), epsilon → 0.

### Combined security

PGG achieves **statistical information-theoretic security** with concrete parameter epsilon. No computational assumptions. The epsilon depends on group parameters (Tg, L, N, T):

1. The ideal conditional bound is perfect (View 1)
2. The real-vs-ideal gap is bounded by epsilon (View 2)
3. The total conditional bound: `var_dist(adversary_posterior, uniform) ≤ epsilon + 2*(T-1)/N`

## Security notions achieved

1. **Endpoint-level collusion bound** (`pgg_collusion_bound.v`, `algebraic_rigidity.v`):
   - SecurityWitness bounds the marginal endpoint distribution:
   - `∀ s, var_dist(fdistmap eval_s rho, uniform_{I_N}) ≤ epsilon`
   - The unconditional endpoint bound follows directly; the conditional bound adds `2(T-1)/N`
   - **Information-theoretic** -- no computational assumptions, conditional on the word sampling distribution

2. **Permutation-level collusion bound** (`pgg_collusion_bound.v`, Theorem 5):
   - Coalition of T-1 parties vs. one hidden party
   - `var_dist(adversary_marginal, uniform) <= eps + 2(T-1)/N`
   - eps = variational distance of rho-induced distribution from uniform on S_N
   - This is an upper bound on the endpoint-level bound (via DPI)

3. **Fiber uniformity** (informal motivation, not a formal theorem in the codebase): Under uniform word distribution, adversary facing all T-1 shares has equally likely candidate words per fiber. The formalized security result is the collusion bound above.

4. **Grover mitigation** (`pgg_security.v`): Doubling word length L->2L restores quadratic security against quantum search. Cost >= kappa^L (exponential in original L; kappa is the free-group ball growth rate, specific to that analysis).

5. **Model**: Semi-honest (passive), static corruptions, t < n/2. Conjectured weaker than simulation-based security (not formally proved in the codebase), but more tractable and algebraically characterized.

## What the dealer prepares

1. **Chooses group element sequence W** (`W : seq gT`)
2. **Computes permutation table**: rho(w) for each w in W (an N x |W| matrix of sheet indices)
3. **Extracts party i's column**: `share(W, i) = [rho(w)(s_i) | w in W]`
4. **Distributes**:
   - `share(W, i)` to party i (secret channel)
   - Public word index P_idx to all (public channel)

Each party computes their endpoint by simple table lookup. The reconstructor collects T endpoints and recovers the secret via the threshold scheme (the framework is parametric over `ThresholdScheme`; AG codes are one instance).

### Setup/online split (formalized)

**Setup phase (offline, not session-typed):** The dealer runs `dealer_solve` to get `SecurityParams` with word length L. It then uniformly samples `w : L.-tuple 'I_Tg` and evaluates `word_eval w` to get a group element P. The share for party j is computed locally as `share PI [:: P] j = [:: rho(P)(starts[j])]`. This is formalized by `dealer_from_words` in `pgg_pismc.v`.

**Online phase (session-typed):** `pdealer` distributes pre-computed shares via secret channels and broadcasts P_idx. This is the session-typed protocol with channel duality proofs.

**Security guarantee:** `dealer_words_correct` in `pgg_dealer_bridge.v` proves that any word of solver-determined length L produces a correct protocol execution, connecting `AlgebraicRigidity` to `pdealer` end-to-end.

This setup/online split is standard in MPC formalizations (EasyCrypt Maurer, CryptHOL 2-party). The piSMC framework is deterministic — randomness is an external parameter, exactly as DSDP handles encryption keys and random blinding factors.

## Axiom boundary status (from git log)

### Fully proved

- **PGL(2,F_q) cardinality**: `|PGL(2,q)| = q(q^2-1)` via GL cardinality + scalar quotient in MathComp (commit 89dcb62)
- **Hyperelliptic Goppa bound** (`hyp_goppa_wt_mdeg`): proved via polynomial resultant R(x) = A^2 - B^2*f, parity + `max_poly_roots` (commit 0a4095a)
- **`dual_root_poly`**: proved from resultant-based dual evaluation encoding (commit c8f12d7)
- **`dual_min_dist`**: proved from `dual_root_poly` via root-counting (commit 483791a)
- **`hyp_priv_surj`**: privacy from dual minimum distance (commit ec5afd7)
- **`AlgebraicRigidity` record**: 0 Admitted, 0 Axioms (commit 89dcb62)
- **`certified_from_witness`**: generic bridge from `SecurityWitness` to `CertifiedSolution`, works for any `GeneratedMonodromyReprType`
- **`star_certified_1`**: concrete `CertifiedSolution` for star at L=1, eps = 2(m+1)/(m+3)
- **`star_protocol_correct`**: end-to-end protocol correctness for star via `ar_protocol_correct` (conditional on `G_stable` Section Hypothesis)
- **`dealer_from_words`**: type-safe word-to-protocol wrapper (`pgg_pismc.v`)
- **`dealer_words_correct`**: end-to-end word→protocol correctness via `ar_protocol_correct` (`pgg_dealer_bridge.v`)
- **`dealer_words_epsilon_bound`**: endpoint security bound from `AlgebraicRigidity` (`pgg_dealer_bridge.v`)

### Axiom declarations (8 total, all in `rigidity_monster_instance.v`)

**Monster instance** (8):
1. `monster_n` — number of sheets (abstract, known to be ~ 10^20)
2. `monster_sigmas` — two generators (exist by 2-generation of finite simple groups, CFSG)
3. `monster_sigmas_distinct` — generators are distinct (injectivity; weakened from former `monster_lfree1` in commit b13f1ec, which is now a derived lemma via `gen_inj_lfree1`)
4. `monster_Lstar` — turning point word length L* for optimal security
5. `monster_weval_inj_Lstar` — word evaluation is injective at L*
6. `monster_eval_s_inj_Lstar` — eval_s is injective on achievable(L*) for each sheet s
7. `monster_covering` — existence of a CoveringScheme
8. `monster_genus0_pgl` — genus-0 PGL bound (vacuously true since |M| >> PGL(2,N))

**Eliminated axioms** (recent commits):
- `genus0_aut_pgl` (was framework-level) — deleted in commit aba8e96; replaced by interface-implementation pattern (`ThresholdWitness.tw_genus0_pgl`)
- `star_covering` (was star instance) — now constructed from `genus0_covering` via Reed-Solomon codes (commit 301cdfe)
- `star_genus0_pgl` — was always a Section Hypothesis, never a global Axiom

The Monster axioms include group data because the group is too large to enumerate computationally. Star and S_5 instances have **0 global Axioms** — all results are conditional on Section Hypotheses about RS code parameters.

## How to embed a new group

The protocol is parameterized by a type hierarchy. Each level adds algebraic data and unlocks more protocol properties. The **main ladder** works for any finite group; the **RAAG refinement** is optional and sharpens round complexity.

### Design principle: HB vs Record

The formalization uses two mechanisms for different roles:

- **HB.mixin / HB.structure**: the **type hierarchy** — properties attached to a type that compose and inherit
- **Record**: **value-level witnesses** — data bundles parameterized by the type hierarchy

```
Type hierarchy (HB):          Value witnesses (Record):
  PGGTypes                      SecurityWitness R M
  ↓ isMonodromyRepr              ThresholdWitness M
  MonodromyReprType              AlgebraicRigidity R M
  ↓ hasGenerators                CoveringScheme M
  GeneratedMonodromyReprType     PGG_Interface
  ↓ isRAAG0
  RAAGType
```

The left column answers "what kind of group is this?" — composed via HB inheritance. The right column answers "what are the concrete security/threshold parameters?" — values you construct for a specific group at specific parameters (e.g., you might have multiple `SecurityWitness` for the same type at different word lengths L). This follows MathComp convention (`finGroupType` is HB; `mxrepresentation`, `socle_data` are Records).

### Main ladder (any group)

```
PGGTypes
  ↓  add rho
MonodromyReprType
  ↓  add generators
GeneratedMonodromyReprType
  ↓  add SecurityWitness + ThresholdWitness + RoundComplexityWitness
AlgebraicRigidity
```

**Level 1: PGGTypes** (`pgg_interface.v`)
- Provide: `gT : finGroupType`, `N' : nat`, `G : {group gT}`
- Unlocks: basic naming (sheets indexed by `'I_N'.+1`)

**Level 2: MonodromyReprType** (`pgg_interface.v`)
- Provide: `rho : {morphism G >-> {perm 'I_N'.+1}}`
- Unlocks: `endpoint`, `endpointM`, `start_sheet`, `share`, `compute`, `endpoints`

**Level 3: GeneratedMonodromyReprType** (`pgg_interface.v`)
- Provide: `sigmas : Tg.-tuple gT` (generators) + proof `<<[set tnth sigmas i | i]>> = G`
- Unlocks: `word_eval`, `search_space L`, `achievable L`, L-freeness (`lfree L`), `pgl_bound`
- Round complexity: L rounds (one per generator position in word)

**Level 4: SecurityWitness** (`algebraic_rigidity.v`)
- Provide: word length `L`, epsilon bound `eps`, distribution `rho_dist`, proof `var_dist rho_dist uniform <= eps`
- Typical construction: prove L-freeness → use `var_dist_lfree_uniform` for automatic epsilon
- Alternative: provide a custom distribution and bound directly

**Level 5: ThresholdWitness** (`algebraic_rigidity.v`)
- Provide: `CoveringScheme M` (covering data + threshold scheme + compatibility + gap bound) + PGL hypothesis (`cd_genus cd = 0 -> #|G| <= pgl_bound M`)
- Star and S_5 instances construct this from `genus0_covering` (Reed-Solomon codes); Monster axiomatizes it

**Level 6: AlgebraicRigidity** — combine SecurityWitness + ThresholdWitness + RoundComplexityWitness via `MkAlgebraicRigidity`
- Unlocks all derived properties: `ar_complexity`, `ar_tradeoff`, `ar_gap_bound`, `ar_protocol_correct`

### RAAG refinement (optional)

When generators have a known commutation structure, embedding as a RAAG refines round complexity from L to Foata depth. Add on top of Level 3:

**isRAAG0** (`pgg_raag.v`):
- `comm : rel 'I_Tg` — symmetric, irreflexive commutation relation
- Proof `raag_Hcomm`: `comm i j -> sigma_i * sigma_j = sigma_j * sigma_i` in G
- Proof `raag_gen_inj`: `tnth sigmas` is injective
- Unlocks: `n_traces L`, `foata_depth`, search space chain `search_space L <= n_traces L <= Tg^L`

**By graph topology:**

| Graph | Commutation pattern | Round complexity | Trace count | Example file |
|-------|-------------------|-----------------|-------------|--------------|
| **Fully disconnected** (L-free) | No generators commute | L (sequential) | Tg^L (maximum) | `pgg_lfree.v` |
| **Star** | Center commutes with all leaves; leaves don't commute | Intermediate | Computed via `n_traces_natB` + `vm_compute` | `pgg_raag_star.v` |
| **Fully connected** (clique/abelian) | All generators commute | Foata depth (= 1 when all letter indices in the word are distinct, since `comm` is irreflexive; otherwise equals number of Foata factors) | Multiset count (minimum) | `pgg_raag_clique.v` |
| **Partial** | Custom graph | Foata depth of graph | Via clique polynomial recurrence | Define custom `comm` relation |

### Running examples

#### Star graph (`rigidity_star_instance.v`)

The star-graph instance with m leaves instantiates each level:

**Level 1–3** (in `pgg_raag_star.v`):
```
gT       := {perm 'I_(m+3)}
N'       := m + 2
G        := <<[set star_gen i | i : 'I_(m+1)]>>
rho      := identity morphism (G ≤ S_N)
sigmas   := star_gen_tuple m  (center tperm + m leaf tperms)
```

**Level 4** (in `rigidity_star_instance.v`):
```
star_security_witness_1 :=
  MkSecurityWitness 1 _                         (* L = 1 *)
    (rho_from_words 1 (star_gen_tuple m))        (* distribution *)
    (var_dist_lfree_uniform star_lfree1)          (* proof via 1-freeness *)
```

**Level 5** (constructed from `genus0_covering`, not axiomatized):
```
star_covering := genus0_covering HG_star qn an HN sigma_fix0 code_auto
```
Requires Section Hypotheses: `HG_star` (group nontriviality), `primeq` (field char), `qn` (RS parameter), `an` (primitive root), `HN` (field size = N), `sigma_fix0` (coord automorphism fixes 0), `code_auto` (RS code compatibility).

`star_genus0_pgl` is a Section **Hypothesis**, not a global Axiom.

**Level 6**:
```
star_rigidity := MkAlgebraicRigidity
  (star_security_witness_1 R m)
  star_threshold_witness
  star_round_complexity_witness
```

**Axiom count**: 0

**Star-specific sub-tasks** (proved in `pgg_raag_star.v`):
1. Define `star_gen_tuple m` — center transposition `tperm 0 1` + m leaf transpositions `tperm 2 (2+i)`
2. Prove `star_comm_sym`, `star_comm_irrefl`, `star_Hcomm`, `star_gen_inj`
3. Verify trace counts via `vm_compute` on `n_traces_natB`
4. Prove `star_lfree1` — 1-freeness holds (all single generators are distinct permutations)

#### Monster group (`rigidity_monster_instance.v`)

The Monster M — largest sporadic simple group (|M| ≈ 8×10^53) — demonstrates that protocol correctness depends only on algebraic structure, not computability:

**Levels 1–3** via `Gen_PGGTypes` (definitional):
```
gT     := {perm 'I_monster_n.+2}       (* ~ 10^20 sheets *)
sigmas := monster_sigmas                (* 2 generators, by CFSG 2-generation *)
M      := @Gen_PGGTypes 1 monster_n monster_sigmas
```

**Level 4** (SecurityWitness — **proved**, not axiomatized):
```
monster_security_witness_1 :=
  MkSecurityWitness 1 _
    (rho_from_words 1 monster_sigmas)
    (var_dist_lfree_uniform monster_lfree1)
```

**Level 5** (axiomatized):
```
Axiom monster_covering : CoveringScheme R_monster.
Axiom monster_genus0_pgl : ...
```

**Axiom count**: 8 (`monster_n`, `monster_sigmas`, `monster_sigmas_distinct`, `monster_Lstar`, `monster_weval_inj_Lstar`, `monster_eval_s_inj_Lstar`, `monster_covering`, `monster_genus0_pgl`)

The axioms are needed because the group data is abstract (star has concrete generators): 3 for group data (`monster_n`, `monster_sigmas`, `monster_sigmas_distinct`), 3 for the security turning point (`monster_Lstar`, `monster_weval_inj_Lstar`, `monster_eval_s_inj_Lstar`), and 2 for the covering scheme (`monster_covering`, `monster_genus0_pgl`). The Monster illustrates the security/threshold tradeoff at an extreme scale:
- Security: astronomically strong (|G| ~ 10^53, so search space upper bound ~ 10^53)
- Threshold: |G| vastly exceeds PGL(2,N), so genus > 0 by the contrapositive. Gap ≤ 2 × genus; the exact genus depends on ramification data via Riemann-Hurwitz, not on |G| alone

#### S_5 group (`rigidity_s5_instance.v`)

S_5 — the symmetric group on 5 elements, generated as a Coxeter group of type A_4 — demonstrates the genus-0 construction with a small concrete group:

**Levels 1–3** (in `pgg_raag_s5.v`):
```
gT     := {perm 'I_5}
N'     := 3
G      := <<[set path_gen i | i : 'I_4]>>    (* = S_5 *)
sigmas := path_gen_tuple 3                    (* 4 adjacent transpositions: (01),(12),(23),(34) *)
```

Commutation: `s_i s_j = s_j s_i` iff `|i-j| ≥ 2`. Independence graph: `{(0,2), (0,3), (1,3)}`.

**Level 4** (SecurityWitness — proved via `vm_compute`):
```
s5_security_witness_1 :=
  MkSecurityWitness 1 _
    (rho_from_words 1 (path_gen_tuple 3))
    (var_dist_lfree_uniform s5_lfree1)           (* 1-freeness by vm_compute *)
```

**Level 5** (constructed from `genus0_covering`, same as star):
```
s5_covering := genus0_covering HG_s5 qn an HN sigma_fix0 code_auto
```
Hypotheses: identical structure to star instance (RS code parameters + coord automorphism compatibility).

`s5_genus0_pgl` is a Section Hypothesis.

**Axiom count**: 0

## Detailed comparison with non-abelian group MPC protocols

### Comparison axes

| Axis | SMC-PGG | Barrington-based (Ishai-Kushilevitz 2000) | ZAS correlations (Beimel et al. 2021) | Desmedt-Frankel non-abelian SS (1994) | Oblivious group actions (Attrapadung et al. 2021) |
|------|---------|------------------------------------------|---------------------------------------|---------------------------------------|--------------------------------------------------|
| **Goal** | N-party secure computation | N-party secure computation | 2-party black-box group computation | Secret sharing | Oblivious shuffling/matrix mult |
| **Group choice** | Parameterized over G (any non-solvable -> NC^1) | Fixed S_5 (contains A_5, smallest non-solvable) | Any non-abelian G | Any non-abelian G | S_n or GL_n |
| **What is distributed** | Columns of monodromy table (permutation endpoints per party) | Randomizing polynomial shares of branching program | Group elements (a,c) to Alice, (b,d) to Bob with a+b+c+d=0 | Group element shares; product = secret | Correlated sub-permutations |
| **Computation class** | NC^1 (any non-solvable G) | NC^1 (S_5 suffices) | Black-box group circuits | N/A (sharing only) | Specific operations (shuffle, linear maps) |
| **Threshold / reconstruction** | AG code on covering curve; genus determines gap | Composable with Shamir (genus-0 AG code, no gap) | N/A (2-party) | Group product | N/A |
| **Security model** | Info-theoretic, semi-honest, passive | Perfect, semi-honest | Perfect, passive | Perfect | Computational (DDH) or info-theoretic |
| **Security quantification** | var_dist bound: eps + 2(T-1)/N, computable from rho | Simulation-based | Simulation-based (completeness proof) | Perfect reconstruction | Simulation-based |
| **Round complexity** | L rounds (general); RAAG -> Foata depth (upper bound) | Linear in branching program length | 1 round (given correlations) | N/A | 1 round (online) |
| **Formal verification** | 50 Rocq files, 8 Axiom declarations (all in monster instance) | None | None | None | None |

### Key structural differences

**1. Computation: same power, different parameterization**

All non-solvable groups compute NC^1 (Barrington-Therien). Barrington-based MPC fixes S_5 (which contains A_5, the smallest non-solvable group). SMC-PGG parameterizes over G, but this does NOT give more computational power — it affects **security parameters**: different G gives different N (sheets), different eps (distance from uniform on S_N), different fiber sizes. The choice of G is a security tuning knob, not a computation knob.

**2. Threshold: Shamir IS genus-0 AG code**

Shamir's secret sharing is polynomial evaluation on the projective line P^1 — a Reed-Solomon code, which is an AG code at genus 0. The Goppa bound at genus 0 gives distance = n - k + 1 (MDS), so threshold = k exactly, no gap.

This means:
- SMC-PGG at genus 0 **recovers Shamir** (no threshold gap)
- SMC-PGG at genus > 0 gets **worse threshold** (gap <= 2g)
- Barrington-based MPC composed with Shamir = Barrington + genus-0 AG code
- The genus is determined by G via Riemann-Hurwitz, so **G determines both security and threshold simultaneously** — they are coupled, not independently tunable

This coupling is the core insight of the `AlgebraicRigidity` record: choosing a larger G may improve security (larger search space, smaller eps) but worsen threshold (higher genus). Whether this tradeoff is favorable depends on the application.

**3. Reconstruction: covering space bridge**

Only SMC-PGG connects group theory to algebraic geometry via covering spaces:
- Monodromy group G -> covering curve C -> genus g(C) via Riemann-Hurwitz -> AG code on C -> threshold scheme
- This bridge is mathematically novel but **constrains** rather than enables: the genus is forced by the group choice, unlike Shamir where threshold is freely chosen

ZAS correlations and Barrington-based MPC have no analogue of this bridge — they don't touch algebraic curves or AG codes.

**4. Round complexity: algebraic characterization**

For any group G with a word of length L, round complexity is trivially L (one generator per round). When the generators carry a RAAG independence graph, commuting generators can execute in parallel, reducing depth to the Foata normal form depth. This is a clean algebraic characterization absent from other protocols. It doesn't yield *fewer* rounds than L — it gives an upper bound on how many rounds a given algebraic choice requires, and quantifies the parallelism available.

**5. Security quantification: computable bound vs. simulation**

SMC-PGG gives a concrete, computable variational distance bound (eps + 2(T-1)/N) derived from the monodromy representation. This is weaker than simulation-based security (used by Barrington-based and ZAS) but more explicit — you can compute the bound from G and rho without constructing a simulator.

### What SMC-PGG genuinely contributes

1. **Covering space perspective**: Connecting monodromy groups to AG codes via Riemann-Hurwitz. No other protocol in this family uses algebraic geometry this way. This reveals that the security/threshold tradeoff is governed by genus.

2. **Coupled parameter framework**: The `AlgebraicRigidity` record formalizes that one algebraic choice (G + generators) determines search space, security, and threshold gap. Round complexity (trivially L; refined to Foata depth when RAAG commutation is specified) and computational power (NC^1 for non-solvable G) are derived separately. Other protocols treat these as independent design decisions.

3. **Machine-checked proofs**: 50 Rocq files. EasyCrypt has formalized Maurer's MPC (abelian/linear, active security); Isabelle/CryptHOL has 2-party multiplication. No non-abelian group MPC has formal verification.

### What SMC-PGG does NOT contribute

1. **More computational power**: NC^1 regardless of G choice, same as Barrington with S_5.
2. **Better threshold**: Genus coupling means potentially worse threshold than Shamir (genus-0). Barrington + Shamir gets optimal threshold for free.
3. **Stronger security model**: Semi-honest only, weaker than simulation-based security achieved by Barrington-based and ZAS.
4. **Practical efficiency**: Research prototype, not deployment-ready. No performance comparison with existing systems.

### Honest summary

Compared to the non-abelian group MPC family, SMC-PGG is not a better protocol on any operational axis. Its contribution is a **mathematical framework** that:
- Reveals the covering-space structure underlying group-based MPC
- Makes the security/threshold tradeoff explicit via genus
- Provides the first formal verification of a non-abelian group MPC
- Connects three independent pipelines (protocol, solver, security proofs) end-to-end via `certified_from_witness` and `ar_protocol_correct`, with a concrete instantiation for the star-graph instance (`star_certified_1`, `star_protocol_correct`)

The framework's value is in **understanding** — showing that protocol properties are algebraically coupled — rather than in **capability**.
