# PGG Entropy Security: Connecting Protocol Program to Information-Theoretic Analysis

*2026-03-18*

## Motivation

DSDP's security proof chains: **Trace → Constraint → Fiber → Entropy → Security**. The trace captures the full protocol execution, the constraint creates linear fibers over Z/pqZ, and CRT guarantees uniform distribution over each fiber, yielding `H(V2,V3 | AliceView) = log(m) = H(V2,V3)` (zero leakage).

For PGG, the heaviest security concerns are at the **preparing stage** (group choice, generator parameters), not at runtime. The protocol execution is simple (dealer distributes shares, parties look up endpoints). But connecting the program to security analysis remains important for the paper narrative and for understanding what the protocol *actually reveals*.

## What VIEW_j Contains

From the piSMC protocol (`pgg_pismc.v`), party j receives:
- **share_j**: the column `[σ_{w_l}(s_j) | l = 1..L]` — how each word-letter permutation acts on j's starting sheet(s)
- **P_idx**: which word to evaluate (index into the L-tuple)

The secret to protect: `σ_P(s_i) = endpoint(word_eval(W), s_i)` for party i ≠ j.

## The Entropy Relation

**Ideal goal:**
```
H(σ_P(s_i) | VIEW_j) = H(σ_P(s_i)) = log(N)
```

**Realistic goal (ε-approximate):**
```
H(σ_P(s_i) | VIEW_j) ≥ log(N) - f(ε)
```

where ε is the existing var_dist parameter from `pgg_collusion_bound.v`.

## Why the DSDP Approach Doesn't Directly Transfer

### Fiber structure mismatch

| Property | DSDP | PGG |
|----------|------|-----|
| Domain | Z/pqZ (commutative ring) | S_N (noncommutative group) |
| Constraint | Linear: u₂v₂ + u₃v₃ = t | Permutation: σ(s_j) = a, σ ∈ achievable(L) |
| Fiber | Affine subspace, coset of ker | Arbitrary subset of 'I_N |
| Cardinality | Constant = m = pq (CRT) | Variable, instance-dependent |
| Distribution | Uniform (CRT guarantees) | Non-uniform in general |

**The fundamental gap**: In DSDP, the fiber `{(v2,v3) | u₂v₂ + u₃v₃ = t}` is a 1-dimensional affine subspace with exactly m elements, and CRT + independence of inputs guarantees uniform distribution over this subspace. In PGG, the "fiber" `{σ(s_i) | σ ∈ achievable(L), σ(s_j) = a}` is just a subset of `'I_N` with no algebraic structure — its size varies with `a`, and the induced distribution is generally non-uniform (words mapping s_j to the same a can cluster at certain values of s_i).

### Independence mismatch

DSDP's proof relies on `VarRV ⊥ CondRV` (inputs of different parties are independent random variables). In PGG, `Endpoint_i` and `Share_j` are both **deterministic functions of the same word W** — there is no independence to exploit. The correlation structure is entirely determined by the group's combinatorics.

### Pinsker direction issue

Pinsker's inequality gives `var_dist² ≤ ½ D_KL(P||Q)` — bounding var_dist FROM divergence. We need the reverse: from var_dist TO entropy. The correct tool is **entropy continuity** (Csiszár–Körner):

```
|H(P) - H(Q)| ≤ δ · log(N-1) + h(δ)    where δ = var_dist(P,Q)
```

This is NOT formalized in infotheo (Pinsker is, but wrong direction).

## Two Feasible Approaches

### Approach A: Entropy as Corollary of Existing var_dist (Recommended)

**Idea**: Don't redo the fiber analysis in entropy language. Instead, derive entropy bounds from the existing `collusion_bound` theorem via a general-purpose entropy-TV inequality.

**Chain**:
```
var_dist(adversary_marginal, uniform) ≤ ε + 2(T-1)/N     [existing theorem]
    ⟹  D_KL(adv || uniform) ≤ -log(1 - δ²/2)            [reverse Pinsker / Bretagnole-Huber]
    ⟹  H(endpoint_i) ≥ log(N) + log(1 - δ²/2)            [since D_KL(P||U) = log N - H(P)]
```

where δ = ε + 2(T-1)/N.

**Alternatively**, use the simpler bound: for distributions on N elements,
```
H(P) ≥ (1 - δ) · log(N)    when δ = var_dist(P, uniform) < 1
```

**Pros**: ~350-500 lines, reuses everything in `pgg_collusion_bound.v`, gives a clean paper statement.
**Cons**: Weaker than the var_dist bound (loses information); the entropy statement is derived, not primitive.

### Approach B: Direct Conditional Entropy via Fiber Analysis (Ambitious)

**Idea**: Define a joint probability space over words, build `Endpoint_i` and `Share_j` as proper random variables, and prove conditional entropy bounds directly.

**Probability space**: `T := L.-tuple 'I_Tg` with `P := fdist_uniform`.
```coq
Endpoint_i : {RV P -> 'I_N} := fun w => endpoint (word_eval w) s_i
Share_j : {RV P -> L.-tuple 'I_N} := fun w => [tuple endpoint (tnth sigmas (tnth w k)) s_j | k < L]
```

**The hard lemma** (conditional uniformity): For each share value `sh`:
```
∀ b : 'I_N, Pr[Endpoint_i = b | Share_j = sh] ≈ 1/N
```
This requires proving that words producing the same share at s_j distribute endpoint_i nearly uniformly — essentially re-deriving the var_dist bound at the conditional level.

**Pros**: Primitive entropy statement, parallels DSDP, connects program execution to information theory.
**Cons**: ~1100-1700 lines, fiber uniformity is hard without DSDP's algebraic shortcuts.

### Approach C: Perfect Case Only (Pragmatic Middle Ground)

**Idea**: Prove `H(Endpoint_i | VIEW_j) = log(N)` only under the strong hypotheses `weval_inj L` + `transitive_action` + `achievable(L) = G` (full group reached).

Under these conditions:
- σ_P is uniform over G
- For transitive G acting on 'I_N: conditioning on σ(s_j) = a leaves σ(s_i) uniform over 'I_N \ {a} (or 'I_N if s_i, s_j in different orbits)
- The conditional entropy equals log(N) or log(N-1) depending on whether s_i ≠ s_j forces σ(s_i) ≠ σ(s_j)

**Pros**: Clean, provable, connects to DSDP pattern.
**Cons**: Only covers the idealized case; real instances always have ε > 0.

## ε-Biased Word Distribution Perspective

The user's idea: if word letters are drawn from an ε-biased distribution (not perfectly uniform), the trace shows how much information each word permutation reveals about the posterior of uncorrupt parties' lookup tables.

**Clarification**: There are two different ε's:
1. **Output ε** (existing): `var_dist(rho_dist, uniform(S_N))` — how far the permutation distribution is from uniform
2. **Input ε** (proposed): bias in the word-letter distribution over `'I_Tg`

Under `weval_inj L`, these are related: `fdistmap_inj_uniform` converts input uniformity to output uniformity. Without injectivity, the word_eval map's fiber structure (multiple words → same permutation) complicates the relationship.

**For the paper narrative**: The input ε perspective is useful for explaining what "group choice" means operationally — choosing generators that maximize the achievable set size (minimize output ε) for a given word length L. The group parameters (Tg, N, commutation graph) "conclude as ε" in the sense that they determine the achievable set structure, which determines the fiber distribution, which determines the entropy gap.

## Recommendation

**Approach A + C combined**:

1. Prove the **perfect case** (H = log N) under idealized hypotheses — this gives the clean DSDP-parallel statement and connects program execution to entropy.
2. Derive the **ε-approximate case** as a corollary of the existing var_dist bound — this covers all real instances with minimal new infrastructure.
3. State the **mutual information form** `I(Endpoint_i ; VIEW_j) ≤ f(ε, T, N)` as the paper's summary statement — this is the most natural information-theoretic formulation.

## Estimated Scope

| Component | Lines | Difficulty |
|-----------|-------|------------|
| `pgg_entropy_trace.v`: probability space, RVs, VIEW_j | 200-300 | Medium |
| Perfect case: H = log(N) under strong hypotheses | 200-300 | Medium |
| Entropy-TV library lemma (general infrastructure) | 150-250 | Hard (new) |
| ε-approximate corollary from collusion_bound | 100-150 | Easy |
| **Total** | **650-1000** | |

## Connection to Existing Infrastructure

| What | Where | Reusable? |
|------|-------|-----------|
| `rho_from_words` (distribution over S_N) | `pgg_collusion_bound.v` | Yes, as base distribution |
| `collusion_bound_unconditional` | `pgg_collusion_bound.v` | Yes, for Approach A |
| `fdistmap_eval_uniform` | `pgg_collusion_bound.v` | Yes, for ideal case |
| `weval_inj` + `word_eval` | `pgg_weval_inj.v` | Yes, for injectivity hypotheses |
| `achievable`, `endpoint` | `pgg_interface.v` | Yes, core definitions |
| `cond_entropy`, `cPr` | `information_theory/entropy.v` | Yes, entropy API |
| Pinsker's inequality | `probability/pinsker.v` | Partial (wrong direction) |
| `cPr_uniform_fiber` | DSDP `entropy_fiber_zpq.v` | Pattern only, not direct |
