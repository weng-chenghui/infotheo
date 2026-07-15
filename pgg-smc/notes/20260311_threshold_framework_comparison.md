# (k,T)-Threshold via AG Codes: Framework Comparison

**Date:** 2026-03-11
**Status:** Analysis complete — AG Codes on Covering Curves selected

## 1. Problem Statement: The (T,T) Barrier

The current PGG-SMC formalization achieves **(T,T)-threshold**: all T parties are needed for reconstruction, and any T−1 colluding parties learn nothing. This is the sum-mod-N secret sharing scheme:

- **Share:** split secret s into T random values summing to s (mod N)
- **Reconstruct:** sum all T shares
- **Privacy:** any T−1 shares are uniformly random (proved as `partial_sum_no_info`)

The limitation: reconstruction requires *all* T shares. If any single party drops out, reconstruction fails. A **(k,T)-threshold** scheme requires only k-of-T shares for reconstruction while maintaining privacy against up to k−1 colluders.

### The MDS Abstraction

The key mathematical insight: a (k,T)-threshold scheme encodes a "shape" (polynomial, codeword, section) that is **pinned by k points**. The remaining T−k shares are redundant — any k suffice to recover the shape.

This is precisely the **MDS (Maximum Distance Separable)** property: a [T, k, T−k+1] code where every k×k submatrix of the generator matrix is invertible.

## 2. Framework Comparison

### Comparison Table

| Framework | (k,T) threshold | Covering-space interpretation | Multiplicative (MPC) | Formalization feasibility | Asymptotic optimality | Genus generalization |
|---|---|---|---|---|---|---|
| **Shamir (Reed-Solomon)** | ✅ exact | ❌ genus 0 only | ✅ (BGW88) | ✅ easy | ✅ for large fields | ❌ genus 0 fixed |
| **Massey (linear codes)** | ✅ general | ❌ abstract codes | ⚠️ not automatic | ✅ moderate | depends on code | ❌ no geometric link |
| **Packed SS (Franklin-Yung)** | ✅ with packing | ❌ | ✅ | ⚠️ moderate | ✅ amortized | ❌ |
| **Algebraic Geometry codes** | ✅ quasi-threshold | ✅ natural | ✅ (Chen-Cramer) | ⚠️ hard but structured | ✅ (Garcia-Stichtenoth) | ✅ full tower |
| **Lattice-based SS** | ✅ | ❌ | ❌ | ❌ very hard | ❌ | ❌ |
| **AG Codes on Covers** | ✅ quasi-threshold | ✅ **exact match** | ✅ (Chen-Cramer) | ⚠️ hard but natural | ✅ | ✅ **native** |

### Criteria Definitions

- **(k,T) threshold:** Can reconstruct from k < T shares while k−1 shares reveal nothing
- **Covering-space interpretation:** Natural connection to PGG-SMC's monodromy/covering framework
- **Multiplicative (MPC):** Supports secure multiplication (not just addition) on shares
- **Formalization feasibility:** How hard to formalize in Rocq/MathComp
- **Asymptotic optimality:** Threshold gap vanishes for large parameters
- **Genus generalization:** Extends naturally across curve genera

## 3. Per-Framework Analysis

### 3.1 Shamir Secret Sharing (Reed-Solomon)

**What it is:** Secret = f(0) for a random degree-(k−1) polynomial f over F_q. Shares = f(α₁), ..., f(α_T) at distinct evaluation points.

**Why it fits:**
- Clean (k,T)-threshold: any k shares determine f by Lagrange interpolation
- Privacy is information-theoretic: k−1 evaluations of a degree-(k−1) polynomial are uniform
- MDS property: Vandermonde matrices are always invertible over distinct points

**Why it's not enough alone:**
- Lives on P¹ (genus 0) — no covering-space structure beyond trivial covers
- Doesn't connect to PGG-SMC's monodromy groups
- But it's the **essential genus-0 baseline** that AG codes generalize

**Formalization feasibility:** Easy. MathComp has `poly`, `horner`, matrix, and finite fields. Lagrange interpolation is a standard exercise.

### 3.2 Massey's Construction (Linear Codes → Secret Sharing)

**What it is:** Given an [n+1, k, d] linear code C, define: secret = c₀, shares = c₁,...,cₙ for codewords c ∈ C.

**Why it fits:**
- Unifies all linear secret sharing schemes under one construction
- Access structure determined by dual code C⊥
- Privacy threshold: d⊥ − 1 (dual minimum distance minus 1)
- Reconstruction threshold: n + 1 − d
- Shamir is the MDS special case: d⊥ − 1 = n + 1 − d = k

**Why it's not enough alone:**
- Abstract — no geometric content
- Multiplicative property doesn't come for free (need ★-product structure)
- No covering-space interpretation

**Formalization feasibility:** Moderate. Builds on infotheo's existing linear code foundations. The dual-code analysis requires careful work with code equivalences.

### 3.3 Packed Secret Sharing (Franklin-Yung)

**What it is:** Pack multiple secrets into one polynomial. Shares = evaluations. Amortize the threshold gap.

**Why it fits:**
- Efficient for batch computations
- Good amortized threshold

**Why it doesn't fit:**
- No geometric interpretation
- Adds complexity without connecting to covering spaces
- Better viewed as an optimization of Shamir, not a new framework

### 3.4 Algebraic Geometry Codes (Riemann-Roch Evaluation)

**What it is:** Replace P¹ with a curve C of genus g. Functions in L(D) (Riemann-Roch space for divisor D) are evaluated at rational points P₁,...,Pₙ.

**Key parameters:**
- Dimension: k = deg(D) − g + 1 (for deg(D) ≥ 2g − 1)
- Minimum distance: d ≥ n − deg(D)
- The genus g introduces a "gap": quasi-threshold is (t, t + 1 + 2g)

**Why it fits:**
- Natural generalization of Reed-Solomon (genus 0 → genus g)
- Curves with many rational points (Garcia-Stichtenoth towers) give asymptotically optimal codes
- Chen-Cramer (2006): AG secret sharing has the **multiplicative** property needed for MPC

**Formalization feasibility:** Hard but structured. Elliptic curves (genus 1) are concrete and well-studied. MathComp has finite fields; curve arithmetic can be built on top.

### 3.5 Lattice-Based Secret Sharing

**Why it doesn't fit:**
- No geometric interpretation connecting to covering spaces
- Post-quantum motivation is irrelevant for information-theoretic security
- Formalization of lattice problems in Rocq is extremely difficult
- Not multiplicative in general

### 3.6 AG Codes on Covering Curves ★ (Selected)

**What it is:** The synthesis — AG codes where the curve C is specifically a **Galois cover** of P¹ (or another base curve) with covering group G.

**Why it wins (all criteria simultaneously):**

1. **(k,T)-threshold:** Inherits from AG code theory. Quasi-threshold with gap 2g, which vanishes asymptotically.

2. **Covering-space interpretation — exact match:**
   - A Galois cover π: C → B with group G has fibers π⁻¹(b) that are G-orbits
   - Evaluating L(D)-functions on a fiber = computing shares for the parties in that G-orbit
   - The monodromy action permutes points within fibers = PGG-SMC's party permutation structure
   - The Galois group of the cover = the deck transformation group = PGG-SMC's monodromy group

3. **Multiplicative (MPC):** Chen-Cramer's result applies directly.

4. **Formalization path:** Start with Shamir (genus 0), add Massey's abstraction, then build AG codes on specific curves. The covering-space bridge connects to existing `pgg_interface.v`.

5. **Asymptotic optimality:** Garcia-Stichtenoth towers of function fields give sequences of curves where n/g → q^{1/2} − 1, making the threshold gap negligible.

## 4. AG Code ↔ Covering Space Bridge

The key conceptual bridge:

```
PGG-SMC world                    AG Code world
─────────────                    ─────────────
Covering space X → Y             Galois cover C → B
Deck transformation group G      Galois group G
Fiber over a point               G-orbit of rational points
Monodromy representation ρ       Galois action on fiber
Party i                          Evaluation point P_i
Share of party i                 f(P_i) for f ∈ L(D)
Reconstruction (sum-mod-N)       Interpolation / AG decoding
Privacy (partial_sum_no_info)    Dual distance bound (d⊥ − 1)
```

The current `pgg_interface.v` defines:
- `MonodromyReprType`: a group G with a representation ρ: G → S_T
- `share`: distributes a secret to T parties via ρ
- `compute`: local computation on shares

The AG code upgrade replaces:
- `share` = polynomial/AG-function evaluation on fiber points
- Reconstruction = Lagrange interpolation (genus 0) or AG decoding (genus g)
- Privacy = information-theoretic bound from code distance

## 5. Compatible (G, Scheme) Pairs

The framework is **parametric over (monodromy group, secret sharing scheme) pairs** linked by a **compatibility condition**: the monodromy group G must preserve the sharing scheme's reconstruction property. This is formalized as:

```
compatible (M : MonodromyReprType) (ss : SharingScheme) :=
  ∀ g ∈ G, ∀ s, ∀ S with |S| ≥ k,
    reconstruct S (λ i. ρ(g)(share(s, i))) = reconstruct S (λ i. share(s, i))
```

The three instances form a hierarchy:

| Instance | Scheme | Compatible G | Threshold |
|----------|--------|-------------|-----------|
| **Sum-mod-N** | Σ s_i mod N | {σ : preserves_sum_mod σ} | (T,T) |
| **AG-on-covers** | AG evaluation on fibers | Aut(C/B) | quasi-(k, k+2g) |
| **Shamir** | Polynomial evaluation | AGL(1,q) | exact (k,T) |

Shamir is the **genus-0 corollary** of AG-on-covers, not a standalone framework.

## 6. Formalization Roadmap

### Phase 0: Abstract sharing framework + sum-mod-N instance (NEW)
- Define `SharingScheme` record (correctness + privacy axioms)
- Define `compatible` predicate linking monodromy to sharing
- Wrap existing sum-mod-N as `sum_mod_sharing` instance
- Prove `sum_mod_compatible` from `preserves_sum_mod`
- **File:** `pgg-smc/reconstruct/pgg_sharing_framework.v`
- **Milestone:** `sum_mod_compatible : compatible M (sum_mod_sharing ...)`

### Phase 1: Massey's abstraction
- Linear code → secret sharing construction
- Dual code analysis for access structure
- Shamir as MDS special case
- **Milestone:** `massey_privacy : d_dual C⊥ - 1 ≤ t → t-private`

### Phase 2: AG-on-covers instance (Instance 2)
- AG codes on Galois covering curves C → B
- Fiber evaluation = share distribution
- Covering automorphisms preserve AG evaluation
- Prove `compatible` for AG scheme
- **Milestone:** `ag_cover_compatible : compatible M (ag_cover_sharing ...)`

### Phase 3: Shamir as genus-0 corollary (Instance 3)
- Specialize AG-on-covers to genus 0 (C = P¹)
- Recover Lagrange interpolation as degenerate AG decoding
- AGL(1,q) as the compatible monodromy group
- **Milestone:** `shamir_from_ag : ag_cover_sharing (genus:=0) ≅ shamir_sharing`

### Phase 4: Integration with PGG-SMC
- Refactor `PGG_Interface` to reference `SharingScheme`
- Multiplicative property for MPC (Chen-Cramer)
- **Milestone:** `pgg_ag_threshold : k ≤ #|S| → reconstruct S = secret`

## 6. References

1. **Shamir, A.** (1979). "How to share a secret." *Communications of the ACM*, 22(11).
2. **Massey, J.L.** (1993). "Minimal codewords and secret sharing." *Proc. 6th Joint Swedish-Russian Workshop on Information Theory*.
3. **Chen, H. & Cramer, R.** (2006). "Algebraic geometric secret sharing schemes and secure multi-party computations over small fields." *CRYPTO 2006*.
4. **Garcia, A. & Stichtenoth, H.** (1996). "On the asymptotic behaviour of some towers of function fields over finite fields." *Journal of Number Theory*, 61(2).
5. **Fan, Y., Lin, L., & Wang, H.** (2021). "Threshold secret sharing from algebraic geometry codes." *IEEE Trans. Information Theory*.
6. **Ben-Or, M., Goldwasser, S., & Wigderson, A.** (1988). "Completeness theorems for non-cryptographic fault-tolerant distributed computation." *STOC 1988*.
7. **Cramer, R., Damgård, I., & Maurer, U.** (2000). "General secure multi-party computation from any linear secret-sharing scheme." *EUROCRYPT 2000*.
