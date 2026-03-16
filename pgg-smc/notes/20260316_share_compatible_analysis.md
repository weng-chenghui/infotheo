# Analysis: `share_compatible` Is Unsatisfiable — Value vs. Coordinate Mismatch

**Date**: 2026-03-16
**Status**: Architectural analysis
**Scope**: All genus instances (genus 0 through genus g)
**Files affected**: `cover_genus0.v`, `cover_genus1.v`, `cover_genus2.v`, `code_compatibility.v`

## 1. The Problem

The hypothesis `rs_share_compat` in `cover_genus0.v:107` (and analogous hypotheses in all other genus files) is **mathematically unsatisfiable** for non-trivial monodromy groups. This is not a proof difficulty — it is a domain-modeling error.

### Affected hypotheses

| File | Hypothesis | Code type |
|------|-----------|-----------|
| `cover_genus0.v:108` | `rs_share_compat` | RS code, d=1 |
| `cover_genus1.v:216` | `ag_ec_share_compat` | AG on elliptic curve |
| `cover_genus1.v:399` | `ag_g_share_compat` | AG on hyperelliptic, genus g |
| `cover_genus2.v:218` | `ag_g2_share_compat` | AG on hyperelliptic, genus 2 |

All use the same broken pattern:
```
sigma_X h x = toF (rho h (ofF x))
```
where `toF/ofF` is an enumerative bijection between sheets `'I_N` and field elements `F` via `enum_val`/`enum_rank`.

## 2. The Architecture (Current, Broken)

The current bridge chain from monodromy to threshold compatibility:

```
ts_compatible (act : gT → shareT → shareT)
  "applying act g to each share VALUE preserves reconstruction"
         ↓  (bridge: share_compat_massey_compat, in code_compatibility.v)
share_compatible C (sigma : F → F)
  "applying sigma to share VALUES of a codeword yields another codeword"
         ↓  (axiom: rs_share_compat — UNSATISFIABLE for d=1)
sigma0 h x = toF (rho h (ofF x))
  "monodromy-induced field permutation"
```

### `share_compatible` definition (from `code_compatibility.v:49-52`)

```coq
Definition share_compatible (sigma : F -> F) : Prop :=
  forall (s : F) (shares : 'rV[F]_n'.+1),
    massey_codeword s shares \in C ->
    massey_codeword s (\row_(j < n'.+1) sigma (shares ord0 j)) \in C.
```

This says: applying `sigma` to each share VALUE (while fixing the secret `s`) must preserve code membership.

### `ts_compatible` definition (from `pgg_sharing_framework.v:94`)

```coq
Definition ts_compatible (act : gT -> shareT -> shareT) : Prop :=
  forall (g : gT) (s : secretT) (shares : T.-tuple shareT),
    g \in G -> ts_valid ts s shares ->
    ts_recon ts [tuple act g (tnth shares i) | i < T] = s.
```

This says: applying `act g` to each share VALUE independently must preserve reconstruction.

## 3. Impossibility Proof for RS d=1

**Claim**: For the Reed-Solomon code `RS.code a n 1` with `n ≥ 2`, the only `sigma : F → F` satisfying `share_compatible` is `sigma = id`.

**Proof sketch**:

RS.code with d=1 has parity-check matrix PCM = `[a^j | j < n]` (one row). A codeword `c = (c_0, c_1, ..., c_{n-1})` satisfies:

$$\sum_{j=0}^{n-1} c_j \cdot a^j = 0$$

In Massey's construction, `massey_codeword s shares` puts `s` at position 0 and `shares` at positions `1, ..., n-1`. So a valid codeword satisfies:

$$s + \sum_{j=1}^{n-1} v_j \cdot a^j = 0$$

The share space for a given secret `s` is:
$$\mathcal{S}(s) = \{(v_1, ..., v_{n-1}) : s + \sum_{j=1}^{n-1} v_j \cdot a^j = 0\}$$

This is a coset of the hyperplane $\ker(\sum v_j \cdot a^j)$, which has dimension $n-2$. The code has dimension $n-1$, so the share space spans $F^{n-1}$ as $s$ varies.

`share_compatible` requires that for ALL `s`:
$$\text{if } (v_1, ..., v_{n-1}) \in \mathcal{S}(s) \text{ then } (\sigma(v_1), ..., \sigma(v_{n-1})) \in \mathcal{S}(s)$$

Since the secret `s` is FIXED (not transformed), `sigma` must preserve each coset $\mathcal{S}(s)$ individually. Since these cosets partition $F^{n-1}$ and $\sigma$ must preserve each one, $\sigma$ must preserve the linear functional $\ell(v) = \sum v_j \cdot a^j$.

For a linear $\sigma$: $\ell(\sigma(v)) = \ell(v)$ for all $v$ implies $\sigma$ acts as identity on the support of $\ell$. Since $a^1, ..., a^{n-1}$ are all distinct and nonzero (generator of $F^\times$), the functional has full support. Hence $\sigma = \text{id}$ on each coordinate.

For a general (nonlinear) $\sigma$: the constraint is even stronger. $\sigma$ must be a permutation of $F$ that preserves every affine hyperplane of the form $\{v : \sum v_j a^j = -s\}$ for each $s \in F$. This forces $\sigma$ to be a linear map (it preserves the affine structure), reducing to the linear case.

**QED**: `share_compatible sigma` with `sigma = toF ∘ rho g ∘ ofF` for non-trivial $g$ is impossible.

## 4. Root Cause: Value vs. Coordinate Mismatch

### What monodromy does (geometrically)

In covering space theory, the monodromy representation $\rho : G \to S_N$ permutes **sheets** of the covering. Each sheet corresponds to a **point in the fiber** over a base point. When we transport along a loop, the sheets get permuted — this is a **coordinate permutation** (which sheet is which), not a value transformation.

### What `share_compatible` assumes

`share_compatible` applies `sigma` to the **value** at each coordinate position. The codeword entry at position $i$ gets transformed: $c_i \mapsto \sigma(c_i)$. The position $i$ stays the same.

### The conflation via `toF/ofF`

The bijection `toF : 'I_N → F` (via `enum_val`) and `ofF : F → 'I_N` (via `enum_rank`) identifies sheets with field elements **enumeratively**: sheet 0 ↔ field element 0, sheet 1 ↔ field element 1, etc. This identification has **no algebraic meaning** — it doesn't respect the group action on sheets or the field operations on `F`.

When monodromy permutes sheet $i$ to sheet $\rho(g)(i)$, the transport interprets this as: "the field value at position $i$ changes from $\text{toF}(i)$ to $\text{toF}(\rho(g)(i))$." This is `sigma0 g x = toF (rho g (ofF x))`.

But this is wrong. Monodromy should change **which position** the party's share occupies, not **what value** sits at that position.

### Sheet IDs are coordinates, not values

A sheet in a covering space is a **coordinate label** — it identifies which copy of the base space a point lies in. The deck transformation (monodromy) permutes these labels. In the evaluation code context:

- Each sheet corresponds to an **evaluation point** on the algebraic curve
- The codeword entry at position $i$ is the function value $f(\alpha_i)$ where $\alpha_i$ is the evaluation point for sheet $i$
- Monodromy permutes the evaluation points: $\alpha_i \mapsto \alpha_{\rho(g)(i)}$
- This is a **coordinate permutation** of the codeword: $(c_0, c_1, ...) \mapsto (c_{\rho(g)^{-1}(0)}, c_{\rho(g)^{-1}(1)}, ...)$

The current code treats sheet indices as **values in the codeword** rather than **positions in the codeword**. This is the fundamental error.

## 5. Tier 1 Fix: Direct `ts_compatible` Hypotheses

Replace the broken bridge chain with a direct hypothesis at each genus level.

### Before (cover_genus0.v)
```coq
Definition sigma0 (h : {perm 'I_N}) (x : F) : F := toF (h (ofF x)).
Hypothesis rs_share_compat : share_compatible C sigma0.  (* UNSATISFIABLE *)

Lemma ts0_compatible : @ts_compatible ... ts0 (fun g x => rho g x).
Proof. ... share_compat_massey_compat ... Qed.
```

### After
```coq
Hypothesis genus0_ts_compat :
  @ts_compatible _ G _ _ ts0 (fun g x => rho g x).
```

This is logically honest: it states exactly what's needed (monodromy-compatible threshold scheme) without routing through an unsatisfiable intermediate.

**Impact**: No change in axiom count. One hypothesis replaces another of equal logical strength. All downstream theorems (`genus0_covering`, `shamir_exact`, tradeoff theorems) still hold.

## 6. Tier 2 Feasibility: Coordinate-Permutation `ts_compatible`

### The goal

Define a version of `ts_compatible` where monodromy acts as coordinate permutation, and PROVE it from code automorphism properties.

### What coordinate permutation looks like

Instead of:
```coq
ts_recon ts [tuple act g (tnth shares i) | i < T] = s    (* value transformation *)
```
we want:
```coq
ts_recon ts [tuple tnth shares (perm g i) | i < T] = s   (* coordinate permutation *)
```

### When value transformation = coordinate permutation

These coincide if the starting sheets `starts` are a G-orbit segment:
$$\text{starts}_{\text{perm}(g)(i)} = \rho(g)(\text{starts}_i) \quad \text{for some permutation perm}(g)$$

Then party $i$ sending $\rho(g)(\text{starts}_i)$ is the same as party $\text{perm}(g)(i)$ sending $\text{starts}_{\text{perm}(g)(i)}$.

### Requirements for provability

1. **G-stable evaluation points**: `sigma0 g` must permute the set $\{\text{toF}(\text{starts}_i)\}_{i < T}$ — the starting sheets must form a G-stable set

2. **G-fixed secret point**: `sigma0 g` must fix $\text{toF}(s)$ (the secret's evaluation point). Since $\sigma_0(g)(\text{toF}(s)) = \text{toF}(\rho(g)(s))$, this requires $\rho(g)(s) = s$ — the secret sheet must be a fixed point of G

3. **Algebraically compatible bijection**: `toF` must map sheets to field elements respecting both the group action and the code structure. The current enumerative bijection does not satisfy this

### Assessment

**Requirement 1** (G-stable evaluation points) is a reasonable structural hypothesis — it says the covering is compatible with the code.

**Requirement 2** (G-fixed secret sheet) is restrictive. Some monodromy groups fix a sheet (cyclic coverings fix branch point fibers), but not all. For the PGG protocol, this would mean: the secret sheet is never moved by any deck transformation. This is a genuine constraint that limits which coverings can be used.

**Requirement 3** (algebraic bijection) requires replacing the enumerative `toF/ofF` with a bijection that respects the algebraic structure. This is a substantial redesign of `rs_massey_bridge.v`.

### New infrastructure needed

- Fixed-point theory for covering spaces (G acts on N sheets, existence of fixed points)
- Evaluation-point-compatible bijection (not enumerative — algebraic)
- Code automorphism formalization (permutation of evaluation points preserves code membership)
- Reconstruction invariance under coordinate permutation (Lagrange interpolation for RS, AG decoding for higher genus)

**Estimated scope**: ~500-800 LOC, touching `pgg_sharing_framework.v`, `code_compatibility.v`, `massey.v`, all `cover_genusX.v`, `rs_massey_bridge.v`, `ag_massey_bridge.v`.

### Verdict

Tier 2 is **sound in principle** — the mathematics works. But it requires formalizing the algebraic geometry of evaluation codes on covering spaces, which is the "deep algebraic geometry" this project deliberately axiomatized away. It is a research contribution in its own right, not a routine refactoring.

## 7. Implementation History

### Tier 1 (2026-03-16, commit `ed5fda8`)

All `share_compatible` hypotheses replaced with direct `ts_compatible` hypotheses. Impossibility remark added to `code_compatibility.v`.

### Tier 2 (2026-03-16, commit `3d3be45`)

Replaced unsatisfiable `ts_compatible` (value transformation) with satisfiable `ts_perm_compatible` (coordinate permutation). Created `coord_perm_compatible.v` with the full bridge from code automorphisms to scheme-level compatibility. Deleted all dead `share_compatible` infrastructure (`code_compatibility.v`, bridge lemmas in `ag_massey_bridge.v`, old `ts_compatible` definition and proofs). See "The interface point" above for Before/After architecture.

## 8. The Protocol Is Not Broken — Security and Reconstruction Are Orthogonal

A natural concern: does the `share_compatible` impossibility mean the PGG protocol itself is broken?

**No.** The protocol's security properties and its reconstruction mechanism are entirely orthogonal concerns that connect only at a single interface point.

### Security side (completely unaffected)

The following properties depend only on the group G, the RAAG generator structure, and word combinatorics — none of them reference the reconstruction scheme, Massey's construction, or `share_compatible`:

- **Collusion bounds** from RAAG trace monoid / partial permutation lookup tables → depends on G and generator set
- **Word length L** → round complexity, depends on RAAG structure
- **Non-abelian requirement** → information-theoretic security, depends on G
- **Fiber equidistribution** → depends on `word_eval` and generator distribution
- **SecurityWitness**, **AlgebraicRigidity** → all group-theoretic

### Reconstruction side (what the impossibility affects)

Only these components are affected:

- How the dealer encodes the secret into starting sheets (the codeword validity constraint)
- Why endpoints still reconstruct correctly after monodromy (the compatibility proof)
- The (k, T) threshold gap derived from code parameters

### The interface point

The two sides connect at exactly one point: the `CoveringScheme` record, which bundles a `ThresholdScheme` (reconstruction) with compatibility (how monodromy interacts with share structure). The security side never looks inside the compatibility proof.

#### BEFORE (Tier 1 — unsatisfiable axiom)

```
CoveringScheme record:
  cs_data       : CoveringData         ← Riemann-Hurwitz (proved)
  cs_scheme     : ThresholdScheme      ← from AG code via Massey (proved)
  cs_compatible : ts_compatible        ← AXIOM (unsatisfiable for non-trivial G)
  cs_gap        : ts_T ≤ ts_k + 2g    ← from code parameters (proved)

ts_compatible (act : gT → shareT → shareT) :=
  ∀ g s shares, g ∈ G → valid s shares →
    recon [tuple act g (tnth shares i) | i < T] = s
                  ↑
                  applies rho g to each share VALUE independently
                  ← WRONG: monodromy permutes COORDINATES, not values

Protocol correctness:
  pgg_secret_invariant :
    ts_compatible ts (fun g x => rho g x) →        ← hypothesis from cs_compatible
    recon(endpoints) = secret

Axiom chain per genus file:
  Hypothesis tsX_compatible :                       ← UNSATISFIABLE
    @ts_compatible _ G _ _ tsX (fun g x => rho g x)
```

#### AFTER (Tier 2 — satisfiable axioms, implemented 2026-03-16)

```
CoveringScheme record:
  cs_data            : CoveringData         ← Riemann-Hurwitz (proved)
  cs_scheme          : ThresholdScheme      ← from AG code via Massey (proved)
  cs_perm            : gT → {perm 'I_T}    ← NEW: monodromy-induced share reordering
  cs_perm_compatible : ts_perm_compatible   ← AXIOM (satisfiable from code automorphism)
  cs_gap             : ts_T ≤ ts_k + 2g    ← from code parameters (proved)

ts_perm_compatible (perm : gT → {perm 'I_T}) :=
  ∀ g s shares, g ∈ G → valid s shares →
    recon [tuple tnth shares (perm g i) | i < T] = s
                                ↑
                                REORDERS shares by coordinate permutation
                                ← CORRECT: matches what monodromy actually does

Protocol correctness:
  pgg_secret_invariant_perm :
    G_stable_starts →                              ← NEW explicit hypothesis
    ts_perm_compatible ts perm →                   ← from cs_perm_compatible
    recon(endpoints) = secret

  G_stable_starts :=
    ∀ g ∈ G, ∀ i, rho g (starts_i) = starts_{perm g i}
    "monodromy maps starting sheets to starting sheets via the same perm"

Axiom chain per genus file (2 satisfiable axioms):
  Variable tsX_perm : gT → {perm 'I_T}
  Hypothesis tsX_perm_compatible :
    @ts_perm_compatible _ G _ _ tsX tsX_perm       ← SATISFIABLE

New infrastructure (coord_perm_compatible.v, ~260 LOC):
  coord_perm_compatible C σ   : col_perm σ preserves code membership
  restrict_perm0_val σ Hfix   : restricts σ fixing pos 0 to share indices
  massey_codeword_col_perm    : col_perm σ (codeword s shares) = codeword s (col_perm σ_sh shares)
  massey_perm_compatible      : code_auto + fix_0 ⟹ ts_perm_compatible for massey_scheme
  transport_perm_compatible   : ts_perm_compatible lifts through transport_scheme

Deleted dead code:
  code_compatibility.v        : share_compatible, share_compat_massey_compat, transport_ts_compatible
  ag_massey_bridge.v §2       : ag_massey_share_compat, ag_genus_share_compat
  pgg_sharing_framework.v     : ts_compatible, ts_compatible_id, pgg_secret_invariant (old)
```

#### Architecture comparison

```
BEFORE:  code auto ──(impossible)──→ share_compatible ──→ ts_compatible ──→ protocol correct
                                         ↑ value transformation (WRONG)

AFTER:   code auto ──(satisfiable)──→ coord_perm_compatible ──→ ts_perm_compatible ──→ protocol correct
                                         ↑ coordinate permutation (CORRECT)    + G_stable_starts
```

### How Tier 2 saves the Massey scheme

The protocol itself doesn't change. Party i still sends `e_i = rho(P)(start_i)`. What changes is the proof of WHY reconstruction works:

**Current (broken) proof path**: interpret `rho(P)(start_i)` as a VALUE transformation `sigma(v_i)` on each share → require `(s, sigma(v_1), ..., sigma(v_T)) ∈ C` → this is `share_compatible` → unsatisfiable.

**Tier 2 (correct) proof path**: if starting sheets are G-stable, then `rho(P)(start_i) = start_{π(P)(i)}` for some permutation π of party indices → the endpoint tuple is a REORDERING of the original shares → the full vector `(ofF(s), ofF(e_0), ..., ofF(e_T))` is a coordinate permutation of the original codeword → code membership preserved (evaluation codes are invariant under evaluation-point permutations) → Massey reconstruction extracts position 0 → recovers s.

The three requirements for Tier 2:
1. **G-stable starting sheets**: `{start_i}` is closed under `rho(g)` → monodromy acts as a party-index permutation
2. **Code automorphism**: C is invariant under the induced coordinate permutation (standard for AG codes — curve automorphisms induce code automorphisms)
3. **Fixed secret position**: π(g) fixes position 0 → secret is preserved

For AG codes at ALL genus values, requirement 2 is a standard fact: automorphisms of the underlying algebraic curve permute evaluation points and induce code automorphisms. This works uniformly for RS (genus 0), elliptic AG (genus 1), hyperelliptic AG (genus 2), and general AG (genus g).

### Summary

The `share_compatible` impossibility is a **formalization-level bug** (wrong abstraction for the compatibility proof), not a **protocol-level bug**. The protocol is sound; the security properties are untouched; and the Massey reconstruction scheme works correctly once the compatibility proof uses coordinate permutation instead of value transformation.

## 9. Two Reconstruction Schemes and When Each Applies

The formalization contains two reconstruction schemes:

| | Sum-mod-N | Massey/code-based |
|---|-----------|-------------------|
| **Reconstruction** | `(Σ e_i) mod N` | Find s such that `(s, shares) ∈ C` |
| **Threshold** | T-out-of-T only (k = T) | (k, T) with k ≤ T from dual distance |
| **Compatibility** | `preserves_sum_mod`: purely group-theoretic | `share_compatible`: requires code automorphism (Tier 2) |
| **Genus 0** | Sufficient | Gives same k = T (no benefit over sum-mod-N) |
| **Genus > 0** | Cannot express k < T gap | Required — the gap T - k is the whole point |

For genus 0, sum-mod-N is simpler and has a clean compatibility condition. For genus > 0, the Massey/AG code scheme is necessary to capture the threshold gap that the covering tradeoff theorem relates to genus.

## 10. Implications for the Paper

The `share_compatible` impossibility does NOT weaken the formalization's claims:

- **SecurityWitness**: Fully proved (no `share_compatible` involved)
- **ThresholdWitness**: Axiomatized at the `ts_perm_compatible` level (Tier 2 makes this satisfiable)
- **AlgebraicRigidity**: Still bundles all four properties; the axiom boundary is at covering scheme existence + code automorphism + G-stable starts
- **Tradeoff theorem**: Unaffected — uses only `cs_gap` and `cs_data`, never compatibility

The paper should state: "The covering scheme coordinate-permutation compatibility (`ts_perm_compatible`) is axiomatized from code automorphism hypotheses. Proving these hypotheses for specific AG codes requires formalizing curve automorphisms — algebraic geometry beyond the scope of this formalization."
