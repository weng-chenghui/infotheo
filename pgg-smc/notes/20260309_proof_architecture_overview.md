# 2026-03-09: PGG-SMC Proof Architecture Overview

## Context

The PGG-SMC (covering-space-based MPC) formalization has grown into paper-level work. This note captures the overall proof architecture and clarifies how the security-fault-tolerance tension is established.

## The Three-Layer Architecture

```
Layer 3: Security Analysis
  ┌─────────────────────────────────────────────────┐
  │  collusion_bound: var_dist(adv, ideal) ≤ ε + 2(T-1)/N  │
  │  Grover: adversary search cost ≥ κ^L            │
  │  Abelian collapse: search_space ≤ C(L+Tg-1,Tg-1) │
  └──────────────────────┬──────────────────────────┘
                         │ depends on search_space(L)
Layer 2: Trace Monoid (Cartier-Foata)
  ┌─────────────────────────────────────────────────┐
  │  search_space(L) ≤ n_traces(L) ≤ Tg^L          │
  │  clique polynomial recurrence = trace count     │
  │  L-freeness: achieves Tg^L (exponential)        │
  └──────────────────────┬──────────────────────────┘
                         │ depends on group structure
Layer 1: Protocol (Covering Space MPC)
  ┌─────────────────────────────────────────────────┐
  │  Share: dealer distributes sheets s_i           │
  │  Compute: party evaluates ρ(P)(s_i)             │
  │  Reconstruct: Σ endpoints ≡ m (mod N)           │
  │  (k,T)-Ramp: partial coalition recovers partial │
  └─────────────────────────────────────────────────┘
```

## The Security-Fault-Tolerance Tension

The protocol has **two knobs** — word length L and group structure — and they pull in opposite directions:

**Security wants:**
- Large search space → adversary must search κ^L elements
- Non-abelian group → avoids polynomial collapse
- L-free generators → search_space = Tg^L (maximal)

**Fault-tolerance wants:**
- Σ endpoints ≡ m (mod N) → full coalition always recovers
- (k,T)-ramp → partial coalitions recover partial information via covered edges
- But larger search space means ε = 2(N! - Tg^L)/N! grows, loosening the collusion bound

**The core tension formula:**
```
var_dist(adversary, ideal) ≤ ε + 2(T-1)/N
                              ↑         ↑
                    search space    threshold
                    quality         structure
```

- Making ε small (good security) requires Tg^L ≈ N! — but N! grows factorially while Tg^L grows exponentially, so you need L ∝ N log N
- Making 2(T-1)/N small requires T ≪ N — but you want T large for fault tolerance

## What's Formalized (as of 2026-03-09)

### Fully formalized:
- Protocol correctness (share/compute/reconstruct) — `pgg_program.v`, `pgg_correctness.v`
- Collusion bound (Theorem 5) — `pgg_collusion_bound.v`
- Search space chain: search_space ≤ n_traces ≤ Tg^L — `pgg_raag.v`
- Abelian collapse (non-abelian is necessary) — `pgg_abelian_collapse.v`, `abelian_word_collapse.v`
- Grover mitigation (doubling L) — `pgg_security.v`
- L-freeness for concrete instances (A₄) — `pgg_lfree.v`
- Foata NF, trace equivalence, n_traces_of_natB — `pgg_raag.v` (10/10 lemmas proved)
- Cartier-Foata identity (clique_traces = n_traces) — `pgg_raag_cartier_foata.v` (`cartier_foata`, axiom-free)
- Star-graph RAAG instance (star_traces_lb ≥ m^L) — `pgg_raag_star.v`
- Graph design principle (α(Γ)≥2 → exponential) — `pgg_raag.v` (`indep_set_traces_lb`)
- (k,T)-ramp threshold structure — `pgg_threshold.v`

### Note:
As of commit d98065c, the entire pgg-smc formalization has **zero admits and zero axioms** across all 23 files. All 27 GitHub issues (#7–#33) are closed.

## Key Files by Layer

### Layer 1: Protocol
| File | Role |
|------|------|
| `pgg_interface.v` | HB mixin (MonodromyReprType), PGG_Interface record, monodromy ops |
| `pgg_program.v` | Protocol phases: share, compute, reconstruct, secret (sum mod N) |
| `pgg_pismc.v` | Session-typed programs (pdealer, pparty, precon) |
| `pgg_session_types.v` | Session wrappers (PGGSend/Recv per dtype) |
| `pgg_correctness.v` | Correctness theorems: composition, bijectivity, distinctness |
| `pgg_sum_mod.v` | Sum-mod-N reconstruction |
| `pgg_threshold.v` | (k,T)-Ramp threshold: covered edges → recoverable bits |
| `pgg_assignment.v` | Assignment graphs on parties |
| `pgg_deck_pairing.v` | Deck pairing: match edges to secret components |

### Layer 2: Trace Monoid
| File | Role |
|------|------|
| `pgg_raag.v` | Core: Foata NF, trace equivalence, search_space ≤ n_traces ≤ Tg^L |
| `pgg_raag_clique.v` | Clique polynomial recurrence, free/abelian growth rates |
| `pgg_raag_cartier_foata.v` | Cartier-Foata theorem: `cartier_foata` (fully formalized, axiom-free) |
| `pgg_lfree.v` | L-freeness: lfree_natB check, A₄ instance |
| `pgg_raag_path.v` | Path graph instance |
| `pgg_raag_star.v` | Star graph instance |

### Layer 3: Security
| File | Role |
|------|------|
| `pgg_collusion_bound.v` | Theorem 5: var_dist(adv, ideal) ≤ ε + 2(T-1)/N |
| `pgg_security.v` | Grover mitigation, κ^L ≤ ball_size(r, L) |
| `pgg_abelian_collapse.v` | Abelian collapse: one endpoint determines permutation |
| `abelian_word_collapse.v` | search_space ≤ C(L+Tg-1, Tg-1) for abelian groups |
| `perm_uniform.v` | Permutation distribution theory |

## Four Reconstruction Methods Explored

Four reconstruction methods were investigated (documented in `aplas2024-poster/pgg-mpc/`). Only two work, and only one is efficient.

### 1. Sum-mod-N (WORKS, EFFICIENT) — formalized in `pgg_sum_mod.v`
- Secret: m = Σ s_i mod N. Reconstruction: Σ e_i mod N.
- **Threshold: (T,T) only** — all parties needed. `partial_sum_no_info` proves strict subsets learn nothing.
- **Efficiency**: O(T) reconstruction — just sum and mod.
- **Limitation**: No fault tolerance at all. All-or-nothing.

### 2. Deck-pairing (WORKS, INEFFICIENT) — formalized in `pgg_deck_pairing.v`
- Secret: bit encoded by whether (s, g(s)) are paired under involution g.
- Reconstruction: check g(e_A) == e_B. Requires σ to commute with g (equivariance).
- **Threshold: (k,T)-ramp** via assignment graph. Each component needs both its parties.
- **Inefficiency**: 6 components × 10 sheets = 60 sheets to encode 6 bits. Sum-mod-N encodes log₂(N) bits in N sheets.
- **Constraint**: requires non-trivial deck group. Only 6/97 transitive classes for N=5 have non-trivial deck group.

### 3. Class-ID (DOESN'T WORK for MPC) — explored in `protocol-description-...-class-id.tex`
- Secret: conjugacy class of the representation (σ₁,...,σᵣ) in S_N.
- Reconstruction: brute-force search over all conjugacy classes for consistency with observed rows.
- **Threshold: (4,5) for N=5** — interesting! But...
- **Fatal flaw for MPC**: reconstruction requires O(C·|S_N|) search, not efficient. Also: the "secret" (conjugacy class) is a structural property of the covering, not a value the dealer freely chooses. 97 classes for N=5 is good entropy but the dealer can't efficiently select one to encode an arbitrary message.
- **Interesting observation**: 91/97 classes have trivial deck group, so deck-pairing can't use them. Class-ID accesses all 97.

### 4. Braid-constrained class-ID (DOESN'T WORK) — explored in `protocol-description-...-braid-class-id.tex`
- Generators constrained to satisfy cubic braid relation σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁.
- **Too few classes**: only 5 transitive classes for N=4, only 2 for N=5.
- **k=1 threshold** (degenerate — all classes distinguishable from single observation).
- **Post-quantum angle**: braid CSP is conjectured hard, but finite S_N image is trivially breakable.
- **Verdict**: interesting cryptographic direction but doesn't work as MPC secret sharing.

### Summary table
```
Method          | Works? | Efficient? | Threshold | Bits (N=10)
Sum-mod-N       | Yes    | O(T)       | (T,T)     | log₂(10) ≈ 3.3
Deck-pairing    | Yes    | O(1)/comp  | (k,T)     | 1 bit/component
Class-ID        | No*    | O(C·N!)    | (4,5)     | log₂(97) ≈ 6.6
Braid class-ID  | No     | O(C·N!)    | (1,T)     | log₂(5) ≈ 2.3
```
*Class-ID "works" for threshold secret sharing but not for efficient MPC.

### Why sum-mod-N wins (and the tension it creates)

Sum-mod-N is the only method that is:
1. **Efficient**: O(T) reconstruction
2. **Information-theoretically secure**: `partial_sum_no_info` gives perfect secrecy below threshold
3. **Compatible with any monodromy group**: no deck group or braid constraints needed

But it forces **(T,T) threshold** — zero fault tolerance. This is the fundamental tension:

- The covering-space framework gives you **exponential search space** (via RAAG/L-free generators) for computational security
- But the only efficient reconstruction method gives you **no fault tolerance**
- The method that gives fault tolerance (deck-pairing) is inefficient and constrains the group structure

### Comparison to Shamir
Shamir's (k,T)-threshold scheme is "almost perfect" because polynomial interpolation gives:
- **Sharp threshold**: < k shares → zero information
- **Flexible k**: any k < T works
- **Efficient**: O(k) reconstruction via Lagrange interpolation
- **Large secret space**: any field element

PGG-SMC with sum-mod-N matches Shamir's per-threshold security but only at k=T. The covering-space structure provides something Shamir doesn't — **computational hardness against quantum adversaries** (via exponential word search space) — but at the cost of the threshold flexibility that makes Shamir so useful.

## The (T,T) Barrier: Structural Analysis

See [20260309_panagopoulos_analysis.md](20260309_panagopoulos_analysis.md) for a detailed comparison with Panagopoulos' group-presentation secret sharing (arXiv:1009.0026), which achieves genuine (t,n) threshold.

**Root cause**: PGG-SMC splits DATA (starting sheets) while keeping the algebraic structure (monodromy representation) shared. Panagopoulos splits the GROUP STRUCTURE itself (defining relations). Only structural splitting enables (t,n) threshold.

All four reconstruction methods (sum-mod-N, deck-pairing, class-ID, braid class-ID) and heterogeneous coverings share this root cause: parties need the FULL monodromy representation to perform the walk, so the group structure cannot be hidden from them.

**Key insight**: computation requires structure, reconstruction requires data. Panagopoulos separates these by making reconstruction depend on structural knowledge (the word problem). PGG-SMC conflates them because both the walk (computation) and the endpoint (reconstruction data) depend on the same full monodromy representation.

## Open Questions

1. Is there a reconstruction method that achieves (k,T) threshold with k < T while remaining efficient and compatible with the exponential search space?
2. Can the class-ID approach be made efficient for reconstruction? (Perhaps via canonical forms or hashing?)
3. Is the (T,T) threshold inherent to sum-mod-N, or can it be relaxed by using redundant sheets (e.g., error-correcting codes on the starting sheets)?
4. What is the right framing: "covering-space MPC as alternative to Shamir" or "covering-space MPC as quantum-resistant MPC at the cost of threshold flexibility"?
5. Can a Panagopoulos-style reconstruction layer be added on top of the covering-space walk — decoupling the walk (which needs full tables) from the reconstruction (which could use partial information)?
