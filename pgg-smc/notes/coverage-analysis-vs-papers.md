# Coverage Analysis: LaTeX Papers vs `pgg-smc/` Implementation

Compared against:
- `theorems-covering-space-mpc.tex` (theorem collection)
- `protocol-description-20260227-224355-sum-mod-N.tex` (worked examples)

## Formalized (with proofs)

| Paper Claim | Coq File | Lemma |
|---|---|---|
| **Thm 1: Correctness** (ρ(gh)(s) = ρ(h)(ρ(g)(s))) | `pgg_correctness.v` | `pgg_correctness` |
| **Thm 2: UPLP/Bijectivity** (σ_P is a permutation) | `pgg_correctness.v` | `pgg_bijectivity` |
| **Prop 3: Distinctness preservation** | `pgg_correctness.v` | `pgg_distinctness` |
| **Prop 4: Row independence** (single uniform perm) | `perm_uniform.v` | `perm_cond_uniform` |
| **Thm: Abelian collapse** (search space ≤ \|G\|, polynomial) | `pgg_abelian.v` | `cyclic_search_space_le` |
| **Thm: Free group exponential** (L-free → search_space = Tg^L) | `pgg_interface.v` | `lfree_search_space` |
| **Thm: RAAG trace equivalence** (swap preserves word_eval) | `pgg_raag.v` | `word_eval_trace` |
| **Thm: search_space ≤ n_traces** | `pgg_raag.v` | `search_space_le_traces` |
| **Thm: Empty comm → Tg^L** (free case) | `pgg_raag.v` | `empty_comm_traces` |
| **Thm: Full comm → C(L+Tg-1,Tg-1)** (abelian case) | `pgg_raag.v` | `full_comm_traces` |
| **Thm: Word-equivalence invariance** (Thm in theorems.tex) | `pgg_raag.v` | `word_eval_adj_swap` + `search_space_le_traces` |
| **Protocol structure** (split/compute/reconstruct) | `pgg_pismc.v` | `pdealer`, `pparty`, `precon` + 6 duality proofs |
| **Non-abelian instance** (star transpositions in S_{T+1}) | `pgg_nonabelian.v` | `nonab_gen_noncommute`, `nonab_lfree1` |
| **Concrete L-freeness** (overlapping 3-cycles, L=2) | `pgg_lfree.v` | `oc_lfree2` via `vm_compute` |
| **Assumption 1: Composed-walk uniformity** (σ_P approximately uniform for L≥2) | `pgg_collusion_bound.v` | `var_dist_lfree_uniform` (line ~459) |
| **Thm: Collusion bound** (d_TV ≤ ε + 2(T-1)/N) | `pgg_collusion_bound.v` | `collusion_bound` (line ~235) |
| **Thm: Graph design principle** (α(Γ)≥2 → exponential) | `pgg_raag.v` | `indep_set_traces_lb` (line ~865) |
| **Cartier-Foata identity** (clique polynomial = trace count) | `pgg_raag_cartier_foata.v` | `cartier_foata` (line ~2907) |
| **RAAG star search space ≥ m^L** | `pgg_raag_star.v` | `star_traces_lb` (line ~266) |

## Partially covered

| Paper Claim | Status | Gap |
|---|---|---|
| **Abelian frequency-vector equivalence** | Conceptually covered by `full_comm_traces` (C(L+Tg-1,Tg-1) = multiset count), but no explicit "word depends only on frequency vector" lemma | |
| **Abelian attack** (single evaluation recovers full permutation) | Not formalized — `cyclic_search_space_le` shows collapse but doesn't model the adversary's attack steps | |

## Not formalized

| Paper Claim | Notes |
|---|---|
| **Star-graph centralizer analysis** (48 candidates for σ_b) | Concrete combinatorial argument, not formalized |
| **Sum-mod-N reconstruction** (Σ e_i mod N = m) | The protocol uses group multiplication, not sum-mod-N; the paper's "sum mod N" is the specific reconstruction for cyclic groups |
| **Security--storage trade-off** (Θ(κ^L) share size) | Not formalized |
| **Depth-L share** (ball B_L(e) evaluation) | `share` in code takes an explicit word list W, not a ball |

## Out of scope

| Paper Claim | Notes |
|---|---|
| **Post-quantum** (Shor/Grover/non-abelian HSP) | Out of scope for Coq formalization |
| **Braid group** (B_4, finite image collapse, order 216) | Not needed for the current paper |
| **Square-graph F_2 × F_2 instance** | Still exponential (Θ(L·3^L)); adds nothing to the security dichotomy beyond the star-graph instance + `indep_set_traces_lb` |

## Key structural observations

1. **Sum-mod-N vs group operation**: The papers describe reconstruction as "Σ e_i mod N", but the Coq formalization uses group-level operations (permutation composition). The sum-mod-N is a specific interpretation when endpoints are ordinals — this isn't explicitly bridged.

2. **No adversary model**: The papers describe semi-honest adversaries, collusion bounds, and attack procedures. The Coq code has no adversary formalization — security is captured indirectly via search space bounds and the row-independence lemma in `perm_uniform.v`.

3. **Share = depth-1 only**: The code's `share W i` takes an explicit word list, while the paper describes depth-L shares (all words in B_L(e)). The code doesn't compute or bound the ball size.

4. **RAAG concrete instances formalized**: `pgg_raag_star.v` provides a concrete star-graph instance with `star_traces_lb` (≥ m^L traces). The general `indep_set_traces_lb` covers the graph design principle for any graph with α(Γ)≥2. The Cartier-Foata identity connects clique polynomials to trace counts.

5. **Zero admits/axioms**: As of commit d98065c, the entire pgg-smc formalization (23 files) has zero admits and zero axioms. All 27 GitHub issues (#7–#33) are closed.
