# Panagopoulos' Group-Presentation Secret Sharing: Analysis and Implications for PGG-SMC

## Reference
Panagopoulos, D. (2010). *Threshold secret sharing scheme based on the word problem.* arXiv:1009.0026.

## The Protocol

### Setup (Steps 1-3 — long-term, before secret is known)

1. Choose group G = <x_1,...,x_k | r_1,...,r_m> with **solvable word problem** and m = C(n, t-1) relations.

2. For each (t-1)-subset A_j of {1,...,n}, associate relation r_j. Define party i's share as:
   R_i = {r_j : i not in A_j}

   Key combinatorial property: each r_j is missing from exactly t-1 of the R_i sets. Therefore:
   - Union of any t sets R_i contains ALL relations -> full presentation of G
   - Union of any t-1 sets R_i is MISSING at least one relation -> different group G' != G

3. Distribute R_i to party i over secure channel. Generators {x_1,...,x_k} are public.

### Secret distribution (Step 4 — can happen later, over open channel)

4. To share binary sequence a_1...a_l, construct words w_1,...,w_l in G such that:
   - w_i =_G 1 iff a_i = 1
   - Each w_i = 1 must involve MOST relations (security requirement)

### Reconstruction
t parties take union of their R_i sets -> get full presentation -> solve word problem w_i =_G 1 for each i.

### Security
t-1 parties get G' = <x_1,...,x_k | r'_1,...,r'_p> with p < m and G' != G. In G', w_i =_G 1 does NOT imply w_i =_G' 1 in general.

### Key Design Features

1. **Two-stage**: shares (relations) distributed once; secrets sent later, repeatedly
2. **Word problem as decision oracle**: reconstruction = deciding w =_G 1
3. **Words encoding 1**: constructed as products of commutators prod [r_j, w_j] where r_j are relations and w_j random
4. **Platform groups**: polycyclic groups or Coxeter groups suggested

## Comparison to PGG-SMC

| Aspect | Panagopoulos | PGG-SMC |
|--------|-------------|---------|
| Secret type | Binary sequence | m in Z/NZ (or bit per component) |
| Shares | Subsets of defining relations | Starting sheets (rows of permutation table) |
| Reconstruction | Word problem decision | Sum endpoints mod N / deck pairing check |
| Threshold | (t,n) — genuine! | (T,T) only (sum-mod-N) |
| Security basis | Word problem hardness | Exponential search space (RAAG) |
| Group structure | Presentation <generators \| relations> | Permutation representation rho: G -> S_N |
| Shares distributed over | Secure channel (once) | Secure channel (per secret) |
| Secret sent over | Open channel | N/A (encoded in starting sheets) |

## Why Panagopoulos Gets (t,n) and PGG-SMC Doesn't

The fundamental difference: **Panagopoulos splits the GROUP STRUCTURE itself** (relations), while **PGG-SMC splits the DATA** (starting sheets).

In Panagopoulos:
- Each party holds a PARTIAL presentation (missing some relations)
- t parties combine to get the FULL presentation
- The word problem answer changes between G and G' -> information-theoretic threshold

In PGG-SMC:
- Each party holds one row of the FULL permutation table
- The group structure (monodromy representation) is shared/public
- Parties differ only in their starting positions
- Sum-mod-N requires ALL positions to reconstruct -> (T,T)

## Can We Adapt Panagopoulos' Idea to PGG-SMC?

**Idea: Split the monodromy representation, not just the starting sheets.**

Instead of giving every party the same lookup tables (permutations sigma_1,...,sigma_r), give each party a PARTIAL set of the defining relations of the RAAG. Then:
- t parties combine their relation subsets -> full RAAG presentation -> can compute foata_nf -> reconstruct
- t-1 parties have a DIFFERENT group (quotient of the RAAG by fewer relations) -> wrong normal forms -> can't distinguish traces

**Challenges:**
1. In PGG-SMC, the lookup tables ARE the representation — parties need them to walk. You can't hide the permutations.
2. The walk is the computation phase — each party independently applies sigma_i to their sheet. They need the FULL table to walk.
3. Panagopoulos' secret is sent AFTER shares — the word w_i is the secret. In PGG-SMC, the secret is encoded in starting sheets BEFORE the walk.

**Possible hybrid:** Use Panagopoulos' structure for the reconstruction phase:
- Walk phase: everyone uses the same lookup tables (as now)
- Reconstruction phase: instead of summing endpoints, encode the answer as a word problem in a group whose relations are split among parties
- This decouples the WALK (which needs full tables) from the RECONSTRUCTION (which can use partial information)

But this adds complexity and may lose the covering-space structure that gives the search space bound.

## Heterogeneous Coverings (previously explored)

File: `aplas2024-poster/pgg-mpc/heterogeneous-coverings.tex`

**Idea**: Each party constructs its own component with different N_j, D_j, rho_j. Secret = tuple (g_1,...,g_m).

**What it achieves**:
- Per-component equivariance (Prop 3.2): correctness works component-by-component
- Negotiated init: parties choose their own component parameters
- Ramp property: sub-threshold coalition recovers some g_j but not all

**Why it doesn't solve the threshold problem**:
1. **Still (T,T) with cyclic assignment**: k_sr = T = 3 (all parties needed for full recovery)
2. **Tiny secret space**: |D_j| = 2 for all components -> product space (Z/2Z)^3 = 8 elements only
3. **|D_j| = 2 exception**: can't publish cycle types without revealing g_j
4. **Getting k_sr < T requires multi-share assignments** — open problem
5. The (T,T) barrier has the SAME root cause as deck-pairing: recovering g_j requires BOTH parties' endpoints

**Connection to Panagopoulos**: Heterogeneous coverings split the DATA (different components per party) but still keep each component's GROUP STRUCTURE shared between its two parties. Panagopoulos splits the group structure ITSELF. That's why he gets (t,n) and this doesn't.

## Synthesis: Why PGG-SMC Is Stuck at (T,T)

All four reconstruction methods and the heterogeneous extension share the same root cause:

| Method | What's split | What's shared | Why (T,T) |
|--------|-------------|---------------|-----------|
| Sum-mod-N | Starting sheets | Full permutation tables | Need ALL sheets to sum |
| Deck-pairing | Starting sheets (paired) | Full permutation tables | Need BOTH endpoints per component |
| Heterogeneous | Components across parties | Full tables within each component | Need BOTH parties per component |
| Class-ID | Starting sheets | Full tables | Reconstruction = brute-force search (not MPC-feasible) |

**The fundamental issue**: in covering-space MPC, parties need the FULL monodromy representation (lookup tables) to perform the walk. You can't hide the group structure from parties because they compute with it. This is structurally different from Panagopoulos, where parties hold PARTIAL group presentations and only need the full presentation for reconstruction (not computation).

## Current Code: Partial Information Already Present

The formalization already gives each party **only their column** of the permutation table:

- `pgg_pismc.v`: `pparty` receives `my_share = [seq rho w (tnth starts i) | w <- W]` (column at starting sheet s_i) + `word_idx` (index of P)
- `pgg_program.v`: `share W i = [seq rho w (tnth starts i) | w <- W]`
- The morphism `rho` is never transmitted — it stays abstract in `MonodromyReprType`

**Why this doesn't help with (k,T)**:
- Sum-mod-N needs ALL T endpoints: sum e_i mod N requires all parties
- Each party's column IS the full orbit of their starting sheet — having only your column doesn't prevent you from computing, it just limits what data you see
- The partial-information boundary is at the DATA level (which endpoints you see), not the STRUCTURAL level (which group relations you know)

**Contrast with Panagopoulos**: Panagopoulos splits STRUCTURAL knowledge (defining relations). PGG-SMC splits DATA (columns). Both give partial information, but only structural splitting enables (t,n) threshold.

## Possible Escape Routes (All Speculative)

1. **Homomorphic evaluation**: parties compute with encrypted tables -> can hide group structure -> but destroys the efficiency advantage
2. **Redundant encoding of starting sheets**: error-correcting codes on (s_1,...,s_T) so that any k sheets suffice -> but sum-mod-N structure may not support this
3. **RAAG-based partial reconstruction**: use commutativity structure to allow partial reconstruction when missing generators correspond to commuting directions -> the "hub generator" idea from star-RAAG
4. **Accept (T,T) and reframe**: the covering-space construction provides quantum-resistant computational security at the cost of threshold flexibility. Different contribution than Shamir.

## Conclusion

Panagopoulos' scheme achieves (t,n) by splitting the algebraic structure (group relations) rather than the data. PGG-SMC splits data (starting sheets) while keeping the algebraic structure shared. This structural difference appears to be WHY PGG-SMC is stuck at (T,T).

The distinction is clean: **computation requires structure, reconstruction requires data**. Panagopoulos separates these by making reconstruction depend on structural knowledge (the word problem). PGG-SMC conflates them because the walk (computation) and the endpoint (data for reconstruction) both depend on the same full monodromy representation.

To get (k,T) in PGG-SMC, one would need to either:
1. Split the monodromy representation itself (but parties need it for the walk)
2. Add a Panagopoulos-style reconstruction layer on top of the covering-space walk
3. Use redundant encoding of starting sheets (error-correcting codes)
4. Accept (T,T) and frame the contribution differently
