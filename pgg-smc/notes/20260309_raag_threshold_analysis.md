# Can RAAG Structure Break the (T,T) Threshold Barrier?

## Date: 2026-03-09

## Summary

This note rigorously analyzes five ideas for using the RAAG (Right-Angled Artin Group) structure in PGG-SMC to achieve (k,T) threshold with k < T. The conclusion is **negative for all five ideas in their pure forms**, but two hybrid constructions emerge as mathematically viable at the cost of departing from the covering-space framework. The core obstruction is identified precisely: the monodromy action maps words to permutations via a homomorphism, and homomorphic images do not decompose by trace-monoid projections.

---

## Prerequisites and Notation

- **PGG-SMC protocol**: T parties hold starting sheets s_0,...,s_{T-1} in {0,...,N-1} with secret m = sum s_i mod N. After walking word W, party i holds e_i = rho(W)(s_i). Reconstruction: sum e_i mod N = m.
- **RAAG M(Gamma)**: generators g_1,...,g_r with g_i g_j = g_j g_i iff (i,j) in E(Gamma). The trace monoid is the quotient of the free monoid by these commutations.
- **Foata NF**: canonical form F_1 . F_2 . ... . F_d where each F_j is a maximal antichain (independent set in the non-commutation graph) of generators, sorted within each layer.
- **Clique projection**: for clique C in Gamma, the projection pi_C : M(Gamma) -> M(C) retains only generators in C. Since C is a clique, M(C) is a free commutative monoid.
- **rho**: the monodromy representation, a group homomorphism from the group presented by the RAAG to S_N.

---

## Idea 1: Projection-Based Reconstruction

### The Proposal

Assign each party to a clique C_i of Gamma. Party i computes information related to pi_{C_i}(W). If k parties' cliques cover all generators, they can reconstruct the full trace class of W. Fewer than k parties whose cliques miss some generators cannot.

### Analysis

**Step 1: Does rho(W) decompose by clique projections?**

This is the critical mathematical question. For a word W = w_1 w_2 ... w_L, define pi_C(W) as the subsequence of W consisting of generators in C. In the free commutative monoid on C, pi_C(W) is determined by the multiset of generators from C that appear in W.

**Claim (negative)**: rho(W) does NOT decompose as a function of {pi_C(W) : C ranges over cliques}.

*Proof sketch*: Consider Gamma = the empty graph on {g_1, g_2} (no edges, so no commutations -- the free case). The only cliques are singletons {g_1} and {g_2}. We have pi_{g_1}(W) = the count of g_1's in W, and pi_{g_2}(W) = the count of g_2's in W. But the free group on two generators is non-abelian, so knowing only the counts of g_1 and g_2 does NOT determine rho(W). For example, rho(g_1 g_2) != rho(g_2 g_1) in general.

More generally: pi_C(W) forgets the ORDER in which generators from C interleave with generators outside C. The trace equivalence class of W remembers all ordering constraints between non-commuting generators. Clique projections forget exactly the inter-clique ordering, which is the non-commuting part -- the part that carries the most information.

**Theorem (obstruction)**: Let Gamma have at least one non-edge (i,j). Then there exist words W, W' with pi_C(W) = pi_C(W') for all cliques C, but rho(W) != rho(W').

*Proof*: Take W = g_i g_j and W' = g_j g_i. For any clique C: if both i,j in C, then (i,j) is an edge of Gamma, contradicting non-edge. So at most one of i,j is in C, meaning pi_C(W) = pi_C(W'). But rho(W) = rho(g_i) rho(g_j) != rho(g_j) rho(g_i) = rho(W') since g_i and g_j don't commute and rho is faithful on generators (raag_gen_inj). QED.

**Consequence**: Clique projections cannot reconstruct rho(W). They lose the ordering information between non-commuting generators, which is precisely the information that determines the permutation.

### The Product-Covering Fix

**Proposed modification**: Replace S_N with a product group G_1 x ... x G_d, one factor per clique. Define rho_C : M(C) -> G_C for each clique C. Each party's "endpoint" is a vector (e_i^{C_1}, ..., e_i^{C_d}).

**Problem 1 (correctness)**: For sum-mod-N reconstruction, we need rho(W) to be a permutation that preserves sum s_i mod N. A product of independent permutations rho_{C_1} x ... x rho_{C_d} acts on a product space, not on {0,...,N-1}. The covering-space structure requires a single connected covering, not a product of coverings.

**Problem 2 (redundancy)**: If the factors G_C are independent, then knowing rho_{C_i}(W) for clique C_i assigned to party i tells you the action on the C_i-component of the product space. But the "secret" must be encoded across all components, and decoding still requires all components. This is heterogeneous coverings revisited (see `20260309_panagopoulos_analysis.md`, Section "Heterogeneous Coverings"), which is already known to give (T,T).

**Problem 3 (interaction)**: If the factors G_C are NOT independent (i.e., there are cross-clique constraints from the RAAG relations), then they don't form a true product, and the projection pi_C doesn't give a well-defined action on any individual factor.

### Verdict on Idea 1

**Fatal flaw**: The monodromy homomorphism rho collapses the trace-monoid structure. Clique projections operate at the word/trace level, but the endpoint e_i = rho(W)(s_i) is a single number determined by the full permutation rho(W). There is no natural decomposition of rho(W) by clique projections unless the group itself is a direct product (which it generally isn't for interesting monodromy groups).

**Is the flaw fixable?** Only by replacing the single covering space with a product structure, which abandons the core PGG-SMC framework and reduces to heterogeneous coverings (known (T,T)).

**Mathematical status**: The obstruction theorem above is a **theorem** (straightforward from non-commutativity of non-commuting generators). The infeasibility of the product-covering fix is a **structural argument** based on the heterogeneous-covering analysis.

---

## Idea 2: Foata-Layer-Based Reconstruction

### The Proposal

Foata NF of W = F_1 . F_2 . ... . F_d. Each layer F_j uses generators from some subset S_j (an independent set in the non-commutation graph, or equivalently a clique in the commutation graph Gamma). Assign parties to layers. For layer F_j, only parties in S_j need to contribute. Reconstruction proceeds layer by layer.

### Analysis

**Step 1: Does rho decompose by layers?**

We have rho(W) = rho(F_1) . rho(F_2) . ... . rho(F_d) since rho is a homomorphism. Within each layer F_j, the generators commute (F_j is a clique in Gamma), so rho(F_j) is a product of commuting permutations. The order within a layer doesn't matter.

**But**: the ORDER of layers matters. rho(F_1 . F_2) != rho(F_2 . F_1) in general. Layer-by-layer reconstruction requires knowing rho(F_1), rho(F_2), ..., rho(F_d) AND the order.

**Step 2: What does "party assigned to layer j contributes" mean?**

Party i holds e_i = rho(W)(s_i) = rho(F_1 . ... . F_d)(s_i). This is a SINGLE number. Party i does NOT know rho(F_j)(s_i) for individual layers -- they only see the final result of applying all layers sequentially.

**Step 3: Can parties compute layer-by-layer information?**

During the WALK phase, party i applies generators one at a time: s_i -> sigma_{w_1}(s_i) -> sigma_{w_2}(sigma_{w_1}(s_i)) -> ... The party sees intermediate sheets at each step. In principle, party i could record the intermediate sheet after each Foata layer boundary.

**But**: this requires the party to know the Foata layer structure, which means knowing the word W and the commutation graph Gamma. In PGG-SMC, the word W is the "program" -- it's public knowledge (or at least known to all parties). So parties CAN identify layer boundaries.

**Step 4: Layer-level partial sums?**

After layer F_1, party i has sheet s_i^{(1)} = rho(F_1)(s_i). After layer F_2, sheet s_i^{(2)} = rho(F_2)(s_i^{(1)}). And so on.

Could we reconstruct layer by layer, with only parties relevant to layer j contributing at step j?

**Fatal problem**: sum s_i^{(j)} mod N != sum s_i^{(j-1)} mod N in general. The sum-mod-N invariant is:

sum rho(W)(s_i) mod N = sum s_i mod N

This holds because rho(W) is a permutation, so sum rho(W)(s_i) = sum s_i (not just mod N, but exactly -- it's a permutation of multisets if sheets are distinct, or of values in general).

**Wait -- is that right?** Let's be precise. If all s_i are distinct (which they need not be), then rho(W) permutes them and the sum is preserved. But if s_i are NOT distinct, rho(W)(s_i) depends on the VALUE of s_i, and the sum is still preserved because rho(W) is a bijection on {0,...,N-1}: sum rho(W)(s_i) = sum s_i when the s_i are ALL distinct elements of {0,...,N-1}. But T < N in general, so the s_i are a T-element subset (or multiset) of {0,...,N-1}.

Actually, the sum-mod-N invariant doesn't require distinct sheets. For any permutation sigma in S_N and any values s_0,...,s_{T-1} in {0,...,N-1}:

sum sigma(s_i) mod N = sum s_i mod N

is FALSE in general! It holds only when sigma preserves sum mod N, which is a special property. The formalization uses `sum_preserving` as a hypothesis.

**Revised analysis**: The sum-mod-N reconstruction requires that rho(W) preserves sum mod N. This is a global property of the full permutation rho(W), not decomposable by layers.

**Could we use layer-level checksums?** Suppose we defined m_j = sum s_i^{(j)} mod N for each layer j. Then m_d = sum e_i mod N = m (the secret). Each m_j depends on all T parties' sheets at layer j. So every layer requires all parties -- no improvement.

### Verdict on Idea 2

**Fatal flaw**: The sum-mod-N reconstruction is a GLOBAL operation on all parties' final endpoints. It doesn't decompose by Foata layers because:
1. Each party only sees the cumulative effect of all layers (a single endpoint), not per-layer intermediate values (unless they record them, which requires protocol modification).
2. Even if per-layer intermediate values were available, the sum-mod-N at each layer involves ALL parties.
3. The layers involve different generators but ALL sheets simultaneously -- there's no "party-to-layer" assignment that reduces the coalition requirement.

**Is the flaw fixable?** Not within sum-mod-N reconstruction. One would need a reconstruction method that is somehow "layered" -- where the secret is encoded across layers rather than across parties. But I don't see how to do this while maintaining the covering-space structure.

**Mathematical status**: The infeasibility is a **structural argument** based on the sum-mod-N reconstruction requiring all endpoints. Not a formal theorem, but a clear and robust argument.

---

## Idea 3: Decoupling Walk from Reconstruction via Trace Encoding

### The Proposal

Two-phase approach:
- **Walk phase**: Standard PGG-SMC. Every party walks, gets endpoint e_i = rho(W)(s_i).
- **Encoding phase**: Encode each e_i as a word in an auxiliary RAAG. Use the auxiliary RAAG's partial commutativity structure to enable (k,T) reconstruction.

This adds a Panagopoulos-style layer on top of the covering-space walk.

### Analysis

**Step 1: What would the auxiliary RAAG look like?**

We need to encode T values e_0,...,e_{T-1} in {0,...,N-1} such that:
- Any k values suffice to recover m = sum e_i mod N
- Fewer than k values give no information about m

This is exactly the problem that Shamir's secret sharing solves! The walk phase produces T values (endpoints), and the reconstruction phase needs (k,T)-threshold on those values.

**Observation**: If we're going to add a threshold secret sharing layer on top of the walk, we might as well use Shamir directly:
1. Walk phase: each party gets e_i.
2. Each party computes a "modified endpoint" e_i' = e_i + r_i mod N where r_i are shares of 0 from a Shamir scheme.
3. Any k parties can reconstruct sum e_i' mod N = sum e_i mod N = m.

But this defeats the purpose of PGG-SMC! The whole point is that the covering-space structure provides post-quantum security via the exponential search space. Adding Shamir on top means the security comes from Shamir (not post-quantum) and the covering-space walk is just overhead.

**Step 2: Could we use RAAG structure instead of Shamir?**

We need a (k,T)-threshold scheme on the values (e_0,...,e_{T-1}). The RAAG provides structure on the WORD SPACE (traces), not on the VALUE SPACE (endpoints). The endpoints are just numbers in {0,...,N-1}; they don't carry RAAG structure.

To use RAAG structure for the reconstruction layer, we would need to:
- Encode the endpoint values as WORDS in an auxiliary RAAG
- Show that the trace-monoid structure enables threshold recovery

But encoding integers as RAAG words and then using trace projections for threshold recovery is just reinventing Panagopoulos' scheme with extra steps. The RAAG structure doesn't add anything that Panagopoulos' general group-presentation approach doesn't already provide.

**Step 3: Does decoupling preserve the search-space security?**

The covering-space search space bound says: an adversary who sees T-1 columns of the permutation table must search over n_traces(L) possible programs to determine rho(W). This bound comes from the walk phase.

If we add a threshold reconstruction layer:
- The walk phase still provides search-space security (the adversary can't determine rho(W) from T-1 columns).
- The reconstruction layer provides information-theoretic threshold security (fewer than k endpoints don't reveal m).
- The combined security is the MINIMUM of the two.

**But**: the walk phase already gives (T,T) threshold for the endpoints (each party's endpoint is individually random to a coalition of T-1, given sum-preserving monodromy). Adding a Shamir/Panagopoulos layer would give (k,T) on the reconstruction step, but the walk-phase information leakage is the binding constraint.

**Wait**: Is this true? Let's think more carefully. The adversary in PGG-SMC sees:
- Their own endpoint(s) (say T-1 of them if T-1 parties collude)
- The public information (word W, commutation graph, etc.)

From T-1 endpoints, the adversary can compute a partial sum. The remaining party's endpoint e_missing is uniformly distributed (by `partial_sum_no_info`). So the adversary has no information about m given T-1 endpoints.

If we use a (k,T) reconstruction layer with k < T, then:
- A coalition of k parties can reconstruct m.
- A coalition of k-1 parties cannot.
- A coalition of T-1 parties (with T-1 >= k) CAN reconstruct m by the threshold property.

So the (k,T) threshold would be PROVIDED by the reconstruction layer, not by the walk phase. The walk phase provides security against external adversaries (search space), and the reconstruction layer provides threshold structure against internal coalition subsets.

**This is actually viable in principle!** The two layers serve different purposes:
- Walk: computational security (post-quantum, exponential search space)
- Reconstruction: information-theoretic threshold (any (k,T)-threshold scheme)

### Detailed Protocol Sketch

1. **Setup**: Choose RAAG Gamma, monodromy rho, word W. Also choose a (k,T)-threshold secret sharing scheme S (Shamir, Panagopoulos, etc.).
2. **Sharing**: Dealer chooses secret m in Z/NZ. Chooses starting sheets s_0,...,s_{T-1} with sum s_i = m mod N. But ALSO: dealer applies a (k,T)-threshold scheme to m, producing auxiliary shares a_0,...,a_{T-1}.
3. **Walk**: Each party i receives s_i and a_i. Party i computes e_i = rho(W)(s_i). Party i also holds a_i.
4. **Reconstruction**: Any k parties pool their auxiliary shares a_i and reconstruct m via the threshold scheme. The endpoints e_i are NOT used for reconstruction (!). Or: combine both sources of information.

**Problem**: This completely sidesteps PGG-SMC. The walk is irrelevant to reconstruction; the threshold comes entirely from the auxiliary scheme. The covering-space structure is reduced to providing computational security against external eavesdroppers, and any threshold scheme would serve for reconstruction.

**Refined version**: Can we make the auxiliary shares DEPEND on the endpoints, so that the walk is integrated into the threshold scheme?

For example:
- Party i's "effective share" for the threshold scheme is f(e_i, a_i) for some function f.
- Reconstruction from k effective shares recovers m.
- Security: fewer than k effective shares reveal nothing.

This would tie the walk phase to the threshold phase. But the function f would need to:
1. Be computable by party i from their endpoint and auxiliary share.
2. Enable k-party reconstruction.
3. Prevent (k-1)-party reconstruction.

This is essentially a threshold scheme where each share is "masked" by the endpoint. The masking is computable by the party but doesn't fundamentally change the threshold structure.

### Verdict on Idea 3

**Not fatally flawed, but does not leverage RAAG structure.** The decoupling idea is mathematically sound: one can layer a (k,T)-threshold scheme on top of the PGG-SMC walk. But:
1. The RAAG/trace-monoid structure plays NO role in the threshold property -- it only provides the search-space bound for computational security.
2. The threshold comes entirely from the auxiliary scheme (Shamir, Panagopoulos, etc.).
3. The resulting protocol is a COMPOSITION of two independent mechanisms, not a unified framework.
4. The covering-space walk becomes a "computational security amplifier" rather than the core mechanism.

**Mathematical status**: The composition is **sound** (both components provide their respective guarantees independently). Whether this counts as "breaking the (T,T) barrier" is a matter of framing -- the PGG-SMC mechanism itself still has (T,T) threshold, but the composite protocol achieves (k,T) by adding an external component.

---

## Idea 4: Star-RAAG Hub Generator

### The Proposal

In K_{1,m} (star graph), generator g_0 (hub) commutes with all leaf generators g_1,...,g_m. The hub is "visible from every direction." Could a party assigned to the hub be made redundant?

### Analysis

**Step 1: Structure of the star RAAG**

In M(K_{1,m}), the hub g_0 commutes with every leaf, but leaves don't commute with each other. The Foata NF has the property that g_0 can appear in any layer (it commutes with everything, so it sinks to the earliest possible position).

The trace equivalence classes of M(K_{1,m}): two words are trace-equivalent iff they agree on:
- The relative order of all pairs of leaf generators (since leaves don't commute).
- The total count of g_0 appearances (since g_0 commutes with everything, its position doesn't matter relative to any generator).

So pi_{g_0}(W) = count of g_0's in W, and this is the ONLY information the hub projection gives. The leaf structure retains the full non-abelian ordering.

**Step 2: Does hub commutativity help with reconstruction?**

The monodromy rho(W) depends on the full permutation rho(g_0)^{n_0} . rho(g_1)^{a_1} ... (but this is NOT how the product works -- the interleaving of g_0 with leaves matters through the leaf ordering, and g_0 commutes past everything). Actually:

rho(W) = rho(g_0)^{n_0} . rho(W') where W' is the de-hubbed word (W with all g_0's removed), and n_0 = count of g_0's in W.

**This IS a valid decomposition!** Because g_0 commutes with all other generators in the RAAG, we have:

rho(W) = rho(g_0)^{n_0} . rho(W_leaves)

where W_leaves is the word restricted to leaf generators. The order of g_0 appearances doesn't matter.

**Step 3: Can we exploit this decomposition?**

The endpoint e_i = rho(W)(s_i) = rho(g_0)^{n_0}(rho(W_leaves)(s_i)).

If party i could compute rho(W_leaves)(s_i) separately from the effect of rho(g_0)^{n_0}, then:
- The "hub contribution" rho(g_0)^{n_0} is a single known permutation (since n_0 = count of g_0 in W, and W is public).
- The "leaf contribution" rho(W_leaves)(s_i) depends on the non-abelian leaf word.

**But**: W is PUBLIC! If W is known to all parties, then every party knows n_0 and can compute rho(g_0)^{n_0}. The hub doesn't provide any threshold advantage because the hub information is already public.

**Step 4: What if W is NOT public?**

If W is secret (known only to the dealer), then:
- Party i sees only e_i = rho(W)(s_i).
- Party i does NOT know W, hence doesn't know n_0 or W_leaves.
- The hub/leaf decomposition is hidden from the parties.

In this case, the hub commutativity is a property of the word space, not of the endpoint space. It reduces the trace count (fewer distinct traces, hence smaller search space) but doesn't help with reconstruction.

**Step 5: Residual question -- does star RAAG structure enable any partial reconstruction?**

Suppose a coalition of T-1 parties (missing party j) tries to reconstruct m. They have T-1 endpoints. The missing endpoint e_j = rho(W)(s_j) is unknown.

The sum-mod-N reconstruction gives: sum_{i != j} e_i + e_j = m mod N. Without e_j, they can't determine m.

The hub structure doesn't help because:
- e_j = rho(g_0)^{n_0}(rho(W_leaves)(s_j)) -- but the coalition doesn't know s_j.
- Even if they knew the hub/leaf decomposition, they'd need to know s_j to compute e_j.

### Verdict on Idea 4

**Fatal flaw**: The hub generator's commutativity is a property of the WORD (trace monoid), not of the ENDPOINT VALUES. Since reconstruction operates on endpoints (not words), the hub's special status doesn't translate into any threshold advantage.

More precisely:
- If W is public: the hub/leaf decomposition is trivially computable by all parties; no party needs to "contribute" hub information.
- If W is secret: the decomposition is hidden; parties can't exploit it.

In either case, the fundamental constraint is that sum-mod-N needs all endpoints, and each endpoint is determined by (rho(W), s_i), both of which are complete objects -- not decomposable by party assignment.

**Mathematical status**: This is a **theorem** (the hub decomposition rho(W) = rho(g_0)^{n_0} . rho(W_leaves) is correct but irrelevant to reconstruction).

---

## Idea 5: Redundant Sheet Encoding via RAAG Independence

### The Proposal

Instead of m = sum s_i mod N with one sheet per party, use the RAAG structure to encode the secret redundantly:
- For each maximal clique C of Gamma, encode a "sub-secret" m_C using the parties in C.
- The sub-secrets are related by consistency conditions from the RAAG.
- Any covering set of cliques allows reconstruction.

### Analysis

**Step 1: What does "encode a sub-secret using parties in clique C" mean?**

A maximal clique C in Gamma corresponds to a set of mutually commuting generators. The sub-monoid generated by C is free abelian (commutative). If we restrict the walk to generators in C, the result is an abelian permutation -- determined entirely by the exponent vector (n_c)_{c in C}.

**Proposal (concrete)**: For each maximal clique C, define m_C = sum rho_C(s_i) mod N_C where rho_C is the abelian sub-representation restricted to generators in C.

**Problem**: rho_C is NOT an independent representation. The generators in C are mapped to permutations sigma_c in S_N under the SAME representation rho. Their product is rho(W_C) where W_C = pi_C(W). But rho(W) != product of rho(W_C) over cliques C (this is the same obstruction as Idea 1).

**Step 2: Independent sub-coverings?**

What if we designed the covering space as a PRODUCT of independent coverings, one per maximal clique?

The covering space X -> B has fiber {0,...,N-1}. If X = X_{C_1} x ... x X_{C_k}, one factor per maximal clique, then:
- Each factor X_{C_j} is a covering with fiber {0,...,N_{C_j}-1}
- The monodromy of X is the product of monodromies: rho = rho_{C_1} x ... x rho_{C_k}
- Each rho_{C_j} acts only on the C_j-component

**This is a direct product representation.** The secret would be m = (m_{C_1}, ..., m_{C_k}) and each m_{C_j} could be reconstructed from the parties in C_j.

**Threshold structure**: If each maximal clique has >= k_j parties, and k_j parties suffice for the sum-mod-N_{C_j} reconstruction of m_{C_j} (which requires k_j = |C_j| since sum-mod-N is (T,T)), then:
- All maximal-clique reconstructions succeed iff ALL parties participate (since every party belongs to some maximal clique and each clique requires all its members).
- This gives (T,T) again!

**Step 3: Error-correcting code structure?**

What if we added REDUNDANCY across cliques? Encode m as a codeword (m_{C_1},...,m_{C_k}) of an error-correcting code, so that not all components are needed?

This requires:
1. The m_{C_j} are related by parity checks: not all configurations (m_{C_1},...,m_{C_k}) represent valid secrets.
2. Recovery from any sufficiently large subset of components.

But: within each component, the sub-reconstruction is STILL (|C_j|, |C_j|) -- all parties in C_j must contribute. The redundancy across components means you don't need ALL components, but you still need all parties within each needed component.

**Example**: Gamma = K_{1,2} (star with 2 leaves, 3 generators). Maximal cliques: {0,1}, {0,2} (hub-leaf pairs). Suppose m = (m_{01}, m_{02}) with m_{01} + m_{02} = m (redundancy via simple sum).
- Reconstructing m_{01} requires parties 0 and 1.
- Reconstructing m_{02} requires parties 0 and 2.
- Reconstructing m requires at least one of the two.
- Coalition {0,1}: can compute m_{01}. Need m_{02} too, but can use m = m_{01} + m_{02} only if they know m_{02}. Can't compute m_{02} without party 2.
- Coalition {0,2}: similarly, can compute m_{02} but not m_{01}.
- Coalition {1,2}: can compute neither m_{01} nor m_{02} (party 0, the hub, is in both cliques).

So: NO strict subset of 3 parties can reconstruct m. This is (3,3) = (T,T) again!

**Root cause**: The hub generator belongs to ALL maximal cliques. The hub party is required for EVERY sub-reconstruction. This makes the hub a single point of failure and prevents any threshold improvement.

**Step 4: What about clique covers that overlap?**

The parties assigned to overlapping cliques share the hub party. Any threshold scheme on the cliques requires the overlapping party for multiple sub-reconstructions. This creates a bottleneck that forces (T,T).

**Formal argument**: Let v be a vertex of Gamma that belongs to all maximal cliques (like the hub in a star). Then party v is needed for every sub-reconstruction. Without party v, NO sub-secret can be recovered. So the threshold is at least T (all parties), i.e., (T,T).

If Gamma has no universal vertex (vertex in all maximal cliques), then there might be hope. But:
- The RAAG with no universal vertex still has the problem that sum-mod-N within each component requires all component members.
- Even if you don't need ALL components, you need all members of each component you use.
- The minimum coalition size is min_C |C| over all maximal cliques C.
- For this to be < T, you need a maximal clique smaller than T, which means the RAAG has some non-commuting generators -- but then the "missing" generators' components are unreconstructable without additional parties.

### Verdict on Idea 5

**Fatal flaw**: The redundant encoding via RAAG cliques reduces to a product-of-coverings scheme where each factor requires all its assigned parties. The RAAG structure (via maximal cliques) doesn't escape the (T,T) barrier because:
1. Each clique-component uses sum-mod-N, which is (|C|, |C|).
2. Overlapping cliques share parties, creating bottleneck vertices.
3. Error-correcting codes across components can't compensate because the component-level threshold is already maximal.

**Mathematical status**: The bottleneck argument (universal vertex forces all-party participation) is a **theorem**. The general insufficiency of clique-based redundancy is a **structural argument**.

---

## Synthesis: The Fundamental Obstruction

All five ideas share a common obstruction:

**The monodromy representation rho is a homomorphism from the RAAG group to S_N. This homomorphism collapses the rich algebraic structure of the RAAG (partial commutativity, Foata layers, clique projections) into a SINGLE permutation. The endpoint e_i = rho(W)(s_i) is a single number that encodes the CUMULATIVE effect of all generators, not a structured object that can be decomposed by RAAG projections.**

More precisely, the obstruction has three layers:

1. **Algebraic**: rho is a homomorphism, so rho(W) depends only on the GROUP ELEMENT represented by W, not on the word itself. All trace-monoid structure (Foata NF, clique projections, layer structure) collapses under rho. Two trace-inequivalent words CAN have the same rho-image (when the group is finite).

2. **Information-theoretic**: sum-mod-N reconstruction requires all endpoints. This is an arithmetic constraint: knowing T-1 terms of a sum modulo N gives zero information about the sum (by `partial_sum_no_info`). No algebraic structure on the WORD can change this fact about the ENDPOINTS.

3. **Structural**: in PGG-SMC, parties need the full monodromy representation to walk. The RAAG structure determines the SEARCH SPACE (how many distinct permutations the adversary must consider) but not the RECONSTRUCTION METHOD (how parties combine their endpoints to recover the secret).

**The RAAG structure lives at the wrong level.** It structures the word/trace space (Layer 2 in the architecture) but reconstruction operates at the endpoint/value level (Layer 1). The monodromy homomorphism rho bridges these levels but does not preserve the RAAG structure.

---

## What Would Work (Speculative)

### Direction A: Post-walk threshold layer (Idea 3, refined)

The most viable direction is to ACCEPT that PGG-SMC provides (T,T) walk-phase security and ADD a separate (k,T)-threshold mechanism for reconstruction:

1. Walk phase: standard PGG-SMC. Each party gets endpoint e_i. Security: exponential search space against external adversary.
2. Threshold reconstruction: apply any (k,T)-secret sharing scheme to the secret m. The shares can be distributed alongside the starting sheets.

The resulting protocol has:
- **Computational security** against external adversaries: exponential search space from RAAG/L-free generators (post-quantum).
- **Information-theoretic threshold** against internal coalitions: (k,T) from the threshold scheme.

**Cost**: the covering-space structure is no longer the sole mechanism. It's a COMPOSITION, not a unified framework.

**Open question**: Can the threshold shares be constructed FROM the endpoints in a way that the walk phase and reconstruction phase are integrated (not independent)? This would require a reconstruction function r(e_{i_1},...,e_{i_k}) = m that works for any k-subset but reveals nothing for (k-1)-subsets. For sum-mod-N, this is impossible (by `partial_sum_no_info`, any T-1 endpoints are consistent with any secret). But perhaps a different reconstruction function, tailored to the monodromy structure, could work.

**Conjecture (negative)**: For any reconstruction function r: ({0,...,N-1})^k -> Z/NZ and any monodromy rho, if the endpoints e_i = rho(W)(s_i) are deterministic functions of (rho(W), s_i), then a coalition of k < T parties who know rho(W) can compute r(e_{i_1},...,e_{i_k}), but this gives them THEIR OWN k values, which are deterministic given (W, s_{i_1},...,s_{i_k}). The remaining T-k values are unknown, and whether m can be recovered depends on whether the k known values constrain m. For sum-mod-N, they don't constrain m at all. For a different function r, some constraint might exist -- but providing k-out-of-T recovery while maintaining (k-1)-out-of-T secrecy requires the Shamir-like algebraic structure on the VALUES, which is not provided by the RAAG structure on the WORDS.

### Direction B: Replace sum-mod-N with a RAAG-structured reconstruction

The most ambitious direction: design a reconstruction method where the RAAG structure directly enables threshold recovery.

**Requirements**:
1. Secret m encoded in starting sheets (s_0,...,s_{T-1}).
2. After walk, endpoints (e_0,...,e_{T-1}).
3. Reconstruction function R(e_{i_1},...,e_{i_k}) = m for any k-subset.
4. Security: R(e_{i_1},...,e_{i_{k-1}}) reveals nothing about m for any (k-1)-subset.
5. The function R should USE the RAAG structure (not be an independent Shamir-like scheme).

**Key insight needed**: The RAAG provides structure on the WORD SPACE. To make this relevant for reconstruction, we need the reconstruction function to depend on WHICH word W was used, not just on the endpoints. If different words W give different reconstruction functions R_W, and the RAAG structure determines which subsets of parties suffice for each R_W, then we might get a word-dependent threshold.

**Speculation**: For certain words W (e.g., those where generators from a clique C dominate), the endpoints of parties in C might suffice for reconstruction. For other words, different cliques suffice. If the dealer chooses W to match the available coalition, this gives ADAPTIVE threshold -- but it requires the dealer to know which parties will be available at reconstruction time.

**Mathematical question**: Does there exist a reconstruction function R_W such that:
- R_W is efficiently computable from the endpoints of parties in some k-subset S(W)?
- The subset S(W) depends on the Foata structure of W?
- R_W(endpoints of parties NOT in S(W)) reveals nothing about m?

This is a well-posed question but I conjecture the answer is NO for sum-preserving monodromy, because the sum-mod-N structure is inherently global (all-party).

### Direction C: Non-sum reconstruction exploiting RAAG structure

What if we abandon sum-mod-N entirely and design a reconstruction method native to the RAAG?

**Idea**: The secret is not m = sum s_i mod N, but rather m = f(s_0,...,s_{T-1}) for some function f that is RAAG-aware. For example:
- Assign generators to parties: party i controls generator g_i.
- The secret is encoded in the WORD W itself (a la Panagopoulos), not in the starting sheets.
- Reconstruction: k parties contribute their generators' actions, and from these, the trace class of W (hence the secret) can be determined.

**But**: this IS Panagopoulos' scheme, specialized to RAAG presentations. The threshold (k,T) would come from the clique cover number of Gamma (the minimum number of cliques needed to cover all generators). This is well-defined and gives k < T when Gamma has efficient covers.

**Mathematical content**: The clique cover number theta(Gamma) of the commutation graph determines the minimum coalition size. A coalition whose generators' support covers all of Gamma can determine the full trace class. A coalition missing some generators cannot.

**Example**: Gamma = K_{1,m} (star). Clique cover number = m (each leaf is its own clique in the complement, or equivalently, the hub plus each leaf is a 2-clique in Gamma, but we need to cover the leaves which form an independent set in Gamma). Actually, the clique cover of the complement graph (non-commutation graph) matters here. Let me reconsider.

For Panagopoulos-style RAAG threshold: the relevant parameter is the covering number of the COMMUTATION RELATIONS, not the generators. Each relation g_i g_j = g_j g_i (i.e., each edge of Gamma) is assigned to a subset of parties. The threshold is determined by how the relations are distributed.

**This is a departure from PGG-SMC.** The covering-space walk is replaced by a Panagopoulos-style word-problem protocol. The RAAG provides the group presentation. But the monodromy representation is no longer central.

---

## Summary Table

| Idea | Core mechanism | Fatal flaw | Fixable? | Would fix stay within PGG-SMC? |
|------|---------------|------------|----------|-------------------------------|
| 1. Clique projections | Decompose rho(W) by clique | rho collapses trace structure | Only via product coverings | No (reduces to heterogeneous, still (T,T)) |
| 2. Foata layers | Layer-by-layer reconstruction | Sum-mod-N is global, not per-layer | No | N/A |
| 3. Decoupling | Add threshold layer on top | Works, but RAAG irrelevant to threshold | Already "fixed" | Partially (composition, not unified) |
| 4. Hub generator | Hub commutativity = redundancy | Hub info is public or hidden; doesn't help endpoints | No | N/A |
| 5. Redundant encoding | Clique-based error correction | Clique components still (|C|,|C|); hub bottleneck | No | N/A |

## Conclusion

**The RAAG structure cannot break the (T,T) barrier within PGG-SMC.** The fundamental reason is a level mismatch: the RAAG structures the word/trace space, but reconstruction operates on the endpoint/value space, and the monodromy homomorphism rho does not preserve the RAAG's decomposition properties.

The only viable path to (k,T) is to add an independent threshold mechanism (Direction A), which makes the RAAG structure irrelevant to the threshold property. Alternatively, one could replace sum-mod-N with a Panagopoulos-style protocol using the RAAG presentation (Direction C), but this abandons the covering-space framework.

**The honest framing**: PGG-SMC provides exponential search-space security (post-quantum) at the cost of (T,T) threshold. The RAAG structure controls the search space size (between C(L+Tg-1,Tg-1) for abelian and Tg^L for free), which is the SECURITY parameter. The THRESHOLD parameter is determined by the reconstruction method (sum-mod-N), which is algebraically independent of the RAAG structure.

**The key mathematical fact**: For any group homomorphism rho: G -> S_N and any decomposition G = A * B (internal product), it is NOT generally true that rho(G) decomposes as rho(A) x rho(B). The image of a product is not the product of images in the non-abelian case. This single fact -- that homomorphisms don't preserve internal decompositions -- is the root of the (T,T) barrier.
