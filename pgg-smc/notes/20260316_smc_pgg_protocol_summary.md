# SMC-PGG Protocol Summary (Meeting Brief)

*2026-03-16*

## What is SMC-PGG?

**Problem.** N parties wish to jointly compute a function of their private inputs without revealing those inputs to any coalition of fewer than T parties. SMC-PGG solves this for functions in the complexity class NC^1 (computable by Boolean circuits of polynomial size and polylogarithmic depth) using algebraic structure rather than circuit garbling.

A **covering-space-based secure multi-party computation** protocol. Instead of encoding computation as Boolean circuits (like Yao/GMW/SPDZ), it uses a **monodromy representation** `rho: G -> S_N` -- a group homomorphism mapping group elements to permutations on N "sheets."

Security comes from the ambiguity in which word (over generators) produced a given observed endpoint — the adversary cannot determine which of the many possible words was used.

## Protocol and adversary model

### What the protocol computes

A **covering** of the Riemann sphere assigns N **sheets** (indexed by `'I_N`) to each point. The **monodromy group** G ≤ S_N is the group of sheet permutations induced by analytic continuation around branch points. Each branch point contributes a **generator** σ_i ∈ G.

The protocol computes a **word** w = (w_0, ..., w_{L-1}) — a tuple of Tg generator **indices** (`w : L.-tuple 'I_Tg` in the code, where Tg is the number of generators). The group element is the product of generators looked up by index:

```
word_eval w := tnth(sigmas, w_0) · tnth(sigmas, w_1) · ... · tnth(sigmas, w_{L-1})   ∈ G
```

Each party i starts on sheet `start_sheet(i)` and receives:

```
endpoint(word_eval w, start_sheet(i)) = rho(word_eval w)(start_sheet(i))   ∈ 'I_N
```

This is the party's **output**: the sheet they end up on after the monodromy action.

### Adversary model

The adversary is a **passive (semi-honest) coalition** of T-1 out of T parties. Each coalition member i ∈ {0, ..., T-2} observes their own endpoint `rho(g)(s_i)` honestly (follows protocol but tries to learn more). The **target** is the unobserved party `ord_max` with starting sheet `s_target`.

**What the adversary sees**: the T-1 values `{ rho(g)(s_0), rho(g)(s_1), ..., rho(g)(s_{T-2}) }`.

**What the adversary wants**: to determine `rho(g)(s_target)` — the unobserved party's endpoint.

**Security guarantee** (collusion bound, `pgg_collusion_bound.v`):
```
var_dist(adversary_marginal, uniform) ≤ ε + 2(T-1)/N
```
where `adversary_marginal` is the distribution of `rho(g)(s_target)` induced by the protocol's word sampling, and ε measures how far the protocol's permutation distribution is from truly uniform over S_N.

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

For genus 0, the additional constraint is `|G| ≤ PGL(2,N)` (automorphisms of P^1 are Möbius transformations). This is **axiomatized** (`genus0_aut_pgl` in `pgl_bound.v`) and appears as one arm of the `security_threshold_tradeoff` disjunction (see below).

### The security/threshold tradeoff

This is the core tension formalized by `AlgebraicRigidity`. The proved theorem (`security_threshold_tradeoff` in `cover_tradeoff.v`) is a **disjunction**:

- **Either** genus = 0, |G| ≤ PGL(2,N), and gap = 0 (ideal threshold, bounded group size)
- **Or** genus > 0, and gap ≤ 2 × genus (non-trivial threshold gap)

You cannot have both a large group (exceeding PGL(2,N)) AND genus-0 (ideal threshold). The contrapositive (`large_group_forces_gap`): if |G| > PGL(2,N), then genus > 0. Note this is NOT a monotone relationship — genus depends jointly on |G|, ramification, and base genus via Riemann-Hurwitz.

One algebraic choice (G, ρ, σ₁...σ_Tg) determines search space, security bound, threshold gap, and round complexity simultaneously — the four properties formalized in the `AlgebraicRigidity` record (which bundles `SecurityWitness`, `ThresholdWitness`, and `RoundComplexityWitness`). Word length L and sampling distribution remain free parameters within `SecurityWitness`. Round complexity is L for any group; RAAG refinement to Foata depth gives a tighter `rc_depth` bound.

### Formalization architecture: two parallel tracks

Security and reconstruction are independent concerns that only meet at `AlgebraicRigidity`:

```
Security:       G, RAAG, words, fibers  ──→  SecurityWitness ──╮
                                                                ╰──→ AlgebraicRigidity
Reconstruction: code auto + fix_0 ──→ ts_perm_compatible ──→ ThresholdWitness ──╯
                                       + G_stable_starts
```

The **security track** (left) depends on the group G, its generators, word combinatorics, and fiber distributions. It produces a `SecurityWitness` (variational distance bound).

The **reconstruction track** (right) depends on the AG code, its automorphisms, and how monodromy acts as a coordinate permutation on shares. It produces a `ThresholdWitness` (covering scheme + PGL hypothesis).

The two tracks share the same group G but are otherwise independent — the security proofs never reference the threshold scheme, and the threshold proofs never reference word distributions. `AlgebraicRigidity` bundles both witnesses, making explicit that one algebraic choice determines both.

## What distinguishes it from circuit-based MPC?

**One algebraic design choice (group G + generators) determines four formalized properties (search space, security, threshold, round complexity):**

| Property | Determined by | Generality | Circuit MPC comparison |
|----------|--------------|------------|----------------------|
| **Computational power** | Group variety (Barrington-Therien) -> NC^1 (polylog-depth, poly-size Boolean circuits) | Any G | Circuits compute all of P |
| **Adversary search space** | Fiber count: words of length L evaluating distinctly, bounded by \|G\| | Any GeneratedMonodromyReprType | No structural bound |
| **Threshold gap** | Riemann-Hurwitz genus -> Goppa code bound: gap <= 2*genus | Any GeneratedMonodromyReprType | Shamir = genus-0 AG code (no gap) |
| **Round complexity** | General: L rounds (one per generator). RAAG refines via independence graph -> Foata depth (abelian = 1, L-free = L, partial = intermediate) | General bound: any G. Foata upper bound: RAAG | O(1) for Yao, O(depth) for GMW |

The `AlgebraicRigidity` record in `pgg-smc/reconstruct/algebraic_rigidity.v` bundles security and threshold into a single formal witness parameterized by `GeneratedMonodromyReprType` (group G + generators). Round complexity is L for any group; RAAG trace counts refine this to Foata depth as a separate derived property.

## Security notions achieved

1. **Collusion bound** (`pgg_collusion_bound.v`, Theorem 5):
   - Coalition of T-1 parties vs. one hidden party
   - `var_dist(adversary_marginal, uniform) <= eps + 2(T-1)/N`
   - eps = variational distance of rho-induced distribution from uniform on S_N
   - **Information-theoretic** -- no computational assumptions, conditional on the word sampling distribution

2. **Fiber uniformity** (informal motivation, not a formal theorem in the codebase): Under uniform word distribution, adversary facing all T-1 shares has equally likely candidate words per fiber. The formalized security result is the collusion bound above.

3. **Grover mitigation** (`pgg_security.v`): Doubling word length L->2L restores quadratic security against quantum search. Cost >= kappa^L (exponential in original L; kappa is the free-group ball growth rate, specific to that analysis).

4. **Model**: Semi-honest (passive), static corruptions, t < n/2. Conjectured weaker than simulation-based security (not formally proved in the codebase), but more tractable and algebraically characterized.

## What the dealer prepares

1. **Chooses group element sequence W** (`W : seq gT`)
2. **Computes permutation table**: rho(w) for each w in W (an N x |W| matrix of sheet indices)
3. **Extracts party i's column**: `share(W, i) = [rho(w)(s_i) | w in W]`
4. **Distributes**:
   - `share(W, i)` to party i (secret channel)
   - Public word index P_idx to all (public channel)

Each party computes their endpoint by simple table lookup. The reconstructor collects T endpoints and recovers the secret via the threshold scheme (the framework is parametric over `ThresholdScheme`; AG codes are one instance).

## Axiom boundary status (from git log)

### Fully proved

- **PGL(2,F_q) cardinality**: `|PGL(2,q)| = q(q^2-1)` via GL cardinality + scalar quotient in MathComp (commit 89dcb62)
- **Hyperelliptic Goppa bound** (`hyp_goppa_wt_mdeg`): proved via polynomial resultant R(x) = A^2 - B^2*f, parity + `max_poly_roots` (commit 0a4095a)
- **`dual_root_poly`**: proved from resultant-based dual evaluation encoding (commit c8f12d7)
- **`dual_min_dist`**: proved from `dual_root_poly` via root-counting (commit 483791a)
- **`hyp_priv_surj`**: privacy from dual minimum distance (commit ec5afd7)
- **`AlgebraicRigidity` record**: 0 Admitted, 0 Axioms (commit 89dcb62)

### Axiom declarations (8 total)

**Framework-level** (1):
1. `genus0_aut_pgl` -- Riemann's theorem: Aut(P^1) = PGL(2,F_q)

**Star instance** (2):
2. `star_covering` -- existence of a CoveringScheme for the star-graph instance
3. `star_genus0_pgl` -- the star instance lives on genus-0

**Monster instance** (5):
4. `monster_n` -- number of sheets (abstract, known to be ~ 10^20)
5. `monster_sigmas` -- two generators (exist by 2-generation of finite simple groups, CFSG)
6. `monster_lfree1` -- L-freeness at L=1 (trivial for distinct permutations)
7. `monster_covering` -- existence of a CoveringScheme
8. `monster_genus0_pgl` -- genus-0 PGL bound

The framework and star axioms are geometric existence statements. The Monster axioms additionally include group data (the group is too large to enumerate computationally).

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
  ↓  add SecurityWitness + ThresholdWitness
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
- Currently axiomatized for the star instance (requires AG code construction)

**Level 6: AlgebraicRigidity** — combine SecurityWitness + ThresholdWitness via `MkAlgebraicRigidity`
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
| **Fully connected** (clique/abelian) | All generators commute | 1 (fully parallel) | Multiset count (minimum) | `pgg_raag_clique.v` |
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

**Level 5** (axiomatized):
```
Axiom star_covering : CoveringScheme R_star.
Axiom star_genus0_pgl : ...                      (* requires AG code construction *)
```

**Level 6**:
```
star_rigidity := MkAlgebraicRigidity
  (star_security_witness_1 R m)
  star_threshold_witness
```

**Axiom count**: 2 (`star_covering`, `star_genus0_pgl`)

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

**Axiom count**: 5 (`monster_n`, `monster_sigmas`, `monster_lfree1`, `monster_covering`, `monster_genus0_pgl`)

The extra 3 axioms vs star are because the group data itself is abstract (star has concrete generators). The Monster illustrates the security/threshold tradeoff at an extreme scale:
- Security: astronomically strong (|G| ~ 10^53, so search space upper bound ~ 10^53)
- Threshold: |G| vastly exceeds PGL(2,N), so genus > 0 by the contrapositive. Gap ≤ 2 × genus; the exact genus depends on ramification data via Riemann-Hurwitz, not on |G| alone

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
| **Formal verification** | 43 Rocq files, 8 Axiom declarations (1 framework + 2 star + 5 monster) | None | None | None | None |

### Key structural differences

**1. Computation: same power, different parameterization**

All non-solvable groups compute NC^1 (Barrington-Therien). Barrington-based MPC fixes S_5 (which contains A_5, the smallest non-solvable group). PGG-SMC parameterizes over G, but this does NOT give more computational power — it affects **security parameters**: different G gives different N (sheets), different eps (distance from uniform on S_N), different fiber sizes. The choice of G is a security tuning knob, not a computation knob.

**2. Threshold: Shamir IS genus-0 AG code**

Shamir's secret sharing is polynomial evaluation on the projective line P^1 — a Reed-Solomon code, which is an AG code at genus 0. The Goppa bound at genus 0 gives distance = n - k + 1 (MDS), so threshold = k exactly, no gap.

This means:
- PGG-SMC at genus 0 **recovers Shamir** (no threshold gap)
- PGG-SMC at genus > 0 gets **worse threshold** (gap <= 2g)
- Barrington-based MPC composed with Shamir = Barrington + genus-0 AG code
- The genus is determined by G via Riemann-Hurwitz, so **G determines both security and threshold simultaneously** — they are coupled, not independently tunable

This coupling is the core insight of the `AlgebraicRigidity` record: choosing a larger G may improve security (larger search space, smaller eps) but worsen threshold (higher genus). Whether this tradeoff is favorable depends on the application.

**3. Reconstruction: covering space bridge**

Only PGG-SMC connects group theory to algebraic geometry via covering spaces:
- Monodromy group G -> covering curve C -> genus g(C) via Riemann-Hurwitz -> AG code on C -> threshold scheme
- This bridge is mathematically novel but **constrains** rather than enables: the genus is forced by the group choice, unlike Shamir where threshold is freely chosen

ZAS correlations and Barrington-based MPC have no analogue of this bridge — they don't touch algebraic curves or AG codes.

**4. Round complexity: algebraic characterization**

For any group G with a word of length L, round complexity is trivially L (one generator per round). When the generators carry a RAAG independence graph, commuting generators can execute in parallel, reducing depth to the Foata normal form depth. This is a clean algebraic characterization absent from other protocols. It doesn't yield *fewer* rounds than L — it gives an upper bound on how many rounds a given algebraic choice requires, and quantifies the parallelism available.

**5. Security quantification: computable bound vs. simulation**

PGG-SMC gives a concrete, computable variational distance bound (eps + 2(T-1)/N) derived from the monodromy representation. This is weaker than simulation-based security (used by Barrington-based and ZAS) but more explicit — you can compute the bound from G and rho without constructing a simulator.

### What PGG-SMC genuinely contributes

1. **Covering space perspective**: Connecting monodromy groups to AG codes via Riemann-Hurwitz. No other protocol in this family uses algebraic geometry this way. This reveals that the security/threshold tradeoff is governed by genus.

2. **Coupled parameter framework**: The `AlgebraicRigidity` record formalizes that one algebraic choice (G + generators) determines search space, security, and threshold gap. Round complexity (trivially L; refined to Foata depth when RAAG commutation is specified) and computational power (NC^1 for non-solvable G) are derived separately. Other protocols treat these as independent design decisions.

3. **Machine-checked proofs**: 43 Rocq files. EasyCrypt has formalized Maurer's MPC (abelian/linear, active security); Isabelle/CryptHOL has 2-party multiplication. No non-abelian group MPC has formal verification.

### What PGG-SMC does NOT contribute

1. **More computational power**: NC^1 regardless of G choice, same as Barrington with S_5.
2. **Better threshold**: Genus coupling means potentially worse threshold than Shamir (genus-0). Barrington + Shamir gets optimal threshold for free.
3. **Stronger security model**: Semi-honest only, weaker than simulation-based security achieved by Barrington-based and ZAS.
4. **Practical efficiency**: Research prototype, not deployment-ready. No performance comparison with existing systems.

### Honest summary

Compared to the non-abelian group MPC family, PGG-SMC is not a better protocol on any operational axis. Its contribution is a **mathematical framework** that:
- Reveals the covering-space structure underlying group-based MPC
- Makes the security/threshold tradeoff explicit via genus
- Provides the first formal verification of a non-abelian group MPC

The framework's value is in **understanding** — showing that protocol properties are algebraically coupled — rather than in **capability**.
