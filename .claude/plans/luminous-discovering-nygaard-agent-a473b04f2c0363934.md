# Candidate Frameworks for (k,T)-Threshold Secret Sharing in Covering-Space MPC

## Summary

Five candidate mathematical frameworks are evaluated for their suitability as (k,T)-threshold secret sharing schemes in a covering-space MPC protocol. Each is assessed on: construction, threshold achieved, Coq/Rocq formalizability, and practical implementations.

---

## 1. Compressive Sensing Secret Sharing (Sparse Recovery)

### Construction
The formal analogy maps:
- **Secret** <-> sparse signal x in R^N (or F_q^N)
- **Shares** <-> compressed measurements y = Ax, where A is an m x N measurement matrix (m << N)
- **Reconstruction** <-> sparse recovery via basis pursuit / OMP

A (k,T)-threshold is achieved by designing the measurement matrix A so that any T rows of A satisfy the Restricted Isometry Property (RIP) of order k -- meaning any k-sparse signal can be recovered from T measurements. The "secret" is the sparse signal, and each party holds one row of A and the corresponding measurement.

### Threshold Achieved
- **Recovery threshold**: If A satisfies RIP of order 2k with constant delta_{2k} < sqrt(2) - 1, then k-sparse signals are recoverable from m = O(k log(N/k)) measurements.
- **Privacy threshold**: Fewer than ~k measurements reveal no information about the k-sparse secret (information-theoretic security only if A is random over a finite field; over R, only computational security).
- **Gap**: The threshold is NOT sharp like Shamir -- there is a gap between the privacy threshold and the reconstruction threshold. This is a fundamental disadvantage for (k,T)-threshold schemes.

### Coq/Rocq Formalizability
- **Difficult.** RIP verification is NP-hard. The theory requires real analysis (or finite-field linear algebra) plus optimization theory (LP relaxation for basis pursuit). No existing Coq formalization of compressed sensing exists.
- MathComp has finite-field linear algebra, but the optimization/recovery algorithms would need to be built from scratch.
- Rating: **Low feasibility** for formal verification.

### Practical Implementations
- Primarily used for **image secret sharing** (visual cryptography), not general MPC.
- Several papers combine CS with chaotic systems for image encryption + sharing (e.g., Springer Multimedia Systems 2023, ScienceDirect 2023).
- No known deployment for general-purpose MPC protocols.

### Verdict for Covering-Space MPC
**Poor fit.** The non-sharp threshold (gap between privacy and reconstruction), NP-hardness of RIP verification, and lack of algebraic structure compatible with covering spaces make this unsuitable. The analogy is suggestive but does not yield clean (k,T)-threshold schemes.

---

## 2. Low-Rank Matrix Completion

### Construction
The idea: represent the secret as an unknown low-rank matrix M (rank r), reveal a subset of entries to each party, and reconstruction = matrix completion.
- **Secret**: rank-r matrix M of size p x q
- **Shares**: subsets of entries of M, determined by a bipartite graph G (rows = "left vertices", columns = "right vertices", edges = known entries)
- **Reconstruction**: complete M from observed entries, possible when the graph G is "rigid" in the sense of Singer-Cucuringu.

### Threshold / Uniqueness Condition (Singer-Cucuringu 2010)
Singer and Cucuringu (SIAM J. Matrix Anal. Appl., 2010) showed that **rigidity theory** governs uniqueness of low-rank matrix completion:
- They define a **completion matrix** (analogous to the rigidity matrix in structural rigidity).
- A rank-r completion is **locally unique** iff the completion matrix has full rank.
- A rank-r completion is **globally unique** under stronger conditions (analogous to global rigidity of bar-and-joint frameworks).
- For a (k,T)-threshold: you need at least T = O(r(p+q) - r^2) observed entries for generic uniqueness, and this is sharp.

### Privacy
- **Not information-theoretic** in general. Even a single entry of M reveals partial information. Unlike Shamir, there is no clean "T-1 entries reveal nothing" property.
- Could potentially be combined with additive noise or over finite fields to get privacy, but this is not standard.

### Coq/Rocq Formalizability
- **Moderate.** The rigidity-theory framework is combinatorial/linear-algebraic. MathComp has matrix rank, graph theory basics.
- The completion matrix is a specific Jacobian-like construction; formalizing its rank conditions would require significant work but is feasible in principle.
- Rating: **Moderate feasibility**, but the lack of clean privacy thresholds is a theoretical obstacle.

### Practical Implementations
- Matrix completion is heavily used in recommender systems (Netflix problem) but NOT for secret sharing or MPC.
- No known cryptographic deployment.

### Verdict for Covering-Space MPC
**Interesting but impractical.** The rigidity-theory connection is elegant and potentially relevant to covering-space geometry (the "completion matrix" could relate to fiber structure). But the lack of information-theoretic privacy makes it unsuitable as a standalone secret sharing scheme. Could potentially serve as an auxiliary construction (e.g., for verifiability or error detection).

---

## 3. Rigidity Theory and Secret Sharing (Graph Rigidity)

### Construction
Graph rigidity studies when a graph embedded in R^d (with fixed edge lengths) has a unique realization (up to rigid motions). The connection to secret sharing would be:
- **Secret**: a geometric configuration (point positions)
- **Shares**: pairwise distances (edge lengths in the graph)
- **Reconstruction**: if the graph is globally rigid, the configuration is uniquely determined

### Threshold via Laman's Theorem / Rigidity Matroids
- In 2D, a graph is minimally rigid iff it satisfies Laman's condition: |E| = 2|V| - 3 and every subgraph on k vertices has at most 2k - 3 edges.
- The **rigidity matroid** determines which sets of edges (shares) allow reconstruction.
- This gives a **matroid-based access structure**, not a simple (k,T)-threshold.

### Connection to Secret Sharing
- The comprehensive review by Combinatorial Press (2024) surveys graph theory applications in secret sharing, but the connection is primarily about modeling access structures as graphs, NOT using rigidity per se.
- **Matroid-based secret sharing** (Brickell-Davenport) shows that ideal secret sharing access structures are matroid ports. Rigidity matroids are a specific class of matroids, so they define a specific class of access structures.
- However, rigidity matroids are NOT in general representable over finite fields (they are defined over R), which limits their use for information-theoretic secret sharing.

### Coq/Rocq Formalizability
- **Moderate.** MathComp has matroid theory (in some libraries). Laman's theorem is combinatorial. But the geometric aspects (rigidity in R^d) require real analysis.
- Rating: **Moderate** for the combinatorial/matroid aspects; **Low** for the geometric aspects.

### Practical Implementations
- No known implementations of rigidity-based secret sharing.

### Verdict for Covering-Space MPC
**Theoretically suggestive, practically unusable.** The matroid connection is real but does not yield (k,T)-threshold schemes -- it yields more complex access structures. The covering-space connection would need to go through the rigidity matroid of the fiber graph, which is speculative. The Singer-Cucuringu matrix completion connection (Topic 2) is the more concrete bridge.

---

## 4. MDS Codes and Overdetermined Systems (The Standard Framework)

### Construction
This is the **gold standard** and the framework that Shamir's scheme belongs to.

- An [n, k, d]_q MDS (Maximum Distance Separable) code has d = n - k + 1 (meets the Singleton bound).
- **Secret sharing from MDS codes**: The secret is encoded as a codeword. Each party gets one coordinate. Any k coordinates determine the codeword (reconstruction), and any k-1 coordinates reveal nothing about the secret (privacy).
- **Shamir's scheme** is the special case where the MDS code is a Reed-Solomon code: the secret is f(0) for a random degree-(k-1) polynomial f, and shares are f(alpha_1), ..., f(alpha_n).

### Threshold Achieved
- **Perfect (k, n)-threshold**: Any k shares reconstruct; any k-1 shares reveal zero information.
- The threshold is sharp, with no gap.
- Over F_q, requires q >= n (need n distinct evaluation points).

### Key Properties
- **McEliece-Sarwate (1981)**: Formally proved the equivalence between Shamir secret sharing and Reed-Solomon codes.
- **Polynomial evaluation = codeword**: f(alpha_1), ..., f(alpha_n) is a Reed-Solomon codeword.
- **Reconstruction = polynomial interpolation**: Lagrange interpolation from any k points.
- **MDS property = every k x k submatrix of the Vandermonde matrix is invertible**.

### Coq/Rocq Formalizability
- **High feasibility.** This is the most formalization-friendly approach:
  - MathComp has finite fields, polynomials, Vandermonde matrices, matrix invertibility.
  - Reed-Solomon codes are already partially formalized in some Coq libraries.
  - The infotheo project already has information-theoretic foundations.
  - Lagrange interpolation over finite fields is straightforward to formalize.
- Rating: **High feasibility**. The algebraic structure is clean and well-supported by existing libraries.

### Practical Implementations
- **Ubiquitous.** Shamir secret sharing is the foundation of virtually all practical MPC protocols (SPDZ, BGW, GMW, etc.).
- Highly optimized implementations exist in every major crypto library.

### Verdict for Covering-Space MPC
**The baseline.** Any covering-space MPC protocol should be compared against MDS/Shamir as the default. The question is whether the covering-space structure provides additional benefits (e.g., smaller field sizes, better communication complexity, natural composition with the group action) that justify departing from this standard.

---

## 5. Algebraic Geometry Codes on Fibers of Covering Maps

### Construction (Chen-Cramer, CRYPTO 2006 + subsequent work)
This is the most directly relevant framework for covering-space MPC.

- Start with an algebraic curve C of genus g over F_q, with n+1 rational points P_0, P_1, ..., P_n.
- Fix a divisor D on C with deg(D) = k-1+g.
- The **Riemann-Roch space** L(D) consists of rational functions with poles bounded by D.
- **Secret**: f(P_0) for a random f in L(D).
- **Shares**: f(P_1), ..., f(P_n).
- This is an **evaluation AG code**: codewords are evaluations of L(D)-functions at the rational points.

### Threshold Achieved
- **Quasi-threshold (T-rejecting, T+1+2g-accepting)**:
  - Any T = k-1 shares reveal nothing (privacy).
  - Any T+1+2g = k+2g shares reconstruct the secret (reconstruction).
  - There is a **gap of 2g** between privacy and reconstruction thresholds.
- When g = 0 (projective line), this reduces exactly to Shamir/Reed-Solomon (MDS).
- Over large fields (2021 result, arXiv:2101.01304): AG secret sharing schemes are **asymptotically threshold** -- the gap 2g becomes negligible relative to n as n grows.

### Connection to Covering Spaces
- When C is a cover of the projective line P^1 (via a morphism pi: C -> P^1), the rational points on C lying over a given point of P^1 form a **fiber**.
- A Galois cover C -> P^1 with Galois group G gives fibers that are G-orbits.
- Evaluating L(D)-functions on fibers of the covering map is exactly the AG code construction.
- **Key insight for your protocol**: If the MPC protocol has a covering-space structure with group G, then the AG code construction naturally respects this structure. The shares correspond to evaluations on fibers, and the group action permutes shares within fibers.

### Advantages Over MDS/Shamir for Covering-Space MPC
1. **Small fields**: AG codes can have n >> q (many rational points over a small field), breaking the q >= n barrier of Reed-Solomon.
2. **Structural compatibility**: The Galois group of the cover acts on the code, providing natural automorphisms that can be exploited in the protocol.
3. **Asymptotic efficiency**: Garcia-Stichtenoth towers give families of curves with n/q -> q-1 (optimal), enabling asymptotically good codes.

### Coq/Rocq Formalizability
- **Moderate-to-High feasibility**, given existing infrastructure:
  - MathComp has finite fields, polynomials, group theory.
  - The infotheo project has information-theoretic foundations and group actions.
  - The algebraic curve / Riemann-Roch theory is the hardest part to formalize. However, for specific curves (elliptic curves, hyperelliptic curves), explicit descriptions exist that avoid general AG machinery.
  - For genus-0 (Shamir), fully formalizable now.
  - For genus-1 (elliptic curves), significant but feasible effort.
  - For general genus, would require substantial development.
- Rating: **Moderate-High** for specific curves; **Moderate** for the general theory.

### Practical Implementations
- Chen-Cramer AG secret sharing has been implemented in research prototypes.
- The VIFF framework and subsequent MPC frameworks have explored AG-code-based protocols.
- Not as widely deployed as Shamir, but the theoretical foundation is solid.

### Verdict for Covering-Space MPC
**Best fit.** This is the natural framework for covering-space MPC:
- The evaluation-on-fibers construction directly mirrors the covering-space structure.
- The Galois group action provides structural compatibility with monodromy-based protocols.
- The quasi-threshold gap 2g is the price for small fields / large n, and is asymptotically negligible.
- Formalization is tractable for specific curves, and the genus-0 case (Shamir) serves as a base case.

---

## Comparative Summary

| Framework | Threshold | Privacy | Gap | Field Size | Coq Feasibility | MPC Deployed | Covering-Space Fit |
|---|---|---|---|---|---|---|---|
| Compressed Sensing | Approx. O(k log N) | Computational only | Large | R (or F_q) | Low | No | Poor |
| Matrix Completion | O(r(p+q)) | None (inherent) | N/A | R (or F_q) | Moderate | No | Interesting but impractical |
| Graph Rigidity | Matroid-dependent | Matroid-dependent | Complex | R | Moderate | No | Theoretically suggestive |
| MDS/Reed-Solomon | Exact k-of-n | Perfect | 0 | q >= n | **High** | **Yes (standard)** | Baseline (genus 0) |
| AG Codes on Covers | k to k+2g | Perfect | 2g | q can be small | Moderate-High | Research prototypes | **Best fit** |

## Recommendation

For a covering-space MPC protocol formalized in Coq/Rocq:

1. **Start with MDS/Shamir** (Topic 4) as the base case -- it is the genus-0 specialization, has the cleanest formalization path, and is the standard against which everything is compared.

2. **Generalize to AG codes on covers** (Topic 5) for the full covering-space structure. The Chen-Cramer framework with quasi-threshold (T, T+1+2g) is the right generalization. The 2g gap is the geometric price for the covering-space structure (genus of the cover curve).

3. **Use the Singer-Cucuringu rigidity connection** (Topic 2/3) as a theoretical tool for understanding uniqueness of the reconstruction problem, but not as a standalone secret sharing scheme.

4. **Avoid compressed sensing** (Topic 1) -- the analogy is superficial and does not yield clean threshold schemes.

---

## Sources

### Topic 1: Compressive Sensing + Secret Sharing
- [Verifiable Secret Image Sharing Based on Compressive Sensing](https://link.springer.com/article/10.1007/s11859-018-1313-2)
- [Low-overhead CS-driven multi-party secret image sharing](https://link.springer.com/article/10.1007/s00530-023-01049-2)
- [Secure and effective image encryption combining parallel CS with secret sharing](https://www.sciencedirect.com/science/article/abs/pii/S2214212623000716)
- [Compressed Sensing: How Sharp Is the RIP?](https://epubs.siam.org/doi/10.1137/090748160)
- [RIP - Wikipedia](https://en.wikipedia.org/wiki/Restricted_isometry_property)

### Topic 2: Matrix Completion + Rigidity
- [Singer & Cucuringu: Uniqueness of Low-Rank Matrix Completion by Rigidity Theory (arXiv)](https://arxiv.org/abs/0902.3846)
- [Singer & Cucuringu (SIAM)](https://epubs.siam.org/doi/10.1137/090750688)
- [Combinatorial Conditions for Unique Completability (SIAM Discrete Math)](https://epubs.siam.org/doi/10.1137/140960098)

### Topic 3: Rigidity + Secret Sharing + Matroids
- [Comprehensive review of graph theory in secret sharing](https://combinatorialpress.com/jcmcc-articles/volume-123/a-comprehensive-review-of-graph-theory-applications-in-secret-sharing-schemes/)
- [On Codes, Matroids and Secure MPC from LSSS](https://link.springer.com/chapter/10.1007/11535218_20)
- [Secret Sharing Schemes, Matroids and Polymatroids](https://eprint.iacr.org/2006/077.pdf)
- [Polynomial Secret Sharing and Algebraic Matroids](https://link.springer.com/chapter/10.1007/978-3-032-12293-3_14)
- [Structural Rigidity - Wikipedia](https://en.wikipedia.org/wiki/Structural_rigidity)

### Topic 4: MDS Codes + Shamir
- [McEliece & Sarwate: On sharing secrets and Reed-Solomon codes (ACM)](https://dl.acm.org/doi/10.1145/358746.358762)
- [Shamir Secret Sharing and Reed-Solomon Codes (MIT notes)](https://www.mit.edu/~linust/files/Secret_Sharing_and_Reed-Solomon_Codes.pdf)
- [MDS Codes, NMDS Codes and Secret-Sharing (Simos)](https://who.rocq.inria.fr/Dimitrios.Simos/docs/NMDS_SSS3.pdf)
- [Secret Sharing Using Near-MDS Codes](https://link.springer.com/chapter/10.1007/978-3-030-16458-4_12)
- [Ideal Hierarchical Secret Sharing based on MDS codes](https://eprint.iacr.org/2013/189.pdf)
- [Massey: Secret Sharing and Linear Complexity (lecture)](https://cs.ioc.ee/yik/schools/win2006/massey/slides3.pdf)
- [Generalized Secret Sharing Based on MDS Codes](https://link.springer.com/chapter/10.1007/978-981-13-8461-5_41)

### Topic 5: AG Codes on Covers
- [Chen & Cramer: AG Secret Sharing over Small Fields (CRYPTO 2006)](https://link.springer.com/chapter/10.1007/11818175_31)
- [AG Secret Sharing over Large Fields Are Asymptotically Threshold (arXiv 2021)](https://arxiv.org/abs/2101.01304)
- [Asymptotically-Good Arithmetic Secret Sharing over Z/p^l](https://link.springer.com/chapter/10.1007/978-3-030-84252-9_22)
- [Secret Sharing for Secure PIR using AG Codes (2024)](https://arxiv.org/html/2408.00542)
- [Efficient Information-Theoretic Secure MPC](https://www.iacr.org/archive/tcc2019/11891202/11891202.pdf)
- [AG Codes survey (Pellikaan et al.)](https://www.cs.utexas.edu/~danama/courses/codes/lec7-AG-codes.pdf)
- [AG Codes - Wikipedia](https://en.wikipedia.org/wiki/Goppa_code)
- [AG Codes and Applications (arXiv survey)](https://arxiv.org/abs/2009.01281)
- [Perfectly Secure Matrix Multiplication](https://www.emergentmind.com/topics/perfectly-secure-matrix-multiplication-psmm-protocol)
- [Threshold LSSS for MPC-in-the-Head (ASIACRYPT 2023)](https://dl.acm.org/doi/10.1007/978-981-99-8721-4_14)
