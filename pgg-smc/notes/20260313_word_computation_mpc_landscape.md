# Word Composition as Computation: SMC-PGG in the MPC Landscape

*Date: 2026-03-13*

**Companion to**: `20260312_words_as_computation_formal_languages.md` (formal language theory correspondence)

## 1. Introduction

The companion note establishes that SMC-PGG's monodromy words are formal language theory objects — fiber languages L_g, trace monoids, Eilenberg varieties. That note asks: *what does FLT tell us about the protocol's security?*

This note asks a different question: **what can SMC-PGG compute?**

The answer turns out to be well-studied. Representing computation as a product of algebraic elements — permutations, matrices, group elements — is a central technique in complexity theory and cryptography. Barrington (1989) showed that width-5 branching programs (= words over S_5) evaluate any NC^1 circuit. This same word-product paradigm underlies indistinguishability obfuscation, randomized encodings, group-based FHE, and the algebraic characterization of information-theoretically secure MPC.

SMC-PGG sits at a specific point in this landscape. This note maps where.

**Contributions.** We (1) survey the "word = computation" paradigm across complexity and cryptography, (2) locate SMC-PGG within this landscape by identifying its closest relatives (commuting permutation systems, Barrington's theorem, randomized encodings), and (3) identify concrete extensions: what SMC-PGG can compute beyond secret sharing, and what algebraic structure is needed.


## 2. The Word-Product Paradigm

The unifying idea: a function f(x_1, ..., x_n) is represented as a **product of algebraic elements**, where each factor depends on one input variable.

```
f(x_1, ..., x_n) = g_1(x_1) · g_2(x_2) · ... · g_n(x_n)    evaluated in some monoid M
```

The output is read from the product — either as identity/non-identity (language recognition), as the image of a fixed point under a permutation (function computation), or as a matrix entry (branching program evaluation).

Different instantiations of M, the reading method, and the encoding of g_i yield different computational models:

| Model | Monoid M | Factors g_i | Output reading | Computational power |
|-------|----------|-------------|----------------|-------------------|
| Branching program | Matrix monoid GL_k(F) | Matrices indexed by x_i | Entry of product matrix | P (unrestricted width) |
| Barrington BP | S_5 (width 5) | Permutations indexed by x_i | Product = id or 5-cycle | NC^1 |
| Permutation automaton | Transformation monoid T(Q) | Transitions δ(−, a_i) | Final state | Regular languages |
| SMC-PGG | Monodromy group G ≤ S_N | ρ(σ_{i_j}) per step | Endpoint (sheet ID) | ? (this note) |
| CPS (see §4) | Direct product of S_k's | Commuting perms π_i(x_i) | Product applied to fixed pt | IT-secure functions |


## 3. Barrington's Theorem and Computational Power

### 3.1 The theorem

**Theorem (Barrington, 1989).** Every Boolean function computable by a polynomial-size, logarithmic-depth circuit (i.e., in NC^1) can be computed by a polynomial-length branching program of width 5.

A width-5 branching program is a sequence of instructions (i_1, π_1^0, π_1^1), ..., (i_L, π_L^0, π_L^1), where each instruction selects a permutation π_j^{x_{i_j}} ∈ S_5 based on one input bit. The product π_1^{x_{i_1}} · ... · π_L^{x_{i_L}} equals either the identity (output 0) or a fixed 5-cycle (output 1).

The key algebraic fact: S_5 is **non-solvable** (equivalently, A_5 is simple and non-abelian). The commutator identity [α, β] = α^{-1}β^{-1}αβ, where α, β are 5-cycles, produces another 5-cycle. This enables inductive simulation of AND/OR gates by nesting commutators, with depth d requiring 4^d permutation factors.

### 3.2 The Barrington–Thérien complexity classification

**Theorem (Barrington–Thérien, 1988).** The algebraic structure of the monoid M in a bounded-width program determines its computational power:

| Monoid class | Complexity class | Characterization |
|-------------|-----------------|------------------|
| Finite non-solvable group | NC^1 | Full bounded-fan-in circuits |
| Finite solvable group | ACC^0 (mod-counting) | Circuits with MOD gates |
| Finite aperiodic monoid | AC^0 | Constant-depth unbounded fan-in |
| Finite group of exponent p | MOD_p | Modular counting |
| Commutative monoid | ACC^0 ∩ comm | Symmetric functions only |

This is the same Eilenberg-variety hierarchy from the companion note, now read as a **computational power hierarchy** rather than a language classification.

### 3.3 Connection to SMC-PGG

In SMC-PGG, each party applies a monodromy permutation ρ(σ_i) to their sheet ID. The composition of all steps is a word w = σ_{i_1} · ... · σ_{i_L} evaluated in the monodromy group G via the representation ρ: F → G.

The Barrington–Thérien classification tells us:

- If G is **non-solvable** (e.g., G = S_N for N ≥ 5): the word-product can compute any NC^1 function of the letters' "input bits." In principle, SMC-PGG over S_N can evaluate arbitrary bounded-depth circuits.
- If G is **solvable but non-abelian**: limited to modular arithmetic (ACC^0).
- If G is **abelian**: limited to symmetric functions of the inputs (sums, counts).
- If G is **trivial**: nothing — which is the degenerate case where the protocol has no computational content.

**Current SMC-PGG** uses the monodromy group for secret sharing (endpoint = share), not for circuit evaluation. But the algebraic machinery is there. The question is whether the protocol structure can be extended to exploit Barrington's construction.


## 4. Commuting Permutation Systems: The MPC Characterization

### 4.1 Definition

**Definition (Agarwal–Anand–Prabhakaran, EUROCRYPT 2019).** A function f: X_1 × ... × X_n → Y has a **Commuting Permutation System (CPS)** if there exist:
- A finite set S with a distinguished element s_0 ∈ S
- For each party i and input x_i ∈ X_i, a permutation π_i(x_i) ∈ Sym(S)

such that:
1. **Commutativity**: π_i(x_i) ∘ π_j(x_j) = π_j(x_j) ∘ π_i(x_i) for all i ≠ j, all x_i, x_j
2. **Correctness**: f(x_1, ..., x_n) = (π_1(x_1) ∘ ... ∘ π_n(x_n))(s_0)

**Theorem (Agarwal–Anand–Prabhakaran, 2019).** A function f admits information-theoretically secure non-interactive MPC (NIMPC) with perfect security if and only if f has a CPS.

### 4.2 CPS and SMC-PGG

The structural parallel is immediate:

| CPS | SMC-PGG |
|-----|---------|
| Finite set S | Sheets {1, ..., N} |
| Distinguished element s_0 | Starting sheet |
| Permutation π_i(x_i) | Monodromy action ρ(σ_{i_j}) |
| Commutativity condition | Independence relation I (trace monoid) |
| Product applied to s_0 | Endpoint of monodromy walk |

The critical difference: CPS requires **full commutativity** (all pairs commute), while SMC-PGG allows **partial commutativity** (only independent generators commute, forming a trace monoid M(Σ, I)). This means:

- **CPS ⊂ SMC-PGG** in algebraic structure: every CPS is an SMC-PGG instance where I = Σ × Σ (all generators commute).
- SMC-PGG with partial commutativity can potentially compute functions that CPS cannot — the non-commuting generators carry additional computational power (per Barrington–Thérien, non-commutativity is exactly what enables NC^1).
- But SMC-PGG pays for this: partial commutativity means the evaluation order matters, requiring interactive rounds (not just simultaneous messages).

### 4.3 The NIMPC spectrum

| Protocol class | Commutativity | Interaction | Computable functions |
|---------------|---------------|-------------|---------------------|
| NIMPC / CPS | Full (abelian) | None (simultaneous) | CPS-characterizable |
| SMC-PGG (RAAG) | Partial (trace monoid) | Round-based | Intermediate — open |
| General MPC | None | Arbitrary rounds | All (with OT) |

SMC-PGG occupies the middle ground. The independence graph of the RAAG determines both the commutativity structure and the round complexity.


## 5. Randomized Encodings and Garbled Words

### 5.1 The Ishai–Kushilevitz construction

**Theorem (Ishai–Kushilevitz, 2002).** Any branching program P of length L and width w over a field F has a degree-3 randomized encoding: a set of degree-3 polynomials in the input bits and random coins whose joint distribution reveals f(x) but nothing else.

The construction: given a matrix branching program M_1(x) · M_2(x) · ... · M_L(x), choose random invertible matrices R_0, R_1, ..., R_L (with R_0 = R_L = I) and output the "garbled" factors:

```
R_0 · M_1(x) · R_1^{-1},   R_1 · M_2(x) · R_2^{-1},   ...,   R_{L-1} · M_L(x) · R_L
```

The product telescopes to M_1(x) · ... · M_L(x) (correctness), but each individual garbled factor is uniformly random given only the product (security).

### 5.2 Connection to SMC-PGG

This "garbled word" technique is structurally similar to how SMC-PGG distributes computation:

- Each party sees only their portion of the word (their monodromy steps).
- The random sheet assignment acts like the random matrices R_i — it masks individual steps while preserving the product structure.
- Security comes from the fact that partial information about the word (individual letters or small subsets) reveals nothing about the full product, given the randomization.

The difference: Ishai–Kushilevitz garbles a branching program for a *predetermined* function, while SMC-PGG distributes a word whose *content* is the secret. In SMC-PGG the word IS the secret; in garbled BPs the word computes ON the secret.

**Potential extension**: Use SMC-PGG's monodromy structure to evaluate a Barrington branching program on secret-shared inputs. Each party contributes their permutation factor (selected by their input bit), and the product reveals the function output. The trace monoid structure determines which steps can be parallelized.


## 6. Landscape Map

```
                        Word-Product Computation in Cryptography
                        ═════════════════════════════════════════

    COMPLEXITY THEORY                          CRYPTOGRAPHY / MPC
    ─────────────────                          ──────────────────

    Branching programs                         Oblivious evaluation
    (width w, length L)          ──────────→   (Ishai-Paskin 2007: eval BP
         │                                      on encrypted data)
         │
         │ Barrington (1989):
         │ NC^1 = width-5 over S_5
         │
         ▼
    Permutation BPs              ──────────→   Indistinguishability Obfuscation
    (word over S_5 / GL_k)                     (Garg+ 2013: encode matrices
         │                                      via multilinear maps)
         │
         │ Barrington-Thérien:
         │ monoid variety = complexity class
         │
         ▼
    Algebraic automata           ──────────→   Commuting Permutation Systems
    (transformation monoid)                    (Agarwal+ 2019: f has IT-secure
         │                                      NIMPC iff f has CPS)
         │                                           │
         │ Eilenberg variety                         │ Relax full commutativity
         │ = language class                          │ to partial commutativity
         │                                           │
         ▼                                           ▼
    Trace monoids M(Σ,I)        ◄──────────→   ┌─────────────────┐
    (Mazurkiewicz 1977)                        │    SMC-PGG       │
         │                                     │                  │
         │ Diekert-Gastin:                     │  Monodromy walk  │
         │ FO-definability on traces           │  on sheets via   │
         │                                     │  RAAG generators │
         ▼                                     └────────┬─────────┘
    Variety hierarchy                                   │
    (star-free ⊂ group ⊂ reg)                          │
         │                                              │
         │ Krohn-Rhodes:                                │ Barrington applied:
         │ cascade decomposition                        │ what can the word compute?
         │                                              │
         ▼                                              ▼
    Simple group + aperiodic     ──────────→   Protocol decomposition
    components                                 (group layers: SMC-PGG;
                                                aperiodic layers: new protocol)

                                               ──────────→
                                               Randomized encodings
                                               (Ishai-Kushilevitz 2002:
                                                garbled branching programs)

                                               ──────────→
                                               Group-based FHE
                                               (Nuida 2014, GRAFHEN 2025:
                                                homomorphic ops = group mult)
```


## 7. What SMC-PGG Can Compute: Three Regimes

### 7.1 Current: Secret sharing only

In the current formalization, the word w = σ_{i_1} · ... · σ_{i_ℓ} encodes a group element g = eval(w), and the protocol computes endpoints — which party holds which sheet after the walk. The "computation" is just the monodromy action; the output is the share assignment.

Computational content: essentially nothing beyond the group operation itself. The word IS the secret, not a program.

### 7.2 Near-term: Function evaluation via Barrington

Suppose parties hold private input bits x_1, ..., x_n. By Barrington's theorem, any NC^1 function f(x_1, ..., x_n) can be expressed as:

```
f(x_1, ..., x_n) = 1  iff  π_1^{x_{i_1}} · π_2^{x_{i_2}} · ... · π_L^{x_{i_L}} = (1 2 3 4 5)
```

where each π_j^0, π_j^1 ∈ S_5 and L = poly(n).

To execute this in SMC-PGG:
1. Set G = S_5 (or any non-solvable group) as the monodromy group.
2. Each instruction (i_j, π_j^0, π_j^1) becomes a monodromy step: party i_j selects permutation π_j^{x_{i_j}} based on their private bit.
3. The endpoint reveals whether the product equals the target 5-cycle.

**What this buys**: Secure evaluation of NC^1 functions — which includes integer comparison, addition, sorting networks, majority, and all regular language recognition — using the monodromy walk as the computational medium.

**What is needed**: The protocol must be extended so that (a) parties select which permutation to apply based on private input (not just execute a fixed word), and (b) the product is revealed without revealing individual factors. The randomized encoding technique (§5) provides the security mechanism.

### 7.3 Speculative: Beyond NC^1 via cascaded rounds

The Krohn–Rhodes decomposition expresses any finite automaton as a cascade (wreath product) of simple groups and aperiodic (counter-free) components. Each layer corresponds to one "round" of computation:

- **Group layers**: Handled by SMC-PGG (monodromy over the simple group).
- **Aperiodic layers**: Require a different protocol primitive — one that computes counter-free (= star-free language recognition) functions without group structure.

Composing rounds could extend SMC-PGG beyond NC^1 to all regular language recognition, and potentially further. This is the direction sketched in the companion note (§7.2). Nobody has developed this.

**Honest assessment**: The single-round Barrington extension (§7.2) is concrete and implementable. The cascaded-round extension is mathematically grounded but requires significant protocol design work. Anything beyond regular languages (e.g., context-free) is speculative.


## 8. The Algebraic Structure ↔ Computational Power Dictionary

| SMC-PGG design choice | Algebraic property | Computational consequence |
|---|---|---|
| Monodromy group G = S_N, N ≥ 5 | Non-solvable | Can compute NC^1 (Barrington) |
| G solvable, non-abelian | Solvable group | Limited to modular counting (ACC^0) |
| G abelian | Commutative | Symmetric functions only (sums, thresholds) |
| Independence relation I = ∅ | Free monoid (no commutativity) | Sequential — no parallelism, but max computational power |
| I = Σ × Σ | Full commutativity | Non-interactive (CPS/NIMPC) — but limited to CPS-computable functions |
| I partial (RAAG) | Trace monoid | Trade-off: more commutativity → more parallelism, less computational power |
| Word length ℓ | Program length | Determines circuit size (poly(n) for Barrington) |
| Number of generators |Σ|| Alphabet size | Determines per-step branching factor |

The fundamental trade-off: **commutativity enables parallelism and non-interaction, but reduces computational power.** A fully commutative protocol (CPS) requires no interaction but can only compute a restricted class of functions. A fully non-commutative protocol (free group) has maximum computational power but requires strict sequential execution.

SMC-PGG's RAAG structure navigates this trade-off: the independence graph I determines which generators commute, allowing parallel execution of independent steps while preserving computational power from the non-commuting part.


## 9. Related Paradigms

### 9.1 Garbled circuits vs garbled words

Yao's garbled circuits (1986) and Ishai–Kushilevitz's garbled branching programs (2002) are both "garbled computation" — one over Boolean circuits, the other over word products. The word-product version has degree-3 randomized encodings (vs. degree-2 for circuits), but branching programs can be exponentially more compact for certain functions.

### 9.2 Group-based FHE

Nuida (2014) proposed fully homomorphic encryption from group theory: encode bits as group elements, perform homomorphic operations via group multiplication. The non-solvability of A_5 (same as Barrington) is essential for computational completeness. GRAFHEN (2025) implements this approach with rewriting systems, achieving orders-of-magnitude speedup over lattice-based FHE.

Both rely on the word-product paradigm: ciphertext = group element, homomorphic eval = word composition.

### 9.3 Oblivious automata evaluation

Ishai–Paskin (2007) evaluate branching programs on encrypted data: given an encryption of x, compute a succinct ciphertext of P(x). The word structure enables step-by-step homomorphic evaluation, with ciphertext size depending on input length and BP length, not BP width.

Applications: private DFA evaluation for DNA pattern matching (Frikken 2009), virus genome detection (WPES 2014), and regex matching on encrypted strings (ACNS 2022).

### 9.4 Private simultaneous messages (PSM)

Feige–Kilian–Naor (1994): in the PSM model, each party sends one message to a referee who computes f. For branching programs of size t, communication is O(t). Each party's message is a "letter"; the referee assembles the "word." This is the minimal-interaction instantiation of the word-product paradigm.


## 10. Open Directions

**1. SMC-PGG as Barrington evaluator.** Extend the protocol so that each monodromy step selects a permutation based on private input (not a fixed generator). This turns SMC-PGG from a secret sharing protocol into an NC^1 function evaluator. The trace monoid structure then determines which Barrington instructions can be executed in parallel.

**2. Quantifying the commutativity–power trade-off.** For a given independence graph I and group G, what is the class of functions computable by polynomial-length words over M(Σ, I) evaluated in G? The extremes are known (I = ∅ → NC^1 for non-solvable G; I = Σ×Σ → CPS). The intermediate cases (partial commutativity) are unstudied.

**3. Garbled monodromy walks.** Apply the Ishai–Kushilevitz randomization to SMC-PGG: garble each monodromy step so that individual permutations are masked but the product is preserved. This would give a concrete randomized encoding for the protocol's computation.

**4. Krohn–Rhodes protocol stack.** Implement the cascaded decomposition: alternate group-layer rounds (SMC-PGG) with aperiodic-layer rounds (a new counter-free primitive). Each layer adds computational power. The composition theorem from Krohn–Rhodes guarantees completeness for all finite-state computation.

**5. From NC^1 to NC.** Barrington's theorem gives NC^1. For higher depth (NC^2, ..., NC), Barrington–Thérien gives polynomial-size programs over monoids of polynomial width. Can SMC-PGG be extended to polynomial-width monodromy (= multiple covering spaces composed)?

**Honest status**: Direction 1 is concrete and requires protocol engineering. Direction 2 is a clean theoretical question. Directions 3–5 are increasingly speculative.


## 11. Summary

SMC-PGG's monodromy walk is a word-product computation over a finite group. This places it in a well-studied landscape:

- **Complexity**: Barrington–Thérien classifies which functions word-products can compute, indexed by the algebraic structure of the group/monoid. Non-solvable groups give NC^1; solvable groups give modular counting; abelian groups give symmetric functions.
- **MPC**: Agarwal–Anand–Prabhakaran's CPS characterizes which functions admit non-interactive secure computation via commuting permutations. SMC-PGG generalizes CPS by allowing partial commutativity (trace monoid).
- **Encoding**: Ishai–Kushilevitz's randomized encodings show how to garble word-products for security. The same technique applies to SMC-PGG's monodromy walks.

The current protocol uses this machinery only for secret sharing (the word encodes the secret). But the algebraic structure supports much more: any NC^1 function can be securely evaluated by composing monodromy permutations, with the RAAG independence graph determining which steps parallelize.

The group variety is simultaneously a language class (Eilenberg), a complexity class (Barrington–Thérien), and a security parameter (SMC-PGG). This three-way correspondence — the same algebraic object viewed from formal language theory, computational complexity, and cryptographic protocol design — is the central observation connecting this note to its companion.


## 12. References

1. Barrington, D.A.M. (1989). "Bounded-Width Polynomial-Size Branching Programs Recognize Exactly Those Languages in NC^1." *JCSS*, 38(1):150–164.

2. Barrington, D.A.M. and Thérien, D. (1988). "Finite Monoids and the Fine Structure of NC^1." *JACM*, 35(4):941–952.

3. Agarwal, S., Anand, A., and Prabhakaran, M. (2019). "Cryptographic Complexity of Multi-Party Computation Problems: Classifications and Separations." In *EUROCRYPT 2019*, LNCS 11477:489–520. [ePrint 2019/278]

4. Beimel, A., Ishai, Y., Kumaresan, R., and Kushilevitz, E. (2018). "On the Cryptographic Complexity of the Worst Functions." In *ICALP 2018*, LIPIcs 107:103:1–103:14.

5. Beimel, A., Gabizon, A., Ishai, Y., and Kushilevitz, E. (2014). "Non-Interactive Secure Multiparty Computation." In *CRYPTO 2014*, LNCS 8617:387–404.

6. Ishai, Y. and Kushilevitz, E. (2002). "Perfect Constant-Round Secure Computation via Perfect Randomizing Polynomials." In *ICALP 2002*, LNCS 2380:244–256.

7. Applebaum, B., Ishai, Y., and Kushilevitz, E. (2006). "Computationally Private Randomizing Polynomials and Their Applications." *Computational Complexity*, 15(2):115–162.

8. Ishai, Y. and Paskin, A. (2007). "Evaluating Branching Programs on Encrypted Data." In *TCC 2007*, LNCS 4392:575–594.

9. Garg, S., Gentry, C., Halevi, S., Raykova, M., Sahai, A., and Waters, B. (2013). "Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits." In *FOCS 2013*, pp. 40–49. [ePrint 2013/451]

10. Feige, U., Kilian, J., and Naor, M. (1994). "A Minimal Model for Secure Computation." In *STOC 1994*, pp. 554–563.

11. Nuida, K. (2014). "A Simple Framework for Noise-Free Construction of Fully Homomorphic Encryption from a Special Class of Non-Commutative Groups." [ePrint 2014/097]

12. GRAFHEN (2025). "Noise-Free Fully Homomorphic Encryption via Group Encodings." [ePrint 2025/1907]

13. Frikken, K.B. (2009). "Practical Private DNA String Searching and Matching through Efficient Oblivious Automata Evaluation." In *DBSec 2009*, LNCS 5645:81–94.

14. Krohn, K. and Rhodes, J. (1965). "Algebraic Theory of Machines. I. Prime Decomposition Theorem for Finite Semigroups and Machines." *Trans. AMS*, 116:450–464.

15. Yao, A.C. (1986). "How to Generate and Exchange Secrets." In *FOCS 1986*, pp. 162–167.
