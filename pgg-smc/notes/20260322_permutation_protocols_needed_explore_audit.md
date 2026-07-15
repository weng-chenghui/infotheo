# Explore-Audit Report: What Protocols Inherently Need Permutation Groups?

**Date:** 2026-03-22
**Directions explored:** 5

## Executive Summary

We investigated what kinds of protocols or computations **inherently require** permutation group structure (not just use permutations combinatorially). Five directions were explored: (1) oblivious shuffling, (2) card-based crypto protocols, (3) branching program MPC, (4) ZK proofs with permutations, and (5) garbled branching programs vs circuits.

**Bottom line:** Permutations appear ubiquitously in crypto (shuffles, ZK, PLONK), but **permutation group theory** (spectral gap, representation theory, monodromy) is almost never used. The two directions where group structure is genuinely structural are:

1. **Card-based cryptographic protocols** — "Barrington Plays Cards" (STACS 2021) explicitly connects card shuffles to S_5 branching programs. No Coq formalization exists. This is PGG's best opportunity.
2. **Constant-round IT-secure NC^1 computation** — Ishai-Kushilevitz (2002) randomizing polynomials give perfect constant-round protocols for branching programs. This is the theoretical flagship.

Everything else (shuffling, PLONK, garbled circuits, mix-nets) uses permutations as combinatorial objects, not as algebraic groups with representation theory.

---

## Direction 1: Oblivious Shuffling / Secure Permutation

### Research Findings

Shuffling IS a permutation (pi in S_N), so the operation is inherently permutation-based. However, current implementations use:
- **Circuit-based networks**: Waksman (O(N log N) swaps), Benes networks
- **Cryptographic assumptions**: DDH, IND-CPA (ElGamal, Paillier)
- **ZK proofs for correctness**: polynomial invariance (Neff, Groth, Bayer-Groth)

No protocol uses spectral gap, monodromy, or Cayley graph properties for shuffling. The computational bottleneck is ZK proof generation, not the permutation operation.

**Exception found by audit**: Symmetric group representations ARE actively used in shuffle proofs (Choi/Bayer ASIACRYPT 2010). Also, Attrapadung et al. (CCS 2021) introduced algebraic group actions for round-optimal oblivious shuffle with 105-152x speedups.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: Shuffling = permutation operation | **TRUE** | Chaum 1981 confirmed |
| C2: Circuit-based (Waksman), not group theory | **SUSPICIOUS** | Overstated — symmetric group representations ARE used in shuffle proofs (Choi/Bayer 2010) |
| C3: Standard assumptions (DDH), not group-theoretic | **TRUE** | DDH/IND-CPA dominate |
| C4: CCS 2021 group actions for shuffle | **TRUE** | Paper verified; 105-152x speedups |
| C5: ZK proofs are bottleneck, not shuffle | **TRUE** | Bayer-Groth O(sqrt(N)) |
| C6: No IT lower bounds mandate group structure | **TRUE** | No such bounds found |
| C7: Expander topology separate from shuffle | **TRUE** | Danezis mix-net routing vs permutation |
| C8: Voting: ZK dominates cost | **TRUE** | Confirmed with nuance |

### Bottom Line
Shuffling uses permutations but not permutation group theory. PGG's monodromy representation would be an unnecessary indirection. **Not a good match for PGG.**

---

## Direction 2: Card-Based Cryptographic Protocols

### Research Findings

Card protocols (den Boer 1989 five-card trick, Mizuki-Sone) are **literally permutation group computation** — shuffles are random permutations of physical cards. Key finding:

**"Barrington Plays Cards" (Dvorak & Koucky, STACS 2021)** directly connects card protocols to Barrington's theorem: card-based protocols compute exactly NC^1 via S_5 branching programs. This is the ONLY published paper explicitly bridging card protocols and permutation group complexity theory.

Current state:
- Security defined via information-theoretic indistinguishability (orbit analysis under S_N)
- Verification uses SAT/SMT bounded model checking, NOT proof assistants
- **No Coq/Isabelle/Lean formalization exists**
- Permutation group structure is "incidental" — protocols don't exploit subgroup lattice, character theory, or representations

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: Card protocols = permutation group computation | **TRUE** | den Boer 1989 confirmed |
| C2: "Barrington Plays Cards" (STACS 2021) | **TRUE** | Verified at Dagstuhl LIPIcs.STACS.2021.26 |
| C3: S_5 nonsolvability fundamental to Barrington | **TRUE** | Commutator structure in JCSS 1989 |
| C4: No Coq/Isabelle formalization of card security | **TRUE** | Zero results across all proof assistants |

### Bottom Line
**This is PGG's best opportunity.** Card protocols inherently need permutation groups, have a direct Barrington connection, use IT security, and lack formal verification. A Coq formalization of card protocol security using PGG's group-theoretic infrastructure would be genuinely new.

---

## Direction 3: MPC for Branching Programs / NC^1 Functions

### Research Findings

The **flagship theoretical advantage** of permutation-group MPC:

- **Ishai-Kushilevitz (ICALP 2002)**: degree-3 randomizing polynomials give **perfect constant-round IT-secure protocols** for any branching program (hence any NC^1 function)
- **Boyle-Gilboa-Ishai (2016-2017)**: Homomorphic Secret Sharing for branching programs under DDH
- **Private Function Evaluation** (Ishai-Paskin 2007): evaluate branching programs on encrypted data with ciphertext size independent of program width

But practically:
- S_5/Barrington construction produces 31.1 GB for a 16-bit point function (obfuscation)
- No real-world MPC framework uses branching programs
- "Free branching" in GMW (MOTIF, CCS 2021) achieves practical speedups WITHOUT S_5

**Real applications of branching program MPC**: private DFA evaluation (DNA pattern matching), private decision tree evaluation (ML inference), finite automata on encrypted data.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C5: Constant-round IT-secure NC^1 (Ishai-Kushilevitz) | **TRUE** | ICALP 2002 confirmed |
| C6: HSS for branching programs is "practical" | **SUSPICIOUS** | Papers exist but "practical" unsubstantiated — no deployments |
| C7: S_5/Barrington impractical (31.1 GB) | **TRUE** | EPRINT 2014/779 confirmed |
| C8: No general advantage for garbled BPs | **TRUE** | Exponential advantage only for specific functions (automata, OBDDs) |

### Bottom Line
Constant-round IT-secure NC^1 computation is theoretically genuine. But Barrington's 4^d blowup makes it impractical for general functions. The real value is for **specific function classes** (automata, decision trees) where branching programs are naturally compact.

---

## Direction 4: Permutation Groups in Zero-Knowledge Proofs

### Research Findings

Permutations appear in ZK proofs as **combinatorial objects**, not algebraic groups:
- **Graph isomorphism ZK** (Blum 1986): random permutation masking
- **Shuffle proofs** (Neff, Groth): polynomial root invariance under permutation
- **PLONK permutation argument**: subgroup generator arithmetic, grand product check
- **Sudoku ZK**: permutation of digits for commitment hiding

**No ZK proof uses spectral gap, mixing time, or representation theory for security.** Security always reduces to polynomial soundness + simulator construction.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C1: GI-ZK is canonical permutation-based ZK | **TRUE** | Standard textbook example |
| C2: Shuffle proofs use polynomial invariance, not group dynamics | **TRUE** | Grand product argument, not representation theory |
| C3: PLONK uses subgroup generators, not spectral gaps | **TRUE** | Subgroup H = {1, omega, ...} for evaluation |
| C4: No spectral gap in ZK security analysis | **CONTESTED** | Auditor notes spectral gap IS used in adjacent crypto (expander hashing, mix-net topology). Claim is mostly true for ZK specifically but overstated as universal |

### Bottom Line
ZK proofs use permutations combinatorially. PGG's spectral-gap approach is orthogonal to ZK. **Not a natural fit**, though an unexplored connection (spectral gap for shuffle soundness) could be novel research.

---

## Direction 5: Garbled Branching Programs vs Garbled Circuits

### Research Findings

Garbled circuits (Yao 1986) dominate practical 2PC. Branching programs offer advantages only when:
1. The function is naturally a branching program (automata, decision trees, OBDDs) — exponentially smaller representation
2. Private function evaluation is needed (hide program structure)

Permutation group structure has NOT been shown to improve garbling efficiency. The Barrington-to-garbling pipeline exists theoretically but is impractical.

### Audit Verdicts

| Claim | Verdict | Key Reasoning |
|-------|---------|---------------|
| C5: Garbled circuits dominate practical 2PC | **TRUE** | Industry standard (FastGC, half-gates, three-halves) |
| C6: BPs exponentially smaller for automata (Ishai-Paskin) | **TRUE** | Size O(input * BP_length) not O(BP_width) |
| C7: PGM/MST not connected to garbling | **OVERSTATED** | Barrington + Ishai-Kushilevitz DO connect permutation groups to garbled BPs |
| C8: No concrete advantage for garbled perm BPs | **OVERSTATED** | Concrete advantages exist for DFA/automata functions |

### Bottom Line
Garbled circuits win for general computation. Branching programs win for **specific function classes**. Permutation group structure connects to garbling via Barrington but provides no garbling efficiency gain.

---

## Cross-Cutting Analysis

### What Survived Audit (TRUE across directions)

1. **Card-based protocols inherently need permutation groups** — and lack formal verification (Direction 2)
2. **Constant-round IT-secure NC^1** via randomizing polynomials is a genuine theoretical advantage (Direction 3, C5)
3. **"Barrington Plays Cards" (STACS 2021)** bridges card protocols and Barrington's theorem — verified paper
4. **S_5/Barrington is impractical** for general-purpose computation (31.1 GB, 9 hours for 16-bit function)
5. **Garbled circuits dominate practice** — no practical MPC framework uses branching programs
6. **ZK proofs use permutations combinatorially**, not via group theory
7. **Symmetric group representations ARE used in shuffle proofs** (audit correction — not zero group theory in crypto)

### What Failed Audit

1. **"Nobody uses group theory for shuffling"** — overstated; Choi/Bayer 2010 use S_n representations, Attrapadung CCS 2021 uses group actions
2. **"No spectral gap in ZK"** — too strong; spectral gap appears in adjacent crypto (expander hashing, mix-net topology)
3. **"HSS for branching programs is practical"** — unsubstantiated; theoretical feasibility only
4. **"PGM/MST not connected to garbling"** — Barrington explicitly connects permutation groups to branching program garbling

### Suspicious Claims Requiring Further Investigation

1. **Can spectral gap improve shuffle proof soundness?** — Nobody has tried. Potentially novel research direction.
2. **Is the Ishai-Kushilevitz constant-round protocol actually more efficient than GMW for any concrete function?** — No benchmark exists.
3. **Can PGG's fiber-entropy security model apply to card-based protocols?** — Card security uses orbit indistinguishability, which IS related to fiber uniformity.

---

## Recommendation

**The honest answer to "what protocols need permutation groups?":**

### Inherently Need Permutation Group Structure
| Protocol/Application | Why Permutations Are Structural | PGG Relevance |
|---------------------|-------------------------------|---------------|
| **Card-based crypto** | Shuffles ARE group elements; security = orbit analysis | **HIGH** — No Coq formalization exists; Barrington connection explicit |
| **Constant-round IT-secure NC^1** | Barrington requires non-solvable groups (S_5) | **MEDIUM** — Theoretical, impractical |
| **Private automata evaluation** | Branching programs naturally compact | **LOW** — Ishai-Paskin exists; PGG adds no value |

### Use Permutations But Don't Need Group Theory
| Protocol/Application | How Permutations Are Used | PGG Relevance |
|---------------------|--------------------------|---------------|
| Mix-nets / shuffling | Combinatorial reordering | **NONE** |
| PLONK permutation argument | Subgroup evaluation points | **NONE** |
| Graph isomorphism ZK | Random masking | **NONE** |
| Garbled circuits | Circuit-level swaps | **NONE** |

### Actionable Recommendation

**If PGG needs a publication venue and a real problem:**

1. **Best bet: Formalize card-based protocol security in Coq/Rocq.** No one has done this. "Barrington Plays Cards" (STACS 2021) provides the complexity-theoretic bridge. PGG already has:
   - S_5 permutation group formalization
   - Barrington's theorem awareness
   - Information-theoretic security proofs
   - MathComp permutation group infrastructure

   **Gap to fill**: Formalize den Boer's five-card trick, prove IT security via orbit analysis using MathComp's `perm` and `fingroup`, then extend to general card protocols via Barrington.

2. **Longer shot: Benchmark Ishai-Kushilevitz vs GMW for specific NC^1 functions.** If constant-round IT-secure branching program evaluation beats circuit-based MPC for ANY concrete function (comparison, majority, AES S-box lookup), that's publishable. But this requires implementation, not just formalization.

3. **Don't pursue**: shuffling, PLONK, mix-nets, or general garbled circuits. These don't need group theory and PGG adds nothing.
