# Monodromy Walk vs Shamir: Where Is the Value?

*Date: 2026-03-14*

---

## The Core Distinction

In conventional MPC (BGW, SPDZ), protocol parameters are **independent choices**: the circuit determines computation, polynomial degree determines threshold, circuit depth determines rounds, simulation determines security. No single algebraic parameter connects them.

In SMC-PGG, **one algebraic choice (G, I) determines four protocol parameters**:

| Parameter | Determined by | How |
|---|---|---|
| Complexity class | G (group variety) | Barrington-Thérien: non-solvable → NC^1, solvable → ACC^0 |
| Round complexity | I (independence graph) | Foata depth of the trace monoid M(Σ, I) |
| Anonymity entropy | G (group size) | Fiber \|L_g\| ≤ \|G\|, IT-secure |
| Threshold gap | G (group size) | \|G\| → genus (Riemann-Hurwitz) → T ≤ k + 2·genus |

Choose G = S_5 with a specific independence graph I, and you know your complexity class, round complexity, anonymity entropy, and threshold gap — all from one algebraic choice.

This is the fundamental value proposition: not replacing Shamir, but enriching it with an algebraic layer where one parameter governs security, computation, rounds, and threshold simultaneously.

---

## Question

Compared to a simple but effective protocol like Shamir, does the monodromy walk idea show any value? There are two parts that feel pretty distant: the security of the monodromy walk (sheet permutation) relies on the group structure; the balance of security and fault-tolerance relies on the AG scheme and is constrained by the group structure via the polynomial curve covering theorem (Riemann-Hurwitz). Hiring Shamir for reconstruction isn't wrong or a lack of novelty, but finding a better AG scheme for reconstruction may increase the value of the work without significantly making the monodromy walk part more valuable compared to Shamir.

---

## Analysis

**There are two essentially independent parts:**

1. **Monodromy walk** (the novel part): Sheet permutations over G, fiber uniformity, RAAG round structure. This is where the algebraic structure lives. Security here means: an adversary seeing partial word execution can't determine which sheet the secret is on. This is IT-secure by fiber counting — has nothing to do with Shamir.

2. **Reconstruction** (the inherited part): Once the walk is done, you have a group element g (the output sheet). To split g into shares for threshold reconstruction, you use Shamir (or an AG code). This is standard and entirely separable from part 1.

**The tradeoff theorem connects them**, but the connection is one-directional: the group G constrains which AG codes are available (via Riemann-Hurwitz). The AG code doesn't feed back into making the monodromy walk better.

**So what does the monodromy walk add over Shamir?**

Shamir splits a *value*. The monodromy walk *computes* on distributed data while maintaining IT security — and the computation structure is algebraically characterized. The closest comparison isn't Shamir alone, it's **Shamir + BGW**:

| | Shamir + BGW | Monodromy walk + Shamir |
|---|---|---|
| What it computes | All of P (gate-by-gate) | NC^1 (word evaluation) |
| How rounds work | Circuit depth (no algebraic knob) | Foata depth (algebraic knob) |
| Security proof structure | Simulation per gate | Fiber uniformity over G |
| Algebraic certificate | None (rich linear algebra, but no complexity classification) | G-variety → complexity class |

**Clarification: BGW and SPDZ are algebraic protocols.** BGW uses polynomial evaluation, Lagrange interpolation, and degree reduction over finite fields. SPDZ uses additive sharing, Beaver triples, and MAC-based verification over rings. Both are deeply algebraic in their *mechanics*. What they lack is not algebra but the dual role described above: BGW's algebraic parameters (polynomial degree, field size) characterize security thresholds, not computational power. The computational universality (all of P) comes from the circuit model, not from an algebraic classification. In SMC-PGG, the same algebraic parameter (the group G) governs both.

The value isn't in replacing Shamir — it's in the **computation layer above Shamir**. BGW computes gate-by-gate with rich linear algebra but no global complexity-theoretic structure. The monodromy walk computes word-by-word with the group as a global invariant that classifies computational power. Whether that algebraic invariant is *worth* the NC^1 restriction is a judgment call, but it's a genuinely different computation model, not a reinvention of sharing.

**The instinct is correct**: upgrading the AG code for reconstruction is a separate axis of improvement that doesn't amplify the monodromy walk's value. The walk stands or falls on its own merits as a computation primitive — and those merits are the algebraic characterization (Barrington-Thérien, Foata depth, fiber security), not the sharing scheme underneath.

---

## What Can BGW Compute That SMC-PGG Cannot?

By P and NC^1, what does Shamir + BGW reach that the monodromy walk cannot?

The concrete separation (assuming NC^1 ≠ P, which is widely believed but unproven):

### P-complete — definitely out of reach for SMC-PGG

| Problem | Why it matters for MPC |
|---|---|
| Iterated matrix multiplication | Multiplying A₁ · A₂ · ... · Aₙ where n is part of the input (see caveat below) |
| Circuit Value Problem | Evaluating an arbitrary circuit — meta-computation |
| Linear programming | Private optimization (auctions, resource allocation) |
| Maximum flow | Private network routing, matching markets |
| Horn-SAT | Private constraint solving |
| Context-free parsing | Private analysis of structured data (e.g., genomic sequences with CFG structure) |

### NL-complete — out of reach if L ≠ NL

| Problem | Why it matters for MPC |
|---|---|
| Directed graph reachability | Private social network queries ("is A connected to B?") |
| 2-SAT | Private constraint satisfaction |

### What NC^1 *does* cover (SMC-PGG's territory)

Comparisons, addition, sorting, voting/majority, parity, pattern matching (regular languages), Boolean formula evaluation, integer multiplication (TC^0 ⊆ NC^1).

### The practical dividing line

If the computation involves a fixed-depth pipeline (compare, add, sort, match, vote), you're in NC^1 and SMC-PGG works. If it involves *iterating* where the iteration count is part of the input — multiplying a variable-length chain of matrices, traversing a graph of variable size, solving an optimization with variable constraints — you need circuit depth that grows with the input, and that's P-territory where only BGW/GMW/SPDZ can go.

---

## Correction: Fixed-Architecture Neural Network Inference Is in NC^1

The claim "ML inference is outside NC^1" is misleading.

**Key insight:** "Iterated matrix multiplication is P-complete" means multiplying A₁ · A₂ · ... · Aₙ where **n is part of the input** (n grows with problem size). A fixed-architecture neural network never has this — the number of layers is a constant baked into the architecture.

A depth-2 fully connected network computes:

```
y = f(W₂ · f(W₁ · x + b₁) + b₂)
```

This is constant depth — two matrix-vector multiplies, two activations. Constant depth → TC^0 ⊆ NC^1.

This applies to **any fixed-architecture network**, not just shallow FNNs. A ResNet-50 has 50 layers, a GPT has 96 transformer blocks — but "50" and "96" are *constants*, not functions of input size n. In complexity theory, constant depth = TC^0 ⊆ NC^1, regardless of how large that constant is.

### Corrected table

| Task | Complexity | NC^1? |
|---|---|---|
| Fixed-architecture inference (any CNN, transformer, FNN) | TC^0 | Yes |
| Variable-depth RNN (input length = depth) | P-complete | No |
| Neural architecture search (architecture is input) | P-complete | No |
| Training (gradient descent, iteration count grows) | P-complete | No |

### Where the real barrier is

The practical barrier isn't complexity class — it's **circuit size**. A 50-layer ResNet is in NC^1, but its Boolean circuit has billions of gates. The Barrington encoding produces n^{2c} permutation factors where n is the circuit size — polynomial, but impractically enormous.

So "mainstream" fixed-architecture ML inference (including deep CNNs and transformers) is within SMC-PGG's theoretical reach. The limitation is efficiency, not computability. The functions that genuinely require P and escape NC^1 are those where **the depth scales with the input**: variable-length RNNs, graph traversal on variable-size graphs, iterative optimization with variable convergence.

---

## A More Natural Academic Direction: Algebraic Structure Upon Shamir

The current framing is top-down: "I found covering spaces, here's an MPC protocol, and it uses Shamir at the bottom." A more natural academic direction is bottom-up — start from Shamir and ask what algebraic structure enriches it:

1. **Start from Shamir.** Everyone knows it. IT-secure, simple, effective.

2. **Ask: what algebraic structure can we impose on top?** Shamir splits a field element — what if the secret lives in a *group* and the shares are related by group actions?

3. **Discover monodromy.** Group actions on shares = permutations of sheets = monodromy walk. The group structure is an *enrichment* of Shamir, not a replacement.

4. **Connect to computation.** Group actions → branching programs → Barrington-Thérien. The enrichment has a precise computational consequence: the group variety determines what you can compute (NC^1 for non-solvable, ACC^0 for solvable).

5. **Discover the RAAG knob.** Commutativity relations among generators → independence graph → Foata depth → round complexity as algebraic parameter.

6. **Discover fiber security.** The preimage of the evaluation morphism gives IT-secure anonymity sets, computable from the Cayley graph.

7. **Close the loop.** The covering space structure (which emerged from the group enrichment) constrains reconstruction parameters via Riemann-Hurwitz — connecting back to Shamir/AG codes.

This way, the AG/Shamir connection isn't an embarrassment — it's the **starting point**. And the contribution is clear: "We enriched Shamir's linear-algebraic sharing with group-theoretic computation structure, and the enrichment has algebraically characterized consequences for computability, round complexity, and security."
