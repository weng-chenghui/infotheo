# Plan: AIPV 2026 Extended Abstract

## Context

The user has been formalizing a covering-space-based MPC protocol (SMC-PGG) in Rocq/MathComp, with Claude doing all the formalization work under human direction. This is a concrete instance of the "inverting the formalization workflow" method from their blog post. The AIPV 2026 workshop (AI for Proof and Verification, Tokyo, May 18–19) accepts 1–2 page extended abstracts. **Deadline: March 15 (tomorrow, AoE).**

Relevant AIPV topics:
- **AI for Theorem Proving**: guiding interactive proof search in dependent type theories
- **Interdisciplinary Approaches**: bridging empirical LLM performance with formal rigor

## The Core Insight (from user's clarification)

The traditional workflow is: learn math domains → design protocol in informal math → formalize as final step.

The **inverted workflow** is: start with a hypothesis from ongoing work ("any surjective relation can hide a secret in MPC — if there's a trapdoor for legitimate parties"; this is a separate generalization effort) → notice covering spaces match this pattern → use LLM + type checker to formalize as **fast prototyping** → learn the math domains *through* the formalization process, iteration after iteration → if it keeps proving, you have solid ground while prototyping.

Key nuances:
- The human does NOT provide mathematical definitions or proof strategies — the LLM contributes math knowledge the human never knew
- The human provides **decision-making** and **judgment** while learning domains they never formally studied
- The human knows the ideas "should make sense" but the "how" is revealed by LLM + type checker together
- Formalization is the prototyping medium, not the final polish step

## Narrative Angle

**Title idea**: "Inverting the Formalization Workflow: Prototyping an MPC Protocol in Rocq with an LLM"

**Core claim**: Formalization can be the *first* step rather than the last. A domain expert starts with a simple cryptographic idea, directs an LLM to formalize it in Rocq/MathComp, and learns the required mathematics through the formalization process itself. The type checker ensures each iteration stands on solid ground. This inverts the traditional order: instead of learn → design → formalize, the workflow is idea → formalize → learn.

**Evidence**: SMC-PGG — starting from a hypothesis about surjective relations in MPC (separate ongoing work) → covering spaces → monodromy groups → RAAG trace monoids → Cartier-Foata → AG codes → collusion bounds. 42 files, 0 Admitted, five mathematical domains the human learned *through* formalization rather than before it.

**Selling points**:
1. **Formalization as prototyping** — each iteration either proves the idea works or reveals exactly where it breaks
2. **Inverse learning** — the human learned group theory, combinatorics, AG geometry, coding theory, and information theory through the formalization, not before it
3. **Cross-domain breadth** from a single human+LLM pair — the LLM's wide knowledge becomes an asset when the type checker filters its depth errors
4. **Completeness** — 0 Admitted, deliberate axiomatization boundaries (not gaps)

## Structure (1.5–2 pages, /rewrite style)

### 1. Opening (1 paragraph)
The timeline problem: formalization comes last, after years of domain study and informal design. What if formalization comes first, as the prototyping medium? An LLM can draft formal models from natural-language direction. The type checker verdicts each draft. The human learns the domain from the structured output of each attempt.

### 2. The Inverted Workflow (2–3 paragraphs)
The starting point was a hypothesis from separate ongoing work on generalizing MPC: any surjective relation can serve as a secret-sharing mechanism if legitimate parties have a trapdoor. Covering spaces in topology match this pattern — the fiber over a basepoint is the secret, the monodromy action is the computation, and the covering map is the reconstruction. Rather than studying the required mathematics first, the author used formalization to test whether this connection holds.

From this seed, formalization becomes exploration. The human does not need to master group theory, algebraic geometry, or information theory before starting. The LLM contributes mathematical knowledge — definitions, lemma statements, proof strategies — that the human has never studied. The type checker ensures each step is logically sound. When a proof attempt fails, the failure is informative: it reveals exactly which assumptions are missing or which mathematical structure is needed. The human learns the domain from these failures and successes, iteration after iteration.

Three roles emerge. The human provides judgment: which direction to explore, which abstractions to introduce, where to draw axiomatization boundaries. The LLM provides mathematical breadth: connecting group theory to combinatorics to AG geometry within a single proof development. The type checker provides certainty: if it compiles, the logical structure holds.

### 3. Case Study: SMC-PGG (2–3 paragraphs)
The seed idea grew into a four-layer formalization:

**Protocol**: A monodromy representation ρ : G → S_N maps group elements to permutations on N sheets. The protocol hides a secret in the fiber structure of a covering space. Formalized as an HB mixin (MonodromyReprType) with session-typed programs.

**Search space**: The adversary's search space is characterized by Right-Angled Artin Group (RAAG) trace equivalence. The Cartier-Foata theorem — proved axiom-free — gives exact trace counts via clique polynomial recurrence. This was a domain the human learned entirely through formalization.

**Reconstruction**: Abstract threshold scheme interface, instantiated by Massey's secret sharing from linear codes. Hyperelliptic AG codes provide parametric (k,T)-thresholds via polynomial resultant, avoiding Riemann-Roch. An algebraic rigidity framework (`AlgebraicRigidity` record) shows one algebraic choice determines four protocol parameters, with a concrete star-graph instance and PGL(2,F_q) bound.

**Security**: Collusion bound (information distance ≤ ε + 2(T−1)/N), Grover mitigation via ball-size enumeration, and the abelian collapse theorem showing non-abelian groups are necessary.

The formalization spans group theory, combinatorics, algebraic geometry, coding theory, and information theory. The human entered knowing cryptographic protocol design. The other four domains were learned through the formalization process.

### 4. Observations (1–2 paragraphs)
The workflow worked because of a tight feedback loop: the LLM drafts, the type checker compiles or rejects within minutes, the human reads the result and steers the next iteration. When it compiled, the human gained confidence the mathematical structure was sound. When it failed, the error messages — especially dependent-type mismatches — pointed precisely to where the reasoning broke down.

Limits remain. Architectural decisions (Record vs Section, file layout, axiomatization boundaries) required human judgment the LLM could not provide. Dependent-type unification failures (e.g., rewriting under `'Z_(p*q)`) required human-level insight to diagnose. The LLM needed explicit safety constraints to avoid memory-blowing tactics. But the balance was productive: the human spent time on judgment, not on tactic syntax.

### 5. Broader Implication + Closing (1–2 paragraphs)
This workflow makes crafting mathematical applications more like software engineering. Software developers do not master every library and system before starting a project — they learn what they need, project by project, trusting that APIs and type systems will catch misuse. The LLM plays an analogous role for mathematics: it helps the author discover which ingredients are available in the wide marketplace of mathematical domains. If a connection is logically sound — prototyped and confirmed by the type checker — it can be extended until the application emerges. The iteration cycle for mathematical applications shortens, and the range of applicable domains widens, without sacrificing rigor.

Formalization need not be the final step. When an LLM serves as proof engineer and the type checker serves as quality gate, formalization becomes the first step — a prototyping medium that simultaneously validates ideas and teaches the domain. The traditional order (learn → design → formalize) can be inverted (idea → formalize → learn) because the prover accepts no shortcuts.

## Writing Style
- Follow /rewrite rules: one deduction per sentence, goal before calculation, clear connectives
- Match user's blog voice: conversational yet rigorous, narrative-driven, concrete before abstract
- No bullet lists in the paper body (rule 9) — narrative paragraphs only
- LaTeX, EasyChair template optional

## Files to Create
- `/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex`

## Key Data Points (use selectively, don't lead with numbers)
- 42 Rocq files, 0 Admitted lemmas
- 5 mathematical domains learned through (not before) formalization
- Key theorems: Cartier-Foata (axiom-free), collusion bound, hyperelliptic Goppa bound
- Deliberate axioms: Goppa weight bound (Riemann-Roch), AG privacy surjection
- Starting point: "surjective relations hide secrets" → covering spaces

## Verification
- Compile LaTeX to PDF
- Check page count (target: 1.5–2 pages)
- Proofread for /rewrite style compliance
