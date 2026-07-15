# Email Draft to Imai-san (Proof Ninja) -- Long Version

**Date:** 2026-03-23
**To:** Yoshihiro Imai (Proof Ninja, proof-ninja.co.jp)
**Subject:** Semi-Automatic Formalization Workflow: A Case Study and Questions

---

Dear Imai-san,

I hope this message finds you well. My name is Cheng-Hui Weng, and I work on formal verification of cryptographic protocols using the Infotheo library built on MathComp/Rocq, together with Reynald Affeldt at AIST. I have been following Proof Ninja's work with great interest, particularly your formalization consulting services and your contributions to the Coq ecosystem such as MerkleTree and CoqPad.

I am writing to share an experience that I believe is relevant to your business, and to ask a few questions about how AI-assisted formalization might fit into the kind of work Proof Ninja does.

## The Experiment

Over the past month, I carried out an experiment in what I call "formalization-first prototyping." The starting point was not a finished protocol or a published paper, but just a basic topological idea: covering spaces are surjections (epimorphisms), so they might be useful for hiding secrets. Beyond this intuition, no concrete protocol existed.

Using Claude (Anthropic's AI) as a collaborative agent, I went through the full cycle of discussing the idea, exploring whether it could become a rigorous cryptographic protocol, auditing whether the security claims hold up, and formalizing the mathematics along the way. The AI agents handled scaffolding of definitions and type classes, batch-proving of routine lemmas, systematic renaming across files, and adversarial review of paper claims. I directed the mathematical architecture, chose the abstractions, and reviewed every proof.

The result after 19 working days (roughly 2 hours per day of discontinuous spare time, since I have a young child) is a Rocq codebase of 58 files, about 21,800 lines, with zero Admitted proofs and only 11 well-justified axioms. The codebase covers protocol correctness, collusion security bounds via Schreier spectral gaps, a Cartier-Foata trace counting framework, fiber entropy analysis with Pinsker bridges, algebraic rigidity classification across five group instances, and coding theory infrastructure including AG codes and Reed-Solomon privacy. An independent audit rated the mathematical depth as "substantial" across all nine theorem categories. I have attached the methodology timeline and theorem audit table below for reference.

## Why This Matters

This workflow inverts the traditional order. Normally, researchers invent a protocol, describe it informally in a paper, implement it in a mainstream programming language, and only then (if ever) verify its security and correctness formally, a process that typically takes months to years. In my experiment, the formalization came first, and it served as the prototyping medium itself. The formal proofs caught a fatal flaw early (abelian groups collapse to full secret recovery), identified two unsatisfiable axiom formulations that required same-day pivots, and an adversarial audit revealed that the protocol sits in an isolated space with no natural connection to established cryptographic primitives.

To me, this demonstrates that AI-assisted formalization is mature enough to be placed at the beginning of the research pipeline, not just the end. Even for an idea that may turn out to have fundamental limitations, having a machine-checked prototype with zero Admitted proofs gives researchers a solid logical foundation to reason about what works and what does not.

Of course, expert review remains critical. Affeldt-san pointed out that some of my proof lines looked literally identical to patterns already in the Infotheo library, which led to useful refactoring. The AI agents also caused two machine crashes (one from concurrent compilation consuming 55 GB of RAM, another from an exponential rewrite consuming 68 GB), which taught me that safety guardrails for AI-driven compilation are essential. This is a semi-automatic workflow, not a fully automatic one, and human judgment is indispensable at every stage.

That said, I believe this kind of workflow could significantly benefit the formalization of well-known mathematical facts and theorems, freeing researchers to focus on the novel and creative parts of their work while the routine verification proceeds more quickly and reliably.

## Questions for You

With this context in mind, I would appreciate hearing your perspective on the following:

**1. Business acceptability.** If a company like Proof Ninja were to clearly and transparently use AI agents to generate formalization proofs as part of a contract with researchers, with human review and revision at every step, would this be acceptable to your clients and to the research community? Some conferences now have policies that allow AI-assisted work as long as the contribution is fully disclosed. Do you see this as an opportunity or a risk for a formalization business?

**2. Intellectual property.** For semi-automatic work products where the AI generates proof scripts and a human architect directs and revises them, how might a company like Proof Ninja claim ownership of the results? Is this analogous to software developed with AI coding assistants, or does formal verification raise different IP considerations?

**3. Public domain and knowledge sharing.** If a company were to take the initiative to produce a large body of semi-automatically generated formalizations of standard mathematical results, and wanted to open this as a knowledge base for researchers, what ownership model would make sense? Would it be better for such results to be contributed to the public domain so that academic researchers can build upon them freely? Or would a licensing model (perhaps similar to MathComp's open-source approach) be more sustainable? I am particularly curious about the case where no specific contract exists but the company wants to create reusable building blocks for the community.

**4. Live demo.** Finally, would you be interested in seeing a demonstration of how this semi-automatic workflow operates in practice? I would be happy to walk through a session showing the interaction between the human architect and the AI agents, including the proving, auditing, and pivot moments. I think it would give a concrete picture of what is currently possible and where the limitations are.

## Attachments

Below I include a summary of the formalization methodology (the full timeline table is available separately) and a theorem completeness audit conducted by an independent mathematical review.

### Theorem Completeness Audit

| Category | Rating | Key Result | Axiom Dependency |
|---|---|---|---|
| Protocol Correctness | Complete | Bijectivity, distinctness, sum-mod reconstruction | None |
| Security Bounds | Mostly Complete | Collusion bound: d(adv,U) <= eps + 2(T-1)/N | 1 axiom (Schreier walk, Diaconis 1988) |
| Abelian Collapse | Complete | One endpoint determines permutation (impossibility) | None |
| Cartier-Foata | Mostly Complete | Foata NF soundness, search_space <= traces <= Tg^L | None (computable NF variant) |
| Information Theory | Mostly Complete | Fiber entropy formula, Pinsker bridge to var_dist | Pinsker from Infotheo library |
| Algebraic Rigidity | Mostly Complete | Genus-0/genus>0 dichotomy, 5 concrete instances | 1 axiom (Hurwitz 1893) |
| Coding Theory | Mostly Complete | AG Singleton bound, RS privacy, PGL cardinality | Goppa weight for non-hyperelliptic |
| Grover Mitigation | Complete | Ball size closed form, security-storage Theta(kappa^L) | None |
| Permutation Uniformity | Complete | card(prescribed(s,v)) = (N-1)!, conditional uniformity | None |

**Overall assessment:** "Substantial formalization of a novel cryptographic construction at the intersection of four mathematical domains (permutation groups, algebraic geometry, information theory, combinatorics on words). Axiom discipline is strong: 11 axioms, all well-justified, none hiding structural gaps."

### Formalization Timeline Summary

- **Duration:** 19 days (Mar 4-22, 2026), roughly 2 hours/day
- **Output:** 73 commits, 58 Rocq files, 21,800 LOC, 0 Admitted
- **AI role:** Scaffolding, batch proving (rocq-expert-prover agents), systematic renaming, adversarial audit (explore-audit with 6 agents), iterative paper review
- **Human role:** Mathematical architecture, abstraction design, axiom formulation, expert review, direction of all pivots
- **Key incidents:** 2 machine crashes from AI actions (concurrent builds, exponential rewrite), 2 unsatisfiable axiom discoveries requiring same-day pivots, 1 existential framing crisis resolved by rebrand

Thank you for taking the time to read this. I look forward to hearing your thoughts, and please feel free to share this with anyone at Proof Ninja or in your network who might find it relevant.

Best regards,
Cheng-Hui Weng
