# Email Draft to Imai-san (Proof Ninja)

**Date:** 2026-03-23
**To:** Yoshihiro Imai (Proof Ninja, proof-ninja.co.jp)
**Subject:** Semi-Automatic AI Formalization: A Case Study and Questions

---

Dear Imai-san,

I hope you have been well. I have been continuing my work on cryptographic protocol verification with Infotheo/MathComp, and recently had an interesting experience with AI-assisted formalization that I thought you might find relevant to Proof Ninja's direction. I would love to hear your thoughts.

## What I did

I recently prototyped a new cryptographic protocol entirely inside Rocq, using AI agents (Claude, Anthropic) as a semi-automatic collaborator. The starting point was just a topological intuition: covering spaces are surjections, so they might hide secrets. No concrete protocol existed yet.

Over 19 days of spare time (roughly 2 hours/day, very discontinuous due to child care), the AI and I together produced 58 Rocq files, about 21,800 lines of code, with 0 Admitted proofs and 11 well-justified axioms. The codebase spans protocol correctness, collusion security bounds, Cartier-Foata trace counting, fiber entropy analysis, algebraic rigidity classification across five group instances, and AG code infrastructure. I directed the mathematical architecture and reviewed proofs, while learning new math knowledge that I never studied before; the AI handled scaffolding, batch proving of routine lemmas, systematic renaming, and adversarial auditing of claims.

## Why it matters

I should note that this is quite different from projects like AlphaProof or other auto-reasoning research, which aim to replace human mathematicians with fully autonomous solvers. What I experienced is closer to a working partnership: the human sets the direction, designs the abstractions, and judges correctness, while the AI handles the labor-intensive parts like writing boilerplate, searching for lemma names, and trying proof strategies in bulk. Neither side could have done this alone in the same timeframe.

This inverts the traditional flow where researchers first invent a protocol informally, then implement, and only much later (if ever) verify formally. Here, formalization came first and served as the prototyping medium. The formal proofs caught a fatal flaw early (abelian groups collapse to full secret recovery) and identified two unsatisfiable axiom formulations that required same-day pivots.

Even though AI-assisted formalization is far from mature, I think this experience suggests it is already worth trying at the beginning of a research pipeline, not just the end, especially for ideas that may have fundamental limitations and benefit from early machine-checked feedback. Of course, expert review remains indispensable: Affeldt-san's feedback on duplicated proof patterns led to useful refactoring, and the AI caused two machine crashes from runaway memory usage, reinforcing that human oversight is essential at every step.

More broadly, I think this workflow could accelerate the formalization of well-known mathematical results, freeing researchers to focus on creative work while routine verification proceeds semi-automatically.

## Questions

I would appreciate your perspective on the following:

1. **Business acceptability.** If Proof Ninja were to transparently use AI agents for generating formalization proofs under contract (with human review at every step and full disclosure), would this be acceptable to clients and the research community? Do you see this as an opportunity or a risk?

2. **Intellectual property.** For semi-automatic work products where AI generates proof scripts and a human directs and revises them, how might a company claim ownership? Is this analogous to software developed with AI coding assistants, or does formal verification raise different considerations?

3. **Public knowledge base.** If a company produced a large body of semi-automatically generated formalizations of standard mathematical results and wanted to open it to researchers, what ownership model would make sense? Public domain, open-source (like MathComp), or something else? I am curious about the case where no contract exists but the company wants to build reusable formalization infrastructure for the community.

4. **Demo.** Would you be interested in a live demonstration of this workflow? I would be happy to walk through a session showing how the human-AI interaction works in practice, including proving, auditing, and pivot moments.

I have attached a theorem audit summary and methodology timeline below for reference. The full details are available if you are interested.

### Theorem Audit Summary

| Category | Rating | Key Result |
|---|---|---|
| Protocol Correctness | Complete | Bijectivity, reconstruction |
| Security Bounds | Mostly Complete | Collusion bound via Schreier spectral gaps |
| Abelian Collapse | Complete | Impossibility result (full recovery) |
| Cartier-Foata | Mostly Complete | Foata NF, search_space <= traces <= Tg^L |
| Information Theory | Mostly Complete | Fiber entropy, Pinsker bridge |
| Algebraic Rigidity | Mostly Complete | Genus dichotomy, 5 instances |
| Coding Theory | Mostly Complete | AG Singleton bound, RS privacy |
| Grover Mitigation | Complete | Ball size formula, security-storage match |
| Permutation Uniformity | Complete | Conditional uniformity from (N-1)! counting |

### Timeline

- **19 days, ~2h/day** -> 73 commits, 58 files, 21.8K LOC, 0 Admitted
- **AI:** scaffolding, batch proving, renaming, adversarial audit
- **Human:** architecture, axiom design, expert review, all pivots

Thank you for reading. I look forward to hearing your thoughts.

Best regards,
Cheng-Hui Weng
