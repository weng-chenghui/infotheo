---
name: feedback_dumb_working_solution
description: Use dumb but 100% working solutions; add all definitions/lemmas (Admitted) before delegating proofs
type: feedback
---

Use dumb but 100% working solutions over "smart" solutions that might have gaps. Before launching prover agents:
1. Add ALL definitions to the file
2. Add ALL lemmas with Admitted
3. Make sure the file compiles with all Admitted
4. THEN delegate individual proofs to agents

The table in the plan must be followed exactly — no deviations, no "consider" language, no alternative approaches.

**Why:** Smart solutions lead to discovering gaps mid-proof. Dumb solutions may be verbose but they work on first try.

**How to apply:** When writing invariant constructors, include every hypothesis from the exhaustive transition table. When writing lemma signatures, match the constructor hypotheses exactly. Compile to verify type-correctness before launching agents.
