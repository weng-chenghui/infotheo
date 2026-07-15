---
name: feedback_do_it_yourself
description: User wants main conversation to prove lemmas directly, not delegate to rocq-expert-prover. Use Show for goals, apply/exact with space.
type: feedback
---

When the user says "you do the job" for Rocq proofs, do the proving directly in the main conversation instead of launching rocq-expert-prover. Still follow the standard practices:
- Use `Show` to inspect goals, never guess
- Use `apply ` and `exact ` (with space) instead of `apply:` and `exact:` for better error messages
- Use `goal.sh` workflow for testing when applicable

**Why:** User wants to stay in the loop and see the proof process directly, especially for scaffolding work where the lemmas are already outlined.

**How to apply:** Only delegate to rocq-expert-prover when the user explicitly asks for it, or for truly complex standalone proofs that benefit from isolated context.
