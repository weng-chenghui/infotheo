---
name: feedback_accept_complexity
description: Accept complexity in plans if it eliminates gaps; don't cut corners with "simpler" approaches
type: feedback
---

Do not take "simpler" or "quicker" approaches that leave gaps. Accept the full complexity needed to solve the problem completely.

**Why:** Previous attempts to simplify the dsdp_inv invariant led to repeated discovery of gaps that required re-enrichment. Each round of simplify→discover gap→fix wastes time.

**How to apply:** When designing invariants or proof structures, enumerate ALL transitions exhaustively, verify ALL hypotheses of ALL target constructors, and include ALL needed tracking from the start. If an invariant needs 10 hypotheses per constructor to be gap-free, use 10 hypotheses.
