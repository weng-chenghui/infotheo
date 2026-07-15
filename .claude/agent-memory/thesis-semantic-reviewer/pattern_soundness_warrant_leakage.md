---
name: pattern-soundness-warrant-leakage
description: interpreter.tex §3 — soundness-corollary warrant habitually placed at end of completeness paragraph instead of soundness paragraph
metadata:
  type: project
---

In `chapters/interpreter.tex` §3 (The Executable Interpreter and Its Correctness),
the bridging warrant sentence that invokes soundness ("Soundness guarantees that
every trace...eligible for privacy analysis") was placed at the end of the
completeness paragraph. This violates P1 paragraph unity. The pattern is:
soundness claim -> proof decomposition -> completeness claim -> soundness corollary.
The corollary belongs either at the end of the soundness paragraph or in a
dedicated two-sentence bridge paragraph after both results are stated.

**Why:** The two results were merged into a tight section and the bridging sentence
was appended to whichever paragraph was edited last.

**How to apply:** In any future section that states sound + complete results
consecutively, verify that the bridging/corollary sentence is attributed to the
correct result and placed in its own paragraph or the soundness paragraph.
