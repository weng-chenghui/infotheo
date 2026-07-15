---
name: feedback-dsdp-grounding-habits
description: ch:dsdp (dsdp.tex) grounding habits confirmed in subsec:dsdp:hops review
metadata:
  type: feedback
---

ch:dsdp coins "micro-chain" (a three-step sub-chain within the outer game chain)
and "translation package" (a front-end package routing a swapped ciphertext slot
through an encryption oracle) without definitions. Both terms are absent from the
term map.

The charlie translation package receives a pen-and-paper shorthand `\mathsf{charlie}`
via an explicit binding sentence. The bob translation package (`game_via_oracle_bob`)
does not -- its raw `\coqin{}` identifier appears in body prose directly. This
inconsistency triggers G1.

**Why:** The author introduced the charlie shorthand for display-math legibility but
did not apply the same treatment to the bob package, leaving a raw code identifier
in body prose.

**How to apply:** On any future dsdp.tex review, check that every package used in
an analogous role to charlie has either a pen-and-paper shorthand or is relegated
to a sidenote.
