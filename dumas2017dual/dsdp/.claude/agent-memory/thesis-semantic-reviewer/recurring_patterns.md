---
name: recurring-patterns
description: Semantic anti-patterns confirmed across multiple thesis review runs
metadata:
  type: project
---

## Pattern A: reduction-section closing paragraph duplicates bridge-section opening

Confirmed in ch:ssprove (sec:ssprove:reduction ll.95-99 vs sec:ssprove:bridge ll.103-106):
a closing paragraph that forward-points to the same chapter as the next section's
opening, pre-empting the next section's topic sentence. Flag immediately whenever a
section's closing paragraph and the next section's opening paragraph share a
forward \ref to the same chapter.

**Why:** The thesis has an abstract-method chapter (ssprove) followed by
instantiation chapters (gameswap, dsdp); each abstract section tends to close with
"this is instantiated in ch:X" while ch:X's corresponding section opens with the
same pointer. Only one of the two should carry that pointer.

**How to apply:** On any section-boundary review, compare the last paragraph of
section N with the first paragraph of section N+1; if both \ref the same
destination chapter for the same concept, flag as major P1/S2.

## Pattern B: single-paragraph subsection spanning two sub-arguments

Confirmed in dsdp ch19 (subsec:dsdp:hops): a subsection that develops hop 1 and
hop 2 in one unbroken paragraph, with the second-hop sentence beginning "The second
hop ... is identical with X as the shim" — a topic shift with no paragraph break
and an ambiguous "is identical with" phrasing that conflates structural identity
with named-package identity.

**Why:** The thesis's game-hopping subsections naturally have two symmetric hops;
authors tend to treat hop 2 as a one-liner appended to hop 1's paragraph rather
than opening a new paragraph. The "identical with X as the shim" phrasing is
idiomatic but logically ambiguous (identical to what? identical with X meaning X is
the thing it's identical to, or X is the role?).

**How to apply:** In any hops/reduction subsection, check for a second-hop sentence
of the form "is identical with/to [package]" without a paragraph break; flag as
major P1/N1 and recommend a break + "follows the same structure, with X as the
shim."

## Pattern D: advantage-section closing sentence pre-empts reduction-section opening

Confirmed in ch:ssprove (sec:ssprove:advantage l.49-52 vs sec:ssprove:reduction l.56):
the final sentence of the advantage section introduces game hopping as a method, which
is then re-introduced as the opening topic of the immediately following reduction
section. This is a variant of Pattern A operating at the intra-chapter sentence level
rather than the section-boundary paragraph level.

**Why:** Authors treat advantage and game hopping as a natural conceptual pair and
introduce both in the same section, but game hopping as a structural technique requires
its own full section; the advance mention displaces the reduction section's topic
sentence and makes the section boundary feel redundant.

**How to apply:** When a section titled "Advantage and ..." ends with a sentence about
game hopping or reduction methodology, and the very next section is titled "The
Reduction Method ...", flag the closing sentence as P1/S1 and remove it from the prior
section.

## Pattern C: micro-chain concept introduced in subordinate position

Confirmed in dsdp subsec:dsdp:hops: the three-step micro-chain concept (the
organising principle of the subsection) is introduced as the conclusion of a
subordinate clause ("it expands into a three-step micro-chain") rather than as the
opening topic sentence or an explicit forecast sentence.

**Why:** Authors introduce the concept in passing after explaining the linking
setup, but the reader needs the structural forecast first to interpret the display
math that follows.

**How to apply:** When a subsection's dominant organizing concept appears for the
first time as the object of "expands into" or "decomposes into" buried in a
mid-paragraph sentence, flag as minor S2 and recommend moving the forecast to the
paragraph's second sentence.
