---
name: recurring-bloat-patterns
description: Habitual redundancies specific to this thesis, observed across concision review runs
metadata:
  type: feedback
---

# Recurring bloat patterns in this thesis

## Pattern 1: Colon-expanded synonym (K12 within-sentence)
**Where seen:** dsdp.tex subsec:dsdp:hops (L632), ssprove.tex sec:ssprove:reduction (L67-68)
**Form:** "X: each is a Y (Z-synonymous-with-X)" — the colon introduces an
expansion that merely renames the predicate with a synonym pair.
**Example:** "are exact: each is a perfect (advantage-zero) equivalence"
**Fix:** drop the leading synonym and colon; keep the fuller technical gloss.

**Why:** The thesis uses "$\approx_0$" notation already established; restating
"exact" before "perfect (advantage-zero)" is pure K12.

## Pattern 2: "without paying anything" after cost-zero statement (K12)
**Where seen:** ssprove.tex L68-69
**Form:** after formally stating a zero contribution, appending an informal
paraphrase "without paying anything."
**Fix:** cut the informal paraphrase; the formal statement suffices.

## Pattern 3: Intentional back-references (preserve, not bloat)
**Where seen:** dsdp subsec:dsdp:hops referencing sec:ssprove:reduction
**Note:** Concrete-instantiation subsections deliberately re-echo the abstract
method with \ref{} back-links. These are NOT K12. Be conservative — do not
flag cross-unit restatements that carry a \ref{} pointer.

**How to apply:** In future runs, flag colon-expanded synonyms and informal
paraphrases after formal zero-cost statements as K12; preserve deliberate
back-reference echoes with \ref{} anchors.

## Pattern 4: Layer-assignment restatement across chapter boundaries (K12 major)
**Where seen:** ssprove.tex lead-in (L3-7) vs sec:ssprove:bridge (L140-144)
**Form:** The chapter lead-in assigns each system to a layer ("\ssprove{} drives
the computational layer, \pismc{} drives the operational layer"). A later bridge
section restates this assignment verbatim as a fresh observation.
**Example:** "Both \pismc{} and \ssprove{} are program artifacts driving the
framework: \ssprove{} drives the computational layer while the \pismc{}
interpreter drives the operational and information-theoretic layer."
**Fix:** Delete the restatement in the bridge section; it adds no new claim.

**Why:** Revision rounds add summary bridging paragraphs that recapitulate the
intro without noticing the intro already said it. This is K12's dominant failure
mode in this thesis.

## Pattern 5: Nominalized padded lead sentence for bridge sections (K12 minor)
**Where seen:** ssprove.tex sec:ssprove:bridge L131-133
**Form:** Bridge sections open with "This thesis uses X to formalize the Y
layer of its hybrid security analysis" — a restatement of the chapter-level
role already given in the chapter intro.
**Fix:** Delete the sentence; let the forward-pointer sentences open the section.

## Pattern 6: Em-dash aside restating a defined term (AGENTS.md + K12)
**Where seen:** ssprove.tex sec:ssprove:reduction L87-89
**Form:** After naming a term (e.g., "shim $P$"), an em-dash aside
re-describes it: "---the shared front-end interposed between the adversary
and the oracles---". The term was fully defined earlier in the same paragraph.
**Fix:** Drop the aside; cite the earlier definition implicitly via the term name.

## Pattern 7: De-em-dash fix turns aside into a standalone sentence (K12/K13)
**Where seen:** ssprove.tex sec:ssprove:reduction L100-101 (second-pass)
**Form:** The style fix split "shim $P$ — the shared front-end..." into two
sentences. The second sentence ("The shim is the shared front-end interposed
between the adversary and the oracles.") is now a pure restatement of the
definition already given three sentences earlier (lines 86-88). The split
moved bloat out of an em-dash aside into a standalone K12 sentence.
**Fix:** Delete the restatement sentence; the term "shim" is already tied
to $P$ and $P$ is already defined.

## Pattern 8: "automated X ... which automates" (K12 doublet via K10)
**Where seen:** ssprove.tex sec:related:simulation L167-168
**Form:** "an automated protocol verifier ... which automates proof search"
— the relative clause verb "automates" restates the adjective "automated."
**Fix:** Drop the relative clause; fold content into the noun phrase:
"an automated protocol verifier that searches proofs for a restricted class."

## Pattern 9: Tail-sentence sub-distribution restatement (K12/K13)
**Where seen:** ssprove.tex sec:ssprove:semantics L49-51
**Form:** After "assigns each linked program a sub-distribution semantics ...
powers game hopping" + "Every typed program therefore denotes a
sub-distribution over its final state and outputs," a closing sentence
"Interpreting programs as sub-distributions lets \ssprove{} reason precisely
about probability" restates both preceding sentences with no new claim.
**Fix:** Delete the closing restatement sentence.

**How to apply:** When a style/semantic fix introduces a sentence split,
check that the new standalone sentence is not a pure echo of an earlier one.
