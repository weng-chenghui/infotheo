---
name: recurring-style-habits
description: Confirmed recurring prose style habits in this thesis across ssprove.tex and dsdp.tex
metadata:
  type: feedback
---

# Recurring thesis-specific style habits (confirmed across runs)

## H1: Negation-framing before the affirmative (A2)
Template: "X is not [adjective]; it [affirmative]."
Example: "The single hop is therefore not atomic; it expands into a three-step micro-chain."
The positive claim always follows the negation in a semicolon pair.
**Why:** Author habit of ruling out a misconception before stating the fact.
**How to apply:** Scan for "not [adj];" or "is not [noun];" constructions; lead with the affirmative instead.

## H2: "is identical" without naming the comparator (A6)
Template: "[X] is identical with [coqin] as the [role]."
Omits "identical to what" -- the structural antecedent (e.g., "same three-step structure") is left implicit.
**Why:** Author assumes the reader tracks the parallel from the preceding hop description.
**How to apply:** Replace "is identical" with "follows the same [structure name]" to make the backward link explicit.

## H3: "shim" used without gloss (A10)
The term "shim" is italicised with \emph{absorbs the shim} in ssprove.tex and reused in dsdp.tex without ever being defined. It is domain-specific jargon for the intermediate translation/reduction package.
**Why:** Author treats it as obvious within the crypto-reduction idiom.
**How to apply:** Gloss as "the intermediate translation package" on first italicised use; subsequent uses are fine.

## H4: Sidenote mid-sentence interruption (A1/A7)
Author places \sidenote{} after a mid-clause noun rather than at the end of the sentence, creating a long parenthetical break between a clause and its consequence.
**Why:** Author attaches the sidenote as close as possible to the named entity it documents.
**How to apply:** Move \sidenote{} to after the completed clause or sentence end; do not split a "so that..." consequence across a sidenote.

## H5: Stress position ending on a bare \ref (A12)
Paragraph-closing sentences end on Section~\ref{...} or Chapter~\ref{...} while the substantive content (e.g., "named translation packages and four-game chain") sits mid-sentence.
**Why:** Author lists forward pointers as trailing qualifiers.
**How to apply:** Split into two active sentences; let the substantive content close each sentence.

## H6: "provide an alternative to X" framing-by-alternative (A2)
Template: "[System] provide(s) an alternative to [EasyCrypt/prior style] while maintaining [property]."
Confirmed in ssprove.tex §related-work. The affirmative contribution (typed packages + state-separation discipline) is subordinated to a contrast with EasyCrypt.
**Why:** Author structures the comparison as "we differ from X" rather than "we do Y."
**How to apply:** Lead with what the framework does ("uses a state-separation discipline"), then add the contrast clause as a subordinate phrase.

## H7: "does not X; instead, it Y" semicolon negation-before-affirmative (A2 + AGENTS.md)
Template: "The [approach] does not [verb]; instead, it [affirmative verb]..."
Confirmed in ssprove.tex line 163-165. Violates both the A2 affirmative-first rule and the AGENTS.md no-semicolon-run-on rule.
**Why:** Author uses the negation to dismiss a common assumption before stating the actual design.
**How to apply:** Delete the negation clause; lead with the affirmative verb directly.
