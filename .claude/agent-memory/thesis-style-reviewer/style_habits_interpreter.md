---
name: style-habits-interpreter
description: Confirmed recurring style habits in interpreter.tex (and likely thesis-wide)
metadata:
  type: feedback
---

## Confirmed recurring habits (catch on every future run)

1. **Negation-framing section openers (A2).**
   Template: "[Component] says/does X but does not Y. To [do Y], we..."
   Seen at line 175: "The relational semantics says which reductions are valid
   but does not compute them."
   Fix template: lead with the affirmative function being introduced, demote
   the limitation to a trailing clause.

2. **Throat-clearing roadmap leads (A13).**
   Template: "This section X, Y, and Z."
   Seen at lines 35-38: "This section fixes...it states...presents...and explains."
   Fix: cut the roadmap sentence and open directly on the content.

3. **Indefinite "one" as abstract subject (A4).**
   Template: "one [verb]s X" instead of "we [verb] X" or naming the agent.
   Seen at line 222: "one pushes the trace map forward."
   Fix: rewrite with "we" or a concrete subject.

4. **"Rather than" contrast framing (A2).**
   Template: "[Subject] does X rather than [what the text presents]."
   Seen at line 251-252: "...rather than running the deterministic trace."
   Also: line 192: "organised around the reduction relation rather than the
   six process constructors."
   Fix: reorder so the affirmative method is the main clause; relegate the
   contrast to a subordinate or trailing clause.

5. **"Instead" contrast pivot (A2-adjacent).**
   Template: "[X]. [Y] is instead [the real thing]."
   Seen at line 167: "Determinism is instead a property of the interpreter."
   Fix: affirmative lead: "The interpreter, not the relation, enforces
   determinism."

6. **Long interrupting absolutes in facade/record paragraphs (A7).**
   Template: "Those X, together with Y and Z, are the fields of one record."
   Or: "The instance fills the record, its field fixed to V and its count N, and reads off..."
   Confirmed in derived-overview.tex lines 47-48 and 53-56.
   Fix: move the interrupting phrase right of the verb or restructure as "with" prepositional.

7. **Cleft inversion to front a topic (A8).**
   Template: "What stays [X] is [noun]..." instead of "[Noun] stays [X]..."
   Confirmed in derived-overview.tex line 38.
   Fix: promote the real noun to subject.

8. **Colon-before-list in roadmap sentences (AGENTS.md).**
   Template: "Chapter X develops the front end: item, item, and item."
   Confirmed in derived-overview.tex lines 113-117.
   Fix: replace colon with "covering" or integrate as "by doing X, Y, and Z."

**Why:** The author habitually motivates components by explaining what they
lack or contrast against, rather than stating their function directly.
**How to apply:** On any new run over this thesis, scan first for "but does
not", "rather than", "instead", "is not", "unlike" at sentence or clause
openings. Also scan facade/record paragraphs for long nominal interruptions
between subject and verb (A7), cleft openers (A8), and colon-before-list
in roadmap sentences (AGENTS.md).
