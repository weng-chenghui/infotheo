---
name: bloat-patterns-interpreter
description: Recurring verbosity patterns found in chapters/interpreter.tex during June 2026 review
metadata:
  type: project
---

Recurring bloat patterns in interpreter.tex (detected June 2026):

1. **K12 "because every execution is finite and deterministic"** — after a
   First/Second/Third restriction triple, the transition paragraph restates the
   triple in a causal clause. Cut the clause; keep only the consequence.

2. **K12 soundness-restatement coda** — the completeness paragraph ends by
   re-asserting the soundness result from the preceding paragraph. The appended
   sentence ("Soundness guarantees that every trace...") is always deletable.

3. **K13 "deterministic: given the same inputs..."** — after establishing a
   process is deterministic by construction, the author glosses the word with
   its definition. Cut the gloss for CS-literate readers.

4. **K7 "eliminates ... entirely"** — "eliminates" implies totality; "entirely"
   is always redundant here.

5. **K12 one-sentence paragraph closing §4** — "The trace function is the
   bridge, and for the scalar-product case study it is complete and verified
   (Qed)." restates the two preceding paragraphs. Delete it.

6. **K12 benefit wind-up** — "By making X both A and B, we gain two benefits
   simultaneously" after sentences that already state A and B. Cut the wind-up;
   keep only the stated benefit clause.

7. **K12 caption re-enumeration** — when the body scope paragraph already
   enumerates declared inputs (e.g. the five-field list: corrupted party's
   program, hop ciphertexts, challenge secret, leak order, two cardinalities),
   the figure caption repeats the same list after "One control record supplies
   the declared fields, ...". Cut to just "the declared fields"; the body
   carries the detail. Detected in derived-overview.tex (June 2026).

8. **K12 $k$-gloss repetition** — "$k$ the corrupted view's hop count" in the
   facade paragraph repeats "$k$ the number of hop sites" from the scope
   paragraph seven lines earlier. Only one definition of $k$ needed.

**Why:** These patterns appear to be revision-round accretions: each fix round
adds a coda or causal clause to re-anchor new material, but the anchors
accumulate without removing prior mentions.

**How to apply:** On any future interpreter.tex or similar chapter review,
grep for "because every execution", "Soundness guarantees", "deterministic:
given", "eliminates.*entirely", "gain.*benefits simultaneously",
"declared fields.*program.*ciphertexts", "with \$k\$ the.*hop" as fast-path
detectors.
