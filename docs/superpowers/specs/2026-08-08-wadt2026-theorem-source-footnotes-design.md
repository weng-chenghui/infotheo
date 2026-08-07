# WADT 2026 Theorem Source Footnotes Design

## Goal

Every rendered theorem block in
`pgg-smc/paper-wadt2026/main.tex` must be checked for a direct Rocq
counterpart. When a counterpart exists, the theorem title carries a footnote
mark. The footnote gives the repository-relative `.v` path and the exact Rocq
declaration names. A paper theorem may have no formal counterpart. In that
case, the paper is not given a fabricated source footnote, and the missing
counterpart is reported to the user in the completion message.

## Coverage

The audit applies to all nine `theorem` environments in the paper:

1. Orbit encoder
2. Orbit split
3. Three-transitivity
4. Executed correctness
5. Recovery ramp
6. Exact privacy for the fixed dealer
7. All-decks exact privacy
8. Shuffle-free deck privacy
9. Finite-step shuffle bound

If one paper theorem combines several formal statements, its footnote lists
every declaration that directly supports a claim in the rendered theorem
body. It does not list proof dependencies or internal helper lemmas. If every
paper theorem has a direct formal counterpart, all nine titles receive source
footnotes.

## Format

Each optional theorem title ends with a footnote mark. Its footnote text is
placed next to the theorem source so that the mark and text cannot be
separated by another footnote. The text uses this form:

```tex
Formalized in \path{pgg-smc/.../file.v} as
\coqin{theorem\_one} and \coqin{theorem\_two}.
```

Paths are relative to the repository root. File paths and Rocq names use
monospace formatting and may break across lines. Existing source-index tables
remain in the paper.

## Claim Mapping Rules

- A name is included only after checking its declaration in the repository.
- Multiple files are listed when one paper theorem draws direct statements
  from more than one file.
- A theorem with no direct formal counterpart receives no source footnote and
  is listed explicitly in the completion message.
- The footnote describes formalization evidence only. It does not add proof
  status, implementation detail, novelty language, or proof sketches.
- No Rocq source file is edited.

## Verification

After the edit:

1. Count nine theorem environments. Check that the number of theorem-title
   source footnotes equals the number of theorem blocks with verified direct
   formal counterparts.
2. Check every listed path exists and every listed Rocq declaration occurs in
   that file.
3. Force-rebuild the PDF with `latexmk -g -pdf`.
4. Check for undefined references, overfull boxes, and duplicate footnote
   numbering.
5. Render and inspect every page containing a theorem. Long paths and names
   must remain readable and must not overlap theorem text or page margins.
6. Report every theorem block with no direct formal counterpart. If there are
   none, state that all nine theorem blocks have verified Rocq counterparts.
7. Confirm that the diff contains no `.v` file.
