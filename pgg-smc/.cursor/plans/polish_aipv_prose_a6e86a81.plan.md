---
name: Polish AIPV Prose
overview: Revise the current extended abstract for smoother academic English by improving transitions, removing em-dash-driven sentence structure, and reducing abrupt concept jumps without expanding beyond the 2-page limit.
todos:
  - id: smooth-abstract-intro
    content: Rewrite the abstract and introduction for complete sentences and smoother transitions
    status: pending
  - id: smooth-workflow
    content: Re-sequence the workflow section so new concepts are introduced with explicit connective sentences
    status: pending
  - id: smooth-case-study
    content: Rewrite the case-study paragraph to reduce abrupt label-style starts while preserving technical density
    status: pending
  - id: normalize-prose-style
    content: Remove em-dash-driven pivots and colon/semicolon compression from observations, related work, and conclusion
    status: pending
  - id: verify-length
    content: Check that the revised abstract still compiles and remains within the 2-page limit
    status: pending
isProject: false
---

# Polish Plan: AIPV Extended Abstract

## What Needs Fixing

The current draft in [/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex](/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex) now has the right high-level structure, but the prose still reads compressed in several places:

- The abstract uses telegraphic fragments such as `Zero \texttt{Admitted}.`
- The introduction still contains em-dash pivots like `What if formalization comes first---not as polished verification, but as a prototyping medium?`
- The workflow section introduces new concepts too quickly, especially in the jump from the surjective-relation hypothesis to covering spaces and then to the human/LLM/type-checker role split.
- The case-study section compresses four technical layers into one paragraph with label-style starts (`\textbf{Protocol:}`, `\textbf{Search-space:}`), which makes transitions feel abrupt.
- The observations, related work, and conclusion sections still rely on colon/semicolon compression instead of explicit connective sentences.

## Rewrite Goal

Keep the current academic extended-abstract structure, but make the English read like continuous academic prose:

- Replace em-dash contrast with full sentences and connective phrases.
- Replace fragmentary statements with complete sentences.
- Add short transition phrases between motivation, method, case study, and takeaway.
- Preserve the 2-page limit by trading compressed punctuation for slightly cleaner sentence sequencing, not by expanding content substantially.

## Planned Edits

### 1. Smooth the Abstract and Introduction

Update the opening so each sentence leads naturally to the next:

- Turn fragment-style claims into full sentences.
- Replace rhetorical em-dash contrasts with explicit transitions such as `Instead,`, `In this workflow,`, `More concretely,`, or `As a result`.
- Recast the contribution sentence so it reads as one coherent claim rather than a packed list.

Focus area:

- [/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex](/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex)

Concise target examples:

```25:27:/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex
Formalization traditionally comes last. A researcher studies the relevant mathematics, designs a construction informally, and only then translates the result into a proof assistant as a final verification step. This ordering makes sense when the researcher already knows the mathematical landscape, but it imposes a high barrier when the construction requires unfamiliar domains.
```

### 2. Add Explicit Transitions in the Workflow Section

Rewrite the workflow section so the logic unfolds in a clearer sequence:

1. Starting hypothesis from MPC.
2. Why covering spaces are the relevant mathematical match.
3. Why formalization was used early rather than late.
4. How the human, LLM, and type checker divide labor.

This section should feel cumulative rather than jumpy. The current prose introduces these ideas correctly, but too abruptly.

### 3. Decompress the Case Study Paragraph

The current case-study paragraph is structurally efficient but stylistically abrupt. Rewrite it into smoother prose while keeping roughly the same length:

- Keep the four protocol/search-space/reconstruction/security ideas.
- Replace bold label starts with transition-led sentences.
- Use one sentence to explain why each layer follows from the previous one.
- Retain the concrete technical terms, but reduce the feeling of a list being poured into a paragraph.

Key passage to rewrite:

```37:39:/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex
The seed idea grew into SMC-PGG (Secure Multi-party Computation via Permutation-Group Graphs), a four-layer formalization. \textbf{Protocol:} A monodromy representation $\rho : G \to S_N$ maps group elements to permutations on $N$ sheets, hiding a secret in the fiber structure of a covering space; packaged as an HB mixin (\texttt{MonodromyReprType}) with session-typed programs. \textbf{Search-space:} The adversary's view is characterized via RAAG trace equivalence; the Cartier-Foata theorem (proved from MathComp primitives alone) gives exact trace counts via clique polynomial recurrence---a domain the LLM introduced when the proof required counting distinct computation histories.
```

### 4. Normalize Punctuation Style Across the Back Half

Systematically remove remaining prose patterns that make the English feel abrupt:

- Remove em dashes used as sentence pivots.
- Reduce semicolon chaining where a period would read more naturally.
- Replace colon-led fragments such as `Tight feedback loop:` and `Limits:` with complete sentences.
- Keep mathematical notation unchanged unless the surrounding sentence must be lightly reworded.

Primary targets:

- `\section{Observations}`
- `\section{Related Work}`
- `\section{Conclusion}`

### 5. Preserve Constraints While Revising

While polishing the prose, keep these constraints intact:

- Stay within the existing 2-page PDF budget.
- Keep the current section structure.
- Preserve the explicit contribution statement, related-work citations, and technical claims.
- Avoid reintroducing blog-style narration.
- Do not weaken the academic tone by making the writing overly conversational.

## Verification

After implementation, verify:

- No em-dash-style prose transitions remain in the body text.
- Abrupt topic starts are replaced by connective sentences.
- The abstract no longer contains sentence fragments.
- The case-study section reads as prose rather than an inline checklist.
- The document still fits in 2 pages.
- The LaTeX file still compiles cleanly.

## File To Modify

- [/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex](/Users/cheng-huiweng/Projects/coq/infotheo/pgg-smc/notes/aipv2026_extended_abstract.tex)

