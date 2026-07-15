---
name: notation-stub
description: Status of frontmatter/notation.tex — it is a TODO stub with zero notation entries.
metadata:
  type: project
---

File: /Users/cheng-huiweng/Projects/aplas2024-poster/thesis/frontmatter/notation.tex

As of 2026-06-01, the file contains:
  \chapter*{Notation and Conventions}
  \addcontentsline{toc}{chapter}{Notation and Conventions}
  % TODO: List notation conventions ...
  %   - Process calculus notation
  %   - Entropy notation
  %   - Rocq-specific conventions
  %   - Cryptographic notation

Zero actual notation entries. The gap flag notation_stub: true in term-map.json reflects this.

The thesis uses numerous notations defined in shared-macros.sty and thesis/macros.tex that are not surfaced to the reader in any front-matter notation table.

**Why:** The term reviewer's gap report (Phase 2) flags this stub as a missing reader aid. The gated fix (Phase 3) may auto-populate it from macro definitions.

**How to apply:** On rebuild, re-read notation.tex and update notation_stub flag. If entries have been added, set notation_stub: false and remove from gaps.
