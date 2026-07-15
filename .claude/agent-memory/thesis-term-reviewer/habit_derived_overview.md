---
name: habit-derived-overview
description: derived-overview.tex habitually introduces terms defined in derived-frontend/backend chapters without forward-reference glosses; canonical G2 pattern for a part lead-in
metadata:
  type: feedback
---

The derived-overview chapter (chapters/derived-overview.tex) introduces the following
technical terms in body prose before they are formally defined in the immediately
following chapters:

- "marshalling" -- defined in ch:derived-frontend §sec:frontend:interface
- "choice types" -- used only here; no definition anywhere in thesis (G3)
- "hop sites" / "hop count" -- defined in ch:derived-backend §sec:backend:syntax
- "receptions" -- defined informally in ch:derived-frontend §sec:frontend:run
- "corrupted view" -- used as established term; no formal definition site found
- "free term algebra" -- defined in ch:derived-frontend §sec:frontend:two-interp

**Why:** This is a part lead-in that telescopes the next three chapters into one
overview. All new technical vocabulary belongs to those later chapters, so every
term in the overview is structurally a forward dependency (G2) unless it also
carries an inline gloss.

**How to apply:** On any review of derived-overview.tex, check every technical
noun phrase against derived-frontend.tex and derived-backend.tex before concluding
it is absent from the term map. The term map predates these chapters (map chapter
order ends at ch:dsdp) so map misses are expected and must fall back to grep.

Also: "control record", "corrupted view", "hop sites", "hop count", "receptions",
"marshalling", and "choice types" are all absent from backmatter/list-of-terms.tex
as of the June 2026 edits. Flag glossary actions for all of them.
