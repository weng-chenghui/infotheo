---
name: pattern_recurring
description: Recurring reference patterns specific to aplas2024-poster/thesis that speed up future audits
metadata:
  type: project
---

## Label ordering habit (class A suppressed)

Every theorem/lemma environment in dsdp.tex follows the pattern:
  `\begin{theorem}[Title]\label{...}%\sidenote{...}%`

The `\label` always appears immediately after the `[Title]` argument and before the
`\sidenote{}`. This is the CORRECT ordering (no class-A counter-capture). Future
audits can confirm the pattern holds rather than re-checking from scratch.

**Why:** The author learned about the sidenote-before-label counter-capture problem
and consistently puts the label first. The `%` after `\label{...}` suppresses
whitespace before the `\sidenote`.

**How to apply:** On each audit, scan dsdp.tex theorem-family environments for any
case where a `\sidenote{` appears before `\label{` on the same or preceding line.

## Archived \iffalse block in dsdp.tex (checker false-positive source)

Lines 1–250 of `chapters/dsdp.tex` are wrapped in `\iffalse ... \fi`. This block
contains the original chapter draft with the same `\label` names as the live
rewrite that follows line 254. The checker script does NOT skip `\iffalse` content,
so it reports all of these as D-multiply findings (14 labels in the 2026-06-02
run). These are false positives: `main.aux` has each label only once (LaTeX never
compiles `\iffalse` content) and `main.log` has no multiply-defined warnings.

**How to apply:** When D-multiply findings all have one location in lines 1–250 and
one in lines 254+, skip them as checker false-positives from the archived block.
Confirm with `grep -c newlabel{LABEL} main.aux` — should return 1.

## D-unreferenced labels in the live dsdp.tex section

As of 2026-06-02 the following labels are defined but never cited in the live
section or anywhere else in the thesis:

- `lem:dsdp:fiber-uniform` (§19.2.1)
- `lem:dsdp:functional-det` (§19.2.3)
- `thm:dsdp:bob-privacy` (§19.2.5)
- `thm:dsdp:charlie-privacy` (§19.2.6)

These are intermediate results used to build up the argument but not cross-cited by
later sections. They were also unreferenced in the archived (iffalse) draft.

**How to apply:** Check whether future sections add cross-refs before flagging these
as needing attention. They are minor (unreferenced theorem-family labels); not
Critical.

## checker script location and invocation

Script: `thesis/.script/check-references.py`
Run from: `thesis/` directory
Command: `python3 .script/check-references.py <thesis-root> --json .thesis-review/reference-map.json`
Output: `.thesis-review/reference-map.json`

The script parses `main.aux` and all source files and classifies findings into
classes A/B/C/D. It does NOT skip `\iffalse` blocks, so D-multiply findings from
the archived dsdp.tex block are expected false positives (see above).

## sec:related:simulation label on a \paragraph

`\label{sec:related:simulation}` is placed on `\paragraph{Related work.}` in
`ssprove.tex` line 147. It resolves to anchor `paragraph*.35`, num `12.6` in the
aux. Both `sec:related:simulation` and `sec:ssprove:bridge` print `12.6` when
referenced — this is intentional: `\paragraph` inherits `\thesection` and does
not have its own numbered counter. NOT a class-A counter-capture. The only
cross-ref is `\S\ref{sec:related:simulation}` in `conclusions.tex` line 43,
using the generic `\S` symbol. Acceptable.

## interpreter.tex multi-label habit (D-multiply, checker blind spot)

`chapters/interpreter.tex` puts multiple `\label` calls on the same `\section`
command. The checker does not detect these because all instances fall on the same
source line:
- Line 34: `\label{sec:interp:relational}\label{sec:procalc:smc}` — both resolve
  to 9.2. `sec:procalc:smc` is referenced by phantom-types.tex and pismc.tex.
- Line 174: `\label{sec:interp:executable}\label{sec:interp:soundness}
  \label{sec:interp:completeness}` — all resolve to 9.3. None are referenced
  (also D-unreferenced).

**How to apply:** On each audit, run:
  `grep -n '\\\\label{.*}\\\\label{' chapters/interpreter.tex`
to catch new co-labels on the same line. The checker will not flag these.
