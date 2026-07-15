---
name: thesis-patterns
description: Recurring reference patterns observed in this thesis across multiple audit runs
metadata:
  type: project
---

## Alias labels on a single \section line

This thesis uses multiple `\label{}` macros on a single `\section{}` line to create
cross-chapter aliases for the same section. These are intentional:

- `interpreter.tex:33` — `\label{sec:interp:relational}\label{sec:procalc:smc}`
  (the section is referenced as "Section 9.2" from phantom-types and pismc chapters)
- `interpreter.tex:173` — three labels: `sec:interp:executable`, `sec:interp:soundness`,
  `sec:interp:completeness` (all resolve to `section.9.3`)

These appear in the aux as duplicate-anchor entries but are NOT defects. The checker
script correctly reports 0 D-multiply findings because each label has one source
definition. Do not flag these as errors on future runs.

## Conclusions chapter section numbering

`chapters/conclusions.tex` is an unnumbered chapter (`\chapter*{}` via kaobook) that
resets its section numbers from 1. This causes `sec:concl:*` labels to share the same
`section.19.N` anchors as `sec:dsdp:*` labels in dsdp.tex (both are in "chapter 19"
numbering space). These are expected collisions with no semantic defect since no `\ref`
targets the conclusions section labels.

## No sidenote-capture habit found

As of the June 2026 audit, this thesis has NO instances of the `\sidenote`-before-
`\label` counter-capture defect (class A). The kaobook class `\sidenote{}` macro is
always placed AFTER the `\label{}` in theorem/lemma/definition headers, or placed in
the theorem body (not the header line). Future runs should still check the aux
anchor_type for NUMBERED_ENVS, but the habit is not present.

## Routinely unreferenced labels

These theorem-family labels are consistently unreferenced by `\ref{}` across audits
(the surrounding prose describes them without a cross-reference):
- `thm:dsdp:bob-privacy` and `thm:dsdp:charlie-privacy` (dsdp.tex) — final
  per-party privacy theorems; prose says "the three theorems" without \ref
- `lem:dsdp:fiber-uniform` and `lem:dsdp:functional-det` (dsdp.tex) — bridge
  hypotheses stated as lemmas; only the succeeding theorems are \ref'd
- `thm:shen37` (smc-spp.tex) — external theorem from Shen et al.; discussed inline
- `def:infotheo:hunp` (information-theory.tex) — unpredictability entropy definition;
  the concept is not cross-referenced from other chapters

**Why:** these are informational D-unreferenced findings (minor severity) with no
broken \ref. They are the full D class for this thesis.

## Hard-coded number false-positive

The string "Theorem 3.7" in smc-spp.tex line 359 appears inside a `\begin{theorem}[...]`
optional title field. The checker correctly strips theorem titles before scanning for
class C, so this external-paper citation number is not reported as class C.
