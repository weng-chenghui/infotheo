# Blueprint chapter: alignment with the SSProve case studies

Date: 2026-07-29. Branch `20260729-0028-reduction-form-security`.
Status: design, not implemented. Follows the reduction-form migration
(`20260728-reduction-form-security-statements.md`, implemented through commit
`458546ea`).

## Goal

Add one blueprint chapter that records, row by row, how this development's
reduction-form statement discipline follows the SSProve case studies. The
blueprint states the bounds; nothing in it yet says the shape is upstream
house style. The evidence currently lives only in this notes directory and in
the `indcpa_ror.v` header.

## Deliverable

One new file `dumas2017dual/blueprint/src/ssprove_alignment.tex`, input from
`security.tex` between the end of the overview chapter and
`\part{Foundations}`. One sentence appended to the overview chapter pointing
forward to it. No other file changes.

- Chapter title: `Alignment with the SSProve case studies`.
- Label: `ch:ssprove_alignment` (matches the `ch:simulation`,
  `ch:guessing_experiment` pattern).
- No theorem environments, no `\rocq{}` citations, no `\uses`. The chapter is
  prose; our identifiers appear as `\texttt` and our results via `\ref` to
  their existing nodes, so `check_coverage.py` semantics are untouched.

## Style constraints

- Paragraphs of at most 4 sentences. A paragraph whose sentences lack
  connective flow becomes a list instead (user rule; `/thesis-prose` is the
  designated rewriting tool when drafting runs long).
- The closing evidence paragraph uses positive framing (what the examples'
  hypotheses ARE), per the standing project rule.
- SSProve citations are file + identifier only, pinned once in the opening
  paragraph to `coq-ssprove` 0.3.1, `theories/Crypt/examples/`.

## Chapter content (draft)

```latex
\chapter{Alignment with the SSProve case studies}
\label{ch:ssprove_alignment}

Every computational bound in this development is the advantage of an
explicitly constructed reduction, written $\epscpaof{E,R}$. This is the
statement style of SSProve's own case studies. The table below records the
correspondence row by row. SSProve sources are cited by file and identifier
against \texttt{coq-ssprove} 0.3.1, directory
\texttt{theories/Crypt/examples/}.

\begin{center}
\begin{tabular}{p{0.30\linewidth}p{0.30\linewidth}p{0.32\linewidth}}
\textbf{SSProve precedent} & \textbf{Pattern} & \textbf{This development} \\
\hline
\texttt{PRF.v}, \texttt{prf\_epsilon} &
the advantage bound is a function of the adversary, not a constant &
\texttt{indcpa\_epsilon}, Definition~\ref{def:indcpa_assumption} \\
\hline
\texttt{PRF.v}, \texttt{security\_based\_on\_prf} &
a headline bounds an advantage by a sum of reduction advantages, with
package validity and state disjointness as the only side conditions &
Theorem~\ref{thm:alice_guess_real} \\
\hline
\texttt{PRF.v}, \texttt{statistical\_gap} &
an information-theoretic summand stands unreduced beside the reduction
terms &
the $1/m$ fiber bound, Theorem~\ref{thm:guess_sdistr_success_le} \\
\hline
\texttt{MACCCA.v} and \texttt{SymmRatchet.v}, \texttt{cpa\_epsilon} &
the name of this quantity at an IND-CPA game pair &
the name \texttt{indcpa\_epsilon} \\
\hline
\texttt{PRFPRG.v}, \texttt{hyb\_security\_based\_on\_prf} &
a hybrid ladder is bounded by a sum over its rungs &
Lemma~\ref{lem:advantage_sum_ladder_le},
Theorem~\ref{thm:advantage_le} \\
\hline
\texttt{StretchPRG.v}, the source comment at its security theorem &
negligibility for a concrete scheme is recorded in prose, not as a formal
hypothesis &
the smallness reading beside Definition~\ref{def:indcpa_assumption} \\
\end{tabular}
\end{center}

Every assumption appearing in those case studies is a structural carrier:
the \texttt{Parameter} declarations of \texttt{Schnorr.v},
\texttt{SigmaProtocol.v}, \texttt{OVN.v} and \texttt{RandomOracle.v} supply
group and message types, for instance \texttt{gT : finGroupType}. Advantage
bounds are always stated, never assumed. This development follows the same
discipline: it declares no axiom of its own, and every headline's residual
trust base is upstream
(chapter~\ref{ch:simulation} and the allowlist note in the repository record
it).
```

The forward-reference sentence appended to the overview chapter:

```latex
Chapter~\ref{ch:ssprove_alignment} records how this statement discipline
follows the SSProve case studies.
```

## Evidence base (verified 2026-07-29 against the installed sources)

| Cited | Verified at |
|---|---|
| `prf_epsilon A := Advantage EVAL A` | `PRF.v:323` |
| `statistical_gap` | `PRF.v:325` |
| `security_based_on_prf` | `PRF.v:383` |
| `cpa_epsilon := Advantage CPA_EVAL` | `MACCCA.v:440` |
| `cpa_epsilon := Advantage CTXT` | `SymmRatchet.v:430` |
| `hyb_security_based_on_prf` | `PRFPRG.v:325` |
| `Negligible by assumption.` comment | `StretchPRG.v:165` |
| `Parameter gT : finGroupType` | `Schnorr.v:41` |

Blueprint labels referenced, all existing: `def:indcpa_assumption`
(`content.tex:487`), `thm:alice_guess_real` (`security.tex:162`),
`thm:guess_sdistr_success_le` (`it_bound_bridge.tex:495`),
`lem:advantage_sum_ladder_le` (`content.tex:551`), `thm:advantage_le`
(`content.tex:565`), `ch:simulation` (`security.tex:189`).

## Precision constraints

- The no-axiom claim is scoped: "declares no axiom of its own". The residual
  upstream trust base (boolp trio, `Axioms.R`, `ax_proof_irrel`,
  `realsum.__admitted__interchange_psum`) is real and is pointed at, not
  hidden.
- Row 6's third column points at `def:indcpa_assumption` because the prose
  smallness sentence sits in the part-intro gloss directly above that node;
  the part heading itself carries no label today. If review prefers a direct
  target, add `\label{part:autoderiv}` to `content.tex:10` and reference it —
  flagged as an implementation-time choice, default is the definition ref.
- `security_based_on_prf`'s bound is `prf_epsilon (A ∘ MOD_CPA_ff_pkg) +
  statistical_gap A + prf_epsilon (A ∘ MOD_CPA_tt_pkg)`; the row's pattern
  cell says "sum of reduction advantages" and the IT summand gets its own row,
  so no row overclaims.

## Risks

`tabular` is unused anywhere in this blueprint, and plasTeX swallows what it
does not recognize instead of failing. Mitigation is part of verification:
grep the generated HTML for a `<table` element and for the cell string
`prf_epsilon`. Fallback if the table does not render: the same six rows as a
`description`-style `itemize`, one item per correspondence, same cells.

## Non-goals

- No new theorem nodes, no changes to existing nodes or their `\uses`.
- No `\rocq{}` citations from this chapter (coverage set stays as is).
- No thesis (phd-thesis repo) changes.

## Naming audit

Created names, checked against project rules and file precedent:

| Name | Verdict | Rule |
|---|---|---|
| `ssprove_alignment.tex` | accept | snake_case file matching `it_bound_bridge.tex`; names the content, no abbreviation |
| `ch:ssprove_alignment` | accept | `ch:` prefix matches `ch:simulation`, `ch:absolute_pr`, `ch:it_bound` |

No Rocq identifiers are created, renamed, or restated.

## Verification

- `bash dumas2017dual/blueprint/make_blueprint.sh` exits 0.
- Generated HTML contains a `<table` element and the string `prf_epsilon`;
  no `undefined reference` in the plasTeX log.
- `python3 dumas2017dual/blueprint/check_coverage.py` prints OK with counts
  unchanged.
- Full-tree `make` untouched (no `.v` change).
