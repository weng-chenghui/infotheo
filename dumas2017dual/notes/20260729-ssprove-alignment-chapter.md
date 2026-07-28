# Blueprint chapter: alignment with the SSProve case studies

Date: 2026-07-29. Branch `20260729-0028-reduction-form-security`.
Status: design, revised after one adversarial audit (verdict: SOUND WITH
FIXES; all 11 findings applied, see the Audit section). Follows the
reduction-form migration (`20260728-reduction-form-security-statements.md`,
implemented through commit `458546ea`).

## Goal

Add one blueprint chapter that records, row by row, how this development's
reduction-form statement discipline follows the SSProve case studies. The
blueprint states the bounds; nothing in it yet says the shape is upstream
house style. The evidence currently lives only in this notes directory and in
the `indcpa_ror.v` header.

## Deliverable

One new file `dumas2017dual/blueprint/src/ssprove_alignment.tex`, input from
`security.tex` between the end of the overview chapter (`security.tex:30`)
and `\part{Foundations}` (`:32`). A two-sentence forward-reference paragraph
appended to the overview chapter. One new label `ch:derivation_overview` on
the existing `\chapter{Overview of the derivation}` (`content.tex:13`), which
the closing paragraph references. No other file changes.

- Chapter title: `Alignment with the SSProve case studies`.
- Label: `ch:ssprove_alignment`.
- No theorem environments, no `\rocq{}` citations, no `\uses`. The chapter is
  prose; our identifiers appear as `\texttt` and our results via `\ref` to
  their existing nodes, so `check_coverage.py` semantics are untouched.
- The word SSProve is set with the blueprint's `\ssprove{}` macro
  (`macros/common.tex:23`), matching the 11 existing usages.

## Style constraints

- Paragraphs of at most 4 sentences. A paragraph whose sentences lack
  connective flow becomes a list instead (user rule; `/thesis-prose` is the
  designated rewriting tool when drafting runs long).
- Positive framing throughout (what things ARE); the audit's rewrites of the
  three "not/never" clauses are incorporated below.
- SSProve citations are file + identifier only, pinned once in the opening
  paragraph to `coq-ssprove` 0.3.1, `theories/Crypt/examples/`.

## Chapter content (draft, post-audit)

```latex
\chapter{Alignment with the \ssprove{} case studies}
\label{ch:ssprove_alignment}

Every computational bound in this development is the advantage of an
explicitly constructed reduction, written $\epscpaof{E,R}$. This is the
statement style of \ssprove{}'s own case studies. The table below records
the correspondence row by row. \ssprove{} sources are cited by file and
identifier against \texttt{coq-ssprove} 0.3.1, directory
\texttt{theories/Crypt/examples/}.

\begin{center}
\begin{tabular}{p{0.30\linewidth}p{0.30\linewidth}p{0.32\linewidth}}
\textbf{\ssprove{} precedent} & \textbf{Pattern} & \textbf{This development} \\
\hline
\texttt{PRF.v}, \texttt{prf\_epsilon} &
the advantage bound is a function of the adversary &
\texttt{indcpa\_epsilon}, Definition~\ref{def:indcpa_assumption} \\
\hline
\texttt{PRF.v}, \texttt{security\_based\_on\_prf} &
the security theorem bounds an advantage by a sum of reduction advantages
(plus one statistical summand), with package validity and state
disjointness as the only side conditions &
Theorem~\ref{thm:alice_view_advantage}, a sum of two reduction advantages
under the same side conditions \\
\hline
\texttt{PRF.v}, \texttt{statistical\_gap} &
an information-theoretic summand stands beside the reduction terms &
the $1/m$ fiber bound, discharged in closed form
(Theorem~\ref{thm:guess_sdistr_success_le}) and composed into
Theorem~\ref{thm:alice_guess_real} \\
\hline
\texttt{MACCCA.v} and \texttt{SymmRatchet.v}, \texttt{cpa\_epsilon} &
the name of this quantity at an IND-CPA game pair, in the left--right
(\texttt{CPA\_EVAL}) and real-or-random (\texttt{CTXT}) variants &
the name \texttt{indcpa\_epsilon}, at a real-or-zero pair \\
\hline
\texttt{PRFPRG.v}, \texttt{hyb\_security\_based\_on\_prf} &
a hybrid ladder is bounded by a sum over its rungs &
Lemma~\ref{lem:advantage_sum_ladder_le},
Theorem~\ref{thm:advantage_le} \\
\hline
\texttt{StretchPRG.v}, the comment at \texttt{prg\_epsilon} (repeated at
the epsilon definitions of \texttt{PRFPRG.v}, \texttt{MACCCA.v},
\texttt{SymmRatchet.v}) &
negligibility of an assumed primitive's advantage is recorded in prose at
its definition &
the smallness sentence in the derivation overview,
Chapter~\ref{ch:derivation_overview} \\
\end{tabular}
\end{center}

Every hypothesis appearing in those case studies supplies algebraic or
interface data: the \texttt{Parameter} declarations of \texttt{Schnorr.v},
\texttt{SigmaProtocol.v}, \texttt{OVN.v}, \texttt{RandomOracle.v} and the
\texttt{Assumptions/} modules declare groups, generators and their facts,
relations, and algorithm carriers, for instance
\texttt{gT :\ finGroupType}. Every advantage bound enters as a proved
statement. This development follows the same discipline: every axiom in its
trust base is upstream, recorded beside the derivation overview
(Chapter~\ref{ch:derivation_overview}) and listed per headline in the
repository note \texttt{notes/20260729-headline-assumptions-allowlist.md}.
```

The forward-reference paragraph appended to the overview chapter, as its own
paragraph (the current second paragraph already has 4 sentences):

```latex
Both computational legs above state their bounds as advantages of explicit
reductions. Chapter~\ref{ch:ssprove_alignment} records how this statement
discipline follows the \ssprove{} case studies.
```

## Evidence base (verified 2026-07-29 against the installed sources)

| Cited | Verified at |
|---|---|
| `prf_epsilon A := Advantage EVAL A` | `PRF.v:323`; used composed, `prf_epsilon (A ∘ MOD_CPA_ff_pkg)`, `:390-392` |
| `statistical_gap` | `PRF.v:325`; used at `:391`, bounded nowhere in the file |
| `security_based_on_prf` | `PRF.v:383`; hypotheses exactly `ValidPackage` + two `fseparate` (`:384-388`) |
| `cpa_epsilon := Advantage CPA_EVAL` (left-right) | `MACCCA.v:440` |
| `cpa_epsilon := Advantage CTXT` (real-or-random) | `SymmRatchet.v:430` |
| `hyb_security_based_on_prf`, bound is a literal bigop sum | `PRFPRG.v:325-333` |
| `Negligible by assumption.` at `prg_epsilon` | `StretchPRG.v:162-167`; same comment `PRFPRG.v:314-318`, `MACCCA.v:427-439`, `SymmRatchet.v:417-429` |
| `Parameter gT : finGroupType` | `Schnorr.v:41`; further Parameters `Schnorr.v:44-45`, `SigmaProtocol.v:39,61-85`, `Assumptions/DDH.v:44-53`, `DL.v:44-53`, `tSDH.v:43-56` — all structural, zero advantage bounds or hardness assumptions, zero `Admitted` in the examples tree |

Blueprint targets, all verified at `b74bc787`:
`def:indcpa_assumption` (`content.tex:487`), `thm:alice_view_advantage`
(`security.tex:149-159`; Rocq side has the single record hypothesis
`Adv : dsdp_indcpa_adversary dsdp_experiment`), `thm:guess_sdistr_success_le`
(`it_bound_bridge.tex:495`), `thm:alice_guess_real` (`security.tex:162`),
`lem:advantage_sum_ladder_le` (`content.tex:551`), `thm:advantage_le`
(`content.tex:565`), `part:autoderiv` (`content.tex:11`, already exists),
smallness sentence (`content.tex:34-36`, in the Overview chapter that
receives the new `ch:derivation_overview` label), upstream-`Admitted` record
(`content.tex:172-176`, same chapter).

## Precision constraints

- Row 2's target is `thm:alice_view_advantage`, whose statement is an
  advantage bounded by exactly two reduction advantages. The guessing
  headline `thm:alice_guess_real` carries the `1/m` summand and two further
  hypotheses (a marshalling cancellation and an injectivity), so it
  instantiates Row 3's composition, and only that.
- The trust-base sentence names the derivation overview chapter and the
  allowlist note. The full residual list there is: the boolp trio,
  `FunctionalExtensionality.functional_extensionality_dep`, `Axioms.R`,
  `SPropBase.ax_proof_irrel`, `realsum.__admitted__interchange_psum`.
- Row 6 records that the shared comment attaches to the epsilon
  *definitions*, and that the assumed-primitive reading ("negligibility of
  an assumed primitive's advantage") is the accurate gloss.

## Risks

`tabular` is unused anywhere in this blueprint. The installed plasTeX 3.1
implements `tabular` with p-column specs and defines `\linewidth`
(`Base/LaTeX/Arrays.py`, `Paragraphs.py:26`), so the risk is low; the
verification still greps the generated HTML for a `<table` element and the
cell string `prf_epsilon`. Fallback if the table fails to render: the same
six rows as an `itemize`, one item per correspondence, same cells.

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
| `ch:derivation_overview` | accept | `ch:` prefix, names the existing `\chapter{Overview of the derivation}`; no clash (grep) |

No Rocq identifiers are created, renamed, or restated.

## Adversarial audit

One round, verdict SOUND WITH FIXES, 11 findings, all applied:

1. (BLOCKER) Row 2 targeted `thm:alice_guess_real`, which is a probability
   bound with a `1/m` summand and extra hypotheses — retargeted to
   `thm:alice_view_advantage`.
2. Row 2's pattern cell hid `statistical_gap` in `security_based_on_prf`'s
   bound — now "(plus one statistical summand)".
3. The closing paragraph cited `ch:simulation` for the trust base, which
   records no axioms — now `ch:derivation_overview` (new label) plus the
   allowlist note by path.
4. The spec claimed `part:autoderiv` does not exist; it exists at
   `content.tex:11` — false sentence deleted, Row 6 retargeted to the
   overview chapter.
5. Row 6's comment attaches to `prg_epsilon`, and identically in three more
   files — row rewritten, citation format honored.
6. `SymmRatchet.v`'s `CTXT` is real-or-random, `MACCCA.v`'s `CPA_EVAL` is
   left-right — both variants named; real-or-random is the closer precedent
   for our real-or-zero pair.
7. Row 3 now says the IT summand is discharged in closed form here, where
   upstream (`PRPCCA.v:12-14`, `PRFMAC.v:10-13`) records it as unfinished.
8. The Parameter survey extended to `Assumptions/` and re-glossed as
   algebraic/interface data (relations, algorithms, generator facts).
9. Positive-framing rewrites: "every advantage bound enters as a proved
   statement", "every axiom in its trust base is upstream"; the two "not"
   table cells dropped their negative clauses.
10. Forward-reference is its own two-sentence paragraph with an explicit
    antecedent.
11. `FunctionalExtensionality.functional_extensionality_dep` added to the
    trust-base list.

## Verification

- `bash dumas2017dual/blueprint/make_blueprint.sh` exits 0.
- Generated HTML contains a `<table` element and the string `prf_epsilon`;
  no `undefined reference` in the plasTeX log.
- `python3 dumas2017dual/blueprint/check_coverage.py` prints OK with counts
  unchanged.
- Full-tree `make` untouched (no `.v` change).
