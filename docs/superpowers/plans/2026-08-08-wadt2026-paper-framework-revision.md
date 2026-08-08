# WADT 2026 Paper Framework Revision Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the methodology section, replace framework prose with an architecture figure and three sourced generic theorems, and give den Boer the agreed historical position in Related Work.

**Architecture:** Keep one `Framework and Generic Theorems` section with two explicit subsections. The first subsection presents the record architecture through an adapted TikZ figure. The second states three generic results in theorem blocks. Artifact details move to one introduction footnote, while Related Work opens with den Boer's five-card trick.

**Tech Stack:** LNCS LaTeX, TikZ, BibTeX, `latexmk`, Poppler PDF rendering, ripgrep, local Rocq source inspection, and the project research knowledge base for citation verification.

## Global Constraints

- Follow `docs/superpowers/specs/2026-08-08-wadt2026-paper-framework-revision-design.md`.
- Modify `pgg-smc/paper-wadt2026/main.tex` only, except for a verified correction to den Boer metadata in `pgg-smc/paper-wadt2026/references.bib`.
- Do not modify any `.v` file and do not create a formalization request.
- Preserve the distinction between the exact uniform law and the finite-step word law.
- Preserve every existing qualification about prior, dealer law, shuffle law, passive adversaries, and the reveal boundary.
- Use short sentences and the language level of `/Users/cheng-huiweng/Projects/aplas2024-poster/forteApr22/forteApr22.tex`.
- Use single-author voice. Do not introduce authorial `we` or `our`.
- Do not use em dashes, semicolons, prose asides, inflated claims, or generic filler.
- Keep mathematical claims inside theorem blocks. Keep motivation, source status, proof strategy, and scope discussion outside them.
- Every new theorem title must have a footnote with a repository-relative Rocq path and exact declaration name.
- The architecture caption may contain only the figure name and the meanings of colors and arrows.
- `pgg-smc/paper-wadt2026/main.tex` already has user-owned uncommitted edits and red `\greg{...}` notes. Do not delete, rewrite, stage, or commit those baseline edits.
- Before each commit, inspect `git diff --cached`. If an approved edit and a baseline user edit cannot be separated safely, stop before committing and ask the user to commit the baseline first.
- Use `apply_patch` for source edits. Do not stage generated PDF, AUX, LOG, BBL, BLG, FDB, or FLS files.

## File Map

- `pgg-smc/paper-wadt2026/main.tex`: owns the section structure, TikZ figure, theorem statements, artifact footnote, Related Work, roadmap, and acknowledgements.
- `pgg-smc/paper-wadt2026/references.bib`: already owns `denBoer1989`. Change it only if source verification proves that its metadata is wrong.
- `/Users/cheng-huiweng/Projects/aplas2024-poster/wadtSep17/slides.tex`: read-only source for the record diagram in the frame titled `The specification: one MonodromyProfile`.
- `/Users/cheng-huiweng/Projects/aplas2024-poster/forteApr22/forteApr22.tex`: read-only prose baseline.
- `pgg-smc/reconstruct/transitivity_privacy.v`: read-only source for `ttrans_view_indep_gen`.
- `pgg-smc/security/pgg_trace_secrecy.v`: read-only source for `trace_secrecy_of_view`.
- `pgg-smc/security/pgg_collusion_bound.v`: read-only source for `var_dist_fdistmap`.

---

### Task 1: Replace the framework prose with architecture and theorem subsections

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex:223-279`
- Read: `/Users/cheng-huiweng/Projects/aplas2024-poster/wadtSep17/slides.tex:496-528`
- Read: `pgg-smc/protocol/pgg_monodromy_profile.v:44-56`
- Read: `pgg-smc/reconstruct/transitivity_privacy.v:615-625`
- Read: `pgg-smc/security/pgg_trace_secrecy.v:25-52`
- Read: `pgg-smc/security/pgg_collusion_bound.v:62-80`

**Interfaces:**
- Consumes: the current model notation `S`, `V_C`, `T_C`, `G`, `U_G`, and unhalved `L_1` distance from Section 2.
- Produces: `Framework Architecture`, figure label `fig:framework-architecture`, `Generic Theorems`, three theorem blocks, and twelve total theorem-source footnotes in the paper.

- [ ] **Step 1: Record the pre-edit structure and protect user changes**

Run:

```bash
git diff -- pgg-smc/paper-wadt2026/main.tex
rg -n '\\begin\{theorem\}|Formalized in \\path' pgg-smc/paper-wadt2026/main.tex
```

Expected: nine theorem blocks and nine source footnotes. Read every existing uncommitted hunk. Preserve all `\greg{...}` notes and all user wording changes.

- [ ] **Step 2: Reopen the three formal statements before drafting**

Run:

```bash
sed -n '615,630p' pgg-smc/reconstruct/transitivity_privacy.v
sed -n '25,58p' pgg-smc/security/pgg_trace_secrecy.v
sed -n '62,82p' pgg-smc/security/pgg_collusion_bound.v
```

Expected evidence:

- `ttrans_view_indep_gen` assumes a Boolean secret prior, a uniform positive-order group, a `t`-transitive action, a coalition of size at most `t`, and a distinct-card encoding.
- `trace_secrecy_of_view` assumes `player_trace = trace_of \`o view`, `cancel trace_of view_of`, and view independence.
- `var_dist_fdistmap` states that finite pushforward does not increase the repository's unhalved variation distance.

- [ ] **Step 3: Replace the architecture prose and insert the adapted figure**

Use this structure and TikZ content. Keep the prose short when applying it to the real file.

```tex
\section{Framework and Generic Theorems}\label{sec:framework}

\subsection{Framework Architecture}

A protocol instance supplies an action, a shuffle-security bound, and a
decoder. The framework packages these components and uses them in one
executable protocol. Its finite algebraic structures use Mathematical
Components~\cite{MathComp}.

\begin{figure}[t]
  \centering
  \resizebox{\linewidth}{!}{%
  \begin{tikzpicture}[
      every node/.style={font=\small},
      rec/.style={draw,rounded corners,fill=blue!8,align=center,inner sep=5pt},
      sub/.style={draw,rounded corners,fill=green!8,align=center,inner sep=4pt,
                 font=\footnotesize},
      arr/.style={-{Latex[length=2mm]},thick}]
    \node[rec] (mp) at (0,1.5) {\textbf{MonodromyProfile}};
    \node[rec] (pi) at (-3.7,0) {\textbf{PGGInterface}\\protocol layout};
    \node[rec] (sw) at (0,0) {\textbf{SecurityWitness}\\endpoint bound};
    \node[rec] (rp) at (3.7,0) {\textbf{ReconPlug}\\reconstruction};
    \node[sub] (se) at (0,-1.2)
      {\textbf{SecurityExact}\\\textbf{SecurityAsymptotic}};
    \node[sub] (ts) at (3.7,-1.05) {\textbf{ThresholdScheme}};
    \node[sub] (ie) at (3.7,-1.8) {\textbf{InputEncoding}};
    \draw[arr] (pi) -- (mp);
    \draw[arr] (sw) -- (mp);
    \draw[arr] (rp) -- (mp);
    \draw[arr] (se) -- (sw);
    \draw[arr] (ie) -- (ts);
    \draw[arr] (ts) -- (rp);
  \end{tikzpicture}}
  \caption{Architecture of the group-parametric card-protocol framework.
  Blue boxes denote the profile and its three component records. Green boxes
  denote supporting records. Arrows denote dependencies.}
  \label{fig:framework-architecture}
\end{figure}

\coqin{PGGInterface} gives the dealer, player, and verifier layout.
\coqin{SecurityWitness} gives an endpoint bound for a shuffle law.
\coqin{ReconPlug} connects the group action to a decoder.
\coqin{MonodromyProfile} packages these three components.

The supporting records refine individual components. Exact and asymptotic
security records justify endpoint bounds. A threshold scheme supplies sharing
and reconstruction data. An input encoding adds committed inputs when a
protocol needs them.
```

Do not copy Beamer commands or the slide sentence that tells a presenter what to prove. The figure must fit `\linewidth` without text smaller than the paper footnotes.

- [ ] **Step 4: Add the explicit theorem transition and three sourced statements**

Use this mathematical content. Keep theorem bodies free of implementation and status prose.

```tex
The records above specify one protocol instance. The next subsection turns
from the architecture to the generic theorems derived from these records.

\subsection{Generic Theorems}

\begin{theorem}[Generic coalition privacy\footnotemark]
\footnotetext{Formalized in
\path{pgg-smc/reconstruct/transitivity_privacy.v} as
\coqin{ttrans\_view\_indep\_gen}.}
Let $G$ act $t$-transitively on the card positions. Let $S$ be a Boolean
secret with any prior, and suppose that every encoded deck has distinct
cards. If $g$ is uniform on $G$, then
\[
  S \mathrel{\perp\!\!\!\perp} V_C
\]
for every coalition $C$ with $|C|\leq t$.
\end{theorem}

\begin{theorem}[Generic trace lifting\footnotemark]
\footnotetext{Formalized in
\path{pgg-smc/security/pgg_trace_secrecy.v} as
\coqin{trace\_secrecy\_of\_view}.}
Let $S$, $V$, and $T$ be finite random variables. Suppose that
$T=\tau(V)$ and that a map $\nu$ satisfies $\nu(\tau(v))=v$ for every $v$.
If $V$ is independent of $S$, then
\begin{equation}
  H(S\mid T)=H(S).
  \label{eq:view-to-trace}
\end{equation}
\end{theorem}

\begin{theorem}[Data processing for finite distributions\footnotemark]
\footnotetext{Formalized in
\path{pgg-smc/security/pgg_collusion_bound.v} as
\coqin{var\_dist\_fdistmap}.}
For finite distributions $P$ and $Q$ on $A$ and a map $f:A\to B$,
\[
  \lVert f_*P-f_*Q\rVert_1\leq\lVert P-Q\rVert_1.
\]
\end{theorem}

The first theorem supplies the exact view argument used by the PGL instance.
The second moves that result to an executed trace. The third transfers a
group-level mixing bound to card endpoints.
```

Check the compiled symbol for independence. If `\mathrel{\perp\!\!\!\perp}` renders poorly, use the existing paper notation for independence without changing the claim.

- [ ] **Step 5: Build and check the new section**

Run:

```bash
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n 'LaTeX Warning:.*undefined|Citation .* undefined|Reference .* undefined|There were undefined references|Overfull \\[hv]box' main.log
rg -c '\\begin\{theorem\}' main.tex
rg -c 'Formalized in \\path' main.tex
```

Expected: `latexmk` exits 0. The warning scan has no matches. Both counts are twelve.

- [ ] **Step 6: Stage only the approved framework hunk and commit**

Run:

```bash
git add -p pgg-smc/paper-wadt2026/main.tex
git diff --cached --check
git diff --cached -- pgg-smc/paper-wadt2026/main.tex
git commit -m 'wadt2026: present framework architecture and generic theorems'
```

Expected: the staged diff contains only the replacement of the framework section. It contains none of the pre-existing user edits or `\greg{...}` notes.

---

### Task 2: Remove the methodology narrative and reduce artifact information

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex:73-79`
- Modify: `pgg-smc/paper-wadt2026/main.tex:117-124`
- Delete from: `pgg-smc/paper-wadt2026/main.tex:660-718`
- Delete from: `pgg-smc/paper-wadt2026/main.tex:801-807`

**Interfaces:**
- Consumes: the introduction's first mention of the Rocq development, the roadmap, the full methodology section, and the ending disclosure blocks.
- Produces: one artifact footnote in the introduction, no methodology section, no artifact subsubsection, and a roadmap that leads from Other Instances to Related Work.

- [ ] **Step 1: Add the one-sentence artifact footnote**

Attach the footnote to the introduction's first use of `The development`:

```tex
The development\footnote{The companion artifact contains the source, theorem
index, assumption report, and build instructions.} in this article instead
uses a proof assistant to state reusable group actions, dealer laws,
participant views, and executed traces.
```

Do not add repository history, hardware, tool versions, claim-matrix details, or release procedures.

- [ ] **Step 2: Update the introduction roadmap**

Replace the two sentences that make Sections `instances` through `related` include methodology with:

```tex
Section~\ref{sec:instances} compares the sibling instances.
Section~\ref{sec:related} places the results among related work.
Section~\ref{sec:conclusion} states the remaining bridge and other future
directions.
```

Preserve all nearby user-owned `\greg{...}` notes and wording changes.

- [ ] **Step 3: Delete the full methodology section**

Delete from:

```tex
\section{Methodology and Artifact}\label{sec:method}
```

through the paragraph ending with:

```tex
formal statements and paper claims remain aligned.
```

After deletion, the last paragraph of `Other Instances` must be followed by:

```tex
\section{Related Work}\label{sec:related}
```

- [ ] **Step 4: Delete the final artifact subsubsection and retain the AI statement**

Delete:

```tex
\subsubsection*{Artifact availability.}

The submission artifact will include the source, theorem index, claim matrix,
per-theorem assumption report, excluded-test-file note, and build
instructions. It will fix the formalization at the commit reported in
Section~\ref{sec:method}.
```

Keep `Acknowledgements and AI-use statement` and `Disclosure of Interests`.
Do not expand the AI-use statement.

- [ ] **Step 5: Check deletion coverage and rebuild**

Run:

```bash
rg -n 'Methodology and Artifact|sec:method|Artifact availability|arm64|OCaml 4\.14\.2|Print Assumptions|claim matrix|excluded-test-file' pgg-smc/paper-wadt2026/main.tex
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n 'LaTeX Warning:.*undefined|Citation .* undefined|Reference .* undefined|There were undefined references|Overfull \\[hv]box' main.log
```

Expected: the deletion scan has no matches. The build exits 0. The warning scan has no matches.

- [ ] **Step 6: Stage only the approved artifact and deletion hunks and commit**

Run:

```bash
git add -p pgg-smc/paper-wadt2026/main.tex
git diff --cached --check
git diff --cached -- pgg-smc/paper-wadt2026/main.tex
git commit -m 'wadt2026: remove methodology narrative'
```

Expected: the staged diff contains the artifact footnote, roadmap correction, methodology deletion, and artifact-subsubsection deletion. It does not stage any pre-existing user note or wording change.

---

### Task 3: Give den Boer the historical opening in Related Work

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`, first paragraph of `Related Work`
- Modify only if verified incorrect: `pgg-smc/paper-wadt2026/references.bib:1-10`

**Interfaces:**
- Consumes: bibliography key `denBoer1989`, the original den Boer publication, one reliable historical source, and the present Related Work structure.
- Produces: a verified priority claim limited to card-based cryptographic protocols and a short technical description of the five-card trick.

- [ ] **Step 1: Verify the den Boer citation through the research knowledge base**

Use the `research-kb` skill before fetching or recording citation evidence. Verify all of the following:

- author is Bert den Boer
- title is `More Efficient Match-Making and Satisfiability: The Five Card Trick`
- the work appeared at EUROCRYPT 1989 and the LNCS proceedings were published in 1990
- pages are 208 through 217 in LNCS 434
- the protocol uses five cards to compute Boolean AND
- a reliable historical source explicitly identifies it as the first card-based cryptographic protocol or as the work that introduced card-based cryptography

Save the supporting slices and metadata in the research knowledge base. Do not treat a search-result snippet as evidence.

- [ ] **Step 2: Compare verified metadata with the local BibTeX entry**

Run:

```bash
sed -n '1,14p' pgg-smc/paper-wadt2026/references.bib
```

Expected: `denBoer1989` matches the verified author, title, venue, LNCS volume, pages, publisher, and proceedings year. If it matches, do not edit `references.bib`. If a field differs, patch only the incorrect field and record the supporting source in the task report.

- [ ] **Step 3: Rewrite the Related Work opening**

Use this content after the verification gate:

```tex
Den Boer introduced the first card-based cryptographic protocol with the
five-card trick~\cite{denBoer1989}. The protocol uses five cards to compute
the AND of two secret bits with perfect security. Later protocols reduced the
number of cards and supported other functions~\cite{MizukiSone2009,
MizukiSone2012,KochWalzerHartel2015}.

Koch, Schrempp, and Kirsten encode bounded protocol spaces for software
bounded model checking~\cite{Koch2019}. Their method searches for protocols
and checks finite lower bounds. The present development proves reusable
group-action, execution, privacy, and mixing lemmas in \Rocq{}. The Kim
instance also connects a biased shuffle model to a concrete finite-step
bound~\cite{KimCetinkaya2025}.
```

If the verified source uses a narrower technical description than `two secret bits with perfect security`, preserve the priority sentence and narrow only the second sentence to match the source.

- [ ] **Step 4: Check the agreed priority scope and build**

Run:

```bash
rg -n 'first.*card-based|first work ever|first.*physical crypt|den Boer|denBoer1989' pgg-smc/paper-wadt2026/main.tex
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n 'Citation .* undefined|There were undefined references|Overfull \\[hv]box' main.log
```

Expected: Related Work says `first card-based cryptographic protocol`. It does not say `first work ever`, `first physical cryptography`, or `first secure computation`. The build exits 0 and the warning scan has no matches.

- [ ] **Step 5: Stage only the Related Work hunk and any verified metadata correction**

Run:

```bash
git add -p pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib
git diff --cached --check
git diff --cached -- pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib
git commit -m 'wadt2026: restore den Boer historical context'
```

Expected: the staged diff contains the Related Work opening and no unrelated bibliography or paper edits.

---

### Task 4: Run the worker's complete source, prose, and PDF audit

**Files:**
- Modify only if needed: `pgg-smc/paper-wadt2026/main.tex`
- Modify only if Task 3 found an error: `pgg-smc/paper-wadt2026/references.bib`
- Inspect: `pgg-smc/paper-wadt2026/main.pdf`

**Interfaces:**
- Consumes: Tasks 1 through 3 and the untouched user-owned baseline edits.
- Produces: a built paper that satisfies the approved revision spec and a report of any preserved red user notes outside this revision's scope.

- [ ] **Step 1: Check structure, source footnotes, and removed material**

Run:

```bash
rg -n '^\\section|^\\subsection|\\begin\{theorem\}|Formalized in \\path' pgg-smc/paper-wadt2026/main.tex
rg -n 'Methodology and Artifact|sec:method|Artifact availability|claim matrix|Print Assumptions' pgg-smc/paper-wadt2026/main.tex
```

Expected: the framework section has the two planned subsections. There are twelve theorem blocks and twelve source footnotes. The removed-material scan has no matches outside preserved `\greg{...}` notes.

- [ ] **Step 2: Run the hard prose scan**

Run:

```bash
rg -n -i '\b(we|our)\b|—|;|Moreover|Furthermore|Consequently|It is worth noting|delve|pivotal|crucial|groundbreaking|comprehensive|robust|seamless' pgg-smc/paper-wadt2026/main.tex | rg -v '\\greg\{'
```

Expected: inspect every match. Remove authorial plural voice, em dashes, prose semicolons, and formulaic AI wording introduced or exposed by this revision. Do not change mathematical punctuation or unrelated user-owned prose merely to silence the scan.

- [ ] **Step 3: Compare the new prose with the FORTE baseline**

Read the complete new framework section, artifact footnote, revised roadmap, and Related Work opening beside:

```bash
sed -n '1,240p' /Users/cheng-huiweng/Projects/aplas2024-poster/forteApr22/forteApr22.tex
```

Check sentence length, term density, transition directness, and use of concrete verbs. Rewrite any new sentence that is harder than the FORTE baseline without changing its claim.

- [ ] **Step 4: Recheck all three theorem mappings**

Run:

```bash
rg -n -A18 '\\begin\{theorem\}\[(Generic coalition privacy|Generic trace lifting|Data processing for finite distributions)' pgg-smc/paper-wadt2026/main.tex
sed -n '615,630p' pgg-smc/reconstruct/transitivity_privacy.v
sed -n '25,58p' pgg-smc/security/pgg_trace_secrecy.v
sed -n '62,82p' pgg-smc/security/pgg_collusion_bound.v
```

Expected: each paper statement has the same relevant hypotheses and conclusion as its named Rocq theorem. Every footnote path exists and every declaration name is exact.

- [ ] **Step 5: Force a complete PDF build and scan the log**

Run:

```bash
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n 'LaTeX Warning:.*undefined|Citation .* undefined|Reference .* undefined|There were undefined references|Overfull \\[hv]box' main.log
```

Expected: build exit 0. The log scan has no matches.

- [ ] **Step 6: Render the PDF and inspect the architecture page**

Run:

```bash
mkdir -p tmp/pdfs/wadt-framework-revision
pdftoppm -png -r 144 pgg-smc/paper-wadt2026/main.pdf tmp/pdfs/wadt-framework-revision/page
```

Open the rendered page that contains `Architecture of the group-parametric card-protocol framework`. Confirm:

- all seven box labels are readable at normal size
- all six arrows terminate at the intended records
- blue and green fills remain distinguishable
- the figure does not cross the text margins
- the caption contains only the figure name and style meanings
- the following `Generic Theorems` heading makes the subject change visible
- theorem-title footnotes are readable and not clipped

- [ ] **Step 7: Commit audit fixes only when they exist**

Run:

```bash
git add -p pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib
git diff --cached --check
git diff --cached
git commit -m 'wadt2026: pass framework revision audit'
```

If the audit makes no tracked edits, do not create an empty commit. Never stage generated files or pre-existing user changes.

---

### Task 5: Parent agent performs the required read-only verification

**Files:**
- Read: all of `pgg-smc/paper-wadt2026/main.tex`
- Read: `pgg-smc/paper-wadt2026/references.bib:1-14`
- Read: the three cited Rocq declarations
- Inspect: `pgg-smc/paper-wadt2026/main.pdf`
- Do not modify the paper or formalization in this task.

**Interfaces:**
- Consumes: the worker's task commits, citation evidence, complete source, and rebuilt PDF.
- Produces: an independent acceptance report or line-specific correction requests returned to the same paper-writing worker.

- [ ] **Step 1: Read the entire paper source in consecutive chunks**

Run:

```bash
sed -n '1,220p' pgg-smc/paper-wadt2026/main.tex
sed -n '221,440p' pgg-smc/paper-wadt2026/main.tex
sed -n '441,660p' pgg-smc/paper-wadt2026/main.tex
sed -n '661,900p' pgg-smc/paper-wadt2026/main.tex
```

Expected: the ranges cover the source through `\end{document}`. Do not rely on
the diff or worker summary. Record the preserved `\greg{...}` notes as
user-owned material outside this revision.

- [ ] **Step 2: Inspect each task commit for scope**

Resolve the three required task commits by their exact messages, then inspect
their complete paper diffs:

```bash
framework_commit="$(git rev-list -1 --grep='^wadt2026: present framework architecture and generic theorems$' HEAD)"
method_commit="$(git rev-list -1 --grep='^wadt2026: remove methodology narrative$' HEAD)"
related_commit="$(git rev-list -1 --grep='^wadt2026: restore den Boer historical context$' HEAD)"
audit_commit="$(git rev-list -1 --grep='^wadt2026: pass framework revision audit$' HEAD)"
git show --stat --oneline "$framework_commit" "$method_commit" "$related_commit"
git show --format=fuller "$framework_commit" "$method_commit" "$related_commit" -- pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib
if test -n "$audit_commit"; then git show --stat --oneline "$audit_commit"; fi
if test -n "$audit_commit"; then git show --format=fuller "$audit_commit" -- pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib; fi
```

Expected: all three variables are nonempty. The commits contain only approved
paper hunks and a verified den Boer metadata correction, if one was needed. No
`.v` file appears in any worker commit. The optional audit commit is inspected
when it exists.

- [ ] **Step 3: Verify the mathematical statements against Rocq**

Read each full declaration, including section variables and hypotheses. Check that:

- generic coalition privacy remains Boolean-prior generic and requires distinct encoded decks
- the trace theorem states both functional correspondence and cancellation
- data processing uses the repository's unhalved L1 convention
- no theorem body adds motivation, status, proof strategy, or unsupported scope

- [ ] **Step 4: Verify the full prose and structure against the design spec**

Confirm every acceptance criterion in:

```text
docs/superpowers/specs/2026-08-08-wadt2026-paper-framework-revision-design.md
```

Check especially the architecture-to-theorem transition, single-author voice, the one-sentence artifact footnote, retained AI-use acknowledgement, removed methodology material, and den Boer's limited priority scope.

- [ ] **Step 5: Rebuild and visually inspect the final PDF**

Run:

```bash
cd pgg-smc/paper-wadt2026
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n 'LaTeX Warning:.*undefined|Citation .* undefined|Reference .* undefined|There were undefined references|Overfull \\[hv]box' main.log
```

Inspect the architecture page and the pages containing the three new theorem blocks. Confirm readable typography, correct footnote placement, stable page breaks, and no clipped content.

- [ ] **Step 6: Return corrections to the same worker when needed**

Each correction must identify the file, current text, exact defect, and required claim or layout. The parent does not edit `main.tex`. The worker applies corrections, reruns Task 4, and reports a new commit. Repeat until all checks pass.

- [ ] **Step 7: Report completion without claiming ownership of formalization changes**

The final report lists:

- paper commit hashes
- whether `references.bib` changed and why
- build result and final page count
- architecture-page visual result
- all three theorem-to-Rocq mappings
- den Boer citation sources and the exact priority wording
- preserved user-owned `\greg{...}` notes
- confirmation that no `.v` file changed
