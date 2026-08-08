# WADT2026 Paper Restructure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Execute the approved spec `docs/superpowers/specs/2026-08-08-wadt2026-restructure-design.md`: two named headline theorems, narrative model opening with sequence diagram, framework bridge table, encoding and ramp figures, theorem re-leveling with formalization footnotes on every result, merged source table, all eight greg notes resolved.

**Architecture:** Single-file LaTeX restructure of `pgg-smc/paper-wadt2026/main.tex` plus one bibliography entry. Tasks run top-of-file downward. No commits until Task 5 (all greg notes live in Sections 1–2; committing earlier would commit notes, which is forbidden). Every edit uses unique anchor strings, not line numbers, because lines shift.

**Tech Stack:** LaTeX (llncs, TikZ, booktabs), latexmk, git, research-kb for citation verification.

**Compile command (used by every task):**
```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg/pgg-smc/paper-wadt2026 && latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
```
Expected: exit 0. On failure, read `main.log` around the first `!` line, fix, recompile.

**Verified source facts used below (do not re-derive):**
- `orbit_encode false` = deck (0,1,2,3,4,5,6,7); `orbit_encode true` = (0,1,2,4,3,5,6,7) (`pgl27_orbit.v:349-355`).
- Hearts are card values 0–3 (`is_heart c := val c < 4`, `pgl27_orbit.v:90`).
- Heart positions: D_0 → {0,1,2,3} = class false = harmonic; D_1 → {0,1,2,4} = class true = equianharmonic (orbit sizes 42/28, `orbit_encodeK`).
- `pgl27_endpoint_mixing` at `pgl27_mixing.v:909`; `pgl27_joint_mixing` at `pgl27_mixing.v:937`.
- All greg notes sit in Sections 1–2 (lines 83, 104, 106, 108, 132, 179, 180, 185, 198).

---

### Task 1: Preamble

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (preamble, lines 8–26 region)

- [ ] **Step 1: Add the TikZ brace library.** Edit:
```latex
OLD: \usetikzlibrary{arrows.meta,positioning}
NEW: \usetikzlibrary{arrows.meta,positioning,decorations.pathreplacing}
```

- [ ] **Step 2: Add the four named theorem environments.** Insert directly after the line `\newcolumntype{L}[1]{>{\raggedright\arraybackslash}p{#1}}`:
```latex
\spnewtheorem*{thmAinf}{Theorem A (informal)}{\bfseries}{\itshape}
\spnewtheorem*{thmBinf}{Theorem B (informal)}{\bfseries}{\itshape}
\spnewtheorem*{thmA}{Theorem A}{\bfseries}{\itshape}
\spnewtheorem*{thmB}{Theorem B}{\bfseries}{\itshape}
```
Constraint (spec D1): these step no counter. Never place `\label` inside them; all references to A and B are the literal words "Theorem A" / "Theorem B".

- [ ] **Step 3: Compile.** Run the compile command. Expected: exit 0 (environments defined but unused is fine).

### Task 2: Shamir citation

**Files:**
- Modify: `pgg-smc/paper-wadt2026/references.bib`

- [ ] **Step 1: Verify metadata via research-kb.** Check the kb for Shamir 1979 (`~/.claude/research-kb/kb.sh`); if absent, verify against the ACM DL (doi 10.1145/359168.359176) and save the slice with honest provenance. Confirm: CACM volume 22, number 11, pages 612–613, year 1979.

- [ ] **Step 2: Append the entry** to `references.bib`:
```bibtex
@article{Shamir1979,
  author  = {Adi Shamir},
  title   = {How to Share a Secret},
  journal = {Communications of the ACM},
  volume  = {22},
  number  = {11},
  pages   = {612--613},
  year    = {1979},
  doi     = {10.1145/359168.359176}
}
```
No other bibliography changes (spec verification item 4).

### Task 3: Section 1 — Introduction

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Section 1)

- [ ] **Step 1: Delete the accepted-abstract paragraph and its greg note.** Delete the block from `\greg{I want to delete the accepted abstract diff` through `and is not a result reported here.` inclusive (greg 83 + paragraph 84–89).

- [ ] **Step 2: Delete the model-dump paragraph and its three greg notes.** Delete the block from `\greg{It is like a sudden jump` through `composition across executions remain outside the model.` inclusive (greg 104/106/108 + paragraph 110–119). The one fact not surviving elsewhere ("no private inputs") is re-added in Task 4 Step 4.

- [ ] **Step 3: Insert the why-two-distributions paragraph.** Insert after the paragraph ending `word-shuffle mixing bound.` (the gap paragraph, before `There are three contributions`):
```latex
Two shuffle distributions organize the analysis. The uniform distribution on
the shuffle group is the ideal object of the security proofs. No dealer
samples a uniform group element in one physical move. A dealer instead
repeats simple cuts, and the repeated cuts follow a word distribution over
the generators of the group. The group parameters pay for this connection.
Transitivity of the action yields coalition privacy, and generation by a
small cut alphabet yields a finite implementable shuffle. The paper proves
the security results in the ideal model and then proves that the word
distribution approximates it.
```

- [ ] **Step 4: Insert the overall paragraph and the informal headline displays.** Insert directly after the paragraph from Step 3 (still before `There are three contributions`):
```latex
Overall, this work contributes a group-parametric framework whose main
instance carries two machine-checked security results.

\begin{thmAinf}
The $\PG$ instance recovers the secret from all eight endpoints for every
group element. Under the uniform shuffle distribution, with a uniform
Boolean secret and the fixed representative dealer, it has recovery
parameters $(t,r,n)=(3,7,8)$ and perfect view and executed-trace privacy
against every passive coalition of at most three
players.\footnotemark
\end{thmAinf}
\footnotetext{Formal statement at the end of
Section~\ref{sec:exact}. The constituent formalized results are
\coqin{pgl27\_run\_recovers}, \coqin{pgl27\_reveal\_ambiguous},
\coqin{pgl27\_seven\_reveal\_class}, \coqin{pgl27\_view\_leak\_k4},
\coqin{pgl27\_view\_indep}, and \coqin{pgl27\_coalition\_trace\_secrecy} in
\path{pgg-smc/instances/pgl27}.}

\begin{thmBinf}
The 200-letter word shuffle over the five generator letters is within
unhalved $L_1$ distance $2^{-40}$ of the uniform shuffle distribution. For
the fixed representative dealer, the coalition view distributions at the two
secrets are within unhalved $L_1$ distance $2^{-39}$ for every passive
coalition of at most three players, and the executed coalition traces
satisfy the same bound. Executed correctness holds for every
word.\footnotemark
\end{thmBinf}
\footnotetext{Formal statement at the end of
Section~\ref{sec:mixing}. The constituent formalized results are
\coqin{pgl27\_word\_mixing}, \coqin{pgl27\_word\_view\_indist},
\coqin{pgl27\_word\_trace\_indist}, and \coqin{pgl27\_word\_run\_recovers} in
\path{pgg-smc/instances/pgl27}.}
```
Hedge discipline (spec §4): A carries prior + dealer + passive; B carries dealer + passive, no prior, distributional phrasing only.

- [ ] **Step 5: Replace the roadmap paragraph.** Replace the paragraph starting `Section~\ref{sec:model} fixes the two distributions` (through `future directions.`) with:
```latex
Section~\ref{sec:model} fixes the protocol flow, the two distributions, and
the security scope. Section~\ref{sec:framework} presents the framework
components used by the proofs. Sections~\ref{sec:pgl} and~\ref{sec:exact}
give the $\PG$ construction and its uniform-shuffle results, ending in
Theorem A. Section~\ref{sec:mixing} proves the word-shuffle results, ending
in Theorem B. Section~\ref{sec:instances} compares the sibling instances and
states the trust base. Section~\ref{sec:related} places the results among
related work. Section~\ref{sec:conclusion} states the remaining extensions
and other future directions.
```

- [ ] **Step 6: Compile.** Expected: exit 0.

### Task 4: Section 2 — Model

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Section 2)

- [ ] **Step 1: Insert the narrative and the sequence diagram at the section top.** Insert directly after `\section{Protocol and Security Model}\label{sec:model}`, and delete the greg note `\greg{Need to start from the flow diagram...}` (greg 132) that currently follows:
```latex
A run of the protocol handles one secret bit and eight face-down cards. A
dealer encodes the secret as a valid arrangement of the eight cards. The
dealer then samples a shuffle from a finite group and rearranges the deck by
its permutation action. Each of eight players receives the card at one
position. The players reveal their cards to a verifier, and the verifier
decodes the secret from the revealed arrangement. Figure~\ref{fig:run}
shows this flow.

\begin{figure}[H]
  \centering
  \resizebox{.92\linewidth}{!}{%
  \begin{tikzpicture}[
     actor/.style={draw,rounded corners,fill=blue!12,minimum width=16mm,
       minimum height=7mm,font=\small\bfseries},
     life/.style={dashed,gray!70},
     msg/.style={-{Latex},thick},
     act/.style={draw,rounded corners,fill=orange!14,inner sep=3pt,
       align=center,font=\footnotesize},
     lbl/.style={midway,above,font=\footnotesize}]
    \node[actor] (D)  at (0,0)    {Dealer};
    \node[actor] (P)  at (5.5,0)  {Players};
    \node[actor] (V)  at (10.8,0) {Verifier};
    \draw[decorate,decoration={brace,amplitude=5pt,raise=2pt}]
      (4.2,0.45) -- (6.8,0.45)
      node[midway,above=5pt,font=\footnotesize]{eight players, one card each};
    \draw[life] (0,-0.4)    -- (0,-4.6);
    \draw[life] (5.5,-0.4)  -- (5.5,-4.6);
    \draw[life] (10.8,-0.4) -- (10.8,-4.6);
    \node[act,anchor=west] at (0.15,-0.85)
      {encode secret $s$\\ as the deck $D_s$};
    \node[act,anchor=west] at (0.15,-1.95)
      {sample a shuffle $g$,\\ rearrange to $\rho(g)D_s$};
    \draw[msg] (0,-2.75) -- (5.5,-2.75) node[lbl]{deal one card per position};
    \draw[msg] (5.5,-3.45) -- (10.8,-3.45) node[lbl]{reveal all cards};
    \node[act,anchor=east] at (10.65,-4.15)
      {decode the class of the\\ heart positions $\to s$};
  \end{tikzpicture}}
  \caption{One protocol run. The shuffle $g$ is drawn from the uniform
  distribution $U_G$ in the uniform-shuffle model and from the word
  distribution $\worddist$ in the word-shuffle model.}
  \label{fig:run}
\end{figure}

Security rests on the shuffle alone. A player sees one card, and a
coalition sees the cards at its positions. The shuffle spreads every small
coalition view over many arrangements, and the privacy theorems make this
spreading exact. The rest of this section states the same flow as
probability distributions.
```

- [ ] **Step 2: Keep the formal-data and views paragraphs unchanged** (from `The framework describes a protocol by the data` through `It therefore learns $S$ by design.`). Verify no greg note remains between them.

- [ ] **Step 3: Rewrite the dealer-variants paragraph in generic vocabulary.** Replace the paragraph from `The primary uniform-shuffle distribution samples a uniform Boolean secret` through `use a uniform Boolean prior.` INCLUDING its two `\footnote{...}` calls (they name `pgl27P`, `orbit\_encode`, `pgl27P\_alldecks`; the footnotes are re-created in Task 7) with:
```latex
The primary execution distribution samples a uniform Boolean secret and
deals one fixed representative arrangement $D_s$ for each secret $s$. It
then applies an independent uniform shuffle. This fixed-representative
dealer is the dealer of the headline theorems. An all-decks dealer instead
samples a uniform valid arrangement in the selected secret class before the
shuffle. Both execution distributions use a uniform Boolean prior.
```

- [ ] **Step 4: Rewrite the security-scope sentences positively.** Keep the block from `The security theorems concern passive, honest-but-curious adversaries.` through the display `H(S\mid T_C)=H(S).` and its `\label{eq:trace-privacy}` VERBATIM (spec audit finding 1: these are the paper's only privacy definitions). Delete the two greg notes (`\greg{Instead of ...}` and `\greg{And it is why ...}`) and replace only the paragraph `The PGL protocol has no private player inputs. Active deviation, security after the verifier's reveal, and composition across executions are outside the model.` with:
```latex
The protected object is a dealt secret, as in a secret-sharing
scheme~\cite{Shamir1979}. The dealer holds the secret, the players hold
card observations in place of shares, and privacy bounds what coalitions of
curious players learn. The protocol has no private player inputs. Active
deviation, security after the verifier's reveal, and composition across
executions are outside the model.
```

- [ ] **Step 5: Word-model motivation and TV meaning.** Delete the greg note `\greg{It is a sudden mentioning of finite-step model...}` and insert before `The word-shuffle model replaces $U_G$ by $\mu^{*L}$.`:
```latex
The word-shuffle model describes the dealer of Figure~\ref{fig:run}
performing the shuffle as a sequence of physical cuts.
```
Delete the greg note `\greg{This is correct but not useful description for a reader...}`. Then insert after the sentence `Thus an $L_1$ bound of $2^{-40}$ gives a halved total variation bound of $2^{-41}$.`:
```latex
In operational terms, a total variation bound of $2^{-41}$ means that no
observer, whatever test they apply, distinguishes the word shuffle from the
uniform shuffle with advantage above $2^{-41}$.
```

- [ ] **Step 6: Move the dealer-program footnote out.** In the unobserved-word paragraph, delete the `\footnote{The dealer program is \coqin{exchange\_dealer} and the $\PG$ witness is the singleton cut list in \coqin{pgl27\_dealer\_run}.}` (re-created in Task 7 Step 1).

- [ ] **Step 7: Recaption and relabel the models figure.** In the `fig:models` figure, edit two node texts and the caption:
```latex
OLD node: {perfect coalition view\\and trace theorems}
NEW node: {Theorem A: perfect view\\and trace privacy}

OLD node: {coalition view and\\trace privacy at $2^{-39}$}
NEW node: {Theorem B: view and\\trace bounds at $2^{-39}$}

OLD caption: The uniform-shuffle and word-shuffle proof paths. The lower path transports
  the mixing certificate to coalition-view and trace privacy.
NEW caption: The two proof paths and the two headline theorems. The upper
  path ends in Theorem A. The lower path transports the mixing certificate
  to Theorem B.
```

- [ ] **Step 8: Remove the greg macro.** All eight notes are now deleted; verify then remove the macro line:
```bash
grep -c 'greg' pgg-smc/paper-wadt2026/main.tex
```
Expected: `1` (only the `\def\greg` line). Delete the line `\def\greg#1{{\color{red}[NB(greg):#1]}}`. Re-run the grep; expected `0`.

- [ ] **Step 9: Compile.** Expected: exit 0. Check in the PDF that the sequence diagram renders on the Section 2 opening page before the data display (spec verification item 6).

### Task 5: First commit (Sections 1–2 + preamble + bib)

- [ ] **Step 1: Confirm no greg content.** `grep -c 'greg' main.tex` returns 0 (precondition for committing main.tex at all).

- [ ] **Step 2: Commit.**
```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg && \
git add pgg-smc/paper-wadt2026/main.tex pgg-smc/paper-wadt2026/references.bib && \
git commit -m "wadt2026: intro headline theorems, model narrative and sequence diagram (spec T1-T4)"
```

### Task 6: Section 3 — Framework

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Section 3)

- [ ] **Step 1: Insert bridge sentence + table, interpreter and instantiation paragraphs.** Replace the paragraph `A protocol instance supplies an action, a shuffle-security bound, and a decoder. The framework packages these components and uses them in one executable protocol. Its finite algebraic structures use Mathematical Components~\cite{MathComp}.` with:
```latex
A protocol instance supplies an action, a shuffle-security bound, and a
decoder. The framework packages these components and uses them in one
executable protocol. Its finite algebraic structures use Mathematical
Components~\cite{MathComp}. The framework records carry the data of
Equation~\ref{eq:model-data} into that executable protocol, and
Table~\ref{tab:bridge} maps each datum to its record role and to the values
the $\PG$ instance supplies.

\begin{table}[t]
  \centering
  \small
  \begin{tabular}{@{}L{.26\linewidth}L{.36\linewidth}L{.30\linewidth}@{}}
    \toprule
    Model datum & Record role & $\PG$ instance supplies \\
    \midrule
    layout of a run & dealer, player, and verifier processes & eight
      players, one card each \\
    $(G,\rho)$ with $\mu$ or $U_G$ & endpoint bound for the shuffle
      distribution & three-transitive action, word bound \\
    decoder & reconstruction against the action & orbit-class decoder \\
    all of the above & one packaged protocol instance & the $\PG$ profile \\
    \bottomrule
  \end{tabular}
  \caption{From model data to framework records. In the sources the four
  roles are \coqin{PGGInterface}, \coqin{SecurityWitness},
  \coqin{ReconPlug}, and \coqin{MonodromyProfile}.}
  \label{tab:bridge}
\end{table}

A small process interpreter executes the layout record. It originates in
the earlier FORTE development~\cite{WengEtAl2025} and produces the executed
traces of Section~\ref{sec:model}. An instance supplies the third column of
Table~\ref{tab:bridge} and receives the executable protocol together with
the generic theorems below. Section~\ref{sec:pgl} is the worked
instantiation.
```

- [ ] **Step 2: Relabel the architecture figure by role.** In `fig:framework-architecture`, replace the node texts and caption:
```latex
OLD: {\textbf{MonodromyProfile}}
NEW: {\textbf{profile bundle}}
OLD: {\textbf{PGGInterface}\\protocol layout}
NEW: {\textbf{protocol layout}\\dealer, players, verifier}
OLD: {\textbf{SecurityWitness}\\endpoint bound}
NEW: {\textbf{shuffle-security bound}\\endpoint bound}
OLD: {\textbf{ReconPlug}\\reconstruction}
NEW: {\textbf{reconstruction}\\group action to decoder}
OLD: {\textbf{SecurityExact}\\\textbf{SecurityAsymptotic}}
NEW: {exact and asymptotic\\security evidence}
OLD: {\textbf{ThresholdScheme}}
NEW: {threshold sharing}
OLD: {\textbf{InputEncoding}}
NEW: {input encoding}
OLD caption: Architecture of the group-parametric card-protocol framework.
  Blue boxes denote the profile and its three component records. Green boxes
  denote supporting records. Arrows denote dependencies.
NEW caption: Architecture of the group-parametric card-protocol framework.
  Blue boxes denote the profile bundle and its three component records
  (\coqin{MonodromyProfile}, \coqin{PGGInterface}, \coqin{SecurityWitness},
  \coqin{ReconPlug}). Green boxes denote supporting records
  (\coqin{SecurityExact}, \coqin{SecurityAsymptotic},
  \coqin{ThresholdScheme}, \coqin{InputEncoding}). Arrows denote
  dependencies.
```

- [ ] **Step 3: Trim the now-redundant record glosses.** Replace the two short paragraphs `\coqin{PGGInterface} gives the dealer, player, and verifier layout. ... packages these three components.` and `The supporting records refine individual components. ... when a protocol needs them.` and the transition `The records above specify one protocol instance. The next subsection turns from the architecture to the generic theorems derived from these records.` with:
```latex
The supporting records refine individual components. Exact and asymptotic
security records justify endpoint bounds, a threshold scheme supplies
sharing and reconstruction data, and an input encoding adds committed
inputs when a protocol needs them. The next subsection states the generic
theorems derived from these records.
```

- [ ] **Step 4: Per-theorem lead-ins.** Insert before the Generic coalition privacy theorem:
```latex
The first generic theorem yields coalition privacy from transitivity. An
instance discharges its hypothesis by exhibiting a $t$-transitive action on
decks of distinct cards, as Section~\ref{sec:pgl} does for $t=3$.
```
Add `\label{thm:generic-privacy}` to that theorem (after its `[...]` title). Insert before the Generic trace lifting theorem:
```latex
The second theorem moves view independence to executed traces.
```
Insert before the Data processing theorem:
```latex
The third theorem transfers a bound between shuffle distributions to any
observable computed from them.
```
Delete the post-hoc paragraph `The first theorem supplies the perfect-privacy view argument used by the PGL instance. The second moves that result to an executed trace. The third transfers a group-level mixing bound to card endpoints.`

- [ ] **Step 5: Compile, then commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex && git commit -m "wadt2026: framework bridge table, role-labeled architecture, generic theorem lead-ins (spec T5)"
```

### Task 7: Sections 4–5 footnote relocations and Section 4 restructure

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Sections 4, 5)

- [ ] **Step 1: Re-create the three relocated footnotes in Section 5.** (Deleted from Section 2 in Task 4 Steps 3 and 6.) In Section 5.1, append to the sentence `The interpreter deals $D_s$, applies an allowed shuffle, and sends one card to each of eight players.`:
```latex
\footnote{The dealer program is \coqin{exchange\_dealer} and the $\PG$
witness is the singleton cut list in \coqin{pgl27\_dealer\_run}.}
```
In Section 5.2, append to the sentence `It deals the fixed representative $D_S$ and samples an independent shuffle $g\leftarrow U_G$.`:
```latex
\footnote{The execution distribution is \coqin{pgl27P} and the
representative is the formal orbit encoder \coqin{orbit\_encode}.}
```
Append to the all-decks lead-in sentence `It then applies an independent uniform $\PG$ shuffle.` (the prose before the all-decks proposition):
```latex
\footnote{The all-decks distribution is \coqin{pgl27P\_alldecks}.}
```

- [ ] **Step 2: Section 4 opening sentence.** Insert directly after `\section{The \texorpdfstring{$\PG$}{PGL(2,7)} Construction}\label{sec:pgl}`:
```latex
This section supplies the instance column of Table~\ref{tab:bridge}. The
group is $\PG$, the action permutes the eight projective points, the
shuffle distribution draws uniform generator letters, and the decoder reads
the orbit class.
```

- [ ] **Step 3: Demote the three Section 4 theorems.** Change `\begin{theorem}[Orbit encoder\footnotemark]` → `\begin{lemma}[Orbit encoder\footnotemark]` with matching `\end{lemma}`; same for `[Orbit split\footnotemark]\label{thm:orbit-split}` and `[Three-transitivity\footnotemark]\label{thm:three-transitive}`. Labels keep their existing names (invisible); footnotes unchanged.

- [ ] **Step 4: Insert the encoding example figure** after the paragraph ending `The encoder chooses one fixed valid arrangement from each class.`:
```latex
\begin{figure}[t]
  \centering
  \begin{tikzpicture}[every node/.style={font=\small},
      card/.style={draw,minimum width=7mm,minimum height=9mm,inner sep=1pt},
      heart/.style={card,fill=red!15}]
    \node at (-1.3,0) {$D_0$};
    \foreach \p/\c/\s in {0/0/heart,1/1/heart,2/2/heart,3/3/heart,
                          4/4/card,5/5/card,6/6/card,7/7/card}
      \node[\s] at (\p*0.85,0) {$\c$};
    \node at (-1.3,-1.6) {$D_1$};
    \foreach \p/\c/\s in {0/0/heart,1/1/heart,2/2/heart,3/4/card,
                          4/3/heart,5/5/card,6/6/card,7/7/card}
      \node[\s] at (\p*0.85,-1.6) {$\c$};
    \foreach \p in {0,...,7}
      \node[gray] at (\p*0.85,0.85) {\p};
  \end{tikzpicture}
  \caption{The two encoded representatives. Gray labels are card positions,
  boxed numbers are card values, and shaded cards are the four hearts, the
  values below four. The heart positions of $D_0$ form the harmonic subset
  $\{0,1,2,3\}$ and those of $D_1$ form the equianharmonic subset
  $\{0,1,2,4\}$. The secret is this orbit class.}
  \label{fig:encoding}
\end{figure}
```
Fidelity note (spec verification item 10): these rows are exactly `orbit_encode false` = (0,1,2,3,4,5,6,7) and `orbit_encode true` = (0,1,2,4,3,5,6,7) from `pgl27_orbit.v:349-355`, hearts = values below four from `pgl27_orbit.v:90`. Add one referencing sentence after the encoder-Lemma (formerly theorem): `Figure~\ref{fig:encoding} shows both representatives.`

- [ ] **Step 5: Discharge sentence.** In the paragraph after the three-transitivity lemma, replace `Theorem~\ref{thm:three-transitive} makes every ordered view of at most three positions uniform under $U_G$. It therefore supplies the group-theoretic premise for coalition privacy.` with:
```latex
Lemma~\ref{thm:three-transitive} makes every ordered view of at most three
positions uniform under $U_G$. It discharges the hypothesis of
Theorem~\ref{thm:generic-privacy} at $t=3$ and thereby supplies the
group-theoretic premise for coalition privacy.
```

- [ ] **Step 6: Remove the Section 4 source table.** Delete the whole `\begin{table}...\end{table}` block with caption `Source index for the PGL construction.` (`tab:pgl-source`). Insert in its place the sentence:
```latex
Table~\ref{tab:source-index} indexes the formal sources for this section.
```

- [ ] **Step 7: Compile, then commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex && git commit -m "wadt2026: PGL section lemmas, encoding example figure, discharge sentence (spec T6)"
```

### Task 8: Section 5 — Uniform-shuffle results and Theorem A

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Section 5)

- [ ] **Step 1: Section opener.** Insert directly after `\section{Correctness, Recovery, and Uniform-Shuffle Privacy}\label{sec:exact}`:
```latex
This section follows the upper path of Figure~\ref{fig:models} and ends in
Theorem A.
```

- [ ] **Step 2: Demote correctness.** Delete the line `\Needspace{10\baselineskip}` (stale sizing). Change `\begin{theorem}[Executed correctness\footnotemark]\label{thm:pgl-correctness}` → `\begin{proposition}[Executed correctness\footnotemark]\label{thm:pgl-correctness}` with matching `\end{proposition}`. Footnote unchanged.

- [ ] **Step 3: Restrict and retitle the ramp.** Insert before the ramp environment (after the paragraph ending `consistent with valid arrangements from both secret classes.`):
```latex
Three parameters summarize the instance. The privacy threshold $t$ is the
largest coalition size with perfect privacy, the recovery threshold $r$ is
the least number of revealed positions that always determines the secret
class, and $n$ is the number of card positions.
```
Replace the whole ramp theorem environment (from `\begin{theorem}[Recovery ramp\footnotemark]\label{thm:recovery-ramp}` through its `\end{theorem}`) with:
```latex
\begin{proposition}[Recovery ramp and sharpness\footnotemark]\label{thm:recovery-ramp}
\footnotetext{Formalized in \path{pgg-smc/instances/pgl27/pgl27_recovery.v}
as \coqin{pgl27\_reveal\_ambiguous} and
\coqin{pgl27\_seven\_reveal\_class}, and in
\path{pgg-smc/instances/pgl27/pgl27_secrecy.v} as
\coqin{pgl27\_view\_dep\_k4} and \coqin{pgl27\_view\_leak\_k4}.}
Every reveal set of at most six positions is compatible with valid
arrangements from both secret classes, and every set of seven revealed
positions determines the secret class. The view of the coalition of the
four heart positions in the identity arrangement depends on the secret and
has positive mutual information with it.
\end{proposition}
```
(The privacy clause `t=3` is asserted only by the privacy proposition and Theorem A; spec D4.)

- [ ] **Step 4: Insert the ramp figure** after the proposition from Step 3:
```latex
\begin{figure}[t]
  \centering
  \begin{tikzpicture}[every node/.style={font=\footnotesize},xscale=1.15]
    \draw[-{Latex}] (-0.4,0) -- (8.6,0) node[right] {size};
    \foreach \x in {0,...,8}
      \draw (\x,-0.07) -- (\x,0.07) node[above=1pt] {\x};
    \node[left] at (-0.5,-0.7) {coalition views};
    \draw[very thick] (0,-0.7) -- (3,-0.7)
      node[midway,below=2pt] {perfect privacy};
    \node at (4,-0.7) {$\times$};
    \node[below=2pt] at (4,-0.7) {leaking witness};
    \node[left] at (-0.5,-1.7) {reveal sets};
    \draw[very thick] (0,-1.7) -- (6,-1.7)
      node[midway,below=2pt] {both classes possible};
    \draw[very thick] (7,-1.7) -- (8,-1.7)
      node[midway,below=2pt] {class determined};
  \end{tikzpicture}
  \caption{The recovery ramp $(t,r,n)=(3,7,8)$. The view track shows
  perfect privacy for coalitions of at most three positions and the leaking
  four-position witness. The reveal track shows ambiguity through six
  positions and determination from seven.}
  \label{fig:ramp}
\end{figure}
```
Marks must match the proposition clauses exactly: 3, 4, 6, 7, 8 (spec verification item 10).

- [ ] **Step 5: Trim the sharpness prose.** Replace `The four-position result uses one fixed coalition, namely the four heart positions in the identity arrangement. The formal development proves that its view depends on the secret and that its mutual information with the secret is positive. This witness makes the privacy cutoff three sharp.` with:
```latex
The witness coalition makes the privacy cutoff three sharp.
```
(Remaining sentences of that paragraph stay.)

- [ ] **Step 6: Remove the two Section 5 source tables.** Delete the `\begin{table}...\end{table}` blocks captioned `Source index for correctness and recovery.` (`tab:recovery-source`) and `Source index for perfect view and trace privacy.` (`tab:privacy-source`).

- [ ] **Step 7: Demote the three privacy theorems.** Change each of `\begin{theorem}[Perfect privacy for the fixed dealer\footnotemark]`, `\begin{theorem}[All-decks perfect privacy\footnotemark]`, `\begin{theorem}[Shuffle-free deck privacy\footnotemark]` to `\begin{proposition}[...]` with matching `\end{proposition}`. Footnotes unchanged. Insert before the all-decks proposition's lead-in sentence `The all-decks dealer tests whether the fixed representative hides a special choice.`:
```latex
Two further dealers act as robustness checks on the fixed representative.
```

- [ ] **Step 8: Replace the trust-base paragraph with Theorem A.** Replace the paragraph `The probability, view, and trace theorems use three classical principles ... including finite computations performed by its virtual machine.` (moved to Section 7 in Task 10) with:
```latex
The propositions of this section combine into the first headline theorem.

\begin{thmA}
The $\PG$ instance recovers the secret from all eight endpoints for every
group element.\footnotemark{} Under the uniform Boolean prior, the fixed
representative dealer, and an independent uniform $\PG$ shuffle, the
instance has recovery parameters
\[
  (t,r,n)=(3,7,8),
\]
and for every passive coalition $C$ with $\lvert C\rvert\leq3$,
\[
  S\mathrel{\perp}V_C
  \quad\text{and}\quad
  H(S\mid T_C)=H(S).
\]
\end{thmA}
\footnotetext{This statement is the conjunction of the following formalized
results: \coqin{pgl27\_run\_recovers} in
\path{pgg-smc/instances/pgl27/pgl27_run.v}, \coqin{pgl27\_reveal\_ambiguous}
and \coqin{pgl27\_seven\_reveal\_class} in
\path{pgg-smc/instances/pgl27/pgl27_recovery.v},
\coqin{pgl27\_view\_leak\_k4} and \coqin{pgl27\_view\_indep} in
\path{pgg-smc/instances/pgl27/pgl27_secrecy.v}, and
\coqin{pgl27\_coalition\_trace\_secrecy} in
\path{pgg-smc/instances/pgl27/pgl27_trace.v}.}

The trust base for these results is stated in
Section~\ref{sec:instances}, and Table~\ref{tab:source-index} indexes the
formal sources.
```

- [ ] **Step 9: Compile, then commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex && git commit -m "wadt2026: section 5 propositions, ramp figure, Theorem A capstone (spec T7)"
```

### Task 9: Section 6 — Word-shuffle results and Theorem B

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Section 6)

- [ ] **Step 1: Section opener.** Insert directly after `\section{Word-Shuffle Approximation of the Uniform-Shuffle Model}\label{sec:mixing}`:
```latex
The word-shuffle model of Section~\ref{sec:model} replaces the uniform
shuffle by the evaluated word of physical cuts. This section certifies that
the two shuffle distributions are close and transports the certificate to
the security observables, ending in Theorem B.
```

- [ ] **Step 2: Demote the mixing bound.** Change `\begin{theorem}[Word-shuffle mixing bound\footnotemark]\label{thm:pgl-mixing}` → `\begin{lemma}[Word-shuffle mixing bound\footnotemark]\label{thm:pgl-mixing}` with matching `\end{lemma}`. Footnote unchanged.

- [ ] **Step 3: Promote the endpoint transfer to a Lemma.** Replace the prose from `The first transfer maps each permutation to the endpoint of one fixed card.` through the sentence `The uniform group action makes the second endpoint distribution uniform on the eight positions.` with:
```latex
The first transfer maps each permutation to the endpoint of one fixed card.

\begin{lemma}[Endpoint transfer\footnotemark]\label{lem:endpoint-transfer}
\footnotetext{Formalized in \path{pgg-smc/instances/pgl27/pgl27_mixing.v}
as \coqin{pgl27\_endpoint\_mixing}.}
By the $L_1$ data-processing inequality, for every card position $i$,
\begin{equation}
  \left\lVert
    (g\mapsto \rho(g)i)_\#\mu^{*200}
    -(g\mapsto \rho(g)i)_\#U_G
  \right\rVert_1
  \leq 2^{-40}.
  \label{eq:endpoint-transfer}
\end{equation}
\end{lemma}

The uniform group action makes the second endpoint distribution uniform on
the eight positions.
```

- [ ] **Step 4: Promote the product transfer to a Lemma.** Replace the prose from `The second transfer adds a secret prior without changing the distance.` through the equation block labeled `eq:product-transfer` with:
```latex
The second transfer adds a secret prior without changing the distance.

\begin{lemma}[Secret-prior product transfer\footnotemark]\label{lem:product-transfer}
\footnotetext{Formalized in \path{pgg-smc/instances/pgl27/pgl27_mixing.v}
as \coqin{pgl27\_joint\_mixing}.}
Let $\pi$ be any distribution on Boolean secrets. Then
\begin{equation}
  \left\lVert
    \pi\mathbin{\times}\mu^{*200}
    -\pi\mathbin{\times}U_G
  \right\rVert_1
  \leq 2^{-40}.
  \label{eq:product-transfer}
\end{equation}
\end{lemma}
```
Keep the following prose `Equation~\ref{eq:product-transfer} compares two distributions on a secret and a shuffle. ... They are not separate mixing certificates.` unchanged. In the TV-restatement footnote `\footnote{The source results are \coqin{pgl27\_word\_mixing}, \coqin{pgl27\_endpoint\_mixing}, and \coqin{pgl27\_joint\_mixing}. ...}`, delete the whole footnote (its three names now live on the Lemma titles).

- [ ] **Step 5: Fold word privacy into Theorem B.** Replace the theorem environment `\begin{theorem}[Word-shuffle coalition privacy\footnotemark]\label{thm:word-privacy}` through its `\end{theorem}` (including its `\footnotetext`) and the preceding sentence `The proved chain reaches group-distribution proximity, every single-card marginal, and the product with any secret prior. Two transport theorems carry the certificate to the security observables.` with:
```latex
The proved chain reaches group-distribution proximity, every single-card
marginal, and the product with any secret prior. Transport through the
protocol interpreter turns the certificate into the second headline
theorem.

\begin{thmB}
Let $\mu$ be uniform on the five-letter symmetric generator
tuple.\footnotemark{} Then
\[
  \left\lVert \mu^{*200}-U_G\right\rVert_1 \leq 2^{-40}.
\]
For the fixed representative dealer, every passive coalition $C$ with
$\lvert C\rvert\leq3$, and all secrets $s,s'\in\{0,1\}$, writing $V_C(s,g)$
for the coalition view at dealt secret $s$ and shuffle $g$,
\begin{equation}
  \left\lVert
    (g\mapsto V_C(s,g))_\#\mu^{*200}
    -(g\mapsto V_C(s',g))_\#\mu^{*200}
  \right\rVert_1
  \leq 2^{-39},
  \label{eq:word-view-privacy}
\end{equation}
and the executed coalition trace satisfies the same bound. Decoding all
eight endpoints returns the dealt secret for every word.
\end{thmB}
\footnotetext{This statement is the conjunction of the following formalized
results: \coqin{pgl27\_word\_mixing} in
\path{pgg-smc/instances/pgl27/pgl27_mixing.v}, and
\coqin{pgl27\_word\_view\_indist}, \coqin{pgl27\_word\_trace\_indist}, and
\coqin{pgl27\_word\_run\_recovers} in
\path{pgg-smc/instances/pgl27/pgl27_word_privacy.v}.}
```
Note: `thm:pgl-mixing`'s displayed equation keeps the label `eq:pgl-mixing`; Theorem B's first display carries no label (the mixing Lemma owns the labeled statement). The proof-sketch paragraph `The proof is a triangle inequality through the uniform group distribution. ...` stays, as does its companion footnote naming `pgl27\_view\_mixing`.

- [ ] **Step 6: Section close.** After the scope paragraph ending `that the product-distribution transfer does not reach.`, append:
```latex
The trust base for these results is stated in
Section~\ref{sec:instances}, and the mixing-transfers group of
Table~\ref{tab:source-index} indexes the formal sources.
```

- [ ] **Step 7: Also fix the correctness cross-reference.** In Section 5.1's paragraph `A corollary instantiates the executed run at the evaluated 200-letter word.`, leave the footnote naming `pgl27\_word\_run\_recovers` unchanged (it is now also cited by Theorem B; duplication across footnotes is intended).

- [ ] **Step 8: Compile, then commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex && git commit -m "wadt2026: section 6 lemmas, transfer lemmas with footnotes, Theorem B capstone (spec T8)"
```

### Task 10: Section 7 — Instances, trust base, merged source table

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (Section 7)

- [ ] **Step 1: Reorder the opener.** Replace `The repository contains four sibling instances. They exercise different parts of the framework. Table~\ref{tab:instances} records the proved coverage.` with:
```latex
The framework's value shows in which arguments transfer across instances
unchanged and which need instance-specific finite or spectral evidence.
Four sibling instances exercise different parts of the framework alongside
the $\PG$ instance, and Table~\ref{tab:instances} records the proved
coverage.
```
(Keep the two following sentences about table semantics unchanged.) In the closing paragraph, delete the sentence `These instances show which proofs use only the common interfaces and which proofs need instance-specific finite or spectral evidence.` (its point moved to the opener; the other sentences of that paragraph stay).

- [ ] **Step 2: Insert the consolidated trust base** after the `tab:instances` table environment:
```latex
The probability, view, and trace results use three classical principles
from the MathComp probability stack: propositional extensionality,
dependent functional extensionality, and constructive indefinite
description. The $S_5$ and $S_5\times S_5$ mixing bounds additionally
import a Rayleigh-quotient premise as an axiom. The $\PG$ group, orbit,
cardinality, correctness, and recovery results are closed under the global
context. The \Rocq{} kernel checks all accepted proof terms, including
finite computations performed by its virtual machine.
```

- [ ] **Step 3: Insert the merged source table** at the section end (after the closing per-instance paragraph):
```latex
\begin{table}[t]
  \centering
  \small
  \begin{tabular}{p{.43\linewidth}p{.49\linewidth}}
    \toprule
    Mathematical statement & Rocq source name \\
    \midrule
    \multicolumn{2}{@{}l}{\emph{Construction}} \\
    three-transitivity & \coqin{pgl27\_3transitive} \\
    equianharmonic and harmonic counts & \coqin{orbit\_class\_split},
      \coqin{orbit\_class\_split\_complement} \\
    encoder returns its class & \coqin{orbit\_encodeK} \\
    group order & \coqin{pgl27\_card} \\
    \midrule
    \multicolumn{2}{@{}l}{\emph{Correctness and recovery}} \\
    executed class recovery & \coqin{pgl27\_run\_recovers\_class} \\
    seven cards determine deck and class &
      \coqin{pgl27\_seven\_reveal\_determines},
      \coqin{pgl27\_seven\_reveal\_class} \\
    at most six cards remain ambiguous &
      \coqin{pgl27\_six\_reveal\_ambiguous},
      \coqin{pgl27\_reveal\_ambiguous} \\
    fixed four-card dependence and leakage &
      \coqin{pgl27\_view\_dep\_k4}, \coqin{pgl27\_view\_leak\_k4} \\
    \midrule
    \multicolumn{2}{@{}l}{\emph{Privacy}} \\
    fixed representative views &
      \coqin{pgl27\_view\_indep}, \coqin{pgl27\_view\_leakage\_le} \\
    fixed representative traces &
      \coqin{pgl27\_trace\_secrecy},
      \coqin{pgl27\_coalition\_trace\_secrecy} \\
    all-decks views and traces &
      \coqin{pgl27\_view\_indep\_alldecks},
      \coqin{pgl27\_alldecks\_trace\_secrecy},
      \coqin{pgl27\_alldecks\_coalition\_secrecy} \\
    shuffle-free views and traces &
      \coqin{pgl27\_view\_indep\_deck\_prior},
      \coqin{pgl27\_deck\_trace\_secrecy},
      \coqin{pgl27\_deck\_coalition\_secrecy} \\
    \midrule
    \multicolumn{2}{@{}l}{\emph{Mixing and transfers}} \\
    word mixing certificate & \coqin{pgl27\_word\_mixing} \\
    endpoint and product transfers &
      \coqin{pgl27\_endpoint\_mixing}, \coqin{pgl27\_joint\_mixing} \\
    word view and trace bounds &
      \coqin{pgl27\_word\_view\_indist},
      \coqin{pgl27\_word\_trace\_indist} \\
    ideal-proximity companion & \coqin{pgl27\_view\_mixing} \\
    word correctness & \coqin{pgl27\_word\_run\_recovers} \\
    \bottomrule
  \end{tabular}
  \caption{Consolidated source index for the $\PG$ results, grouped by the
  sections that prove them.}
  \label{tab:source-index}
\end{table}
```

- [ ] **Step 4: Compile, then commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex && git commit -m "wadt2026: instances opener, consolidated trust base and source index (spec T9)"
```

### Task 11: Abstract and conclusion alignment

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex` (abstract, Section 9)

- [ ] **Step 1: Abstract one-word edit.** `These privacy theorems assume` → `These privacy results assume` (spec D7).

- [ ] **Step 2: Conclusion references the headline theorems.** Replace the first conclusion paragraph `I presented a group-parametric \Rocq{} framework ... The verifier learns the secret.` with:
```latex
I presented a group-parametric \Rocq{} framework for card-based protocols
and instantiated it with the action of $\PG$ on eight positions. Theorem A
gives executed correctness, recovery parameters $(3,7,8)$, and perfect view
and trace privacy for coalitions of at most three players under the uniform
group distribution. These security results use a uniform Boolean prior, the
fixed representative dealer, passive adversaries, and the dealer
distributions stated in Section~\ref{sec:model}. The verifier learns the
secret.
```
Replace the second paragraph `For a finite shuffle implementation, a checked fiber certificate ... privacy at $2^{-39}$.` with:
```latex
For a finite shuffle implementation, Theorem B gives an unhalved $L_1$
distance of at most $2^{-40}$ after 200 generator letters, the same bound
for every single-card endpoint and for a product with any Boolean secret
prior, and approximate coalition-view and executed-trace bounds at
$2^{-39}$.
```
(The remaining conclusion paragraphs stay, including the open entropy-form problem, which Theorem B's distributional phrasing keeps consistent.)

- [ ] **Step 3: Compile, then commit.**
```bash
git add pgg-smc/paper-wadt2026/main.tex && git commit -m "wadt2026: abstract and conclusion aligned to Theorems A and B (spec T10)"
```

### Task 12: Verification sweep (spec section 8)

- [ ] **Step 1: Clean build.** Delete aux state, full rebuild:
```bash
cd pgg-smc/paper-wadt2026 && latexmk -C && latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
```
Then check the log:
```bash
grep -iE "undefined|multiply|destination.*duplic" main.log
```
Expected: no undefined references, no multiply-defined labels; hyperref duplicate-destination warnings absent (spec D1: A/B are unnumbered and unlabeled).

- [ ] **Step 2: Greg sweep.** `grep -c 'greg' main.tex` → 0.

- [ ] **Step 3: Prose-rule sweep over the diff.**
```bash
git diff a16d564 -- main.tex | grep '^+' | grep -nE '—|;' 
git grep -n 'law' -- pgg-smc/paper-wadt2026/main.tex
```
Review every hit: math-mode semicolons are fine, prose semicolons and em-dashes are violations; "law" must not appear. Manually scan new paragraphs for prose parentheses.

- [ ] **Step 4: Re-leveling reference audit.**
```bash
grep -n 'Theorem~\\ref\|Lemma~\\ref\|Proposition~\\ref' main.tex
```
Check each hit's word matches the environment its label sits on (`thm:orbit-split`, `thm:three-transitive`, `thm:recovery-ramp`, `thm:pgl-correctness`, `thm:pgl-mixing` are now lemma/proposition environments; `thm:generic-privacy` is a theorem). Also `grep -n 'ref{thm:word-privacy}' main.tex` → no hits (environment removed).

- [ ] **Step 5: Informal-formal agreement.** Read the compiled Section 1 displays against the Section 5/6 capstones clause by clause with the spec §4 hedge lists: A has prior + dealer + passive + distribution-free correctness; B has dealer + passive, no prior, distributional wording, unhalved distances 2^-40 and 2^-39.

- [ ] **Step 6: Figure inspection.** Read the PDF pages containing `fig:run`, `fig:framework-architecture`, `fig:encoding`, `fig:ramp` (Read tool renders PDF pages). Check: sequence diagram before the formal data; no Rocq identifiers in any figure body; encoding rows exactly (0,1,2,3,4,5,6,7) and (0,1,2,4,3,5,6,7) with hearts shaded at values 0–3; ramp marks at 3, 4, 6, 7, 8.

- [ ] **Step 7: Prose-run cap (spec D14).** Page through the PDF: no section of Sections 2–7 runs more than three consecutive paragraphs without a display, figure, table, itemize, or theorem-family environment; Section 1 allowed four before the informal displays.

- [ ] **Step 8: Jargon check.** Word-count each new prose block (`why-two`, narrative, trust base). Any block over 200 words gets a jargon table (term / H-M-L / plain rewrite) and a simplification pass before finishing.

- [ ] **Step 9: Footnote coverage (user requirement).** For every `\begin{theorem}`, `\begin{lemma}`, `\begin{proposition}`, `\begin{thmA}`, `\begin{thmB}`, `\begin{thmAinf}`, `\begin{thmBinf}` in the file, confirm a `\footnotemark`/`\footnotetext` pair naming the formalization path (or directory, for the informal pair) and Rocq name(s):
```bash
grep -n 'begin{theorem}\|begin{lemma}\|begin{proposition}\|begin{thmA\|begin{thmB' main.tex
```
Cross-check each against its footnote. Expected: 3 theorems (generic), 6 lemmas, 6 propositions, 4 named environments, every one footnoted.

- [ ] **Step 10: Fix-and-recommit.** If any step 1–9 found violations, fix and commit:
```bash
git add pgg-smc/paper-wadt2026/main.tex && git commit -m "wadt2026: verification sweep fixes"
```

---

## Self-review record

- Spec coverage: D1→T1/T3/T8/T9; D2→T7.6/T8.6/T9.6/T10.3; D3→no task (accepted); D4→T8.3; D5→T8.8/T9.5; D6→T8.8/T9.6/T10.2; D7→T11.1; D8→T2; D9→T4.1; D10→T6.2; D11→T6.1; D12→T7.4; D13→T8.4; D14→T12.7; greg map→T3/T4; per-section tables→T3–T11; verification 1–10→T12.
- Placeholder scan: all LaTeX content literal; deck values and lemma paths pre-extracted from sources.
- Consistency: environment names `thmA/thmB/thmAinf/thmBinf` defined in T1 and used in T3/T8/T9; labels `tab:bridge`, `fig:run`, `fig:encoding`, `fig:ramp`, `tab:source-index`, `thm:generic-privacy`, `lem:endpoint-transfer`, `lem:product-transfer` each defined once and referenced consistently.
