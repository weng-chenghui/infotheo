# WADT2026 Architecture + Five-Card Family Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement spec rev 12 (`docs/superpowers/specs/2026-08-09-wadt2026-architecture-section-design.md`): framework rename/cleanup with three validated corollaries, the expanded Section 3.1, the five-card family section, the single-standard distance convention, and the flow-diagram relocation.

**Architecture:** Two Rocq commits land first (rename/cleanup, then corollaries), each leaving the build green via rocq-mcp compiles and passing the two-stage audit gate. Five paper commits follow (Section 3.1, distance convention, model-section generalization, five-card section, sibling-section adjustment), each compiling clean. A final verification sweep discharges spec requirements 1-16.

**Tech Stack:** Rocq/MathComp (rocq-mcp for compiles, never make except stated), LaTeX (llncs, latexmk with `-g`), TikZ, listings.

**Conventions used throughout:**
- Repo root: `/Users/cheng-huiweng/Projects/coq/infotheo-pgg`. All git commands use `git -C` with this absolute path.
- Compile check for the paper (run from `pgg-smc/paper-wadt2026/`):
  `latexmk -g -pdf -halt-on-error -interaction=nonstopmode main.tex > /dev/null 2>&1; echo "exit: $?"` — expect `exit: 0`.
- Rocq compile check: `mcp__rocq-mcp__rocq_compile_file` on the named file with workspace `/Users/cheng-huiweng/Projects/coq/infotheo-pgg`. Do NOT use `make -j4`; if a bulk dependency refresh is ever needed, `make -j1` only.
- Paper edits are anchor-string edits (Edit tool old/new), never line numbers, because lines shift between tasks.
- Transient undefined references are EXPECTED between Tasks 3 and 7 (forward references to `sec:fivecard`, `fig:fivecard-run`, `tab:witness-mechanism` before their tasks land). Per-task check is exit 0 only; the zero-undefined-references check is Task 8.
- Style rules for all new prose: no em-dashes, no semicolons, no parenthetical asides, "distribution" never "law", no abbreviations, Theorems A and B by literal text only.

---

### Task 1: Framework rename and cleanup (D16-D18)

**Files:**
- Modify: `pgg-smc/protocol/pgg_monodromy_profile.v`
- Modify: `pgg-smc/instances/pgl27/pgl27_profile.v`
- Modify: `pgg-smc/instances/s5/s5_profile.v`
- Modify: `pgg-smc/instances/s5x5/s5x5_profile.v`
- Modify: `pgg-smc/instances/abelian/abel_profile.v`
- Modify: `pgg-smc/instances/denboer1989/den_boer_profile.v`

- [ ] **Step 1.1: Rename the section and its comment mentions in `pgg_monodromy_profile.v`**

Three edits. First, the header comment near line 13: replace `section run_profile` with `section protocol_of_profile` (keep the comment box; re-pad trailing spaces so the `*)` column stays aligned). Second, the docstring near line 46: replace `the generic run_profile` with `the generic protocol_of_profile`. Third, the section markers:

Old: `Section run_profile.` → New: `Section protocol_of_profile.`
Old: `End run_profile.` → New: `End protocol_of_profile.`

- [ ] **Step 1.2: Delete `run_dealer` and its docstring (D16)**

Remove this entire block (nothing depends on it):

```coq
(** run_dealer — the dealer of the shared program, plugged at mp_PI.
    Kind: instance.
    Why: exchange_dealer at the profile's interface; it bakes the plug's
    content readout rp_content into each dealt column so the revealed values
    are the plug's readout of the plugged group's shuffle. *)
Definition run_dealer (W : seq (pgg_gT M)) (P_idx : nat) :=
  exchange_dealer PI (rp_content plug) players W P_idx.
```

- [ ] **Step 1.3: Rename the five non-running members (D18), docstrings included**

Apply these five renames in `pgg_monodromy_profile.v`. Rename both the docstring head-word and the definition; bodies are unchanged.

```coq
(** profile_eps — the anonymity character of the profile. Kind: definition.
    Why: the security epsilon read off mp_security; group-sensitive. *)
Definition profile_eps : R := sw_bound_eps (mp_security mp).

(** profile_k — the privacy-threshold character of the profile.
    Kind: definition.
    Why: the threshold k read off the plug's scheme. *)
Definition profile_k : nat := ts_k (rp_scheme plug).

(** profile_anonymous — the sent distribution is profile_eps-close to uniform.
    Kind: main.
    Why: the security guarantee, consuming mp_security (its sw_bound field). *)
Definition profile_anonymous := sw_bound (mp_security mp).

(** profile_private — fewer than profile_k shares cannot distinguish two
    secrets. Kind: main.
    Why: the privacy guarantee, consuming the plug's scheme (ts_private). *)
Definition profile_private := ts_private (rp_scheme plug).

(** profile_recon_encode — reconstructing the canonical encoding returns the
    dealt secret. Kind: main.
    Why: the correctness guarantee, consuming the plug's scheme (ts_correct on
    the canonical encoding). *)
Lemma profile_recon_encode (s : mp_secretT mp) :
  run_recover (ts_encode (rp_scheme plug) s) = s.
Proof. exact: ts_correct (ts_encode_valid (rp_scheme plug) s). Qed.
```

`run_party`, `run_verifier`, `run_recover` keep their names and docstrings.

- [ ] **Step 1.4: Compile the framework file**

Run `mcp__rocq-mcp__rocq_compile_file` on `pgg-smc/protocol/pgg_monodromy_profile.v`. Expected: success, no errors.

- [ ] **Step 1.5: Rename the five instance character lemmas**

`pgg-smc/instances/pgl27/pgl27_profile.v` — two edits. Header index line (near line 19):

Old: `(*   run_k_pgl27         == the plug's privacy threshold is four              *)`
New: `(*   profile_k_pgl27     == the plug's privacy threshold is four              *)`

Lemma block (near line 108):

```coq
(** profile_k_pgl27 — the PGL(2,7) plug's privacy threshold is four.
    @main bound: coalitions of at most three cards are private, k = 4. *)
Lemma profile_k_pgl27 (R : realType) : profile_k (pgl27_profile R) = 4.
Proof. by []. Qed.
```

`pgg-smc/instances/denboer1989/den_boer_profile.v` (near line 90):

```coq
(** profile_k_denboer — the five-card plug's privacy threshold is 2.
    @main architecture: profile_k (den_boer_profile R) = 2; the contrast
    character (any single revealed card leaks nothing about the AND, but two
    may), read off the shared profile_k of the five-card plug. *)
Lemma profile_k_denboer (R : realType) : profile_k (den_boer_profile R) = 2.
Proof. by []. Qed.
```

`pgg-smc/instances/s5/s5_profile.v`, `pgg-smc/instances/s5x5/s5x5_profile.v`, `pgg-smc/instances/abelian/abel_profile.v`: in each file, grep for `run_k` (word-boundary) and replace every occurrence with `profile_k`, and the lemma names `run_k_s5` → `profile_k_s5`, `run_k_s5x5` → `profile_k_s5x5`, `run_k_abel` → `profile_k_abel` (lemma line plus the `What:`/`Why:` doc-comment mentions at `s5_profile.v:56-57`, `s5x5_profile.v:47-49`, `abel_profile.v:74-75`).

- [ ] **Step 1.6: Compile all five instance files**

Run `mcp__rocq-mcp__rocq_compile_file` on each of: `pgg-smc/instances/pgl27/pgl27_profile.v`, `pgg-smc/instances/denboer1989/den_boer_profile.v`, `pgg-smc/instances/s5/s5_profile.v`, `pgg-smc/instances/s5x5/s5x5_profile.v`, `pgg-smc/instances/abelian/abel_profile.v`. Expected: all succeed. Then compile the downstream files that import the renamed profiles to catch stale references: `pgg-smc/instances/pgl27/pgl27_run.v`, `pgg-smc/instances/denboer1989/den_boer_run.v`, `pgg-smc/instances/kim2025/kim_run.v` (and any file `rocq_compile_file` reports as broken).

- [ ] **Step 1.7: Retired-name sweep (verification requirement 11)**

Run:
```bash
cd /Users/cheng-huiweng/Projects/coq/infotheo-pgg/pgg-smc
for n in run_dealer run_eps run_k run_anonymous run_private run_recovers run_profile; do
  echo "== $n"; grep -rn "\b$n\b" --include="*.v" . ; done
```
Expected: zero output for every name (the executed-layer `*_run_recovers` lemmas do not match at a word boundary).

- [ ] **Step 1.8: Commit (audit gate runs)**

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/protocol/pgg_monodromy_profile.v pgg-smc/instances/pgl27/pgl27_profile.v pgg-smc/instances/denboer1989/den_boer_profile.v pgg-smc/instances/s5/s5_profile.v pgg-smc/instances/s5x5/s5x5_profile.v pgg-smc/instances/abelian/abel_profile.v
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "pgg: protocol_of_profile section, profile_* characters, run_dealer removed (spec D16-D18)"
```
The pre-commit audit gate runs on the staged `.v` files. If Stage 2 hits the token cap, `ROCQ_AUDIT_BYPASS=1` is the sanctioned fallback (log the event in the commit message trailer text, not with `--no-verify`).

---

### Task 2: Three framework-usage corollaries (D14)

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_run.v` (import + two corollaries)
- Modify: `pgg-smc/instances/pgl27/pgl27_profile.v` (one lemma)

- [ ] **Step 2.1: Add the import to `pgl27_run.v`**

After the existing line `From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.` add:

```coq
From pgg_smc Require Import pgg_monodromy_profile.
```

- [ ] **Step 2.2: Append the two corollaries at the end of `pgl27_run.v` (top-level context)**

```coq
(** run_recover_pgl27 — the executed PGL(2,7) run decodes through the
    profile's derived decoder.
    @main architecture: the verifier's executed endpoints reconstruct the
    dealt secret via run_recover of pgl27_profile, for any cut in the
    group. *)
Corollary run_recover_pgl27 (R : realType) (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  @run_recover R (pgl27_profile R)
    (tcast (pgl27_endpoints_size s w0)
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp pgl27_fuel (pgl27_procs s w0)).2 1))))
  = s.
Proof. exact: pgl27_run_recovers. Qed.

(** run_party_pgl27 — each executed PGL(2,7) player is the profile's derived
    player role at its ordinal.
    @main architecture: the instance's player processes coincide with
    run_party of pgl27_profile. *)
Corollary run_party_pgl27 (R : realType) (i : 'I_(pi_T' pgl27_PI).+1) :
  @run_party R (pgl27_profile R) i = exchange_player pgl27_PI i.
Proof. by []. Qed.
```

Both were validated in-kernel on 2026-08-09 (rocq-mcp preamble session; `exact: pgl27_run_recovers.` in 11 ms, `by [].` in 6 ms). If `realType` is not in scope at the append point, the file already imports `reals` (line 32), so it is.

- [ ] **Step 2.3: Append `profile_eps_pgl27` to `pgl27_profile.v`, next to `profile_k_pgl27`**

```coq
(** profile_eps_pgl27 — the PGL(2,7) profile's security character is zero:
    perfect single-position endpoint uniformity.
    @main security: the eps read off pgl27_profile is 0. *)
Lemma profile_eps_pgl27 (R : realType) :
  @profile_eps R (pgl27_profile R) = 0%R.
Proof. by []. Qed.
```

Validated pre-rename as `run_eps_pgl27 = 0%R` (`by [].`, 3 ms); the rename changes only the constant name.

- [ ] **Step 2.4: Compile both files**

`mcp__rocq-mcp__rocq_compile_file` on `pgg-smc/instances/pgl27/pgl27_profile.v` then `pgg-smc/instances/pgl27/pgl27_run.v` (this order: run imports profile). Expected: success.

- [ ] **Step 2.5: Commit (audit gate runs)**

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/instances/pgl27/pgl27_run.v pgg-smc/instances/pgl27/pgl27_profile.v
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "pgl27: framework-usage corollaries run_recover_pgl27, run_party_pgl27, profile_eps_pgl27 (spec D14)"
```

---

### Task 3: Paper preamble and Section 3.1 replacement (D1-D15)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 3.1: Add `\lstset` to the preamble (D6)**

After the existing `\usepackage{listings}` line add:

```latex
\lstset{basicstyle=\ttfamily\footnotesize,columns=fullflexible,keepspaces=true,breaklines=true,xleftmargin=2mm,aboveskip=2pt,belowskip=2pt}
```

- [ ] **Step 3.2: Replace the Section 3.1 body**

Replace everything between `\subsection{Framework Architecture}` and `\subsection{Generic Theorems}` with the following, KEEPING the existing `tab:bridge` table environment and the existing `fig:framework-architecture` figure environment verbatim at their marked positions (only the figure caption gains one sentence).

```latex
An instance is specified by filling one record. The record type
\coqin{MonodromyProfile} has five fields, and they carry the data of
Equation~\ref{eq:model-data} into the executable protocol: the group with
its action and generators, the secret type, the layout of a run, the
shuffle-security bound, and the decoder. Here $R$ is the real closed field
of Equation~\ref{eq:model-data}, not a protocol datum. The finite algebraic
structures use Mathematical Components~\cite{MathComp}, and
Table~\ref{tab:bridge} maps each model datum to its record role and to the
values the $\PG$ instance supplies.

%% KEEP the existing tab:bridge table environment here, unchanged.

The central record and its derived protocol follow.\footnote{Formalized in
\path{pgg-smc/protocol/pgg_monodromy_profile.v}. The listing elides
argument types and implicit parameters.}

\begin{lstlisting}
Record MonodromyProfile (R : realType) := MkMonodromyProfile {
  (* the group, its action, and its generators *)
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_secretT  : Type ;                   (* secret type    *)
  mp_PI       : PGGInterface mp_M ;      (* run layout     *)
  mp_security : SecurityWitness R mp_M ; (* endpoint bound *)
  mp_plug     : ReconPlug mp_M mp_secretT }. (* decoder    *)

Section protocol_of_profile. (* the protocol of profile mp *)
Definition run_party i    := exchange_player PI i.
Definition run_verifier   := exchange_verifier PI players.
Definition run_recover c  := ts_recon (rp_scheme plug) c.
Definition profile_eps  : R  := sw_bound_eps (mp_security mp).
Definition profile_k : nat   := ts_k (rp_scheme plug).
Definition profile_anonymous := sw_bound (mp_security mp).
Definition profile_private   := ts_private (rp_scheme plug).

Lemma profile_recon_encode s :
  run_recover (ts_encode (rp_scheme plug) s) = s.
Proof. exact: ts_correct (ts_encode_valid (rp_scheme plug) s). Qed.
\end{lstlisting}

Filling the record means discharging three proof obligations.
\begin{itemize}
\item Every single card position lands close to uniform: \coqin{sw\_bound}
  bounds the distance of each position's endpoint distribution from the
  uniform distribution by \coqin{sw\_bound\_eps}.
\item The threshold scheme recovers and hides: \coqin{ts\_correct} decodes
  every valid share tuple to its secret, and \coqin{ts\_private} gives
  every coalition below the threshold a share pattern that is equally
  consistent with either secret.
\item Reconstruction is shuffle-invariant: for any allowed shuffle and any
  valid share tuple, \coqin{rp\_recon\_invariant} states that permuting the
  shares by the shuffle leaves the recovered secret unchanged.
\end{itemize}

Once the record is filled, the \coqin{protocol\_of\_profile} section
derives the players, the verifier, and the recovery map as definitions
over the fields. It re-exports the certified characters and proves the
round-trip correctness lemma \coqin{profile\_recon\_encode} in one line
from the record's obligations, so no new proof obligation arises at wiring
time. In the worked instance the players and the verifier are exactly the
generic processes at its layout record, and the dealer is the same generic
dealing program carrying the instance's own content readout. Each player
coincides with the derived role, the correctness is restated through the
shared decoder, and the characters are read off the shared
definitions.\footnote{\coqin{run\_party\_pgl27} and
\coqin{run\_recover\_pgl27} in
\path{pgg-smc/instances/pgl27/pgl27_run.v}, \coqin{profile\_k\_pgl27} and
\coqin{profile\_eps\_pgl27} in
\path{pgg-smc/instances/pgl27/pgl27_profile.v}.} The threshold character
has value four under the successor convention, so the largest private
coalition size is three.

A small process interpreter executes the layout record. It originates in
the earlier FORTE development~\cite{WengEtAl2025} and produces the
executed traces of Section~\ref{sec:model}. The group, its action, and its
shuffle distribution fix the dealing and the endpoint bound, and the
decoder is an independent choice, so instances over the same group differ
only in the reconstruction component.
Figure~\ref{fig:framework-architecture} shows the dependencies.

The record path certifies correctness, endpoint uniformity, and the
sharing threshold. The coalition-view, trace, and word-shuffle privacy
theorems of Sections~\ref{sec:exact} and~\ref{sec:mixing} are stated
separately. They consume the transitivity of the action and the shuffle
distribution directly, not the record fields. The two optional slots of
the security witness encode the proof mechanism, and
Table~\ref{tab:witness-mechanism} shows the realized combinations.
Section~\ref{sec:pgl} is the difficult worked instantiation.

\begin{table}[H]
  \centering
  \small
  \begin{tabular}{@{}llL{.34\linewidth}L{.22\linewidth}@{}}
    \toprule
    Exact slot & Asymptotic slot & Mechanism & Realized by \\
    \midrule
    present & absent & exact equality at $\varepsilon=0$ under the uniform
      group distribution & den Boer, $\PG$ \\
    present & present & exact count with geometric decay in the word
      length & Kim \\
    absent & present & spectral certificate with an imported gap premise
      & $S_5$, $S_5\times S_5$ \\
    \bottomrule
  \end{tabular}
  \caption{Realized combinations of the security witness's two optional
  slots. Section~\ref{sec:mixing} treats the word-shuffle counterpart of
  the $\PG$ row, Section~\ref{sec:fivecard} proves the den Boer and Kim
  rows, and Table~\ref{tab:instances} records the per-instance evidence.}
  \label{tab:witness-mechanism}
\end{table}

With an \coqin{InputEncoding}, a commit prologue collects the players'
inputs and assembles the dealt deck from them, so the same flow evaluates
a function of committed inputs. The realized encoding is den Boer's. Its
obligation \coqin{ie\_orbit} places equal-output inputs in one shuffle
orbit, and its derived lemma \coqin{ie\_output\_correct} shows the
shuffled layout reconstructs the output for every allowed shuffle. The Kim
variant reuses the den Boer program unchanged. With an empty input list
the prologue reduces by computation to the plain dealer, which is the
secret-sharing case, and the $\PG$ instance passes exactly this empty
list. Section~\ref{sec:fivecard} realizes the committed-input flow, and
the instance table of Section~\ref{sec:instances} records the full
landscape.

%% KEEP the existing fig:framework-architecture figure environment here,
%% appending this sentence to its caption:
%%   Filling the three component records yields the derived protocol
%%   roles, the certified characters, and the round-trip lemma of the
%%   listing.

The next subsection states the generic theorems the framework supplies to
every instance.
```

Note for the implementer: the deleted range includes the old closing paragraph ("The supporting records refine individual components...") whose final sentence contradicted the boundary sentence (spec D13).

- [ ] **Step 3.3: Compile check**

Run the latexmk command from Conventions. Expected `exit: 0`. Undefined references to `sec:fivecard` are expected until Task 6.

- [ ] **Step 3.4: Commit**

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/paper-wadt2026/main.tex
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "wadt2026: section 3.1 rebuilt around MonodromyProfile listing and derived protocol (spec D1-D15)"
```

---

### Task 4: Distance convention, one standard and one footnote (D22)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 4.1: Add the convention footnote at the first in-text bound**

In the introduction paragraph BEFORE the informal Theorem B environment, the sentence ends `...is within unhalved $L_1$ distance $2^{-40}$ of the uniform group distribution.` Rewrite it to:

```latex
...is within $L_1$ distance $2^{-40}$ of the
uniform group distribution.\footnote{The $L_1$ distance is
$\lVert P-Q\rVert_1=\sum_x\lvert P(x)-Q(x)\rvert$, called variation
distance in the formal development, with maximum value 2. The common total
variation distance is half of it. An $L_1$ bound of $2^{-40}$ therefore
bounds every observer's distinguishing advantage by $2^{-41}$.}
```

- [ ] **Step 4.2: Grep-driven "unhalved" sweep**

Run `grep -n "unhalved" pgg-smc/paper-wadt2026/main.tex`. At every hit (known sites: abstract, two in the informal Theorem B environment, the contributions bullet, the model-section lead-in, the `tab:instances` caption, the relocating sibling-section sentence, the conclusion), delete the word "unhalved" and one adjacent space, so "unhalved $L_1$ distance" becomes "$L_1$ distance" and "the unhalved distance in Equation..." becomes "the distance in Equation...". Re-run the grep. Expected: zero hits.

- [ ] **Step 4.3: Delete the halved-convention block in the model section**

Delete this block (keeping the `eq:l1-definition` display above it):

```latex
The repository calls Equation~\ref{eq:l1-definition} variation distance.
The common halved total variation distance is
\begin{equation}
  d_{\mathrm{TV}}(P,Q)=\tfrac12\lVert P-Q\rVert_1.
  \label{eq:tv-definition}
\end{equation}
Thus an $L_1$ bound of $2^{-40}$ gives a halved total variation bound of
$2^{-41}$. In operational terms, a total variation bound of $2^{-41}$ means
that no observer, whatever test they apply, distinguishes the word shuffle
from the uniform shuffle with advantage above $2^{-41}$.
```

- [ ] **Step 4.4: Delete the mixing-section conversion sentence**

Delete:

```latex
Under the halved convention in Equation~\ref{eq:tv-definition}, each of
these bounds is at most $2^{-41}$ in total variation.
```

- [ ] **Step 4.5: Convention checks**

Run: `grep -cn "unhalved\|halved\|total variation\|tv-definition" pgg-smc/paper-wadt2026/main.tex`. Expected: exactly the footnote's "total variation" mention (1 hit region), nothing else. Compile check: `exit: 0`.

- [ ] **Step 4.6: Commit**

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/paper-wadt2026/main.tex
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "wadt2026: single L1 convention with one total-variation footnote (spec D22)"
```

---

### Task 5: Model-section generalization and flow-diagram relocation (D23)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 5.1: Generalize the model section's opening paragraph**

Replace:

```latex
A run of the protocol handles one secret bit and eight face-down cards. A
dealer encodes the secret as a valid arrangement of the eight cards. The
dealer then samples a shuffle from a finite group and rearranges the deck by
its permutation action. Each of eight players receives the card at one
position. The players reveal their cards to a verifier, and the verifier
decodes the secret from the revealed arrangement. Figure~\ref{fig:run}
shows this flow.
```

with:

```latex
A run of the protocol handles one secret and a deck of face-down cards. A
dealer encodes the secret as a valid arrangement of the deck. The dealer
then samples a shuffle from a finite group and rearranges the deck by its
permutation action. Each player receives the card at one position. The
players reveal their cards to a verifier, and the verifier decodes the
secret from the revealed arrangement. Each instance section shows its own
run as a flow diagram.
```

- [ ] **Step 5.2: Cut the `fig:run` figure environment from the model section**

Cut (do not delete) the entire `\begin{figure}[H] ... \label{fig:run} \end{figure}` block that follows the opening paragraph. Keep its TikZ code for Step 5.4.

- [ ] **Step 5.3: Fix the word-shuffle sentence**

Replace `The word-shuffle model describes the dealer of Figure~\ref{fig:run}
performing the shuffle as a sequence of physical cuts.` (as wrapped in the file) with `The word-shuffle model describes the dealer performing the shuffle as a
sequence of physical cuts.`

- [ ] **Step 5.4: Paste `fig:run` into the PGL construction section**

Insert the cut figure block immediately after the PGL section's first paragraph (the one ending `...and the decoder reads the orbit class.`). Replace its caption with:

```latex
  \caption{One $\PG$ run: eight players, one card each, no player inputs,
  and the verifier decodes the orbit class of the heart positions. The
  shuffle $g$ is drawn from the uniform distribution $U_G$ in the
  uniform-shuffle model and from the word distribution $\worddist$ in the
  word-shuffle model. This is the no-input counterpart of
  Figure~\ref{fig:fivecard-run}.}
```

- [ ] **Step 5.5: Compile and commit**

Compile check `exit: 0` (undefined `fig:fivecard-run` expected until Task 6). Then:

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/paper-wadt2026/main.tex
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "wadt2026: model section generalized, PGL flow diagram relocated to its construction section (spec D23)"
```

---

### Task 6: The five-card family section (D19, D21)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 6.1: Insert the new section**

Insert the following complete section between the end of the framework section (after `\subsection{Generic Theorems}`'s last theorem, immediately before `\section{The \texorpdfstring{$\PG$}{PGL(2,7)} Construction}`):

```latex
\section{A First Instance: The Five-Card Family}\label{sec:fivecard}

The simplest instantiation of the framework covers two classic protocols
with one record. Five cards carry the deck, the cyclic group $C_5$ acts by
rotation, and the decoder reads whether the three hearts are consecutive.
Den Boer's five-card protocol~\cite{denBoer1989} and the Kim and
\c{C}etinkaya variant~\cite{KimCetinkaya2025} differ only in the dealing
distribution, so one profile at bias $\varepsilon$ specifies both.
Figure~\ref{fig:fivecard-run} shows a run.

\begin{figure}[H]
  \centering
  \resizebox{.97\linewidth}{!}{%
  \begin{tikzpicture}[
     actor/.style={draw,rounded corners,fill=blue!12,minimum width=14mm,
       minimum height=7mm,font=\small\bfseries},
     life/.style={dashed,gray!70},
     msg/.style={-{Latex},thick},
     act/.style={draw,rounded corners,fill=orange!14,inner sep=3pt,
       align=center,font=\footnotesize},
     lbl/.style={midway,above,font=\footnotesize}]
    \node[actor] (A) at (0,0)    {Alice};
    \node[actor] (B) at (2.9,0)  {Bob};
    \node[actor] (D) at (6.6,0)  {Dealer};
    \node[actor] (P) at (10.0,0) {Players};
    \node[actor] (V) at (13.2,0) {Verifier};
    \draw[decorate,decoration={brace,amplitude=4pt,raise=2pt}]
      (-0.8,0.45) -- (3.7,0.45)
      node[midway,above=4pt,font=\footnotesize]{input committers};
    \draw[decorate,decoration={brace,amplitude=4pt,raise=2pt}]
      (8.9,0.45) -- (11.1,0.45)
      node[midway,above=4pt,font=\footnotesize]{five players, one card each};
    \draw[life] (0,-0.4)    -- (0,-5.6);
    \draw[life] (2.9,-0.4)  -- (2.9,-5.6);
    \draw[life] (6.6,-0.4)  -- (6.6,-5.6);
    \draw[life] (10.0,-0.4) -- (10.0,-5.6);
    \draw[life] (13.2,-0.4) -- (13.2,-5.6);
    \draw[msg] (0,-0.8)  -- (6.6,-0.8)
      node[lbl]{one card value committing $a$};
    \draw[msg] (2.9,-1.5) -- (6.6,-1.5)
      node[lbl]{one card value committing $b$};
    \node[act,anchor=west] at (6.75,-2.2)
      {assemble the five-card deck};
    \node[act,anchor=west] at (6.75,-3.0)
      {draw the cut, deal one card per player};
    \draw[msg] (6.6,-3.7) -- (10.0,-3.7) node[lbl]{deal, face down};
    \draw[msg] (10.0,-4.35) -- (13.2,-4.35) node[lbl]{reveal all cards};
    \node[act,anchor=east] at (13.05,-5.0)
      {read: are the three hearts consecutive};
    \draw[msg] (13.2,-5.5) -- (0,-5.5) node[lbl]{announce $a\wedge b$};
  \end{tikzpicture}}
  \caption{One five-card run with committed inputs. The physical protocol
  commits each input bit as two face-down cards, and the formalization
  encodes each committed bit as one card value.}
  \label{fig:fivecard-run}
\end{figure}

The central record and the profile that fills it
follow.\footnote{Formalized in
\path{pgg-smc/instances/kim2025/five_card_family.v} as
\coqin{five\_card\_profile}; the listing elides the three bias
hypotheses.}

\begin{lstlisting}
Definition five_card_profile (R : realType) (eps : R)
    (* three bias hypotheses elided *) (L : nat) : MonodromyProfile R :=
  @MkMonodromyProfile R FiveCardKim_M bool FiveCardKim_PI
    (fc_kim_security_witness ... L) (* biased-cut witness    *)
    five_card_plug.                 (* three-hearts decoder  *)
\end{lstlisting}

The dealing distribution is the biased cut
\begin{equation}
  w_\varepsilon(a^k)=\begin{cases}\tfrac{1}{5}-\varepsilon, & k=0,\\[2pt]
  \tfrac{1}{5}+\tfrac{\varepsilon}{4}, & k=1,2,3,4,\end{cases}
  \qquad -\tfrac{4}{5}<\varepsilon<\tfrac{1}{5}.
  \label{eq:fivecard-weight}
\end{equation}
At bias zero the witness bound collapses to zero for any positive word
length, which is the precise sense in which the unbiased member is den
Boer's protocol.\footnote{\coqin{five\_card\_eps0\_eq0} in
\path{pgg-smc/instances/kim2025/five_card_family.v}.}

Figure~\ref{fig:fivecard-leakage} quantifies every reveal
case.\footnote{\coqin{leak\_k1}, \coqin{leak\_k2\_adj},
\coqin{leak\_k2\_dist2}, \coqin{leak\_k3}, \coqin{leak\_k4},
\coqin{leak\_k5}, and the cap \coqin{H\_secret} in
\path{pgg-smc/instances/denboer1989/five_card_leakage.v}. For example
\coqin{leak\_k2\_adj} $=\tfrac{27}{10}-\tfrac14\log 5-\tfrac{7}{10}\log
7$.} One revealed card carries no information about the conjunction, which
is the information-theoretic counterpart of the scheme's privacy
threshold, and the ramp climbs to the secret's own entropy
$2-\tfrac34\log 3\approx 0.811$. The decimals are evaluations of the
proven closed forms.

\begin{figure}[H]
  \centering
  \begin{tikzpicture}[x=8.5mm,y=-11.5mm,
     card/.style={draw,rounded corners=1pt,minimum width=6.5mm,
       minimum height=8.5mm,font=\small},
     down/.style={card,fill=blue!30!gray!60},
     lab/.style={font=\small,anchor=west}]
    \node[card] at (0,1) {$\clubsuit$};
    \node[down] at (1,1) {}; \node[down] at (2,1) {};
    \node[down] at (3,1) {}; \node[down] at (4,1) {};
    \node[lab] at (4.8,1) {$0$ bits, nothing};
    \node[card] at (0,2) {$\clubsuit$};
    \node[card] at (1,2) {\textcolor{red}{$\heartsuit$}};
    \node[down] at (2,2) {}; \node[down] at (3,2) {};
    \node[down] at (4,2) {};
    \node[lab] at (4.8,2) {$0.154$ bits};
    \node[card] at (0,3) {$\clubsuit$};
    \node[down] at (1,3) {};
    \node[card] at (2,3) {\textcolor{red}{$\heartsuit$}};
    \node[down] at (3,3) {}; \node[down] at (4,3) {};
    \node[lab] at (4.8,3) {$0.119$ bits};
    \node[card] at (0,4) {$\clubsuit$};
    \node[card] at (1,4) {\textcolor{red}{$\heartsuit$}};
    \node[card] at (2,4) {\textcolor{red}{$\heartsuit$}};
    \node[down] at (3,4) {}; \node[down] at (4,4) {};
    \node[lab] at (4.8,4) {$0.487$ bits};
    \node[card] at (0,5) {$\clubsuit$};
    \node[card] at (1,5) {\textcolor{red}{$\heartsuit$}};
    \node[card] at (2,5) {\textcolor{red}{$\heartsuit$}};
    \node[card] at (3,5) {\textcolor{red}{$\heartsuit$}};
    \node[down] at (4,5) {};
    \node[lab] at (4.8,5) {$0.811$ bits, the cap};
    \node[card] at (0,6) {$\clubsuit$};
    \node[card] at (1,6) {\textcolor{red}{$\heartsuit$}};
    \node[card] at (2,6) {\textcolor{red}{$\heartsuit$}};
    \node[card] at (3,6) {\textcolor{red}{$\heartsuit$}};
    \node[card] at (4,6) {$\clubsuit$};
    \node[lab] at (4.8,6) {$0.811$ bits, the cap};
  \end{tikzpicture}
  \caption{Mutual information between the revealed cards and the
  conjunction, one machine-checked value per reveal pattern. The drawn
  card faces are one illustrative arrangement, and the printed values
  average over the whole distribution of arrangements.}
  \label{fig:fivecard-leakage}
\end{figure}

\begin{proposition}[Seven-cut security at bias $1/100$\footnotemark]
\label{prop:fivecard-mixing}
\footnotetext{Formalized in
\path{pgg-smc/instances/kim2025/five_card_kim.v} as
\coqin{kim\_bound\_centi} and \coqin{kim\_deal\_centi\_lt}.}
Let the shuffle distribution be the biased cut $w_{1/100}$ repeated seven
times. Then every single-card endpoint distribution is within $L_1$
distance $2^{-40}$ of uniform, and the kernel checks the computation.
\end{proposition}

The two members share one executed program, so correctness transfers
verbatim. The Kim program is the den Boer program, and its recovery
theorem is the den Boer proof reused.\footnote{\coqin{kim\_procs} and
\coqin{kim\_run\_recovers} in
\path{pgg-smc/instances/kim2025/kim_run.v}.} The committed inputs of the
two players realize the function-evaluation flow of
Section~\ref{sec:framework} with den Boer's input encoding. Den Boer's
uniform cut gives the exact endpoint distribution after one shuffle, and a
single corrupted player's executed trace leaves the secret's conditional
entropy equal to its plain
entropy.\footnote{\coqin{kim\_trace\_secrecy} in
\path{pgg-smc/instances/kim2025/kim_trace.v}.}
Table~\ref{tab:instances} in Section~\ref{sec:instances} records the full
landscape.

The five-card family keeps the group cyclic and the deck small enough for
kernel enumeration. The next sections instantiate the same records where
enumeration fails. The $\PG$ construction adds coalition privacy beyond
one card via three-transitivity, an orbit-class secret, and word
certificates proven without computing in the group.
```

- [ ] **Step 6.2: Compile check**

Compile: `exit: 0`. All references defined from here on.

- [ ] **Step 6.3: Commit**

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/paper-wadt2026/main.tex
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "wadt2026: five-card family section with input-flow diagram and reveal-leakage figure (spec D19, D21)"
```

---

### Task 7: Sibling-instances section adjustment (D20)

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex`

- [ ] **Step 7.1: Delete the relocated paragraph**

Delete (its content now lives in the five-card section, restated without the word "unhalved" which Task 4 already removed):

```latex
Den Boer's instance samples a uniform cyclic cut. One cut therefore gives
the exact endpoint distribution used by its single-card privacy proof. Kim's variant
uses a biased cyclic cut~\cite{KimCetinkaya2025}. For bias $1/100$, the
formal development proves in the kernel that seven repeated cuts put every
single-card endpoint within $2^{-40}$ of uniform in $L_1$ distance.
```

(If Task 4's sweep changed this paragraph's wording, match the then-current text.)

- [ ] **Step 7.2: Adjust the section opener**

Replace:

```latex
The framework's value shows in which arguments transfer across instances
unchanged and which need instance-specific finite or spectral evidence.
Four sibling instances exercise different parts of the framework alongside
the $\PG$ instance, and Table~\ref{tab:instances} records the proved
coverage.
```

with:

```latex
The framework's value shows in which arguments transfer across instances
unchanged and which need instance-specific finite or spectral evidence.
Beyond the instances of Sections~\ref{sec:fivecard} and~\ref{sec:pgl}, the
$S_5$ and $S_5\times S_5$ instances exercise the spectral part of the
framework, and Table~\ref{tab:instances} records the proved coverage
across all five.
```

Keep the two sentences that follow ("Perfect privacy in the table refers..." onward) unchanged.

- [ ] **Step 7.3: Compile and commit**

Compile: `exit: 0`. Then:

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/paper-wadt2026/main.tex
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "wadt2026: sibling-instances section adjusted after five-card relocation (spec D20)"
```

---

### Task 8: Verification sweep (spec requirements 1-16)

**Files:**
- Read/verify only, plus fixes and one final commit if defects surface.

- [ ] **Step 8.1: Clean build and reference integrity (reqs 1, 13)**

From `pgg-smc/paper-wadt2026/`: `latexmk -g -pdf -halt-on-error -interaction=nonstopmode main.tex > /dev/null 2>&1; echo "exit: $?"` then `grep -E "^!" main.log | head`, `grep -c "undefined" main.log`, `grep -c "multiply defined" main.log`. Expected: exit 0, no `^!` lines, zero undefined, zero multiply defined. Also `grep -nE "Section [0-9]" main.tex` — expected zero hits (all references label-based).

- [ ] **Step 8.2: Page count (req 2)**

`pdfinfo main.pdf | grep Pages` (or `mdls -name kMDItemNumberOfPages main.pdf`). Record before/after; expected about 20.5 (grew from 17).

- [ ] **Step 8.3: Identifier greps (reqs 3, 10, 12)**

Run the full identifier-to-file grep list from spec verification requirements 3, 10, and 12 (post-rename names in `pgg_monodromy_profile.v`; `sw_*` in `algebraic_rigidity.v`; `ts_*` in `pgg_sharing_framework.v`; `rp_*` in `covering_scheme.v`; `ie_orbit`/`ie_output_correct` in `input_encoding.v`; `exchange_dealer`/`exchange_player`/`exchange_verifier` in `card_exchange_pismc.v:221,239,249`; `run_recover_pgl27`/`run_party_pgl27` in `pgl27_run.v`; `profile_k_pgl27`/`profile_eps_pgl27` in `pgl27_profile.v`; the seven leakage names in `five_card_leakage.v`; the five-card and Kim names in their files). Every identifier must resolve in its named file.

- [ ] **Step 8.4: Style sweeps (req 4)**

On the changed regions (Section 3.1, the five-card section, the model section, all touched captions and footnotes): `grep -n "—" main.tex` (zero in prose), semicolon check on prose sentences (TikZ statement terminators exempt), "law" check (zero), parenthetical-aside read-through, abbreviation read-through.

- [ ] **Step 8.5: Prose-run caps (req 5) and honesty checks (reqs 6, 7)**

Count consecutive prose paragraphs in the new Section 3.1 (Block 5 is 3, then the mechanism table) and in the five-card section (never more than 2). Re-read the wiring paragraphs against the spec's Record-to-theorem boundary section: no sentence claims Theorems 1, 2, 3, A, or B derive from the records, and no sentence attributes the instance's dealer or verifier to the derived section. Threshold wording matches D12 (value four, largest private coalition three).

- [ ] **Step 8.6: PDF visual inspection (reqs 8, 15, 16)**

Open `main.pdf` and check page by page: the Section 3.1 listing has no overfull lines, both new tables fit the text width, the two flow diagrams render with `fig:fivecard-run` before `fig:run` in page order, the model section has no flow diagram but keeps `fig:models`, the leakage figure's six rows match the spec's position sets and the illustrative arrangement (club, three hearts, club), no float drifted past the bibliography.

- [ ] **Step 8.7: Convention checks (req 14)**

`grep -n "unhalved\|halved" main.tex` — zero. `grep -cn "total variation" main.tex` — hits only inside the one footnote. `grep -n "tv-definition" main.tex` — zero. `grep -n "2^{-41}" main.tex` — only inside the footnote. Spot-check every `2^{-40}` and `2^{-39}` site against its named lemma.

- [ ] **Step 8.8: Rocq re-verification (reqs 9, 11)**

Re-run the Task 1.7 retired-name sweep (zero hits). Confirm the six Task-1 files and two Task-2 files all have fresh `.vo` newer than their `.v` (`ls -la` timestamps), recompiling via rocq-mcp if any edit happened since.

- [ ] **Step 8.9: Fix any defects found, recompile, and commit the sweep fixes**

```bash
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg add pgg-smc/paper-wadt2026/main.tex
git -C /Users/cheng-huiweng/Projects/coq/infotheo-pgg commit -m "wadt2026: verification sweep fixes (spec requirements 1-16)"
```

(Skip the commit if the sweep found nothing.)

---

## Self-review

- Spec coverage: D1-D15 → Task 3 (with D6 in 3.1, D13 noted in 3.2); D14 → Task 2; D16-D18 → Task 1; D19/D21 → Task 6; D20 → Task 7; D22 → Task 4; D23 → Task 5; verification requirements 1-16 → Task 8 (req 11 also in Task 1.7). The lstlisting content matches the spec's post-rename listing; the F2/F5 figures match the rev-12 audit-corrected content (one card value per commit, player tier present, position sets named).
- Placeholder scan: no TBD/TODO; every code step shows complete code; the two intentional `...` elisions inside listings are display elisions declared by their footnotes, not plan placeholders.
- Consistency: names introduced in Task 1 (`profile_eps`, `profile_k`, `protocol_of_profile`, `profile_recon_encode`, `profile_k_denboer`) are the ones Task 2's `profile_eps_pgl27` and Task 3's listing use; Task 5's caption forward-references `fig:fivecard-run` which Task 6 defines; Task 4 runs before Task 7 so the relocated paragraph's wording note in Step 7.1 is accurate.
