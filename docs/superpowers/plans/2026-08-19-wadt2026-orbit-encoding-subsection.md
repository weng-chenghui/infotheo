# WADT 2026 Orbit Encoding Subsection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Reorganize the beginning of the PGL(2,7) construction so the paper gives a self-contained mathematical explanation of orbit encoding, static shuffle correctness, and the separate role of uniform three-transitivity in privacy.

**Architecture:** Keep the existing paper in one LaTeX source file. Replace the current PGL opening with three local subsections: orbit encoding, generators, and local views. Reuse the existing figures and formal results, but move them into dependency order and attach formal evidence only through block-title footnotes.

**Tech Stack:** LaTeX with LNCS theorem environments, TikZ, `latexmk`, Poppler rendering, and source-level prose scans.

**Spec:** `docs/superpowers/specs/2026-08-19-wadt2026-orbit-encoding-subsection-design.md`

## Global Constraints

- Modify only `pgg-smc/paper-wadt2026/main.tex` and normal local build artifacts.
- Do not modify any `.v` file or create a formalization request.
- Preserve the existing uncommitted `makebox` changes in the model and framework figures.
- Use a single authorial voice. Do not introduce “we” or “our”.
- Keep the prose plain and at the language level of the attached FORTE paper.
- Use mathematical notation to carry precision. Keep explanatory sentences short.
- Every theorem-like block with formal counterparts has a title footnote naming the source path and exact Rocq declarations.
- Distinguish card positions from card values and heart-position orbits from labelled-deck orbits.
- Use the paper's reindexing convention `(g\star D)(i)=D(\rho(g)(i))`, which gives `H(g\star D)=\rho(g)^{-1}\cdot H(D)`.
- State that orbit invariance proves correctness, not privacy.
- State the privacy transition only under an independent uniform element `g\leftarrow U_G`.
- Run LaTeX serially. No Rocq build is required because no formalization file changes.

---

### Task 1: Correct the framework's use of the input-orbit obligation

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex:475-485`

**Interfaces:**
- Consumes: the existing `InputEncoding` paragraph and the mathematical distinction fixed in the spec.
- Produces: an accurate bridge from equal-output input layouts to correctness, without claiming that `ie_orbit` proves `ie_output_correct`.

- [ ] **Step 1: Record the current paragraph and its source evidence**

Run:

```bash
nl -ba pgg-smc/paper-wadt2026/main.tex | sed -n '470,490p'
sed -n '24,58p' pgg-smc/reconstruct/input_encoding.v
```

Expected: the paper currently joins `ie_orbit` directly to `ie_output_correct`, while the Rocq proof uses `ie_assemble_valid` and `rp_recon_invariant`.

- [ ] **Step 2: Replace the inaccurate causal sentence**

Use this mathematical content in plain prose:

```latex
The realized encoding is den Boer's. Its orbit obligation places the
assembled layouts of equal-output inputs in one shuffle orbit. This property
relates different inputs that produce the same result. Correctness uses two
other facts: the assembled layout is valid, and reconstruction is invariant
under every allowed shuffle. It follows that the shuffled layout reconstructs
the intended output.
```

Keep the existing statements that Kim reuses the den Boer program and that an empty input list gives the no-input secret-sharing flow.

- [ ] **Step 3: Check the local claim and style**

Run:

```bash
sed -n '470,490p' pgg-smc/paper-wadt2026/main.tex
rg -n "ie_orbit.*ie_output_correct|derived lemma.*ie_output_correct" pgg-smc/paper-wadt2026/main.tex
```

Expected: the paragraph distinguishes equal-output orbit structure from shuffle correctness. The second command returns no match.

### Task 2: Rebuild the PGL opening around orbit encoding

**Files:**
- Modify: `pgg-smc/paper-wadt2026/main.tex:731-919`

**Interfaces:**
- Consumes: the existing run diagram, generator figure, generator example, encoded-representative figure, Orbit encoder lemma, Orbit split lemma, and Three-transitivity lemma.
- Produces: subsections `Orbit Encoding of the Secret`, `Action and Generators`, and `Three-Transitivity and Local Views`, with all existing labels preserved where they remain externally referenced.

- [ ] **Step 1: Introduce the acting set and two carriers before the new subsection**

Replace the current section opener with a short introduction containing:

```latex
Let
\[
  X=\mathbb P^1(\mathbb F_7)=\{0,1,\ldots,6,\infty\}.
\]
The group $G=\PG$ acts on the eight points of $X$ by fractional linear
transformations, and $|G|=336$. The formal representation writes the point
$\infty$ as position seven. Card positions belong to $X$, while card values
belong to $C=\{0,1,\ldots,7\}$.
```

Preserve Equation `eq:pgl-order` for the order `336` rather than duplicating an unlabelled display.

- [ ] **Step 2: Add the standard orbit definition**

Start `\subsection{Orbit Encoding of the Secret}` and add a definition block containing:

```latex
\Omega_4=\{A\subseteq X\mid |A|=4\},
\qquad
\operatorname{Orb}_G(A)=\{g\cdot A\mid g\in G\},
```

```latex
A\sim_G B \quad\Longleftrightarrow\quad
B\in\operatorname{Orb}_G(A).
```

Follow it with exactly the two reader-facing facts: an orbit is the set of heart-position patterns reachable by allowed shuffles, and every orbit in this subsection lies in `\Omega_4`, not in the space of fully labelled decks.

- [ ] **Step 3: Define decks, heart positions, the cross-ratio classifier, and decoding**

Add a titled definition with a footnote naming `is_heart`, `deck_ok`, `heart_set`, `cross_ratio`, `equianharmonic`, `subset_class`, and `orbit_class` in `pgl27_orbit.v`.

Its mathematical content is:

```latex
D:X\longrightarrow C \text{ is a bijection},
\qquad
H(D)=\{i\in X\mid D(i)\in\{0,1,2,3\}\}.
```

For `A=\{a<b<c<d\}` under `0<1<\cdots<6<\infty`, display:

```latex
[a,b;c,d]=\frac{(a-c)(b-d)}{(a-d)(b-c)},
\qquad
[a,b;c,\infty]=\frac{a-c}{b-c}.
```

Then define:

```latex
\kappa(A)=1 \Longleftrightarrow [a,b;c,d]\in\{3,5\},
\qquad
\operatorname{dec}(D)=\kappa(H(D)).
```

State that `1` is equianharmonic and `0` is harmonic. Display the typed path `D\xmapsto{H}\Omega_4\xmapsto{\kappa}\{0,1\}`.

- [ ] **Step 4: State the complete orbit classification theorem**

Replace the current count-only `Orbit split` block with a theorem labelled `thm:orbit-split`. Its title footnote names `subset_class_orbit`, `subset_class_orbitE`, `orbit_class_split`, and `orbit_class_split_complement`.

The visible statement contains:

```latex
\kappa(A)=\kappa(B)
\quad\Longleftrightarrow\quad
\exists g\in G,\ B=g\cdot A,
```

```latex
\Omega_4/G\cong\{0,1\},
\qquad
|\kappa^{-1}(0)|=42,
\qquad
|\kappa^{-1}(1)|=28.
```

Put the equivalence before the counts. Do not leave a second nearby theorem that repeats only the counts.

- [ ] **Step 5: Define and draw the two encoded representatives**

Add a definition block with a title footnote naming `orbit_encode` and `orbit_encode_deck`:

```latex
D_0=(0,1,2,3,4,5,6,7),
\qquad
D_1=(0,1,2,4,3,5,6,7),
\qquad
\operatorname{enc}(s)=D_s.
```

Move the existing `fig:encoding` immediately after this block. Preserve its visual design. Adjust the caption so it states card positions, card values, heart shading, `0 = harmonic`, and `1 = equianharmonic`.

- [ ] **Step 6: Add the decoding example and the complete forward map**

Replace the old `Orbit encoder` lemma with a titled example whose title footnote names `orbit_encodeK`. Display:

```latex
H(D_0)=\{0,1,2,3\},\quad \kappa(H(D_0))=0,
```

```latex
H(D_1)=\{0,1,2,4\},\quad \kappa(H(D_1))=1,
```

```latex
s\longmapsto D_s\longmapsto H(D_s)\xmapsto{\kappa}s,
\qquad
\operatorname{dec}(\operatorname{enc}(s))=s.
```

- [ ] **Step 7: Define the deck action and prove static shuffle correctness**

Add a lemma whose title footnote names `subset_class_invariant`, `orbit_class_invariant`, and `deck_stable`. The footnote says that the heart-set identity is the local equality `Hheart` inside the proof of `orbit_class_invariant`, not a public theorem.

Display:

```latex
(g\star D)(i)=D(\rho(g)(i)),
\qquad
H(g\star D)=\rho(g)^{-1}\!\cdot H(D),
```

```latex
g\star D\text{ is valid},
\qquad
\operatorname{dec}(g\star D)=\operatorname{dec}(D).
```

Then add a corollary titled `Shuffle correctness of orbit decoding`. Its footnote names `orbit_encodeK` and `orbit_class_invariant`, and identifies `orbit_recon_invariant` in `pgl27_scheme.v` as the packaged reconstruction counterpart. Display:

```latex
\operatorname{dec}(g\star\operatorname{enc}(s))
=\operatorname{dec}(\operatorname{enc}(s))=s.
```

End with the exact conceptual boundary from the spec: orbit invariance preserves the secret under every allowed shuffle, but does not itself hide it. Privacy begins under an independent uniform shuffle and uses three-transitivity as its group-action premise.

- [ ] **Step 8: Place the run diagram after the complete correctness chain**

Move `fig:run` here. Change the internal shuffle label from `\rho(g)D_s` to `g\star D_s`. Keep the caption's distinction between the uniform and word shuffle models.

- [ ] **Step 9: Restore generator material under a clear subsection**

Start `\subsection{Action and Generators}`. Move the existing three generator maps, `fig:pgl-generators`, and `ex:pgl-letters` here. Keep their formal footnote and mathematical content. Remove claims that define the orbit encoding a second time.

- [ ] **Step 10: Start privacy as a separate conceptual step**

Start `\subsection{Three-Transitivity and Local Views}` immediately before the existing Three-transitivity lemma. Introduce it with:

```latex
Global orbit invariance gives correctness. Privacy asks a different question:
what does a small named set of positions observe when
$g\leftarrow U_G$ is independent and uniform?
```

Retain the theorem statement and formal footnote. Rewrite the following paragraph so it says three-transitivity supplies the group-action premise of the later privacy theorem. It must not imply privacy under an arbitrary shuffle distribution.

- [ ] **Step 11: Run structural source checks**

Run:

```bash
rg -n '^\\subsection|Orbit|cross ratio|g\\star|three-transit|ie_orbit|ie_output_correct' pgg-smc/paper-wadt2026/main.tex
rg -n 'rho\(g\)D_s|random group element|Privacy follows from the transitivity' pgg-smc/paper-wadt2026/main.tex
```

Expected: the three new subsection titles and all required mathematical terms appear. The second command returns no stale PGL wording.

### Task 3: Build and inspect the revised paper

**Files:**
- Verify: `pgg-smc/paper-wadt2026/main.tex`
- Generate locally: `pgg-smc/paper-wadt2026/main.pdf` and normal LaTeX auxiliaries

**Interfaces:**
- Consumes: the complete LaTeX revision from Tasks 1 and 2.
- Produces: a clean PDF with stable references and readable PGL pages.

- [ ] **Step 1: Build the paper from its source directory**

Run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Working directory: `pgg-smc/paper-wadt2026`.

Expected: exit code `0` and `main.pdf` produced.

- [ ] **Step 2: Check warnings that affect correctness or layout**

Run:

```bash
rg -n "Undefined|multiply defined|Citation.*undefined|Reference.*undefined|Overfull|Underfull" main.log
```

Expected: no undefined citation or reference. Any box warning must be inspected at the reported line and either fixed or documented as pre-existing and harmless.

- [ ] **Step 3: Render the PGL pages for visual inspection**

Find the PGL section's page range with `pdftotext -layout main.pdf -`, then render those pages with `pdftoppm -png -f N -l M -r 150 main.pdf tmp/pdfs/orbit-encoding`.

Inspect every rendered page containing the new subsection. Verify:

- no clipped equation, theorem title, footnote, or TikZ figure;
- the encoded-deck figure stays next to its definition and example;
- the run diagram follows the static correctness chain;
- headings do not become isolated at the foot of a page;
- the math blocks remain readable at normal page scale.

- [ ] **Step 4: Rebuild after any layout correction**

Run the same `latexmk` command after each source correction. Repeat the warning scan and render inspection until the revised pages have no new layout defect.

### Task 4: Audit prose, mathematical fidelity, and completion

**Files:**
- Modify if needed: `pgg-smc/paper-wadt2026/main.tex`
- Verify: `docs/superpowers/specs/2026-08-19-wadt2026-orbit-encoding-subsection-design.md`

**Interfaces:**
- Consumes: the built and visually inspected paper.
- Produces: a final paper edit that satisfies the spec, uses plain language, and avoids AI-writing patterns.

- [ ] **Step 1: Compare every displayed claim with the formal source**

Check the revised blocks against:

```bash
sed -n '55,115p' pgg-smc/instances/pgl27/pgl27_orbit.v
sed -n '280,375p' pgg-smc/instances/pgl27/pgl27_orbit.v
sed -n '512,535p' pgg-smc/instances/pgl27/pgl27_orbit.v
sed -n '699,730p' pgg-smc/instances/pgl27/pgl27_orbit.v
sed -n '40,105p' pgg-smc/instances/pgl27/pgl27_scheme.v
```

Verify the cross-ratio convention, Boolean class assignment, orbit sizes, inverse-image action, encoder rows, and cited declaration names.

- [ ] **Step 2: Run the avoid-ai-writing audit in detect-only mode**

Audit only the revised framework paragraph and PGL section. Flag formulaic transitions, redundant summaries, fake contrasts, repeated conclusion sentences, heavy nominalizations, and prose that merely reads equations aloud.

Apply only findings that preserve every formula, scope condition, footnote, and claim. Keep first-person singular if an authorial choice must be stated. Do not introduce collective “we”.

- [ ] **Step 3: Run mechanical prose checks**

Run:

```bash
rg -n '—|;' pgg-smc/paper-wadt2026/main.tex
rg -n '\bwe\b|\bWe\b|\bour\b|\bOur\b' pgg-smc/paper-wadt2026/main.tex
rg -n 'not only|not merely|It is important|crucial|key insight|serves as|underscores|highlights' pgg-smc/paper-wadt2026/main.tex
```

Inspect hits in the revised scope. Equations and bibliography data are not prose findings.

- [ ] **Step 4: Perform final build and evidence checks**

Run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
rg -n "Undefined|multiply defined|Citation.*undefined|Reference.*undefined" main.log
git diff --check -- pgg-smc/paper-wadt2026/main.tex
```

Expected: build exit code `0`, no undefined references or citations, and no whitespace errors.

- [ ] **Step 5: Review the final diff and commit only the paper**

Run:

```bash
git diff -- pgg-smc/paper-wadt2026/main.tex
git status --short
git add pgg-smc/paper-wadt2026/main.tex
git diff --cached --check
git diff --cached --name-only
git commit -m "paper: explain orbit encoding in PGL instance"
```

Expected: the commit contains only `pgg-smc/paper-wadt2026/main.tex`. The earlier uncommitted `makebox` lines remain included because they already belong to this paper file and must not be discarded.
