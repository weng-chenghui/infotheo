# Orbit Encoding Subsection for the WADT 2026 Paper

Date: 2026-08-19

Target: `pgg-smc/paper-wadt2026/main.tex`

Scope: paper writing only. No Rocq source file may be changed.

## Goal

Add a dedicated mathematical subsection near the beginning of the
`PGL(2,7)` construction that lets a reader understand the following idea as
one continuous argument:

1. the shuffle group acts on four-element sets of card positions;
2. this action partitions those sets into two orbits;
3. the two orbits carry the two Boolean secrets;
4. the encoder chooses one deck whose heart positions represent each orbit;
5. every allowed shuffle stays inside the selected orbit, so decoding remains
   correct;
6. orbit invariance gives correctness, while privacy needs the later and
   separate three-transitivity argument.

The subsection must make this idea visible through notation, definitions,
displayed equations, theorem statements, and examples. Rocq identifiers must
not carry the explanation in the body. They serve only as footnoted evidence
for the mathematical blocks.

## Current readability problem

The existing paper contains the relevant facts but presents them in different
places:

- the section opener says that the decoder reads an orbit class before an
  orbit class has been defined;
- the group generators and their permutation tables precede the explanation
  of what the group action preserves;
- the current `Orbit split` lemma states the sizes `28` and `42`, but the
  visible statement omits the central equivalence saying that equal classifier
  values are exactly membership in the same orbit;
- the encoder round trip, shuffle invariance, and executed correctness appear
  in separate passages without a displayed derivation joining them;
- the paper does not promptly distinguish the orbit of a four-element set of
  positions from an orbit of a fully labelled deck;
- the body does not clearly say that orbit invariance proves correctness but
  not privacy.

This causes a dependency inversion. A reader sees how the generators move the
deck before learning why their action is useful.

## Placement and revised local structure

The beginning of Section `The PGL(2,7) Construction` will have this order:

1. **Section opener.** State that the instance uses the action of
   `PGL(2,7)` on the eight points of the projective line.
2. **Short group introduction.** Introduce
   `\mathbb P^1(\mathbb F_7)`, its eight points, the action, and
   `|PGL(2,7)|=336`. State that tuple position `7` represents the point
   `\infty`. Do not yet introduce the generator alphabet.
3. **New subsection: `Orbit Encoding of the Secret`.** Give the complete
   mathematical account specified below.
4. **Action and generator material.** Present the three generating maps, the
   generator figure, and the existing generator example.
5. **Three-transitivity material.** State how the action controls local
   observations and leads into the later privacy section.

The existing run diagram belongs after the seven mathematical blocks, the
displayed correctness chain, and the sentence separating correctness from
privacy. Its labels then reuse known terms instead of introducing “orbit
class” inside a figure caption. It must not interrupt the encoder, example,
invariance, and correctness sequence.

## Mathematical carriers and notation

Keep positions and card values as distinct carriers. Let

\[
  X=\mathbb P^1(\mathbb F_7)=\{0,1,\ldots,6,\infty\}
\]

be the eight card positions, and let

\[
  C=\{0,1,\ldots,7\}
\]

be the eight card values. A valid deck is a bijection `D:X\to C`. When a
deck is written as an eight-entry tuple, its entries are ordered by the
positions `0,1,\ldots,6,\infty`, so the last tuple position is written as
position `7` in the formal representation. The heart values are
`\{0,1,2,3\}\subset C`.

Let

\[
  \Omega_4=
  \left\{A\subseteq X\mid |A|=4\right\}.
\]

The group `G = PGL(2,7)` acts on `\Omega_4` through its action on the
projective line. For `A\in\Omega_4`, define

\[
  \operatorname{Orb}_G(A)=\{g\cdot A\mid g\in G\},
  \qquad
  A\sim_G B \iff B\in\operatorname{Orb}_G(A).
\]

This carrier must remain explicit. The secret is encoded by the orbit of the
four heart positions. The subsection must state visibly:

> Every orbit in this subsection is an orbit in `\Omega_4`. A labelled deck
> `D` supplies the heart-position representative `H(D)` of such an orbit.

The paper must not say or imply that every fully labelled deck of one secret
class lies in a single `G`-orbit.

For a valid deck `D`, define its heart-position set by

\[
  H(D)=\{i\in X\mid D(i)\in\{0,1,2,3\}\}.
\]

Thus `H(D)\in\Omega_4`. Let

\[
  \kappa:\Omega_4\longrightarrow\{0,1\}
\]

be the cross-ratio classifier. For

\[
  A=\{a<b<c<d\},
  \qquad 0<1<\cdots<6<\infty,
\]

define the projective cross ratio by

\[
  [a,b;c,d]
  =\frac{(a-c)(b-d)}{(a-d)(b-c)}
  \quad\text{in }\mathbb F_7.
\]

Because `\infty` is last in the chosen order, only `d` can equal `\infty`,
and then

\[
  [a,b;c,\infty]=\frac{a-c}{b-c}.
\]

Define

\[
  \kappa(A)=1
  \iff
  [a,b;c,d]\in\{3,5\}\subset\mathbb F_7.
\]

The value `1` is the equianharmonic class. The complementary value `0` is the
harmonic class, whose cross-ratio values are `\{2,4,6\}`. Define the deck
decoder by

\[
  \operatorname{dec}(D)=\kappa(H(D)).
\]

The prose may give one short sentence about why a projective transformation
preserves this two-valued classification. It must not expand into a derivation
of the cross-ratio formula or its cases at infinity. Those details do not help
the reader understand the encoding pattern.

The shuffle convention must also be explicit. Let `\rho:G\to S_X` be the
permutation action, and write the shuffled deck as `g\star D`, where

\[
  (g\star D)(i)=D(\rho(g)(i)).
\]

Under this reindexing convention,

\[
  H(g\star D)=\rho(g)^{-1}\!\cdot H(D).
\]

The inverse is essential. It must not be replaced by
`H(g\star D)=\rho(g)\cdot H(D)`. Since the group is closed under inverses,
the two heart-position sets still lie in the same orbit.

## Required mathematical blocks

### 1. Definition: orbits of four positions

The first block defines `\Omega_4`, `\operatorname{Orb}_G(A)`, and
`\sim_G`. Its interpretation is one sentence: an orbit contains exactly the
heart-position patterns reachable from one another by allowed shuffles.

This block uses standard group-action notation. It does not need to describe
the Rocq representation of finite sets or permutations.

### 2. Definition: heart-position map and decoder

The second block distinguishes `X` from `C`, defines valid decks, heart card
values, `H`, `\kappa`, and `\operatorname{dec}`. The title
must carry a footnote citing:

- `pgg-smc/instances/pgl27/pgl27_orbit.v`;
- `is_heart`;
- `deck_ok`;
- `heart_set`;
- `cross_ratio`;
- `equianharmonic`;
- `subset_class`;
- `orbit_class`.

The body contains only the mathematical definitions and the mapping

\[
  D\xmapsto{H}\Omega_4\xmapsto{\kappa}\{0,1\}.
\]

### 3. Theorem: the two orbit classes

The visible theorem must state both classification and size. For all
`A,B\in\Omega_4`,

\[
  \kappa(A)=\kappa(B)
  \iff
  \exists g\in G,\ B=g\cdot A,
\]

Equivalently, the classifier induces

\[
  \Omega_4/G\cong\{0,1\}.
\]

State the orbit equivalence before the secondary counting fact

\[
  |\kappa^{-1}(0)|=42,
  \qquad
  |\kappa^{-1}(1)|=28.
\]

The theorem title must carry a footnote citing the same source file and:

- `subset_class_orbit`;
- `subset_class_orbitE`;
- `orbit_class_split`;
- `orbit_class_split_complement`.

The theorem must identify value `0` with the harmonic orbit and value `1`
with the equianharmonic orbit. The count alone is not an adequate substitute
for the orbit equivalence.

### 4. Definition: the encoder

The encoder chooses one valid deck from each class:

\[
  D_0=(0,1,2,3,4,5,6,7),
\]

\[
  D_1=(0,1,2,4,3,5,6,7),
  \qquad
  \operatorname{enc}(s)=D_s.
\]

The title must carry a footnote citing:

- `pgg-smc/instances/pgl27/pgl27_orbit.v`;
- `orbit_encode`;
- `orbit_encode_deck`.

The current two-row card figure remains here as the visual example of these
two representatives. The caption must keep its existing explanation of card
positions, card values, and heart shading, and it must state the mapping
`0 = harmonic` and `1 = equianharmonic` plainly.

### 5. Example: decoding the representatives

The example title must carry a footnote citing
`pgg-smc/instances/pgl27/pgl27_orbit.v` as `orbit_encodeK`. The definition
block above cites `orbit_encode` and `orbit_encode_deck`, while this example
cites the round-trip fact where it is used.

The example computes

\[
  H(D_0)=\{0,1,2,3\},
  \qquad
  \kappa(H(D_0))=0,
\]

\[
  H(D_1)=\{0,1,2,4\},
  \qquad
  \kappa(H(D_1))=1.
\]

It concludes

\[
  \operatorname{dec}(\operatorname{enc}(s))=s.
\]

It must also display the whole forward path once:

\[
  s\longmapsto D_s
   \longmapsto H(D_s)
   \xmapsto{\kappa}s.
\]

This example must explain the two rows of the figure without repeating its
caption in prose.

### 6. Lemma: invariance under shuffling

For every `g\in G` and every valid deck `D`, first define the deck action by

\[
  (g\star D)(i)=D(\rho(g)(i)),
\]

and state

\[
  H(g\star D)=\rho(g)^{-1}\!\cdot H(D).
\]

Then state both validity preservation and decoder invariance:

\[
  g\star D\text{ is valid},
  \qquad
  \operatorname{dec}(g\star D)=\operatorname{dec}(D).
\]

The title must carry a footnote citing:

- `pgg-smc/instances/pgl27/pgl27_orbit.v`;
- `subset_class_invariant`;
- `orbit_class_invariant`;
- `deck_stable`.

The footnote must also say that the inverse-image equation for `H` is the
local equality named `Hheart` inside the proof of `orbit_class_invariant`.
It is not a separate top-level theorem. The footnote must not present
`Hheart` as a public declaration.

The body must not discuss proof scripts or finite enumeration. One sentence
must explain that `\rho(g)^{-1}\in G`, so shuffling changes the representative
inside `\Omega_4` but not its orbit label.

### 7. Corollary: correctness of orbit encoding

For every `s\in\{0,1\}` and every `g\in G`, display the complete chain

\[
\begin{aligned}
  \operatorname{dec}(g\star\operatorname{enc}(s))
    &=\operatorname{dec}(\operatorname{enc}(s))\\
    &=s.
\end{aligned}
\]

The title must carry a footnote saying that the direct equality is formalized
by:

- `pgg-smc/instances/pgl27/pgl27_orbit.v` as `orbit_encodeK` and
  `orbit_class_invariant`.

The same footnote may add that
`pgg-smc/instances/pgl27/pgl27_scheme.v` packages this equality for the
reconstruction interface as `orbit_recon_invariant`. It must distinguish the
direct mathematical evidence from this packaged counterpart.

This is a static correctness statement. It must not be called executed
correctness. The later proposition `Executed correctness` remains in the
correctness section because it also needs the interpreter endpoint theorem.

## Readability requirements

The subsection is mathematical, but it must remain readable without the
formal source. It must satisfy all of the following:

1. Every symbol is introduced before its first use.
2. Each block has one job. It either defines an object, classifies the orbits,
   gives the representatives, establishes invariance, or derives correctness.
3. Each displayed statement is followed by at most two short sentences that
   explain its role. The prose must not read the formula aloud.
4. The carrier changes are visible in both directions used by the argument:
   `secret -> representative deck -> heart-position set -> orbit label` and
   `deck -> heart-position set -> orbit label`.
5. The reader sees the phrase “reachable by allowed shuffles” immediately
   after the orbit definition.
6. The reader sees the assignment `0 = harmonic` and
   `1 = equianharmonic` before meeting `D_0` and `D_1`.
7. The correctness chain appears in one place and requires no backward search.
8. The subsection ends with the boundary:

   > Orbit invariance preserves the secret under every allowed shuffle. It
   > does not by itself hide the secret. Under an independent uniform shuffle
   > `g\leftarrow U_G`, privacy begins with the distribution of partial
   > observations and uses three-transitivity as its group-action premise.

9. No body paragraph names `MonodromyProfile`, `ThresholdScheme`, record
   fields, source files, proof scripts, kernel computations, or theorem
   identifiers.
10. Formal evidence appears only in footnotes attached to the corresponding
    block titles.
11. The prose uses the same plain English level as the rest of the paper.
    Mathematical notation carries the precision. Sentences remain short.
12. The subsection does not introduce topology, covering spaces, monodromy,
    or the origin story of the construction.

## Transition into and out of the subsection

The paragraph before the subsection introduces only the acting group and the
eight-point set. It must make the reader ask what invariant of this action can
carry a secret.

After the seven blocks and the correctness/privacy boundary, place the current
run diagram. The paragraph after that diagram introduces the generators as a physical
and computational realization of the already-defined action. It should say
that the generators implement the allowed shuffles, while every word in them
preserves the orbit label established above.

The three-transitivity passage must begin a new conceptual step. It must say
that global invariance explains correctness, whereas privacy concerns what a
small named set of positions observes under an independent uniform group
element `g\leftarrow U_G`. Three-transitivity supplies the group-action
premise for the privacy proof. It is not by itself the full privacy argument.
The nonuniform word distribution belongs to the later approximate analysis.

## Distinguish the two uses of orbit in the paper

The revision must not merge the PGL orbit encoding with the earlier
`InputEncoding` discussion.

- In the PGL construction, the Boolean secret is the orbit label of a
  four-element heart-position set. Different secrets select different
  orbits.
- In the five-card input encoding, inputs with the same function output have
  assembled layouts in the same shuffle orbit.

The earlier framework sentence claiming that `ie_orbit` derives
`ie_output_correct` must be corrected when this paper edit is implemented.
The correctness lemma follows from valid assembly and reconstruction
invariance. The equal-output orbit field supports the relationship among
encodings of inputs with the same output. The new PGL subsection must not be
used to justify that separate five-card claim.

## Existing material to preserve or move

Preserve the following content, with only the changes needed for the new
dependency order:

- the eight-point description of `\mathbb P^1(\mathbb F_7)`;
- the group order `336`;
- the run diagram;
- the generator maps and their card-row figure;
- the generator example;
- the two encoded-representative figure;
- the formal evidence currently attached to the encoder, orbit split, and
  three-transitivity results;
- the later executed correctness, recovery, privacy, and word-shuffle
  statements.

The revision may merge or rename the current visible `Orbit encoder` and
`Orbit split` blocks when their claims are covered exactly by the required
blocks above. It must not duplicate the same theorem statement in two nearby
blocks.

## Non-goals

- No change to any `.v` file.
- No new formalization request.
- No claim that orbit encoding alone proves privacy.
- No claim that all valid labelled decks of one secret form one orbit.
- No full tutorial on cross ratios or projective geometry.
- No change to Theorem A or Theorem B.
- No change to the security model, adversary model, or word-shuffle bound.
- No new informal proof that exceeds the formalized theorem statements.

## Evidence map

| Mathematical claim | Formal source | Declarations |
|---|---|---|
| Valid decks, heart values, heart-position set, and classifier | `pgg-smc/instances/pgl27/pgl27_orbit.v` | `deck_ok`, `is_heart`, `heart_set`, `subset_class`, `orbit_class` |
| Cross-ratio classification | `pgg-smc/instances/pgl27/pgl27_orbit.v` | `cross_ratio`, `equianharmonic` |
| Classifier fibers are orbits | `pgg-smc/instances/pgl27/pgl27_orbit.v` | `subset_class_orbit`, `subset_class_orbitE` |
| Orbit sizes | `pgg-smc/instances/pgl27/pgl27_orbit.v` | `orbit_class_split`, `orbit_class_split_complement` |
| Encoded representatives | `pgg-smc/instances/pgl27/pgl27_orbit.v` | `orbit_encode`, `orbit_encode_deck` |
| Representative decoding example | `pgg-smc/instances/pgl27/pgl27_orbit.v` | `orbit_encodeK` |
| Shuffle invariance | `pgg-smc/instances/pgl27/pgl27_orbit.v` | `subset_class_invariant`, `orbit_class_invariant`, `deck_stable` |
| Heart-set inverse image under the deck action | proof of `orbit_class_invariant` in `pgg-smc/instances/pgl27/pgl27_orbit.v` | local equality `Hheart`, not a public declaration |
| Reconstruction invariance | `pgg-smc/instances/pgl27/pgl27_scheme.v` | `orbit_recon_invariant` |
| Executed endpoint correctness, retained later | `pgg-smc/instances/pgl27/pgl27_run.v` | `pgl27_run_recovers` |

## Audit requirements

Before implementation, a read-only adversarial reviewer must audit this spec
against the current paper and formal evidence. The reviewer must focus on a
reader who knows elementary group actions but has not read the Rocq source.
The report must answer:

1. Can the reader state in one sentence what object carries the secret?
2. Can the reader distinguish a heart-position orbit from a labelled-deck
   orbit?
3. Does the notation make the path
   `secret -> representative deck -> heart-position set -> orbit label`
   recoverable without inference?
4. Does the classification theorem visibly say that classifier fibers equal
   orbits?
5. Does the text define the deck action, expose the inverse-image equation for
   heart positions, and thereby explain why every shuffle preserves
   correctness?
6. Does it avoid suggesting that orbit invariance proves privacy?
7. Are the cross-ratio details sufficient to ground `\kappa` without
   interrupting the main idea?
8. Are any definitions introduced too early, too late, or under an unclear
   title?
9. Are any theorem blocks mathematically redundant?
10. Do the footnotes support exactly the claims in their blocks?

Any NO-GO finding must identify the precise dependency or reader inference
that fails and propose the smallest correction to the spec.

## First adversarial audit and resolutions

The first readability audit returned `NO-GO`. Its findings are resolved in
this version as follows.

| Finding | Resolution |
|---|---|
| The deck action was undefined and hid an inverse | Define `g\star D` and require `H(g\star D)=\rho(g)^{-1}\cdot H(D)` visibly. |
| Position and card-value carriers were conflated | Introduce separate carriers `X` and `C`, define a deck as `D:X\to C`, identify position `7` with `\infty`, and list the four heart values. |
| The deck-orbit distinction was only a prohibition | Require a visible positive sentence saying that all orbits in the subsection lie in `\Omega_4` and a deck supplies `H(D)`. |
| The privacy transition allowed an arbitrary random shuffle | Require an independent uniform element `g\leftarrow U_G` and describe three-transitivity as one group-action premise. |
| The classifier `\kappa` was not reproducibly defined | Fix the point order, display the cross-ratio formula and its only needed `\infty` specialization, and state the equianharmonic and harmonic value sets. |
| The forward path still had to be assembled by the reader | Add `s\mapsto D_s\mapsto H(D_s)\xmapsto{\kappa}s` to the representative example. |
| The run diagram could interrupt the correctness chain | Place it only after Block 7 and the correctness/privacy boundary. |
| Evidence was attached to overly broad or wrong blocks | Cite `orbit_encode` and validity at the encoder, `orbit_encodeK` at the example, validity and invariance at the invariance lemma, and distinguish direct from packaged correctness evidence. |

The second audit found two remaining evidence and definition gaps. This
version resolves them by displaying the cross-ratio formula, adding
`is_heart` and `deck_ok` to the decoder block's footnote, and identifying the
heart-set inverse-image equation honestly as the local equality `Hheart`
inside the proof of `orbit_class_invariant`.

## Acceptance criteria

The design is ready for an implementation plan only when:

- the adversarial readability audit has no unresolved blocking finding;
- the spec contains no `TBD`, `TODO`, placeholder, or pending decision;
- the subsection has one explicit carrier, one classifier, one encoder, one
  invariance statement, and one correctness derivation;
- correctness and privacy are separated in both structure and prose;
- every nonstandard mathematical block has a precise formal-evidence footnote;
- the existing paper claims remain unchanged outside the identified
  clarification of `ie_orbit`;
- implementation is confined to
  `pgg-smc/paper-wadt2026/main.tex` and its normal LaTeX build artifacts.
