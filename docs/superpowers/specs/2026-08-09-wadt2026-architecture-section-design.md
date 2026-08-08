# WADT2026 Architecture Section Expansion — Design Spec

Date: 2026-08-09
Target: `pgg-smc/paper-wadt2026/main.tex`, Section 3.1 (Framework Architecture)
Status: draft for user review after Opus audit

## Goal

Expand Section 3.1 from three thin paragraphs into a concrete formalization-paper
architecture section: show how the framework records organize the specification
of a card-based protocol, and present the fulfill-one-record feature, in which a
completed `MonodromyProfile` value yields the runnable protocol roles and the
certified security characters by definition. Organization follows the wadtSep17
slides (`/Users/cheng-huiweng/Projects/aplas2024-poster/wadtSep17/slides.tex`,
frames "The specification: one MonodromyProfile", "SecurityWitness: certified
leakage", "Recovery is a separate component", "One flow, two protocol families").

## Verified source facts

Every claim in the new prose is grounded in one of these, checked 2026-08-09.

| Fact | Source |
|---|---|
| `MonodromyProfile` fields: `mp_M`, `mp_secretT`, `mp_PI`, `mp_security`, `mp_plug` | `pgg-smc/protocol/pgg_monodromy_profile.v:50-57` |
| Derived definitions `run_dealer`, `run_party`, `run_verifier`, `run_recover`, `run_eps`, `run_k`, `run_anonymous`, `run_private` in the `run_profile` section, all projections or generic assemblies over the record fields | `pgg-smc/protocol/pgg_monodromy_profile.v:63-110` |
| `PGGInterface` fields: `pi_T'`, `pi_starts`, `pi_starts_uniq` | `pgg-smc/protocol/pgg_interface.v:379-383` |
| `SecurityWitness` fields: `sw_L`, `sw_bound_eps`, `sw_rho_dist`, `sw_bound`, `sw_exact : option SecurityExact`, `sw_asymptotic : option SecurityAsymptotic` | `pgg-smc/reconstruct/algebraic_rigidity.v:147-160` |
| `SecurityExact` (equality), `SecurityAsymptotic` (floor + geometric decay `sa_eps_inf + sqrt(N)(1-gap)^L`) | `pgg-smc/reconstruct/algebraic_rigidity.v:90-137` |
| `ReconPlug` fields: `rp_scheme`, `rp_content`, `rp_monodromy`, `rp_recon_invariant` | `pgg-smc/reconstruct/covering_scheme.v:117-123` |
| `ThresholdScheme` fields: `ts_T'`, `ts_k'`, `ts_valid`, `ts_recon`, `ts_encode`, `ts_correct`, `ts_private`, `ts_encode_valid` | `pgg-smc/reconstruct/pgg_sharing_framework.v:47-65` |
| `InputEncoding` fields: `ie_assemble`, `ie_output`, `ie_assemble_valid`, `ie_orbit`; derived `ie_output_correct` | `pgg-smc/reconstruct/input_encoding.v:28-55` |
| Empty commit prologue degenerates to the plain dealer: `exchange_dealer_with_commit_nil` | `pgg-smc/protocol/pgg_input_commitment.v:145` |
| Generic input-commit dealer `dealer_with_input_encoding` | `pgg-smc/protocol/pgg_run.v:45` |
| Realized witness combinations: den Boer `Some`/`None` at eps 0 (`uniform_security_witness`), Kim `Some`/`Some` (`fc_kim_security_witness`), S5 `None`/`Some` (`s5_security_witness_schreier`), PGL `Some`/`None` at eps 0 (`pgl27_security`) | `pgg_uniform_security.v:186-190`, `five_card_kim.v:507-517`, `rigidity_s5_instance.v:202-208`, `pgl27_profile.v:97-99` |
| PGL profile value: `pgl27_profile = MkMonodromyProfile pgl27_M bool pgl27_PI pgl27_security pgl27_plug` | `pgg-smc/instances/pgl27/pgl27_profile.v:104-105` |
| `listings` package already loaded, no `\lstset` yet; `\coqin` = `\texttt` | `main.tex:12,21` |

## Record-to-theorem boundary (honesty baseline)

The new prose may claim only the following derivations.

Record path (consumed by paper results):
- `pi_starts`/`pi_starts_uniq` define the executed run; `pgl27_run_recovers` and
  the traces behind `pgl27_coalition_trace_secrecy` are stated over this layout.
- `ts_correct` and `ts_recon` feed Theorem A's correctness clause
  (`pgl27_run.v:177-191`).
- `ts_private` at threshold 4 is Theorem A's coalition bound, re-exported as
  `run_private`; the ramp propositions sharpen it per reveal count.
- `rp_recon_invariant` gives the for-every-shuffle quantifier in correctness.
- `sw_bound` with `sw_exact` at eps 0 certifies single-position endpoint
  uniformity, re-exported as `run_anonymous`/`run_eps`.
- `InputEncoding` feeds den Boer and Kim function-evaluation correctness only.

Theorem-side (bypasses the records; prose must NOT claim record derivation):
- Theorem 1 `ttrans_view_indep_gen` consumes three-transitivity of the action,
  the uniform shuffle, and distinct cards; `pgl27_view_indep` instantiates it
  (`pgl27_secrecy.v:81`). Theorems 2 and 3 are generic lemmas.
- All four Theorem B components: `pgl27_mixing.v` and `pgl27_word_privacy.v`
  never reference the records (grep verified). Kim's witness hosts its word
  bound inside `sw_bound`, so the record can carry a word-shuffle bound; the
  PGL instance keeps its word results theorem-side.

Unrelated fields (never oversold in prose): `sw_L` (bookkeeping tag),
`sw_asymptotic` for the PGL instance (`None`; hosts Kim's and S5's decay
certificates), `mp_secretT` (type plumbing), `ts_encode`/`ts_valid`/
`ts_encode_valid` (statement support), the `CoveringScheme`/`CoveringData`
genus layer (absent from this paper).

## Decisions

| # | Decision |
|---|---|
| D1 | Approach: reorganize Section 3.1 as one subsection following the slides' arc; no new sub-subsections, no renumbering. |
| D2 | One combined code listing: condensed `MonodromyProfile` record plus the derived `run_*` definitions, with elision comments. First and only listing in the paper. |
| D3 | Include the one-flow-two-families paragraph, introducing `InputEncoding` and the commit-prologue degeneration. |
| D4 | Wiring claims are bounded by the honesty baseline above: fulfilling the profile derives the runnable roles and re-exports eps and k with their certificates; coalition-view, trace, and word-shuffle theorems are stated separately and consume the action directly. One boundary sentence states this explicitly in the paper. |
| D5 | Symbol care: the paper's Equation 1 uses R for the real field; the recovery component is never written R (the slides' usage). The decoder stays "the decoder" or "the reconstruction component". |
| D6 | Listing style: add `\lstset{basicstyle=\ttfamily\scriptsize,columns=fullflexible,keepspaces=true,breaklines=true,xleftmargin=2mm,aboveskip=2pt,belowskip=2pt}` to the preamble (mirrors the slides). No language definition; plain text mode. |
| D7 | The listing carries a `\footnotemark`/`\footnotetext` naming `pgg-smc/protocol/pgg_monodromy_profile.v`, matching the paper's formalization-footnote convention. |
| D8 | The bridge table (`tab:bridge`) stays as the opener anchor; the architecture figure stays as the closing anchor with its caption extended to name the derived outputs. |
| D9 | The proof-mechanism encoding is presented as a compact table of REALIZED witness combinations (verified above), not the source comment's hypothetical list. |
| D10 | Prose rules carried over: no em-dashes, no prose semicolons, no parenthetical asides, "distribution" never "law", no abbreviations, Theorems A and B by literal text only, D14 prose-run cap (at most 3 consecutive prose paragraphs). |

## New Section 3.1 structure

Replaces `main.tex` lines 309-385 (current subsection body). Block order, each
with its anchor:

| # | Block | Anchor |
|---|---|---|
| 1 | Opener paragraph: an instance is specified by filling one record, `MonodromyProfile`, whose five fields carry the data of Equation 1 into the executable protocol; MathComp basis sentence kept; reference to `tab:bridge` | existing `tab:bridge` |
| 2 | Bridge table, unchanged content | table |
| 3 | The combined listing (draft below) with source footnote | new `lstlisting` |
| 4 | Duties paragraph + enumerated list: the three proof obligations an instance discharges (draft below) | itemize |
| 5 | Wiring paragraph: derived roles and characters, FORTE interpreter sentence, boundary sentence (draft below) | prose, at most 3 paragraphs |
| 6 | Proof-mechanism table + one lead-in sentence (draft below) | new small table |
| 7 | Two-families paragraph (draft below) | prose |
| 8 | Architecture figure, caption extended | existing figure |

## Draft content

### Block 3: the listing

```latex
\begin{lstlisting}
Record MonodromyProfile (R : realType) := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ; (* group, action, generators *)
  mp_secretT  : Type ;                           (* secret type               *)
  mp_PI       : PGGInterface mp_M ;              (* run layout                *)
  mp_security : SecurityWitness R mp_M ;         (* endpoint bound            *)
  mp_plug     : ReconPlug mp_M mp_secretT }.     (* decoder                   *)

Section run_profile.        (* derived for every profile mp *)
Definition run_dealer   ... := exchange_dealer PI (rp_content plug) ...
Definition run_party i      := exchange_player PI i.
Definition run_verifier     := exchange_verifier PI players.
Definition run_recover c    := ts_recon (rp_scheme plug) c.
Definition run_eps  : R     := sw_bound_eps (mp_security mp).
Definition run_k    : nat   := ts_k (rp_scheme plug).
Definition run_anonymous    := sw_bound (mp_security mp).
Definition run_private      := ts_private (rp_scheme plug).
\end{lstlisting}
```

Footnote text: "The record and the derived definitions are in
`pgg-smc/protocol/pgg_monodromy_profile.v`. The listing elides implicit
arguments and the dealer's word parameters."

### Block 4: duties

Lead-in: "Filling the record means discharging three proof obligations."
Then an itemize:

- The dealt deck is close to uniform: `sw_bound` bounds the distance of every
  single card position's marginal from the uniform distribution by
  `sw_bound_eps`.
- The threshold scheme recovers and hides: `ts_correct` decodes every valid
  share tuple to its secret, and `ts_private` makes coalitions below the
  threshold unable to distinguish two secrets.
- Reconstruction is shuffle-invariant: `rp_recon_invariant` states that a
  shuffle permutes the shares but never changes the recovered secret.

### Block 5: wiring

Content points, in order:

1. Once the record is filled, the `run_profile` section derives the dealer, the
   players, the verifier, and the recovery map as definitions over the fields,
   and re-exports the certified characters: the bound `run_eps` with its
   certificate `run_anonymous`, and the threshold `run_k` with its certificate
   `run_private`. No new proof obligation arises at wiring time.
2. The small process interpreter that executes the layout originates in the
   earlier FORTE development (existing sentence, kept, citation kept). The
   executed traces of Section 2 are its output.
3. Boundary sentence: "The record path certifies correctness, endpoint
   uniformity, and the sharing threshold. The coalition-view, trace, and
   word-shuffle theorems of Sections 5 and 6 are stated separately: they
   consume the transitivity of the action and the shuffle distribution
   directly, not the record fields." Follow with the existing forward
   reference to Section 4 as the worked instantiation.

### Block 6: proof-mechanism table

Lead-in sentence: "The two optional slots of the security witness encode the
proof mechanism, and the instances realize three of the four combinations."

| `sw_exact` | `sw_asymptotic` | Mechanism | Instance |
|---|---|---|---|
| present | absent | exact equality at eps 0, perfect endpoint uniformity | den Boer, this paper's instance |
| present | present | exact count with geometric decay in the word length | Kim |
| absent | present | spectral certificate with an imported gap premise | S5 |

(In LaTeX: a `tabular` in the paper's existing table style, `Some`/`None`
written as "present"/"absent"; the instance column for this paper's instance
uses `$\PG$`, which the paper already places in table cells at
`tab:instances`.)

### Block 7: two families

One paragraph: with an `InputEncoding`, a commit prologue collects the
players' inputs and assembles the dealt deck from them, so the same flow
evaluates a function of committed inputs, which is the den Boer and Kim case.
Its obligation `ie_orbit` puts equal-output inputs in one shuffle orbit, so the
revealed deck determines the output and nothing more. With no inputs the
prologue reduces by definition to the plain dealer
(`exchange_dealer_with_commit_nil`), which is the secret-sharing case this
paper's instance uses. Forward reference to Section 7's instance table.

### Block 8: figure caption extension

Append to the existing caption: "Filling the three component records yields
the derived protocol roles and the certified characters of the listing."

## Constraints

- All of D10 (style rules).
- The honesty baseline: no sentence may claim that Theorems 1, 2, 3, A, or B
  are derived from the records. Verified by re-reading the final prose against
  the Record-to-theorem boundary section of this spec.
- Every identifier in the listing and prose must appear verbatim in the cited
  source file (grep check before commit).
- Section 3.2 (Generic Theorems) body is unchanged. The only edit outside
  Section 3.1 is the preamble `\lstset` addition.
- Expected page growth: about one page (17 to 18). No page constraint is in
  force.

## Verification requirements

1. `latexmk -g -pdf -halt-on-error -interaction=nonstopmode main.tex` exits 0;
   `grep -E "^!" main.log` empty; no undefined or multiply-defined references.
2. Page count recorded before and after (expected 17 to 18).
3. Grep check: each of `mp_M`, `mp_secretT`, `mp_PI`, `mp_security`,
   `mp_plug`, `run_dealer`, `run_party`, `run_verifier`, `run_recover`,
   `run_eps`, `run_k`, `run_anonymous`, `run_private`, `sw_bound`,
   `sw_bound_eps`, `sw_exact`, `sw_asymptotic`, `ts_correct`, `ts_private`,
   `ts_recon`, `ts_k`, `rp_content`, `rp_scheme`, `rp_monodromy`,
   `rp_recon_invariant`, `ie_orbit`, `exchange_dealer`, `exchange_player`,
   `exchange_verifier`, `exchange_dealer_with_commit_nil` resolves in the
   named source file.
4. Style sweeps on the changed region: no em-dash, no prose semicolon, no
   "law", no parenthetical asides, no abbreviations.
5. D14 check on the new Section 3.1: no run of more than 3 consecutive prose
   paragraphs.
6. The boundary sentence is present and the wiring paragraph claims nothing
   beyond the honesty baseline.
7. Visual inspection of the compiled listing and both tables in the PDF (no
   overfull boxes in the listing, table fits the text width).

## Out of scope

- Any edit to Sections 2, 3.2, 4, 5, 6, 8, 9.
- Section 7 gains no new content (the two-families paragraph forward-references
  its existing table only).
- The genus and covering-scheme narrative stays out of the paper.
- No new theorem environments, no changes to Theorems A and B.
