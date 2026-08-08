# WADT2026 Paper Restructure — Design Spec

Date: 2026-08-08
Target: `pgg-smc/paper-wadt2026/main.tex` (839 lines, 15 pages, llncs)
Source audit: scratchpad `wadt2026-structure-map.md` (session 974905e1); all line
numbers below refer to the current working-tree `main.tex`.

## 1. Goal

Restructure the paper so that two headline theorems visibly organize every
other result, the introduction states the core claims, the model section opens
with a protocol narrative, the framework architecture is explained rather than
listed, every theorem has a lead-in, and section seams connect. All eight
`\greg{}` notes are resolved and removed. Content of existing formal claims is
preserved exactly; only structure, prose, and result levels change.

## 2. Locked decisions

| # | Decision | Choice |
|---|---|---|
| D1 | Headline style | Informal "Theorem A"/"Theorem B" displayed in the introduction via unnumbered `\spnewtheorem*` environments; formal capstone theorems at the end of Sections 5 and 6 reusing the same names. Supporting results demoted to Lemma/Proposition. The three generic framework theorems stay Theorems. |
| D2 | Source-index tables | The three tables (lines 389, 468, 555) merge into one consolidated table at the end of Section 7, grouped construction / correctness-recovery / privacy, referenced from Sections 4–6. |
| D3 | Page budget | None for this pass. Trim later once the submission format is confirmed. |
| D4 | Recovery ramp | The ramp result is restricted to the recovery side (seven positions determine the class, at most six stay ambiguous, the fixed four-position witness gives sharpness). The full triple (t,r,n)=(3,7,8) is assembled only in Theorem A. Removes the privacy-claim duplication between lines 440–456 and 495–509. |
| D5 | Theorem A placement | Capstone at the end of Section 5, assembled from the section's propositions. Section opener announces it as the destination. Same pattern for Theorem B in Section 6. |
| D6 | Trust base | The floating axioms paragraph (548–553) moves to Section 7 and merges with the S5 Rayleigh-axiom discussion (736–741) into a short consolidated trust-base passage next to the coverage table, which already has a trust-base column. |
| D7 | Abstract | Unchanged in this pass. It already states both results in order. |
| D8 | New citation | Add Shamir, "How to share a secret", CACM 1979 to `references.bib` (currently absent). Verify via research-kb before citing. |
| D9 | Sequence diagram | Adapt the Dealer/Players/Verifier lifeline TikZ diagram from `~/Projects/aplas2024-poster/wadtSep17/slides.tex` (the S5xS5 variant near line 398, the closest structural match: dealt secret, no player inputs) to PGL. Labels use reader-meaning vocabulary, never Rocq identifiers. |
| D10 | Figure 2 relabeling | Architecture-diagram boxes relabeled by role (protocol layout; shuffle-security bound; reconstruction; profile bundle; supporting records). Rocq record names move to the caption. |

## 3. Theorem re-leveling table

Every current environment, its disposition, and its new home. "Footnote"
means the Rocq source-name footnote, which must survive every move.

| Current (line) | Current title | New level | New home | Notes |
|---|---|---|---|---|
| 295 | Generic coalition privacy | Theorem (keep) | §3.2 | Add lead-in with instantiation pointer (t-transitivity, discharged in §4). |
| 307 | Generic trace lifting | Theorem (keep) | §3.2 | Add lead-in. |
| 319 | Data processing | Theorem (keep) | §3.2 | Add lead-in. |
| 350 | Orbit encoder | Lemma | §4 | One-sentence lead-in. |
| 361 | Orbit split | Lemma | §4 | Existing bridge prose kept. |
| 373 | Three-transitivity | Lemma | §4 | Followed by explicit discharge sentence: this lemma discharges the hypothesis of the generic coalition-privacy theorem with t = 3. |
| 417 | Executed correctness | Proposition | §5.1 | Unchanged statement. |
| 440 | Recovery ramp | Proposition | §5.1 | Restricted per D4; keeps recovery footnotes; the k=4 sharpness witness stays in the following prose or as part of the statement. |
| 495 | Perfect privacy, fixed dealer | Proposition | §5.2 | Feeds Theorem A. |
| 516 | All-decks privacy | Proposition | §5.2 | Framed as robustness check (lead-in at 511–514 already does this). |
| 537 | Shuffle-free privacy | Proposition | §5.2 | Framed as robustness check. |
| NEW | **Theorem A** (uniform-shuffle security of the PGL instance) | Theorem, named | end §5 | Bundles executed correctness, (t,r,n)=(3,7,8), and perfect view and trace privacy for coalitions of at most three, under the uniform Boolean prior, fixed representative dealer, passive adversaries. Footnote lists all constituent Rocq names. |
| 596 | Word-shuffle mixing bound | Lemma | §6 | The checked certificate. |
| 612–624 | Endpoint transfer (prose Eq. 4) | Lemma | §6 | Promoted from inline equation. |
| 626–639 | Product transfer (prose Eq. 5) | Lemma | §6 | Promoted from inline equation. |
| 651 | Word-shuffle coalition privacy | folded into Theorem B | end §6 | Statement becomes clauses of B. |
| NEW | **Theorem B** (word-shuffle security) | Theorem, named | end §6 | Clauses: (i) unhalved L1 distance of mu*200 from U_G at most 2^-40; (ii) coalition view and executed-trace privacy within 2^-39 for coalitions of at most three, fixed representative dealer; (iii) executed correctness unchanged for every word. Footnote: `pgl27_word_mixing`, `pgl27_word_view_indist`, `pgl27_word_trace_indist`, `pgl27_word_run_recovers`. |

LaTeX mechanics: two starred environments via `\spnewtheorem*` (llncs), e.g.
`thmA` printing "Theorem A", used twice each: once in Section 1 with an
"(informal)" bracket title, once formally in the home section. Numbered
environments keep llncs defaults; all `\ref`s updated after re-leveling.

## 4. Informal headline statements (draft, for Section 1)

> **Theorem A (informal).** Under the uniform shuffle distribution, with a
> uniform Boolean secret and the fixed representative dealer, the PGL(2,7)
> instance recovers the secret from all eight endpoints for every shuffle, has
> recovery parameters (t,r,n) = (3,7,8), and gives perfect view and
> executed-trace privacy against every passive coalition of at most three
> players.

> **Theorem B (informal).** The 200-letter word shuffle over the five
> generator letters is within unhalved L1 distance 2^-40 of the uniform
> shuffle distribution. The instance keeps exact correctness and gives view
> and executed-trace privacy within 2^-39 against the same coalitions.

Both informal statements must carry the hedges of the formal versions
(uniform Boolean prior, fixed representative dealer, passive adversaries);
the math audit checks informal-formal agreement clause by clause.

## 5. Per-section changes

### Section 1 — Introduction (63–128)

| Change | Detail |
|---|---|
| Delete 84–89 | Accepted-abstract history paragraph (greg 83). Barrington deferral already lives in the conclusion. |
| Delete 110–119 | Compressed model dump (greg 104/106/108). Content survives in §2. |
| New paragraph: why two distributions | After the gap paragraph (73–81). Story: the uniform shuffle is the ideal object of the security analysis, but no dealer samples a uniform group element physically; a dealer repeats simple cuts, which yields a word distribution; the paper proves the ideal results and proves the physical implementation approximates them. |
| New paragraph: "Overall" + informal A and B | The two `\spnewtheorem*` displays from §4 of this spec, introduced by one sentence naming the core result pair. |
| Keep | Context paragraph (65–71), contributions list (91–102), roadmap (121–128, references updated). |

Resulting spine: context, gap and approach, why two distributions, overall
claim with informal A and B, contributions, roadmap.

### Section 2 — Model (130–239)

| Change | Detail |
|---|---|
| New opening: protocol narrative + sequence diagram | Two to three paragraphs walking through a run before any formula: the dealer encodes the secret as a deck, samples a shuffle, deals one card to each player, players reveal to the verifier, the verifier decodes. New TikZ figure per D9: actors Dealer, Players 0..7 (collapsed with a brace), Verifier; messages "encode secret s as orbit-class deck D_s", "sample shuffle g, deal rho(g) D_s", reveal arrows, "decode orbit class". The shuffle node stays distribution-agnostic; the caption says g is drawn from U_G in the uniform model and from mu*L in the word model, tying both models to one physical flow. |
| Formal data (133–145) | Kept, now after the narrative (resolves greg 132). |
| Views and traces (146–157) | Kept. |
| Dealer variants (158–169) | Rewritten in generic vocabulary (fixed-representative dealer, all-decks dealer). Instance footnotes naming `pgl27P`, `orbit_encode`, `pgl27P_alldecks` move to §5 where the objects are instantiated. |
| Security framing (171–183) | Positive reframing (greg 179/180): state what is protected, a dealt secret against coalitions of curious players, the same object a secret-sharing scheme protects, cite Shamir (D8); then one sentence on exclusions (active deviation, post-reveal, composition). |
| Word model (185–199) | Add a motivation sentence before the definition (greg 185): the word model is what the dealer of the narrative actually performs. Add the operational meaning sentence after Eq. tv-definition (greg 198): a total variation bound of 2^-41 means no observer, whatever test they apply, distinguishes the word shuffle from the uniform shuffle with advantage above 2^-41. |
| Unobserved-word assumption (202–210) | Kept; instance footnote (`exchange_dealer`, `pgl27_dealer_run`) moves to §5. |
| Fig models (212–239) | Kept at end of section, recaptioned as the map of the two headline theorems: upper path Theorem A, lower path Theorem B. |

### Section 3 — Framework (241–331)

| Change | Detail |
|---|---|
| New bridge paragraph | Maps Eq. model-data onto the records: the layout record carries the dealer, player, and verifier processes; the security-witness record carries the endpoint bound for the shuffle distribution; the reconstruction record carries the decoder against the action; the profile bundles the three. |
| New interpreter paragraph | Two sentences: where the interpreter lives in the framework and its FORTE ancestry (cite WengEtAl2025 here, not only in related work). |
| New instantiation-cost paragraph | What an instance must supply and what it gets back, forward-pointing to §4 as the worked instantiation. |
| Fig 2 relabeling (250–278) | Per D10. Boxes by role, Rocq names to caption. |
| Generic theorems (295–331) | Distribute the post-hoc paragraph (328–331) into per-theorem lead-ins: before generic coalition privacy, one sentence on what the instance must discharge (t-transitivity, distinct cards) with a forward pointer to §4; before trace lifting, one sentence (moves view independence to executed traces); before data processing, one sentence (transfers a group-distribution bound to any observable). |

### Section 4 — PGL construction (333–405)

| Change | Detail |
|---|---|
| New opening paragraph | The instantiation mapping: G = PGL(2,7), rho = the action on the eight projective points, mu = uniform on the five-letter symmetric generator tuple, decoder = orbit-class decoder. One sentence linking back to the instantiation-cost paragraph of §3. |
| Demotions | Orbit encoder, orbit split, three-transitivity become Lemmas with one-sentence lead-ins (existing bridges 357–359, 370–371 kept). |
| Explicit discharge sentence | After the three-transitivity lemma: it discharges the hypothesis of the generic coalition-privacy theorem with t = 3 (strengthens 383–387). |
| Table 389–405 | Removed here; content goes to the consolidated table (D2). |

### Section 5 — Uniform-shuffle results (407–579)

| Change | Detail |
|---|---|
| New opening sentence | Ties to the upper path of the Fig models map and announces Theorem A as the destination. |
| Correctness (417–425), distribution-free remark (427–432) | Kept; correctness becomes a Proposition. |
| Ramp (434–466) | Proposition restricted per D4; sharpness-witness prose (458–466) kept. |
| Privacy propositions (488–546) | Existing lead-ins kept; three theorems become Propositions; robustness framing for all-decks and shuffle-free. |
| Trust base (548–553) | Moved to §7 (D6). |
| NEW Theorem A | Formal capstone at section end, per the re-leveling table, with one assembling sentence before it. |
| Table 468–486, Table 555–579 | Removed here; content goes to the consolidated table (D2). |

### Section 6 — Word-shuffle results (581–681)

| Change | Detail |
|---|---|
| New opening paragraph | Recalls the word-shuffle model of §2, states the section goal (certify mixing, transport it to the security observables), announces Theorem B as the destination. |
| Generators and fiber method (583–594) | Kept after the opener. |
| Mixing bound (596–610) | Becomes a Lemma; certificate-inputs paragraph kept. |
| Transfers (612–649) | Become two Lemmas per the re-leveling table; TV restatement and chain-summary prose kept. |
| Word privacy (651–677) | Folded into Theorem B; the triangle-inequality proof sketch (669–677) kept as B's proof sketch. |
| Scope paragraph (679–681) | Kept as the section close. |

### Section 7 — Instances (683–747)

| Change | Detail |
|---|---|
| Reordered opener | The reuse question first (currently buried at 743–747): which arguments transfer unchanged across instances and which need instance-specific evidence. Drop "The repository contains" phrasing. |
| Coverage table (691–727) | Kept. |
| Per-instance paragraphs (729–747) | Kept, minus the sentences promoted to the opener. |
| Consolidated trust base | New short passage merging 548–553 with the Rayleigh discussion (736–741), placed next to the coverage table. |
| Consolidated source-index table | New table per D2 at section end, grouped construction / correctness-recovery / privacy, referenced from §§4–6. |

### Sections 8–9

Related work: unchanged. Conclusion: references to results renamed to
Theorems A and B; content otherwise unchanged.

## 6. Greg-note resolution map

| Note (line) | Resolved by |
|---|---|
| 83 (delete abstract diff) | §1 deletion of 84–89. |
| 104 (sudden jump, two models unexplained) | §1 why-two-distributions paragraph. |
| 106 (packed paragraph, move to sections) | §1 deletion of 110–119. |
| 108 ("Overall" style core claim) | §1 overall paragraph + informal A and B. |
| 132 (flow diagram first) | §2 narrative + sequence diagram (D9). |
| 179/180 (positive security framing, Shamir) | §2 security reframing + D8 citation. |
| 185 (sudden word model) | §2 word-model motivation sentence. |
| 198 (TV meaning) | §2 operational meaning sentence. |

All `\greg{}` commands are deleted once their items are implemented. The
`\def\greg` macro itself is removed when the last note goes.

## 7. Constraints

- Prose rules: no em-dashes, no parenthetical asides, no semicolons in new
  prose; explicit English connectors; "distribution", never "law"; no
  abbreviations in submitted prose; identifiers and narrative metaphors stay
  out of theorem names and diagram labels.
- Theorem-statement style: statement bodies are declarative mathematics only;
  strategy or design rationale goes to surrounding prose or comments.
- Every existing Rocq source-name footnote survives its move; no formal claim
  is strengthened, weakened, or re-scoped by the rewrite (D4 removes a
  duplicate, not a claim).
- Git hygiene: `main.tex` carries uncommitted `\greg{}` notes; commits of the
  rewritten paper use index surgery so unrelated working-tree changes stay
  uncommitted. `notes/` stays gitignored.
- llncs mechanics: `\spnewtheorem*` for the named A/B environments; numbered
  environments keep class defaults; `hyperref` refs must resolve.

## 8. Verification requirements (for the implementation plan)

1. `latexmk` build clean: no undefined references, no duplicate labels, no
   overfull layout regressions from the new figure and merged table.
2. Informal-formal agreement: clause-by-clause check of the §1 informal A and
   B against the formal capstones, hedges included.
3. Re-leveling audit: every `\ref` to a demoted or folded result updated;
   prose words "Theorem/Proposition/Lemma" match the environment they cite.
4. Citation check: Shamir 1979 metadata verified via research-kb before the
   `references.bib` entry lands; no other bibliography changes.
5. Jargon table for each new prose block over 200 words before finalizing.
6. Diagram check: rendered sequence diagram and relabeled architecture figure
   visually verified in the compiled PDF; labels use reader vocabulary.
7. Greg-note sweep: `grep -c 'greg' main.tex` returns zero at the end.
8. Prose-rule sweep over the diff: no em-dash, no semicolon, no parenthetical
   aside, no "law", in new or edited sentences.
