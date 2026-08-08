# WADT2026 Paper Restructure — Design Spec

Date: 2026-08-08 (revised same day after Opus adversarial audit, 17 findings applied)
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
| D1 | Headline style | Informal "Theorem A"/"Theorem B" displayed in the introduction via unnumbered `\spnewtheorem*` environments; formal capstone theorems at the end of Sections 5 and 6 reusing the same names. Supporting results demoted to Lemma/Proposition. The three generic framework theorems stay Theorems. The starred llncs environments do not step a counter, so Theorems A and B are referred to by literal text "Theorem A" / "Theorem B" everywhere, never by `\label`/`\ref`. |
| D2 | Source-index tables | The three tables (lines 389, 468, 555) merge into one consolidated table at the end of Section 7, grouped construction / correctness-recovery / privacy / mixing-transfers. The mixing-transfers group absorbs the Section 6 footnote names (643–645, 652–654, 675–677) so Section 6 has something to point at. None of the three current tables is `\ref`'d today, so every cross-reference is new work: Sections 4, 5, and 6 each gain one explicit reference sentence to the merged table. |
| D3 | Page budget | None for this pass, per user decision. Known accepted cost: the restructure adds roughly +1.5 to +2 pages, and a second trim pass will be needed once the submission format is confirmed. |
| D4 | Recovery ramp | The Proposition is retitled "Recovery ramp and sharpness". Its statement keeps the recovery side (seven positions determine the class, at most six stay ambiguous) and includes the fixed four-position leakage witness as an explicit sharpness clause, since the sharpness of t = 3 in Theorem A rests on it. The full triple (t,r,n)=(3,7,8) is assembled only in Theorem A. The Proposition, or the sentence directly before it, defines t, r, and n explicitly, because the current gloss at 452–455 is restructured and no other definition exists (the triple is used at lines 47, 705, 802). Removes the privacy-claim duplication between lines 440–456 and 495–509. |
| D5 | Theorem A placement | Capstone at the end of Section 5, assembled from the section's propositions. Section opener announces it as the destination. Same pattern for Theorem B in Section 6. |
| D6 | Trust base | The floating axioms paragraph (548–553) moves to Section 7 and merges with the S5 Rayleigh-axiom discussion (735–741) into a short consolidated trust-base passage next to the coverage table, which already has a trust-base column. Sections 5 and 6 each keep a one-sentence pointer at section end ("The trust base for these results is stated in Section 7"). |
| D7 | Abstract | One word-level edit only: "These privacy theorems" (line 49) becomes "These privacy results", since the referents become Propositions. Otherwise unchanged. |
| D8 | New citation | Add Shamir, "How to share a secret", CACM 1979 to `references.bib` (currently absent). Verify via research-kb before citing. |
| D9 | Sequence diagram | Adapt the Dealer/Players/Verifier lifeline TikZ diagram from `~/Projects/aplas2024-poster/wadtSep17/slides.tex` (the S5xS5 variant near line 398, the closest structural match: dealt secret, no player inputs) to PGL. Labels use reader-meaning vocabulary, never Rocq identifiers. Placed with `\begin{figure}[H]` (the `float` package is already loaded, main.tex line 7) so it renders before the formal data, which is the entire point of greg 132. Note the float-pressure interaction with the architecture figure's existing `[H]` at line 250. |
| D10 | Architecture figure (`fig:framework-architecture`) relabeling | Boxes relabeled by role (protocol layout; shuffle-security bound; reconstruction; profile bundle; supporting records). Rocq record names move to the caption. Figure numbering after the insertions: sequence diagram = Fig. 1, `fig:models` = Fig. 2, `fig:framework-architecture` = Fig. 3, encoding example (D12) = Fig. 4, recovery ramp (D13) = Fig. 5. All in-text uses are `\ref`s, so renumbering is automatic. |
| D11 | §3 bridge is a table, not a paragraph | The model-to-framework bridge is one lead sentence plus a table with columns: model datum from Eq. `eq:model-data` / record role / what the PGL instance supplies. The third column also does the work of §4's instantiation-mapping paragraph, which shrinks to one sentence pointing back at the table. |
| D12 | Encoding example figure (§4) | New TikZ figure: the two encoded representatives D_0 and D_1 as eight card slots labeled by projective points, hearts marked on the four-subset, caption stating that the secret is the orbit class of the heart positions (equianharmonic versus harmonic). Fidelity requirement: the depicted decks must match the actual `orbit_encode` output in `pgl27_orbit.v`, checked at implementation. |
| D13 | Recovery-ramp figure (§5) | New TikZ figure: a two-track number line over sizes 0..8. View track: perfect privacy for coalitions up to 3, the leaking fixed 4-coalition witness marked at 4. Reveal track: ambiguity through 6, class determination at 7, decoder reads 8. Makes (t,r,n)=(3,7,8) visible and makes the coalition-view versus reveal-set distinction explicit. |
| D14 | Prose-run cap | No section may run more than three consecutive paragraphs without a displayed equation, figure, table, itemize, or theorem-family environment. §1 is allowed four before the informal A/B displays. Enforced as verification item 9. |

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
| 417 | Executed correctness | Proposition | §5.1 | Unchanged statement. Delete or resize the `\Needspace` at 416, which was sized for a theorem and is stale after demotion. |
| 440 | Recovery ramp | Proposition | §5.1 | Restricted and retitled per D4; keeps recovery footnotes; the k=4 sharpness witness is a clause of the statement, not prose. |
| 495 | Perfect privacy, fixed dealer | Proposition | §5.2 | Feeds Theorem A. |
| 516 | All-decks privacy | Proposition | §5.2 | Framed as robustness check (lead-in at 511–514 already does this). |
| 537 | Shuffle-free privacy | Proposition | §5.2 | Framed as robustness check. |
| NEW | **Theorem A** (uniform-shuffle security of the PGL instance) | Theorem, named, unnumbered | end §5 | Bundles executed correctness, (t,r,n)=(3,7,8), and perfect view and trace privacy for coalitions of at most three, under the uniform Boolean prior, fixed representative dealer, passive adversaries. Footnote opens "This statement is the conjunction of the following formalized results:" and lists all constituent Rocq names. |
| 596 | Word-shuffle mixing bound | Lemma | §6 | The checked certificate. |
| 612–624 | Endpoint transfer (prose Eq. 4) | Lemma | §6 | Promoted from inline equation. |
| 626–639 | Product transfer (prose Eq. 5) | Lemma | §6 | Promoted from inline equation. |
| 651 | Word-shuffle coalition privacy | folded into Theorem B | end §6 | Statement becomes clauses of B. |
| NEW | **Theorem B** (word-shuffle security) | Theorem, named, unnumbered | end §6 | Clauses: (i) unhalved L1 distance of mu*200 from U_G at most 2^-40; (ii) for the fixed representative dealer and every passive coalition of at most three players, the coalition view distributions at the two secrets are within unhalved L1 distance 2^-39, and the executed coalition traces satisfy the same bound; (iii) executed correctness holds for every word. B never uses the bare word "privacy" without the distributional qualifier, since the entropy form is open (main.tex 814–816). Footnote opens with the conjunction phrase and lists `pgl27_word_mixing`, `pgl27_word_view_indist`, `pgl27_word_trace_indist`, `pgl27_word_run_recovers`. |

LaTeX mechanics: two starred environments via `\spnewtheorem*` (llncs), e.g.
`thmA` printing "Theorem A", used twice each: once in Section 1 with an
"(informal)" bracket title, once formally in the home section. The starred
path steps no counter, so no `\label` is ever placed inside these
environments and all references to A and B are literal text. Numbered
environments keep llncs defaults; all `\ref`s to demoted results updated.

## 4. Informal headline statements (draft, for Section 1)

> **Theorem A (informal).** The PGL(2,7) instance recovers the secret from
> all eight endpoints for every group element. Under the uniform shuffle
> distribution, with a uniform Boolean secret and the fixed representative
> dealer, it has recovery parameters (t,r,n) = (3,7,8) and perfect view and
> executed-trace privacy against every passive coalition of at most three
> players.

> **Theorem B (informal).** The 200-letter word shuffle over the five
> generator letters is within unhalved L1 distance 2^-40 of the uniform
> shuffle distribution. For the fixed representative dealer, the coalition
> view distributions at the two secrets are within unhalved L1 distance
> 2^-39 for every passive coalition of at most three players, and the
> executed coalition traces satisfy the same bound. Executed correctness
> holds for every word.

Correctness is stated distribution-free in A, matching its quantification
over every group element (main.tex 427–432), and is not scoped under the
uniform distribution. Per-theorem hedge lists: A carries the uniform Boolean
prior, the fixed representative dealer, and passive adversaries. B carries
the fixed representative dealer and passive adversaries only, and no secret
prior, because `pgl27_word_view_indist` and `pgl27_word_trace_indist`
quantify over both secrets with no prior. The math audit checks
informal-formal agreement clause by clause.

## 5. Per-section changes

### Section 1 — Introduction (63–128)

| Change | Detail |
|---|---|
| Delete 84–89 | Accepted-abstract history paragraph (greg 83). Barrington deferral already lives in the conclusion. |
| Delete 110–119 | Compressed model dump (greg 104/106/108). Every fact survives elsewhere except "the protocol has no private player inputs", which is added to the §2 security-framing content list below. |
| New paragraph: why two distributions | After the gap paragraph (73–81). Story, drafted to prose rules: the uniform shuffle is the ideal object of the security analysis. No dealer samples a uniform group element physically. A dealer repeats simple cuts, and the repeated cuts yield a word distribution. The paper proves the ideal results and proves that the physical implementation approximates them. The paragraph also says what group-based shuffles buy a card protocol (greg 104, second half): transitivity of the action yields coalition privacy, and generation by a small cut alphabet yields a finite implementation. |
| New paragraph: "Overall" + informal A and B | The two `\spnewtheorem*` displays from §4 of this spec, introduced by one sentence naming the core result pair. |
| Keep | Context paragraph (65–71), contributions list (91–102), roadmap (121–128, references updated). |

Resulting spine: context, gap and approach, why two distributions, overall
claim with informal A and B, contributions, roadmap.

### Section 2 — Model (130–239)

| Change | Detail |
|---|---|
| New opening: protocol narrative + sequence diagram | Two to three paragraphs walking through a run before any formula: the dealer encodes the secret as a deck, samples a shuffle, deals one card to each player, players reveal to the verifier, the verifier decodes. New TikZ figure per D9 with `[H]` placement: actors Dealer, Players 0..7 (collapsed with a brace), Verifier; messages "encode secret s as orbit-class deck D_s", "sample shuffle g, deal rho(g) D_s", reveal arrows, "decode orbit class". The shuffle node stays distribution-agnostic; the caption says g is drawn from U_G in the uniform model and from mu*L in the word model, tying both models to one physical flow. |
| Formal data (133–142) | Kept, now after the narrative (resolves greg 132). |
| Views and traces (144–156) | Kept. |
| Dealer variants (158–169) | Rewritten in generic vocabulary (fixed-representative dealer, all-decks dealer). Instance footnotes naming `pgl27P`, `orbit_encode`, `pgl27P_alldecks` move to §5 where the objects are instantiated. |
| Security framing (170–183) | Lines 170–177 are kept verbatim: they carry the adversary model and the paper's only definitions of coalition privacy and trace privacy, including Eq. `eq:trace-privacy`. Only 181–183 is rewritten, positively (greg 179/180): state what is protected, a dealt secret against coalitions of curious players, the same object a secret-sharing scheme protects, cite Shamir (D8); state that the protocol has no private player inputs (fact rescued from deleted 110–119); then one sentence on exclusions (active deviation, post-reveal, composition). |
| Word model (186–200) | Add a motivation sentence before the definition (greg 185): the word model is what the dealer of the narrative actually performs. Add the operational meaning sentence after line 200, where 2^-41 has been introduced (greg 198): a total variation bound of 2^-41 means no observer, whatever test they apply, distinguishes the word shuffle from the uniform shuffle with advantage above 2^-41. |
| Unobserved-word assumption (202–210) | Kept; instance footnote (`exchange_dealer`, `pgl27_dealer_run`) moves to §5. |
| Fig models (212–239) | Kept at end of section, recaptioned as the map of the two headline theorems: upper path Theorem A, lower path Theorem B. Becomes Fig. 2 per D10. |

### Section 3 — Framework (241–331)

| Change | Detail |
|---|---|
| New bridge table (D11) | One lead sentence, then the table mapping each datum of Eq. `eq:model-data` to its record role and to what the PGL instance supplies: the layout record carries the dealer, player, and verifier processes, the security-witness record carries the endpoint bound for the shuffle distribution, the reconstruction record carries the decoder against the action, the profile bundles the three. Anchor: the table itself, followed directly by the architecture figure. |
| New interpreter paragraph | Two sentences: where the interpreter lives in the framework and its FORTE ancestry (cite WengEtAl2025 here, not only in related work). Anchor: sits between the bridge table and the architecture figure. |
| New instantiation-cost paragraph | What an instance must supply and what it gets back, forward-pointing to §4 as the worked instantiation and to the bridge table's third column. Anchor: the bridge table. |
| Architecture figure relabeling (250–278) | Per D10. Boxes by role, Rocq names to caption. |
| Generic theorems (295–331) | Distribute the post-hoc paragraph (328–331) into per-theorem lead-ins: before generic coalition privacy, one sentence on what the instance must discharge (t-transitivity, distinct cards) with a forward pointer to §4; before trace lifting, one sentence (moves view independence to executed traces); before data processing, one sentence (transfers a group-distribution bound to any observable). |

### Section 4 — PGL construction (333–405)

| Change | Detail |
|---|---|
| New opening sentence | One sentence stating that this section supplies the third column of the §3 bridge table: G = PGL(2,7), rho = the action on the eight projective points, mu = uniform on the five-letter symmetric generator tuple, decoder = orbit-class decoder. Shrunk from a paragraph per D11. |
| New encoding example figure (D12) | Placed after the encoder prose (344–348), before or after the orbit-encoder Lemma: D_0 and D_1 as card rows, hearts on the four-subset, caption gives secret = orbit class. Anchors the encoder Lemma and the orbit-split Lemma. |
| Demotions | Orbit encoder, orbit split, three-transitivity become Lemmas with one-sentence lead-ins (existing bridges 357–359, 370–371 kept). |
| Explicit discharge sentence | After the three-transitivity lemma: it discharges the hypothesis of the generic coalition-privacy theorem with t = 3 (strengthens 383–387). |
| Table 389–405 | Removed here; content goes to the consolidated table (D2). One sentence referencing the merged table added. |

### Section 5 — Uniform-shuffle results (407–579)

| Change | Detail |
|---|---|
| New opening sentence | Ties to the upper path of the Fig. 2 map and announces Theorem A as the destination. |
| Correctness (416–425), distribution-free remark (427–432) | Kept; correctness becomes a Proposition; `\Needspace` at 416 deleted or resized. |
| Ramp (434–466) | Proposition restricted and retitled per D4, with the k=4 witness as a statement clause and an explicit definition of t, r, n; sharpness-witness prose (458–466) kept where not absorbed into the statement. |
| New recovery-ramp figure (D13) | Placed next to the ramp Proposition. Compensates for the two tables this section loses to D2, so §5 does not become the only anchor-free section. |
| Privacy propositions (488–546) | Existing lead-ins kept; three theorems become Propositions; robustness framing for all-decks and shuffle-free. |
| Trust base (548–553) | Moved to §7 (D6); one-sentence pointer stays at section end. |
| NEW Theorem A | Formal capstone at section end, per the re-leveling table, with one assembling sentence before it. |
| Table 468–486, Table 555–579 | Removed here; content goes to the consolidated table (D2). One sentence referencing the merged table added. |

### Section 6 — Word-shuffle results (581–681)

| Change | Detail |
|---|---|
| New opening paragraph | Recalls the word-shuffle model of §2, states the section goal (certify mixing, transport it to the security observables), announces Theorem B as the destination. |
| Generators and fiber method (583–594) | Kept after the opener. |
| Mixing bound (596–610) | Becomes a Lemma; certificate-inputs paragraph kept. |
| Transfers (612–649) | Become two Lemmas per the re-leveling table; TV restatement and chain-summary prose kept. |
| Word privacy (651–677) | Folded into Theorem B; the triangle-inequality proof sketch (669–677) kept as B's proof sketch. |
| Scope paragraph (679–681) | Kept, followed by the trust-base pointer sentence (D6) and one sentence referencing the merged table's mixing-transfers group (D2). |

### Section 7 — Instances (683–747)

| Change | Detail |
|---|---|
| Reordered opener | The reuse question first (currently buried at 743–747): which arguments transfer unchanged across instances and which need instance-specific evidence. Drop "The repository contains" phrasing. |
| Coverage table (691–727) | Kept. |
| Per-instance paragraphs (729–747) | Kept, minus the sentences promoted to the opener. |
| Consolidated trust base | New short passage merging 548–553 with the Rayleigh discussion (735–741), placed next to the coverage table. |
| Consolidated source-index table | New table per D2 at section end, four groups (construction / correctness-recovery / privacy / mixing-transfers), referenced from §§4–6. |

### Sections 8–9

Related work: unchanged. Conclusion: references to results renamed to
Theorems A and B (literal text, per D1); content otherwise unchanged. The
open-problem sentence at 814–816 (entropy form of approximate privacy) is
kept and is consistent with B's distributional phrasing.

## 5b. Non-prose anchor inventory

Guarantee against prose-after-prose: every section's anchors after the
restructure, with the gap each new element closes. New elements marked NEW.

| Section | Anchors after restructure | Longest prose run | Notes |
|---|---|---|---|
| §1 | contributions itemize, informal A and B displays | 3 paragraphs (context, gap, why-two) before the displays | Within the D14 allowance of four. |
| §2 | NEW sequence diagram (Fig. 1), Eq. model-data, Eq. coalition-view, Eq. trace-privacy, Eq. l1, Eq. tv, Fig. 2 map | 2–3 narrative paragraphs anchored by Fig. 1 | Already equation-rich. |
| §3 | NEW bridge table (D11), Fig. 3 architecture, three Theorem environments | interpreter + instantiation-cost paragraphs between table and figure | Was the worst risk: three abstract prose paragraphs; the table absorbs one and anchors the other two. |
| §4 | Eq. pgl-order, NEW encoding example figure (D12), three Lemma environments | 2 paragraphs | Example grounds the encoder and orbit-split Lemmas. |
| §5 | two Proposition environments + NEW ramp figure (D13) in 5.1; three Propositions + Theorem A in 5.2 | sharpness prose (458–466) | Was made anchor-free by D2's table removal; D13 compensates. |
| §6 | Eq. pgl-mixing, Eq. endpoint-transfer, Eq. product-transfer, three Lemmas, Theorem B | certificate-inputs + TV + chain paragraphs, each adjacent to a display | No new element needed. |
| §7 | coverage table (two parts), NEW merged source table | per-instance paragraphs between tables | No new element needed. |
| §8–9 | none (citation prose, conclusion) | full section | Conventional for related work and conclusion; exempt from D14. |

Every new prose paragraph in the per-section tables above carries an
"Anchor:" annotation naming the display, figure, or table it serves; a new
paragraph with no nameable anchor is a spec violation, not a style choice.

## 6. Greg-note resolution map

| Note (line) | Resolved by |
|---|---|
| 83 (delete abstract diff) | §1 deletion of 84–89. |
| 104 (sudden jump, two models unexplained) | §1 why-two-distributions paragraph, both halves: why two models, and what they do for group and card protocols. |
| 106 (packed paragraph, move to sections) | §1 deletion of 110–119, with the no-private-inputs fact rescued into §2. |
| 108 ("Overall" style core claim) | §1 overall paragraph + informal A and B. |
| 132 (flow diagram first) | §2 narrative + sequence diagram with `[H]` placement (D9). |
| 179/180 (positive security framing, Shamir) | §2 security reframing + D8 citation, keeping 170–177 verbatim. |
| 185 (sudden word model) | §2 word-model motivation sentence. |
| 198 (TV meaning) | §2 operational meaning sentence after line 200. |

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
  duplicate, not a claim). Theorem B is stated in distributional terms only;
  the entropy form stays an open problem in the conclusion.
- Theorems A and B are never `\label`'d and never `\ref`'d; all references
  are literal text.
- Git hygiene: `main.tex` carries uncommitted `\greg{}` notes; commits of the
  rewritten paper use index surgery so unrelated working-tree changes stay
  uncommitted. `notes/` stays gitignored.
- llncs mechanics: `\spnewtheorem*` for the named A/B environments; numbered
  environments keep class defaults; `hyperref` refs must resolve.

## 8. Verification requirements (for the implementation plan)

1. `latexmk` build clean: no undefined references, no duplicate labels, no
   duplicate hyperref destinations, no overfull layout regressions from the
   new figure and merged table.
2. Informal-formal agreement: clause-by-clause check of the §1 informal A and
   B against the formal capstones, hedges included, per the per-theorem hedge
   lists in §4 of this spec.
3. Re-leveling audit: every `\ref` to a demoted or folded result updated;
   prose words "Theorem/Proposition/Lemma" match the environment they cite;
   no `\ref` targets Theorem A or B.
4. Citation check: Shamir 1979 metadata verified via research-kb before the
   `references.bib` entry lands; no other bibliography changes.
5. Jargon table for each new prose block over 200 words before finalizing.
6. Diagram check: rendered sequence diagram and relabeled architecture figure
   visually verified in the compiled PDF; labels use reader vocabulary; the
   sequence diagram renders before the formal-data paragraph.
7. Greg-note sweep: `grep -c 'greg' main.tex` returns zero at the end.
8. Prose-rule sweep over the diff: no em-dash, no semicolon, no parenthetical
   aside, no "law", in new or edited sentences.
9. Prose-run sweep (D14): in the compiled PDF, no section of §§2–7 runs more
   than three consecutive paragraphs without a displayed equation, figure,
   table, itemize, or theorem-family environment; §1 is allowed four before
   the informal displays; §§8–9 exempt.
10. Example fidelity: the D12 card rows match the actual `orbit_encode`
    output in `pgl27_orbit.v`, and the D13 ramp marks match the ramp
    Proposition's clauses exactly (3, 4, 6, 7, 8).
