# WADT2026 Architecture Section Expansion — Design Spec

Date: 2026-08-09 (rev 11: D23 moves the flow diagrams to the instances — the model section keeps no figure and generalizes, the committed-input flow leads in the five-card section, the no-input flow relocates into the PGL construction)
Target: `pgg-smc/paper-wadt2026/main.tex`, Section 3.1 (Framework Architecture)
Status: for user review

## Goal

Expand Section 3.1 from three thin paragraphs into a concrete formalization-paper
architecture section: show how the framework records organize the specification
of a card-based protocol, and present the fulfill-one-record feature. The
feature, stated honestly: the `protocol_of_profile` section (renamed from
`run_profile` by D17; each profile is the configuration plus its evidence, and
the section yields the certified protocol it determines) derives, for every
completed `MonodromyProfile` value, the protocol roles, the certified
characters, and the generic correctness lemma `profile_recon_encode` (renamed
from `run_recovers` by D18) with a one-line proof. The paper's
correctness and endpoint-uniformity theorems are the sharp executed-trace forms
of these guarantees, proven over the interpreter's output at the same layout
record; the coalition-privacy theorems are separate results proven from
transitivity.

Rev 7 adds a second deliverable: a new top-level section "A First Instance:
The Five-Card Family" between the framework section and the PGL construction,
presenting den Boer and Kim as one epsilon-parameterized profile
(`five_card_profile`) — the simple worked instance before the difficult one.
Its results stay at proposition level; Theorems A and B remain the paper's
only named theorems. Organization
follows the wadtSep17 slides
(`/Users/cheng-huiweng/Projects/aplas2024-poster/wadtSep17/slides.tex`,
frames "The specification: one MonodromyProfile", "SecurityWitness: certified
leakage", "Recovery is a separate component", "One flow, two protocol families").

## Verified source facts

Every claim in the new prose is grounded in one of these. First check
2026-08-09; corrected and extended after the Opus audit re-verification.

| Fact | Source |
|---|---|
| `MonodromyProfile` fields: `mp_M`, `mp_secretT`, `mp_PI`, `mp_security`, `mp_plug` | `pgg-smc/protocol/pgg_monodromy_profile.v:50-57` |
| Derived definitions `run_dealer`, `run_party`, `run_verifier`, `run_recover`, `run_eps`, `run_k`, `run_anonymous`, `run_private` in the `run_profile` section (pre-rename names, see D16-D18) | `pgg-smc/protocol/pgg_monodromy_profile.v:63-110` |
| Derived lemma `run_recovers : run_recover (ts_encode (rp_scheme plug) s) = s`, proof `exact: ts_correct (ts_encode_valid ...)` (pre-rename name, `profile_recon_encode` after D18) | `pgg-smc/protocol/pgg_monodromy_profile.v:116-118` |
| Consumer status (pre-rename names, see D16-D18): `run_k` is read off per instance (`run_k_pgl27 = 4` at `pgl27_profile.v:111`, siblings `run_k_s5`, `run_k_s5x5`, `run_k_abel`); the other `run_*` definitions and `run_recovers` have no downstream consumers | grep sweep 2026-08-09 |
| All eight D17/D18 target names (`protocol_of_profile`, `profile_k`, `profile_eps`, `profile_anonymous`, `profile_private`, `profile_recon_encode`, `profile_eps_pgl27`, `profile_k_pgl27`) unused in the codebase | grep sweep 2026-08-09 |
| The PGL executed program is the same generic processes at the profile's layout: `pgl27_dealer_run = dealer_with_input_encoding pgl27_PI (fun _ => tnth (ts_encode orbit_scheme s)) ...` with empty input list; `pgl27_saprocs` lists `exchange_verifier pgl27_PI` and eight `exchange_player pgl27_PI` | `pgg-smc/instances/pgl27/pgl27_run.v:63-83` |
| `PGGInterface` fields: `pi_T'`, `pi_starts`, `pi_starts_uniq` | `pgg-smc/protocol/pgg_interface.v:379-383` |
| `SecurityWitness` fields: `sw_L`, `sw_bound_eps`, `sw_rho_dist`, `sw_bound`, `sw_exact : option SecurityExact`, `sw_asymptotic : option SecurityAsymptotic` | `pgg-smc/reconstruct/algebraic_rigidity.v:147-157` |
| `sw_bound` bounds, for each position `s`, the distance of the single-position endpoint distribution from uniform (a marginal, not a joint bound) | `pgg-smc/reconstruct/algebraic_rigidity.v:151-154` |
| `SecurityExact` (equality), `SecurityAsymptotic` (floor plus geometric decay `sa_eps_inf + sqrt(N)(1-gap)^L`) | `pgg-smc/reconstruct/algebraic_rigidity.v:90-137` |
| `ReconPlug` fields: `rp_scheme`, `rp_content`, `rp_monodromy`, `rp_recon_invariant` | `pgg-smc/reconstruct/covering_scheme.v:117-123` |
| `ThresholdScheme` fields: `ts_T'`, `ts_k'`, `ts_valid`, `ts_recon`, `ts_encode`, `ts_correct`, `ts_private`, `ts_encode_valid`; `ts_k = ts_k'.+1` (successor convention) | `pgg-smc/reconstruct/pgg_sharing_framework.v:47-65,99-100` |
| `ts_private` is an existence statement (a valid re-deal for the other secret agreeing on the coalition), not a distributional indistinguishability | `pgg-smc/reconstruct/pgg_sharing_framework.v:57-63` |
| `ts_recon_perm_invariant` requires `g \in G` AND `ts_valid` before concluding invariance | `pgg-smc/reconstruct/pgg_sharing_framework.v:125-129` |
| `pgl27_private` (the `ts_private` field of `orbit_scheme`, `ts_k' = 3`) is discharged by the generic transitivity bridge `ttrans_private` | `pgg-smc/instances/pgl27/pgl27_scheme.v:58-84`, `pgg-smc/reconstruct/transitivity_privacy.v:336` |
| `pgl27_run_recovers` proof uses `ts_recon`, `ts_encode`, `ts_encode_valid`, and `orbit_recon_invariant` (the proof term stored in the `rp_recon_invariant` field); `ts_correct` does not occur in the file | `pgg-smc/instances/pgl27/pgl27_run.v:177-206`, `pgg-smc/instances/pgl27/pgl27_scheme.v:98-100` |
| Word-shuffle correctness reuses the scheme: `pgl27_word_run_recovers` calls `ts_recon orbit_scheme`; the word-shuffle privacy results (`pgl27_word_view_indist`, `pgl27_word_trace_indist`, mixing lemmas) reference no record | `pgg-smc/instances/pgl27/pgl27_word_privacy.v:51-56`, grep of `pgl27_mixing.v` |
| `InputEncoding` fields: `ie_assemble`, `ie_output`, `ie_assemble_valid`, `ie_orbit`; derived `ie_output_correct` (the shuffled layout reconstructs the output for every allowed shuffle) | `pgg-smc/reconstruct/input_encoding.v:28-55` |
| The only `InputEncoding` value is den Boer's; Kim reuses the den Boer program wholesale (`kim_procs := den_boer_procs`) | `pgg-smc/instances/denboer1989/den_boer_encoding.v:104-105`, `pgg-smc/instances/kim2025/kim_run.v:28` |
| The commit prologue on an empty input list reduces by computation to the plain dealer; `exchange_dealer_with_commit_nil` records this for the committed dealer (no downstream consumer, cite the mechanism, not the lemma) | `pgg-smc/protocol/pgg_input_commitment.v:145-152` |
| Generic input-commit dealer `dealer_with_input_encoding` | `pgg-smc/protocol/pgg_run.v:45-51` |
| Realized witness combinations: den Boer present/absent at eps 0 (`uniform_security_witness`), Kim present/present (`fc_kim_security_witness`), S5 and S5xS5 absent/present (`s5_security_witness_schreier`, s5x5 witness), PGL present/absent at eps 0 under the uniform group distribution (`pgl27_security` over `pgl27_rho_dist`) | `pgg_uniform_security.v:186-190`, `five_card_kim.v:507-517`, `rigidity_s5_instance.v:200-207`, `rigidity_s5x5_instance.v:278-281`, `pgl27_profile.v:63,97-99` |
| PGL profile value: `pgl27_profile = MkMonodromyProfile pgl27_M bool pgl27_PI pgl27_security pgl27_plug` | `pgg-smc/instances/pgl27/pgl27_profile.v:104-105` |
| New corollaries `run_recover_pgl27` (proof `exact: pgl27_run_recovers.`), `run_party_pgl27` (proof `by [].`), and `profile_eps_pgl27` (proof `by [].`, validated pre-rename as `run_eps_pgl27 = 0%R`) validated in-kernel via rocq-mcp preamble session over the compiled chain; `run_verifier` equality fails elaboration (list-dependent session type), `run_dealer` equality is false (content readout) | this spec, New Rocq code section, 2026-08-09 |
| `listings` package already loaded, no `\lstset` yet; `\coqin` = `\texttt`; no listing environment exists in the paper | `main.tex:12,21` |
| `five_card_profile (R) (eps) Hlt Hgt Hspec (L) = MkMonodromyProfile FiveCardKim_M bool FiveCardKim_PI (fc_kim_security_witness ...) five_card_plug`; hypotheses `eps < 1/5`, `-4/5 < eps` | `pgg-smc/instances/kim2025/five_card_family.v:164-168` |
| `five_card_eps0_eq0`: at bias 0 and any positive word length, `sw_bound_eps ... = 0` (den Boer recovered as the unbiased member) | `pgg-smc/instances/kim2025/five_card_family.v:180-185` |
| Biased weight: `kim_weight_fun k = 1/5 - eps` at `k = 0`, `1/5 + eps/4` otherwise | `pgg-smc/instances/kim2025/five_card_kim.v:160-163` |
| Kernel-checked Kim numbers: `kim_bound_centi` (bias 1/100, length 7, spectral bound below `2^-40`) and `kim_deal_centi_lt` (variation distance of the 7-cut deal below `2^-40`) | `pgg-smc/instances/kim2025/five_card_kim.v:613,635` |
| Kim reuses den Boer's executed program (`kim_procs := den_boer_procs`, `kim_run_recovers` by `exact: den_boer_run_recovers`); `kim_trace_secrecy` | `kim_run.v:28,38-42`, `kim_trace.v:46` |
| Section 7 paragraph to relocate: den Boer uniform-cut exactness and Kim seven-cut `2^-40` sentences | `main.tex:889-895` |
| `var_dist(P,Q) = \sum_(a : A) abs(P a - Q a)` — unhalved, maximum 2 | `probability/variation_dist.v:33` |
| Case-by-case reveal leakage, all Qed: `leak_k1 = 0`, `leak_k2_adj = 27/10 - (1/4)log 5 - (7/10)log 7` (about 0.154), `leak_k2_dist2` (about 0.119), `leak_k3` (about 0.487), `leak_k4`, `leak_k5`, cap `H_secret = 2 - (3/4)log 3` (about 0.811); decimals recomputed from the closed forms this session | `pgg-smc/instances/denboer1989/five_card_leakage.v:86,245,317,383,448,527,546` |
| Poster Pencil node "denboerCards 2" (id `u6aAF5`, `pgg-smc/notes/may18aipv2026/poster.pen`) holds the six-row reveal-leakage card figure with the same values; `notes/` is untracked, so the paper figure is authored fresh in TikZ | screenshot inspected 2026-08-09 |
| Paper's existing convention handling: unhalved L1 definition display and the halved total variation relation with the `2^-40` to `2^-41` conversion; "unhalved" wording at the abstract and introduction uses; a `2^-41` total variation sentence | `main.tex:253-265,57,116-118,137,777` |
| `fig:framework-architecture` is labeled but never `\ref`ed in the current paper | grep of `main.tex` |

## Record-to-theorem boundary (honesty baseline)

Rebuilt from the dependency trace of `pgl27_run.v`, `pgl27_secrecy.v`,
`pgl27_trace.v`, `pgl27_mixing.v`, `pgl27_word_privacy.v`. The new prose may
claim only the following.

Record path (what the records carry into paper results):
- `pi_starts`/`pi_starts_uniq` fix the layout; the players and the verifier of
  the executed run are exactly the generic `exchange_player` and
  `exchange_verifier` at this interface, and the dealer is the same generic
  dealing program carrying the instance's own content readout
  (`pgl27_run.v:63-83`), so an instance writes no process code. Correctness
  and the trace statements are over this layout.
- `ts_recon` of the plug's scheme reads the verifier endpoints in BOTH
  correctness results, uniform (`pgl27_run_recovers`) and word
  (`pgl27_word_run_recovers`); the proof closes by the scheme's reconstruction
  invariance under the action, the proof term stored in `rp_recon_invariant`.
- `ts_correct` is consumed by the generic derived lemma `profile_recon_encode`
  (today `run_recovers`, `pgg_monodromy_profile.v:116-118`), the
  framework-level correctness guarantee; the instance's executed-trace
  correctness is its sharp form.
- `ts_private` (threshold `ts_k' = 3`, so `profile_k = 4` by the successor
  convention) is a record obligation: a re-dealability statement discharged by
  the generic transitivity bridge `ttrans_private`. It is NOT Theorem A's
  coalition clause; that clause is `pgl27_view_indep` via
  `ttrans_view_indep_gen`.
- `sw_bound` with `sw_exact` at eps 0, under the uniform group distribution,
  certifies single-position endpoint uniformity, re-exported as
  `profile_eps`/`profile_anonymous`.
- `profile_k` and `profile_eps` are the shared characters read off per
  instance (`profile_k_pgl27 = 4` and three siblings; `profile_eps_pgl27 = 0`).
- `InputEncoding`: den Boer's committed evaluation only; the Kim variant
  reuses the den Boer program unchanged.

Theorem-side (bypasses the record proof fields; prose must NOT claim record
derivation):
- Theorem 1 `ttrans_view_indep_gen` consumes three-transitivity of the action,
  the uniform shuffle, and distinct cards; `pgl27_view_indep` instantiates it
  (`pgl27_secrecy.v:81`). Theorems 2 and 3 are generic lemmas. Note the
  transitivity route also discharges the record obligation `ts_private` via
  `ttrans_private`, so transitivity feeds both sides.
- Theorem B's privacy results (mixing, view and trace indistinguishability)
  consume the word distribution and the transfer lemmas only. Theorem B's
  correctness clause reuses `ts_recon` of the scheme, as recorded above.

Orphan honesty (per the load-bearing rule): after D16-D18, `run_verifier`,
`profile_anonymous`, `profile_private`, and the generic `profile_recon_encode`
have no downstream consumers (`run_dealer` is deleted). `run_recover`,
`run_party`, and `profile_eps` gain consumers with this spec: the corollaries
`run_recover_pgl27`, `run_party_pgl27`, and `profile_eps_pgl27` (see New Rocq
code below), all validated in-kernel 2026-08-09. The prose therefore presents
the `protocol_of_profile` section as the framework's uniform derivation and
grounds it with the facts that ARE load-bearing: each executed player
coincides with the derived player role (`run_party_pgl27`), the verifier is
the same generic process at the layout record (read off `pgl27_saprocs`), the
executed-trace correctness is restated through the shared decoder
(`run_recover_pgl27`), and the characters `profile_k` and `profile_eps` are
read off per instance (`profile_k_pgl27`, `profile_eps_pgl27`). No sentence
may say the PGL instance obtains its dealer or verifier from the derived
section (D15 and D16 record why).

Unrelated fields (never oversold): `sw_L` (bookkeeping tag), `sw_asymptotic`
for the PGL instance (`None`; hosts Kim's, S5's, and S5xS5's decay
certificates), `mp_secretT` (type plumbing), the `CoveringScheme`/
`CoveringData` genus layer (absent from this paper).

## Decisions

| # | Decision |
|---|---|
| D1 | Approach: reorganize Section 3.1 as one subsection following the slides' arc; no new sub-subsections, no renumbering. |
| D2 | One combined code listing in Section 3.1: condensed `MonodromyProfile` record, the derived cast and `profile_*` characters (post-rename names), AND the derived lemma `profile_recon_encode` with its one-line proof (the fulfill-and-it-is-proved artifact). `\footnotesize` type. The five-card section adds the paper's second, shorter listing (D19); no others. |
| D3 | Include the one-flow-two-families paragraph, introducing `InputEncoding` and the commit-prologue degeneration by computation. |
| D4 | Wiring claims are bounded by the honesty baseline above, including the orphan-honesty rule. One boundary sentence states the record/theorem split explicitly in the paper. |
| D5 | Symbol care: the paper's Equation 1 uses R for the real field; the recovery component is never written R (the slides' usage). The decoder stays "the decoder" or "the reconstruction component". |
| D6 | Listing style: add `\lstset{basicstyle=\ttfamily\footnotesize,columns=fullflexible,keepspaces=true,breaklines=true,xleftmargin=2mm,aboveskip=2pt,belowskip=2pt}` to the preamble. No language definition; plain text mode. |
| D7 | The listing's source is cited with a plain `\footnote{Formalized in \path{pgg-smc/protocol/pgg_monodromy_profile.v}. The listing elides argument types and the dealer's word parameters.}` attached to the lead-in sentence. No `\footnotemark` (verbatim environments swallow it). |
| D8 | The bridge table (`tab:bridge`) stays as the opener anchor; the architecture figure stays as the closing anchor with its caption extended, and the wiring paragraph gains the paper's first `Figure~\ref{fig:framework-architecture}` reference. |
| D9 | The proof-mechanism encoding is presented as a compact table of REALIZED witness combinations with a distribution qualifier for the eps-0 row; instance names appear with a forward reference to `tab:instances`, and Section 7's own mixing sentences are left unchanged. |
| D10 | Prose rules carried over: no em-dashes, no prose semicolons, no parenthetical asides, "distribution" never "law", no abbreviations, Theorems A and B by literal text only, at most 3 consecutive prose paragraphs between anchors. |
| D11 | Recovery modularity gets one explicit sentence: the group, its action, and its shuffle distribution fix the dealing and the endpoint bound, and the decoder is an independent choice, so instances over the same group differ only in the reconstruction component. |
| D12 | The threshold character is named by meaning ("the largest private coalition size") and the successor convention is stated in the same sentence, so `profile_k = 4` never collides with Theorem A's `t = 3` in the reader's head. |
| D13 | The existing closing paragraph of Section 3.1 (`main.tex:381-385`) is removed, including its sentence "the generic theorems derived from these records", which the boundary sentence contradicts. Block 9 supplies the replacement bridge. |
| D14 | Three new Rocq corollaries are added so the paper's framework-usage claims have in-repo consumers: `run_recover_pgl27` and `run_party_pgl27` in `pgg-smc/instances/pgl27/pgl27_run.v` (derived decoder and player role) and `profile_eps_pgl27` in `pgg-smc/instances/pgl27/pgl27_profile.v` (the security character, value 0). All statements and one-line proofs are validated in-kernel (rocq-mcp preamble session, 2026-08-09; the third under its pre-rename name with an identical statement). The `.v` commits run the two-stage audit gate; the corollaries carry role tags and the sibling-convention names. |
| D15 | No example corollary for `run_verifier` or the dealer, each for a verified reason recorded in the New Rocq code section: the verifier equality does not typecheck (session types depend on the player list, and `enum 'I_8` is not convertible to the instance's literal ordinal list, which exists precisely so `vm_compute` can reduce the dealer), and the dealer equality is false (the executed dealer carries the instance's content readout under a commit prologue, while `run_dealer` bakes `rp_content = id`). The paper's verifier and dealer sentences stay grounded by `pgl27_saprocs` and `pgl27_dealer_run` as prose observations. |
| D16 | `run_dealer` is removed from the framework section. It has zero consumers, its content model contradicts every executed dealer (the D15 falsity), and keeping it forced the audit's hedged wording. The paper's dealer story runs through `dealer_with_input_encoding`, which is what actually executes. |
| D17 | The section `run_profile` in `pgg-smc/protocol/pgg_monodromy_profile.v` is renamed `protocol_of_profile`: the profile is the configuration plus its evidence, and the section yields the certified protocol it determines. Section names are file-local in Rocq, so the rename touches only the `Section`/`End` lines and the two same-file comment mentions (lines 13 and 46). The word "run" is reserved for the interpreter layer, which actually executes. |
| D18 | Non-running members of the section are renamed `profile_*`: `run_k` to `profile_k`, `run_eps` to `profile_eps`, `run_anonymous` to `profile_anonymous`, `run_private` to `profile_private`, and the lemma `run_recovers` to `profile_recon_encode` (matching the `ts_recon_encode` round-trip naming one level down). The cast keeps `run_` (`run_party`, `run_verifier`, `run_recover` are the pieces that really run). Downstream: `run_k_pgl27`, `run_k_s5`, `run_k_s5x5`, `run_k_abel` become `profile_k_*` (the abel rename is build consistency only; the instance stays out of paper scope). The executed-layer `*_run_recovers` lemmas keep their names. All eight new names verified unused in the codebase (grep, 2026-08-09). |
| D19 | A new top-level section "A First Instance: The Five-Card Family" (label `sec:fivecard`) is inserted between the framework section and the PGL construction, presenting den Boer and Kim as one record, `five_card_profile` at bias epsilon. The section is anchor-dense, never prose-heavy: two figures (the committed-input flow diagram and the case-by-case reveal-leakage figure), one listing, one display, one Proposition, with never more than two consecutive prose paragraphs. All results stay at Lemma/Proposition level; Theorems A and B remain the only named theorems. Expected length 2 to 2.5 pages. Sections renumber automatically; the PGL construction becomes Section 5. |
| D20 | Section 7 (Other Instances) transfers its den Boer and Kim mixing prose (`main.tex:889-895`) to the new section; the consolidated instance table keeps all five rows, and the trust-base paragraph and the S5 and S5xS5 prose stay in Section 7. Section 7's opener sentence is adjusted so it introduces the two remaining sibling instances plus the table. |
| D21 | Section 3.1's five-card forward references (mechanism-table caption, two-families paragraph) point at `sec:fivecard`; the new section's coda is the ramp sentence into the PGL construction, naming what the difficult instance adds: coalitions beyond one card via three-transitivity, an orbit-class secret, and certificates without `vm_compute` on the group. |
| D23 | Flow-diagram placement follows the instances, not the model. Edits: (a) the model section loses its flow diagram and its instance specialization: the opening walkthrough is rewritten for a general run (n face-down cards, a dealer encoding the secret as a valid arrangement, T players receiving one card each, a verifier decoding from the revealed arrangement), with no instance numerals and no figure; the sentence "Figure~\ref{fig:run} shows this flow" is removed; the model section's anchors are its displays. (b) The existing `fig:run` TikZ relocates unchanged into the PGL construction section, near its start; its label is kept; its caption is extended to name the eight players and the orbit-class decode and to call it the no-input counterpart of Figure~\ref{fig:fivecard-run}. (c) The five-card section's `fig:fivecard-run` becomes the paper's first flow diagram; its caption does not reference `fig:run`. (d) Every `\ref{fig:run}` site is reread and rewritten where the relocation makes it read oddly, in particular the word-shuffle sentence "the dealer of Figure~\ref{fig:run} performing the shuffle" becomes "the dealer performing the shuffle". (e) Reading order invariant: exactly two flow diagrams in the paper, the committed-input flow first, the no-input flow second. |
| D22 | ONE distance standard from beginning to end: the $L_1$ distance $\lVert P-Q\rVert_1$, whose constants match the Rocq lemmas verbatim (infotheo `var_dist`, `variation_dist.v:33`). ONE footnote carries every convention remark; no scattered qualifiers. Edits: (a) delete EVERY occurrence of the word "unhalved" in the paper, grep-driven, wording becomes plain "$L_1$ distance" (known sites include the abstract at line 57, the introduction at 116, 118, 137, the model section lead-in at 253, and the sibling-instances sentence that D20 relocates; the sweep, not this list, is authoritative). (b) Delete the halved-convention block `main.tex:258-267`: the repository-name sentence, the `eq:tv-definition` display, the conversion sentence, and the operational-advantage sentences; their content moves into the footnote. (c) Delete the Section 6 sentence `main.tex:776-777` ("Under the halved convention ... $2^{-41}$ in total variation"), which references the deleted display. (d) The definition display `eq:l1-definition` (`main.tex:254-257`) stays as the body's only formal definition. (e) The footnote attaches to the first in-text bound, the informal Theorem B display in the introduction. Draft: "The $L_1$ distance is $\lVert P-Q\rVert_1=\sum_x\lvert P(x)-Q(x)\rvert$, called variation distance in the formal development, with maximum value 2. The common total variation distance is half of it. An $L_1$ bound of $2^{-40}$ therefore bounds every observer's distinguishing advantage by $2^{-41}$." (f) The abstract gains no footnote and simply says "$L_1$ distance". (g) The five-card F6 proposition and every other bound say "$L_1$ distance" with no re-explanation. No printed constant changes. |

## Framework rename and cleanup: per-file changes (D16-D18)

| File | Change |
|---|---|
| `pgg-smc/protocol/pgg_monodromy_profile.v` | `Section run_profile` and `End run_profile` become `protocol_of_profile`; comment mentions at lines 13 and 46 updated; `run_dealer` definition and its docstring deleted; `run_k`, `run_eps`, `run_anonymous`, `run_private`, `run_recovers` renamed per D18 with docstrings adjusted |
| `pgg-smc/instances/pgl27/pgl27_profile.v` | `run_k_pgl27` becomes `profile_k_pgl27` (statement now `profile_k (pgl27_profile R) = 4`); new `profile_eps_pgl27` appended (D14) |
| `pgg-smc/instances/s5/s5_profile.v` | `run_k_s5` becomes `profile_k_s5`; the two "shared run_k" comment lines updated |
| `pgg-smc/instances/s5x5/s5x5_profile.v` | `run_k_s5x5` becomes `profile_k_s5x5`; comment updated |
| `pgg-smc/instances/abelian/abel_profile.v` | `run_k_abel` becomes `profile_k_abel`; comment updated (build consistency only, out of paper scope) |
| `pgg-smc/instances/pgl27/pgl27_run.v` | import line added; `run_recover_pgl27` and `run_party_pgl27` appended (D14) |

Ordering: the framework rename commit lands first and must leave the whole
`pgg-smc` build green (rocq-mcp `rocq_compile_file` on each touched file,
dependents included); the paper commit follows.

## New Section 3.1 structure

Replaces `main.tex` lines 309-385 (current subsection body, including the
closing paragraph per D13). Block order, each with its anchor:

| # | Block | Anchor |
|---|---|---|
| 1 | Opener paragraph: an instance is specified by filling one record, `MonodromyProfile`, whose five fields carry the data of Equation 1 into the executable protocol; MathComp basis sentence kept; reference to `tab:bridge`; half-sentence re-fixing R as the real field | existing `tab:bridge` |
| 2 | Bridge table, unchanged content | table |
| 3 | The combined listing (draft below); lead-in sentence carries the D7 footnote | new `lstlisting` |
| 4 | Duties paragraph + enumerated list: the three proof obligations (drafts below) | itemize |
| 5 | Wiring paragraphs: derived roles and characters with orphan-honest grounding, FORTE interpreter sentence, recovery-modularity sentence (D11), figure reference (D8), boundary sentence; the proof-mechanism lead-in folds into the final paragraph (D10 prose-run cap control) | prose, at most 3 paragraphs |
| 6 | Proof-mechanism table | new small table |
| 7 | Two-families paragraph (draft below) | prose |
| 8 | Architecture figure, caption extended | existing figure |
| 9 | Bridge sentence into Section 3.2: "The next subsection states the generic theorems the framework supplies to every instance." | prose, 1 sentence |

## Draft content

### Block 3: the listing

Lead-in sentence (carries the D7 footnote): "The central record and its
derived protocol follow." All listing lines are at most 72 columns (N3).

```latex
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
```

### Block 4: duties

Lead-in: "Filling the record means discharging three proof obligations."
Then an itemize:

- Every single card position lands close to uniform: `sw_bound` bounds the
  distance of each position's endpoint distribution from the uniform
  distribution by `sw_bound_eps`.
- The threshold scheme recovers and hides: `ts_correct` decodes every valid
  share tuple to its secret, and `ts_private` gives every coalition below the
  threshold a share pattern that is equally consistent with either secret.
- Reconstruction is shuffle-invariant: for any allowed shuffle and any valid
  share tuple, `rp_recon_invariant` states that permuting the shares by the
  shuffle leaves the recovered secret unchanged.

### Block 5: wiring

Content points, in order (at most 3 paragraphs):

1. Once the record is filled, the `protocol_of_profile` section derives the
   players, the verifier, and the recovery map as definitions over the
   fields, re-exports the certified characters, and proves the round-trip
   correctness lemma `profile_recon_encode` in one line from the record's
   obligations. No new proof obligation arises at wiring time. Grounding
   sentence (orphan-honest, N1 wording): in the worked instance the players
   and the verifier are exactly the generic processes at its layout record,
   the dealer is the same generic dealing program carrying the instance's own
   content readout, each player coinciding with the derived role and the
   correctness restated through the shared decoder (footnote:
   `run_party_pgl27` and `run_recover_pgl27` in
   `\path{pgg-smc/instances/pgl27/pgl27_run.v}`, `profile_k_pgl27` and
   `profile_eps_pgl27` in `\path{pgg-smc/instances/pgl27/pgl27_profile.v}`),
   and the threshold character is read off the shared definition, with value
   four under the successor convention, so the largest private coalition size
   is three (D12 wording).
2. The small process interpreter that executes the layout originates in the
   earlier FORTE development (existing sentence, kept, citation kept). The
   executed traces of Section 2 are its output. Recovery-modularity sentence
   (D11). `Figure~\ref{fig:framework-architecture}` reference (D8).
3. Boundary sentence: "The record path certifies correctness, endpoint
   uniformity, and the sharing threshold. The coalition-view, trace, and
   word-shuffle privacy theorems of
   Sections~\ref{sec:exact} and~\ref{sec:mixing} are stated separately: they
   consume the transitivity of the action and the shuffle distribution
   directly, not the record fields." Then the folded lead-in for Block 6: "The
   two optional slots of the security witness encode the proof mechanism, and
   Table~\ref{tab:witness-mechanism} shows the realized combinations." Then
   the existing forward reference to Section 4 as the worked instantiation.

### Block 6: proof-mechanism table

The table's label is `tab:witness-mechanism`.

| `sw_exact` | `sw_asymptotic` | Mechanism | Realized by |
|---|---|---|---|
| present | absent | exact equality at eps 0 under the uniform group distribution | den Boer, $\PG$ |
| present | present | exact count with geometric decay in the word length | Kim |
| absent | present | spectral certificate with an imported gap premise | $S_5$, $S_5\times S_5$ |

Table note (one sentence, in the caption): "Section~\ref{sec:mixing} treats
the word-shuffle counterpart of the $\PG$ row,
Section~\ref{sec:fivecard} proves the den Boer and Kim rows, and
Table~\ref{tab:instances} records the per-instance evidence." In LaTeX: a `tabular` in the paper's existing
table style; `Some`/`None` written as "present"/"absent".

### Block 7: two families

One paragraph: with an `InputEncoding`, a commit prologue collects the
players' inputs and assembles the dealt deck from them, so the same flow
evaluates a function of committed inputs. The realized encoding is den
Boer's, whose obligation `ie_orbit` places equal-output inputs in one shuffle
orbit, and whose derived lemma `ie_output_correct` shows the shuffled layout
reconstructs the output for every allowed shuffle. The Kim variant reuses the
den Boer program unchanged. With an empty input list the prologue reduces by
computation to the plain dealer, which is the secret-sharing case, and the
$\PG$ instance passes exactly this empty list. Forward references: to
Section~\ref{sec:fivecard} for the realized committed-input instance, and to
the instance table of the sibling-instances section for the full landscape.
No parenthetical asides; the degeneration is attributed to the mechanism, not
to a named lemma.

### New Rocq code (validated in-kernel 2026-08-09)

Appended at the end of `pgg-smc/instances/pgl27/pgl27_run.v`, top-level
context, together with one import line added to the file's import block:
`From pgg_smc Require Import pgg_monodromy_profile.`

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
```

```coq
(** run_party_pgl27 — each executed PGL(2,7) player is the profile's derived
    player role at its ordinal.
    @main architecture: the instance's player processes coincide with
    run_party of pgl27_profile. *)
Corollary run_party_pgl27 (R : realType) (i : 'I_(pi_T' pgl27_PI).+1) :
  @run_party R (pgl27_profile R) i = exchange_player pgl27_PI i.
Proof. by []. Qed.
```

Appended to `pgg-smc/instances/pgl27/pgl27_profile.v`, next to
`profile_k_pgl27` (post-rename):

```coq
(** profile_eps_pgl27 — the PGL(2,7) profile's security character is zero:
    perfect single-position endpoint uniformity.
    @main security: the eps read off pgl27_profile is 0. *)
Lemma profile_eps_pgl27 (R : realType) :
  @profile_eps R (pgl27_profile R) = 0%R.
Proof. by []. Qed.
```

The third lemma was validated under its pre-rename statement
`@run_eps R (pgl27_profile R) = 0%R` (proof `by [].`, 3 ms); the D18 rename
changes only the constant's name, so the validation carries over.

Validation record: rocq-mcp preamble session over the compiled `.vo` chain
(imports mirroring `pgl27_run.v` plus `pgl27_run` and
`pgg_monodromy_profile`); `rocq_check` closed `run_recover_pgl27` with
`exact: pgl27_run_recovers. Qed.` in 11 ms and `run_party_pgl27` with
`by [].` in 6 ms. The equalities typecheck because `run_recover` at
`pgl27_profile` unfolds definitionally to `ts_recon orbit_scheme`,
`mp_secretT (pgl27_profile R)` to `bool`, and `run_party` to
`exchange_player pgl27_PI`.

Rejected candidates, with the verified reasons (D15):

- `run_verifier_pgl27` stating
  `run_verifier (pgl27_profile R) = exchange_verifier pgl27_PI pgl27_players`
  FAILS ELABORATION: the verifier's session type depends on the player list
  (`iter (size players) ...` and a `fold_senv` over the list), `run_verifier`
  uses `enum 'I_8`, and the instance uses the literal ordinal list of
  `pgl27_run.v:54-56`, kept literal so the dealer reduces under `vm_compute`.
  The two lists are extensionally equal but not convertible, so the equality
  is not even well-typed. The only well-typed variant restates `run_verifier`
  against `enum 'I_8`, a tautology with no evidential value, and a run-level
  endpoint equivalence would be a fresh `vm_compute` proof of real cost.
- `run_dealer_pgl27` as an equality with the executed dealer is FALSE:
  `rp_content pgl27_plug = id` while `pgl27_dealer_run` deals
  `tnth (ts_encode orbit_scheme s)` under the commit prologue (audit finding
  N1).

The Block 5 grounding sentence cites the two added corollaries in a footnote
naming `\path{pgg-smc/instances/pgl27/pgl27_run.v}`, `run_recover_pgl27`,
and `run_party_pgl27`.

### Block 8: figure caption extension

Append to the existing caption: "Filling the three component records yields
the derived protocol roles, the certified characters, and the round-trip
lemma of the listing."

## New paper section: A First Instance — The Five-Card Family (D19-D21)

Inserted after the framework section, before the PGL construction. Title "A
First Instance: The Five-Card Family", label `sec:fivecard`. Anchor-dense
per D19 (two figures, one listing, one display, one proposition; at most two
consecutive prose paragraphs anywhere). Block order:

| # | Block | Anchor |
|---|---|---|
| F1 | Opener: the simplest instantiation of the framework; five cards, the cyclic group acting by rotation, the three-consecutive-hearts decoder; two classic protocols, one record | prose |
| F2 | Committed-input flow diagram: Alice and Bob commit card pairs, the dealer assembles and shuffles, the verifier reveals and announces the conjunction | figure (`fig:fivecard-run`) |
| F3 | The filled record: compact listing of `five_card_profile` with a source footnote | second `lstlisting` |
| F4 | The distribution family: biased-weight display plus the epsilon-zero collapse recovering den Boer | display |
| F5 | Case-by-case reveal leakage: six reveal patterns as card rows with their exact mutual-information values, every value a Qed lemma | figure (`fig:fivecard-leakage`) |
| F6 | Proposition: seven-cut security at bias 1/100, kernel-checked, below `2^-40` | proposition |
| F7 | Correctness and trace privacy in one short paragraph; one executed program serves both members; committed inputs realize the function-evaluation family of Section 3.1 | prose |
| F8 | Ramp coda (D21): what the PGL construction adds | prose |

### F2: the committed-input flow diagram

The FIRST flow diagram of the paper under D23; its caption does not
reference the PGL run figure, which now comes later and is captioned as the
no-input counterpart of this one. Content: actors Alice, Bob (braced "input
committers"), Dealer, Verifier; messages "two cards encoding $a$", "two
cards encoding $b$"; dealer actions "assemble the five-card deck", "draw the
cut, deal"; message "shuffled deck, face down"; verifier action "reveal: are
the three hearts consecutive"; closing message "announce $a\wedge b$".
Author fresh in the paper's existing sequence-diagram TikZ style
(`fig:run`); the talk's den Boer sequence frame
(`aplas2024-poster/wadtSep17/slides.tex:339-396`) is the content reference.

### F5: the case-by-case reveal-leakage figure

Recreates the analysis of the poster Pencil node "denboerCards 2" (node
`u6aAF5` in `pgg-smc/notes/may18aipv2026/poster.pen`; `notes/` is
untracked, so the figure is authored fresh in TikZ, reusing the card-row
style of the paper's encoding figure). Six rows, face-down cards as filled
squares, revealed cards showing suit; right column gives the mutual
information with the conjunction:

| Revealed positions | Value (bits) | Lemma |
|---|---|---|
| position 0 (one club) | 0 | `leak_k1` |
| positions 0,1 | about 0.154 | `leak_k2_adj` |
| positions 0,2 | about 0.119 | `leak_k2_dist2` |
| positions 0,1,2 | about 0.487 | `leak_k3` |
| four positions | about 0.811 | `leak_k4` |
| all five | about 0.811 | `leak_k5` |

The cap is the secret's own entropy `H_secret` $= 2 - \tfrac34\log 3
\approx 0.811$, since the conjunction is a quarter-biased bit. The figure
footnote names all seven lemmas in
`\path{pgg-smc/instances/denboer1989/five_card_leakage.v}` and states one
closed form as a sample (`leak_k2_adj`: $\tfrac{27}{10} - \tfrac14\log 5 -
\tfrac{7}{10}\log 7$). Accompanying prose (one paragraph): this is the
$(k,T)$ ramp of the framework's threshold obligation made concrete, one
card reveals nothing and the ramp climbs to the cap; the decimals are
evaluations of the proven closed forms. Card patterns and position sets
MUST match the `ViewA` sets of the lemmas and a valid den Boer encoding
(three hearts, two clubs); verified at implementation against the source.

### F3: the listing

```latex
\begin{lstlisting}
Definition five_card_profile (eps : R) (* bias bounds elided *)
    (L : nat) : MonodromyProfile R :=
  @MkMonodromyProfile R FiveCardKim_M bool FiveCardKim_PI
    (fc_kim_security_witness ... L) (* biased-cut witness    *)
    five_card_plug.                 (* three-hearts decoder  *)
\end{lstlisting}
```

Footnote on the lead-in sentence: `Formalized in
\path{pgg-smc/instances/kim2025/five_card_family.v} as
\coqin{five\_card\_profile}; the listing elides the three bias hypotheses.`

### F4: the display and the collapse

Display:
\[ w_\varepsilon(a^k) = \tfrac{1}{5}-\varepsilon \text{ if } k=0, \qquad
   \tfrac{1}{5}+\tfrac{\varepsilon}{4} \text{ otherwise}, \qquad
   -\tfrac{4}{5} < \varepsilon < \tfrac{1}{5}. \]
Following sentence: at bias zero the witness bound collapses to zero for any
positive word length, which is the precise sense in which the unbiased member
is den Boer's protocol. Footnote: `five_card_eps0_eq0` in
`\path{pgg-smc/instances/kim2025/five_card_family.v}`.

### F6: the proposition

Statement (adapting the relocated Section 7 sentence, D20, with the D22
wording): for bias $1/100$ and seven repeated cuts, every single-card
endpoint distribution is within $L_1$ distance $2^{-40}$ of uniform, and the
kernel checks the computation. Footnote: `kim_bound_centi` and
`kim_deal_centi_lt` in `\path{pgg-smc/instances/kim2025/five_card_kim.v}`.

### F7: correctness and trace privacy

Content points: the two members share one executed program, so correctness
transfers verbatim (`kim_procs := den_boer_procs`, `kim_run_recovers` by the
den Boer proof); the committed inputs of the two players realize the
function-evaluation family of Section 3.1 with den Boer's input encoding; a
single corrupted player's executed trace leaves the secret's conditional
entropy equal to its plain entropy (`kim_trace_secrecy`, statement verified
against `kim_trace.v:46-49`). Also relocates the den Boer uniform-cut
exactness sentence (D20). Forward reference to the sibling-instances table.

### F8: the ramp coda

One short paragraph, per D21: the five-card family keeps the group cyclic
and the deck small enough for kernel enumeration; the next sections
instantiate the same records where enumeration fails, and add coalition
privacy beyond one card via three-transitivity, an orbit-class secret, and
word certificates proven without computing in the group.

## Constraints

- All of D10 (style rules) plus D11-D13.
- The honesty baseline, including the orphan-honesty rule: no sentence may
  claim that Theorems 1, 2, 3, A, or B are derived from the records, and no
  sentence may say the worked instance obtains its roles from the `run_*`
  definitions. Verified by re-reading the final prose against the
  Record-to-theorem boundary section of this spec.
- Every identifier in the listing and prose must appear verbatim in its
  source file per the mapping in Verification requirement 3.
- Section 3.2 (Generic Theorems) body is unchanged. The only edit outside
  Section 3.1 is the preamble `\lstset` addition.
- Expected page growth: about three and a half pages across the deliverables
  (17 to about 20.5). No page constraint is in force.

## Verification requirements

1. `latexmk -g -pdf -halt-on-error -interaction=nonstopmode main.tex` exits 0;
   `grep -E "^!" main.log` empty; no undefined or multiply-defined references.
2. Page count recorded before and after (expected 17 to about 20.5).
3. Grep check, identifier to source file: `mp_M`, `mp_secretT`, `mp_PI`,
   `mp_security`, `mp_plug`, `run_party`, `run_verifier`, `run_recover`,
   `profile_eps`, `profile_k`, `profile_anonymous`, `profile_private`,
   `profile_recon_encode` in `pgg-smc/protocol/pgg_monodromy_profile.v`
   (post-rename); `sw_bound`,
   `sw_bound_eps`, `sw_exact`, `sw_asymptotic` in
   `pgg-smc/reconstruct/algebraic_rigidity.v`; `ts_correct`, `ts_private`,
   `ts_recon`, `ts_encode`, `ts_encode_valid`, `ts_k` in
   `pgg-smc/reconstruct/pgg_sharing_framework.v`; `rp_content`, `rp_scheme`,
   `rp_recon_invariant` in `pgg-smc/reconstruct/covering_scheme.v`;
   `ie_orbit`, `ie_output_correct` in
   `pgg-smc/reconstruct/input_encoding.v`; `exchange_dealer`,
   `exchange_player`, `exchange_verifier` in
   `pgg-smc/protocol/card_exchange_pismc.v:221,239,249`.
4. Style sweeps on the changed regions (Section 3.1 and the new five-card
   section): no em-dash, no prose semicolon, no "law", no parenthetical
   asides, no abbreviations.
5. D10 prose-run check on the new Section 3.1 and the five-card section: no
   run of more than 3 consecutive prose paragraphs (Block 5 is capped at 3
   and is followed by the Block 6 table; the five-card section interleaves
   listing, display, and proposition).
6. The boundary sentence is present, the wiring paragraph claims nothing
   beyond the honesty baseline, and no sentence attributes the instance's
   roles to `run_*` definitions.
7. The threshold appears only with the D12 wording (largest private coalition
   size three, character value four by the successor convention).
8. Visual inspection of the compiled listing and both tables in the PDF (no
   overfull lines in the listing, tables fit the text width).
9. The framework rename and the D14 corollaries: every file in the per-file
   change table recompiles via rocq-mcp `rocq_compile_file` (not make, per
   the compile-tooling rule), dependents included, and the `.v` commits pass
   the two-stage audit gate. Input source for this verification: the three
   statements validated in the rocq-mcp preamble session of 2026-08-09
   recorded in the New Rocq code section, re-run against the edited files
   under the post-rename names.
10. Grep check extension: `run_recover_pgl27` and `run_party_pgl27` resolve
    in `pgg-smc/instances/pgl27/pgl27_run.v`, `profile_k_pgl27` and
    `profile_eps_pgl27` in `pgg-smc/instances/pgl27/pgl27_profile.v`, and
    the paper footnotes naming them match those files.
11. Retired-name sweep at implementation end: word-boundary grep over
    `pgg-smc/**/*.v` finds zero occurrences of `run_dealer`, `run_eps`,
    `run_k`, `run_anonymous`, `run_private`, `run_recovers` (standalone; the
    executed-layer `*_run_recovers` lemmas do not match at a word boundary),
    and `run_profile`.
12. Five-card section greps: `five_card_profile`, `five_card_eps0_eq0` in
    `pgg-smc/instances/kim2025/five_card_family.v`; `kim_weight_fun`,
    `kim_bound_centi`, `kim_deal_centi_lt` in
    `pgg-smc/instances/kim2025/five_card_kim.v`; `kim_procs`,
    `kim_run_recovers` in `pgg-smc/instances/kim2025/kim_run.v`;
    `kim_trace_secrecy` in `pgg-smc/instances/kim2025/kim_trace.v`;
    `leak_k1`, `leak_k2_adj`, `leak_k2_dist2`, `leak_k3`, `leak_k4`,
    `leak_k5`, `H_secret` in
    `pgg-smc/instances/denboer1989/five_card_leakage.v`.
13. Renumbering integrity: after the section insertion, zero hard-coded
    section numbers in `main.tex` prose (grep for literal "Section" followed
    by a digit), every `\ref`/`\label` resolves, and the Theorems A and B
    literal-text mentions are untouched.
14. Distance-convention check (D22): exactly one footnote mentions total
    variation; zero occurrences of "unhalved", "halved", or "total
    variation" anywhere else in the paper; the label `eq:tv-definition` is
    gone and nothing references it; `eq:l1-definition` still resolves; no
    constant in the paper differs from its Rocq counterpart by a factor of
    two (spot-check every `2^{-40}`, `2^{-39}`, and `2^{-41}` site against
    the named lemma; `2^{-41}` should survive only inside the footnote);
    the footnote wording passes the style sweeps.
15. Reveal-leakage figure fidelity (F5): each row's decimal is recomputed
    from its lemma's closed form; each row's revealed-position set matches
    the `ViewA` argument of its lemma; the shown card values form a valid
    den Boer arrangement of three hearts and two clubs consistent with the
    revealed positions; the flow diagram's messages match the executed
    program roles of `den_boer_run.v`. Input sources: the lemma statements
    in `five_card_leakage.v` and the inspected Pencil node.
16. Flow-diagram placement check (D23): the model section contains no
    figure and passes the prose-run cap after the removal; exactly two flow
    diagrams exist, `fig:fivecard-run` before `fig:run` in page order;
    every `\ref{fig:run}` site reads correctly after the relocation; the
    model section's run description carries no instance numerals.

## Out of scope

- Any edit to the model section, the generic-theorems subsection, the PGL
  construction and its two results sections, related work, and the
  conclusion, beyond the automatic renumbering the D19 insertion causes. The
  exceptions are D22 and D23, whose complete edit lists (the grep-driven
  "unhalved" sweep, the two convention deletions in the model and mixing
  sections, the one introduction footnote, the model-section generalization
  with the figure relocation into the PGL construction section, and the
  `\ref{fig:run}` reread) are enumerated in the decisions themselves; they
  authorize those edits and no others.
- The sibling-instances section keeps its consolidated table (all five
  rows), its trust-base paragraph, and its S5 and S5xS5 prose; it loses only
  the den Boer and Kim mixing paragraph (D20) and gets an adjusted opener.
- The genus and covering-scheme narrative stays out of the paper.
- No new named theorem environments; Theorems A and B unchanged; the
  five-card section uses the existing proposition environment.
- Sibling instances (den Boer, Kim, S5, S5xS5) get no analogous
  `run_recover_*` corollary in this spec; the paper's architecture section
  cites only the worked instance. A parity sweep is a separate task if ever
  wanted.
