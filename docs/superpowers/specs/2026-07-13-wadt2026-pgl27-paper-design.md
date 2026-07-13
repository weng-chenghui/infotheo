# WADT 2026 full paper: design spec

Date: 2026-07-13. Status: approved design, pre-plan.

## Deliverable and venue

One LNCS paper for the WADT 2026 refereed post-proceedings
(Springer LNCS, 12-20 pages excluding references and appendices).
Submission deadline 2026-09-17, notification 2026-10-29, EasyChair
`staf2026`. The paper extends the abstract accepted and presented at
the workshop day (2026-06-30, Rennes); source of the abstract, the
slides, and the diagrams: `~/Projects/aplas2024-poster/wadtSep17/`.

- Title (continuity with the accepted abstract):
  **Algebraic Specification of Card-Based Cryptographic Protocols in Rocq**.
- Author: Cheng-Hui Weng, Nagoya University, solo. Funding line to be
  confirmed at drafting (the ITP 2026 source used mercari R4D).
- Not anonymous. Bibliography style `splncs04.bst`. The
  `WengEtAl2025` bib entry currently says `Anonymous Authors`; fix to
  the real author list before any build ships.

## Repository layout (new, in this repo)

```
pgg-smc/papers/wadt2026/
  main.tex               llncs; inputs sections/*.tex
  llncs.cls              copied from wadtSep17
  splncs04.bst           copied from wadtSep17
  wadt2026-macros.sty    copied from wadtSep17
  shared-macros.sty      copied from aplas2024-poster (kill the ../ path)
  sections/01-intro.tex ... 11-conclusion.tex
  figures/               PNGs + TikZ sources reused from wadtSep17
  references.bib         seeded from wadtSep17/references.bib
  Makefile               latexmk -shell-escape (minted)
  .gitignore             build artifacts
```

Prose-style and AI-declaration-style reference:
`~/Projects/aplas2024-poster/feb12ITP2026/feb12ITP2026.tex`
(minted `coq` blocks, `\coqin{file.v}` footnotes, Protocol/Program
floats, itemized Generative AI Declaration).

## Headline claims (both get a dedicated pre-submission audit)

1. Results: a Rocq framework in which a card protocol is a finite
   group with a permutation representation and a shuffle law,
   `(G, rho, mu; R)`, instantiated five times; in depth the new
   PGL(2,7) instance: coalition privacy from 3-transitivity, an exact
   recovery ramp (private through 3 revealed cards, determined at 7),
   executed-trace secrecy, and an in-kernel variation-distance bound
   `2^-40` at `L = 200`. Bounded against Koch-Schrempp-Kirsten 2021:
   interactive proof assistant plus information-theoretic coalition
   privacy, versus SAT-backed bounded model checking.
2. Method: to the author's knowledge, the first refereed development
   of new machine-checked security theorems whose proofs were written
   by LLM agents, under a disclosed human-specification /
   agent-proof division of labor, with the claim matrix as the
   conformance artifact binding every prose claim to a kernel object
   or an explicit disclosure.

## Introduction plan (problem-first; SSProve TOPLAS 15:2-15:3 pattern)

1. Setting: card-based protocols realise MPC with physical cards;
   security arguments are combinatorial, per-protocol, pen-and-paper
   (den Boer 1989; Mizuki-Shizuya 2014; Kim-Cetinkaya 2025).
2. Gap: machine verification so far is bounded model checking over
   fixed decks (Koch et al. 2019); it ignores algebraic structure and
   fixes deck size, shuffle length, and shuffle distribution; manual
   spectral analyses are single-parameter.
3. Contribution paragraph ("the main contribution of this work is..."),
   stating claim 1.
4. Technique paragraph: MathComp + infotheo; the transitivity-privacy
   bridge; executed-trace secrecy over a session-typed interpreter;
   binary-N walk certificates.
5. Method paragraph, stating claim 2.
6. Organization.

No metaphor opening. The surjection/fiber material and the
idea-evolution story are cut; at most one sentence each where they
naturally fit (Sections 2 and 9).

## Section map with sources (target 12-20 pp)

| S | Content | Sources | pp |
|---|---------|---------|----|
| 1 | Introduction (plan above) | - | 2 |
| 2 | Background: card protocols, Mizuki-Shizuya model, security as `H(secret\|view) = H(secret)`; two protocol families in one sentence (input-commit degenerates to plain dealer, which pgl27 executes with empty inputs) | MizukiShizuya2014, denBoer1989, KochWalzerHartel2015, Koch2019, KimCetinkaya2025 | 1.5 |
| 3 | The framework as used, each component introduced by its role under pgl27: interface types (`Gen_PGGTypes`, `pgg_rho`, `pgg_data`); `ThresholdScheme` `(k,T)` (`orbit_scheme`, `ts_recon_perm_invariant`); the piSMC runner (`run_interp`, `exchange_dealer/player/verifier`, `endpoints_of_trace`); the transitivity-privacy bridge (six theorems incl. `ttrans_view_indep_gen`, `coalition_view_mutual_info_le`); the trace-secrecy keystone (`trace_secrecy_of_view`); word-law vocabulary (`rho_from_words_weighted`, `endpoint_dist_weighted`). One honest paragraph presents `MonodromyProfile`/`SecurityWitness`/`ReconPlug` as thin uniformity packaging | pgg_interface.v, pgg_sharing_framework.v, smc_interpreter.v, smc_session_types.v, card_exchange_pismc.v, pgg_run.v, transitivity_privacy.v, pgg_trace_secrecy.v, pgg_weighted_words.v | 2.5 |
| 4 | The PGL(2,7) instance: orbit-class secret, the 14+56 orbit split, in-kernel 3-transitivity word search | pgl27_group.v, pgl27_orbit.v (`pgl27_3transitive`, `orbit_class_split`, `orbit_encodeK`) | 2 |
| 5 | Correctness and the exact recovery ramp; recovery-component table across instances (hearts-read 3, sum-mod 0, product sum-mod 5, pgl27 reveal ramp); den Boer 0.811-bit leakage cap in one sentence | pgl27_run.v, pgl27_recovery.v (`pgl27_run_recovers_class`, `pgl27_seven_reveal_determines`, `pgl27_six_reveal_ambiguous`, `pgl27_view_dep_k4`) | 2 |
| 6 | Privacy: view independence and leakage bounds; six executed-trace secrecy theorems; all-decks dealer; deck marginal (class-proportional prior = uniform over 40,320 decks) | pgl27_secrecy.v, pgl27_trace.v (`pgl27_view_indep*`, `pgl27_trace_secrecy`, `pgl27_coalition_trace_secrecy`, `pgl27_alldecks_*`, `pgl27_deck_*`) | 2.5 |
| 7 | Mixing: per-instance certified table (den Boer eps=0 at L=1; Kim 2^-40 at L=7 in-kernel; S5 2^-40 at L=286 external certificate; S5xS5 floor; pgl27 2^-40 at L=200 in-kernel); the binary-N certificate technique; `pgl27_card = 336` and `pgl27_gen5_eq` as zero-axiom byproducts. The general bound `mixing_bound_gen` is a `Local` lemma in the instance file and is credited as an instance contribution | pgl27_mixing.v; Stdlib BinNat | 2.5 |
| 8 | Sibling instances in brief: the eps-family (`five_card_profile`; den Boer = eps 0, Kim = biased); S5 and S5xS5 with sum-mod recovery; one context paragraph on the Klein cap `max(2n,60)` and Hurwitz genus bounds explaining why recovery is combinatorial rather than algebraic-geometry codes; honest S5 disclosure (external Rayleigh certificate, group-order axiom) | instances/, slides table, accepted abstract | 1 |
| 9 | Methodology: roles table (human = specification, design, audit, acceptance; agents = proof authorship; kernel = soundness; audit pipeline = statement integrity); the claim matrix as a prose-to-kernel conformance artifact with the termination rule; two-stage audit gate; axiom hygiene (trust base = boolp trio + vm_compute; group/orbit/recovery rows zero-axiom); full effort accounting (models, agent counts, wall-clock, tokens, audit statistics) reconstructed from git history, session logs, and `token-usage.json`; failure catalog (three lazy-eval bombs, agent stalls) playing the SSProve found-an-error role; trajectory from the abstract's "lemma development under supervision" to the claim-boundary regime | claim-boundary note `docs/superpowers/notes/20260713-pgl27-claim-boundary.md`, audit pipeline, git log | 2 |
| 10 | Related work, two lanes. Lane 1 card-crypto and verification: Mizuki-Shizuya, den Boer, Koch-Walzer, KSK 2021 (SBMC), Kim-Cetinkaya, and proof-assistant crypto frameworks (SSProve, CryptHOL, Butler et al.) as computational/simulation-based contrast. Lane 2 LLM formalization: AlphaProof (Nature 2025), Putnam-Rocq (arXiv 2603.20405), CertiCoq-ANF (arXiv 2602.20082), Gauss/strongpnt (web), EconCSLib (EC'26 workshop), ETP (arXiv 2512.07087) | research-kb slices | 1 |
| 11 | Conclusion: honest-gap progress (executed-trace secrecy landed for all instances since the talk; simulation-based composition still open); future work (algebraic-geometry recovery for feasible-genus groups; quantum direction in one line); Generative AI Declaration, itemized in the ITP 2026 style but covering agent proof authorship | boundary note, slides conclusion | 1 |

Overflow policy: Sections 4-8 compress first (proofs live in the
repo; the paper states and cites); Section 9 never compresses.

## Framework coverage policy (from the adversarial audit, 2026-07-13)

- LOAD-BEARING, presented fully: `pgg_interface`,
  `transitivity_privacy`, the piSMC runner layer, `pgg_trace_secrecy`,
  `ThresholdScheme`, `pgg_weighted_words` vocabulary.
- CONTEXT-ONLY, one honest sentence or paragraph:
  `MonodromyProfile` (single consumer proved `by []`),
  `SecurityWitness`/`SecurityExact` and `ReconPlug` (packaging; fields
  never projected in pgl27 proofs), `pgg_collusion_bound` (one
  transport lemma borrowed), `pismc.v` notations.
- CUT from credited content: covering/genus/Klein records
  (`CoveringScheme`, `ThresholdWitness`, `AlgebraicRigidity` record),
  `DropoutWitness`, `InputEncoding` beyond the degenerate prologue,
  `SecurityAsymptotic`, collusion-bound headline theorems,
  `leak_k1`/`additive_view_indep`/`leakage_product` machinery,
  algebraic-geometry code sections, `pgl27_pgl2_order` (orphan; no
  consumers; `pgl27_card` is proven independently).
- Forced honesty items for Section 9: `content_of` is copy-pasted in
  four instance files, not shared framework; the mixing bound's
  general lemma is instance-local; MathComp `primitive_action`
  (`ntransitive`, `dtuple_on`) and Stdlib binary-N arithmetic are
  credited as true dependencies.

## Voice and prose discipline

- Personal "I" for decisions and direction; mathematical
  reader-inclusive "we" only inside proofs and constructions; agents
  are the instrument, never authors.
- Theorem-environment bodies are terse mathematical statements; no
  meta, status, or effort talk in statement bodies.
- No em-dashes, no parenthetical asides, no semicolons in prose; no
  unexpanded abbreviations ("algebraic-geometry code", not "AG-code").
- Rocq identifiers appear in `\coqin{}` footnotes; body prose uses
  pen-and-paper names.
- Diagrams reused from the slides where they carry technical content:
  the `(G,rho,mu)` pipeline, the den Boer sequence diagram, the
  mixing-convergence plot, the records tree relabeled to the used
  subset. Labels use reader variables, never bare Rocq identifiers.

## Evidence pipeline (pre-submission obligations)

1. Full-text passes for every abstract-level knowledge-base slice
   cited: putnam2025-rocq-opus, econcslib-ec26, certicoq-anf-claude,
   AlphaProof Nature, gauss-mathinc (web-only; cite as such). No
   citation ships from an abstract-level slice.
2. First-claim audits for both headline claims: cross-instance check
   plus a fresh literature sweep near the deadline.
3. Effort-accounting reconstruction: commits, dates, proof-line
   counts from git history; agent counts, wall-clock, and tokens from
   session logs; audit statistics from
   `.claude/audit/central-state/token-usage.json` and run metadata.
4. Statistics recount at submission (the abstract said 85 files, 33K
   lines, 42 main theorems; the count has grown since).
5. Jargon table for the full draft; adversarial writing audit and
   citation audit before submission; Springer LNCS AI-policy re-read
   at submission time.
6. Confirm the EasyChair full-paper submission path and any
   presenter-eligibility fine print early (the abstract was presented,
   so this is expected to be a formality).

## Out of scope

- Fixing the framework-wide eps = 0 witness semantics or the
  pointwise 2-epsilon form (disclosed, not fixed).
- Refactoring `content_of` into shared framework code.
- Any new Rocq proof work beyond what effort accounting requires.
- The quantum direction beyond one future-work sentence.

## Next step

Invoke superpowers:writing-plans to produce the implementation plan:
directory scaffold, section drafting order (3 -> 4-7 -> 9 -> 2,8 ->
10,11 -> 1 last), audit and accounting tasks, and the build check.
