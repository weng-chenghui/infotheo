# Explore-Audit Report: Mechanically checking whether a theorem prover's output is "mathematically meaningful" vs vacuous

**Date:** 2026-05-24
**Directions explored:** 5
**Method:** 5 parallel research agents (Phase 1) + 5 parallel adversarial audit agents that re-verified every citation and codebase claim independently (Phase 2).

---

## Executive Summary

The question "is this proved theorem *meaningful*, or merely vacuously true?" is a real, named problem with deep prior art in five distinct literatures. The strongest finding, consistent across all five, is an **asymmetry**: the *negative* side ("this is known-meaningless") is mechanizable and largely complete on known patterns; the *positive* side ("this is significant / deep / interesting") has resisted 40+ years of mechanization (AM, EURISKO, HR, DeepMind) and still bottoms out in human judgment or learned proxies. So the honest design target is **not** "certify meaningful" but "certify *not-known-to-be-meaningless*" = pass a blacklist of vacuity patterns + a faithfulness check that the formal statement matches the intended informal claim. This is exactly what current LLM-autoformalization pipelines do (goal-falsification vacuity check, triviality-by-automation filter, bidirectional-equivalence faithfulness), and it is exactly the pattern your own DSDP code already practices (`card_t_msg_gt0` + "residual non-vacuous"), where the audit also confirmed a genuine open gap (no `epsilon_cpa < 1` constraint, so the headline bound is currently vacuous-if-instantiated-badly).

**Answer to your framing question (blacklist / whitelist / middle):** a *layered middle*, but asymmetric. A blacklist is the mechanizable workhorse; a semantic faithfulness layer sits in the middle; a whitelist of "significance" is not mechanizable and should stay a human/learned call. Details in the Recommendation.

---

## Direction 1: Vacuity detection in model checking / temporal logic

### Research findings
The canonical CS literature on "the property passed for a trivial reason." Originated with Beer, Ben-David, Eisner, Rodeh (CAV 1997 / FMSD 2001): `AG(request -> AF grant)` passes vacuously when no request ever occurs (antecedent failure). Kupferman & Vardi generalized it (ACTL -> CTL/CTL*) with the "subformula does-not-affect" definition: replace a subformula with true/false and re-check; if the verdict never changes, the subformula is irrelevant and the pass is vacuous. Refinements: Armoni et al. (mixed polarity), Namjoshi (proof-based detection), Temporal Antecedent Failure (the reliably-actionable subset). Dual notion: *coverage* (Chockler-Kupferman-Vardi) = "spec misses parts of the design" vs vacuity = "spec is too weak." ~20% of industrial specs reportedly pass vacuously on first run.

### Audit verdicts

| Claim | Verdict | Key reasoning |
|-------|---------|---------------|
| C1 Origin Beer et al. CAV 1997 + FMSD 2001 18(2):141-163 | TRUE | Confirmed title/venue/pages. |
| C2 Semantic per-formula (Kupferman & Vardi) | SUSPICIOUS (venue error) | Method/definition correct, but it was **CHARME 1999, LNCS 1703** (not CAV 1999 / LNCS 1633). |
| C3 Armoni et al. enhanced/mixed-polarity | MIXED (venue error) | Authors + contribution real, but **CAV 2003, LNCS 2725** (not LNCS 2933). |
| C4 Temporal Antecedent Failure FMSD 2015 | TRUE | Ben-David, Copty, Fisman et al., FMSD 46(1):81-104. |
| C5 Vacuity/coverage duality CHARME 2003 | TRUE | Confirmed. |
| C6 Namjoshi proof-based CAV 2004 | PARTLY TRUE | Paper real; exact O(n^2) phrasing not confirmed verbatim. |
| C7 ~20% pass vacuously (IBM RuleBase) | UNVERIFIED | Plausible, widely repeated, but no single transparent primary source pinned down. |
| C8 "Does NOT transfer to Coq/Rocq" | OVERSTATED | Algorithm doesn't port, but the *concept* (antecedent failure, unused hypotheses) clearly does; Coq has `Print Assumptions` + proof-term analysis as adaptation paths. |

### Bottom line
Literature is real and foundational; the report's "doesn't transfer to proof assistants" conclusion conflates algorithm-transfer with concept-transfer and is overstated. The concept transfers; the finite-state algorithm does not.

---

## Direction 2: Autoformalization faithfulness (LLM <-> formal meaning)

### Research findings
The most directly relevant direction. An LLM autoformalizes an informal claim; the result type-checks and even proves, but doesn't mean what was intended (vacuous premise, wrong quantifier scope, trivial unfolding). Concrete mechanical filters already deployed:
- **Goal-falsification vacuity check** ("Don't Trust: Verify", ICLR 2024): replace the goal with `False`; if a prover closes it, the hypotheses are contradictory -> statement is vacuous -> discard.
- **Triviality filter** (LeanConjecturer): if `aesop`/`exact?` alone closes it, mark non-novel/trivial.
- **Faithfulness metrics**: BEq (bidirectional definitional equivalence: prove `PA -> PB` and `PB -> PA`); GTED (tree-edit distance); round-trip re-informalization + embedding similarity; FormalAlign; type-check + self-consistency selection.
- miniF2F-v1 had >50% statements misaligned with intent (-> v2 hand-corrected), quantifying how common the failure is.

### Audit verdicts

| Claim | Verdict | Key reasoning |
|-------|---------|---------------|
| C1 Vacuous statements a recognized failure mode | TRUE | All four cited papers exist and confirm it. |
| C2 `show false` goal-falsification vacuity check | TRUE | Verbatim method in "Don't Trust: Verify" (ICLR 2024). |
| C3 `aesop`/`exact?` triviality filter | TRUE | Verbatim in LeanConjecturer. |
| C4 No pure blacklist/whitelist; semantic middle ground | TRUE | Symbolic-equivalence + semantic-consistency (NeurIPS 2024). |
| C5 BEq bidirectional equivalence | TRUE | Confirmed (both-direction provability). |
| C6 "+18.3% -> 53.2% on ProofNet" | SUSPICIOUS | Conflated numbers; actual reported ~31.0% -> 45.1% on ProofNet#. Treat the specific figure as unreliable. |
| C7 GTED / BEq+ / ProofFlow metrics | MOSTLY TRUE | Metrics real; "ProofScore" as a standalone metric not cleanly confirmed. |
| C8 No standardized meaningfulness-filter stage; open problem | TRUE | Survey + FormalAlign confirm it's unsolved/active. |
| **All ~15 arXiv IDs (incl. suspicious-looking 2604.25031, 2512.xxxxx)** | TRUE | Every ID resolved to the claimed title. 2604.25031 = "Faithful Autoformalization via Roundtrip Verification and Repair" (Apr 2026). No fabricated citations. |

### Bottom line
After dropping the one inflated percentage, the core holds fully: mechanical vacuity + triviality + faithfulness filters exist and are in use. This is the most mature and most directly transplantable body of work for the user's goal.

---

## Direction 3: Specification quality / triviality / mutation testing

### Research findings
The engineering literature on "is my spec strong enough or trivially satisfied?" Key pieces: vacuity in model checking (VaqUoT); **mutation testing of specs** (IronSpec, OSDI 2024; MutDafny) - mutate the system and check the spec still catches it, else the spec is too weak; **property specification patterns** (Dwyer-Avrunin-Corbett 1999) as a vetted whitelist of "good shapes"; Alloy/TLA+ over-constraint detection via unsat cores; Coq `Print Assumptions` for axiom-dependency (a real but narrow "meaningfulness" slice: trust, not triviality); proof-irrelevance (Lovas & Pfenning).

### Audit verdicts

| Claim | Verdict | Key reasoning |
|-------|---------|---------------|
| C1 VaqUoT + ~20% vacuous | TRUE (model-checking only) | Real; not for dependent types. |
| C2 MutDafny / IronSpec; ~1 weak spec / 241 LOC | TRUE but DATE ERROR | Both real, finding confirmed; **MutDafny is arXiv 2511.15403 = Nov 2025, not 2024**. |
| C3 Temporal anti-patterns ICSE 2023 NIER; "58 microservice antipatterns" | PARTLY TRUE | Anti-patterns paper real; the "58 microservice" figure is misattributed/overstated. |
| C4 Dwyer-Avrunin-Corbett ICSE 1999 whitelist | TRUE | Confirmed, pp. 411-420. |
| C5 Proof relevance/irrelevance distinct (Lovas & Pfenning TLCA 2009) | TRUE | Confirmed. |
| C6 `Print Assumptions` = axiom check not vacuity | TRUE | Correct and real. |
| C7 "Proof length is the ONLY triviality metric" | OVERSTATED | Closure-by-`trivial`/`auto`/`aesop` is also a triviality signal. |
| C8 Over-constraint != vacuous truth | TRUE | Distinct failure modes. |
| Negative claim: "no Coq vacuity tooling exists" | INCOMPLETE | Audit flags missed neighbors: Isabelle **Mutabelle**/Bulwahn QuickCheck (mutation/counterexample), **Hammer for Coq** relevance filtering, `Print Assumptions`. None is a full vacuity detector, but the gap is smaller than stated. |

### Bottom line
Direction is sound but conflates "spec in a weak logic" with "proof in dependent types," and missed adjacent Coq/Isabelle tooling. Mutation testing of *proofs* (does the proof still go through after deleting/mutating a hypothesis?) is the transplantable idea here.

---

## Direction 4: Interestingness / significance in automated theorem discovery

### Research findings
The oldest attempt to mechanize "is this worth caring about?" AM/EURISKO (hand-coded interestingness heuristics; Lenat pivoted to Cyc), Ritchie-Hanna critique (the "meaning" was smuggled in via undocumented heuristics), Colton's HR (weighted interestingness: novelty + surprisingness + difficulty; sequences accepted into OEIS), Fajtlowicz GRAFFITI's Dalmatian heuristic (discard non-informative conjectures), **QuickSpec/Hipster** (irreducibility + subsumption: drop any conjecture already provable from known equations), ML premise selection (usefulness-as-significance proxy), DeepMind 2021 Nature (AI finds patterns, humans judge significance).

### Audit verdicts

| Claim | Verdict | Key reasoning |
|-------|---------|---------------|
| C1 AM/EURISKO hand-coded; -> Cyc | TRUE w/ caveat | "metareasoning abandoned" is misleading; pivot was about knowledge-engineering cost, not impossibility. |
| C2 Ritchie & Hanna critique 1984 (AIJ 23(3)) | TRUE | Confirmed. |
| C3 HR weighted interestingness; **"20 OEIS sequences"** | PARTLY FALSE | HR contributed **17**, not 20; exact additive formula is inferred, not stated. |
| C4 GRAFFITI Dalmatian heuristic; ~80 papers | TRUE | Confirmed. |
| C5 QuickSpec/Hipster irreducibility + subsumption | TRUE | Confirmed; this is a true triviality/redundancy *blacklist*. |
| C6 ML premise selection; "61% reprove on Mizar" | SUSPICIOUS | Number exists but is config-specific and muddled across systems. |
| C7 DeepMind 2021 Nature | TRUE | Davies et al., Nature 600:70-74. |
| C8 LLM conjecturing still needs multi-stage + human | TRUE | LeanConjecturer + "Mining Math Conjectures" confirmed. |

### Bottom line
The thesis - *negative/triviality filters (blacklist) mechanize and work; positive significance criteria (whitelist) don't scale without humans* - survives scrutiny despite the "17 vs 20" inflation and the muddled 61% figure. Most transferable technique: **irreducibility + subsumption filtering** (drop conjectures provable from what you already have).

---

## Direction 5: Crypto / IT-security vacuity (incl. your codebase)

### Research findings
Vacuous security definitions are a recognized hazard: a definition everything satisfies, an advantage bound with RHS >= 1 (trivially true since advantage <= 1), a zero-leakage `I(secret;view)=0` claim that holds only because the *view* was modeled too coarsely, a UC simulator that "succeeds" only because the ideal functionality over-leaks. Formal-crypto frameworks (EasyCrypt, CryptHOL, FCF, SSProve, CertiCrypt) mechanize the *games* but do not prevent vacuous *definitions*. The audit independently opened your files and confirmed concrete findings.

### Audit verdicts

| Claim | Verdict | Key reasoning (real file:line) |
|-------|---------|--------------------------------|
| C1 Defs must admit secure & exclude broken (Goldwasser-Micali) | TRUE | Confirmed. |
| C2 Frameworks don't prevent vacuity; FCF arXiv 1410.3735 | TRUE | Confirmed. |
| C3 Perfect secrecy `I=0`; Shannon date | TRUE | Correctly dated 1949 ("Communication Theory of Secrecy Systems"). |
| C4 UC trivial simulators (Canetti eprint 2000/067) | TRUE | Confirmed. |
| C5 Advantage bound >= 1 is vacuous | TRUE | Sound. |
| C6 `card_t_msg_gt0` + bound + "residual non-vacuous" | TRUE | `dsdp_security_indcpa.v:796` hypothesis; `:877` bound `<= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa`; `ref/dsdp_security_indcpa_concrete.v:308` comment + `:315` lemma. All verified verbatim. |
| C7 No `epsilon_cpa < 1`; only `epsilon_cpa_ge0` | TRUE | `dsdp_security_indcpa.v:883` `epsilon_cpa_ge0`; `indcpa_ror.v:242` bare `Parameter epsilon_cpa`; grep finds no `< 1` anywhere. |
| C7c "bound vacuous if epsilon_cpa = 1" | TRUE but CONTEXT-DEPENDENT | Math sound (RHS >= 2 > 1). But abstract theorem is currently `Aborted`, and `epsilon_cpa` stays an abstract section hypothesis in concrete instances (never set), so the gap is real-but-not-yet-triggered; standard practice assumes the instantiator bounds it small. |
| C8 General mechanical crypto-meaningfulness checker | TRUE | Arithmetic vacuities (RHS>=1, |set|<=1, eps>=1) mechanizable; semantic ones (over-leaking sim, degenerate view) need domain axioms. |
| C9 "Bernstein (2010), arXiv:2010.11961" | **FALSE / misattributed** | That paper is **Renes & Renner (2020)**, "Are quantum cryptographic security claims vacuous?", *responding to* Bernstein's critique. Year is 2020 (arXiv 2010 = Oct 2020), author is not Bernstein. Do not cite as given. |

### Bottom line
Your codebase claims are real and accurately reported against the actual files, and the `epsilon_cpa < 1` omission is a genuine (currently latent) vacuity gap. Crypto/IT-security is the *most feasible* domain for a partial mechanical checklist because so many vacuity conditions are arithmetic (RHS<1, cardinality>1, residual>0, epsilon<1), and you already use the pattern.

---

## Cross-Cutting Analysis

### What survived audit (robust, reusable)
1. **Vacuity-by-goal-falsification** (replace goal with `False`; provable => contradictory hypotheses => vacuous). Real, deployed (ICLR 2024). Ports to Coq/Rocq directly.
2. **Triviality-by-automation** (closed by `trivial`/`auto`/`easy`/`firstorder`/hammer alone => trivial). Real (LeanConjecturer, QuickSpec).
3. **Irreducibility + subsumption** (follows from already-known lemmas => redundant). Real (QuickSpec/Hipster).
4. **Hypothesis-necessity via mutation** (delete/mutate a hypothesis; if proof still closes, hypothesis was decorative/vacuous). Real (IronSpec/MutDafny lineage; adaptable to proof terms).
5. **Faithfulness / BEq** (formal statement <-> informal intent, bidirectional provability or round-trip informalization). Real, the "true but not what we meant" catch.
6. **Domain arithmetic guards** for crypto (advantage RHS < 1, |support| > 1, epsilon < 1, IT residual > 0). Real, and already partially in your code.
7. **`Print Assumptions`** as an axiom-trust slice (orthogonal to vacuity but cheap and real).

### What failed audit (do not rely on)
- The "Bernstein 2010 / arXiv:2010.11961" citation (misattributed; it is Renes & Renner 2020).
- "HR contributed 20 OEIS sequences" (it was 17).
- The autoformalization "+18.3% -> 53.2% on ProofNet" figure (conflated; ~31% -> 45.1%).
- The blanket "vacuity detection does not transfer to proof assistants" (overstated: concept transfers).
- The implication that "no Coq/Isabelle proof-vacuity tooling exists" (missed Mutabelle, Hammer relevance, `Print Assumptions`).
- Minor venue/volume/date slips: Kupferman-Vardi = CHARME 1999/LNCS 1703; Armoni = CAV 2003/LNCS 2725; MutDafny = Nov 2025.

### Suspicious claims needing follow-up before relying on them
- The "~20% of specs pass vacuously" industrial figure (repeated everywhere, no clean primary source pinned).
- The "61% reprove on Mizar" premise-selection number (config-specific; check Kaliszyk-Urban 2015 directly before quoting).

---

## Recommendation

**Direct answer to "blacklist, whitelist, or middle?":** Build a **layered, asymmetric middle**, and be honest about what each layer certifies.

- **Layer A - Blacklist of vacuity/triviality (mechanizable, do this first).** A finite, growable catalog of *known-meaningless patterns*, each a decidable check on the statement + proof term:
  - goal-falsification vacuity (goal := False provable),
  - triviality (closed by automation alone),
  - redundancy/subsumption (follows from existing lemmas),
  - unused-hypothesis / mutation (proof survives hypothesis deletion),
  - degenerate-domain guards (|type| <= 1, trivial group/ring, empty index),
  - crypto arithmetic guards (RHS >= 1, epsilon >= 1, residual = 0).
  This layer is where the LLM+prover tool's output can be **mechanically rejected**. It is near-complete on *known* patterns and grows monotonically as you discover new ones - this is the right home for "we know what is NOT meaningful."

- **Layer B - Faithfulness (semantic middle, partly mechanizable).** Does the proved formal statement actually mean the informal claim it was generated from? Use BEq-style bidirectional equivalence and/or round-trip re-informalization. This is the only layer that catches "true, non-vacuous, but answers the wrong question."

- **Layer C - Significance / "interesting" (NOT a mechanical whitelist).** 40 years of evidence says don't try to *certify* depth/importance mechanically. Keep this as a human or learned-proxy signal (e.g., does the lemma get used downstream?). Treat a passing item as **"not-known-to-be-meaningless,"** never as **"proven meaningful."**

**Framing to adopt:** the tool should output a verdict like *"non-vacuous (passed blacklist) and faithful (passed BEq) - significance unjudged,"* not *"meaningful."* This is both the honest position and the one the literature converges on.

**Where it has teeth in your own work:** your DSDP files already implement Layer A for one pattern (`card_t_msg_gt0`, "residual non-vacuous"). Two concrete next steps that double as a proof-of-concept for the whole idea: (1) add the missing `epsilon_cpa < 1` (ideally a smallness/negligibility hypothesis) so the headline bound cannot be instantiated vacuously, and (2) write a small Ltac/meta check that, given a security bound `Pr[...] <= e`, fails if `e` is not provably `< 1`. That single check is a working instance of a mechanical crypto-vacuity blacklist entry, and it is the cheapest path from "interesting idea" to "demonstrated on a real codebase."

**If you want to publish/position this:** the gap the audit confirms is real - there is no standardized, reusable *meaningfulness filter* stage for dependent-type proof assistants (autoformalization filters are Lean-centric and statement-level; crypto guards are ad hoc; interestingness is human). A "vacuity/faithfulness linter for Rocq proofs, seeded from the crypto blacklist and the autoformalization goal-falsification + BEq checks" would be extending an open frontier, not reimplementing a solved one.

---

## Citation hygiene note (for any downstream writeup)
- Correct: Renes & Renner, "Are quantum cryptographic security claims vacuous?", arXiv:2010.11961 (2020), responding to Bernstein - **not** Bernstein 2010.
- Correct: HR contributed **17** OEIS sequences.
- Correct venues: Kupferman & Vardi - CHARME 1999 (LNCS 1703); Armoni et al. - CAV 2003 (LNCS 2725); MutDafny - arXiv 2511.15403 (Nov 2025).
- Do not quote the "+18.3% -> 53.2% ProofNet" figure; use the paper's actual ~31% -> 45.1%.
- The "~20% specs vacuous" and "61% Mizar reprove" numbers need a primary-source check before use.
