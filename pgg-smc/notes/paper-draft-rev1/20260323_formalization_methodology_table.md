## PGG Formalization Timeline: Semi-Automatic AI Workflow

**Duration:** 19 days (Mar 4–22, 2026) · **73 commits** · **58 files, 21.8K LOC** · **0 Admitted**

### Phase Table

| Phase | Dates | Commits | What Happened | Mood | AI Role | Key Moment |
|-------|-------|---------|---------------|------|---------|------------|
| **1. Scaffolding** | Mar 4–5 | 4 | HB mixin design (`PGGTypes`, `isMonodromyRepr`), piSMC session types, `perm_uniform` library, cyclic group instance | **Positive** — clean start | Human designs architecture, AI writes boilerplate via Write tool | `pgg_interface.v` + `pgg_pismc.v` established; learned painful lesson about dependent-type Send (separate send per dtype) |
| **2. Search Space Theory** | Mar 5–6 | 6 | RAAG trace equivalence, `hasGenerators` mixin, L-freeness via `vm_compute`, independent-set bound, free group ball-size, abelian word collapse | **Positive** — rapid expansion | AI scaffolds definitions; human directs mathematical structure | `vm_compute` reflection for L-freeness — a key AI-assisted technique |
| **3. Security Core** | Mar 6 | 3 | `pgg_security.v` security proof, abelian security collapse, security-storage tradeoff | **Positive** — theorems flowing | AI proves all axioms/admitted in `pgg_security.v` and `abelian_word_collapse.v` | First end-to-end security result |
| **4. Reconstruction** | Mar 7 | 3 | Prove Assumption 1, `partial_sum_no_info`, eliminate all axioms in reconstruct/ | **Positive** — axiom elimination | `rocq-expert-prover` agents handle individual lemmas | "eliminate last axiom in PGG-SMC reconstruct" — milestone |
| **5. Cartier-Foata** | Mar 7–9 | 4 | Clique traces, `total_comm_pairs`, Foata NF, generalized collusion bound | **Mixed** — hard combinatorics | `rocq-expert-prover` for batches of lemmas (3+7+3 = 10/10 Foata NF lemmas proved) | **Incident**: `rewrite !addn1` consumed 68 GB RAM, crashed machine. Led to `CLAUDE.md` safety rules |
| **6. Concurrent Build Crash** | Mar 9 | — | Subagent launched `make -j4` while main had `make -j4` running. 3 rocqworkers = 55 GB | **Frustration** — machine crash | AI self-inflicted wound: agents not reading memory | Created `CLAUDE.md` with compilation safety rules. Key lesson: *put critical rules where agents see them* |
| **7. Coding Theory Layer** | Mar 11–12 | 3 | Massey secret sharing from linear codes, AG codes on covering curves, axiom rationale docs | **Positive** — broadening | Human directs mathematical framing; AI writes code + documentation | `CoveringData`, `CoveringScheme` — algebraic geometry enters |
| **8. Paper Sprint #1** | Mar 13–14 | 8 | RS-Massey bridge, code-level axiom layer, extended abstract, 4 rounds of `fix-paper-review` | **Intense** — deadline pressure | `/review-paper` + `/fix-paper-review` skills used iteratively (rev1→rev3→rev4) | `aipv2026_extended_abstract.tex` tracked; hyperelliptic Goppa bound proved; `0 Admitted in reconstruct/` |
| **9. Algebraic Rigidity** | Mar 14–16 | 8 | `AlgebraicRigidity` records, Monster instance, fiber equidistribution, generalize from RAAG to `GeneratedMonodromyReprType` | **Positive** — unification | AI builds record hierarchy; human designs the abstraction | Monster group instance — "too large to enumerate but algebraic properties still hold" |
| **10. Unsatisfiable Axiom Crisis** | Mar 16 | 4 | `share_compatible` discovered unsatisfiable → replace with `ts_compatible` → also unsatisfiable → replace with `ts_perm_compatible` | **Frustration** — two pivots in one day | Human diagnoses; AI implements rewrites | 4 commits in one day just fixing axiom formulations. Architecture diagrams added to track Before/After |
| **11. Axiom Elimination Push** | Mar 17 | 7 | Derive `ts_perm_compatible` from code autos, weaken `monster_lfree1`, eliminate `star_covering` axiom, S₅ and overlapping-cycles AlgebraicRigidity instances | **Positive** — recovering | `rocq-expert-prover` proves derived lemmas | `genus0_covering` construction eliminates star axiom |
| **12. Pipeline Integration** | Mar 18 | 6 | `SecurityWitness` refactor, `certified_from_witness` bridge, `star_protocol_correct` end-to-end, `dealer_from_words` solver→protocol bridge | **Positive** — connecting | Human architects pipeline; AI builds bridges | End-to-end: solver output → protocol → security certificate |
| **13. Entropy Layer** | Mar 19 | 2 | General fiber entropy formula, Pinsker bridge, rename `RAAGDesc` → `GroupDesc` | **Positive** — clean math | AI formalizes information theory | Exact closed-form entropy for pushforward distributions |
| **14. Unified Pipeline** | Mar 20 | 2 | `ts_encode` in ThresholdScheme, unified two-phase security pipeline through AlgebraicRigidity | **Positive** — culmination | AI propagates through covering schemes | Two-phase pipeline: algebraic (group) + analytic (entropy) |
| **15. Pivot Crisis** | Mar 21 | — | 6-agent explore-audit: Barrington, oblivious permutation, mixing networks — **all three framings fail** | **Negative** — existential | `/explore-audit` with 3 research + 3 adversarial agents | "PGG is in a dead zone: theoretically interesting but practically isolated" |
| **16. Card Protocol Rebrand** | Mar 22 | 3 | Diaconis card-shuffle interpretation, rename MPC→card terminology throughout, drop "SMC" from headers | **Pivot** — new identity | AI does systematic rename (30 files); human chooses framing | share→dealt_hand, party→player, secret→outcome. Reframe as card-based crypto, not MPC |
| **17. Venue & Paper Strategy** | Mar 23 | — | Second explore-audit (ITP framing survives); venue survey identifies New Generation Computing as target | **Cautiously positive** | `/explore-audit` for paper framing; research agent for venue survey | "Zero Admitted, first ITP card-crypto" — the honest selling point |

### Narrative Arc Summary

```
Mood
  ▲
  │  ●1-4          ●11-14
  │   Scaffolding    Recovery &
  │   + Security     Unification        ●16-17
  │                                      Pivot to
  │        ●5                            card-crypto
  │        Cartier-Foata
  │        (hard but productive)
  │
  ├─────────────────────────────────────────────► Time
  │
  │              ●6              ●10
  │              RAM crash       Unsatisfiable
  │                              axioms (×2)
  │                                       ●15
  │                                       "Dead zone"
  ▼                                       audit
```

### AI Workflow Patterns Observed

| Pattern | Description | Frequency |
|---------|-------------|-----------|
| **Human architects, AI scaffolds** | Human designs types/records/pipeline; AI writes `.v` files via Write tool | Phases 1, 9, 12 |
| **Batch proving via `rocq-expert-prover`** | Delegate batches of lemmas to prover subagents (e.g., 10/10 Foata NF) | Phases 4, 5, 11 |
| **Adversarial self-audit** | `/explore-audit` with research + adversarial agents to stress-test claims | Phases 15, 17 |
| **Iterative paper review** | `/review-paper` → `/fix-paper-review` × 4 rounds | Phase 8 |
| **Systematic rename via AI** | AI handles mechanical 30-file renames after human decides direction | Phases 5, 13, 16 |
| **AI-inflicted incidents** | `rewrite !addn1` (68 GB), concurrent `make -j4` (55 GB) | Phase 5–6 |
| **Axiom discovery loop** | Formalize → discover unsatisfiable → pivot axiom → re-verify | Phase 10 |

### Key Frustration/Pivot Moments (for narrative)

1. **Mar 9 — Machine crash** (×2): concurrent builds + `rewrite !` blowup. Led to `CLAUDE.md` safety protocol. *"Subagents don't read memory — put rules where they'll see them."*
2. **Mar 16 — Unsatisfiable axioms**: `share_compatible` can't be instantiated → `ts_compatible` also can't → finally `ts_perm_compatible` works. Two false starts in one day.
3. **Mar 21 — "Dead zone" audit**: All three alternative framings (Barrington, oblivious permutation, mixing networks) fail adversarial review. *"Surface-level algebraic similarity mistaken for protocol-level connection."*
4. **Mar 22 — Rebrand pivot**: Abandon MPC framing entirely. Recast as card-based cryptography extending Diaconis shuffle fairness. 30 files renamed in one commit.
