# Rocq grinder: scale and feasibility evaluation

**Date:** 2026-05-23
**Status:** Research evaluation only. No design commitment. No plan written. Pause requested before any further stage.

## TL;DR

Building a Lean-`grind`-style tactic in Rocq is **feasible but expensive**, and the scope splits cleanly into a **modest MVP (4–9 person-months)** and an **ambitious full port (2–4 person-years)**. Lean's `grind` is ~43,000 lines of code, 806 commits over ~24 months, 88% authored by Leonardo de Moura — effectively a ~2-person-year sustained single-architect effort. Rocq already has the *infrastructure* (kernel reduction, `Evd`, an existing congruence-closure plugin) but lacks the *integration*: nothing in the Rocq ecosystem currently does congruence closure + E-matching with triggers + arithmetic/Boolean propagators in one saturated loop. The closest existing tools are `sauto`/`hauto`/`qauto` (CoqHammer), which use CIC inhabitation rather than SMT-style saturation, and `itauto`, which is propositional-only with theory leaves. The realistic first step is **extending `plugins/cc/cctac.ml` with `simp` + `lia` glue and an `@[grind]`-style hint DB**, deferring E-matching and theory propagators to a later phase.

## 1. What we are trying to match

Lean's `grind` is an SMT-inspired one-shot prover. Its named components:

- **Congruence closure** over a shared union-find e-graph, ignoring types/instances/proofs.
- **E-matching with multi-patterns** (1,599 LoC just for the theorem index), with user-declarable triggers via `@[grind]`, `@[grind →]`, `@[grind ←]`, `@[grind =]`, plus a `grind_pattern` command and `where` filter DSL.
- **Theory solvers** (12,370 LoC): `Cutsat` (cutting-plane linear integer, supersedes `omega`/`linarith` inside grind), `Linear` (rational LA), `CommRing` (Gröbner-basis solver), `Order`, `AC` completion.
- **Propagators** for Boolean, injectivity, and user-extensible theories.
- **Splitting / case analysis** driven by the congruence engine, not a SAT core — DPLL-flavored but congruence-led.
- **`grind_norm` simp set** for pre-normalization; `grind only [...]` restricts the lemma set; `#grind_lint` flags runaway patterns.
- Produces kernel-checkable proof terms.

Scale and effort (verified via `lean4` master, May 2026):

| Component                           | Files | LoC    |
|-------------------------------------|-------|--------|
| `src/Init/Grind/`                   | 41    | 10,720 |
| `src/Lean/Meta/Tactic/Grind/`       | 157   | 29,379 |
| `src/Lean/Elab/Tactic/Grind/`       | 17    | 2,856  |
| **Total grind**                     | **215** | **~42,955** |
| `aesop` (community/leanprover-community) | 250 | ~24,309 |

806 commits over 2024-05-14 to 2026-05-11, 88% by de Moura. ~1.77× the size of `aesop`. No peer-reviewed paper specifically on `grind` yet; the canonical reference is the Lean 4.22.0 (2025-08-14) release notes plus the reference-manual chapter.

What `grind` is **strong on**: equational reasoning with congruence, mixed `Nat`/`Int`/`Bool` ground goals, linear integer arithmetic, commutative-ring identities, propositional/Boolean propagation, and goals where a finite tagged lemma set plus arithmetic closes everything.

What `grind` is **weak on**: higher-order unification, dependent-type elaboration puzzles, non-ground first-order reasoning (no built-in resolution/superposition), large SMT-scale formulas, goals needing creative induction.

## 2. Where Rocq stands today

Built-in: `auto`/`eauto` (hint-db backward chaining), `intuition`/`tauto` (propositional, LJT), `firstorder` (naive Gentzen FOL), `congruence` (Nelson-Oppen ground CC, no quantifiers, no arithmetic), `lia`/`nia`/`lra`/`nra`/`psatz` (arithmetic, ground), `field`/`ring` (reflective normalizers), `decide`/`decide equality`. MathComp adds `mczify` to retarget `lia`/`nia`/`lra` onto `ssrnum`/`ssrint`, plus keyed-matching `rewrite`.

External: **CoqHammer** ships an ATP bridge (`hammer`) and a standalone CIC-inhabitation engine (`sauto`/`hauto`/`qauto`) which is currently Rocq's strongest single-button tactic. **Tactician** offers learning-based tactic suggestion (k-NN, Graph2Tac); reportedly solves up to 26% of theorems autonomously as of 2024. **Itauto** is a reflexive DPLL-based intuitionistic SAT with theory leaves — the spiritual closest to "SAT modulo theories lite" in Rocq, but propositional. **Mtac2** and **Coq-Elpi** are metaprogramming platforms (no public grind-class client). **CPDT's `crush`** is a hand-rolled `repeat (intuition; subst; eauto; congruence; lia)` blob, still used in some developments.

**The specific gap.** Nothing in the Rocq ecosystem does:
- E-matching with user-declarable triggers as a first-class facility
- Integrated ground completion / Knuth-Bendix beyond `ring`/`aac`
- A single unified normalize + congruence + simp + arithmetic fixed-point loop
- Theory propagators (Nat, Int, Bool) integrated inside the congruence engine

`sauto` solves many goals `grind` would, but via different mechanics (inversion, heuristic instantiation, hint-driven search). The two are not directly comparable; `grind` would win on SMT-flavored goals with rich equational rewriting, `sauto` on inductive/inversion-heavy goals.

## 3. Implementation pathways

**Language choice.** Pure Ltac1 is inadequate. Ltac2 has hashtables and arrays but the FFI cost and missing hash-cons exposure make the CC+E-match inner loop awkward; usable for the *frontend*. **OCaml plugin (`Declare ML Module`)** is the proven path — `congruence`, `lia`, `firstorder`, `Btauto` all live there. Coq-Elpi is strong for E-matching prototyping (λProlog HO-pattern unification is native) but weak for the imperative CC core. MetaCoq and Mtac2 pay reification cost on every step; not competitive for a hot inner loop.

**Realistic pathway: hybrid.** OCaml plugin core (CC engine + E-matching index + propagator framework), Ltac2 frontend (hint registration, splitting policy, simp integration).

**Reuse opportunity.** `plugins/cc/cctac.ml` and `ccalgo.ml` already implement Nelson-Oppen-style congruence closure with proof reconstruction in Rocq — a ~20-year asset and the natural extension target. `EConstr`/`Evd`/`Reductionops.whd_all` for term manipulation. `Hints` DB for hint storage (though backward-chaining-shaped; would need a parallel forward/E-matching DB). `Conv_oracle` for the "transparent for grind" oracle. The existing CC predates `EConstr` in places and is not designed for incremental push/pop, so the extension is non-trivial.

**Algorithmic challenges specific to Rocq.**

- **Universe polymorphism.** CC must treat universe instances of e.g. `@eq@{u}` as equal-up-to-unification or it will duplicate equivalence classes. Manageable but real engineering cost.
- **Typeclass / canonical-structure resolution** can fire during unification and diverge. The plugin must use rigid matching modes (`Evarconv` with classes disabled).
- **MathComp `eqType` lifting.** Goals stated with `==` (boolean equality) must be lifted to `=` via `eqP` for the CC engine, or MathComp users get nothing. This is a finite but real engineering surface.
- **Reducer choice.** Lean has one canonical reducer; Rocq has `cbn`/`cbv`/`lazy`/`simpl`/`vm_compute`/`native_compute`. Probable answer: `cbn` for user-facing normal forms, `vm_compute` only for closed ground certificate-check (à la `lia`). Documenting and defaulting the choice is half the design work.

## 4. Effort estimate

Honest ranges; treat as order-of-magnitude.

| Scope                                                                | Single senior author | Notes |
|----------------------------------------------------------------------|----------------------|-------|
| MVP: extend `cctac` with `simp` + `lia`/`nia` glue, `@[grind]` hint DB, Ltac2 frontend; no E-matching | **4–9 person-months** | ~60% of `grind`'s utility on first-order + decidable-arith goals |
| Add E-matching with triggers + Boolean propagator                    | +6–12 person-months  | This is where the engineering depth shows |
| Add cutsat-equivalent integer solver + Gröbner ring + AC completion  | +12–18 person-months | Each is a separate research-grade deliverable |
| **Full grind-equivalent**                                            | **~2–4 person-years** | + 0.5–1 person-year of kernel/elaborator collaboration |

For comparison: Lean's `grind` consumed ~2 person-years of de Moura's time directly. Rocq starts ahead on CC (`cctac` exists) and arithmetic (`lia` exists) but loses ground on universe handling, the Rocq 8.x→9.x split maintenance matrix, and the lack of an integrated simp framework comparable to Lean's.

## 5. Risk factors

- **Performance.** OCaml plugins can match Lean in principle. Realistic expectation: 1.5–3× slower than Lean `grind` on equivalent goals, driven primarily by `EConstr` being less hash-cons-friendly than Lean 4's kernel terms. Not a deal-breaker.
- **MathComp adoption.** Without `eqType` lifting and `ssrnum` integration via `mczify`-style retargeting, the tool is dead on arrival in the MathComp community.
- **Community fragmentation.** Users have invested in `sauto`/`hammer`/`itauto`/`lia` ladders. A grinder must be *strictly better than `sauto` with cooked hints* to displace usage. `sauto` is already widely effective with the right invocation.
- **Rocq 8.x ↔ 9.x split.** The 2025-03-20 Rocq 9.0 release forks the maintenance matrix. Expect ~10–20% continuous engineering overhead just tracking API changes, the dominant cost for plugins like `coq-equations` and `mathcomp`.
- **Strategic posture.** Some Rocq users cite `grind`/`aesop` as their reason to migrate to Lean. Building this is partly defensive. Whether it is *visionary* depends on whether the Rocq core team also commits to the kernel-side investments (hash-consing, reducer unification) that make `grind` shine in Lean.

## 6. Recommendation

If the goal is "ship something useful within a year," the realistic minimum-viable version is:

> Extend `plugins/cc/cctac.ml` with a `simp` / `lia` / `nia` driver, expose `@[grind]`-style hint annotations via a fresh hint DB, ship an Ltac2 frontend.

This is a **4–9 month single-author project** that delivers maybe 60% of `grind`'s utility on first-order and decidable-arithmetic goals, without committing to E-matching or theory propagators. It is the smallest unit that produces a recognizable "grind" experience for Rocq users.

The ambitious version (E-matching + propagators + splitting + MathComp `eqType` integration + cutsat-equivalent + Gröbner) is **multi-person-year** and only worth doing if paired with kernel-side investment in hash-consing and reducer unification.

**Smart first step (before any implementation):** profile `cctac` on a Lean-`grind` benchmark suite ported to Rocq, identify the top-3 missing capabilities (almost certainly: rewriting-during-CC, `lia` integration, and `eqType` lifting), and ship those as a `cctac+` extension before committing to a full E-matching engine. Do not start from scratch — `ccalgo.ml` is a 20-year asset.

## 7. Open questions for the next gate

Before proceeding past evaluation into design, the project needs an answer to each of these. Pausing now.

1. **Scope target.** MVP (4–9 PM, partial `grind` parity) or full port (2–4 PY)? Or research-prototype-only (3 PM, paper-shaped)?
2. **Who.** Is there a person budgeted? Lean's `grind` was 88% one person; the same author concentration would be needed in Rocq.
3. **Audience.** Pure-Rocq users, MathComp users, or both? MathComp support roughly doubles the engineering surface.
4. **Strategic frame.** Is this defensive (slow Lean migration) or offensive (deliver something Lean doesn't have)? The two have different design priorities.
5. **Funding / governance.** Rocq inria team buy-in needed for `plugins/cc` extensions? Or out-of-tree plugin first?
6. **Benchmark.** Without a Lean-`grind` benchmark ported to Rocq, the MVP scope cannot be sized accurately. Building that benchmark is itself ~2–4 weeks.

## References

```
[1] (https://lean-lang.org/doc/reference/latest/The--grind--tactic/)
    Lean Language Reference, "The grind tactic" chapter. Canonical user-facing
    documentation: components, attributes, E-matching, theory solvers.

[2] (https://lean-lang.org/doc/reference/latest/releases/v4.22.0/)
    Lean 4.22.0 release notes (2025-08-14). First stable release announcing
    grind + cutsat + Gröbner.

[3] (https://github.com/leanprover/lean4/tree/master/src/Lean/Meta/Tactic/Grind)
    The grind implementation itself (~30k LoC across 157 files in this subdir).

[4] (https://leanprover-community.github.io/mathlib4_docs/Init/Grind/Tactics.html)
    Mathlib4 docs, Init.Grind.Tactics — mirror of the upstream attribute/syntax
    reference; useful for surveying @[grind] usage.

[5] (https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/logic.html)
    Rocq Reference Manual, solvers for logic and equality. Covers auto, eauto,
    intuition, tauto, firstorder, congruence.

[6] (https://coqhammer.github.io/)
    CoqHammer project page; sauto/hauto/qauto are the closest existing Rocq
    analogue to grind/aesop.

[7] (https://www.mimuw.edu.pl/~lukaszcz/sauto.pdf)
    Czajka, "Practical proof search for Coq by type inhabitation", IJCAR 2020.
    Algorithmic basis of sauto.

[8] (https://coq-tactician.github.io/)
    Tactician project page. Learning-based tactic suggestion; orthogonal to
    grind (search guidance, not theory reasoning).

[9] (https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.9)
    Besson, "Itauto: An Extensible Intuitionistic SAT Solver", ITP 2021.
    Closest Rocq analogue in spirit (SAT-with-theory-leaves) but propositional-only.

[10] (https://github.com/rocq-prover/rocq/tree/master/plugins/cc)
     Rocq cc plugin source. ccalgo.ml and cctac.ml implement the existing
     congruence-closure procedure with proof reconstruction; the natural
     extension point for a grind-style tactic.

[11] (https://rocq-prover.org/news/2025-03-20-rocq-9.0/)
     Rocq 9.0 release notes (2025-03-20). Documents the API surface changes
     affecting plugin authors maintaining across 8.20 LTS and 9.x.

[12] (https://github.com/LPCIC/coq-elpi)
     Coq-Elpi repository. Elpi is λProlog with HO-pattern unification; candidate
     frontend for E-matching-style pattern queries.
```

Unverified / best-effort caveats:
- Exact mathlib coverage of `@[grind]` annotations is still actively expanding; no canonical count.
- The "supersedes `omega`" claim is verbatim from the 4.22.0 release note but mathlib still defaults to `omega` standalone in many places.
- No peer-reviewed paper specifically on `grind`; the canonical references are de Moura's Zulip threads, the reference-manual chapter, and the release notes.
- Effort estimates are order-of-magnitude; treat the ranges accordingly. The MVP range (4–9 PM) is the most reliable; the full-port range (2–4 PY) carries the most uncertainty.
- `sauto` vs `grind` head-to-head benchmarks have not been published; comparative claims in this report are based on architectural analysis, not empirical data.
