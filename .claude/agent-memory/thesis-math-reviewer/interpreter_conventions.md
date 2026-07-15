---
name: interpreter-conventions
description: Math-review conventions and pitfalls for thesis chapters/interpreter.tex vs smc/smc_interpreter*.v
metadata:
  type: project
---

Terminology map between thesis `chapters/interpreter.tex` and the Rocq
formalization (`smc/smc_interpreter.v`, `smc/smc_interpreter_sound.v`,
branch itp2026-dumas2017dual).

**Why:** the §3 soundness-decomposition prose is checked against the code; the
mapping is not 1:1 and one mismatch recurs.

**How to apply:** when reviewing this chapter, reuse this map instead of
re-reading the .v files.

- `proc` has exactly 6 constructors: Init, Send, Recv, Ret, Finish, Fail. So
  "six-constructor analysis" / "six-way" in the prose is accurate.
- `rstep` (and thesis Eq. procalc:proc-rules) has exactly 3 rules:
  rinit/rret/rcomm. "three reduction rules" / "three canonical reduction
  kinds" is accurate. `reduction_spec` constructors RSinit/RSret/RScomm
  package these three.
- `index_class`/`classify` constructors are `Inert` and `Disjoint`. Prose word
  "reducible" == `Disjoint`. A matched `Recv` index IS classified Disjoint
  (reducible).
- PITFALL: the soundness induction (`step_sound_list`) is over
  `active_senders`, NOT over all reducible (Disjoint) parties. `active_senders`
  filters on `is_sender` (true for Init/Ret/Send, false for Recv). A matched
  Recv party is reducible but excluded so each RScomm is counted once from the
  sender side. So "induction over the list of reducible parties" overcounts;
  the precise list is reducible *sender* parties.
- `rstep_disjoint` says: two reductions fireable from one config are
  (identical) OR (act on disjoint indices). Prose "identical or act on
  disjoint party indices" is exact.
- `step_sound` concludes `rsteps ps ps' tr` (closure incl. trace); prose
  shorthand $P \xrightarrow{*} Q$ drops the trace label, acceptable.
- Leakage-freeness (`du2002/spp_proof.v scalar_product_is_leakage_free`) is
  genuinely two-sided: H(x2|alice_traces)=H(x2) AND H(x1|bob_traces)=H(x1).
  §4 prose matches.

**Notation / macro discipline:** `shared-macros.sty` defines
`\qinit \qsend \qrecv \qret \qfinish` (used in smc-spp.tex, render as
`Send_A(x)` etc.). interpreter.tex instead writes inline `\mathsf{Init}` ...
`\mathsf{Fail}` in the grammar/reduction displays and prose. The surface forms
differ (prefix `Send j x. P` vs subscript `Send_j(x)`), so a blanket macro
swap would change the displayed syntax. Treat the inline `\mathsf{}`
constructor names as Minor un-macro'd notation, not a safe math-pillar
rewrite; a name-only macro is the right vehicle (flag to grounding/adjudicator).
