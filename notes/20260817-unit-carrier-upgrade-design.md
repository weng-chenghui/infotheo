# Unit-carrier upgrade: `plain : finComNzRingType` → `finComUnitRingType`

Date: 2026-08-17
Status: PROBED AND AUDITED (all ledger rows GO; soundness GO, naming GO).
Plan: notes/20260817-unit-carrier-upgrade-plan.md

## Decision context

The corrupted-Alice sections assume
`Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v)`
(dsdp_alice_fdist_secrecy.v:209, dsdp_alice_trace_link.v:490). The author wants
the reader-facing form `w_u3 \is a GRing.unit`, which is not stateable today
because the AHE carrier `plain : finComNzRingType` (he_types.v:38) carries no
unit-ring structure, and MathComp does not join finite+ring into unit-ring at
the abstract-structure level (the `FinRing.isNzRing` factory in finalg.v
equips only concrete instances built through it).

Three options were discussed in session on 2026-08-17; the user chose
**option 2**: upgrade the carrier field to `finComUnitRingType` and restate the
hypothesis as unit membership. (Option 1, the `exists v, w_u3 * v = 1` form on
the unchanged carrier, remains the documented fallback if a probe or audit
returns NO-GO.)

## Carrier pin

The weakest structure the spec promises: `plain : finComUnitRingType`.
Concrete carriers that must instantiate it (all four `MkHE` sites):

| Site | plain carrier | Why it should carry finComUnitRingType |
|---|---|---|
| benaloh1994/benaloh_ahe.v:72 | `'Z_r` (r : nat variable) | Zp canonical instances, unconditional (`'Z_r = 'I_(r.-2.+2)`) |
| paillier1999/paillier_ahe.v:48 | `'Z_n` (n : nat variable) | same |
| idealized/idealized_ahe.v:49 (msgT variable at :41) | abstract; used at `'F_2` (idealized_indcpa.v:40) | finFieldType ⟹ finComUnitRingType |
| dsdp core: `Idealized_HETypes msg`, `msg := 'F_m` (dsdp_correctness.v:62, dsdp_pismc.v:433,538,691) | `'F_m` (m : nat variable) | 'F_m is canonically a finFieldType for every m (via pdiv) |

## Edit set (complete, by grep evidence)

1. he_types.v:38 — field type, one word. Header comment at :12 follows.
2. idealized/idealized_ahe.v:41 — `Variable msgT : finComNzRingType` →
   `finComUnitRingType` (only variable that flows into the `plain` field).
3. dsdp_alice_fdist_secrecy.v:209 —
   `Hypothesis w_u3_unit : w_u3 \is a GRing.unit.` plus
   `Let w_u3_inj : injective (fun v : plain AHE => w_u3 * v) := mulrI w_u3_unit.`
   Existing proof bodies untouched (they use `w_u3_inj`). A `Naming:` comment
   goes above the Hypothesis per the file's 16-instance convention:
   `(* Naming: [w_u3_unit] reads "w_u3 is a unit" (cf. mathcomp
   [row_ebase_unit]); the derived [w_u3_inj] keeps the former hypothesis
   name so proof bodies are unchanged. *)`
   The lambda annotation `v : plain AHE` stays: it is the probed-verbatim C3
   form (the ascription itself is load-bearing; the audit notes the
   annotation could be dropped, a follow-up nit at most).
4. dsdp_alice_trace_link.v:490 — Hypothesis replaced by the unit form ONLY,
   no derived Let: the naming audit found the Let is dead in this file (its
   sole injectivity uses are val_inj/can_inj; build-verified removable). The
   positional pass-through at :613 (`pkey_of_dk w_v1 w_u1 w_u2 w_u3_inj` →
   `... w_u3_unit`) follows the closed lemmas' new premise. The closed
   Arguments line is otherwise identical (audit-verified), so this is a pure
   binder rename with no arity risk.
5. Docs (expanded per soundness audit findings 4-5):
   .v comments: symbolic_game/dsdp_game_derivation.v:22 ("requires
   plain : finComNzRingType" -> finComUnitRingType) and
   counting/dsdp_entropy.v:421 (comment claims the _ring section is
   parametric in finComUnitRingType; the code at :437 says finComNzRingType
   and is RIGHT, so the comment is corrected to finComNzRingType).
   Paper (sep10CPP2027/main.tex), six loci: prose :1991-1992 and :2304-2305
   ("multiplication by the third weight is injective" -> the third weight is
   invertible, matching the paper's own :1358-1363 wording); summaries :2214
   and :2354 ("the injectivity hypothesis" -> the invertibility hypothesis);
   footnotes :1993 and :2307 (\coqin{w_u3_inj} -> \coqin{w_u3_unit});
   HETypes prose :830-831 and minted listing :843 (finComNzRingType ->
   finComUnitRingType, prose gloss adjusted).
   Thesis (thesis/chapters/ahe-hierarchy.tex), two loci: record listing :58
   and prose :65 (same carrier correction).

Non-edits, by evidence:
- homomorphic_encryption.v:132 (`Variable msg : finComNzRingType`,
  Party_Enc_Types) does not feed the `plain` field; richer instantiations
  coerce down. Recompiles, no text change.
- counting/dsdp_entropy.v:437 ring-generic section stays at
  `finComNzRingType`; consumers reach it by forgetful coercion (probed, C5).
- smc/security_models/spp_bridge.v:61 is the separate SPP development, no
  HETypes dependency.
- No file outside the two fdist_hopping files names `w_u3_inj` or applies the
  endpoint theorems (grep over non-scratch, non-legacy .v: empty).
- Thesis .tex: no `w_u3_inj` occurrences (grep empty); only the CPP paper cites it.

## Claim ledger

| # | Claim | Passing evidence | Status |
|---|---|---|---|
| C1 | `'Z_n` elaborates as finComUnitRingType for abstract n | probe definition forces elaboration; mutation: same at a bare finComNzRingType variable fails | GO (probe_unit_carrier_instances.v, exit 0; mutation fails with unit-predicate-not-stateable error) |
| C2 | `'F_p` elaborates as finComUnitRingType for abstract p | same probe | GO (same probe; same mutation) |
| C3 | `Let w_u3_inj := mulrI w_u3_unit` typechecks at the eta-expanded statement `injective (fun v => w_u3 * v)`, and `inj_eq w_u3_inj` closes a miniature of the secrecy.v:797 step | Qed'd miniature | GO: `Let w_u3_inj : injective (fun v : plain AHE => w_u3 * v) := mulrI w_u3_unit.` compiles VERBATIM (mulrI has `Arguments [R x] _ [x1 x2] _`); 797-step miniature Qed; premise-drop mutation fails |
| C4 | Unit form ⟺ injective form (endpoint content unchanged) | both directions Qed'd | GO (probe_unit_hyp_shape.v: forward = the Let, converse `unit_of_inj` Qed via inj_card_bij + unitrPr) |
| C5 | Ring-generic counting lemmas (`dsdp_fiber_card_ring`, conditional-uniformity chain) apply at a finComUnitRingType carrier via forgetful coercion | probe Requires dsdp_entropy, applies at 'Z_15 | GO (probe_unit_counting_transport.v; strengthened with abstract-carrier variant `fiber_card_at_abstract_carrier` exercising the forgetful coercion — the load-bearing case) |
| C6 | The 4-file edit set recompiles the whole dependency closure (HB rebuild, no shadowed instances, no hidden consumers) | full build of edited copy of the repo, zero errors | GO (closure build of edited copy: 28 files rebuilt, exit 0, one predicted pass-through fix at trace_link:613, endpoint axiom sets byte-identical to baseline) |
| C7 | Edit-set completeness: only he_types.v:38 and idealized_ahe.v:41 feed `plain` | grep enumeration above | grep: GO |
| C8 | No external consumer of the hypothesis or endpoint theorems | grep enumeration above | grep: GO |
| C9 | Docs blast radius enumerated | initially 2 tex footnotes + 1 v comment; soundness audit finding 4-5 expanded it to 6 paper loci + 2 thesis loci + 2 .v comments + he_types header | GO after expansion (audit-verified enumeration) |
| C10 | The unit structure selected at 'Z_ / 'F_ carriers is the canonical Zp/finField one (no competing instance) | instance print in probe | GO with caveat: 'Z_ side pinned by computation (2 unit, 3 non-unit, inverse arithmetic); 'F_ side by elaboration + unitr1 only (sound: 'F_p reuses the Zp instance) |
| C11 | Hypothesis set satisfiable after restatement (vacuity) | concrete unit witness at 'Z_15 compiled | GO (vacuity_witness elaborates at 'Z_15, u3=2) |

## Soundness invariants

- No new `Axiom`, no assumed constant. The hypothesis remains a section
  premise; after the section closes it is an antecedent of every endpoint
  theorem. Verified: `Print Assumptions` on both rebuilt endpoints is
  byte-identical to baseline (three standard boolp classical axioms).
- Statement equivalence, not strengthening: C4 shows the new premise is
  interderivable with the old on the (finite, commutative) carrier, so the
  endpoint theorems' mathematical content is unchanged. The *class of carriers*
  shrinks (finComNzRingType instances that are not unit rings lose access), but
  every carrier the development instantiates is a unit ring (C1/C2), and the
  corrupted-Alice bounds were only ever claimed at such carriers.
- Scope unchanged: average-case over uniform honest inputs, single-query,
  fixed-key, semi-honest; the vacuous-regime paragraph in
  dsdp_alice_fdist_secrecy.v:180-189 is untouched.
- Vacuity: C11 gives a concrete satisfying instance of the full hypothesis row.

## Naming

- `w_u3_unit` follows the file's `w_`-prefixed protocol-parameter convention
  (w_v1, w_u1, w_u2, w_u3) and MathComp's `_unit` suffix reading
  ("is a unit"); the derived `Let w_u3_inj` keeps the old name so proof bodies
  and the in-file citation pattern survive verbatim.
- Precedent in dependencies (softened per naming audit): benaloh_ahe.v's rand
  carrier `{unit 'Z_n}` is the unit-GROUP subtype, not the `\is a GRing.unit`
  predicate; what it evidences is that the unit machinery is already loaded
  and idiomatic in this development, not a hypothesis-form precedent.
- MathComp precedent for the name (audit-verified): `_unit`-suffixed
  statements meaning "is a unit" (`row_ebase_unit`, `col_ebase_unit`,
  `character_table_unit`, `spectral_unit`); hypothesis shape per the
  subject_property convention (`n_gt0`, `x_inj`). Rejected: `w_u3_is_unit`
  (no `is_` hypothesis precedent), `Uw_u3` (the U-prefix only ever attaches
  to short subjects).

## Probes

All under `.scratch/`, never `Require`d from permanent files, never deleted:

- `.scratch/probe_unit_carrier_instances.v` — C1, C2, C10 (+ mutation checks
  as `Fail` commands).
- `.scratch/probe_unit_hyp_shape.v` — C3, C4, C11 miniatures (+ mutation
  checks).
- `.scratch/probe_unit_counting_transport.v` — C5.
- C6 runs as a build of an edited rsync copy of the repo (outside the working
  tree; the working tree and branch are not touched). The copy's diff is the
  plan's verbatim source FOR THE CODE EDITS (items 1-4); item 5's docs edits
  are applied at plan execution, not in the copy (soundness finding 9). The
  plan deviates from the copy in two audit-driven ways, both build-verified:
  trace_link.v drops the dead Let, and secrecy.v gains a Naming: comment. Decomposition probe: for a refactor spec the
  headline "the closure recompiles with the new premise" *is* the
  decomposition; C6 subsumes it, and the per-claim miniatures (C3-C5) cover
  the new proof shapes.

Copy location (kept): scratchpad `wt-unit-carrier/` per session scratch dir.

## Probe/audit outcomes

### Probe run 1 (rocq-prover, 2026-08-17): C1-C5, C10, C11 all GO

- All three probe files compiled exit 0 as drafted; every Fail mutation
  genuinely fails; Print Assumptions on every named endpoint returns
  "Closed under the global context" (zero axioms, including through the
  dsdp_entropy import).
- C3 exact compiled form for the plan (do NOT substitute can_inj (mulKr _),
  which also works but is longer):
  `Let w_u3_inj : injective (fun v : plain AHE => w_u3 * v) := mulrI w_u3_unit.`
- C5 was under-tested as drafted (concrete 'Z_15 resolves structure straight
  from the ordinal); the prover added `fiber_card_at_abstract_carrier` at
  `Variable R : finComUnitRingType`, which exercises the forgetful coercion
  the upgraded secrecy file will rely on. Same tactic closes it.
- New finding folded into edit set item 5: dsdp_entropy.v lines 416-431
  comment claims the _ring section is "parametric in [R : finComUnitRingType]"
  while line 437 declares `Variable R : finComNzRingType`. The declaration is
  correct and stays; the comment is wrong and joins the docs edits.
- Toolchain note for the plan: `eval $(opam env)` selects the repo-local
  switch (Rocq 9.0.0, mathcomp 2.5.0) only when CWD is inside the repo;
  build commands must cd first.

### Probe run 2 (C6 closure build, 2026-08-17): GO

- Edited rsync copy at session scratchpad `wt-unit-carrier/` (kept; the
  plan's verbatim source). Build exit 0; rebuilt set = exactly the 28-file
  closure of he_types.v (nothing under smc/ or probability/).
- The `Let := mulrI w_u3_unit` form compiled first-try in BOTH permanent
  files, matching probe run 1.
- Exactly one pass-through fix, at the site the spec predicted
  (trace_link.v:613): `pkey_of_dk w_v1 w_u1 w_u2 w_u3_inj` ->
  `... w_u3_unit`. No other site flagged in the whole closure.
- Print Assumptions on both endpoint theorems in the copy: the three
  standard boolp classical axioms (propositional_extensionality,
  functional_extensionality_dep, constructive_indefinite_description),
  verified byte-identical to the untouched baseline repo. Nothing new.
- grep Admitted/Axiom/Abort over both edited files: zero.
- Environment: building from the copy requires
  `eval $(opam env --switch=/Users/cheng-huiweng/Projects/coq --set-switch)`;
  a bare `opam env` there selects the wrong switch and fails at he_types.v:27.

### Naming audit (mathcomp-style-auditor, 2026-08-17): GO

- `w_u3_unit` confirmed idiomatic; alternatives rejected with precedent.
- The `Let ... := term` idiom confirmed (quotient.v:638-640, action.v:1373);
  a Fact/Lemma would wrongly export a global `w_u3_inj`.
- Verified: the Let does NOT leak into closed statements; the closed
  Arguments line changes only the binder name; `w_u3_unit` collides with
  nothing (.v and .tex grep clean).
- Finding folded: trace_link.v's Let is dead — dropped from edit set item 4.
- Finding folded: Naming: comment added to edit set item 3.
- Finding folded: benaloh precedent wording softened (Naming section).
- Pre-existing, out of scope, recorded only: 9 `boolp.`-qualified names,
  Variable/Hypothesis interleave at :205-207, header Scope paragraph could
  mention the new premise (optional docs nicety), asymmetric `[w_u3]`
  implicit (unchanged by this edit).

### Soundness audit (general-purpose, compile-capable, 2026-08-17): GO

- Equivalence verified BEYOND the probes: the old-form endpoint statements
  were re-derived from the new endpoint theorems in the copy (exit 0, boolp
  axioms only), so the closed theorems are interderivable, not merely the
  hypotheses.
- Closed statements otherwise unchanged: About-diff shows only carrier sort,
  antecedent, and binder name; [w_u3] implicit status and argument order
  identical; the Let never leaks.
- Axiom sets byte-identical to baseline, independently reproduced.
- Carrier shrinkage harmless: all built consumers inside the 28-file
  closure; non-built consumers (declarative.v commented block, abstract
  probe/scripts files, legacy/) unaffected.
- MAJOR findings 4-5 (docs under-enumeration) folded into edit-set item 5
  and C9. MINOR finding 9 (verbatim-source wording) folded into Probes.
- Vacuity witness confirmed real and non-degenerate.

## Plan gate

Plan may be written only after C1-C11 are all GO/NO-GO-resolved and both
audits have returned explicit verdicts folded into this file. Fallback on any
NO-GO in C1/C2/C6: option 1 (existential-inverse hypothesis, no carrier
change), already probed GO in session scratch.
