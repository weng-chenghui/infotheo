# Unit-carrier upgrade: `plain : finComNzRingType` → `finComUnitRingType`

Date: 2026-08-17
Status: spec under probe/audit (rocq-probe-first-spec). Not yet a plan.

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
   Existing proof bodies untouched (they use `w_u3_inj`).
4. dsdp_alice_trace_link.v:490 — same restatement; the positional pass-through
   at :613 (`pkey_of_dk w_v1 w_u1 w_u2 w_u3_inj` → `... w_u3_unit`) follows the
   closed lemmas' new premise.
5. Docs: symbolic_game/dsdp_game_derivation.v:22 comment ("requires
   plain : finComNzRingType") updated; paper footnotes
   sep10CPP2027/main.tex:1993 and :2307 rename the cited hypothesis.

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
| C1 | `'Z_n` elaborates as finComUnitRingType for abstract n | probe definition forces elaboration; mutation: same at a bare finComNzRingType variable fails | pending |
| C2 | `'F_p` elaborates as finComUnitRingType for abstract p | same probe | pending |
| C3 | `Let w_u3_inj := mulrI w_u3_unit` typechecks at the eta-expanded statement `injective (fun v => w_u3 * v)`, and `inj_eq w_u3_inj` closes a miniature of the secrecy.v:797 step | Qed'd miniature | pending |
| C4 | Unit form ⟺ injective form (endpoint content unchanged) | both directions Qed'd | pending |
| C5 | Ring-generic counting lemmas (`dsdp_fiber_card_ring`, conditional-uniformity chain) apply at a finComUnitRingType carrier via forgetful coercion | probe Requires dsdp_entropy, applies at 'Z_15 | pending |
| C6 | The 4-file edit set recompiles the whole dependency closure (HB rebuild, no shadowed instances, no hidden consumers) | full build of edited copy of the repo, zero errors | pending |
| C7 | Edit-set completeness: only he_types.v:38 and idealized_ahe.v:41 feed `plain` | grep enumeration above | grep: GO |
| C8 | No external consumer of the hypothesis or endpoint theorems | grep enumeration above | grep: GO |
| C9 | Docs blast radius enumerated (2 tex footnotes + 1 v comment + he_types header) | grep enumeration above | grep: GO |
| C10 | The unit structure selected at 'Z_ / 'F_ carriers is the canonical Zp/finField one (no competing instance) | instance print in probe | pending |
| C11 | Hypothesis set satisfiable after restatement (vacuity) | concrete unit witness at 'Z_15 compiled | pending |

## Soundness invariants

- No new `Axiom`, no assumed constant. The hypothesis remains a section
  premise; after the section closes it is an antecedent of every endpoint
  theorem. `Print Assumptions` on the rebuilt endpoints must list nothing new.
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
- Precedent for `\is a GRing.unit` hypotheses in dependencies: benaloh_ahe.v
  rand carrier `{unit 'Z_n}` already imports the unit machinery.

## Probes

All under `.scratch/`, never `Require`d from permanent files, never deleted:

- `.scratch/probe_unit_carrier_instances.v` — C1, C2, C10 (+ mutation checks
  as `Fail` commands).
- `.scratch/probe_unit_hyp_shape.v` — C3, C4, C11 miniatures (+ mutation
  checks).
- `.scratch/probe_unit_counting_transport.v` — C5.
- C6 runs as a build of an edited rsync copy of the repo (outside the working
  tree; the working tree and branch are not touched). The copy's diff is the
  plan's verbatim source. Decomposition probe: for a refactor spec the
  headline "the closure recompiles with the new premise" *is* the
  decomposition; C6 subsumes it, and the per-claim miniatures (C3-C5) cover
  the new proof shapes.

Copy location (kept): scratchpad `wt-unit-carrier/` per session scratch dir.

## Probe/audit outcomes

Pending. To be filled from actual probe compiles and audit reports only.

## Plan gate

Plan may be written only after C1-C11 are all GO/NO-GO-resolved and both
audits have returned explicit verdicts folded into this file. Fallback on any
NO-GO in C1/C2/C6: option 1 (existential-inverse hypothesis, no carrier
change), already probed GO in session scratch.
