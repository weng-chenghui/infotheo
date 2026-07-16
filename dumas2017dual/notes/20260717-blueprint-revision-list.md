# Blueprint revision list

Date: 2026-07-17
Consolidates: the three content.tex audits (coverage / accuracy / explanatory),
the structure audit of the security-story design, the epsilon_cpa fix, and the
Option A decision.
Related: 20260715-blueprint-v2-design.md, 20260716-option-a-feasibility-probes.md

Legend: [DONE] resolved in code this session · [FIX] mechanical, low-judgment ·
[CORRECT] a false statement to fix · [WRITE] new prose/node · [DECIDE] open
decision · (v) personally verified this session · (a) from an audit, not
re-verified.

The final blueprint = security-story Parts (new, threat-model spine) + a final
Auto-derivation Part (repurposed content.tex, scoped to the ciphertext channel).
Bucket A below is the Auto-derivation Part; Bucket B is the security-story Parts;
Bucket C is tooling.

---

## 0. Settled — context, do not re-litigate

- [DONE] (v) `epsilon_cpa : AHEncType -> R`. Every blueprint bound of shape
  `2*epsilon_cpa` is now stale and must show the scheme index (Bucket A1).
- [DONE] (v) Option A declined. Auto-derivation is scoped to the ciphertext
  channel; output secrecy is the Infotheo fiber argument over a hand-supplied
  scalar-product trace. Resolves the G1 FATAL. (Bucket A3.)

---

## Bucket A — the Auto-derivation Part (repurpose content.tex + it_bound_bridge.tex)

Baseline: 23 of 36 content.tex nodes are accurate as-is (a). content.tex has 0
dangling refs; the 5 dangling refs are all in it_bound_bridge.tex.

### A1 — epsilon_cpa staleness [FIX] (v, stale from the epsilon_cpa commit)
34 `\epscpa` loci split into 5 scheme-varying (must show the argument) and 29
scheme-fixed (bare is fine once one sentence declares ε is per-scheme).
- macros/common.tex: keep `\epscpa` (= ε of DSDP's fixed scheme), add
  `\epscpaof{#1}`.
- `def:indcpa_assumption` (F1, FATAL): add the `forall E` quantifier and
  `epsilon_cpa AHE`. Today it states the vacuous pre-fix axiom.
- `thm:generic_secrecy` (M3): `epsilon_cpa (exp_enc_scheme P)` — indexed by the
  record field.
- `thm:advantage_le`, `lem:advantage_hop`, `lem:advantage_sum_ladder_le` (M5):
  `epsilon_cpa AHE` (section variable).
- figure boxes + caption (A1), intro "full bound 1/m + 2 epsilon_cpa": add the
  index / a declaring sentence.

### A2 — dangling \rocq refs [FIX] (a) — 5, all in it_bound_bridge.tex
- `S_output_cell` -> `Sout_cell`
- `id_s_get` -> `id_Sout_get`
- `dsdp_guess_fiber.Pr_fst_agree_locs` -> `dsdp_convert.Pr_fst_agree_locs`
- `dsdp_guess_fiber.Pr_fst_closed` -> `dsdp_convert.Pr_fst_closed`
- `dsdp_guess_fiber.guess_advantage_le` (does not exist) ->
  `dsdp_main.dsdp_alice_guess_advantage_le`

### A3 — scope the output channel to Infotheo [CORRECT/WRITE] (v, the decision)
- Stop claiming the output game is derived. `def:games_leak_s` body ("denoted
  from the output-exposing derivation") is false; rewrite.
- Present output secrecy as the Infotheo fiber-counting argument (a different
  tool): hand-supplied scalar-product trace `u1*v1+u2*v2+u3*v3`, the 1/m bound is
  information-theoretic (`dsdp_alice_guess_ideal_le`, IND-CPA-free).
- Drop the line-count claim (F4, backwards: derivation is ~9% larger). Replace
  with the reuse argument: the 1078-line back end is protocol-generic; the
  per-protocol cost is the symbolic instance + a ~20-line record.

### A4 — false statements to correct [CORRECT] (v)
- `def:lower_obs_output` (F2, FATAL): "game_code is not extended" — false,
  `GC_put_output` is a dedicated 6th constructor.
- `def:embedding` (M4): grammar lists 5 constructors, type has 6 (add
  `GC_put_output`).
- `lem:guess_advantage_le` (M2): conflates an equality (`guess_advantage_eq`)
  with the `<= 2*eps` bound (a different lemma); also the dangling ref in A2.
- 2 Part II headline nodes (M6): drop all hypotheses (`Hinj`, `card_renc_neq`,
  the `fseparate` side-conditions). Add them.

### A5 — status honesty [FIX] (v)
- Legend "Part II is blue / under construction" (F3, FATAL): every Part II node
  is green. Fix, and remove the unused blue-dashed legend entry.
- Admitted `interchange_psum` (M7): ~19 nodes (7 in content.tex, ~12 in
  it_bound_bridge) are proved MODULO an upstream `Admitted` lemma. Add a third
  status marker (e.g. green-hollow / "modulo upstream admit") and qualify the
  "Part I green throughout" / "every node machine-checked" claims. The
  "one cryptographic assumption" claim survives (the admit is not cryptographic).

### A6 — explanatory writing [WRITE] (a, highest leverage per word)
- 7 chapter-opening paragraphs (F3-explanatory): every content.tex chapter jumps
  straight from `\chapter` to `\begin{definition}`. This is the top edit.
- The real faithfulness anchor (F2-explanatory): `palice_sym = @palice
  Symbolic_DSDP_Interface ...` — the same program term at a different instance.
  The document never states its own best argument. Add it.
- Undefined-term nodes/glosses: `\AdvE` (used in Part I, defined only in Part II),
  `m`, a marshalling node before Chapter 4, the package/oracle structure of
  `denote_game`, the `hop_equiv` round-trip, `collect_samples` first-appearance
  order, `resolve_term`'s `idx`/Γ. (M8-M14.)
- Style table (~18 node bodies): move meta/status/advocacy sentences to
  surrounding prose or delete, per the statement-comment rule.

### A7 — new nodes for coverage [WRITE] (a)
108 undocumented declarations across the four derivation modules; ~35
load-bearing, clustering to ~6-8 nodes:
- The seam's left half (G2, FATAL for the argument): concrete instance +
  preserved proofs (2 nodes) AND add `core/dsdp_interface.v`, `core/dsdp_pismc.v`
  to MODULES.
- Denotation environment (11 decls -> 1 node); game state/oracle interface (9 ->
  1); the real/zero oracles (4 -> 1); fold `symbolic_Recv_*`/`ek_sym` into
  `def:symbolic_interface`.
- `dsdp_faithful` (F2/G-coverage): legacy bridge to the unused `gc_dsdp` fixture;
  its body "the fixture is therefore derived" is backwards. Delete the node (and
  consider deleting the code), OR demote to an explicit regression-test caveat.

### A8 — restructure [DECIDE]
- Move `ch:deriving_output` into the Auto-derivation Part (0 broken edges, 0
  macro migration; fixes 2 dangling refs en route). BUT reconcile with A3: given
  the output channel is now presented as Infotheo, decide how much of
  `ch:deriving_output` (the S-exposing derivation) survives vs becomes "the
  output trace is supplied; here is the IT argument".

---

## Bucket B — the security-story Parts (new, threat-model spine)

### B1 — structure [DECIDE, mostly settled]
- D1 threat-model spine: SURVIVES. 18-chapter TOC (5-Part shape: Foundations /
  Corrupted Alice / Corrupted relay, with the Auto-derivation Part last).
- D4 simulation scope + one blue worst-case node: SURVIVES.

### B2 — corrections the security chapters must carry [CORRECT] (v)
- Part III is NOT "malicious Alice": `U2=1,U3=0` are legal semi-honest inputs,
  and exactly the case `Hinj` excludes from Part I. Re-place as Part I's
  tightness witness (right after the 1/m chapter), retitle.
- `dsdp_centropy_uniform` conditions on `[%V1,U1,U2,U3,S]`, not Alice's real view
  (which also has `Dk_a,R2,R3` + 3 ciphertexts). The source comment at
  `dsdp_main.v:180` already misstates this; fix comment and blueprint.
- Correctness is proved and in no chapter: state `dsdp_is_correct` in Part 0
  (context, one node; note it is the Idealized instance).
- `card_renc_neq` is an interpreter artifact, not a security condition; tag it as
  such. `u3 in (0,min(p,q))` is a magnitude restriction (~sqrt(m) of m weights);
  state it. `predictor_locs_disj` is security-critical, not hygiene.

### B3 — tooling for the security chapters [DECIDE]
- The chain-walker (D3) and generated-hypothesis-block (D2) ideas were REFUTED
  (.glob misses autorewrite/hint/canonical deps; push_val on-chain; scope
  undefinable). Re-decide: keep the regex checker (fix its bugs, Bucket C) with a
  hand-curated node set, or a different mechanism. Node count under the settled
  library cut (dumas2017dual + smc + homomorphic_encryption in-tree, rest
  library) is ~506 before plumbing rules — larger than the ~150 first estimated.
- Hypothesis blocks: use `About <thm>` off the `.vo` (100% recall), not the glob
  (48% recall, 0% on two headlines).

---

## Bucket C — the coverage checker (check_coverage.py) [DECIDE/FIX]

- (v) Multi-name `\rocq{a, b}` regex bug: the character class excludes `,`, so
  22 multi-name nodes (60 of 98 names) are invisible; 51 exclude entries are
  false waivers, and 5 dangling refs were hidden by it.
- (v) `DECL_KW` omits `Parameter`, so `epsilon_cpa` is invisible to the ratchet.
- (v) The checker is currently RED (5 dsdp_main uncovered + the phantom `exact`
  from ssreflect tactic brackets). Nothing has been enforcing the ratchet.
- (v) Two stale waivers (`relay_privacy_n` gone; `guess_sdistr_success_real`
  alive but the `dsdp_main:` entry stale).
- Decision needed: fix the regex checker in place (multi-name, `Parameter`, the
  constructor false-positive) and keep the exclude-list model, or replace it.
  Given B3, do NOT pursue the glob chain-walker.

---

## Suggested execution order

1. **Safe mechanical batch (A1, A2, A5):** epsilon_cpa staleness, dangling refs,
   status flags. Pure accuracy, no design judgment. Do first.
2. **False-statement corrections (A3 body fix, A4, B2):** verified, bounded.
3. **Checker fix (C):** so the ratchet actually holds before new nodes land.
4. **Structural decisions (A8, B1, B3):** decide before writing.
5. **New writing (A6, A7):** chapter prose + clustering nodes. The bulk, and the
   part no tool checks. Last, once structure is fixed.

## Non-goals / already done
No epsilon_cpa code change (done). No Option A / route 1 build (declined). No
blueprint_v1 move until the checker (C) passes on the current document, so the
ratchet is never off during the migration.
