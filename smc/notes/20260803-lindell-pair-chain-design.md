# pair_eqP: Lindell's joint comparison as one machine-checked chain

Date: 2026-08-03.  Workflow: /rocq-probe-first-spec.
Probes: `smc/security_models/.scratch/probe_pair_readoff.v` (round 1, DONE:
readoff diagonal + pair_eq_consistent, generic core at abstract carriers)
and its round-2 extension (pair_eq_simP remaining directions, in flight).
Companion spec: [[20260802-dealt-key-three-axes-design]] (the instances the
chain terminates in).  User directives (2026-08-03): complete the keystone
(option 2), launch a WHOLE-CHAIN audit agent when done, and add a thesis
diagram connecting every lemma end to end.

## Purpose

The logic chain from Lindell's Sec. 4.2 joint-comparison quote to the
entropy characterization currently has machine-checked ends and a
prose-argued middle.  This arc lands the middle as one general theorem in
entropy_link.v's section:

  pair_eq_simP (S) :
    (forall x, real_pair x = ideal_pair_of S x)
    <-> [/\ delivery_law_ok, consistent S, triangle S
          & output_independent]
  pair_eqP : the exists-S packaging of both sides.

After landing, the chain reads (every arrow a named Qed):

  Lindell joint equality (exists S, forall x, pair equality)
    <->  [pair_eqP]
  delivery_law_ok /\ exists S (consistent /\ triangle /\ output_indep)
    <->  [perfect_privacy_centropyP; needs injective input split]
  H(Xh,Yh | V, XA, YA) = H(Xh,Yh | XA, YA)
    <->  [perfect_privacy_cond_mutual_info0P]
  I((Xh,Yh); V | XA, YA) = 0

with side edges: triangle <-> def:smc:perfect-privacy
[triangle_perfect_privacyP]; both pairs concentrate on the read-off
diagonal [real_pair_readoff / ideal_pair_readoff, hypothesis readoff on
the real side, consistency on the ideal side]; Lindell equality already
forces consistency [pair_eq_consistent, with the single-input
pair_eq_consistent_at as the content-carrying form].

## Claim ledger

Round-1 rows (probed, Qed, axioms = boolp trio):

| # | identifier | claim |
|---|---|---|
| L1 | `real_pair` (Definition) | fdistmap (view_at, run) P_Omega at x |
| L2 | `ideal_pair_of` (Definition) | F x >>= fun y => tensor (S (proj_xa x, proj_ya y)) (fdist1 y) |
| L3 | `real_pair_readoff` | positive mass -> out_adv v = proj_ya y (real diagonal; uses readoff) |
| L4 | `ideal_pair_atE` | pointwise collapse: mass at (v,y) = F x y * S (...) v |
| L5 | `ideal_pair_readoff` | consistency -> ideal diagonal |
| L6 | `pair_eq_consistent_at` | pair equality AT ONE x -> read-off correct at every y the functionality reaches at x (no mu_full needed) |
| L7 | `pair_eq_consistent` | delivery + all-x pair equality -> consistent S |
| L8 | helpers `fdistmap_supp_pred`, `fdistbind_supp_pred`, `fdistmap_supp_cst`, `fdistmap_neq0_ex` | support-transport facts absent upstream |
| L9 | per-module instances (dealt_key_leak, biased_key, rerouted_key) of L3/L5; biased_key `ideal_pair_of_readoff` with the fully applied `consistent` premise | Qed |
| L10 | mutation: `sim_bad` off-diagonal witness + `not_readoff_without_consistency` (premise-free form is FALSE) | Qed falsity certificates |
| L11 | vacuity discipline: `rerouted_key exists_pair_eq` (premise non-empty there) vs `biased_key not_exists_pair_eq` (vacuous there) | Qed both sides |

Round-2 rows (probed, Qed; 51 targets, 49 boolp trio + 2 closed):

| # | identifier | status / claim |
|---|---|---|
| K1 | `pair_eq_delivery` (+ `snd_real_pairE`, `snd_ideal_pair_ofE`) | Qed; ideal side = fdistmap_bind + tensor_fdist1r + fdistbind1 |
| K2 | `pair_eq_triangle` (+ `fst_real_pairE`, `fst_ideal_pair_ofE`) | Qed; collapses to entropy_link.triangle's RHS via fdistbindA + fdist1bind |
| K3 | `pair_eq_output_independent` (+ `fdistmap_ideal_pair_ofE`, `pfwd1_view_yh_cond`) | Qed, FIVE lines via proba.v's `cinde_RV_factor` (D10) — no pointwise cpr computation |
| K4 | fiber-splitting keystone | RESOLVED BY EXISTING LEMMA: `entropy_link.triangle_cond_component` is verbatim the needed statement; reused, nothing new lands |
| K5 | `conditions_pair_eq` (+ `eq_split_y`, `pfwd1_yh_cond_deliveryE`, `pfwd1_view_yh_pairE`) | Qed; NEW hypothesis `split_y_inj : injective (fun y => (proj_ya y, proj_yh y))` confirmed needed, ONLY in this converse (D11); mu_full inherited from the section's standing hypotheses (D13) |
| K6 | `pair_eq_simP`, `pair_eqP` | Qed, statement texts recorded in the probe report; delivery sits outside the existential in pair_eqP |
| K7 | `split_counterexample.pair_eq_needs_split` | Qed FIRST ATTEMPT (D12): all four conditions + mu_full hold, split_y_inj fails, real pair (diagonal coin) <> ideal pair (product) at (true, false) |
| K8 | `rerouted_key_probe.real_ideal_pair_eq_via_conditions` / `conditions_via_real_ideal_pair_eq` | Qed both directions; derived and landed direct proofs agree on the statement |
| K9 | axioms | boolp trio everywhere (49) or closed under global context (2) |

Forward direction is hypothesis-free relative to the section (neither
split_y_inj nor mu_full); the converse needs mu_full (standing) +
split_y_inj (new, necessity machine-checked).  The three forward
contrapositives stay cited at the instances (biased_key delivery,
dealt_key_leak independence, masking_verdicts triangle — whose
hand-derivation at examples_f3.v:411 is exactly pair_eq_triangle's
contrapositive, now generalized).

## Landing layout (decided)

- Generic: `real_pair`, `ideal_pair_of`, L3-L7, K1-K6 into entropy_link.v's
  existing `Section entropy_link` (all variables and the `readoff` /
  `mu_full` hypotheses are already in scope), placed after
  `output_independent` and before the centropy block, so
  perfect_privacy_centropyP can sit next to pair_eqP in the file's
  narrative order.
- Helpers L8 into finstoch.v beside `fdistmap_bind` (same upstreaming
  precedent as 0112f732).
- Instances L9 INSIDE the three modules (the Let-bound view_at/run/out_adv
  are in scope there — probe D1; no Let promotion).  Module-local names
  may shadow the entropy_link ones inside the module; they are
  module-qualified outside.  Subject to the naming audit (probe D8).
- biased_key gains nothing from K5 (vacuous there, probe D6); its
  citation stays the refutation side.

## Soundness invariants

- No new axiom; boolp trio everywhere.
- Vacuity: K5's hypothesis set witnessed non-empty at rerouted_key
  (`exists_pair_eq`); K7 certifies split_y_inj is not droppable; L10
  certifies consistency is not droppable in L5.
- Honesty of the thesis sentence (probe round-1 caveats): the
  decomposition assumes nothing beyond WHAT THE DELIVERY LAW SUPPLIES
  (pair_eq_consistent routes through delivery_law_ok in the all-x form);
  the content-carrying form is single-input `_at`, which needs neither
  delivery nor mu_full.  The converse of consistency-from-pair fails at
  dealt_key_leak (consistent + triangle + delivery, yet
  real_ideal_pair_neq).
- Quantifier bridge: Lindell is per-input; the entropy end is drawn-input;
  full support + injective INPUT split convert (perfect_privacy_centropyP
  hypotheses).  pair_eqP itself is per-input on both sides and needs
  neither; K5 introduces the OUTPUT split injectivity instead.

## Whole-chain audit (user directive; after landing)

One dedicated agent, remit: walk the chain end to end and certify NO
prose gap remains —
1. every arrow of the Purpose diagram is a named, landed, Qed lemma;
   compile a client file that composes them: from
   `exists S, forall x, real_pair x = ideal_pair_of S x` derive the
   entropy equality and back, using only the named lemmas;
2. statement-match: the thesis quote (Lindell Sec. 4.2), the table's
   Joint column, the diagram labels, and the Rocq statements all speak of
   the same objects (crypto-vacuity discipline: English-statement,
   vacuity, variable-tracing, parallel-track tests);
3. hypothesis accounting: every hypothesis consumed anywhere on the chain
   (readoff, mu_full, input split, output split, delivery premises)
   appears in the thesis text or diagram caption — none silent;
4. GO/NO-GO with per-edge evidence.
Plus the standard naming audit on the new identifiers.

## Thesis touchpoints (after landing; working tree still carries the
uncommitted dealt-key rewrite — these edits stack on it)

- The convention-bridge passage (drafted 2026-08-03 in conversation,
  revised with the two probe caveats): replaces the read-off paragraph
  before def:smc:output-consistency; ends with the qualified sentence
  "Under delivery-law correctness, Lindell's single equality already
  forces output consistency ... the converse fails at the dealt-key
  example" with sidenote citing pair_eq_consistent / _at /
  real_ideal_pair_neq.
- THE CHAIN DIAGRAM (user directive): a displayed figure in
  sec:smc:it-characterization after prop:smc:entropy-characterization,
  four boxed statements connected by <-> arrows, each arrow labeled with
  the lemma name in \texttt (minted \coqin does not survive tikz nodes;
  the sidenote carries the \coqin forms), side edges for
  triangle_perfect_privacyP and the read-off diagonal, hypotheses on the
  arrows they enter (input split + full support on the centropy arrow,
  output split on the converse half of pair_eqP).  Caption states the
  quantifier bridge.
- Sidenote for prop:smc:entropy-characterization gains "the joint-pair
  form of the left side is pair_eqP".

## Plan (one atomic task per commit)

1. Round-2 probe (in flight, same agent as round 1).
2. Fold back deviations; re-commit this spec.
3. Naming + whole-chain soundness audits in parallel (audit prompts per
   the section above); fold back; re-commit.
4. Land: finstoch helpers commit; entropy_link generic section + module
   instances commit; golf (bodies only); axioms; gate UNBYPASSED.
5. Thesis: convention passage + chain diagram + sidenotes; build;
   commit decision deferred to the user (the dealt-key rewrite is still
   under review in the working tree).

## Deviations / findings folded back

Round 1 (2026-08-03): D1 Let-bound internals -> instances live inside
modules; D2 rerouted_key had no out_adv (probe supplies v.2); D3
biased_key never instantiated entropy_link.consistent — the probe builds
the fully applied form; D4 no premise weakening needed (biased coins have
full support); D5 generic pair_eq_consistent does not instantiate at
biased_key (delivery fails there) — single-input _at + module support
lemmas instead; D6 biased_key instance vacuous, machine-checked both ways
(load-bearing evidence at rerouted_key); D7 the all-x premise weakens to
single-input (_at is the content); D8 shadowing decision recorded in
Landing layout; D9 instantiation ergonomics (explicit readoff argument,
named implicits, @-qualification for R).

Round 2 (2026-08-03): D10 output-independence via `cinde_RV_factor`
(proba.v:2448), no cpr computation; D11 `split_y_inj` needed only in
the converse — declared as a late section Hypothesis so discharge
carries it only where used; D12 the necessity counterexample Qed'd on
the first attempt (unit/bool carrier, view = the delivered bit, real
pair diagonal vs ideal product); D13 mu_full inherited, not new — the
honest scope line is "the converse holds under entropy_link's existing
standing hypotheses plus split_y_inj"; D14 instances need `@m.f R` to
pin the implicit realType; D15 section Lets are opaque to /= — rewrite
/proj_ya /proj_yh before flattened intro patterns.  Probe-suggested
name `conditions_pair_eq` (spec had `pair_eq_of_conditions`) — naming
audit adjudicates.
