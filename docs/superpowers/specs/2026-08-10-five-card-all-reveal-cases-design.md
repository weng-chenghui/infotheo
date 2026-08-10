# Five-card leakage: every reveal case (design)

Date: 2026-08-10.
Target file: `pgg-smc/instances/denboer1989/five_card_leakage.v`.
Paper target: `pgg-smc/paper-wadt2026/main.tex` (three loci, listed below).
Status: probe phase. This spec follows `/rocq-probe-first-spec`: the claim
ledger below is checked by compiled probes and two adversarial audits before
any implementation plan is written.

## Goal

One theorem quantifying the mutual information between the den Boer secret
and the revealed card colours for every subset of the five row positions,
so the wadt2026 paper can claim "every reveal pattern" instead of
"six reveal patterns".

## Decisions (from the brainstorm, in order taken)

1. Scope: master theorem over every subset `A : {set 'I_5}`, including
   `set0`, so the statement carries no side condition.
2. Statement form: set-indexed, with a closed-form function
   `fc_leak : {set 'I_5} -> R`.
3. Paper edits are part of this package, strictly gated on the compiled
   `.vo`.
4. Architecture: rotation symmetry plus seven anchors. Brute-force
   enumeration in the existing `cardV`/`cardJ` style remains a per-branch
   fallback only.
5. Probing follows `/rocq-probe-first-spec` (user directive this session):
   compiled probes and two adversarial audits before the plan.
6. Refinement recorded during spec writing: the coordinate-permutation
   fact is packaged as invariance of mutual information under an injective
   relabeling `g` of the view alphabet, applied with a concrete `g` per
   wrap-around branch. No `'S_k` and no `perm` import.

## Ground truth (exact 20-outcome enumeration)

Script: `.claude/probes/2026-08-10-five-card-all-reveals/five_card_leak_enum.py`, mirroring
`fc_encode`, `fc_negate`, `fc_arrange`, `fc_shuffle k = rot k` from
`five_card_program.v`. Results:

| orbit representative | orbit size | I(Secret; View) |
|---|---|---|
| {0} | 5 | 0 |
| {0,1} adjacent | 5 | 27/10 - (1/4) log 5 - (7/10) log 7 |
| {0,2} distance-2 | 5 | 5/2 - (3/20) log 3 - (1/2) log 5 - (7/20) log 7 |
| {0,1,2} consecutive | 5 | 6/5 - (9/20) log 3 |
| {0,1,3} gapped | 5 | 6/5 - (9/20) log 3 (same value) |
| {0,1,2,3} | 5 | 2 - (3/4) log 3 = H(Secret) |
| {0,1,2,3,4} | 1 | 2 - (3/4) log 3 |

Every one of the 31 nonempty subsets was computed individually; each equals
its orbit representative exactly (max deviation 0.0), confirming rotation
equivariance numerically before any proof.

Fibre tables for the missing {0,1,3} anchor (view value, view count nv,
joint count with secret true nt, with secret false nf):

| view | nv | nt | nf |
|---|---|---|---|
| FFF | 0 | 0 | 0 |
| FFT | 1 | 1 | 0 |
| FTF | 3 | 0 | 3 |
| FTT | 4 | 1 | 3 |
| TFF | 3 | 0 | 3 |
| TFT | 4 | 1 | 3 |
| TTF | 2 | 2 | 0 |
| TTT | 3 | 0 | 3 |

Only two fibres are non-deterministic, both nv = 4 with (nt, nf) = (1, 3),
exactly as in `leak_k3`; hence the same closed form, and the proof needs
only the existing `binent_1_4`, `binent_det0`, `binent_det1` helpers.

## Carrier (pinned)

All probes and all new results elaborate inside the existing section
context of `five_card_leakage.v`:

```coq
Variable R : realType.
Definition Omega : finType := [the finType of (bool * bool * 'I_5)%type].
Definition P : R.-fdist Omega := fdist_uniform card_Omega20.
Definition Secret : {RV P -> bool} := fun w => let: (a, b, _) := w in a && b.
```

with `Local Open Scope ring_scope` and the fdist/proba/entropy scopes open.
This is the weakest structure the spec supports; no probe may substitute a
more convenient carrier.

## Formal core

New definitions (statement sketches; exact forms fixed by the object probe):

```coq
(* successor position mod 5, avoiding a zmodp import *)
Definition succ5 (i : 'I_5) : 'I_5 := inord (i.+1 %% 5).

(* position-tuple view: component i reads the card at position tnth t i *)
Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

(* set view: positions of A in ascending enumeration order *)
Definition ViewS (A : {set 'I_5}) : {RV P -> #|A|.-tuple bool} :=
  ViewT (enum-as-tuple of A).   (* enum_tuple if available, else Tuple + cardE cast *)

(* the two elements of a 2-set at cyclic distance 1 *)
Definition fc_adjacent (A : {set 'I_5}) : bool :=
  [exists i : 'I_5, A == [set i; succ5 i]].

Definition fc_leak (A : {set 'I_5}) : R :=
  match #|A| with
  | 0 => 0
  | 1 => 0
  | 2 => if fc_adjacent A
         then 27%:R/10%:R - 4%:R^-1 * log 5%:R - (7%:R/10%:R) * log 7%:R
         else 5%:R/2%:R - (3%:R/20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
              - (7%:R/20%:R) * log 7%:R
  | 3 => 6%:R/5%:R - (9%:R/20%:R) * log 3%:R
  | _ => 2%:R - (3%:R/4%:R) * log 3%:R
  end.
```

New results:

1. `leak_k3_gap` : `` `I( Secret ; ViewA [:: 0; 1; 3]%N ) = 6%:R/5%:R - (9%:R/20%:R) * log 3%:R ``.
   Direct reuse of the `leak_k3` template with the fibre tables above.
2. `mutual_info_view_inj` (find in infotheo or derive) : for finite types
   `A B`, `Y : {RV P -> A}`, `g : A -> B` injective,
   `` `I( Secret ; g `o Y ) = `I( Secret ; Y ) ``.
3. `leak_rot1` : `` `I( Secret ; ViewT (map_tuple succ5 t) ) = `I( Secret ; ViewT t ) ``.
   Via the cut-shift bijection `phi (a, b, k) = (a, b, k + 1 mod 5)`:
   `fdistmap phi P = P`, `Secret \o phi = Secret`, and
   `ViewT (map_tuple succ5 t) = (ViewT t) \o phi` componentwise, hence equal
   joint distributions and equal mutual information.
4. `leak_view_nil` : `` `I( Secret ; ViewT [tuple] ) = 0 `` (constant view).
5. Anchor bridges: for each of the seven concrete patterns, the `ViewT`
   form of the anchor equals the proven `ViewA` form (same definitional
   value type at concrete sizes; `boolp.funext` + `val_inj`).
6. Master theorem `leak_view_set` :
   `` forall A : {set 'I_5}, `I( Secret ; ViewS A ) = fc_leak A ``.
   Proof: case split on the five membership bits of `A` (32 branches);
   each branch identifies `A` with a set literal, computes its ascending
   position tuple, chains `leak_rot1` and `mutual_info_view_inj` (with a
   concrete relabeling per wrap-around branch) to an anchor, and computes
   `fc_leak`.

All new results live in `five_card_leakage.v`, same section, `Qed` only,
boolp classical axioms only. The seven existing lemmas are not modified.

## Claim ledger

Pass criteria are machine checks; a row passes only when its probe compiles
(and, where stated, is mutation-checked). Probe files listed in the probe
plan below.

| # | Claim | What counts as passing | Status |
|---|---|---|---|
| L1 | The file's existing MI toolkit (`mutual_info_RVE`, `centropy_RVE'`, `centropy1_RV`, `dist_of_RV`, `fdistmap`) elaborates at the pinned carrier for the new statements | object probe uses each in a compiled statement at the carrier | probe |
| L2 | Injective-relabeling invariance exists in infotheo or is derivable | either a named infotheo lemma found via `rocq_query`/Search, or a Qed'd miniature of `H(S \| g o Y) = H(S \| Y)`, g injective, at the carrier | probe |
| L3 | A canonical `#\|A\|`-tuple enumerating `A : {set 'I_5}` exists (`enum_tuple` or `Tuple` + `cardE` cast) and reduces to a literal tuple on concrete sets | `ViewS` typechecks; `val (enum-as-tuple [set literal])` computes to the ascending literal seq | probe |
| L4 | `ViewT` as an mktuple over `tnth` typechecks at the carrier | Definition compiles in-section | probe |
| L5 | `fc_adjacent` computes on concrete sets | `fc_adjacent [set 0; 1] = true` and `fc_adjacent [set 0; 2] = false` by compute, inside the probe | probe |
| L6 | `fc_leak` compiles under `ring_scope` and reduces on literals | `fc_leak [set ord0]` reduces to `0`; one 2-set and one 3-set reduce to their closed forms | probe |
| L7 | The cut-shift bijection transports MI: `fdistmap phi P = P` and joint-distribution equality give `leak_rot1` | Qed'd miniature of the full `leak_rot1` shape (any fixed small k) | probe |
| L8 | `nth`-of-`rot` at size 5: `nth false (rot k s) i = nth false s ((i + k) %% 5)` for `size s = 5`, `i, k < 5` | Qed'd lemma in the probe (general or 25-case concrete) | probe |
| L9 | The empty view is constant and leaks 0 | Qed'd miniature of `leak_view_nil` | probe |
| L10 | The 32-way membership-bit case split identifies an abstract `A : {set 'I_5}` with a literal | Qed'd miniature at `'I_2` (4 subsets) of the same shape, plus one worked `'I_5` branch | probe |
| L11 | Anchor bridge: `ViewT` concrete tuple equals `ViewA` concrete seq as RVs | Qed'd miniature for the singleton anchor | probe |
| L12 | The seven anchors compose to the master theorem | decomposition probe: master statement derived to Qed from `Admitted` supports (the one legitimate `Admitted`, probe file only) | probe |
| L13 | {0,1,3} fibre tables are as computed above | Python enumeration (done); one view count and one joint count re-derived by compute in the object probe | partial (Python done) |
| L14 | `fc_shuffle k = rot k` | verified at `five_card_program.v:84` | GO |
| L15 | Paper loci: contribution bullet lines 137-138, section sentence + footnote line 592, figure caption line 644 of `main.tex` | grep verified this session | GO |
| L16 | The six existing anchors and `H_secret` are `Qed` in the target file with the claimed statements | read this session; re-confirmed by the decomposition probe importing nothing and restating them | GO (restate in probe) |

## Soundness invariants

- No new axiom, no assumed constant, no `Admitted` outside the
  decomposition probe file. `Print Assumptions leak_view_set` (and each new
  lemma) shows boolp classical facts only, matching the existing seven.
- Every stated value is an exact closed form of a Shannon mutual
  information; no approximation and no computational-indistinguishability
  substitute anywhere.
- Scope, stated honestly: values are average-case Shannon mutual
  information in bits (log base 2) under the uniform prior on
  `(a, b, cut)`, i.e. the unbiased (epsilon = 0) den Boer member only; one
  passive observer sees one reveal event at a fixed position set; no claim
  about biased family members, adaptive observers, or repeated reveals.
  The quantifier is: for each fixed `A`, MI averages over the 20-outcome
  space.
- Non-vacuity: the carrier is a concrete instantiated fdist on a concrete
  20-element finType; probes elaborate every hypothesis at it. The
  hypothesis set of every new lemma is satisfied by the file's own
  concrete objects.
- Cited library objects (file, shape):
  - `mutual_info_RVE` (infotheo `proba`/`entropy` layer): `I(X;Y) = H(X) - H(X|Y)`; already used by all six leak lemmas.
  - `centropy_RVE'`, `centropy1_RV`, `centropy_RV_comp0` (infotheo): conditional-entropy expansions; used by `leak_k2_*`, `leak_k3`, `leak_k4`.
  - `fdist_uniform`, `fdistmapE`, `fdistmap` (infotheo `fdist`): uniform distribution and pushforward; used by `H_secret`, `count_pr`.
  - `boolp.funext` (mathcomp-analysis boolp): RV extensionality; used by `leak_k4`/`leak_k5`.
  - `rot`, `nth`, `map_tuple`, `mktuple`, `tnth`, `inord`, `enum`, `cardE` (mathcomp `seq`/`tuple`/`fintype`): all standard; L3/L4/L8 probe their composition at the carrier.
  - `[set _; _]`, `[exists _, _]`, `setP`, `inE` (mathcomp `finset`): finite-set literals and membership; L5/L10 probe them.

## Probe plan

Probe directory (kept permanently, never imported by a permanent file,
outside `_CoqProject`'s explicit file list so `make` never sweeps it):

```
.claude/probes/2026-08-10-five-card-all-reveals/
  five_card_leak_enum.py  — ground-truth enumeration (already run)
  probe_objects.v         (L1, L3, L4, L5, L6, L8, L13)
  probe_shapes.v          (L2, L7, L9, L10, L11)  — Qed miniatures
  probe_decomposition.v   (L12, L16) — headline from Admitted supports
  MUTATIONS.md            — per-probe perturbation and its observed failure
```

Each probe file opens with the real imports of `five_card_leakage.v` plus
any proposed new import, and replicates the section context verbatim, so a
scope breakage introduced by a new import fails the probe. Mutation checks
per file: at least one deliberately wrong variant (wrong carrier, dropped
hypothesis, wrong count) confirmed to fail, recorded in `MUTATIONS.md`.

Compile loop: delegated to a `rocq-prover` subagent with `model: opus`,
using `rocq_compile_file` / `rocq_check` (never a permissive ad-hoc
invocation); the orchestrating session re-verifies compiles and
`rocq_assumptions` afterwards. Stopping rule per the skill: after two
failed attempts on a row, write the smallest isolating counter-probe and
attribute the failure before touching anything else.

## Adversarial audits

Launched in parallel after the probes compile, both given this spec, the
probe files, and repo read access; each returns explicit GO / NO-GO with
machine-checked evidence per finding:

- Soundness audit: compile-capable general-purpose agent. Is each ledger
  claim true, is each route possible, do the English statements match the
  formal ones, are the closed forms the ones enumerated, is nothing
  vacuous (vacuity probe: instantiate every hypothesis concretely;
  tautology probe: `Fail reflexivity` on the master statement).
- Naming/style audit: `mathcomp-skills:mathcomp-style-auditor`. Do
  `succ5`, `ViewT`, `ViewS`, `fc_adjacent`, `fc_leak`, `leak_k3_gap`,
  `leak_rot1`, `leak_view_nil`, `leak_view_set`, `mutual_info_view_inj`
  follow project and MathComp conventions; does an existing lemma already
  provide any of them; do the claimed precedents exist at live paths.

Findings fold back into this spec (changed claims, or rejections with
reasons); the spec is re-committed before the implementation plan.

## Implementation outline (the plan will quote probe code verbatim)

1. `leak_k3_gap` by the `leak_k3` template with the fibre tables above.
2. `mutual_info_view_inj` (or the found infotheo lemma).
3. `succ5`, the cut-shift bijection, `fdistmap phi P = P`, `ViewT`,
   `leak_rot1`.
4. `leak_view_nil`.
5. Seven anchor bridges to `ViewT` form.
6. `fc_adjacent`, `fc_leak`, `ViewS`.
7. Membership-split helper and `leak_view_set`.
8. Paper edits (below), after the `.vo` gate.

One atomic task per commit; each compiles before the next starts. Any
stuck master-theorem branch falls back to the brute-force enumeration
template locally, without changing any statement.

## Verification gates

1. `Print Assumptions` on every new lemma: boolp classical axioms only;
   no `Admitted`; no new axiom.
2. `make -j1 pgg-smc/instances/denboer1989/five_card_leakage.vo` compiles
   clean (rocq-mcp for intermediate checks; the single full compile
   persists the `.vo`).
3. The commit passes the two-stage rocq-audit normally, no bypass; every
   new declaration carries its H-series role tag (`@main security` for
   `leak_view_set` and `leak_k3_gap`, `@composes`/`@intent` for helpers).

## Paper edits (gated on gate 2)

- `main.tex` lines 137-138 (contribution bullet): "exact
  mutual-information leakage values for six reveal patterns" becomes
  "exact mutual-information leakage values for every reveal pattern".
- Line 592: "quantifies six reveal patterns exactly" becomes "quantifies
  every reveal pattern exactly"; the footnote gains `leak_view_set` and
  `leak_k3_gap` alongside the six existing lemma names.
- One added sentence recording the finding: every three-card reveal leaks
  the same 6/5 - (9/20) log 3 bits, so only the two-card case
  distinguishes the pattern's shape, adjacent versus distance-two.
- Figure caption at line 644 already reads "one machine-checked value per
  reveal pattern" and stays.
- The paper builds; page count stays at 21; house prose rules (no
  em-dashes, no parenthetical asides, "distribution" never "law",
  no abbreviations).

## Risks

- Lazy-eval hazards are low (20-outcome space, no BFS-scale tables), and
  side conditions go premise-first regardless.
- The 32-branch master proof is tedious but mechanical; the per-branch
  brute-force fallback bounds the damage of any stuck branch.
- Stage-2 audit token caps: the work lands as a small number of
  single-file commits, far under the daily cap.
- If `mutual_info_view_inj` has no infotheo ancestor, the derivation adds
  roughly 40 lines via `centropy_RVE'` reindexing; the shape miniature in
  `probe_shapes.v` de-risks it before the plan exists.
