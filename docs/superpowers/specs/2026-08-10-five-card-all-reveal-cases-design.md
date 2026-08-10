# Five-card leakage: every reveal case (design)

Date: 2026-08-10.
Target file: `pgg-smc/instances/denboer1989/five_card_leakage.v`.
Paper target: `pgg-smc/paper-wadt2026/main.tex` (three loci, listed below).
Status: probe round 1 complete (all rows GO); adversarial audits complete
(soundness GO; naming NO-GO with nine blocking findings, all resolved
below); probe round 2 complete (R1-R5 all GO; `probe_round2.v` compiles
with the master theorem Qed over ALL 32 branches as real chains, single
Admitted support `leak_k3_gap`). Ready for the user review gate, then the
implementation plan. This spec follows `/rocq-probe-first-spec`.

## Goal

One theorem quantifying the mutual information between the den Boer secret
and the revealed card colours for every subset of the five row positions,
so the wadt2026 paper can claim "every reveal pattern" instead of
"six reveal patterns".

## Decisions (from the brainstorm and the audit round, in order taken)

1. Scope: master theorem over every subset `S : {set 'I_5}`, including
   `set0`, so the statement carries no side condition.
2. Statement form: set-indexed, with a closed-form function
   `leak : {set 'I_5} -> R`.
3. Paper edits are part of this package, strictly gated on the compiled
   `.vo`.
4. Architecture: rotation symmetry plus the seven proven pattern lemmas.
   Brute-force enumeration in the existing `cardV`/`cardJ` style remains a
   per-branch fallback only.
5. Probing follows `/rocq-probe-first-spec` (user directive this session):
   compiled probes and two adversarial audits before the plan.
6. The coordinate-permutation fact is packaged as invariance of mutual
   information under an injective relabeling of the view alphabet, applied
   with `rot_tuple` per wrap-around branch. (The original rationale "avoids
   a perm import" was false — naming audit F4: `perm` and `fingroup` are
   already in the destination compilation unit via `five_card_program.v` —
   but the packaging stands on simplicity alone.)
7. Audit round 1 renames and reuse (resolutions table below): the cyclic
   position shift is `fc_sigma_fun`/`fc_sigma_inv`/`fc_sigmaK` reused from
   `five_card_group.v:50-74`, not re-invented; `fc_leak`/`fc_adjacent`
   become `leak`/`adjacent` (the `fc_` namespace is program/group
   vocabulary); the seven per-anchor bridges collapse into one general
   `ViewT_ViewA` lemma; ordinal literals use the `Ordinal … isT` encoding
   via `Local Notation p0..p4`, matching `five_card_group.v`.

## Ground truth (exact 20-outcome enumeration)

Script: `docs/superpowers/probes/2026-08-10-five-card-all-reveals/five_card_leak_enum.py`,
mirroring `fc_encode`, `fc_negate`, `fc_arrange`, `fc_shuffle k = rot k`
from `five_card_program.v` (faithfulness re-verified line-by-line by the
soundness audit, which also re-implemented the enumeration independently:
`audit/independent_enum.py`, checks C1-C5, zero failures). Results:

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
Two of the eight rows are re-derived in-kernel (probe round 1,
`cardV013_FTT`, `cardJ013_true_FTT`); the table is not fully
machine-checked until `leak_k3_gap` is Qed (naming audit F27).

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

## Formal core (post-audit names; final shapes fixed by probe round 2)

New imports in the permanent file: `From mathcomp Require Import div`
(needed for `%%` in the rotation arithmetic; regression-tested by the
soundness audit compiling a full copy of the file with `div` added:
`audit/audit_div_regression.v`) and `From pgg_smc Require Import
five_card_group` (makes `fc_sigma_fun` importable by name; the module is
already in the Require closure).

```coq
Local Notation p0 := (Ordinal (isT : (0 < 5)%N)).  (* .. p1 p2 p3 p4 *)

(* position-tuple view: component i reads the card at position tnth t i *)
Definition ViewT k (t : k.-tuple 'I_5) : {RV P -> k.-tuple bool} :=
  fun w => [tuple nth false (arr w) (val (tnth t i)) | i < k].

(* set view: positions of S in ascending enumeration order; enum_tuple
   used directly (mathcomp/ssreflect/tuple.v:430, a Canonical) *)
Definition ViewS (S : {set 'I_5}) : {RV P -> #|S|.-tuple bool} :=
  ViewT (enum_tuple S).

(* the two elements of a 2-set at cyclic distance 1; fc_sigma_fun is the
   group file's cyclic shift sigma(i) = (i + 1) mod 5 *)
Definition adjacent (S : {set 'I_5}) : bool :=
  [exists i : 'I_5, S == [set i; fc_sigma_fun i]].

Definition leak (S : {set 'I_5}) : R :=
  match #|S| with
  | 0 => 0
  | 1 => 0
  | 2 => if adjacent S
         then 27%:R / 10%:R - 4%:R^-1 * log 5%:R - (7%:R / 10%:R) * log 7%:R
         else 5%:R / 2%:R - (3%:R / 20%:R) * log 3%:R - 2%:R^-1 * log 5%:R
              - (7%:R / 20%:R) * log 7%:R
  | 3 => 6%:R / 5%:R - (9%:R / 20%:R) * log 3%:R
  | _ => 2%:R - (3%:R / 4%:R) * log 3%:R  (* #|S| >= 4 determines the secret *)
  end.
```

New results (variable conventions per naming audit F46: `A : seq nat` for
position seqs as in the existing file, `S : {set 'I_5}` for sets,
`T U : finType` for the general lemma):

1. `leak_k3_gap` : `` `I( Secret ; ViewA [:: 0; 1; 3]%N ) = 6%:R/5%:R - (9%:R/20%:R) * log 3%:R ``.
   Direct reuse of the `leak_k3` template with the fibre tables above.
2. `injective_mutual_info_RV` : for finite types `T U`, RVs
   `X : {RV P -> T'}`, `Y : {RV P -> T}` and injective `g : T -> U`,
   `` `I( X ; g `o Y ) = `I( X ; Y ) ``. Generalized over the first RV
   (free generality, upstream-ready next to infotheo's
   `injective_joint_entropy`, entropy.v:341); derived from
   `cPr_centropy_RV_comp` (entropy.v:581), `pfwd1_comp` (proba.v:1046),
   `cpr_eqE` (proba.v:2061) — no single infotheo ancestor exists (verified
   by both probe and audit). Stated locally, not upstreamed (reason:
   editing `information_theory/entropy.v` forces a full downstream rebuild
   of infotheo; out of scope).
3. `mutual_info_ViewT_sigma` : `` `I( Secret ; ViewT (map_tuple fc_sigma_fun t) ) = `I( Secret ; ViewT t ) ``.
   Via the cut-shift map `cut_sigma (a, b, k) = (a, b, fc_sigma_fun k)`:
   `fdistmap cut_sigma P = P` (cancellation from `fc_sigmaK`), the
   componentwise transport `ViewT (map_tuple fc_sigma_fun t) = ViewT t \o
   cut_sigma`, and equality of joint distributions.
4. `mutual_info_ViewT_rot` : `` `I( Secret ; ViewT (rot_tuple n t) ) = `I( Secret ; ViewT t ) ``,
   from `injective_mutual_info_RV` with `g = rot_tuple n` (injective by
   `rot_tuple_inj`, a local tuple fact).
5. `leak_k0` : `` `I( Secret ; ViewT ([tuple] : 0.-tuple 'I_5) ) = 0 ``
   (constant view; the `leak_k<n>` family name at n = 0).
6. `ViewT_ViewA` (the one general bridge, replacing seven per-pattern
   bridges) : for `A : seq nat` and `t : (size A).-tuple 'I_5`,
   `map val (val t) = A -> ViewT t = ViewA A`. The six proven `leak_k*`
   lemmas and `leak_k3_gap` are consumed directly through it.
7. `mutual_info_ViewS_ViewT` : for `S : {set 'I_5}`, `k`, a tuple
   `t : k.-tuple 'I_5` and `e : #|S| = k`,
   `map val (val (enum_tuple S)) = map val (val t) ->
   `` `I( Secret ; ViewS S ) = `I( Secret ; ViewT t ) ``. Confines the
   dependent cast to one proof (`case: k / e`); no cast in any statement.
8. Master theorem `leak_view_set` :
   `` forall S : {set 'I_5}, `I( Secret ; ViewS S ) = leak S ``.
   Proof: present `S` by its five membership bits (`setb5` + `setb5_onto`),
   32 branches; each branch computes its ascending position tuple through
   the `enum_setb5`/`card_setb5` rewriting bridge, chains
   `mutual_info_ViewT_sigma` and `mutual_info_ViewT_rot` to a proven
   pattern lemma via `ViewT_ViewA`, and computes `leak` (adjacency by
   `adjacentE`, the computational form on the five bits). Landed in
   `probe_round2.v`: ALL 32 branches are real chains, Qed; the round-1
   `leak_view_rest` escape hatch does not exist in round 2 (naming audit
   F23 satisfied by construction).

Supporting infrastructure (probe rounds 1-2):
- idP-opacity bridge: `enum_val5`, `card_val5`, `card_setb5`,
  `enum_setb5` — `enum_tuple`, `#|S|` and set literals are
  conversion-blocked on the Qed-opaque `idP` inside `insub`, so branch
  computations go through these rewriting lemmas rather than
  `vm_compute` (necessity verified by the soundness audit's
  `Fail Check (erefl : #|[set p0]| = 1%N)`).
- `val_fc_sigma_fun : val (fc_sigma_fun i) = (i.+1 %% 5)%N` (the name
  `fc_sigma_funE` is taken by `five_card_program.v:128` and silently
  shadows on import — round-2 finding); `fc_sigmaKV : cancel fc_sigma_inv
  fc_sigma_fun`, absent from `five_card_group.v`, proved locally.
- `map_tnth`: `[seq f (tnth t i) | i <- enum 'I_n] = [seq f j | j <- val t]`
  — absorbs the `map_comp`/`map_tnth_enum`/`tval` matching frictions in
  the bridge proof (round-2 finding).
- `exists_ord5` (five-instance expansion of `[exists i : 'I_5, _]`, which
  is idP-blocked) and `setb5_eq` (set equality as bit equality), feeding
  `adjacentE`.
- `leakE<n>` value lemmas reading `leak (setb5 …)` off `card_setb5` and
  `adjacentE` per branch family.

Residual name hazard, recorded: `adjacent` exists as a notation in
`mathcomp.analysis.sequences`; it is unreachable from the destination
file today, but importing `sequences` there later would clash.

All new results live in `five_card_leakage.v`, same section, `Qed` only,
boolp classical axioms only. The seven existing lemmas are not modified
(statements or proofs).

## Claim ledger

Round 1 (all GO, probe files + audit evidence):

| # | Claim | Evidence | Status |
|---|---|---|---|
| L1 | The file's MI toolkit elaborates at the pinned carrier for the new statements | `probe_mi_toolkit` (probe_objects.v) | GO |
| L2 | Injective-relabeling invariance derivable (no single infotheo ancestor) | `mutual_info_view_inj` Qed (probe_shapes.v); ancestors verified at live paths by both audits; replayed at the real imported carrier in `audit/audit_supports_real.v` | GO |
| L3 | A canonical `#\|S\|`-tuple enumerating `S` exists, and branch values are reachable through a rewriting bridge (`enum_val5`/`card_val5`) — NOT by computation: `enum_tuple`/`#\|S\|`/`inord` are conversion-blocked on Qed-opaque `idP` (wording amended per soundness Finding 10) | `set_tuple_013` (probe_objects.v); `Fail Check` opacity probes (`audit/audit_decomp_checks.v`) | GO (amended) |
| L4 | `ViewT` typechecks at the carrier | Definition compiles | GO |
| L5 | `adjacent` computes on literals | 3 pairs (probe round 1) upgraded to all 10 pairs Qed (`audit/audit_decomp_checks.v`) | GO |
| L6 | `leak` compiles under ring_scope and reduces on literals | `fc_leak_singleton`/`_2adj`/`_3gap` (probe_objects.v) | GO |
| L7 | The cut-shift bijection transports MI | `leak_rot1` Qed at general k (probe_shapes.v; real-carrier replay in audit_supports_real.v) | GO |
| L8 | `nth`-of-`rot` at size 5 | `nth_rot5` Qed | GO |
| L9 | The empty view is constant and leaks 0 | `leak_view_nil` Qed | GO |
| L10 | Membership-bit case split identifies an abstract `S` with a literal | `set2_cases`, `set5_branch_04`, and the stronger `setb5_ex` used by the headline | GO |
| L11 | `ViewT`/`ViewA` bridge exists | singleton bridge Qed; GENERALIZED in round 2 (R2) per naming F14/F15 | GO (superseded by R2) |
| L12 | The supports compose to the master theorem: the composition MACHINERY type-checks and six representative chains close (identity, 1-step and 4-step rotation, wrap relabeling at both arities, empty). NOT evidence that all 32 chains exist; the remaining 26 are implementation work with the demonstrated pattern (wording amended per soundness Finding 7) | `leak_view_set` Qed from 12 Admitted supports (probe_decomposition.v); assumption cone recomputed independently by orchestrator and audit | GO (amended) |
| L13 | {0,1,3} fibre tables as computed | 2 of 8 rows in-kernel; all 8 by two independent enumerations | GO (full check lands with `leak_k3_gap`) |
| L14 | `fc_shuffle k = rot k` | five_card_program.v:84 | GO |
| L15 | Paper loci: contribution bullet lines 138-139 (corrected from 137-138, soundness Finding 9), section sentence + footnote line 592, figure caption line 644 | grep, both audits | GO (corrected) |
| L16 | The six anchors and `H_secret` are Qed with the claimed statements | five_card_leakage.v:86-546; consumed by the decomposition probe | GO |

Round 2 (complete; all verified at the REAL imported carrier; compile and
assumption cone re-verified firsthand by the orchestrator):

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| R1 | Rotation cluster rebuilt on `fc_sigma_fun`/`fc_sigma_inv`/`fc_sigmaK`, no `succ5`/`pred5` | GO | `mutual_info_ViewT_sigma` Qed; `fc_sigmaKV` proved locally (absent upstream); zero Admitted in the cluster |
| R2 | General `ViewT_ViewA` bridge in the `Ordinal`-literal encoding; all published `leak_k*` transfer through it | GO | one extra support `map_tnth` needed (matching friction, recorded above) |
| R3 | Distance-2 branches close through real chains with `adjacentE` Qed | GO | both `{0,2}` (direct) and `{0,3}` (3 sigma steps + `rot_tuple 1` relabel) real; `adjacentE`'s five-disjunct formula Qed |
| R4 | `ViewS S := ViewT (enum_tuple S)` direct | GO | no `set_tuple` wrapper |
| R5 | Renamed identifiers collision-free | GO | one collision found and fixed (`fc_sigma_funE` → `val_fc_sigma_fun`); 41-name repo + library sweep otherwise clean; `adjacent` notation hazard recorded |

Round-2 exceedance: `leak_view_set` Qed over ALL 32 branches as real
chains (floor was 8); assumption cone = boolp trio + `leak_k3_gap` only.
probe_round2.v: 33 Qed, 1 Admitted, 0 Abort/Axiom, 0 lines over 80
columns. MUTATIONS.md round 2: M7 (adjacentE wrong wrap disjunct), M8
({0,3} asserted at the adjacent value — route completes, value refuses),
M9 (adjacency misread) — all confirmed failing.

## Soundness invariants

- No new axiom, no assumed constant, no `Admitted` outside the
  decomposition probes. `Print Assumptions leak_view_set` (and each new
  lemma) shows boolp classical facts only, matching the existing seven.
  Verified for round 1 by orchestrator and soundness audit independently.
- Every stated value is an exact closed form of a Shannon mutual
  information; no approximation and no computational-indistinguishability
  substitute anywhere.
- Scope, stated honestly: values are average-case Shannon mutual
  information in bits (log base 2) under the uniform prior on
  `(a, b, cut)`, i.e. the unbiased (epsilon = 0) den Boer member only; one
  passive observer sees one reveal event at a fixed position set; no claim
  about biased family members, adaptive observers, or repeated reveals.
  The quantifier is: for each fixed `S`, MI averages over the 20-outcome
  space.
- Non-vacuity: the carrier is a concrete instantiated fdist on a concrete
  20-element finType; probes elaborate every hypothesis at it. The
  headline is not a tautology: `Fail reflexivity` / `Fail (by [])` succeed
  for content reasons (audit_decomp_checks.v).
- Cited library objects (verified at live paths by the naming audit):
  - infotheo: `mutual_info_RVE` entropy.v:989, `centropy_RVE'` :442,
    `centropy1_RV` :416, `centropy_RV_comp0` :498, `cPr_centropy_RV_comp`
    :581, `injective_joint_entropy` :341, `chain_rule_RV` :644,
    `inde_RV_joint_entropyE` :1541, `pfwd1_comp` proba.v:1046, `cpr_eqE`
    :2061, `fdistmap_comp` fdist.v:393, `fdist_ext` :234.
  - mathcomp 2.4.0: `enum_tuple` ssreflect/tuple.v:430 (a Canonical),
    `val_enum_ord` fintype.v:1776, `rot_tuple` tuple.v:212, `rot_inj`
    seq.v:882, `map_rot` seq.v:2533, `big_pred1` bigop.v:1869, `ltn_pmod`
    div.v:137, `modnDml`/`modnDmr` div.v:295/298, `cardE` fintype.v:456,
    `cards1` finset.v:762, `eq_from_tnth` tuple.v:96, `tnth_mktuple`
    tuple.v:459, `inj_map` seq.v:2545.
  - this repo: `fc_sigma_fun`/`fc_sigma_inv`/`fc_sigmaK`
    five_card_group.v:50/62/74; `fc_shuffle` five_card_program.v:84.

## Probe plan

Probe directory (kept permanently, never imported by a permanent file,
outside `_CoqProject`'s file list):

```
docs/superpowers/probes/2026-08-10-five-card-all-reveals/
  five_card_leak_enum.py   — ground-truth enumeration (run; audited)
  probe_objects.v          — round 1: L1, L3-L6, L8, L13 (Qed, kept as evidence)
  probe_shapes.v           — round 1: L2, L7, L9-L11 (Qed, kept as evidence)
  probe_decomposition.v    — round 1: L12, L16 (headline Qed, 12 Admitted supports)
  MUTATIONS.md             — six perturbations, each confirmed failing
  audit/                   — soundness-audit evidence (independent_enum.py,
                             audit_decomp_checks.v, audit_no_div.v,
                             audit_div_regression.v, audit_supports_real.v)
  probe_round2.v           — round 2 (landed): R1-R5 at the real imported
                             carrier; 33 Qed, 1 Admitted (leak_k3_gap),
                             all 32 master branches real; the plan's
                             verbatim source
```

Round-1 files are audit evidence and stay untouched; round 2 supersedes
them as the plan's verbatim source. Compile loop: `rocq-prover` subagent,
`model: opus`, rocq-mcp workflow, sequential compiles only. Stopping rule
unchanged.

## Adversarial audit round 1 — results and resolutions

Soundness audit: **GO**, no blocking findings. Fold-ins: L3 and L12
wording amended (above); paper locus corrected to 138-139; enumeration
script docstring fixed (float entropy sums over exact integer counts).
Evidence upgrades adopted: real-carrier replays (audit_supports_real.v),
full-file `div` regression compile, all-10-pair adjacency classification.

Naming audit: **NO-GO**, nine blocking findings. Resolutions (accepted
unless stated; the finding numbers are the audit's):

| Finding | Resolution |
|---|---|
| F1/F2/F3 `succ5`/`pred5`/cancel pair duplicate `fc_sigma_fun`/`fc_sigma_inv`/`fc_sigmaK`; `pred5` collides with MathComp `pred1..pred4` | ACCEPTED. Reuse the group file's trio; `succ5`, `pred5` and their val/cancel lemmas deleted. Round 2 R1 |
| F4 decision 6's "no perm import" premise false | ACCEPTED. Decision 6 amended; packaging kept on simplicity grounds |
| F11 `anchorT_*` metaphor names | ACCEPTED. Eliminated entirely by the general bridge (F14) |
| F14/F15/F26 bridge chain does not close; encoding mismatch (`inord` vs `Ordinal`) | ACCEPTED. One general `ViewT_ViewA`; `Ordinal`-literal encoding via `Local Notation p0..p4` repo-consistent with five_card_group.v. Round 2 R2 |
| F16 file-scope `i0..i4` shadow canonical index names | ACCEPTED. `Local Notation p0..p4` |
| F17 `fc_leak`/`fc_adjacent` namespace break | ACCEPTED. `leak` / `adjacent` (verified free repo-wide) |
| F23 `leak_view_rest` drift token | ACCEPTED. Probe-only; all 32 chains are real in implementation |
| F24/F25 no distance-2 branch, no `adjacentE` | ACCEPTED. Round 2 R3 |
| F42 probe comments are meta/status narration | ACCEPTED. Every transcribed comment rewritten declaratively; H-series role tags added in the plan text (F43) |
| F6/F7 relabeling lemma name and location | ACCEPTED name `injective_mutual_info_RV`, generalized over the first RV. Placement REJECTED-in-part: stays local to five_card_leakage.v, not upstreamed to entropy.v (a core-file edit forces a full downstream infotheo rebuild; out of scope). Upstream candidacy noted in its comment |
| F8 `leak_rot1`/`leak_rotT` name hazard | ACCEPTED. `mutual_info_ViewT_sigma` / `mutual_info_ViewT_rot` |
| F9 `leak_view_nil` naming | ACCEPTED. `leak_k0` |
| F10 extract shared independence route used by `leak_k1` and `leak_k0` | REJECTED. `leak_k0` reuses the probe's own Qed proof; refactoring `leak_k1`'s published proof body is churn on a paper-cited lemma with zero statement gain. Optional later golf |
| F12 `rotV_inj` misreads as inverse | ACCEPTED. `rot_tuple_inj`, kept local (not lib/ssr_ext.v: same rebuild-cost reason as F7) |
| F13 `set_tuple` thin wrapper | ACCEPTED. Dropped; `enum_tuple` used directly. Round 2 R4 |
| F18 `leak_view_of_tuple` name | ACCEPTED. `mutual_info_ViewS_ViewT` |
| F19 `tuple5_eq` misleading and inlinable | ACCEPTED. Dropped, term inlined |
| F20 `setb5_ex` suffix | ACCEPTED. `setb5_onto` |
| F21 `cutS` names, dead `cutS_bij` | ACCEPTED. `cut_sigma`; bijectivity lemma dropped (cancellations used directly) |
| F22 `set2_cases`/`set5_branch_04` scaffolding | ACCEPTED. Probe-only, not transcribed |
| F28 relabeling lemma over-general | REJECTED. General form kept: it is the already-Qed proof, and generality is what makes it upstream-ready |
| F29 citation nit (`mathcomp.boot.tuple:427`) | ACCEPTED. Corrected to ssreflect/tuple.v:430, a Canonical |
| F34 `div` reverse-dependency risk | ACCEPTED as residual: full-copy compile is clean (audit); `Require Import` is not transitive re-export, so dependents see no new notations; the final `make` gate covers the closure |
| F46 parameter-name overloading | ACCEPTED. `A : seq nat`, `S : {set 'I_5}`, `T U : finType` |
| F47 `leak` catch-all branch | ACCEPTED-with-modification: catch-all kept (explicit `\| 4 \| 5` adds proof cases for zero semantic gain on 'I_5), one-line comment added |
| F48 `nth_rot5` proved twice in probes | ACCEPTED. One named lemma in the permanent file. Promoting den_boer_encoding.v's inline `rotjk` is out of scope (separate cleanup) |
| F35-F41 mechanical style items | ACCEPTED. Applied at transcription (line lengths, `{hm}` discharge idiom, drop the two removable `@`, scope-delimiter consistency; `boolp.funext` kept qualified per destination-file precedent) |

## Implementation outline (the plan will quote probe_round2.v verbatim)

With round 2 landing all 32 branches Qed, implementation reduces to two
proof tasks plus transcription:

1. Imports: `div`, `five_card_group`.
2. `leak_k3_gap` by the `leak_k3` template with the fibre tables above —
   the ONLY remaining new proof of substance (the probe's single Admitted).
3. Transcribe probe_round2.v into `five_card_leakage.v`: the rotation
   cluster, `injective_mutual_info_RV`, `rot_tuple_inj`, `leak_k0`,
   `ViewT_ViewA`, `map_tnth`, `exists_ord5`/`setb5_eq`/`adjacentE`,
   `adjacent`/`leak`/`ViewS`/`setb5`/`setb5_onto`, the idP bridge lemmas,
   `mutual_info_ViewS_ViewT`, the `leakE<n>` value lemmas, and
   `leak_view_set` with its 32 Qed chains — with declarative statement
   comments and H-series role tags added at transcription (`@main
   security` for `leak_view_set` and `leak_k3_gap`; `@composes`/`@intent`
   for the rest; `@composes` targets resolve only once the names are in
   the repo, so tags land with the code, not before).
4. Paper edits (below), after the `.vo` gate.

Every transcribed declaration gets a declarative statement comment plus
its H-series role tag (`@main security` for `leak_view_set` and
`leak_k3_gap`; `@composes`/`@intent` for the rest). One atomic task per
commit; each compiles before the next starts.

## Verification gates

1. `Print Assumptions` on every new lemma: boolp classical axioms only;
   no `Admitted`; no new axiom.
2. `make -j1 pgg-smc/instances/denboer1989/five_card_leakage.vo` compiles
   clean, then the reverse-dependency closure (`denboer_secrecy`,
   `denboer_trace`, `kim_secrecy`, `kim_trace`, `kim_input_privacy`,
   `pgg_cyclic_cut_leakage`, `den_boer_encoding`) rebuilds clean under the
   added imports.
3. Commits pass Stage 1 of the rocq-audit; Stage 2 is skipped via
   `ROCQ_AUDIT_BYPASS=fast` (user directive 2026-08-10). The naming and
   soundness review Stage 2 would have provided is already covered for
   this package by the two adversarial audit agents recorded above.

## Paper edits (gated on gate 2)

- `main.tex` lines 138-139 (contribution bullet): "exact
  mutual-information leakage values for six reveal patterns" becomes
  "exact mutual-information leakage values for every reveal pattern".
- Line 592: "quantifies six reveal patterns exactly" becomes "quantifies
  every reveal pattern exactly"; the footnote gains `leak_view_set` and
  `leak_k3_gap` alongside the six existing lemma names.
- One added sentence recording the finding: every three-card reveal leaks
  the same 6/5 - (9/20) log 3 bits, so only the two-card case
  distinguishes the pattern's shape, adjacent versus distance-two.
  (Licensed: soundness audit Finding 14.)
- Figure caption at line 644 already reads "one machine-checked value per
  reveal pattern" and stays.
- The paper builds; page count stays at 21; house prose rules (no
  em-dashes, no parenthetical asides, "distribution" never "law",
  no abbreviations).

## Risks

- Master-theorem branch risk is retired: all 32 chains are Qed in
  probe_round2.v; transcription risk only.
- The idP-opacity bridge is Qed and audited; no `vm_compute` on
  set-valued terms anywhere.
- `rewrite e !mutual_info_ViewT_sigma` in the branch chains uses `!` on a
  non-arithmetic lemma bounded by the `map_tuple` nesting depth (max 4);
  this is within the project's bounded-`!` allowance, not the forbidden
  arithmetic pattern.
- The `adjacent` notation hazard (mathcomp.analysis.sequences) is
  recorded; no action unless that import ever reaches the file.
- Lazy-eval hazards are low (20-outcome space); side conditions go
  premise-first regardless.
