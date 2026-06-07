# PGG piSMC Protocol Merge: Design

Date: 2026-06-07
Status: v4, revised after two pre-implementation gates. (1) A `rocq-prover`
typecheck of the record shapes against the live source: the `ReconPlug` /
`CoveringScheme` refactor is sound and implementable as written. (2) An
adversarial math/feasibility re-audit: corrected the den Boer content readout
(fixed face map, not the arrangement), re-rated the den Boer rebuild as MEDIUM,
replaced the impossible "reuse FCCommit/FCRecvCommit" plan with new pgg-typed
commit wrappers, and corrected the s5x5 operative genus. Both the den Boer `'I_5`
rebuild AND the input-commitment stage are in scope for this merge, done
sequentially (den Boer first, then input-commitment). Ready for implementation
planning after a final user review.

## 0. Revision note (what changed across versions)

- v1 -> v2: an adversarial audit found v1 not Rocq-feasible. v2 proposed
  **Option B**: generalize the threshold/recovery records and the session wire to
  arbitrary `secretT`/`shareT`. Option B forced generalizing `pgg_data` and
  re-proving the `native_compute` session duality.
- v2 -> v3: a clearer-plug brainstorm replaced Option B with **Option C**: keep
  the framework monomorphic at `ThresholdScheme 'I_N 'I_N`, encode den Boer's
  `bool` as `{0,1} ⊂ 'I_5`, add a content readout `'I_N -> 'I_N`, and carve
  recovery into a 4-field `ReconPlug` (recon-symmetry fields dropped; invariance
  over the full `pgg_G`). The wire stays `'I_N`, so no wire duality re-proof.
- v3 -> v4: two pre-implementation gates ran.
  - GATE 1 (`rocq-prover`, record shapes vs live source): all three shapes
    elaborate. `rp_recon_invariant` resolves at `pgg_G M` (compatible group
    type); `Notation cs_scheme` is safe (zero first-class uses); `cs_T'` /
    `cs_scheme_T` have zero consumers and are droppable; every retained instance
    pins `cs_recon_symmetry = pgg_G` via `subxx`, so the drop loses nothing for
    them. The record refactor is confirmed implementable.
  - GATE 2 (adversarial re-audit) found three corrections, all in the den Boer
    integration, plus a genus inaccuracy:
    1. **content correction.** The den Boer `content` is a FIXED face map
       `face : 'I_5 -> 'I_5`, NOT `encode_bool ∘ fc_arrange`. The latter is
       secret-dependent and type-incoherent (`fc_arrange : bool -> bool ->
       seq bool`). The secret arrangement lives in `ts_encode`/the starts; the
       dealer bakes the fixed face readout, so the wire reveals faces, not card
       identities (faithful to the trick) and stays `'I_5` (Section 5b).
    2. **den Boer rebuild is MEDIUM, not LOW.** den Boer's scheme must be rebuilt
       from `ThresholdScheme bool bool` to `'I_5` and must prove a NEW
       `ts_recon_perm_invariant` (three-consec rotation-invariance) that does not
       exist today. Transport of validity/recon/encode/correctness/privacy via
       `encode_bool`/`decode_bool` is mechanical, but the perm-invariance lemma
       and the content/encode split are real work (Section 5b, Section 16).
    3. **input-commitment cannot reuse FCCommit/FCRecvCommit.** Those are typed
       over `fc_dtype`/`fc_data`, incompatible with the protocol's
       `pgg_dtype`/`pgg_data`. The stage needs NEW pgg-typed commit wrappers and
       a dealer-prologue duality re-proof (Section 6). It is kept in scope, after
       the den Boer rebuild.
    4. **s5x5 genus.** The operative `cd_genus` in the s5x5 record is not the
       "Bring's genus 8" the spec claimed; reconcile the figure honestly
       (Section 9, Section 12).

## 1. Goal

Make the general piSMC protocol the single source of truth, fold in the bundling
prototyped under wreath7, and turn every concrete protocol (den Boer, Kim, S_5,
S_5 x S_5) into a thin instance of that one protocol. After the merge:

- one canonical protocol in `protocol/`, with `protocol/` no longer importing
  instance files (the current inversion in `card_exchange_pismc.v:13-16`, which
  imports `rigidity_monster_instance` and `rigidity_abelian_instance` for its
  duality demos, is removed by moving those demos to the instance dirs);
- den Boer's piSMC program and its recovery express the original Five Card Trick
  through that protocol, with its `bool` inputs/outputs encoded into
  `{0,1} ⊂ 'I_5` so the shared wire is the same `'I_N` every instance uses;
- `S_5 x S_5` is the canonical non-abelian `T > k` exemplar;
- wreath7 is retired, after `s5x5` reaches parity and the generic plug machinery
  is relocated.

## 2. Background: current state

Three layers, with duplication:

- Canonical program: `protocol/card_exchange_pismc.v` (`exchange_dealer/player/
  verifier`, parametric over `MonodromyReprType` + `PGGInterface`, with generic
  `native_compute` session duality). It currently imports instance files for its
  duality demos (the inversion above).
- Bundling prototype: `instances/wreath7/wreath_monodromy_profile.v` defines the
  `MonodromyProfile` record, `run_*`, the characters `run_eps`/`run_k`, the
  guarantees `run_anonymous`/`run_private`/`run_recovers`, and the plugs
  `abel_profile`, `s5_profile`. It imports instance files, so it sits above the
  instance layer.
- Bespoke instances: `instances/wreath7/wreath_smc.v` and
  `instances/denboer1989/five_card_pismc.v` are standalone session programs that
  do not reuse `exchange_*`.

Two models of "what gets shuffled":

- Position model (PGG): observable is a deck position `rho(P)(start_i)`; starts
  `uniq`; reconstruction reads positions; `shareT = 'I_N`.
- Value model (den Boer, the card protocols): observable is a face value at a
  slot; reconstruction reads face values, which may repeat. Modeled in Option C
  as a FIXED face readout on top of a uniq identity permutation (Section 5b).

The framework's `ts_recon_perm_invariant` (`pgg_sharing_framework.v:125`) and
`ThresholdScheme` (`pgg_sharing_framework.v:47`) are polymorphic in
`secretT`/`shareT`, but the whole downstream stack (`Section
pgg_protocol_secret`, `CoveringScheme`, `dealer_bridge.v`) is instantiated at
`'I_N 'I_N`. Option C **keeps that monomorphic instantiation** and bridges the
value model with a content readout `'I_N -> 'I_N`, rather than threading new type
parameters through the stack.

## 3. Architecture: single canonical protocol, with a record/plug split

`protocol/` holds:

1. `exchange_dealer/player/verifier`, with the content readout applied by the
   dealer (Section 5) and the input-commitment prologue (Section 6).
2. The `MonodromyProfile` record and `run_*`, moved out of wreath7. They depend
   only on `card_exchange_pismc` + the framework + `algebraic_rigidity`, so they
   live in `protocol/`. `MonodromyProfile` carries the `ReconPlug` as a field.

`instances/` holds:

3. The plugs `abel_profile`, `s5_profile`, and the new `s5x5_profile`, built from
   instance-level witnesses (cannot move to `protocol/` without inverting the
   layering). This is a record/plug split: record + `run_*` up to `protocol/`;
   plugs stay in `instances/`.

The instance-specific duality demos currently inside `card_exchange_pismc.v`
(Monster, abelian) move to their instance dirs so `protocol/` imports no
instances.

## 4. The unified role model and stages

Roles (virtual-dealer reading; the dealer is a virtual coordinator, not a
trusted third party):

- Dealer (virtual): builds the permutation table, splits it so each party knows
  only its own column, decides the group letter (word) and sends the whole word
  to the parties. It applies the content readout when building each column, so
  the readout is baked into the dealt values and the players and verifier never
  see card identities or the secret arrangement.
- Parties (players): receive their column plus the letter and shuffle by applying
  `word_eval(w)` to their own part, then reveal a plain `'I_N` value. The shuffle
  is a player action, not the dealer's. Faithful to den Boer and Kim (verified
  against arXiv:2511.05111: no dealer; the cut is a player action; the paper
  escalates to a malicious shuffling player).
- Verifier: collects endpoints (plain `'I_N` values) and forwards them to
  recovery.

Stages:

0. Input-commitment (Section 6): `M` input parties commit; a dealer-side
   `assemble` produces the secret-bearing layout (the starts). Degenerate
   `M = 0/1` is the single-dealer case.
1. Split / deal: build `perm_table`, apply the fixed content readout to each
   column, deal each party its column, send the word.
2. Compute / shuffle: each party applies the word to its column entry and reveals
   a plain `'I_N` value.
3. Recover (outside the session): collect the endpoints into a tuple, apply
   `ts_recon`; den Boer adds a final `decode_bool`. The content readout was
   already applied at the dealer, so recovery never reads identities/arrangement.

Letter length `L` unifies instances: den Boer `L = 1`, Kim `L` many, s5x5 `L`
tuned to the security target.

## 5. Option C: the `ReconPlug` and the content readout (the core refactor)

Keep the framework monomorphic at `ThresholdScheme 'I_N 'I_N`. Bridge the value
model with a content readout `'I_N -> 'I_N` applied by the dealer, and carve the
recovery side into a small pluggable record. The security side
(`SecurityWitness`, `var_dist` on `'I_N`) is independent of the recovery scheme
and is NOT touched.

The reconstruction plug (the two recon-symmetry fields dropped, Section 8):

```coq
Record ReconPlug (M : MonodromyReprType) := MkReconPlug {
  rp_scheme    : ThresholdScheme 'I_N 'I_N ;          (* the recovery scheme *)
  rp_content   : 'I_N -> 'I_N ;                        (* FIXED readout; id for position model *)
  rp_monodromy : pgg_gT M -> {perm 'I_(ts_T' rp_scheme).+1} ;
  rp_recon_invariant :
    @ts_recon_perm_invariant _ (pgg_G M) _ _ rp_scheme rp_monodromy ;  (* over the FULL group *)
}.
```

`rp_content` is SECRET-INDEPENDENT by construction (it is a field of the plug,
not a function of the secret). The secret-bearing data lives entirely in
`rp_scheme`'s `ts_encode` / the starts. This is the load-bearing correction from
GATE 2: a pointwise `'I_N -> 'I_N` map cannot carry a secret arrangement, so the
arrangement must live in the encode, and `content` is only the fixed readout.

The optional genus/tradeoff certificate wraps the plug:

```coq
Record CoveringScheme (M : MonodromyReprType) := MkCoveringScheme {
  cs_plug : ReconPlug M ;
  cs_data : CoveringData M ;
  cs_gap  : ts_T (rp_scheme cs_plug) <= ts_k (rp_scheme cs_plug) + 2 * cd_genus cs_data ;
}.
Notation cs_scheme cs := (rp_scheme (cs_plug cs)).    (* transparent back-compat *)
```

GATE 1 confirmed: `cs_T'` and `cs_scheme_T` (the share-count cache field and its
equation, current `covering_scheme.v:123`) have zero consumers and are dropped;
the `Notation cs_scheme` covers all 103 applied consumer uses (no first-class
uses exist).

Concretely:

1. `Section pgg_protocol_secret` (`pgg_sharing_framework.v:254`): keep
   `ts : ThresholdScheme 'I_N 'I_N`; add `Variable content : 'I_N -> 'I_N`.
   Redefine:
   - `pgg_recon_endpoints P := ts_recon ts [tuple content (rho P (tnth starts i)) | i]`
   - `pgg_hidden_invariant_perm`: the `G_stable` bridge becomes
     `content (rho g (start_i)) = tnth [tuple content (start_j) | j] (perm g i)`.
     With `content = id` this collapses to the current statement definitionally.
     `pgg_hidden_invariant_perm` already quantifies over an arbitrary
     `H : {group gT}` with `H \subset pgg_G M`; instantiating `H := pgg_G M`,
     `HsubG := subxx _` is all the recon-symmetry drop needs (GATE 1).
2. `CoveringScheme` (`covering_scheme.v:119`) becomes `{ cs_plug ; cs_data ;
   cs_gap }`. `cs_gap`/`cd_genus`/`cd_hurwitz` are unchanged in shape.
3. `AlgebraicRigidity` is kept; the `CoveringScheme` literal it transitively
   contains is restructured to nest the bare-plug fields into `cs_plug` (Section
   9). `ar_protocol_correct` threads `content` (`= id` for these). The
   `Notation cs_scheme` keeps consuming lemmas compiling unchanged. The
   reconstruct-layer covering builders `cover_genus0/1/2.v` also construct
   `CoveringScheme` records and are restructured the same way.

Specializations:

- Position model (sum-mod, s5x5, Kim, monster, oc, ...): `rp_content = id`,
  recovering today's recon definitionally. Mechanical but broad (every
  position-model instance file plus `cover_genus0/1/2.v` and `dealer_bridge.v`).
- den Boer: `rp_content = face` (a FIXED `'I_5 -> 'I_5` map, hearts ↦ 1,
  non-hearts ↦ 0), `rp_scheme =` the three-consecutive-hearts scheme over `'I_5`,
  with the secret arrangement in `ts_encode`/starts (Section 5b).

`pi_starts_uniq` stays a required field, discharged by `ord_tuple` slots in the
position model and by the card-identity permutation in den Boer (identities are
distinct, so starts stay `uniq`; face values repeat only after `content`).

### 5a. The wire does NOT change

Because the dealer applies the fixed content readout when building each column,
every revealed value is a plain `'I_N`. The verifier collects an `'I_N`-tuple and
`ts_recon` runs on it outside the session, exactly as today. GATE 2 confirmed:

- `pgg_data` (`pgg_interface.v:309-312`, payload `PGG_sheet 'I_N` / `PGG_hand
  (seq 'I_N)` / `PGG_idx nat`) is unchanged; `dealt_hand` payload stays
  `seq 'I_N`.
- The `native_compute` duality proofs for `exchange_player`/`exchange_verifier`
  are unchanged for ALL instances (position model and den Boer).
- den Boer reveals face values (`{0,1} ⊂ 'I_5`), never card identities: the
  dealer bakes `face` before the value reaches the wire, so faithfulness (the
  trick reveals faces, not card serials) and the unchanged wire hold together.

The only duality re-proof in the merge is the dealer commit prologue (Section 6),
not the player/verifier wire.

### 5b. The den Boer `'I_5` rebuild (MEDIUM)

den Boer is rebuilt as a `ThresholdScheme 'I_5 'I_5` so it plugs into the
monomorphic framework. The pieces:

- `encode_bool x := if x then 1 else 0` (into `{0,1} ⊂ 'I_5`), `decode_bool s :=
  (s == 1)`. Recovery returns `decode_bool (ts_recon collected)`.
- `rp_content = face : 'I_5 -> 'I_5`, the deck's fixed face map. The secret
  arrangement (a permutation of the five card identities determined by the two
  input bits via `assemble`/`fc_arrange`) is the `ts_encode` output / the starts,
  carried as a `uniq` identity tuple. Reading `content (rho w (start_i))` yields
  the face value at each cut position, exactly the trick's revealed sequence.
- `rp_scheme` over `'I_5`: `ts_valid s shares := fc_three_consec (map decode_bool
  shares) == decode_bool s`; `ts_recon shares := encode_bool (fc_three_consec
  (map decode_bool shares))`; `ts_encode` the canonical arrangement. These
  transport mechanically from the existing `bool` scheme
  (`five_card_pismc.v:241-244`, `fc_ts_valid/recon/encode`, `fc_correct`,
  `fc_three_consec`) through `encode_bool`/`decode_bool` cancellation.
- NET-NEW proof: `rp_recon_invariant : ts_recon_perm_invariant` over the full
  `Z_5`, i.e. three-consec rotation-invariance for all valid share tuples. It is
  true (`fc_three_consec` checks all five cyclic windows over `s ++ s`,
  `five_card_program.v:93-96`) and was confirmed mathematically sound by GATE 2,
  but it does not exist today and must be proved. This is why the rebuild is
  MEDIUM, not LOW.
- Privacy transports from `fc_ts_private` (`five_card_pismc.v:215-237`) via the
  bijection.

Security needs NO position-to-face-value bridge: it holds via the existing
`fc_security_uniform` witness (`eps = 0`, perfect security from the cyclic
group's regular, transitive action) plus threshold privacy `k = 2`. The
`card_protocol.v` decode lemmas (`cs_decode_encode_correct`,
`card_word_decode_correct`) are NOT usable: they require a fixed-point-free
involution (`is_fpf g`), and den Boer's `(0 1)(2 3)` has a fixed point
(`five_card_group.v:140`). The `card_security_from_endpoint` bridge named in a
stale comment (`card_protocol.v:28`) does not exist and that comment is removed
during the merge.

Out of scope still: value-transforming (non-permutation) shuffles. The
`ts_recon_perm_invariant` route is reindexing-only; no in-scope instance needs
otherwise.

## 6. The input-commitment stage (new pgg-typed wrappers)

First-class new stage: `M` input parties each commit; a dealer-side `assemble`
builds the secret-bearing layout (the starts). den Boer is `M = 2`,
`assemble = fc_arrange` (mapping `(a, b)` to the card-identity arrangement);
secret-sharing instances are `M = 0/1` (`assemble` returns the canonical layout).

GATE 2 correction: the existing `FCCommit`/`FCRecvCommit`
(`five_card_session_types.v:125-148`) CANNOT be reused. They are
`@sproc fc_dtype fc_data ...` over `fc_dtype = {DT_CardVal, DT_Commit}` and
`fc_data = {FC_card bool, FC_commit (seq bool)}`, a different inductive universe
from the protocol's `pgg_dtype = {DT_Sheet, DT_Hand, DT_Idx}` /
`pgg_data` (`pgg_interface.v:309-312`); an `fc_dtype` sub-process cannot be
spliced into a `pgg_dtype` `sproc`. So the stage is built with NEW commit /
recv-commit `sproc` wrappers over the EXISTING `pgg_dtype`/`pgg_data`: the
committed payload reuses an existing constructor (a sheet/card value), so the
player/verifier wire and their duality proofs stay unchanged (Section 5a), and
only the dealer gains a commit prologue.

Feasibility: `exchange_dealer` is a closed `sproc` ending in `SFinish` with
dependent fuel and `senv` threading (`card_exchange_pismc.v:210-221`). Exposing
its deal body as a continuation and prepending the new commit wrappers is a
dependent-session-type retype that requires re-proving the `native_compute`
duality lemmas for the new dealer shape. This is the one duality re-proof
obligation in the merge, and it is done AFTER the den Boer rebuild (Section 15).

## 7. Shuffle-by-players and the trust model

The shuffler is the player layer, not the dealer. The security witness is a
statement about the shuffler's distribution, which may be biased (Kim) or
adversarial. Separation of duties: the party that knows the secret/inputs does
not control the randomization. This reattributes the existing `word_eval`
machinery; no new mathematics.

## 8. The recon-symmetry fields are dropped (invariance over the full group)

`covering_scheme.v:125-128` currently carries `cs_recon_symmetry : {group
pgg_gT M}`, `cs_recon_symmetry_sub`, and states `cs_recon_invariant` on that
subgroup. Those fields only carry information when the recoverable scope is a
PROPER subgroup of the shuffle scope, which was the retired wreath case. GATE 1
confirmed every retained instance (den Boer, Kim, s5, s5x5) sets
`cs_recon_symmetry = pgg_G` via `subxx` (s5 `rigidity_s5_instance.v:339`, s5x5
`rigidity_s5x5_instance.v:391`, Kim/den Boer via `genus0_covering`
`cover_genus0.v:173`). So the two fields are dropped: `ReconPlug` states
`rp_recon_invariant` over the full `pgg_G M`, and correctness routes through it.

This ripples (GATE 1 enumerated it) to: `cs_monodromy cs -> rp_monodromy (cs_plug
cs)`; `cs_recon_symmetry cs -> pgg_G M`; `cs_recon_symmetry_sub -> subxx _`;
`cs_recon_invariant -> rp_recon_invariant (cs_plug cs)` in
`pgg_covering_correctness.v:53-65`, `pgg_protocol_landscape.v:319-331`,
`algebraic_rigidity.v:405-420`, and `dealer_bridge.v:42` (`Let G := pgg_G M`).
For every retained instance this is exactly what was already proved (the field
was `pgg_G`), so the change is mechanical, not new mathematics. The generic
engine `pgg_hidden_invariant_perm` is unchanged (it already takes an arbitrary
subgroup; we feed `pgg_G` / `subxx`).

GATE 1 flagged, consistently with project scope: wreath7 (`wcore`, a proper
abelian core) and star use a PROPER subgroup, so they could never return under
this record without re-introducing a per-plug symmetry field. They are out of
scope, so the drop is safe.

## 9. The T > k tradeoff (route-scoped)

Formalized: `cs_gap : ts_T <= ts_k + 2 * genus` (`covering_scheme.v`), so a
`CoveringScheme` with `T > k` requires genus > 0 (`genus0_exact`).
`security_threshold_tradeoff` (`cover_tradeoff.v:140`) is the genus/PGL
disjunction. The tradeoff lives on the `CoveringScheme` decoration, not on the
bare `ReconPlug`: correctness never needs it (GATE 2 confirmed no consumer forces
den Boer to build a `CoveringScheme`).

Three `T > k` routes, with different transitivity:

- Product route (s5x5): recon-symmetry is the pile-stabilizer, **intransitive**
  (two pile-orbits), so anonymity is within-pile with a cross-pile floor.
  Non-abelian, large. Carries a `CoveringScheme`.
- den Boer three-consec: a custom code on `Z_5`, **transitive**, `T = 5 > k = 2`,
  proved at the **bare-`ReconPlug`** level via `pgg_hidden_invariant_perm`. No
  `CoveringScheme`, no genus, no curve axiom. Small, abelian, hand-crafted, does
  not generalize to large non-abelian groups.
- AG route: excluded by design (`D_*`/Frobenius only; `s5_nogo.v`). The
  concrete-recovery survey
  (`notes/20260607T015612Z-concrete-recovery-mechanisms-survey.md`)
  confirms the positive-genus AG path (`cover_genus1.v`/`cover_genus2.v`) is the
  only recovery mechanism with no concrete instantiation, so excluding it costs
  the merge no working instance. The genus-0 RS5/Massey decode over GF(5) is
  concrete and axiom-free, and remains available to den Boer/Kim.

So `T > k` does NOT force intransitivity (den Boer refutes that). The product
route specifically gives intransitivity; there is no large non-abelian transitive
`T > k` construction. Hence s5x5 (intransitive, with the within-pile floor) is
the large non-abelian `T > k` exemplar; the floor is a property of the product
construction, not of `T > k` per se.

Genus honesty (GATE 2 correction): the genus number is meaningful only as the
genus of an actual cover realizing `G` (backed by a `realised_by_curve` axiom).
Attach it only where a real cover backs it: genus 0 (`P^1`, sum-mod/RS5) and
s5x5 (Bring's curve, `Aut = S_5`). The CURRENT s5x5 record carries
`cd_genus = 173` in `s5x5_covering_data` (`rigidity_s5x5_instance.v:337`) while
`s5x5_cs_gap` is proved against a smaller genus witness and lifted by
`leq_trans`; the two-component Bring's reading (genus 8) is a separate decoration
(`:505-574`). The spec does NOT present genus 8 as load-bearing. Reconciling the
173 / gap-witness / 8 figures to a single coherent operative genus is a cleanup
item in the s5x5 instance (Section 16), not a blocker for the record refactor.

Each instance declares its security target as uniform on its orbit(s):
transitive instances (den Boer, Kim, s5) target uniform on all `N`; s5x5 targets
within-pile uniform plus an honest floor (`sa_eps_inf = 1`), with threshold
privacy `k` intact. Both s5x5's within-pile mixing and wreath's old claim rest on
a Rayleigh axiom; this is disclosed (Section 14), so the wreath-vs-s5x5 honesty
contrast is about coherence (shuffle group = recovery group), not about being
axiom-free.

## 10. Instance lineup after the merge

| instance | group | T vs k | transitivity | security target | content / scheme |
|---|---|---|---|---|---|
| den Boer | Z_5 cyclic | T=5 > k=2 (three-consec), bare plug, no genus | transitive | uniform on 5, eps=0 | `content = face` (fixed `'I_5->'I_5`); arrangement-secret in `ts_encode`; three-consec `'I_5` scheme |
| Kim | Z_5 cyclic, biased | T=k | transitive | uniform on 5, vanishing, leakage vs bias | `content = id` |
| s5 | S_5 | T=k=5 (sum-mod) | transitive | uniform on 5, vanishing | `content = id` |
| s5x5 | S_5 x S_5 | T=10 > k=5 (product sum-mod), positive genus (Bring's, figure TBR-reconciled) | intransitive | within-pile vanishing + floor | `content = id`; product sum-mod scheme + `CoveringScheme` |

Under Option C den Boer is unified onto its real scheme (three-consec, encoded
into `'I_5`), resolving v1's two-scheme split: the protocol scheme and the
recovery scheme become the same `ReconPlug`. den Boer's old genus-0 RS5
`AlgebraicRigidity` (`five_card_security.v:325`) is deleted, not migrated (GATE 2
confirmed no external consumer); it carries no `CoveringScheme`. den Boer and Kim
still share `Z_5`; den Boer's uniform cut is Kim at `eps = 0`.

## 11. Wreath7 retirement: acceptance criteria

Wreath7 retires only after both 11a and 11b.

Reference: `notes/20260606T143722Z-wreath7-failure-and-s5x5-comparison.md`.

### 11a. s5x5 closes the per-instance parity gaps

1. Non-abelian lemma for `S_5 x S_5`.
2. Pure encode/recover program, den Boer analog (round-trip), as corollaries of
   `ts_encode`/`ts_recon_perm_invariant`.
3. Concrete `s5x5_PI : PGGInterface R_s5x5` (starts `= ord_tuple 10`).
4. Discharge `G_stable` concretely. `pgg_rho g = g` (identity inclusion,
   `pgg_interface.v:543`) is the easy part; the real work is the cast
   reconciliation between the deck-position `'I_10` and the share-index `'I_10`
   (`tnth_cast_tuple`/`cast_ord` bookkeeping across `cast_tuple (esym (congr1 S
   HT))`). Sound because `pgg_N'+1 = ts_T'+1 = 10` definitionally for s5x5.
5. End-to-end protocol correctness discharged unconditionally (from 3+4).
6. `CombinatorialRigidity` instance for s5x5 (fiber + crypto-secure), from
   `s5x5_large_group`, `s5x5_group_order_bound`, `s5x5_covering`.

### 11b. Generic plug machinery relocated (record/plug split)

7. Move `MonodromyProfile` + `run_*` from
   `wreath7/wreath_monodromy_profile.v` to `protocol/`. `MonodromyProfile` gains
   `mp_plug : ReconPlug`; `run_dealer` applies `rp_content`, `run_recover`
   applies `rp_scheme`'s `ts_recon`.
8. Keep `abel_profile`, `s5_profile` in `instances/`; add `s5x5_profile`
   (needs item 3). The plugs do not move to `protocol/`.
9. Relocate the floor-vs-vanishing comparison
   (`wreath7/wreath_profile_security.v`) to an instance-level location;
   optionally add s5x5's within-pile-floor character.
10. The canonical `exchange_*` (content readout) replaces the bespoke
    `wreath_smc.v` and `five_card_pismc.v` programs; no bespoke `s5x5_smc.v`.

Only after 1-10: delete the wreath-specific files and directory. Dependency check
(done): no file outside `instances/wreath7/` imports a wreath module (the one
external grep hit, `pgg_abelian.v:274`, is a comment), so deletion is safe once
the generic machinery is relocated. Naive directory deletion before relocation is
forbidden.

## 12. Feasibility: curves

s5x5's recovery is the product sum-mod route
(`product_sum_mod_perm_compatible`, `product_threshold.v:452`), curve-free, and
already discharged. No AG, no Bring's-curve formalization. The only curve content
anywhere is `realised_by_curve` axioms (documentation markers) on the genus
decoration: the existing ones for s5x5 and the genus-0 instances. NO new curve
axiom for den Boer (it carries no genus). Building s5x5's `CombinatorialRigidity`
and the `MonodromyProfile` plug needs only `nat` arithmetic and the existing
witnesses, no curve obligation. The operative s5x5 genus figure is reconciled as
a cleanup (Section 9, Section 16).

## 13. Non-goals

- No value-transforming shuffles (Section 5b limit).
- No cross-pile transitivity for the product `T > k` instance (impossible; it is
  the within-pile floor).
- No partial / per-party letter splitting in the deal stage.
- No polymorphic generalization of the framework or the wire (Option C keeps it
  monomorphic at `'I_N 'I_N`). The record work is the `ReconPlug` carve-out and
  the `CoveringScheme` restructure only, monomorphic, not a type generalization.

## 14. Verification bar and preconditions

- Precondition: green build first. The working tree is mid-refactor (a
  `MonodromyReprWithGeneratorType` rename and the `cs_recon_symmetry` field
  addition are in progress; `.vo` were stale). GATE 1 already re-greened the
  reconstruct dependency chain (`pgg_interface`, `pgg_sharing_framework`,
  `covering_scheme`, `cover_tradeoff`, `algebraic_rigidity`,
  `pgg_covering_correctness`); the merge starts from green and re-greens the rest
  (`card_exchange_pismc`, `dealer_bridge`).
- Everything compiles (`make -j1` / rocq-mcp per file).
- No new custom axioms beyond those already present. In particular, NO den Boer
  genus / curve axiom.
- The session wire is unchanged (Section 5a), so player/verifier duality proofs
  are reused verbatim for ALL instances. The one duality re-proof is the dealer
  commit prologue (Section 6).
- The monomorphic content readout preserves every existing instance's behavior
  (`content = id` for the position model, definitionally the old recon).
- den Boer's `'I_5` rebuild is faithful to the trick: faces (not card identities)
  reach the wire, because the dealer bakes the fixed `face` readout.
- The pre-commit rocq-audit gate passes.

## 15. Phasing (for the implementation plan)

A natural order that keeps the build green between phases:

1. Re-establish green build of the working tree (GATE 1 already greened the
   reconstruct chain).
2. `ReconPlug` carve-out + `CoveringScheme` restructure (`{ cs_plug ; cs_data ;
   cs_gap }`, `Notation cs_scheme`), drop `cs_T'`/`cs_scheme_T` and the
   recon-symmetry fields, add the `content` readout to `pgg_protocol_secret`, and
   thread `content = id` through all position-model instances,
   `cover_genus0/1/2.v`, and `dealer_bridge.v` (`G := pgg_G`). Build green.
3. Relocate `MonodromyProfile` + `run_*` to `protocol/` with `mp_plug`; keep
   plugs in `instances/`; remove protocol-to-instance imports. Build green.
4. s5x5 parity items 1-6 and `s5x5_profile`; reconcile the genus figure. Green.
5. den Boer `'I_5` rebuild: `rp_content = face` (fixed), arrangement-secret in
   `ts_encode`, the three-consec `'I_5` scheme (validity/recon/encode/correctness/
   privacy transported via `encode_bool`/`decode_bool`), the NET-NEW
   `ts_recon_perm_invariant`, `decode_bool` at recovery, and the canonical
   program replacing `five_card_pismc.v`. Delete the old genus-0 RS5
   `AlgebraicRigidity` and the stale `card_protocol.v:28` comment. Build green.
6. Input-commitment stage: NEW pgg-typed commit / recv-commit wrappers over the
   existing `pgg_dtype`/`pgg_data`; dealer commit prologue; dealer-side duality
   re-proof; den Boer `M = 2` assemble. Build green.
7. Retire wreath7 (delete files). Build green.

## 16. Open questions and risks (post-gate severities)

- HIGH: the input-commitment continuation + the dealer commit-prologue duality
  re-proof (NEW pgg-typed wrappers, not FCCommit reuse; Section 6) are
  dependent-session-type work, not mechanical.
- MEDIUM: den Boer's `'I_5` rebuild (Section 5b). Transport is mechanical, but
  the NET-NEW `ts_recon_perm_invariant` (three-consec rotation-invariance) and
  the content/encode split are real work. (Re-rated up from v3's LOW by GATE 2.)
- MEDIUM: the `ReconPlug`/`CoveringScheme` restructure breadth: it touches every
  instance rigidity file, `cover_genus0/1/2.v`, and `dealer_bridge.v`. GATE 1
  validated it is mechanical (no re-proofs; `*_perm_compatible`/`*_cs_gap`/
  `*_hurwitz` survive verbatim, `Notation` safe, dropped fields have no
  consumers), but it is broad; the risk is volume and keeping the build green
  between edits.
- LOW: reconcile the s5x5 operative genus figure (173 / gap-witness / 8) to one
  coherent number; clean the stale s5x5 genus comment
  (`rigidity_s5x5_instance.v:362-364`) and the `card_protocol.v:28` comment.
- LOW: den Boer's `encode_bool`/`decode_bool` bijection; small, reuses
  `fc_correct`.

GATE-CONFIRMED SOUND (tried and could not break): wire unchanged for
`content = id`; den Boer needs no genus/`CoveringScheme` for correctness; the
three-consec invariance over the full `Z_5` is real (not the obstruction); the
recon-symmetry drop for the retained four; the `Notation cs_scheme`; the
`cs_T'`/`cs_scheme_T` drop.
