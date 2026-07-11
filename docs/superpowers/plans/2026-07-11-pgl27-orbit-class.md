# PGL(2,7) Orbit-Class Instance + Transitivity-Privacy Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the fifth PGG instance `pgl27` (8-card scheme, bool secret = PGL(2,7) orbit-class of the heart 4-subset, coalitions of size <= 3 perfectly private) plus the reusable t-transitivity privacy bridge `transitivity_privacy.v`.

**Architecture:** Two parallel tracks (bridge | group+orbit) join at the scheme, then profile/run/secrecy/trace assemble s5-style, then Theorem A tails. Everything proved abstractly over the group; no `vm_compute` on permutations (plain `'I_8 -> 'I_8` function tables and `'F_7` arithmetic MAY vm_compute).

**Tech Stack:** Rocq 9.x + MathComp (fingroup/perm/action/primitive_action/finfield) + infotheo (fdist/proba/entropy/variation_dist) + the live pgg-smc framework. Proof iteration through rocq-mcp; `make -j1` mutex-serialized; commits through the rocq-audit gate.

**Spec:** `docs/superpowers/specs/2026-07-11-pgl27-orbit-class-design.md` (locked decisions L1-L9, D1-D8). Probe: `.local/wip/pgl_plan_probe.v` (compiles; normative for record invocations).

---

## Execution rules (read first, apply to every task)

1. **Agents and models (L9):** every proof task goes to a `rocq-prover` agent on **Opus**. Escalation only for Task 2's `pgl_3transitive`/`pgl27_card` (Opus -> `rocq:autoprove` -> Fable retry -> justified axiom) and Task 1's Theorem B (Opus -> Fable -> combinatorial fallback; NEVER an axiom).
2. **Concurrency (L6):** Tasks 1 and 2+3 run in parallel (two rocq-prover agents, one per track). Max 2 rocqworkers alive; at most ONE compile (`rocq_compile_file` or `make -j1`) running at any instant across both tracks — the orchestrator enforces the mutex by instructing each agent to compile only its own file and by staggering launches. Combined rocqworker RAM cap ~14 GB; on breach, pause one track.
3. **Rocq TDD loop per lemma:** (a) write the statement with `Admitted`, (b) `rocq_compile_file` must SUCCEED (statement typechecks = the failing-test analog: the proof obligation exists), (c) prove via the mathcomp-skills `proof-development.md` loop (`rocq_start` -> `Search` -> `rocq_step_multi` battery -> `rocq_check`), (d) replace with `Qed`, (e) `rocq_compile_file` again, (f) `rocq_assumptions` on the lemma. Batteries MUST NOT contain `lia.`/`nia.`; never `rewrite !` with arithmetic lemmas.
4. **Style:** every declaration carries exactly one H-series role tag (`@intent:` / `@composes: <lemma>` / `@main <security|correctness|architecture|bound>:`), terse declarative comment, mathcomp-skills naming (`mainSymbol_suffixes`, no metaphors). Consult per-file: Task 2/3 -> `domains/46_tuple_perm_binomial.md` + `domains/40_finset.md` + `domains/41_int_rat.md`; Task 1/7/8 -> `reference.md` section 34; stuck -> `templates.md`/`phrasebook.md`.
5. **Commits:** one checkpoint commit per completed file, through the audit gate. If Stage 2 emits the S996 token-cap sentinel, retry with `ROCQ_AUDIT_BYPASS=1 git commit ...` and note the bypass in the commit message (kim-L7 precedent).
6. **pgl_M is a Notation, never a Definition** (probe finding): `Notation pgl27_M := (@Gen_PGGTypes 2 6 pgl27_gens).` A `Definition ... : MonodromyReprType` seals away the HB `hasGenerators` mixin and `SecurityWitness R pgl27_M` stops typechecking.
7. **Agent launch prompts** must include (per CLAUDE.md): pre-built `.vo` status, exact target line ranges, section Variables in scope, a turn budget (60 turns default, max 2 full-file compilations beyond the per-lemma loop), and the 4-phase rocq-mcp workflow reminder.

## File map

| # | File | Task | Track |
|---|------|------|-------|
| 0 | `_CoqProject` (+ dir scaffold) | 0 | pre |
| 1 | `pgg-smc/reconstruct/transitivity_privacy.v` | 1 (Thm B + fiber core), 9 (Thm A) | 1 |
| 2 | `pgg-smc/instances/pgl27/pgl27_group.v` | 2 | 2 |
| 3 | `pgg-smc/instances/pgl27/pgl27_orbit.v` | 3 | 2 |
| 4 | `pgg-smc/instances/pgl27/pgl27_scheme.v` | 4 | join |
| 5 | `pgg-smc/instances/pgl27/pgl27_profile.v` | 5 | join |
| 6 | `pgg-smc/instances/pgl27/pgl27_run.v` | 6 | join |
| 7 | `pgg-smc/instances/pgl27/pgl27_secrecy.v` | 7 | join |
| 8 | `pgg-smc/instances/pgl27/pgl27_trace.v` | 8 | join |
| — | final gate | 10 | tail |

Compile order = table order. Task dependencies: 4 needs 1,2,3; 5 needs 4 (and 1's fiber core for eps=0); 6 needs 5; 7 needs 5 + 1's corollary; 8 needs 7; 9 and 10 last.

---

### Task 0: Scaffold and `_CoqProject`

**Files:** Modify: `_CoqProject`. Create: `pgg-smc/instances/pgl27/` (directory).

- [ ] **Step 0.1:** `mkdir -p pgg-smc/instances/pgl27`
- [ ] **Step 0.2:** In `_CoqProject`, add `-R pgg-smc/instances/pgl27 pgg_smc` next to the other instance `-R` lines, and append to the file list (near the other reconstruct/instance entries, respecting compile order):

```
pgg-smc/reconstruct/transitivity_privacy.v
pgg-smc/instances/pgl27/pgl27_group.v
pgg-smc/instances/pgl27/pgl27_orbit.v
pgg-smc/instances/pgl27/pgl27_scheme.v
pgg-smc/instances/pgl27/pgl27_profile.v
pgg-smc/instances/pgl27/pgl27_run.v
pgg-smc/instances/pgl27/pgl27_secrecy.v
pgg-smc/instances/pgl27/pgl27_trace.v
```

- [ ] **Step 0.3:** Regenerate the Makefile if the repo does so from `_CoqProject` (check `Makefile` header; if `coq_makefile` generated, rerun the documented command; otherwise nothing).
- [ ] **Step 0.4:** Commit: `git add _CoqProject && git commit -m "pgl27: scaffold instance directory and _CoqProject entries"` (no `.v` staged yet -> audit gate trivially passes).

---

### Task 1 (Track 1): `transitivity_privacy.v` — fiber core, Theorem B, distributional corollary

**Files:** Create: `pgg-smc/reconstruct/transitivity_privacy.v`.
**Deps:** framework `.vo`s only (all built). Nothing from Track 2.

Import block: copy from `.local/wip/pgl_plan_probe.v` (HB, ssreflect suite, `primitive_action`, `boolp reals`, infotheo `realType_ext fdist proba variation_dist`, `pgg_interface`, `pgg_sharing_framework`). Section over abstract group data — NOT over `pgl_M`:

```coq
Section transitivity_privacy.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable t : nat.
Hypothesis Htrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P.
```

- [ ] **Step 1.1 (statement + Admitted, compile):** the reusable fiber-counting core. For `k <= t` and a fixed injective k-tuple of positions, uniform-on-G pushes forward to uniform on injective k-tuples. State it in the two forms consumers need:

```coq
(** rho_tuple_fiber_card — all fibers of the k-tuple orbit map have equal size.
    @composes: uniform_ktuple_pushforward *)
Lemma rho_tuple_fiber_card (k : nat) (p q : k.-tuple 'I_N'.+1) :
  (k <= t)%N -> p \in dtuple_on k [set: 'I_N'.+1] ->
  q \in dtuple_on k [set: 'I_N'.+1] ->
  #|[set g in G | [tuple (rho g) (tnth p i) | i < k] == q]|
  = (#|G| %/ #|dtuple_on k [set: 'I_N'.+1]|)%N.
```

Strategy: `ntransitive_weak` (t -> k), transitivity makes every fiber nonempty; two nonempty fibers biject by left translation with any group element mapping one target to the other (cosets of the pointwise stabiliser). Search anchors: `ntransitive_weak`, `dtuple_on`, `atrans`, `card_orbit`, `orbit_stabilizer` in `primitive_action.v` / `action.v`.

- [ ] **Step 1.2 (prove 1.1 to Qed).**
- [ ] **Step 1.3 (statement + Admitted, compile):** Theorem B, the re-dealing privacy bridge. Abstract over the scheme data:

```coq
Section redeal.
Variable orbit_class : N'.+1.-tuple 'I_N'.+1 -> bool.
Variable deck_ok     : N'.+1.-tuple 'I_N'.+1 -> bool.
Hypothesis Hdeck_uniq : forall sh, deck_ok sh -> uniq sh.
Hypothesis Hinv : forall g sh, g \in G ->
  orbit_class [tuple tnth sh (rho g i) | i < N'.+1] = orbit_class sh.
Hypothesis Hdeck_stable : forall g sh, g \in G ->
  deck_ok [tuple tnth sh (rho g i) | i < N'.+1] = deck_ok sh.
Hypothesis Hpopulated : forall b : bool,
  exists sh, deck_ok sh /\ orbit_class sh = b.

(** ttrans_private — a t-transitive shuffle over a distinct-card deck admits,
    for every coalition of at most t positions and every target secret, a
    re-dealt valid arrangement agreeing with the coalition's exact view.
    @main security: the transitivity privacy bridge discharging ts_private. *)
Theorem ttrans_private (s1 s2 : bool) (sh : N'.+1.-tuple 'I_N'.+1)
    (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> deck_ok sh -> orbit_class sh = s1 ->
  exists sh', [/\ deck_ok sh', orbit_class sh' = s2 &
    forall i, i \in C -> tnth sh' i = tnth sh i].
End redeal.
```

Proof skeleton (validated on paper; see spec section 5): (i) from `Hpopulated` get `sh2` with class `s2`; (ii) `deck_ok` + `uniq` on an `N'.+1`-tuple over `'I_N'.+1` gives a bijection, so each coalition card value `tnth sh i` occurs at a unique position `j_i` in `sh2`; the `j_i` are distinct because the values are (injectivity of `sh` on distinct positions — the coalition positions are distinct, `uniq sh` makes their values distinct); (iii) extend both distinct partial tuples (coalition positions; the `j_i`) to distinct k-tuples with `k = #|C| <= t` and get `g \in G` with `rho g` mapping `j_i` families onto coalition positions, via `Htrans` through `ntransitive_weak`; (iv) set `sh' := [tuple tnth sh2 (rho g i) | i < N'.+1]` oriented so `tnth sh' i = tnth sh2 (rho g i) = tnth sh2 j_i = tnth sh i` for `i \in C`; fix the direction (g vs g^-1) to whatever `Hinv`/`Hdeck_stable` consume — group closure gives the inverse membership; (v) `Hinv`/`Hdeck_stable` close class and deck. If the tuple-extension bookkeeping stalls, fallback: restate with `#|C| == t` first and derive `<= t` by padding C (still no axiom).

- [ ] **Step 1.4 (prove 1.3 to Qed).** This is the HIGH-risk item; escalation ladder per execution rule 1.
- [ ] **Step 1.5 (statement + Admitted, compile):** the distributional corollary. Over `R : realType`, a product sampler and the dealt-arrangement view:

```coq
Section view_indep.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis HG : (0 < #|G|)%N.
Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.
Let P : R.-fdist (bool * gT)%type := secretP `x (`U HG).
(* view of coalition C at sample (s,g): the dealt values at C *)
Definition coalition_view (C : {set 'I_N'.+1}) : {RV P -> {ffun 'I_N'.+1 -> 'I_N'.+1}} :=
  fun u => [ffun i => if i \in C then tnth (encode u.1) (rho u.2 i) else ord0].
Definition dealt_secret : {RV P -> bool} := fun u => u.1.

(** ttrans_view_indep — the coalition view of the uniformly shuffled dealt
    arrangement is independent of the secret when the encoding is injective
    per secret and the coalition has at most t positions.
    @main security: distributional corollary of the transitivity bridge. *)
Lemma ttrans_view_indep (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> (forall b, uniq (encode b)) ->
  P |= coalition_view C _|_ dealt_secret.
End view_indep.
```

Strategy: unfold `inde_RV`; the joint at `(v, b)` factors through `secretP b * Pr_{`U HG}[view_b = v]`; show `Pr[view_b = v]` is independent of `b`: the view is determined by the injective k-tuple `(rho g i)_{i in C}`, whose law is uniform on injective k-tuples by `rho_tuple_fiber_card` (step 1.1), and composing a uniform injective position-tuple with the bijection `encode b` yields a `b`-independent law on value-tuples. Search anchors: `inde_RV`, `fdist_prod`, `fdistmap`, `Pr_fdistmap`, infotheo `proba.v` product lemmas.

- [ ] **Step 1.6 (prove 1.5 to Qed).** Fallback if the ffun-law bookkeeping stalls: prove first for `C = [set i]` singletons (all that Task 8 strictly consumes) and leave the general statement as a second lemma; the general form must still land before Task 10.
- [ ] **Step 1.7 (transitive single-point marginal, for Task 5):**

```coq
(** ttrans_point_uniform — the single-point pushforward of the uniform draw
    over a transitive permutation group is exactly uniform.
    @composes: pgl27_security *)
Lemma ttrans_point_uniform (Hpos : (0 < #|G|)%N) (s : 'I_N'.+1) :
  (0 < t)%N ->
  fdistmap (fun g : gT => rho g s) (`U Hpos) = fdist_uniform (card_ord N'.+1).
```

Wait — `` `U Hpos `` samples over ALL of gT with support G; `rho` is only defined on the morphism domain: apply `rho` as the underlying function (morphisms are total functions in mathcomp); values off G are irrelevant only if the support argument is threaded — state instead over `fdistmap (fun g => rho g s)` and prove pointwise with `fdist_uniform_supp_in/notin` splitting on `g \in G`. Prove via the k=1 case of `rho_tuple_fiber_card` (`dtuple_on 1` ~ points; `ntransitive` at 1 follows from `ntransitive_weak` since `0 < t`). Then Qed.

- [ ] **Step 1.8:** `rocq_assumptions` on `ttrans_private`, `ttrans_view_indep`, `ttrans_point_uniform` — expect boolp trio only.
- [ ] **Step 1.9:** Commit: `git add pgg-smc/reconstruct/transitivity_privacy.v _CoqProject && git commit -m "pgl27: transitivity privacy bridge (fiber core, ttrans_private, view independence)"`.

---

### Task 2 (Track 2): `pgl27_group.v` — generators, card, 3-transitivity

**Files:** Create: `pgg-smc/instances/pgl27/pgl27_group.v`.
**Deps:** framework `.vo`s; `pgl_bound.vo` (for `card_pgl2` narrative only).

- [ ] **Step 2.1 (definitions, compile):** the P^1(F_7) identification and the three generators as explicit `'I_8 -> 'I_8` tables wrapped into permutations. Point 7 is infinity; 0..6 are the field elements. Concrete images (row = input 0..7):

```coq
(* z |-> z+1        *) Definition tr_tbl := [:: 1; 2; 3; 4; 5; 6; 0; 7].
(* z |-> 3z         *) Definition sc_tbl := [:: 0; 3; 6; 2; 5; 1; 4; 7].
(* z |-> -1/z       *) Definition inv_tbl := [:: 7; 6; 3; 2; 5; 4; 1; 0].
```

(`-1/z` table check: 1->6, 2->3, 3->2, 4->5, 5->4, 6->1, 0->inf, inf->0.) Wrap each as `fun_of_tbl : 'I_8 -> 'I_8 := fun i => inord (nth 0 tbl i)`, prove `injectiveb` by a finite decision (`by apply/injectiveP; ...` or decidable check — plain 'I_8 functions, vm_compute is SAFE here, no perms), and form `{perm 'I_8}` via the `perm` constructor on the injectivity proof. Then:

```coq
Definition pgl27_gens : 3.-tuple {perm 'I_8} := [tuple tr_perm; sc_perm; inv_perm].
Notation pgl27_M := (@Gen_PGGTypes 2 6 pgl27_gens).   (* NOTATION, per rule 6 *)
Lemma pgl27_N' : pgg_N' pgl27_M = 7. Proof. by []. Qed.
```

- [ ] **Step 2.2 (Moebius function layer, compile then prove):** matrix-parameterised Moebius maps as plain functions (NO group quotients, NO HB actions):

```coq
(* moebius a b c d : 'I_8 -> 'I_8, the map z |-> (az+b)/(cz+d) on P^1(F_7),
   total via the infinity case split; requires a*d - b*c != 0. *)
Definition moebius (a b c d : 'F_7) : 'I_8 -> 'I_8 := ...
```

with the standard case split (finite point with `c*z+d != 0` -> field formula; `c*z+d == 0` -> infinity; infinity -> `a/c` or infinity when `c == 0`). Prove: `moebius_comp` (composition = matrix product, det multiplicative), `moebius_id` (identity matrix), and that each generator equals a `moebius`: `tr = moebius 1 1 0 1`, `sc = moebius 3 0 0 1` (3 is a non-square mod 7), `inv = moebius 0 (-1) 1 0` — each by finite pointwise check over 'I_8 (vm_compute-safe, these are functions).

- [ ] **Step 2.3 (Bruhat decomposition, prove):** every nonsingular Moebius map is a word in the three generators:

```coq
(** moebius_gen — every Moebius map with nonzero determinant lies in the
    subgroup generated by translation, scaling, and inversion.
    @composes: pgl27_3transitive *)
Lemma moebius_gen (a b c d : 'F_7) : a * d - b * c != 0 ->
  perm_of_moebius ... \in <<[set x | x \in pgl27_gens]>>.
```

Strategy: case `c == 0`: map is `z |-> (a/d) z + (b/d)`; `a/d` is a power of 3 ('F_7^* is cyclic generated by 3: 3,2,6,4,5,1 — provable by finite check), so the map = `tr^(b/d as nat) * sc^(log)` — realize powers via `groupX`/`groupM`. Case `c != 0`: Bruhat `(az+b)/(cz+d) = a/c - ((ad-bc)/c^2) / (z + d/c)`, i.e. `tr^{a/c} o sc^{k} o inv o tr^{d/c}` for the right scaling power k — verify the matrix identity in 'F_7 algebra (field_simp style manual rewriting; NO lia), then transport along `moebius_comp`. Group membership by `groupM`, `groupX`, `mem_gen`.

- [ ] **Step 2.4 (sharp interpolation, prove):**

```coq
(** moebius_interp — for any two distinct-point triples there is a nonsingular
    Moebius map carrying the first to the second.
    @composes: pgl27_3transitive *)
```

Strategy: classical — the unique map sending a distinct triple (x1,x2,x3) to (0,1,inf) has an explicit matrix (cross-ratio matrix); compose one such with the inverse of the other. All field algebra with case splits on infinity membership; tedious but elementary. Also prove `moebius_fix3_id`: a Moebius map fixing 0, 1, inf is the identity (gives sharpness and the card upper bound).

- [ ] **Step 2.5 (targets, prove):**

```coq
(** pgl27_3transitive — the generated monodromy group acts 3-transitively.
    @main architecture: the load-bearing transitivity hypothesis of the bridge. *)
Lemma pgl27_3transitive :
  ntransitive 3 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P.

(** pgl27_card — the shuffle group has 336 elements.
    @main bound: |PGL(2,7)| = 8*7*6. *)
Lemma pgl27_card : #|pgg_G pgl27_M| = 336.
```

`pgl27_3transitive`: unfold `ntransitive`/`dtuple_on`; given distinct triples, `moebius_interp` + `moebius_gen` produce the group element (pgg_rho is the identity inclusion so image membership is inclusion). `pgl27_card`: >= 336 by orbit-stabiliser on the triple action (3-transitivity just proved, orbit size 8*7*6); <= 336 by `moebius_fix3_id` (triple-stabiliser trivial) — or compare against `#|pgl2 'F_7| = 336` (`card_pgl2 card_Fp`, see probe tail) only as narrative. ESCALATION: if either stalls past budget, the L2 fallback is `Axiom pgl27_3transitive_ax` (and/or card) with the s5 justification template (rigidity_s5_instance.v:263) — isolated, named, `(* Naming: ... *)`-tagged, reported in Task 10.

- [ ] **Step 2.6:** `rocq_assumptions` on both targets (boolp trio, or the declared axioms). Commit: `git commit -m "pgl27: group file (generators, Bruhat closure, 3-transitivity, card 336)"` (add the file).

---

### Task 3 (Track 2): `pgl27_orbit.v` — deck, cross-ratio classifier, invariance, split, encode

**Files:** Create: `pgg-smc/instances/pgl27/pgl27_orbit.v`. **Deps:** `pgl27_group.vo`.

- [ ] **Step 3.1 (definitions, compile):**

```coq
Definition is_heart (c : 'I_8) : bool := (c < 4)%N.
Definition deck_ok (sh : 8.-tuple 'I_8) : bool := uniq sh.
Definition heart_set (sh : 8.-tuple 'I_8) : {set 'I_8} :=
  [set i | is_heart (tnth sh i)].
(* cross-ratio of an ordered distinct 4-tuple of P^1(F_7) points, valued in
   'I_8 (result is a field value 2..6 on distinct inputs; degenerate inputs
   map to a sentinel). Total function, plain 'F_7 arithmetic + infinity cases. *)
Definition cross_ratio (x1 x2 x3 x4 : 'I_8) : 'I_8 := ...
Definition equianharmonic (l : 'I_8) : bool := (l == inord 3) || (l == inord 5).
(* orbit_class: the class of the heart 4-subset, read off one fixed ordering
   (the sorted enumeration of heart_set); true = harmonic 42-orbit,
   false = equianharmonic 28-orbit. *)
Definition orbit_class (sh : 8.-tuple 'I_8) : bool := ...
```

`orbit_class` implementation: take `s := enum (heart_set sh)`; if `size s == 4`, compute `~~ equianharmonic (cross_ratio s0 s1 s2 s3)` on the four elements in enum order, else `false` (dead branch under `deck_ok`, which forces exactly 4 hearts: the 8 distinct codes contain exactly codes 0..3).

- [ ] **Step 3.2 (well-definedness, prove):** `cr_class_perm_stable` — the `equianharmonic` verdict of `cross_ratio` on a distinct 4-tuple is invariant under re-ordering the 4 points. Finite: the S3-class {3,5} vs {2,4,6} closure under the six cross-ratio transforms; provable by the 24 permutations acting on 4 symbolic points reduced to the 6 classical transforms, or directly by a finite decision over all distinct 4-tuples of 'I_8 (8*7*6*5 = 1680 cases of pure 'F_7 arithmetic — vm_compute-safe, NO perms involved: state as a boolean `forallb`-style reflection over `'I_8^4` and close with vm_compute).
- [ ] **Step 3.3 (Moebius invariance, prove):** `cr_moebius_invariant` — `cross_ratio` is unchanged under applying any of the three GENERATORS simultaneously to its four arguments (per-generator finite check over distinct 4-tuples, 3 x 1680 ground cases of table lookups + field arithmetic — vm_compute-safe). Then lift to the group:

```coq
(** orbit_class_invariant — the orbit classifier is invariant under the
    coordinate action of any group element.
    @composes: pgl27_private *)
Lemma orbit_class_invariant (g : pgg_gT pgl27_M) (sh : 8.-tuple 'I_8) :
  g \in pgg_G pgl27_M ->
  orbit_class [tuple tnth sh (@pgg_rho pgl27_M g i) | i < 8] = orbit_class sh.
```

Lift strategy: per-generator invariance + induction over the generated group (`gen_prodgP` / subgroup-generated induction: the invariant property is closed under multiplication and inverses); heart_set of the permuted tuple = preimage of heart_set under rho g, and the classifier's value transports along `cr_moebius_invariant` + `cr_class_perm_stable` (the enum ordering changes — this is exactly why 3.2 exists).

- [ ] **Step 3.4 (deck stability + populated, prove):** `deck_stable` (permuting positions preserves `uniq` — `map_inj_uniq`-style, tuple lemma) and:

```coq
Lemma orbit_populated (b : bool) :
  exists sh : 8.-tuple 'I_8, deck_ok sh /\ orbit_class sh = b.
```

by exhibiting two explicit ground tuples (hearts 0..3 placed at a harmonic 4-subset for `true`, an equianharmonic one for `false` — e.g. try positions {0,1,2,3}: cr(0,1,2,3) computes to a definite value; adjust to hit both classes; ground `by vm_compute`-closable).

- [ ] **Step 3.5 (encode, prove):** `orbit_encode : bool -> 8.-tuple 'I_8` := the two ground tuples of 3.4; `orbit_encodeK : orbit_class (orbit_encode s) = s` and `orbit_encode_deck : deck_ok (orbit_encode s)` — both `by case; vm_compute` style ground checks.
- [ ] **Step 3.6 (split, prove):**

```coq
(** orbit_class_split — the seventy heart-placements split 42 harmonic vs 28
    equianharmonic. @main bound: the 42/28 orbit sizes. *)
Lemma orbit_class_split :
  #|[set S : {set 'I_8} | (#|S| == 4) && <class-of-S-as-true>]| = 42
  /\ #|[set S : {set 'I_8} | (#|S| == 4) && <class-of-S-as-false>]| = 28.
```

(phrase the classifier on subsets: factor `orbit_class` through a `subset_class : {set 'I_8} -> bool` so this statement is natural — do that refactor in 3.1). Ground finite count over 256 subsets, no perms: `by vm_compute` expected to close; if the finset enum does not reduce, fall back to counting over `4.-tuples` or reflect through `enum`. This lemma is narrative (not consumed by ts_private) — if it resists past 10 turns, mark it deferred-to-Task-10 rather than blocking the track.

- [ ] **Step 3.7:** `rocq_assumptions` on `orbit_class_invariant`, `orbit_populated`, `orbit_encodeK`. Commit: `git commit -m "pgl27: orbit file (classifier, invariance, 42/28 split, encode)"`.

---

### Task 4 (Join): `pgl27_scheme.v` — ThresholdScheme + ReconPlug

**Files:** Create: `pgg-smc/instances/pgl27/pgl27_scheme.v`. **Deps:** Tasks 1, 2, 3 `.vo`s.

- [ ] **Step 4.1 (compile whole file with 2 Admitted, then prove):** exactly the probe shapes (`.local/wip/pgl_plan_probe.v` is normative — same field order, same `@` forms), with Variables replaced by the Task 2/3 artifacts:

```coq
Definition orbit_valid (s : bool) (sh : 8.-tuple 'I_8) : Prop :=
  deck_ok sh /\ orbit_class sh = s.

Lemma orbit_correct s sh : orbit_valid s sh -> orbit_class sh = s.
Proof. by move=> [_ ->]. Qed.

(** pgl27_private — coalition privacy for the orbit scheme via the bridge.
    @main security: any <= 3 coalition view is re-dealable to either secret. *)
Lemma pgl27_private (s1 s2 : bool) (sh : 8.-tuple 'I_8) (C : {set 'I_8}) :
  (#|C| < 3.+1)%N -> orbit_valid s1 sh ->
  exists sh', orbit_valid s2 sh' /\
    (forall i, i \in C -> tnth sh' i = tnth sh i).
Proof. (* instantiate ttrans_private with pgl27_3transitive,
          orbit_class_invariant, deck_stable, orbit_populated;
          #|C| < 4 <-> #|C| <= 3 by ltnS *) ... Qed.

Lemma orbit_encode_valid s : orbit_valid s (orbit_encode s).
Proof. by split; [exact: orbit_encode_deck | exact: orbit_encodeK]. Qed.

Definition orbit_scheme : ThresholdScheme bool 'I_8 :=
  @MkThresholdScheme bool 'I_8 (pgg_N' pgl27_M) 3
    orbit_valid orbit_class orbit_encode
    orbit_correct pgl27_private orbit_encode_valid.

(** orbit_recon_invariant — reconstruction is invariant under the coordinate
    action of the shuffle group. @composes: pgl27_run_recovers *)
Lemma orbit_recon_invariant :
  @ts_recon_perm_invariant _ (pgg_G pgl27_M) bool 'I_8
    orbit_scheme (fun g => @pgg_rho pgl27_M g).
Proof. (* from orbit_class_invariant + orbit_valid's second conjunct *) ... Qed.

Definition pgl27_plug : ReconPlug pgl27_M bool :=
  @MkReconPlug pgl27_M bool orbit_scheme id
    (fun g => @pgg_rho pgl27_M g) orbit_recon_invariant.
```

The bridge instantiation needs the morphism-vs-inclusion plumbing: `transitivity_privacy` section takes `rho : {morphism G >-> {perm 'I_N'.+1}}`; instantiate with `@pgg_rho pgl27_M` at `N' := 7`, `t := 3`, threading `pgl27_3transitive` (note the bridge's Htrans is over `rho @* G` exactly as Task 2 states it).

- [ ] **Step 4.2:** `rocq_assumptions pgl27_private` — boolp trio (+ Task 2 axioms if the fallback fired). Commit: `git commit -m "pgl27: threshold scheme and plug (privacy via transitivity bridge)"`.

---

### Task 5 (Join): `pgl27_profile.v` — PI, SecurityWitness (eps = 0), MonodromyProfile

**Files:** Create: `pgg-smc/instances/pgl27/pgl27_profile.v`. **Deps:** Task 4 + Task 1 (`ttrans_point_uniform`).

- [ ] **Step 5.1 (compile with Admitted, then prove):** probe Decision 3 is normative:

```coq
Lemma pgl27_starts_uniq : uniq (ord_tuple 8).
Proof. by rewrite val_ord_tuple enum_uniq. Qed.   (* mirror s5_profile.v:30 *)

Definition pgl27_PI : PGGInterface pgl27_M :=
  @MkPGGI pgl27_M 7 (ord_tuple 8) pgl27_starts_uniq.

Section witness.
Variable R : realType.
Lemma pgl27_G_pos : (0 < #|pgg_G pgl27_M|)%N. Proof. exact: cardG_gt0. Qed.
Definition pgl27_rho_dist : R.-fdist {perm 'I_8} := `U pgl27_G_pos.

(** pgl27_point_uniform — the single-card pushforward of the uniform shuffle
    is exactly uniform. @composes: pgl27_security *)
Lemma pgl27_point_uniform (s : 'I_8) :
  fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist
  = fdist_uniform (card_ord 8).
Proof. (* ttrans_point_uniform at t=3 via pgl27_3transitive; pgg_rho is the
          identity inclusion so (fun g => rho g s) = (fun g => g s) *) ... Qed.

Lemma pgl27_se_exact : forall s : 'I_8,
  var_dist (fdistmap (fun sigma : {perm 'I_8} => sigma s) pgl27_rho_dist)
           (fdist_uniform (card_ord 8)) = 0.
Proof. (* rewrite pgl27_point_uniform; var_dist_id-style: distance of a
          distribution to itself is 0 (Search var_dist refl) *) ... Qed.

Definition pgl27_security : SecurityWitness R pgl27_M :=
  @MkSecurityWitness R pgl27_M 0 0 pgl27_rho_dist pgl27_sw_bound
    (Some (@MkSecurityExact R pgl27_M pgl27_rho_dist 0 pgl27_se_exact)) None.
(* pgl27_sw_bound: <= 0 from the = 0 exact lemma, lexx after rewrite *)

Definition pgl27_profile : MonodromyProfile R :=
  @MkMonodromyProfile R pgl27_M bool pgl27_PI pgl27_security pgl27_plug.
End witness.

Lemma run_k_pgl27 (R : realType) : run_k (pgl27_profile R) = 4.
Proof. by []. Qed.   (* ts_k = ts_k'.+1 = 4; coalitions <= 3 are private *)
```

(Check `run_k`'s definition against `pgg_monodromy_profile.v` before asserting 4 — s5's `run_k = 5` with `ts_k' = 4`; if `run_k` unfolds differently for this plug, state whatever the true value is and document the k/k' convention per spec section 1.)

- [ ] **Step 5.2:** `rocq_assumptions` on `pgl27_security` fields. Commit: `git commit -m "pgl27: profile (PI, exact eps=0 security witness, MonodromyProfile)"`.

---

### Task 6 (Join): `pgl27_run.v` — dealer run, endpoints, run_recovers

**Files:** Create: `pgg-smc/instances/pgl27/pgl27_run.v`. **Deps:** Task 5. Template: `s5_run.v` line-for-line at N = 8.

- [ ] **Step 6.1 (definitions, compile):** mirror `s5_run.v`: `pgl27_players : seq 'I_8` as the 8 explicit `@Ordinal 8 k isT`; `pgl27_dealer_run s w0 := dealer_with_input_encoding pgl27_PI (fun _ => tnth (ts_encode orbit_scheme s)) [:: w0] [::] pgl27_players 0`; `pgl27_saprocs` = dealer + verifier + 8 `exchange_player`s (10 procs, ids 0..9); `pgl27_procs` erased.
- [ ] **Step 6.2 (terminates, prove):** `pgl27_run_terminates : (run_interp FUEL (pgl27_procs s w0)).1 = nseq 10 Finish` — start `FUEL := 220` (s5 used 150 for 7 procs); if vm_compute yields a non-Finish residue, raise fuel until it closes and freeze the value.
- [ ] **Step 6.3 (endpoints, prove):** `pgl27_verifier_endpoints` (abstract-content form mirroring `s5_verifier_endpoints` with symbolic `g`, `w0`, `st`) then `pgl27_endpoints` and `pgl27_endpoints_size` exactly as s5 (the `s5_players = enum 'I_5` step becomes `pgl27_players = enum 'I_8` via `inj_map val_inj` + `val_enum_ord`).
- [ ] **Step 6.4 (recovers, prove):**

```coq
(** pgl27_run_recovers — the executed run's endpoints reconstruct the dealt
    orbit secret for any cut in the group.
    @main correctness: end-to-end recovery over the piSMC run. *)
Lemma pgl27_run_recovers (s : bool) (w0 : pgg_gT pgl27_M) :
  w0 \in pgg_G pgl27_M ->
  ts_recon orbit_scheme
    (tcast (pgl27_endpoints_size s w0)
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp FUEL (pgl27_procs s w0)).2 1)))) = s.
```

Proof mirrors `s5_run_recovers` but SIMPLER: instead of s5's inline sum-mod Hinv, use `orbit_recon_invariant` directly with `ts_encode_valid` (`orbit_encode_valid`); the endpoint-tuple equality bookkeeping (`tcastE`, `tnth_mktuple`, `nth_map`) is verbatim s5.

- [ ] **Step 6.5:** `rocq_assumptions pgl27_run_recovers`. Commit: `git commit -m "pgl27: piSMC run (10-proc dealer run, endpoints, run_recovers)"`.

---

### Task 7 (Join): `pgl27_secrecy.v` — view independence

**Files:** Create: `pgg-smc/instances/pgl27/pgl27_secrecy.v`. **Deps:** Tasks 1, 5.

- [ ] **Step 7.1 (compile, prove):** instantiate the Task 1 corollary at the instance:

```coq
Section secrecy. Variable R : realType.
Definition pgl27P : R.-fdist (bool * pgg_gT pgl27_M)%type :=
  fdist_uniform (card_bool) `x (`U (pgl27_G_pos)).
Definition pgl27_secret : {RV pgl27P -> bool} := fun u => u.1.
Definition pgl27_view (C : {set 'I_8}) : {RV pgl27P -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then
              tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i) else ord0].

(** pgl27_view_indep — any <= 3 coalition's view of the shuffled dealt
    arrangement is independent of the orbit secret.
    @main security: instance view independence from the bridge corollary. *)
Lemma pgl27_view_indep (C : {set 'I_8}) : (#|C| <= 3)%N ->
  pgl27P |= pgl27_view C _|_ pgl27_secret.
Proof. (* ttrans_view_indep at t := 3, Htrans := pgl27_3transitive,
          encode := orbit_encode, uniq by orbit_encode_deck *) ... Qed.
End secrecy.
```

Alignment obligations the agent must resolve here (not silently): the corollary's `coalition_view`/sampler must be DEFINITIONALLY the instance's (define `pgl27_view` as a specialization of `coalition_view` if the shapes drift; adjust Task 1's section variables if a mismatch is found and recompile Track 1 FIRST — that is a plan-defect checkpoint, see Task 10 rule).

- [ ] **Step 7.2:** `rocq_assumptions pgl27_view_indep`. Commit: `git commit -m "pgl27: coalition view independence (secrecy file)"`.

---

### Task 8 (Join): `pgl27_trace.v` — executed-trace secrecy

**Files:** Create: `pgg-smc/instances/pgl27/pgl27_trace.v`. **Deps:** Tasks 6, 7. Template: `s5_trace.v`.

- [ ] **Step 8.1 (abstract-leaf run, prove):** mirror `s5_trace.v`'s Section `abstract_leaf` at N = 8: `content_of` reuse (it is generic over N — import it if exported from s5_trace, else re-define locally with the same body), `pgl27_aprocs_abs` over abstract readout `g : 'I_8 -> 'I_8` and identity cut, `pgl27_rho1_index`, and EIGHT per-player projection lemmas `pgl27_abs_p0 .. pgl27_abs_p7`, each `rewrite /pgl27_aprocs_abs -[in RHS](pgl27_rho1_index (@Ordinal 8 K isT)); vm_compute; reflexivity`.
- [ ] **Step 8.2 (sampler + trace RV, compile):** here the run is over the SECRET-dealt readout (not additive tape): sampler := `pgl27P` from Task 7 restricted to identity cut? NO — the executed run's cut is the shuffle. Model: the run at sample `u = (s, g)` deals `fun _ => tnth (orbit_encode s)` with cut `w0 := g` — i.e. reuse the CONCRETE run from Task 6, not the abstract-leaf identity-cut run. Define:

```coq
Definition pgl27_player_trace (i : 'I_8) : {RV pgl27P -> 'I_8} :=
  fun u => content_of (nth [::] (run_interp FUEL (pgl27_procs u.1 u.2)).2 (2 + i)).
```

and prove `pgl27_player_trace_E (i) : pgl27_player_trace i = (fun u => tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 (tnth (pi_starts pgl27_PI) i)))` — the per-player vm_compute pattern of 8.1 BUT with the cut symbolic; if vm_compute stalls on the symbolic cut, follow s5's exact factoring (abstract the whole readout `fun i => tnth (orbit_encode s) (rho g i)` as the leaf `g`-function of `pgl27_aprocs_abs`, then instantiate — this is what the abstract_leaf section exists for; see the interp-trace-abstract-leaves pattern).

- [ ] **Step 8.3 (per-player trace secrecy, prove):**

```coq
(** pgl27_trace_secrecy — a single corrupted player's executed trace leaves the
    secret's conditional entropy unchanged.
    @main security: executed-trace secrecy via the bridge, coalition size 1. *)
Lemma pgl27_trace_secrecy (i : 'I_8) :
  `H( pgl27_secret | pgl27_player_trace i ) = `H `p_ pgl27_secret.
Proof.
(* trace_secrecy_of_view with view := the singleton-coalition view [set start_i]
   (tnth pi_starts i), trace_of := the ffun-to-point projection f |-> f start_i,
   view_of := the point-to-ffun injection; cancel holds on the masked ffun;
   independence := pgl27_view_indep [set start_i] (cards1 <= 3). *)
... Qed.
```

Note `trace_of`/`view_of` must cancel ON THE VIEW'S IMAGE: with the Task 7 masked-ffun view, `view_of (trace_of v) = v` needs the mask structure — if the ffun round-trip resists, change the singleton view to the bare point RV (`fun u => tnth ... (rho u.2 start_i)`) derived from `pgl27_view` via `inde_RV_comp` (s5_share_indep pattern, s5_trace.v:175-182) and take `trace_of := id`.

- [ ] **Step 8.4 (coalition-trace corollary, prove — the beyond-s5 statement):** for any `C` with `#|C| <= 3`, the coalition's JOINT trace tuple is secrecy-preserving: state over the ffun view directly (`trace_of := id`) — this is immediate from `pgl27_view_indep` + `leakage_of_view_indep`-style transport (same keystone with id/id). Name: `pgl27_coalition_trace_secrecy`, tag `@main security:`.
- [ ] **Step 8.5:** `rocq_assumptions` on both secrecy lemmas. Commit: `git commit -m "pgl27: executed-trace secrecy (per-player and <=3 coalition)"`.

---

### Task 9 (Tail): Theorem A in `transitivity_privacy.v`

**Files:** Modify: `pgg-smc/reconstruct/transitivity_privacy.v` (append a section).

- [ ] **Step 9.1 (statement + Admitted, compile):**

```coq
Section monotone_ramp.
Context {R : realType} {U : finType} {P : R.-fdist U}.
Variables (secretT viewT : finType) (secret : {RV P -> secretT}).
Variable fullview : {RV P -> viewT}.
Variable proj : viewT -> viewT.   (* sub-view = deterministic reduction *)

(** view_mutual_info_le — a deterministic reduction of the view cannot
    increase mutual information with the secret.
    @main bound: the monotone leakage ramp making (k,T) well-defined. *)
Lemma view_mutual_info_le : ...
End monotone_ramp.
```

Exact statement: `mutual_info` of the joint `(secret, proj `o fullview)` <= that of `(secret, fullview)` — match infotheo's `mutual_info` API (it is stated on joint fdists; build the joints with `fdistmap` of the pair RVs; the Markov chain `secret -> fullview -> proj view` feeds `data_processing_inequality` at entropy.v:1634; check its exact `markov_chain` premise shape with `rocq_query About` FIRST and mold the statement to minimize transport). Position-subset monotonicity (`A \subset B`) is the corollary: the `A`-mask is a deterministic function of the `B`-mask (proj := re-masking ffun). Non-gating: if the fdist plumbing exceeds budget, land the DPI-instantiation lemma alone and note the subset corollary as future work in the file header — but the theorem itself must be Qed (spec L4 keeps it in scope).

- [ ] **Step 9.2 (prove, Qed, assumptions).** Commit: `git commit -m "pgl27: Theorem A monotone leakage ramp (DPI at RV level)"`.

---

### Task 10 (Final gate)

- [ ] **Step 10.1:** full-chain build, serialized: `make -j1 pgg-smc/instances/pgl27/pgl27_trace.vo` (pulls the whole dependency chain); then `make -j1 pgg-smc/reconstruct/transitivity_privacy.vo` if not already fresh. Expected: clean.
- [ ] **Step 10.2:** axiom report: `rocq_assumptions` on `ttrans_private`, `pgl27_private`, `pgl27_run_recovers`, `pgl27_trace_secrecy`, `pgl27_coalition_trace_secrecy`, `pgl27_3transitive`, `pgl27_card`. Acceptance: boolp trio (funext/propext/cid) everywhere, plus AT MOST the two L2 justified axioms; anything else = defect, fix before proceeding.
- [ ] **Step 10.3:** deferred items check: `orbit_class_split` landed (3.6)? Theorem A's subset corollary? If deferred, either close now (one bounded attempt each) or document in the spec-note status update.
- [ ] **Step 10.4:** style: run `/mathcomp-review` over the 8 files (fan-out `mathcomp-style-auditor`); fix findings; recompile touched files (`make -j1`, one at a time).
- [ ] **Step 10.5:** memory + docs: update `project_pgg_instance_scope` memory (pgl27 is the fifth in-scope instance); prepend a status line to `pgg-smc/notes/20260702-114631-pgl27-orbit-class-ROCQ-formalization-spec.md` ("Implemented 2026-07-1x, see docs/superpowers/plans/2026-07-11-pgl27-orbit-class.md"); write a completion memory (axiom outcome for pgl_3transitive, any deferred items).
- [ ] **Step 10.6:** final commit of any Task-10 fixes: `git commit -m "pgl27: final gate (style fixes, axiom report, docs)"`.

**Plan-defect rule (goal condition):** if during execution a task hits a TYPE-LEVEL mismatch between two tasks' artifacts (e.g. Task 7's view vs Task 1's corollary) that a local fix cannot resolve, that is a plan defect: STOP the affected track, record the defect in this plan file under a `## Defects` heading, fix the plan, and only then resume. Proof difficulty is NOT a plan defect — it has escalation ladders.
