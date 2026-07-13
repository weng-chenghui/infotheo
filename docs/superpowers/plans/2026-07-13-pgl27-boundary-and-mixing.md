# pgl27 Boundary Closure + Mixing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fill the last three claim-matrix cells of the exact-shuffle model, commit the claim-boundary note, and prove the in-kernel L-word mixing bound `pgl27_word_mixing` (with `pgl27_card` as a load-bearing byproduct) plus its corollaries.

**Architecture:** Part 1 adds bounded corollaries to existing pgl27 files. Part 2 is a docs-only note. Part 3 is a new `pgl27_mixing.v` built with the two-layer technique: a nat-table/binary-N ground layer discharged by `vm_compute`, bridged to `rho_from_words_weighted` by a fiber-counting induction. Spec: `docs/superpowers/specs/2026-07-13-pgl27-boundary-and-mixing-design.md` (audited twice; L = 200 frozen by exact integer probe, 2.9x margin).

**Tech Stack:** Rocq + MathComp 2.4.0, infotheo fdist/proba/variation_dist, Stdlib `BinNat` (`N`) for the walk arithmetic, rocq-mcp for all interactive checking.

**Non-negotiable execution rules (project CLAUDE.md + session lessons):**
- `make -j1` only; ONE rocqworker; NO parallel prover agents.
- Never `rewrite !arith-lemma`; `%N` discipline inside `ring_scope`.
- `lia`/`zify` only as last-resort scalar-leaf fallback (landed `five_card_kim.v` precedent); prefer `N` morphism lemmas.
- rocq-mcp 4-phase workflow; PREAMBLE-mode `rocq_start` (position mode times out on heavy pgl27 files); `Print Assumptions` via `rocq compile` scratch file with the `_CoqProject` `-R` flags, never via `rocq_query`.
- Every non-`Local` declaration carries exactly one role tag (`@intent:` / `@composes:` / `@main <label>:`); `Local` escapes the gate.
- Never `vm_compute` on perms, `{set {perm 'I_8}}`, or any enumeration of the 40320-element perm type or the 16.7M-element tuple type. All computation at nat-table / binary-N level.

**Key verified API facts (from the two audits; do not re-derive):**
- `pgg_weighted_words.v:42-54`: section vars `N''` (N = N''.+2), `m` (Tg = m.+1), `L`, `sigmas : Tg.-tuple {perm 'I_N}`, `W : R.-fdist 'I_Tg`. For pgl27: `N'' := 6`, `m := 4`, `L := 200`.
- `rho_from_words_weighted := fdistmap (word_eval M) word_weighted : R.-fdist {perm 'I_N}` (:64); `fiber_prob_weighted : rho_from_words_weighted g = \sum_(w in fiber_weighted g) word_weighted w` (:88); `endpoint_dist_weighted s := fdistmap (fun sigma => sigma s) rho_from_words_weighted` (:99); `rho_weighted_is_uniform` (:142) collapses uniform-W to `rho_from_words`; `fiber_prob` (pgg_collusion_bound.v:575) gives `#|fiber g|%:R / (Tg^L)%:R`; the two `fdist_uniform` witnesses `card_word_L` vs `card_word_L'` are bridged by `eq_irrelevance`.
- `word_eval w = \prod_(i < L) tnth sigmas (tnth w i)` (pgg_interface.v:163) — left-to-right; last-letter split via `big_ord_recr`: `fiber_L(g) = union_j rcons-image of fiber_{L-1}(g * (g_j)^-1)`.
- `var_dist P Q = \sum_a |P a - Q a|` (variation_dist.v:33, FULL L1); `var_dist_fdistmap` (pgg_collusion_bound.v:73) is the pushforward monotonicity; `leq_var_dist` (variation_dist.v:51).
- `gen_prodgP` (fingroup.v:2094): `x \in <<A>>` iff x is a `\prod` of elements of A itself (no inverses needed).
- `pgl27_point_uniform` (pgl27_profile.v:68-74): full fdist equality for the single-point pushforward of the uniform shuffle.
- `ttrans_view_indep_deck` (transitivity_privacy.v:833) generic over `secretP`; `uniform_deckP`/`uniform_deck_view` at :819-827; alldecks instance style at pgl27_secrecy.v:198-237.
- `pgl27_abs_p0..p7`/`pgl27_full_p0..p7` (pgl27_trace.v:55-235) generic over readout g AND cut w0; at `w0 := 1%g` the readout index reduces by `morph1` + `perm1` with no membership premise; `pi_starts pgl27_PI = ord_tuple 8`.
- `pgl27_procs_deck sh w0` (pgl27_run.v:~107) already deals an arbitrary deck.

---

### Task 1: Part 1 — the three residual cells (commit 1)

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_secrecy.v` (append in section)
- Modify: `pgg-smc/instances/pgl27/pgl27_trace.v` (append in section)
- Modify: `pgg-smc/instances/pgl27/pgl27_recovery.v` (append)

- [ ] **Step 1.1 (cell: prior-generic + marginal identification, pgl27_secrecy.v).** Append inside `Section pgl27_secrecy`:

```coq
(** pgl27_view_indep_deck_prior — for every secret prior, a dealer dealing a
    uniform valid deck of the secret's class gives, with no further shuffle,
    every coalition of at most three cards a view independent of the secret.
    @main security: prior-free representative-free all-decks privacy. *)
Lemma pgl27_view_indep_deck_prior (secretP : R.-fdist bool)
    (C : {set 'I_8}) : (#|C| <= 3)%N ->
  uniform_deckP secretP (R:=R) pgl27_class_decks_pos
  |= uniform_deck_view secretP pgl27_class_decks_pos C
  _|_ ((fun u => u.1)
        : {RV (uniform_deckP secretP pgl27_class_decks_pos) -> bool}).
Proof.
move=> HC.
exact: (ttrans_view_indep_deck pgl27_3transitive secretP pgl27_G_pos
  (fun sh H => H) orbit_class_invariant deck_stable
  pgl27_class_decks_pos HC).
Qed.

(** pgl27_decks_pos — the valid decks form a nonempty set.
    @composes: pgl27_deck_marginal *)
Lemma pgl27_decks_pos : (0 < #|[set sh : 8.-tuple 'I_8 | deck_ok sh]|)%N.
Proof.
by apply/card_gt0P; exists (orbit_encode false); rewrite inE orbit_encode_deck.
Qed.

(** pgl27_deck_marginal — at the class-proportional prior the dealt-deck
    marginal of the shuffle-free dealer is uniform over ALL valid decks.
    @main security: the uniform-over-valid-decks reading of the dealer. *)
Lemma pgl27_deck_marginal (secretP : R.-fdist bool) :
  (forall s : bool,
     secretP s = #|class_decks orbit_class deck_ok s|%:R
                 / #|[set sh : 8.-tuple 'I_8 | deck_ok sh]|%:R :> R) ->
  fdistmap (fun u : bool * 8.-tuple 'I_8 => u.2)
    (uniform_deckP secretP (R:=R) pgl27_class_decks_pos)
  = `U pgl27_decks_pos.
```

Proof route for `pgl27_deck_marginal` (develop interactively): `fdist_ext => sh; rewrite fdistmapE fdist_uniform_supp*`; the preimage sum over `bool * deck` pairs with second component `sh` has exactly two summands (s = true, false); `fdist_prodE` gives `secretP s * (`U (pgl27_class_decks_pos s)) sh`; the class-conditional factor is `1/#|class_decks s|` when `orbit_class sh = s` and 0 otherwise (`fdist_uniform_supp_in/notin` with membership `inE`: `deck_ok sh && (orbit_class sh == s)`), so for a valid `sh` exactly ONE summand survives and equals `(#|class_cs|/#|valid|) * (1/#|class_cs|) = 1/#|valid|` (cancel with `mulrA mulVf`, nonzero cardinals via `pnatr_eq0`/`card_gt0P` from `Hpop`); for invalid `sh` both summands vanish and `fdist_uniform_supp_notin` gives 0. No numeric cardinalities are ever computed — everything symbolic. If summing over the pair type resists, use `partition_big` on `u.1` or `big_pair`/`sum over bool = big_bool`.

- [ ] **Step 1.2 (cell: shuffle-free trace, pgl27_trace.v).** Append inside `Section pgl27_trace_sec` (after the alldecks block):

```coq
(** pgl27P_deck — the shuffle-free all-decks joint law: a uniform orbit
    secret and a uniform valid deck of its class, no cut.
    @intent: the shuffle-free dealer sample space of the executed run. *)
Definition pgl27P_deck : R.-fdist (bool * 8.-tuple 'I_8) :=
  uniform_deckP (fdist_uniform card_bool) (R:=R) pgl27_class_decks_pos.

(** pgl27_deck_secret — the dealt orbit-class secret component.
    @intent: the orbit-secret random variable of the shuffle-free run. *)
Definition pgl27_deck_secret : {RV pgl27P_deck -> bool} := fun u => u.1.

(** pgl27_deck_trace — player i's executed-trace content when the sampled
    deck is dealt at the identity cut.
    @intent: single-player executed trace of the shuffle-free run. *)
Definition pgl27_deck_trace (i : 'I_8) : {RV pgl27P_deck -> 'I_8} :=
  fun u =>
    content_of
      (nth [::] (run_interp pgl27_fuel (pgl27_procs_deck u.2 1%g)).2 (2 + i)).

(** pgl27_deck_trace_E — the shuffle-free player trace is the dealt card at
    the player's own position.
    @composes: pgl27_deck_trace_secrecy *)
Lemma pgl27_deck_trace_E (i : 'I_8) :
  pgl27_deck_trace i = (fun u => tnth u.2 i).
```

Proof: `boolp.funext => u; rewrite /pgl27_deck_trace pgl27_procs_deck_abs`; 8-way `case: i` split; branch k rewrites `(pgl27_abs_pk (tnth u.2) 1%g) tnth_ord_tuple morph1 perm1` then `congr`/`val_inj` as in `pgl27_alldecks_trace_E` (pgl27_trace.v, alldecks block). If `morph1` does not fire on `@pgg_rho pgl27_M 1%g`, try plain `by []` (rho is the identity inclusion, so `rho 1 x` may be convertible to `x`) or `permE`/`perm1` variants via `rocq_step_multi`.

```coq
(** pgl27_deck_point_indep — one player's dealt card under the shuffle-free
    dealer is independent of the secret.
    @composes: pgl27_deck_trace_secrecy *)
Lemma pgl27_deck_point_indep (i : 'I_8) :
  pgl27P_deck |= (fun u => tnth u.2 i) _|_ pgl27_deck_secret.
Proof.
have Hcard : (#|[set i]| <= 3)%N by rewrite cards1.
have Hview := pgl27_view_indep_deck R (C := [set i]) Hcard.
have -> : (fun u : bool * 8.-tuple 'I_8 => tnth u.2 i)
        = (fun f : {ffun 'I_8 -> 'I_8} => f i)
          `o uniform_deck_view (R:=R) (fdist_uniform card_bool)
               pgl27_class_decks_pos [set i].
  by apply: boolp.funext => u;
     rewrite /comp_RV /uniform_deck_view ffunE in_set1 eqxx.
exact: (inde_RV_comp (fun f : {ffun 'I_8 -> 'I_8} => f i) Hview).
Qed.

(** pgl27_deck_trace_secrecy — a single corrupted player's executed trace of
    the shuffle-free run leaves the secret's conditional entropy equal to its
    plain entropy.
    @main security: shuffle-free executed-trace secrecy. *)
Lemma pgl27_deck_trace_secrecy (i : 'I_8) :
  `H( pgl27_deck_secret | pgl27_deck_trace i ) = `H `p_ pgl27_deck_secret.
Proof.
apply: (trace_secrecy_of_view (view := (fun u => tnth u.2 i))
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_deck_trace_E.
- by [].
- exact: pgl27_deck_point_indep i.
Qed.

(** pgl27_deck_coalition_trace — the coalition's joint executed-trace record
    of the shuffle-free run.
    @intent: the coalition's joint executed trace, ord0 outside C. *)
Definition pgl27_deck_coalition_trace (C : {set 'I_8}) :
    {RV pgl27P_deck -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then pgl27_deck_trace i u else ord0].

(** pgl27_deck_coalition_trace_E — the coalition's joint executed trace of
    the shuffle-free run equals its shuffle-free coalition view.
    @composes: pgl27_deck_coalition_secrecy *)
Lemma pgl27_deck_coalition_trace_E (C : {set 'I_8}) :
  pgl27_deck_coalition_trace C
  = uniform_deck_view (R:=R) (fdist_uniform card_bool)
      pgl27_class_decks_pos C.
Proof.
apply: boolp.funext => u; apply/ffunP => i.
rewrite /pgl27_deck_coalition_trace /uniform_deck_view !ffunE.
case: ifP => // _.
by rewrite (pgl27_deck_trace_E i).
Qed.

(** pgl27_deck_coalition_secrecy — the joint executed trace of any coalition
    of at most three cards under the shuffle-free dealer leaves the secret's
    conditional entropy equal to its plain entropy.
    @main security: shuffle-free coalition executed-trace secrecy. *)
Lemma pgl27_deck_coalition_secrecy (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  `H( pgl27_deck_secret | pgl27_deck_coalition_trace C )
  = `H `p_ pgl27_deck_secret.
Proof.
move=> HC.
apply: (trace_secrecy_of_view
          (view := uniform_deck_view (R:=R) (fdist_uniform card_bool)
                     pgl27_class_decks_pos C)
          (trace_of := id) (view_of := id)).
- by rewrite pgl27_deck_coalition_trace_E.
- by [].
- exact: (pgl27_view_indep_deck R (C:=C) HC).
Qed.
```

- [ ] **Step 1.3 (cell: sub-6 ambiguity, pgl27_recovery.v).** Append:

```coq
(** pgl27_reveal_ambiguous — for every revealed position set of at most six
    positions there are two valid decks of opposite orbit classes agreeing on
    all revealed positions.
    @main security: at most six revealed cards never determine the orbit
    class, for every choice of the revealed set. *)
Lemma pgl27_reveal_ambiguous (D : {set 'I_8}) : (#|D| <= 6)%N ->
  exists sh1 sh2 : 8.-tuple 'I_8,
    [/\ deck_ok sh1, deck_ok sh2, orbit_class sh1 != orbit_class sh2 &
        {in D, forall i, tnth sh1 i = tnth sh2 i}].
Proof.
move=> HD.
have Hc : (2 <= #|~: D|)%N.
  by rewrite cardsCs setCK; move: HD; rewrite -(cardsC D) card_ord ... 
have /card_gt1P[p [q [Hp Hq npq]]] : (1 < #|~: D|)%N := ...
have [sh1 [sh2 [Hok1 Hok2 Hcl Hagree]]] := pgl27_six_reveal_ambiguous npq.
exists sh1, sh2; split=> // i iD.
apply: Hagree.
- by apply: contraTneq iD => ->; rewrite -in_setC ... 
- ...
Qed.
```

The two `...` blocks are arithmetic/set plumbing to develop interactively: `#|~:D| = 8 - #|D| >= 2` via `cardsC` (`#|D| + #|~:D| = #|T|`) and `leq_subRL`-style steps (NO `!` rewrites); `card_gt1P` yields the distinct pair with memberships `Hp Hq : _ \in ~: D`; the agreement premises `i != p`, `i != q` follow from `i \in D` vs `p \in ~: D` (`contraTneq` + `in_setC`). Check the exact shape of `card_gt1P` with `rocq_query "About card_gt1P."` (it may produce `exists x y` unpacked differently).

- [ ] **Step 1.4:** Rebuild: `rm -f pgg-smc/instances/pgl27/pgl27_secrecy.vo pgg-smc/instances/pgl27/pgl27_trace.vo pgg-smc/instances/pgl27/pgl27_recovery.vo && make -j1 pgg-smc/instances/pgl27/pgl27_trace.vo pgg-smc/instances/pgl27/pgl27_recovery.vo`. Expected: clean.
- [ ] **Step 1.5:** Assumptions via `rocq compile` scratch (flags: `-R . infotheo -R pgg-smc/lib pgg_smc -R pgg-smc/protocol pgg_smc -R pgg-smc/groups pgg_smc -R pgg-smc/security pgg_smc -R pgg-smc/reconstruct pgg_reconstruct -R pgg-smc/instances/pgl27 pgg_smc`): `pgl27_reveal_ambiguous` → Closed under the global context; `pgl27_deck_coalition_secrecy`, `pgl27_deck_marginal` → boolp trio only.
- [ ] **Step 1.6:** Update the three file headers' key-results lists with the new names (one line each, box-comment aligned). Commit:

```bash
git add pgg-smc/instances/pgl27/pgl27_secrecy.v pgg-smc/instances/pgl27/pgl27_trace.v pgg-smc/instances/pgl27/pgl27_recovery.v
git commit -m "pgl27: fill the last three exact-shuffle claim-matrix cells

Shuffle-free executed-trace secrecy (single + coalition), prior-generic
uniform-deck privacy with the uniform-over-valid-decks marginal
identification, and sub-6 reveal ambiguity for every revealed set."
```

---

### Task 2: Part 2 — the claim-boundary note (commit 2)

**Files:**
- Create: `pgg-smc/notes/20260713-pgl27-claim-boundary.md`

- [ ] **Step 2.1:** Write the note with these sections (content locked; expand each lemma row from the named file's header if a summary line is wanted):

```markdown
# pgl27 claim boundary (2026-07-13)

Rule: pgl27 is closed when every prose sentence about it maps either
to a Qed theorem in a committed file or to an explicitly disclosed
non-claim below. New work enters only when a new prose claim needs
it; each such claim opens its own spec with its own finite matrix.

## Claim matrix (exact-shuffle model; all Qed)

Group/orbit (zero axioms): pgl27_3transitive, pgl27_rho_im,
pgl27_pgl2_order (pgl27_group.v); orbit_class_split,
orbit_class_split_complement, orbit_class_invariant, deck_stable,
orbit_encodeK, orbit_encode_deck, orbit_populated (pgl27_orbit.v).
Correctness: pgl27_run_recovers (pgl27_run.v);
pgl27_run_recovers_class, pgl27_player_trace_full,
pgl27_alldecks_trace_full (pgl27_trace.v; the first two zero-axiom).
Recovery sharpness (zero axioms): pgl27_seven_reveal_determines,
pgl27_seven_reveal_class, pgl27_six_reveal_ambiguous,
pgl27_reveal_ambiguous, pgl27_2transitive (pgl27_recovery.v).
View privacy (boolp only): pgl27_view_indep, pgl27_view_leakage_le,
pgl27_view_dep_k4, pgl27_view_leak_k4, pgl27_view_indep_alldecks,
pgl27_view_indep_deck, pgl27_view_indep_deck_prior,
pgl27_deck_marginal (pgl27_secrecy.v).
Trace privacy (boolp only): pgl27_trace_secrecy,
pgl27_coalition_trace_secrecy, pgl27_alldecks_trace_secrecy,
pgl27_alldecks_coalition_secrecy, pgl27_deck_trace_secrecy,
pgl27_deck_coalition_secrecy (pgl27_trace.v).
Scheme/profile: pgl27_private, orbit_recon_invariant
(pgl27_scheme.v); exact eps=0 SecurityWitness (pgl27_profile.v; see
disclosure 5).
Realistic shuffle (Part 3 of the 2026-07-13 spec): pgl27_word_mixing,
pgl27_endpoint_mixing, pgl27_card (pgl27_mixing.v) — row added when
landed.

## Disclosed non-claims

1. The verifier learns the secret (endpoints flow to it by design);
   post-reveal knowledge is out of the model (headers say so).
2. Passive (honest-but-curious) adversaries only; no active
   deviation, no composition across executions.
3. Quantitative leakage at 4..6 revealed cards is not computed (only
   positivity at 4, monotonicity, and ambiguity through 6).
4. The all-decks dealer results are claimed for pgl27 only, not
   framework-wide (sibling instances keep representative samplers).
5. The framework SecurityWitness eps=0 measures the single-card
   marginal; coalition-level exactness is carried by the view/trace
   theorems, not the witness.
6. Until pgl27_word_mixing lands: the shuffle is exactly uniform on
   the group; word-of-generators realism is Part 3's claim.

## Trust base

boolp trio (propositional_extensionality,
functional_extensionality_dep, constructive_indefinite_description)
via infotheo probability; the Rocq kernel incl. the vm_compute
virtual machine. Group/orbit/recovery rows are closed under the
global context (no axioms at all).
```

- [ ] **Step 2.2:** Commit:

```bash
git add pgg-smc/notes/20260713-pgl27-claim-boundary.md
git commit -m "pgl27: claim-boundary note (matrix, disclosures, termination rule)"
```

---

### Task 3: Part 3 ground layer — `pgl27_mixing.v` tables, N-walk, checker (no commit yet)

**Files:**
- Create: `pgg-smc/instances/pgl27/pgl27_mixing.v`
- Modify: `_CoqProject` (add `pgg-smc/instances/pgl27/pgl27_mixing.v` after the pgl27 block, line ~254)

- [ ] **Step 3.1: File skeleton.** Header comment (terse, statement-style), imports:

```coq
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_collusion_bound pgg_weighted_words.
From pgg_smc Require Import pgl27_group pgl27_profile.
```

(Adjust the security-file module paths after `rocq_query "Locate rho_from_words_weighted."`; add `Set Implicit Arguments` block and scopes as in sibling files. `BinNat`: ssrnat already provides `nat_of_bin`/`bin_of_nat`; `N` literals via `%num`/`%N`-scope care — check with `rocq_query "Check (5%num * 5%num)%num."` and use `N.add`/`N.mul` explicitly if the scopes fight.)

- [ ] **Step 3.2: Generators and tables.**

```coq
(** pgl27_sym_sigmas — the inverse-closed symmetrized generator tuple of the
    realistic word shuffle: translation, scaling, inversion and the inverses.
    @intent: the letter alphabet of the L-word shuffle. *)
Definition pgl27_sym_sigmas : 5.-tuple {perm 'I_8} :=
  [tuple tnth pgl27_gens (@Ordinal 3 0 isT);
         ((tnth pgl27_gens (@Ordinal 3 0 isT))^-1)%g;
         tnth pgl27_gens (@Ordinal 3 1 isT);
         ((tnth pgl27_gens (@Ordinal 3 1 isT))^-1)%g;
         tnth pgl27_gens (@Ordinal 3 2 isT)].

Local Definition mtbl (j : nat) : seq nat :=
  nth [::] [:: [:: 1; 2; 3; 4; 5; 6; 0; 7]     (* z+1        *)
             ; [:: 6; 0; 1; 2; 3; 4; 5; 7]     (* z-1        *)
             ; [:: 0; 3; 6; 2; 5; 1; 4; 7]     (* 3z         *)
             ; [:: 0; 5; 3; 1; 6; 4; 2; 7]     (* 5z = z/3   *)
             ; [:: 7; 6; 3; 2; 5; 4; 1; 0]] j. (* -1/z       *)

(* Table-vs-perm consistency, one per letter. *)
Local Lemma mtbl_val (j : 'I_5) (x : 'I_8) :
  val (tnth pgl27_sym_sigmas j x) = nth 0 (mtbl j) (val x).
```

Proof: `case: j => -[|[|[|[|[|//]]]]] Hj`; per branch `case: x => -[|...] Hx; rewrite !(tnth_nth 1%g) /= ?permE ?permE //`. The two inverse branches need the inverse-perm evaluation: `(p^-1)%g x` — evaluate via `permE`? Use `invg_perm`/`permK`-style: the equality `(tr_perm^-1)%g x = y` iff `tr_perm y = x`; the clean route is `apply/(canRL (permKV _))`-style or verify by `apply: (canLR (permK _))`; alternatively state the branch as `val_inj`-checked table equality by first proving `(tnth pgl27_gens 0)^-1 = perm-of-inverse-table` via `permP => y; apply: (canLR (permK _))` + 8-case split. Develop with `rocq_step_multi`; the audit confirmed this is the same 8-case pattern as `tr_inj` (pgl27_group.v:67).

- [ ] **Step 3.3: Element BFS, successor and predecessor tables** (all `Local`):

```coq
Local Definition mcomp (t1 t2 : seq nat) : seq nat :=
  map (fun x => nth 0 t2 x) t1.                     (* apply t1 then t2 *)
Local Definition idt : seq nat := [:: 0; 1; 2; 3; 4; 5; 6; 7].

Local Fixpoint elem_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | S f =>
    let nxt := flatten
      [seq [seq (mcomp tw.1 (mtbl j), rcons tw.2 j) | j <- [:: 0; 1; 2; 3; 4]]
      | tw <- seen] in
    let add := foldl (fun acc tw =>
      if has (fun sw : seq nat * seq nat => sw.1 == tw.1) (seen ++ acc)
      then acc else rcons acc tw) [::] nxt in
    if size add == 0 then seen else elem_bfs f (seen ++ add)
  end.

Local Definition elem_table : seq (seq nat * seq nat) :=
  elem_bfs 12 [:: (idt, [::])].

Local Definition tbl_index (t : seq nat) : nat :=
  find (fun sw : seq nat * seq nat => sw.1 == t) elem_table.

(* pred_table: for state k and letter j, the index i with i*g_j = k,
   i.e. the entry whose table composed with mtbl j gives entry k;
   computed as the index of (mcomp k-table (inverse-letter table)). *)
Local Definition inv_letter (j : nat) : nat := nth 0 [:: 1; 0; 3; 2; 4] j.
Local Definition pred_table : seq (seq nat) :=
  [seq [seq tbl_index (mcomp sw.1 (mtbl (inv_letter j))) | j <- [:: 0; 1; 2; 3; 4]]
  | sw <- elem_table].
```

- [ ] **Step 3.4: Binary-N walk and checker** (all `Local`):

```coq
Local Fixpoint walkN (L : nat) : seq N :=
  match L with
  | 0 => 1%num :: nseq 335 0%num
  | L'.+1 =>
    let v := walkN L' in
    [seq foldl (fun acc i => (acc + nth 0%num v i)%num) 0%num preds
    | preds <- pred_table]
  end.

Local Definition absdiffN (a b : N) : N :=
  if (a <? b)%num then (b - a)%num else (a - b)%num.

Local Definition mixing_bound_ok : bool :=
  let D := (5 ^ 200)%num in
  let S := foldl (fun acc c => (acc + absdiffN (336 * c)%num D)%num) 0%num
                 (walkN 200) in
  ((2 ^ 40) * S <=? 336 * D)%num.

Local Definition elem_table_ok : bool :=
  [&& size elem_table == 336, uniq (unzip1 elem_table),
      nth ([::], [::]) elem_table 0 == (idt, [::]),
      all (fun sw : seq nat * seq nat =>
             foldl (fun t j => mcomp t (mtbl j)) idt sw.2 == sw.1)
          elem_table
    & all (fun sw : seq nat * seq nat =>
             all (fun j => nth [::] (unzip1 elem_table)
                     (tbl_index (mcomp sw.1 (mtbl j))) == mcomp sw.1 (mtbl j))
                 [:: 0; 1; 2; 3; 4])
          elem_table].

Local Lemma elem_table_okT : elem_table_ok.
Proof. by vm_compute. Qed.

Local Lemma mixing_bound_okT : mixing_bound_ok.
Proof. by vm_compute. Qed.
```

Notation caution: `N` operations may need `N.mul`/`N.add`/`N.pow`/`N.ltb`/`N.leb` spelled out if `%num` scope notations are unavailable in this import set — resolve with `rocq_query` first (`Check (N.pow 5 200).`). Timing: expect seconds; if `mixing_bound_okT` exceeds ~5 minutes, STOP and report (do not retry blindly).

- [ ] **Step 3.5:** Interactive check of every definition and the two vm_compute lemmas via preamble-mode rocq-mcp BEFORE writing the file; then write the file, add the `_CoqProject` line, and `make -j1 pgg-smc/instances/pgl27/pgl27_mixing.vo`. Expected: clean. No commit yet.

---

### Task 4: closure-list = G, `pgl27_card`, `<<3>> = <<5>>` (no commit yet)

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_mixing.v` (append)

- [ ] **Step 4.1: Word/perm bridge over the 5-letter alphabet** (Local): clone the landed 3-letter pattern (pgl27_group.v word_perm block):

```coq
Local Definition gen5_of (j : nat) : {perm 'I_8} :=
  nth (tnth pgl27_sym_sigmas (@Ordinal 5 4 isT))
      [seq tnth pgl27_sym_sigmas j | j : 'I_5 <- enum 'I_5] j.
Local Definition word5_perm (w : seq nat) : {perm 'I_8} :=
  foldl (fun g j => (g * gen5_of j)%g) 1%g w.
Local Lemma gen5_of_mem (j : nat) : gen5_of j \in pgg_G pgl27_M.
Local Lemma word5_perm_mem (w : seq nat) : word5_perm w \in pgg_G pgl27_M.
Local Lemma word5_perm_tbl (w : seq nat) (x : 'I_8) :
  val (word5_perm w x)
  = nth 0 (foldl (fun t j => mcomp t (mtbl j)) idt w) (val x).
```

`gen5_of_mem`: the three originals via `mem_gen`/`imsetP` (as `gen_of_mem`, pgl27_group.v), the two inverses via `groupV`. `word5_perm_tbl`: generalized-accumulator foldl induction using `mtbl_val` and `permM` (mirror `word_perm_val`, pgl27_group.v; the accumulator now carries a TABLE, so the invariant is `val (foldl step g w x) = nth 0 (foldl tstep (table-of g) w) (val x)` — state it with an explicit `forall t, (forall y, val (g y) = nth 0 t (val y)) -> ...` premise).

- [ ] **Step 4.2: Entry perms and the group equality.**

```coq
Local Definition entry_perm (k : nat) : {perm 'I_8} :=
  word5_perm (nth ([::], [::]) elem_table k).2.

(** pgl27_gen5_eq — the symmetrized five-letter alphabet generates the same
    group as the three PGL(2,7) generators.
    @composes: pgl27_card *)
Lemma pgl27_gen5_eq :
  <<[set tnth pgl27_sym_sigmas j | j : 'I_5]>>%G = pgg_G pgl27_M.

(** pgl27_card — the PGL(2,7) shuffle group has exactly 336 elements.
    @main architecture: the in-kernel order of the generated group, tying the
    walk's 336-entry state space to the whole group. *)
Lemma pgl27_card : #|pgg_G pgl27_M| = 336.
```

Proof routes (develop interactively): `pgl27_gen5_eq` by `eqEsubset`: forward `gen_subG` + per-letter membership (`gen5_of_mem` content); backward `genS` after showing the 3-generator imset is a subset of the 5-generator imset (`apply/subsetP => x /imsetP[i _ ->]; apply/mem_gen/imsetP`; map i in 'I_3 to the matching 'I_5 index 0/2/4). `pgl27_card`: build the bijection between `pgg_G pgl27_M` and the 336 uniq entry tables. Direction 1 — every `g \in pgg_G` is some `entry_perm k`: by `gen_prodgP` (after rewriting with `pgl27_gen5_eq` backwards NOT needed — use the 3-generator group directly: `gen_prodgP` gives a product of the THREE generators; every 3-letter word is also a 5-letter word; induction on the product length shows its table is reachable by `elem_table`'s closure (checker conjunct 5: closure under all five letters, hence under the three); the table determines the perm (`permP` + `val_inj` pointwise from `word5_perm_tbl`). Direction 2 — entries are distinct elements of G: `word5_perm_mem` + `uniq (unzip1 elem_table)` (checker) + injectivity of the table map (two perms with equal tables are equal by `permP`/`val_inj`). Then `#|G| = size elem_table = 336` via `card_uniqP`-style counting over the image list (the `class_count`/`card_uniqP` pattern landed in pgl27_orbit.v:476-504 is the model). Cross-check: `pgl27_pgl2_order` (pgl27_group.v:161) = 336 for the abstract quotient — narrative only, not used.

- [ ] **Step 4.3:** `make -j1 pgg-smc/instances/pgl27/pgl27_mixing.vo`; scratch `Print Assumptions pgl27_card` → Closed under the global context. No commit yet.

---

### Task 5: fiber counting and the headline bound (commit 3)

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_mixing.v` (append)

- [ ] **Step 5.1: The walk monodromy and the word law.** Fix the instantiation objects:

```coq
Local Notation M5 := (@Gen_PGGTypes 4 6 pgl27_sym_sigmas).
Definition Wuni : R.-fdist 'I_5 := fdist_uniform (card_ord 5).   (* inside a Section with Variable R *)
```

(Open a `Section pgl27_mixing_sec. Variable R : realType.` for the R-dependent part; keep the nat/N ground layer outside the section.)

- [ ] **Step 5.2: Fiber counting.** The counting bridge, stated over the entry indexing:

```coq
Local Lemma fiber_count (L : nat) (k : nat) : (k < 336)%N ->
  #|[set w : L.-tuple 'I_5 | word_eval M5 w == entry_perm k]|
  = nat_of_bin (nth 0%num (walkN L) k).
```

Proof by induction on L. Base: `word_eval` of the empty tuple is `1%g`; the only k with `entry_perm k = 1` is k = 0 (identity entry, checker conjunct 3 + uniq); `walkN 0` is `1 :: nseq 335 0`. Step: split each (L+1)-tuple as `[tuple of rcons w' j]` (the `tuple_rcons`/`big_ord_recr` route: `word_eval (rcons-tuple) = word_eval w' * tnth sigmas j` — prove as a Local lemma via `big_ord_recr` + `tnth` of rcons); partition the fiber by the last letter j; the sub-fiber for letter j bijects with the L-fiber of `entry_perm (pred_table k j)` (right-cancel by `gen5_of j`: `w' * g_j = entry_k` iff `w' = entry_k * g_j^-1` = the predecessor entry — table-level fact from checker conjunct 5 + `word5_perm_tbl` + `permP`); card of the disjoint union = sum over j; `walkN (L+1)` computes exactly that sum with `nat_of_add_bin` distributing `nat_of_bin` over the foldl (prove a tiny Local lemma `nat_of_bin (foldl N.add 0 s) = \sum nat_of_bin s` by induction). Budget: this is the load-bearing proof; if it exceeds 60 rocq-mcp turns without the induction shape closing, STOP and report rather than thrash.

- [ ] **Step 5.3: The headline assembly.**

```coq
(** pgl27_word_mixing — the law of a uniform 200-letter generator word is
    within 2^-40 of the uniform shuffle in variation distance.
    @main security: the realistic-shuffle mixing certificate. *)
Lemma pgl27_word_mixing :
  var_dist (@rho_from_words_weighted R 6 4 200 pgl27_sym_sigmas Wuni)
           (`U pgl27_G_pos)
  <= 2%:R ^- 40.
```

Proof skeleton: `rho_weighted_is_uniform` collapses to `rho_from_words`; `eq_irrelevance` reconciles the `card_word_L`/`card_word_L'` witnesses; `var_dist` unfolds to `\sum_(g : {perm 'I_8}) |...|`; `bigID (fun g => g \in pgg_G pgl27_M)`; off-G: both laws are 0 (`fdist_uniform_supp_notin`; `fiber_prob` numerator 0 because a nonempty fiber puts g in G via `word5_perm_mem`-style membership — actually via `word_eval` membership: each letter in `pgg_G` by `gen5_of_mem` content, product closed by `group_prod`); on-G: reindex the sum over the 336 `entry_perm` list (`big_uniq`/`big_seq` over the uniq entry list, coverage by `pgl27_card` direction 1); each term is `|#|fiber|/5^200 - 1/336|` (`fiber_prob`, `fdist_uniform_supp_in` + `pgl27_card`); rewrite by `fiber_count`; bound the real sum by the N-level `mixing_bound_okT` via `nat_of_bin` monotone reflection (per-index case split on `336*n_i >= 5^200` matching `absdiffN`'s comparison; `ler_pdivrMr`-style cross-multiplication with positive `336%:R * (5^200)%:R * (2^40)%:R`; `natrX`/`natrM` push `%:R` through). This assembly is real-analysis plumbing but every ingredient is named; expect the longest interactive session here.

- [ ] **Step 5.4:** `make -j1 pgg-smc/instances/pgl27/pgl27_mixing.vo`; scratch `Print Assumptions pgl27_word_mixing` → boolp trio only. Commit:

```bash
git add pgg-smc/instances/pgl27/pgl27_mixing.v _CoqProject
git commit -m "pgl27: in-kernel realistic-shuffle mixing bound at L=200

Binary-N walk over the 336-entry closure (vm_compute), fiber-counting
bridge to rho_from_words_weighted, var_dist <= 2^-40 against the
uniform shuffle; pgl27_card = 336 returns as a load-bearing theorem."
```

---

### Task 6: corollaries, closure-note update, final verification (commit 4)

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_mixing.v` (append)
- Modify: `pgg-smc/notes/20260713-pgl27-claim-boundary.md`

- [ ] **Step 6.1: Endpoint corollary.**

```coq
(** pgl27_endpoint_mixing — each single-card marginal of the 200-letter word
    shuffle is within 2^-40 of uniform.
    @main security: the realistic-shuffle single-card mixing bound. *)
Lemma pgl27_endpoint_mixing (s : 'I_8) :
  var_dist (@endpoint_dist_weighted R 6 4 200 pgl27_sym_sigmas Wuni s)
           (fdist_uniform (card_ord 8))
  <= 2%:R ^- 40.
Proof.
(* endpoint_dist_weighted = fdistmap (eval s) rho_from_words_weighted;
   rewrite fdist_uniform (card_ord 8) as fdistmap (eval s) (`U pgl27_G_pos)
   via pgl27_point_uniform (check its exact statement/orientation with
   About first); conclude by
   le_trans (var_dist_fdistmap ...) pgl27_word_mixing. *)
```

- [ ] **Step 6.2: Joint-law stretch goal** (attempt; defer with a disclosure if it exceeds 40 turns):

```coq
(* var_dist of kernel-equal products factorizes through the first marginal. *)
Local Lemma var_dist_prodR (A B : finType) (P : R.-fdist A)
    (Q1 Q2 : R.-fdist B) :
  var_dist (P `x Q1) (P `x Q2) = var_dist Q1 Q2.

(** pgl27_joint_mixing — the joint secret-and-shuffle law of the 200-letter
    word run is within 2^-40 of the exact-shuffle joint law.
    @main security: every observable of the realistic-shuffle run differs
    from the exact-shuffle one by at most 2^-40 in variation distance. *)
Lemma pgl27_joint_mixing (secretP : R.-fdist bool) :
  var_dist
    (secretP `x (@rho_from_words_weighted R 6 4 200 pgl27_sym_sigmas Wuni))
    (secretP `x (`U pgl27_G_pos))
  <= 2%:R ^- 40.
Proof.
(* rewrite var_dist_prodR; exact: pgl27_word_mixing. *)
```

`var_dist_prodR`: `\sum_(ab) |P ab.1 * Q1 ab.2 - P ab.1 * Q2 ab.2|` = `\sum_a P a * \sum_b |Q1 b - Q2 b|` (`-mulrBr normrM ger0_norm` on `P a >= 0`, `pair_big`/`big_pair` split, `-big_distrl FDist.f1 mul1r`). The honest pointwise 2-epsilon corollary is OUT of this round (disclosed in the note) — the joint-law form is the deliverable.

- [ ] **Step 6.3:** Update the closure note: move the mixing row from "added when landed" to the matrix proper (pgl27_word_mixing, pgl27_endpoint_mixing, pgl27_joint_mixing if landed, pgl27_card); rewrite disclosure 6 to: "The realistic-shuffle claims hold at L = 200 letters with variation distance at most 2^-40 (joint-law form); pointwise approximate-independence constants (2-epsilon form) are not stated." Update the mixing file header key-results list.
- [ ] **Step 6.4: Final verification.**

```bash
grep -rn "^Axiom\|Admitted" pgg-smc/instances/pgl27/ && echo FAIL || echo OK
make -j1   # or targeted: the seven pgl27 .vo files + pgl27_mixing.vo
```

Scratch Print Assumptions: `pgl27_word_mixing`, `pgl27_endpoint_mixing` → boolp trio; `pgl27_card` → Closed under the global context. Commit:

```bash
git add pgg-smc/instances/pgl27/pgl27_mixing.v pgg-smc/notes/20260713-pgl27-claim-boundary.md
git commit -m "pgl27: mixing corollaries (endpoint, joint-law) + boundary note update"
```

---

## Stop conditions (report instead of thrashing)

- `mixing_bound_okT` vm_compute exceeds ~5 minutes (arithmetic-layer defect).
- `fiber_count` induction shapeless after 60 rocq-mcp turns (bridge defect).
- Any statement requires enumerating `{perm 'I_8}` or the tuple type in vm_compute (design defect).
Each of these is a plan defect: stop, record findings, report.
