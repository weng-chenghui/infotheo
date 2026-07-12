# pgl27 Open Questions Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the four open pgl27 audit items: prove `pgl27_3transitive` in-kernel (axiom becomes theorem), add the sharp recovery pair (7 reveals determine, 6 never do), prove all-valid-decks dealer privacy, and sweep the reveal-phase prose.

**Architecture:** Item 1 replaces the axiom in `pgl27_group.v` with the two-layer BFS word-witness proof (nat-level `vm_compute` ground layer, MathComp bridge). Item 3 is a new file `pgl27_recovery.v` built on the item-1 theorem. Item 2 adds a kernel-product independence layer plus a generic all-decks section to `transitivity_privacy.v` and instantiates it in `pgl27_secrecy.v`. Item 4 is a docs/header sweep. Spec: `docs/superpowers/specs/2026-07-12-pgl27-open-questions-design.md` (audited 2026-07-12).

**Tech Stack:** Rocq + MathComp 2.4.0 (fingroup, perm, action, primitive_action), infotheo fdist/proba, rocq-mcp for all interactive checking.

**Non-negotiable execution rules (from project CLAUDE.md):**
- `make -j1` only, never `-j4`; one rocqworker at a time; NO parallel prover agents.
- Never `rewrite !lemma` with arithmetic lemmas; never `lia`; `%N` discipline in `ring_scope` files (`pgl27_group.v` opens `ring_scope` at line 43, `pgl27_secrecy.v` at line 75).
- Validate interactively with rocq-mcp (`rocq_start` → `rocq_query` → `rocq_check`/`rocq_step_multi` → apply to file); reserve `make -j1` for the end-of-task bulk rebuild.
- Every non-`Local` declaration carries exactly one H-series role tag (`@intent:` / `@composes: <lemma>` / `@main <label>:`); `Local` declarations escape the gate.
- rocq-prover subagent launches must state: pre-built `.vo` status, exact line ranges, section context, turn budget, and the 4-phase rocq-mcp workflow.

**Verified probe results available to workers (2026-07-12 session):**
1. `(pgg_rho pgl27_M @* pgg_G pgl27_M)%g = pgg_G pgl27_M` closes by `by rewrite morphimEdom imset_id.`
2. The BFS + checker below closes `by vm_compute.` in 910 ms.
3. After `rewrite /ntransitive` + collapse + `apply/imsetP; exists [tuple ord0; 1; 2]`, the two goals are base-tuple membership in `3.-dtuple([set: 'I_8])` and `3.-dtuple([set: 'I_8]) = orbit ('P * 3) (pgg_G pgl27_M) t0`.

---

### Task 1: Ground layer in `pgl27_group.v` (BFS words + vm_compute checker)

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_group.v` (insert before the axiom block at lines 165-189)

- [ ] **Step 1.1: Insert the nat-level definitions.** All `Local` (escape the H-gate). They reuse the existing `tr_tbl`/`sc_tbl`/`inv_tbl` (lines 52-54) as the single source of truth:

```coq
(* ---------------------------------------------------------------------- *)
(* In-kernel 3-transitivity: nat-level word search.                        *)
(* A word is a seq of generator indices (0 = translation, 1 = scaling,     *)
(* 2 = inversion). A fueled BFS from the base triple [:: 0; 1; 2] finds,   *)
(* for each of the 336 ordered distinct code triples, a word carrying the  *)
(* base triple to it; the checker re-verifies every entry by computation.  *)
(* ---------------------------------------------------------------------- *)

Local Definition wgenn (i : nat) (a : nat) : nat :=
  nth 0 (nth [::] [:: tr_tbl; sc_tbl; inv_tbl] i) a.

Local Definition papply (w : seq nat) (a : nat) : nat :=
  foldl (fun x i => wgenn i x) a w.

Local Definition wstep (i : nat) (t : seq nat) : seq nat := map (wgenn i) t.

Local Definition wapply (w : seq nat) (t : seq nat) : seq nat :=
  foldl (fun acc i => wstep i acc) t w.

Local Fixpoint word_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | S f =>
    let nxt := flatten
      [seq [seq (wstep i tw.1, rcons tw.2 i) | i <- [:: 0; 1; 2]] | tw <- seen] in
    let add := foldl (fun acc tw =>
      if has (fun sw : seq nat * seq nat => sw.1 == tw.1) (seen ++ acc)
      then acc else rcons acc tw) [::] nxt in
    if size add == 0 then seen else word_bfs f (seen ++ add)
  end.

Local Definition word_table : seq (seq nat * seq nat) :=
  word_bfs 12 [:: ([:: 0; 1; 2], [::])].

Local Definition word_table_ok : bool :=
  all (fun a => all (fun b => all (fun c =>
    (a != b) && (a != c) && (b != c) ==>
    has (fun sw : seq nat * seq nat =>
      (sw.1 == [:: a; b; c]) && (wapply sw.2 [:: 0; 1; 2] == [:: a; b; c]))
      word_table)
    (iota 0 8)) (iota 0 8)) (iota 0 8).
```

Note vs. the probe: the probe used a dispatch `if i == 0 then ptrn ...`; this version reads the table list by `nth`, which is equivalent and shorter. If `vm_compute` in Step 1.3 fails to reduce for any reason, fall back to the probe's literal dispatch form.

- [ ] **Step 1.2: Add the two computational lemmas:**

```coq
(* Every word in the table re-verifies against every distinct code triple. *)
Local Lemma word_table_okT : word_table_ok.
Proof. by vm_compute. Qed.

(* Word application on a triple is coordinatewise scalar application. *)
Local Lemma wapply_map (w : seq nat) (a b c : nat) :
  wapply w [:: a; b; c] = [:: papply w a; papply w b; papply w c].
Proof. by elim: w a b c => [|i w IH] a b c //=. Qed.
```

If the `wapply_map` one-liner does not close, the expected shape is `elim: w a b c => [|i w IH] a b c //=; rewrite IH` (foldl unfolds one step; `wstep i [:: a; b; c]` reduces to the mapped triple by `/=`).

- [ ] **Step 1.3: Check interactively.** `rocq_start` with preamble = the imports of `pgl27_group.v` lines 29-43 plus `From pgg_smc Require Import pgl27_group.` is NOT possible while editing the same file; instead run `rocq_start(file="pgg-smc/instances/pgl27/pgl27_group.v", line=163, character=0)` (position mode, before the axiom block) and `rocq_check` each definition and lemma in order. Expected: `word_table_okT` closes by `vm_compute` in about 1 s (probe evidence).

---

### Task 2: Bridge layer + `pgl27_3transitive` theorem in `pgl27_group.v`

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_group.v` (continue after Task 1's insertions; then REPLACE the axiom block lines 165-189 and update the header lines 20-26)

- [ ] **Step 2.1: Word-to-perm bridge definitions and lemmas** (all `Local` except `pgl27_rho_im`):

```coq
Local Definition gen_of (i : nat) : {perm 'I_8} :=
  if i == 0 then tr_perm else if i == 1 then sc_perm else inv_perm.

Local Definition word_perm (w : seq nat) : {perm 'I_8} :=
  foldl (fun g i => (g * gen_of i)%g) 1%g w.

Local Lemma gen_of_mem (i : nat) : gen_of i \in pgg_G pgl27_M.
Proof.
apply: mem_gen; apply/imsetP; rewrite /gen_of.
case: (i == 0); first by exists (@Ordinal 3 0 isT).
case: (i == 1); first by exists (@Ordinal 3 1 isT).
by exists (@Ordinal 3 2 isT).
Qed.

Local Lemma word_perm_mem (w : seq nat) : word_perm w \in pgg_G pgl27_M.
Proof.
rewrite /word_perm.
have: 1%g \in pgg_G pgl27_M := group1 _.
elim: w (1%g) => [|i w IH] g gG //=.
by apply: IH; apply: groupM => //; exact: gen_of_mem.
Qed.

Local Lemma gen_of_val (i : nat) (x : 'I_8) : val (gen_of i x) = wgenn i (val x).
Proof.
rewrite /gen_of /wgenn; case: (i == 0); last case: (i == 1).
- by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE.
- by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE.
- by case: x => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt; rewrite permE.
Qed.

Local Lemma word_perm_val (w : seq nat) (x : 'I_8) :
  val (word_perm w x) = papply w (val x).
Proof.
rewrite /word_perm /papply.
have H : forall (w : seq nat) (g : {perm 'I_8}) (x : 'I_8),
    val (foldl (fun h i => (h * gen_of i)%g) g w x)
    = foldl (fun a i => wgenn i a) (val (g x)) w.
  by elim=> [|i w' IH] g y //=; rewrite IH permM gen_of_val.
by rewrite H perm1.
Qed.
```

`tnth pgl27_gens (Ordinal 0) = tr_perm` (for `gen_of_mem`): if the `exists` leaves that goal, close with `by rewrite (tnth_nth tr_perm).` or plain `by []`; try `rocq_step_multi(["by [].", "by rewrite (tnth_nth tr_perm).", "by apply: val_inj."])`.

- [ ] **Step 2.2: Extraction lemma** (`Local`, mirrors `gen_class` of `pgl27_orbit.v:181`):

```coq
Local Lemma triple_word (x y z : 'I_8) :
  x != y -> x != z -> y != z ->
  exists w : seq nat,
    [/\ papply w 0 = val x, papply w 1 = val y & papply w 2 = val z].
Proof.
move=> nxy nxz nyz.
have Hin : forall n : 'I_8, val n \in iota 0 8.
  by move=> n; rewrite mem_iota; case: n.
have Hd : (val x != val y) && (val x != val z) && (val y != val z).
  by rewrite !val_eqE nxy nxz nyz.
move: word_table_okT.
move=> /allP/(_ _ (Hin x))/allP/(_ _ (Hin y))/allP/(_ _ (Hin z)).
move=> /implyP/(_ Hd)/hasP[[t w] /= _ /andP[/eqP Ht /eqP Hw]].
exists w; move: Hw; rewrite Ht wapply_map.
by case=> -> -> ->.
Qed.
```

Watch: inside `ring_scope`, the `mem_iota` rewrite produces nat comparisons; if `case: n` does not close the `Hin` goal, use `by move=> n; rewrite mem_iota add0n leq0n /=; exact: ltn_ord.` with explicit `%N` if needed.

- [ ] **Step 2.3: The exported collapse lemma** (non-`Local`, needs an H-tag):

```coq
(** pgl27_rho_im — the permutation image of the monodromy morphism is the
    generated shuffle group itself.
    @composes: pgl27_3transitive *)
Lemma pgl27_rho_im :
  (@pgg_rho pgl27_M @* pgg_G pgl27_M)%g = pgg_G pgl27_M.
Proof. by rewrite morphimEdom imset_id. Qed.
```

- [ ] **Step 2.4: Replace the axiom block (lines 165-189) with the theorem.** Delete the entire justification comment block AND the `Axiom` declaration. Insert:

```coq
(* -------------------------------------------------------------------------- *)
(* Sharp 3-transitivity, in-kernel: for every ordered distinct triple the     *)
(* BFS word table exhibits a generator word carrying the base triple (0,1,2)  *)
(* to it; the orbit of the base triple is therefore all of 3.-dtuple.         *)
(* -------------------------------------------------------------------------- *)

(** pgl27_3transitive — the PGL(2,7) monodromy group acts 3-transitively on
    the eight projective points.
    @main security: the transitivity feeding every coalition-privacy result
    of the pgl27 instance. *)
Lemma pgl27_3transitive :
  ntransitive 3 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P.
Proof.
rewrite /ntransitive pgl27_rho_im.
pose t0 : 3.-tuple 'I_8 :=
  [tuple (@Ordinal 8 0 isT); (@Ordinal 8 1 isT); (@Ordinal 8 2 isT)].
have Ht0 : t0 \in 3.-dtuple([set: 'I_8]).
  by rewrite inE; apply/andP; split=> //; apply/subsetP => u _; rewrite inE.
apply/imsetP; exists t0 => //.
apply/setP => u; apply/idP/idP => [Hu | /orbitP[a aG <-]]; last first.
  apply: n_act_dtuple => //.
  by apply/astabsP => v; rewrite !inE.
case/tupleP: u Hu => x u; case/tupleP: u => y u; case/tupleP: u => z u.
rewrite tuple0 inE => /andP[Huniq _].
have [nxy nxz nyz] : [/\ x != y, x != z & y != z].
  by move: Huniq; rewrite /= !inE !negb_or => /andP[/andP[-> ->] /andP[-> _]].
have [w [Hx Hy Hz]] := triple_word nxy nxz nyz.
apply/orbitP; exists (word_perm w); first exact: word_perm_mem.
apply: eq_from_tnth => j.
rewrite [n_act _ _ _]tnth_map.
case: j => -[|[|[|//]]] Hj; apply: val_inj => /=.
- by rewrite [tnth t0 _]/= word_perm_val Hx.
- by rewrite [tnth t0 _]/= word_perm_val Hy.
- by rewrite [tnth t0 _]/= word_perm_val Hz.
Qed.
```

This skeleton encodes the probed structure; the exact `tnth`/`tnth_map` simplifications in the last block are the expected friction point. Work them in rocq-mcp: after `eq_from_tnth => j`, `Show` the goal, and expect to need `(tnth_nth ord0)` or `tnth_mktuple`-style rewrites plus `tnth_map` on the `n_act` side (`n_act to t a = [tuple of map (to^~ a) t]`, so `tnth (n_act 'P t0 g) j = 'P (tnth t0 j) g = g (tnth t0 j)` via `tnth_map` and `apermE`/`permE`). Try `rocq_step_multi` with: `rewrite tnth_map tnth_ord_tuple.`, `rewrite !(tnth_nth ord0) /=.`, `rewrite apermE.`.

- [ ] **Step 2.5: Update the file header.** Line 23 `pgl27_3transitive == ... (axiom)` becomes `pgl27_3transitive      == the group acts 3-transitively on 'I_8`; delete lines 25-26 (the axiom-justification pointer); add a line for `pgl27_rho_im` in the key-results list.

- [ ] **Step 2.6: Whole-file check.** Run `mcp rocq_compile_file` on `pgg-smc/instances/pgl27/pgl27_group.v` (or `make -j1 pgg-smc/instances/pgl27/pgl27_group.vo` after `rm -f` of that `.vo`). Expected: compiles with no `Axiom` remaining. Then `rocq_assumptions` (or `rocq_query "Print Assumptions pgl27_3transitive."` in file mode). Expected: `Closed under the global context`.

---

### Task 3: Downstream rebuild and commit 1

**Files:**
- No new edits; rebuild `pgl27_orbit.vo`, `pgl27_scheme.vo`, `pgl27_profile.vo`, `pgl27_secrecy.vo`, `pgl27_run.vo`, `pgl27_trace.vo`

- [ ] **Step 3.1:** `make -j1 pgg-smc/instances/pgl27/pgl27_trace.vo pgg-smc/instances/pgl27/pgl27_secrecy.vo pgg-smc/instances/pgl27/pgl27_profile.vo` (make resolves the dependency order; single job). Expected: all six pgl27 `.vo` files rebuild cleanly with zero source changes outside `pgl27_group.v`.
- [ ] **Step 3.2:** `grep -rn "^Axiom" pgg-smc/instances/pgl27/` — expected: no output.
- [ ] **Step 3.3:** `rocq_query "Print Assumptions pgl27_view_indep." (file mode on pgl27_secrecy.v)` — expected: boolp axioms only (functional_extensionality_dep etc.), no `pgl27_3transitive`.
- [ ] **Step 3.4: Commit.**

```bash
git add pgg-smc/instances/pgl27/pgl27_group.v
git commit -m "pgl27: prove pgl27_3transitive in-kernel (axiom deleted)

BFS word table over the 336 ordered distinct triples, vm_compute
checker, word-to-perm bridge; the pgl27 chain is now boolp-only."
```

Audit gate: stage 2 runs; the only non-Local additions are `pgl27_rho_im` (`@composes`) and `pgl27_3transitive` (`@main security`), both tagged above.

---

### Task 4: `pgl27_recovery.v` — seven-reveal determination

**Files:**
- Create: `pgg-smc/instances/pgl27/pgl27_recovery.v`
- Modify: `_CoqProject` (add `pgg-smc/instances/pgl27/pgl27_recovery.v` next to the other pgl27 entries, lines ~247-253)

- [ ] **Step 4.1: Create the file** with header and imports (mirror `pgl27_orbit.v`'s import block):

```coq
(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_recovery: the sharp recovery threshold of the eight-card scheme      *)
(*                                                                            *)
(* A valid deck deals the eight distinct cards, so seven revealed positions   *)
(* leave a unique missing card: seven reveals determine the deck and hence    *)
(* the orbit class. Six reveals never do: for every choice of two hidden      *)
(* positions there are two valid decks of opposite orbit classes agreeing on  *)
(* the six revealed ones. Together with the privacy threshold three and the   *)
(* four-position leak (pgl27_secrecy.v), the ramp reads: private up to        *)
(* three, leaky from four, ambiguous through six, determined at seven.        *)
(* The implemented protocol decoder (pgl27_run.v) reads all eight endpoints.  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_seven_reveal_determines == decks agreeing off one position agree   *)
(*   pgl27_seven_reveal_class      == seven reveals determine the class       *)
(*   pgl27_six_reveal_ambiguous    == six reveals never determine the class   *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import ssralg ssrnum order.
From mathcomp Require Import primitive_action.
From pgg_smc Require Import pgg_interface.
From pgg_smc Require Import pgl27_group pgl27_orbit.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
```

- [ ] **Step 4.2: The determination pair:**

```coq
(** pgl27_seven_reveal_determines — two valid decks agreeing everywhere off
    one position are equal: the eight distinct cards leave a unique missing
    card for the hidden position.
    @main correctness: seven revealed cards determine the deck. *)
Lemma pgl27_seven_reveal_determines (p : 'I_8) (sh1 sh2 : 8.-tuple 'I_8) :
  deck_ok sh1 -> deck_ok sh2 ->
  (forall i : 'I_8, i != p -> tnth sh1 i = tnth sh2 i) ->
  sh1 = sh2.
Proof.
move=> u1 u2 Hagree.
have inj1 : injective (tnth sh1) by apply/tuple_uniqP.
have inj2 : injective (tnth sh2) by apply/tuple_uniqP.
have Himg : [set tnth sh1 i | i in [set~ p]]
          = [set tnth sh2 i | i in [set~ p]].
  apply: eq_in_imset => i; rewrite inE => nip.
  by rewrite Hagree.
have Hout : forall (sh : 8.-tuple 'I_8), injective (tnth sh) ->
    tnth sh p \notin [set tnth sh i | i in [set~ p]].
  move=> sh injs; apply/imsetP => -[j]; rewrite inE => njp Heq.
  by move: njp; rewrite (injs _ _ Heq) eqxx.
have Hcard : #|~: [set tnth sh1 i | i in [set~ p]]| = 1%N.
  rewrite cardsCs setCK card_imset ?cardsC1 ?card_ord //.
  by move=> i j /inj1.
case/cards1P: Hcard => a Ha.
have E1 : tnth sh1 p = a.
  by move: (Hout _ inj1); rewrite -in_setC Ha inE => /eqP.
have E2 : tnth sh2 p = a.
  by move: (Hout _ inj2); rewrite Himg -in_setC Ha inE => /eqP.
apply: eq_from_tnth => i.
have [->|nip] := eqVneq i p; first by rewrite E1 E2.
exact: Hagree.
Qed.

(** pgl27_seven_reveal_class — two valid decks agreeing off one position have
    the same orbit class: a seven-position decoder for the secret exists.
    @main correctness: seven revealed cards determine the orbit class. *)
Lemma pgl27_seven_reveal_class (p : 'I_8) (sh1 sh2 : 8.-tuple 'I_8) :
  deck_ok sh1 -> deck_ok sh2 ->
  (forall i : 'I_8, i != p -> tnth sh1 i = tnth sh2 i) ->
  orbit_class sh1 = orbit_class sh2.
Proof.
by move=> u1 u2 /(pgl27_seven_reveal_determines u1 u2) ->.
Qed.
```

API notes for the worker: `[set~ p]` is the complement of the singleton; `cardsC1 : #|[set~ a]| = #|T|.-1`. The `Hcard` chain may need adjustment; the target fact is `#|~: (f @: [set~ p])| = 1` from `#|f @: [set~ p]| = 7` and `#|'I_8| = 8`; candidates: `cardsCs`, `cardsC`, `card_imset`, `cardsC1`, `card_ord`. If the one-line chain resists, prove `#|f @: [set~ p]| = 7` first, then use `cardsC` (`#|A| + #|~:A| = #|T|`) and arithmetic (`addnC`, no `!` rewrites).

- [ ] **Step 4.3:** `_CoqProject`: add the file line. Then `rocq_compile_file` on the new file (only these two lemmas present). Expected: clean compile.

---

### Task 5: `pgl27_recovery.v` — six-reveal ambiguity, commit 2

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_recovery.v` (append)

- [ ] **Step 5.1: 2-transitivity corollary and base witness:**

```coq
(** pgl27_2transitive — the PGL(2,7) monodromy acts 2-transitively on the
    eight projective points, weakened from sharp 3-transitivity.
    @composes: pgl27_six_reveal_ambiguous *)
Lemma pgl27_2transitive :
  ntransitive 2 (@pgg_rho pgl27_M @* pgg_G pgl27_M) [set: 'I_8] 'P.
Proof. exact: ntransitive_weak (isT : (2 <= 3)%N) pgl27_3transitive. Qed.

(* The two encoded decks agree away from positions 3 and 4. *)
Local Lemma encode_agree_off34 (i : 'I_8) :
  i != (@Ordinal 8 3 isT) -> i != (@Ordinal 8 4 isT) ->
  tnth (orbit_encode true) i = tnth (orbit_encode false) i.
Proof.
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hlt // _ _; apply: val_inj.
Qed.
```

For `encode_agree_off34`: at codes 3 and 4 the corresponding disequality hypothesis is false (both sides are the same ordinal up to `val`), so those branches discharge by the hypothesis itself; the worker may need `move=> /negP[]` or `rewrite eqE /=` per branch — probe with `rocq_step_multi`.

- [ ] **Step 5.2: The transfer lemma:**

```coq
(** pgl27_six_reveal_ambiguous — for every two hidden positions there are two
    valid decks of opposite orbit classes agreeing on the six revealed
    positions.
    @main security: six revealed cards never determine the orbit class. *)
Lemma pgl27_six_reveal_ambiguous (p q : 'I_8) : p != q ->
  exists sh1 sh2 : 8.-tuple 'I_8,
    [/\ deck_ok sh1, deck_ok sh2, orbit_class sh1 != orbit_class sh2 &
        forall i : 'I_8, i != p -> i != q -> tnth sh1 i = tnth sh2 i].
Proof.
move=> npq.
pose p3 : 'I_8 := @Ordinal 8 3 isT.
pose p4 : 'I_8 := @Ordinal 8 4 isT.
have Hpq : [tuple p; q] \in 2.-dtuple([set: 'I_8]).
  rewrite inE; apply/andP; split.
    by rewrite /= !inE andbT npq.
  by apply/subsetP => u _; rewrite inE.
have H34 : [tuple p3; p4] \in 2.-dtuple([set: 'I_8]).
  rewrite inE; apply/andP; split=> //.
  by apply/subsetP => u _; rewrite inE.
have Htr := pgl27_2transitive.
rewrite /ntransitive pgl27_rho_im in Htr.
have [g gG Hg] := atransP2 Htr Hpq H34.
have [Hgp Hgq] : g p = p3 /\ g q = p4.
  move: Hg => /(congr1 (fun t : 2.-tuple 'I_8 => (tnth t (@Ordinal 2 0 isT),
                                                  tnth t (@Ordinal 2 1 isT)))).
  by rewrite !tnth_map => -[-> ->].
exists [tuple tnth (orbit_encode true) (@pgg_rho pgl27_M g i) | i < 8],
       [tuple tnth (orbit_encode false) (@pgg_rho pgl27_M g i) | i < 8].
split.
- by rewrite -[deck_ok _]/(deck_ok _) (deck_stable g _ gG) orbit_encode_deck.
- by rewrite (deck_stable g _ gG) orbit_encode_deck.
- by rewrite !(orbit_class_invariant g _ gG) !orbit_encodeK.
- move=> i nip niq; rewrite !tnth_mktuple; apply: encode_agree_off34.
  + apply: contra nip => /eqP Hgi; apply/eqP; apply: (@perm_inj _ g).
    by rewrite Hgi Hgp.
  + apply: contra niq => /eqP Hgi; apply/eqP; apply: (@perm_inj _ g).
    by rewrite Hgi Hgq.
Qed.
```

Direction check (audited): the deck action `d_k i = tnth (orbit_encode k) (rho g i)` differs between k = true/false exactly on `(rho g)^-1 {3,4}`, so the pair `(p,q)` must map TO `(3,4)`; `atransP2` is applied with `x := [tuple p; q]`, `y := [tuple 3; 4]`. `atransP2` gives `y = to x a` coordinatewise under `'P * 2`; extracting the two coordinates uses `tnth_map` (n_act is a map) plus `apermE`/`permE` as needed — expect friction, use `Show` and `rocq_step_multi`. Since `rho` is the identity inclusion, `@pgg_rho pgl27_M g i` is convertible to `g i`; if the `tnth_mktuple` rewrite leaves `pgg_rho` wrappers, add `rewrite [pgg_rho _ _]/=` or unfold via `rewrite /=`.

- [ ] **Step 5.3:** `rocq_compile_file` on `pgl27_recovery.v`. Expected: clean. Then `rocq_query "Print Assumptions pgl27_six_reveal_ambiguous."` (file mode). Expected: `Closed under the global context` (no boolp needed — pure combinatorics).
- [ ] **Step 5.4:** Update `pgl27_scheme.v` header sentence (line 8-9): replace "while reconstruction reads all eight endpoints" with "while the implemented reconstruction reads all eight endpoints; seven already determine the class and six never do (pgl27_recovery.v)". Also add the reveal-phase qualifier sentence to this header now (same sentence as Task 9.1), so the file is touched once; Task 9 then skips `pgl27_scheme.v`. Statement comment at line ~75 (`orbit_scheme`) stays terse; only ensure it says "reads", not "requires".
- [ ] **Step 5.5:** Rebuild scheme downstream if the header edit touched it (comment-only edit still changes the file): `make -j1 pgg-smc/instances/pgl27/pgl27_trace.vo`. Expected: clean.
- [ ] **Step 5.6: Commit.**

```bash
git add pgg-smc/instances/pgl27/pgl27_recovery.v _CoqProject pgg-smc/instances/pgl27/pgl27_scheme.v
git commit -m "pgl27: sharp recovery threshold (7 reveals determine, 6 never do)

New pgl27_recovery.v: missing-card determination at seven reveals;
2-transitive transfer of the encode-pair witness to every hidden
position pair. Scheme header reframed: reveal-all is the implemented
decoder, not an information-theoretic necessity."
```

---

### Task 6: Kernel-product lemmas in `transitivity_privacy.v`

**Files:**
- Modify: `pgg-smc/reconstruct/transitivity_privacy.v` (insert two new sections after `Section uniform_bijection` ends, line ~127)

- [ ] **Step 6.1: Kernel independence section:**

```coq
Section kernel_independence.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (R : realType) (A B : finType) (P : R.-fdist A) (W : A -> R.-fdist B).

(** inde_prod_kernel_fst == over a kernel product, a random variable whose
    conditional law given any first coordinate of positive mass is a fixed
    law is independent of the first coordinate.
    @composes: ttrans_view_indep_alldecks *)
Lemma inde_prod_kernel_fst (T : finType) (Z : A * B -> T) (mu : R.-fdist T) :
  (forall a, P a != 0 -> fdistmap (fun b => Z (a, b)) (W a) = mu) ->
  (P `X W) |= (Z : {RV (P `X W) -> T})
    _|_ ((fun ab => ab.1) : {RV (P `X W) -> A}).

(** fdistmap_prod_const == a kernel product pushes forward to the common law
    of its positive-mass sections.
    @composes: ttrans_view_indep_alldecks *)
Lemma fdistmap_prod_const (T : finType) (f : A * B -> T) (mu : R.-fdist T) :
  (forall a, P a != 0 -> fdistmap (fun b => f (a, b)) (W a) = mu) ->
  fdistmap f (P `X W) = mu.

(** fdistmap_prod_snd_const == over a product with a constant kernel, if every
    positive-mass second-coordinate section pushes the first marginal to the
    same law, the pair pushforward is that law.
    @composes: alldecks_shuffle_absorb *)
Lemma fdistmap_prod_snd_const (T : finType) (P2 : R.-fdist B)
    (f : A * B -> T) (mu : R.-fdist T) :
  (forall b, P2 b != 0 -> fdistmap (fun a => f (a, b)) P = mu) ->
  fdistmap f (P `x P2) = mu.

End kernel_independence.
```

Proof guidance: `inde_prod_kernel_fst` mirrors `inde_prod_fst` (lines 62-103 of the same file) step by step; `fdist_prodE` already yields `P ab.1 * W ab.1 ab.2` for kernels; in the `HZa` block add the case split `have [Pa0|Pa0] := eqVneq (P a) 0` — in the zero branch both sides vanish (`Pa0` kills each summand and the RHS via `mul0r`); in the positive branch use the hypothesis at `a`. `fdistmap_prod_const` is the `HZz` sub-argument of the same proof extracted standalone: `fdist_ext t; rewrite fdistmapE; partition_big` over `ab.1`, per-`a` block equals `P a * mu t` (zero case as above), then `-big_distrl FDist.f1 mul1r`. `fdistmap_prod_snd_const`: either swap via `fdistX` machinery (`fdistXE`, `fdistX_prod` if present — Search first: `rocq_query "Search fdistX fdist_prod."`) or prove directly by the mirrored `partition_big` over `ab.2` — the direct proof is the fallback and is authorized immediately if the Search comes back empty.

- [ ] **Step 6.2: Uniform-support bijection section:**

```coq
Section uniform_supp_bij.
Local Open Scope ring_scope.
Variables (R : realType) (A : finType) (C : {set A}).
Hypothesis HC : (0 < #|C|)%N.

(** fdist_uniform_supp_bij == an injective endomap stabilising the support
    pushes the uniform-support law to itself.
    @composes: alldecks_shuffle_absorb *)
Lemma fdist_uniform_supp_bij (f : A -> A) :
  injective f -> (forall a, (f a \in C) = (a \in C)) ->
  fdistmap f (fdist_uniform_supp R HC) = fdist_uniform_supp R HC.

End uniform_supp_bij.
```

Proof guidance: mirror `bij_uniform` (lines 112-127): `injF_bij` upgrades `f` to a bijection with inverse `f'`; `fdist_ext a; fdistmapE`; the preimage of `a` is the singleton `f' a`; case on `a \in C` — by stability `f' a \in C` iff `a \in C`; `fdist_uniform_supp_in` / `fdist_uniform_supp_notin` finish. Check the exact `` `U `` notation and constructor arguments first with `rocq_query "About fdist_uniform_supp."`.

- [ ] **Step 6.3:** Each lemma: write statement with `Admitted.`, confirm it typechecks via `rocq_check`, then develop the proof interactively and replace. Whole-file compile at the end of the task: `rocq_compile_file` on `transitivity_privacy.v`. Expected: clean, existing lemmas untouched.

---

### Task 7: Generic all-decks section in `transitivity_privacy.v`

**Files:**
- Modify: `pgg-smc/reconstruct/transitivity_privacy.v` (append a new section AFTER `Section transitivity_privacy_gen`, i.e. at file end)

- [ ] **Step 7.1: Section header and forced definitions.** Variable order is pinned; unused hypotheses discharge away silently, so anything unused is simply dropped — do not reorder:

```coq
Section alldecks_view_indep.
Local Open Scope ring_scope.
Local Open Scope proba_scope.
Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
Variable t : nat.
Hypothesis Htrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P.
Variable R : realType.
Variable secretP : R.-fdist bool.
Hypothesis HG : (0 < #|G|)%N.
Variable orbit_class : N'.+1.-tuple 'I_N'.+1 -> bool.
Variable deck_ok : N'.+1.-tuple 'I_N'.+1 -> bool.
Hypothesis Hdeck_uniq : forall sh, deck_ok sh -> uniq sh.
Hypothesis Hinv : forall g sh, g \in G ->
  orbit_class [tuple tnth sh (rho g i) | i < N'.+1] = orbit_class sh.
Hypothesis Hdeck_stable : forall g sh, g \in G ->
  deck_ok [tuple tnth sh (rho g i) | i < N'.+1] = deck_ok sh.

(** class_decks == the valid decks of orbit class s.
    @intent: the support of the all-decks dealer at secret s. *)
Definition class_decks (s : bool) : {set N'.+1.-tuple 'I_N'.+1} :=
  [set sh | deck_ok sh && (orbit_class sh == s)].

Hypothesis Hpop : forall s : bool, (0 < #|class_decks s|)%N.

(** alldecksP == the joint law of a secret, a uniform valid deck of that
    class, and an independent uniform shuffle.
    @intent: the all-decks dealer sample space. *)
Definition alldecksP : R.-fdist (bool * (N'.+1.-tuple 'I_N'.+1 * gT)) :=
  secretP `X (fun s => (`U (Hpop s)) `x (`U HG)).

(** alldecks_secret == the dealt secret component.
    @intent: the secret random variable of the all-decks dealer. *)
Definition alldecks_secret : {RV alldecksP -> bool} := fun u => u.1.

(** alldecks_view == the dealt card values a coalition C observes after the
    shuffle, and ord0 outside C.
    @intent: the coalition observable of the all-decks dealer. *)
Definition alldecks_view (C : {set 'I_N'.+1}) :
    {RV alldecksP -> {ffun 'I_N'.+1 -> 'I_N'.+1}} :=
  fun u => [ffun i => if i \in C then tnth u.2.1 (rho u.2.2 i) else ord0].
```

Check whether `` `U (Hpop s) `` elaborates (the notation takes the positivity proof; the set is inferred from its type). If inference fails, use the explicit `fdist_uniform_supp R (Hpop s)` form everywhere.

- [ ] **Step 7.2: The deck-and-shuffle independence theorem:**

```coq
(** ttrans_view_indep_alldecks == a dealer dealing a uniform valid deck of the
    secret's class followed by a t-transitive uniform shuffle gives every
    coalition of at most t positions a view independent of the secret.
    @main security: the all-decks dealer privacy bridge. *)
Lemma ttrans_view_indep_alldecks (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N -> alldecksP |= alldecks_view C _|_ alldecks_secret.
```

Proof skeleton (adapt `ttrans_view_indep_gen`, lines 484-519 of the same file):
1. `pose k := size (enum C)`, `pose p := in_tuple (enum C)`, derive `Hk`, `Hp`, `Hdt` exactly as there.
2. `pose maskf := ...` identical to line 497.
3. Apply `inde_prod_kernel_fst` with `mu := fdistmap maskf (`U Hdt)`. Note `alldecks_secret` is `u.1` — the same `fun ab => ab.1` shape the lemma expects; if the RV coercion resists unification, `rewrite /alldecks_secret` or restate via `exact:` with explicit type ascriptions.
4. Per-s obligation: `fdistmap (fun dg => alldecks_view C (s, dg)) ((`U (Hpop s)) `x (`U HG)) = mu`. Apply `fdistmap_prod_const` (first coordinate = deck). Per-deck obligation at `sh` with `(`U (Hpop s)) sh != 0`: membership `sh \in class_decks s` via `fdist_uniform_supp` support characterization (`fdist_uniform_supp_notin` contrapositive, or Search for `fdist_uniform_supp_neq0`), hence `deck_ok sh` hence `uniq sh` by `Hdeck_uniq`.
5. The section over `g` at fixed `sh` composes as `maskf \o (fun g => [tuple tnth sh (rho g (tnth p l)) | l < k])` — the identical `Hcomp` funext argument of lines 501-516 with `encode b` replaced by `sh`. Then `-fdistmap_comp` and `ktuple_encode_uniform` with `encode := fun _ => sh`, `b := true`, `Hub := uniq sh`.

- [ ] **Step 7.3: Shuffle absorption and the shuffle-free theorem:**

```coq
(** alldecks_shuffle_absorb == the uniform shuffle preserves the uniform law
    on the valid decks of a class.
    @composes: ttrans_view_indep_deck *)
Lemma alldecks_shuffle_absorb (s : bool) :
  fdistmap (fun shg : N'.+1.-tuple 'I_N'.+1 * gT =>
              [tuple tnth shg.1 (rho shg.2 i) | i < N'.+1])
           ((`U (Hpop s)) `x (`U HG))
  = `U (Hpop s).
```

Proof skeleton: `fdistmap_prod_snd_const` over the shuffle coordinate; at fixed `g` with `(`U HG) g != 0` (hence `g \in G`), the section is `fdistmap (act g) (`U (Hpop s))` where `act g sh := [tuple tnth sh (rho g i) | i < N'.+1]`; close with `fdist_uniform_supp_bij`:
- injectivity of `act g`: two decks with equal `g`-reindexed tuples are equal by `eq_from_tnth` + evaluating at `rho (g^-1) i`-style indices, or directly: `apply/eq_from_tnth => i; move/(congr1 (fun sh => tnth sh (rho g^-1 ... )))` — the clean route is `tnth (act g sh) i = tnth sh (rho g i)` (by `tnth_mktuple`) and `rho g` is a bijection of indices, so `act g` is `sh ∘ (rho g)` reindexing: injective because reindexing along a bijection is injective (`eq_from_tnth` with `j := (rho g)^-1 i` — note `rho g^-1 = (rho g)^-1` by `morphV` since `g \in G`).
- support stability: `act g sh \in class_decks s = (sh \in class_decks s)` by `inE`, `Hdeck_stable`, `Hinv`.

```coq
(** uniform_deckP == the joint law of a secret and a uniform valid deck of
    that class, with no shuffle.
    @intent: the shuffle-free all-decks dealer sample space. *)
Definition uniform_deckP : R.-fdist (bool * N'.+1.-tuple 'I_N'.+1) :=
  secretP `X (fun s => `U (Hpop s)).

(** uniform_deck_view == the dealt card values a coalition C reads directly
    off the dealt deck, and ord0 outside C.
    @intent: the coalition observable of the shuffle-free dealer. *)
Definition uniform_deck_view (C : {set 'I_N'.+1}) :
    {RV uniform_deckP -> {ffun 'I_N'.+1 -> 'I_N'.+1}} :=
  fun u => [ffun i => if i \in C then tnth u.2 i else ord0].

(** ttrans_view_indep_deck == a dealer dealing a uniform valid deck of the
    secret's class gives, with no further shuffle, every coalition of at most
    t positions a view independent of the secret.
    @main security: representative-free all-decks privacy. *)
Lemma ttrans_view_indep_deck (C : {set 'I_N'.+1}) :
  (#|C| <= t)%N ->
  uniform_deckP |= uniform_deck_view C
    _|_ ((fun u => u.1) : {RV uniform_deckP -> bool}).

End alldecks_view_indep.
```

Proof skeleton for `ttrans_view_indep_deck`: `inde_prod_kernel_fst` with the same `mu`; per-s obligation `fdistmap (restrict_C) (`U (Hpop s)) = mu` where `restrict_C sh := [ffun i => if i \in C then tnth sh i else ord0]`: rewrite `` `U (Hpop s) `` backwards along `alldecks_shuffle_absorb s`, then `fdistmap_comp` composes `restrict_C ∘ act` which is exactly the per-s section of `alldecks_view`, already computed = `mu` in the Task 7.2 proof — extract that computation as a `Local` helper lemma (`alldecks_view_law`) used by both theorems to avoid duplicating the argument:

```coq
(* The per-class law of the shuffled coalition view, deck-independent. *)
Local Lemma alldecks_view_law (C : {set 'I_N'.+1}) (k := size (enum C)) ... 
```

(The worker shapes `alldecks_view_law`'s exact statement while proving 7.2: it should state `fdistmap (fun dg => alldecks_view C (s, dg)) ((`U (Hpop s)) `x (`U HG)) = fdistmap maskf (`U Hdt)` with `maskf`, `Hdt` fixed as in the skeleton; both 7.2 and 7.3 then consume it.)

- [ ] **Step 7.4:** Whole-file compile: `rocq_compile_file` on `transitivity_privacy.v`. Expected: clean; then `rocq_query "Print Assumptions ttrans_view_indep_deck."` in file mode. Expected: boolp only (funext via `boolp.funext` in `Hcomp`).

---

### Task 8: Instance layer in `pgl27_secrecy.v`, commit 3

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_secrecy.v` (append inside `Section pgl27_secrecy`; the section has `Variable R : realType` in scope)

- [ ] **Step 8.1: Positivity and instance statements:**

```coq
(** pgl27_class_decks_pos — both orbit classes are realised by valid decks,
    so each class-conditional uniform deck law is well defined.
    @composes: pgl27_view_indep_alldecks *)
Lemma pgl27_class_decks_pos (s : bool) :
  (0 < #|class_decks (N':=7) orbit_class deck_ok s|)%N.
Proof.
apply/card_gt0P; exists (orbit_encode s).
by rewrite inE orbit_encode_deck orbit_encodeK eqxx.
Qed.

(** pgl27_view_indep_alldecks — a dealer dealing a uniform valid deck of the
    secret's class followed by the uniform PGL(2,7) shuffle gives every
    coalition of at most three cards a view independent of the orbit secret.
    @main security: all-decks dealer coalition privacy at three cards. *)
Lemma pgl27_view_indep_alldecks (C : {set 'I_8}) : (#|C| <= 3)%N ->
  alldecksP (fdist_uniform card_bool) pgl27_class_decks_pos pgl27_G_pos
  |= alldecks_view (rho := @pgg_rho pgl27_M) ... C
  _|_ alldecks_secret ... .

(** pgl27_view_indep_deck — a dealer dealing a uniform valid deck of the
    secret's class gives, with no further shuffle, every coalition of at most
    three cards a view independent of the orbit secret.
    @main security: representative-free all-decks privacy at three cards. *)
Lemma pgl27_view_indep_deck (C : {set 'I_8}) : (#|C| <= 3)%N -> ... .
```

The exact argument lists of the instantiated statements depend on how the section variables of `alldecks_view_indep` discharge (declaration order, unused dropped). The worker MUST first run `rocq_query "About ttrans_view_indep_alldecks." / "About alldecksP."` (file mode on the recompiled `transitivity_privacy.v`) and copy the discharged signatures, then shape the instance statements as direct `exact:` applications in the style of the existing `pgl27_view_indep` (lines 66-73): arguments will be drawn from `pgl27_3transitive`, `fdist_uniform card_bool`, `pgl27_G_pos`, `orbit_class`, `deck_ok`, `(fun sh H => H : deck_ok sh -> uniq sh)` (note `deck_ok = uniq` definitionally, so `id` works: `fun sh => id`), `orbit_class_invariant`-shaped and `deck_stable`-shaped arguments (their statements in `pgl27_orbit.v:283,302` match the hypothesis shapes with `g \in pgg_G pgl27_M` premises in the same order), and `pgl27_class_decks_pos`. If a hypothesis-shape mismatch appears (argument order g/sh), wrap in a lambda.

- [ ] **Step 8.2: Header update** for `pgl27_secrecy.v`: add the two new key results to the header list and the sentence "The all-decks dealer results remove the fixed-representative scope limit: the dealt deck is uniform over ALL valid decks of the class."
- [ ] **Step 8.3:** Compile: `make -j1 pgg-smc/instances/pgl27/pgl27_secrecy.vo` (after `rm -f`), then `make -j1 pgg-smc/instances/pgl27/pgl27_trace.vo` (secrecy is imported downstream). `rocq_query "Print Assumptions pgl27_view_indep_deck."` — expected: boolp only.
- [ ] **Step 8.4: Commit.**

```bash
git add pgg-smc/reconstruct/transitivity_privacy.v pgg-smc/instances/pgl27/pgl27_secrecy.v
git commit -m "pgl27: all-decks dealer privacy (kernel-product bridge + instance)

Generic alldecks section: deck-and-shuffle independence and the
shuffle-free uniform-deck corollary via shuffle absorption; pgl27
instantiation closes the fixed-representative scope limit."
```

---

### Task 9: Prose sweep, docs, memory, commit 4

**Files:**
- Modify: `pgg-smc/instances/pgl27/pgl27_secrecy.v`, `pgl27_trace.v`, `pgl27_run.v` (headers only)
- Modify: `docs/superpowers/specs/2026-07-11-pgl27-orbit-class-design.md`, `docs/superpowers/plans/2026-07-11-pgl27-orbit-class.md` (post-notes)
- Modify: memory files `project_pgl27_instance_landed.md`, `project_pgl27_audit_findings.md` (in the auto-memory directory)

- [ ] **Step 9.1: The qualifier sentence**, verbatim, for each file header (`pgl27_secrecy.v`, `pgl27_trace.v`, `pgl27_run.v`): `(* The secrecy statements concern the pre-reveal execution: after the public reveal every player learns the secret by design. *)` — placed as the last paragraph of the header comment block, adapted to the box-comment layout of each file.
- [ ] **Step 9.2:** `pgl27_run.v` header additionally gets: "The implemented decoder reads all eight endpoints; seven already determine the class and six never do (pgl27_recovery.v)."
- [ ] **Step 9.3:** 2026-07-11 spec + plan post-notes: append one dated paragraph each: axiom now a theorem (commit ref of Task 3), "(no sub-8 recovery)" superseded by the sharp 7/6 pair (commit ref of Task 5), all-decks dealer landed (commit ref of Task 8), reveal-phase qualifier added.
- [ ] **Step 9.4:** Memory updates (Write tool, update the two existing files in place; keep MEMORY.md hooks accurate): `project_pgl27_instance_landed.md` — axioms line becomes "boolp only (pgl27_3transitive PROVEN in-kernel 2026-07-12)"; add the sharp recovery pair and the all-decks dealer results. `project_pgl27_audit_findings.md` — mark the four open items closed with lemma names.
- [ ] **Step 9.5:** Comment-only .v edits still recompile: `make -j1 pgg-smc/instances/pgl27/pgl27_trace.vo`. Expected: clean.
- [ ] **Step 9.6: Commit.**

```bash
git add pgg-smc/instances/pgl27/pgl27_secrecy.v pgg-smc/instances/pgl27/pgl27_trace.v pgg-smc/instances/pgl27/pgl27_run.v docs/superpowers/specs/2026-07-11-pgl27-orbit-class-design.md docs/superpowers/plans/2026-07-11-pgl27-orbit-class.md
git commit -m "pgl27: reveal-phase prose sweep and status post-notes

Mid-execution qualifier in the three headers; spec/plan post-notes
updated for the axiom proof, the sharp 7/6 recovery pair, and the
all-decks dealer."
```

---

## Final verification (after Task 9)

- [ ] `grep -rn "^Axiom" pgg-smc/instances/pgl27/` → empty.
- [ ] `rocq_query "Print Assumptions pgl27_3transitive."` → closed under the global context.
- [ ] `rocq_query "Print Assumptions pgl27_six_reveal_ambiguous."` → closed under the global context.
- [ ] `rocq_query "Print Assumptions pgl27_view_indep_deck."` → boolp only.
- [ ] All six pre-existing pgl27 `.vo` files + `pgl27_recovery.vo` rebuilt via `make -j1`.
- [ ] `git log --oneline -5` shows the four commits.
