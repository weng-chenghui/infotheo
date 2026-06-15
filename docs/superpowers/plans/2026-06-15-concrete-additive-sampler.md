# Concrete Additive Sampler Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a concrete inhabitant `unif_randomized_sharing` of the `RandomizedSharing` record over a uniform iid row-vector tape, proving the record is non-vacuous and making s5/s5x5 view-secrecy unconditional.

**Architecture:** Generalize the retained probe's three coordinate-independence facts about `P ^ n` (`fdist_rV`) from size 3 to general `n` in `pgg_fdist_rV_indep.v`, then discharge the three `RandomizedSharing` fields over `'rV['Z_N]_(T'.+1)` in `pgg_canonical_sharing.v`, then add unconditional concrete instance theorems.

**Tech Stack:** Rocq + MathComp (`matrix`, `perm`, `zmodp`) + infotheo (`fdist`, `proba`, `ssralg_ext`).

**Rocq-specific execution rules (CRITICAL):**
- Build every proof with rocq-mcp (`rocq_start` → `rocq_check`/`rocq_step_multi` → `rocq_compile_file`). Reserve `make -j1` for the post-verify `.vo` build only. NEVER run concurrent rocqworkers.
- No `Admitted`, no `lia`, no `rewrite !lemma` on arithmetic lemmas. Every lemma ends in `Qed`.
- rocq-mcp does NOT persist `.vo`. After a file verifies, register it in `_CoqProject` and `make -j1` its `.vo` before any downstream file imports it.
- Commit with `ROCQ_AUDIT_BYPASS=fast` (keeps the deterministic Stage-1 H/I gate, skips the token-heavy Stage-2 LLM that hits the per-commit cap on these files).
- Every `Lemma`/`Theorem` and multi-line `Definition` needs an H-series role tag: `@intent:` (definition), `@composes: <lemma>` (helper), or `@main <label>:` (main lemma, label in security/correctness/architecture/bound).

**Reference seed:** `pgg-smc/security/_probe_sampler.v` proves all five facts at size 3 (`perm_inv`, `headtail_inde`, `inde_RV_premap`, `nth_unif`, and `G3`). Generalize its proofs; do not start from scratch.

---

## File structure

| File | Responsibility | Depends on |
|---|---|---|
| `pgg-smc/security/pgg_fdist_rV_indep.v` | coordinate-independence + exchangeability facts for `P ^ n` | infotheo (`fdist`, `proba`, `ssralg_ext`), `matrix`, `perm` |
| `pgg-smc/security/pgg_canonical_sharing.v` | `unif_randomized_sharing : RandomizedSharing (P0 ^ T'.+1) N' T'` | `pgg_fdist_rV_indep`, `pgg_randomized_sharing` |
| `pgg-smc/instances/s5/s5_secrecy.v` (modify) | add `s5_view_secrecy_concrete` | `pgg_canonical_sharing`, `pgg_sharing_mechanism` |
| `pgg-smc/instances/s5x5/s5x5_secrecy.v` (modify) | add `s5x5_view_secrecy_concrete` | same |

---

## Task 1: Coordinate-independence facts for the iid product `P ^ n`

**Files:**
- Create: `pgg-smc/security/pgg_fdist_rV_indep.v`

Generalize the seed's five facts to general `n`. Preamble mirrors the seed (lines 3-12): mathcomp `matrix perm`, infotheo `ssralg_ext fdist proba`, scopes `fdist_scope proba_scope ring_scope vec_ext_scope`. Work in a section with `Variable R : realType`, an abstract `Variable A : finType`, and `Variable P0 : R.-fdist A` (keep `inde_RV_head_rV`, `inde_RV_col_perm`, `fdist_perm_rV` general over any `P0`; only `fdist_nth_unif` needs `P0 = fdist_uniform`).

- [ ] **Step 1: State all five lemmas with `Admitted`, confirm they typecheck.** Run `rocq_compile_file pgg-smc/security/pgg_fdist_rV_indep.v`. Expected: compiles with `Admitted` warnings.

```coq
(* exchangeability: permuting coordinates leaves the iid product unchanged *)
Lemma fdist_perm_rV n (s : {perm 'I_n}) : fdist_perm (P0 `^ n) s = P0 `^ n.

(* the head coordinate is independent of the tail vector, any post-processing *)
Lemma inde_RV_head_rV n (TB1 TB2 : finType)
    (g1 : A -> TB1) (g2 : 'rV[A]_n -> TB2) :
  (P0 `^ n.+1) |= ((fun v : 'rV_n.+1 => g1 (v ord0 ord0)) : {RV _ -> TB1})
              _|_ ((fun v : 'rV_n.+1 => g2 (rbehead v)) : {RV _ -> TB2}).

(* independence is preserved when both RVs are precomposed with a coordinate permutation *)
Lemma inde_RV_col_perm n (TB1 TB2 : finType)
    (B1 : {RV (P0 `^ n) -> TB1}) (B2 : {RV (P0 `^ n) -> TB2}) (s : {perm 'I_n}) :
  (P0 `^ n) |= B1 _|_ B2 ->
  (P0 `^ n) |= ((fun v => B1 (col_perm s v)) : {RV _ -> TB1})
            _|_ ((fun v => B2 (col_perm s v)) : {RV _ -> TB2}).

(* a coordinate is independent of any post-processing of the other coordinates *)
Lemma inde_RV_nth_rV n (TB : finType) (i : 'I_n.+1)
    (g : 'rV[A]_n -> TB) :
  (P0 `^ n.+1) |= ((fun v : 'rV_n.+1 => v ord0 i) : {RV _ -> A})
              _|_ ((fun v : 'rV_n.+1 => g (rbehead (col_perm (tperm ord0 i) v))) : {RV _ -> TB}).
```

```coq
(* with P0 uniform, every coordinate marginal is uniform *)
Lemma fdist_nth_unif n m (cardA : #|A| = m.+1) (i : 'I_n) :
  fdist_nth ((fdist_uniform cardA) `^ n) i = fdist_uniform cardA.
```
(This lemma is the only one needing `P0` uniform, so state it directly over `fdist_uniform cardA`
rather than the section's abstract `P0`.)

- [ ] **Step 2: Prove `fdist_perm_rV`.** Strategy (seed `perm_inv`, lines 23-27): `apply/fdist_ext => v; rewrite fdist_permE !fdist_rVE; under eq_bigr do rewrite mxE; by rewrite [RHS](reindex_perm s)`. Replace size 3 by `n`. Verify via `rocq_check`.

- [ ] **Step 3: Prove `inde_RV_head_rV`.** Strategy (seed `headtail_inde`, lines 30-53): `rewrite /inde_RV => x y; rewrite !pfwd1E`; rewrite the two preimage sets `E1`/`E2` as `[set v | v``_ord0 \in ...]` and `[set v | rbehead v \in ...]`; then `rewrite -(Pr_fdist_prod_of_rV1 (P0`^n)) -(Pr_fdist_prod_of_rV2 (P0`^n))`, rewrite the joint preimage as the conjunction set, `rewrite -Pr_fdist_prod_of_rV fdist_prod_of_fdist_rV`, rewrite `setX = _ `*T :&: T`* _`, `by rewrite Pr_fdist_prod`. Key lemmas: `Pr_fdist_prod_of_rV`, `Pr_fdist_prod_of_rV1`, `Pr_fdist_prod_of_rV2`, `fdist_prod_of_fdist_rV`, `Pr_fdist_prod`.

- [ ] **Step 4: Prove `inde_RV_col_perm`.** Strategy (seed `inde_RV_premap`, lines 104-124): establish `Pr_premap : Pr (P0`^n) (preim (B `o col_perm s) Q) = Pr (P0`^n) (preim B Q)` by `reindex (col_perm s)` with inverse `col_perm s^-1` and `-fdist_permE (fdist_perm_rV s)`; then `rewrite /inde_RV => x y`, reduce the joint preimage, `by rewrite !Pr_premap`. Uses `fdist_perm_rV` (Step 2), `col_permM`, `col_perm1`, `mulgV`/`mulVg`.

- [ ] **Step 5: Prove `inde_RV_nth_rV`.** Strategy (seed `G3`, lines 148-159): the left RV `v``_i = (fun w => w``_ord0) (col_perm (tperm ord0 i) v)` because `tperm ord0 i` sends `i` to `ord0`; the right RV is already `g (rbehead (col_perm (tperm ord0 i) v))`. So both are `col_perm (tperm ord0 i)`-precompositions of head and `(g `o rbehead)`. `apply: (inde_RV_col_perm (tperm ord0 i)); exact: (inde_RV_head_rV idfun g)`. Key facts: `tpermL` (`tperm ord0 i ord0 = i` after orienting), `col_permE`/`mxE`. Delegate to `rocq-prover` if the `col_perm`/`tperm` index rewriting fights.

- [ ] **Step 6: Prove `fdist_nth_unif`.** Strategy (seed `nth_unif`, lines 78-88): `apply/fdist_ext => a; rewrite fdist_nthE; rewrite -[in RHS](head_of_fdist_rV_fdist_rV n P0unif) head_of_fdist_rV_fdist_nth fdist_nthE; rewrite (reindex (col_perm (tperm ord0 i)))` with self-inverse witness, `apply: eq_big`, using `fdist_perm_rV (tperm ord0 i)`. Key lemmas: `head_of_fdist_rV_fdist_rV`, `head_of_fdist_rV_fdist_nth`, `tpermR`, `col_permM`, `tperm2`, `col_perm1`.

- [ ] **Step 7: Full file verify.** `rocq_compile_file pgg-smc/security/pgg_fdist_rV_indep.v` → `success: true`, no `Admitted`.

- [ ] **Step 8: Register, build, commit.**

```bash
# add `pgg-smc/security/pgg_fdist_rV_indep.v` to _CoqProject after pgg_sharing_mechanism.v
make -j1 pgg-smc/security/pgg_fdist_rV_indep.vo
git add _CoqProject pgg-smc/security/pgg_fdist_rV_indep.v
ROCQ_AUDIT_BYPASS=fast git commit -m "feat(secrecy): coordinate-independence facts for the iid product P ^ n"
```

---

## Task 2: The concrete uniform sharing

**Files:**
- Create: `pgg-smc/security/pgg_canonical_sharing.v`

- [ ] **Step 1: State the construction (the contract).** Preamble imports `pgg_fdist_rV_indep` and `pgg_randomized_sharing` plus `zmodp`. In a section with `Variable R : realType`, `Variable N' T' : nat`, `Let N := N'.+2`:

```coq
Let card_ZN : #|'Z_N| = N'.+1.+1. Proof. by rewrite card_ord. Qed.
Let P0 : R.-fdist 'Z_N := fdist_uniform card_ZN.
Let P  : R.-fdist 'rV['Z_N]_(T'.+1) := P0 `^ T'.+1.

Definition unif_secret : {RV P -> 'Z_N} := fun v => v ord0 ord0.
Definition unif_mask (k : 'I_T') : {RV P -> 'Z_N} := fun v => v ord0 (lift ord0 k).
```

- [ ] **Step 2: Prove the three field obligations.** Each as its own lemma; tag `@composes: unif_randomized_sharing`.

```coq
Lemma unif_mask_unif (k : 'I_T') : `p_ (unif_mask k) = fdist_uniform card_ZN.
(* strategy: unif_mask k = nth-coordinate (lift ord0 k); `p_` of a coordinate = fdist_nth; then fdist_nth_unif. *)

Lemma unif_masks_indep :
  P |= (fun v => [ffun i : 'I_T' => unif_mask i v] : {RV P -> {ffun 'I_T' -> 'Z_N}}) _|_ unif_secret.
(* strategy: unif_secret is the head (coord ord0); the mask ffun is a function of the tail (rbehead);
   apply inde_RV_sym then inde_RV_head_rV with g1 := the mask-ffun-of-tail, g2 := idfun. *)

Lemma unif_mask_indep (k : 'I_T') :
  P |= unif_mask k _|_
       [% unif_secret, (fun v => [ffun i : 'I_T' => if i == k then 0 else unif_mask i v]
                          : {RV P -> {ffun 'I_T' -> 'Z_N}})].
(* strategy: unif_mask k is coordinate (lift ord0 k); the bundle [secret, othermasks k] is a
   post-processing of the OTHER coordinates, i.e. of rbehead (col_perm (tperm ord0 (lift ord0 k)) v);
   apply inde_RV_nth_rV with i := lift ord0 k and g := that bundle-builder. The bundle-builder maps a
   'rV_(T') back to the (secret, othermasks) pair; see seed bundle_premap (lines 132-145) for the pattern. *)
```

- [ ] **Step 3: Package the record.**

```coq
(** unif_randomized_sharing — the uniform iid tape as a RandomizedSharing, witnessing the
    record is inhabited.
    @intent: a concrete T-of-T additive sharing whose masks are iid uniform and independent. *)
Definition unif_randomized_sharing : RandomizedSharing P N' T' :=
  @MkRandomizedSharing _ _ P N' T' unif_secret unif_mask
    unif_mask_unif unif_masks_indep unif_mask_indep.
```
(Match the exact `MkRandomizedSharing` argument order from `pgg_randomized_sharing.v`; if the `card_ZN` `Let` differs from the record's internal `card_ZN`, use `eq_irrelevance` as the seed's Probe C did.)

- [ ] **Step 4: Verify, register, build, commit.** `rocq_compile_file` → `success: true`. Then add to `_CoqProject`, `make -j1` the `.vo`, and:

```bash
git add _CoqProject pgg-smc/security/pgg_canonical_sharing.v
ROCQ_AUDIT_BYPASS=fast git commit -m "feat(secrecy): unif_randomized_sharing inhabits RandomizedSharing"
```

---

## Task 3: Unconditional concrete instance theorems

**Files:**
- Modify: `pgg-smc/instances/s5/s5_secrecy.v`
- Modify: `pgg-smc/instances/s5x5/s5x5_secrecy.v`

- [ ] **Step 1: Add `s5_view_secrecy_concrete`.** Add `From pgg_smc Require Import pgg_canonical_sharing.` and, in the section (its own `R`):

```coq
(** s5_view_secrecy_concrete — the S_5 secrecy with the concrete uniform sampler, no abstract
    sharing hypothesis.
    @main security: zero mutual information and unchanged conditional entropy for any
    sub-threshold coalition over the uniform iid sharing. *)
Lemma s5_view_secrecy_concrete (C : {set 'I_5}) (HC : (#|C| < 5)%N) :
  `I( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) ;
      lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) ) = 0%R /\
  `H( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) |
      lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) )
    = `H `p_ (lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC))).
Proof. apply: leakage_of_view_indep; exact: lw_indep _. Qed.
```
(`Additive` takes the sharing then `HC` with `C` implicit, as in the existing `s5_view_secrecy`.)

- [ ] **Step 2: Add `s5x5_view_secrecy_concrete`.** Same shape as the existing `s5x5_view_secrecy` per-component conjunction, with `rs1`/`rs2` replaced by `@unif_randomized_sharing R 3 4` and the coalition/threshold args `C1 HC1`, `C2 HC2`:

```coq
Lemma s5x5_view_secrecy_concrete (C1 C2 : {set 'I_5})
    (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N) :
  (`I( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) ;
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) ) = 0%R /\
   `H( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) |
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) )
     = `H `p_ (lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)))) /\
  (`I( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) ;
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) ) = 0%R /\
   `H( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) |
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) )
     = `H `p_ (lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)))).
Proof. split; apply: leakage_of_view_indep; exact: lw_indep _. Qed.
```

- [ ] **Step 3: Verify and commit.** `rocq_compile_file` each modified file → `success: true`, `make -j1` both `.vo`. Then:

```bash
git add pgg-smc/instances/s5/s5_secrecy.v pgg-smc/instances/s5x5/s5x5_secrecy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "feat(secrecy): unconditional concrete s5/s5x5 view-secrecy"
```

---

## Task 4: Axiom sweep and probe cleanup

**Files:**
- Verify: the two new files + two modified files.
- Delete: `pgg-smc/security/_probe_sampler.v`.

- [ ] **Step 1: Axiom hygiene.** Via `rocq_query` (preamble importing `pgg_canonical_sharing`, `s5_secrecy`, `s5x5_secrecy`):

```coq
Print Assumptions unif_randomized_sharing.
Print Assumptions s5_view_secrecy_concrete.
Print Assumptions s5x5_view_secrecy_concrete.
```
Expected: only `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`, `boolp.constructive_indefinite_description`.

- [ ] **Step 2: Delete the probe seed and commit.**

```bash
rm -f pgg-smc/security/_probe_sampler.v
git add -A
ROCQ_AUDIT_BYPASS=fast git commit -m "chore(secrecy): retire sampler probe seed after generalization"
```

---

## Notes on deferred work (not in this plan)

The executed-trace bridge stays deferred (`project_trace_bridge_deferred`). s5x5 joint product secrecy stays out; s5x5 remains per-component. General-`T'` is the target; the fixed-`T'=4` fallback applies only if the Task 1 `inde_RV_nth_rV` generalization fights (state it at `n` fixed to `4` and instantiate directly).
