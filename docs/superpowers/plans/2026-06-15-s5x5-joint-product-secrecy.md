# s5x5 Joint Product Secrecy Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove `s5x5_joint_view_secrecy`: the combined coalition view across both s5x5 components is independent of the joint secret `(s1, s2)`, unconditionally.

**Architecture:** A generic `leakage_product : LeakageWitness P1 -> LeakageWitness P2 -> LeakageWitness (P1 `x P2)` combinator, built from the probe-proven `joint_view_indep` plus two product-`fdist` helpers, instantiated for s5x5 with two copies of `unif_randomized_sharing` on the two factors.

**Tech Stack:** Rocq + MathComp + infotheo (`fdist`, `proba`, `graphoid`), du2002 (`spp_proba`).

**Rocq execution rules:** build proofs with rocq-mcp; no `Admitted`/`lia`; after a file verifies, register in `_CoqProject` and `make -j1` its `.vo` before downstream import; commit with `ROCQ_AUDIT_BYPASS=fast`; every Lemma/multi-line Definition needs an H-series role tag (`@intent:`/`@composes:`/`@main <label>:`).

---

## File structure

| File | Responsibility | Depends on |
|---|---|---|
| `pgg-smc/security/pgg_leakage_product.v` | `joint_view_indep`, `inde_RV_fst_snd`, `inde_RV_fst`/`inde_RV_snd`, `leakage_product` | infotheo, `spp_proba`, `pgg_leakage_witness` |
| `pgg-smc/instances/s5x5/s5x5_secrecy.v` (modify) | `s5x5_joint_view_secrecy` | `pgg_leakage_product`, `pgg_canonical_sharing`, `pgg_sharing_mechanism` |

---

## Task 1: The product combinator

**Files:**
- Create: `pgg-smc/security/pgg_leakage_product.v`

PREAMBLE: mathcomp (`ssreflect ... fintype finset ssralg reals`), infotheo (`realType_ext fdist proba graphoid`), `Require Import spp_proba.`, `From pgg_smc Require Import pgg_leakage_witness.` Open `fdist_scope`, `proba_scope`. (Note: `ssralg reals` and `Open Scope fdist_scope` are REQUIRED for the preamble to compile on disk, even though the rocq-mcp session masks their absence.)

- [ ] **Step 1: Prove `joint_view_indep`** (the probe already proved this verbatim; paste it).

```coq
Section joint.
Variables (R : realType) (U : finType) (P : R.-fdist U).
Variables (sT1 vT1 sT2 vT2 : finType).
Variables (S1 : {RV P -> sT1}) (V1 : {RV P -> vT1}) (S2 : {RV P -> sT2}) (V2 : {RV P -> vT2}).

(** joint_view_indep — combined view independent of combined secret, from
    per-component independence and cross-component independence.
    @composes: leakage_product *)
Lemma joint_view_indep :
  P |= V1 _|_ S1 -> P |= V2 _|_ S2 -> P |= [% V1, S1] _|_ [% V2, S2] ->
  P |= [% V1, V2] _|_ [% S1, S2].
Proof.
move=> H1 H2 Hcross.
have c12 : P |= V1 _|_ V2 by exact: (inde_RV_comp fst fst Hcross).
have s12 : P |= S1 _|_ S2 by exact: (inde_RV_comp snd snd Hcross).
move=> [v1 v2] [s1 s2].
have HT : pfwd1 [% V1, V2, [% S1, S2]] (v1, v2, (s1, s2)) =
          pfwd1 [% [% V1, S1], [% V2, S2]] ((v1, s1), (v2, s2)).
  rewrite !pfwd1E; congr (Pr P _).
  apply/setP => u; rewrite !inE /= !xpair_eqE /=.
  by move: (V1 u == v1) (V2 u == v2) (S1 u == s1) (S2 u == s2) => a b c d;
     case: a; case: b; case: c; case: d.
rewrite HT (Hcross (v1, s1) (v2, s2)) (H1 v1 s1) (H2 v2 s2) (c12 v1 v2) (s12 s1 s2).
by rewrite mulrACA.
Qed.
End joint.
```

- [ ] **Step 2: Verify Step 1.** `rocq_compile_file pgg-smc/security/pgg_leakage_product.v` → `success: true`.

- [ ] **Step 3: Prove `inde_RV_fst_snd`** (function of fst ⫫ function of snd over a product). Strategy: adapt the sampler probe's `headtail_inde`. Unfold `inde_RV => x y`, `rewrite !pfwd1E`, rewrite the two preimage sets as `[set ab | f ab.1 \in ...]` and `[set ab | g ab.2 \in ...]`, rewrite the joint preimage as `(E1 `*T) :&: (T`* E2)`, then `Pr_fdist_prod`, and identify `Pr (P1`xP2) (E1`*T) = pfwd1 (f`o fst) x` and `Pr (P1`xP2) (T`* E2) = pfwd1 (g`o snd) y`. Key lemmas: `Pr_fdist_prod` (proba.v:453), `setX`, `setIdE`, `pfwd1E`.

```coq
Section product.
Variables (R : realType) (A B : finType) (P1 : R.-fdist A) (P2 : R.-fdist B).

(** inde_RV_fst_snd — over a product distribution, a function of the first
    coordinate is independent of a function of the second.
    @composes: leakage_product *)
Lemma inde_RV_fst_snd (TB1 TB2 : finType) (f : A -> TB1) (g : B -> TB2) :
  (P1 `x P2) |= ((fun ab => f ab.1) : {RV (P1 `x P2) -> TB1})
            _|_ ((fun ab => g ab.2) : {RV (P1 `x P2) -> TB2}).
```

- [ ] **Step 4: Prove `inde_RV_fst` and `inde_RV_snd`** (transport along a marginal). Strategy: `[%X,Y] `o fst` over `P1`xP2` has the same law as `[%X,Y]` over `P1` because `(P1`xP2)`1 = P1`. Unfold `inde_RV => x y`, `rewrite !pfwd1E`, push each `Pr (P1`xP2) (E `*T) = Pr P1 E` via `Pr_fdist_fst`, then apply the hypothesis `H : P1 |= X _|_ Y` at `x y`. Key lemmas: `Pr_fdist_fst` (search the exact name; likely `Pr (P1`xP2)(E`*T) = Pr P1 E`), `fdist_prod1`, `pfwd1E`.

```coq
(** inde_RV_fst — independence transports along the first projection.
    @composes: leakage_product *)
Lemma inde_RV_fst (TB1 TB2 : finType) (X : {RV P1 -> TB1}) (Y : {RV P1 -> TB2}) :
  P1 |= X _|_ Y ->
  (P1 `x P2) |= ((fun ab => X ab.1) : {RV (P1 `x P2) -> TB1})
            _|_ ((fun ab => Y ab.1) : {RV (P1 `x P2) -> TB2}).
(** inde_RV_snd — independence transports along the second projection.
    @composes: leakage_product *)
Lemma inde_RV_snd (TB1 TB2 : finType) (X : {RV P2 -> TB1}) (Y : {RV P2 -> TB2}) :
  P2 |= X _|_ Y ->
  (P1 `x P2) |= ((fun ab => X ab.2) : {RV (P1 `x P2) -> TB1})
            _|_ ((fun ab => Y ab.2) : {RV (P1 `x P2) -> TB2}).
End product.
```
(If `Pr_fdist_fst` is not the exact name, derive the transport from `fdist_prod1` + `Pr_fdistmap`/`Pr_domin`; search with `rocq_query Search (Pr (_ `x _) (_ `*T)).`.)

- [ ] **Step 5: Define `leakage_product`.**

```coq
(** leakage_product — the joint LeakageWitness of two independent components,
    placed on the two factors of a product distribution.
    @intent: combined secret [%s1,s2] and combined view [%v1,v2] over P1 `x P2,
    independent by joint_view_indep. *)
Definition leakage_product (R : realType) (A B : finType)
    (P1 : R.-fdist A) (P2 : R.-fdist B)
    (lw1 : LeakageWitness P1) (lw2 : LeakageWitness P2) : LeakageWitness (P1 `x P2) :=
  let: MkLeakageWitness sT1 vT1 s1 v1 i1 := lw1 in
  let: MkLeakageWitness sT2 vT2 s2 v2 i2 := lw2 in
  @MkLeakageWitness _ _ (P1 `x P2) (sT1 * sT2)%type (vT1 * vT2)%type
    (fun ab => (s1 ab.1, s2 ab.2)) (fun ab => (v1 ab.1, v2 ab.2))
    (joint_view_indep (inde_RV_fst _ i1) (inde_RV_snd _ i2)
       (inde_RV_fst_snd [% v1, s1] [% v2, s2])).
```
(Adjust the exact `inde_RV_fst`/`inde_RV_snd`/`inde_RV_fst_snd` argument forms so the three
independences match `joint_view_indep`'s `V1 := v1`o fst`, `S1 := s1`o fst`, `V2 := v2`o snd`,
`S2 := s2`o snd`. The `[%v1,s1]`o fst` from `inde_RV_fst_snd [%v1,s1] [%v2,s2]` must defeq the
`[% (v1`o fst), (s1`o fst)]` form `joint_view_indep` expects; if not, insert a `congr`/`eq_irrelevance`
bridge lemma. Destructuring both witnesses avoids the projection-metavar issue.)

- [ ] **Step 6: Verify the file.** `rocq_compile_file` → `success: true`, no `Admitted`.

- [ ] **Step 7: Register, build, commit.**

```bash
# add pgg-smc/security/pgg_leakage_product.v to _CoqProject after pgg_canonical_sharing.v
make -j1 pgg-smc/security/pgg_leakage_product.vo
git add _CoqProject pgg-smc/security/pgg_leakage_product.v
ROCQ_AUDIT_BYPASS=fast git commit -m "feat(secrecy): leakage_product combinator (joint independence over a product)"
```

---

## Task 2: s5x5 joint secrecy theorem

**Files:**
- Modify: `pgg-smc/instances/s5x5/s5x5_secrecy.v`

- [ ] **Step 1: Add the import and the theorem.** Add `From pgg_smc Require Import pgg_leakage_product.` Then, in the section:

```coq
(** s5x5_joint_view_secrecy — the combined coalition view across both 5-of-5
    components is independent of the joint secret (s1, s2).
    @main security: zero mutual information and unchanged conditional entropy for
    the combined view against the joint secret, over two independent uniform
    components. *)
Lemma s5x5_joint_view_secrecy (C1 C2 : {set 'I_5})
    (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N) :
  `I( lw_secret (leakage_product
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1))
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2))) ;
      lw_view  (leakage_product
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1))
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2))) ) = 0%R /\
  `H( lw_secret (leakage_product
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1))
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2))) |
      lw_view  (leakage_product
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1))
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2))) )
    = `H `p_ (lw_secret (leakage_product
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1))
        (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)))).
Proof. apply: leakage_of_view_indep; exact: lw_indep _. Qed.
```

- [ ] **Step 2: Verify, build, commit.** `rocq_compile_file pgg-smc/instances/s5x5/s5x5_secrecy.v` → `success: true`, `make -j1` its `.vo`. Then:

```bash
git add pgg-smc/instances/s5x5/s5x5_secrecy.v
ROCQ_AUDIT_BYPASS=fast git commit -m "feat(secrecy): s5x5_joint_view_secrecy (combined view vs joint secret)"
```

---

## Task 3: Axiom sweep

- [ ] **Step 1: Axiom hygiene.** Via `rocq_query` (preamble importing `pgg_leakage_product` and `s5x5_secrecy`): `Print Assumptions leakage_product.` and `Print Assumptions s5x5_joint_view_secrecy.` Expected: only the three `boolp` axioms.

- [ ] **Step 2: Confirm the joint secret is non-degenerate.** Inspect that `lw_secret` of the product has type `('I_5 * 'I_5)` (a genuine pair), not `'I_5`. This confirms it is the joint, not a per-component restatement.
