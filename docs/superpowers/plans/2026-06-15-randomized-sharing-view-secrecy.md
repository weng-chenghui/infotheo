# Randomized Sharing View-Level Secrecy Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove, for all four in-scope PGG instances, the distributional secrecy `I(Secret; view) = 0` and `H(Secret | view) = H(Secret)` for any sub-threshold coalition view, upgrading the combinatorial `ts_private` to an information-theoretic statement.

**Architecture:** A type-packed `LeakageWitness` interface fed by a generic tail (`leakage_of_view_indep`), produced by two family heads: an additive one-time-pad head (`additive_view_indep`, T-of-T, via du2002 `lemma_3_5'`) for s5/s5x5, and a cyclic-cut counting head for den Boer (reuses `leak_k1`) and kim. A `SharingMechanism` variant marks the family. The executed-trace bridge is out of scope (deferred, see `project_trace_bridge_deferred`).

**Tech Stack:** Rocq + MathComp + infotheo (`fdist`, `proba`, `entropy`), du2002 (`spp_proba`, `spp_entropy`), denboer1989 (`five_card_leakage`).

**Rocq-specific execution rules (CRITICAL):**
- Build every proof with rocq-mcp (`rocq_start` → `rocq_check`/`rocq_step_multi` → `rocq_compile_file`). Reserve `make -j1` for one-shot dependency refreshes only. NEVER run concurrent rocqworkers.
- No `Admitted`, no `lia`, no `rewrite !lemma` on arithmetic lemmas. Every lemma ends in `Qed`.
- "Test fails" = the statement is stated but the proof is `Admitted`/absent and the file does not yet compile clean. "Test passes" = `rocq_compile_file` returns `success: true` with the lemma `Qed`.
- Delegate heavy proofs to the `rocq-prover` agent with the statement, strategy, and key lemmas from the relevant task.
- Daily Stage-2 audit token cap is 2M; commits stage `.v` files and trigger the audit gate.

---

## File structure

| File | Responsibility | Depends on |
|---|---|---|
| `pgg-smc/security/pgg_leakage_witness.v` | `LeakageWitness` record + generic tail `leakage_of_view_indep` | infotheo only |
| `pgg-smc/security/pgg_randomized_sharing.v` | `RandomizedSharing` record + `additive_view_indep` (T-of-T) + `additive_leakage` | leakage_witness, spp_proba, spp_entropy |
| `pgg-smc/security/pgg_cyclic_cut_leakage.v` | `CyclicCutData` record + `cyclic_cut_leakage` + den Boer wrap | leakage_witness, five_card_leakage |
| `pgg-smc/security/pgg_sharing_mechanism.v` | `SharingMechanism` variant + `mechanism_leakage` | randomized_sharing, cyclic_cut_leakage |
| `pgg-smc/instances/s5/s5_secrecy.v` | s5 `Additive` mechanism + `s5_view_secrecy` | sharing_mechanism, s5_run |
| `pgg-smc/instances/s5x5/s5x5_secrecy.v` | s5x5 `Additive` (product) + `s5x5_view_secrecy` | sharing_mechanism, s5x5_run |
| `pgg-smc/instances/denboer1989/denboer_secrecy.v` | den Boer `CyclicCut` + `denboer_view_secrecy` | sharing_mechanism, five_card_leakage |
| `pgg-smc/instances/kim2025/kim_secrecy.v` | kim cyclic-cut head + `CyclicCut` + `kim_view_secrecy` | sharing_mechanism, five_card_family |

All new `.v` files must be reachable by `_CoqProject` (the `pgg-smc/security` and instance dirs are already mapped). Confirm each compiles standalone via rocq-mcp before committing.

---

## Task 1: LeakageWitness interface and the generic tail

**Files:**
- Create: `pgg-smc/security/pgg_leakage_witness.v`

The generic tail is already proven over abstract finTypes during the shape audit; this task lands it as tracked code.

- [ ] **Step 1: State the record and the tail (the contract).**

```coq
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset bigop ssralg ssrnum reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Import GRing.Theory Num.Theory.
Set Implicit Arguments. Unset Strict Implicit. Import Prenex Implicits.
Local Open Scope fdist_scope. Local Open Scope proba_scope. Local Open Scope entropy_scope.

Section leakage_witness.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.

Record LeakageWitness := MkLeakageWitness {
  lw_secretT : finType ;
  lw_viewT   : finType ;
  lw_secret  : {RV P -> lw_secretT} ;
  lw_view    : {RV P -> lw_viewT} ;
  lw_indep   : P |= lw_view _|_ lw_secret }.

(** leakage_of_view_indep — a sub-threshold view independent of the secret leaks
    zero mutual information and leaves the secret's entropy unchanged. *)
Lemma leakage_of_view_indep (secretT viewT : finType)
    (Secret : {RV P -> secretT}) (view : {RV P -> viewT}) :
  P |= view _|_ Secret ->
  `I( Secret ; view ) = 0%R /\ `H( Secret | view ) = `H `p_ Secret.

End leakage_witness.
```

- [ ] **Step 2: Verify it fails (no proof yet).** Add `Proof. Admitted.` temporarily, run `rocq_compile_file pgg-smc/security/pgg_leakage_witness.v`. Expected: compiles with an `Admitted` warning. This confirms the statements typecheck.

- [ ] **Step 3: Prove `leakage_of_view_indep`.** Strategy (lifted verbatim from `du2002/_probe_c_pgg_secrecy.v` lines 53-75, generalized to abstract finTypes):
  - `move=> Hinde.` Note the seed has `P |= Secret _|_ view`; here the hypothesis is `view _|_ Secret`, so use `inde_RV_sym` to orient as needed.
  - Conditional-entropy conjunct: `have := chain_rule_RV view Secret. rewrite -joint_entropy_RVC (inde_RV_joint_entropyE H) => H1.` then the `addrI` trick from the seed to get `H(Secret|view) = H `p_ Secret`.
  - Mutual-info conjunct: `rewrite mutual_info_RVE`, rewrite the conditional-entropy equality, `subrr`.
  - `split`. Key lemmas: `chain_rule_RV`, `joint_entropy_RVC`, `inde_RV_joint_entropyE`, `mutual_info_RVE`, `inde_RV_sym`, `subrr`, `addrI`.

- [ ] **Step 4: Verify it passes.** Run `rocq_compile_file pgg-smc/security/pgg_leakage_witness.v`. Expected: `success: true`, no `Admitted`.

- [ ] **Step 5: Commit.**

```bash
git add pgg-smc/security/pgg_leakage_witness.v
git commit -m "feat(secrecy): LeakageWitness interface + generic view-secrecy tail"
```

---

## Task 2: Additive one-time-pad head (T-of-T)

**Files:**
- Create: `pgg-smc/security/pgg_randomized_sharing.v`
- Delete: `du2002/_probe_c_pgg_secrecy.v` (after the seed content is promoted)

This is the main new proof. Generalize the proven T=2 single-mask result (`du2002/_probe_c_pgg_secrecy.v`) to any sub-threshold coalition of a T-of-T sharing.

- [ ] **Step 1: Promote the seed and state the record.** Copy the preamble and the T=2 lemmas from `du2002/_probe_c_pgg_secrecy.v` into the new file (so a compiling baseline exists), then add:

```coq
(* preamble: same imports as the seed, plus: *)
From pgg_smc Require Import pgg_leakage_witness.

Section randomized_sharing.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.
Variable N' : nat.  Let N := N'.+2.   (* Z/N additive group, N >= 2 *)
Variable T' : nat.  Let T := T'.+1.   (* T-of-T sharing, T >= 1 *)
(* card_ZN is DERIVED, not assumed, so it is not a spurious record parameter:
   `Let card_ZN : #|'Z_N| = N := card_Zp (ltn0Sn N'.+1)` (adjust to card_Zp's
   exact form / card_ord if needed during execution). *)
Let card_ZN : #|'Z_N| = N'.+1.+1 := card_Zp (ltn0Sn N'.+1).

Record RandomizedSharing := MkRandomizedSharing {
  rsh_secret     : {RV P -> 'Z_N} ;
  rsh_mask       : 'I_T' -> {RV P -> 'Z_N} ;   (* T' = T-1 free masks *)
  rsh_mask_unif  : forall j, `p_ (rsh_mask j) = fdist_uniform card_ZN ;
  rsh_mask_indep : forall j : 'I_T',
    P |= rsh_mask j _|_
         [% rsh_secret,
            ((fun u => [ffun i : 'I_T' => rsh_mask i u]) : {RV P -> {ffun 'I_T' -> 'Z_N}})] }.

(* the dealt shares: free masks at j < T', the dependent share at the last index *)
Definition rsh_share (rs : RandomizedSharing) (j : 'I_T) : {RV P -> 'Z_N} :=
  if @unlift _ ord_max j is Some j' then rsh_mask rs j'
  else (rsh_secret rs \- (\sum_(i < T') rsh_mask rs i)).
```

- [ ] **Step 2: State the coalition-independence head (the contract).**

```coq
(* the view of a coalition C of share-positions *)
Definition rsh_view (rs : RandomizedSharing) (C : {set 'I_T}) :
    {RV P -> {ffun 'I_T -> 'Z_N}} :=
  fun u => [ffun j => if j \in C then rsh_share rs j u else 0].

(** additive_view_indep — any sub-threshold coalition view is independent of the secret. *)
Lemma additive_view_indep (rs : RandomizedSharing) (C : {set 'I_T}) :
  #|C| < T ->
  P |= rsh_view rs C _|_ rsh_secret rs.
```

- [ ] **Step 3: Verify the statements typecheck.** Add `Admitted.`, run `rocq_compile_file`. Expected: compiles with `Admitted` warnings. If `rsh_share`/`rsh_view` fight the type system (ordinal `unlift`, ffun RV coercions), fix the definitions until they typecheck before proving.

- [ ] **Step 4: Prove `additive_view_indep`.** Strategy (the "all-but-one" reduction):
  1. Since `#|C| < T`, there exists an excluded index `k ∉ C` (`have [k Hk] : exists k, k \notin C` from a cardinality argument: `C != setT`, so its complement is nonempty).
  2. `rsh_view rs C` is a function of `rsh_view rs (~: [set k])` (the all-but-k view), since `C ⊆ ~: [set k]`. Reduce via `inde_RV_comp` (du2002/spp_proba.v:101): it suffices to prove `P |= rsh_view rs (~: [set k]) _|_ rsh_secret rs`.
  3. The all-but-k view omits exactly share `k`. Case on `k`:
     - `k = ord_max` (the dependent share excluded): the view is the T' free masks, jointly independent of the secret by `rsh_mask_indep` (the bundle form gives mask vs [secret, all masks]; assemble the joint mask-tuple independence from the per-mask bundle facts, or use the bundle directly since the view IS the mask family).
     - `k != ord_max` (a free mask excluded): the dependent share `secret - sum masks` is a one-time pad of the secret by the excluded uniform mask `k`. Apply `lemma_3_5'` with `Z := neg_RV (rsh_mask k)` (uniform via `neg_RV_dist_eq`, jointly independent via `neg_RV_inde_eq` + `inde_RV_comp`), exactly as the seed proves the T=2 case (`du2002/_probe_c_pgg_secrecy.v:34-50`). The other seen masks are carried in the conditioning.
  Key lemmas: `inde_RV_comp`, `lemma_3_5'`, `sub_RV_eq`, `neg_RV_dist_eq`, `neg_RV_inde_eq`, `inde_RV_sym`, `unlift`/`lift` ordinal lemmas, `bigD1` for splitting `\sum_(i<T') rsh_mask i` around the excluded index. This step is the bulk of the work; delegate to `rocq-prover` with this strategy.

- [ ] **Step 5: State and prove `additive_leakage`.**

```coq
Definition additive_leakage (rs : RandomizedSharing) (C : {set 'I_T})
    (HC : #|C| < T) : LeakageWitness P :=
  @MkLeakageWitness _ _ P _ _ (rsh_secret rs) (rsh_view rs C) (additive_view_indep rs C HC).
```

  Verify it typechecks (it is a packaging, no proof obligation beyond `additive_view_indep`).

- [ ] **Step 6: Verify the whole file passes.** Run `rocq_compile_file pgg-smc/security/pgg_randomized_sharing.v`. Expected: `success: true`, no `Admitted`. Run `Print Assumptions additive_view_indep` (via rocq-mcp) and confirm only `boolp` axioms.

- [ ] **Step 7: Delete the seed and commit.**

```bash
git rm du2002/_probe_c_pgg_secrecy.v
git add pgg-smc/security/pgg_randomized_sharing.v
git commit -m "feat(secrecy): additive T-of-T one-time-pad head; retire probe seed"
```

---

## Task 3: Cyclic-cut head and den Boer wrap

**Files:**
- Create: `pgg-smc/security/pgg_cyclic_cut_leakage.v`

- [ ] **Step 1: State `CyclicCutData` and `cyclic_cut_leakage`.**

```coq
(* preamble: infotheo + From pgg_smc Require Import pgg_leakage_witness. *)
Section cyclic_cut.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.

Record CyclicCutData := MkCyclicCutData {
  ccd_secretT : finType ;
  ccd_viewT   : finType ;
  ccd_secret  : {RV P -> ccd_secretT} ;
  ccd_view    : {RV P -> ccd_viewT} ;
  ccd_indep   : P |= ccd_view _|_ ccd_secret }.

Definition cyclic_cut_leakage (cc : CyclicCutData) : LeakageWitness P :=
  @MkLeakageWitness _ _ P _ _ (ccd_secret cc) (ccd_view cc) (ccd_indep cc).
End cyclic_cut.
```

- [ ] **Step 2: Verify it typechecks.** Run `rocq_compile_file`. Expected: `success: true` (no proofs, pure packaging).

- [ ] **Step 3: Commit.**

```bash
git add pgg-smc/security/pgg_cyclic_cut_leakage.v
git commit -m "feat(secrecy): CyclicCutData record + cyclic_cut_leakage packaging"
```

Note: den Boer's concrete `CyclicCutData` (built from `leak_k1`) and kim's new head are constructed in the instance files (Tasks 6, 8), where their probability spaces (`Omega`, kim's analogue) are in scope.

---

## Task 4: Family wrapper

**Files:**
- Create: `pgg-smc/security/pgg_sharing_mechanism.v`

- [ ] **Step 1: State the variant and dispatch.**

```coq
(* preamble: From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing pgg_cyclic_cut_leakage. *)
Section sharing_mechanism.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.
Variable N' T' : nat.   (* additive dimensions; the CyclicCut branch ignores them *)

Variant SharingMechanism :=
  | Additive  (rs : @RandomizedSharing R U P N' T')
              (C : {set 'I_T'.+1}) (HC : #|C| < T'.+1)
  | CyclicCut (cc : CyclicCutData P).

Definition mechanism_leakage (m : SharingMechanism) : LeakageWitness P :=
  match m with
  | Additive rs C HC => additive_leakage rs C HC
  | CyclicCut cc     => cyclic_cut_leakage cc
  end.
End sharing_mechanism.
```

  The `Additive` branch fixes the additive dimensions `N' T'` as section parameters of `SharingMechanism`; the `CyclicCut` branch (a `bool` secret) ignores them. This is the type-packing crux: it typechecks only because `LeakageWitness` packs `secretT`/`viewT` as fields (Task 1), so `mechanism_leakage`'s two branches can return the one `LeakageWitness P` type despite the `'Z_N`-vs-`bool` secret mismatch. If `@RandomizedSharing R U P N' T'` does not match the record's actual parameter order after Task 2's section closes, adjust the explicit arguments to match; keep `mechanism_leakage` total.

- [ ] **Step 2: Verify it typechecks** (this is the type-packing crux confirmed by the shape audit). Run `rocq_compile_file`. Expected: `success: true`. If the two branches' differing secret types are rejected, confirm `LeakageWitness` packs `secretT`/`viewT` as fields (it does, Task 1).

- [ ] **Step 3: Commit.**

```bash
git add pgg-smc/security/pgg_sharing_mechanism.v
git commit -m "feat(secrecy): SharingMechanism variant + mechanism_leakage dispatch"
```

---

## Task 5: s5 instance secrecy

**Files:**
- Create: `pgg-smc/instances/s5/s5_secrecy.v`

- [ ] **Step 1: Build the s5 `RandomizedSharing` and conclude.** Strategy: s5's secret is `'I_5 = 'Z_5` over a sampler `P`. Construct a `RandomizedSharing` for `N'=3, T'=4` (matching `sum_mod_scheme 3 4`), choose the sub-threshold coalition `C` (size `< 5`), form `Additive rs C HC`, and obtain:

```coq
Lemma s5_view_secrecy (rs : RandomizedSharing P) (C : {set 'I_5}) (HC : #|C| < 5) :
  let w := mechanism_leakage (Additive rs C HC) in
  `I( lw_secret w ; lw_view w ) = 0%R /\ `H( lw_secret w | lw_view w ) = `H `p_ (lw_secret w).
Proof. exact: leakage_of_view_indep (lw_indep _). Qed.
```

  Adjust the exact form so `leakage_of_view_indep` applies to the witness's fields. The proof is a one-liner once the witness is built.

- [ ] **Step 2: Verify and commit.** `rocq_compile_file pgg-smc/instances/s5/s5_secrecy.v` → `success: true`.

```bash
git add pgg-smc/instances/s5/s5_secrecy.v
git commit -m "feat(secrecy): s5 view-level secrecy via Additive mechanism"
```

---

## Task 6: s5x5 instance secrecy

**Files:**
- Create: `pgg-smc/instances/s5x5/s5x5_secrecy.v`

- [ ] **Step 1: Build the product `RandomizedSharing` and conclude.** Strategy: `s5x5_scheme = product_scheme (sum_mod_scheme 3 4) (sum_mod_scheme 3 4)`. Instantiate `RandomizedSharing` on each component, and for a coalition below `min(k1,k2)` (sub-threshold on each component per `product_threshold.v`), apply `additive_view_indep` per component and combine. Conclude `s5x5_view_secrecy` in the same shape as Task 5 via `leakage_of_view_indep`.

- [ ] **Step 2: Verify and commit.** `rocq_compile_file` → `success: true`.

```bash
git add pgg-smc/instances/s5x5/s5x5_secrecy.v
git commit -m "feat(secrecy): s5x5 view-level secrecy via product Additive mechanism"
```

---

## Task 7: den Boer instance secrecy

**Files:**
- Create: `pgg-smc/instances/denboer1989/denboer_secrecy.v`

- [ ] **Step 1: Build `CyclicCutData` from `leak_k1` and conclude.** Strategy: over `five_card_leakage.v`'s space (`Omega`, `P = fdist_uniform card_Omega20`, `Secret = a&&b`, `ViewA [::0]`), `leak_k1` gives `I(Secret; ViewA[::0]) = 0`; but `CyclicCutData` needs `P |= ViewA[::0] _|_ Secret`. Extract that independence from `leak_k1`'s proof (it proves `Hinde : P |= Secret _|_ ViewA [::0]` internally, `five_card_leakage.v:247`). Re-expose it as a standalone lemma if needed, then:

```coq
Definition denboer_ccd : CyclicCutData P :=
  @MkCyclicCutData _ _ P _ _ Secret (ViewA [:: 0%N]) denboer_view_indep.
Lemma denboer_view_secrecy :
  `I( Secret ; ViewA [:: 0%N] ) = 0%R /\ `H( Secret | ViewA [:: 0%N] ) = `H `p_ Secret.
Proof. exact: leakage_of_view_indep (ccd_indep denboer_ccd). Qed.
```

  where `denboer_view_indep : P |= ViewA [::0] _|_ Secret` is `inde_RV_sym` of `leak_k1`'s `Hinde`. If `leak_k1` does not export `Hinde`, prove `denboer_view_indep` directly with the same `count_pr` cardinality argument from `leak_k1` (`five_card_leakage.v:247-300`).

- [ ] **Step 2: Verify and commit.** `rocq_compile_file` → `success: true`.

```bash
git add pgg-smc/instances/denboer1989/denboer_secrecy.v
git commit -m "feat(secrecy): den Boer view-level secrecy via CyclicCut (leak_k1)"
```

---

## Task 8: kim instance secrecy

**Files:**
- Create: `pgg-smc/instances/kim2025/kim_secrecy.v`

This is the second new proof: kim has no leakage proof today.

- [ ] **Step 1: State kim's cyclic-cut head.** Strategy: kim uses the same `fcI_scheme` (bool secret) over `FiveCardKim_M` with cut group `<[fc_sigma]>` (all five rotations). Build the kim sample space analogous to `five_card_leakage.v`'s `Omega` (inputs plus the uniform cut over `<[fc_sigma]>`), define `Secret` and a single-card `View`, and state:

```coq
Lemma kim_view_indep : P_kim |= kim_view _|_ kim_secret.
```

- [ ] **Step 2: Prove `kim_view_indep`.** Strategy: adapt the den Boer counting argument (`five_card_leakage.v` `leak_k1`, `count_pr`, per-view cardinality enumeration) to kim's cut group. Since kim's cut is the full five-rotation cyclic group (the same `'I_5` rotation structure as den Boer), the single-card view distribution is rotation-uniform and independent of the secret by the same counting. Reuse `five_card_program`/`five_card_family` lemmas where the layout matches. Delegate to `rocq-prover` with the den Boer proof as the template. Key risk: kim's secret/output function may differ from `a&&b`; confirm the secret definition against `five_card_family.v` before counting.

- [ ] **Step 3: Build `CyclicCutData` and conclude `kim_view_secrecy`** (same packaging as Task 7).

- [ ] **Step 4: Verify and commit.** `rocq_compile_file` → `success: true`, `Print Assumptions kim_view_indep` shows only `boolp` axioms.

```bash
git add pgg-smc/instances/kim2025/kim_secrecy.v
git commit -m "feat(secrecy): kim view-level secrecy via new cyclic-cut head"
```

---

## Task 9: Records-parity and axiom-hygiene sweep

**Files:**
- Verify: all eight new files.

- [ ] **Step 1: Parity check.** Confirm each of the four instances has a persisted `<inst>_view_secrecy` theorem with the same statement shape, and a `SharingMechanism` value. Grep:

```bash
grep -rn "_view_secrecy" pgg-smc/instances/*/[a-z]*_secrecy.v
```
Expected: four matches, one per instance.

- [ ] **Step 2: Axiom hygiene.** For each `<inst>_view_secrecy`, `additive_view_indep`, `kim_view_indep`, run `Print Assumptions` via rocq-mcp. Expected: only `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`, `boolp.constructive_indefinite_description`. No custom axiom.

- [ ] **Step 3: Full build sanity (single-threaded).** Run `make -j1` on the four instance `_secrecy.vo` targets to confirm they integrate with the build manifest. Expected: clean `.vo` for all four.

- [ ] **Step 4: Final commit (if any manifest/_CoqProject changes).**

```bash
git add -A
git commit -m "chore(secrecy): records-parity + axiom-hygiene sweep across four instances"
```

---

## Notes on deferred work (not in this plan)

The executed-trace operational layer (`trace_secrecy`, per-instance trace-ok lemmas, lifting `run_interp` to a probability space) is deferred. See `project_trace_bridge_deferred` and the spec's Non-goals. Do not attempt it here.
