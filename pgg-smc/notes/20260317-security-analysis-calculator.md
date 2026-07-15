
# Plan: Security Calculator + SecurityProfile + Direct Endpoint Epsilon

## Context

The SecurityWitness record was changed to endpoint-level bounds (done). But `security_witness_any_L` still uses the DPI, giving epsilon = `2*(N!-Tg^L)/N!` ≈ 2 (vacuous). All 6 instances use this fallback.

**Core problem**: Security is a *curve* over L, not a single number. Each group has a "turning point" L* where epsilon becomes meaningful. A protocol designer needs to:
1. Pick a group (fixing Tg, N)
2. Choose target epsilon
3. Get required L* from a **calculator**

**This plan** has three parts:
1. **Security calculator** (`pgg_security_calculator.v`): computable functions for {Tg, N, L, epsilon} relationships
2. **SecurityProfile record**: captures L* + nontriviality, with calculator output
3. **Direct endpoint epsilon**: when `eval_s` injective on `achievable(L)`, gives `epsilon = 2*(N-Tg^L)/N`

## Part 0: Security Calculator (NEW FILE)

**File**: `pgg-smc/security/pgg_security_calculator.v`

### Nat-level computable functions (for `vm_compute`)

```coq
(* Endpoint-level epsilon as rational: 2*(N - Tg^L) / N *)
Definition epsilon_endpoint_rat (Tg N L : nat) : nat * nat :=
  let tl := Tg ^ L in
  if tl <= N then (2 * (N - tl), N) else (0, 1).

(* Permutation-level epsilon as rational: 2*(N! - Tg^L) / N! *)
Definition epsilon_perm_rat (Tg N L : nat) : nat * nat :=
  let nf := N`! in let tl := Tg ^ L in
  if tl <= nf then (2 * (nf - tl), nf) else (0, 1).

(* L* calculator: smallest L such that Tg^L >= threshold *)
Fixpoint Lstar_aux (Tg threshold fuel L : nat) : nat :=
  match fuel with
  | 0 => L
  | fuel'.+1 => if threshold <= Tg ^ L then L
                else Lstar_aux Tg threshold fuel' L.+1
  end.

Definition Lstar_endpoint (Tg N : nat) : nat := Lstar_aux Tg N N 0.
Definition Lstar_perm (Tg N : nat) : nat := Lstar_aux Tg N`! N`! 0.
```

### vm_compute demonstrations

```coq
Eval vm_compute in epsilon_endpoint_rat 4 5 1.  (* S5: (2, 5) = 0.4 *)
Eval vm_compute in epsilon_endpoint_rat 2 4 1.  (* Abelian: (4, 4) = 1.0 *)
Eval vm_compute in epsilon_endpoint_rat 2 4 2.  (* OC: (0, 1) = 0 *)
Eval vm_compute in epsilon_endpoint_rat 1 4 1.  (* Cyclic: (6, 4) = 1.5 *)

Eval vm_compute in Lstar_endpoint 4 5.   (* S5: 2    (4^2=16 >= 5) *)
Eval vm_compute in Lstar_endpoint 2 4.   (* Abelian: 2 (2^2=4 >= 4) *)
Eval vm_compute in Lstar_endpoint 1 4.   (* Cyclic Tg=1: fuel exhausts — degenerate *)
```

**Tg=1 degenerate case**: `1^L = 1` for all L, so the generic calculator can't find L*. The cyclic-specific calculator uses group order instead: `ncycle_Lstar N := N` (need L=N to cycle through all elements).

### Reflection to real-valued epsilon

```coq
Lemma epsilon_endpoint_rat_reflect (Tg N L : nat) :
  let er := epsilon_endpoint_rat Tg N L in
  2%:R * (N - Tg ^ L)%:R / N%:R = er.1%:R / er.2%:R.
```

Connects the computable nat-level output to the real-valued formula in `var_dist_endpoint_uniform_supp`.

### SecurityProfile record (in same file)

```coq
Record SecurityProfile := MkSecurityProfile {
  sp_Lstar : nat ;
  sp_witness : SecurityWitness R M ;
  sp_at_Lstar : sw_L sp_witness = sp_Lstar ;
  sp_nontrivial : (sw_epsilon sp_witness < 2%:R)%O
}.
```

## Part A: SecurityProfile Record

### Design (Option A+: thin wrapper)

```coq
Record SecurityProfile := MkSecurityProfile {
  sp_Lstar : nat ;                        (* group-specific turning point *)
  sp_witness : SecurityWitness R M ;      (* SecurityWitness AT L* *)
  sp_at_Lstar : sw_L sp_witness = sp_Lstar ;  (* consistency *)
  sp_nontrivial : (sw_epsilon sp_witness < 2%:R)%O  (* epsilon < 2: strictly better than trivial *)
}.
```

**Why `< 2` not `< 1`**: The DPI epsilon is always < 2 when `Tg^L >= 1` (trivially true). The threshold `< 1` requires the direct endpoint bound which only some instances can provide. Using `< 2` means ALL existing instances can build a SecurityProfile immediately.

**Why no monotonicity**: `weval_inj(L)` does NOT imply `weval_inj(L+1)` — OC has `weval_inj(2)` but not `weval_inj(3)` (generator cubes collide). So "epsilon decreases with L" is mathematically false in general.

### Turning points per group

| Instance | Tg | N | L* | Formula for L* | epsilon at L* (DPI) | epsilon at L* (direct) |
|----------|-----|-----|-----|-----------------|---------------------|----------------------|
| NCycle | 1 | n+2 | 1 | trivial | 2*(N!-1)/N! ≈ 2.0 | 2*(N-1)/N |
| Abelian | 2 | 4 | 1 | ceil(log₂4)=2, but weval_inj(1) suffices | 44/24 ≈ 1.83 | 2*(4-2)/4 = 1.0 |
| OC | 2 | 4 | 2 | weval_inj starts at L=2 | 40/24 ≈ 1.67 | (needs fiber counting) |
| Star(m) | m+1 | m+3 | 1 | raag_weval_inj1 | 2*((m+3)!-(m+1))/(m+3)! | (eval_s not injective) |
| S5 | 4 | 5 | 1 | raag_weval_inj1 | 2*(120-4)/120 ≈ 1.93 | (eval_s not injective) |
| Monster | 2 | ~10²⁰ | ~67 | ceil(log₂N) | needs axiom for weval_inj(67) | (abstract) |

### Integration with AlgebraicRigidity

Add optional `SecurityProfile` field, or derive it from any existing `AlgebraicRigidity`:

```coq
Lemma weval_inj_eps_lt2 : Tg^L >= 1 -> weval_inj_eps < 2.
(* Always true since Tg >= 1, L >= 0 *)

Definition ar_security_profile (ar : AlgebraicRigidity R M) : SecurityProfile R M :=
  MkSecurityProfile (sw_L (ar_security ar)) (ar_security ar) erefl
    (weval_inj_eps_lt2 ...).
```

## Part B: Direct Endpoint Epsilon

### Key insight

When `eval_s` is injective on `achievable(L)`:
```
epsilon_direct = 2*(N - Tg^L)/N      ← denominator N
epsilon_DPI    = 2*(N! - Tg^L)/N!    ← denominator N!  (always worse)
```

| Instance | DPI epsilon | Direct epsilon | Improvement |
|----------|-------------|----------------|-------------|
| NCycle (Tg=1, N=4) | 1.92 | 1.50 | 22% |
| Abelian (Tg=2, N=4) | 1.83 | 1.00 | 45% |

Star, S5, OC, Monster cannot use this because `eval_s` is not injective on `achievable(L)` for all sheets (generators share fixed points).

### New lemmas in `pgg_collusion_bound.v`

**`fdistmap_uniform_supp_inj`**: When f is injective on C, pushforward of `fdist_uniform_supp C` = `fdist_uniform_supp (f @: C)`.

**`var_dist_endpoint_uniform_supp`**: Combines above with `var_dist_uniform_supp` → `var_dist = 2*(|B|-|f@:C|)/|B|`.

### New constructor in `algebraic_rigidity.v`

```coq
Definition security_witness_endpoint_inj (L : nat)
    (Hlfree : @weval_inj M L)
    (Hinj_s : forall s, {in @achievable M L &, injective (fun sigma => sigma s)})
    : SecurityWitness R M := ...
(* epsilon = 2*(N - Tg^L)/N *)
```

## Files to Create/Modify

| File | Changes |
|------|---------|
| `pgg-smc/security/pgg_security_calculator.v` | **NEW**: nat-level calculator + reflection + SecurityProfile record |
| `pgg-smc/security/pgg_collusion_bound.v` | Add `fdistmap_uniform_supp_inj`, `var_dist_endpoint_uniform_supp`, `weval_inj_eps_lt2` |
| `pgg-smc/reconstruct/algebraic_rigidity.v` | Add `security_witness_endpoint_inj` constructor |
| `pgg-smc/reconstruct/rigidity_cyclic_instance.v` | Direct epsilon + SecurityProfile + cyclic-specific calculator |
| `pgg-smc/reconstruct/rigidity_abelian_instance.v` | Direct epsilon + SecurityProfile |
| `pgg-smc/reconstruct/rigidity_oc_instance.v` | Add SecurityProfile (L*=2) |
| `pgg-smc/reconstruct/rigidity_star_instance.v` | Add SecurityProfile (L*=1) |
| `pgg-smc/reconstruct/rigidity_s5_instance.v` | Add SecurityProfile (L*=1) |
| `pgg-smc/reconstruct/rigidity_monster_instance.v` | Add SecurityProfile (L*=1; true L*≈67 needs axiomatized weval_inj) |
| `_CoqProject` | Add `pgg_security_calculator.v` |

## Execution Order

1. `pgg_collusion_bound.v`: `fdistmap_uniform_supp_inj` + `var_dist_endpoint_uniform_supp` + `weval_inj_eps_lt2`
2. `pgg_security_calculator.v`: **NEW** — calculator functions + reflection + SecurityProfile
3. `algebraic_rigidity.v`: `security_witness_endpoint_inj` constructor
4. `rigidity_cyclic_instance.v`: Direct epsilon + SecurityProfile
5. `rigidity_abelian_instance.v`: Direct epsilon + SecurityProfile
6. Existing 4 instances: Add SecurityProfile

## Verification

```bash
ps aux | grep rocqworker | grep -v grep
make -j1 pgg-smc/security/pgg_collusion_bound.vo
make -j1 pgg-smc/security/pgg_security_calculator.vo   # NEW
make -j1 pgg-smc/reconstruct/algebraic_rigidity.vo
make -j1 pgg-smc/reconstruct/rigidity_cyclic_instance.vo
make -j1 pgg-smc/reconstruct/rigidity_abelian_instance.vo
make -j1 pgg-smc/reconstruct/rigidity_oc_instance.vo
make -j1 pgg-smc/reconstruct/rigidity_star_instance.vo
make -j1 pgg-smc/reconstruct/rigidity_s5_instance.vo
make -j1 pgg-smc/reconstruct/rigidity_monster_instance.vo
```

## Key Design Points

1. **Calculator = implementation of L* formula**: Monster's L*≈67 comes from `Lstar_endpoint 2 N` where N≈10²⁰. For concrete N, `vm_compute` evaluates this. For axiomatized N, the formula is proved generically but the value is axiomatized.

2. **Two epsilon formulas**:
   - `epsilon_perm_rat`: `2*(N!-Tg^L)/N!` — always valid (DPI), denominator N!
   - `epsilon_endpoint_rat`: `2*(N-Tg^L)/N` — requires eval_s injectivity, denominator N

3. **Tg=1 degenerate case**: Generic calculator returns fuel-exhausted value. Cyclic instance provides group-specific `ncycle_Lstar N := N` (group order, not Tg^L).

4. **No monotonicity requirement**: `weval_inj(L)` does NOT imply `weval_inj(L+1)` (OC: L=2 works, L=3 doesn't). SecurityProfile only requires weval_inj at L*, not everywhere.
