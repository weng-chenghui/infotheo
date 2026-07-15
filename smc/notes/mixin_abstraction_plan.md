# Mixin Abstraction Plan for Session Type Proofs

## Architectural Insight: Typed vs Erased Interpreter

### Current Architecture (Erased Interpreter)

The current `interp` operates on erased processes (`proc`), losing type information.
Resource tracking requires post-hoc reconstruction via case analysis:

```
proc (erased) ──> interp ──> proc (erased)
                               │
                               └──> reconstruct aproc (case analysis)
                                    ├── fuel bound ✓
                                    └── senv bound ✓ (but coupled!)
```

**Limitation**: Adding a new resource requires extending the reconstruction
with more case analysis. Resources cannot be tracked independently.

### Ideal Architecture (Typed Interpreter)

A typed interpreter preserving `aproc` indices would enable independent
resource tracking via separate mixin instances:

```
aproc (typed) ──> typed_interp ──> aproc (typed)
                                    │
                                    ├── fuel: isStepDecreasing instance
                                    ├── senv: isStepDecreasing instance
                                    └── new_resource: isStepDecreasing instance
```

**Benefits**:
- Each resource has its own `isStepDecreasing` instance
- Resources are tracked independently and can be composed
- Adding new resources doesn't require modifying existing proofs

### Current Status

The mixins in `graded_resource.v` are **forward-looking infrastructure**:
- `isNatGraded`, `isStepDecreasing`, `isDecomposableInterp` are ready
- `sum_level_decreases` generalizes collection-level termination
- Generic termination lemmas (`suffices_generic`, `fuel_suffices_alt`)

To fully utilize this infrastructure, a **typed interpreter** is needed.
Until then, `fuel_senv_decreases` in `smc_session_types.v` couples the
resources via case analysis reconstruction.

---

## Current Structure Analysis

The `sproc` type is indexed by three things:
```coq
Inductive sproc (party : nat) : nat -> senv dtype -> Type
                                 ↑fuel    ↑session env
```

Both indices change during execution:
- **Fuel**: `n.+1 → n` (decreases by 1 on each step, or stays same if blocked)
- **Session Env**: `senv_send env dst dt → env` or `senv_recv env src dt → env` (pops head)

The key lemmas share a common pattern:
1. **`fuel_decreases`**: After step, new fuel + did_step ≤ old fuel
2. **`fuel_suffices_nored`**: Sufficient fuel → termination (no more reductions)
3. **`interpD`**: Interpreter decomposes along fuel addition
4. **`fuel_suffices`**: Extra fuel doesn't change result

---

## Core Insight: Nat-Indexed Families

Both fuel and session env are **indexed by nat** (the fuel level). When fuel decreases:
- Fuel itself: `n.+1 → n` (trivial change)
- Session env: "reduces" by one communication step

This suggests abstracting over **nat-indexed type families** rather than concrete resource types.

---

## Relationship to Math-Comp

**NatGraded is novel** - math-comp provides specific nat-indexed types:
- `n.-tuple T` (fixed-length sequences, with `behead : n.+1.-tuple → n.-tuple`)
- `'I_n` (bounded naturals / ordinals)
- `'M[R]_(m,n)` (matrices)

However, math-comp does **not** have a general mixin for nat-indexed type families with step-down operations. These are all concrete data structures, not an abstraction pattern.

The `isNatGraded` pattern we propose is simple enough to be worth defining ourselves:
- Just 2 fields: `base` and `down`
- Captures a common pattern (tower of types with projection)
- Allows fuel and session env to be treated uniformly

---

## Math-Comp Naming Conventions

Based on math-comp library patterns:

| Element | Convention | Examples |
|---------|------------|----------|
| **Mixin** | `is<Name>` or `has<Feature>` | `isSemigroup`, `hasMul` |
| **Structure** | Singular noun | `Monoid`, `Zmodule`, `Field` |
| **Instance** | Anonymous (`Definition _`) | `HB.instance Definition _ := ...` |
| **Fields** | Algebraic lemma names, `_subproof` suffix | `mulgA`, `addrC` |

---

## Layer 1: Generic Abstractions (Reusable)

These mixins are independent of session types and could be reused elsewhere.

### 1.1 Nat-Graded Type Family

**Purpose**: Abstract over type families indexed by nat with level-decreasing operations.

```coq
(* Mixin: a family of types indexed by nat *)
HB.mixin Record isNatGraded (T : nat -> Type) := {
  base : T 0 ;                                    (* terminal value at level 0 *)
  down : forall n, T n.+1 -> T n ;                (* step down one level *)
}.

HB.structure Definition NatGraded := { T of isNatGraded T }.
```

**Bundle type**: A "bundle" is a value paired with its level index - i.e., `{ n : nat & T n }` (Coq's `sigT`). For `sproc`, the existing `aproc` record already serves this purpose:
```coq
(* aproc is essentially sigT (sproc party) *)
Record aproc party := { aproc_fuel : nat ; ... ; aproc_proc : sproc party aproc_fuel ... }.
```

### 1.2 Step-Decreasing Property

**Purpose**: Stepping may decrease the level (progressed) or keep it same (blocked).

```coq
(* Mixin: step operation that respects level grading *)
(* B is the bundle type (e.g., aproc). Context type is a field, similar to 'run' in isDecomposableInterp *)
HB.mixin Record isStepDecreasing (B : Type) := {
  (* Context type for stepping (e.g., traces, other processes) *)
  step_ctx : Type ;

  (* Extract level from bundle *)
  level : B -> nat ;

  (* Step a bundled value, returning new bundle and progress indicator (0 or 1) *)
  step_bundle : B -> step_ctx -> B * nat ;

  (* Key property: new level + progress <= old level *)
  step_decreases_subproof : forall b c,
    level (step_bundle b c).1 + (step_bundle b c).2 <= level b ;
}.

HB.structure Definition StepDecreasing := { B of isStepDecreasing B }.
```

**Note**: `B` is the bundle type (like `aproc`). The context type `step_ctx` is a field of the mixin (not a type parameter) to fit HB's single-key structure model. We extract `level` from bundles rather than requiring `sigT` structure, making it easier to use existing record types.

### 1.3 Decomposable Interpreter

**Purpose**: Interpreter decomposes along nat addition.

```coq
(* Mixin: interpreter decomposes along addition *)
HB.mixin Record isDecomposableInterp (S : Type) (interp : nat -> S -> S) := {
  interpD : forall n m s, interp (n + m) s = interp m (interp n s) ;
  interp0 : forall s, interp 0 s = s ;
}.

HB.structure Definition DecomposableInterp S :=
  { interp of isDecomposableInterp S interp }.
```

### 1.4 Generic Termination Lemmas

**Purpose**: Derive termination from the mixins above.

```coq
Section GenericTermination.
  Variables (B C S : Type).
  Variable interp : nat -> S -> S.

  Context `{isStepDecreasing B C}.
  Context `{isDecomposableInterp S interp}.

  (* Connection: interpreter uses step_bundle internally *)
  Variable interp_uses_step : (* ... application-specific connection ... *).

  (* Generic: if all values reached level 0 or blocked, no more progress *)
  Lemma suffices_nored_generic n s :
    let s' := interp n s in
    all_terminated_or_blocked s' ->
    forall m, interp m s' = s'.

  (* Generic: extra fuel doesn't change result *)
  Lemma fuel_suffices_generic n m s :
    sufficient_fuel n s ->
    n <= m ->
    interp m s = interp n s.
  Proof.
    move=> Hsuff Hle.
    rewrite -(subnK Hle) interpD.
    (* use suffices_nored_generic *)
  Qed.

End GenericTermination.
```

---

## Layer 2: Application-Specific (Session Types)

These definitions instantiate the generic mixins for `sproc`.

### 2.1 NatGraded Instances

Both fuel and session environments are instances of `isNatGraded`, enabling analogous termination lemmas.

```coq
(* Fuel: trivially indexed by nat *)
Definition fuel_family (n : nat) : Type := unit.

HB.instance Definition _ := isNatGraded.Build fuel_family
  tt                          (* base: unit at level 0 *)
  (fun _ _ => tt).            (* down: trivial *)

(* Session environment: indexed by session depth *)
Fixpoint stype_depth (s : stype dtype) : nat :=
  match s with
  | STEnd => 0
  | STSend _ k => (stype_depth k).+1
  | STRecv _ k => (stype_depth k).+1
  end.

Definition senv_family (n : nat) (parties : seq nat) : Type :=
  { env : senv dtype | senv_depth env parties = n }.

HB.instance Definition _ := isNatGraded.Build (senv_family parties)
  (exist _ senv_end eq_refl)                      (* base: empty env *)
  (fun n e => (* senv_reduce e *) ...).           (* down: pop one comm *)
```

See "Questions Resolved" and "Revised Layer 2: Parallel Instances" for details.

### 2.2 StepDecreasing Instance for sproc

```coq
Section SprocStepDecreasing.
  Variable party : nat.

  (* aproc is the bundle type for sproc *)

  (* Step function for aproc *)
  Definition aproc_step (ap : aproc party) (ctx : step_context)
      : aproc party * nat :=
    let res := step (aproc_erase ap) ctx in
    (lift_to_aproc res.1, res.2).

  (* Proof that step decreases fuel *)
  Lemma aproc_step_decreases ap ctx :
    let (ap', d) := aproc_step ap ctx in
    aproc_fuel ap' + d <= aproc_fuel ap.
  Proof.
    (* case analysis on sproc constructors *)
    case: ap => [n env sp].
    case: sp => [|d|n' env' d s|...] /=.
    - (* SFinish *) ...
    - (* SRet *) ...
    - (* SInit *) ...
    - (* SSend *) ...
    - (* SRecv *) ...
    - (* SFail *) ...
  Qed.

  HB.instance Definition _ := isStepDecreasing.Build
    (aproc party) step_context
    aproc_fuel          (* level function *)
    aproc_step          (* step function *)
    aproc_step_decreases.

End SprocStepDecreasing.
```

### 2.3 DecomposableInterp Instance

```coq
HB.instance Definition _ := isDecomposableInterp.Build
  state interp
  interpD_proof    (* forall n m s, interp (n + m) s = interp m (interp n s) *)
  interp0_proof.   (* forall s, interp 0 s = s *)
```

### 2.4 Derived Lemmas for sproc

```coq
(* These now follow from generic lemmas *)
Lemma fuel_suffices_nored party n env (ps : seq (sproc party n env)) traces res :
  interp n (map erase_sproc ps, traces) = res ->
  ~~ has snd [seq step res.1 (nth [::] res.2 i) i | i <- iota 0 (size ps)].
Proof. apply: suffices_nored_generic. Qed.

Lemma fuel_suffices party n m env (ps : seq (sproc party n env)) traces :
  n <= m ->
  interp m (map erase_sproc ps, traces) = interp n (map erase_sproc ps, traces).
Proof. apply: fuel_suffices_generic. Qed.
```

---

## How to Add a New Instance

When you have a new indexed type that follows the "step decreases level" pattern, follow these steps:

### Step 1: Define Your Type Family

```coq
(* Your type indexed by nat *)
Inductive my_proc : nat -> my_env -> Type := ...

(* Or wrap an existing type *)
Definition my_family (n : nat) : Type := { x : my_type | depth x = n }.
```

### Step 2: Prove isNatGraded

```coq
(* Provide base case and step-down function *)
HB.instance Definition _ := isNatGraded.Build my_family
  my_base_value           (* : my_family 0 *)
  my_down_function.       (* : forall n, my_family n.+1 -> my_family n *)
```

### Step 3: Define Bundle and Step

```coq
(* Bundle packs value with its level - may already exist as a record *)
(* e.g., aproc is the bundle for sproc *)

(* Use existing record or define new one *)
Record my_bundle := {
  my_level : nat ;
  my_value : my_family my_level ;
}.

(* Define step function on bundles *)
Definition my_step (b : my_bundle) (ctx : my_context) : my_bundle * nat :=
  (* return (new_bundle, 0_or_1) where 1 means progress made *)
  ...
```

### Step 4: Prove isStepDecreasing

```coq
(* Prove the key property: new_level + progress <= old_level *)
Lemma my_step_decreases b ctx :
  let (b', d) := my_step b ctx in
  my_level b' + d <= my_level b.
Proof.
  (* Usually case analysis on constructors *)
  case: b => [n v].
  case: v => [...constructors...] /=.
  - (* case 1 *) ...
  - (* case 2 *) ...
Qed.

HB.instance Definition _ := isStepDecreasing.Build
  my_bundle my_context
  my_level            (* level function *)
  my_step             (* step function *)
  my_step_decreases.
```

### Step 5: Connect to Interpreter (if applicable)

```coq
(* If you have an interpreter, prove decomposition *)
Lemma my_interpD n m s : my_interp (n + m) s = my_interp m (my_interp n s).
Proof. (* ... *) Qed.

Lemma my_interp0 s : my_interp 0 s = s.
Proof. (* ... *) Qed.

HB.instance Definition _ := isDecomposableInterp.Build
  my_state my_interp
  my_interpD
  my_interp0.
```

### Step 6: Get Termination Lemmas for Free

```coq
(* Now generic lemmas apply to your type *)
Lemma my_fuel_suffices n m s :
  n <= m -> my_interp m s = my_interp n s.
Proof. apply: fuel_suffices_generic. Qed.
```

---

## Comparison: Old vs New Approach

| Aspect | Old (Concrete) | New (Generic Mixins) |
|--------|----------------|---------------------|
| Resource type | `nat`, `senv`, etc. | `T : nat -> Type` |
| Step property | Lemma per type | `isStepDecreasing` mixin |
| Interpreter | Lemma per interpreter | `isDecomposableInterp` mixin |
| Termination | Manual proof each time | Generic `fuel_suffices_generic` |
| New types | Copy-paste proofs | Instantiate mixins |

**Advantages**:
1. **Reusability**: Termination proofs derived from mixins
2. **Modularity**: Clear separation of concerns
3. **Extensibility**: New types just need to instantiate mixins
4. **Documentation**: Mixins document the required properties

---

## Recommended Implementation Plan

### Phase 1: Define Generic Infrastructure
1. Create `graded_resource.v`:
   - `isNatGraded` mixin and `NatGraded` structure
   - `bundle` record
   - `isStepDecreasing` mixin
   - `isDecomposableInterp` mixin
   - Generic termination lemmas

### Phase 2: Define Instances for sproc
2. `fuel_family` instance (trivial)
3. `senv_family` instance (requires `senv_depth`)
4. `isStepDecreasing` instance for `aproc`/`sproc`
5. `isDecomposableInterp` instance for `interp`

### Phase 3: Refactor Existing Proofs
6. Replace `fuel_decreases` with instance proof
7. Derive `fuel_suffices_nored` and `fuel_suffices` from generic lemmas
8. Ensure existing proofs still compile

### Phase 4: Validate and Document
9. Test with a second indexed type (if available)
10. Document the "How to Add New Instance" pattern
11. Add examples in comments

---

## File Organization

```
smc/
├── graded_resource.v          (* Generic: isNatGraded, isStepDecreasing,
│                                  isDecomposableInterp, generic lemmas *)
├── smc_interpreter.v          (* Existing: step, interp definitions *)
├── smc_session_types.v        (* Existing: sproc, aproc + NEW instances *)
└── smc_termination.v          (* Simplified: now uses generic lemmas *)
```

---

## Questions Resolved

### 1. Should `senv_depth` be defined?

**Answer: Yes, `senv_depth` is needed for the session env instance.**

While the fuel parameter of `sproc` already tracks session depth for the current implementation:
```coq
| SSend : ... sproc party n env -> sproc party n.+1 (senv_send env dst dt)
| SRecv : ... (data -> sproc party n env) -> sproc party n.+1 (senv_recv env src dt)
```

The goal of the mixin abstraction is to support **multiple instances**:
1. **Fuel instance** → derives `fuel_suffices`
2. **Session env instance** → derives `senv_suffices` (analogous property)

For session environments to be a proper NatGraded instance, we need:

```coq
(* Depth of a single session type *)
Fixpoint stype_depth (s : stype dtype) : nat :=
  match s with
  | STEnd => 0
  | STSend _ k => (stype_depth k).+1
  | STRecv _ k => (stype_depth k).+1
  end.

(* Depth of session environment - max over all parties *)
(* Note: requires finite party assumption or specific party set *)
Definition senv_depth (env : senv dtype) (parties : seq nat) : nat :=
  \max_(p <- parties) stype_depth (env p).
```

**Design consideration**: Since `senv` is `nat -> stype` (infinite domain), we need either:
- A finite party set to compute depth, OR
- A sigma type `{ env : senv & senv_depth env = n }` with proof of finiteness

This enables proving properties like:
```coq
(* Analogous to fuel_suffices *)
Lemma senv_suffices env parties n :
  senv_depth env parties >= n ->
  (* session protocol execution property *)
```

### 2. How do `senv_send`/`senv_recv` work?

**Answer: They prepend operations; execution consumes them.**

```coq
(* senv is a function type: nat -> stype *)
Definition senv : Type := nat -> stype.

Definition senv_send (env : senv) (dst : nat) (d : dtype) : senv :=
  fun p => if p == dst then STSend d (env p) else env p.

Definition senv_recv (env : senv) (src : nat) (d : dtype) : senv :=
  fun p => if p == src then STRecv d (env p) else env p.
```

- `senv_send` prepends `STSend d` to party `dst`'s session type
- `senv_recv` prepends `STRecv d` to party `src`'s session type
- During execution, the process "moves back" to the continuation environment

This is not a "reduce" operation in the traditional sense—it's building up a session type during construction, then unwinding it during execution.

### 3. What is the exact type of `step_context`?

**Answer: `step : seq proc -> seq data -> nat -> proc * seq data * bool`**

From `smc_interpreter.v`:
```coq
Definition step (ps : seq proc) (trace : seq data) (i : nat) :=
  let p := nth default_proc ps i in
  let nop := (p, trace, false) in
  match p with
  | Recv frm f => ...
  | Send dst w next => ...
  | Init d next => (next, d::trace, true)
  | Ret d => (Finish, d :: trace, true)
  | Finish => nop
  | Fail => nop
  end.
```

For the mixin, define:
```coq
Record step_context := {
  processes : seq proc ;    (* all processes *)
  trace : seq data ;        (* trace for current process *)
  process_idx : nat ;       (* index of process to step *)
}.
```

The return type is `(proc, seq data, bool)` where the bool indicates whether progress was made.

---

## Revised Layer 2: Parallel Instances

The key insight is that **both fuel and session environments** are instances of the same generic pattern, deriving analogous lemmas.

### 2.1 Fuel Instance

```coq
(* Fuel family: trivially indexed by nat *)
Definition fuel_family (n : nat) : Type := unit.

HB.instance Definition _ := isNatGraded.Build fuel_family
  tt                          (* base: unit at level 0 *)
  (fun _ _ => tt).            (* down: trivial *)

(* Bundle: aproc with fuel as level *)
HB.instance Definition _ := isStepDecreasing.Build
  (aproc party) step_context
  aproc_fuel                  (* level = fuel *)
  aproc_step
  aproc_step_decreases.

(* Derived from generic lemma *)
Lemma fuel_suffices h ps traces :
  h >= [>ps] -> interp h ps traces = interp [>ps] ps traces.
Proof. apply: suffices_generic. Qed.
```

### 2.2 Session Env Instance

```coq
(* Session type depth *)
Fixpoint stype_depth (s : stype dtype) : nat :=
  match s with
  | STEnd => 0
  | STSend _ k => (stype_depth k).+1
  | STRecv _ k => (stype_depth k).+1
  end.

(* Step down a session type *)
Definition stype_down (s : stype dtype) : stype dtype :=
  match s with
  | STEnd => STEnd
  | STSend _ k => k
  | STRecv _ k => k
  end.

(* Session env family indexed by depth *)
Definition senv_family (n : nat) (parties : seq nat) : Type :=
  { env : senv dtype | senv_depth env parties = n }.

HB.instance Definition _ := isNatGraded.Build (senv_family parties)
  (exist _ senv_end eq_refl)  (* base: empty env at depth 0 *)
  senv_down_proof.            (* down: reduce depth by 1 *)

(* Bundle for session-env-indexed types *)
(* ... application-specific ... *)

(* Derived from generic lemma - analogous to fuel_suffices *)
Lemma senv_suffices env parties n :
  senv_depth env parties >= n ->
  (* session protocol property - e.g., all communications complete *)
Proof. apply: suffices_generic. Qed.
```

### 2.3 The Pattern

| Instance | Level Function | Derived Lemma |
|----------|---------------|---------------|
| Fuel | `aproc_fuel` | `fuel_suffices` |
| Session Env | `senv_depth` | `senv_suffices` |
| (Future types) | `my_level` | `my_suffices` |

Both derive their termination properties from the same generic `suffices_generic` lemma.

---

## Agent Tasks

Actionable tasks for implementation, in dependency order.

### General Instructions

1. **New files**: Add to `_CoqProject` before compiling
2. **Single file validation**: Use `coqtop` with absolute path
3. **Whole change validation**: Run `make dsdp`
4. **Proof debugging**: Follow `.cursor/commands/coqdebug.md`:
   - One tactic per line
   - Insert `Show` after each proof line to see goal/context
   - Use `apply` instead of `apply:` for more information
   - Use explicit application `@lemma ...` for correct arguments
   - Remove `.vo` files before `make` to verify changes
   - For dependent type errors, make types explicit or split to helper lemmas
   - Report any `Hypothesis`, `Abort`, `Admitted` to the user
   - For repeated issues, create inline test file with `cat >> ... << EOF`

### Task 1: Create `graded_resource.v` with Generic Mixins

**File**: `smc/graded_resource.v`

**Deliverables**:
1. Add `smc/graded_resource.v` to `_CoqProject`
2. `isNatGraded` mixin and `NatGraded` structure
3. `isStepDecreasing` mixin and `StepDecreasing` structure
4. `isDecomposableInterp` mixin and `DecomposableInterp` structure

**Acceptance criteria**:
- File added to `_CoqProject`
- File compiles with `From HB Require Import structures.`
- Follows math-comp naming conventions
- Includes module documentation header

---

### Task 2: Prove Generic Termination Lemmas

**File**: `smc/graded_resource.v` (extend)

**Deliverables**:
1. `Section GenericTermination` with context variables
2. `suffices_nored_generic` lemma
3. `suffices_generic` lemma (analogous to `fuel_suffices`)

**Dependencies**: Task 1

**Acceptance criteria**:
- Lemmas are stated in terms of mixin fields only
- No application-specific types (sproc, aproc, senv) referenced

---

### Task 3: Define `stype_depth` and `senv_depth`

**File**: `smc/smc_session_types.v` (extend)

**Deliverables**:
1. `Fixpoint stype_depth (s : stype dtype) : nat`
2. `Definition senv_depth (env : senv dtype) (parties : seq nat) : nat`
3. Basic lemmas: `stype_depth_send`, `stype_depth_recv`, `senv_depth_end`

**Dependencies**: None (can run in parallel with Tasks 1-2)

**Acceptance criteria**:
- Definitions match the specification in this plan
- Proofs about depth decreasing under `stype_down`

---

### Task 4: Create `isNatGraded` Instance for Fuel

**File**: `smc/smc_session_types.v` (extend)

**Deliverables**:
1. `Definition fuel_family (n : nat) : Type := unit.`
2. `HB.instance` for `isNatGraded.Build fuel_family`

**Dependencies**: Task 1

**Acceptance criteria**:
- Instance compiles and is recognized by HB
- Trivial implementation (base = tt, down = fun _ _ => tt)

---

### Task 5: Create `isNatGraded` Instance for Session Env

**File**: `smc/smc_session_types.v` (extend)

**Deliverables**:
1. `Definition senv_family (n : nat) (parties : seq nat) : Type`
2. `Definition senv_down` (step down operation)
3. `HB.instance` for `isNatGraded.Build (senv_family parties)`
4. Proof that `senv_down` reduces depth by 1

**Dependencies**: Tasks 1, 3

**Acceptance criteria**:
- Instance compiles
- `senv_down` correctly handles all `stype` constructors

---

### Task 6: Create `isStepDecreasing` Instance for `aproc` (Fuel)

**File**: `smc/smc_session_types.v` (extend)

**Purpose**: Instance where level = fuel. This derives `fuel_suffices`.

**Deliverables**:
1. `Definition step_context` record type
2. `Definition aproc_step : aproc party -> step_context -> aproc party * nat`
3. `Lemma aproc_step_fuel_decreases` (fuel decreasing property)
4. `HB.instance` for `isStepDecreasing.Build (aproc party) step_context` with `aproc_fuel` as level

**Dependencies**: Task 1

**Acceptance criteria**:
- Proof by case analysis on `sproc` constructors
- All cases handled (SFinish, SRet, SInit, SSend, SRecv, SFail)
- Level function is `aproc_fuel`

---

### Task 6b: Create `isStepDecreasing` Instance for Session Env

**File**: `smc/smc_session_types.v` (extend)

**Purpose**: Instance where level = senv_depth. This derives `senv_suffices`.

**Deliverables**:
1. Define bundle type for session-env-indexed stepping (may reuse `aproc` or define new)
2. `Definition aproc_step_senv` or similar step function
3. `Lemma aproc_step_senv_decreases` (senv depth decreasing property)
4. `HB.instance` for `isStepDecreasing.Build` with `senv_depth` as level

**Dependencies**: Tasks 1, 3

**Acceptance criteria**:
- Level function is `senv_depth` (not `aproc_fuel`)
- Step decreases session env depth when communication happens
- Complements Task 6 (fuel instance) for the parallel pattern

**Design note**: The same `aproc` type can have multiple `isStepDecreasing` instances with different level functions. Alternatively, define a newtype wrapper if HB requires distinct types.

---

### Task 7: Create `isDecomposableInterp` Instance

**File**: `smc/smc_session_types.v` (extend)

**Deliverables**:
1. `Lemma interpD_proof : forall n m s, interp (n + m) s = interp m (interp n s)`
2. `Lemma interp0_proof : forall s, interp 0 s = s`
3. `HB.instance` for `isDecomposableInterp.Build state interp`

**Dependencies**: Task 1

**Acceptance criteria**:
- Uses existing `interpD` lemma if available, or proves it
- Instance compiles

---

### Task 8: Derive `fuel_suffices` from Generic Lemma

**File**: `smc/smc_session_types.v` (refactor)

**Deliverables**:
1. New proof of `fuel_suffices` using `suffices_generic`
2. New proof of `fuel_suffices_nored` using `suffices_nored_generic`
3. Preserve original lemma statements (API compatibility)

**Dependencies**: Tasks 2, 6 (fuel instance), 7

**Acceptance criteria**:
- Existing code that uses `fuel_suffices` still compiles
- Proofs are shorter than originals (just `apply: suffices_generic`)
- Uses the fuel `isStepDecreasing` instance (Task 6)

---

### Task 9: Derive `senv_suffices` (New Lemma)

**File**: `smc/smc_session_types.v` (extend)

**Deliverables**:
1. `Lemma senv_suffices` statement and proof
2. Documentation of what the lemma means for session protocols

**Dependencies**: Tasks 2, 5, 6b (senv instance)

**Acceptance criteria**:
- Proof uses `suffices_generic`
- Lemma is analogous to `fuel_suffices` but for session env depth
- Uses the senv `isStepDecreasing` instance (Task 6b)

---

### Task 10: Validate with Build

**Commands**:
- Single file: `coqtop` with absolute path (e.g., `coqtop -Q . infotheo < /absolute/path/to/file.v`)
- Whole change: `make dsdp` in project root

**Deliverables**:
1. All files compile without errors
2. No new warnings introduced
3. Existing tests pass

**Dependencies**: All previous tasks

**Acceptance criteria**:
- `make dsdp` completes successfully
- `_CoqProject` updated with new files
- No `Admitted` or `Abort` in final code

---

## Task Dependency Graph

```
Task 1 (mixins) ──┬──> Task 2 (generic lemmas) ──┬──> Task 8 (fuel_suffices)
                  │                               │
                  ├──> Task 4 (fuel NatGraded)    │
                  │                               │
                  ├──> Task 6 (aproc StepDecr     │
                  │            fuel instance) ────┤
                  │                               │
                  └──> Task 7 (interp Decomp) ────┘

Task 3 (stype_depth) ──┬──> Task 5 (senv NatGraded)
                       │
                       └──> Task 6b (aproc StepDecr ──> Task 9 (senv_suffices)
                                     senv instance)
                                           │
                            Task 2 ────────┘

All ──> Task 10 (validate build)
```

**Parallelization**:
- Tasks 1, 3 can run in parallel (no dependencies)
- Tasks 4, 6, 7 can run in parallel after Task 1
- Task 6b requires Tasks 1 and 3
- Task 8 requires Tasks 2, 6, 7
- Task 9 requires Tasks 2, 5, 6b

---

## Implementation Progress

### Task 1: ✅ COMPLETE

**File created**: `smc/graded_resource.v`

**Design notes**:
- `isStepDecreasing` is now an HB mixin with `step_ctx` (the context type) as a field, similar to how `run` is a field in `isDecomposableInterp`. This fits HB's single-key structure model.
- `isDecomposableInterp` is now an HB mixin with the interpreter as a field named `run` (avoiding name collision with common `interp` functions).

**Deliverables**:
- `isNatGraded` - HB mixin for nat-indexed type families
- `isStepDecreasing` - HB mixin with `step_ctx` as field (context type)
- `isDecomposableInterp` - HB mixin with `run`, `runD`, `run0` fields
- `DecomposableInterp` - HB structure for types with decomposable interpreter

**Validation**: File compiles successfully with `make smc/graded_resource.vo`

**Current mixin definition**:
```coq
HB.mixin Record isDecomposableInterp (S : Type) := {
  run : nat -> S -> S ;
  runD : forall n m s, run (n + m) s = run m (run n s) ;
  run0 : forall s, run 0 s = s ;
}.
HB.structure Definition DecomposableInterp := { S of isDecomposableInterp S }.
```

Note: Field is named `run` instead of `interp` to avoid shadowing common `interp` functions in application code.

### Task 2: ✅ COMPLETE

**File extended**: `smc/graded_resource.v`

**Deliverables**:
- `Section GenericTermination` with `S : DecomposableInterp.type` context
- `quiescent_run_id` helper lemma: quiescent states are fixed points under any fuel
- `suffices_generic` lemma: extra fuel beyond total_level doesn't matter

**Application-specific hypotheses required**:
- `total_level : S -> nat` - total level of a state
- `is_quiescent : S -> bool` - quiescence predicate
- `quiescent_fixed` - quiescent states don't change under single step (`run 1 s = s`)
- `fuel_leads_to_quiescence` - enough fuel leads to quiescence

**Validation**: File compiles successfully

### Task 3: ✅ COMPLETE

**File extended**: `smc/smc_session_types.v`

**Deliverables**:
- `stype_depth` - Fixpoint to compute depth of a session type (counts send/recv operations)
- `senv_depth` - Definition to compute max depth over a set of parties
- `stype_depth_send`, `stype_depth_recv`, `stype_depth_end` - Basic computational lemmas
- `senv_depth_end` - Empty environment has depth 0
- `leq_bigmax_seq_simple` - Helper lemma for proving membership in bigmax
- `senv_depth_send`, `senv_depth_recv` - Session operations increase depth

**Code**:
```coq
Fixpoint stype_depth (s : stype dtype) : nat :=
  match s with
  | STEnd => 0
  | STSend _ k => (stype_depth k).+1
  | STRecv _ k => (stype_depth k).+1
  end.

Definition senv_depth (env : senv dtype) (parties : seq nat) : nat :=
  \max_(p <- parties) stype_depth (env p).
```

**Validation**: File compiles successfully with `make smc/smc_session_types.vo`

### Task 10: ✅ COMPLETE (Partial)

**Commands run**: `make dsdp`

**Result**: All files in `smc/`, `homomorphic_encryption/`, and `dumas2017dual/` compile successfully.

**Files validated**:
- `smc/graded_resource.vo` - Generic mixins and termination lemmas
- `smc/smc_session_types.vo` - Session types with depth definitions and isDecomposableInterp instance
- All other SMC and DSDP files compile without errors

### Task 7: ✅ COMPLETE

**File extended**: `smc/smc_session_types.v`

**Deliverables**:
- `interp_state` - Type alias for interpreter state: `seq (proc data) * seq (seq data)`
- `interp_on_state` - Wrapper matching `isDecomposableInterp` signature: `nat -> interp_state -> interp_state`
- `run0_state` - Proof that `interp 0` is identity
- `runD_state` - Proof that `interp (n + m) s = interp m (interp n s)`
- HB instance of `isDecomposableInterp` for `interp_state`

**Code**:
```coq
Definition interp_on_state (h : nat) (s : interp_state) : interp_state :=
  let (ps, traces) := s in interp h ps traces.

HB.instance Definition _ := @isDecomposableInterp.Build
  interp_state interp_on_state runD_state run0_state.
```

**Validation**: File compiles successfully with `make smc/smc_session_types.vo`

### Task 4: ✅ COMPLETE

**Status**: Complete. Implemented in `smc/smc_session_types.v`.

**Notes**: Trivial implementation - `fuel_family (n : nat) : Type := unit` with `base = tt` and `down = fun _ _ => tt`.

### Task 5: ✅ COMPLETE

**Status**: Complete. Implemented in `smc/smc_session_types.v`.

**Notes**: Implemented with exact depth semantics:
- `stype_down`: pops outer Send/Recv constructor
- `senv_down`: applies `stype_down` pointwise
- `senv_family n`: `{ env | senv_depth env parties = n }`
- Key lemmas: `predn_max`, `bigmax_pred`, `senv_depth_down`
- HB instance with `senv_family_base` and `senv_family_down`

### Task 6: ✅ COMPLETE

**Status**: Complete. Implemented in `smc/smc_session_types.v`.

**Design changes**:
- `isStepDecreasing` was converted from a plain Record to an HB mixin with `step_ctx` as a field (similar to how `run` is a field in `isDecomposableInterp`). This allows HB to manage it properly with a single type parameter.

**Implementation notes**:
- `aproc_local_step`: Steps an aproc locally (handles Init/Ret, others stay blocked)
- Context type is `unit` since local stepping doesn't need external context
- Level function is `aproc_fuel`
- Destructuring aproc uses `[party [n [env sp]]]` for nested sigT
- Constructors need `party:=party` annotation for implicit args (e.g., `mk_aproc (party:=party) SFinish`)
- SFail needs explicit indices: `@mk_aproc _ _ party n' env' SFail`

**Code**:
```coq
Definition aproc_local_step (ap : aproc dtype data) : aproc dtype data * nat.
(* Case analysis on sproc constructors *)

HB.instance Definition _ := @isStepDecreasing.Build (aproc dtype data)
  unit
  aproc_fuel
  (fun ap _ => aproc_local_step ap)
  (fun ap _ => aproc_local_step_decreases ap).
```

### Task 6-full: ✅ COMPLETE

**Status**: Complete. Implemented in `smc/smc_session_types.v`.

**Purpose**: Full context step function that handles Send/Recv with matching partners.

**Implementation notes**:
- `aproc_full_ctx`: Record with `ctx_procs : seq (proc data)`, `ctx_trace : seq data`, `ctx_idx : nat`
- `aproc_full_step`: Steps an aproc using full context to check for matching Send/Recv
- For SSend: checks if `nth procs dst` is a `Recv` from `ctx_idx`
- For SRecv: checks if `nth procs src` is a `Send` to `ctx_idx`, extracts value
- Case analysis on `proc` constructors: Init, Send, Recv, Ret, Finish, Fail
- Proof follows same pattern as `aproc_local_step_decreases`

**Code**:
```coq
Record aproc_full_ctx := {
  ctx_procs : seq (proc data) ;
  ctx_trace : seq data ;
  ctx_idx : nat ;
}.

Definition aproc_full_step (ap : aproc dtype data) (ctx : aproc_full_ctx)
    : aproc dtype data * nat.
(* Case analysis on sproc, then on proc at dst/src *)

Lemma aproc_full_step_decreases (ap : aproc dtype data) (ctx : aproc_full_ctx) :
  aproc_fuel (aproc_full_step ap ctx).1 + (aproc_full_step ap ctx).2 <= aproc_fuel ap.
```

**Note**: No HB instance created because HB requires distinct types. The local step instance is canonical; this full context version is available for direct use.

### Task 2-extended: ✅ COMPLETE

**File extended**: `smc/graded_resource.v`

**Added**: `sum_level_decreases` - the key aggregation lemma for lifting single-bundle stepping to collection-level.

**Purpose**: This lemma bridges the gap between `isStepDecreasing` (single bundle property) and termination proofs over collections of processes. It abstracts the induction step of `fuel_suffices_nored`.

**Code**:
```coq
Section SumDecreasing.
Variable B : Type.
Variable level : B -> nat.
Variable step_ctx : Type.
Variable step_bundle : B -> step_ctx -> B * nat.
Variable default_b : B.
Variable default_c : step_ctx.
Hypothesis step_decreases : forall b c,
  level (step_bundle b c).1 + (step_bundle b c).2 <= level b.

Lemma sum_level_decreases (bs : seq B) (cs : seq step_ctx) :
  (exists k, k < size bs /\
    (step_bundle (nth default_b bs k) (nth default_c cs k)).2 = 1) ->
  stepped_levels bs cs < original_levels bs.
```

**Connection to fuel_suffices_nored**: Documents how this lemma corresponds to the induction step where one process making progress decreases total fuel.

### Task 6b: ✅ PARTIAL COMPLETE

**Status**: Implemented `senv_step_nonincreasing` (weaker form). Full `isStepDecreasing` instance not created.

**File extended**: `smc/smc_session_types.v`

**Key insight**: Unlike fuel which strictly decreases by 1 on progress, `senv_depth` decrease depends on which party is involved. The depth only strictly decreases when the communicating party (dst for SSend, src for SRecv) has the maximum depth.

**Implemented**:
- `big_max_mono` - monotonicity of bigmax over sequences
- `senv_depth_senv_send_geq` - senv_send preserves or increases depth
- `senv_depth_senv_recv_geq` - senv_recv preserves or increases depth
- `senv_step_nonincreasing` - session env depth never increases after a step

**Why non-increasing is sufficient**:
1. Fuel bounds the number of steps
2. Each step preserves or decreases senv depth
3. Therefore, after fuel steps, senv depth is bounded
4. `fuel_suffices` already guarantees termination; senv termination follows

**Code**:
```coq
Lemma senv_step_nonincreasing (ap : aproc dtype data) (ctx : aproc_ctx) :
  senv_depth (aproc_env (aproc_step ap ctx).1) parties 
  <= senv_depth (aproc_env ap) parties.
```

**Note**: A strict decrease version would require tracking whether the max-depth party is involved in the communication, which adds complexity without clear benefit since fuel termination is already guaranteed.

### Task 8: ⏳ PENDING

**Status**: Not started. Depends on Tasks 2, 6, 7 (all complete).

**Notes**: Derive `fuel_suffices` from `suffices_generic` or `fuel_suffices_alt`. 

**Design options**:
1. Use `fuel_suffices_alt` directly with `fuel_suffices_nored` providing quiescence
2. Instantiate `sum_level_decreases` with `aproc` to simplify `fuel_suffices_nored` proof
3. Keep original proofs and use generic lemmas as documentation

**Recommended approach**: Use `fuel_suffices_alt` - the original `fuel_suffices` proof already follows this pattern implicitly.

### Task 9: ⏳ PENDING (Simplified)

**Status**: Simplified - `senv_suffices` follows from `fuel_suffices` + `senv_step_nonincreasing`.

**Notes**: Since `senv_step_nonincreasing` shows senv depth never increases, and `fuel_suffices` shows the interpreter reaches quiescence, the session environment is guaranteed to be in its final state. A separate `senv_suffices` lemma may not be needed.

**Alternative formulation**: If needed, `senv_suffices` could state:
```coq
(* After sufficient fuel, all sessions have ended or are blocked *)
Lemma senv_suffices h (ps : seq (aproc dtype data)) traces parties :
  (h >= [> ps])%N ->
  senv_depth (aproc_env (nth aproc_default ps 0)) parties 
  <= senv_depth (aproc_env (nth aproc_default (fst (interp h ...)) 0)) parties.
```
But this is essentially `senv_step_nonincreasing` composed over all steps.
