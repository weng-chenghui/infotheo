# PGG piSMC Trace Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the shared PGG piSMC program executable through the interpreter and derive protocol correctness from the executed trace, for all four in-scope instances (den Boer, Kim, S5, S5×S5), mirroring DSDP.

**Architecture:** A generic `protocol/pgg_run.v` provides the input-derived-content dealer, a trace-endpoint reader, and a generic bridge lemma. Each instance gets a thin `<inst>_run.v` with `interp`-executed procs, a `traces_ok` structural lemma, and a `recovers` correctness lemma, exactly as `dumas2017dual/dsdp/dsdp_correctness.v` does for DSDP. The dealer's word stays the identity; permutation values stay symbolic; correctness closes via the existing word-independent recon lemmas.

**Tech Stack:** Rocq + MathComp + infotheo; the piSMC interpreter (`smc/smc_interpreter.v`, `smc/pismc.v`, `smc/smc_session_types.v`); `rocq-mcp` for interactive proving; `make -j1` for builds.

**Spec:** `docs/superpowers/specs/2026-06-14-pgg-piSMC-trace-bridge-design.md`.

---

## Conventions for this plan (Rocq TDD)

The TDD analog for proofs: **state the lemma with `Admitted` (the "failing test"), confirm it typechecks, prove it (delegate the proof body to `rocq-prover` per project convention in CLAUDE.md), confirm `Qed` + file compiles, check axioms, commit.** "Test fails" = `Admitted`/incomplete; "test passes" = `Qed` + clean `Print Assumptions`.

- **Build a single file:** `make -j1 <path>.vo` (RAM safety: never `-j4`).
- **Interactive check during proving:** `rocq-mcp` `rocq_compile`/`rocq_check`; **max 2 full-file compilations per delegated proof** (CLAUDE.md).
- **Axiom check:** `rocq_query("Print Assumptions <name>.")`; allowed: `boolp`/classical axioms already used by the instances; **no new custom axioms** without explicit approval.
- **Never** `rewrite !lemma` on nat arithmetic; **never** `lia`. Keep perm values symbolic (do not force `nat_of_ord (rho _ _)` to a number).
- **Stage only files touched this task**; print the staged set before committing.

Validated facts from the 2026-06-14 feasibility spike (reuse, do not re-derive):
- `run_interp h (erase_aprocs aps)` reduces the `ForList` dealer to all-`Finish`; `(…).1 = [:: Finish; …]` proves `by vm_compute`.
- Trace **structure** (`map size …`) proves `by vm_compute`. Trace **values** (perm applications) stay symbolic.
- Pipeline: session `sproc` → `mk_aproc`/`[aprocs …]` → `erase_aprocs` → `seq (proc data)` → `run_interp h …` / `interp_traces h …`.
- DSDP template shape: `dsdp_correctness.v:137` (`[aprocs …]`), `:142` (`erase_aprocs`), `:145` (`interp …`), `:168` (`interp_traces`), `:186` (`dsdp_traces_ok`), `:201` (`dsdp_is_correct`, closed by `ring`).

---

## File Structure

- **Create** `pgg-smc/protocol/pgg_run.v` — generic: `identity_deck`, `dealer_with_input_encoding`, `sheets_of`/`endpoints_of_trace`, `recovers_of_endpoints` (bridge). Responsibility: the interpreter-execution + trace→recon glue, group/secret-agnostic.
- **Create** `pgg-smc/instances/kim2025/kim_run.v`, `pgg-smc/instances/s5/s5_run.v`, `pgg-smc/instances/s5x5/s5x5_run.v` — per-instance `<inst>_procs`, `<inst>_traces_ok`, `<inst>_recovers`.
- **Modify** `pgg-smc/instances/denboer1989/den_boer_run.v` — add `den_boer_procs`, `den_boer_traces_ok`, `den_boer_recovers`; generalize `den_boer_dealer_layout` to call the generic dealer.
- **Modify** `pgg-smc/instances/denboer1989/den_boer_profile.v` — delete the conflated `den_boer_assemble := [:: 1%g]` (Phase E).
- **Modify** `_CoqProject` — register the four new files (in dependency order, after their deps).

Party-index/order contract (all instances): the `seq (proc data)` is indexed by process id — `[dealer(0); verifier(1); player₀(2) … player_{T-1}(T+1); input-parties…]`. Players occupy ids `2..T+1`; den Boer/Kim input parties occupy `7,8` (`den_boer_profile.v` uses `[:: 7; 8]`).

---

## Phase A — Generic module `protocol/pgg_run.v`

### Task A1: Module skeleton + `identity_deck` + `dealer_with_input_encoding`

**Files:**
- Create: `pgg-smc/protocol/pgg_run.v`
- Modify: `_CoqProject` (add `pgg-smc/protocol/pgg_run.v` after `card_exchange_pismc.v`/`pgg_input_commitment.v`, before instances)

- [ ] **Step 1: Write the module header + definitions**

```coq
(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG piSMC trace bridge: execute the shared program and read correctness    *)
(* off the executed trace (DSDP-style). The cut stays the identity; endpoint  *)
(* values stay symbolic.                                                       *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop.
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc
                            pgg_input_commitment.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section pgg_run.
Variable M : MonodromyReprWithGeneratorType.
Variable PI : PGGInterface M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let data := pgg_data N.

(** identity_deck — the singleton deck carrying the identity cut. *)
Definition identity_deck : seq (pgg_gT M) := [:: 1%g].

(** dealer_with_input_encoding — generic input-derived-content dealer: a commit
    prologue collecting [inputs], then [exchange_dealer] with the committed
    content readout and the identity cut. Generalizes den_boer_dealer_layout. *)
Definition dealer_with_input_encoding
    (content_of : seq 'I_N -> ('I_N -> 'I_N))
    (inputs : seq nat) (players : seq 'I_T) (P_idx : nat) :=
  pgg_commit_prologue
    (fun committed =>
       exchange_dealer PI (content_of committed) players identity_deck P_idx)
    [::] inputs.

End pgg_run.

Arguments identity_deck {M}.
Arguments dealer_with_input_encoding {M} PI.
```

- [ ] **Step 2: Register in `_CoqProject` and compile-check**

Add the line `pgg-smc/protocol/pgg_run.v` immediately after the `pgg_input_commitment.v` line in `_CoqProject` (around line 137).

Run (rocq-mcp): `rocq_compile` on the file content above, `workspace=/Users/cheng-huiweng/Projects/coq/infotheo-pgg`.
Expected: success, no errors. If `pgg_commit_prologue`'s implicit `{dn}/{denv}` need fixing, supply them as in `exchange_dealer_with_commit` (`pgg_input_commitment.v:67`).

- [ ] **Step 3: Commit**

```bash
git add pgg-smc/protocol/pgg_run.v _CoqProject
git commit -m "pgg_run: generic identity_deck + dealer_with_input_encoding"
```

### Task A2: `sheets_of` / `endpoints_of_trace`

**Files:**
- Modify: `pgg-smc/protocol/pgg_run.v` (inside `Section pgg_run`, after `dealer_with_input_encoding`)

- [ ] **Step 1: Add the trace-endpoint reader**

```coq
(** sheets_of — the PGG_sheet payloads of a trace, in trace order. *)
Definition sheets_of (tr : seq data) : seq 'I_N :=
  pmap (fun d => if d is PGG_sheet x then Some x else None) tr.

(** endpoints_of_trace — the T endpoints the verifier collected, as a T-tuple.
    The verifier Inits one PGG_sheet per player; sheets_of reads them out. The
    [rev]/order is pinned in each instance's traces_ok against the executed
    trace (verifier pushes player T-1 first). *)
Definition endpoints_of_trace (verifier_trace : seq data) : seq 'I_N :=
  rev (sheets_of verifier_trace).
```

(Note: this returns a `seq`; each instance's `recovers` rewrites it to the
`T.-tuple` `[tuple content (rho 1 (start i)) | i < T]` via `traces_ok`. Keeping
it a `seq` here avoids a size-proof obligation in the generic layer.)

- [ ] **Step 2: Compile-check** — `rocq_compile` the file; Expected: success.

- [ ] **Step 3: Commit**

```bash
git add pgg-smc/protocol/pgg_run.v
git commit -m "pgg_run: endpoints_of_trace reader (PGG_sheet payloads, reversed)"
```

### Task A3: Generic bridge `recovers_of_endpoints`

**Files:**
- Modify: `pgg-smc/protocol/pgg_run.v`

This bridge says: if the executed verifier endpoints equal the abstract endpoint
tuple `[tuple content (rho P (start i)) | i<T]`, then reconstructing them yields
the secret. It is a thin wrapper over `pgg_recon_monodromy_correct`
(`reconstruct/pgg_sharing_framework.v:293`).

- [ ] **Step 1: Read the source lemma, then state the bridge as `Admitted`**

First read `reconstruct/pgg_sharing_framework.v:284-340` to transcribe
`pgg_recon_endpoints`/`pgg_recon_monodromy_correct` exactly (section variables
`M PI secretT ts HT content`, plus the lemma's `(H : {group gT}) (s) (P) (perm)
(HsubG) (G_stable)`). The bridge re-exposes that conclusion against the executed
endpoint seq. Its statement is **the `pgg_recon_monodromy_correct` conclusion
with the abstract endpoint tuple replaced by `in_tuple eps` under the size proof
`size eps = T`**, i.e. (schematically, finalize the exact hypotheses by copying
the source lemma):

```coq
From pgg_reconstruct Require Import pgg_sharing_framework.

(* In a section with the SAME variables as pgg_recon_monodromy_correct, plus: *)
Lemma recovers_of_endpoints (eps : seq 'I_N) (Hsz : size eps = T)
    (Heps : eps = [seq content (rho P (tnth starts i)) | i <- enum 'I_T]) :
  P \in H ->
  ts_valid ts s [tuple content (tnth (cast_tuple (esym (congr1 S HT))
                  (pi_starts PI)) j) | j < (ts_T' ts).+1] ->
  ts_recon ts (cast_tuple (esym (congr1 S HT))
    (tcast (esym Hsz) (in_tuple eps))) = s.
Proof. Admitted.
```

NOTE: `tcast (esym Hsz) (in_tuple eps) : T.-tuple 'I_N`. **Delegate to
`rocq-prover`** to (a) copy the precise section context + remaining hypotheses
from `pgg_sharing_framework.v:293-318`, (b) `rewrite Heps` so `in_tuple eps`
becomes the abstract `[tuple content (rho P (start i)) | i<T]` (use
`eq_from_tnth`/`tnth_map`), and (c) `exact: pgg_recon_monodromy_correct …`. Only
`in_tuple`/`tcast`/`cast_tuple` (all MathComp) and source-lemma names are used.

- [ ] **Step 2: Typecheck the `Admitted` statement** — `rocq_compile`; Expected: success with an `Admitted` warning only.

- [ ] **Step 3: Prove (delegate to `rocq-prover`)**

Dispatch a `rocq-prover` task: "Prove `recovers_of_endpoints` in `pgg-smc/protocol/pgg_run.v`. It must reduce to `pgg_recon_monodromy_correct` (`reconstruct/pgg_sharing_framework.v:293`). Copy that lemma's exact section hypotheses; the only new content is identifying the executed endpoint seq with the abstract `[tuple content (rho P (start i)) | i<T]`. Deps prebuilt: pgg_sharing_framework.vo, card_exchange_pismc.vo. Budget 30 turns, max 2 full compiles, rocq-mcp 4-phase workflow. No new axioms."

- [ ] **Step 4: Verify `Qed` + axioms**

Run (rocq-mcp): `rocq_query("Print Assumptions recovers_of_endpoints.", file=pgg-smc/protocol/pgg_run.v)`.
Expected: only classical/`boolp` axioms already used by the framework; no custom axioms. Then `make -j1 pgg-smc/protocol/pgg_run.vo`; Expected: success.

- [ ] **Step 5: Commit**

```bash
git add pgg-smc/protocol/pgg_run.v
git commit -m "pgg_run: recovers_of_endpoints bridge (executed endpoints -> secret)"
```

---

## Phase B — den Boer run (spike: input-encoded, N=5)

This is the first concrete run and the de-risking spike for the commit prologue.

### Task B1: `den_boer_procs`

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_run.v` (add after the existing `den_boer_dealer_layout` block; reuse `den_boer_players`, `den_boer_encoding`, `den_boer_decode`)

- [ ] **Step 1: Add the executed-program assembly**

```coq
From pgg_smc Require Import pgg_run.

(** den_boer_dealer_run — the den Boer dealer via the generic input-encoding
    dealer: identity cut, input-derived content from den_boer_encoding. *)
Definition den_boer_dealer_run (P_idx : nat) :=
  dealer_with_input_encoding FiveCardKim_PI
    (fun committed => tnth (ie_assemble den_boer_encoding (den_boer_decode committed)))
    [:: 7; 8] den_boer_players P_idx.

(** den_boer_saprocs — dealer ++ verifier ++ players ++ input parties, ordered
    by process id. *)
Definition den_boer_saprocs (a b : bool) (P_idx : nat)
    : seq (aproc pgg_dtype (pgg_data (pgg_N' FiveCardKim_M).+1)) :=
  [aprocs den_boer_dealer_run P_idx
        ; exchange_verifier FiveCardKim_PI den_boer_players
        ; exchange_player FiveCardKim_PI (@Ordinal 5 0 isT)
        ; exchange_player FiveCardKim_PI (@Ordinal 5 1 isT)
        ; exchange_player FiveCardKim_PI (@Ordinal 5 2 isT)
        ; exchange_player FiveCardKim_PI (@Ordinal 5 3 isT)
        ; exchange_player FiveCardKim_PI (@Ordinal 5 4 isT)
        ; pgg_commit FiveCardKim_M 7 (encode_bool a)
        ; pgg_commit FiveCardKim_M 8 (encode_bool b)].

Definition den_boer_procs (a b : bool) (P_idx : nat) :=
  erase_aprocs (den_boer_saprocs a b P_idx).
```

- [ ] **Step 2: Compile-check** — `rocq_compile` the file. Expected: success. If `tnth (ie_assemble …)` has an `'I_(ts_T'+1)` vs `'I_N` index mismatch, insert the `FiveCardKim_Teq` cast exactly as `den_boer_dealer_layout` does (`den_boer_run.v:74-79`) — copy its content expression verbatim.

- [ ] **Step 3: Commit**

```bash
git add pgg-smc/instances/denboer1989/den_boer_run.v
git commit -m "den_boer_run: den_boer_procs via generic input-encoding dealer"
```

### Task B2: `den_boer_traces_ok` (executed structure)

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_run.v`

- [ ] **Step 1: State the structural lemmas as `Admitted`**

```coq
(** den_boer_run_terminates — every process reaches Finish. *)
Lemma den_boer_run_terminates (a b : bool) (P_idx : nat) :
  (run_interp 80 (den_boer_procs a b P_idx)).1 = nseq 9 Finish.
Proof. Admitted.

(** den_boer_endpoints — the verifier (index 1) collected the five endpoints,
    each PGG_sheet (rho 1 (start i)) read through the input-derived content. *)
Lemma den_boer_endpoints (a b : bool) (P_idx : nat) :
  endpoints_of_trace (nth [::] (run_interp 80 (den_boer_procs a b P_idx)).2 1)
  = [seq tnth (den_boer_layout (a, b)) i | i <- enum 'I_5].
Proof. Admitted.
```

NOTE: `nseq 9 Finish` reflects 9 procs (1 dealer + 1 verifier + 5 players + 2
inputs). The RHS of `den_boer_endpoints` is the symbolic endpoint seq; with the
identity cut and `starts = ord_tuple 5`, `content (rho 1 (start i)) = tnth
(den_boer_layout (a,b)) i`. **Delegate to `rocq-prover`** to pin the exact RHS
order (the verifier pushes player 4 first; `endpoints_of_trace` already
`rev`-erses) and the fuel constant (80 is an upper bound; lower it if it reduces
faster). Proof tactic: `by vm_compute` for `_terminates`; for `_endpoints`,
`vm_compute`-reduce the structure (both sides carry the same symbolic
`tnth (den_boer_layout …)` term) then `reflexivity`, or `rewrite interp_traces_ok`
then structural (mirror `dsdp_traces_ok`, `dsdp_correctness.v:186`).

- [ ] **Step 2: Typecheck** — `rocq_compile`; Expected: success with `Admitted` warnings.

- [ ] **Step 3: Prove (delegate to `rocq-prover`)**

Dispatch: "Prove `den_boer_run_terminates` and `den_boer_endpoints` in `den_boer_run.v`. `_terminates` is `by vm_compute` (validated: ForList reduces). For `_endpoints`, reduce control flow and match the symbolic `den_boer_layout` endpoints; perm values stay symbolic — do NOT force `nat_of_ord`. Adjust the fuel constant and the RHS order empirically via `rocq_query Eval vm_compute in …`. Deps prebuilt. Budget 40 turns, max 2 full compiles."

- [ ] **Step 4: Verify** — `make -j1 pgg-smc/instances/denboer1989/den_boer_run.vo`; `Print Assumptions den_boer_endpoints.` Expected: success; no custom axioms.

- [ ] **Step 5: Commit**

```bash
git add pgg-smc/instances/denboer1989/den_boer_run.v
git commit -m "den_boer_run: den_boer_run_terminates + den_boer_endpoints (executed trace structure)"
```

### Task B3: `den_boer_recovers` (correctness from the executed trace)

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_run.v`

- [ ] **Step 1: State the lemma as `Admitted`**

```coq
(** den_boer_recovers — reconstructing the verifier's executed endpoints returns
    the committed AND. The DSDP dsdp_is_correct analog for den Boer. *)
Lemma den_boer_recovers (a b : bool) (P_idx : nat) :
  ts_recon fcI_scheme
    (in_tuple (endpoints_of_trace
       (nth [::] (run_interp 80 (den_boer_procs a b P_idx)).2 1)))
  = a && b.
Proof. Admitted.
```

NOTE: connect `den_boer_endpoints` (Task B2) to the existing word-independent
`den_boer_run_output` (`den_boer_run.v:29`, already `= ab.1 && ab.2`). **Delegate
to `rocq-prover`**: `rewrite den_boer_endpoints`, reshape the seq into the tuple
`pgg_recon_endpoints` consumes, then `exact: den_boer_run_output` (or
`recovers_of_endpoints`). The `in_tuple` size/cast is the only fiddly step; pin
it against `fcI_scheme`'s `ts_T' = 4`.

- [ ] **Step 2: Typecheck** — `rocq_compile`; Expected: success with `Admitted` warning.

- [ ] **Step 3: Prove (delegate to `rocq-prover`)**

Dispatch: "Prove `den_boer_recovers` in `den_boer_run.v` by rewriting with `den_boer_endpoints` then reducing to `den_boer_run_output` (`:29`) or `recovers_of_endpoints` (pgg_run.v). Word-independent; cut is identity. Budget 30 turns, max 2 compiles. No new axioms."

- [ ] **Step 4: Verify** — `make -j1 …/den_boer_run.vo`; `Print Assumptions den_boer_recovers.` Expected: success; only pre-existing axioms.

- [ ] **Step 5: Commit**

```bash
git add pgg-smc/instances/denboer1989/den_boer_run.v
git commit -m "den_boer_run: den_boer_recovers (executed trace reconstructs a && b)"
```

---

## Phase C — S5×S5 run (spike: largest size N=10, position-model)

Position-model: `secretT = 'I_10`, no input parties, fixed-`rp_content` dealer
(`content = id`). De-risks the N=10 trace-structure reduction.

### Task C1: `s5x5_procs`

**Files:**
- Create: `pgg-smc/instances/s5x5/s5x5_run.v`
- Modify: `_CoqProject` (add after `rigidity_s5x5_instance.v`)

- [ ] **Step 1: Write the file**

```coq
(* … standard header + imports … *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface card_exchange_pismc pgg_run.
From pgg_reconstruct Require Import (* s5x5 plug/scheme deps as needed *).
From pgg_smc Require Import (* s5x5_profile / rigidity_s5x5_instance for s5x5_M, s5x5_PI *).

(** s5x5_players — the ten dealing players as an explicit list (so folds reduce
    under vm_compute). *)
Definition s5x5_players : seq 'I_(pi_T' s5x5_PI).+1 :=
  [seq (@Ordinal 10 i _) | i <- iota 0 10].   (* spell out the 10 ordinals literally *)

Definition s5x5_saprocs (P_idx : nat) : seq (aproc pgg_dtype (pgg_data 10)) :=
  [aprocs run_dealer (* fixed rp_content dealer at s5x5 profile *) [::] P_idx
        ; exchange_verifier s5x5_PI s5x5_players
        ; (* exchange_player s5x5_PI <ord i> for i = 0..9 *) ].

Definition s5x5_procs (P_idx : nat) := erase_aprocs (s5x5_saprocs P_idx).
```

NOTE: **Delegate the exact assembly to `rocq-prover`** — the literal 10-ordinal
list and the fixed-content dealer term (`run_dealer` from
`pgg_monodromy_profile.v:78` plugged at the s5x5 profile, `content = rp_content`).
The structure mirrors `den_boer_saprocs` minus input parties.

- [ ] **Step 2: Register in `_CoqProject` and compile-check** — `rocq_compile`; Expected: success.

- [ ] **Step 3: Commit**

```bash
git add pgg-smc/instances/s5x5/s5x5_run.v _CoqProject
git commit -m "s5x5_run: s5x5_procs (position-model, N=10)"
```

### Task C2: `s5x5_traces_ok` + `s5x5_recovers`

**Files:**
- Modify: `pgg-smc/instances/s5x5/s5x5_run.v`

- [ ] **Step 1: State `Admitted` lemmas**

```coq
Lemma s5x5_run_terminates (P_idx : nat) :
  (run_interp 200 (s5x5_procs P_idx)).1 = nseq 12 Finish.
Proof. Admitted.

Lemma s5x5_recovers (s : 'I_10) (P_idx : nat) :
  ts_recon s5x5_ts
    (in_tuple (endpoints_of_trace
       (nth [::] (run_interp 200 (s5x5_procs P_idx)).2 1))) = s.
Proof. Admitted.
```

NOTE: 12 procs (dealer + verifier + 10 players). The fixed-content dealer deals
the encoded secret directly; `s5x5_recovers` reduces to the existing position-model
recon (`rigidity_s5x5_instance.v` G-stability + recon-invariance). **Delegate to
`rocq-prover`.** Watch the fuel (200 is an upper bound; N=10 needs more steps than
N=5). If `vm_compute` on `_terminates` is slow, lower the fuel to the minimal value
that still terminates (find it via `rocq_query Eval vm_compute`).

- [ ] **Step 2: Typecheck** — `rocq_compile`; Expected: success with `Admitted` warnings.

- [ ] **Step 3: Prove (delegate to `rocq-prover`)** — same recipe as B2/B3, position-model recon. Budget 45 turns (larger N), max 2 compiles.

- [ ] **Step 4: Verify** — `make -j1 pgg-smc/instances/s5x5/s5x5_run.vo`; `Print Assumptions s5x5_recovers.` Expected: success; only pre-existing axioms (incl. `s5_group_order_eq`-style if already present).

- [ ] **Step 5: Commit**

```bash
git add pgg-smc/instances/s5x5/s5x5_run.v
git commit -m "s5x5_run: terminates + recovers (executed trace, N=10)"
```

---

## Phase D — Kim and S5 runs (mirror)

### Task D1: `kim_run.v`

**Files:**
- Create: `pgg-smc/instances/kim2025/kim_run.v`
- Modify: `_CoqProject`

- [ ] **Step 1: Mirror Phase B** for Kim (`FiveCardKim_M`, `FiveCardKim_PI`, the five-card plug, `secretT = bool`). Kim has an `InputEncoding`? If not, reuse `den_boer_encoding`'s shape or use the fixed-content dealer if Kim's run has no committed inputs. Define `kim_procs`, `kim_run_terminates`, `kim_recovers`.

NOTE: **Delegate to `rocq-prover`.** Confirm first (via `git grep "InputEncoding" instances/kim2025`) whether Kim has its own input encoding; if not, Kim's run uses the fixed-content five-card dealer and `kim_recovers` reduces to `FiveCardKim_protocol_correct` (`den_boer_profile.v:143`).

- [ ] **Step 2: Register + compile** — `rocq_compile`; Expected: success.
- [ ] **Step 3: Prove (delegate)** — recipe as Phase B.
- [ ] **Step 4: Verify** — `make -j1 …/kim_run.vo`; `Print Assumptions kim_recovers.`
- [ ] **Step 5: Commit**

```bash
git add pgg-smc/instances/kim2025/kim_run.v _CoqProject
git commit -m "kim_run: kim_procs + terminates + recovers"
```

### Task D2: `s5_run.v`

**Files:**
- Create: `pgg-smc/instances/s5/s5_run.v`
- Modify: `_CoqProject`

- [ ] **Step 1: Mirror Phase C** for S5 (`s5_M`, `s5_PI`, `secretT = 'I_5`, position-model, fixed content, no input parties; 7 procs = dealer + verifier + 5 players). Define `s5_procs`, `s5_run_terminates`, `s5_recovers`.
- [ ] **Step 2: Register + compile** — `rocq_compile`; Expected: success.
- [ ] **Step 3: Prove (delegate)** — recipe as Phase C.
- [ ] **Step 4: Verify** — `make -j1 …/s5_run.vo`; `Print Assumptions s5_recovers.`
- [ ] **Step 5: Commit**

```bash
git add pgg-smc/instances/s5/s5_run.v _CoqProject
git commit -m "s5_run: s5_procs + terminates + recovers"
```

---

## Phase E — Rename / cleanup

### Task E1: Delete the conflated `den_boer_assemble`

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_profile.v` (delete `den_boer_assemble`, `:190-191`, and rewire its two users `den_boer_dealer_committed` `:210` and `den_boer_dealer_layout` `den_boer_run.v:74` to the generic dealer)

- [ ] **Step 1: Find all users**

Run: `git grep -n "den_boer_assemble" pgg-smc/`
Expected: `den_boer_profile.v` (def + `den_boer_dealer_committed`), `den_boer_run.v` (`den_boer_dealer_layout`, `den_boer_run_output` proof).

- [ ] **Step 2: Rewire users to `dealer_with_input_encoding` / `identity_deck`**

Replace `den_boer_dealer_layout`'s body (`den_boer_run.v:74-79`) with `den_boer_dealer_run` (Task B1). Replace `den_boer_dealer_committed`'s use of `den_boer_assemble` with `identity_deck`. Delete the `den_boer_assemble` definition and its `@intent` comment.

- [ ] **Step 3: Compile the affected files and their dependents**

Run: `make -j1 pgg-smc/instances/denboer1989/den_boer_profile.vo pgg-smc/instances/denboer1989/den_boer_run.vo`
Expected: success. If `den_boer_run_output`'s proof referenced `den_boer_assemble`, repair it (delegate to `rocq-prover` if non-trivial).

- [ ] **Step 4: Audit-gate dry run + commit**

The commit stages `.v` files, so the rocq-audit pre-commit gate fires. Run the commit; if blocked, address findings or `ROCQ_AUDIT_BYPASS=1` only with explicit user approval.

```bash
git add pgg-smc/instances/denboer1989/den_boer_profile.v pgg-smc/instances/denboer1989/den_boer_run.v
git commit -m "denboer: delete conflated den_boer_assemble; route through identity_deck/dealer_with_input_encoding"
```

### Task E2 (OPTIONAL, gate on user confirmation): rename `den_boer_layout`→`den_boer_ie_assemble`, `den_boer_decode`→`den_boer_ie_decode`

**Files:**
- Modify: `pgg-smc/instances/denboer1989/den_boer_encoding.v`, `den_boer_run.v` (and dependents)

- [ ] **Step 1: Confirm with the user** whether the rename churn is wanted (the spec §5.3 lists it; the user flagged it as optional). If declined, skip Phase E2 entirely.
- [ ] **Step 2: Rename via `git grep` + `sed`-guided edits**, one identifier at a time; `make -j1` each touched file after each rename.
- [ ] **Step 3: Commit** `git commit -m "denboer: rename layout/decode to ie_assemble/ie_decode for clarity"`.

---

## Final verification

- [ ] **Whole-project build of touched files:** `make -j1` each new `.vo` in dependency order:
  `pgg-smc/protocol/pgg_run.vo`, then `den_boer_run.vo`, `s5x5_run.vo`, `kim_run.vo`, `s5_run.vo`.
  Expected: all succeed.
- [ ] **Axiom sweep:** for each of `recovers_of_endpoints`, `den_boer_recovers`, `s5x5_recovers`, `kim_recovers`, `s5_recovers`, run `rocq_query("Print Assumptions <name>.")`. Expected: no NEW custom axioms beyond those the instances already carry.
- [ ] **Definition-of-done check (spec §7):** all four `<inst>_recovers` are `Qed`; `den_boer_assemble := [:: 1%g]` removed; no existing correctness/privacy theorem weakened.
