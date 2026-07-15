# DSDP_n as a Stepwise Transition List

## Context

`dsdp_fsm.v` (2506 LOC) + `dsdp_fsm_progress.v` (2916 LOC) prove that the
imperative DSDP_n protocol (written in `dsdp_pismc.v` via the four templates
`palice_n` / `DParty_first` / `DParty_intermediate` / `DParty_last`) produces
the expected full trace and that Alice returns the dot product. The cost is
~5400 LOC of FSM phase Records (`phase_state`, `recv_phase`, `send_phase`,
`drain_phase`, `tail_phase`), 7 `dsdp_inv` constructors in `dsdp_progress.v`,
and ~700 LOC of `dsdp_inv_step_*` bookkeeping.

Earlier exploration considered a generic piSMC→FSM *compiler*. That is too
expensive for DSDP alone (costed at 800–1500 LOC soundness theorem + oracle
record + bridge). The user instead wants the direct version: **write DSDP_n
as a single list of `(party_id, dsdp_action)` pairs**, where actions are small
finite instructions (`AInit / AEnc / ADec / AMul / APow / AAdd / ASend /
ARet`), state is a `party_id → sw_party_state` record with three finsets (plain /
cipher / priv_key), and `sw_step` updates state directly. Knowledge is a field
of the state, not a separate inductive predicate. Correctness becomes

```coq
ret_of dsdp_n_final alice = Some (\sum_(i < n_relay.+2) u i * v_all i)
```

proved by one induction on `n_relay` (~80 LOC). A separate bridge theorem
(~200 LOC) connects this list to `rsteps` on the existing `dsdp_n_procs`
using the `*_erase` lemmas already in `dsdp_pismc.v:853-941`.

The deliverable is a new file `dumas2017dual/dsdp/dsdp_stepwise.v` that
lives alongside `dsdp_fsm.v`. No existing file is touched. Retirement of
`dsdp_fsm.v`/`dsdp_fsm_progress.v` is **explicitly out of scope**; this
plan only delivers the alternative presentation and the bridge.

## Locked design decisions (no loose ends)

| # | Question | Decision |
|---|---|---|
| D1 | File location | `dumas2017dual/dsdp/dsdp_stepwise.v` (+ `dsdp_stepwise_bridge.v`) |
| D2 | Input DSL | `seq (party_id * dsdp_action)` — one list per program, no `proc`, no `sproc` |
| D3 | Action-output semantics | **Outputs are computed by `sw_step` from the inputs** (option b from the discussion). So `AEnc pk m r`, `ADec c dk`, `AMul c1 c2`, `APow c x`, `AAdd a b` — no explicit "out" field. `ASend dst c` takes an already-held cipher. `AInit v dk` seeds local state. `ARet x` requires `x` to already be in `ps_plain`. |
| D4 | State type | `Record sw_party_state := { ps_plain : {fset plain}; ps_cipher : {fset cipher}; ps_priv : {fset priv_key}; ps_ret : option plain }` |
| D5 | Global state | `Definition sw_global_state := party_id -> sw_party_state.` (function, not finmap — we only read) |
| D6 | Failure model | `sw_step` returns `option sw_global_state`; `None` means precondition violated (e.g. `ASend` of a cipher not in sender's `ps_cipher`). Execution is `foldM sw_step`. |
| D7 | Indexing | Match `dsdp_pismc.v` exactly: alice = party 0, relay `j : 'I_n_relay.+1` lives at party `j.+1`, `alice_send_dest j = maxn 1 j`, `dk : 'I_n_relay.+1 → priv_key`, `v : 'I_n_relay.+1 → plain`, `u : 'I_n_relay.+2 → plain`, `r : 'I_n_relay.+1 → plain`, `ra, rb1, rb2 : 'I_n_relay.+1 → rand`, plus `dk_alice`, `v_alice`, `r_tail` at the top. |
| D8 | Parameter form | Section variables, identical to `dsdp_pismc.v:292-312`, so the bridge theorem can instantiate them without re-declaration. |
| D9 | `sw_pk_of` signature | `sw_pk_of : 'I_n_relay.+2 → pub_key AHE`, total. `sw_pk_of ord0 = pub_of dk_alice`; `sw_pk_of (lift ord0 j) = pub_of (dk j)`. No `nat`-based fallback. |
| D10 | Intermediate filter | `[seq j : 'I_n_relay.+1 <- enum 'I_n_relay.+1 \| (0 < val j < n_relay)%N]`. When `n_relay = 1` this is `[::]`. |
| D11 | Correctness theorem | `dsdp_n_correct : ret_of dsdp_n_final alice = Some (dot_product u v_all)` where `v_all : 'I_n_relay.+2 → plain` is `v_alice` at 0 and `v` shifted at `j.+1`. |
| D12 | Induction axis | On `n_relay`. Base `n_relay = 1` (first relay + last relay, no intermediates). Step: `n_relay.+1` adds one intermediate to the β-chain. |
| D13 | Bridge theorem scope | **In scope**. Stated as `dsdp_n_program_sound : rsteps_observation (dsdp_n_procs …) chain_schedule = dsdp_n_program`. Implementation lives in a sibling file `dsdp_stepwise_bridge.v`. Uses `palice_n_erase`, `DParty_first_erase`, `DParty_intermediate_erase`, `DParty_last_erase` from `dsdp_pismc.v:853-941`. |
| D14 | Retirement of `dsdp_fsm.v` | **Out of scope for this plan.** The stepwise file lives alongside; rewiring downstream (`dsdp_security.v`) is a separate future task. |
| D15 | Finset universe | `{fset plain}`, `{fset cipher}`, `{fset priv_key}` using `finmap` (already imported in `dsdp_pismc.v:3`). Choice types provided by HB instances on AHE types; confirmed present. |
| D16 | `ps_ret` convention | `ARet x` sets `ps_ret` to `Some x`, fails if already `Some _`. `ret_of g p := ps_ret (g p)`. |
| D17 | `ord_predS` (does not exist in mathcomp) | Define locally: `Definition ord_predS {n} (j : 'I_n.+1) : 'I_n.+1 := if val j is k.+1 then inord k else ord0`. Accessor lemma `ord_predS_lift : forall j : 'I_n, val (ord_predS (lift ord0 j)) = val j`. Budget 8 LOC. |
| D18 | `foldM` (does not exist in infotheo) | Define locally: `Fixpoint foldM {A B} (f : B -> A -> option B) (b : B) (l : seq A) : option B := match l with [::] => Some b \| a :: l' => obind (fun b' => foldM f b' l') (f b a) end`. Budget 4 LOC. |
| D19 | Bridge target — which operational engine? | **Commit to `rsteps` (relational)**, not `interp` (computable). Define `sw_trace_of : rsteps_derivation → seq (party_id * dsdp_action)` as a new helper that walks the derivation and emits one stepwise action per `rstep` firing, inverting the `erase` lemmas. Budget ~60 LOC (L16 below). |
| D20 | `chain_schedule` type and construction | `chain_schedule : seq lens` (concrete list of two-party lens pairs, one per firing). Built by `Fixpoint` over phases: `relay i sends c_i to alice`, then `alice fans α_j to dest(j)`, then `relay j receives β, decrypts, sends β_{j+1}`, etc. Explicit, not abstracted. Budget ~25 LOC. |
| **D21** | **`sw_step` precondition semantics — RELAXED (revised after Phase 2a wall)** | **`sw_step` is a cipher-tracking semantics, not a Dolev-Yao derivability semantics.** Preconditions: `AEnc pk m r` — **no** precondition (add `enc pk r m` to `ps_cipher`); `APow c x` — require `c ∈ ps_cipher` only (no check on `x`); `AMul c1 c2` — require `c1, c2 ∈ ps_cipher`; `AAdd a b` — **no** precondition (add `a + b` to `ps_plain`); `ADec c dk` — require `c ∈ ps_cipher` and `ps_priv = Some _` (no key-equality check because `priv_key` lacks `eqType`); `ASend dst c` — require `c ∈ ps_cipher(p)`; `ARet x` — require `ps_ret = None` only (**no** `x ∈ ps_plain` check). **Rationale**: plaintext values `u i`, `r j`, `ra j` are Section parameters in scope for the entire protocol, not derived knowledge. Requiring them to be injected into `ps_plain` would either force a parallel `AInject` action and bloat `dsdp_n_phase0`, or prevent phase2/phase4 from type-checking at all (the Phase 2a block). This relaxation is sound for **correctness** proofs (the scope of this plan) but weakens **security** claims (out of scope per D14). **Invariant (documented, not enforced)**: `sw_step` tracks **cipher provenance only**. Plaintext operands are assumed to be Section-scope parameters or closed-form derivations; correctness theorems must witness their definitional equality, not their membership in `ps_plain`. **Any future security/Dolev-Yao analysis must layer a separate `sw_knows_plain` predicate on top — do not re-strengthen `sw_step`.** |
| D14-note | Security layering (added after D21 audit) | Because D21 decouples `sw_step` from plaintext derivability, future security-layer work must reintroduce plaintext tracking as a **separate judgement** rather than strengthening `sw_step` in place. |
| **D22** | **`dsdp_n_phase2` send destination — fix (Phase 2c wall)** | Phase 1's skeleton wrote `R (alice_send_dest (val j))`, but `R k := nat_to_party_id k.+1` — this introduces an off-by-one: alpha₀/alpha₁ end up at party 2 instead of party 1. **Corrected**: use `nat_to_party_id (alice_send_dest (val j))` directly. This matches `dsdp_pismc.v:317` `Send<(alice_send_dest j)>`. |
| **D23** | **`dsdp_n_first_relay` action list — fix (Phase 2c wall)** | Phase 1 wrote `AMul (sw_alpha ord0) (sw_alpha j1); ADec (sw_alpha ord0 *h sw_alpha j1) (dk 0); ...`. This is **semantically wrong**: `sw_alpha 0` and `sw_alpha 1` are under *different* keys (`dk 0` and `dk 1`), so their `Emul` is not a fresh encryption and `dec_correct` does not apply. **Corrected** (mirrors `DParty_first` at `dsdp_pismc.v:221-229`): `ADec (sw_alpha ord0) (dk 0)` → `AEnc (sw_pk_of (lift ord0 (lift ord0 ord0))) (sw_Delta ord0) (rb2 ord0)` → `AMul (sw_alpha (lift ord0 ord0)) <the fresh enc>` → `ASend (nat_to_party_id 2) (sw_beta ord0 (lift ord0 ord0))`. The first Dec extracts `d_val = sw_Delta ord0`; the fresh Enc produces a ciphertext under `dk 1` (the next relay's key); AMul with `sw_alpha 1` (also under `dk 1`) produces `sw_beta ord0 (lift ord0 ord0)`. |
| **D24** | **`dsdp_n_intermediate` action list — fix (Phase 2c wall)** | Phase 1 wrote `AMul (sw_beta (ord_predS j) j) (sw_alpha j); ADec <product> (dk j); ...`. This **double-counts** the j-th term (sw_alpha j is already absorbed into sw_beta via `sw_alpha_eq_fresh_enc`). **Corrected** (mirrors `DParty_intermediate` at `dsdp_pismc.v:238-244`): `ADec (sw_beta (ord_predS j) j) (dk j)` → `AEnc (sw_pk_of (lift ord0 (lift ord0 j))) (sw_Delta j) (rb2 j)` → `AMul (sw_alpha (lift ord0 j)) <fresh enc>` → `ASend (nat_to_party_id (val j).+2) (sw_beta j (lift ord0 j))`. |
| **D25** | **Helper lemmas for `dec_correct` firing** | Add two lemmas before L5: `sw_alpha_eq_fresh_enc (j : 'I_n_relay.+1) : exists rr, sw_alpha j = enc (sw_pk_of (lift ord0 j)) (u (lift ord0 j) * v j + r j) rr` proved by `Emul_addM` + `Epow_scalarM` (see `homomorphic_encryption/ahe_enc.v:82-99` and the 3-party pattern at `dsdp_program.v:200-262`). And `sw_beta_eq_fresh_enc (j jnext : 'I_n_relay.+1) : val jnext = (val j).+1 → exists rr, sw_beta j jnext = enc (sw_pk_of (lift ord0 jnext)) (u (lift ord0 jnext) * v jnext + r jnext + sw_Delta j) rr` proved similarly. These two lemmas enable `dec_correct` to extract `sw_Delta j` inside L5 and L6. Budget ~30 LOC total. |

## The artefact (literal content to produce)

### Event / action types

```coq
Inductive dsdp_action :=
| AInit  (v : plain AHE) (dk : priv_key AHE)
| AEnc   (pk : pub_key AHE) (m : plain AHE) (r : rand AHE)
| ADec   (c : cipher AHE) (dk : priv_key AHE)
| AMul   (c1 c2 : cipher AHE)
| APow   (c : cipher AHE) (x : plain AHE)
| AAdd   (a b : plain AHE)
| ASend  (dst : party_id) (c : cipher AHE)
| ARet   (x : plain AHE).
```

### State and `sw_step`


```coq
Record sw_party_state := {
  ps_plain  : {fset plain AHE};
  ps_cipher : {fset cipher AHE};
  ps_priv   : {fset priv_key AHE};
  ps_ret    : option (plain AHE)
}.

Definition sw_global_state := party_id -> sw_party_state.
Definition sw_init_state : sw_global_state := fun _ => mk_ps fset0 fset0 fset0 None.

Definition sw_step (p : party_id) (a : dsdp_action) (g : sw_global_state) : option sw_global_state.
(* REVISED — cipher-tracking semantics (see D21):
   AInit v dk       → add v to ps_plain(p), dk to ps_priv(p)
   AEnc pk m r      → unconditional; add enc pk r m to ps_cipher(p)
   ADec c dk        → require c ∈ ps_cipher(p) and ps_priv(p) = Some _;
                      add dec dk c to ps_plain(p)
   AMul c1 c2       → require both in ps_cipher(p); add (c1 *h c2)
   APow c x         → require c ∈ ps_cipher(p); add (c ^h x)
   AAdd a b         → unconditional; add (a + b) to ps_plain(p)
   ASend dst c      → require c ∈ ps_cipher(p); add c to ps_cipher(dst)
   ARet x           → require ps_ret(p) = None; set ps_ret(p) := Some x *)
```

### Pre-computed closed-form names

```coq
Let sw_pk_of : 'I_n_relay.+2 -> pub_key AHE := ...   (* ord0 ↦ alice; lift ord0 j ↦ relay j *)

Definition sw_c   (j : 'I_n_relay.+1) : cipher AHE := enc (sw_pk_of (lift ord0 j)) (rb1 j) (v j).
Definition sw_alpha (j : 'I_n_relay.+1) : cipher AHE :=
  (sw_c j ^h u (lift ord0 j)) *h enc (sw_pk_of (lift ord0 j)) (ra j) (r j).
Definition sw_Delta (j : 'I_n_relay.+1) : plain AHE :=
  \sum_(k < j.+1) (u (lift ord0 (widen_ord (ltnW (ltn_ord j)) k))
                 * v (widen_ord (ltnW (ltn_ord j)) k)
                 + r (widen_ord (ltnW (ltn_ord j)) k)).
Definition sw_beta (j jnext : 'I_n_relay.+1) : cipher AHE :=
  sw_alpha jnext *h enc (sw_pk_of (lift ord0 jnext)) (rb2 j) (sw_Delta j).
Definition sw_gamma : cipher AHE := enc (sw_pk_of ord0) r_tail (sw_Delta ord_max).
Definition sw_S  : plain AHE   := sw_Delta ord_max - (\sum_(k < n_relay.+1) r k) + u ord0 * v_alice.
```

### Four phases and `dsdp_n_program`

```coq
Definition dsdp_n_phase0 : seq (party_id * dsdp_action) :=
  (alice, AInit v_alice dk_alice)
    :: [seq (R j, AInit (v j) (dk j)) | j : 'I_n_relay.+1].

Definition dsdp_n_phase1 : seq (party_id * dsdp_action) :=
  flatten [seq [:: (R j, AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j))
                 ; (R j, ASend alice (sw_c j))]
          | j : 'I_n_relay.+1].

Definition dsdp_n_phase2 : seq (party_id * dsdp_action) :=
  flatten [seq let dest := R (inord (maxn 1 j)) in
               [:: (alice, AEnc (sw_pk_of (lift ord0 j)) (r j) (ra j))
                 ; (alice, APow (sw_c j) (u (lift ord0 j)))
                 ; (alice, AMul (sw_c j ^h u (lift ord0 j))
                                (enc (sw_pk_of (lift ord0 j)) (ra j) (r j)))
                 ; (alice, ASend dest (sw_alpha j))]
          | j : 'I_n_relay.+1].

Definition dsdp_n_first_relay : seq (party_id * dsdp_action) := ...   (* 4 actions *)
Definition dsdp_n_intermediate (j : 'I_n_relay.+1) : seq (party_id * dsdp_action) := ... (* 4 actions *)
Definition dsdp_n_last_relay : seq (party_id * dsdp_action) := ...    (* 3 actions *)

Definition dsdp_n_phase3 : seq (party_id * dsdp_action) :=
  dsdp_n_first_relay
    ++ flatten [seq dsdp_n_intermediate j
               | j : 'I_n_relay.+1 & (0 < val j < n_relay)%N]
    ++ dsdp_n_last_relay.

Definition dsdp_n_phase4 : seq (party_id * dsdp_action) :=
  [:: (alice, ADec sw_gamma dk_alice)
    ; (alice, AAdd (sw_Delta ord_max) (u ord0 * v_alice))
    ; (alice, AAdd (sw_Delta ord_max + u ord0 * v_alice)
                   (- \sum_(k < n_relay.+1) r k))
    ; (alice, ARet sw_S)].

Definition dsdp_n_program : seq (party_id * dsdp_action) :=
  dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2 ++ dsdp_n_phase3 ++ dsdp_n_phase4.

Definition dsdp_n_final : option sw_global_state :=
  foldM (fun g '(p, a) => sw_step p a g) sw_init_state dsdp_n_program.
```

## Definitions and Lemmas — Final Result Table

| # | Name | Kind | Statement (informal) | Why we need it |
|---|---|---|---|---|
| T1 | `dsdp_action` | Inductive | 8 constructors as above | The finite instruction set; input DSL |
| T2 | `sw_party_state`, `sw_global_state`, `sw_init_state` | Record/Definition | 4 fields, three fsets + option ret | State type with knowledge as a field (replaces `dsdp_inv` phase Records) |
| T3 | `sw_step` | Definition | `party_id → dsdp_action → sw_global_state → option sw_global_state` | Operational semantics of the stepwise DSL |
| T4 | `sw_pk_of` | Let | `'I_n_relay.+2 → pub_key AHE`, total dispatch | Uniform key access for both alice and relays without `nat` fallback |
| T5 | `sw_c`, `sw_alpha`, `sw_Delta`, `sw_beta`, `sw_gamma`, `sw_S` | Definition | Closed-form values | Named handles for every wire value so phase definitions are readable and proofs can `rewrite` on them |
| T6 | `dsdp_n_phase0..dsdp_n_phase4` | Definition | Four `seq (party_id * dsdp_action)` blocks | The protocol, split by Algorithm-2 phase |
| T7 | `dsdp_n_program` | Definition | `dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2 ++ dsdp_n_phase3 ++ dsdp_n_phase4` | The entire DSDP_n protocol as one list |
| T8 | `dsdp_n_final` | Definition | `foldM sw_step sw_init_state dsdp_n_program` | The resulting global state |
| L1 | `sw_step_AInit_eq`, `sw_step_AEnc_eq`, ..., `sw_step_ARet_eq` | Lemma | For each action, a constructive update lemma giving the resulting state | Needed to avoid reasoning with `match` on option; 8 small lemmas, ~3 LOC each |
| L2 | `dsdp_n_phase0_state` | Lemma | After `dsdp_n_phase0`, every party holds its init plain and priv key | Seeds the induction |
| L3 | `dsdp_n_phase1_state` | Lemma | After `dsdp_n_phase0 ++ dsdp_n_phase1`, alice's `ps_cipher` contains `sw_c j` for every `j`; each relay holds its `sw_c j` locally | Establishes that alice has the inputs to `dsdp_n_phase2` |
| L4 | `dsdp_n_phase2_state` | Lemma | After `dsdp_n_phase0..dsdp_n_phase2`, (a) the first relay holds `sw_alpha ord0` and `sw_alpha (lift ord0 ord0)`; (b) each relay `j > 0` holds `sw_alpha (lift ord0 j)` | Establishes that every relay has its α before the β-chain starts |
| L5 | `dsdp_n_first_relay_eq` | Lemma | After `dsdp_n_first_relay`, party 1 (first relay) holds `sw_Delta ord0` in `ps_plain` and `sw_beta ord0 (lift ord0 ord0)` in `ps_cipher`; furthermore party 2 (next relay) now holds `sw_beta ord0 (lift ord0 ord0)` in `ps_cipher` | Base of the β-chain induction |
| L6 | `dsdp_n_intermediate_telescope` | Lemma | For any intermediate `j`, if before its 4 actions the relay holds `sw_beta (ord_predS j) j` and `sw_alpha (lift ord0 j)`, then after it holds `sw_Delta j`, emits `sw_beta j (lift ord0 j)`, and the next relay receives it | Inductive step of the β-chain; this is the *telescoping sum* lemma |
| L7 | `dsdp_n_beta_chain_eq` | Lemma | After `dsdp_n_phase3`, the last relay holds `sw_Delta ord_max` in `ps_plain` and alice holds `sw_gamma` in `ps_cipher` | Combines L5, L6 via induction on `n_relay` |
| L8 | `dsdp_n_phase4_state` | Lemma | After `dsdp_n_phase4`, `ps_ret (dsdp_n_final alice) = Some sw_S` | Discharges the return formula from `sw_gamma` via dec + two adds |
| L9 | `sw_S_eq_dot_product` | Lemma | `sw_S = \sum_(i < n_relay.+2) u i * v_all i` | Algebraic identity — telescoping `sw_Delta ord_max` against `\sum r` |
| **TH1** | **`dsdp_n_correct`** | **Theorem** | **`ret_of dsdp_n_final alice = Some (dot_product u v_all)`** | **Headline correctness; composes L8 + L9** |
| L10 | `sw_step_rstep_eq_*` | Lemma (×8) | One per action constructor: `sw_step p a g` corresponds to a specific `rstep` on `dsdp_n_procs` given the matching `proc` shape | Atomic bricks for the bridge theorem |
| L11 | `palice_n_phases_eq` | Lemma | `palice_n`'s unfolding via `palice_n_erase` produces exactly `dsdp_n_phase0_alice ++ dsdp_n_phase1_alice_recvs ++ dsdp_n_phase2 ++ dsdp_n_phase4` (alice's projection) | Bridges alice's imperative code to her stepwise slice |
| L12 | `DParty_first_phases_eq` | Lemma | `DParty_first`'s unfolding via `DParty_first_erase` produces exactly `(R ord0, ...)`-projection of `dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_first_relay` | Bridges first relay |
| L13 | `DParty_intermediate_phases_eq` | Lemma | `DParty_intermediate`'s unfolding produces the intermediate's projection | Bridges intermediates |
| L14 | `DParty_last_phases_eq` | Lemma | `DParty_last`'s unfolding produces the last relay's projection | Bridges last relay |
| L15 | `chain_schedule_wf` | Lemma | The chain schedule `sched` is well-formed (every send has a matching recv, no stalls) | Precondition for `rsteps` |
| L16 | `sw_trace_of` / `sw_trace_of_flatten` | Definition + Lemma | `sw_trace_of : {d : _ & rsteps ps ps' d} → seq (party_id * dsdp_action)` walks an `rsteps` derivation and emits one stepwise action per firing; `sw_trace_of_flatten` is its fold-fusion lemma | **New helper** needed because `rsteps_observation` does not exist in `smc_interpreter.v`. Budget ~60 LOC |
| L17 | `ord_predS_lift` | Lemma | `forall j : 'I_n, val (ord_predS (lift ord0 j)) = val j` | Glue lemma for D17; needed inside L6 |
| **TH2** | **`dsdp_n_program_sound`** | **Theorem** | **`exists d, rsteps (dsdp_n_procs …) final_procs d ∧ sw_trace_of (existT _ d _) = dsdp_n_program`** (after `chain_schedule_wf`) | **Bridge: the stepwise list is exactly what the imperative interpreter emits under the chain schedule; composes L10–L16** |

Total artefact budget: **~530 LOC** (90 LOC definitions + ~80 LOC TH1 proof + **~400 LOC TH2 proof including L16 flattener and L15 schedule-wf** + ~25 LOC ordinal glue).

## Action Items

| # | Action Item | Why | Phase |
|---|---|---|---|
| A1 | Create `dumas2017dual/dsdp/dsdp_stepwise.v` with Section header, imports (`smc_interpreter`, `dsdp_pismc`, `finmap`, `bigop`), and Section variables matching `dsdp_pismc.v:292-312` exactly (D7, D8) | File skeleton; reusing the parameter block lets TH2 instantiate without re-declaration | 1 — Skeleton |
| A2 | Define `dsdp_action` inductive (T1), `sw_party_state` record, `sw_global_state`, `sw_init_state`, `foldM` (D18), and `sw_step` (T2, T3) | The DSL and its semantics; no other proof can begin until these type-check. **`foldM` must be defined locally — not in infotheo.** | 1 — Skeleton |
| A2b | Define `ord_predS` (D17) and prove `ord_predS_lift` (L17) — 8 + 4 LOC | `ord_predS` is **not** a mathcomp name; must be defined locally before any `sw_beta` / intermediate step can type-check | 1 — Skeleton |
| A3 | Define `sw_pk_of` (T4) and the six closed-form values `sw_c`, `sw_alpha`, `sw_Delta`, `sw_beta`, `sw_gamma`, `sw_S` (T5), using `widen_ord (ltnW (ltn_ord j)) k` inside the `\sum` for `sw_Delta` (cite `widen_ord_inj` + `big_ord_widen` for later telescoping; ~25 LOC of ordinal glue, not 15) | These are the names every later definition and lemma references | 1 — Skeleton |
| A4 | Define `dsdp_n_phase0..dsdp_n_phase4` and `dsdp_n_program`, `dsdp_n_final` (T6, T7, T8). Include the intermediate filter `[seq j \| 0 < val j < n_relay]` (D10) | The actual protocol object | 1 — Skeleton |
| A5 | Prove the 8 `sw_step_A*_eq` lemmas (L1). Each is ~3 LOC by `case`/`rewrite /sw_step/=`. Parallelisable | Removes option-matching noise from downstream proofs | 2 — Evaluation Lemmas |
| A6 | Prove `dsdp_n_phase0_state` (L2), `dsdp_n_phase1_state` (L3), `dsdp_n_phase2_state` (L4). Each by unfolding `flatten` + `foldM` on the comprehension and applying L1 | Establish pre-β-chain state invariants | 3 — Phase Results |
| A7 | Prove `dsdp_n_first_relay_eq` (L5) — 4-step straight-line reasoning on the first-relay block | Base of the β-chain induction | 3 — Phase Results |
| A8 | Prove `dsdp_n_intermediate_telescope` (L6) — the *telescoping sum* lemma; unfolds `sw_Delta` at successor, uses `big_ord_recr` from mathcomp | Inductive step of β-chain; the only lemma with non-trivial algebraic content | 4 — β-chain Induction |
| A9 | Prove `dsdp_n_beta_chain_eq` (L7) by induction on `n_relay` using L5 base and L6 step, with the `n_relay = 1` base (empty intermediate filter) handled separately | Collapses β-chain into a single postcondition | 4 — β-chain Induction |
| A10 | Prove `dsdp_n_phase4_state` (L8) — 4-action straight-line evaluation after L7 | Gets the return value to `Some sw_S` | 5 — Alice Return |
| A11 | Prove `sw_S_eq_dot_product` (L9) by pure ring algebra on `sw_Delta ord_max - \sum r + u ord0 * v_alice`. Uses `big_ord_recl`, `big_split`, `opprD` | The telescoping identity that makes DSDP correct | 5 — Alice Return |
| A12 | Prove `dsdp_n_correct` (TH1) as a one-line corollary of L8 + L9 | Headline theorem of file 1 | 5 — Alice Return |
| A13 | Create `dumas2017dual/dsdp/dsdp_stepwise_bridge.v`. Import `dsdp_stepwise` and `dsdp_pismc`. Match parameter Section. Define `chain_schedule : seq lens` concretely (D20) — ~25 LOC. | Bridge file skeleton. `chain_schedule` must be defined explicitly; it was an unmade decision in v1 of the plan. | 6 — Bridge Skeleton |
| A13b | Define `sw_trace_of` helper (L16): walks an `rsteps` derivation and emits one stepwise action per firing, inverting the `*_erase` lemmas. Budget ~60 LOC | **New helper required** because `rsteps_observation` does not exist in `smc_interpreter.v`. TH2 cannot even be stated without this. | 6 — Bridge Skeleton |
| A14 | Prove the 8 `sw_step_rstep_eq_*` lemmas (L10). Each directly compares one `sw_step` case to one `rstep` firing | Atomic per-action correspondence | 6 — Bridge Skeleton |
| A15 | Prove `palice_n_phases_eq` (L11) using `palice_n_erase` from `dsdp_pismc.v:853`. `ForList` expands via `erase_sproc_iter` (already inside `palice_n_erase`'s proof — piggyback on it). Cross-check `dsdp_chlipala.v` / `dsdp_entropy_trace.v` for existing `ForList` helpers before rolling new ones. Budget ~20 LOC | Imperative ↔ stepwise correspondence for alice | 7 — Template Matching |
| A16 | Prove `DParty_first_phases_eq` (L12), `DParty_intermediate_phases_eq` (L13), `DParty_last_phases_eq` (L14) using the three `*_erase` lemmas at `dsdp_pismc.v:886`, `:911`, `:930` | Imperative ↔ stepwise correspondence for each relay kind | 7 — Template Matching |
| A17 | Prove `chain_schedule_wf` (L15) by induction on the constructed `chain_schedule` list — every send lens has a matching recv lens in the templates at the given point. **This is non-trivial** because `rstep`'s `lens`-based interleaving is not aligned by the `*_erase` lemmas alone. Budget ~80 LOC. | Precondition for applying `rsteps` cleanly. **This was the hidden cost in v1's 200 LOC estimate.** | 7 — Template Matching |
| A18 | Prove `dsdp_n_program_sound` (TH2) by composing L10–L16 and inducting on `chain_schedule`. The existential witness is built alongside the `sw_trace_of` fold. Budget ~80 LOC on top of L15. | Headline theorem of bridge file | 8 — Bridge Theorem |
| A19 | `make -j1 dumas2017dual/dsdp/dsdp_stepwise.vo` and `make -j1 dumas2017dual/dsdp/dsdp_stepwise_bridge.vo` cleanly, with no `Admitted` | Validates the entire plan compiles against the current master | 9 — Verification |
| A20 | `Compute dsdp_n_final` at concrete `n_relay := 1` and `n_relay := 3` in a scratch `Eval` block (not checked in); verify the resulting `sw_global_state` has `ps_ret alice = Some expected_dot_product` | Sanity check that `sw_step` actually reduces at fixed N — catches any `ps_*` opacity traps | 9 — Verification |

## Audit Findings Incorporated

A Rocq-expert audit of v1 of this plan surfaced **five blockers and one tightening**, all now folded into the tables above:

1. **`ord_predS` does not exist in mathcomp** → D17 + A2b (locally defined, 8 LOC + 4 LOC accessor).
2. **`foldM` does not exist in infotheo** → D18 + A2 (locally defined, 4 LOC).
3. **`rsteps_observation` does not exist in `smc_interpreter.v`** (the original TH2 statement was literally untypeable) → D19 + L16 + A13b: commit to `rsteps` relational semantics and write a `sw_trace_of` flattener (~60 LOC).
4. **`chain_schedule` was undefined** → D20 + A13: explicit `seq lens` construction, ~25 LOC.
5. **TH2 budget was understated** (v1 said 200 LOC; realistic is ~400 LOC because `chain_schedule_wf` hides a real scheduling-order argument that the `*_erase` lemmas do not discharge) → L15 raised to 80 LOC, TH2 raised to 80 LOC on top, total artefact budget raised from ~350 to ~530 LOC.
6. **`ForList` reuse opportunity** → A15 cites `dsdp_chlipala.v` and `dsdp_entropy_trace.v` as potential sources before rolling new helpers.

The audit also **confirmed**:
- `dsdp_security.v` imports only `dsdp_program` and `dsdp_entropy` (not `dsdp_fsm`/`dsdp_progress`), so D14 (out-of-scope retirement) carries no breakage risk.
- The `option`-based `sw_step` signature (D3) is correct — a `Prop` relation would simplify correctness but complicate the bridge, which is the opposite of the right tradeoff since correctness is ~80 LOC and the bridge is the dominant cost.
- The `*_erase` lemmas at `dsdp_pismc.v:853-941` are the right primary engine for L11–L14.

## Critical Files (read-only references)

- `smc/smc_interpreter.v` — `proc`, `sw_step`, `rsteps`, `rsteps_observation`
- `dumas2017dual/dsdp/dsdp_pismc.v:221-355` — the four templates and `palice_n`
- `dumas2017dual/dsdp/dsdp_pismc.v:853-941` — the four `*_erase` lemmas used by the bridge
- `dumas2017dual/dsdp/dsdp_fsm.v` — reference for the current approach; **not modified**
- `dumas2017dual/dsdp/dsdp_fsm_progress.v` — reference for the target statements (`fsm_full_trace`, `fsm_return_value`); **not modified**
- `dumas2017dual/dsdp/dsdp_progress.v:1479` — reference for `dsdp_inv`; **not modified**

## Verification Plan

1. **After phase 1** (A1–A4): `make -j1 dumas2017dual/dsdp/dsdp_stepwise.vo` must succeed with only the definitions in place (no lemmas yet; use `Admitted` stubs if needed to check type-checking of the phase list).
2. **After phase 5** (A5–A12): file 1 compiles cleanly, zero `Admitted`. `Check dsdp_n_correct.` prints the expected type.
3. **After phase 8** (A13–A18): file 2 compiles cleanly, zero `Admitted`. `Check dsdp_n_program_sound.` prints the expected type.
4. **Operational sanity** (A20): at `n_relay := 1` (3-party, first + last, no intermediates), `Eval vm_compute in ps_ret (dsdp_n_final P0)` produces `Some` of the expected dot product. Repeat at `n_relay := 3`.
5. **No regression**: `make -j1` of the rest of the `dumas2017dual/dsdp/` directory still succeeds (the two new files do not `Import` or shadow existing definitions).
6. **Compilation safety**: every `make` invocation is preceded by `ps aux | grep rocqworker | grep -v grep` and `ps aux | grep pet | grep -v grep` per `CLAUDE.md`. All builds use `make -j1`, never `-j4`.

## Naming Audit (Post-Review)

Audited against `smc/smc_interpreter.v`, `dumas2017dual/dsdp/dsdp_pismc.v`, `dumas2017dual/dsdp/dsdp_progress.v`, `dumas2017dual/dsdp/dsdp_fsm.v`, and mathcomp conventions.

### Type / term renames

| Original | Verdict | Recommended | Justification |
|---|---|---|---|
| "action" (bare) | ambiguous | `dsdp_action` | `action` is a very generic identifier, trivially collision-prone; infotheo DSDP convention is the `dsdp_` prefix (`dsdp_n_procs`, `dsdp_inv`, `dsdp_dtype`). |
| party-state (bare, original) | style-drift | `sw_party_state` | New public name in a DSDP file; infotheo uses `ps_*` field prefixes and scope-prefixes for bundles (`phase_state`, `recv_phase`). `sw_` (stepwise) disambiguates from `dsdp_fsm.v`'s own phase_state. |
| global-state (bare, original) | style-drift | `sw_global_state` | Same reason; too generic for a file-local bundle. |
| "sw_init_state" (bare) | style-drift | `sw_init_state` | Overly generic and imprecise (it is not empty — all parties exist). Mathcomp style prefers `init` / `initial` for starting configurations. |
| "party" as type (bare) | collision | `party_id` | infotheo's existing type is `party_id` (see `dsdp_pismc.v:42-44`, `Variable alice : party_id`). The plan's use of bare `party` would shadow/diverge. |
| "step" (bare) | **COLLISION** | `sw_step` | `smc_interpreter.v:54` already defines `Definition step`. Using the same name in a new file that imports `smc_interpreter` is a hard conflict. `sw_` (stepwise) prefix is local-scoped. |
| pk-of (bare, original) | style-drift | `sw_pk_of` | short and potentially colliding; infotheo prefers prefixed helpers (`alice_send_dest`, `enc_pub_key`). |
| "c_", "sw_alpha", "sw_Delta", "sw_beta", "sw_gamma", "S_" (bare, trailing-underscore) | style-drift | `sw_c`, `sw_alpha`, `sw_Delta`, `sw_beta`, `sw_gamma`, `sw_S` | Trailing-underscore bare-greek identifiers are unusual in infotheo/mathcomp; existing style uses descriptive prefixes (`chain_acc`, `alice_enc`, `r_tail`). `sw_` prefix + greek name is readable and uncolliding. |
| "phase0..phase4" (bare) | style-drift | `dsdp_n_phase0 .. dsdp_n_phase4` | Extremely generic; `dsdp_fsm.v` already has a `phase_state` concept so the bare word is loaded. Prefix with `dsdp_n_` to match `dsdp_n_program`, `dsdp_n_final`, `dsdp_n_procs`. |
| "dsdp_n_first_relay", "dsdp_n_intermediate", "dsdp_n_last_relay" (bare) | style-drift | `dsdp_n_first_relay`, `dsdp_n_intermediate`, `dsdp_n_last_relay` | consistency with `dsdp_n_` prefix family; `_steps` is redundant since type already says `seq (party_id * dsdp_action)`. |
| `dsdp_n_program` | OK | `dsdp_n_program` | consistent with `dsdp_n_procs`/`dsdp_n_saprocs`. |
| `dsdp_n_final` | OK | `dsdp_n_final` | descriptive and well-scoped. |
| ord-pred (bare, original) | style-drift | `ord_predS` | mathcomp has no `ord_pred`; the closest pattern is `ord_succ` / `bump`. Since this function's input is essentially `j.+1`-shaped and it predecessors a lifted ordinal, the suffix `S` (for "of a successor") follows mathcomp style (cf. `lift0`, `lift_max`, `bump`). Accessor lemma: `ord_predS_lift`. |
| `foldM` | OK | `foldM` | no collision in infotheo; the name mirrors Haskell/common functional convention; kept as-is. |
| trace-of (bare, original) | style-drift | `sw_trace_of` | `trace` is an overloaded term (Mazurkiewicz traces, execution traces). Prefix disambiguates. |
| `chain_schedule` | OK | `chain_schedule` | no collision; descriptive. |

### Lemma / theorem renames

| Original | Verdict | Recommended | Justification |
|---|---|---|---|
| step_A\*_ok (×8, original) | style-drift | `sw_step_AInit_eq`, ..., `sw_step_ARet_eq` | `step` → `sw_step`; `_ok` is non-standard in infotheo (rare), whereas `_eq` is the dominant suffix for equational lemmas (e.g. `chain_acc_eq`, `relay_body_eq`, `enc_curry_eq`, `alice_cross_eq`). |
| phaseK_result for K=0..4 (original) | style-drift | `dsdp_n_phase0_state` .. `dsdp_n_phase4_state` | `_result` is informal and not used in infotheo; these lemmas describe the resulting global-state after a phase, so `_state` is more precise. Prefix matches renamed definitions. |
| `first_relay_step_sound` (original) | style-drift | `dsdp_n_first_relay_eq` | `_sound` is rare here; the lemma is an equational/state postcondition, matching the `_eq` family. |
| `intermediate_step_telescope` (original) | OK (suffix clarified) | `dsdp_n_intermediate_telescope` | `_telescope` is appropriate and informative — kept. Prefix added for consistency. |
| original-beta-chain-result | style-drift | `dsdp_n_beta_chain_eq` | ditto `_result` → `_eq`. |
| original-S-eq-dot-product | OK | `sw_S_eq_dot_product` | `_eq_` is the right form; only the leading `sw_S` needs prefixing per the type rename. |
| `dsdp_n_correct` | OK | `dsdp_n_correct` | `_correct` is attested in infotheo (`dec_correct`, `interp_correct`); kept. |
| `step_matches_rstep_*` (×8, original) | style-drift | `sw_step_rstep_eq_*` | `_matches` is non-standard; `_eq` matches infotheo convention. `sw_step`/`rstep` juxtaposition conveys the correspondence. |
| `palice_n_phases_match` (original) | style-drift | `palice_n_phases_eq` | `_match` → `_eq`; lemma is an equality between an imperative-erased trace and a stepwise projection. |
| `DParty_first_matches` (original) | style-drift | `DParty_first_phases_eq` | same as above; name keeps the `DParty_first` reference and uses the `_eq` suffix. |
| `DParty_intermediate_matches` (original) | style-drift | `DParty_intermediate_phases_eq` | same reason. |
| `DParty_last_matches` (original) | style-drift | `DParty_last_phases_eq` | same reason. |
| `chain_schedule_wf` | OK | `chain_schedule_wf` | `_wf` is attested throughout infotheo (`proc_wf`, `all_proc_wf`, `dsdp_reachable_proc_wf`); kept. |
| `dsdp_n_program_sound` | OK | `dsdp_n_program_sound` | `_sound` is acceptable for this class of "stepwise reflects imperative" theorems; kept. |
| trace-of-flatten (original `trace_of_flatten`) | style-drift | `sw_trace_of_flatten` | follows `trace_of` → `sw_trace_of` rename. |
| ord-pred-lift (original `ord_pred_lift`) | style-drift | `ord_predS_lift` | follows `ord_pred` → `ord_predS` rename. |

### Summary of preserved names

`foldM`, `dsdp_n_program`, `dsdp_n_final`, `chain_schedule`, `chain_schedule_wf`, `dsdp_n_correct`, `dsdp_n_program_sound`, `dsdp_n_intermediate_telescope`'s `_telescope` suffix.

### Summary of renames

The dominant pattern is: (i) add `sw_` prefix for small file-local helpers whose names would otherwise collide or read as generic (`sw_step`, `sw_pk_of`, `sw_c`/`sw_alpha`/..., `sw_trace_of`, `sw_party_state`, `sw_global_state`, `sw_init_state`); (ii) add `dsdp_n_` prefix for phase-level objects (`phase0..4`, `dsdp_n_first_relay`, etc.) to match the existing `dsdp_n_procs` / `dsdp_n_saprocs` family; (iii) `party` → `party_id` to match infotheo's existing type; (iv) `_ok` / `_matches` / `_result` → `_eq` to match infotheo convention (`_eq` is attested ~30× in the DSDP directory); (v) `ord_pred` → `ord_predS` to echo mathcomp's suffix conventions; (vi) `action` → `dsdp_action` to avoid an extremely generic identifier.
