# `obs_of_procs` Implementation Plan

> **For agentic workers:** the `.v` work is delegated to the `rocq-prover` agent,
> one atomic task at a time, each verified (`rocq_check`/`rocq_compile` or `make`)
> and committed before the next starts. Steps use `- [ ]` checkboxes.

**Goal:** Replace the hand-written `dsdp_alice_obs` with a derivation: a generic
`obs_of_procs` walks the corrupted party's symbolic program and emits the whole
corrupted-Alice trace, with every derivation parameter centralized in one record
`dsdp_indcpa_secrecy_problem`.

**Architecture:** Front end only. A dual-purpose walk reads the hops (party + secret)
off the senders' first sends and the combines off the corrupted party's sends, threading
opaque result names; a free-variable pass synthesizes the sample prefix in first-appearance
order; the trace lowers through the reused `game_of_trace` to a `game_code` that equals a
minimally-rebuilt `gc_dsdp` (two de Bruijn indices). The back end (`denote_game`,
`advantage_le`) is reused unchanged.

**Tech stack:** Rocq + MathComp + SSProve. Design: `dumas2017dual/notes/20260608-obs-of-procs-facade-design.md`.

**Invariant held at every commit:** the full suite builds (`make`). Additive tasks (A, B)
add new definitions and check-lemmas without replacing anything; the switchover (task D)
edits `gc_dsdp` and redefines `dsdp_alice_obs` together so the green build is preserved.

---

## File structure

- `dumas2017dual/dsdp/dsdp_symbolic.v` — add the senders' symbolic runs and the structured
  hop-reception stream (task A).
- `dumas2017dual/dsdp/dsdp_game_symbolic.v` — add the walk, the sample synthesis, the two
  records, the projections, `obs_of_procs`, `dsdp_problem`; redefine `dsdp_alice_obs`;
  re-prove the faithfulness and bound results (tasks B, D, E).
- `dumas2017dual/dsdp/dsdp_game_code.v` — rebuild `gc_dsdp` (two indices) (task C, landed in
  the same commit as task D).

Compilation order (`_CoqProject`): `dsdp_game_code.v` (137) before `dsdp_symbolic.v` (138)
before `dsdp_game_symbolic.v` (139). So the `gc_dsdp` edit (C) is upstream and must land
atomically with the `dsdp_alice_obs` redefinition (D).

---

## Design refinement carried into the code

`obs_of_procs` takes the *loose symbolic arguments*, and the record projection
`corrupted_view P` applies it to `P`'s symbolic fields. This keeps `dsdp_alice_obs`
scheme-agnostic while `dsdp_problem` still bundles everything:

```coq
obs_of_procs (corrupt : proc symbolic_data) (hop_sends : seq symbolic_data)
  (challenge : nat) (leak : seq nat -> seq nat -> seq nat)
  (card_msg card_renc : nat) : seq alice_obs
corrupted_view (P) := obs_of_procs (sp_corrupted_party_program P)
  (sp_received_hop_ciphertexts P) (sp_challenge_secret P) (sp_leak_order P)
  (sp_card_plaintext P) (sp_card_randomness P)
```

So `corrupted_view (dsdp_problem cm cr scheme…)` reduces to `dsdp_alice_obs cm cr`.

---

## Task A — senders' symbolic runs and the structured hop stream

**Files:** Modify `dumas2017dual/dsdp/dsdp_symbolic.v` (after `palice_sym`).

- [ ] **A1. Add `pbob_sym`, `pcharlie_sym`** mirroring `palice_sym:133`. Bob's secret is
  `HE_var 10` (= v2), Charlie's is `HE_var 11` (= v3); the randomness slots are unused
  names (they sit inside the hop ciphertext, never read by the hop):

```coq
Definition pbob_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pbob Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 10) 22 23).
Definition pcharlie_sym : proc symbolic_data :=
  smc_session_types.erase
    (@pcharlie Symbolic_DSDP_Interface decode_sym ek_sym 0 (HE_var 11) 24 25).
```

- [ ] **A2. Add `first_send`** (head `Send` payload, walking past `Init`):

```coq
Fixpoint first_send (p : proc symbolic_data) : option symbolic_data :=
  match p with
  | smc_interpreter.Init _ k => first_send k
  | smc_interpreter.Send _ d _ => Some d
  | _ => None
  end.
```

- [ ] **A3. Add `dsdp_received_hop_ciphertexts`** and a check lemma fixing its value:

```coq
Definition dsdp_received_hop_ciphertexts : seq symbolic_data :=
  pmap first_send [:: pbob_sym ; pcharlie_sym].

Lemma dsdp_received_hop_ciphertexts_eq :
  dsdp_received_hop_ciphertexts
  = [:: SD_cipher (HE_enc 1 (HE_var 10) 22)
      ; SD_cipher (HE_enc 2 (HE_var 11) 24) ].
Proof. by []. Qed.
```

- [ ] **A4. Verify** `rocq_compile` of `dsdp_symbolic.v`. The check lemma closing `by []`
  confirms `pbob_sym`/`pcharlie_sym` erase to the expected shape and `first_send` reads the
  right payload. If `by []` does not close, fall back to `by vm_compute` and record which.
- [ ] **A5. Commit** (`dsdp: senders' symbolic runs + structured hop stream`).

---

## Task B — the walk, the sample synthesis, and `obs_of_procs`

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_symbolic.v` (after `game_of_trace`).
All definitions ADDED; `dsdp_alice_obs` is NOT touched yet, so the build stays green.

- [ ] **B1. Add `walk_obs`** — the dual-purpose drive. One name counter allocates fresh
  result names for both hops and combines (distinctness is all `game_of_trace` needs; it
  resolves by position):

```coq
Fixpoint walk_obs (p : proc symbolic_data) (resp : seq symbolic_data) (next : nat)
  : seq alice_obs :=
  match p with
  | smc_interpreter.Init _ k => walk_obs k resp next
  | smc_interpreter.Recv _ f =>
      match resp with
      | [::] => [::]                       (* halt at the decrypt-receive *)
      | r :: rs =>
          match symbolic_get_cipher r with
          | Some (HE_enc party (HE_var secret) _) =>
              AO_recv_hop party secret next
                :: walk_obs (f (SD_cipher (HE_var next))) rs next.+1
          | _ => [::]
          end
      end
  | smc_interpreter.Send _ d k =>
      match symbolic_get_cipher d with
      | Some c => AO_combine next c :: walk_obs k resp next.+1
      | None => walk_obs k resp next
      end
  | smc_interpreter.Ret _ => [::]
  | smc_interpreter.Finish => [::]
  | smc_interpreter.Fail => [::]
  end.
```

- [ ] **B2. Check `walk_obs`** on the DSDP corrupted run (result names start at 100):

```coq
Lemma walk_obs_dsdp :
  walk_obs palice_sym dsdp_received_hop_ciphertexts 100
  = [:: AO_recv_hop 1 10 100 ; AO_recv_hop 2 11 101
      ; AO_combine 102 (HE_emul (HE_epow (HE_var 100) (HE_var 12))
                                (HE_enc 1 (HE_var 14) 20))
      ; AO_combine 103 (HE_emul (HE_epow (HE_var 101) (HE_var 13))
                                (HE_enc 2 (HE_var 15) 21)) ].
Proof. by []. Qed.
```

  This is the load-bearing reduction (risk R1). If `by []` is too slow, use
  `by vm_compute`; record the tactic actually used.

- [ ] **B3. Add the free-variable / sample synthesis** `collect_samples`. It walks the
  hop-and-combine list, tracking result names as bound, and emits the free value names
  (`AO_sample_val card_msg`) in first appearance, then the free randomness slots
  (`AO_sample_rnd card_renc`). Spec of the helper (the `rocq-prover` agent picks the exact
  `he_term` recursion; the contract is the check in B5):
  - `bound` = the result names of every `AO_recv_hop`/`AO_combine`.
  - value names = first-appearance `HE_var` names from each hop secret and each combine
    term, minus `bound`, deduped.
  - randomness slots = first-appearance `HE_enc _ _ r` slots from each combine term,
    minus `bound`, deduped.

- [ ] **B4. Add `obs_of_procs`** assembling the trace:

```coq
Definition obs_of_procs (corrupt : proc symbolic_data)
    (hop_sends : seq symbolic_data) (challenge : nat)
    (leak : seq nat -> seq nat -> seq nat) (card_msg card_renc : nat)
  : seq alice_obs :=
  let w := walk_obs corrupt hop_sends 100 in
  collect_samples card_msg card_renc w
    ++ [:: AO_put challenge]
    ++ w
    ++ [:: AO_leak (leak (combine_names w) (recv_names w)) ]
```

  where `combine_names`/`recv_names` extract the `AO_combine`/`AO_recv_hop` result names
  from `w` (small helpers, added here).

- [ ] **B5. Check `obs_of_procs`** reproduces the intended derived trace for DSDP:

```coq
Lemma obs_of_procs_dsdp (cm cr : nat) :
  obs_of_procs palice_sym dsdp_received_hop_ciphertexts 10
    (fun combines recvs => combines ++ recvs) cm cr
  = [:: AO_sample_val cm 10 ; AO_sample_val cm 11 ; AO_sample_val cm 12 ;
        AO_sample_val cm 14 ; AO_sample_val cm 13 ; AO_sample_val cm 15 ;
        AO_sample_rnd cr 20 ; AO_sample_rnd cr 21 ;
        AO_put 10 ;
        AO_recv_hop 1 10 100 ; AO_recv_hop 2 11 101 ;
        AO_combine 102 (HE_emul (HE_epow (HE_var 100) (HE_var 12))
                                (HE_enc 1 (HE_var 14) 20)) ;
        AO_combine 103 (HE_emul (HE_epow (HE_var 101) (HE_var 13))
                                (HE_enc 2 (HE_var 15) 21)) ;
        AO_leak [:: 102 ; 103 ; 100 ; 101 ] ].
Proof. by []. Qed.
```

  Note the value-sample order `10,11,12,14,13,15` (= v2,v3,u2,r2,u3,r3, first appearance).

- [ ] **B6. Verify** `rocq_compile` of `dsdp_game_symbolic.v`. **Commit**
  (`dsdp: dual-purpose corrupted-view walk + sample synthesis`).

---

## Task C+D — the records, `gc_dsdp` rebuild, and the switchover (one commit)

This is the atomic switchover: `gc_dsdp` is reordered AND `dsdp_alice_obs` is redefined in
the same commit, so the build never breaks.

**Files:** Modify `dsdp_game_code.v` (rebuild) and `dsdp_game_symbolic.v` (records +
redefinition + faithfulness).

- [ ] **C1. Rebuild `gc_dsdp`** (`dsdp_game_code.v:923`): two de Bruijn indices, prefix
  comment. The `GC_sample` prefix text is unchanged (all six value samples have the same
  cardinality); only the two combines shift:
  - `a1` (line 936): `HE_enc 1 (HE_var 3) 1` → `HE_enc 1 (HE_var 4) 1`.
  - `a2` (line 938): `HE_epow (HE_var 1) (HE_var 5)` → `HE_epow (HE_var 1) (HE_var 4)`.
  - comment `iV2 iV3 iU2 iU3 iR2 iR3` → `iV2 iV3 iU2 iR2 iU3 iR3`.
- [ ] **C2. Verify** `rocq_compile dsdp_game_code.v`; confirm `hop_sites_gc_dsdp` and
  `advantage_gc_dsdp` still close (they are order-agnostic).

- [ ] **D1. Add the two records** `dsdp_indcpa_secrecy_problem` and
  `dsdp_indcpa_adversary` (`dsdp_game_symbolic.v`), with the audited field names from the
  design doc §4–§5.
- [ ] **D2. Add the projections** `corrupted_view`, `game_of_problem`, `real_game`,
  `zero_game`, and the thin oracle/interface projections. **Two compile-verified
  conventions (audit blockers):**
  - **Access every record field via `P.(field)`, never `field P`.** Under
    `Set Primitive Projections` (active at `dsdp_game_symbolic.v:57`) the record argument is
    implicit for function-valued fields whose domain mentions the record
    (`sp_rand_of_carrier`, `sp_choice_msg_of_plain`, `sp_plain_of_choice_msg`,
    `sp_choice_cipher_of_cipher`, `sp_msg_of_index`, the two cancel fields), so `field P`
    fails to elaborate. `P.(field)` works uniformly for all fields.
  - **Name the thin projections `game_iface_P`, `protocol_state_P`, `real_oracle_P`,
    `zero_oracle_P`** (the `_P` suffix), not bare `game_iface`/`protocol_state` which clash
    with the imported back-end globals.
  - **Wire the real/zero oracles asymmetrically:** `oracle_real_pkg` arg 3 is
    `P.(sp_plain_of_choice_msg)` (the `t_msg -> plain` decoder), but `oracle_zero_pkg` arg 3
    is `P.(sp_choice_msg_type)` (the choice_type itself), per `dsdp_advantage_derived:277,280`.
    `denote_game`'s `AHE Renc card_renc t_msg t_cipher card_msg` leading args are all
    IMPLICIT; first explicit is `P.(sp_rand_carrier_card)`.
- [ ] **D3. Add `dsdp_problem`** (record literal; symbolic fields `palice_sym`,
  `dsdp_received_hop_ciphertexts`, challenge `10`, leak `fun c r => c ++ r`; scheme block
  as section parameters).
- [ ] **D4. Redefine `dsdp_alice_obs`** as the derived trace:

```coq
Definition dsdp_alice_obs (card_msg card_renc : nat) : seq alice_obs :=
  obs_of_procs palice_sym dsdp_received_hop_ciphertexts 10
    (fun combines recvs => combines ++ recvs) card_msg card_renc.
```

- [ ] **D5. Re-prove faithfulness** against the rebuilt fixture:

```coq
Lemma dsdp_faithful (card_msg card_renc : nat) :
  game_of_trace (dsdp_alice_obs card_msg card_renc) = gc_dsdp card_renc card_msg.
Proof. by []. Qed.

Lemma dsdp_obs_hops (card_msg card_renc : nat) :
  count_obs_hops (dsdp_alice_obs card_msg card_renc) = 2.
Proof. by []. Qed.
```

  If `dsdp_faithful` does not close `by []`, the two rebuilt indices are wrong — re-derive
  from the stack trace in design §7 (do not weaken the lemma).

- [ ] **D6. (removed — the earlier whole-trace regression is provably false).** Asserting
  `game_of_trace (dsdp_alice_obs cm cr) = game_of_trace <old literal>` cannot close: the
  rebuild deliberately changes the value-sample order (`10,11,12,14,13,15` vs the old
  `10,11,12,13,14,15`), confirmed by the feasibility check's C-F. `dsdp_faithful` (D5),
  `game_of_trace (dsdp_alice_obs …) = gc_dsdp` against the rebuilt validated fixture, is the
  exact correctness guard and subsumes it. If a pre-switchover sanity check is still wanted,
  compare the two derived `AO_combine` `he_term`s to `dsdp_observed_combines` under the
  recv-name renaming `30 -> 100, 31 -> 101` (that term-level equality IS true).
- [ ] **D7. Verify** full `make`. **Commit** (`dsdp: derive dsdp_alice_obs via obs_of_procs;
  rebuild gc_dsdp to structural order`).

---

## Task E — the record-based secrecy theorem

**Files:** Modify `dumas2017dual/dsdp/dsdp_game_symbolic.v`.

- [ ] **E1. State `dsdp_indcpa_secrecy` GENERIC over any `P`** and prove it via the generic
  `advantage_le` (NOT the `gc_dsdp`-specific `advantage_gc_dsdp` transport, which times out
  for an abstract `P` because the hop count stays stuck and the `dsdp_faithful` rewrite
  cannot fire). Audit-verified proof body (closes to `Qed`, 0 admits):

```coq
Theorem dsdp_indcpa_secrecy (P : dsdp_indcpa_secrecy_problem)
    (Adv : dsdp_indcpa_adversary P) :
  AdvantageE (real_game P) (zero_game P) (adv_package Adv)
    <= (count_obs_hops (corrupted_view P))%:R * epsilon_cpa.
Proof.
rewrite /real_game /zero_game /game_of_problem.
have Hcnt : count_obs_hops (corrupted_view P)
    = size (hop_sites (game_of_trace (corrupted_view P)))
  by rewrite -count_hops_game_of_trace /hop_sites size_iota.
rewrite Hcnt.
eapply advantage_le.                              (* vanilla eapply; apply: OOMs/times out *)
3: apply: (adv_valid Adv).                        (* discharge ValidPackage first to pin ?LA *)
1: apply: (P.(sp_choice_cipher_of_cipherK)).
1: apply: (P.(sp_choice_msg_of_plainK)).
1: apply: (adv_disjoint_from_protocol_state Adv).
1: apply: (adv_disjoint_from_real_oracle Adv).
1: apply: (adv_disjoint_from_zero_oracle Adv).
Qed.
```

  (The `1:`/`3:` goal selectors are required by `Set Default Goal Selector "!"`.) This is a
  stronger result than the old `dsdp_advantage_derived`: it bounds *every* instance of the
  facade by `count_obs_hops · epsilon_cpa`.
- [ ] **E2. Keep `dsdp_advantage_derived`** as a thin corollary specialising
  `dsdp_indcpa_secrecy` to `P := dsdp_problem …` and loose arguments (for the concrete `P`,
  `count_obs_hops (corrupted_view P)` reduces to `2` and `real_game P`/`zero_game P` reduce
  to the loose `denote_game …`). **Build the adversary with the explicit constructor**
  `@Build_dsdp_indcpa_adversary P LA A …`, not an anonymous `{| adv_valid := … |}` record
  literal (which leaves the field-type index `game_iface_P ?P` an unresolved evar and
  fails). Grep first; delete `dsdp_advantage_derived` only if nothing references it.
- [ ] **E3. Verify** `Print Assumptions dsdp_indcpa_secrecy` lists only the inherited
  `enc_ind_cpa_real_or_zero` / `epsilon_cpa` + SSProve/classical axioms (no new custom
  axioms), and full `make`.
- [ ] **E4. Commit** (`dsdp: one-record IND-CPA secrecy theorem`).

---

## Pre-execution verification (the user's workflow; before task A starts)

1. **Compile-test the cited library APIs** against the real opam switch (minimal `/tmp`
   file or `rocq_start`): the `@pbob`/`@pcharlie` application arity, that `erase` yields an
   `Init/Send` head, the `proc` constructor pattern, `pmap`/`symbolic_get_cipher`. This is
   exactly the A1–A3 check lemma; run it first as the feasibility check.
2. **Confirm the two foundational reductions** close (`walk_obs_dsdp`, B2; and
   `dsdp_faithful`, D5) in a scratch copy before committing the plan to execution — these
   are risk R1 and R2.
3. **Adversarial audit** of this plan (subagent): does any cited reduction silently fail,
   is the `gc_dsdp` index rebuild correct, does `collect_samples`'s bound-set exclusion
   actually drop the hop/combine result names. Incorporate findings before execution.

## Risks (from the design)

- **R1: `walk_obs`/`obs_of_procs` reduction.** First-order, same regime as the existing
  `by []` `dsdp_observed_combines_eq`; `vm_compute`/`native_compute` fallback. Gated by B2,
  B5.
- **R2: the two rebuilt `gc_dsdp` indices.** Guarded by `dsdp_faithful` (D5).
- **R3: `collect_samples` bound-set exclusion.** The hop/combine result names (100–103)
  must not leak into the sample prefix. Gated by B5 (the expected trace has exactly the
  eight samples 10–15,20,21).

## Out of scope

Retiring `gc_dsdp`; the information-theoretic leg; multi-corruption or decrypted-value
leaks (the single-sort `he_term` limit).
