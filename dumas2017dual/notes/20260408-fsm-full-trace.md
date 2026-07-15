Now I have the complete picture. Building the table.

  DSDP n-party connection chain via FSM

  dsdp_fsm.v and dsdp_fsm_progress.v form a self-contained branch — they do NOT import dsdp_progress.v. The chain currently terminates at the trace/return-value theorems; the bridge into dsdp_security.v is future
  work explicitly noted in the file header (lines 13–17 of dsdp_fsm_progress.v).

  Stage: 1. Program
  Artifact: dsdp_n_procs (Definition)
  File:line: dsdp_pismc.v:341
  Content: The n-party process tuple Alice :: Relay₁ :: … :: Relayₙ :: nil produced from dsdp_n_saprocs via erase_aprocs. Entry point.
  ────────────────────────────────────────
  Stage: 1a. Tuple lift
  Artifact: procs / procs_tup (Let)
  File:line: dsdp_fsm_progress.v:151,157
  Content: procs := @dsdp_n_procs …; procs_tup is the n_parties.-tuple form for rsteps.
  ────────────────────────────────────────
  Stage: 2. Init bridge
  Artifact: init_matches_recv_at_j0 (Lemma)
  File:line: dsdp_fsm.v:1595
  Content: After 2 init steps, one_step_procs (one_step_procs procs) = ps_procs (st_recv ord0). Bridges raw program to FSM start state.
  ────────────────────────────────────────
  Stage: 2a. Init step trace
  Artifact: alice_step1_trace_local, alice_step2_trace_local (Lemmas)
  File:line: dsdp_fsm_progress.v:226,234
  Content: Each init step's Alice trace fragment: [priv_key_local dk], then [d v0].
  ────────────────────────────────────────
  Stage: 2b. Init progress
  Artifact: initial_has_progress, initial_step1_has_progress, init_not_terminated (Lemmas)
  File:line: dsdp_fsm.v:1577,1585,1655
  Content: Initial state has progress and is not terminated (preconditions for fuel induction).
  ────────────────────────────────────────
  Stage: 3. FSM data layer
  Artifact: phase_state (Record) + recv_phase / send_phase / drain_phase / tail_phase (Records)
  File:line: dsdp_fsm.v:214, 2316, 2398, 2452, 2490
  Content: Bundles process list + trace fragment + per-position invariants. The four phase Records carry the per-position relay-bg state.
  ────────────────────────────────────────
  Stage: 3a. Chain invariant
  Artifact: known_ret_state (Inductive) + KnownRetBase / KnownRetStep constructors
  File:line: dsdp_fsm.v (in Section dsdp_fsm_chain)
  Content: Backwards inductive: a state is in known_ret_state iff it reaches st_ret via one_step_procs, with progress at every intermediate step.
  ────────────────────────────────────────
  Stage: 4. Phase transitions
  Artifact: recv_phase_to_send_phase (L1), drain_phase_step (L4), send_phase_to_drain_when_j_eq_nrelay (L2), send_phase_to_drain_when_nrelay_eq_2 (L3), drain_phase_to_tail_phase (L5),
    tail_phase_from_recv_when_nrelay_eq_1 (L8)
  File:line: dsdp_fsm_progress.v:1199, 1025, 1472, 1776, 2012, 2135
  Content: Per-step transitions building the next-phase Record from the previous one. Each takes one operational step.
  ────────────────────────────────────────
  Stage: 4a. Per-step→known_ret_state
  Artifact: known_ret_of_drain_phase (L6), known_ret_of_tail_phase (L7)
  File:line: dsdp_fsm_progress.v:2069, 2006
  Content: Lift each phase Record to the chain invariant by induction on the drain measure / direct from known_ret_tail.
  ────────────────────────────────────────
  Stage: 5. Top-level invariant
  Artifact: recv_phase_to_known
  File:line: dsdp_fsm_progress.v:2333
  Content: Composition: from any recv_phase, reach known_ret_state by chaining L1 → L2/L3 → L4* → L5 → L7 (3-way dispatch on n_relay).
  ────────────────────────────────────────
  Stage: 5a. Initial chain entry
  Artifact: mk_recv_init (Definition), known_ret_recv_at_j0 (Lemma, was ks2_recv0)
  File:line: dsdp_fsm_progress.v:2471, 2484
  Content: Builds the initial recv_phase at j=0 and proves known_ret_state (st_recv ord0).
  ────────────────────────────────────────
  Stage: 5b. Bridge to retract
  Artifact: known_ret_state_to_known, known_ret_state_has_progress, known_ret_state_step (Lemmas)
  File:line: dsdp_fsm_progress.v:196, 208, 218
  Content: Three projections from the known_ret_state invariant: convert to older known_state, extract progress witness, extract one-step successor. Used by the trace induction below.
  ────────────────────────────────────────
  Stage: 5c. Tail of chain
  Artifact: known_ret_state_terminal (was known_state2_term_ret)
  File:line: dsdp_fsm_progress.v:(in Phase B renames)
  Content: If a known_ret_state is all_terminated, its process list equals ret_procs. Connects the chain's terminal step to Alice returning Ret concrete_val.
  ────────────────────────────────────────
  Stage: 6. Initial bridge for trace
  Artifact: init_to_recv0 (Lemma)
  File:line: dsdp_fsm_progress.v:2550
  Content: Combines steps 2 + 5a: starting from procs_tup, after 2 rsteps, get (ps_init, tr_init) with tr_init[0] = [d v0; priv_key_local dk], ps_init matches st_recv ord0, AND known_state_recv_at_j0 holds.
  ────────────────────────────────────────
  Stage: 6a. Fuel transfer
  Artifact: init_fuel_transfer (Lemma)
  File:line: dsdp_fsm_progress.v:2661
  Content: If procs terminates in h steps, then osp (osp procs) terminates in some h' steps. Lets the trace induction skip the 2 init steps.
  ────────────────────────────────────────
  Stage: 7. Trace induction
  Artifact: fsm_trace_induction (Lemma)
  File:line: dsdp_fsm_progress.v:2599
  Content: Fuel-driven induction over known_state: at each step, accumulate the per-step trace fragment; when all_terminated, return the full trace prefixed with the suffix.
  ────────────────────────────────────────
  Stage: 7a. Ret-tracking induction
  Artifact: fsm_ret_induction (Lemma)
  File:line: dsdp_fsm_progress.v:2692
  Content: Same as 7 but threads known_ret_state instead of known_state, so the terminal step is forced to be KnownRetBase (Alice = Ret concrete_val), not KS_done (Finish).
  ────────────────────────────────────────
  Stage: 8. Trace correctness
  Artifact: fsm_trace_correctness (Theorem)
  File:line: dsdp_fsm_progress.v:2753
  Content: Main trace theorem. For any sufficient fuel h, there exists a final tuple and trace such that tnth tr ord0 = suffix ++ [d v0; priv_key_local dk].
  ────────────────────────────────────────
  Stage: 9. Return-value correctness
  Artifact: fsm_return_value (Theorem, Admitted)
  File:line: dsdp_fsm_progress.v:2778
  Content: Same trace + nth (tval final) 0 = Ret concrete_val. Body marked as future work.
  ────────────────────────────────────────
  Stage: 10. Full trace
  Artifact: expected_trace (Definition), fsm_full_trace (Theorem, Admitted)
  File:line: dsdp_fsm_progress.v:2788, 2795
  Content: Per-cipher explicit trace including concrete_val, the tail send, the chain of relay encs, and the init prefix. Connects the operational trace to the cipher-level structure required by entropy/security
    proofs.
  ────────────────────────────────────────
  Stage: 11. Security
  Artifact: (none reachable from FSM)
  File:line: —
  Content: No FSM-based bridge exists yet. dsdp_security.v (dsdp_entropic_security_n at dsdp_security.v:1787, eavesdropper_security_n at line 2185, relay_privacy_n at line 2411) flows through dsdp_progress.v /
    dsdp_entropy.v — the older Prop-based path. The "operational-to-distributional bridge" connecting fsm_full_trace to AliceTraces_n is documented as future work in dsdp_fsm_progress.v:13–17.

  Summary of the FSM-only chain:

  dsdp_n_procs                                  [program]
    ↓ init_matches_recv_at_j0 + 2 rsteps
  st_recv ord0  +  known_ret_state              [FSM start state with chain invariant]
    ↓ recv_phase_to_known (L1..L8 composition)
  known_ret_state covering all reachable states [chain invariant for the whole run]
    ↓ fsm_trace_induction / fsm_ret_induction
  fsm_trace_correctness                         [trace = suffix ++ init prefix]   ← REACHED
  fsm_return_value                              [Alice = Ret concrete_val]        ← Admitted
  fsm_full_trace                                [trace = expected_trace rr_tail]  ← Admitted
    ↓ (operational → distributional bridge — NOT YET PROVED)
  AliceTraces_n random variable                 [used by dsdp_security.v]
    ↓ existing entropy lemmas in dsdp_entropy.v
  relay_privacy_n / eavesdropper_security_n     [security; currently reached via dsdp_progress.v, not FSM]

  The two Admitted theorems (fsm_return_value, fsm_full_trace) and the missing operational-to-distributional bridge are the only gaps between the FSM path and the n-party security results. Everything before that is
   Qed-proved in the two FSM files (dsdp_fsm.v 0 admits, dsdp_fsm_progress.v 2 admits — exactly these two).
