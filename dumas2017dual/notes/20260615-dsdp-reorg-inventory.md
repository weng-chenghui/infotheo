# DSDP reorganization — scan inventory and bucket manifest

Date: 2026-06-15 (Phase A of the reorg per `20260615-dsdp-reorg-design.md`)
Method: mechanical declaration index (source-extracted, line-anchored) + per-file labelling by
read-only agents. 14 live files, 259 top-level declarations scanned. 0 `Admitted` / `admit` /
`Axiom` across all live files (section `Hypothesis` parameters are noted per file, not dangling).

## Checkpoint decisions

1. **`dsdp_security.v` -> `counting/`.** It is a self-contained information-theoretic entropy
   security analysis: conditional-entropy bounds `H(party_input | adversary_view) = log m` for
   each party (`bob_privacy_V1/V3`, `charlie_privacy_V1/V2`, `BobView_indep_*`,
   `CharlieView_indep_*`), plus the malicious-Alice disclosure `US_compromised_leaks_V2`. It is
   the IT-security conclusion built on the solution-counting in `dsdp_entropy.v`, so it sits in
   `counting/` alongside it. Leaf; 0 Admitted; 57 section Hypotheses. Not superseded (it is the
   information-theoretic track, orthogonal to the computational IND-CPA track in the fiber file).

2. **`convert/` -> CREATE, extract from the fiber file.** All SDist<->fdist conversion machinery
   in the live tree (132-occurrence footprint) lives in `dsdp_security_indcpa_fiber.v`, as a
   contiguous generic block before `Section dsdp_guess_distribution` (line 360): `Section
   sdistr_to_fdist` (`sdistr_to_fdist`, `sdistr_to_fdistE`, `Pr_sdistr_to_fdist`, lines 123-157)
   plus the framing lemmas `dmargin_comp`, `dlet_dmargin_eq`, `Pr_fst_map`, `Pr_fst_agree_locs`,
   `Pr_fst_closed`, `Pr_fst_put_invariant`, `eq_in_dlet`, `dlet_const_unit`, `dmargin_fst_const`,
   `Pr_code_preserves`, `fdistmap_bij_unif`, `mean1_eq1` (lines 159-355). These mention only
   SSProve (`distr`, `Pr_code`, `Locations`) and Infotheo (`FDist`, `fdist_uniform`, `Pr`) notions,
   never any DSDP object, so they form a clean library. They are consumed only inside the fiber
   file today (and `probe_fiber_reflection.v` re-defines `Pr_fst_closed` locally, evidence the
   block is reusable infrastructure). Extraction realizes the user-requested axis and shrinks the
   2127-line fiber file; it is justified by organization/legibility, not by current cross-file
   reuse. Done as Phase D after the moves are committed green. Exact cut boundaries confirmed at
   extraction time.

## Final bucket map (revised by the scan)

```
dsdp/
  core/            dsdp_interface, dsdp_session_types, dsdp_program, dsdp_pismc, dsdp_correctness
  symbolic_game/   dsdp_symbolic, dsdp_game_code, dsdp_game_symbolic, dsdp_game_gen_literal
  indcpa_hopping/  dsdp_indcpa_security, dsdp_security_indcpa_fiber
  counting/        dsdp_entropy, dsdp_entropy_trace, dsdp_security
  convert/         dsdp_convert        (extracted from the fiber file in Phase D)
  legacy/
    scratch/       dsdp_chlipala, dsdp_security_indcpa_clone, dsdp_security_indcpa_concrete_clone,
                   dsdp_security_indcpa_pismc_clone, probe_fiber_reflection, scratch_fiber_dev,
                   dsdp_syntax, dsdp_syntax_demo
    superseded/    dsdp_security_indcpa, dsdp_security_indcpa_concrete,
                   dsdp_security_indcpa_pismc, dsdp_trace_bridge
```

`dsdp/.scratch/` (5 untracked probe/audit `.v`) is out of scope: untouched.

## Per-file manifest (live files)

### core/

- **dsdp_interface.v** (34 decls, 0 adm) — unified `DSDP_Interface` record bundling data types
  and ops; `Standard_DSDP_Interface` canonical instance over `AHEncType`. Confirmed.
- **dsdp_session_types.v** (15 decls, 0 adm) — session-typed wrappers `DRecv_enc/dec`, `DSend`,
  `DInit/DRet/DFinish` and iteration variants over `DSDP_Interface`. Confirmed.
- **dsdp_program.v** (60 decls, 0 adm) — DSDP 3-party programs (`palice/pbob/pcharlie`); headline
  algebraic correctness `dsdp_computes_dot_product` (L286) and N-party `_n` (L321). Confirmed.
- **dsdp_pismc.v** (193 decls, 0 adm) — piSMC session-typed realization; duality lemmas
  (`alice_bob_dual` ...), termination/non-fail (`dsdp_ideal_senv_zero`, `dsdp_n4_senv_zero`),
  cross-equality with `dsdp_program`. Confirmed.
- **dsdp_correctness.v** (42 decls, 0 adm) — computational correctness over idealized / Benaloh /
  Paillier AHE (`dsdp_is_correct`, `dsdp_computes_dot_product_{benaloh,paillier}`). The live file
  that instantiates the concrete schemes. Confirmed.

### symbolic_game/

- **dsdp_symbolic.v** (21 decls, 0 adm) — symbolic interface instance; derives Alice's emitted
  combines (`dsdp_observed_combines_eq`) and hop ciphertexts (`dsdp_received_hop_ciphertexts_eq`)
  by computation. Confirmed.
- **dsdp_game_code.v** (79 decls, 0 adm) — `he_term` / `game_code` ASTs; hybrid-ladder machinery
  (`denote_run`, `denote_game`, `hybrid_ladder`, `advantage_le`). Confirmed.
- **dsdp_game_symbolic.v** (48 decls, 0 adm) — corrupted-Alice obs derivation (`obs_of_procs`,
  `obs_of_procs_dsdp`); generic secrecy `dsdp_indcpa_secrecy` (<= hops * epsilon_cpa); leak-S
  variant `dsdp_advantage_derived_leak_S`. Confirmed.
- **dsdp_game_gen_literal.v** (32 decls, 0 adm) — reflection-certified hand-spelled programs equal
  the generator's denotation (`gen_literal_zeroE`, `gen_literal_realE`). Confirmed.

### indcpa_hopping/

- **dsdp_indcpa_security.v** (33 decls, 0 adm) — public IND-CPA facade; `dsdp_problem` control
  record; `dsdp_problem_secure` (<= 2 * epsilon_cpa). Confirmed.
- **dsdp_security_indcpa_fiber.v** (148 decls, 0 adm) — final composed bound
  `dsdp_alice_secrecy_leak_S <= 1/card_msg + 2*epsilon_cpa`. Holds the generic SDist<->fdist
  conversion block (-> extracted to `convert/` in Phase D) plus the DSDP guess-distribution proof.

### counting/

- **dsdp_entropy.v** (142 decls, 0 adm; 48 section Hypotheses) — solution counting: `dsdp_fiber`,
  `dsdp_fiber_card` (= pq), uniform-on-solutions, conditional entropy `dsdp_centropy_uniform`
  (= 2*log pq), N-party variants, ring-generic variants. Confirmed.
- **dsdp_entropy_trace.v** (43 decls, 0 adm) — trace structure and algebraic correctness over
  traces (`dsdp_result_correct`, `dsdp_algebraic_correctness`). Confirmed.
- **dsdp_security.v** (259 decls, 0 adm; 57 section Hypotheses) — see checkpoint decision 1.

## Legacy (not scanned for bucketing; placement decided in design spec)

- `legacy/superseded/`: `dsdp_security_indcpa` (2507 L, prior hand-written hybrid bound, same
  headline as the live fiber file), `dsdp_security_indcpa_concrete` (Benaloh/Paillier security
  instantiation; live build keeps Benaloh/Paillier via `dsdp_correctness.v`),
  `dsdp_security_indcpa_pismc` (rests on open `Hypothesis game_real_eq_pismc`), `dsdp_trace_bridge`
  (partial bridge, does not discharge that hypothesis).
- `legacy/scratch/`: untracked clones / probe / scratch / empty `dsdp_syntax` / unused
  `dsdp_syntax_demo`.
