# DSDP formalization — directory map

The 3-party Dumas et al. (2017) dual scalar-product protocol (DSDP), formalized over Infotheo
and SSProve. Files are grouped by role. All paths load under `-R . infotheo`, so a file's
logical name is `infotheo.dumas2017dual.dsdp.<bucket>.<basename>`; imports use the short
basename and resolve by suffix.

## Buckets

- **core/** — protocol definition and embedding.
  `dsdp_interface` (the `DSDP_Interface` record), `dsdp_session_types` (session-typed wrappers),
  `dsdp_program` (the 3-party programs + algebraic correctness `dsdp_computes_dot_product`),
  `dsdp_pismc` (piSMC realization, duality, termination), `dsdp_correctness` (computational
  correctness over idealized / Benaloh / Paillier AHE).

- **symbolic_game/** — the symbolic walk that auto-derives the SSProve game.
  `dsdp_symbolic` (symbolic execution), `dsdp_game_code` (`he_term` / `game_code` IR + hybrid
  ladder), `dsdp_game_symbolic` (corrupted-Alice observation derivation + generic
  `dsdp_indcpa_secrecy`), `dsdp_game_gen_literal` (reflection-certified literal programs).

- **indcpa_hopping/** — the IND-CPA game-hopping secrecy result.
  `dsdp_indcpa_security` (the `dsdp_problem` facade, `<= 2*epsilon_cpa`),
  `dsdp_security_indcpa_fiber` (the composed bound
  `dsdp_alice_secrecy_leak_S <= 1/card_msg + 2*epsilon_cpa`).

- **fdist_hopping/** — the SSProve-free game-hopping secrecy result over Infotheo distributions.
  `dsdp_alice_fdist_secrecy` (the real-or-zero advantage `indcpa_fdist_epsilon`, the two hop
  reductions, the guess / unpredictability / simulator-closeness headlines),
  `dsdp_alice_trace_link` (the same bounds at the executed fifteen-round piSMC trace).

- **counting/** — the information-theoretic / solution-counting leg.
  `dsdp_entropy` (fiber cardinality `dsdp_fiber_card`, conditional entropy `dsdp_centropy_uniform`),
  `dsdp_entropy_trace` (trace-based entropy), `dsdp_security` (per-party entropy bounds
  `H(input | view) = log m`).

- **convert/** — generic SDist<->fdist + `Pr_code` framing library.
  `dsdp_convert` bridges SSProve `distr.distr` / `Pr_code` and Infotheo `FDist` / `Pr`
  (`sdistr_to_fdist`, `Pr_sdistr_to_fdist`, `dmargin_comp`, `Pr_fst_map`, `fdistmap_bij_unif`,
  `mean1_eq1`, ...). Consumed by `indcpa_hopping/dsdp_security_indcpa_fiber`.

- **legacy/** — not part of the verified build (excluded from `_CoqProject`).
  - `scratch/` — throwaway dev artifacts (clones, probes, the empty `dsdp_syntax`, the unused
    `dsdp_syntax_demo`, the Chlipala-style experiment).
  - `superseded/` — the prior hand-written security development, replaced by the auto-derived
    `indcpa_hopping/dsdp_security_indcpa_fiber`. See `legacy/superseded/README.md`.
