# DSDP formalization — directory map

The 3-party Dumas et al. (2017) dual scalar-product protocol (DSDP), formalized over Infotheo.
Files are grouped by role. All paths load under `-R . infotheo`, so a file's
logical name is `infotheo.dumas2017dual.dsdp.<bucket>.<basename>`; imports use the short
basename and resolve by suffix.

## Buckets

- **core/** — protocol definition and embedding.
  `dsdp_interface` (the `DSDP_Interface` record), `dsdp_session_types` (session-typed wrappers),
  `dsdp_program` (the 3-party programs + algebraic correctness `dsdp_computes_dot_product`),
  `dsdp_pismc` (piSMC realization, duality, termination), `dsdp_correctness` (computational
  correctness over idealized / Benaloh / Paillier AHE).

- **fdist_hopping/** — the game-hopping secrecy result over Infotheo distributions.
  `dsdp_alice_fdist_secrecy` (the real-or-zero advantage `indcpa_fdist_epsilon`, the two hop
  reductions, the guess / unpredictability / simulator-closeness headlines),
  `dsdp_alice_trace_link` (the same bounds at the executed fifteen-round piSMC trace).

- **counting/** — the information-theoretic / solution-counting leg.
  `dsdp_entropy` (fiber cardinality `dsdp_fiber_card`, conditional entropy `dsdp_centropy_uniform`),
  `dsdp_entropy_trace` (trace-based entropy), `dsdp_malicious_dotp` (degenerate dot-product
  queries and their leakage).

- **dsdp_main.v** — the headline theorems of both axes, each proved over a cloned copy of
  its source section context; supporting machinery stays in the axis files. The counting-axis
  headlines are unconditional; the fdist-hopping headlines carry two IND-CPA advantage terms,
  one at Bob's key and one at Charlie's.

- **dsdp_main_ssprove.v** — rename-aside copy of the pre-deprecation SSProve development
  (games, IND-CPA hopping, simulator). Outside `_CoqProject`; kept for reference only.
