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

- **hopping/** — the hopping secrecy result over Infotheo distributions.
  `indcpa_game` (the real-or-zero game, the advantage `indcpa_epsilon`, the adversary-class
  assumption record, the scheme record `indcpa_scheme`, `negligible_fun`),
  `paillier_indcpa_scheme` / `benaloh_indcpa_scheme`
  (the two concrete schemes as `indcpa_scheme` values, scheme side only, fixed and indexed
  by a security parameter), `dsdp_alice_hop_secrecy` (the two hop reductions, the guess / unpredictability /
  simulator-closeness headlines), `dsdp_alice_trace_link` (the same bounds at the executed
  fifteen-round piSMC trace), `dsdp_instance_sequence` (the DSDP instance record, the
  sequence record over it, the asymptotic headline, the idealized-scheme witness, and the
  DSDP bounds read off at the Paillier and Benaloh instances).

- **counting/** — the information-theoretic / solution-counting leg.
  `dsdp_entropy` (fiber cardinality `dsdp_fiber_card`, conditional entropy `dsdp_centropy_uniform`),
  `dsdp_entropy_trace` (trace-based entropy), `dsdp_malicious_dotp` (degenerate dot-product
  queries and their leakage).

- **dsdp_security.v** holds `dsdp_security`, the data a 3-party DSDP security statement
  is made over at every security parameter: the hopping axis's instance sequence, the
  plaintext modulus at `k` as its two primes, the sample space and its law, the eleven
  random inputs with each one independent of the joint of the other ten, the five uniform
  laws, and the one link field `card_plain` equating the k-th plaintext count with `p * q`.
  A derived section gives Alice's output and the eleven laws one setting yields at one `k`,
  and `idealized_security` is a value of the record, at the idealized scheme over a
  composite modulus and the uniform law on eight coordinates.

- **dsdp_main.v** — the headline theorems of both axes, each stated over one
  `dsdp_security` value and one security parameter, and proved over a cloned copy of its
  source section context; supporting machinery stays in the axis files. The counting-axis
  headlines are unconditional; the hopping headlines carry two IND-CPA advantage terms,
  one at Bob's key and one at Charlie's.

- **dsdp_main_ssprove.v** — rename-aside copy of the pre-deprecation SSProve development
  (games, IND-CPA hopping, simulator). Outside `_CoqProject`; kept for reference only.
