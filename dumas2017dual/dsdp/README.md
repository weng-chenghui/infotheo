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
  `dsdp_alice_hop_secrecy` (the two hop reductions, the guess / unpredictability /
  simulator-closeness headlines), `dsdp_alice_trace_link` (the same bounds at the executed
  fifteen-round piSMC trace), `dsdp_instance_sequence` (the DSDP instance record, the
  sequence record over it, the asymptotic headline, the idealized-scheme witness, and the
  DSDP bounds read off at the Paillier and Benaloh instances, in residuosity currency).
  The game vocabulary, the two schemes and the asymptotics these files use live outside
  this tree, in `computational_security/`.

- **computational_security/**, a sibling of `dumas2017dual/`, is the scheme-independent
  computational layer that `dsdp/` consumes; its files depend on no DSDP file, and their
  logical names are `infotheo.computational_security.<basename>`.
  `negligible` (`negligible_fun` and its closure lemmas, the asymptotic reading every
  concrete bound below is given), `indcpa_game` (the real-or-zero game, the advantage
  `indcpa_epsilon`, the adversary-class assumption record, the scheme record
  `indcpa_scheme`), `epshop` (the epsHop language, in which a chain of hops carries an
  accumulated loss as a list of labelled terms together with the soundness field a
  multi-hop bound is read off),
  `paillier_indcpa_scheme` / `benaloh_indcpa_scheme`
  (the two concrete schemes as `indcpa_scheme` values, scheme side only, fixed and indexed
  by a security parameter, each with the reduction that derives its IND-CPA assumption
  from a residuosity assumption: `dcr_of_adversary` / `dcr_of_adversary_zero` giving
  `paillier_indcpa_assumption`, and `residuosity_of_adversary` /
  `residuosity_of_adversary_zero` giving `benaloh_indcpa_assumption`, at twice the
  residuosity epsilon per key).
  The three epsHop programs live in the files whose reductions they write.
  `paillier_chain` in `paillier_indcpa_scheme.v` and `benaloh_chain` in
  `benaloh_indcpa_scheme.v` each hop twice around one identity, logging one residuosity
  call per hop, so each loss reads as twice the assumed residuosity epsilon, and each
  takes its two class memberships as parameters;
  `alice_chain` in `hopping/dsdp_alice_hop_secrecy.v` hops twice over the two received
  ciphertexts, logging one IND-CPA reduction advantage per hop, and ends in the terminal
  statement that bounds the all-zero endpoint under a third label, so its loss reads as
  the inverse plaintext count plus the two advantages. The three headline statements are
  unchanged and are now closed by `chain_sound` or `bound_sound` at the chain itself,
  the one triangle inequality of the argument having been discharged once in
  `epshop.v`.

- **Scheme assumptions** — `homomorphic_encryption/residuosity_game.v` states the e-th
  residuosity problem in a finite commutative unit ring: the two challenge laws
  `unit_fdist` and `residue_fdist`, the distinguisher record, `residuosity_advantage`,
  the assumption record `residuosity_assumption`, the translation-invariance fact
  `unit_fdist_translateE`, and the zero-epsilon witness `decide_constant_assumption`.
  `computational_security/paillier_indcpa_scheme.v` instantiates it as `dcr_assumption`
  at the ring Z/(pq)^2 Z and exponent `p * q`, which is decisional composite residuosity,
  and `computational_security/benaloh_indcpa_scheme.v` as `benaloh_residuosity_assumption`
  at Z/nZ and exponent `r`.

- **counting/** holds the information-theoretic, solution-counting leg, listed in
  `_CoqProject` load order.
  `dsdp_entropy_trace` (trace-based entropy), `dsdp_entropy` (fiber cardinality
  `dsdp_fiber_card`, the conditional entropy `dsdp_centropy_uniform` and its N-party form
  `dsdp_centropy_uniform_n`), `dsdp_malicious_dotp` (the degenerate dot-product query,
  Alice's view `AliceDotpView` at it, and the leakage theorems `US_e1_centropy_V2_eq0`
  and its N-party form `US_e1_centropy_VS0_eq0`), `dsdp_relay_secrecy` (`BobView` and
  `CharlieView`, their independence of `V1`, and the four relay privacy theorems
  `bob_privacy_V1`, `charlie_privacy_V1`, `bob_privacy_V3`, `charlie_privacy_V2`).
  The last two load after `hopping/`.

- **dsdp_setting.v** holds `dsdp_setting`, the data a 3-party DSDP security statement
  is made over at every security parameter: the hopping axis's instance sequence, the
  plaintext modulus at `k` as its two primes, and one `dsdp_random_inputs` per `k`,
  which carries the sample space with its law, the eleven random inputs with each one
  independent of the joint of the other ten, and the five uniform laws. The one link
  field `card_plain` equates the k-th plaintext count with `p * q`. The file also holds
  the two query records `dsdp_honest_query` and `dsdp_corrupted_query`, Alice's output
  and each party's view at one setting and one `k`, the laws those fields imply, and
  the values `uniform_inputs`, `idealized_setting` and `corrupted_setting` that show the
  records inhabited.

- **dsdp_security.v** holds `dsdp_admissible_predictor`, the trace predictor whose two
  reduction adversaries the sequence's assumption admits, `dsdp_security`, the twenty-six
  statements one setting proves, and `dsdp_securityP`, the value every setting has, whose
  every field is an axis theorem applied to the projections of that setting. Everything
  naming an adversary or stating a bound lives here, and everything that exists before an
  adversary is named lives in `dsdp_setting.v`.

- **dsdp_main.v** holds three values of `dsdp_setting` with their parameters fed, Paillier,
  Benaloh at block size `p * q`, and the idealized scheme, and projects each of the
  twenty-six fields at each of them as a corollary whose statement is written out at that
  instance. Nothing is proved here.

- **dsdp_main_ssprove.v** — rename-aside copy of the pre-deprecation SSProve development
  (games, IND-CPA hopping, simulator). Outside `_CoqProject`; kept for reference only.
