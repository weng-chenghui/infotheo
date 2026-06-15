# Superseded DSDP security development

These four files are the prior hand-written computational-security development for DSDP-Alice.
They are excluded from the build (not in `_CoqProject`). They are kept for reference and history,
not maintained.

They are replaced by the auto-derived path
`core -> symbolic_game -> indcpa_hopping`, whose final result
`indcpa_hopping/dsdp_security_indcpa_fiber.v` proves the same headline bound by deriving the
SSProve game from the single DSDP program rather than by hand:

    dsdp_alice_secrecy_leak_S <= 1/card_msg + 2*epsilon_cpa.

## Files

- **dsdp_security_indcpa.v** — the prior hybrid closed-form bound
  `Pr[A(AliceView) = V_2] <= 1/m + 2*epsilon_cpa` (hand-written; same headline as the live fiber
  file).
- **dsdp_security_indcpa_concrete.v** — security-side Benaloh/Paillier concrete instantiation. The
  live build still exercises Benaloh/Paillier through `core/dsdp_correctness.v`.
- **dsdp_security_indcpa_pismc.v** — piSMC-rooted variant; rests on an open
  `Hypothesis game_real_eq_pismc`.
- **dsdp_trace_bridge.v** — partial piSMC<->SSProve trace bridge; does not discharge that
  hypothesis.
