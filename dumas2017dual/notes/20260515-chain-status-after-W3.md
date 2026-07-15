# DSDP secrecy chain status after W3

Date: 2026-05-15.
Latest commit: `414fbab dsdp: transported corollaries dsdp_alice_secrecy_pismc + entropy_ge_bound_pismc (W3)`

## Three-leg chain

**Leg 1 — piSMC DSDP program ⇄ SSProve `game_real`.** Now formally
bridged via the W1-W3 commits:

- `dumas2017dual/dsdp/dsdp_security_indcpa_pismc.v`:
  - `dsdp_palice_code`, `dsdp_pbob_code`, `dsdp_pcharlie_code`
    (translated via `translate_pismc_to_ssprove`).
  - `pbob_head_send_eq`, `pcharlie_head_send_eq` (head-send equalities
    using `translate_correct_marginal_send` at
    `smc/pismc_to_ssprove.v:315`).
  - `dsdp_recv_oracle` (serves c_2 / c_3 to Alice's translated code).
  - `game_real_pismc` (composes the translated palice with the recv
    oracle, returns the four-element list matching `game_real`'s
    leaked-ciphertext output).
  - `Theorem dsdp_alice_secrecy_pismc` and
    `Theorem entropy_ge_bound_pismc` (transported U1/U2 bounds).
- `smc/pismc_to_ssprove.v:240-241`: `code_of_proc`'s `Ret d` rule
  patched from `[data_to_cipher d]` (singleton) to `[::]` (empty list).
  Semantic motivation: `Ret` payload is the piSMC program's local
  return value, not a wire send.

**Remaining gap in leg 1**: the W2 `Hypothesis game_real_eq_pismc`
is undischarged. Proof sketch verified up to 11 `ssprove_sync` +
2 `r_put_rhs` steps; the inner unfolding of `code_link
dsdp_palice_code dsdp_recv_oracle` (translator reduction lemmas +
recv-oracle `get` resolution + `chcipher_of_cipherK` /
`chmsg_of_msgK` cancellations + 4-element list alignment) is the
multi-day SSProve composition proof flagged in the W2 lemma's
docstring.

**Leg 2 — SSProve IND-CPA hops.** Closed (commits `543fee0`, `3579110`,
`5b8a7d4`). Load-bearing axiom: `indcpa_ror.enc_ind_cpa_real_or_zero`.
Section hypotheses in the closure: `Pr_guess_enc_zero_le_invm` (the
IT residual), `Pr_guess_real_ge_invm` (new from U2),
`epsilon_cpa_ge0` (new from U2).

**Leg 3 — IT residual ⇄ SSProve indicator hypothesis.** Still open.
`cPr_V2_V3_uniform_on_fiber_joint`
(`dsdp_security_indcpa.v:3563`) proves conditional uniformity of
`(V_2, V_3)` on the dsdp fiber in `fdist_game_enc_zero_joint`, but no
lemma proves `Pr_guess_enc_zero_le_invm` from it. The bridge would route
through `bridge_enc_zero_to_fdist` (`dsdp_security_indcpa.v:1885`,
partially implemented) and the SDistr-to-fdist machinery.

## Out-of-scope items

1. Discharging `game_real_eq_pismc` (W2 Hypothesis).
2. Discharging `Pr_guess_enc_zero_le_invm` (~80-120 lines per the sprightly
   plan).
3. Discharging `Pr_guess_real_ge_invm` (note: NOT trivially true for
   adversarial predictors that anti-correlate with V_2; the bound may
   need a constraint on the predictor class or a weaker
   formulation `0 < Pr`).
4. Discharging `epsilon_cpa_ge0` (trivial at any concrete AHE
   instantiation; stays as a Section hypothesis in the abstract
   theory).
5. piSMC-rooted variants of U1/U3 concrete corollaries
   (`Concrete.secrecy_random_guess_pismc` etc. at Idealized /
   Benaloh / Paillier) — ~400 new lines mirroring the existing
   concrete-corollary patterns.
6. Closing the upstream `__admitted__interchange_psum` admit.

## `Print Assumptions` of the latest results

Both `dsdp_alice_secrecy_pismc` and `entropy_ge_bound_pismc`
transitively depend on:

- `game_real_eq_pismc` (W2 Hypothesis; pins the piSMC-translated
  machinery `dsdp_palice_code` / `dsdp_pbob_code` /
  `dsdp_pcharlie_code` / head-send lemmas / `dsdp_recv_oracle`
  through the type of the Hypothesis).
- `enc_ind_cpa_real_or_zero` (IND-CPA axiom, load-bearing).
- `__admitted__interchange_psum` (upstream pending).
- Standard SSProve / mathcomp-analysis axioms (propositional
  extensionality, functional extensionality, classical choice, proof
  irrelevance, `Axioms.R`, `epsilon_cpa`).

The U1/U3 concrete corollaries (`Concrete.secrecy_random_guess`,
`Idealized.entropy_random_guess`, etc.) do NOT depend on
`game_real_eq_pismc` — they're stated against the hand-authored
`game_real`. To produce piSMC-rooted concrete corollaries, item 5
above is needed.
