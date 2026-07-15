---
name: reference_dsdp_security_identifiers
description: All game/oracle/lemma identifiers in dsdp_security_indcpa.v verified; no Admitted; proof closures confirmed
metadata:
  type: reference
---

File: /Users/cheng-huiweng/Projects/coq/infotheo-itp/dumas2017dual/dsdp/ref/dsdp_security_indcpa.v

All verified to exist and match described roles:

**Games (Definitions):**
- game_real (line 325): real DSDP execution package
- game_hybrid_one (line 385): first IND-CPA hop — Charlie's ciphertext zeroed
- game_hybrid_two (line 445): second IND-CPA hop — Bob's ciphertext zeroed
- game_enc_zero (line 516): residual game, both ciphertexts zeroed

**Oracle packages (Definitions):**
- oracle_encrypt_real_pkg (homomorphic_encryption/indcpa_ror.v:173): real encryption oracle
- oracle_encrypt_zero_pkg (homomorphic_encryption/indcpa_ror.v:198): zero encryption oracle
- game_via_oracle_charlie (line 600): translation package for Charlie's slot
- game_via_oracle_bob (line 672): translation package for Bob's slot

**Reduction packages (Definitions):**
- predictor_via_oracle_charlie (line 739): `predictor ∘ pack game_via_oracle_charlie`
- predictor_via_oracle_bob (line 752): `predictor ∘ pack game_via_oracle_bob`

**Perfect-equivalence lemmas (all Qed-closed):**
- game_real_equiv_charlie_real (line 833): game_real ≈₀ game_via_oracle_charlie ∘ oracle_real
- charlie_zero_equiv_game_hybrid_one (line 1000): game_via_oracle_charlie ∘ oracle_zero ≈₀ game_hybrid_one
- game_hybrid_one_equiv_bob_real (line 1032): game_hybrid_one ≈₀ game_via_oracle_bob ∘ oracle_real
- bob_zero_equiv_game_hybrid_two (line 1063): game_via_oracle_bob ∘ oracle_zero ≈₀ game_hybrid_two
- game_hybrid_two_perfect_game_enc_zero (line 1096): game_hybrid_two ≈₀ game_enc_zero

**Advantage-hop lemmas (all Qed-closed):**
- advantage_hop_real_h1 (line 1124): AdvantageE game_real game_hybrid_one predictor <= epsilon_cpa
- advantage_hop_h1_h2 (line 1292): AdvantageE game_hybrid_one game_hybrid_two predictor <= epsilon_cpa

**No Admitted in dsdp_security_indcpa.v (grep count = 0).**
