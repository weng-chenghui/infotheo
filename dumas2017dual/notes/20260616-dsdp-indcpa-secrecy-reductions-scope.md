# Scope: IND-CPA secrecy reductions for corrupted Bob / Charlie (future work)

Date: 2026-06-16
Status: design memo. No code yet. Companion to
`20260616-dsdp-malicious-leak-sound-reconstruction.md`.

## 1. What this replaces

Commit `d3098a9` deleted the semi-honest party-privacy theorems
`bob_privacy_V1`, `bob_privacy_V3`, `charlie_privacy_V1`, `charlie_privacy_V2`.
Each asserted, for an honest-but-curious party, `H(V_i | PartyView) = log m` — the
view leaves a relay's input fully uncertain. The proofs rested on the unsound
`E_enc_inde` (a ciphertext is information-theoretically independent of every
variable). The statements are **false in the IT model**: a party's view contains
ciphertexts of the secrets, and conditional entropy leaks through a deterministic
encryption. Only a computational, game-based reading is sound.

## 2. Sound target

For each corrupted party `X ∈ {Bob, Charlie}` and each relay input `V_i` that `X`
should not learn, the secrecy claim is the corrupted-`X` analogue of the existing
corrupted-Alice guessing triangle: the advantage of distinguishing the real game
from its all-zero endpoint, and the success probability of guessing `V_i`, are
bounded by IND-CPA cost plus the `1/m` output fiber.

```
AdvantageE (real_game_X) (zero_game_X) (adv_package Adv) <= (hops_X)%:R * epsilon_cpa
guess_success_X <= 1/m + (hops_X)%:R * epsilon_cpa
H_unp^C(V_i | View_X) >= log m - log (1 + hops_X * m * epsilon_cpa)
```

where `hops_X` is the encryption-hop count of `X`'s corrupted trace.

## 3. Machinery already in place

- **Corrupted-party programs** — `palice_sym`, `pbob_sym`, `pcharlie_sym` all
  exist (`dsdp_symbolic_exec.v`). The Bob/Charlie reductions instantiate at
  `pbob_sym` / `pcharlie_sym` instead of `palice_sym`.
- **Trace derivation** — `obs_of_procs` derives a corrupted party's full trace
  (samples, hops, combines, leak) from its program; it is party-generic.
- **Generic secrecy bound** — `dsdp_indcpa_secrecy` bounds any experiment's
  real-vs-all-zero advantage by `count_obs_hops * epsilon_cpa`. It is already
  party-agnostic; the Alice headline `dsdp_alice_view_advantage_le` is its
  instance at `dsdp_experiment` (hop count two).
- **Guessing / fiber side** — `guess_success_sdistr_eq_fdist` (SSProve→Infotheo
  connector), `guess_fdist_success_le` (the `1/m` fiber), and
  `dsdp_advantage_derived_leak_S` (the output-exposing endpoint advantage) drive
  the Alice triangle; their statements are parameterized by the seed and
  predictor, not by which party is corrupt.

## 4. Open work

1. **Per-party experiment records.** Define `dsdp_experiment_bob`,
   `dsdp_experiment_charlie` (the corrupted-`X` analogues of `dsdp_experiment`):
   corrupted program `pbob_sym` / `pcharlie_sym`, the received-hop ciphertexts of
   `X`, and the challenge secret `X` must not learn.
2. **Hop counts.** Establish `count_obs_hops (corrupted_view dsdp_experiment_X) =
   hops_X` (the `Example`-style fact, analogue of `dsdp_experiment_hops`). Bob and
   Charlie see different numbers of ciphertext hops than Alice.
3. **View headlines.** Instantiate `dsdp_indcpa_secrecy` at each record to get
   `bob_view_advantage_le`, `charlie_view_advantage_le`.
4. **Guessing triangle per party.** Instantiate the guessing/fiber lemmas at the
   corrupted-`X` seed to get `bob_guess_real_le`, `charlie_guess_real_le`, and the
   unpredictability lower bounds.
5. **Seed plumbing.** Each party's seed exposes a different set of plaintext
   values (`seed_w*` hypotheses); the injectivity side-condition
   (`injective (fun v => w_u * v)`) must be re-derived per party.

## 5. Open-status caveat (two tiers)

- **Tier 1 (machinery, done):** corrupted-party programs, the party-generic
  `obs_of_procs` derivation, the generic `dsdp_indcpa_secrecy` bound, and the
  guessing/fiber connectors all exist and are machine-checked.
- **Tier 2 (instantiation, not done):** the per-party experiment records, hop
  counts, and the Bob/Charlie view + guessing headlines of Section 4 are not yet
  written. Until they are, the only machine-checked secrecy result is for
  corrupted Alice; Bob/Charlie semi-honest secrecy is design-complete but
  unproven.

## 6. Relation to the leak result

This secrecy work is orthogonal to `US_n_compromised_leaks_secret` /
`US_compromised_leaks_V2`. The leak is a from-below fact (a malicious party reads
a relay's input off the plaintext output) needing no encryption assumption; these
secrecy bounds are from-above facts (an honest-but-curious party learns nothing
beyond IND-CPA slack) and need the game-based reduction above.
