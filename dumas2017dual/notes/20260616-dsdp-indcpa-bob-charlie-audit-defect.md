# Audit: the Bob/Charlie IND-CPA secrecy plan has a structural defect

Date: 2026-06-16
Status: audit finding. Audits `20260616-dsdp-indcpa-secrecy-reductions-scope.md`.
Outcome: **do not implement Section 4 as written.** The IND-CPA hopping
architecture is structurally specific to corrupted Alice; the Bob/Charlie
"instantiation" produces vacuous view headlines and an unrealisable guessing
triangle.

## 1. The plan's load-bearing claims

The scope memo (Section 3) claims the reductions are a near-mechanical
instantiation: `obs_of_procs` "derives a corrupted party's full trace ... it is
party-generic", `dsdp_indcpa_secrecy` is "already party-agnostic", and the
guessing/fiber lemmas "are parameterized by the seed and predictor, not by which
party is corrupt." Section 4 then asks to point new experiment records at
`pbob_sym`/`pcharlie_sym`, compute `hops_X`, and instantiate the Alice headlines.

## 2. Finding 1 — Bob and Charlie have zero IND-CPA hops

A reception becomes an IND-CPA hop only when its incoming wire value has the bare
shape `HE_enc party (HE_var secret) _` (`walk_obs`,
`dsdp_game_derivation.v:247-257`; `count_obs_hops`, ibid:124-130). In DSDP only
Alice ever receives secrets in that shape: each relay's first send to Alice is
the bare ciphertext of its own secret (`dsdp_received_hop_ciphertexts` =
`[Enc(Bob,v2); Enc(Charlie,v3)]`), giving Alice two hops (`dsdp_obs_hops = 2`).

The relays never receive a bare secret-bearing ciphertext. Walking the real
programs against the streams they actually receive on the wire:

- **Bob** receives Alice's two sends to him, the homomorphic combos
  `a1 = c2^u2 * E(Bob,r2)` and `a2 = c3^u3 * E(Charlie,r3)` (both `HE_emul ...`).
  His own head send `Enc(Bob,v2)` is a send (`AO_combine`), not a reception.
  `count_obs_hops (obs_of_procs pbob_sym <a1,a2> ...) = 0`.
- **Charlie** receives Bob's single send to him, the aggregate combo
  (`HE_emul (HE_emul ...) (HE_enc 2 (HE_dec ...) 23)`).
  `count_obs_hops (obs_of_procs pcharlie_sym <combo> ...) = 0`.

Verified by computation in
`dumas2017dual/dsdp/.scratch/probe_bob_charlie_hops.v` (compiles clean, Rocq
9.0.0). The methodology reproduces Alice's `2` when fed Alice's actual received
stream (the relays' bare-Enc head sends), so the `0`s are not an artifact of
mis-built streams. The asymmetry is intrinsic: relays send their secrets to
Alice as bare ciphertexts; Alice and the relays forward only homomorphic
combos. The secret a relay should not learn (v3 for Bob, nothing for v1) reaches
it, if at all, buried inside a combo, which the hop machinery does not reach.

### Consequence for Section 4 items 1-3 (view headlines)

`dsdp_indcpa_secrecy` IS generic over `dsdp_indcpa_experiment`, so a
`dsdp_experiment_bob`/`_charlie` record does instantiate. But with
`count_obs_hops = 0` the bound is `AdvantageE (real_game) (zero_game) Adv <= 0`,
and at zero hop sites `all_real gc` and `all_zero gc` are the same game_code
(`zero_hop_prefix 0 gc`; `dsdp_game_code.v:93-133`), so `real_game = zero_game`
and the advantage is identically `0`. The headline is provable but **vacuous**:
two identical games, no statement about whether the corrupt party learns v1/v3.
This fails the crypto vacuity test (numerical bound match is not statement
match).

## 3. Finding 2 — the guessing triangle is Alice-specific, not seed-generic

The fiber/output-leak stack (`dsdp_guess_fiber.v`, `dsdp_indcpa_advantage.v`) is
hard-wired to Alice, contradicting the plan's "parameterized by the seed only":

- `guess_fdist_success_le` (the `1/card_msg` fiber) bakes in the scalar-product
  output `S = u1*v1 + u2*v2 + u3*v3`, the four seed weights at `de_val_nth seed
  0..3` (= Alice's `u1,u2,u3,v1`), and `injective (fun v => w_u3 * v)`. Its core
  steps (`guess_cinde_V2`, `guess_V2_cond_Sout`, `dsdp_fiber_ring`) quantify over
  the third secret `v3` conditional on Alice's specific output map.
- `real_game_leak_S` / `zero_game_leak_S` / `dsdp_advantage_derived_leak_S` are
  built from `dsdp_alice_obs_leak_S_seeded`, hard-coded to Alice's trace; "S" is
  Alice's scalar-product return, and the challenge is fixed to Bob's `v2`
  (name 10).
- `indcpa_hopping/` contains zero Bob/Charlie machinery.

Even setting genericity aside, the fiber bound is unattainable for a relay: it
holds at the all-zero endpoint, where the hop ciphertexts are swapped to zero so
only the leaked output constrains the secret. A relay has no hops to swap, so the
combo that carries the secret (e.g. `a2` ⊇ `Enc(Charlie,v3)` for Bob) stays real
at the "all-zero" endpoint; a guesser reads the secret off that ciphertext in the
denotation, so `<= 1/card_msg` is false there.

## 4. Why Alice is special

DSDP's IND-CPA hopping reduction is an Alice-corruption tool by construction.
Only the aggregator receives every relay's secret as a top-level bare ciphertext
that the hybrid can swap to zero. A corrupted relay's secrecy of another relay's
input rests on a ciphertext **nested inside** a homomorphic combo it forwards;
the current trace/lowering pass (`game_of_trace`) leaks top-level hops directly
and never rebuilds a combo around a swapped sub-ciphertext.

## 5. What a sound Bob/Charlie reduction would actually require (not instantiation)

1. Extend the observation model so a ciphertext nested inside a forwarded combo
   (`HE_epow (HE_enc party (HE_var secret) _) _` inside `HE_emul`) can be marked a
   hop, and extend `game_of_trace`/the back-end ladder to swap a nested
   sub-ciphertext while re-deriving the surrounding combo. This is new front-end
   and back-end machinery, not a record instantiation.
2. Generalise the fiber/output-leak layer off Alice's fixed scalar-product seed:
   per-party output map, per-party challenge secret, per-party injectivity
   side-condition, and new `*_leak_S` games rooted in the relay's trace.

Both are substantial; neither is covered by the existing axes.

## 6. Recommendation

Leave the IND-CPA-dependent relay secrecy (V3 from Bob, V2 from Charlie) as
documented future work. Do not add `≤ 0` view headlines: an identically-zero
advantage between two equal games reads as a secrecy theorem while asserting
nothing, which is worse than the honest "unproven" status. If those results are
wanted, scope the two machinery extensions in Section 5 as their own project.

## 7. What was implemented instead (the sound core)

The audit isolated a sound, non-vacuous fragment the IND-CPA route obscured:
**Alice's input V1 occurs in no protocol message**, so it is information-
theoretically absent from both relays' full views (every view component is a
deterministic function of inputs disjoint from V1). This needs no encryption
assumption and is the IT-sound half of the originally deleted `bob_privacy_V1` /
`charlie_privacy_V1` (their V3/V2 siblings genuinely need IND-CPA and stay
deleted).

Added to `dsdp_main.v`, section `dsdp_relay_secrecy_v1`:

- `bob_privacy_V1`, `charlie_privacy_V1` — `H(V1 | RelayView) = log m > 0` for
  each corrupted relay's full real view (key, own input, forwarded/derived
  ciphertexts). [3-party]
- `BobView_indep_V1`, `CharlieView_indep_V1` — the view-independence, DERIVED
  (not assumed) from a single primitive `[%relay inputs] _|_ V1` via
  `inde_RV_comp`, so the headline is not "assume the conclusion": the only
  assumption is that V1 is sampled uniformly and independently of relay data,
  which is satisfiable precisely because V1 is absent from the view. The same
  derivation is impossible for V3-from-Bob / V2-from-Charlie, since those secrets
  ARE bijectively present in the views via `E' = EncFor`.

Engine: `inde_cond_entropy` (`H(X|View)=H(p_X)` under independence) +
`entropy_uniform`, mirroring the generic `relay_privacy_n`. Verified: full
`dsdp_main.v` compiles; `Print Assumptions` shows only the ambient `boolp`
axioms (no `E_enc_inde`, no admits). Blueprint coverage updated
(`blueprint-exclude.txt`, the convention for the sibling IT headlines).
