# pgl27 claim boundary (2026-07-13)

Rule: pgl27 is closed when every prose sentence about it maps either
to a Qed theorem in a committed file or to an explicitly disclosed
non-claim below. New work enters only when a new prose claim needs
it; each such claim opens its own spec with its own finite matrix.

## Claim matrix (exact-shuffle model; all Qed)

Group and orbit (zero axioms): pgl27_3transitive, pgl27_rho_im,
pgl27_pgl2_order (pgl27_group.v); orbit_class_split,
orbit_class_split_complement, orbit_class_invariant, deck_stable,
orbit_encodeK, orbit_encode_deck, orbit_populated (pgl27_orbit.v).

Correctness: pgl27_run_recovers, pgl27_endpoints (pgl27_run.v);
pgl27_run_recovers_class, pgl27_player_trace_full,
pgl27_alldecks_trace_full (pgl27_trace.v; the class-recovery and
trace-fullness results are zero-axiom).

Recovery sharpness (zero axioms): pgl27_seven_reveal_determines,
pgl27_seven_reveal_class, pgl27_six_reveal_ambiguous,
pgl27_reveal_ambiguous, pgl27_2transitive (pgl27_recovery.v). The
ramp: private up to three revealed cards, leaking from four,
ambiguous through six, determined at seven; the implemented decoder
reads all eight.

View privacy (boolp trio only): pgl27_view_indep,
pgl27_view_leakage_le, pgl27_view_dep_k4, pgl27_view_leak_k4,
pgl27_view_indep_alldecks, pgl27_view_indep_deck,
pgl27_view_indep_deck_prior, pgl27_deck_marginal (pgl27_secrecy.v).

Trace privacy (boolp trio only): pgl27_trace_secrecy,
pgl27_coalition_trace_secrecy, pgl27_alldecks_trace_secrecy,
pgl27_alldecks_coalition_secrecy, pgl27_deck_trace_secrecy,
pgl27_deck_coalition_secrecy (pgl27_trace.v).

Scheme and profile: pgl27_private, orbit_recon_invariant
(pgl27_scheme.v); the exact eps = 0 SecurityWitness
(pgl27_profile.v; see disclosure 5).

Realistic shuffle (boolp trio only unless noted): pgl27_word_mixing
(the 200-letter word law is within 2^-40 of the uniform shuffle in
variation distance), pgl27_endpoint_mixing (each single-card
marginal), pgl27_joint_mixing (the joint secret-and-shuffle law, any
prior); pgl27_gen5_eq and pgl27_card (|G| = 336) — the latter two
zero-axiom (pgl27_mixing.v).

## Disclosed non-claims

1. The verifier learns the secret (endpoints flow to it by design);
   post-reveal knowledge is out of the model (file headers say so).
2. Passive (honest-but-curious) adversaries only; no active
   deviation, no composition across executions.
3. Quantitative leakage at 4..6 revealed cards is not computed (only
   positivity at 4, monotonicity, and ambiguity through 6).
4. The all-decks dealer results are claimed for pgl27 only, not
   framework-wide (sibling instances keep representative samplers).
5. The framework SecurityWitness eps = 0 measures the single-card
   marginal; coalition-level exactness is carried by the view and
   trace theorems, not by the witness.
6. The realistic-shuffle claims hold at L = 200 letters with
   variation distance at most 2^-40 (group law, single-card marginal
   and the joint secret-and-shuffle law); pointwise approximate
   independence constants (the 2-epsilon form) are not stated.

## Trust base

boolp trio (propositional_extensionality,
functional_extensionality_dep, constructive_indefinite_description)
via infotheo probability; the Rocq kernel including the vm_compute
virtual machine. The group, orbit and recovery rows are closed under
the global context (no axioms at all).
