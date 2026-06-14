# Memo: PGG piSMC trace bridge, academic claims

Datetime: 2026-06-14T03:13:46Z
Author: trace-bridge implementation session
Scope: claims defensible after commits 650de98..47d6805 (every theorem Qed, "Closed under the global context")
Related: 2026-06-14-pgg-piSMC-trace-bridge-design.md (section 8), 2026-06-14-pgg-piSMC-trace-bridge-academic-claims-review.md

## Can claim

1. Executable operational semantics for the shared protocol. The PGG piSMC programs are no longer abstract definitions or session-typed stubs. For all four instances the dealer, players, and verifier program runs to completion through the interpreter. Evidence: den_boer_run_terminates, kim_run_terminates, s5_run_terminates, s5x5_run_terminates, each of the form (run_interp h procs).1 = nseq k Finish.

2. End-to-end operational correctness read off the executed trace. The secret reconstructed from the verifier's dynamically collected endpoints equals the intended value, for every instance. den Boer and Kim recover a && b. S5 and S5x5 recover the dealt position. Evidence: den_boer_run_recovers, kim_run_recovers, s5_run_recovers, s5x5_run_recovers, each connecting run_interp output to reconstruction.

3. One generic protocol, four monodromy groups. A single group-agnostic module (pgg_run.v: dealer_with_input_encoding, endpoints_of_trace) is instantiated by C5 (den Boer, Kim), S5, and S5xS5 with no change to the protocol layer. This realizes the same-protocol, different-permutation design.

4. Verification by symbolic execution. Correctness holds even though permutation application and decoding are computationally opaque under kernel reduction. The proofs keep trace endpoints symbolic and close algebraically, so the result does not depend on brute-force evaluation. Evidence: the abstract-leaf helper lemmas (den_boer_verifier_endpoints and the s5, s5x5 analogs).

5. Fully axiom-free. Every executed-trace correctness theorem is "Closed under the global context," using no axioms, not even the pre-existing group-order or algebraic-geometry axioms that other parts of the development carry.

6. A working MPC input mechanism for the heterogeneous case. den Boer and Kim feed committed party inputs (Alice and Bob each commit a bit) into an input-derived layout via the InputEncoding component, and the executed run recovers the AND. The position-model instances feed a position secret through the threshold scheme. Both route through the identical executed bridge.

## Cannot claim

7. Privacy from the execution traces. Unlike the DSDP line, these traces are not lifted to random variables. Privacy remains a distributional property over the random cut, in a separate abstract layer.

8. Security against active or malicious adversaries. The interpreter models deterministic honest execution only.

9. That the run models the real randomized cut. The executed cut is the identity. Correctness is word-independent, so the run proves correctness, not the effect of the shuffle.

10. A deployment-runnable extracted program. Untested and out of scope. Note that vm_compute being stuck on permutation values does not by itself settle extractability either way, so do not claim it is unextractable on those grounds.

## One-line framing for a paper

DSDP traces carried both correctness and privacy. This work makes the PGG piSMC traces carry correctness for four distinct permutation-group instances under one generic protocol, axiom-free, with privacy left to a separate abstract layer.
