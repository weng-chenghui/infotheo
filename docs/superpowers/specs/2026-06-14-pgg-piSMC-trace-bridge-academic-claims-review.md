# PGG piSMC Trace Bridge — Academic Claims Review (reference)

Date: 2026-06-14
Companion to: `2026-06-14-pgg-piSMC-trace-bridge-design.md`
Status: reference only (no implementation action). Fact-checked against the codebase and the
referenced papers (`~/Projects/aplas2024-poster/feb12ITP2026/feb12ITP2026.tex`,
`~/Projects/aplas2024-poster/forteApr22/forteApr22.tex`).

---

## A. The review opinions (as received)

### 1. Valid Academic Claims (what you CAN claim after the plan is done)

Claims center on **operational correctness** and **symbolic execution**:

- **Executable Operational Semantics:** the PGG piSMC protocols are no longer abstract definitions
  or session-type-checked stubs; they have a concrete, executable operational semantics via the
  pi-calculus interpreter.
- **End-to-End Operational Correctness:** protocol correctness is derived directly from executed
  program traces. Specifically, the verifier's dynamically collected buffer during execution matches
  the input required by the abstract reconstruction lemma (`pgg_recon_endpoints`), ensuring the
  protocol computes the intended secret in practice.
- **Verification via Symbolic Execution:** the methodology verifies correctness even when
  cryptographic operations (permutation applications) are computationally opaque/stuck. Keeping
  trace endpoints symbolic proves control-flow and structural correctness algebraically without
  brute-force evaluation.
- **Generality of the Trace Bridge:** the interpreter-based correctness architecture (`pgg_run.v`)
  is generic enough to uniformly verify heterogeneous protocols (den Boer, Kim) and position-model
  instances (S5, S5x5).

### 2. Suspicious or False Claims (what you CANNOT claim)

- **"We verified the privacy of the protocol using execution traces." (FALSE):** in `forteApr22.tex`
  interpreter traces were lifted to random variables to prove information leakage freedom
  (H(X_i | View_j) = H(X_i)). This refactoring does **not** do that for piSMC. Privacy remains a
  distributional property over the abstract random cut, decoupled from the interpreter.
- **"The formalization verifies the protocol against malicious/active adversaries." (FALSE):** the
  interpreter traces model a deterministic, honest execution.
- **"The execution models the real randomized cut." (FALSE):** the dealer's word stays the identity
  and the permutation is not threaded; the trace only proves word-independent correctness.
- **"The interpreter yields a concretely executable program for deployment." (SUSPICIOUS):** because
  permutation applications do not reduce to numbers (`nat_of_ord` stays stuck), claiming a runnable
  software implementation (extraction to OCaml/Rust) is highly suspicious; it is symbolic execution
  for verification only.

### 3. Typical Claims in this Domain (context from the papers and famous formalizations)

For protocols like Shamir's Secret Sharing (SSS) and the reference SMC protocols, academics
typically claim **both** correctness and privacy in one framework.

- **Correctness (reconstructability):** any authorized subset reconstructs the secret; the trace
  bridge achieves the operational equivalent (verifier reconstructs from collected endpoints).
- **Privacy (t-privacy / perfect privacy):**
  - SSS t-privacy: any unauthorized subset (<= t) gives zero information; shown by uniform,
    secret-independent share distribution.
  - `feb12ITP2026.tex`: Peer-wise Perfect Privacy, via conditional entropy
    (H(V_2 | View_Alice) = H(V_2)); the output leaks joint info but individual secrets stay private.
  - `forteApr22.tex`: Information Leakage Freedom; observing the execution trace does not reduce
    uncertainty about secret inputs.

**Narrative summary:** distinguish this piSMC work from DSDP. For DSDP, interpreter traces gave
*both* correctness and privacy. For piSMC, this refactoring makes traces give *correctness*, but
*privacy* is handled by a separate, abstract mathematical layer (the random cut lemmas).

---

## B. Fact-check verdict (verified 2026-06-14)

**Overall: the review is accurate.** Every load-bearing claim checks out against the papers and the
code. One technical justification (2.4) is imprecise; the caution it raises is still correct.

| Review claim | Verdict | Evidence |
|---|---|---|
| 1.* valid claims (executable semantics, correctness-from-trace, symbolic execution, generic bridge) | TRUE | Match the spec §1/§4/§5; the verifier buffer equals `pgg_recon_endpoints`'s input (`pgg_sharing_framework.v:284`, `card_exchange_pismc.v:247`); symbolic-execution shape validated by today's experiments. |
| 2.1 piSMC does NOT prove privacy from traces; privacy is distributional over the cut | TRUE | Spec §2 non-goals; privacy lives in `den_boer_input_private : cond_mutual_info = 0` (`den_boer_encoding.v`) and `five_card_leakage.v`, decoupled from `interp`. |
| forteApr22 lifted traces to RVs for leakage freedom, H(X_i\|View_j)=H(X_i) | TRUE | `forteApr22.tex:61–74,116–117,168–177,196–211` ("input traces verified for correctness and information leakage freedom"; the VIEW equation "does not increase party j's knowledge of x_i"). |
| 2.2 honest, not active-adversary model | TRUE | `feb12ITP2026.tex:127` "honest parties"; VIEW is passive observation; the interpreter steps deterministically with no malicious deviation. |
| 2.3 execution does not model the real randomized cut (word stays identity; word-independent correctness only) | TRUE | Spec §2; correctness via `pgg_recon_monodromy_correct` holds for all P incl. identity. |
| 3 DSDP traces gave BOTH correctness and privacy | TRUE | `feb12ITP2026.tex:210` "From these collected traces ... construct each party's view and verify ... perfect privacy"; `dsdp_entropy_trace.v:20` `centropy_AliceTraces_AliceView : H(v\|AliceTraces)=H(v\|AliceView)`; correctness `dsdp_is_correct` (`dsdp_correctness.v:201`). |
| feb12ITP2026 = Peer-wise Perfect Privacy, Def H(X_i\|View_j)=H(X_i) | TRUE | `feb12ITP2026.tex:125–127,186–190,1241–1252` (Definition "Perfect Privacy": `HH{X_i}[View_j] = HH{X_i}`, i != j; section "Peer-wise Perfect Privacy"). |
| 2.4 not a deployment-runnable program (SUSPICIOUS) | CONCLUSION TRUE, JUSTIFICATION IMPRECISE | The spec is verification-only and makes no extraction/deployment claim, so the caution is right. But the stated reason ("`nat_of_ord` stays stuck => cannot extract") conflates **kernel `vm_compute` reduction** with **program extraction**: extraction erases opaque proofs and a perm finfun can extract to runnable OCaml. `vm_compute`-stuckness alone does not establish unextractability. Whether extraction yields a runnable artifact is untested and out of scope; do not claim it either way. |

### Note for the paper narrative

The single most important distinction to state explicitly, and it is correct: **DSDP's traces carry
both correctness and privacy; this piSMC bridge carries correctness only, with privacy in a separate
abstract layer (the random-cut lemmas).** Verified by feb12ITP2026 (trace -> view -> perfect
privacy) and forteApr22 (trace -> leakage freedom) on the DSDP side, versus this spec's explicit
non-goals plus the distributional `five_card_leakage` / `den_boer_input_private` on the piSMC side.
