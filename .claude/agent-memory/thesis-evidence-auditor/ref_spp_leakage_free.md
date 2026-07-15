---
name: ref_spp_leakage_free
description: Verification record for scalar_product_is_leakage_freeP in du2002/spp_proof.v — two-sided, Qed-closed
metadata:
  type: reference
---

`Theorem scalar_product_is_leakage_freeP` at du2002/spp_proof.v:458, Qed at line 466.

Proof body:
  split.
  - rewrite alice_traces_entropy. exact: proof_alice.
  - rewrite bob_traces_entropy.  exact: proof_bob.

Confirms the two-sided claim in chapters/interpreter.tex lines 235-240: Alice-side and Bob-side
conditional entropy equalities are both established. No Admitted, no external Axiom.

**Why:** Cited in the "From Trace to Distribution" section; stable as of 2026-06-01.
