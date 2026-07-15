---
name: reference_indcpa_ror_axiom
description: enc_ind_cpa_real_or_zero is an Axiom (line 262) in indcpa_ror.v; epsilon_cpa is a Parameter (line 242)
metadata:
  type: reference
---

File: /Users/cheng-huiweng/Projects/coq/infotheo-itp/homomorphic_encryption/indcpa_ror.v

- `epsilon_cpa` declared as `Parameter` (line 242) — abstract real security parameter
- `enc_ind_cpa_real_or_zero` declared as `Axiom` (line 262) — the IND-CPA assumption

The thesis sidenote (dsdp.tex:652-654) calls it "Assumption enc_ind_cpa_real_or_zero" which is
accurate. The thesis does NOT claim this is proved — it correctly frames it as a hypothesis/assumption.
No ADMITTED overclaim issue here.

The dsdp_security_indcpa.v imports this as:
  `Require Import homomorphic_encryption indcpa_ror.`
(flat module names, no path prefix in the import).

The cited path in the thesis sidenote `homomorphic_encryption/indcpa_ror.v` is correct as a
relative file path from the infotheo-itp root, matching the _CoqProject entry.
