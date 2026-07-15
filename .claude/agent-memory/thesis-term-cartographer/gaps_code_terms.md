---
name: gaps-code-terms
description: Code and concept terms introduced in thesis chapters but absent from backmatter/list-of-terms.tex as of 2026-06-01.
metadata:
  type: project
---

As of 2026-06-01 (map commit 66b3ecc), the following terms appear prominently in the thesis with \coqin{} or \coqin{native\_compute} markup but are NOT listed in backmatter/list-of-terms.tex:

## From ch:interpreter (§3 soundness proof machinery)
- step_sound (smc/smc_interpreter_sound.v:808)
- index_class (smc/smc_interpreter_sound.v:216)
- Inert (smc/smc_interpreter_sound.v:217)
- Disjoint (smc/smc_interpreter_sound.v:219)
- reduction_spec (smc/smc_interpreter_sound.v:68)
- rstep_disjoint (smc/smc_interpreter.v:186)
- step_complete (smc/smc_interpreter.v:145)
- scalar_product_uncurry (du2002/spp_proof.v:167)
- scalar_product_is_leakage_freeP (du2002/spp_proof.v:458)

## From ch:phantom
- native_compute (Rocq built-in tactic; no codebase_ref)
- phantom-type index (concept, no code binding)

## From ch:infotheo
- Hunp (dumas2017dual/dsdp/dsdp_security_indcpa_clone.v:891)
- centropy_jcond_determined_fibers (entropy_fiber/entropy_fiber.v)

## From ch:ahe
- HETypes (homomorphic_encryption/he_types.v)
- isEncDec (homomorphic_encryption/enc_dec.v)
- isAHEnc (homomorphic_encryption/ahe_enc.v)
- AHEncType (homomorphic_encryption/ahe_enc.v)

## From ch:ssprove
- raw_code (SSProve upstream; no codebase_ref in infotheo-itp)

## From ch:entropy-fiber
- abstract_privacy_bridge (entropy_fiber/entropy_fiber.v)

## From ch:gameswap
- Hunp_ge_bound (dumas2017dual/dsdp/dsdp_security_indcpa_clone.v:899)

## Ungrounded (gloss cannot be backed by infotheo-itp grep)
- fdist: lives in the upstream infotheo library (fdist.v), not in infotheo-itp repo. Gloss derived from information-theory.tex prose only. Mark as ungrounded.

**Why:** The gaps list is the primary output the thesis-review Phase 2 report surfaces and the Phase 3 gated fix may address. Keeping it stable across runs lets reviewers track which terms were fixed.

**How to apply:** On each rebuild, reconcile this list against list-of-terms.tex to detect entries that were added (remove from gaps) or removed (add back).
