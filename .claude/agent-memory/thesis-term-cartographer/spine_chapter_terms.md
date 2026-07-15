---
name: spine-chapter-terms
description: Stable map of which thesis chapter first introduces each major recurring term; includes overloaded terms and code-term codebase refs.
metadata:
  type: project
---

Thesis root: /Users/cheng-huiweng/Projects/aplas2024-poster/thesis/
Map artifact: thesis/.thesis-review/term-map.json (rebuilt 2026-06-01, commit 66b3ecc)

## Chapter introduction spine (reading order)

- ch:introduction: SMC/MPC concept, pismc, ssprove (as concepts), coq
- ch:smc: semi-honest, simulation-based security, information-theoretic security, AHE/PHE/FHE, OTP, spp, dsdp
- ch:infotheo: conditional entropy, unpredictability entropy (+ Hunp code), fdist code, centropy_jcond_determined_fibers code
- ch:procalc: pi-calculus (concept only, no code terms)
- ch:rocq: mathcomp, hb
- ch:he: IND-CPA, Benaloh, Paillier (as concepts)
- ch:algebra: fiber/fiber-cardinality (OVERLOADED), Rouche-Capelli theorem, CRT
- ch:framework-overview: (no new terms)
- ch:interpreter: proc, data, rstep, rsteps, step, interp, step_sound, index_class, Inert, Disjoint, reduction_spec, rstep_disjoint, step_complete; input trace, trace map, leakage-free, fuel parameter, scalar_product_uncurry, scalar_product_is_leakage_freeP
- ch:phantom: sproc, erase, channels_dual, senv, native_compute, phantom-type index
- ch:ssprove: raw_code, AdvantageE
- ch:ahe: HETypes, isEncDec, isAHEnc, AHEncType
- ch:entropy-fiber: abstract_privacy_bridge
- ch:gameswap: Hunp_ge_bound

## Overloaded terms

- "fiber" has two senses in the corpus:
  1. Preimage: f^{-1}(c) as a set (ch:algebra through ch:fiber — algebraic sense)
  2. Fiber cardinality: |f^{-1}(c)| as a number (ch:fiber, ch:entropy-fiber, glossary entry — combinatorial/privacy sense)
  The glossary entry combines both under one description item. The term reviewer must verify that each use site is unambiguous or explicitly disambiguated.

## Key codebase refs

- proc: smc/smc_interpreter.v:42
- rstep: smc/smc_interpreter.v:117
- rsteps: smc/smc_interpreter.v:126
- step: smc/smc_interpreter.v:54
- interp: smc/smc_interpreter.v:80
- step_sound: smc/smc_interpreter_sound.v:808
- index_class: smc/smc_interpreter_sound.v:216
- Inert: smc/smc_interpreter_sound.v:217
- Disjoint: smc/smc_interpreter_sound.v:219
- reduction_spec: smc/smc_interpreter_sound.v:68
- rstep_disjoint: smc/smc_interpreter.v:186
- step_complete: smc/smc_interpreter.v:145
- sproc: smc/smc_session_types.v:234
- erase: smc/smc_session_types.v:631
- channels_dual: smc/smc_session_types.v:534
- senv: smc/smc_session_types.v:52
- scalar_product_uncurry: du2002/spp_proof.v:167
- scalar_product_is_leakage_freeP: du2002/spp_proof.v:458
- Hunp: dumas2017dual/dsdp/dsdp_security_indcpa_clone.v:891
- Hunp_ge_bound: dumas2017dual/dsdp/dsdp_security_indcpa_clone.v:899
- abstract_privacy_bridge: entropy_fiber/entropy_fiber.v
- centropy_jcond_determined_fibers: entropy_fiber/entropy_fiber.v
- fdist: upstream infotheo library (not in infotheo-itp) — ungrounded in our repos

**Why:** The term reviewer needs to know first-introduction locations to judge "explained before" claims. This spine is the oracle for that judgment and should be loaded at the start of any /thesis-review run.

**How to apply:** Load term-map.json from cache if no source files are newer; otherwise rebuild per term-cartography-protocol.md. The stable spine here can seed a fast rebuild by pre-populating the chapter-order and code-term codebase_ref fields.
