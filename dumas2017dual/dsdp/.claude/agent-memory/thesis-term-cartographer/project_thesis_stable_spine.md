---
name: thesis-stable-spine
description: Which chapter first introduces each recurring term; code terms absent from the glossary; overloaded terms in the thesis corpus
metadata:
  type: project
---

## Chapter introduction spine (recurring terms)

| Term | First chapter | Kind |
|------|--------------|------|
| SMC/MPC | ch:introduction | concept |
| pismc, ssprove-framework, coq | ch:introduction | concept |
| semi-honest, simulation-based security, IT-security | ch:smc | concept |
| AHE/MHE/PHE/FHE, OTP, spp, dsdp | ch:smc | concept |
| conditional entropy, unpredictability entropy, fdist | ch:infotheo | concept/code |
| centropy_jcond_determined_fibers | ch:infotheo | code |
| fiber, Rouche-Capelli, CRT | ch:algebra | concept |
| computational indistinguishability, IND-CPA | ch:he | concept |
| proc, data, Init/Send/Recv/Ret/Finish/Fail, rstep/rsteps, step, interp | ch:interpreter | code |
| input trace, trace map, leakage-free, fuel parameter | ch:interpreter | concept |
| step_sound, index_class, Inert/Disjoint, reduction_spec, rstep_disjoint, step_complete | ch:interpreter | code |
| scalar_product_uncurry, scalar_product_is_leakage_freeP | ch:interpreter | code |
| phantom-type index, sproc, senv, erase, channels_dual, native_compute, fuel_suffices, terminated_nonfail_senv_zero | ch:phantom | concept/code |
| package, raw_code, code, sequential composition, linking, sub-distribution semantics | ch:ssprove | concept/code |
| advantage, indistinguishability, game hopping, perfect hop, assumption-bounded hop | ch:ssprove | concept |
| game chain, advantage linking, front-end package, shim, reduction, relative monad, state-separating | ch:ssprove | concept |
| code_of_send, Advantage_triangle, Advantage_link, link_assoc | ch:ssprove | code |
| view-as-input adversary model, Run, code_of_proc, game_real | ch:gameswap | concept/code |
| HETypes, isEncDec, isAHEnc, AHEncType | ch:ahe | code |
| E_enc_ce_contract (ciphertext contraction) | ch:ahe | code |
| perfect privacy, abstract_privacy_bridge | ch:entropy-fiber | concept/code |
| Pr_dsdp_sol_uniform, Pr_dsdp_sol_uniform_ring, game_enc_zero, dsdp_alice_secrecy, Hunp_ge_bound | ch:dsdp | code |

## Code terms never reaching the glossary (stable gap list)

Init, Send, Recv, Ret, Finish, Fail, step_sound, index_class, Inert, Disjoint,
reduction_spec, rstep_disjoint, step_complete, fuel_suffices, terminated_nonfail_senv_zero,
native_compute, Hunp, HETypes, isEncDec, isAHEnc, AHEncType, E_enc_ce_contract,
raw_code, code, code_of_send, code_of_proc, Advantage_triangle, Advantage_link,
link_assoc, Run, game_real, game_enc_zero, dsdp_alice_secrecy,
abstract_privacy_bridge, centropy_jcond_determined_fibers,
Pr_dsdp_sol_uniform, Pr_dsdp_sol_uniform_ring, Hunp_ge_bound,
scalar_product_uncurry, scalar_product_is_leakage_freeP

## Overloaded terms

| Term | Senses |
|------|--------|
| fiber | (1) preimage set f^{-1}(c) (ch:algebra, ch:fiber); (2) cardinality |f^{-1}(c)| (ch:fiber, ch:entropy-fiber, glossary) |
| linking | (1) general associative composition of packages in SSProve (ch:ssprove); (2) advantage linking identity (ch:ssprove sec:ssprove:reduction) |

**Why:** These overloads cause G7-type term-grounding issues: reviewer cannot assume the sense without looking at the chapter.
**How to apply:** Flag both senses whenever either "fiber" or "linking" appears in a review; check that the local context disambiguates.
