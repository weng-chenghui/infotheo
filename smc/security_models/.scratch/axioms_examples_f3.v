(* Axiom hygiene for smc/security_models/examples_f3.v: every named result,
   nothing beyond the boolp trio.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/axioms_examples_f3.v                    *)

Require Import examples_f3.

Print Assumptions card_F3.
Print Assumptions mask_chanE.
Print Assumptions mask_chan_unif3.
Print Assumptions mask_chan_uniform_hides.
Print Assumptions biased3_0.
Print Assumptions biased3_1.
Print Assumptions biased3_2.
Print Assumptions mask_chan_biased_leaks.
Print Assumptions biased_uniform_eps.
Print Assumptions statdist_mask_chan.
Print Assumptions dirac_shiftE.
Print Assumptions draw_add_mask.

Print Assumptions masking_verdicts.functionality_compat.
Print Assumptions masking_verdicts.run_correct.
Print Assumptions masking_verdicts.ideal_route.
Print Assumptions masking_verdicts.real_route.
Print Assumptions masking_verdicts.allow_const.
Print Assumptions masking_verdicts.view_law_maskE.
Print Assumptions masking_verdicts.sim_view_maskE.
Print Assumptions masking_verdicts.perfect_privacy_uniform.
Print Assumptions masking_verdicts.eps_privacy_biased.
Print Assumptions masking_verdicts.view_law_plainE.
Print Assumptions masking_verdicts.insecurity_no_mask.

Print Assumptions coin_leak.exec_lawE.
Print Assumptions coin_leak.pfwd1_ord1.
Print Assumptions coin_leak.pfwd1_view_input.
Print Assumptions coin_leak.pfwd1_view_allow.
Print Assumptions coin_leak.pfwd1_honest_allow.
Print Assumptions coin_leak.pfwd1_view_honest_allow.
Print Assumptions coin_leak.view_only_triangle.
Print Assumptions coin_leak.not_cinde_honest.
Print Assumptions coin_leak.centropy_view_honest0.
Print Assumptions coin_leak.honest_lawE.
Print Assumptions coin_leak.joint_honest_allow.
Print Assumptions coin_leak.centropy_honest_allow.
Print Assumptions coin_leak.centropy_view_honest_neq.
