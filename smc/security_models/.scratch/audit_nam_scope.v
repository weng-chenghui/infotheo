(* Naming-audit scope check: after the UNION of the imports the eight
   permanent files plan to make, Locate every planned top-level
   identifier.  Any output line other than "No object of suffix ..."
   is a pre-existing referent the new name would shadow or sit beside.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/audit_nam_scope.v                *)
From mathcomp Require Import all_ssreflect all_algebra finalg reals lra.
Require Import realType_ext realType_ln fdist proba jfdist_cond entropy.
Require Import graphoid.

Locate stoch. Locate dirac. Locate stoch_comp. Locate stoch_compE.
Locate stoch_compA. Locate stoch_comp_idl. Locate stoch_comp_idr.
Locate dirac_comp. Locate stoch_comp_dirac_fdistmap. Locate eq_fdistmap.
Locate fdistmap_cst. Locate fdistmap_cst_eq. Locate tensor. Locate tensorE.
Locate tensor_fdist1. Locate tensor_dirac_l.
Locate statdist. Locate statdist_ge0. Locate statdist_sym.
Locate statdist_triangle. Locate statdist_eq0. Locate tester. Locate accept.
Locate adv. Locate class_adv. Locate class_adv_ge0. Locate class_adv_sym.
Locate class_advxx. Locate class_adv_triangle. Locate class_adv_sub.
Locate class_adv_all. Locate statdist_test_le. Locate statdist_test_max.
Locate draw. Locate view_law. Locate view_lawE. Locate allow. Locate allowE.
Locate f_a. Locate simulator. Locate sim_view. Locate perfect_privacy.
Locate eps_privacy. Locate factors_through. Locate insecurity.
Locate real_route_f. Locate ideal_route_f. Locate test_adv.
Locate perfect_privacy_testP. Locate eps_privacy_testP. Locate hybrid_bound.
Locate x_all. Locate s_all. Locate y_all. Locate exec_ctx. Locate out_all.
Locate view_space. Locate x_adv. Locate y_adv. Locate proj_adv.
Locate proj_x_adv. Locate proj_y_adv. Locate view. Locate out_adv.
Locate in_adv. Locate readoff_square. Locate in_adv_records.
Locate reveals_output. Locate reveal_chain. Locate kernel_data.
Locate party_to_kernel.
Locate triangle_cinde. Locate cinde_centropy_eq. Locate view_rv.
Locate input_rv. Locate allow_rv.
Locate predictor. Locate pred_success. Locate ideal_guess.
Locate unp_entropy_ge.
Locate dirac_shiftE. Locate mask_chan. Locate mask_chanE.
Locate mask_chan_uniform_hides. Locate mask_chan_biased_leaks.
Locate biased3. Locate unif3. Locate draw_add_mask.
Locate cond_law_to_bind. Locate bob_simulator. Locate var_dist.
Locate sum_diff_complement. Locate sum_diff_le. Locate statdist_pos_part.
