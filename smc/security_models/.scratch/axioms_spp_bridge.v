(* Axiom hygiene for smc/security_models/spp_bridge.v: every named result,
   nothing beyond the boolp trio.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/axioms_spp_bridge.v                     *)

Require Import spp_bridge.

Print Assumptions dist_of_RV_bind.
Print Assumptions spp_bob_factorization.
Print Assumptions spp_alice_share.
Print Assumptions spp_ideal_share_lawE.
Print Assumptions spp_y2_indep.
Print Assumptions spp_delivery_law_ok.
Print Assumptions spp_delivery_law.
