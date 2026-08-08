
(* -------------------------------------------------------------------------- *)
(* Probe-only checks, spec sections 6.5 and 6.6.                              *)
(* -------------------------------------------------------------------------- *)

(* 6.5: the two chosen representatives are four-subsets of the projective
   line, and they carry opposite classifier values. *)
Lemma rep_card_class :
  [/\ #|list_to_set [:: 0; 1; 2; 4]| = 4,
      #|list_to_set [:: 0; 1; 2; 3]| = 4,
      subset_class (list_to_set [:: 0; 1; 2; 4]) = true &
      subset_class (list_to_set [:: 0; 1; 2; 3]) = false].
Proof.
have A1 : asc4 [:: 0; 1; 2; 4] by vm_compute.
have A2 : asc4 [:: 0; 1; 2; 3] by vm_compute.
split.
- exact: (card_list_to_set _ A1).
- exact: (card_list_to_set _ A2).
- by rewrite (subset_class_list_to_set _ A1); vm_compute.
- by rewrite (subset_class_list_to_set _ A2); vm_compute.
Qed.

(* 6.6, at the level of the theorem rather than the certificate: the two
   representatives are not shuffle-related.  The forward implication of
   subset_class_orbit is therefore not vacuous, and the two fibers are two
   distinct orbits rather than one. *)
Lemma orbit_mutation_check :
  ~ (exists g : pgg_gT pgl27_M,
       g \in pgg_G pgl27_M /\
       list_to_set [:: 0; 1; 2; 4] = g @: list_to_set [:: 0; 1; 2; 3]).
Proof.
case=> g [gG Heq].
have A1 : asc4 [:: 0; 1; 2; 4] by vm_compute.
have A2 : asc4 [:: 0; 1; 2; 3] by vm_compute.
have Hinv := subset_class_invariant g (list_to_set [:: 0; 1; 2; 3]) gG.
rewrite -Heq (subset_class_list_to_set _ A1) in Hinv.
rewrite (subset_class_list_to_set _ A2) in Hinv.
by move: Hinv; vm_compute.
Qed.

Print Assumptions subset_class_invariant.
Print Assumptions subset_class_orbit.
Print Assumptions subset_class_orbitE.
Print Assumptions orbit_mutation_check.
