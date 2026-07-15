(* Fixture: triggers H002. Do NOT compile. *)

(** template_helper — stacked-slot template form.
    Kind: helper.
    Why: needed by chain_ge0.
    Used by: chain_ge0. *)
Lemma template_helper : 0 < 1.
Proof. by []. Qed.

(* Closes the gap for the U3 task in
   ~/.claude/plans/sprightly-finding-robin.md (line 142). *)
Lemma stale_crossref : forall n : nat, 0 < n.+1.
Proof. by []. Qed.

(* For every natural number n, zero is less than n plus one. *)
Lemma type_restatement : forall n : nat, 0 < n + 1.
Proof. by case=> [|n']; rewrite ?ltn0Sn. Qed.

(** over_length_helper — paraphrases the predicate.
    Kind: helper.
    Why: needed for closing the base case in a longer chain
    of arithmetic reasoning leading to the headline result.
    Used by: chain_ge0_strict.
    Notes: this fixture exceeds the 5-line budget. *)
Lemma over_length_helper : 0 < 5.
Proof. by []. Qed.

(* The proof reduces directly to enum_rankK. *)
Lemma mechanism_only_bad : forall n : nat, n = n.
Proof. by []. Qed.

(* Strict positivity by case analysis on n; obligations close trivially. *)
Lemma case_analysis_bad : forall n : nat, 0 < n.+1.
Proof. by []. Qed.
