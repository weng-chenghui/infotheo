(* Probe A for docs/superpowers/requests/                                     *)
(*   2026-08-08-pgl27-orbit-split-ROCQ-formalization-spec.md                  *)
(*                                                                            *)
(* Tests the one claim with no precedent in the repo: that a fueled BFS over  *)
(* sorted four-code-lists, started at one representative per Boolean fiber,   *)
(* reaches every four-subset of that fiber, and that a re-verifying checker   *)
(* discharges by vm_compute.                                                  *)
(*                                                                            *)
(* Standalone on purpose: it duplicates only the nat-level arithmetic of      *)
(* pgg-smc/instances/pgl27/pgl27_orbit.v, so the risky computation is timed   *)
(* without the mathcomp finset/fingroup/action load.                          *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import path div.

(* -------------------------------------------------------------------------- *)
(* Copied verbatim from pgl27_orbit.v: nat-mod-7 cross-ratio and the verdict. *)
(* -------------------------------------------------------------------------- *)

Definition inv7 (a : nat) : nat := nth 0 [:: 0; 1; 4; 5; 2; 3; 6] a.
Definition sub7 (a b : nat) : nat := (a + 7 - b) %% 7.
Definition mul7 (a b : nat) : nat := (a * b) %% 7.
Definition div7 (a b : nat) : nat := mul7 a (inv7 b).

Definition crn (x1 x2 x3 x4 : nat) : nat :=
  if x1 == 7 then div7 (sub7 x2 x4) (sub7 x2 x3)
  else if x2 == 7 then div7 (sub7 x1 x3) (sub7 x1 x4)
  else if x3 == 7 then div7 (sub7 x2 x4) (sub7 x1 x4)
  else if x4 == 7 then div7 (sub7 x1 x3) (sub7 x2 x3)
  else div7 (mul7 (sub7 x1 x3) (sub7 x2 x4)) (mul7 (sub7 x1 x4) (sub7 x2 x3)).

Definition equianharmonic (l : nat) : bool := (l == 3) || (l == 5).

Definition nclass (L : seq nat) : bool :=
  match sort leq L with
  | [:: a; b; c; d] => equianharmonic (crn a b c d)
  | _ => false
  end.

Definition trn (a : nat) : nat := nth 0 [:: 1; 2; 3; 4; 5; 6; 0; 7] a.
Definition scn (a : nat) : nat := nth 0 [:: 0; 3; 6; 2; 5; 1; 4; 7] a.
Definition invn (a : nat) : nat := nth 0 [:: 7; 6; 3; 2; 5; 4; 1; 0] a.

Definition sorted4 : seq (seq nat) :=
  flatten [seq flatten [seq flatten [seq [seq [:: a; b; c; d]
    | d <- iota c.+1 (8 - c.+1)]
    | c <- iota b.+1 (8 - b.+1)]
    | b <- iota a.+1 (8 - a.+1)]
    | a <- iota 0 8].

(* -------------------------------------------------------------------------- *)
(* New: the word layer at the level of four-subsets.                          *)
(* -------------------------------------------------------------------------- *)

(* Nat-level action of generator i on a code. *)
Definition wgenn (i : nat) : nat -> nat :=
  if i == 0 then trn else if i == 1 then scn else invn.

(* Application of a word (left-to-right) to a single code. *)
Definition papply (w : seq nat) (a : nat) : nat :=
  foldl (fun x i => wgenn i x) a w.

(* One generator step on a four-subset, kept in ascending canonical form. *)
Definition sstep (i : nat) (L : seq nat) : seq nat :=
  sort leq (map (wgenn i) L).

(* Fueled BFS over four-subsets, keeping one carrying word per reached set. *)
Fixpoint set_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
    seq (seq nat * seq nat) :=
  match fuel with
  | 0 => seen
  | S f =>
    let nxt := flatten
      [seq [seq (sstep i Lw.1, rcons Lw.2 i)
             | i <- [:: 0; 1; 2]] | Lw <- seen] in
    let add := foldl (fun acc Lw =>
      if has (fun sw : seq nat * seq nat => sw.1 == Lw.1) (seen ++ acc)
      then acc else rcons acc Lw) [::] nxt in
    if size add == 0 then seen else set_bfs f (seen ++ add)
  end.

(* The two fiber representatives: heart sets of orbit_encode true / false. *)
Definition rep_true : seq nat := [:: 0; 1; 2; 4].
Definition rep_false : seq nat := [:: 0; 1; 2; 3].

Definition set_table (L0 : seq nat) : seq (seq nat * seq nat) :=
  set_bfs 12 [:: (L0, [::])].

(* Every ascending four-list of verdict b carries a word from L0 to it.
   The check re-verifies each word from scratch, so a BFS bookkeeping bug
   cannot make this true. *)
Definition set_table_ok (L0 : seq nat) (b : bool) : bool :=
  all (fun L => (nclass L == b) ==>
         has (fun sw : seq nat * seq nat =>
                sort leq (map (papply sw.2) L0) == L) (set_table L0))
      sorted4.

(* -------------------------------------------------------------------------- *)
(* Spec section 6.5: the representatives have four elements and opposite      *)
(* classifier values.                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma rep_true_size : size rep_true = 4. Proof. by vm_compute. Qed.
Lemma rep_false_size : size rep_false = 4. Proof. by vm_compute. Qed.
Lemma rep_true_class : nclass rep_true = true. Proof. by vm_compute. Qed.
Lemma rep_false_class : nclass rep_false = false. Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* The certificate itself.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma set_table_okT : set_table_ok rep_true true. Proof. by vm_compute. Qed.
Lemma set_table_okF : set_table_ok rep_false false. Proof. by vm_compute. Qed.

(* The BFS saturates each fiber, matching orbit_class_split (28) and
   orbit_class_split_complement (42). *)
Lemma set_table_sizeT : size (set_table rep_true) = 28.
Proof. by vm_compute. Qed.
Lemma set_table_sizeF : size (set_table rep_false) = 42.
Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* Spec section 6.6: mutation checks.  Swapping the classifier value must     *)
(* break the reachability claim, otherwise the certificate is vacuous.        *)
(* -------------------------------------------------------------------------- *)

Lemma mutate_true_fiber : set_table_ok rep_true false = false.
Proof. by vm_compute. Qed.
Lemma mutate_false_fiber : set_table_ok rep_false true = false.
Proof. by vm_compute. Qed.

(* A second mutation: starting the BFS at the wrong representative must fail
   on its own fiber. *)
Lemma mutate_swap_reps : set_table_ok rep_false true = false.
Proof. by vm_compute. Qed.

Print Assumptions set_table_okT.
Print Assumptions set_table_okF.
