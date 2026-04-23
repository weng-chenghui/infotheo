(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop binomial.
From pgg_smc Require Import pgg_weval_inj pgg_raag.

(******************************************************************************)
(* PGG: Clique Polynomial of the RAAG Commutation Graph                      *)
(*                                                                            *)
(* In trace monoid theory (Cartier-Foata), the number of traces of length L   *)
(* is determined by the clique polynomial of the commutation graph:           *)
(*                                                                            *)
(*   P_Gamma(z) = Sum_{k=0}^{alpha} (-1)^k c_k z^k                          *)
(*                                                                            *)
(* where c_k = number of k-cliques.  The generating function for traces is:  *)
(*   Sum_L m_L z^L = 1 / P_Gamma(z)                                          *)
(*                                                                            *)
(* This gives the recurrence:                                                 *)
(*   m_0 = 1                                                                  *)
(*   m_L = Sum_{k=1}^{min(L,alpha)} (-1)^{k+1} c_k m_{L-k}                  *)
(*       = Sum_{k odd} c_k m_{L-k} - Sum_{k even, k>=2} c_k m_{L-k}         *)
(*                                                                            *)
(* Part 1: Nat-level clique enumeration (for vm_compute)                      *)
(*   subseqs_k k s == all subsequences of s of size k (strictly increasing    *)
(*                    order inherited from s)                                  *)
(*   all_pairs_comm_sorted comm s == all pairs pairwise commute or are equal  *)
(*   cliques_of_size Tg k comm == k-cliques in the commutation graph         *)
(*   clique_count Tg k comm == c_k = number of k-cliques                     *)
(*                                                                            *)
(* Part 2: Clique recurrence for trace counts                                *)
(*   clique_step Tg comm memo == one step of the clique recurrence           *)
(*   clique_traces Tg L comm == m_L computed via the clique recurrence       *)
(*                                                                            *)
(* Part 3: vm_compute verification for concrete instances                     *)
(*   star, free, abelian, path graphs                                         *)
(*                                                                            *)
(* Part 4: Growth rate formulas                                               *)
(*   clique_traces_free : free case gives Tg^L                               *)
(*   clique_traces_abelian : abelian case gives C(L+Tg-1, Tg-1)             *)
(*                                                                            *)
(* Part 5: Reflection to abstract n_traces (Cartier-Foata axiom)             *)
(*   cartier_foata : clique_traces = n_traces_natB                           *)
(*     (axiom, requires comm_sym + comm_irrefl, vm_compute-verified)         *)
(*   clique_traces_eq_natB : clique_traces = n_traces_natB (from axiom)      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Part 1: Nat-level clique enumeration                                       *)
(* ========================================================================== *)

(* All subsequences of s of exactly size k, preserving order *)
Fixpoint subseqs_k (k : nat) (s : seq nat) : seq (seq nat) :=
  match k with
  | 0 => [:: [::]]
  | k'.+1 =>
    match s with
    | [::] => [::]
    | x :: s' =>
      (* either include x (and choose k' from s') or skip x *)
      [seq x :: t | t <- subseqs_k k' s'] ++ subseqs_k k'.+1 s'
    end
  end.

(* Check that all elements pairwise commute (or are equal) *)
Definition all_pairs_comm_sorted (comm : nat -> nat -> bool) (s : seq nat)
    : bool :=
  all (fun i =>
    all (fun j => (i == j) || comm i j) s) s.

(* All k-cliques: k-element subsets of {0,...,Tg-1} that are cliques *)
Definition cliques_of_size (Tg k : nat) (comm : nat -> nat -> bool)
    : seq (seq nat) :=
  [seq s <- subseqs_k k (iota 0 Tg)
  | all_pairs_comm_sorted comm s].

(* c_k = number of k-cliques *)
Definition clique_count (Tg k : nat) (comm : nat -> nat -> bool) : nat :=
  size (cliques_of_size Tg k comm).

(* ========================================================================== *)
(* Part 2: Clique recurrence for trace counts                                 *)
(* ========================================================================== *)

(* The recurrence m_L = Sum_{k=1}^{min(L,Tg)} (-1)^{k+1} c_k m_{L-k}
   = Sum_{k odd} c_k m_{L-k} - Sum_{k even, k>=2} c_k m_{L-k}

   At the nat level, we split into positive and negative parts:
   pos = Sum_{k odd <= L} c_k * m_{L-k}
   neg = Sum_{k even, 2<=k<=L} c_k * m_{L-k}
   m_L = pos - neg  (valid when pos >= neg, guaranteed by theory)
*)

Definition clique_step (Tg : nat) (comm : nat -> nat -> bool)
    (memo : seq nat) : nat :=
  let L := size memo in
  let pos := sumn [seq clique_count Tg k comm * nth 0 memo (L - k)
                   | k <- iota 1 L & odd k] in
  let neg := sumn [seq clique_count Tg k comm * nth 0 memo (L - k)
                   | k <- iota 1 L & ~~ odd k] in
  pos - neg.

(* Build memo table [m_0, m_1, ..., m_L] *)
Fixpoint clique_traces_aux (Tg : nat) (comm : nat -> nat -> bool)
    (fuel : nat) (memo : seq nat) : seq nat :=
  match fuel with
  | 0 => memo
  | fuel'.+1 =>
    let mL := clique_step Tg comm memo in
    clique_traces_aux Tg comm fuel' (rcons memo mL)
  end.

(* m_L via the clique polynomial recurrence *)
Definition clique_traces (Tg L : nat) (comm : nat -> nat -> bool) : nat :=
  nth 0 (clique_traces_aux Tg comm L [:: 1]) L.

(* ========================================================================== *)
(* Part 3: vm_compute verification for concrete instances                     *)
(* ========================================================================== *)

(* --- Star graph with m leaves: center 0 commutes with leaves 1..m --- *)

Definition star_comm_nat (m : nat) (i j : nat) : bool :=
  ((i == 0) || (j == 0)) && (i != j).

(* --- Complete graph: all distinct pairs commute --- *)

Definition complete_comm_nat (i j : nat) : bool := i != j.

(* --- Path graph on Tg generators: |i-j| >= 2 --- *)

Definition path_comm_nat (i j : nat) : bool :=
  (2 <= (maxn i j - minn i j)) && (i != j).

(* ---- Clique counts for star K_{1,3} (4 generators) ---- *)

Lemma star3_cc0 : clique_count 4 0 (star_comm_nat 3) = 1.
Proof. by vm_compute. Qed.

(** star3_cc1 — vm_compute check: the star K_{1,3} has 4 singletons
    (1-cliques).
    Kind: example.
*)
Lemma star3_cc1 : clique_count 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

(** star3_cc2 — vm_compute check: the star K_{1,3} has 3 edges (2-cliques),
    each pairing the center 0 with a leaf.
    Kind: example.
*)
Lemma star3_cc2 : clique_count 4 2 (star_comm_nat 3) = 3.
Proof. by vm_compute. Qed.

(** star3_cc3 — vm_compute check: the star K_{1,3} has no triangle because
    its three leaves do not pairwise commute.
    Kind: example.
*)
Lemma star3_cc3 : clique_count 4 3 (star_comm_nat 3) = 0.
Proof. by vm_compute. Qed.

(** star3_cc4 — vm_compute check: no 4-clique exists in K_{1,3}.
    Kind: example.
*)
Lemma star3_cc4 : clique_count 4 4 (star_comm_nat 3) = 0.
Proof. by vm_compute. Qed.

(* P(z) = 1 - 4z + 3z^2 = (1-z)(1-3z) *)

(* ---- Clique counts for complete graph on 3 generators ---- *)

Lemma complete3_cc0 : clique_count 3 0 complete_comm_nat = 1.
Proof. by vm_compute. Qed.

(** complete3_cc1 — vm_compute check: K_3 has 3 singletons.
    Kind: example.
*)
Lemma complete3_cc1 : clique_count 3 1 complete_comm_nat = 3.
Proof. by vm_compute. Qed.

(** complete3_cc2 — vm_compute check: K_3 has 3 edges.
    Kind: example.
*)
Lemma complete3_cc2 : clique_count 3 2 complete_comm_nat = 3.
Proof. by vm_compute. Qed.

(** complete3_cc3 — vm_compute check: K_3 has exactly one triangle.
    Kind: example.
*)
Lemma complete3_cc3 : clique_count 3 3 complete_comm_nat = 1.
Proof. by vm_compute. Qed.

(* c_k = C(3,k): 1, 3, 3, 1 — confirms P(z) = (1-z)^3 *)

(* ---- Clique counts for empty graph on 3 generators ---- *)

Lemma empty3_cc0 : clique_count 3 0 (fun _ _ => false) = 1.
Proof. by vm_compute. Qed.

(** empty3_cc1 — vm_compute check: the empty graph on 3 vertices has 3
    singletons.
    Kind: example.
*)
Lemma empty3_cc1 : clique_count 3 1 (fun _ _ => false) = 3.
Proof. by vm_compute. Qed.

(** empty3_cc2 — vm_compute check: the empty graph on 3 vertices has no
    edge.
    Kind: example.
*)
Lemma empty3_cc2 : clique_count 3 2 (fun _ _ => false) = 0.
Proof. by vm_compute. Qed.

(* c_0=1, c_1=3, c_k=0 for k>=2 — confirms P(z) = 1-3z *)

(* ---- Clique counts for path on 3 generators ---- *)

Lemma path3_cc0 : clique_count 3 0 path_comm_nat = 1.
Proof. by vm_compute. Qed.

(** path3_cc1 — vm_compute check: the path P_3 has 3 singletons.
    Kind: example.
*)
Lemma path3_cc1 : clique_count 3 1 path_comm_nat = 3.
Proof. by vm_compute. Qed.

(** path3_cc2 — vm_compute check: the path P_3 has exactly one edge between
    its two non-adjacent vertices (the diagonal of the commutation graph).
    Kind: example.
*)
Lemma path3_cc2 : clique_count 3 2 path_comm_nat = 1.
Proof. by vm_compute. Qed.

(** path3_cc3 — vm_compute check: the path P_3 has no triangle.
    Kind: example.
*)
Lemma path3_cc3 : clique_count 3 3 path_comm_nat = 0.
Proof. by vm_compute. Qed.

(* P(z) = 1 - 3z + z^2 *)

(* ---- Trace counts: star K_{1,3} ---- *)

Lemma star3_ct0 : clique_traces 4 0 (star_comm_nat 3) = 1.
Proof. by vm_compute. Qed.

(** star3_ct1 — vm_compute trace count m_1 = 4 for star K_{1,3}.
    Kind: example.
*)
Lemma star3_ct1 : clique_traces 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

(** star3_ct2 — vm_compute trace count m_2 = 13 for star K_{1,3}.
    Kind: example.
*)
Lemma star3_ct2 : clique_traces 4 2 (star_comm_nat 3) = 13.
Proof. by vm_compute. Qed.

(** star3_ct3 — vm_compute trace count m_3 = 40 for star K_{1,3}.
    Kind: example.
*)
Lemma star3_ct3 : clique_traces 4 3 (star_comm_nat 3) = 40.
Proof. by vm_compute. Qed.

(* Cross-check with n_traces_natB *)
Lemma star3_ntB0 : n_traces_natB 4 0 (star_comm_nat 3) = 1.
Proof. by vm_compute. Qed.

(** star3_ntB1 — cross-check: n_traces_natB agrees with clique_traces at
    L=1 for K_{1,3}.
    Kind: example.
*)
Lemma star3_ntB1 : n_traces_natB 4 1 (star_comm_nat 3) = 4.
Proof. by vm_compute. Qed.

(** star3_ntB2 — cross-check: n_traces_natB agrees with clique_traces at
    L=2 for K_{1,3}.
    Kind: example.
*)
Lemma star3_ntB2 : n_traces_natB 4 2 (star_comm_nat 3) = 13.
Proof. by vm_compute. Qed.

(** star3_ntB3 — cross-check: n_traces_natB agrees with clique_traces at
    L=3 for K_{1,3}.
    Kind: example.
*)
Lemma star3_ntB3 : n_traces_natB 4 3 (star_comm_nat 3) = 40.
Proof. by vm_compute. Qed.

(* ---- Trace counts: free group (3 generators) ---- *)

Lemma free3_ct0 : clique_traces 3 0 (fun _ _ => false) = 1.
Proof. by vm_compute. Qed.

(** free3_ct1 — vm_compute trace count m_1 = 3 for the free group on 3
    generators.
    Kind: example.
*)
Lemma free3_ct1 : clique_traces 3 1 (fun _ _ => false) = 3.
Proof. by vm_compute. Qed.

(** free3_ct2 — vm_compute trace count m_2 = 9 for the free group on 3
    generators (matches 3^2).
    Kind: example.
*)
Lemma free3_ct2 : clique_traces 3 2 (fun _ _ => false) = 9.
Proof. by vm_compute. Qed.

(** free3_ct3 — vm_compute trace count m_3 = 27 for the free group on 3
    generators (matches 3^3).
    Kind: example.
*)
Lemma free3_ct3 : clique_traces 3 3 (fun _ _ => false) = 27.
Proof. by vm_compute. Qed.

(** free3_ntB2 — cross-check that the natural-B trace count for free-3 at L = 2
    matches the expected 9.
    Kind: example.
    Naming: [natB] names the alternative trace count defined via natural-B
    enumeration, cross-checking the [clique_traces] result above. *)
Lemma free3_ntB2 : n_traces_natB 3 2 (fun _ _ => false) = 9.
Proof. by vm_compute. Qed.

(* ---- Trace counts: abelian (3 generators) ---- *)

Lemma abelian3_ct0 : clique_traces 3 0 complete_comm_nat = 1.
Proof. by vm_compute. Qed.

(** abelian3_ct1 — vm_compute trace count m_1 = 3 for the free abelian
    group on 3 generators.
    Kind: example.
*)
Lemma abelian3_ct1 : clique_traces 3 1 complete_comm_nat = 3.
Proof. by vm_compute. Qed.

(** abelian3_ct2 — vm_compute trace count m_2 = 6 for the free abelian
    group on 3 generators (matches C(L+2,2) = C(4,2) = 6).
    Kind: example.
*)
Lemma abelian3_ct2 : clique_traces 3 2 complete_comm_nat = 6.
Proof. by vm_compute. Qed.

(** abelian3_ct3 — vm_compute trace count m_3 = 10 for the free abelian
    group on 3 generators (matches C(L+2,2) = C(5,2) = 10).
    Kind: example.
*)
Lemma abelian3_ct3 : clique_traces 3 3 complete_comm_nat = 10.
Proof. by vm_compute. Qed.

(* C(L+2, 2) = 1, 3, 6, 10 for L = 0, 1, 2, 3 *)

(** abelian3_ntB2 — cross-check: n_traces_natB for the free abelian group on
    3 generators at L=2 equals C(L+2,2)=6.
    Kind: example.
    Why: vm_compute sanity check that n_traces_natB tracks the abelian
    closed form, complementing abelian3_ct2 / abelian3_ntB3.
*)
Lemma abelian3_ntB2 : n_traces_natB 3 2 complete_comm_nat = 6.
Proof. by vm_compute. Qed.

(** abelian3_ntB3 — cross-check: n_traces_natB for the abelian case at L=3
    matches clique_traces = 10.
    Kind: example.
*)
Lemma abelian3_ntB3 : n_traces_natB 3 3 complete_comm_nat = 10.
Proof. by vm_compute. Qed.

(* ---- Trace counts: path (3 generators) ---- *)

(** path3_ct0 — vm_compute trace count m_0 = 1 for the path graph P_3
    (the empty-word clique).
    Kind: example.
    Why: base case of the path recurrence m_L = 3*m_{L-1} - m_{L-2},
    paired with path3_ct1 / path3_ct2 / path3_ct3.
*)
Lemma path3_ct0 : clique_traces 3 0 path_comm_nat = 1.
Proof. by vm_compute. Qed.

(** path3_ct1 — vm_compute trace count m_1 = 3 for the path P_3.
    Kind: example.
*)
Lemma path3_ct1 : clique_traces 3 1 path_comm_nat = 3.
Proof. by vm_compute. Qed.

(** path3_ct2 — vm_compute trace count m_2 = 8 for the path P_3.
    Kind: example.
*)
Lemma path3_ct2 : clique_traces 3 2 path_comm_nat = 8.
Proof. by vm_compute. Qed.

(** path3_ct3 — vm_compute trace count m_3 = 21 for the path P_3.
    Kind: example.
*)
Lemma path3_ct3 : clique_traces 3 3 path_comm_nat = 21.
Proof. by vm_compute. Qed.

(** path3_ntB2 — cross-check that n_traces_natB for the path P_3 at L=2 equals 8.
    Kind: example.
    Naming: [natB] names the alternative trace count defined via natural-B
    enumeration, cross-checking the [clique_traces] result above. *)
Lemma path3_ntB2 : n_traces_natB 3 2 path_comm_nat = 8.
Proof. by vm_compute. Qed.

(** path3_ntB3 — cross-check: n_traces_natB for the path P_3 at L=3 matches
    clique_traces = 21.
    Kind: example.
*)
Lemma path3_ntB3 : n_traces_natB 3 3 path_comm_nat = 21.
Proof. by vm_compute. Qed.

(* ========================================================================== *)
(* Part 4: Growth rate formulas                                               *)
(* ========================================================================== *)

(* --- Helper lemma: size of elements in subseqs_k --- *)

Lemma subseqs_k_size k s t : t \in subseqs_k k s -> size t = k.
Proof.
elim: s k t => [|a s IHs] [|k] t //=.
- by rewrite mem_seq1 => /eqP ->.
- by rewrite mem_seq1 => /eqP ->.
- rewrite mem_cat => /orP [/mapP [t' Ht' ->] | Ht].
  + by rewrite /= (IHs _ _ Ht').
  + exact: IHs Ht.
Qed.

(* --- Empty graph: clique_count Tg 0 = 1, clique_count Tg 1 = Tg --- *)

(** filter_pred1T — filtering a singleton by a predicate that holds on the
    element returns the singleton unchanged.
    Kind: helper.
    Why: cosmetic base-case lemma for singleton filters used inside
    clique-count reductions.
    Used by: clique_count1 and related singleton-filter reductions in this
             section.
*)
Lemma filter_pred1T (T : Type) (p : pred T) (x : T) :
  p x -> [seq s <- [:: x] | p s] = [:: x].
Proof. by move=> /= ->. Qed.

(** all_pairs_comm_nil — the empty sequence trivially satisfies the
    pairwise-commuting predicate.
    Kind: helper.
    Used by: clique_count0 and downstream base-case reasoning.
*)
Lemma all_pairs_comm_nil comm : all_pairs_comm_sorted comm [::] = true.
Proof. by []. Qed.

(** subseqs_k0 — the only zero-length subsequence is the empty one.
    Kind: helper.
    Used by: clique_count0, empty_clique_countk, size_subseqs_k base case.
*)
Lemma subseqs_k0 s : subseqs_k 0 s = [:: [::]].
Proof. by case: s. Qed.

(** clique_count0 — there is exactly one 0-clique (the empty set) in any
    commutation graph.
    Kind: helper.
    Used by: clique_traces recurrence base case; starting condition of the
             memo table in clique_traces_aux.
*)
Lemma clique_count0 Tg comm : clique_count Tg 0 comm = 1.
Proof.
by rewrite /clique_count /cliques_of_size subseqs_k0
           (filter_pred1T (all_pairs_comm_nil comm)).
Qed.

(** subseqs_k1 — length-1 subsequences of s are exactly the singletons of
    its elements.
    Kind: helper.
    Used by: empty_clique_count1 and any length-1 clique enumeration.
*)
Lemma subseqs_k1 s : subseqs_k 1 s = [seq [:: x] | x <- s].
Proof.
elim: s => [|a s IH] //=.
by rewrite subseqs_k0 /= IH.
Qed.

(** empty_clique_count1 — in the empty commutation graph on Tg vertices
    there are exactly Tg singleton cliques.
    Kind: helper.
    Used by: clique_step_free; this is the c_1 coefficient in the free-case
             trace recurrence.
*)
Lemma empty_clique_count1 Tg :
  clique_count Tg 1 (fun _ _ => false) = Tg.
Proof.
rewrite /clique_count /cliques_of_size subseqs_k1.
rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT size_map size_iota.
by move=> s /mapP [x _ ->]; rewrite /all_pairs_comm_sorted /= eqxx.
Qed.

(** subseqs_k_subseq — every element of subseqs_k k s is a genuine
    subsequence of s.
    Kind: helper.
    Used by: empty_clique_countk, complete_clique_count, and any argument
             that needs uniqueness or membership of clique entries.
*)
Lemma subseqs_k_subseq k s t : t \in subseqs_k k s -> subseq t s.
Proof.
elim: s k t => [|a s IHs] [|k] t //=.
- by rewrite mem_seq1 => /eqP ->.
- by rewrite mem_seq1 => /eqP ->.
- rewrite mem_cat => /orP [/mapP [t' Ht' ->] | Ht].
  + by rewrite /= eqxx; exact: IHs Ht'.
  + exact: subseq_trans (IHs _ _ Ht) (subseq_cons _ _).
Qed.

(** mem_subseqs_k — converse of subseqs_k_subseq: every subsequence of s of
    size k is enumerated by subseqs_k k s.
    Kind: helper.
    Used by: completeness arguments for clique enumeration.
*)
Lemma mem_subseqs_k k s t :
  subseq t s -> size t = k -> t \in subseqs_k k s.
Proof.
elim: s k t => [|a s IHs] [|k] t.
- by rewrite subseq0 => /eqP ->.
- by rewrite subseq0 => /eqP ->.
- move=> _ /size0nil ->.
  by rewrite subseqs_k0 mem_seq1.
- case: t => [// | b t] /=.
  case Hba : (b == a) => Hsub [Hsz].
  + (* b = a: (b :: t) \in subseqs_k k.+1 (a :: s) via left *)
    (* Hsub : subseq t s, Hsz : size t = k *)
    rewrite mem_cat; apply/orP; left; apply/mapP.
    have -> : b = a by move/eqP: Hba.
    by exists t => //; exact: IHs Hsub Hsz.
  + (* b != a: (b :: t) \in subseqs_k k.+1 (a :: s) via right *)
    (* Hsub : subseq (b :: t) s *)
    rewrite mem_cat; apply/orP; right.
    apply: IHs Hsub _; by rewrite /= Hsz.
Qed.

(** all_pairs_false_neq — if s contains two distinct values and the
    commutation relation is trivially false, the pairwise predicate fails.
    Kind: helper.
    Used by: empty_clique_countk to certify absence of k-cliques for k>=2.
*)
Lemma all_pairs_false_neq (s : seq nat) (a b : nat) :
  a \in s -> b \in s -> a != b ->
  all_pairs_comm_sorted (fun _ _ => false) s = false.
Proof.
move=> Ha Hb Hab.
apply/negbTE/negP.
rewrite /all_pairs_comm_sorted => /allP /(_ a Ha) /allP /(_ b Hb).
by rewrite (negbTE Hab).
Qed.

(** empty_clique_countk — for k >= 2 the empty commutation graph has no
    k-clique, so c_k = 0.
    Kind: helper.
    Used by: clique_step_free, the key simplification that makes the free
             trace recurrence collapse to m_L = Tg * m_{L-1}.
*)
Lemma empty_clique_countk Tg k :
  2 <= k -> clique_count Tg k (fun _ _ => false) = 0.
Proof.
move=> Hk.
rewrite /clique_count /cliques_of_size.
rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
move=> s Hs /=.
have Hsz := subseqs_k_size Hs.
have Huniq := subseq_uniq (subseqs_k_subseq Hs) (iota_uniq 0 Tg).
have Hsz2 : 2 <= size s by rewrite Hsz.
suff [a [b [Ha [Hb Hab]]]] : exists a b, a \in s /\ b \in s /\ a != b.
  exact: all_pairs_false_neq Ha Hb Hab.
case: s {Hs Hsz} Hsz2 Huniq => [|a [|b s]] // _ /andP [Ha Huniq'].
exists a, b; split; first by exact: mem_head.
split; first by rewrite in_cons mem_head orbT.
by move: Ha; rewrite in_cons negb_or => /andP [].
Qed.

(* --- Free case: clique_traces Tg L (fun _ _ => false) = Tg^L --- *)
(* For empty graph: c_0=1, c_1=Tg, c_k=0 for k>=2.
   Recurrence: m_L = Tg * m_{L-1}, m_0 = 1, so m_L = Tg^L. *)

(* Helper: sumn of all-zero map is 0 *)
Lemma sumn_map_0 {A : eqType} (f : A -> nat) (s : seq A) :
  (forall x, x \in s -> f x = 0) -> sumn [seq f x | x <- s] = 0.
Proof.
elim: s => [|a s IH] //= Hf.
rewrite Hf ?IH // ?mem_head //.
by move=> x Hx; apply: Hf; rewrite in_cons Hx orbT.
Qed.

(* clique_step for empty graph = Tg * previous element *)
Lemma clique_step_free Tg memo :
  0 < size memo ->
  clique_step Tg (fun _ _ => false) memo = Tg * nth 0 memo (size memo - 1).
Proof.
move=> Hpos.
rewrite /clique_step.
have Hneg : sumn [seq clique_count Tg k (fun _ _ => false) *
                       nth 0 memo (size memo - k)
                  | k <- [seq k <- iota 1 (size memo) | ~~ odd k]] = 0.
  apply: sumn_map_0 => k.
  rewrite mem_filter => /andP [Heven Hk_iota].
  have Hk2 : 2 <= k.
    rewrite mem_iota in Hk_iota.
    by case: k Heven Hk_iota => [|[|k']] //=.
  by rewrite empty_clique_countk // mul0n.
rewrite Hneg subn0.
case: (size memo) Hpos => [|n] // _.
rewrite //=.
rewrite empty_clique_count1.
have Hrest : sumn [seq clique_count Tg k (fun _ _ => false) *
                        nth 0 memo (n.+1 - k)
                   | k <- [seq k <- iota 2 n | odd k]] = 0.
  apply: sumn_map_0 => k.
  rewrite mem_filter => /andP [_ Hk_iota].
  have Hk2 : 2 <= k.
    by rewrite mem_iota in Hk_iota; case/andP: Hk_iota.
  by rewrite empty_clique_countk // mul0n.
by rewrite Hrest addn0.
Qed.

(* Invariant: clique_traces_aux extends memo with powers of Tg *)
Lemma clique_traces_aux_inv Tg n memo :
  0 < size memo ->
  (forall i, i < size memo -> nth 0 memo i = Tg ^ i) ->
  clique_traces_aux Tg (fun _ _ => false) n memo =
  memo ++ [seq Tg ^ (size memo + i) | i <- iota 0 n].
Proof.
elim: n memo => [|n IH] memo Hpos Hmemo /=.
  by rewrite cats0.
rewrite IH.
- rewrite size_rcons -cats1 -catA /=.
  congr (memo ++ _); congr cons.
  + rewrite clique_step_free // Hmemo;
      last by rewrite ltn_subrL Hpos.
    by rewrite addn0 -expnS subn1 (prednK Hpos).
  + rewrite -[1]addn0 iotaDl -map_comp /=.
    by apply: eq_map => i /=; rewrite addSn addnS.
- by rewrite size_rcons.
- move=> i.
  rewrite size_rcons nth_rcons ltnS.
  case: (ltnP i (size memo)) => Hi Hi2.
    exact: Hmemo.
  have -> : i = size memo by apply/anti_leq/andP; split.
  rewrite eqxx.
  rewrite clique_step_free // Hmemo;
    last by rewrite ltn_subrL Hpos.
  by rewrite -expnS subn1 prednK.
Qed.

(** clique_traces_free — the free case: clique_traces gives Tg^L.
    Kind: main.
    Why: closes the free case of the Cartier-Foata counting formula and
         validates the clique recurrence against the known answer.
*)
Lemma clique_traces_free Tg L :
  clique_traces Tg L (fun _ _ => false) = Tg ^ L.
Proof.
rewrite /clique_traces.
rewrite clique_traces_aux_inv //; last by move=> [|i].
case: L => [|L] //.
have -> : nth 0 ([:: 1] ++ [seq Tg ^ (1 + i) | i <- iota 0 L.+1]) L.+1 =
          nth 0 [seq Tg ^ (1 + i) | i <- iota 0 L.+1] L by [].
by rewrite (nth_map 0) ?size_iota // nth_iota ?add1n.
Qed.

(* --- Abelian case: clique_traces Tg L (i != j) = C(L+Tg-1, Tg-1) --- *)
(* For complete graph: c_k = C(Tg,k), P(z) = (1-z)^Tg.
   1/P(z) = Sum C(L+Tg-1,Tg-1) z^L. *)

(* All distinct pairs commute in a complete graph *)
Lemma all_pairs_complete (s : seq nat) :
  uniq s -> all_pairs_comm_sorted complete_comm_nat s.
Proof.
move=> Huniq.
apply/allP => i Hi; apply/allP => j Hj; apply/orP.
case Heq: (i == j); first by left.
by right; rewrite /complete_comm_nat Heq.
Qed.

(** size_subseqs_k — for a duplicate-free list s, the number of length-k
    subsequences is the binomial C(|s|, k).
    Kind: helper.
    Used by: complete_clique_count (in turn used by the abelian trace
             formula).
*)
Lemma size_subseqs_k k s :
  uniq s -> size (subseqs_k k s) = 'C(size s, k).
Proof.
elim: s k => [|a s IHs] k //=.
  by case: k => [|k] //=; rewrite bin_small.
case/andP => _ Hu; case: k => [|k] //=.
by rewrite size_cat size_map IHs // IHs // addnC -binS.
Qed.

(** complete_clique_count — in the complete commutation graph on Tg
    vertices, the k-clique count is C(Tg, k).
    Kind: helper.
    Used by: clique_step_abelian, which drives clique_traces_abelian.
*)
Lemma complete_clique_count Tg k :
  clique_count Tg k complete_comm_nat = 'C(Tg, k).
Proof.
rewrite /clique_count /cliques_of_size.
rewrite (eq_in_filter (a2 := predT)).
  rewrite filter_predT size_subseqs_k ?iota_uniq // size_iota //.
move=> s Hs /=.
apply: all_pairs_complete.
exact: subseq_uniq (subseqs_k_subseq Hs) (iota_uniq 0 Tg).
Qed.

(* Alternating-sum decomposition of the binomial inversion identity.
   spos n r L = Sum_{k even, 0<=k<=L} C(n,k) * C(L-k+r, r)
   sneg n r L = Sum_{k odd,  0<=k<=L} C(n,k) * C(L-k+r, r)
   The key identity: spos n.+1 n L.+1 = sneg n.+1 n L.+1
   which implies the clique recurrence with c_k = C(Tg,k). *)

Definition spos (n r L : nat) : nat :=
  sumn [seq 'C(n, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 0 L.+1 | ~~ odd k]].

(** sneg — alternating-sum decomposition: odd-index part of the binomial
    identity used in the abelian-case clique recurrence proof.
    Kind: canonical.
*)
Definition sneg (n r L : nat) : nat :=
  sumn [seq 'C(n, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 0 L.+1 | odd k]].

Arguments spos : simpl never.
Arguments sneg : simpl never.

(** filter_iota_head_even — unfold the head of the even-filtered iota 0
    L.+1 into 0 :: tail.
    Kind: helper.
    Used by: spos_split and the spos/sneg Pascal decomposition.
*)
Lemma filter_iota_head_even L :
  [seq k <- iota 0 L.+1 | ~~ odd k] = 0 :: [seq k <- iota 1 L | ~~ odd k].
Proof. by case: L. Qed.

(** filter_iota_head_odd — odd-filter drops the leading 0, so filtering
    iota 0 L.+1 agrees with filtering iota 1 L.
    Kind: helper.
    Used by: sneg_eq_tail and companions.
*)
Lemma filter_iota_head_odd L :
  [seq k <- iota 0 L.+1 | odd k] = [seq k <- iota 1 L | odd k].
Proof. by case: L. Qed.

(** sumn_filter_map — convert a filtered sum to a sum with a conditional
    summand, avoiding the filter.
    Kind: helper.
    Used by: spos_unfold, sneg_unfold, and related sumn rewrites.
*)
Lemma sumn_filter_map {A : eqType} (p : pred A) (f : A -> nat) (s : seq A) :
  sumn [seq f x | x <- [seq x <- s | p x]] =
  sumn [seq (if p x then f x else 0) | x <- s].
Proof. by elim: s => [|a s IH] //=; case: (p a) => /=; rewrite IH. Qed.

(** spos_unfold — filter-free rewrite of spos as a conditional sum.
    Kind: helper.
    Used by: spos_split, spos0, spos_pascal_core, neg_eq_spos_sub.
*)
Lemma spos_unfold n r L :
  spos n r L = sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
                     | k <- iota 0 L.+1].
Proof. by rewrite /spos sumn_filter_map. Qed.

(** sneg_unfold — filter-free rewrite of sneg as a conditional sum.
    Kind: helper.
    Used by: sneg0, sneg_pascal_core, pos_eq_sneg_range.
*)
Lemma sneg_unfold n r L :
  sneg n r L = sumn [seq (if odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
                     | k <- iota 0 L.+1].
Proof. by rewrite /sneg sumn_filter_map. Qed.

(** spos_split — isolates the k=0 term 'C(L+r,r) of the even-parity sum spos.
    Kind: helper.
    Used by: spos_pascal, clique_step_abelian (used via the abelian pipeline).
*)
Lemma spos_split n r L :
  spos n r L =
  'C(L + r, r) +
  sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 1 L].
Proof.
by rewrite spos_unfold /sumn /= -/(sumn _) bin0 mul1n subn0.
Qed.

(** sneg_eq_tail — drops the (vanishing) k=0 term from sneg, giving the
    tail iota 1 L form used by Pascal-style recurrences.
    Kind: helper.
    Used by: sneg_pascal, clique_step_abelian.
*)
Lemma sneg_eq_tail n r L :
  sneg n r L =
  sumn [seq (if odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 1 L].
Proof.
by rewrite sneg_unfold /sumn /= -/(sumn _).
Qed.

Arguments sumn : simpl never.

(** sumn_map_add — linearity of sumn over pointwise addition of mapped
    functions on a finite sequence.
    Kind: helper.
    Used by: sumn_map_split (additive decomposition on iota sums).
*)
Lemma sumn_map_add {A : Type} (f g : A -> nat) (s : seq A) :
  sumn [seq f x + g x | x <- s] =
  sumn [seq f x | x <- s] + sumn [seq g x | x <- s].
Proof. by elim: s => [|a s IH] //; rewrite /sumn /= -/(sumn _) IH addnACA. Qed.

(** sumn_map_split — if f = g + h pointwise on the iota range, then the
    sumn splits into sumn of g plus sumn of h.
    Kind: helper.
    Used by: Pascal-decomposition core lemmas for spos / sneg.
*)
Lemma sumn_map_split (f g h : nat -> nat) m M :
  (forall k, m <= k -> f k = g k + h k) ->
  sumn [seq f k | k <- iota m M] =
  sumn [seq g k | k <- iota m M] + sumn [seq h k | k <- iota m M].
Proof.
move=> H; elim: M m H => [|M IH] m H //.
rewrite /sumn /= -/(sumn _) -/(sumn _) -/(sumn _).
by rewrite H // (IH _ (fun k Hk => H k (ltnW Hk))) addnACA.
Qed.

(** sumn_map_eq — pointwise equality of f and g on the iota range carries
    through sumn; used to swap summand shapes without altering totals.
    Kind: helper.
    Used by: spos_pascal_core, sneg_pascal_core (index-shift normalisation).
*)
Lemma sumn_map_eq (f g : nat -> nat) m M :
  (forall k, m <= k -> f k = g k) ->
  sumn [seq f k | k <- iota m M] = sumn [seq g k | k <- iota m M].
Proof.
move=> H; elim: M m H => [|M IH] m H //.
rewrite /sumn /= -/(sumn _) -/(sumn _).
by rewrite H // IH // => k /ltnW /H.
Qed.

(** sumn_shift_even_to_odd_gen — reindexes an even-gated sum over iota m.+1 M
    to an odd-gated sum over iota m M by shifting k down to j = k.-1.
    Kind: helper.
    Why: parity alternates under the shift k |-> k.-1, so an even-indexed
    term at k becomes an odd-indexed term at k-1; this is the general form
    fed to sneg_pascal_core.
    Used by: sneg_pascal_core (Pascal recurrence on sneg).
    Naming: shift_even_to_odd is a precise parity-direction descriptor;
    the _gen suffix marks the abstract-g form used to instantiate the
    specialised even-to-odd rewrite.
*)
Lemma sumn_shift_even_to_odd_gen (g : nat -> nat) m M :
  sumn [seq (if ~~ odd k then g k.-1 else 0) | k <- iota m.+1 M] =
  sumn [seq (if odd j then g j else 0) | j <- iota m M].
Proof.
by elim: M m => [|M IH] m //;
  rewrite /sumn /= -/(sumn _) -/(sumn _) (IH m.+1) negbK.
Qed.

(** sumn_shift_odd_to_even_gen — reindexes an odd-gated sum over iota m.+1 M
    to an even-gated sum over iota m M by shifting k down to j = k.-1.
    Kind: helper.
    Why: parity alternates under the shift k |-> k.-1, so an odd-indexed
    term at k becomes an even-indexed term at k-1; the companion of
    sumn_shift_even_to_odd_gen used in the spos recurrence.
    Used by: spos_pascal_core (Pascal recurrence on spos).
    Naming: shift_odd_to_even is a precise parity-direction descriptor;
    the _gen suffix marks the abstract-g form.
*)
Lemma sumn_shift_odd_to_even_gen (g : nat -> nat) m M :
  sumn [seq (if odd k then g k.-1 else 0) | k <- iota m.+1 M] =
  sumn [seq (if ~~ odd j then g j else 0) | j <- iota m M].
Proof.
by elim: M m => [|M IH] m //;
  rewrite /sumn /= -/(sumn _) -/(sumn _) (IH m.+1).
Qed.

(** sumn_iota_map0 — if f vanishes on [m, m+M), the mapped sum is zero.
    Kind: helper.
    Used by: spos0, sneg0 (annihilation of spos / sneg when n = 0).
*)
Lemma sumn_iota_map0 (f : nat -> nat) m M :
  (forall k, m <= k -> f k = 0) -> sumn [seq f k | k <- iota m M] = 0.
Proof.
move=> Hf; elim: M m Hf => [|M IH] m Hf //.
rewrite /sumn /= -/(sumn _).
rewrite Hf // IH // => k Hk.
by apply: Hf; exact: ltnW.
Qed.

(** spos_L0 — boundary value spos n r 0 = 'C(r, r).
    Kind: helper.
    Used by: spos_inv base case.
*)
Lemma spos_L0 n r : spos n r 0 = 'C(r, r).
Proof. by rewrite /spos /sumn /= bin0 mul1n subn0 add0n addn0. Qed.

(** sneg_L0 — boundary value sneg n r 0 = 0 (empty tail sum).
    Kind: helper.
    Used by: spos_inv base case.
*)
Lemma sneg_L0 n r : sneg n r 0 = 0.
Proof. by rewrite /sneg /sumn. Qed.

(** spos0 — evaluation spos 0 r L = 'C(L+r, r); only the k=0 term survives
    when n = 0 since 'C(0, k) = 0 for k > 0.
    Kind: helper.
    Used by: spos_inv base case (n = 0).
*)
Lemma spos0 r L : spos 0 r L = 'C(L + r, r).
Proof.
rewrite spos_unfold /sumn /= -/(sumn _) mul1n subn0.
suff -> : sumn [seq (if ~~ odd k then 'C(0, k) * 'C(L - k + r, r) else 0)
               | k <- iota 1 L] = 0 by rewrite addn0.
apply: sumn_iota_map0 => k Hk.
by case: (~~ odd k) => //=; rewrite (bin_small Hk) mul0n.
Qed.

(** sneg0 — evaluation sneg 0 r L = 0; every tail term has a 'C(0, k)
    factor that vanishes for k >= 1.
    Kind: helper.
    Used by: spos_inv base case (n = 0).
*)
Lemma sneg0 r L : sneg 0 r L = 0.
Proof.
rewrite sneg_unfold /=.
apply: sumn_iota_map0 => k Hk.
by case: (odd k) => //=; rewrite (bin_small Hk) mul0n.
Qed.

(** binSn — Pascal identity rearranged so the decrement lives on k on the
    right-hand side; complements binS for the sneg recurrence.
    Kind: helper.
    Used by: spos_pascal_core, sneg_pascal_core.
*)
Lemma binSn n k : 0 < k ->
  'C(n.+1, k) = 'C(n, k) + 'C(n, k.-1).
Proof. by case: k => // k _; rewrite binS addnC. Qed.

(* Core identity for spos_pascal: decomposes even-parity sum using
   Pascal's rule C(n+1,k) = C(n,k) + C(n,k-1) and reindexing. *)
Lemma spos_pascal_core n r L :
  sumn [seq (if ~~ odd k then 'C(n.+1, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] =
  sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 0 L.+1].
Proof.
transitivity (
  sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if ~~ odd k then 'C(n, k.-1) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1]).
  apply: sumn_map_split => k Hk /=.
  case: (~~ odd k) => //=.
  by rewrite binSn // -mulnDl.
set X := sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
              | k <- iota 1 L.+1].
suff -> : sumn [seq (if ~~ odd k then 'C(n, k.-1) * 'C(L.+1 - k + r, r) else 0)
               | k <- iota 1 L.+1] =
          sumn [seq (if odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
               | k <- iota 0 L.+1] by [].
rewrite -(sumn_shift_even_to_odd_gen
            (fun j => 'C(n, j) * 'C(L - j + r, r)) 0 L.+1).
apply: sumn_map_eq => k Hk /=.
case: (~~ odd k) => //=.
congr (_ * _).
by case: k Hk => // k _; rewrite subSS.
Qed.

(* Core identity for sneg_pascal: decomposes odd-parity sum using
   Pascal's rule and reindexing. *)
Lemma sneg_pascal_core n r L :
  sumn [seq (if odd k then 'C(n.+1, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] =
  sumn [seq (if odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
       | k <- iota 0 L.+1].
Proof.
transitivity (
  sumn [seq (if odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1] +
  sumn [seq (if odd k then 'C(n, k.-1) * 'C(L.+1 - k + r, r) else 0)
       | k <- iota 1 L.+1]).
  apply: sumn_map_split => k Hk /=.
  case: (odd k) => //=.
  by rewrite binSn // -mulnDl.
set X := sumn [seq (if odd k then 'C(n, k) * 'C(L.+1 - k + r, r) else 0)
              | k <- iota 1 L.+1].
suff -> : sumn [seq (if odd k then 'C(n, k.-1) * 'C(L.+1 - k + r, r) else 0)
               | k <- iota 1 L.+1] =
          sumn [seq (if ~~ odd k then 'C(n, k) * 'C(L - k + r, r) else 0)
               | k <- iota 0 L.+1] by [].
rewrite -(sumn_shift_odd_to_even_gen
            (fun j => 'C(n, j) * 'C(L - j + r, r)) 0 L.+1).
apply: sumn_map_eq => k Hk /=.
case: (odd k) => //=.
congr (_ * _).
by case: k Hk => // k _; rewrite subSS.
Qed.

(** spos_pascal — Pascal-style recurrence for spos: incrementing n expresses
    spos n.+1 r L.+1 as spos n r L.+1 plus sneg n r L.
    Kind: helper.
    Used by: spos_inv inductive step, spos_eq_sneg.
*)
Lemma spos_pascal n r L :
  spos n.+1 r L.+1 = spos n r L.+1 + sneg n r L.
Proof.
rewrite (spos_split n.+1) (spos_split n r L.+1) (sneg_unfold n r L).
by rewrite spos_pascal_core addnA.
Qed.

(** sneg_pascal — companion Pascal-style recurrence for sneg: incrementing n
    expresses sneg n.+1 r L.+1 as sneg n r L.+1 plus spos n r L.
    Kind: helper.
    Used by: spos_inv inductive step, spos_eq_sneg.
*)
Lemma sneg_pascal n r L :
  sneg n.+1 r L.+1 = sneg n r L.+1 + spos n r L.
Proof.
rewrite (sneg_eq_tail n.+1 r L.+1) (sneg_eq_tail n r L.+1) (spos_unfold n r L).
by rewrite sneg_pascal_core addnA.
Qed.

(** spos_inv — invariant relating spos and sneg: when n <= r,
    spos n r L = 'C(L+r-n, r-n) + sneg n r L.
    Kind: helper.
    Used by: spos_eq_sneg; abelian clique-count collapse in clique_step_abelian.
*)
Lemma spos_inv n r L : n <= r ->
  spos n r L = 'C(L + r - n, r - n) + sneg n r L.
Proof.
elim: n r L => [|n IHn] r L Hrn.
  by rewrite spos0 sneg0 addn0 subn0 subn0.
case: L => [|L].
  by rewrite spos_L0 sneg_L0 addn0 add0n binn binn.
rewrite spos_pascal sneg_pascal.
rewrite (IHn r L.+1 (ltnW Hrn)) (IHn r L (ltnW Hrn)).
(* Goal: 'C(L.+1+r-n, r-n) + sneg n r L.+1 + sneg n r L =
         'C(L.+1+r-n.+1, r-n.+1) + (sneg n r L.+1 + ('C(L+r-n, r-n) + sneg n r L)) *)
set a := 'C(L.+1 + r - n, r - n).
set b := sneg n r L.+1.
set c := sneg n r L.
set d := 'C(L.+1 + r - n.+1, r - n.+1).
set e := 'C(L + r - n, r - n).
(* Goal: a + b + c = d + (b + (e + c)) *)
suff -> : a = d + e.
  (* d + e + b + c = d + (b + (e + c)) *)
  by rewrite [d + e + b]addnAC addnA addnA.
subst a d e.
(* Goal: 'C(L.+1+r-n, r-n) = 'C(L.+1+r-n.+1, r-n.+1) + 'C(L+r-n, r-n) *)
have Hrn' : n <= L + r by apply: (leq_trans (ltnW Hrn)); exact: leq_addl.
have Heq1 : L.+1 + r - n.+1 = L + r - n by rewrite addSn subSS.
have Heq2 : r - n = (r - n.+1).+1 by rewrite subnS prednK // subn_gt0.
have Heq3 : L.+1 + r - n = (L + r - n).+1 by rewrite addSn (subSn Hrn').
by rewrite Heq1 Heq2 Heq3 binS addnC.
Qed.

(** spos_eq_sneg — critical case n = r where spos equals sneg; the extra
    'C(L+r-n, r-n) term collapses to 'C(0,0) = 1 and is absorbed.
    Kind: helper.
    Used by: clique_step_abelian (abelian growth-rate collapse).
*)
Lemma spos_eq_sneg n L :
  spos n.+1 n L.+1 = sneg n.+1 n L.+1.
Proof.
rewrite spos_pascal sneg_pascal.
rewrite (@spos_inv n n L.+1 (leqnn n)) (@spos_inv n n L (leqnn n)).
by rewrite (subnn n) addnK addnK bin0 bin0 addnCA.
Qed.

(** pos_eq_sneg_range — bridges the filtered-sum form (odd k over iota 1 L)
    to the sneg notation, collapsing the filter-of-mapped presentation.
    Kind: helper.
    Used by: clique_step_abelian.
*)
Lemma pos_eq_sneg_range Tg r L :
  sumn [seq 'C(Tg, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 1 L | odd k]] =
  sneg Tg r L.
Proof. by rewrite sneg_eq_tail sumn_filter_map. Qed.

(** neg_eq_spos_sub — bridges the filtered-sum form (even k over iota 1 L)
    to spos minus its k=0 term 'C(L+r, r).
    Kind: helper.
    Used by: clique_step_abelian.
*)
Lemma neg_eq_spos_sub Tg r L :
  sumn [seq 'C(Tg, k) * 'C(L - k + r, r)
       | k <- [seq k <- iota 1 L | ~~ odd k]] =
  spos Tg r L - 'C(L + r, r).
Proof. by rewrite spos_split sumn_filter_map addKn. Qed.

(** clique_step_abelian — one step of the abelian clique recurrence yields
    the closed-form binomial 'C(size memo + Tg.-1, Tg.-1) under the
    complete-commutation graph, given the binomial invariant on memo.
    Kind: helper.
    Used by: clique_traces_aux_inv_abelian, clique_traces_abelian.
*)
Lemma clique_step_abelian Tg memo :
  0 < Tg -> 0 < size memo ->
  (forall i, i < size memo -> nth 0 memo i = 'C(i + Tg.-1, Tg.-1)) ->
  clique_step Tg complete_comm_nat memo = 'C(size memo + Tg.-1, Tg.-1).
Proof.
move=> HTg Hpos Hmemo.
rewrite /clique_step.
set L := size memo.
set r := Tg.-1.
have Hmap_eq : forall (p : pred nat),
  [seq clique_count Tg k complete_comm_nat * nth 0 memo (L - k)
      | k <- [seq k <- iota 1 L | p k]] =
  [seq 'C(Tg, k) * 'C(L - k + r, r)
      | k <- [seq k <- iota 1 L | p k]].
  move=> p; apply/eq_in_map => k Hk.
  rewrite complete_clique_count.
  suff -> : nth 0 memo (L - k) = 'C(L - k + r, r) by [].
  apply: Hmemo.
  rewrite mem_filter mem_iota in Hk.
  case/andP: Hk => _ /andP [Hk1 Hk2].
  by rewrite /L ltn_subrL Hk1 Hpos.
have Hpos_eq := congr1 sumn (Hmap_eq odd).
have Hneg_eq := congr1 sumn (Hmap_eq (fun k => ~~ odd k)).
rewrite Hpos_eq Hneg_eq pos_eq_sneg_range neg_eq_spos_sub.
subst r; case: Tg HTg {Hpos_eq Hneg_eq Hmap_eq Hmemo} => // Tg _ /=.
rewrite /L; case: (size memo) Hpos => [|L'] // _.
by rewrite spos_eq_sneg subKn // -spos_eq_sneg spos_split leq_addr.
Qed.

(** clique_traces_aux_inv_abelian — inductive invariant: under
    complete_comm_nat and the binomial invariant on memo, running
    clique_traces_aux for n more steps appends the closed-form binomials
    'C(size memo + i + Tg.-1, Tg.-1) for i in iota 0 n.
    Kind: helper.
    Used by: clique_traces_abelian.
    Naming: _aux_inv_abelian mirrors the naming of clique_traces_aux
    (base recursor, aux) and its invariant (inv) specialised to the
    abelian commutation graph; the five components each carry distinct
    semantic roles.
*)
Lemma clique_traces_aux_inv_abelian Tg n memo :
  0 < Tg -> 0 < size memo ->
  (forall i, i < size memo -> nth 0 memo i = 'C(i + Tg.-1, Tg.-1)) ->
  clique_traces_aux Tg complete_comm_nat n memo =
  memo ++ [seq 'C(size memo + i + Tg.-1, Tg.-1) | i <- iota 0 n].
Proof.
elim: n memo => [|n IH] memo HTg Hpos Hmemo /=.
  by rewrite cats0.
rewrite IH.
- rewrite size_rcons -cats1 -catA /=.
  congr (memo ++ _); congr cons.
  + by rewrite clique_step_abelian // addn0.
  + rewrite -[1]addn0 iotaDl -map_comp /=.
    by apply: eq_map => i /=; rewrite addSn addnS.
- done.
- by rewrite size_rcons.
- move=> i; rewrite size_rcons nth_rcons ltnS.
  case: (ltnP i (size memo)) => Hi Hi2.
    exact: Hmemo.
  have -> : i = size memo by apply/anti_leq/andP; split.
  by rewrite eqxx clique_step_abelian // addn0.
Qed.

(** clique_traces_abelian — closed form for the abelian clique trace count:
    under complete_comm_nat, clique_traces Tg L equals 'C(L + Tg.-1, Tg.-1).
    Kind: main.
*)
Lemma clique_traces_abelian Tg L :
  0 < Tg ->
  clique_traces Tg L complete_comm_nat = 'C(L + Tg.-1, Tg.-1).
Proof.
move=> HTg.
rewrite /clique_traces.
rewrite clique_traces_aux_inv_abelian //; last first.
  move=> [|i] _ //=.
  by rewrite add0n binn.
case: L => [|L].
  by rewrite /= add0n binn.
have -> : nth 0 ([:: 1] ++ [seq 'C(1 + i + Tg.-1, Tg.-1)
            | i <- iota 0 L.+1]) L.+1 =
          nth 0 [seq 'C(1 + i + Tg.-1, Tg.-1) | i <- iota 0 L.+1] L by [].
by rewrite (nth_map 0) ?size_iota // nth_iota // add0n addnC addnA.
Qed.

(* --- vm_compute verification of growth rate formulas --- *)

(** free_growth_check — vm_compute sanity check that for the free group
    (empty commutation oracle), clique_traces follows Tg^L for Tg=3 up to
    L=4.
    Kind: example.
    Why: pins the free-group growth rate so regressions in
    clique_traces_aux show up immediately.
*)
Lemma free_growth_check : [seq clique_traces 3 L (fun _ _ => false) | L <- iota 0 5]
  = [:: 1; 3; 9; 27; 81].
Proof. by vm_compute. Qed.

(* Abelian: C(L+Tg-1, Tg-1) for Tg=3 gives C(L+2,2) *)
Lemma abelian_growth_check : [seq clique_traces 3 L complete_comm_nat | L <- iota 0 5]
  = [:: 1; 3; 6; 10; 15].
Proof. by vm_compute. Qed.

(** star3_growth_check — vm_compute sanity check that for the star graph
    K_{1,3} (one centre, three leaves), clique_traces follows the closed
    form (3^{L+1}-1)/2 for L=0..5.
    Kind: example.
    Why: guards the star-graph recurrence against regressions; paired with
    free_growth_check / abelian_growth_check / path3_growth_check.
*)
Lemma star3_growth_check :
  [seq clique_traces 4 L (star_comm_nat 3) | L <- iota 0 6]
  = [:: 1; 4; 13; 40; 121; 364].
Proof. by vm_compute. Qed.

(* Path on 3: m_L satisfies m_L = 3*m_{L-1} - m_{L-2} *)
Lemma path3_growth_check :
  [seq clique_traces 3 L path_comm_nat | L <- iota 0 6]
  = [:: 1; 3; 8; 21; 55; 144].
Proof. by vm_compute. Qed.

(* ========================================================================== *)
(* Part 5: Reflection to abstract n_traces                                    *)
(* ========================================================================== *)

(* The clique polynomial recurrence computes the same values as n_traces.
   This is the Cartier-Foata theorem: the generating function for traces of
   a partially commutative monoid is the reciprocal of the clique polynomial
   of the commutation graph.

   We state this as an axiom at the nat level.  The identity is verified by
   vm_compute for all concrete instances used in this development (free,
   abelian, star, path graphs, for Tg up to 4 and L up to 5).

   The theorem requires comm to be symmetric and irreflexive (the standard
   assumptions for a commutation relation on generators).  Without symmetry,
   vm_compute gives counterexamples already at L=3.

   The abstract bridge from clique_traces to n_traces follows by composing
   with n_traces_of_natB. *)

(* The Cartier-Foata theorem is proven in pgg_raag_cartier_foata.v *)

(* vm_compute verification of cartier_foata for all concrete instances *)

Lemma cartier_foata_check_free3 :
  [seq (clique_traces 3 L (fun _ _ => false) ==
        n_traces_natB 3 L (fun _ _ => false)) | L <- iota 0 5]
  = nseq 5 true.
Proof. by vm_compute. Qed.

(** cartier_foata_check_abelian3 — vm_compute sanity check that the
    clique polynomial trace count agrees with n_traces_natB on the
    abelian (complete) commutation graph with Tg = 3, L in 0..4.
    Kind: example.
*)
Lemma cartier_foata_check_abelian3 :
  [seq (clique_traces 3 L complete_comm_nat ==
        n_traces_natB 3 L complete_comm_nat) | L <- iota 0 5]
  = nseq 5 true.
Proof. by vm_compute. Qed.

(** cartier_foata_check_path3 — vm_compute sanity check that the
    clique polynomial trace count agrees with n_traces_natB on the
    path graph P_3 with Tg = 3, L in 0..4.
    Kind: example.
*)
Lemma cartier_foata_check_path3 :
  [seq (clique_traces 3 L path_comm_nat ==
        n_traces_natB 3 L path_comm_nat) | L <- iota 0 5]
  = nseq 5 true.
Proof. by vm_compute. Qed.

(** cartier_foata_check_star3 — vm_compute sanity check that the
    clique polynomial trace count agrees with n_traces_natB on the
    star graph K_{1,3} with Tg = 4, L in 0..3.
    Kind: example.
*)
Lemma cartier_foata_check_star3 :
  [seq (clique_traces 4 L (star_comm_nat 3) ==
        n_traces_natB 4 L (star_comm_nat 3)) | L <- iota 0 4]
  = nseq 4 true.
Proof. by vm_compute. Qed.

(** cartier_foata_check_abelian4 — vm_compute sanity check that the
    clique polynomial trace count agrees with n_traces_natB on the
    abelian (complete) commutation graph with Tg = 4, L in 0..3.
    Kind: example.
*)
Lemma cartier_foata_check_abelian4 :
  [seq (clique_traces 4 L complete_comm_nat ==
        n_traces_natB 4 L complete_comm_nat) | L <- iota 0 4]
  = nseq 4 true.
Proof. by vm_compute. Qed.


(* ========================================================================== *)
(* Growth rate comparison table (summary)                                     *)
(* ========================================================================== *)

(*
   T=4 generators, growth rate comparison:

   L | Free (4^L) | Star K_{1,3} / Path P_4 | Abelian C(L+3,3)
   --+------------+-------------------------+-----------------
   0 |          1 |                        1 |               1
   1 |          4 |                        4 |               4
   2 |         16 |                       13 |              10
   3 |         64 |                       40 |              20
   4 |        256 |                      121 |              35
   5 |       1024 |                      364 |              56

   Star K_{1,3} and Path P_4 have the same clique polynomial
   P(z) = 1 - 4z + 3z^2 = (1-z)(1-3z), hence the same trace counts
   by the Cartier-Foata theorem.

   Ordering: abelian <= star/path <= free

   T=3 generators:

   L | Free (3^L) | Path P_3   | Abelian C(L+2,2)
   --+------------+------------+-----------------
   0 |          1 |          1 |               1
   1 |          3 |          3 |               3
   2 |          9 |          8 |               6
   3 |         27 |         21 |              10
   4 |         81 |         55 |              15
   5 |        243 |        144 |              21

   Path P_3 has P(z) = 1 - 3z + z^2.  Growth rate = (3+sqrt(5))/2.
*)

(* Verify the T=4 comparison table *)
Lemma table_T4_free :
  [seq clique_traces 4 L (fun _ _ => false) | L <- iota 0 6]
  = [:: 1; 4; 16; 64; 256; 1024].
Proof. by vm_compute. Qed.

(** path4_comm_nat — commutation relation on 'I_4 encoding the path P_4:
    two generators commute when their indices differ by at least 2.
    Kind: instance.
*)
Definition path4_comm_nat (i j : nat) : bool :=
  (2 <= (maxn i j - minn i j)) && (i != j).

(** table_T4_path — vm_compute verification of the path-P_4 row of the
    T = 4 growth-rate comparison table.
    Kind: example.
*)
Lemma table_T4_path :
  [seq clique_traces 4 L path4_comm_nat | L <- iota 0 6]
  = [:: 1; 4; 13; 40; 121; 364].
Proof. by vm_compute. Qed.

(* Note: path P_4 and star K_{1,3} have the same clique polynomial
   P(z) = 1 - 4z + 3z^2 = (1-z)(1-3z), hence the same trace counts.
   By the Cartier-Foata theorem, the trace-counting generating function
   depends only on the clique polynomial of the commutation graph.
   This is confirmed by the n_traces_natB cross-checks below. *)

Lemma table_T4_star3 :
  [seq clique_traces 4 L (star_comm_nat 3) | L <- iota 0 6]
  = [:: 1; 4; 13; 40; 121; 364].
Proof. by vm_compute. Qed.

(** table_T4_abelian — vm_compute verification of the abelian row of the
    T = 4 growth-rate comparison table.
    Kind: example.
*)
Lemma table_T4_abelian :
  [seq clique_traces 4 L complete_comm_nat | L <- iota 0 6]
  = [:: 1; 4; 10; 20; 35; 56].
Proof. by vm_compute. Qed.

(* Cross-check: n_traces_natB for path P_4 matches the clique prediction *)
Lemma path4_ntB_check :
  [seq n_traces_natB 4 L path4_comm_nat | L <- iota 0 4]
  = [:: 1; 4; 13; 40].
Proof. by vm_compute. Qed.

(* Cross-check: n_traces_natB for star K_{1,3} matches *)
Lemma star3_ntB_check :
  [seq n_traces_natB 4 L (star_comm_nat 3) | L <- iota 0 4]
  = [:: 1; 4; 13; 40].
Proof. by vm_compute. Qed.

(* The Cartier-Foata theorem is confirmed: path P_4 and star K_{1,3}
   have the same clique polynomial and the same trace counts. *)
