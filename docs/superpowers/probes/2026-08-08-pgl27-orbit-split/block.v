
(* -------------------------------------------------------------------------- *)
(* Each Boolean fiber of the classifier is one orbit of the shuffle group.    *)
(* -------------------------------------------------------------------------- *)

(** subset_class_invariant — the four-subset classifier is invariant under
    the image action of a shuffle-group element.
    @main security: the shuffle moves a four-subset without moving its
    orbit class. *)
Lemma subset_class_invariant (g : pgg_gT pgl27_M) (S : {set 'I_8}) :
  g \in pgg_G pgl27_M -> subset_class (g @: S) = subset_class S.
Proof. by move=> gG; move/stabpP: (subsetP G_sub_stabp _ gG); apply. Qed.

(* The word layer: generator indices act on codes by the tables above. *)
Local Definition wgenn (i : nat) : nat -> nat :=
  if i == 0 then trn else if i == 1 then scn else invn.

(* Application of a word, left to right, to a single code. *)
Local Definition papply (w : seq nat) (a : nat) : nat :=
  foldl (fun x i => wgenn i x) a w.

(* The generator perm selected by a word index. *)
Local Definition gen_of (i : nat) : {perm 'I_8} :=
  tnth pgl27_gens (if i == 0 then @Ordinal 3 0 isT
                   else if i == 1 then @Ordinal 3 1 isT
                   else @Ordinal 3 2 isT).

(* A word folded into the composite shuffle permutation. *)
Local Definition word_perm (w : seq nat) : {perm 'I_8} :=
  foldl (fun g i => (g * gen_of i)%g) 1%g w.

Local Lemma gen_of_val (i : nat) (x : 'I_8) :
  val (gen_of i x) = wgenn i (val x).
Proof.
rewrite /gen_of /wgenn; case: (i == 0); first exact: gen0_val.
by case: (i == 1); [exact: gen1_val | exact: gen2_val].
Qed.

Local Lemma gen_of_mem (i : nat) : gen_of i \in pgg_G pgl27_M.
Proof.
apply: mem_gen; apply/imsetP; rewrite /gen_of.
case: (i == 0); first by exists (@Ordinal 3 0 isT).
case: (i == 1); first by exists (@Ordinal 3 1 isT).
by exists (@Ordinal 3 2 isT).
Qed.

Local Lemma word_perm_mem (w : seq nat) : word_perm w \in pgg_G pgl27_M.
Proof.
rewrite /word_perm.
have g1 : 1%g \in pgg_G pgl27_M by exact: group1.
elim: w (1%g) g1 => [|i w IH] g gG //=.
by apply: IH; apply: groupM => //; exact: gen_of_mem.
Qed.

Local Lemma word_perm_val (w : seq nat) (x : 'I_8) :
  val (word_perm w x) = papply w (val x).
Proof.
rewrite /word_perm /papply.
have H : forall (w' : seq nat) (g : {perm 'I_8}) (y : 'I_8),
    val (foldl (fun h i => (h * gen_of i)%g) g w' y)
    = foldl (fun a i => wgenn i a) (val (g y)) w'.
  by elim=> [|i w' IH] g y //=; rewrite IH permM gen_of_val.
by rewrite H perm1.
Qed.

(* -------------------------------------------------------------------------- *)
(* Finite reachability certificate: a fueled BFS over four-subsets.           *)
(* -------------------------------------------------------------------------- *)

(* One generator step on a four-subset, in ascending canonical form. *)
Local Definition sstep (i : nat) (L : seq nat) : seq nat :=
  sort leq (map (wgenn i) L).

(* Fueled BFS over four-subsets, one carrying word per reached subset. *)
Local Fixpoint set_bfs (fuel : nat) (seen : seq (seq nat * seq nat)) :
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

(* The representative four-subset of each Boolean class, as a code list. *)
Local Definition rep_list (b : bool) : seq nat :=
  if b then [:: 0; 1; 2; 4] else [:: 0; 1; 2; 3].

Local Definition set_table (b : bool) : seq (seq nat * seq nat) :=
  set_bfs 12 [:: (rep_list b, [::])].

(* Every ascending four-list of verdict b carries a word from rep_list b.
   The check recomputes each word from scratch, so a BFS bookkeeping error
   cannot make it true. *)
Local Definition set_table_ok (b : bool) : bool :=
  all (fun L => (nclass L == b) ==>
         has (fun sw : seq nat * seq nat =>
                sort leq (map (papply sw.2) (rep_list b)) == L)
             (set_table b))
      sorted4.

Local Lemma set_table_okT : set_table_ok true. Proof. by vm_compute. Qed.
Local Lemma set_table_okF : set_table_ok false. Proof. by vm_compute. Qed.

(* -------------------------------------------------------------------------- *)
(* From the code-level certificate to subsets of the projective line.         *)
(* -------------------------------------------------------------------------- *)

(* The image of a code-coded subset is coded by the word applied codewise. *)
Local Lemma word_perm_imset (w : seq nat) (L : seq nat) :
  all (fun n => (n < 8)%N) L ->
  word_perm w @: list_to_set L = list_to_set (map (papply w) L).
Proof.
move=> HL; apply/setP => x; apply/imsetP/idP => [[y]|Hx].
  rewrite inE => yL ->; rewrite inE; apply/mapP.
  by exists (val y); rewrite // word_perm_val.
move: Hx; rewrite inE => /mapP[a aL Ha].
have Ha8 : (a < 8)%N by move/allP: HL => /(_ a aL).
exists (Ordinal Ha8); first by rewrite inE.
by apply/val_inj; rewrite word_perm_val.
Qed.

(* list_to_set reads membership only, so sorting the code list is invisible. *)
Local Lemma list_to_set_sort (L : seq nat) :
  list_to_set (sort leq L) = list_to_set L.
Proof. by apply/setP => i; rewrite !inE mem_sort. Qed.

(* The code list of a four-subset's enumeration is an ascending four-list. *)
Local Lemma asc4_val_enum (S : {set 'I_8}) :
  #|S| = 4 -> asc4 (map val (enum S)).
Proof.
move=> HcS; rewrite /asc4 sorted_val_enum /=; apply/andP; split.
  by apply/allP => n /mapP[i _ ->]; exact: ltn_ord.
by rewrite size_map -cardE HcS.
Qed.

(* Every four-subset is a shuffle image of the representative of its class. *)
Local Lemma subset_class_reach (S : {set 'I_8}) :
  #|S| = 4 ->
  exists w : seq nat,
    S = word_perm w @: list_to_set (rep_list (subset_class S)).
Proof.
move=> HcS.
have AL : asc4 (map val (enum S)) by exact: asc4_val_enum.
have Hcl : nclass (map val (enum S)) = subset_class S by rewrite subset_classE.
have Hmem := sorted4_complete _ AL.
have Hok : set_table_ok (subset_class S).
  by case: (subset_class S); [exact: set_table_okT | exact: set_table_okF].
have H8 : all (fun n => (n < 8)%N) (rep_list (subset_class S))
  by case: (subset_class S).
move: Hok => /allP/(_ _ Hmem)/implyP.
rewrite Hcl eqxx => /(_ isT)/hasP[[L w] /= _ /eqP Hw].
exists w; rewrite (word_perm_imset w _ H8).
by rewrite -list_to_set_sort Hw list_to_setK.
Qed.

(* -------------------------------------------------------------------------- *)
(* The orbit split.                                                           *)
(* -------------------------------------------------------------------------- *)

(* A product of shuffles acts by successive images. *)
Local Lemma imsetM (g h : {perm 'I_8}) (A : {set 'I_8}) :
  (g * h)%g @: A = h @: (g @: A).
Proof. by rewrite -imset_comp; apply: eq_imset => x; rewrite permM. Qed.

(* The inverse shuffle undoes the image of a shuffle. *)
Local Lemma perm_imsetK (g : {perm 'I_8}) (A : {set 'I_8}) :
  (g^-1)%g @: (g @: A) = A.
Proof.
apply/setP => x; apply/imsetP/idP => [[y /imsetP[z zA ->] ->]|xA].
  by rewrite permK.
by exists (g x); [apply/imsetP; exists x | rewrite permK].
Qed.

(** subset_class_orbit — two four-subsets of the projective line carry the
    same classifier value exactly when one is the shuffle image of the other.
    @main architecture: each Boolean fiber of the classifier is a single
    orbit of the PGL(2,7) shuffle group on four-subsets. *)
Lemma subset_class_orbit (S T : {set 'I_8}) :
  #|S| = 4 -> #|T| = 4 ->
  (subset_class S = subset_class T <->
   exists g : pgg_gT pgl27_M, g \in pgg_G pgl27_M /\ T = g @: S).
Proof.
move=> HcS HcT; split => [Hcl|[g [gG ->]]]; last first.
  by rewrite (subset_class_invariant _ _ gG).
have [w1 Hw1] := subset_class_reach _ HcS.
have [w2 Hw2] := subset_class_reach _ HcT.
rewrite Hcl in Hw1.
exists ((word_perm w1)^-1 * word_perm w2)%g; split.
  by apply: groupM; [rewrite groupV|]; exact: word_perm_mem.
by rewrite Hw2 Hw1 imsetM perm_imsetK.
Qed.

(** subset_class_orbitE — the orbit of a four-subset under the shuffle group
    is the classifier fiber it belongs to.
    @main architecture: the equianharmonic fiber and the harmonic fiber are
    the two orbits of the PGL(2,7) shuffle group on four-subsets. *)
Lemma subset_class_orbitE (S : {set 'I_8}) :
  #|S| = 4 ->
  orbit 'P^* (pgg_G pgl27_M) S
  = [set T : {set 'I_8} | (#|T| == 4) && (subset_class T == subset_class S)].
Proof.
move=> HcS; apply/setP => T; rewrite inE.
apply/orbitP/andP => [[g gG <-]|[/eqP HcT /eqP Hcl]].
  have ginj : injective g by exact: perm_inj.
  rewrite (card_imset _ ginj) HcS eqxx /=; split=> //; apply/eqP.
  exact: (subset_class_invariant g S gG).
have [g [gG ->]] : exists g : pgg_gT pgl27_M,
    g \in pgg_G pgl27_M /\ T = g @: S
  by apply/(subset_class_orbit S T HcS HcT); exact: (esym Hcl).
by exists g.
Qed.
