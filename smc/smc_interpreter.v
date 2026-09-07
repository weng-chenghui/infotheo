From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg ring.
From mathcomp Require Import reals finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.

(**md**************************************************************************)
(* # Interpreter for Secure Multiparty Protocols                              *)
(*                                                                            *)
(* Unindexed process type for simple interpretation.                          *)
(* Session types and fuel are handled separately in smc_session_types.v.      *)
(*                                                                            *)
(* ```                                                                        *)
(*                proc == unindexed process type                              *)
(*   [procs p1;..;pn ] == pack processes into seq proc                        *)
(*            Sample f == draw the head of the party's own seed stream        *)
(*       interp_traces == traces of a run, as h-bounded seqs                  *)
(* ```                                                                        *)
(*                                                                            *)
(* Each party carries a seed stream beside its trace.  A Sample draws the     *)
(* head of that stream and writes nothing to the trace, so every trace        *)
(* entry is the program's image of the drawn values.                          *)
(*                                                                            *)
(* The reduction relation below is read at a fixed seed assignment, so an     *)
(* rsteps models at most one draw per party; interp consumes the stream.      *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section interp.
Variable data : Type.

(* Unindexed process type - no fuel or session type indices *)
(* This simplifies interpreter and relational semantics proofs *)
Inductive proc : Type :=
  | Init : data -> proc -> proc
  | Send : nat -> data -> proc -> proc
  | Recv : nat -> (data -> proc) -> proc
  | Sample : (data -> proc) -> proc
  | Ret : data -> proc
  | Finish : proc
  | Fail : proc.

(* Default process for out-of-bounds access *)
Definition default_proc : proc := Fail.

(* TODO: the result of step is a nameless 4-tuple read by .1.1.1, .1.1.2,
   .1.2 and .2 throughout this file and smc_interpreter_sound.v.  The record
   below names the four components; adopting it means re-running the
   soundness proofs that destructure the tuple.
     Record step_result := {
       step_proc  : proc ;       (* the party's next process *)
       step_trace : seq data ;   (* its trace after the step *)
       step_seed  : seq data ;   (* its remaining seed stream *)
       step_fired : bool }.      (* whether the step made progress *)
   *)

(* Step function for process list.  [Sample f] consumes the head of the
   running party's seed stream and passes it to the continuation; an
   exhausted stream blocks the party instead of fabricating a value. *)
Definition step (ps : seq proc) (trace seed : seq data) (i : nat) :=
  let p := nth default_proc ps i in
  let nop := (p, trace, seed, false) in
  match p with
  | Recv frm f =>
      match nth default_proc ps frm with
      | Send dst v next =>
          if dst == i then (f v, v::trace, seed, true) else nop
      | _ => nop
      end
  | Send dst w next =>
      match nth default_proc ps dst with
      | Recv frm f =>
          if frm == i then (next, trace, seed, true) else nop
      | _ => nop
      end
  | Init d next =>
      (next, d::trace, seed, true)
  | Sample f =>
      if seed is r :: seed' then (f r, trace, seed', true) else nop
  | Ret d =>
      (Finish, d :: trace, seed, true)
  | Finish => nop
  | Fail => nop
  end.

(* Fuel-bounded driver: each round runs step at every party and keeps going
   while any party fired, returning the final processes, traces and seeds. *)
Fixpoint interp h (ps : seq proc) (traces : seq (seq data))
                  (seeds : seq (seq data)) :=
  if h is h.+1 then
    let res := [seq step ps (nth [::] traces i) (nth [::] seeds i) i
               | i <- iota 0 (size ps)] in
    if has snd res then
      let ps' := unzip1 (unzip1 (unzip1 res)) in
      let trs' := unzip2 (unzip1 (unzip1 res)) in
      let sds' := unzip2 (unzip1 res) in
      interp h ps' trs' sds'
    else (ps, traces, seeds)
  else (ps, traces, seeds).

(* Entry point: run the interpreter from empty traces for the given fuel. *)
Definition run_interp h procs seeds :=
  interp h procs (nseq (size procs) [::]) seeds.

Local Open Scope tuple_ext_scope.
Local Open Scope fset_scope.

(* Lenses (from qecc) name the subset of parties a reduction touches. *)
Section lens.
Variables n m : nat.
(* A choice of m party indices among n, addressing a sub-tuple. *)
Definition lens : Type := m.-tuple 'I_n.
Variables (l : lens) (T : Type).
(* Read the m selected entries out of a full n-tuple. *)
Definition extract (t : n.-tuple T) := map_tuple (tnth t) l.
(* Write m new entries back into a full n-tuple at the selected positions. *)
Definition inject (t : n.-tuple T) (t' : m.-tuple T) :=
  [tuple nth (t !_ i) t' (index i l) | i < n].
End lens.

(* extract commutes with a pointwise map: lets the soundness proof push
   data transformations through the lens. *)
Lemma map_extract n m A B (l : lens n m) (f : A -> B) v :
  map_tuple f (extract l v) = extract l (map_tuple f v).
Proof. by apply: eq_from_tnth => i; rewrite !tnth_map. Qed.

(* Relational reduction - single step reductions.
   The relation is read at one seed assignment, so a sampling party draws that
   stream's head.  A run therefore models at most one draw per party. *)
Inductive rstep {n} (sds : n.-tuple (seq data)) : forall {m}, lens n m ->
      m.-tuple proc -> m.-tuple proc -> m.-tuple (seq data) -> Prop :=
  | rinit i x p : rstep sds [tuple i] [tuple Init x p] [tuple p] [tuple [:: x]]
  | rret i x : rstep sds [tuple i] [tuple Ret x] [tuple Finish] [tuple [:: x]]
  | rcomm i j x pi pj :
    rstep sds [tuple i; j] [tuple Send j x pi; Recv i pj] [tuple pi; pj x]
          [tuple nil; [:: x]]
  | rsample i f r sd : sds !_ i = r :: sd ->
    rstep sds [tuple i] [tuple Sample f] [tuple f r] [tuple nil].

(* Reflexive transitive closure of rstep *)
Inductive rsteps {n} (sds : n.-tuple (seq data)) :
      n.-tuple proc -> n.-tuple proc -> n.-tuple (seq data) -> Prop :=
  | rone m (l : lens n m) ps ps' traces :
    rstep sds l (extract l ps) ps' traces ->
    rsteps sds ps (inject l ps ps') (inject l [tuple nil | _ < n] traces)
  | rrefl ps : rsteps sds ps ps [tuple nil | _ < n]
  | rtrans ps1 ps2 ps3 tr1 tr2 tr3 :
    rsteps sds ps1 ps2 tr1 -> rsteps sds ps2 ps3 tr2 ->
    tr3 = [tuple tr2 !_ i ++ tr1 !_ i | i < n] ->
    rsteps sds ps1 ps3 tr3.

(* One party's step result: the surviving process, its trace, the remaining
   seed stream, and whether it fired. *)
Definition step_resultT := (proc * seq data * seq data * bool)%type.

(* Project the surviving process out of each party's step result. *)
Definition result_procs n (res : n.-tuple step_resultT) :=
  map_tuple (fun r : step_resultT => r.1.1.1) res.
(* Project the accumulated trace out of each party's step result. *)
Definition result_traces n (res : n.-tuple step_resultT) :=
  map_tuple (fun r : step_resultT => r.1.1.2) res.

(* The step function does all possible reductions at once, at the seed
   assignment the relation is read at. *)
Lemma step_complete n m (sds : n.-tuple (seq data)) (l : lens n m) ps ps'
    traces' :
  rstep sds l (extract l ps) ps' traces' ->
  let res := extract l [tuple step ps nil (sds !_ i) i | i < n] in
  result_procs res = ps' /\
  result_traces res = traces'.
Proof.
move Hps: (extract l ps) => psl H.
case: H Hps => /=.
- move=> i x p [] Hps.
  split; apply /val_inj;
    by rewrite /= tnth_mktuple /= /step -tnth_nth Hps.
- move=> i x [] Hps.
  split; apply /val_inj;
    by rewrite /= tnth_mktuple /= /step -tnth_nth Hps.
- move=> i j x pi pj [] Hi Hj.
  rewrite /result_procs /result_traces !map_extract.
  split; apply /val_inj; congr ([:: _; _]);
    rewrite /= tnth_map tnth_mktuple /= /step;
    by rewrite -tnth_nth (Hi,Hj) -tnth_nth (Hi,Hj) eqxx.
- move=> i f r sd Hsd [] Hps.
  split; apply /val_inj;
    by rewrite /= tnth_mktuple /= /step -tnth_nth Hps Hsd.
Qed.

(* Characterization of a 2-party reduction at indices a, b: it must be a
   matched Send/Recv pair. The reflection target for rstep2P. *)
Variant rstep2_spec n (ps : n.-tuple proc) (a b : 'I_n) : Prop :=
  | Rstep2Comm x pi pj of
      ps !_ a = Send b x pi & ps !_ b = Recv a pj
    : rstep2_spec ps a b.

(* Invert a 2-party rstep into the Send/Recv pair that produced it. *)
Lemma rstep2P n (sds : n.-tuple (seq data)) (ps : n.-tuple proc)
    (a b : 'I_n) ps' traces :
  rstep sds [tuple a; b] (extract [tuple a; b] ps) ps' traces ->
  rstep2_spec ps a b.
Proof.
inversion 1; subst.
exact: (Rstep2Comm (esym H3) (esym H4)).
Qed.

(* Two reductions fireable from one state are either identical or act on
   disjoint party indices.  That disjointness lets the soundness proof
   compose per-party reductions in any order. *)
Lemma rstep_disjoint n m p (sds : n.-tuple (seq data)) (ps : n.-tuple proc)
  (l1 : lens n m) (l2 : lens n p) psl1 psl2 ps1 tr1 ps2 tr2 :
  psl1 = extract l1 ps -> psl2 = extract l2 ps ->
  rstep sds l1 psl1 ps1 tr1 -> rstep sds l2 psl2 ps2 tr2 ->
  l1 == l2 :> seq _ /\ ps1 = ps2 :> seq _ /\ tr1 = tr2 :> seq _
  \/ {in l1 & l2, forall a b, a != b}.
  (* [disjoint l1 & l2] *)
Proof.
move=> Hpsl1 Hpsl2 Hred1 Hred2.
(* Fallback: the constructor equality is consumed as a view in destructuring
   position, so goal-level congr does not apply.  The equation between the two
   indices is kept as [Eii'] instead of being substituted, because two sampling
   reductions at one index need it to compare their seed streams. *)
case: Hred1 Hpsl1 =>
  [i j pi | i x | i j x pi pj | i f r sd Hsd] /(congr1 val) /= [] Hpi;
case: Hred2 Hpsl2 =>
  [i' j' pi' | i' x' | i' j' x' pi' pj' | i' f' r' sd' Hsd']
    /(congr1 val) /=[];
  (have [Eii'|ii' Hpi'] := eqVneq i i'; [rewrite -Eii' -Hpi // => -[]
   | right => a b; rewrite !inE; try by do! move /eqP ->]).
 by move=> <- <-; left.
 move=> /eqP-> /orP[] /eqP->; apply/eqP => ij; by rewrite ij -(Hpi',H) in Hpi.
 by move=> <-; left.
 move=> /eqP-> /orP[] /eqP->; apply/eqP => ij; by rewrite ij -(Hpi',H) in Hpi.
 move=> /orP[] /eqP-> /eqP->; apply/eqP => ij; by rewrite -ij -(Hpi,H) in Hpi'.
 move=> /orP[] /eqP-> /eqP->; apply/eqP => ij; by rewrite -ij -(Hpi,H) in Hpi'.
 by move=> /val_inj -> -> -> <- [] <-; left.
 move: H H0.
  have [<-|jj' Hpj' Hpj] := eqVneq j j'.
    by move=> <- [] /val_inj /eqP; rewrite (negbTE ii').
  move=> /orP[] /eqP -> /orP[] /eqP -> //; apply/eqP => ij.
  + by rewrite ij -Hpj' in Hpi.
  + by rewrite ij -Hpi' in Hpj.
 move=> /orP[] /eqP-> /eqP->; apply/eqP => ij; by rewrite -ij -(Hpi,H) in Hpi'.
 move=> /eqP-> /orP[] /eqP->; apply/eqP => ij; by rewrite ij -(Hpi',H) in Hpi.
move=> Eff'; rewrite Eii' Hsd' in Hsd; case: Hsd => Err' _.
by left; rewrite Eff' Err'.
Qed.

Lemma extract_inject_disj n m m' A
      (l : lens n m) (l' : lens n m') (ps : n.-tuple A) ps' :
  {in l & l', forall a b : 'I_n, a != b} ->
  extract l' (inject l ps ps') = extract l' ps.
Proof.
move=> Hdisj.
apply: eq_from_tnth => i.
rewrite !(tnth_mktuple,tnth_map) nth_default //.
rewrite leqNgt size_tuple -{2}(size_tuple l) index_mem.
apply/negP => Hi.
move: (Hdisj (l' !_ i) (l' !_ i)) => /=.
by rewrite Hi mem_tnth eqxx => /(_ isT isT).
Qed.

Lemma injectC_disj n m m' A
      (l : lens n m) (l' : lens n m') (ps : n.-tuple A) ps1 ps2 :
  {in l & l', forall a b : 'I_n, a != b} ->
  inject l' (inject l ps ps1) ps2 = inject l (inject l' ps ps2) ps1.
Proof.
move=> Hdisj.
apply: eq_from_tnth => i.
rewrite !(tnth_mktuple,tnth_map).
case/boolP: (i \in l') => il'.
  have Hps1 : (size ps1 <= index i l)%N.
    rewrite size_tuple -{1}(size_tuple l) leqNgt index_mem.
    apply/negP => il.
    by move: (Hdisj i i); rewrite il il' eqxx => /(_ isT isT).
  by rewrite !(nth_default _ (n:=index i l)).
have Hps2 : (size ps2 <= index i l')%N.
  by rewrite size_tuple -{1}(size_tuple l') leqNgt index_mem.
by rewrite !(nth_default _ (n:=index i l')).
Qed.

Definition concat_traces n (tr1 tr2 : n.-tuple (seq data)) :=
  [tuple tr1 !_ i ++ tr2 !_ i | i < n].
Definition empty_traces {n} := [tuple (@nil data) | _ < n].

(* Alternative definition of reduction, better for induction *)
Inductive rstepl {n} (sds : n.-tuple (seq data)) :
      n.-tuple proc -> n.-tuple proc -> n.-tuple (seq data) -> Prop :=
  | rnil ps : rstepl sds ps ps [tuple nil | _ < n]
  | rcons m (l : lens n m) ps ps1 ps2 tr1 tr2 tr3 :
    rstep sds l (extract l ps) ps1 tr1 ->
    rstepl sds (inject l ps ps1) ps2 tr2 ->
    tr3 = concat_traces tr2 (inject l empty_traces tr1) ->
    rstepl sds ps ps2 tr3.

Lemma rconcat n (sds : n.-tuple (seq data)) (ps ps1 ps2 : n.-tuple proc)
    tr1 tr2 :
  rstepl sds ps ps1 tr1 -> rstepl sds ps1 ps2 tr2 ->
  rstepl sds ps ps2 (concat_traces tr2 tr1).
Proof.
elim: ps ps1 tr1 / => [ps Hr|].
  rewrite (_ : concat_traces _ _ = tr2) //.
  by apply: eq_from_tnth => i; rewrite !tnth_mktuple cats0.
move=> m l ps ps1 ps3 tr3 tr4 tr' Hr Hrl1 IH Htr' Hrl2.
apply: (rcons Hr).
  exact: (IH Hrl2).
by apply: eq_from_tnth => i; rewrite Htr' !tnth_mktuple catA.
Qed.

(* Equiavalence of of rsteps and rstepl *)
Lemma rstepsP n (sds : n.-tuple (seq data)) (ps1 ps2 : n.-tuple proc) tr :
  rsteps sds ps1 ps2 tr <-> rstepl sds ps1 ps2 tr.
Proof.
split.
- elim: ps1 ps2 tr/ =>
    [m l ps ps1 tr1 Hr | ps | ps ps1 ps3 tr1 tr3 tr4 Hr1 IH1 Hr2 IH2 ->].
  + apply: (rcons Hr).
      exact: rnil.
    apply: eq_from_tnth => i.
    by rewrite !tnth_mktuple.
  + exact: rnil.
  + exact: (rconcat IH1 IH2).
elim: ps1 ps2 tr / => [ps |].
  exact: rrefl.
move=> m l ps ps1 ps2 tr1 tr2 tr' Hr Hrl1 IH ->.
exact: (rtrans (rone Hr) IH).
Qed.

Lemma cat_inj_right A (s : seq A) : injective (cat s).
Proof. by move=> s1 s2; elim: s => //= a s IH []. Qed.

Lemma cat_inj_left A (s : seq A) : injective (cat ^~ s).
Proof.
move=> s1 s2 /(f_equal rev).
rewrite !rev_cat => /cat_inj_right /(f_equal rev).
by rewrite !revK.
Qed.

(* Uniqueness of normal forms *)
(* Note that alone, this gives neither confluence nor termination.
   However, as sound as we have termination, we get confluence,
   and we also proved that the pismc sublanguage is terminating. *)
Lemma rstepl_normalisation n (sds : n.-tuple (seq data))
    (ps ps1 ps2 : n.-tuple proc) tr1 tr2 :
  rstepl sds ps ps1 tr1 ->
  (forall m (l : lens n m) ps' tr', ~ rstep sds l (extract l ps1) ps' tr') ->
  rstepl sds ps ps2 tr2 ->
  exists tr3, rstepl sds ps2 ps1 tr3 /\ tr1 = concat_traces tr3 tr2.
Proof.
move=> Hr1 Hterm.
pose tr0 := @empty_traces n.
elim: ps ps1 tr1 / Hr1 ps2 tr2 Hterm =>
  [ps | m l ps ps1 ps3 tr1 tr3 tr4 Hr Hrl1 IH ->] /= ps2 tr2 Hterm Hr2.
  exists tr2.
  case: ps ps2 tr2 / Hr2 Hterm => [ps Hterm |].
    do! split => //.
      exact: rnil.
    by apply eq_from_tnth => i; rewrite !tnth_mktuple.
  move=> m l ps ps1 ps2 t1 tr2 tr3 Hr _ _ Hterm.
  elim: (Hterm _ _ _ _ Hr).
elim: ps ps2 tr2 / Hr2 ps1 ps3 tr1 tr3 Hr Hrl1 IH Hterm =>
    [ps | m' l' ps ps2 ps3' tr2 tr3' tr4' Hr' Hrl2 IH' ->]
    /= ps1 ps3 tr1 tr3 Hr1 Hrl1 IH Hterm.
  pose tr3' := concat_traces tr3 (inject l empty_traces tr1).
  exists tr3'.
  do! split => //.
  - exact: (rcons Hr1 Hrl1).
  - by apply: eq_from_tnth => i; rewrite !tnth_mktuple cats0.
case:(rstep_disjoint (erefl (extract l ps)) (erefl (extract l' ps)) Hr1 Hr').
  case => /eqP ll'.
  have mm' : m = m'.
    by rewrite -(size_tuple l) -(size_tuple l') -ll'.
  case: m' / mm' l' ps2 tr2 ll' Hr' Hrl2 IH' => l' ps2 tr2 ll' Hr' Hrl2 IH'.
  have {}ll' : l = l' by apply: val_inj.
  rewrite -ll' in Hr' *.
  case => ps12 tr12.
  have {}ps12 : ps1 = ps2 by apply: val_inj.
  have {}tr12 : tr1 = tr2 by apply: val_inj.
  subst l' ps2 tr2.
  case: (IH _ _ Hterm Hrl2) => tr1' [Hrl3] Htr3.
  exists tr1'.
  do! split => //.
  by apply: eq_from_tnth => i; rewrite !(tnth_mktuple,catA,Htr3).
move=> /= ll'.
rewrite extract_inject_disj in IH'; last first.
  by move=> a b Ha Hb; rewrite eq_sym; apply: ll'.
pose tr2' := inject l' tr0 tr2.
have Hrll' :
  rstepl sds (inject l ps ps1) (inject l' (inject l ps ps1) ps2) tr2'.
  apply: (rcons (l:=l')).
      rewrite extract_inject_disj //.
      exact: Hr'.
    exact: rnil.
  by apply: eq_from_tnth => i; rewrite !tnth_mktuple.
case: (IH _ _ Hterm Hrll').
move => tr3a [Hrl3] Htr3.
rewrite injectC_disj // in Hrl3.
have [] // := IH' _ _ _ _ Hr1 Hrl3.
- move=> ps5 tr5 Hterm' Hrl5.
  rewrite injectC_disj // in Hrl5.
  have Hrl5' := rconcat Hrll' Hrl5.
  case: (IH _ _ Hterm Hrl5') => tr6 [Hrl53] Htr6.
  exists tr6; split => //.
  move: Htr6; rewrite Htr3 => H.
  apply: eq_from_tnth => i; move/(f_equal (fun t => tnth t i)): H.
  by rewrite !tnth_mktuple catA => /cat_inj_left.
- by move=> a b Ha Hb; rewrite eq_sym; apply: ll'.
move=> tr3b [Hrl3'] Htr3b.
exists tr3b; split => //.
apply: eq_from_tnth => i.
move/(f_equal (fun t => tnth t i)): Htr3b.
rewrite Htr3 !tnth_mktuple catA => <-.
case/boolP: (i \in l) => il.
  rewrite nth_default ?cats0 //.
  rewrite size_tuple -{1}(size_tuple l') leqNgt index_mem.
  apply/negP => il'.
  by move: (ll' i i); rewrite il il' eqxx => /(_ isT isT).
symmetry; rewrite nth_default ?cats0 //.
by rewrite size_tuple -{1}(size_tuple l) leqNgt index_mem.
Qed.
End interp.

Arguments Finish {data}.
Arguments Fail {data}.
Arguments Init {data}.
Arguments Send {data}.
Arguments Recv {data}.
Arguments Sample {data}.
Arguments Ret {data}.

Section sampling.
Variable data : Type.

(* A Sample substitutes the head of the party's stream into its continuation,
   advances the stream, and leaves the trace alone. *)
Lemma step_sample (ps : seq (proc data)) tr i f r sd :
  nth (default_proc data) ps i = Sample f ->
  step ps tr (r :: sd) i = (f r, tr, sd, true).
Proof. by rewrite /step => ->. Qed.

(* An exhausted stream blocks the party rather than fabricating a value. *)
Lemma step_sample_nil (ps : seq (proc data)) tr i f :
  nth (default_proc data) ps i = Sample f ->
  step ps tr [::] i = (Sample f, tr, [::], false).
Proof. by rewrite /step => ->. Qed.

(* One step's trace is a function of the process list and the party index
   alone.  A drawn value reaches a later trace only through the
   continuation. *)
Lemma step_trace_seed_indep (ps : seq (proc data)) tr sd1 sd2 i :
  (step ps tr sd1 i).1.1.2 = (step ps tr sd2 i).1.1.2.
Proof.
rewrite /step.
case: (nth (default_proc data) ps i) => [d p|n d p|n f|f|d| |] //.
- by case: (nth (default_proc data) ps n) => [*|*|m g|*|*| |] //=; case: ifP.
- by case: (nth (default_proc data) ps n) => [*|m w q|*|*|*| |] //=; case: ifP.
- by case: sd1 => [|r1 sd1']; case: sd2.
Qed.

(* A datum reaches party i's trace only by an Init or Ret of i, or a Send
   to i. *)
Definition trace_datum (ps : seq (proc data)) (i : nat) (d : data) : Prop :=
  (exists p, nth (default_proc data) ps i = Init d p)
  \/ nth (default_proc data) ps i = Ret d
  \/ (exists frm p, nth (default_proc data) ps frm = Send i d p).

(* One step either leaves the trace alone or prepends a single datum licensed
   by an Init, Ret or Send node.  A Sample falls in the first case, so a drawn
   value is never a trace entry. *)
Lemma step_trace_extends (ps : seq (proc data)) tr sd i :
  (step ps tr sd i).1.1.2 = tr
  \/ exists d, (step ps tr sd i).1.1.2 = d :: tr /\ trace_datum ps i d.
Proof.
rewrite /step /trace_datum.
case Hi: (nth (default_proc data) ps i) => [d p|n d p|n f|f|d| |] /=.
- by right; exists d; split=> //; left; exists p.
- case: (nth (default_proc data) ps n) => [*|*|m g|*|*| |] /=; try by left.
  by case: ifP => _; left.
- case Hn: (nth (default_proc data) ps n) => [x q|m w q|m g|g|x| |] /=;
    try by left.
  case: ifP => [/eqP Hm|_]; last by left.
  by right; exists w; split=> //; right; right; exists n, q; rewrite Hn Hm.
- by case: sd => [|r sd']; left.
- by right; exists d; split=> //; right; left.
- by left.
- by left.
Qed.

End sampling.

Section traces.
Variable data : Type.
Local Open Scope nat_scope.

(* One step appends at most one datum to the party's trace. *)
Lemma step_size_le (ps : seq (proc data)) (tr sd : seq data) (i : nat) :
  size (step ps tr sd i).1.1.2 <= (size tr).+1.
Proof.
rewrite /step.
case: (nth _ ps i) => [d1 p1|dst1 d1 p1|frm1 f1|f1|d1||] //=.
- by case: (nth _ ps dst1) => [? ?|? ? ?|? ?|?|?||] //=; case: ifP.
- by case: (nth _ ps frm1) => [? ?|? ? ?|? ?|?|?||] //=; case: ifP.
- by case: sd.
Qed.

(* Fuel bounds every party's trace length, stated by index rather than by
   membership, so the data carrier needs no eqType. *)
Lemma size_interp_nth h (ps : seq (proc data)) (trs sds : seq (seq data)) k :
  (forall i, size (nth [::] trs i) <= k) ->
  forall i, size (nth [::] (interp h ps trs sds).1.2 i) <= k + h.
Proof.
elim: h k ps trs sds => [k ps trs sds Hk i|h IH k ps trs sds Hk i] /=;
  first by rewrite addn0.
case: ifP => _; last by apply: (leq_trans (Hk i)); rewrite leq_addr.
rewrite addnS -addSn; apply: IH => j.
rewrite /unzip2 /unzip1 -3!map_comp.
case: (ltnP j (size ps)) => Hj; last first.
  by rewrite nth_default // size_map size_iota.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /=.
apply: (leq_trans (step_size_le ps (nth [::] trs j) (nth [::] sds j) j)).
by rewrite ltnS; exact: Hk.
Qed.

(* interp preserves the party count: the process and trace lists keep the
   same length as the input across all rounds. *)
Lemma size_interp h (procs : seq (proc data)) (traces seeds : seq (seq data)) :
  size procs = size traces ->
  size (interp h procs traces seeds).1.1 = size procs /\
  size (interp h procs traces seeds).1.2 = size procs.
Proof.
elim: h procs traces seeds => // h IH procs traces seeds Hsz /=.
case: ifP => _ //.
rewrite /unzip1 /unzip2 -!map_comp.
set map1 := map _ _.
set map2 := map _ _.
set map3 := map _ _.
case: (IH map1 map2 map3).
  by rewrite !size_map.
move=> -> ->.
by rewrite !size_map size_iota.
Qed.

(* Per-party fuel bound on trace length, supplying the size proof needed to
   package traces as bounded sequences. *)
Lemma size_traces_nth h (ps : seq (proc data)) (sds : seq (seq data))
    (i : nat) :
  size (nth [::] (run_interp h ps sds).1.2 i) <= h.
Proof.
rewrite /run_interp -[h]add0n; apply: size_interp_nth => j.
by rewrite nth_nseq; case: ifP.
Qed.

(* Final traces packaged as a tuple of length-bounded sequences, the form
   downstream entropy and security reasoning consumes. *)
Definition interp_traces h procs sds : (size procs).-tuple (h.-bseq data) :=
  [tuple Bseq (size_traces_nth h procs sds i) | i < size procs].

(* interp_traces is faithful: stripping the bounds recovers exactly the
   raw traces returned by run_interp. *)
Lemma interp_traces_ok h procs sds :
 map val (interp_traces h procs sds) = (run_interp h procs sds).1.2.
Proof.
apply (eq_from_nth (x0:=[::])).
  rewrite size_map /= size_map size_enum_ord.
  by rewrite (size_interp _ _ _).2 ?size_nseq.
move=> i Hi.
rewrite size_map in Hi.
rewrite (nth_map [bseq]) // /interp_traces.
rewrite size_tuple in Hi.
by rewrite (_ : i = Ordinal Hi) // nth_mktuple.
Qed.

End traces.

Section traces_eqType.
Variable data : eqType.
Local Open Scope nat_scope.

(* Membership form of [size_traces_nth]: every trace produced in h rounds has
   at most h entries. *)
Lemma size_traces h (procs : seq (proc data)) (sds : seq (seq data)) :
  forall s, s \in (run_interp h procs sds).1.2 -> size s <= h.
Proof. by move=> s /(nthP [::])[i _ <-]; exact: size_traces_nth. Qed.

End traces_eqType.

(* Convenient notations for process lists *)
Declare Scope proc_scope.

Notation "[procs p ; .. ; q ]" := 
  (cons p .. (cons q nil) ..)
  (at level 0) : proc_scope.

(******************************************************************************)
(** * Termination Predicates                                                  *)
(******************************************************************************)

Section termination.
Variable data : Type.

(* Check if a process is in a final state (Finish or Fail) *)
Definition is_final (p : proc data) : bool :=
  match p with
  | Finish => true
  | Fail => true
  | _ => false
  end.

(* Check if all processes in a list are in final states *)
Definition all_final (ps : seq (proc data)) : bool :=
  all is_final ps.

End termination.

