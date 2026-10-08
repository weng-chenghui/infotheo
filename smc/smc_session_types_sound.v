From HB Require Import structures.
From mathcomp Require Import all_boot.
Require Import ssr_ext smc_interpreter smc_session_types.

(**md**************************************************************************)
(* # Relational semantics of session environments                             *)
(*                                                                            *)
(* One communication consumes a send head and its matching receive head.      *)
(* `stype_rsteps` closes it reflexively and transitively. The round           *)
(* `stype_step`, the fuel loop `stypes_interp` and compatibility              *)
(* `stypes_compat` are sound for this semantics.                              *)
(*                                                                            *)
(* The objects are protocol types: `stype` has `STSend j d k`, `STRecv i d k` *)
(* and `STEnd`, with no data, only the data kind `d`. `stype_step_sound`      *)
(* states that running `stype_step` once at every party gives a tuple of      *)
(* types that `stype_rsteps` reaches from the input: one functional round is  *)
(* a reduction path of the relational semantics.                              *)
(*                                                                            *)
(* ```                                                                        *)
(*            stype_rstep l qs qs' == one communication at the 2-lens l       *)
(* stype_comm_available_at l ps qs == that communication, available in ps     *)
(*             stype_rsteps ps ps' == reflexive transitive closure, n parties *)
(*                 stypes_round ps == one parallel round of stype_step        *)
(*                stype_fires ps i == party i fires in the round              *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section stype_rstep.
Variable dtype : eqType.
Local Notation stype := (stype dtype).

(* One communication: the send head at party `i` and the matching receive
   head at party `j` are consumed together. It is the session-type
   counterpart of `rcomm` and the only reduction of session types. *)
Variant stype_rstep {n} :
    lens n 2 -> 2.-tuple stype -> 2.-tuple stype -> Prop :=
  | stype_rcomm (i j : 'I_n) d si sj :
      stype_rstep [tuple i; j]
        [tuple STSend j d si; STRecv i d sj] [tuple si; sj].

End stype_rstep.

(* `extract [tuple a; b] ps = [tuple tnth ps a; tnth ps b]` reads the types
   of parties `a` and `b` out of the `n`-party environment as a 2-tuple.
   `stype_rstep` is defined on that 2-tuple, the local view of the two
   parties, not on the `n`-tuple. A communication between `a` and `b`
   available in `ps` is therefore written
   `stype_rstep [tuple a; b] (extract [tuple a; b] ps) qs`, abbreviated
   `stype_comm_available_at [tuple a; b] ps qs`. The converse
   `inject [tuple a; b] ps qs` writes `qs` back at the positions `a` and
   `b` of `ps`; the other `n - 2` parties keep their types. When `qs` holds
   the two continuations, the result is the environment in which `a` and
   `b` have continued, `stypes_continue_at [tuple a; b] ps qs`. *)

(* A communication between the two parties of `l`, available in `ps`, with
   continuations `qs`. *)
Notation stype_comm_available_at l ps qs := (stype_rstep l (extract l ps) qs).

(* The environment `ps` after the two parties of `l` continue as `qs`. *)
Notation stypes_continue_at l ps qs := (inject l ps qs).

Section stype_sound.
Variable dtype : eqType.
Local Notation stype := (stype dtype).

(* `stype_rsteps ps ps'` holds when `ps'` is reachable from `ps` by zero or
   more communications. One communication rewrites the two parties of a
   lens and leaves the others unchanged. *)
Inductive stype_rsteps {n} : n.-tuple stype -> n.-tuple stype -> Prop :=
  | stype_rone (l : lens n 2) ps qs :
      stype_comm_available_at l ps qs ->
      stype_rsteps ps (stypes_continue_at l ps qs)
  | stype_rrefl ps : stype_rsteps ps ps
  | stype_rtrans ps1 ps2 ps3 :
      stype_rsteps ps1 ps2 -> stype_rsteps ps2 ps3 -> stype_rsteps ps1 ps3.

(* One parallel round of `stype_step` at every party, as an `n`-tuple. It
   is the body of one `stypes_interp` iteration at fixed length. *)
Definition stypes_round n (ps : n.-tuple stype) : n.-tuple stype :=
  [tuple (stype_step ps i).1 | i < n].

(* Party `i` fires in the round: `stype_step` consumes its head and returns
   the flag `true`. *)
Definition stype_fires n (ps : n.-tuple stype) (i : 'I_n) : bool :=
  (stype_step ps i).2.

(* Party `a` sends kind `d` to `b` and continues as `sa`, party `b`
   receives kind `d` from `a` and continues as `sb`. `qs` is the pair
   `(sa, sb)`. *)
Variant stype_rstep_spec n (ps : n.-tuple stype) (a b : 'I_n)
    (qs : 2.-tuple stype) : Prop :=
  | StypeRstepComm d sa sb of
      tnth ps a = STSend b d sa & tnth ps b = STRecv a d sb
      & qs = [tuple sa; sb] : stype_rstep_spec ps a b qs.

(* A reduction at the lens `[tuple a; b]` is exactly a matched send at `a`
   and receive at `b`. The relation therefore contains head communications
   only. *)
Lemma stype_rstepP n (ps : n.-tuple stype) (a b : 'I_n) qs :
  stype_comm_available_at [tuple a; b] ps qs <->
  stype_rstep_spec ps a b qs.
Proof.
split.
  move Hl: [tuple a; b] => l; move Hps: (extract l ps) => psl H.
  case: H Hl Hps => i j d si sj /(congr1 val) [-> ->] /(congr1 val) /=.
  by case=> Ha Hb; apply: StypeRstepComm Ha Hb _.
case=> d sa sb Ha Hb ->.
have -> : extract [tuple a; b] ps = [tuple STSend b d sa; STRecv a d sb].
  by apply: val_inj; rewrite /= Ha Hb.
exact: stype_rcomm.
Qed.

(* Every communication available in `ps` is performed by the round: both
   parties fire and receive their continuations. The round omits none of
   the reductions of the relational semantics. *)
Lemma stype_step_complete n (l : lens n 2) (ps : n.-tuple stype) qs :
  stype_comm_available_at l ps qs ->
  extract l (stypes_round ps) = qs /\ all (stype_fires ps) l.
Proof.
move Hps: (extract l ps) => psl H.
case: H Hps => i j d si sj /(congr1 val) /= [Hi Hj].
have Hsi : stype_step ps i = (si, true).
  by rewrite /stype_step -tnth_nth Hi -tnth_nth Hj !eqxx.
have Hsj : stype_step ps j = (sj, true).
  by rewrite /stype_step -tnth_nth Hj -tnth_nth Hi !eqxx.
split; first by apply: val_inj; rewrite /= !tnth_mktuple Hsi Hsj.
by rewrite /stype_fires Hsi Hsj.
Qed.

(* Two reductions available in one environment are equal or act on
   disjoint parties. Hence the communications of one round commute. *)
Lemma stype_rstep_disjoint n (ps : n.-tuple stype) (l1 l2 : lens n 2)
    qs1 qs2 :
  stype_comm_available_at l1 ps qs1 -> stype_comm_available_at l2 ps qs2 ->
  l1 = l2 /\ qs1 = qs2 \/ {in l1 & l2, forall a b, a != b}.
Proof.
move Hp1: (extract l1 ps) => psl1 H1; move Hp2: (extract l2 ps) => psl2 H2.
case: H1 Hp1 => i j d si sj /(congr1 val) /= [Hi Hj].
case: H2 Hp2 => i' j' d' si' sj' /(congr1 val) /= [Hi' Hj'].
case: (eqVneq i i') => [Eii'|ii'].
  move: Hi' Hj'; rewrite -Eii' Hi => -[/val_inj <- <- <-].
  by rewrite Hj => -[<-]; left.
right=> a c; rewrite !inE => /orP[] /eqP -> /orP[] /eqP -> //.
- by apply/eqP => E; move: Hi; rewrite E Hj'.
- by apply/eqP => E; move: Hj; rewrite E Hi'.
- apply/eqP => E; move: Hj; rewrite E Hj' => -[/val_inj E'].
  by rewrite E' eqxx in ii'.
Qed.

(* Party `i` holds a send head whose matching receive is present, so the
   round consumes both. *)
Definition stype_send_fires n (ps : n.-tuple stype) (i : 'I_n) : bool :=
  if tnth ps i is STSend _ _ _ then stype_fires ps i else false.

(* The senders whose communication the round performs, in index order.
   Each performed communication appears once, from its send side. *)
Definition stypes_active_senders n (ps : n.-tuple stype) : seq 'I_n :=
  [seq i <- enum 'I_n | stype_send_fires ps i].

(* Sender `i` sends kind `d` to `j`, `j` receives kind `d` from `i`, and
   the round gives `i` the pair `(si, true)` and `j` the pair `(sj, true)`. *)
Variant stype_send_fires_spec n (ps : n.-tuple stype) (i : 'I_n) : Prop :=
  | StypeSendComm (j : 'I_n) d si sj of
      tnth ps i = STSend j d si & tnth ps j = STRecv i d sj
      & stype_step ps i = (si, true) & stype_step ps j = (sj, true)
    : stype_send_fires_spec ps i.

(* A firing sender has a receiver that exists, matches its kind and fires in
   the same round. *)
Lemma stype_send_firesP n (ps : n.-tuple stype) (i : 'I_n) :
  stype_send_fires ps i -> stype_send_fires_spec ps i.
Proof.
rewrite /stype_send_fires /stype_fires; case Ha: (tnth ps i) => [j d sa|//|//].
rewrite /stype_step -tnth_nth Ha.
have [jn|jn] := ltnP j n; last by rewrite nth_default ?size_tuple.
have -> : nth STEnd ps j = tnth ps (Ordinal jn) by rewrite (tnth_nth STEnd).
case Hb: (tnth _ (Ordinal jn)) => [//|i' d' sb|//] /=.
case: andP => // -[/eqP Ei' /eqP Ed'] _; subst i' d'.
have Hsa : stype_step ps i = (sa, true).
  rewrite /stype_step -tnth_nth Ha -[j]/(nat_of_ord (Ordinal jn)).
  by rewrite -tnth_nth Hb /= !eqxx.
have Hss : stype_step ps (Ordinal jn) = (sb, true).
  by rewrite /stype_step -tnth_nth Hb -tnth_nth Ha /= !eqxx.
exact: (StypeSendComm (j := Ordinal jn)) Ha Hb Hsa Hss.
Qed.

(* Only the receiver that `a` addresses can fire on the send of `a`. Two
   receivers waiting on `a` cannot both fire. *)
Lemma stype_step_recv_matched n (ps : n.-tuple stype) (a b i : 'I_n)
    d sa d' k :
  tnth ps a = STSend b d sa ->   (* `a` sends to `b` *)
  tnth ps i = STRecv a d' k ->   (* `i` waits on a message from `a` *)
  stype_fires ps i ->            (* `i` fires in the round *)
  i = b.                         (* so `i` is `b` *)
Proof.
rewrite /stype_fires !(tnth_nth STEnd) => Ha Hi.
by rewrite /stype_step Hi Ha /=; case: ifP => // /andP[/eqP/val_inj ->].
Qed.

(* Every party that fires in the round belongs to a communication
   available in `ps`. Together with completeness, the round performs
   exactly the available communications. *)
Lemma stype_fires_rstep n (ps : n.-tuple stype) (i : 'I_n) :
  stype_fires ps i ->
  exists l : lens n 2,
    exists2 qs, i \in l & stype_comm_available_at l ps qs.
Proof.
move=> Hf; case Hi: (tnth ps i) => [j d k|a d k|].
- have /stype_send_firesP[j' d' si sj Hi' Hj' _ _] : stype_send_fires ps i.
    by rewrite /stype_send_fires Hi.
  exists [tuple i; j'], [tuple si; sj]; first by rewrite !inE eqxx.
  by apply/stype_rstepP; apply: StypeRstepComm Hi' Hj' _.
- move: (Hf); rewrite /stype_fires /stype_step -tnth_nth Hi.
  case Hj: (nth STEnd ps a) => [i' d' k'| |] //=.
  case: ifP => // /andP[/eqP Hii' /eqP Hdd'] _.
  have [ha|ha] := ltnP a n; last by move: Hj; rewrite nth_default ?size_tuple.
  have /stype_send_firesP[j' d1 sa sb Ha Hb _ _] :
      stype_send_fires ps (Ordinal ha).
    rewrite /stype_send_fires /stype_fires (tnth_nth STEnd) /= Hj.
    by rewrite /stype_step Hj -Hii' -tnth_nth Hi /= Hdd' !eqxx.
  have Eij := stype_step_recv_matched Ha Hi Hf; rewrite -{}Eij in Ha Hb.
  exists [tuple Ordinal ha; i], [tuple sa; sb]; first by rewrite !inE eqxx orbT.
  by apply/stype_rstepP; apply: StypeRstepComm Ha Hb _.
- by move: Hf; rewrite /stype_fires /stype_step -(tnth_nth STEnd) Hi.
Qed.

(* Party `i` is one of the senders `s`, or a receiver that waits on a sender
   in `s` and fires in the round. *)
Definition stype_active_on n (s : seq 'I_n) (ps : n.-tuple stype)
    (i : 'I_n) : bool :=
  (i \in s) ||
  (if tnth ps i is STRecv a _ _
   then (a \in map val s) && stype_fires ps i else false).

(* The round restricted to the senders in `s` and their matched receivers.
   Every other party keeps its type. *)
Definition stypes_round_on n (s : seq 'I_n) (ps : n.-tuple stype) :
    n.-tuple stype :=
  [tuple if stype_active_on s ps i then (stype_step ps i).1 else tnth ps i
  | i < n].

(* The round restricted to no sender leaves every session type in place. *)
Lemma stypes_round_on_nil n (ps : n.-tuple stype) :
  stypes_round_on [::] ps = ps.
Proof.
apply: eq_from_tnth => i; rewrite tnth_mktuple /stype_active_on /=.
by case: (tnth ps i).
Qed.

(* The round restricted to distinct firing senders is a sequence of their
   communications, one per sender. *)
Lemma stypes_round_on_sound n (ps : n.-tuple stype) (s : seq 'I_n) :
  uniq s -> all (stype_send_fires ps) s ->
  stype_rsteps ps (stypes_round_on s ps).
Proof.
elim: s => [|a s IH] /=.
  by move=> _ _; rewrite stypes_round_on_nil; apply: stype_rrefl.
case/andP => Has Hu /andP[/stype_send_firesP[b d sa sb Ha Hb Hsa Hsb] Hall].
have Hbs : b \notin s.
  by apply/negP => /(allP Hall); rewrite /stype_send_fires Hb.
have Hext : extract [tuple a; b] (stypes_round_on s ps) =
    [tuple STSend b d sa; STRecv a d sb].
  apply: val_inj => /=; rewrite !tnth_mktuple /stype_active_on.
  by rewrite (negbTE Has) (negbTE Hbs) Ha Hb /= (mem_map val_inj) (negbTE Has).
have Hinj : stypes_continue_at [tuple a; b] (stypes_round_on s ps)
    [tuple sa; sb] = stypes_round_on (a :: s) ps.
  apply: eq_from_tnth => i; rewrite !tnth_mktuple /=.
  case: eqP => [<-|/eqP Hai]; first by rewrite /stype_active_on mem_head Hsa.
  case: eqP => [<-|/eqP Hbi].
    by rewrite /stype_active_on /stype_fires Hb /= mem_head Hsb orbT.
  congr (if _ then _ else _).
  rewrite /stype_active_on in_cons (eq_sym i) (negbTE Hai) /=.
  case Hi: (tnth ps i) => [j d' k|j d' k|] //=.
  rewrite in_cons; case: eqP Hi => [-> Hi|] //=.
  rewrite (mem_map val_inj) (negbTE Has) /=.
  suff -> : stype_fires ps i = false by [].
  by apply/negbTE; apply: contra Hbi => /(stype_step_recv_matched Ha Hi) ->.
apply: stype_rtrans (IH Hu Hall) _.
by rewrite -Hinj; apply: stype_rone; rewrite Hext; apply: stype_rcomm.
Qed.

(* A party that does not fire keeps its session type. *)
Lemma stype_step_idle n (ps : n.-tuple stype) (i : 'I_n) :
  ~~ stype_fires ps i -> (stype_step ps i).1 = tnth ps i.
Proof.
rewrite /stype_fires /stype_step (tnth_nth STEnd).
by case: (nth STEnd ps i) => [j ? ?|j ? ?|] //=;
  case: (nth STEnd ps j) => // ? ? ?; case: ifP.
Qed.

(* Restricted to the active senders, the round is the full round. Every
   firing party is an active sender or its matched receiver. *)
Lemma stypes_round_on_active n (ps : n.-tuple stype) :
  stypes_round_on (stypes_active_senders ps) ps = stypes_round ps.
Proof.
apply: eq_from_tnth => i; rewrite !tnth_mktuple.
case: ifP => // Hnt; apply/esym/stype_step_idle; apply: contraFN Hnt => Hf.
rewrite /stype_active_on; case Hi: (tnth ps i) => [j d k|j d k|].
- by rewrite orbF mem_filter mem_enum andbT /stype_send_fires Hi.
- apply/orP; right; rewrite Hf andbT.
  move: Hf; rewrite /stype_fires /stype_step -tnth_nth Hi.
  case Hj: (nth STEnd ps j) => [i' d' k'| |] //=.
  case: ifP => // /andP[/eqP Hii' /eqP Hdd'] _.
  have [hj|hj] := ltnP j n; last by move: Hj; rewrite nth_default ?size_tuple.
  apply/mapP; exists (Ordinal hj) => //.
  rewrite mem_filter mem_enum andbT /stype_send_fires (tnth_nth STEnd) /= Hj.
  by rewrite /stype_fires /stype_step Hj -Hii' -tnth_nth Hi /= Hdd' !eqxx.
- by move: Hf; rewrite /stype_fires /stype_step -(tnth_nth STEnd) Hi.
Qed.

(* The tuple round is the seq round that `stypes_interp` iterates. It
   transfers the fuel lemmas of the seq interpreter to tuples. *)
Lemma val_stypes_round n (ps : n.-tuple stype) :
  val (stypes_round ps) = unzip1 [seq stype_step ps i | i <- iota 0 (size ps)].
Proof. by rewrite size_tuple /unzip1 -map_comp map_iota_tuple. Qed.

(* One parallel round of `stype_step` is a sequence of pairwise
   communications. Every environment the functional interpreter reaches in
   a round is reachable in the relational semantics. *)
Lemma stype_step_sound n (ps : n.-tuple stype) :
  stype_rsteps ps (stypes_round ps).
Proof.
rewrite -stypes_round_on_active.
apply: stypes_round_on_sound; first exact: filter_uniq (enum_uniq _).
exact: filter_all.
Qed.

(* With fuel at least `stypes_interp_fuel ps`, the result of
   `stypes_interp` is reachable from `ps` by pairwise communications. *)
Lemma stypes_interp_sound n (ps : n.-tuple stype) h :
  h >= stypes_interp_fuel ps ->
  exists2 ps' : n.-tuple stype,
    stype_rsteps ps ps' & stypes_interp h ps = ps'.
Proof.
elim: h ps => [|h IH] ps; first by rewrite /stypes_interp_fuel addn1.
rewrite /stypes_interp_fuel addn1 ltnS => Hfuel /=.
case: ifP => Hh; last by exists ps; first exact: stype_rrefl.
have := stypes_interp_fuel_step Hh; rewrite -val_stypes_round => Hf.
have [ps' Hs ->] := IH _ (leq_trans Hf Hfuel).
by exists ps'; first exact: stype_rtrans (stype_step_sound ps) Hs.
Qed.

(* A compatible environment reduces by pairwise communications to the
   all-ended environment. Compatibility, defined through one parallel
   schedule, implies that the session can be completed in the relational
   semantics. *)
Lemma stypes_compat_rsteps n (ps : n.-tuple stype) :
  stypes_compat ps -> stype_rsteps ps [tuple STEnd | _ < n].
Proof.
rewrite /stypes_compat.
have [ps' Hs ->] := stypes_interp_sound (leqnn (stypes_interp_fuel ps)).
move=> /all_tnthP Hall; suff -> : [tuple STEnd | _ < n] = ps' by [].
by apply: eq_from_tnth => i; rewrite tnth_mktuple (eqP (Hall i)).
Qed.

End stype_sound.
