From HB Require Import structures.
From mathcomp Require Import all_boot.
Require Import ssr_ext smc_interpreter smc_session_types.
Require Import smc_session_types_sound.

(**md**************************************************************************)
(* # Preservation of session types along process reductions                   *)
(*                                                                            *)
(* Erasure forgets session types before execution. The forgotten types       *)
(* follow every relational execution of the erased processes: each `rstep`   *)
(* lifts to typed residual processes whose environments are an               *)
(* `stype_rsteps` reduct, and compatibility, in its schedule-free form        *)
(* `stypes_rcompat`, is preserved.                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*       aprocs_rstep_lift == one rstep of the erased processes lifts         *)
(*  aprocs_rsteps_preserve == compatibility is preserved along rsteps         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* A pointwise map commutes with writing through a lens. It moves erasure and
   the environment projection across `inject`. *)
Lemma map_inject n m A B (l : lens n m) (f : A -> B)
    (t : n.-tuple A) (t' : m.-tuple A) :
  map_tuple f (inject l t t') = inject l (map_tuple f t) (map_tuple f t').
Proof.
apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple tnth_map /=.
case: (ltnP (index i l) (size t')) => [lt|ge].
  by rewrite (nth_map (tnth t i)).
by rewrite !nth_default ?size_map.
Qed.

(* Writing a coordinate back into its own tuple changes nothing. *)
Lemma inject1_id n (T : Type) (t : n.-tuple T) (i : 'I_n) :
  inject [tuple i] t [tuple tnth t i] = t.
Proof.
apply: eq_from_tnth => k; rewrite tnth_mktuple /=.
by case: (eqVneq i k) => [->|ik] /=; rewrite ?eqxx // eq_sym (negbTE ik).
Qed.

Section aprocs_preservation.
Variables (dtype : eqType) (data : Type).
Local Notation stype := (stype dtype).
Local Notation aproc := (aproc dtype data).

(* A typed process erasing to `Init x p` continues as a typed process erasing
   to `p` with the same environment. *)
Lemma erase_aproc_Init (ap : aproc) x p :
  erase_aproc ap = Init x p ->
  exists2 ap' : aproc, erase_aproc ap' = p & aproc_env ap' = aproc_env ap.
Proof.
case: ap => party [n [env sp]].
case: n env / sp => //= n env d k [_ <-].
by exists (mk_aproc k).
Qed.

(* A typed process erasing to `Ret x` continues as a finished typed process
   with the same environment. *)
Lemma erase_aproc_Ret (ap : aproc) x :
  erase_aproc ap = Ret x ->
  exists2 ap' : aproc,
    erase_aproc ap' = Finish & aproc_env ap' = aproc_env ap.
Proof.
case: ap => party [n [env sp]].
case: n env / sp => //= d _.
by exists (mk_aproc (SFinish (party:=party))).
Qed.

(* A typed process erasing to `Send j x p` has a send head to `j` and
   continues as a typed process erasing to `p`. *)
Lemma erase_aproc_Send (ap : aproc) j x p :
  erase_aproc ap = Send j x p ->
  exists d, exists2 ap' : aproc,
    erase_aproc ap' = p & aproc_env ap = STSend j d (aproc_env ap').
Proof.
case: ap => party [n [env sp]].
case: n env / sp => //= n env dst dt d k [<- _ <-].
by exists dt, (mk_aproc k).
Qed.

(* A typed process erasing to `Recv i f` has a receive head from `i`. Every
   value `x` continues as a typed process erasing to `f x`, at one
   environment. *)
Lemma erase_aproc_Recv (ap : aproc) i f :
  erase_aproc ap = Recv i f ->
  exists d e, exists2 g : data -> aproc,
    aproc_env ap = STRecv i d e &
    forall x, erase_aproc (g x) = f x /\ aproc_env (g x) = e.
Proof.
case: ap => party [n [env sp]].
case: n env / sp => //= n env src dt k [<- <-].
by exists dt, env, (fun x => mk_aproc (k x)).
Qed.

(* One reduction of the erased processes lifts to typed residual processes
   whose environments are reachable by `stype_rsteps`. The premise
   `stypes_rcompat` excludes the kind mismatch that lets an erased
   communication fire without a typed one. *)
Lemma aprocs_rstep_lift n m (l : lens n m) (aps : n.-tuple aproc) ps' tr :
  rstep l (extract l (map_tuple erase_aproc aps)) ps' tr ->
  stypes_rcompat (map_tuple aproc_env aps) ->
  exists2 aps' : m.-tuple aproc,
    map_tuple erase_aproc aps' = ps' &
    stype_rsteps (map_tuple aproc_env aps)
                 (map_tuple aproc_env (inject l aps aps')).
Proof.
move Hps: (extract l _) => psl H; case: H Hps => [i x p | i x | i j x pi pj]
  /(congr1 val) /=.
1,2: rewrite tnth_map => -[+] _;
  (move/erase_aproc_Init || move/erase_aproc_Ret) => -[ap' Hp Henv];
  exists [tuple ap']; first by apply: val_inj; rewrite /= Hp.
1,2: rewrite map_inject (_ : map_tuple aproc_env [tuple ap'] =
         [tuple tnth (map_tuple aproc_env aps) i]) ?inject1_id;
  [exact: stype_rrefl | by apply: val_inj; rewrite /= tnth_map Henv].
rewrite !tnth_map => -[/erase_aproc_Send [d [api Hpi Hei]]].
move=> /erase_aproc_Recv [d' [e [g Hej Hg]]] Hend.
have Edd := stypes_rcompat_kind_match Hend
  (etrans (tnth_map _ _ _) Hei) (etrans (tnth_map _ _ _) Hej).
have [Hgx Hge] := Hg x.
exists [tuple api; g x]; first by apply: val_inj; rewrite /= Hpi Hgx.
rewrite map_inject.
have -> : map_tuple aproc_env [tuple api; g x] =
          [tuple aproc_env api; e].
  by apply: val_inj; rewrite /= Hge.
apply: stype_rone.
have -> : extract [tuple i; j] (map_tuple aproc_env aps) =
          [tuple STSend j d (aproc_env api); STRecv i d e].
  by apply: val_inj; rewrite /= !tnth_map Hei Hej Edd.
exact: stype_rcomm.
Qed.

(* Every relational execution of the erased processes is tracked by a
   relational reduction of their session environments. Session types
   describe every interleaving of the erased processes. *)
Lemma aprocs_rsteps_lift n (aps : n.-tuple aproc) ps' tr :
  rsteps (map_tuple erase_aproc aps) ps' tr ->
  stypes_rcompat (map_tuple aproc_env aps) ->
  exists2 aps' : n.-tuple aproc,
    map_tuple erase_aproc aps' = ps' &
    stype_rsteps (map_tuple aproc_env aps) (map_tuple aproc_env aps').
Proof.
move Hps: (map_tuple erase_aproc aps) => ps0 H; elim: H aps Hps
  => {ps0 ps' tr} [m l ps ps' tr Hs | ps | ps1 ps2 ps3 tr1 tr2 tr3 _ IH1 _ IH2 _
     ] aps Hps Hend; subst.
- have [aps' <- Hst] := aprocs_rstep_lift Hs Hend.
  by exists (inject l aps aps'); rewrite // map_inject.
- by exists aps => //; exact: stype_rrefl.
- have [aps2 Hps2 Hst1] := IH1 aps erefl Hend.
  have [aps3 Hps3 Hst2] := IH2 aps2 Hps2 (stypes_rcompat_rsteps Hst1 Hend).
  by exists aps3 => //; exact: stype_rtrans Hst2.
Qed.

(* Compatibility is preserved along every relational execution of the erased
   processes, with environments reduced by `stype_rsteps`. Values are never
   checked, so neither progress nor the absence of `Fail` follows. *)
Lemma aprocs_rsteps_preserve n (aps : n.-tuple aproc) ps' tr :
  aprocs_compat aps ->
  rsteps (map_tuple erase_aproc aps) ps' tr ->
  exists2 aps' : n.-tuple aproc,
    map_tuple erase_aproc aps' = ps' &
    stype_rsteps (map_tuple aproc_env aps) (map_tuple aproc_env aps') /\
    aprocs_compat aps'.
Proof.
move=> /stypes_compatP Hend /aprocs_rsteps_lift/(_ Hend)[aps' Hps' Hst].
exists aps' => //; split => //.
by apply/stypes_compatP; exact: stypes_rcompat_rsteps Hst Hend.
Qed.

End aprocs_preservation.
