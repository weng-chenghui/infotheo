From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
Require Import smc_session_types.

(* Scope and custom entry *)
Declare Scope pismc_scope.
Declare Custom Entry pismc.

(* Program delimiter, written \pi{ e } because the brace-bar form clashes
   with Rocq record syntax. *)
Notation "'\pi{' e '}'" := e (e custom pismc at level 99) : pismc_scope.

(* Shared piSMC notations - protocol-independent constructors.
   Send/Recv notations are protocol-specific (dtype-dependent) and
   remain in each protocol's _pismc.v file. *)

(* Lift identifiers into the pismc custom entry.
   Allows bare variables (e.g., loop continuation) in pismc positions. *)
Notation "x" := x (in custom pismc at level 0, x ident).

(* Terminal state *)
Notation "'Finish'" := SFinish (in custom pismc at level 0).

(* Return a value *)
Notation "'Ret' x" := (SRet x)
  (in custom pismc at level 80, x constr at level 0).

(* Init - single value *)
Notation "'Init' x ; P" := (SInit x P)
  (in custom pismc at level 85, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Init - multi-var tuple *)
Notation "'Init' '(' x ',' .. ',' y ')' ; P" :=
  (SInit x .. (SInit y P) ..)
  (in custom pismc at level 85,
   x constr at level 0, y constr at level 0,
   P custom pismc at level 85, right associativity).

(* Sample - draw the head of the party's own seed stream.
   No channel is used, so the session environment is unchanged. *)
Notation "'Sample' x '=>' P" := (SSample (fun x => P))
  (in custom pismc at level 85, x name,
   P custom pismc at level 85, right associativity).

(* Iterate a body over the elements of a finType, one sproc layer per
   element.  Usage: ForEach 'I_n as f, i => body ; P. *)
Notation "'ForEach' fT 'as' f ',' i '=>' body ; P" :=
  (sproc_iter _ S _ (fun f i => body) (enum fT) 0 P)
  (in custom pismc at level 85, fT constr at level 0, f name, i name,
   body constr at level 0,
   P custom pismc at level 85, right associativity).

(* ForEach with explicit fuel step function.
   Usage: ForEach 'I_n step (fun k => k.+2) as f, i => ... ; P *)
Notation "'ForEach' fT 'step' s 'as' f ',' i '=>' body ; P" :=
  (sproc_iter _ s _ (fun (f : fT) i => body) (enum fT) 0 P)
  (in custom pismc at level 85, fT constr at level 0, s constr at level 0,
   f name, i name, body constr at level 0,
   P custom pismc at level 85, right associativity).

(* ForEach with explicit fuel step and env step functions.
   Usage: ForEach 'I_n step s enstep es as f, i => ... ; P
   Use when env_step can't be inferred (e.g., body has SFail branches). *)
Notation "'ForEach' fT 'step' s 'enstep' es 'as' f ',' i '=>' body ; P" :=
  (sproc_iter _ s es (fun (f : fT) i => body) (enum fT) 0 P)
  (in custom pismc at level 85, fT constr at level 0, s constr at level 0,
   es constr at level 0, f name, i name, body constr at level 0,
   P custom pismc at level 85, right associativity).

(* Like ForEach but iterating an explicit list, for cases where enum does
   not reduce under vm_compute. *)
Notation "'ForList' ls 'step' s 'enstep' es 'as' f ',' i '=>' body ; P" :=
  (sproc_iter _ s es (fun f i => body) ls 0 P)
  (in custom pismc at level 85, ls constr at level 0, s constr at level 0,
   es constr at level 0, f name, i name, body constr at level 0,
   P custom pismc at level 85, right associativity).

Notation "'ForList' ls 'step' s 'enstep' es 'as' f 'cont' k '=>' body 'end' ; P" :=
  (sproc_iter _ s es (fun f _ _ _ k => body) ls 0 P)
  (in custom pismc at level 85, ls constr at level 0, s constr at level 0,
   es constr at level 0, f name, k name, body custom pismc at level 85,
   P custom pismc at level 85, right associativity).

