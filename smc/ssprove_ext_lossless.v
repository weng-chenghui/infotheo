(** SSProve extension: LosslessCode closed under monadic bind.

    Per the audited plan at ~/.claude/plans/sprightly-finding-robin.md (Task 11).

    SSProve's [LosslessCode] class (in [SSProve.Crypt.Pr], a.k.a.
    [nominal/Pr.v]) is defined as [psum (Pr_fst c) = 1].  The library
    ships instances [Lossless_ret], [Lossless_sample], [Lossless_if],
    but NO [Lossless_bind].  This file adds the missing bind instance.

    Naming convention.  SSProve names its [Op]-level instance
    [LosslessOp_uniform] (PascalCase + underscore + lowercase), and its
    [raw_code]-level instance [Lossless_ret].  The plan asks for
    [LosslessOp_ret] and [LosslessOp_bind] (per Task 11's verbatim
    statement).  Since the bind instance is genuinely new and ranges
    over [raw_code], we register it as [LosslessOp_bind] on
    [LosslessCode] (the [raw_code]-class), and provide [LosslessOp_ret]
    as an alias for the existing [Lossless_ret] under the requested
    name.  The audit (user memory [feedback_mathcomp_naming.md])
    explicitly accepts this PascalCase exception to match upstream
    SSProve naming. *)

From HB Require Import structures.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From SSProve.Crypt Require Import Package SubDistr Pr.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Theory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

Section LosslessExt.
Context {A B : choiceType}.

(** LosslessOp_ret — alias for SSProve's [Lossless_ret].
    Kind: instance.
    Why: Task 11 requests this instance under the [LosslessOp_]
    upstream-naming-style prefix.  Upstream ships [Lossless_ret] (in
    [nominal/Pr.v]); we re-register under the requested name so
    consumers of this file write [LosslessOp_ret] uniformly with the
    new [LosslessOp_bind].
    Used by: Task 12 bridge to [{fdist _}]; resolution test below.
    Naming: upstream PascalCase + underscore + lowercase, matching
    [LosslessOp_uniform] in [pkg_distr.v]. *)
#[export] Instance LosslessOp_ret (a : A) : LosslessCode (ret a)
  := Lossless_ret a.

(** LosslessOp_bind — closure of [LosslessCode] under monadic [bind].
    Kind: instance.
    Why: the audit (sprightly-finding-robin agent A) flagged this as
    one of two upstream gaps blocking the SSProve-to-fdist bridge;
    [Lossless_sample] alone cannot discharge an iterated [bind] tree
    built from cipher-and-uniform samples (e.g. [game_real]).
    Used by: Task 12 bridge [bridge_total_mass]; any subsequent
    composition of lossless code fragments.
    Naming: see file header; upstream-style PascalCase exception.
    Proof outline.  Reduce [Pr_fst (bind c f)] to
    [\dlet_(x <- Pr_fst c) Pr_fst (f x)] via [Pr_fst_bind] (requires
    [ValidCode emptym [interface] c]; the [LosslessCode] hypothesis
    forces [c] to be in the [emptym]/[interface]-closed fragment since
    [Pr_code_call = dnull] and [Pr_code_get/put] thread state — we
    supply the validity as a hypothesis).  Then mass = 1 follows from
    [dletC] using losslessness of [f] pointwise and of [c]. *)
#[export] Instance LosslessOp_bind
    (c : raw_code A) (f : A -> raw_code B)
    {hc : LosslessCode c}
    (vc : ValidCode emptym [interface] c)
    {hf : forall a, LosslessCode (f a)} :
  LosslessCode (x ← c ;; f x).
Proof.
  unfold LosslessCode in *.
  rewrite (Pr_fst_bind vc).
  (* Goal: psum (\dlet_(x <- Pr_fst c) Pr_fst (f x)) = 1. *)
  (* Strategy: apply [dletE] pointwise, then [interchange_psum] to swap
     the order of summation, then factor [Pr_fst c y] out and apply
     losslessness of [f] pointwise. *)
  under eq_psum=> y do rewrite dletE.
  rewrite interchange_psum.
  2: { intros x; apply summable_mu_wgtd => y.
       apply /andP; split; [ done | apply le1_mu1 ]. }
  2: { eapply eq_summable.
       - intros x; rewrite -dletE; reflexivity.
       - apply summable_mu. }
  rewrite -hc.
  apply eq_psum => x.
  rewrite psumZ //.
  by rewrite hf GRing.mulr1.
Qed.

End LosslessExt.

(** Resolution smoke tests — confirms typeclass search finds both
    instances on small bind chains. *)
Section LosslessResolutionTests.
Context {A : choiceType}.

Check (fun a : A => (_ : LosslessCode (ret a))).

(* A small bind chain: [x ← ret a ;; ret x] is lossless.
   This requires [LosslessOp_bind] to fire with [vc] supplied
   manually (typeclass search does not synthesise [ValidCode]
   hypotheses automatically for non-class arguments).  We
   demonstrate the resolution path via an explicit check. *)
Definition lossless_chain_bound (a : A) :
  LosslessCode (x ← ret a ;; ret x).
Proof. by apply: LosslessOp_bind. Qed.

End LosslessResolutionTests.
