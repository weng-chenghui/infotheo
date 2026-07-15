(* PROBE P6 — heap-parametric losslessness for stateful resolved code.

   Design-validation probe for the DSDP SSProve simulator work.  SSProve's
   [LosslessCode] (nominal/Pr.v) closes total mass one only for the [emptym]
   marginal [Pr_fst], and its bind instance [LosslessOp_bind]
   (smc/ssprove_ext_lossless.v) requires the prefix to be
   [ValidCode emptym [interface]] — so code containing #put / get is outside
   the closure.  The resolved DSDP view code is stateful (V_2_cell, Sout_cell
   writes and a Sout get), so it sits outside that closure.

   Part A1 builds a heap-parametric class [LosslessHeapCode] over the joint
   output/heap subdistribution [Pr_code c h] for EVERY starting heap h, with
   ret / sample / get / put / bind / if instances that carry no
   [ValidCode emptym] restriction, plus a bridge back to the [Pr_fst]-based
   mass-1 statement.  Part A2 discharges the class on the resolved DSDP view
   code.  Part B type-checks the [sim_view_body] allowed-info abstraction.

   This file is not imported by any other module. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum distr.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr pkg_rhl.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import spp_proba bayes spp_entropy.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code.
Require Import dsdp_symbolic_exec.
Require Import dsdp_game_derivation.
Require Import dsdp_indcpa_advantage.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

Notation R := SSProve.Crypt.Axioms.R.

(* ================================================================= *)
(* PART A1 — heap-parametric losslessness class                      *)
(* ================================================================= *)

(* psum_dlet_const1 — the total mass of a mixture whose every fibre
   continuation has total mass one equals the total mass of the mixing
   subdistribution.  Mirrors the interchange-of-summation core of upstream
   [Lossless_sample]; inherits its [interchange_psum] (admitted in
   mathcomp-analysis experimental_reals) dependency. *)
Lemma psum_dlet_const1 {T U : choiceType}
    (mu : {distr T / R}) (G : T -> {distr U / R}) :
  (forall x, psum (distr.mu (G x)) = 1) ->
  psum (distr.mu (\dlet_(x <- mu) G x)) = psum (distr.mu mu).
Proof.
move=> HG.
under eq_psum => y do rewrite dletE.
rewrite __admitted__interchange_psum.
1:{ apply: eq_psum => y.
    by rewrite psumZ ?ge0_mu // HG GRing.mulr1. }
1:{ by move=> x; apply: summable_mlet. }
eapply eq_summable; first by move=> x; rewrite -dletE.
exact: summable_mu.
Qed.

(* LosslessHeapCode c — heap-parametric losslessness: the joint output/heap
   subdistribution has total mass one from every starting heap. *)
Definition LosslessHeapCode {A : choiceType} (c : raw_code A) : Prop :=
  forall h : heap, psum (distr.mu (Pr_code c h)) = 1.

(* LosslessHeap_ret — a return terminates with mass one. *)
Lemma LosslessHeap_ret {A : choiceType} (a : A) :
  LosslessHeapCode (ret a).
Proof. move=> h; rewrite Pr_code_ret; exact: Couplings.psum_SDistr_unit. Qed.

(* LosslessHeap_sample — a sample of a lossless operation followed by a
   uniformly lossless continuation terminates with mass one. *)
Lemma LosslessHeap_sample {A : choiceType} (D : Op) (k : Arit D -> raw_code A) :
  LosslessOp D -> (forall x, LosslessHeapCode (k x)) ->
  LosslessHeapCode (x ← sample D ;; k x).
Proof.
move=> HD Hk h; rewrite Pr_code_sample.
rewrite psum_dlet_const1; first exact: HD.
by move=> x; exact: Hk.
Qed.

(* LosslessHeap_get — a read followed by a continuation lossless at every read
   value terminates with mass one. *)
Lemma LosslessHeap_get {A : choiceType} (l : Location) (k : l -> raw_code A) :
  (forall v, LosslessHeapCode (k v)) ->
  LosslessHeapCode (x ← get l ;; k x).
Proof. move=> Hk h; rewrite Pr_code_get; exact: Hk. Qed.

(* LosslessHeap_put — a write followed by a lossless continuation terminates
   with mass one. *)
Lemma LosslessHeap_put {A : choiceType} (l : Location) (a : l) (k : raw_code A) :
  LosslessHeapCode k -> LosslessHeapCode (#put l := a ;; k).
Proof. move=> Hk h; rewrite Pr_code_put; exact: Hk. Qed.

(* LosslessHeap_bind — a prefix code lossless at every heap sequenced with a
   uniformly lossless continuation terminates with mass one, with no
   [ValidCode emptym] restriction on the prefix. *)
Lemma LosslessHeap_bind {A B : choiceType} (c : raw_code B) (f : B -> raw_code A) :
  LosslessHeapCode c -> (forall x, LosslessHeapCode (f x)) ->
  LosslessHeapCode (x ← c ;; f x).
Proof.
move=> Hc Hf h; rewrite Pr_code_bind.
rewrite psum_dlet_const1; first exact: (Hc h).
by move=> y; exact: Hf.
Qed.

(* LosslessHeap_if — a lossless conditional terminates with mass one. *)
Lemma LosslessHeap_if {A : choiceType} (b : bool) (c1 c2 : raw_code A) :
  LosslessHeapCode c1 -> LosslessHeapCode c2 ->
  LosslessHeapCode (if b then c1 else c2).
Proof. by case: b. Qed.

(* LosslessHeap_Pr_fst — heap-parametric losslessness gives the [Pr_fst]-based
   mass-1 statement of SSProve's [LosslessCode] at the empty heap. *)
Lemma LosslessHeap_Pr_fst {A : choiceType} (c : raw_code A) :
  LosslessHeapCode c -> psum (distr.mu (Pr_fst c)) = 1.
Proof.
move=> Hc; rewrite /Pr_fst dmarginE.
rewrite psum_dlet_const1; first exact: (Hc emptym).
by move=> x; exact: Couplings.psum_SDistr_unit.
Qed.

(* ================================================================= *)
(* PART B — sim_view_body allowed-info abstraction typecheck          *)
(* ================================================================= *)

Section sim_view_body_typecheck.
(* Cloned context of Section dsdp_alice_guess (dsdp_main.v ~705). *)
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable seed : denv AHE.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher)
  (in custom pack_type at level 2).

(* id_ideal_run — the allowed-information run operation identifier; the game
   oracles occupy 0 / 2 / 3, so 4 is the first free identifier. *)
Definition id_ideal_run : nat := 4%N.

(* I_dsdp_ideal — the allowed-information interface exported by the ideal
   package: a state-only run and the two reveal oracles. *)
Definition I_dsdp_ideal : Interface :=
  [interface
     #val #[ id_ideal_run ] : 'unit → 'unit ;
     #val #[ id_v2_get    ] : 'unit → msg ;
     #val #[ id_Sout_get  ] : 'unit → msg ].

(* sim_view_body run_ideal get_S — the simulator view builder parameterised by
   the two allowed-information accesses (the ideal run and the leaked scalar
   product S) as raw_code arguments.  It runs the ideal, reads S, samples the
   masks r2, r3, the mask-encryption randomnesses ra1, ra2 and the two hop
   randomnesses, and rebuilds the four-cipher view [a1; a2; c2; c3] with the
   project's own enc / Emul / Epow. *)
Definition sim_view_body (run_ideal : raw_code 'unit) (get_S : raw_code t_msg) :
  raw_code (cipher_list t_cipher) :=
  _ ← run_ideal ;;
  _ ← get_S ;;
  x_r2  ← sample uniform card_msg ;;
  x_r3  ← sample uniform card_msg ;;
  x_ra1 ← sample uniform card_renc ;;
  x_ra2 ← sample uniform card_renc ;;
  x_c2  ← sample uniform card_renc ;;
  x_c3  ← sample uniform card_renc ;;
  let r2  := msg_of_idx x_r2 in
  let r3  := msg_of_idx x_r3 in
  let ra1 := rand_of_renc (@sample_to_renc _ _ renc_card x_ra1) in
  let ra2 := rand_of_renc (@sample_to_renc _ _ renc_card x_ra2) in
  let pk1 := pkey_of_party (nat_to_party_id 1) in
  let pk2 := pkey_of_party (nat_to_party_id 2) in
  let c2c := enc pk1 (0%R : plain AHE)
                 (rand_of_renc (@sample_to_renc _ _ renc_card x_c2)) in
  let c3c := enc pk2 (0%R : plain AHE)
                 (rand_of_renc (@sample_to_renc _ _ renc_card x_c3)) in
  let u2 := as_plain (de_val_nth seed 1) in
  let u3 := as_plain (de_val_nth seed 2) in
  let a1c := Emul (Epow c2c u2) (enc pk1 r2 ra1) in
  let a2c := Emul (Epow c3c u3) (enc pk2 r3 ra2) in
  ret ([:: chcipher_of_cipher a1c; chcipher_of_cipher a2c;
           chcipher_of_cipher c2c; chcipher_of_cipher c3c ]
       : cipher_list t_cipher).

(* valid_sim_view_body — sim_view_body is valid code over any interface that
   validates its two allowed-information accesses; the remaining samples and
   the cipher-view return impose no interface constraint. *)
Lemma valid_sim_view_body (L : Locations) (I : Interface)
    (run_ideal : raw_code 'unit) (get_S : raw_code t_msg)
    (H1 : ValidCode L I run_ideal) (H2 : ValidCode L I get_S) :
    ValidCode L I (sim_view_body run_ideal get_S).
Proof.
rewrite /sim_view_body.
apply: valid_bind.
move=> _; apply: valid_bind.
move=> _; ssprove_valid.
Qed.

(* Register valid_sim_view_body so the [package] validity resolver descends
   through the opaque sim_view_body head. *)
#[local] Hint Extern 2 (ValidCode ?L ?I (sim_view_body ?r ?s)) =>
  eapply valid_sim_view_body
  : typeclass_instances ssprove_valid_db.

(* test_pkg_valid — the abstracted view op body validates over I_dsdp_ideal
   once the two allowed-information accesses are written in bind-wrapped call
   form (a bare [c tt] leaves a beta-redex the valid_opr hint cannot match). *)
Lemma test_pkg_valid :
  ValidCode emptym I_dsdp_ideal
    (sim_view_body
       (#import {sig #[ id_ideal_run ] : 'unit → 'unit } as c ;;
        x ← c Datatypes.tt ;; ret x)
       (#import {sig #[ id_Sout_get ] : 'unit → msg } as c ;;
        x ← c Datatypes.tt ;; ret x)).
Proof. ssprove_valid. Qed.

(* dsdp_simulator_view_pkg — the simulator importing I_dsdp_ideal and
   exporting game_iface_leak_S, with op id_game_run driven by sim_view_body
   applied to the ideal-run and Sout call expressions. *)
Definition dsdp_simulator_view_pkg :
  package I_dsdp_ideal (game_iface_leak_S t_msg t_cipher) :=
  [package emptym ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      sim_view_body
        (#import {sig #[ id_ideal_run ] : 'unit → 'unit } as call_ideal ;;
         r ← call_ideal Datatypes.tt ;; ret r)
        (#import {sig #[ id_Sout_get ] : 'unit → msg } as call_Sout ;;
         s ← call_Sout Datatypes.tt ;; ret s)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      #import {sig #[ id_v2_get ] : 'unit → msg } as call_v2 ;;
      x ← call_v2 Datatypes.tt ;;
      ret x
    } ;
    #def #[ id_Sout_get ] (_ : 'unit) : msg
    {
      #import {sig #[ id_Sout_get ] : 'unit → msg } as call_Sout ;;
      x ← call_Sout Datatypes.tt ;;
      ret x
    }
  ].

End sim_view_body_typecheck.

(* ================================================================= *)
(* PART A2 — heap-parametric losslessness of the real game code       *)
(* ================================================================= *)

Section view_zero_mass1_section.
(* Cloned context of Section dsdp_alice_guess (dsdp_main.v ~705), WITH
   card_renc_neq and the sample-cardinality positivity hypotheses. *)
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Hypothesis card_renc_neq : card_renc != card_msg.
Hypothesis card_msg_pos : (0 < card_msg)%N.
Hypothesis card_renc_pos : (0 < card_renc)%N.

(* gc_sample_cards gc — every GC_sample cardinality in gc is card_msg or
   card_renc, so denote_run's sample-sort dispatch stays lossless. *)
Fixpoint gc_sample_cards (gc : game_code) : bool :=
  match gc with
  | GC_sample n k => ((n == card_msg) || (n == card_renc)) && gc_sample_cards k
  | GC_put _ k => gc_sample_cards k
  | GC_put_output _ k => gc_sample_cards k
  | GC_let _ k => gc_sample_cards k
  | GC_enc_hop _ _ k => gc_sample_cards k
  | GC_ret _ => true
  end.

(* denote_run_lossless_heap — the denoted game-code core is heap-parametric
   lossless whenever its sample cardinalities are the two positive sorts.
   Proven by induction on the game_code AST, so the giant resolved term is
   never materialised. *)
Lemma denote_run_lossless_heap (gc : game_code) (e : denv AHE) :
  gc_sample_cards gc ->
  LosslessHeapCode (@denote_run AHE Renc card_renc renc_card rand_of_renc
    t_msg t_cipher chmsg_of_msg chcipher_of_cipher pkey_of_party card_msg
    msg_of_idx rand0 e gc).
Proof.
elim: gc e => [n k IH|t k IH|t k IH|t k IH|pk secret k IH|outs] e /=.
- move=> /andP[Hn Hk]; case/orP: Hn => /eqP Heq.
  + rewrite Heq eqxx.
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x; exact: (IH _ Hk).
  + rewrite Heq (negbTE card_renc_neq) eqxx.
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x; exact: (IH _ Hk).
- move=> Hk; apply: LosslessHeap_put; exact: (IH _ Hk).
- move=> Hk; apply: LosslessHeap_put; exact: (IH _ Hk).
- move=> Hk; exact: (IH _ Hk).
- move=> Hk; apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
  move=> x; exact: (IH _ Hk).
- by move=> _; exact: LosslessHeap_ret.
Qed.

End view_zero_mass1_section.
