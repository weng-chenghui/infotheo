(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5 executed-trace secrecy (proof-of-concept instance of the executed-trace *)
(* bridge). A randomized 5-of-5 additive run deals the uniform iid layout      *)
(* with the identity cut; one player's executed trace, projected to its single *)
(* dealt share, is fed through trace_secrecy_of_view (cancel = id, since        *)
(* 'Z_5 = 'I_5) to obtain single-player trace secrecy.                          *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_smc Require Import pgg_raag_s5 s5_profile pgg_raag_path.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_trace_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section s5_trace_sec.
Variable R : realType.

(** s5_M — the S_5 adjacent-transposition monodromy template (N = 5).
    @intent: a notation for the Gen_PGGTypes form s5_PI carries, so the run
    definitions share their type. *)
Local Notation s5_M := (@Gen_PGGTypes 3 3 (path_gen_tuple 3)).

(** s5_players — the five-player list for the S_5 dealing phase.
    @intent: the explicit five-element list of 'I_5 player ordinals; a concrete
    list lets the dealer's fold_senv reduce under vm_compute. *)
Definition s5_players : seq 'I_(pi_T' s5_PI).+1 :=
  [:: @Ordinal 5 0 isT; @Ordinal 5 1 isT; @Ordinal 5 2 isT;
      @Ordinal 5 3 isT; @Ordinal 5 4 isT].

(** content_of — the informative coordinate of a player's executed trace: the
    head of the first dealt hand, with default ord0 for an empty trace.
    @intent: extract a finType content from a non-finite seq (pgg_data N.+1)
    trace. *)
Definition content_of (N : nat) (tr : seq (pgg_data N.+1)) : 'I_N.+1 :=
  if tr is _ :: PGG_hand (x :: _) :: _ then x else ord0.

Section abstract_leaf.
Variable g : 'I_5 -> 'I_5.

(** s5_aprocs_abs — dealer (content readout g, identity cut, empty input
    prologue) ++ verifier ++ five players, with the content function held
    abstract so vm_compute reduces the run skeleton without unfolding the
    dealt share value.
    @intent: the seven session-typed processes of one S_5 run over an abstract
    content readout g. *)
Definition s5_aprocs_abs :=
  erase_aprocs
  [:: mk_aproc (dealer_with_input_encoding s5_PI
                  (fun _ => g) [:: (1%g : pgg_gT s5_M)] [::] s5_players 0)
    ; mk_aproc (exchange_verifier s5_PI s5_players)
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 0 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 1 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 2 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 3 isT))
    ; mk_aproc (exchange_player s5_PI (@Ordinal 5 4 isT))].

(** s5_rho1_index — at the identity cut and ord_tuple starts, the readout index
    of player i is i.
    @composes: s5_player_trace_E
    Naming: `_index` denotes the readout-index value, not a MathComp suffix. *)
Lemma s5_rho1_index (i : 'I_5) : @pgg_rho s5_M 1%g (tnth (pi_starts s5_PI) i) = i.
Proof. by rewrite morph1 perm1 tnth_ord_tuple. Qed.

(* The five player traces are stated per concrete player index so that both the
   process-list ordinal and the readout index share the canonical isT proof,
   which lets vm_compute close each case by reflexivity (a symbolic ordinal
   proof would leave a dead tnth_default branch mismatch). *)
(** s5_abs_p0 — player 0's executed-trace content is the readout g at index 0.
    @composes: s5_player_trace_E
    Naming: `p0` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma s5_abs_p0 :
  content_of (nth [::] (run_interp 150 s5_aprocs_abs).2 (2 + 0)) = g (@Ordinal 5 0 isT).
Proof. rewrite /s5_aprocs_abs -[in RHS](s5_rho1_index (@Ordinal 5 0 isT)); vm_compute; reflexivity. Qed.

(** s5_abs_p1 — player 1's executed-trace content is the readout g at index 1.
    @composes: s5_player_trace_E
    Naming: `p1` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma s5_abs_p1 :
  content_of (nth [::] (run_interp 150 s5_aprocs_abs).2 (2 + 1)) = g (@Ordinal 5 1 isT).
Proof. rewrite /s5_aprocs_abs -[in RHS](s5_rho1_index (@Ordinal 5 1 isT)); vm_compute; reflexivity. Qed.

(** s5_abs_p2 — player 2's executed-trace content is the readout g at index 2.
    @composes: s5_player_trace_E
    Naming: `p2` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma s5_abs_p2 :
  content_of (nth [::] (run_interp 150 s5_aprocs_abs).2 (2 + 2)) = g (@Ordinal 5 2 isT).
Proof. rewrite /s5_aprocs_abs -[in RHS](s5_rho1_index (@Ordinal 5 2 isT)); vm_compute; reflexivity. Qed.

(** s5_abs_p3 — player 3's executed-trace content is the readout g at index 3.
    @composes: s5_player_trace_E
    Naming: `p3` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma s5_abs_p3 :
  content_of (nth [::] (run_interp 150 s5_aprocs_abs).2 (2 + 3)) = g (@Ordinal 5 3 isT).
Proof. rewrite /s5_aprocs_abs -[in RHS](s5_rho1_index (@Ordinal 5 3 isT)); vm_compute; reflexivity. Qed.

(** s5_abs_p4 — player 4's executed-trace content is the readout g at index 4.
    @composes: s5_player_trace_E
    Naming: `p4` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma s5_abs_p4 :
  content_of (nth [::] (run_interp 150 s5_aprocs_abs).2 (2 + 4)) = g (@Ordinal 5 4 isT).
Proof. rewrite /s5_aprocs_abs -[in RHS](s5_rho1_index (@Ordinal 5 4 isT)); vm_compute; reflexivity. Qed.

End abstract_leaf.

(** s5_rs — the concrete uniform iid 5-of-5 additive randomized sharing.
    @intent: the randomized additive sharing whose shares the run deals. *)
Definition s5_rs := @unif_randomized_sharing R 3 4.

(** s5_rlayout — the dealt layout at tape u: position i carries share i.
    @intent: randomized dealt layout, share i at position i. *)
Definition s5_rlayout (u : 'rV['Z_5]_5) : 5.-tuple 'I_5 :=
  [tuple rsh_share s5_rs i u | i < 5].

(** s5_rprocs — the randomized s5 run at tape u: the abstract run skeleton fed
    the tape-dependent share-tuple readout, identity cut.
    @intent: the erased randomized process list of one S_5 run. *)
Definition s5_rprocs (u : 'rV['Z_5]_5) := s5_aprocs_abs (tnth (s5_rlayout u)).

(** s5P — the uniform iid sampler distribution over the 'rV['Z_5]_5 tape.
    @intent: the fdist underlying s5_rs's random variables. *)
Let s5P : R.-fdist 'rV['Z_5]_5 :=
  fdist_uniform (pgg_canonical_sharing.card_ZN_subproof 3) `^ 5.

(** s5_player_trace — player i's executed-trace content, lifted over the
    sampler tape via the run_interp projection at process index 2+i.
    @intent: single-player executed trace as a content random variable. *)
Definition s5_player_trace (i : 'I_5) : {RV s5P -> 'I_5} :=
  fun u => content_of (nth [::] (run_interp 150 (s5_rprocs u)).2 (2 + i)).

(** s5_player_trace_E — the lifted player trace equals the dealt share at
    player i.
    @composes: s5_trace_secrecy *)
Lemma s5_player_trace_E (i : 'I_5) : s5_player_trace i = rsh_share s5_rs i.
Proof.
apply: boolp.funext => u; rewrite /s5_player_trace /s5_rprocs.
case: i => -[|[|[|[|[|//]]]]] Hi.
- rewrite (s5_abs_p0 (tnth (s5_rlayout u))) tnth_mktuple; congr (rsh_share s5_rs _ u); exact: val_inj.
- rewrite (s5_abs_p1 (tnth (s5_rlayout u))) tnth_mktuple; congr (rsh_share s5_rs _ u); exact: val_inj.
- rewrite (s5_abs_p2 (tnth (s5_rlayout u))) tnth_mktuple; congr (rsh_share s5_rs _ u); exact: val_inj.
- rewrite (s5_abs_p3 (tnth (s5_rlayout u))) tnth_mktuple; congr (rsh_share s5_rs _ u); exact: val_inj.
- rewrite (s5_abs_p4 (tnth (s5_rlayout u))) tnth_mktuple; congr (rsh_share s5_rs _ u); exact: val_inj.
Qed.

(** s5_share_indep — one player's single share is independent of the secret,
    reducing the coalition view additive_view_indep to a single share.
    @composes: s5_trace_secrecy *)
Lemma s5_share_indep (i : 'I_5) : s5P |= rsh_share s5_rs i _|_ rsh_secret s5_rs.
Proof.
have Hcard : (#|[set i]| < 5)%N by rewrite cards1.
have Hview := additive_view_indep s5_rs (C := [set i]) Hcard.
have -> : rsh_share s5_rs i = (fun f => f i) `o rsh_view s5_rs [set i].
  by apply: boolp.funext => u; rewrite /comp_RV ffunE in_set1 eqxx.
exact: (inde_RV_comp (fun f : {ffun 'I_5 -> 'Z_5} => f i) Hview).
Qed.

(** s5_trace_secrecy — a single corrupted player's executed s5 trace leaves the
    secret's conditional entropy equal to its plain entropy.
    @main security: single-player executed-trace secrecy over the randomized
    additive s5 run, via the executed-trace bridge with cancel = id. *)
Lemma s5_trace_secrecy (i : 'I_5) :
  `H( (rsh_secret s5_rs) | (s5_player_trace i) ) = `H `p_ (rsh_secret s5_rs).
Proof.
apply: (trace_secrecy_of_view (view := rsh_share s5_rs i)
          (trace_of := id) (view_of := id)).
- by rewrite s5_player_trace_E.
- by [].
- exact: s5_share_indep.
Qed.

End s5_trace_sec.
