(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* den Boer executed-trace secrecy (instance of the executed-trace bridge).   *)
(* The randomized five-card run commits the two input bits and deals the       *)
(* den Boer layout under the cyclic cut fc_sigma^k realizing rotation k. One   *)
(* player's executed trace, projected to its single dealt card position, is    *)
(* encode_bool of the single-card colour the partial view ViewA reads at that  *)
(* player; this is the monodromy rotation identity (the cut fc_sigma^k equals   *)
(* the leakage rotation k). The colour view is fed through trace_secrecy_of_view *)
(* with the encode_bool/decode_bool codec to obtain single-player trace secrecy. *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_smc Require Import five_card_group five_card_program five_card_scheme_I5.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme input_encoding.
From pgg_smc Require Import den_boer_profile den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage denboer_secrecy pgg_leakage_witness pgg_trace_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(** content_of — the informative coordinate of a player's executed trace: the
    head of the first dealt hand, with default ord0 for an empty trace.
    @intent: extract a finType content from a non-finite seq (pgg_data N.+1)
    trace. *)
Definition content_of (N : nat) (tr : seq (pgg_data N.+1)) : 'I_N.+1 :=
  if tr is _ :: PGG_hand (x :: _) :: _ then x else ord0.

Section abstract_leaf.
Variable g : seq 'I_(pgg_N' FiveCardKim_M).+1 -> ('I_5 -> 'I_5).
Variable va vb : 'I_5.
Variable w0 : pgg_gT FiveCardKim_M.

(** denboer_aprocs_abs — committed dealer (content readout g, cut w0, input
    prologue committing va, vb at parties 7 and 8) ++ verifier ++ five players
    ++ two input parties, with the content readout held abstract so vm_compute
    reduces the run skeleton without unfolding the dealt layout value.
    @intent: the nine session-typed processes of one den Boer run over an
    abstract content readout g and abstract committed inputs va, vb. *)
Definition denboer_aprocs_abs :=
  erase_aprocs
  [:: mk_aproc (pgg_commit_prologue (fun committed =>
         exchange_dealer FiveCardKim_PI (g committed) den_boer_players [:: w0] 0) [::] [:: 7; 8])
    ; mk_aproc (exchange_verifier FiveCardKim_PI den_boer_players)
    ; mk_aproc (exchange_player FiveCardKim_PI (@Ordinal 5 0 isT))
    ; mk_aproc (exchange_player FiveCardKim_PI (@Ordinal 5 1 isT))
    ; mk_aproc (exchange_player FiveCardKim_PI (@Ordinal 5 2 isT))
    ; mk_aproc (exchange_player FiveCardKim_PI (@Ordinal 5 3 isT))
    ; mk_aproc (exchange_player FiveCardKim_PI (@Ordinal 5 4 isT))
    ; mk_aproc (@pgg_commit FiveCardKim_M 7 va)
    ; mk_aproc (@pgg_commit FiveCardKim_M 8 vb)].

(* The five player traces are stated per concrete player index so that both the
   process-list ordinal and the readout index share the canonical isT proof,
   which lets vm_compute close each case by reflexivity (a symbolic ordinal
   proof would leave a dead tnth_default branch mismatch). *)
(** denboer_abs_p0 — player 0's executed-trace content is the readout g at the
    monodromy image of player 0's start.
    @composes: denboer_player_trace_shape
    Naming: `p0` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma denboer_abs_p0 :
  content_of (nth [::] (run_interp 100 denboer_aprocs_abs).2 (2 + 0))
  = g [:: va; vb] (@pgg_rho FiveCardKim_M w0 (tnth (pi_starts FiveCardKim_PI) (@Ordinal 5 0 isT))).
Proof. rewrite /denboer_aprocs_abs; vm_compute; reflexivity. Qed.

(** denboer_abs_p1 — player 1's executed-trace content is the readout g at the
    monodromy image of player 1's start.
    @composes: denboer_player_trace_shape
    Naming: `p1` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma denboer_abs_p1 :
  content_of (nth [::] (run_interp 100 denboer_aprocs_abs).2 (2 + 1))
  = g [:: va; vb] (@pgg_rho FiveCardKim_M w0 (tnth (pi_starts FiveCardKim_PI) (@Ordinal 5 1 isT))).
Proof. rewrite /denboer_aprocs_abs; vm_compute; reflexivity. Qed.

(** denboer_abs_p2 — player 2's executed-trace content is the readout g at the
    monodromy image of player 2's start.
    @composes: denboer_player_trace_shape
    Naming: `p2` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma denboer_abs_p2 :
  content_of (nth [::] (run_interp 100 denboer_aprocs_abs).2 (2 + 2))
  = g [:: va; vb] (@pgg_rho FiveCardKim_M w0 (tnth (pi_starts FiveCardKim_PI) (@Ordinal 5 2 isT))).
Proof. rewrite /denboer_aprocs_abs; vm_compute; reflexivity. Qed.

(** denboer_abs_p3 — player 3's executed-trace content is the readout g at the
    monodromy image of player 3's start.
    @composes: denboer_player_trace_shape
    Naming: `p3` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma denboer_abs_p3 :
  content_of (nth [::] (run_interp 100 denboer_aprocs_abs).2 (2 + 3))
  = g [:: va; vb] (@pgg_rho FiveCardKim_M w0 (tnth (pi_starts FiveCardKim_PI) (@Ordinal 5 3 isT))).
Proof. rewrite /denboer_aprocs_abs; vm_compute; reflexivity. Qed.

(** denboer_abs_p4 — player 4's executed-trace content is the readout g at the
    monodromy image of player 4's start.
    @composes: denboer_player_trace_shape
    Naming: `p4` pins the concrete player ordinal; each of the five lemmas fixes
    the canonical isT proof so vm_compute reduces the run skeleton to a ground
    equality closed by reflexivity. *)
Lemma denboer_abs_p4 :
  content_of (nth [::] (run_interp 100 denboer_aprocs_abs).2 (2 + 4))
  = g [:: va; vb] (@pgg_rho FiveCardKim_M w0 (tnth (pi_starts FiveCardKim_PI) (@Ordinal 5 4 isT))).
Proof. rewrite /denboer_aprocs_abs; vm_compute; reflexivity. Qed.

End abstract_leaf.

Section denboer_trace_sec.
Variable R : realType.

Let dbP := P R.

(** denboer_rprocs — the den Boer run at leakage outcome (a, b, k): the two
    input bits committed, dealt under the cut fc_sigma^k realizing rotation k.
    @intent: the erased process list of one den Boer run at the leakage outcome. *)
Definition denboer_rprocs (w : Omega) :=
  let: (a, b, k) := w in den_boer_procs a b (five_card_group.fc_sigma ^+ k)%g 0.

(** denboer_player_trace — player i's executed-trace content, lifted over the
    leakage space via the run_interp projection at process index 2+i.
    @intent: single-player executed trace as a content random variable. *)
Definition denboer_player_trace (i : 'I_5) : {RV dbP -> 'I_5} :=
  fun w => content_of (nth [::] (run_interp 100 (denboer_rprocs w)).2 (2 + i)).

(** denboer_player_trace_shape — the run_interp projection at player i is the
    single dealt layout entry at the monodromy image of player i's start.
    @composes: denboer_trace_secrecy *)
Lemma denboer_player_trace_shape (a b : bool) (k : 'I_5) (i : 'I_5) :
  denboer_player_trace i (a, b, k)
    = tnth (den_boer_layout (a, b))
        (@pgg_rho FiveCardKim_M (five_card_group.fc_sigma ^+ k)%g (tnth (pi_starts FiveCardKim_PI) i)).
Proof.
rewrite /denboer_player_trace /denboer_rprocs.
have Hbr : den_boer_procs a b (five_card_group.fc_sigma ^+ k)%g 0
  = denboer_aprocs_abs (fun committed => tnth (den_boer_layout (den_boer_decode committed)))
      (encode_bool a) (encode_bool b) (five_card_group.fc_sigma ^+ k)%g by [].
rewrite Hbr.
case: i => -[|[|[|[|[|//]]]]] Hi.
- rewrite (denboer_abs_p0 (fun committed => tnth (den_boer_layout (den_boer_decode committed)))
    (encode_bool a) (encode_bool b) (five_card_group.fc_sigma ^+ k)%g) den_boer_decodeK.
  by congr (tnth _ (pgg_rho _ (tnth _ _))); apply: val_inj.
- rewrite (denboer_abs_p1 (fun committed => tnth (den_boer_layout (den_boer_decode committed)))
    (encode_bool a) (encode_bool b) (five_card_group.fc_sigma ^+ k)%g) den_boer_decodeK.
  by congr (tnth _ (pgg_rho _ (tnth _ _))); apply: val_inj.
- rewrite (denboer_abs_p2 (fun committed => tnth (den_boer_layout (den_boer_decode committed)))
    (encode_bool a) (encode_bool b) (five_card_group.fc_sigma ^+ k)%g) den_boer_decodeK.
  by congr (tnth _ (pgg_rho _ (tnth _ _))); apply: val_inj.
- rewrite (denboer_abs_p3 (fun committed => tnth (den_boer_layout (den_boer_decode committed)))
    (encode_bool a) (encode_bool b) (five_card_group.fc_sigma ^+ k)%g) den_boer_decodeK.
  by congr (tnth _ (pgg_rho _ (tnth _ _))); apply: val_inj.
- rewrite (denboer_abs_p4 (fun committed => tnth (den_boer_layout (den_boer_decode committed)))
    (encode_bool a) (encode_bool b) (five_card_group.fc_sigma ^+ k)%g) den_boer_decodeK.
  by congr (tnth _ (pgg_rho _ (tnth _ _))); apply: val_inj.
Qed.

(** denboer_player_trace_ok — the lifted player trace is encode_bool of the
    single-card colour the player sees: the monodromy rotation by fc_sigma^k
    equals the leakage rotation k.
    @composes: denboer_trace_secrecy *)
Lemma denboer_player_trace_ok (i : 'I_5) :
  denboer_player_trace i = encode_bool `o ((@thead 0 bool) `o (ViewA R [:: nat_of_ord i])).
Proof.
apply: boolp.funext => -[[a b] k].
rewrite denboer_player_trace_shape.
rewrite /comp_RV {1}/den_boer_layout tnth_map.
congr encode_bool.
rewrite /ViewA /arr /fc_shuffle.
rewrite /thead tnth_map (tnth_nth false) (tnth_nth i) /= nth_ord_enum.
have nth_rot_mod : forall (n p : nat) (xs : seq bool),
    n < 5 -> p < 5 -> size xs = 5 ->
    nth false (rot n xs) p = nth false xs ((p + n) %% 5).
  move=> n p xs Hn Hp Hxs.
  rewrite /rot nth_cat size_drop Hxs.
  case: (ltnP p (5 - n)) => Hpn.
    by rewrite nth_drop addnC modn_small // addnC -ltn_subRL.
  have Hqn : p - (5 - n) < n by rewrite ltn_subLR // subnK ?(ltnW Hn).
  rewrite nth_take //.
  have Heq2 : p + n - 5 = p - (5 - n) by rewrite subnBA ?(ltnW Hn).
  have Hpn5 : (5 <= p + n)%N by rewrite -(subnK (ltnW Hn)) leq_add2r.
  by rewrite -Heq2 -(subnK Hpn5) modnDr modn_small ?addnK //
     Heq2 (leq_ltn_trans (leq_subr _ _) Hp).
rewrite nth_rot_mod //.
- congr (nth false (fc_arrange a b) _).
  rewrite fc_sigma_pow_val.
  congr ((_ + k) %% 5); apply: val_inj => /=; rewrite (tnth_nth i) //.
- exact: ltn_ord.
- by rewrite fc_arrange_size.
Qed.

(** denboer_trace_secrecy — a single corrupted player's executed den Boer trace
    leaves the secret's conditional entropy equal to its plain entropy.
    @main security: single-player executed-trace secrecy via the monodromy-cut
    bridge, transporting the single-card view secrecy through the encode_bool
    codec. *)
Lemma denboer_trace_secrecy :
  `H( Secret R | denboer_player_trace ord0 ) = `H `p_ (Secret R).
Proof.
apply: (trace_secrecy_of_view (view := (@thead 0 bool) `o (ViewA R [:: 0%N]))
          (trace_of := encode_bool) (view_of := decode_bool)).
- exact: denboer_player_trace_ok ord0.
- exact: decode_encode_bool.
- exact: (inde_RV_comp (@thead 0 bool) (denboer_indep R)).
Qed.

End denboer_trace_sec.
