(* DSDP corrupted-Alice simulation: the ideal-functionality and simulator
   packages and the type-level allowed-information witness.

   [dsdp_ideal_pkg] is the ideal functionality over the protocol state: its run
   oracle samples the honest inputs v2, v3, writes V_2 and the scalar-product
   output S = u1*v1 + u2*v2 + u3*v3 (weights from the seed) into [V_2_cell] and
   [Sout_cell], and returns unit; the two reveal oracles read the cells.
   [dsdp_simulator_pkg] imports the ideal interface and exports
   [game_iface_leak_S]: [sim_view_body] rebuilds the four-cipher corrupted view
   from the ideal run alone, so v2 / v3 / S have no path into the fabricated
   view — the type-level allowed-information witness.  [dsdp_adm] is the DSDP
   admissibility class.

   The cell writes and the reveal-oracle None fallbacks here mirror the real
   denotation [denote_run]'s GC_put / GC_put_output cases and
   [denote_v2_get_body] / [denote_Sout_get_body]; the leaked S matches the
   real [output_term] / [denote_output_termE] (u1*v1 + u2*v2 + u3*v3).  These
   are the ideal and simulator of the factorization
     [zero_game_leak_S ≈₀ dsdp_simulator_pkg ∘ dsdp_ideal_pkg].

   Scope: average-case corrupted-Alice secrecy — the honest inputs v2, v3 are
   sampled inside the ideal package, not fixed as adversary-chosen. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

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
Require Import smc.ssprove_ext_simulator smc.ssprove_ext_lossless_heap.
Require Import dsdp_game_code.
Require Import dsdp_symbolic_exec.
Require Import dsdp_game_derivation.
Require Import dsdp_indcpa_advantage.
Require Import dsdp_convert dsdp_guess_fiber.

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

Local Notation R := SSProve.Crypt.Axioms.R.

Section dsdp_simulator.
(* cloned context of Section dsdp_alice_guess (dsdp_main.v ~705), with the
   inverse embedding msg_of_chmsg and the sample-cardinality hypotheses the
   forthcoming factorization needs. *)
Variables (AHE : AHEncType) (Renc : finType) (card_renc : nat)
  (renc_card : #|Renc| = card_renc) (rand_of_renc : Renc -> rand AHE)
  (t_msg t_cipher : choice_type)
  (chmsg_of_msg : plain AHE -> t_msg)
  (chcipher_of_cipher : cipher AHE -> t_cipher)
  (pkey_of_party : party_id -> pub_key AHE)
  (card_msg : nat) (msg_of_idx : 'I_card_msg -> plain AHE) (rand0 : rand AHE).
Variable seed : denv AHE.
Variable msg_of_chmsg : t_msg -> plain AHE.
Hypothesis chmsg_of_msgK : cancel chmsg_of_msg msg_of_chmsg.
Hypothesis card_renc_neq : card_renc != card_msg.
Hypothesis card_msg_pos : (0 < card_msg)%N.
Hypothesis card_renc_pos : (0 < card_renc)%N.

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" := (cipher_list t_cipher)
  (in custom pack_type at level 2).

(* id_ideal_run — the allowed-information run operation identifier.  The
   identifiers 0/1/2/3 are id_game_run/id_guess/id_v2_get/id_Sout_get, so 4 is
   the first unused identifier. *)
Definition id_ideal_run : nat := 4%N.

(* I_dsdp_ideal — the allowed-information interface exported by the ideal
   package: a state-only run oracle and the two reveal oracles for the
   protocol V_2 sample and the scalar-product output S. *)
Definition I_dsdp_ideal : Interface :=
  [interface
     #val #[ id_ideal_run ] : 'unit → 'unit ;
     #val #[ id_v2_get    ] : 'unit → msg ;
     #val #[ id_Sout_get  ] : 'unit → msg ].

(* dsdp_ideal_pkg — the ideal functionality over the protocol state: the run
   oracle samples the honest inputs v2, v3, writes Some (chmsg_of_msg v2) into
   V_2_cell and Some (chmsg_of_msg (u1*v1 + u2*v2 + u3*v3)) into Sout_cell
   (weights u1,u2,u3,v1 = as_plain (de_val_nth seed 0/1/2/3)), and returns
   unit; the reveal oracles read the cells, returning chmsg_of_msg 0 when unset.
   The cell writes and the None fallbacks mirror denote_run's GC_put /
   GC_put_output cases and denote_v2_get_body / denote_Sout_get_body. *)
Definition dsdp_ideal_pkg :
  package [interface] I_dsdp_ideal :=
  [package (protocol_state t_msg) ;
    #def #[ id_ideal_run ] (_ : 'unit) : 'unit
    {
      x2 ← sample uniform card_msg ;;
      x3 ← sample uniform card_msg ;;
      let v2 := msg_of_idx x2 in
      let v3 := msg_of_idx x3 in
      let u1 := as_plain (de_val_nth seed 0) in
      let u2 := as_plain (de_val_nth seed 1) in
      let u3 := as_plain (de_val_nth seed 2) in
      let v1 := as_plain (de_val_nth seed 3) in
      #put (V_2_cell t_msg) := Some (chmsg_of_msg v2) ;;
      #put (Sout_cell t_msg) :=
        Some (chmsg_of_msg (u1 * v1 + u2 * v2 + u3 * v3)) ;;
      ret tt
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get (V_2_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None   => ret (chmsg_of_msg (0%R : plain AHE))
      end
    } ;
    #def #[ id_Sout_get ] (_ : 'unit) : msg
    {
      stored ← get (Sout_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None   => ret (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(* sim_view_body run_ideal — the simulator's fabricated corrupted-Alice view,
   quantifying over the ideal-run trigger run_ideal as its only
   allowed-information access.  It runs the ideal, samples the masks r2, r3,
   the mask-encryption randomnesses ra1, ra2 and the two hop randomnesses, and
   rebuilds the four-cipher view [a1; a2; c2; c3] from zeroed hop ciphertexts
   with the project's own enc / Emul / Epow.  v2, v3 and S have no path into
   this code: the type-level allowed-information witness. *)
Definition sim_view_body (run_ideal : raw_code 'unit) :
  raw_code (cipher_list t_cipher) :=
  _ ← run_ideal ;;
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
   validates its allowed-information access run_ideal; the samples and the
   cipher-view return impose no further interface constraint. *)
Lemma valid_sim_view_body (L : Locations) (I : Interface)
    (run_ideal : raw_code 'unit)
    (H1 : ValidCode L I run_ideal) :
    ValidCode L I (sim_view_body run_ideal).
Proof.
rewrite /sim_view_body.
apply: valid_bind.
move=> _; ssprove_valid.
Qed.

(* Register valid_sim_view_body so the [package] validity resolver descends
   through the opaque sim_view_body head. *)
#[local] Hint Extern 2 (ValidCode ?L ?I (sim_view_body ?r)) =>
  eapply valid_sim_view_body
  : typeclass_instances ssprove_valid_db.

(* dsdp_simulator_pkg — the simulator importing I_dsdp_ideal and exporting
   game_iface_leak_S: id_game_run drives sim_view_body on the ideal-run call,
   and the two reveal oracles pass the ideal's V_2 and S reads through. *)
Definition dsdp_simulator_pkg :
  package I_dsdp_ideal (game_iface_leak_S t_msg t_cipher) :=
  [package emptym ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      sim_view_body
        (#import {sig #[ id_ideal_run ] : 'unit → 'unit } as call_ideal ;;
         r ← call_ideal Datatypes.tt ;; ret r)
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

(* dsdp_adm — the DSDP admissibility class: the adversary locations are
   disjoint from the protocol state and from the real and zero encryption
   oracle location sets. *)
Definition dsdp_adm (LA : Locations) (A : raw_package) : Prop :=
  fseparate LA (protocol_state t_msg) /\
  fseparate LA (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                        chcipher_of_cipher pkey_of_party)) /\
  fseparate LA (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                        chcipher_of_cipher pkey_of_party)).

(* dsdp_simulator_factorization — the output-exposing all-zero endpoint game
   is perfectly equivalent to the simulator composed with the ideal
   functionality, with no epsilon term.  Average-case scope: the honest
   inputs v2, v3 are sampled inside the ideal. *)
Lemma dsdp_simulator_factorization :
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed
  ≈₀ dsdp_simulator_pkg ∘ dsdp_ideal_pkg.
Proof.
eapply eq_rel_perf_ind_eq.
simplify_eq_rel m.
(* id_game_run: collapse the stuck cardinality-dispatch guards, then commute
   the ideal's two early cell writes (V_2, Sout) rightward past the
   simulator's mask and hop-randomness samples so both sides share the run's
   sample-then-write order; the de Bruijn value reads compute to the same
   scalar product and cipher view. *)
1: rewrite !eqxx !(negbTE card_renc_neq).
- ssprove_sync_eq=> x_v2.
  ssprove_sync_eq=> x_v3.
  ssprove_swap_seq_rhs [:: 1; 2; 3; 4; 5; 6]%N.
  ssprove_swap_seq_rhs [:: 0; 1; 2; 3]%N.
  ssprove_sync_eq=> x_r2.
  ssprove_sync_eq=> x_r3.
  ssprove_sync_eq=> x_ra1.
  ssprove_sync_eq=> x_ra2.
  ssprove_sync_eq.
  ssprove_sync_eq=> x_c2.
  ssprove_sync_eq=> x_c3.
  cbn [de_val_nth de_rand_nth de_val de_rand push_val push_rand nth
       as_plain as_cipher nat_to_party_id].
  by rewrite /de_val_nth; ssprove_sync_eq; apply: r_ret; move=> ? ? ->.
- ssprove_code_simpl.
  rewrite /denote_v2_get_body.
  ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
- ssprove_code_simpl.
  rewrite /denote_Sout_get_body.
  ssprove_sync_eq=> stored.
  by case: stored => [v|]; apply: r_ret.
Qed.

(* dsdp_adv_sim_le — the output-exposing real game is
   bounded-simulation secure against dsdp_ideal_pkg with simulator
   dsdp_simulator_pkg over the dsdp_adm class, with bound [2 * epsilon_cpa].
   Average-case scope: the honest inputs v2, v3 are sampled inside the
   ideal package. *)
Lemma dsdp_adv_sim_le
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher) :
  adv_sim_le (game_iface_leak_S t_msg t_cipher) dsdp_adm
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    dsdp_ideal_pkg dsdp_simulator_pkg
    (2%:R * epsilon_cpa).
Proof.
apply: (adv_sim_le_from_endpoint
  (Endpoint := zero_game_leak_S renc_card rand_of_renc chmsg_of_msg
     chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed)).
- move=> LA A A_valid [Hstate [Hore Hoze]].
  eapply dsdp_advantage_derived_leak_S.
  + exact: chcipher_of_cipherK.
  + exact: chmsg_of_msgK.
  + exact: A_valid.
  + exact: Hstate.
  + exact: Hore.
  + exact: Hoze.
- move=> LA A A_valid [Hstate _].
  exact: (dsdp_simulator_factorization A_valid Hstate Hstate).
Qed.

(* view_pair_challenger — the pair-returning experiment: run the game and read
   the leaked output S, returning the pair (cipher view, S). *)
Definition view_pair_challenger :
  package (game_iface_leak_S t_msg t_cipher)
    [interface #val #[ 0%N ] : 'unit → (ciphers × msg) ] :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : (ciphers × msg)
    {
      #import {sig #[ id_game_run ] : 'unit → ciphers } as call_run ;;
      #import {sig #[ id_Sout_get ] : 'unit → msg } as call_Sout ;;
      view ← call_run Datatypes.tt ;;
      Sout_val ← call_Sout Datatypes.tt ;;
      ret (view, Sout_val)
    }
  ].

(* view_op — the operation signature reading view_pair_challenger's pair. *)
Definition view_op : opsig :=
  (0%N, (chUnit, chProd (cipher_list t_cipher) t_msg)).

(* view_resolved G — the view-dumper challenger linked with a game G,
   resolved at view_op into closed pair-returning code. *)
Definition view_resolved (G : raw_package) :
  raw_code (chProd (cipher_list t_cipher) t_msg) :=
  resolve (view_pair_challenger ∘ G) view_op Datatypes.tt.

(* test_adversary D — the boolean distinguisher applying the predicate D to
   the pair (cipher view, S). *)
Definition test_adversary (D : (cipher_list t_cipher * t_msg)%type -> bool) :
  package (game_iface_leak_S t_msg t_cipher) A_export :=
  [package emptym ;
    #def #[ 0%N ] (_ : 'unit) : 'bool
    {
      #import {sig #[ id_game_run ] : 'unit → ciphers } as call_run ;;
      #import {sig #[ id_Sout_get ] : 'unit → msg } as call_Sout ;;
      view ← call_run Datatypes.tt ;;
      Sout_val ← call_Sout Datatypes.tt ;;
      ret (D (view, Sout_val) : 'bool)
    }
  ].

(* view_resolve_eq — the first-projection subdistribution of the resolved
   distinguisher is the pushforward under D of the first-projection
   subdistribution of the resolved view-dumper experiment. *)
Lemma view_resolve_eq (G : raw_package)
    (D : (cipher_list t_cipher * t_msg)%type -> bool) :
  Pr_fst (resolve (test_adversary D ∘ G) RUN Datatypes.tt)
  = distr.dmargin (fun p => (D p : 'bool)) (Pr_fst (view_resolved G)).
Proof.
have resolve_eq :
  resolve (test_adversary D ∘ G) RUN Datatypes.tt
  = (p ← view_resolved G ;; ret (D p : 'bool)).
{ rewrite /view_resolved !resolve_link.
  have body_eq : resolve (test_adversary D) RUN Datatypes.tt
    = (p ← resolve view_pair_challenger view_op Datatypes.tt ;;
       ret (D p : 'bool)).
  { rewrite /resolve /test_adversary /view_pair_challenger /=.
    by rewrite !coerce_kleisliE /=. }
  by rewrite body_eq code_link_bind. }
by rewrite resolve_eq Pr_fst_map.
Qed.

(* sample_cards_msg_renc gc — every GC_sample cardinality in gc is card_msg or
   card_renc. *)
Fixpoint sample_cards_msg_renc (gc : game_code) : bool :=
  match gc with
  | GC_sample n k =>
      ((n == card_msg) || (n == card_renc)) && sample_cards_msg_renc k
  | GC_put _ k => sample_cards_msg_renc k
  | GC_put_output _ k => sample_cards_msg_renc k
  | GC_let _ k => sample_cards_msg_renc k
  | GC_enc_hop _ _ k => sample_cards_msg_renc k
  | GC_ret _ => true
  end.

(* denote_run_lossless_heap — the denoted game-code core is heap-parametric
   lossless whenever its sample cardinalities are the two positive sorts. *)
Lemma denote_run_lossless_heap (gc : game_code) (e : denv AHE) :
  sample_cards_msg_renc gc ->
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

(* sample_cards_msg_renc_all_zero — the all-zero output-exposing DSDP game
   has only card_msg and card_renc sample cardinalities. *)
Local Lemma sample_cards_msg_renc_all_zero :
  sample_cards_msg_renc
    (all_zero (game_of_trace_seeded dsdp_weight_names
       (dsdp_alice_obs_leak_S_seeded card_msg card_renc))) = true.
Proof.
rewrite /all_zero /game_of_trace_seeded /dsdp_weight_names
        /dsdp_alice_obs_leak_S_seeded.
cbn [sample_cards_msg_renc lower_obs zero_hop_prefix count_hops].
by rewrite !eqxx !orbT.
Qed.

(* sample_cards_msg_renc_all_real — the all-real output-exposing DSDP game
   has only card_msg and card_renc sample cardinalities. *)
Local Lemma sample_cards_msg_renc_all_real :
  sample_cards_msg_renc
    (all_real (game_of_trace_seeded dsdp_weight_names
       (dsdp_alice_obs_leak_S_seeded card_msg card_renc))) = true.
Proof.
rewrite /all_real /game_of_trace_seeded /dsdp_weight_names
        /dsdp_alice_obs_leak_S_seeded.
cbn [sample_cards_msg_renc lower_obs zero_hop_prefix count_hops].
by rewrite !eqxx !orbT.
Qed.

(* resolve_denote_game_leak_S_run — the run oracle of the output-exposing
   denotation resolves to the game-code run denotation. *)
Local Lemma resolve_denote_game_leak_S_run (gc : game_code) :
  resolve
    (denote_game_leak_S_raw renc_card rand_of_renc chmsg_of_msg
       chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed gc)
    (id_game_run, ('unit, cipher_list t_cipher)) Datatypes.tt
  = denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
      pkey_of_party msg_of_idx rand0 seed gc.
Proof.
rewrite /resolve /denote_game_leak_S_raw mkfmapE
        /id_game_run /id_v2_get /id_Sout_get /fst.
cbn [getm_def]; cbn [fst snd].
by rewrite eqxx /mkdef coerce_kleisliE.
Qed.

(* resolve_denote_game_leak_S_Sout — the output-reveal oracle of the
   output-exposing denotation resolves to the Sout-cell read body. *)
Local Lemma resolve_denote_game_leak_S_Sout (gc : game_code) :
  resolve
    (denote_game_leak_S_raw renc_card rand_of_renc chmsg_of_msg
       chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed gc)
    (id_Sout_get, ('unit, t_msg)) Datatypes.tt
  = denote_Sout_get_body chmsg_of_msg.
Proof.
rewrite /resolve /denote_game_leak_S_raw mkfmapE
        /id_game_run /id_v2_get /id_Sout_get /fst.
cbn [getm_def]; cbn [fst snd].
by rewrite -[(3 == 0)%N]/false -[(3 == 2)%N]/false eqxx /mkdef coerce_kleisliE.
Qed.

(* view_resolved_denote — the resolved view-dumper over a denoted game is
   the run denotation sequenced with the Sout read and the pair return. *)
Local Lemma view_resolved_denote (gc : game_code) :
  view_resolved
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed gc)
  = (view ← denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
               pkey_of_party msg_of_idx rand0 seed gc ;;
     Sout_val ← denote_Sout_get_body chmsg_of_msg ;;
     ret (view, Sout_val)).
Proof.
rewrite /view_resolved resolve_link /resolve /view_pair_challenger /=.
rewrite coerce_kleisliE.
cbn [code_link].
rewrite resolve_denote_game_leak_S_run resolve_denote_game_leak_S_Sout.
by rewrite /denote_Sout_get_body.
Qed.

(* view_mass1_denote — the resolved view-dumper over a denoted game whose
   sample cardinalities are the two positive sorts has first-projection
   subdistribution mass one. *)
Local Lemma view_mass1_denote (gc : game_code) :
  sample_cards_msg_renc gc ->
  psum (distr.mu (Pr_fst (view_resolved
    (denote_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed gc)))) = 1.
Proof.
move=> Hcards.
rewrite view_resolved_denote.
apply: LosslessHeap_Pr_fst.
apply: LosslessHeap_bind.
- by apply: denote_run_lossless_heap.
- move=> view.
  apply: LosslessHeap_bind.
  + rewrite /denote_Sout_get_body.
    apply: LosslessHeap_get => v; case: v => [x|]; exact: LosslessHeap_ret.
  + move=> Sout_val; exact: LosslessHeap_ret.
Qed.

(* view_zero_mass1 — the resolved view-dumper over the all-zero endpoint game
   has first-projection subdistribution mass one. *)
Lemma view_zero_mass1 :
  psum (distr.mu (Pr_fst (view_resolved
    (zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)))) = 1.
Proof.
rewrite /zero_game_leak_S.
apply: view_mass1_denote.
exact: sample_cards_msg_renc_all_zero.
Qed.

(* view_real_mass1 — the resolved view-dumper over the all-real endpoint game
   has first-projection subdistribution mass one. *)
Lemma view_real_mass1 :
  psum (distr.mu (Pr_fst (view_resolved
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)))) = 1.
Proof.
rewrite /real_game_leak_S.
apply: view_mass1_denote.
exact: sample_cards_msg_renc_all_real.
Qed.

(* view_simulated_mass1 — the resolved view-dumper over the simulator composed
   with the ideal functionality has first-projection subdistribution mass
   one. *)
Lemma view_simulated_mass1 :
  psum (distr.mu (Pr_fst (view_resolved
    (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)))) = 1.
Proof.
apply: LosslessHeap_Pr_fst.
rewrite /view_resolved resolve_link /resolve /view_pair_challenger /=.
rewrite coerce_kleisliE.
cbn [code_link].
rewrite !resolve_link.
apply: LosslessHeap_bind.
- rewrite /resolve setmE eqxx /mkdef coerce_kleisliE.
  rewrite /sim_view_body code_link_bind.
  apply: LosslessHeap_bind.
  + cbn [code_link].
    rewrite /resolve setmE eqxx coerce_kleisliE.
    apply: LosslessHeap_bind.
    * apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
      move=> x2.
      apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
      move=> x3.
      apply: LosslessHeap_put.
      apply: LosslessHeap_put.
      exact: LosslessHeap_ret.
    * move=> b1; exact: LosslessHeap_ret.
  + move=> b1.
    cbn [code_link].
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x_r2.
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x_r3.
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x_ra1.
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x_ra2.
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x_c2.
    apply: LosslessHeap_sample; first exact: LosslessOp_uniform.
    move=> x_c3.
    exact: LosslessHeap_ret.
- move=> b_view.
  apply: LosslessHeap_bind.
  + rewrite /resolve /id_game_run /id_v2_get /id_Sout_get !setmE /fst.
    rewrite -[(3 == 0)%N]/false -[(3 == 2)%N]/false eqxx /mkdef coerce_kleisliE.
    cbn [code_link].
    rewrite /resolve /id_ideal_run !setmE /fst.
    rewrite -[(3 == 4)%N]/false -[(3 == 2)%N]/false eqxx coerce_kleisliE.
    apply: LosslessHeap_bind.
    * apply: LosslessHeap_get => stored.
      case: stored => [v|]; exact: LosslessHeap_ret.
    * move=> b0; exact: LosslessHeap_ret.
  + move=> b0; exact: LosslessHeap_ret.
Qed.

End dsdp_simulator.
