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

End dsdp_simulator.
