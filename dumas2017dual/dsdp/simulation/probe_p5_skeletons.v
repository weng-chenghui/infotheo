(* PROBE P5 — simulation-security skeletons (design probe).

   Type-checks the statements and package interfaces of a planned SSProve
   simulator extension for DSDP: a generic bounded-simulation layer (Part A),
   the DSDP ideal/simulator packages and headline theorems (Part B), and the
   P4 view-dumper resolution shape (Part C).  Proofs are Admitted where a
   perfect-equivalence obligation is out of probe scope; every other proof is
   closed with Qed.  This file is not imported by any other module. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum lra.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import homomorphic_encryption indcpa_ror.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code dsdp_symbolic_exec dsdp_game_derivation.
Require Import dsdp_indcpa_advantage dsdp_convert dsdp_guess_fiber.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

(* Pin SSProve's real type as the ambient realType. *)
Notation R := SSProve.Crypt.Axioms.R.

(* ================================================================= *)
(* PART A — generic bounded simulation security                      *)
(* ================================================================= *)

Section bounded_simulation.

(* adv_sim_le E adm Real Ideal Sim eps — bounded simulation security relative
   to the admissible-adversary class adm: every valid, admissible adversary
   distinguishes the real package from the simulator composed with the ideal
   package with advantage at most eps. *)
Definition adv_sim_le (E : Interface) (adm : Locations -> raw_package -> Prop)
    (Real Ideal Sim : raw_package) (eps : R) : Prop :=
  forall (LA : Locations) (A : raw_package),
    ValidPackage LA E A_export A -> adm LA A ->
    AdvantageE Real (Sim ∘ Ideal) A <= eps.

(* Simulates_from_endpoint — a real-versus-endpoint advantage bound of eps and
   a perfect equivalence between the endpoint and the simulated ideal package
   give bounded simulation security with bound eps. *)
Lemma Simulates_from_endpoint
    (E : Interface) (adm : Locations -> raw_package -> Prop)
    (Real Endpoint Ideal Sim : raw_package) (eps : R)
    (Hgame : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> adm LA A ->
       AdvantageE Real Endpoint A <= eps)
    (Hsim : forall (LA : Locations) (A : raw_package),
       ValidPackage LA E A_export A -> adm LA A ->
       AdvantageE Endpoint (Sim ∘ Ideal) A = 0) :
  adv_sim_le E adm Real Ideal Sim eps.
Proof.
move=> LA A A_valid A_adm.
apply: (le_trans (Advantage_triangle Real (Sim ∘ Ideal) Endpoint A)).
rewrite (Hsim LA A A_valid A_adm) addr0.
exact: (Hgame LA A A_valid A_adm).
Qed.

(* Simulates_reduction — bounded simulation security transports across a
   common context T applied on the left: for any admissible composite adversary
   [A ∘ T], the advantage of A against the T-linked real and simulated ideal
   packages is at most eps.  Admissibility must be closed under [A ∘ T]. *)
Lemma Simulates_reduction
    (E : Interface) (adm : Locations -> raw_package -> Prop)
    (Real Ideal Sim : raw_package) (eps : R)
    (Hsim : adv_sim_le E adm Real Ideal Sim eps)
    (T A : raw_package) (LAT : Locations)
    (AT_valid : ValidPackage LAT E A_export (A ∘ T))
    (AT_adm : adm LAT (A ∘ T)) :
  AdvantageE (T ∘ Real) (T ∘ Sim ∘ Ideal) A <= eps.
Proof.
rewrite -Advantage_link.
exact: (Hsim LAT (A ∘ T) AT_valid AT_adm).
Qed.

End bounded_simulation.

(* ================================================================= *)
(* PART B — DSDP ideal / simulator instantiation                     *)
(* ================================================================= *)

Section dsdp_simulation_skeleton.
(* Cloned context of Section dsdp_alice_guess (dsdp_main.v). *)
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

Local Notation "'msg'" := t_msg (in custom pack_type at level 2).
Local Notation "'ciphers'" :=
  (cipher_list t_cipher) (in custom pack_type at level 2).

(* id_ideal_run — the allowed-information run operation identifier.  The game
   oracles id_game_run/id_guess/id_v2_get/id_Sout_get occupy 0/1/2/3, so 4 is
   the first free identifier. *)
Definition id_ideal_run : nat := 4%N.

(* I_dsdp_ideal — the allowed-information interface exported by the ideal
   package: a state-only run and the two reveal oracles. *)
Definition I_dsdp_ideal : Interface :=
  [interface
     #val #[ id_ideal_run ] : 'unit → 'unit ;
     #val #[ id_v2_get    ] : 'unit → msg ;
     #val #[ id_Sout_get  ] : 'unit → msg ].

(* dsdp_ideal_pkg — the ideal package over protocol_state exporting
   I_dsdp_ideal: id_ideal_run is a state update, the reveal oracles read
   V_2_cell and Sout_cell (placeholder bodies). *)
Definition dsdp_ideal_pkg :
  package [interface] I_dsdp_ideal :=
  [package protocol_state t_msg ;
    #def #[ id_ideal_run ] (_ : 'unit) : 'unit
    {
      #put (Sout_cell t_msg) := None ;;
      @ret 'unit tt
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get (V_2_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None => ret (chmsg_of_msg (0%R : plain AHE))
      end
    } ;
    #def #[ id_Sout_get ] (_ : 'unit) : msg
    {
      stored ← get (Sout_cell t_msg) ;;
      match stored with
      | Some v => ret v
      | None => ret (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(* dsdp_simulator_pkg — the simulator importing I_dsdp_ideal and exporting
   game_iface_leak_S: id_game_run drives the ideal run and returns an empty
   cipher list, the reveal oracles are pass-throughs (placeholder bodies). *)
Definition dsdp_simulator_pkg :
  package I_dsdp_ideal (game_iface_leak_S t_msg t_cipher) :=
  [package emptym ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      #import {sig #[ id_ideal_run ] : 'unit → 'unit } as call_ideal ;;
      _ ← call_ideal Datatypes.tt ;;
      @ret (cipher_list t_cipher) [::]
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

(* dsdp_simulator_factorization — the all-zero output-exposing game is
   perfectly equivalent to the simulator composed with the ideal package. *)
Lemma dsdp_simulator_factorization :
  zero_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 seed
  ≈₀ dsdp_simulator_pkg ∘ dsdp_ideal_pkg.
Proof.
Admitted.

(* dsdp_adm — the DSDP admissibility class: the adversary locations are
   disjoint from the protocol state and from the real and zero encryption
   oracle locations. *)
Definition dsdp_adm (LA : Locations) (A : raw_package) : Prop :=
  fseparate LA (protocol_state t_msg) /\
  fseparate LA (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                        chcipher_of_cipher pkey_of_party)) /\
  fseparate LA (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                        chcipher_of_cipher pkey_of_party)).

(* dsdp_simulation_secure — the output-exposing real game is
   bounded-simulation secure against dsdp_ideal_pkg with simulator
   dsdp_simulator_pkg, over the
   dsdp_adm class, with bound [2 * epsilon_cpa]. *)
Lemma dsdp_simulation_secure
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher) :
  adv_sim_le (game_iface_leak_S t_msg t_cipher) dsdp_adm
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    dsdp_ideal_pkg dsdp_simulator_pkg
    (2%:R * epsilon_cpa).
Proof.
apply: (Simulates_from_endpoint
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
  apply: (dsdp_simulator_factorization A_valid Hstate).
  exact: Hstate.
Qed.

(* dsdp_simulator_headline — every valid adversary whose locations are
   disjoint from the protocol state and the two encryption oracle location sets
   distinguishes the output-exposing real game from the simulator composed with
   the ideal package with advantage at most [2 * epsilon_cpa]. *)
Theorem dsdp_simulator_headline
    (cipher_of_chcipher : t_cipher -> cipher AHE)
    (chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher)
    (LA : Locations) (A : raw_package)
    (A_valid : ValidPackage LA (game_iface_leak_S t_msg t_cipher) A_export A)
    (A_disj_state : fseparate LA (protocol_state t_msg))
    (A_disj_ore : fseparate LA
       (locs (oracle_real_pkg renc_card rand_of_renc msg_of_chmsg
                chcipher_of_cipher pkey_of_party)))
    (A_disj_oze : fseparate LA
       (locs (oracle_zero_pkg renc_card rand_of_renc t_msg
                chcipher_of_cipher pkey_of_party))) :
  AdvantageE
    (real_game_leak_S renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
       pkey_of_party msg_of_idx rand0 seed)
    (dsdp_simulator_pkg ∘ dsdp_ideal_pkg)
    A <= 2%:R * epsilon_cpa.
Proof.
apply: (dsdp_simulation_secure chcipher_of_cipherK).
by split;
  [exact: A_disj_state | split; [exact: A_disj_ore | exact: A_disj_oze]].
Qed.

(* ================================================================= *)
(* PART C — P4 view-dumper resolution shape                          *)
(* ================================================================= *)

(* view_dump_challenger — the pair-returning experiment code: it runs the game
   and reads the leaked output S, returning the pair (cipher view, S). *)
Definition view_dump_challenger :
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

(* view_op — the operation signature reading view_dump_challenger's pair
   output. *)
Definition view_op : opsig :=
  (0%N, (chUnit, chProd (cipher_list t_cipher) t_msg)).

(* view_dump_resolved — the closed pair-returning experiment: the view-dumper
   challenger linked with a game G, resolved at view_op. *)
Definition view_dump_resolved (G : raw_package) :
  raw_code (chProd (cipher_list t_cipher) t_msg) :=
  resolve (view_dump_challenger ∘ G) view_op Datatypes.tt.

(* test_adversary D — the boolean distinguisher applying a predicate D to the
   pair (cipher view, S). *)
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

(* view_dump_resolve_eq — the first-projection subdistribution of the resolved
   distinguisher is the pushforward under D of the first-projection
   subdistribution of the resolved view-dumper experiment. *)
Lemma view_dump_resolve_eq (G : raw_package)
    (D : (cipher_list t_cipher * t_msg)%type -> bool) :
  Pr_fst (resolve (test_adversary D ∘ G) RUN Datatypes.tt)
  = distr.dmargin (fun p => (D p : 'bool)) (Pr_fst (view_dump_resolved G)).
Proof.
Admitted.

End dsdp_simulation_skeleton.
