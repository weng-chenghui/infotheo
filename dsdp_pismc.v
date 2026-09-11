From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import smc_interpreter pismc.
Require Import smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.

Local Open Scope pismc_scope.
Local Open Scope ring_scope.

Section smc_dsdp_program.

(* Parameterize by a standalone DSDP interface.
   The same protocol text drives the cryptographic (Standard) instance below
   and a parameter-free symbolic instance. *)
Variable DI : DSDP_Interface.

(* Per-instance decoder for recv-and-decrypt (Standard supplies the scheme's
   [dec]; the symbolic instance supplies [HE_dec]). *)
Variable decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI).

(* Extract types from the interface *)
Let msgT := di_msgT DI.
Let randT := di_randT DI.
Let encT := di_cipherT DI.
Let priv_keyT := di_priv_keyT DI.
Let pub_keyT := di_pub_keyT DI.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_data_of_plain DI.
Let e := di_data_of_cipher DI.
Let priv_key := di_data_of_priv_key DI.

(* HE operations sourced from the interface *)
Let Emul := di_emul DI.
Let Epow := di_epow DI.

(* The plaintext ring operations of the interface, used by the final Ret.  They
   let the procs typecheck at a symbolic instance whose plaintexts carry no
   ring structure. *)
Let dadd := di_add DI.
Let dsub := di_sub DI.
Let dmul := di_mul DI.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Party identities *)
Variable alice : party_id.
Variable bob : party_id.
Variable charlie : party_id.

(* Concrete party indices for session type tracking *)
(* These must be distinct for duality verification to work with native_compute *)
Definition alice_idx : nat := 0.
Definition bob_idx : nat := 1.
Definition charlie_idx : nat := 2.

Coercion nat_to_party_id : nat >-> party_id.

(* Make dtype and data explicit for sproc type annotations *)
Arguments sproc dtype data party {_} {_}.

(* Use session-typed wrappers parameterized by the interface *)
Let PSend {party n env} := @DSend DI party n env.
Let Recv_dec {party n env} := @DRecv_dec DI decode party n env.
Let Recv_enc {party n env} := @DRecv_enc DI party n env.

(** * Data wrapper shorthand notations *)

(* #x -> (priv_key x) for private key *)
Local Notation "# x" := (priv_key x) (at level 0, x at level 0) : pismc_scope.
(* &x -> (d x) for data/message *)
Local Notation "& x" := (d x) (at level 0, x at level 0) : pismc_scope.
(* $x -> (e x) for encrypted *)
Local Notation "$ x" := (e x) (at level 0, x at level 0) : pismc_scope.

(* Finish, Init, and generic Ret notations are shared from pismc.v.
   Data wrapper notations (#, &, $) are parsed in constr scope
   within the shared Init/Ret notations. *)

Notation "'Send<' p '>' x ; P" := (PSend p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Protocol-specific Recv notations *)
Local Notation "'Recv<' p '>' x '=>' P" :=
  (Recv_enc p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Notation "'Recv<' p '>' '#' dk x '=>' P" :=
  (Recv_dec p dk (fun x => P))
  (in custom pismc at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom pismc at level 85, right associativity).

(******************************************************************************)
(** * DSDP Protocol Programs with Session Type Tracking                       *)
(** * Each encryption E(party, msg, rand) needs explicit randomness.          *)
(******************************************************************************)

(* Public key mapping: each party has an associated public key *)
Variable ek : party_id -> di_pub_keyT DI.

(* Party-indexed encryption: maps party to their public key for enc *)
Definition enc_pub_key (p : party_id) (m : msgT) (r : randT) : encT :=
  di_encrypt DI (ek p) m r.
Local Notation "'E<' r '>' p m" := (enc_pub_key p m r)
  (at level 10, r constr at level 0, p constr at level 0, m constr at level 0,
   format "'E<' r '>'  p  m").

(* Bob's protocol - using concrete indices for session type duality *)
Definition pbob (dk : priv_keyT)(v2 : msgT)(rb1 rb2 : randT)
    : sproc dsdp_dtype data bob_idx :=
  \pi{ Init (#dk, &v2) ;
     Send<alice_idx> $(E<rb1> bob_idx v2);
     Recv<alice_idx> #dk d2 =>
     Recv<alice_idx> a3 =>
     Send<charlie_idx> $(a3 *h (E<rb2> charlie_idx d2)) ;
     Finish }.

(* Charlie's protocol *)
Definition pcharlie (dk : priv_keyT)(v3 : msgT)(rc1 rc2 : randT)
    : sproc dsdp_dtype data charlie_idx :=
  \pi{ Init (#dk, &v3) ;
     Send<alice_idx> $(E<rc1> charlie_idx v3) ;
     Recv<bob_idx> #dk d3 =>
     Send<alice_idx> $(E<rc2> alice_idx d3) ;
     Finish }.

(* Alice's protocol *)
Definition palice (dk : priv_keyT)(v1 u1 u2 u3 r2 r3: msgT)(ra1 ra2 : randT)
    : sproc dsdp_dtype data alice_idx :=
  \pi{ Init (#dk, &v1, &u1, &u2, &u3, &r2, &r3) ;
     Recv<bob_idx> c2 =>
     Recv<charlie_idx> c3 =>
     Send<bob_idx> $(c2 ^h u2 *h (E<ra1> bob_idx r2)) ;
     Send<bob_idx> $(c3 ^h u3 *h (E<ra2> charlie_idx r3)) ;
     Recv<charlie_idx> #dk g =>
     Ret &(dadd (dsub (dsub g r2) r3) (dmul u1 v1)) }.


(******************************************************************************)
(** * Session Type Duality Verification                                       *)
(******************************************************************************)

Variables (dk : priv_keyT) (v1 u1 u2 u3 r2 r3 v2 v3 : msgT)
(ra1 ra2 rb1 rb2 rc1 rc2 : randT).

(* Wrap in aproc for duality checking *)
Definition aproc_alice := mk_aproc (palice dk v1 u1 u2 u3 r2 r3 ra1 ra2).
Definition aproc_bob := mk_aproc (pbob dk v2 rb1 rb2).
Definition aproc_charlie := mk_aproc (pcharlie dk v3 rc1 rc2).

(* Three-party duality verification *)
Lemma dsdp_compat : aprocs_compat [:: aproc_alice; aproc_bob; aproc_charlie].
Proof. by []. Qed.

(******************************************************************************)
(** * N-Party Protocol Templates (from Algorithm 2)                           *)
(******************************************************************************)

(* P₂: first relay party — recv_dec + recv_enc from P₁ *)
Definition DParty_first (self downstream : nat)
    (dk : priv_keyT) (v : msgT) (r1 r2 : randT)
    : sproc dsdp_dtype data self :=
  \pi{ Init (#dk, &v) ;
       Send<alice_idx> $(E<r1> self v) ;
       Recv<alice_idx> #dk d_val =>
       Recv<alice_idx> a_next =>
       Send<downstream> $(a_next *h (E<r2> downstream d_val)) ;
       Finish }.

(* Pᵢ (3≤i≤n-1): intermediate relay — recv_enc from P₁ + recv_dec from upstream *)
Definition DParty_intermediate (self alice_src upstream downstream : nat)
    (dk : priv_keyT) (v : msgT) (r1 r2 : randT)
    : sproc dsdp_dtype data self :=
  \pi{ Init (#dk, &v) ;
       Send<alice_src> $(E<r1> self v) ;
       Recv<alice_src> a_next =>
       Recv<upstream> #dk d_val =>
       Send<downstream> $(a_next *h (E<r2> downstream d_val)) ;
       Finish }.

(* Pₙ: last party — recv_dec from upstream, re-encrypt, send to P₁ *)
Definition DParty_last (self upstream : nat)
    (dk : priv_keyT) (v : msgT) (r1 r2 : randT)
    : sproc dsdp_dtype data self :=
  \pi{ Init (#dk, &v) ;
       Send<alice_idx> $(E<r1> self v) ;
       Recv<upstream> #dk d_val =>
       Send<alice_idx> $(E<r2> alice_idx d_val) ;
       Finish }.

(* Cross-equality: existing 3-party definitions are instances of templates *)
Lemma pbob_is_first dk' v2' rb1' rb2' :
  pbob dk' v2' rb1' rb2' =
  DParty_first bob_idx charlie_idx dk' v2' rb1' rb2'.
Proof. reflexivity. Qed.

Lemma pcharlie_is_last dk' v3' rc1' rc2' :
  pcharlie dk' v3' rc1' rc2' =
  DParty_last charlie_idx bob_idx dk' v3' rc1' rc2'.
Proof. reflexivity. Qed.

(* Duality verification on templated protocols *)
Definition aproc_bob_tmpl :=
  mk_aproc (DParty_first bob_idx charlie_idx dk v2 rb1 rb2).
Definition aproc_charlie_tmpl :=
  mk_aproc (DParty_last charlie_idx bob_idx dk v3 rc1 rc2).

Lemma dsdp_compat_tmpl :
  aprocs_compat [:: aproc_alice; aproc_bob_tmpl; aproc_charlie_tmpl].
Proof. by []. Qed.

(******************************************************************************)
(** * N-Party Alice Protocol                                                  *)
(******************************************************************************)

Section dsdp_n_party.

Variable n_relay : nat.

(* Destination for Alice's i-th send: relays 0 and 1 both go to party 1
   (first relay receives two messages), relay j >= 2 goes to party j *)
Definition alice_send_dest (j : nat) : nat := maxn 1 j.

(* N-party Alice over n_relay.+1 relays, the last of which returns the
   accumulated result.  At relay j she receives v_{j+1} and sends
   a_j = c_j^{u_{j+1}} * E(party_{j+1}, r_j, rand_j) to dest(j). *)
Let alice_env_step (j : 'I_n_relay.+1) (env : senv dsdp_dtype) :=
  senv_recv (senv_send env (alice_send_dest j) DT_Enc) j.+1 DT_Enc.

Definition palice_n
    (relays : seq 'I_n_relay.+1)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT)
    (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    : sproc dsdp_dtype data alice_idx :=
  \pi{ Init (#dk, &v0) ;
     ForList relays step (fun k => k.+2) enstep alice_env_step as j cont k =>
       Recv<(j.+1)> c =>
       Send<(alice_send_dest j)>
         $(c ^h (u (lift ord0 j)) *h (enc_pub_key j.+1 (r j) (rand_a j))) ;
       k
     end ;
     Recv<(n_relay.+1)> #dk g =>
     Ret &(dadd (foldl (fun acc j => dsub acc (r j)) g
                       (enum 'I_n_relay.+1))
                (dmul (u ord0) v0)) }.

(* Map relay index j to the appropriate relay template (first/intermediate/last).
   Requires n_relay >= 1 (at least 3 parties). *)
Definition relay_aproc (j : nat)
    (dk_j : priv_keyT) (v_j : msgT) (r1_j r2_j : randT)
    : aproc dsdp_dtype data :=
  if j == 0 then
    mk_aproc (DParty_first j.+1 j.+2 dk_j v_j r1_j r2_j)
  else if j == n_relay then
    mk_aproc (DParty_last j.+1 j dk_j v_j r1_j r2_j)
  else
    mk_aproc (DParty_intermediate j.+1 alice_idx j j.+2 dk_j v_j r1_j r2_j).

(* Build the full N-party aproc list: Alice + n_relay.+1 relay parties.
   Assumes n_relay >= 1 (at least 3 total parties). *)
Definition dsdp_n_saprocs
    (relays : seq 'I_n_relay.+1)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (dk_relay : 'I_n_relay.+1 -> priv_keyT)
    (v_relay : 'I_n_relay.+1 -> msgT)
    (r1_relay r2_relay : 'I_n_relay.+1 -> randT)
    : seq (aproc dsdp_dtype data) :=
  mk_aproc (palice_n relays dk v0 u r rand_a) ::
  map (fun j : 'I_n_relay.+1 =>
    relay_aproc j (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))
    relays.

Definition dsdp_n_procs
    (relays : seq 'I_n_relay.+1)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (dk_relay : 'I_n_relay.+1 -> priv_keyT)
    (v_relay : 'I_n_relay.+1 -> msgT)
    (r1_relay r2_relay : 'I_n_relay.+1 -> randT)
    : seq (proc data) :=
  erase_aprocs (dsdp_n_saprocs relays dk v0 u r rand_a dk_relay v_relay r1_relay r2_relay).

End dsdp_n_party.

(*******************************************************************************)
(** * Interpreter Integration                                                  *)
(*******************************************************************************)

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Session-typed processes for duality checking and fuel computation *)
Definition dsdp_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice dk v1 u1 u2 u3 r2 r3 ra1 ra2; pbob dk v2 rb1 rb2; pcharlie dk v3 rc1 rc2].

(* Erased processes for interpreter (strips session type indices) *)
Definition dsdp_procs : seq (proc data) :=
  erase_aprocs dsdp_saprocs.

(* Fuel bound computed from program structure:
   - palice: 14 (7*Init + 2*Recv_enc + 2*Send + Recv_dec + Ret=2)
   - pbob: 7 (2*Init + Send + Recv_dec + Recv_enc + Send + Finish=1)
   - pcharlie: 6 (2*Init + Send + Recv_dec + Send + Finish=1)
   Total: 14 + 7 + 6 = 27 *)
Lemma dsdp_max_fuel_ok : [> dsdp_saprocs] = 27.
Proof. reflexivity. Qed.

End smc_dsdp_program.

(******************************************************************************)
(** * Cross-equality with dsdp_program                                        *)
(** * Proves that piSMC programs equal the original dsdp_program definitions  *)
(******************************************************************************)

(* The piSMC procs above are discharged over an abstract [DSDP_Interface].
   The reference programs in dsdp_program.v are discharged over an
   [AHEncType].  The cross-equality therefore only typechecks once the piSMC
   procs are instantiated at the Standard interface [Standard_DSDP_Interface
   AHE] with [decode := @dec AHE] — the very instance dsdp_program.v also uses
   internally.  Hence this block lives AFTER the section, quantified over
   [AHE]. *)
Section dsdp_cross_equality.

Variable AHE : AHEncType.
Let DI := Standard_DSDP_Interface AHE.
Let decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) := @dec AHE.

(* Abstract party identifiers and the party-to-index mapping. *)
Variable alice : party_id.
Variable bob : party_id.
Variable charlie : party_id.
Variable pn : party_id -> nat.
Variable ek : party_id -> pub_key AHE.

Hypothesis pn_alice : pn alice = alice_idx.
Hypothesis pn_bob : pn bob = bob_idx.
Hypothesis pn_charlie : pn charlie = charlie_idx.
Hypothesis np_alice : nat_to_party_id alice_idx = alice.
Hypothesis np_bob : nat_to_party_id bob_idx = bob.
Hypothesis np_charlie : nat_to_party_id charlie_idx = charlie.

(* piSMC procs instantiated at the Standard interface. *)
Let palice_std := @palice DI decode ek.
Let pbob_std := @pbob DI decode ek.
Let pcharlie_std := @pcharlie DI decode ek.

(* Reference programs from dsdp_program. *)
Let palice_orig := @dsdp_program.palice AHE bob charlie pn ek.
Let pbob_orig := @dsdp_program.pbob AHE alice bob charlie pn ek.
Let pcharlie_orig := @dsdp_program.pcharlie AHE alice bob charlie pn ek.

(* Erased processes agree although their sproc types differ in session env
   indices.  The equality holds when pn maps parties to the expected indices. *)
Lemma alice_cross_eq dk' v1' u1' u2' u3' r2' r3' ra1' ra2' :
  erase (palice_std dk' v1' u1' u2' u3' r2' r3' ra1' ra2') =
  erase (palice_orig dk' v1' u1' u2' u3' r2' r3' ra1' ra2').
Proof.
by rewrite /palice_std /palice_orig /palice /dsdp_program.palice
           pn_bob pn_charlie
           /enc_pub_key /dsdp_program.enc_pk np_bob np_charlie.
Qed.

(* bob_cross_eq: the session-typed [pbob] at the Standard interface erases to
   the same [proc] as the reference [dsdp_program.pbob]. *)
Lemma bob_cross_eq dk' v2' rb1' rb2' :
  erase (pbob_std dk' v2' rb1' rb2') =
  erase (pbob_orig dk' v2' rb1' rb2').
Proof.
by rewrite /pbob_std /pbob_orig /pbob /dsdp_program.pbob
           pn_alice pn_charlie
           /enc_pub_key /dsdp_program.enc_pk np_bob np_charlie.
Qed.

(* charlie_cross_eq: the session-typed [pcharlie] at the Standard interface
   erases to the same [proc] as the reference [dsdp_program.pcharlie]. *)
Lemma charlie_cross_eq dk' v3' rc1' rc2' :
  erase (pcharlie_std dk' v3' rc1' rc2') =
  erase (pcharlie_orig dk' v3' rc1' rc2').
Proof.
by rewrite /pcharlie_std /pcharlie_orig /pcharlie /dsdp_program.pcharlie
           pn_alice pn_bob
           /enc_pub_key /dsdp_program.enc_pk np_alice np_charlie.
Qed.

End dsdp_cross_equality.
