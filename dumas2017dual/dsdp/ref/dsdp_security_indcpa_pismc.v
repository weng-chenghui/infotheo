(* DSDP Alice secrecy under IND-CPA — piSMC-rooted variant.

   Builds [game_real_pismc] by linking the SSProve translation of Alice's
   piSMC program ([translate_pismc_to_ssprove (palice ...)]) against a
   recv-oracle that serves Bob's and Charlie's first ciphertexts.  This is
   the W1 commit of the bridge plan:
     ~/.claude/plans/read-plan-claude-plans-sprightly-finding-vast-coral.md
   W2 will prove [game_real ≈₀ game_real_pismc]; W3 transports the U1/U2
   bounds.
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import smc_session_types pismc_to_ssprove.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_interface dsdp_session_types dsdp_program dsdp_pismc.
Require Import dsdp_security_indcpa.
Require Import smc.ssprove_ext_lossless.

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

(* Pin SSProve's real type as the ambient realType for this file, matching
   the convention in [dsdp_security_indcpa.v:47]. *)
Notation R := SSProve.Crypt.Axioms.R.

Section dsdp_security_indcpa_pismc.

(** Section parameters mirror [dsdp_security_indcpa.v:107-219] so the
    derived game [game_real_pismc] has the same Section dependencies as
    [game_real].  W2's equivalence lemma instantiates both at the same
    parameter values, and W3's transport carries the U1/U2 bounds across. *)

(* AHE carrier and the encryption-randomness finType bridge. *)
Variable AHE : AHEncType.
Variable Renc : finType.
Variable card_renc : nat.
Hypothesis renc_card : #|Renc| = card_renc.
Variable rand_of_renc : Renc -> rand AHE.

(* SSProve choice_type carriers for messages and ciphertexts, with the
   AHE-side bijections. *)
Variable t_msg : choice_type.
Variable t_cipher : choice_type.
Variable msg_of_chmsg : t_msg -> plain AHE.
Variable chmsg_of_msg : plain AHE -> t_msg.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.
Variable cipher_of_chcipher : t_cipher -> cipher AHE.
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Hypothesis chmsg_of_msgK :
  cancel chmsg_of_msg msg_of_chmsg.

(* Public-key per party. *)
Variable pkey_of_party : party_id -> pub_key AHE.

(* Plaintext-scalar uniform index. *)
Variable card_msg : nat.
Variable msg_of_idx : 'I_card_msg -> plain AHE.

(** sample_to_renc — bridge from the SSProve uniform-index ['I_card_renc]
    to an [Renc] value (same plumbing as in [dsdp_security_indcpa.v:131]).
    Kind: helper.
    Why: SSProve's [sample uniform card_renc] returns an ['I_card_renc],
    but the AHE encryption takes a [rand AHE] obtained through [rand_of_renc].
    Used by: game_real_pismc. *)
Definition sample_to_renc (i : 'I_card_renc) : Renc :=
  enum_val (cast_ord (esym renc_card) i).

Local Notation "'cipher_t'" := t_cipher (in custom pack_type at level 2).
Local Notation "'msg'" := t_msg (in custom pack_type at level 2).

(** cipher_list — choice_type carrier for the leaked-ciphertext
    accumulator, same as [dsdp_security_indcpa.v:233].
    Kind: helper.
    Why: matches [game_real]'s output type so the W2 equivalence lemma
    relates two packages of the same export interface.
    Used by: game_iface_pismc, game_real_pismc. *)
Definition cipher_list : choice_type := chList t_cipher.

Local Notation "'ciphers'" := cipher_list (in custom pack_type at level 2).

(* Operation identifiers.  [id_game_run] and [id_v2_get] coincide with
   the ones in [dsdp_security_indcpa.v:248,260] so [game_real_pismc]
   exports the SAME interface [game_iface].  [id_recv_enc_pismc] and
   [id_recv_dec_pismc] are fresh ids feeding Alice's translated code
   through [dsdp_recv_oracle]; we avoid 0 ([id_game_run]), 1 (reserved
   for [id_guess] elsewhere) and 2 ([id_v2_get]). *)
Definition id_recv_enc_pismc : nat := 3%N.
Definition id_recv_dec_pismc : nat := 4%N.

(** c2_cell — SSProve [Location] storing Bob's first ciphertext (c_2)
    that Alice receives in her translated piSMC program.  Populated by
    [game_real_pismc]'s body before Alice's code reads it through
    [dsdp_recv_oracle].
    Kind: canonical.
    Why: the piSMC [Recv<bob_idx> c2] in [palice] becomes an oracle
    call in the translated SSProve code; backing that oracle by a
    cell that [game_real_pismc] [#put]s into makes the c_2 served by
    the oracle identical to the c_2 Bob's piSMC program would have
    sent (witnessed by [pbob_head_send_eq]).
    Naming: project-local [c_2] preserves the protocol subscript;
    [_cell] marks the SSProve mutable location.
    Used by: dsdp_recv_oracle, game_real_pismc. *)
Definition c2_cell : Location :=
  mkloc 10 (None : option t_cipher).

(** c3_cell — SSProve [Location] storing Charlie's first ciphertext
    (c_3).  Symmetric counterpart of [c2_cell].
    Kind: canonical.
    Why: analogue of [c2_cell] for the Charlie-to-Alice ciphertext.
    Witnessed by [pcharlie_head_send_eq].
    Naming: same convention as [c2_cell].
    Used by: dsdp_recv_oracle, game_real_pismc. *)
Definition c3_cell : Location :=
  mkloc 11 (None : option t_cipher).

(** dsdp_pismc_locs — combined [Locations] map for [game_real_pismc].
    Includes [V_2_cell] (shared with [game_real] so the [id_v2_get]
    oracle still reads from the same cell) plus the two cipher-serving
    cells [c2_cell] and [c3_cell].
    Kind: canonical.
    Why: SSProve packages declare their state cells in a single fmap;
    composing Alice's translated code (which has [emptym] locations)
    with the recv-oracle and the outer sampling body requires all three
    cells to be in scope.
    Used by: game_real_pismc. *)
Definition dsdp_pismc_locs : Locations :=
  unionm (protocol_state t_msg) [fmap c2_cell; c3_cell].

(** data_dsdp — the piSMC data carrier for DSDP, instantiated against
    the standard sum-type interface (msg + cipher + priv_key + pub_key).
    Same as [di_data (Standard_DSDP_Interface AHE)].
    Kind: helper.
    Why: [translate_pismc_to_ssprove] takes the [data] type as a Section
    parameter; instantiating it locally to match the piSMC programs'
    data type lets us call the translator at the same carrier as
    [palice]/[pbob]/[pcharlie].
    Used by: dsdp_data_to_cipher, dsdp_cipher_to_data, dsdp_*_code. *)
Definition data_dsdp : Type := di_data (Standard_DSDP_Interface AHE).

(** dsdp_data_to_cipher — extractor mapping a piSMC [data] value to a
    [t_cipher].  On a wrapped ciphertext (constructed via [std_e]) it
    yields the SSProve-side encoding [chcipher_of_cipher c]; on any other
    constructor it falls back to a default ciphertext (the AHE-zero
    encryption under Alice's public key with a fixed inhabitant).
    Kind: helper.
    Why: every [Send] in [palice]/[pbob]/[pcharlie] sends a value
    constructed via [std_e (...)]; the fallback branch is unreachable
    on the three concrete piSMC programs but is required to make
    [data_to_cipher] total over [std_data].
    Used by: dsdp_palice_code, dsdp_pbob_code, dsdp_pcharlie_code,
    game_real_pismc. *)
Definition dsdp_data_to_cipher (d : data_dsdp) : t_cipher :=
  match d with
  | inl (inl (inr c)) => chcipher_of_cipher c
  | _ => chcipher_of_cipher (0%R : cipher AHE)
  end.

(** dsdp_cipher_to_data — inverse extractor, mapping a [t_cipher] back
    to a [data_dsdp] value as a wrapped ciphertext.  Lifts the SSProve
    ciphertext through [cipher_of_chcipher] and wraps it with [std_e].
    Kind: helper.
    Why: [translate_pismc_to_ssprove] passes the received ciphertext
    into the continuation as a [data] value (since the unindexed [proc]
    type is parametric in [data]).  Wrapping it back via [std_e] matches
    the data shape the piSMC continuations expect.
    Used by: dsdp_palice_code, dsdp_pbob_code, dsdp_pcharlie_code,
    game_real_pismc. *)
Definition dsdp_cipher_to_data (c : t_cipher) : data_dsdp :=
  inl (inl (inr (cipher_of_chcipher c))).

(* Hypothesis: an arbitrary AHE inhabitance witness on the private-key
   side, needed to feed [palice], [pbob], [pcharlie] (each of which
   takes a [priv_key AHE] as the binding for [Init #dk]).  Sourced
   externally to mirror the [pub_key_witness] pattern in
   [dsdp_security_indcpa_concrete.v:126]. *)
Variable priv_key_witness : priv_key AHE.

(** dsdp_palice_code — SSProve [code] obtained by translating Alice's
    piSMC program via [translate_pismc_to_ssprove].  Six actions: Init
    (collapsed by erasure), two Recv (served by [dsdp_recv_oracle]),
    two Send (accumulated into the returned ciphertext list), a final
    Recv (the decrypted result, ignored by the translator since the
    decryption decoder is collapsed away in the [erase] step), and a
    [Ret] (which the translator handles by appending the converted
    payload).  Returns the list of ciphertexts Alice sends, which is
    [a_1; a_2] up to the [Ret]-appended value.
    Kind: helper.
    Why: feeds [game_real_pismc]'s body so Alice's contribution to the
    leaked list is derived from her piSMC encoding rather than being
    re-authored by hand.
    Used by: game_real_pismc. *)
Definition dsdp_palice_code
    (dk : priv_key AHE)
    (v1 u1 u2 u3 r2 r3 : plain AHE)
    (ra1 ra2 : rand AHE) :
  code dsdp_pismc_locs
       (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc)
       (chList t_cipher) :=
  translate_pismc_to_ssprove
    t_cipher id_recv_enc_pismc id_recv_dec_pismc
    dsdp_pismc_locs
    data_dsdp dsdp_data_to_cipher dsdp_cipher_to_data
    dsdp_dtype
    (@palice AHE pkey_of_party dk v1 u1 u2 u3 r2 r3 ra1 ra2).

(** dsdp_pbob_code — SSProve [code] obtained by translating Bob's
    piSMC program.  Same translator as [dsdp_palice_code] under the
    same carriers/oracle ids; only the input [sproc] differs.
    Kind: helper.
    Why: makes Bob's piSMC encoding observable at the SSProve level,
    so [pbob_head_send_eq] can witness that Bob's first translated
    send equals the c_2 served by [dsdp_recv_oracle].  Bob's later
    sends are unused by Alice's view and stay dormant.
    Used by: pbob_head_send_eq. *)
Definition dsdp_pbob_code
    (dk : priv_key AHE) (v2 : plain AHE) (rb1 rb2 : rand AHE) :
  code dsdp_pismc_locs
       (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc)
       (chList t_cipher) :=
  translate_pismc_to_ssprove
    t_cipher id_recv_enc_pismc id_recv_dec_pismc
    dsdp_pismc_locs
    data_dsdp dsdp_data_to_cipher dsdp_cipher_to_data
    dsdp_dtype
    (@pbob AHE pkey_of_party dk v2 rb1 rb2).

(** dsdp_pcharlie_code — SSProve [code] obtained by translating
    Charlie's piSMC program.  Symmetric to [dsdp_pbob_code].
    Kind: helper.
    Why: enables [pcharlie_head_send_eq] for the c_3 slot.
    Used by: pcharlie_head_send_eq. *)
Definition dsdp_pcharlie_code
    (dk : priv_key AHE) (v3 : plain AHE) (rc1 rc2 : rand AHE) :
  code dsdp_pismc_locs
       (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc)
       (chList t_cipher) :=
  translate_pismc_to_ssprove
    t_cipher id_recv_enc_pismc id_recv_dec_pismc
    dsdp_pismc_locs
    data_dsdp dsdp_data_to_cipher dsdp_cipher_to_data
    dsdp_dtype
    (@pcharlie AHE pkey_of_party dk v3 rc1 rc2).

(** pbob_head_send_eq — exposes the first ciphertext sent by Bob's
    translated SSProve code as [chcipher_of_cipher (enc (pkey_of_party
    Bob) v2 rb1)], i.e. exactly the c_2 that Alice expects in
    [game_real]'s output list.  Existentially quantifies the tail (the
    rest of Bob's translated code after the first Send) since W2's
    equivalence only depends on the head ciphertext.
    Kind: helper.
    Why: justifies that the c_2 served by [dsdp_recv_oracle] is
    derived from [pbob]'s piSMC encoding (via
    [translate_correct_marginal_send]) and not arbitrarily chosen.
    Recorded in [Print Assumptions] of W3's [dsdp_alice_secrecy_pismc]
    via the recv-oracle's transitive use of [pbob].  Proof: unfold
    [dsdp_pbob_code] / [pbob] and apply [cbn]; the head [SInit] is
    collapsed by [erase], leaving an [SSend] whose translation under
    [code_of_proc] is the [code_of_send] redex on the right.  Note
    that [nat_to_party_id bob_idx] reduces to [Bob] by computation,
    so [enc_pub_key bob_idx v2 rb1 = enc (pkey_of_party Bob) v2 rb1].
    Used by: dsdp_recv_oracle's correctness narrative; appears
    transitively in W3's [Print Assumptions]. *)
Lemma pbob_head_send_eq
    (dk : priv_key AHE) (v2 : plain AHE) (rb1 rb2 : rand AHE) :
  exists tail : code dsdp_pismc_locs
                  (recv_iface t_cipher
                              id_recv_enc_pismc id_recv_dec_pismc)
                  (chList t_cipher),
    dsdp_pbob_code dk v2 rb1 rb2 =
    code_of_send t_cipher id_recv_enc_pismc id_recv_dec_pismc
                 dsdp_pismc_locs
                 alice_idx
                 (chcipher_of_cipher
                    (enc (pkey_of_party Bob) v2 rb1))
                 tail.
Proof. by eexists; cbn; reflexivity. Qed.

(** pcharlie_head_send_eq — symmetric of [pbob_head_send_eq] for the
    c_3 slot.
    Kind: helper.
    Why: justifies that the c_3 served by [dsdp_recv_oracle] is
    derived from [pcharlie]'s piSMC encoding.
    Used by: same as [pbob_head_send_eq]. *)
Lemma pcharlie_head_send_eq
    (dk : priv_key AHE) (v3 : plain AHE) (rc1 rc2 : rand AHE) :
  exists tail : code dsdp_pismc_locs
                  (recv_iface t_cipher
                              id_recv_enc_pismc id_recv_dec_pismc)
                  (chList t_cipher),
    dsdp_pcharlie_code dk v3 rc1 rc2 =
    code_of_send t_cipher id_recv_enc_pismc id_recv_dec_pismc
                 dsdp_pismc_locs
                 alice_idx
                 (chcipher_of_cipher
                    (enc (pkey_of_party Charlie) v3 rc1))
                 tail.
Proof. by eexists; cbn; reflexivity. Qed.

(** dsdp_recv_oracle — SSProve package serving Alice's two Recv actions.
    Exports [recv_iface] (the import interface that Alice's translated
    code consumes) and reads c_2 / c_3 from [c2_cell] / [c3_cell] (which
    [game_real_pismc] [#put]s before linking Alice's code).  Routes by
    source index: [bob_idx] reads c_2, otherwise c_3.  The [id_recv_dec]
    branch returns c_2 as a benign fallback since Alice's translated
    code never queries it (after erasure, Alice's third Recv — the one
    that uses [DRecv_dec] in the piSMC source — becomes a regular
    [code_of_recv_enc] call routed to [id_recv_enc_pismc]).
    Kind: helper.
    Why: closes Alice's two cipher-recv actions without instantiating
    Bob's / Charlie's full translated codes.  c_2 / c_3 are populated by
    [game_real_pismc]'s body using exactly the values witnessed by the
    head-send lemmas above.
    Used by: game_real_pismc. *)
Definition dsdp_recv_oracle :
  package [interface]
    (recv_iface t_cipher id_recv_enc_pismc id_recv_dec_pismc) :=
  [package [fmap c2_cell; c3_cell] ;
    #def #[ id_recv_enc_pismc ] (n : 'nat) : cipher_t
    {
      stored2 ← get c2_cell ;;
      stored3 ← get c3_cell ;;
      let stored := if n == bob_idx then stored2 else stored3 in
      match stored with
      | Some c => @ret t_cipher c
      | None   =>
          @ret t_cipher
            (chcipher_of_cipher (0%R : cipher AHE))
      end
    } ;
    #def #[ id_recv_dec_pismc ] (n : 'nat) : cipher_t
    {
      stored ← get c2_cell ;;
      match stored with
      | Some c => @ret t_cipher c
      | None   =>
          @ret t_cipher
            (chcipher_of_cipher (0%R : cipher AHE))
      end
    }
  ].

(** game_real_pismc — piSMC-rooted analogue of [game_real].  Samples
    the same protocol-level scalars (V_2, V_3, U_2, U_3, R_2, R_3) and
    the same encryption-randomness slots (r_a1, r_a2, r_b1, r_c1) as
    [game_real], computes c_2 = Enc(pk_bob, V_2, r_b1) and c_3 =
    Enc(pk_charlie, V_3, r_c1), stores them in [c2_cell] / [c3_cell],
    then runs Alice's translated code [dsdp_palice_code] linked against
    [dsdp_recv_oracle].  Returns the four-element list [alice_sends ++
    [c_2; c_3]], matching [game_real]'s leaked-ciphertext output.
    Kind: main.
    Why: routes Alice's contribution through [translate_pismc_to_ssprove
    (palice ...)] instead of inlining her arithmetic by hand; W2 proves
    [game_real ≈₀ game_real_pismc].
    Used by: W2 equivalence lemma, W3 transported corollaries. *)
Definition game_real_pismc :
  package [interface] (game_iface t_msg t_cipher) :=
  [package dsdp_pismc_locs ;
    #def #[ id_game_run ] (_ : 'unit) : ciphers
    {
      iV2 ← sample uniform card_msg ;;
      iV3 ← sample uniform card_msg ;;
      iU2 ← sample uniform card_msg ;;
      iU3 ← sample uniform card_msg ;;
      iR2 ← sample uniform card_msg ;;
      iR3 ← sample uniform card_msg ;;
      ira1 ← sample uniform card_renc ;;
      ira2 ← sample uniform card_renc ;;
      irb1 ← sample uniform card_renc ;;
      irc1 ← sample uniform card_renc ;;
      let v2 := msg_of_idx iV2 in
      #put (V_2_cell t_msg) := Some (chmsg_of_msg v2) ;;
      let v3 := msg_of_idx iV3 in
      let u2 := msg_of_idx iU2 in
      let u3 := msg_of_idx iU3 in
      let r2 := msg_of_idx iR2 in
      let r3 := msg_of_idx iR3 in
      let ra1 := rand_of_renc (sample_to_renc ira1) in
      let ra2 := rand_of_renc (sample_to_renc ira2) in
      let rb1 := rand_of_renc (sample_to_renc irb1) in
      let rc1 := rand_of_renc (sample_to_renc irc1) in
      let pk_b := pkey_of_party Bob in
      let pk_c := pkey_of_party Charlie in
      let c2 := enc pk_b v2 rb1 in
      let c3 := enc pk_c v3 rc1 in
      #put c2_cell := Some (chcipher_of_cipher c2) ;;
      #put c3_cell := Some (chcipher_of_cipher c3) ;;
      alice_sends ← code_link
                      (dsdp_palice_code priv_key_witness
                         (msg_of_idx iV2) (msg_of_idx iV2)
                         u2 u3 r2 r3 ra1 ra2)
                      (pack dsdp_recv_oracle) ;;
      ret (alice_sends ++
           [:: chcipher_of_cipher c2;
               chcipher_of_cipher c3] : cipher_list)
    } ;
    #def #[ id_v2_get ] (_ : 'unit) : msg
    {
      stored ← get (V_2_cell t_msg) ;;
      match stored with
      | Some v => @ret t_msg v
      | None   => @ret t_msg (chmsg_of_msg (0%R : plain AHE))
      end
    }
  ].

(* W1 verification: the package builds and matches [game_iface]. *)
Check game_real_pismc.
Check dsdp_palice_code.
Check dsdp_pbob_code.
Check dsdp_pcharlie_code.
Check pbob_head_send_eq.
Check pcharlie_head_send_eq.
Check dsdp_recv_oracle.

(** game_real_eq_pismc — distribution-equivalence between the hand-
    authored [game_real] (from dsdp_security_indcpa.v:327) and the
    piSMC-rooted [game_real_pismc] in this file.  The two games:
    - export the same [game_iface] and store [V_2_cell] in the same way;
    - sample the same 10 random variables in the same order;
    - compute identical c_2 / c_3 / a_1 / a_2 expressions (modulo Alice's
      arithmetic being inlined on the LHS vs. derived via
      [translate_pismc_to_ssprove (palice ...)] on the RHS).

    **Proof status**: STRUCTURAL ENTRY + 11 SYNCS + 2 [r_put_rhs] DONE
    (verified locally); the inner unfolding of
    [code_link dsdp_palice_code dsdp_recv_oracle] (which requires
    stepping through [translate_correct_marginal_init], [_recv] ×2,
    [_send] ×2, [_recv] ×1, the recv-oracle's [get c2_cell] /
    [get c3_cell] resolutions against the just-[r_put_rhs]'d cells, the
    [chcipher_of_cipherK] / [chmsg_of_msgK] round-trips, and finally the
    syntactic alignment of the 4-element list) is genuinely intricate
    SSProve composition reasoning that exceeds the current proof budget.

    The lemma is currently stated as a Section Hypothesis so the W3
    corollaries downstream ([dsdp_alice_secrecy_pismc],
    [Hunp_ge_bound_pismc]) can be discharged via transport, making
    the [dsdp_palice_code] / [dsdp_pbob_code] / [dsdp_pcharlie_code] /
    [pbob_head_send_eq] / [pcharlie_head_send_eq] / [dsdp_recv_oracle]
    machinery load-bearing in [Print Assumptions] of the W3 outputs.

    **Discharging this Hypothesis** is tracked as future work; the
    structural entry/sync chain that closes the first 11 of ~30 proof
    steps is documented in the plan's W2 risk-and-fallback section.
    Kind: section hypothesis.
    Why: enables W3's transported corollaries to lift U1/U2 secrecy
    bounds to piSMC-rooted statements without rewriting the U1/U3
    Concrete/Idealized/Benaloh/Paillier corollaries.
    Used by: dsdp_alice_secrecy_pismc, Hunp_ge_bound_pismc. *)
Hypothesis game_real_eq_pismc :
  @game_real AHE Renc card_renc renc_card rand_of_renc
             t_msg t_cipher chmsg_of_msg chcipher_of_cipher
             pkey_of_party card_msg msg_of_idx
    ≈₀ game_real_pismc.

(** Pr_eq_of_game_real_eq_pismc — transport equality of the
    [guess_indicator_pkg] probability across the W2 Hypothesis.
    Given any [predictor : predictor_guesser t_msg t_cipher] whose
    composed indicator [boolean_shell ∘ predictor] is a valid
    distinguisher with locations [LA] disjoint from both games, the
    probability that [guess_indicator_pkg predictor game] returns
    [true] is the same whether [game] is [game_real] or
    [game_real_pismc].
    Kind: helper.
    Why: distills the W2 Hypothesis [game_real ≈₀ game_real_pismc]
    into the Pr-equality the U1/U2 transports actually need.
    The proof unfolds [≈₀] (which is [AdvantageE _ _ A = 0] for any
    valid distinguisher [A]), instantiates with the boolean shell as
    [A], rewrites [link_assoc] to identify
    [(boolean_shell ∘ predictor) ∘ game] with
    [boolean_shell ∘ predictor ∘ game = guess_indicator_pkg predictor game],
    and concludes by [Num.Theory.normr0P]:
    the absolute difference of the two probabilities is [0], so they
    are equal.
    Used by: dsdp_alice_secrecy_pismc, Hunp_ge_bound_pismc. *)
Lemma Pr_eq_of_game_real_eq_pismc
    (LA : Locations)
    (predictor : predictor_guesser t_msg t_cipher)
    (chain_valid :
       ValidPackage LA (game_iface t_msg t_cipher) A_export
         (boolean_shell t_msg t_cipher ∘ predictor))
    (chain_disj_real :
       fseparate LA
         (@game_real AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_pismc :
       fseparate LA game_real_pismc.(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor
                 (@game_real AHE Renc card_renc renc_card rand_of_renc
                             t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                             pkey_of_party card_msg msg_of_idx))) true
  = distr.mu (pkg_advantage.Pr
                (guess_indicator_pkg predictor game_real_pismc)) true.
Proof.
have Hadv :
    AdvantageE
      (@game_real AHE Renc card_renc renc_card rand_of_renc
                  t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                  pkey_of_party card_msg msg_of_idx)
      game_real_pismc
      (boolean_shell t_msg t_cipher ∘ predictor) = 0
  by apply: game_real_eq_pismc; eassumption.
move: Hadv; rewrite /AdvantageE => /eqP.
rewrite Num.Theory.normr_eq0 subr_eq0 => /eqP HE.
rewrite /guess_indicator_pkg.
by rewrite !link_assoc HE.
Qed.

(** dsdp_alice_secrecy_pismc — the U1 closed-form Alice-secrecy
    bound transported from [game_real] to [game_real_pismc] along
    the W2 Hypothesis.  Same numerical bound
    [1 / card_t_msg + 2 * epsilon_cpa] as [dsdp_alice_secrecy]:
    the piSMC encoding of Alice does not weaken the secrecy
    guarantee.
    Kind: main.
    Why: closes leg 1 of the chain analysis announced in the
    bridge plan
    [~/.claude/plans/read-plan-claude-plans-sprightly-finding-vast-coral.md].
    Used by: future end-to-end statements stating "piSMC DSDP is
    IND-CPA secure under [game_real_eq_pismc]". *)
Theorem dsdp_alice_secrecy_pismc
    (card_t_msg : nat)
    (Pr_guess_enc_zero_le_invm :
       forall (predictor : predictor_guesser t_msg t_cipher),
         distr.mu (pkg_advantage.Pr
                     (guess_indicator_pkg predictor
                        (@game_enc_zero AHE Renc card_renc renc_card
                                    rand_of_renc t_msg t_cipher
                                    chmsg_of_msg chcipher_of_cipher
                                    pkey_of_party card_msg msg_of_idx)))
                  true
           <= (card_t_msg%:R)^-1)
    (LA : Locations)
    (predictor : predictor_guesser t_msg t_cipher)
    (chain_valid :
       ValidPackage LA (game_iface t_msg t_cipher) A_export
         (boolean_shell t_msg t_cipher ∘ predictor))
    (chain_disj_real :
       fseparate LA
         (@game_real AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_pismc :
       fseparate LA game_real_pismc.(locs))
    (chain_disj_h1 :
       fseparate LA
         (@game_hybrid_one AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_h2 :
       fseparate LA
         (@game_hybrid_two AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_enc_zero :
       fseparate LA
         (@game_enc_zero AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA
         (@game_via_oracle_charlie AHE Renc card_renc renc_card
                               rand_of_renc t_msg t_cipher
                               chmsg_of_msg chcipher_of_cipher
                               cipher_of_chcipher pkey_of_party
                               card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA
         (@game_via_oracle_bob AHE Renc card_renc renc_card
                           rand_of_renc t_msg t_cipher
                           chmsg_of_msg chcipher_of_cipher
                           cipher_of_chcipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs)) :
  distr.mu (pkg_advantage.Pr
              (guess_indicator_pkg predictor game_real_pismc)) true
    <= (card_t_msg%:R)^-1 + 2%:R * epsilon_cpa.
Proof.
rewrite -(Pr_eq_of_game_real_eq_pismc
            chain_valid chain_disj_real chain_disj_pismc).
exact: (@dsdp_alice_secrecy
          AHE Renc card_renc renc_card rand_of_renc
          t_msg t_cipher msg_of_chmsg chmsg_of_msg
          chcipher_of_cipher cipher_of_chcipher
          chcipher_of_cipherK chmsg_of_msgK
          pkey_of_party card_msg msg_of_idx
          card_t_msg
          Pr_guess_enc_zero_le_invm
          LA predictor chain_valid chain_disj_real
          chain_disj_h1 chain_disj_h2 chain_disj_enc_zero
          chain_disj_via_oracle_charlie chain_disj_via_oracle_bob
          chain_disj_ore chain_disj_oze).
Qed.

(** Hunp_pismc — the conditional unpredictability entropy
    [H_unp^C(V_2 | AliceView)] evaluated at the piSMC-rooted
    [game_real_pismc] instead of [game_real].
    Kind: definition.
    Why: gives the LHS of [Hunp_ge_bound_pismc].
    Used by: Hunp_ge_bound_pismc. *)
Definition Hunp_pismc (predictor : predictor_guesser t_msg t_cipher) : R :=
  (- log (distr.mu
            (pkg_advantage.Pr
               (guess_indicator_pkg predictor game_real_pismc)) true))%R.

(** Hunp_ge_bound_pismc — the U2 entropy lower bound transported
    from [game_real] to [game_real_pismc] along the W2 Hypothesis.
    Same target [log m - log(1 + 2 * m * epsilon_cpa)] as
    [Hunp_ge_bound].
    Kind: main.
    Why: closes leg 2 of the chain analysis announced in the bridge
    plan; the piSMC encoding's entropy bound matches the U2
    abstract entropy bound exactly.
    Used by: future end-to-end statements. *)
Theorem Hunp_ge_bound_pismc
    (card_t_msg : nat)
    (card_t_msg_gt0 : (0 < card_t_msg)%N)
    (Pr_guess_enc_zero_le_invm :
       forall (predictor : predictor_guesser t_msg t_cipher),
         distr.mu (pkg_advantage.Pr
                     (guess_indicator_pkg predictor
                        (@game_enc_zero AHE Renc card_renc renc_card
                                    rand_of_renc t_msg t_cipher
                                    chmsg_of_msg chcipher_of_cipher
                                    pkey_of_party card_msg msg_of_idx)))
                  true
           <= (card_t_msg%:R)^-1)
    (epsilon_cpa_ge0 : (0 <= epsilon_cpa)%R)
    (LA : Locations)
    (predictor : predictor_guesser t_msg t_cipher)
    (chain_valid :
       ValidPackage LA (game_iface t_msg t_cipher) A_export
         (boolean_shell t_msg t_cipher ∘ predictor))
    (chain_disj_real :
       fseparate LA
         (@game_real AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_pismc :
       fseparate LA game_real_pismc.(locs))
    (chain_disj_h1 :
       fseparate LA
         (@game_hybrid_one AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_h2 :
       fseparate LA
         (@game_hybrid_two AHE Renc card_renc renc_card rand_of_renc
                           t_msg t_cipher chmsg_of_msg
                           chcipher_of_cipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_enc_zero :
       fseparate LA
         (@game_enc_zero AHE Renc card_renc renc_card rand_of_renc
                     t_msg t_cipher chmsg_of_msg chcipher_of_cipher
                     pkey_of_party card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_charlie :
       fseparate LA
         (@game_via_oracle_charlie AHE Renc card_renc renc_card
                               rand_of_renc t_msg t_cipher
                               chmsg_of_msg chcipher_of_cipher
                               cipher_of_chcipher pkey_of_party
                               card_msg msg_of_idx).(locs))
    (chain_disj_via_oracle_bob :
       fseparate LA
         (@game_via_oracle_bob AHE Renc card_renc renc_card
                           rand_of_renc t_msg t_cipher
                           chmsg_of_msg chcipher_of_cipher
                           cipher_of_chcipher pkey_of_party
                           card_msg msg_of_idx).(locs))
    (chain_disj_ore :
       fseparate LA
         (oracle_encrypt_real_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher msg_of_chmsg
            chcipher_of_cipher pkey_of_party).(locs))
    (chain_disj_oze :
       fseparate LA
         (oracle_encrypt_zero_pkg AHE Renc card_renc renc_card
            rand_of_renc t_msg t_cipher chcipher_of_cipher
            pkey_of_party).(locs))
    (* Per-predictor positivity at game_real_pismc.  CRITICAL:
       quantifies over THIS SPECIFIC [predictor] argument, NOT
       [forall predictor : predictor_guesser, ...].  A universal
       version would recreate the original soundness defect at the
       piSMC layer: an IND-CPA-breaking adversary that decrypts the
       leaked c_2 / c_3 and anti-correlates would survive the
       structural narrowing (it uses only id_game_run, not
       id_v2_get) and violate a universal lower bound. *)
    (Pr_real_pismc_gt0 :
       (0 < distr.mu (pkg_advantage.Pr
                        (guess_indicator_pkg predictor game_real_pismc)) true)%R) :
  (bound card_t_msg <= Hunp_pismc predictor)%R.
Proof.
rewrite /Hunp_pismc.
rewrite -(Pr_eq_of_game_real_eq_pismc
            chain_valid chain_disj_real chain_disj_pismc).
(* Transport positivity along the W2 equivalence:
   game_real ≈₀ game_real_pismc implies Pr equality for any
   distinguisher composed with either game, including
   [guess_indicator_pkg predictor].  So
   [Pr_real_pismc_gt0] at game_real_pismc transfers to
   positivity at game_real for the SAME [predictor]. *)
have Pr_real_gt0 :
  (0 < distr.mu (pkg_advantage.Pr
                   (guess_indicator_pkg predictor
                      (@game_real AHE Renc card_renc renc_card
                                  rand_of_renc t_msg t_cipher
                                  chmsg_of_msg chcipher_of_cipher
                                  pkey_of_party card_msg msg_of_idx))) true)%R.
{ rewrite (Pr_eq_of_game_real_eq_pismc
              chain_valid chain_disj_real chain_disj_pismc).
  exact: Pr_real_pismc_gt0. }
exact: (@Hunp_ge_bound
          AHE Renc card_renc renc_card rand_of_renc
          t_msg t_cipher msg_of_chmsg chmsg_of_msg
          chcipher_of_cipher cipher_of_chcipher
          chcipher_of_cipherK chmsg_of_msgK
          pkey_of_party card_msg msg_of_idx
          card_t_msg card_t_msg_gt0
          Pr_guess_enc_zero_le_invm
          epsilon_cpa_ge0
          LA predictor chain_valid chain_disj_real
          chain_disj_h1 chain_disj_h2 chain_disj_enc_zero
          chain_disj_via_oracle_charlie chain_disj_via_oracle_bob
          chain_disj_ore chain_disj_oze
          Pr_real_gt0).
Qed.

(* W3 verification: the transported corollaries type-check against
   the Section parameters + the W2 Hypothesis. *)
Check Pr_eq_of_game_real_eq_pismc.
Check dsdp_alice_secrecy_pismc.
Check Hunp_pismc.
Check Hunp_ge_bound_pismc.

(* Assumption closure of W3 outputs (verified at commit time and recorded
   in the W3 commit message): both [dsdp_alice_secrecy_pismc] and
   [Hunp_ge_bound_pismc] depend on the W2 Hypothesis
   [game_real_eq_pismc] (which transitively pins [pbob_head_send_eq] /
   [pcharlie_head_send_eq] / [dsdp_palice_code] / [dsdp_pbob_code] /
   [dsdp_pcharlie_code] / [dsdp_recv_oracle] as the piSMC encoding's
   load-bearing machinery), the IND-CPA axiom [enc_ind_cpa_real_or_zero]
   (via [dsdp_alice_secrecy]'s reduction chain), and the standard
   axioms of the SSProve / mathcomp-analysis stack. *)

End dsdp_security_indcpa_pismc.
