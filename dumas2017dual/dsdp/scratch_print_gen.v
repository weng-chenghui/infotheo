(* scratch_print_gen.v — prints the SSProve real-game body that the generation
   function [denote_run] produces for the DSDP corrupted-Alice view, with the
   crypto operations left abstract and concrete demo cardinalities
   (card_msg = 3, card_renc = 2) so the [n == card_msg] dispatch guards reduce.

   NOT a build target; do not add to _CoqProject and do not Require Import it.

   How to render the generated program readably via the Rocq MCP.  The
   shorthand notations below are section-local (they name the section
   variables), so they only render INSIDE [Section Demo] — inspect there:
     1. rocq_start(file=this, theorem="gen_printedE")
     2. rocq_step_multi(from_state=<id>, tactics=[
          "rewrite /gen_printed /gen; simpl; \
           cbv [de_rand_nth de_rand de_val push_rand push_val empty_denv]; simpl."])
        Both sides display as the readable program: the LHS is the hand-written
        [gen_printed], the RHS is the generator call [gen] reduced to the same
        normal form.  [gen_printedE] proves they are equal.

   Notes on reductions tried:
     - cbv at definition time / "Eval cbv in gen" blows up (unfolds the
       distribution + monad machinery); avoid.
     - selective "cbv [gen denote_run ...]" without the nat-equality constants
       trifurcates every GC_sample on the unresolved [n == card_msg] guard
       (exponential); avoid.
     - "simpl" resolves the guards and keeps the monad folded but leaves the
       denv lookups [de_rand_nth (push_… )] in the two combine terms; the extra
       "cbv [de_rand_nth …]; simpl" above finishes those. *)

From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
Set Warnings "notation-overridden,ambiguous-paths".
From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba bayes.
Require Import spp_entropy.
Require Import homomorphic_encryption indcpa_ror.
Require Import dsdp_program dsdp_entropy dsdp_pismc.
Require Import smc.ssprove_ext_lossless.
Require Import dsdp_game_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Section Demo.
Variable AHE : AHEncType.
Variable Renc : finType.
Hypothesis renc_card : #|Renc| = 2.
Variable rand_of_renc : Renc -> rand AHE.
Variables t_msg t_cipher : choice_type.
Variable chmsg_of_msg : plain AHE -> t_msg.
Variable chcipher_of_cipher : cipher AHE -> t_cipher.
Variable pkey_of_party : party_id -> pub_key AHE.
Variable msg_of_idx : 'I_3 -> plain AHE.
Variable rand0 : rand AHE.

(* ---- readable shorthands for the printed program -------------------------- *)
(* [*h] [^h] reuse the piSMC homomorphic spellings (reserved at level 40 by
   dsdp_program.v:36-37).  [E<p,s>(| m |)] is the encryption, parameterised by
   the recipient party [p] and the randomness sample [s] in the angle brackets,
   over the plaintext payload [m] in the (| |):
     E<p,s>(| m |) = enc (pkey_of_party p) m (rand_of_renc (sample_to_renc renc_card s))
   Other shorthands:
     m[ i ]   = msg_of_idx i           (plaintext drawn at sample i)
     <[ c ]>  = chcipher_of_cipher c   (cipher placed on the wire)
   [^h] raises a CIPHERTEXT to a plaintext exponent, so in a combine term the
   exponent sits OUTSIDE the payload:  E<Bob,s>(| m[x] |) ^h m[x1]  is the
   ciphertext Enc(v2) raised to u2, not an encryption of the (ill-typed)
   plaintext [m[x] ^h m[x1]].  [*h]/[^h] share the reserved non-associative
   level 40, so a power inside a product needs parens: (c ^h u) *h e. *)
Set Warnings "-notation-overridden".
Notation "u *h w" := (Emul u w) (at level 40).
Notation "u ^h w" := (Epow u w) (at level 40).
Notation "'E<' p ',' s '>(|' m '|)'" :=
  (enc (pkey_of_party p) m (rand_of_renc (sample_to_renc renc_card s)))
  (at level 10, p constr at level 0, s constr at level 0, m constr at level 200,
   format "'E<' p ',' s '>(|'  m  '|)'").
Notation "'m[' i ']'" := (msg_of_idx i) (at level 0).
Notation "'<[' c ']>'" := (chcipher_of_cipher c) (at level 0).
Set Warnings "notation-overridden".

(* gen — the SSProve real game the generator emits for the corrupted-Alice DSDP
   view: the back end's [denote_run] run on the real endpoint of the [gc_dsdp]
   fixture, at the demo cardinalities, with the crypto operations abstract. *)
Definition gen :=
  denote_run renc_card rand_of_renc chmsg_of_msg chcipher_of_cipher
    pkey_of_party msg_of_idx rand0 (empty_denv AHE) (all_real (gc_dsdp 2 3)).

(* gen_printed — the program spelled out by hand, transcribed verbatim from the
   reduced normal form of [gen] (the printing recipe in the header).  Binder
   names follow the printout: x..x4 = iV2 iV3 iU2 iU3 iR2 iR3; x5 x6 = ra1 ra2;
   ir_hop ir_hop0 = rb1 rc1 (the inline hop randomness). *)
Definition gen_printed : raw_code (cipher_list t_cipher) :=
  x  ← sample uniform 3 ;;
  x0 ← sample uniform 3 ;;
  x1 ← sample uniform 3 ;;
  x2 ← sample uniform 3 ;;
  x3 ← sample uniform 3 ;;
  x4 ← sample uniform 3 ;;
  x5 ← sample uniform 2 ;;
  x6 ← sample uniform 2 ;;
  #put V_2_cell t_msg := Some (chmsg_of_msg m[x]) ;;
  ir_hop  ← sample uniform 2 ;;
  ir_hop0 ← sample uniform 2 ;;
  ret ([:: <[ (E<Bob, ir_hop>(| m[x] |) ^h m[x1]) *h E<Bob, x5>(| m[x3] |) ]>
  ; <[ (E<Charlie, ir_hop0>(| m[x0] |) ^h m[x2]) *h E<Charlie, x6>(| m[x4] |) ]>
  ; <[ E<Bob, ir_hop>(| m[x] |) ]>
  ; <[ E<Charlie, ir_hop0>(| m[x0] |) ]>
  ] : cipher_list t_cipher).

(* gen_printedE — the hand-transcribed [gen_printed] is exactly the body the
   generator emits for the corrupted-Alice DSDP real game, so the readable
   transcription kept in this scratch file is trustworthy.  Holds by kernel
   computation. *)
Lemma gen_printedE : gen_printed = gen.
Proof. by []. Qed.

End Demo.
