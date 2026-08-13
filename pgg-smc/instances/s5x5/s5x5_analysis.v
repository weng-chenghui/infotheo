(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5x5_analysis: the typed facade of the ten-seat S_5 x S_5 instance         *)
(*                                                                            *)
(* The facade presents the S_5 x S_5 analysis cone through one alias per      *)
(* public value, inside Module S5x5Analysis, in seven fixed source sections:  *)
(*                                                                            *)
(*   1 Program   2 Execution   3 Observers   4 Models                         *)
(*   5 Correctness   6 Security   7 Transfer                                  *)
(*                                                                            *)
(* The instance carries two analysis paths over one profile. The              *)
(* deterministic path deals a position in 'I_10 and proves recovery; the      *)
(* randomized path deals two additive sharings, one per pile, and carries the *)
(* executed secrecy results about the pile pair. Aliases naming a plug or a   *)
(* model of the randomized path are prefixed rand_, those of the finite-word  *)
(* endpoint model word_, and the prefix exec_ marks a result read at an       *)
(* executed observer.                                                         *)
(*                                                                            *)
(* Every observer of the randomized path that reads pile data is pile-tagged: *)
(* pile1_ and pile2_ aliases carry the five-element party index and the pile  *)
(* carriers 'Z_5 and {ffun 'I_5 -> 'Z_5}, and joint_ aliases carry their      *)
(* pair. No alias flattens the two piles into one ten-seat coalition.         *)
(*                                                                            *)
(* The facade contract:                                                       *)
(*                                                                            *)
(*   - every declaration is a Definition whose body is the landed constant,   *)
(*     so the alias carries the landed type verbatim;                         *)
(*   - no proof body appears in this file, and no statement, observer         *)
(*     carrier, assumption or numeric constant is restated;                   *)
(*   - the module supplies the namespace, so the aliases drop the s5x5_       *)
(*     prefix of their targets;                                               *)
(*   - the type vocabulary the alias types are written in is Require          *)
(*     Export'ed, and the S_5 x S_5 instance cone is Require Import'ed only.  *)
(*                                                                            *)
(* Section 6 states exact secrecy results of the randomized path only. The    *)
(* endpoint marginal bounds of the finite-word model are a separate sub-block *)
(* after section 6: they bound one position's endpoint distribution, they are *)
(* conditional on s5_rayleigh_Q2_R, and they are not privacy statements.      *)
(******************************************************************************)

From HB Require Import structures.

(* Exported type vocabulary: every constant an alias type is written in. *)
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Export div fintype tuple finfun finset fingroup perm.
From mathcomp Require Export morphism action bigop order ssrnum ssralg.
From mathcomp Require Export boolp reals zmodp matrix.
From infotheo Require Export realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Export pgg_interface pgg_monodromy_profile.
From pgg_smc Require Export pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Export pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Export pgg_collusion_bound pgg_randomized_sharing.
From pgg_smc Require Export pgg_canonical_sharing.
From pgg_smc Require Export pgg_analysis_status.

(* Imported instance cone: loaded, never re-exported. *)
Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run.
From pgg_smc Require Import pgg_leakage_witness pgg_sharing_mechanism.
From pgg_smc Require Import pgg_leakage_product pgg_trace_secrecy.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import product_threshold.
From pgg_smc Require Import pgg_s5x5 s5x5_pile rigidity_s5x5_instance.
From pgg_smc Require Import s5x5_profile s5x5_run s5x5_secrecy s5x5_trace.
From pgg_smc Require Import s5_mixing s5x5_mixing.
From pgg_smc Require Import s5_exec s5x5_exec s5x5_models.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Module S5x5Analysis.

(******************************************************************************)
(* ===== 1. Program ===== *)
(******************************************************************************)

(** profile — the probability-independent ten-seat two-pile program profile.
    @intent: alias of s5x5_profile. *)
Definition profile := s5x5_profile.

(** profile_k — the profile's privacy threshold is five: inside one pile,
    fewer than five shares cannot distinguish two secrets.
    @intent: alias of profile_k_s5x5. *)
Definition profile_k := profile_k_s5x5.

(******************************************************************************)
(* ===== 2. Execution ===== *)
(*                                                                            *)
(* Two plugs over the one profile. Their run arguments differ: the dealt      *)
(* position 'I_10 for the deterministic plug and the product sampler tape     *)
(* 'rV['Z_5]_5 * 'rV['Z_5]_5 for the randomized plug. Their process lists are *)
(* not claimed equal.                                                         *)
(******************************************************************************)

(** exec_plug — the deterministic execution plug over that profile.
    @intent: alias of s5x5_exec_plug. *)
Definition exec_plug := s5x5_exec_plug.

(** rand_exec_plug — the randomized execution plug over that profile.
    @intent: alias of s5x5_rand_exec_plug. *)
Definition rand_exec_plug := s5x5_rand_exec_plug.

(******************************************************************************)
(* ===== 3. Observers ===== *)
(*                                                                            *)
(* Carriers, kept distinct: a message list for the raw traces, the dealt      *)
(* position 'I_10 for one seat's endpoint and for one seat's read trace       *)
(* content, a finfun of positions for a ten-seat coalition's endpoints, a     *)
(* sequence of positions for the verifier's endpoint list, and the two pile   *)
(* carriers 'Z_5 and {ffun 'I_5 -> 'Z_5} for the pile-tagged readers. The raw *)
(* trace extractors carry a message list and are navigation only: they are    *)
(* not finite random variables. Only the randomized path carries finite       *)
(* readers, that being the path the secrecy results are stated on.            *)
(******************************************************************************)

(** seat_endpoint — one seat's deterministic executed endpoint, a dealt
    position.
    @intent: exec_seat_endpoint specialized at s5x5_exec_plug. *)
Definition seat_endpoint := @exec_seat_endpoint s5x5_profile s5x5_exec_plug.

(** coalition_endpoints — a coalition's deterministic executed endpoints, a
    finfun of dealt positions indexed by seats.
    @intent: exec_coalition_endpoints specialized at s5x5_exec_plug. *)
Definition coalition_endpoints :=
  @exec_coalition_endpoints s5x5_profile s5x5_exec_plug.

(** verifier_trace — the verifier's raw executed trace on the deterministic
    plug, a message list.
    @intent: exec_verifier_trace specialized at s5x5_exec_plug. *)
Definition verifier_trace := @exec_verifier_trace s5x5_profile s5x5_exec_plug.

(** verifier_endpoints — the deterministic executed endpoint list of the run,
    the dealt positions the verifier reads.
    @intent: exec_endpoints specialized at s5x5_exec_plug. *)
Definition verifier_endpoints := @exec_endpoints s5x5_profile s5x5_exec_plug.

(** player_raw_trace — one seat's raw executed trace on the deterministic
    plug, a message list.
    @intent: exec_participant_trace specialized at s5x5_exec_plug. *)
Definition player_raw_trace :=
  @exec_participant_trace s5x5_profile s5x5_exec_plug.

(** observed — the deterministic observed execution: the run, its static
    observation and the value it recovers.
    @intent: alias of s5x5_observed. *)
Definition observed := s5x5_observed.

(** rand_seat_endpoint — one seat's randomized executed endpoint, a two-pile
    layout entry read as a position.
    @intent: exec_seat_endpoint specialized at s5x5_rand_exec_plug. *)
Definition rand_seat_endpoint :=
  @exec_seat_endpoint s5x5_profile s5x5_rand_exec_plug.

(** rand_coalition_endpoints — a ten-seat coalition's randomized executed
    endpoints, a finfun of layout entries indexed by seats.
    @intent: exec_coalition_endpoints specialized at s5x5_rand_exec_plug. *)
Definition rand_coalition_endpoints :=
  @exec_coalition_endpoints s5x5_profile s5x5_rand_exec_plug.

(** rand_content_trace — seat j's randomized executed trace content, a random
    variable on the product tape distribution with carrier 'I_10.
    @intent: alias of s5x5_sample_content_trace, the executed finite
    reader. *)
Definition rand_content_trace := @s5x5_sample_content_trace.

(** rand_verifier_trace — the verifier's raw executed trace on the randomized
    plug, a message list.
    @intent: exec_verifier_trace specialized at s5x5_rand_exec_plug. *)
Definition rand_verifier_trace :=
  @exec_verifier_trace s5x5_profile s5x5_rand_exec_plug.

(** rand_verifier_endpoints — the randomized executed endpoint list of the
    run, the layout entries the verifier reads.
    @intent: exec_endpoints specialized at s5x5_rand_exec_plug. *)
Definition rand_verifier_endpoints :=
  @exec_endpoints s5x5_profile s5x5_rand_exec_plug.

(** rand_player_raw_trace — one seat's raw executed trace on the randomized
    plug, a message list.
    @intent: exec_participant_trace specialized at s5x5_rand_exec_plug. *)
Definition rand_player_raw_trace :=
  @exec_participant_trace s5x5_profile s5x5_rand_exec_plug.

(** rand_observed — the randomized observed execution.
    @intent: alias of s5x5_rand_observed. *)
Definition rand_observed := s5x5_rand_observed.

(** pile1_seats — the ten-seat image of a first-pile coalition.
    @intent: alias of s5x5_p1_seats. *)
Definition pile1_seats := s5x5_p1_seats.

(** pile2_seats — the ten-seat image of a second-pile coalition.
    @intent: alias of s5x5_p2_seats. *)
Definition pile2_seats := s5x5_p2_seats.

(** pile1_seat_view — one first-pile party's executed share, a random variable
    on the product tape distribution with carrier 'Z_5.
    @intent: alias of s5x5_p1_seat_view. *)
Definition pile1_seat_view := @s5x5_p1_seat_view.

(** pile2_seat_view — one second-pile party's executed share, a random
    variable on the product tape distribution with carrier 'Z_5.
    @intent: alias of s5x5_p2_seat_view. *)
Definition pile2_seat_view := @s5x5_p2_seat_view.

(** pile1_coalition_view — a first-pile coalition's executed shares, a random
    variable with carrier {ffun 'I_5 -> 'Z_5} indexed by first-pile parties.
    @intent: alias of s5x5_p1_view. *)
Definition pile1_coalition_view := @s5x5_p1_view.

(** pile2_coalition_view — a second-pile coalition's executed shares, a random
    variable with carrier {ffun 'I_5 -> 'Z_5} indexed by second-pile parties.
    @intent: alias of s5x5_p2_view. *)
Definition pile2_coalition_view := @s5x5_p2_view.

(** joint_view — the pair of the two executed pile coalition readers, the two
    pile memberships kept separate.
    @intent: alias of s5x5_joint_view. *)
Definition joint_view := @s5x5_joint_view.

(******************************************************************************)
(* ===== 4. Models ===== *)
(*                                                                            *)
(* Each model is followed by the equation identifying its cut distribution,   *)
(* so that a statement about a named distribution can be attached to a named  *)
(* executed observer. The two sample spaces differ by definition and no       *)
(* theorem relates their base distributions.                                  *)
(******************************************************************************)

(** rand_sample — the randomized product exact-secrecy model at the product
    uniform iid tape distribution and the identity cut.
    @intent: alias of s5x5_rand_sample. *)
Definition rand_sample := @s5x5_rand_sample.

(** word_sample — the finite-word endpoint model at an arbitrary secret prior
    and word length.
    @intent: alias of s5x5_word_sample. *)
Definition word_sample := @s5x5_word_sample.

(** rand_family — the randomized product-tape model as a unit-indexed typed
    family.
    @intent: alias of s5x5_rand_family. *)
Definition rand_family := s5x5_rand_family.

(** word_family — the finite-word model family, indexed by a secret prior
    and a word length; shared by the endpoint and limitation rows.
    @intent: alias of s5x5_word_family. *)
Definition word_family := s5x5_word_family.

(** rand_cut_distE — the randomized model's cut distribution is the point
    distribution at the identity.
    @intent: alias of s5x5_rand_cut_distE. *)
Definition rand_cut_distE := @s5x5_rand_cut_distE.

(** word_cut_distE — the finite-word model's cut distribution is the
    word-induced shuffle distribution.
    @intent: alias of s5x5_word_cut_distE. *)
Definition word_cut_distE := @s5x5_word_cut_distE.

(******************************************************************************)
(* ===== 5. Correctness ===== *)
(*                                                                            *)
(* Six statements over two plugs, and one caveat. exec_correct, exec_recovers *)
(* and observed_recovers belong to the deterministic plug and recover the     *)
(* dealt position; rand_correct, rand_recovers and rand_observed_recovers     *)
(* belong to the randomized plug and recover the 'I_10 image of the two pile  *)
(* secrets under combine_secret. That image is not the pile pair:             *)
(* combine_not_injectiveE exhibits two distinct pile pairs with the same      *)
(* image, which is why the secrecy results of section 6 are stated about the  *)
(* pile pair and read at the executed observers, not at this recovered value. *)
(******************************************************************************)

(** exec_correct — deterministic termination, endpoint count and recovery
    together.
    @intent: alias of s5x5_exec_correct. *)
Definition exec_correct := @s5x5_exec_correct.

(** exec_recovers — the deterministic executed run decodes to the dealt
    position.
    @intent: alias of s5x5_exec_recovers. *)
Definition exec_recovers := @s5x5_exec_recovers.

(** observed_recovers — the deterministic observed run decodes to the dealt
    position.
    @intent: alias of s5x5_observed_recovers. *)
Definition observed_recovers := @s5x5_observed_recovers.

(** rand_correct — randomized termination, endpoint count and recovery
    together.
    @intent: alias of s5x5_rand_correct. *)
Definition rand_correct := @s5x5_rand_correct.

(** rand_recovers — the randomized executed run decodes to the combined pile
    secrets.
    @intent: alias of s5x5_rand_exec_recovers. *)
Definition rand_recovers := @s5x5_rand_exec_recovers.

(** rand_observed_recovers — the randomized observed run decodes to the
    combined pile secrets.
    @intent: alias of s5x5_rand_observed_recovers. *)
Definition rand_observed_recovers := @s5x5_rand_observed_recovers.

(** combine_not_injectiveE — two distinct pile pairs have the same combined
    secret.
    @intent: alias of s5x5_combine_not_injectiveE. *)
Definition combine_not_injectiveE := s5x5_combine_not_injectiveE.

(******************************************************************************)
(* ===== 6. Security ===== *)
(*                                                                            *)
(* Four aliases, all stating exact privacy of the randomized path at the      *)
(* executed observers of rand_sample and all about the pile pair             *)
(* JointSecret. The first is trace secrecy in conditional entropy form for    *)
(* one seat's trace content. The next two are exact privacy in mutual         *)
(* information and conditional entropy form for one sub-threshold pile        *)
(* coalition, one per pile. The fourth is the same for two sub-threshold pile *)
(* coalitions read together, under the two per-pile cardinality bounds; it is *)
(* the joint statement and is not inferred from the two per-pile ones. None   *)
(* is an approximate-privacy statement, and the deterministic path carries no *)
(* secrecy result.                                                            *)
(******************************************************************************)

(** exec_trace_secrecy — trace secrecy in conditional entropy form: one seat's
    executed trace content leaves the pile pair's conditional entropy equal to
    its entropy.
    @intent: alias of s5x5_exec_trace_secrecy. *)
Definition exec_trace_secrecy := @s5x5_exec_trace_secrecy.

(** exec_p1_secrecy — exact privacy in mutual information and conditional
    entropy form: a first-pile coalition of fewer than five parties has zero
    mutual information with the pile pair.
    @intent: alias of s5x5_exec_p1_secrecy. *)
Definition exec_p1_secrecy := @s5x5_exec_p1_secrecy.

(** exec_p2_secrecy — exact privacy in mutual information and conditional
    entropy form: a second-pile coalition of fewer than five parties has zero
    mutual information with the pile pair.
    @intent: alias of s5x5_exec_p2_secrecy. *)
Definition exec_p2_secrecy := @s5x5_exec_p2_secrecy.

(** exec_joint_secrecy — exact privacy in mutual information and conditional
    entropy form for the two pile coalitions read together, under the two
    per-pile cardinality bounds.
    @intent: alias of s5x5_exec_joint_secrecy. *)
Definition exec_joint_secrecy := @s5x5_exec_joint_secrecy.

(******************************************************************************)
(* ===== bound (endpoint marginal, not security) ===== *)
(*                                                                            *)
(* The three aliases below are endpoint marginal mixing bounds: each bounds   *)
(* the distance from a reference distribution of ONE position's endpoint      *)
(* distribution after a word of L cuts, in the repository's full-L1           *)
(* convention. Each quantifies over one position, mentions no coalition view  *)
(* and no second secret, and is conditional on the trusted analytical         *)
(* certificate s5_rayleigh_Q2_R. They are neither exact nor approximate       *)
(* privacy, and are recorded as endpoint marginal bounds in the analysis      *)
(* manifest. The two pile bounds are taken against the uniform distribution   *)
(* on their own pile and vanish with L; the seat bound is taken against       *)
(* global uniform on ten seats and does not vanish, its leading summand 1     *)
(* being the distance between a pile-uniform distribution and global uniform. *)
(******************************************************************************)

(** word_pile1_bound — endpoint marginal mixing inside the first pile at word
    length L, conditional on s5_rayleigh_Q2_R.
    @intent: alias of s5x5_word_pile1_bound. *)
Definition word_pile1_bound := @s5x5_word_pile1_bound.

(** word_pile2_bound — endpoint marginal mixing inside the second pile at word
    length L, conditional on s5_rayleigh_Q2_R.
    @intent: alias of s5x5_word_pile2_bound. *)
Definition word_pile2_bound := @s5x5_word_pile2_bound.

(** word_seat_bound — the one-seat endpoint marginal bound against global
    uniform on ten seats at word length L, conditional on s5_rayleigh_Q2_R.
    @intent: alias of s5x5_word_seat_bound. *)
Definition word_seat_bound := @s5x5_word_seat_bound.

(******************************************************************************)
(* ===== 7. Transfer ===== *)
(*                                                                            *)
(* One status per analysis path. The deterministic path compares no model     *)
(* with an idealized one. The randomized path carries its executed observers  *)
(* back to the landed static results by the reader equalities below, and      *)
(* compares no idealized model. The two finite-word endpoint paths compare no *)
(* model either: the landed pile spectral theorems bound pushforwards on the  *)
(* carrier 'I_10, while the generic transfer theorem needs a bound on the     *)
(* carrier {perm 'I_10}, which is the premise word_missing_premise names and  *)
(* which the repository does not supply. The two global-uniform limitation    *)
(* paths do carry a theorem transporting an obstruction to their own          *)
(* observer: the exact distance one between a pile-uniform distribution and   *)
(* global uniform combined with the conditional endpoint upper bound by the   *)
(* reverse triangle inequality, positive from word length seventeen on.       *)
(******************************************************************************)

(** det_transfer_status — the deterministic path's transfer status.
    @intent: NoModelComparison, the path carrying recovery only. *)
Definition det_transfer_status : TransferStatus := NoModelComparison.

(** rand_transfer_status — the randomized path's transfer status.
    @intent: StaticExecutedOnly, the path carrying its landed static secrecy
    results to its executed observers and no ideal-to-finite theorem. *)
Definition rand_transfer_status : TransferStatus := StaticExecutedOnly.

(** rand_content_traceE — the executed content reader is the landed
    player-trace random variable, one of the equalities witnessing
    rand_transfer_status.
    @intent: alias of s5x5_sample_content_traceE. *)
Definition rand_content_traceE := @s5x5_sample_content_traceE.

(** rand_pile1_seat_viewE — the executed first-pile seat reader is that
    party's first-pile share, one of the equalities witnessing
    rand_transfer_status.
    @intent: alias of s5x5_p1_seat_viewE. *)
Definition rand_pile1_seat_viewE := @s5x5_p1_seat_viewE.

(** rand_pile2_seat_viewE — the executed second-pile seat reader is that
    party's second-pile share, one of the equalities witnessing
    rand_transfer_status.
    @intent: alias of s5x5_p2_seat_viewE. *)
Definition rand_pile2_seat_viewE := @s5x5_p2_seat_viewE.

(** rand_pile1_viewE — the executed first-pile coalition reader is the first
    pile's randomized sharing view, one of the equalities witnessing
    rand_transfer_status.
    @intent: alias of s5x5_p1_viewE. *)
Definition rand_pile1_viewE := @s5x5_p1_viewE.

(** rand_pile2_viewE — the executed second-pile coalition reader is the second
    pile's randomized sharing view, one of the equalities witnessing
    rand_transfer_status.
    @intent: alias of s5x5_p2_viewE. *)
Definition rand_pile2_viewE := @s5x5_p2_viewE.

(** rand_joint_viewE — the executed joint reader is the product leakage
    witness's view, the joint equality witnessing rand_transfer_status.
    @intent: alias of s5x5_joint_viewE. *)
Definition rand_joint_viewE := @s5x5_joint_viewE.

(** pile1_word_transfer_status — the first pile's finite-word path's transfer
    status.
    @intent: NoModelComparison, the base-distribution premise of the generic
    transfer theorem being absent at the cut carrier. *)
Definition pile1_word_transfer_status : TransferStatus := NoModelComparison.

(** pile2_word_transfer_status — the second pile's finite-word path's transfer
    status.
    @intent: NoModelComparison, for the same absent premise. *)
Definition pile2_word_transfer_status : TransferStatus := NoModelComparison.

(** word_missing_premise — the absent premise named as a proposition.
    @intent: alias of s5x5_word_base_premise, a variation-distance bound
    between the finite-word cut distribution on {perm 'I_10} and a reference
    distribution on that carrier. *)
Definition word_missing_premise := @s5x5_word_base_premise.

(** word_transfer_conditional — the generic transfer inequality at the
    finite-word cut distribution, under that premise.
    @intent: alias of s5x5_word_transfer_conditional. *)
Definition word_transfer_conditional := @s5x5_word_transfer_conditional.

(** pile1_limitation_transfer_status — the first pile's global-uniform
    limitation path's transfer status.
    @intent: NegativeTransfer, the path carrying a lower bound on the distance
    from global uniform to its own executed endpoint distribution. *)
Definition pile1_limitation_transfer_status : TransferStatus :=
  NegativeTransfer.

(** pile2_limitation_transfer_status — the second pile's global-uniform
    limitation path's transfer status.
    @intent: NegativeTransfer, for the same reason. *)
Definition pile2_limitation_transfer_status : TransferStatus :=
  NegativeTransfer.

(** word_pile1_floor — negative mixing result for the first pile: the reverse
    triangle lower bound to global uniform on ten seats, conditional on
    s5_rayleigh_Q2_R.
    @intent: alias of s5x5_word_pile1_floor. *)
Definition word_pile1_floor := @s5x5_word_pile1_floor.

(** word_pile2_floor — negative mixing result for the second pile: the reverse
    triangle lower bound to global uniform on ten seats, conditional on
    s5_rayleigh_Q2_R.
    @intent: alias of s5x5_word_pile2_floor. *)
Definition word_pile2_floor := @s5x5_word_pile2_floor.

(** word_positive_regime — the word lengths at which the two floors are
    positive, named by the numeric fact that delimits them.
    @intent: alias of s5x5_lazy_bound_lt1, the statement that the mixing
    factor sqrt 5 times the L-th power of the lazy coefficient is below one
    from word length seventeen on. *)
Definition word_positive_regime := @s5x5_lazy_bound_lt1.

(** word_pile1_floor_gt0 — negative mixing result for the first pile in its
    positive regime: at word length at least seventeen the first pile's
    executed endpoint distribution is at positive distance from global
    uniform, conditional on s5_rayleigh_Q2_R.
    @intent: alias of s5x5_word_pile1_floor_gt0. *)
Definition word_pile1_floor_gt0 := @s5x5_word_pile1_floor_gt0.

(** word_pile2_floor_gt0 — negative mixing result for the second pile in its
    positive regime: at word length at least seventeen the second pile's
    executed endpoint distribution is at positive distance from global
    uniform, conditional on s5_rayleigh_Q2_R.
    @intent: alias of s5x5_word_pile2_floor_gt0. *)
Definition word_pile2_floor_gt0 := @s5x5_word_pile2_floor_gt0.

End S5x5Analysis.

(******************************************************************************)
(*     Retention checks                                                       *)
(*                                                                            *)
(* Value-level identity is checked for the two program-layer aliases, the two *)
(* plugs and the six transfer statuses, whose bodies do not reach the piSMC   *)
(* interpreter, so each of those lines pins the constant or the constructor   *)
(* the alias carries. On every other alias the value-level form               *)
(* Check (erefl : alias = landed) DIVERGES: the unifier unfolds past the      *)
(* alias into exec_participant_trace and evaluates run_interp. Those aliases  *)
(* are retained by spelled type ascriptions, one representative per section,  *)
(* so the assumptions, observers and numeric constants are legible in the     *)
(* source and not only up to conversion. Every line is Timeout-guarded, so a  *)
(* future re-aim of an alias into interpreter territory fails loudly at a     *)
(* named line instead of hanging the build.                                   *)
(******************************************************************************)

Timeout 60 Check (erefl : S5x5Analysis.profile = s5x5_profile).
Timeout 60 Check (erefl : S5x5Analysis.profile_k = profile_k_s5x5).
Timeout 60 Check (erefl : S5x5Analysis.exec_plug = s5x5_exec_plug).
Timeout 60 Check
  (erefl : S5x5Analysis.rand_exec_plug = s5x5_rand_exec_plug).

(* 1 Program *)
Timeout 60 Check (S5x5Analysis.profile : MonodromyProfile).

(* 2 Execution: the two plugs stand over the one profile. *)
Timeout 60 Check
  (S5x5Analysis.exec_plug : ExecutionPlug S5x5Analysis.profile).
Timeout 60 Check
  (S5x5Analysis.rand_exec_plug : ExecutionPlug S5x5Analysis.profile).

(* 3 Observers: the pile-tagged coalition reader keeps the five-element party
   index of its own pile and the pile carrier, and is a random variable on the
   product tape distribution. *)
Timeout 60 Check (S5x5Analysis.pile1_coalition_view :
  forall (R : realType), {set 'I_5} ->
    {RV (s5x5_rand_sampleP R) -> {ffun 'I_5 -> 'Z_5}}).
Timeout 60 Check (S5x5Analysis.pile2_seat_view :
  forall (R : realType), 'I_5 -> {RV (s5x5_rand_sampleP R) -> 'Z_5}).
Timeout 60 Check (S5x5Analysis.joint_view :
  forall (R : realType), {set 'I_5} -> {set 'I_5} ->
    {RV (s5x5_rand_sampleP R)
     -> ({ffun 'I_5 -> 'Z_5} * {ffun 'I_5 -> 'Z_5})%type}).

(* 4 Models: the finite-word adapter keeps its dependent index on the
   deterministic plug, its arbitrary secret prior and its word length. *)
Timeout 60 Check (S5x5Analysis.word_sample :
  forall (R : realType), R.-fdist 'I_10 -> forall L : nat,
    SampleAdapter R S5x5Analysis.exec_plug).

(* 5 Correctness: randomized recovery keeps its group-membership hypothesis
   and returns the combined pile secrets, not the pile pair. *)
Timeout 60 Check (S5x5Analysis.rand_observed_recovers :
  forall (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type) (w0 : pgg_gT s5x5_M),
    w0 \in pgg_G s5x5_M ->
    exec_decode S5x5Analysis.rand_exec_plug
      (OE.oe_endpoints_size S5x5Analysis.rand_observed uv w0)
    = s5x5_codec (s5x5_joint_tape_secret uv)).

(* 6 Security: executed joint secrecy keeps both per-pile cardinality
   hypotheses and both of its forms, at the executed joint reader of the
   randomized model. *)
Timeout 60 Check (S5x5Analysis.exec_joint_secrecy :
  forall (R : realType) (C1 C2 : {set 'I_5}),
    (#|C1| < 5)%N -> (#|C2| < 5)%N ->
    `I( JointSecret R ; S5x5Analysis.joint_view R C1 C2 ) = 0 /\
    `H( JointSecret R | S5x5Analysis.joint_view R C1 C2 )
      = `H `p_ (JointSecret R)).

(* bound: the pile-1 endpoint marginal bound keeps its one-position
   quantifier, its sqrt-5 factor and its L-th power of the lazy
   coefficient. *)
Timeout 60 Check (S5x5Analysis.word_pile1_bound :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
    var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma (widen5to10 s))
                (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
             (fdist_uniform_pile1 R)
    <= Num.sqrt 5%:R * (s5_lazy_alpha_R R) ^+ L).

(* 7 Transfer: the six statuses are typed values of the manifest vocabulary,
   the absent premise is a proposition on the cut carrier {perm 'I_10}, and
   the positive regime is the word lengths from seventeen on. *)
Timeout 60 Check
  (erefl : S5x5Analysis.det_transfer_status = NoModelComparison).
Timeout 60 Check
  (erefl : S5x5Analysis.rand_transfer_status = StaticExecutedOnly).
Timeout 60 Check
  (erefl : S5x5Analysis.pile1_word_transfer_status = NoModelComparison).
Timeout 60 Check
  (erefl : S5x5Analysis.pile2_word_transfer_status = NoModelComparison).
Timeout 60 Check
  (erefl : S5x5Analysis.pile1_limitation_transfer_status = NegativeTransfer).
Timeout 60 Check
  (erefl : S5x5Analysis.pile2_limitation_transfer_status = NegativeTransfer).
Timeout 60 Check (S5x5Analysis.word_missing_premise :
  forall (R : realType), R.-fdist 'I_10 -> forall L : nat,
    R.-fdist {perm 'I_10} -> R -> Prop).
Timeout 60 Check (S5x5Analysis.word_positive_regime :
  forall (R : realType) (n : nat), (17 <= n)%N ->
    Num.sqrt 5%:R * s5_lazy_alpha_R R ^+ n < 1).
