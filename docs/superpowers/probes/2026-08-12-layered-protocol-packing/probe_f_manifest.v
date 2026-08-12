(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* probe_f_manifest: the provisional repository-level analysis manifest.      *)
(*                                                                            *)
(* Probe unit F of the 2026-08-12 layered-protocol-packing gate: section      *)
(* 15.8, phase H1 of section 13.3.  The file re-exports the two featured      *)
(* facades, records one row per analysis path, and closes with a compile-time *)
(* checker that names every alias the table names.                            *)
(******************************************************************************)

From lpp_probe Require Export probe_f_pgl27_facade probe_f_five_card_facade.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The analysis manifest, part 1: identity of each path                   *)
(*                                                                            *)
(* | # | protocol and model | profile alias | execution alias |               *)
(* |---|---|---|---|                                                          *)
(* | 1 | PGL(2,7), exact uniform    | fa_pgl27_profile | fa_pgl27_exec_plug | *)
(* | 2 | PGL(2,7), finite word      | fa_pgl27_profile | fa_pgl27_exec_plug | *)
(* | 3 | five-card, uniform cut     | fa_five_card_profile                    *)
(*                                  | fa_five_card_exec_plug |                *)
(* | 4 | five-card, single biased   | fa_five_card_profile                    *)
(*                                  | fa_five_card_exec_plug |                *)
(* | 5 | five-card, repeated and seven-cut | fa_five_card_profile             *)
(*                                  | fa_five_card_exec_plug |                *)
(*                                                                            *)
(* Observed-execution alias: ABSENT on every row.  The ObservedExecution      *)
(* record is probe unit C and is stated over the post-migration               *)
(* parameterless records; it does not exist in the landed API this probe      *)
(* aliases.  Production reaches level Observed on all five rows through the   *)
(* migrated records, and the production manifest gains one further column     *)
(* entry per row.  Here the column is empty and every level is capped below   *)
(* Observed for that reason alone.                                            *)
(*                                                                            *)
(*     The analysis manifest, part 2: models, observers and results           *)
(*                                                                            *)
(* | # | sample alias | observer alias : carrier |                            *)
(* |---|---|---|                                                              *)
(* | 1 | fa_pgl27_sample | fa_pgl27_coalition_trace : {ffun 'I_8 -> 'I_8} |   *)
(* | 2 | fa_pgl27_word_sample | fa_pgl27_static_view : {ffun 'I_8 -> 'I_8} |  *)
(* | 3 | fa_five_card_sample | fa_five_card_content_trace : 'I_5,             *)
(*                             fa_five_card_dealer_trace : bool * bool |      *)
(* | 4 | fa_kim_single_sample | fa_five_card_colour_view :                    *)
(*                              (size A).-tuple bool |                        *)
(* | 5 | fa_kim_repeated_sample, fa_kim_centi_repeated_sample                 *)
(*     | fa_five_card_verifier_endpoints : seq 'I_5 |                         *)
(*                                                                            *)
(* | # | bound or certificate alias | bridge theorem alias |                  *)
(* |---|---|---|                                                              *)
(* | 1 | none | none in this manifest; see the level note below |             *)
(* | 2 | fa_pgl27_word_mixing | fa_pgl27_transfer, over fa_var_dist_transfer, *)
(*       reaching fa_pgl27_word_view_indist and fa_pgl27_word_trace_indist |  *)
(* | 3 | none | none; the capability theorems are                             *)
(*       fa_five_card_exec_trace_secrecy,                                     *)
(*       fa_five_card_exec_input_trace_secrecy,                               *)
(*       fa_five_card_exec_dealer_pair_centropy0 and                          *)
(*       fa_five_card_exec_dealer_trace_centropy0 |                           *)
(* | 4 | fa_kim_leak_bound | none; the capability theorem is                   *)
(*       fa_five_card_colour_view_leak_bound |                                *)
(* | 5 | fa_fc_kim_security_bound, fa_kim_deal_centi_lt,                      *)
(*       fa_kim_security_witness_centi | NONE, and none may be manufactured   *)
(*       from the bounds; see probe_f_mutation.v |                            *)
(*                                                                            *)
(* | # | completion level | theorem capability |                              *)
(* |---|---|---|                                                              *)
(* | 1 | Sampled | exact privacy, trace privacy, conditional entropy |        *)
(* | 2 | Security-bridged, at the static-view layer                           *)
(*     | approximate privacy, trace privacy |                                 *)
(* | 3 | Sampled | trace privacy, conditional entropy, correctness |          *)
(* | 4 | Sampled | mutual information |                                       *)
(* | 5 | Sampled | endpoint marginal bound |                                  *)
(*                                                                            *)
(*     How each level is justified from the aliases present                   *)
(*                                                                            *)
(* The rule used here: a row is Security-bridged only when this manifest      *)
(* names a typed alias that DERIVES a security conclusion for the very        *)
(* distribution the row's sample alias carries.  A row whose security         *)
(* theorems are stated over a distribution that no alias in this manifest     *)
(* type-links to the row's sample adapter stays Sampled, and its proved       *)
(* results are recorded as capabilities.  This is the conservative reading of *)
(* section 13.5, which asks that a missing bridge lower the level rather than *)
(* be papered over.                                                           *)
(*                                                                            *)
(* Row 1 is Sampled.  fa_pgl27_sample is the uniform model on the group;      *)
(* fa_pgl27_coalition_trace_secrecy and fa_pgl27_view_mixing are exact-layer  *)
(* theorems over fa_pgl27_prior, the static uniform prior.  The equality      *)
(* linking the sample adapter's executed observation to that static prior is  *)
(* pgl27_exact_coalition_distE of probe unit D2 and is not aliased here, so   *)
(* the exact privacy capability is recorded at the static layer and the level *)
(* stays Sampled.                                                             *)
(*                                                                            *)
(* Row 2 is Security-bridged at the static-view layer.  fa_pgl27_transfer     *)
(* derives the 2^-39 coalition bound at rho_word, which is the cut            *)
(* distribution of fa_pgl27_word_sample, from fa_var_dist_transfer and        *)
(* fa_pgl27_word_mixing.  The observer it bridges to is the static coalition  *)
(* view fa_pgl27_static_view, not the executed reader; the executed-layer     *)
(* bridge is probe unit D2 and is production work.  The qualifier "at the     *)
(* static-view layer" is part of the claim and is not decoration.             *)
(*                                                                            *)
(* Row 3 is Sampled.  fa_five_card_exec_trace_secrecy and the two dealer      *)
(* results are stated over fa_five_card_prior, which is also the sample space *)
(* of fa_five_card_sample, but no alias here equates the sample adapter's cut *)
(* or seat distribution with it, so the trace privacy and conditional entropy *)
(* results are recorded as capabilities at level Sampled.                     *)
(*                                                                            *)
(* Row 4 is Sampled with the mutual information capability.                   *)
(* fa_five_card_colour_view_leak_bound bounds the conditional mutual          *)
(* information the decoded colour sequence carries about the inputs given the *)
(* output, under Kim's biased distribution, which is the sample space of      *)
(* fa_kim_single_sample.  It is a leakage bound, not an indistinguishability  *)
(* bridge, so the level stays Sampled.                                        *)
(*                                                                            *)
(* Row 5 is Sampled with the endpoint marginal bound capability and is NOT    *)
(* Security-bridged.  fa_fc_kim_security_bound and fa_kim_deal_centi_lt bound *)
(* the distance from uniform of ONE seat's endpoint distribution.  Neither    *)
(* quantifies over a coalition view and neither can inhabit the type of an    *)
(* indistinguishability bridge; probe_f_mutation.v exhibits the rejection.    *)
(******************************************************************************)

(******************************************************************************)
(*     The deterministic checker                                              *)
(*                                                                            *)
(* One line per alias named in a column of the table above.  Deleting an      *)
(* alias from a facade makes the corresponding line here fail with "The       *)
(* reference ... was not found", and retyping one makes it fail with a type   *)
(* mismatch; either way probe_f_manifest.v itself stops compiling, so the     *)
(* table cannot drift away from the code.                                     *)
(*                                                                            *)
(* Where an ascription carries a hole, the hole stands for a subterm built    *)
(* from an instance-internal name that the facades deliberately do not        *)
(* re-export.  The full written type of every such statement is checked       *)
(* inside its own facade, where the instance names are in scope; the checker  *)
(* here pins the alias identity, the hypothesis structure, the observer and   *)
(* the numeric constants.                                                     *)
(******************************************************************************)

(* --- row 1 and row 2: PGL(2,7) --- *)

Timeout 60 Check (fa_pgl27_profile : forall R : realType, MonodromyProfile R).

Timeout 60 Check (fa_pgl27_exec_plug :
  forall R : realType, ExecutionPlug (fa_pgl27_profile R)).

Timeout 60 Check (fa_pgl27_sample :
  forall R : realType, SampleAdapter (fa_pgl27_exec_plug R)).

Timeout 60 Check (fa_pgl27_word_sample :
  forall R : realType, R.-fdist bool -> SampleAdapter (fa_pgl27_exec_plug R)).

Timeout 60 Check (fa_pgl27_coalition_trace :
  forall R : realType,
    {set 'I_8} -> {RV (fa_pgl27_prior R) -> {ffun 'I_8 -> 'I_8}}).

Timeout 60 Check (fa_pgl27_static_view :
  forall R : realType,
    {set 'I_8} -> {RV (fa_pgl27_prior R) -> {ffun 'I_8 -> 'I_8}}).

Timeout 60 Check (fa_pgl27_coalition_trace_secrecy :
  forall (R : realType) (C : {set 'I_8}),
    (#|C| <= 3)%N ->
    `H( (fa_pgl27_secret R) | (fa_pgl27_coalition_trace R C))
    = `H `p_ (fa_pgl27_secret R)).

Timeout 60 Check (fa_pgl27_word_mixing :
  forall R : realType, var_dist _ _ <= 2%:R^-40).

Timeout 60 Check (fa_var_dist_transfer :
  forall (R : realType) (A B : finType) (P Q : R.-fdist A) (fx fy : A -> B)
    (delta : R),
    var_dist P Q <= delta ->
    fdistmap fx Q = fdistmap fy Q ->
    var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta).

Timeout 60 Check (fa_pgl27_transfer :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N -> var_dist _ _ <= 2%:R^-39).

Timeout 60 Check (fa_pgl27_word_view_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N -> var_dist _ _ <= 2%:R^-39).

Timeout 60 Check (fa_pgl27_word_trace_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N -> var_dist _ _ <= 2%:R^-39).

(* --- rows 3, 4 and 5: five-card --- *)

Timeout 60 Check (fa_five_card_profile :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps -> `|eps| < 4%:R / 5%:R ->
    nat -> MonodromyProfile R).

Timeout 60 Check (fa_five_card_exec_plug :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    ExecutionPlug (fa_five_card_profile Hlt Hgt Hspec L)).

Timeout 60 Check (fa_five_card_sample :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    SampleAdapter (fa_five_card_exec_plug Hlt Hgt Hspec L)).

Timeout 60 Check (fa_kim_single_sample :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    SampleAdapter (fa_five_card_exec_plug Hlt Hgt Hspec L)).

Timeout 60 Check (fa_kim_repeated_sample :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    SampleAdapter (fa_five_card_exec_plug Hlt Hgt Hspec L)).

Timeout 60 Check (fa_kim_centi_repeated_sample :
  forall R : realType, SampleAdapter (fa_five_card_exec_plug _ _ _ 7)).

Timeout 60 Check (fa_five_card_content_trace :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    'I_(pi_T' (mp_PI (fa_five_card_profile Hlt Hgt Hspec L))).+1 ->
    {RV (fa_five_card_prior R) -> 'I_5}).

Timeout 60 Check (fa_five_card_dealer_trace :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps -> `|eps| < 4%:R / 5%:R ->
    nat -> {RV (fa_five_card_prior R) -> (bool * bool)}).

Timeout 60 Check (fa_five_card_colour_view :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat)
    (A : seq nat),
    bool * bool -> _ -> (size A).-tuple bool).

Timeout 60 Check (fa_five_card_verifier_endpoints :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    ep_inputT (fa_five_card_exec_plug Hlt Hgt Hspec L) -> _ -> nat -> seq _).

Timeout 60 Check (fa_five_card_exec_trace_secrecy :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    `H( (fa_five_card_secret R)
      | (@fa_five_card_content_trace R eps Hlt Hgt Hspec L ord0))
    = `H `p_ (fa_five_card_secret R)).

Timeout 60 Check (fa_five_card_exec_input_trace_secrecy :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R)
    (L j : nat),
    `H( (fa_five_card_secret R)
      | (fa_five_card_input_trace Hlt Hgt Hspec L j))
    = `H `p_ (fa_five_card_secret R)).

Timeout 60 Check (fa_five_card_exec_dealer_pair_centropy0 :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    `H( [eta fst] | (fa_five_card_dealer_trace Hlt Hgt Hspec L)) = 0).

Timeout 60 Check (fa_five_card_exec_dealer_trace_centropy0 :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    `H( (fa_five_card_secret R) | (fa_five_card_dealer_trace Hlt Hgt Hspec L))
    = 0).

Timeout 60 Check (fa_five_card_colour_view_leak_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat),
    0 < 5%:R^-1 - `|eps| ->
    forall A : seq nat, cond_mutual_info _ <= fa_kim_leak_bound eps).

Timeout 60 Check (fa_kim_leak_bound : forall R : realType, R -> R).

Timeout 60 Check (fa_kim_lambda2 : forall R : realType, R -> R).

Timeout 60 Check (fa_fc_kim_security_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    `|eps| < 4%:R / 5%:R ->
    forall (L : nat) (s : 'I_5),
      var_dist _ (fdist_uniform (card_ord 5))
      <= Num.ExtraDef.sqrtr 5%:R * fa_kim_lambda2 eps ^+ L).

Timeout 60 Check (fa_kim_deal_centi_lt :
  forall (R : realType) (s : 'I_5),
    var_dist (fdistmap _ (sw_rho_dist (fa_kim_security_witness_centi R)))
             (fdist_uniform (card_ord 5))
    < 2%:R^-40).

Timeout 60 Check (fa_five_card_exec_recovers :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (Hspec : `|eps| < 4%:R / 5%:R) (L : nat)
    (a b : bool) (w0 : _),
    w0 \in _ ->
    exec_decode (fa_five_card_exec_plug Hlt Hgt Hspec L) _ = a && b).

Timeout 60 Check (fa_pgl27_exec_recovers :
  forall (R : realType) (s : bool) (w0 : _),
    w0 \in _ -> exec_decode (fa_pgl27_exec_plug R) _ = s).
