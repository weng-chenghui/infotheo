(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_analysis_manifest: the repository-level analysis manifest              *)
(*                                                                            *)
(* The manifest re-exports the two featured facades, so that one import       *)
(* reaches every public alias of the eight-card orbit instance and of the     *)
(* five-card development, and records one row per analysis path. Each row     *)
(* names its profile, execution, observed-execution, sample, observer,        *)
(* bound or certificate and final bridge aliases, its completion level, and   *)
(* one capability line per (theorem, distribution, observer, security         *)
(* notion) tuple.                                                             *)
(*                                                                            *)
(* Completion levels are cumulative and are read off the typed witnesses      *)
(* this manifest names, never asserted:                                       *)
(*                                                                            *)
(*   Algebraic        profile alias                                           *)
(*   Executable       + execution-plug alias indexed by that profile          *)
(*   Observed         + observed-execution alias indexed by profile and plug  *)
(*   Sampled          + sample-adapter alias AND its distribution-to-observer *)
(*                     bridge                                                 *)
(*   Security-bridged + bridge alias to a named security theorem about the    *)
(*                     same distribution and the same observer                *)
(*                                                                            *)
(* Every identifier in the table below is checked at the end of this file by  *)
(* one Timeout-guarded Check against its spelled type. Deleting an alias      *)
(* makes its line fail with "The reference ... was not found" and retyping    *)
(* one makes it fail with a type mismatch, so the table cannot drift away     *)
(* from the code.                                                             *)
(******************************************************************************)

From pgg_smc Require Export pgl27_analysis five_card_analysis.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Row 1: eight-card orbit instance, exact uniform shuffle                *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | PGL(2,7) orbit deck, exact uniform cut |     *)
(* | profile alias      | PGL27Analysis.profile |                             *)
(* | execution alias    | PGL27Analysis.exec_plug |                           *)
(* | observed alias     | PGL27Analysis.observed |                            *)
(* | sample alias       | PGL27Analysis.exact_sample,                         *)
(*                        PGL27Analysis.fixed_exact_sample |                  *)
(* | observers          | PGL27Analysis.coalition_endpoints                   *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.content_trace                         *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.static_view                           *)
(*                          : {ffun 'I_8 -> 'I_8}, random variable on prior;  *)
(*                        PGL27Analysis.coalition_trace                       *)
(*                          : {ffun 'I_8 -> 'I_8}, random variable on prior;  *)
(*                        PGL27Analysis.secret : bool |                       *)
(* | distribution-to-observer bridges | PGL27Analysis.sample_cut_distE,       *)
(*                        PGL27Analysis.fixed_cut_distE,                      *)
(*                        PGL27Analysis.exact_coalition_distE,                *)
(*                        PGL27Analysis.content_traceE |                      *)
(* | bound or certificate | PGL27Analysis.marginal_bound,                     *)
(*                          PGL27Analysis.certificate_bundle |                *)
(* | final bridge theorem | PGL27Analysis.exact_view_indep |                  *)
(* | completion level     | Security-bridged |                                *)
(*                                                                            *)
(* Capabilities, one line per (theorem, distribution, observer, notion):      *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exact_view_indep | prior R, the distribution of exact_sample             *)
(*   | coalition_endpoints, through exact_coalition_distE | exact privacy |   *)
(* | coalition_trace_secrecy | prior R                                        *)
(*   | coalition_trace, linked to content_trace by content_traceE             *)
(*   | conditional entropy |                                                  *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. profile gives Algebraic; exec_plug is indexed by      *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed; exact_sample is a SampleAdapter over    *)
(* that plug and exact_coalition_distE identifies its executed coalition      *)
(* distribution with the pushforward of prior along static_view, giving       *)
(* Sampled; exact_view_indep is a security theorem whose right-hand side      *)
(* names sa_coalition_dist (exact_sample R) 0 C itself, so the theorem, the   *)
(* distribution and the observer are this row's own, giving                   *)
(* Security-bridged.                                                          *)
(*                                                                            *)
(*     Row 2: eight-card orbit instance, finite two-hundred-letter word       *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | PGL(2,7) orbit deck, word shuffle at         *)
(*                               length 200 |                                 *)
(* | profile alias      | PGL27Analysis.profile |                             *)
(* | execution alias    | PGL27Analysis.exec_plug |                           *)
(* | observed alias     | PGL27Analysis.observed |                            *)
(* | sample alias       | PGL27Analysis.word_sample at an arbitrary secret    *)
(*                        prior, PGL27Analysis.fixed_word_sample at a fixed   *)
(*                        secret |                                            *)
(* | observers          | PGL27Analysis.coalition_endpoints                   *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.content_trace                         *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.static_view,                          *)
(*                        PGL27Analysis.coalition_trace                       *)
(*                          : {ffun 'I_8 -> 'I_8};                            *)
(*                        PGL27Analysis.secret : bool |                       *)
(* | distribution-to-observer bridges | PGL27Analysis.word_cut_distE,         *)
(*                        PGL27Analysis.fixed_word_cut_distE,                 *)
(*                        PGL27Analysis.fixed_word_coalition_distE,           *)
(*                        PGL27Analysis.fixed_word_content_trace_distE,       *)
(*                        PGL27Analysis.word_joint_viewE,                     *)
(*                        PGL27Analysis.word_sample_joint_distE |             *)
(* | bound or certificate | PGL27Analysis.word_mixing, the 2^-40 distance of  *)
(*                          the word shuffle from uniform |                   *)
(* | final bridge theorem | PGL27Analysis.exec_view_indist,                   *)
(*                          PGL27Analysis.exec_trace_indist,                  *)
(*                          PGL27Analysis.word_view_indist_via_transfer |     *)
(* | completion level     | Security-bridged |                                *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exec_view_indist | rho_word, the cut distribution of fixed_word_sample   *)
(*   by fixed_word_cut_distE | coalition_endpoints, executed, through         *)
(*   fixed_word_coalition_distE | approximate privacy at 2^-39 |              *)
(* | exec_trace_indist | rho_word | content_trace, executed, through          *)
(*   fixed_word_content_trace_distE | approximate privacy at 2^-39 |          *)
(* | word_view_indist | rho_word | static_view                                *)
(*   | approximate privacy at 2^-39 |                                         *)
(* | word_trace_indist | rho_word | coalition_trace                           *)
(*   | approximate privacy at 2^-39 |                                         *)
(* | view_mixing | pgl27P_word_gen secretP, the joint distribution of         *)
(*   word_sample by word_sample_joint_distE | the pair of static_view and     *)
(*   secret | approximate privacy at 2^-40 |                                  *)
(* | word_view_indist_via_transfer | rho_word | static_view                   *)
(*   | approximate privacy at 2^-39, derived from var_dist_transfer and       *)
(*     word_mixing |                                                          *)
(*                                                                            *)
(* Level justification. The first three levels are witnessed by the same      *)
(* three aliases as row 1. fixed_word_sample is a SampleAdapter over that     *)
(* plug and fixed_word_coalition_distE identifies its executed coalition      *)
(* distribution with the pushforward of rho_word along static_view, giving    *)
(* Sampled. exec_view_indist and exec_trace_indist are stated directly at     *)
(* that sample layer, at the executed coalition observation and at the        *)
(* executed content reader, giving Security-bridged at both executed          *)
(* observers rather than at the static layer alone.                           *)
(*                                                                            *)
(*     Row 3: five-card development, uniform cut (den Boer)                   *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | five-card AND evaluation, uniform rotation   *)
(*                               cut |                                        *)
(* | profile alias      | FiveCardAnalysis.profile, and the same program      *)
(*                        under FiveCardAnalysis.den_boer_profile |           *)
(* | execution alias    | FiveCardAnalysis.exec_plug |                        *)
(* | observed alias     | FiveCardAnalysis.observed, and the same value under *)
(*                        FiveCardAnalysis.den_boer_observed |                *)
(* | sample alias       | FiveCardAnalysis.uniform_sample |                   *)
(* | observers          | FiveCardAnalysis.content_trace : 'I_5, executed;    *)
(*                        FiveCardAnalysis.dealer_trace : bool * bool,        *)
(*                          executed;                                         *)
(*                        FiveCardAnalysis.input_trace : 'I_5, executed;      *)
(*                        FiveCardAnalysis.verifier_endpoints                 *)
(*                          : seq 'I_5;                                       *)
(*                        FiveCardAnalysis.secret : bool |                    *)
(* | distribution-to-observer bridges | FiveCardAnalysis.sample_cut_distE,    *)
(*                        FiveCardAnalysis.sample_cut_witnessE,               *)
(*                        FiveCardAnalysis.witness_rotationE |                *)
(* | bound or certificate | FiveCardAnalysis.marginal_bound,                  *)
(*                          FiveCardAnalysis.perfect |                        *)
(* | final bridge theorem | FiveCardAnalysis.exec_trace_secrecy |             *)
(* | completion level     | Security-bridged |                                *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exec_trace_secrecy | prior R, the distribution of uniform_sample         *)
(*   | content_trace R ord0, executed | trace privacy |                       *)
(* | dealer_trace_centropy0 | prior R | dealer_trace, executed                *)
(*   | conditional entropy |                                                  *)
(* | dealer_pair_centropy0 | prior R | dealer_trace, executed                 *)
(*   | conditional entropy |                                                  *)
(* | input_trace_secrecy | prior R | input_trace, executed                    *)
(*   | conditional entropy (constant conditioning) |                          *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | verifier_endpoints | correctness |                                     *)
(*                                                                            *)
(* Level justification, stated explicitly because this row is the one whose   *)
(* level depends on an identity rather than on a named bridge lemma.          *)
(* uniform_sample is the sample adapter whose carrier is the den Boer sample  *)
(* space, whose distribution is prior R, whose argument map is the first      *)
(* projection and whose cut map is the rotation fc_sigma ^+ k of the second.  *)
(* content_trace R ord0 is a random variable on that same prior R whose value *)
(* is the content of the executed seat row at exactly that argument and that  *)
(* cut. exec_trace_secrecy is stated at that random variable. So the          *)
(* theorem's distribution is the row's sample distribution, its observer is   *)
(* an aliased executed observer of the row, and sample_cut_distE names the    *)
(* row's cut distribution; the row is Security-bridged with the trace         *)
(* privacy capability. input_trace_secrecy is NOT counted towards that level: *)
(* the input rows of the executed trace are empty, so its conditioning        *)
(* variable is constant and it is recorded as conditional entropy under       *)
(* constant conditioning, an architecture statement rather than a privacy     *)
(* bound.                                                                     *)
(*                                                                            *)
(*     Row 4: five-card development, single biased cut                        *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | five-card AND evaluation, one biased cut at  *)
(*                               Kim's input distribution |                   *)
(* | profile alias      | FiveCardAnalysis.profile |                          *)
(* | execution alias    | FiveCardAnalysis.exec_plug |                        *)
(* | observed alias     | FiveCardAnalysis.observed |                         *)
(* | sample alias       | FiveCardAnalysis.single_biased_sample |             *)
(* | observers          | FiveCardAnalysis.colour_view                        *)
(*                          : (size A).-tuple bool, the decoded colour        *)
(*                            sequence at a list A of seat indices into the   *)
(*                            endpoint list |                                 *)
(* | distribution-to-observer bridges | FiveCardAnalysis.single_cut_distE,    *)
(*                        FiveCardAnalysis.colour_viewE,                      *)
(*                        FiveCardAnalysis.colour_view_RV_E |                 *)
(* | bound or certificate | none; kim_leak_bound is the numeric constant of   *)
(*                          the bridge theorem, not a shuffle certificate |   *)
(* | final bridge theorem | FiveCardAnalysis.colour_view_leak_bound |         *)
(* | completion level     | Security-bridged |                                *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | colour_view_leak_bound | kim_input_dist eps_lt_inv5 eps_gt_neg4inv5,     *)
(*   the distribution of single_biased_sample | colour_view A, executed       *)
(*   | mutual information, at most kim_leak_bound eps |                       *)
(*                                                                            *)
(* Hypotheses of that capability: eps_lt_inv5, eps_gt_neg4inv5 and the        *)
(* small-bias hypothesis eps_small : 0 < 5^-1 - `|eps|. All three are         *)
(* explicit arguments of the aliased theorem; none is discharged silently.    *)
(*                                                                            *)
(* Level justification. single_biased_sample is the sample adapter with the   *)
(* same carrier and the same argument and cut maps as uniform_sample and with *)
(* Kim's biased distribution, and single_cut_distE identifies its cut         *)
(* distribution with the biased rotation, giving Sampled.                     *)
(* colour_view_leak_bound bounds a conditional mutual information of a joint  *)
(* distribution whose middle component is the executed reader colour_view     *)
(* itself, over that same biased distribution, giving Security-bridged.       *)
(*                                                                            *)
(*     Row 5: five-card development, repeated biased cuts and seven cuts      *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | five-card AND evaluation, L repeated biased  *)
(*                               cuts, and its seven-cut member at bias one   *)
(*                               hundredth |                                  *)
(* | profile alias      | FiveCardAnalysis.profile |                          *)
(* | execution alias    | FiveCardAnalysis.exec_plug |                        *)
(* | observed alias     | FiveCardAnalysis.observed |                         *)
(* | sample alias       | FiveCardAnalysis.repeated_sample,                   *)
(*                        FiveCardAnalysis.centi_sample |                     *)
(* | observers          | one seat's endpoint distribution, reached through   *)
(*                        FiveCardAnalysis.repeated_seat_distE and            *)
(*                        FiveCardAnalysis.centi_repeated_seat_distE;         *)
(*                        FiveCardAnalysis.verifier_endpoints : seq 'I_5 |    *)
(* | distribution-to-observer bridges | FiveCardAnalysis.repeated_cut_distE,  *)
(*                        FiveCardAnalysis.centi_cut_distE,                   *)
(*                        FiveCardAnalysis.centi_witness_rhoE,                *)
(*                        FiveCardAnalysis.repeated_seat_distE,               *)
(*                        FiveCardAnalysis.centi_repeated_seat_distE |        *)
(* | bound or certificate | FiveCardAnalysis.kim_bundle,                      *)
(*                          FiveCardAnalysis.centi_bundle,                    *)
(*                          FiveCardAnalysis.endpoint_bound,                  *)
(*                          FiveCardAnalysis.deal_centi_lt |                  *)
(* | final bridge theorem | NONE |                                            *)
(* | completion level     | Sampled |                                         *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | endpoint_bound | the weighted word shuffle at word length L              *)
(*   | one seat's endpoint distribution | endpoint marginal bound |           *)
(* | deal_centi_lt | the cut distribution of centi_sample, by                 *)
(*   centi_cut_distE | one seat's endpoint distribution                       *)
(*   | endpoint marginal bound |                                              *)
(*                                                                            *)
(* Level justification. Both models are sample adapters over the plug and     *)
(* both cut distributions are named, giving Sampled. The row is NOT           *)
(* Security-bridged. endpoint_bound and deal_centi_lt bound the distance      *)
(* from uniform of ONE seat's endpoint distribution: neither quantifies over  *)
(* a coalition, neither mentions a second secret, and neither has the shape   *)
(* of an indistinguishability or leakage statement. A ShuffleCertificate-     *)
(* Bundle exists for both models and does not raise the level.                *)
(*                                                                            *)
(*     Aliases carrying no capability yet                                     *)
(*                                                                            *)
(* These are public observers and correctness statements of the two facades   *)
(* that no row above attaches a security notion to. They are named here so    *)
(* that the checker pins the whole facade surface, not only the rows.         *)
(*                                                                            *)
(* | facade | aliases |                                                       *)
(* |---|---|                                                                  *)
(* | PGL27Analysis | verifier_trace, player_raw_trace, coalition_raw_trace,   *)
(*                   seat_endpoint, prior, exec_correct, exec_recovers,       *)
(*                   var_dist_transfer |                                      *)
(* | FiveCardAnalysis | verifier_trace, player_raw_trace,                     *)
(*                      coalition_raw_trace, input_raw_trace,                 *)
(*                      dealer_raw_trace, prior, exec_correct, exec_recovers, *)
(*                      procs_biasE |                                         *)
(*                                                                            *)
(*     Absent capabilities                                                    *)
(*                                                                            *)
(* The five-card development has no transfer-layer result: section 7 of its   *)
(* facade is empty and no row cites a transfer capability. No row is filled   *)
(* with a dummy theorem, an option-valued proof, an axiom or a placeholder,   *)
(* and no endpoint marginal bound is recorded as a privacy or security        *)
(* capability.                                                                *)
(******************************************************************************)

(******************************************************************************)
(*     The deterministic checker: eight-card orbit instance                   *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (PGL27Analysis.profile : MonodromyProfile).

(* --- 2 Execution --- *)

Timeout 60 Check (PGL27Analysis.exec_plug :
  ExecutionPlug PGL27Analysis.profile).

Timeout 60 Check (PGL27Analysis.verifier_trace :
  ep_inputT PGL27Analysis.exec_plug ->
  pgg_gT (mp_M PGL27Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M PGL27Analysis.profile)).+1)).

(* --- 3 Observers --- *)

Timeout 60 Check (PGL27Analysis.player_raw_trace :
  bool -> pgg_gT (mp_M PGL27Analysis.profile) ->
  'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M PGL27Analysis.profile)).+1)).

Timeout 60 Check (PGL27Analysis.coalition_raw_trace :
  bool -> pgg_gT (mp_M PGL27Analysis.profile) ->
  {set 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
        seq (pgg_data (pgg_N' (mp_M PGL27Analysis.profile)).+1)}).

Timeout 60 Check (PGL27Analysis.seat_endpoint :
  ep_inputT PGL27Analysis.exec_plug ->
  pgg_gT (mp_M PGL27Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M PGL27Analysis.profile)).+1).

Timeout 60 Check (PGL27Analysis.coalition_endpoints :
  ep_inputT PGL27Analysis.exec_plug ->
  pgg_gT (mp_M PGL27Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M PGL27Analysis.profile)).+1}).

Timeout 60 Check (PGL27Analysis.content_trace :
  {set 'I_8} -> bool -> pgg_gT (mp_M PGL27Analysis.profile) ->
  {ffun 'I_8 -> 'I_8}).

Timeout 60 Check (PGL27Analysis.static_view :
  forall R : realType,
    {set 'I_8} -> {RV (PGL27Analysis.prior R) -> {ffun 'I_8 -> 'I_8}}).

Timeout 60 Check (PGL27Analysis.coalition_trace :
  forall R : realType,
    {set 'I_8} -> {RV (PGL27Analysis.prior R) -> {ffun 'I_8 -> 'I_8}}).

Timeout 60 Check (PGL27Analysis.secret :
  forall R : realType, {RV (PGL27Analysis.prior R) -> bool}).

Timeout 60 Check (PGL27Analysis.prior :
  forall R : realType,
    R.-fdist (bool * pgg_gT (mp_M PGL27Analysis.profile))%type).

Timeout 60 Check (PGL27Analysis.observed : OE.ObservedExecution).

(* --- 4 Models --- *)

Timeout 60 Check (PGL27Analysis.exact_sample :
  forall R : realType, SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.word_sample :
  forall R : realType,
    R.-fdist bool -> SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.fixed_exact_sample :
  forall R : realType, bool -> SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.fixed_word_sample :
  forall R : realType, bool -> SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.sample_cut_distE :
  forall R : realType,
    sa_cut_dist (PGL27Analysis.exact_sample R)
    = sw_rho_dist (PGL27Analysis.marginal_bound R)).

Timeout 60 Check (PGL27Analysis.word_cut_distE :
  forall (R : realType) (secretP : R.-fdist bool),
    sa_cut_dist (@PGL27Analysis.word_sample R secretP)
    = pgl27_word_privacy.rho_word R).

Timeout 60 Check (PGL27Analysis.fixed_cut_distE :
  forall (R : realType) (s : bool),
    sa_cut_dist (PGL27Analysis.fixed_exact_sample R s)
    = (`U pgl27_profile.pgl27_G_pos
       : R.-fdist (pgg_gT (mp_M PGL27Analysis.profile)))).

Timeout 60 Check (PGL27Analysis.fixed_word_cut_distE :
  forall (R : realType) (s : bool),
    sa_cut_dist (PGL27Analysis.fixed_word_sample R s)
    = pgl27_word_privacy.rho_word R).

Timeout 60 Check (PGL27Analysis.exact_coalition_distE :
  forall (R : realType) (C : {set 'I_8}),
    sa_coalition_dist (PGL27Analysis.exact_sample R) 0 C
    = fdistmap (PGL27Analysis.static_view R C) (PGL27Analysis.prior R)).

Timeout 60 Check (PGL27Analysis.fixed_word_coalition_distE :
  forall (R : realType) (C : {set 'I_8}) (s : bool),
    sa_coalition_dist (PGL27Analysis.fixed_word_sample R s) 0 C
    = fdistmap (fun g => PGL27Analysis.static_view R C (s, g))
        (pgl27_word_privacy.rho_word R)).

Timeout 60 Check (PGL27Analysis.fixed_word_content_trace_distE :
  forall (R : realType) (C : {set 'I_8}) (s : bool),
    fdistmap (fun w : 200.-tuple 'I_5 =>
                PGL27Analysis.content_trace C s (word_eval w))
      (pgl27_exec.pgl27_word_wordP R)
    = fdistmap (fun g => PGL27Analysis.coalition_trace R C (s, g))
        (pgl27_word_privacy.rho_word R)).

Timeout 60 Check (PGL27Analysis.word_joint_viewE :
  forall (R : realType) (secretP : R.-fdist bool) (C : {set 'I_8}),
    fdistmap (fun u : bool * 200.-tuple 'I_5 =>
                (PGL27Analysis.coalition_endpoints u.1 (word_eval u.2) 0 C,
                 u.1))
      (@pgl27_exec.pgl27_word_sampleP R secretP)
    = fdistmap (fun v => (PGL27Analysis.static_view R C v,
                          PGL27Analysis.secret R v))
        (@pgl27_word_privacy.pgl27P_word_gen R secretP)).

Timeout 60 Check (PGL27Analysis.word_sample_joint_distE :
  forall (R : realType) (secretP : R.-fdist bool),
    sa_joint_dist (sa_arg (s := @PGL27Analysis.word_sample R secretP))
    = @pgl27_word_privacy.pgl27P_word_gen R secretP).

(* --- 5 Correctness --- *)

Timeout 60 Check (PGL27Analysis.exec_correct :
  forall (s : bool) (w0 : pgg_gT (mp_M PGL27Analysis.profile)),
    w0 \in pgg_G (mp_M PGL27Analysis.profile) ->
    [/\ (@exec_run PGL27Analysis.profile PGL27Analysis.exec_plug s w0 0).1
        = nseq (size (@exec_procs PGL27Analysis.profile
                        PGL27Analysis.exec_plug s w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints PGL27Analysis.profile PGL27Analysis.exec_plug
                s w0 0)
        = (pi_T' (mp_PI PGL27Analysis.profile)).+1
      & exec_decode PGL27Analysis.exec_plug
          (exec_endpoints_size (pgl27_exec.pgl27_exec_endpoints s w0)) = s]).

Timeout 60 Check (PGL27Analysis.exec_recovers :
  forall (s : bool) (w0 : pgg_gT (mp_M PGL27Analysis.profile)),
    w0 \in pgg_G (mp_M PGL27Analysis.profile) ->
    exec_decode PGL27Analysis.exec_plug
      (exec_endpoints_size (pgl27_exec.pgl27_exec_endpoints s w0)) = s).

Timeout 60 Check (PGL27Analysis.observed_recovers :
  forall (s : bool) (w0 : pgg_gT (mp_M PGL27Analysis.profile)),
    w0 \in pgg_G (mp_M PGL27Analysis.profile) ->
    exec_decode PGL27Analysis.exec_plug
      (OE.oe_endpoints_size PGL27Analysis.observed s w0) = s).

(* --- 6 Security --- *)

Timeout 60 Check (PGL27Analysis.content_traceE :
  forall (R : realType) (C : {set 'I_8})
    (u : bool * pgg_gT (mp_M PGL27Analysis.profile)),
    PGL27Analysis.content_trace C u.1 u.2
    = PGL27Analysis.coalition_trace R C u).

Timeout 60 Check (PGL27Analysis.word_view_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun g => PGL27Analysis.static_view R C (s, g))
         (pgl27_word_privacy.rho_word R))
      (fdistmap (fun g => PGL27Analysis.static_view R C (s', g))
         (pgl27_word_privacy.rho_word R))
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.word_trace_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun g => PGL27Analysis.coalition_trace R C (s, g))
         (pgl27_word_privacy.rho_word R))
      (fdistmap (fun g => PGL27Analysis.coalition_trace R C (s', g))
         (pgl27_word_privacy.rho_word R))
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.exec_view_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist (sa_coalition_dist (PGL27Analysis.fixed_word_sample R s) 0 C)
             (sa_coalition_dist (PGL27Analysis.fixed_word_sample R s') 0 C)
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.exec_trace_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun w : 200.-tuple 'I_5 =>
                   PGL27Analysis.content_trace C s (word_eval w))
         (pgl27_exec.pgl27_word_wordP R))
      (fdistmap (fun w : 200.-tuple 'I_5 =>
                   PGL27Analysis.content_trace C s' (word_eval w))
         (pgl27_exec.pgl27_word_wordP R))
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.view_mixing :
  forall (R : realType) (secretP : R.-fdist bool) (C : {set 'I_8}),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun u => (PGL27Analysis.static_view R C u,
                           PGL27Analysis.secret R u))
         (@pgl27_word_privacy.pgl27P_word_gen R secretP))
      ((fdistmap (PGL27Analysis.static_view R C)
          (@pgl27_word_privacy.pgl27P_gen R secretP))
       `x (fdistmap (PGL27Analysis.secret R)
             (@pgl27_word_privacy.pgl27P_gen R secretP)))%fdist
    <= 2%:R^-40).

Timeout 60 Check (PGL27Analysis.word_mixing :
  forall R : realType,
    var_dist
      (rho_from_words_weighted 200 pgl27_mixing.pgl27_sym_sigmas
         (pgl27_mixing.Wuni R))
      (`U pgl27_profile.pgl27_G_pos)
    <= 2%:R^-40).

Timeout 60 Check (PGL27Analysis.coalition_trace_secrecy :
  forall (R : realType) (C : {set 'I_8}),
    (#|C| <= 3)%N ->
    `H( (PGL27Analysis.secret R) | (PGL27Analysis.coalition_trace R C))
    = `H `p_ (PGL27Analysis.secret R)).

Timeout 60 Check (PGL27Analysis.exact_view_indep :
  forall (R : realType) (C : {set 'I_8}),
    (#|C| <= 3)%N ->
    fdistmap (fun u => (PGL27Analysis.static_view R C u,
                        PGL27Analysis.secret R u)) (PGL27Analysis.prior R)
    = ((sa_coalition_dist (PGL27Analysis.exact_sample R) 0 C)
       `x (fdistmap (PGL27Analysis.secret R) (PGL27Analysis.prior R)))%fdist).

Timeout 60 Check (PGL27Analysis.marginal_bound :
  forall R : realType,
    ShuffleMarginalBound R (mp_M PGL27Analysis.profile)).

Timeout 60 Check (PGL27Analysis.certificate_bundle :
  forall R : realType,
    ShuffleCertificateBundle R (mp_M PGL27Analysis.profile)).

(* --- 7 Transfer --- *)

Timeout 60 Check (PGL27Analysis.var_dist_transfer :
  forall (R : realType) (A B : finType) (P Q : R.-fdist A) (fx fy : A -> B)
    (delta : R),
    var_dist P Q <= delta ->
    fdistmap fx Q = fdistmap fy Q ->
    var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta).

Timeout 60 Check (PGL27Analysis.word_view_indist_via_transfer :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun g => PGL27Analysis.static_view R C (s, g))
         (pgl27_word_privacy.rho_word R))
      (fdistmap (fun g => PGL27Analysis.static_view R C (s', g))
         (pgl27_word_privacy.rho_word R))
    <= 2%:R^-39).

(******************************************************************************)
(*     The deterministic checker: five-card development                       *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (FiveCardAnalysis.profile : MonodromyProfile).

Timeout 60 Check (FiveCardAnalysis.den_boer_profile : MonodromyProfile).

(* --- 2 Execution --- *)

Timeout 60 Check (FiveCardAnalysis.exec_plug :
  ExecutionPlug FiveCardAnalysis.profile).

Timeout 60 Check (FiveCardAnalysis.verifier_trace :
  ep_inputT FiveCardAnalysis.exec_plug ->
  pgg_gT (mp_M FiveCardAnalysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

(* --- 3 Observers --- *)

Timeout 60 Check (FiveCardAnalysis.player_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
  'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

Timeout 60 Check (FiveCardAnalysis.coalition_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
  {set 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1 ->
        seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)}).

Timeout 60 Check (FiveCardAnalysis.input_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

Timeout 60 Check (FiveCardAnalysis.input_trace :
  forall R : realType, nat -> {RV (FiveCardAnalysis.prior R) -> 'I_5}).

Timeout 60 Check (FiveCardAnalysis.dealer_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

Timeout 60 Check (FiveCardAnalysis.dealer_trace :
  forall R : realType,
    {RV (FiveCardAnalysis.prior R) -> (bool * bool)%type}).

Timeout 60 Check (FiveCardAnalysis.verifier_endpoints :
  ep_inputT FiveCardAnalysis.exec_plug ->
  pgg_gT (mp_M FiveCardAnalysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M FiveCardAnalysis.profile)).+1).

Timeout 60 Check (FiveCardAnalysis.content_trace :
  forall R : realType,
    'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1 ->
    {RV (FiveCardAnalysis.prior R) -> 'I_5}).

Timeout 60 Check (FiveCardAnalysis.colour_view :
  forall A : seq nat,
    bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
    (size A).-tuple bool).

Timeout 60 Check (FiveCardAnalysis.secret :
  forall R : realType, {RV (FiveCardAnalysis.prior R) -> bool}).

Timeout 60 Check (FiveCardAnalysis.prior :
  forall R : realType, R.-fdist five_card_leakage.Omega).

Timeout 60 Check (FiveCardAnalysis.observed : OE.ObservedExecution).

Timeout 60 Check (FiveCardAnalysis.den_boer_observed : OE.ObservedExecution).

(* --- 4 Models --- *)

Timeout 60 Check (FiveCardAnalysis.uniform_sample :
  forall R : realType, SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.single_biased_sample :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps ->
    SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.repeated_sample :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps -> nat ->
    SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.centi_sample :
  forall R : realType, SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.sample_cut_distE :
  forall R : realType,
    five_card_exec.five_card_sample_cut_dist R
    = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
        (fdist_uniform (card_ord 5))).

Timeout 60 Check (FiveCardAnalysis.sample_cut_witnessE :
  forall R : realType,
    five_card_exec.five_card_sample_cut_dist R
    = sw_rho_dist (FiveCardAnalysis.marginal_bound R)).

Timeout 60 Check (FiveCardAnalysis.witness_rotationE :
  forall R : realType,
    sw_rho_dist (FiveCardAnalysis.marginal_bound R)
    = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
        (fdist_uniform (card_ord 5))).

Timeout 60 Check (FiveCardAnalysis.single_cut_distE :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    sa_cut_dist (@FiveCardAnalysis.single_biased_sample R eps Hlt Hgt)
    = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
        (five_card_kim.kim_weight_dist Hlt Hgt)).

Timeout 60 Check (FiveCardAnalysis.repeated_cut_distE :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (L : nat),
    sa_cut_dist (@FiveCardAnalysis.repeated_sample R eps Hlt Hgt L)
    = rho_from_words_weighted L five_card_kim.fc_kim_sigmas
        (five_card_kim.kim_weight_dist Hlt Hgt)).

Timeout 60 Check (FiveCardAnalysis.repeated_seat_distE :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (L : nat)
    (i : 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1),
    sa_seat_dist (@FiveCardAnalysis.repeated_sample R eps Hlt Hgt L) 0 i
    = fdistmap
        (@sa_static_seat_view R FiveCardAnalysis.profile
           FiveCardAnalysis.exec_plug
           (@FiveCardAnalysis.repeated_sample R eps Hlt Hgt L)
           five_card_exec.five_card_content_obs i)
        (@five_card_models.kim_repeated_dist R eps Hlt Hgt L)).

Timeout 60 Check (FiveCardAnalysis.centi_cut_distE :
  forall R : realType,
    sa_cut_dist (FiveCardAnalysis.centi_sample R)
    = sw_rho_dist (scb_bound (FiveCardAnalysis.centi_bundle R))).

Timeout 60 Check (FiveCardAnalysis.centi_witness_rhoE :
  forall R : realType,
    sw_rho_dist (scb_bound (FiveCardAnalysis.centi_bundle R))
    = rho_from_words_weighted 7 five_card_kim.fc_kim_sigmas
        (five_card_kim.kim_weight_dist (five_card_kim.kim_centi_lt R)
           (five_card_kim.kim_centi_gt R))).

Timeout 60 Check (FiveCardAnalysis.centi_repeated_seat_distE :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1),
    sa_seat_dist
      (@FiveCardAnalysis.repeated_sample R (1 / 100)
         (five_card_kim.kim_centi_lt R) (five_card_kim.kim_centi_gt R) 7) 0 i
    = fdistmap
        (@sa_static_seat_view R FiveCardAnalysis.profile
           FiveCardAnalysis.exec_plug
           (@FiveCardAnalysis.repeated_sample R (1 / 100)
              (five_card_kim.kim_centi_lt R) (five_card_kim.kim_centi_gt R) 7)
           five_card_exec.five_card_content_obs i)
        (@five_card_models.kim_repeated_dist R (1 / 100)
           (five_card_kim.kim_centi_lt R) (five_card_kim.kim_centi_gt R) 7)).

(* --- 5 Correctness --- *)

Timeout 60 Check (FiveCardAnalysis.exec_correct :
  forall (a b : bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile)),
    w0 \in pgg_G (mp_M FiveCardAnalysis.profile) ->
    [/\ (@exec_run FiveCardAnalysis.profile FiveCardAnalysis.exec_plug
           (a, b) w0 0).1
        = nseq (size (@exec_procs FiveCardAnalysis.profile
                        FiveCardAnalysis.exec_plug (a, b) w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints FiveCardAnalysis.profile
                FiveCardAnalysis.exec_plug (a, b) w0 0)
        = (pi_T' (mp_PI FiveCardAnalysis.profile)).+1
      & exec_decode FiveCardAnalysis.exec_plug
          (exec_endpoints_size
             (five_card_exec.five_card_exec_endpoints a b w0)) = a && b]).

Timeout 60 Check (FiveCardAnalysis.exec_recovers :
  forall (a b : bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile)),
    w0 \in pgg_G (mp_M FiveCardAnalysis.profile) ->
    exec_decode FiveCardAnalysis.exec_plug
      (exec_endpoints_size (five_card_exec.five_card_exec_endpoints a b w0))
    = a && b).

Timeout 60 Check (FiveCardAnalysis.observed_recovers :
  forall (x : bool * bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile)),
    w0 \in pgg_G (mp_M FiveCardAnalysis.profile) ->
    exec_decode FiveCardAnalysis.exec_plug
      (OE.oe_endpoints_size FiveCardAnalysis.observed x w0) = x.1 && x.2).

Timeout 60 Check (FiveCardAnalysis.procs_biasE :
  forall (a b : bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile))
    (P_idx : nat),
    @exec_procs FiveCardAnalysis.profile FiveCardAnalysis.exec_plug
      (a, b) w0 P_idx
    = @exec_procs FiveCardAnalysis.profile FiveCardAnalysis.exec_plug
        (a, b) w0 P_idx).

(* --- 6 Security --- *)

Timeout 60 Check (FiveCardAnalysis.exec_trace_secrecy :
  forall R : realType,
    `H( (FiveCardAnalysis.secret R)
      | (FiveCardAnalysis.content_trace R ord0))
    = `H `p_ (FiveCardAnalysis.secret R)).

Timeout 60 Check (FiveCardAnalysis.input_trace_secrecy :
  forall (R : realType) (j : nat),
    `H( (FiveCardAnalysis.secret R) | (FiveCardAnalysis.input_trace R j))
    = `H `p_ (FiveCardAnalysis.secret R)).

Timeout 60 Check (FiveCardAnalysis.dealer_pair_centropy0 :
  forall R : realType,
    `H( [eta fst] | (FiveCardAnalysis.dealer_trace R)) = 0).

Timeout 60 Check (FiveCardAnalysis.dealer_trace_centropy0 :
  forall R : realType,
    `H( (FiveCardAnalysis.secret R) | (FiveCardAnalysis.dealer_trace R))
    = 0).

Timeout 60 Check (FiveCardAnalysis.colour_viewE :
  forall (R : realType) (A : seq nat) (w : five_card_leakage.Omega),
    FiveCardAnalysis.colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)
    = five_card_leakage.ViewA R A w).

Timeout 60 Check (FiveCardAnalysis.colour_view_RV_E :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (A : seq nat),
    (fun w : five_card_leakage.Omega =>
       FiveCardAnalysis.colour_view A w.1 (five_card_group.fc_sigma ^+ w.2))
    = kim_input_privacy.kim_view Hlt Hgt A).

Timeout 60 Check (FiveCardAnalysis.colour_view_leak_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    0 < 5%:R^-1 - `|eps| ->
    forall A : seq nat,
      cond_mutual_info
        (`p_ [% kim_input_privacy.kim_inputs Hlt Hgt,
               (fun w : five_card_leakage.Omega =>
                  FiveCardAnalysis.colour_view A w.1
                    (five_card_group.fc_sigma ^+ w.2)),
               kim_input_privacy.kim_secret Hlt Hgt])
      <= kim_input_privacy.kim_leak_bound eps).

Timeout 60 Check (FiveCardAnalysis.marginal_bound :
  forall R : realType,
    ShuffleMarginalBound R (mp_M FiveCardAnalysis.profile)).

Timeout 60 Check (FiveCardAnalysis.perfect :
  forall R : realType, sw_bound_eps (FiveCardAnalysis.marginal_bound R) = 0).

(* --- bound (endpoint marginal, not security) --- *)

Timeout 60 Check (FiveCardAnalysis.kim_bundle :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps -> `|eps| < 4%:R / 5%:R ->
    nat -> ShuffleCertificateBundle R (mp_M FiveCardAnalysis.profile)).

Timeout 60 Check (FiveCardAnalysis.centi_bundle :
  forall R : realType,
    ShuffleCertificateBundle R (mp_M FiveCardAnalysis.profile)).

Timeout 60 Check (FiveCardAnalysis.endpoint_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    `|eps| < 4%:R / 5%:R ->
    forall (L : nat) (s : 'I_5),
      var_dist
        (endpoint_dist_weighted L five_card_kim.fc_kim_sigmas
           (five_card_kim.kim_weight_dist Hlt Hgt) s)
        (fdist_uniform (card_ord 5))
      <= Num.Def.sqrtr 5%:R * five_card_kim.kim_lambda2 eps ^+ L).

Timeout 60 Check (FiveCardAnalysis.deal_centi_lt :
  forall (R : realType) (s : 'I_5),
    var_dist
      (fdistmap (fun g : {perm 'I_5} => g s)
         (sw_rho_dist (scb_bound (FiveCardAnalysis.centi_bundle R))))
      (fdist_uniform (card_ord 5))
    < 2%:R^-40).

(* --- 7 Transfer: the five-card facade has none, so there is nothing to
   check here; the PGL transfer aliases are checked above. --- *)
