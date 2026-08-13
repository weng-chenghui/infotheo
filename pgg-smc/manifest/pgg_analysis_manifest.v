(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_analysis_manifest: the repository-level analysis manifest              *)
(*                                                                            *)
(* The manifest re-exports the five instance facades, so that one import      *)
(* reaches every public alias of the eight-card orbit instance, the five-card *)
(* development, the five-seat S_5 instance, the ten-seat S_5 x S_5 instance   *)
(* and the four-seat abelian instance, and records one row per analysis path. *)
(* Each row names its protocol instance, probability model, profile,          *)
(* execution, observed-execution and sample aliases, its observers with their *)
(* carriers, its correctness theorem, its security, leakage, mixing or        *)
(* limitation theorem, its static-to-executed bridge and model-transfer       *)
(* theorem when present, the missing model-transfer premise when none is      *)
(* claimed, its exact capability, its completion level and its assumption     *)
(* status.                                                                    *)
(*                                                                            *)
(* Each row is also a typed value of AnalysisPathRow below, carrying the      *)
(* observed execution of the path, its typed model slot apr_model, an         *)
(* AnalysisModelFamily witness mandatory at Sampled and AnalysisBridged and   *)
(* optional below, and the three typed statuses of pgg_analysis_status.v.     *)
(* The record stores no theorem: theorems stay facade aliases and are pinned  *)
(* by spelled type in the checker at the end of this file.                    *)
(*                                                                            *)
(* Completion levels are the constructors of CompletionLevel. They are        *)
(* cumulative and are read off the typed witnesses this manifest names, never *)
(* asserted:                                                                  *)
(*                                                                            *)
(*   Algebraic       profile alias                                            *)
(*   Executable      + execution-plug alias indexed by that profile           *)
(*   Observed        + observed-execution alias indexed by profile and plug   *)
(*   Sampled         + sample-adapter alias AND its distribution-to-observer  *)
(*                    bridge                                                  *)
(*   AnalysisBridged + bridge alias to a named security, leakage, mixing or   *)
(*                    limitation theorem about the same distribution and the  *)
(*                    same observer                                           *)
(*                                                                            *)
(* AnalysisBridged is the typed form of the prose label Security-bridged of   *)
(* the earlier banner. The rename is what lets a negative mixing result       *)
(* classify accurately: the Abelian limitation path is bridged and carries no *)
(* security claim at all.                                                     *)
(*                                                                            *)
(* Three conventions hold throughout the rows.                                *)
(*                                                                            *)
(* (1) The classical trio propositional_extensionality,                       *)
(* functional_extensionality_dep and constructive_indefinite_description is   *)
(* the repository baseline, inherited from boolp through the infotheo         *)
(* probability layer. It is NOT listed in an assumption status. A row is      *)
(* BaselineClassicalOnly when Print Assumptions reports the trio and        *)
(* nothing else, and                                                          *)
(* AcceptsAxioms when it reports named repository assumptions beyond it. The  *)
(* three constructors of PggAxiom are the only such assumptions, and a status *)
(* covers the public results of the path, not only the values the row stores. *)
(*                                                                            *)
(* (2) Completion levels are cumulative and are stated at the level the       *)
(* theorems actually reach. The two limitation families differ on this point  *)
(* and stay at different levels: the S_5 x S_5 limitation rows stay Sampled   *)
(* because their floors are stated at the sheet-endpoint reader of the        *)
(* word-cut distribution, which is a pushforward of that distribution and not *)
(* an interpreter-executed content observer, while the Abelian limitation row *)
(* is AnalysisBridged because its distance-one theorem is stated at the two   *)
(* adapters' own executed observation.                                        *)
(*                                                                            *)
(* (3) A capability line uses the narrowest label the theorem statement       *)
(* supports, from the list of section 11 of the request: correctness, exact   *)
(* privacy, approximate privacy, trace secrecy, conditional entropy, mutual   *)
(* information, endpoint marginal mixing, negative mixing result, anonymity   *)
(* or privacy limitation. A theorem conditional on the trusted analytical     *)
(* certificate s5_rayleigh_Q2_R is described as conditional in every          *)
(* capability line that depends on it. A limitation theorem carrying a        *)
(* security role tag is a mixing limitation, never a privacy failure.         *)
(*                                                                            *)
(* Every identifier in the tables below is checked at the end of this file by *)
(* one Timeout-guarded Check against its spelled type, and every row by one   *)
(* Check against AnalysisPathRow together with three erefl pins on its status *)
(* fields. Deleting an alias makes its line fail with a reference-not-found   *)
(* message, retyping one makes it fail with a type mismatch and restatusing a *)
(* row makes its pin fail, so the tables cannot drift away from the code.     *)
(******************************************************************************)

From pgg_smc Require Export pgl27_analysis five_card_analysis s5_analysis
                            s5x5_analysis abelian_analysis.

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
(* | correctness theorem  | PGL27Analysis.observed_recovers |                 *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | none: the path compares no idealized model, its   *)
(*                          shuffle being the exact uniform distribution on   *)
(*                          the group already |                               *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | pgl27_row_exact |                                 *)
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
(* AnalysisBridged.                                                           *)
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
(* | correctness theorem  | PGL27Analysis.observed_recovers |                 *)
(* | model transfer       | PGL27Analysis.var_dist_transfer, discharged at    *)
(*                          this instance by                                  *)
(*                          PGL27Analysis.word_view_indist_via_transfer |     *)
(* | missing premise      | none: PGL27Analysis.word_mixing supplies the      *)
(*                          base-distribution bound the generic transfer      *)
(*                          inequality needs, on the cut carrier itself |     *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | IdealFinite |                                     *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | pgl27_row_word |                                  *)
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
(* executed content reader, giving AnalysisBridged at both executed           *)
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
(* | correctness theorem  | FiveCardAnalysis.observed_recovers |              *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | the ideal distribution equality: the second       *)
(*                          hypothesis of var_dist_fdistmap_transfer, an      *)
(*                          equality of two reader pushforwards under an      *)
(*                          ideal distribution, which the five-card           *)
(*                          development does not supply |                     *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | five_card_row_uniform |                           *)
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
(* row's cut distribution; the row is AnalysisBridged with the trace          *)
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
(* | correctness theorem  | FiveCardAnalysis.observed_recovers |              *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | the ideal distribution equality, as in row 3 |    *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | five_card_row_biased |                            *)
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
(* itself, over that same biased distribution, giving AnalysisBridged.        *)
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
(* | correctness theorem  | FiveCardAnalysis.observed_recovers |              *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | the ideal distribution equality, as in row 3, and *)
(*                          in addition no security statement is attached to  *)
(*                          either model |                                    *)
(* | completion level     | Sampled |                                         *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | five_card_row_repeated |                          *)
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
(* AnalysisBridged. endpoint_bound and deal_centi_lt bound the distance       *)
(* from uniform of ONE seat's endpoint distribution: neither quantifies over  *)
(* a coalition, neither mentions a second secret, and neither has the shape   *)
(* of an indistinguishability or leakage statement. A ShuffleCertificate-     *)
(* Bundle exists for both models and does not raise the level.                *)
(*                                                                            *)
(*     Row 6: five-seat S_5 instance, deterministic dealt position            *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | five-seat S_5 path-generated instance |           *)
(* | probability model    | none: the path is distribution-free |             *)
(* | profile alias        | S5Analysis.profile |                              *)
(* | execution alias      | S5Analysis.exec_plug |                            *)
(* | observed alias       | S5Analysis.observed |                             *)
(* | sample alias         | none |                                            *)
(* | observers            | S5Analysis.seat_endpoint : 'I_5, executed;        *)
(*                          S5Analysis.coalition_endpoints                    *)
(*                            : {ffun 'I_5 -> 'I_5}, executed;                *)
(*                          S5Analysis.verifier_endpoints : seq 'I_5,         *)
(*                            executed;                                       *)
(*                          S5Analysis.verifier_trace,                        *)
(*                          S5Analysis.player_raw_trace : message lists,      *)
(*                            navigation only, not random variables |         *)
(* | distribution-to-observer bridges | none: the path has no sample layer |  *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | S5Analysis.exec_correct, S5Analysis.exec_recovers,*)
(*                          S5Analysis.observed_recovers |                    *)
(* | security, leakage, mixing or limitation theorem | none |                 *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | not applicable: the path names no model, so there *)
(*                          is no distribution to compare with an idealized   *)
(*                          one |                                             *)
(* | completion level     | Observed |                                        *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | AcceptsAxioms [:: AxS5GroupOrder] |               *)
(* | typed row            | s5_row_det |                                      *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. profile gives Algebraic; exec_plug is indexed by that *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed. No sample adapter stands over this      *)
(* plug, so the row stops at Observed with an empty optional model slot. The  *)
(* assumption status is the group-order assumption of the instance:           *)
(* Print Assumptions on the row reports s5_group_order_eq beyond the          *)
(* classical trio, because the profile's threshold data is proved from the    *)
(* order of the generated group.                                              *)
(*                                                                            *)
(*     Row 7: five-seat S_5 instance, randomized additive sharing             *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | five-seat S_5 path-generated instance |           *)
(* | probability model    | uniform independent tape 'rV['Z_5]_5 with the     *)
(*                          identity cut |                                    *)
(* | profile alias        | S5Analysis.profile |                              *)
(* | execution alias      | S5Analysis.rand_exec_plug |                       *)
(* | observed alias       | S5Analysis.rand_observed |                        *)
(* | sample alias         | S5Analysis.rand_sample |                          *)
(* | observers            | S5Analysis.rand_content_trace R i : 'I_5, a       *)
(*                            random variable on the tape distribution,       *)
(*                            executed;                                       *)
(*                          sa_coalition_view of rand_sample at offset zero   *)
(*                            : {ffun 'I_5 -> 'I_5}, executed;                *)
(*                          S5Analysis.rand_seat_endpoint : 'I_5, executed;   *)
(*                          S5Analysis.rand_verifier_endpoints : seq 'I_5;    *)
(*                          the secret is rsh_secret of the randomized        *)
(*                            sharing, carrier 'Z_5 |                         *)
(* | distribution-to-observer bridges | S5Analysis.rand_cut_distE,            *)
(*                          S5Analysis.rand_content_traceE,                   *)
(*                          S5Analysis.rand_coalition_viewE |                 *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | S5Analysis.rand_correct,                          *)
(*                          S5Analysis.rand_recovers,                         *)
(*                          S5Analysis.rand_observed_recovers |               *)
(* | security, leakage, mixing or limitation theorem                          *)
(*                        | S5Analysis.exec_trace_secrecy,                    *)
(*                          S5Analysis.exec_coalition_secrecy |               *)
(* | final bridge theorem | S5Analysis.exec_coalition_secrecy |               *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | none is needed: the path states exact results at  *)
(*                          its own executed observers and compares no        *)
(*                          idealized model |                                 *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | AcceptsAxioms [:: AxS5GroupOrder] |               *)
(* | typed row            | s5_row_rand |                                     *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exec_coalition_secrecy | the uniform tape distribution of rand_sample    *)
(*   | sa_coalition_view of rand_sample at offset zero, executed              *)
(*   | exact privacy: zero mutual information, and conditional entropy equal  *)
(*     to entropy, for a coalition of fewer than five seats |                 *)
(* | exec_trace_secrecy | the same distribution                               *)
(*   | rand_content_trace R i, executed | trace secrecy |                     *)
(* | rand_observed_recovers | none, the statement is distribution-free        *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. profile, rand_exec_plug and rand_observed give the    *)
(* first three levels. rand_sample is a SampleAdapter over rand_exec_plug and *)
(* rand_cut_distE names its cut distribution, giving Sampled.                 *)
(* exec_coalition_secrecy is stated at sa_coalition_view of rand_sample       *)
(* itself, so the theorem's distribution and observer are the row's own,      *)
(* giving AnalysisBridged. The two reader equalities rand_content_traceE and  *)
(* rand_coalition_viewE identify those executed observers with the static     *)
(* readers of s5_trace and s5_secrecy, which is the content of the            *)
(* StaticExecutedOnly status:                                                 *)
(* results travel from the static layer to the executed one, and no           *)
(* idealized model is compared.                                               *)
(*                                                                            *)
(*     Row 8: five-seat S_5 instance, finite generator word                   *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | five-seat S_5 path-generated instance |           *)
(* | probability model    | the product of an arbitrary secret prior with the *)
(*                          uniform distribution on generator words of length *)
(*                          L, the cut being the word's evaluation in S_5 |   *)
(* | profile alias        | S5Analysis.profile |                              *)
(* | execution alias      | S5Analysis.exec_plug |                            *)
(* | observed alias       | S5Analysis.observed |                             *)
(* | sample alias         | S5Analysis.word_sample at a secret prior and a    *)
(*                          word length; the row's typed model witness is     *)
(*                          S5Analysis.word_family, the family indexed by     *)
(*                          exactly that prior and that length |              *)
(* | observers            | one position's endpoint distribution, the         *)
(*                          pushforward of the cut distribution along the     *)
(*                          evaluation of a permutation at that position,     *)
(*                          carrier 'I_5 |                                    *)
(* | distribution-to-observer bridges | S5Analysis.word_cut_distE,            *)
(*                          S5Analysis.word_cut_imageE |                      *)
(* | bound or certificate | S5Analysis.word_endpoint_bound |                  *)
(* | correctness theorem  | S5Analysis.observed_recovers, shared with row 6:  *)
(*                          the model stands over the same plug |             *)
(* | security, leakage, mixing or limitation theorem | none |                 *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | S5Analysis.word_transfer_conditional, the generic *)
(*                          inequality under the premise below, and no        *)
(*                          unconditional transfer theorem |                  *)
(* | missing premise      | S5Analysis.word_missing_premise: a bound          *)
(*                          var_dist (sa_cut_dist (word_sample secretP L)) Q  *)
(*                          <= delta on the cut carrier {perm 'I_5}, against  *)
(*                          a named reference distribution Q |                *)
(* | completion level     | Sampled |                                         *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R] |*)
(* | typed row            | s5_row_word |                                     *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | word_endpoint_bound | the cut distribution of word_sample, named by      *)
(*   word_cut_distE | one position's endpoint distribution                    *)
(*   | endpoint marginal mixing, conditional on s5_rayleigh_Q2_R |            *)
(*                                                                            *)
(* Level justification. word_sample is a SampleAdapter over exec_plug and     *)
(* word_cut_distE names its cut distribution, giving Sampled. The row is NOT  *)
(* AnalysisBridged: word_endpoint_bound bounds the distance from uniform of   *)
(* ONE position's endpoint distribution, quantifies over no coalition,        *)
(* mentions no second secret and has neither the shape of an                  *)
(* indistinguishability statement nor that of a leakage statement. No         *)
(* finite-word coalition claim is made anywhere on this path. The bound is    *)
(* conditional on the trusted analytical certificate s5_rayleigh_Q2_R, which  *)
(* is why the assumption status of this row lists AxRayleighQ2R next to the   *)
(* instance's group-order assumption.                                         *)
(*                                                                            *)
(*     Row 9: ten-seat S_5 x S_5 instance, deterministic dealt position       *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | ten-seat two-pile S_5 x S_5 instance |            *)
(* | probability model    | none: the path is distribution-free |             *)
(* | profile alias        | S5x5Analysis.profile |                            *)
(* | execution alias      | S5x5Analysis.exec_plug |                          *)
(* | observed alias       | S5x5Analysis.observed |                           *)
(* | sample alias         | none |                                            *)
(* | observers            | S5x5Analysis.seat_endpoint : 'I_10, executed;     *)
(*                          S5x5Analysis.coalition_endpoints                  *)
(*                            : {ffun 'I_10 -> 'I_10}, executed;              *)
(*                          S5x5Analysis.verifier_endpoints : seq 'I_10;      *)
(*                          S5x5Analysis.verifier_trace,                      *)
(*                          S5x5Analysis.player_raw_trace : message lists,    *)
(*                            navigation only, not random variables |         *)
(* | distribution-to-observer bridges | none: the path has no sample layer |  *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | S5x5Analysis.exec_correct,                        *)
(*                          S5x5Analysis.exec_recovers,                       *)
(*                          S5x5Analysis.observed_recovers |                  *)
(* | security, leakage, mixing or limitation theorem | none |                 *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | not applicable: the path names no model |         *)
(* | completion level     | Observed |                                        *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | AcceptsAxioms [:: AxS5x5GroupOrder] |             *)
(* | typed row            | s5x5_row_det |                                    *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. As in row 6: profile, plug and observed value give    *)
(* the first three levels and no sample adapter stands over this plug. The    *)
(* assumption status is the instance's own group-order assumption:            *)
(* Print Assumptions on the row reports s5x5_group_order_eq and not the S_5   *)
(* one.                                                                       *)
(*                                                                            *)
(*     Row 10: ten-seat S_5 x S_5 instance, randomized two-pile sharing       *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | ten-seat two-pile S_5 x S_5 instance |            *)
(* | probability model    | the product of two uniform independent tapes,     *)
(*                          one per pile, with the identity cut |             *)
(* | profile alias        | S5x5Analysis.profile |                            *)
(* | execution alias      | S5x5Analysis.rand_exec_plug |                     *)
(* | observed alias       | S5x5Analysis.rand_observed |                      *)
(* | sample alias         | S5x5Analysis.rand_sample |                        *)
(* | observers            | S5x5Analysis.rand_content_trace R j : 'I_10, a    *)
(*                            random variable on the product tape             *)
(*                            distribution, executed;                         *)
(*                          S5x5Analysis.pile1_seat_view,                     *)
(*                          S5x5Analysis.pile2_seat_view : 'Z_5, one party's  *)
(*                            executed share in its own pile;                 *)
(*                          S5x5Analysis.pile1_coalition_view,                *)
(*                          S5x5Analysis.pile2_coalition_view                 *)
(*                            : {ffun 'I_5 -> 'Z_5}, one pile coalition's     *)
(*                            executed shares, indexed by that pile's five    *)
(*                            parties;                                        *)
(*                          S5x5Analysis.joint_view : the pair of the two,    *)
(*                            the two pile memberships kept separate;         *)
(*                          the secret is JointSecret, the pile pair |        *)
(* | distribution-to-observer bridges | S5x5Analysis.rand_cut_distE,          *)
(*                          S5x5Analysis.rand_content_traceE,                 *)
(*                          S5x5Analysis.rand_pile1_seat_viewE,               *)
(*                          S5x5Analysis.rand_pile2_seat_viewE,               *)
(*                          S5x5Analysis.rand_pile1_viewE,                    *)
(*                          S5x5Analysis.rand_pile2_viewE,                    *)
(*                          S5x5Analysis.rand_joint_viewE |                   *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | S5x5Analysis.rand_correct,                        *)
(*                          S5x5Analysis.rand_recovers,                       *)
(*                          S5x5Analysis.rand_observed_recovers, recovering   *)
(*                          the 'I_10 image of the pile pair, with            *)
(*                          S5x5Analysis.combine_not_injectiveE recording     *)
(*                          that the image is not the pair |                  *)
(* | security, leakage, mixing or limitation theorem                          *)
(*                        | S5x5Analysis.exec_trace_secrecy,                  *)
(*                          S5x5Analysis.exec_p1_secrecy,                     *)
(*                          S5x5Analysis.exec_p2_secrecy,                     *)
(*                          S5x5Analysis.exec_joint_secrecy |                 *)
(* | final bridge theorem | S5x5Analysis.exec_joint_secrecy |                 *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | none is needed: the path states exact results at  *)
(*                          its own executed observers |                      *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | AcceptsAxioms [:: AxS5x5GroupOrder] |             *)
(* | typed row            | s5x5_row_rand |                                   *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exec_joint_secrecy | the product tape distribution of rand_sample        *)
(*   | joint_view R C1 C2, executed | exact privacy of the pile pair: zero    *)
(*     mutual information, and conditional entropy equal to entropy, under    *)
(*     the two per-pile cardinality bounds |                                  *)
(* | exec_p1_secrecy, exec_p2_secrecy | the same distribution                 *)
(*   | pile1_coalition_view, pile2_coalition_view, executed                   *)
(*   | exact privacy of the pile pair against one sub-threshold pile          *)
(*     coalition |                                                            *)
(* | exec_trace_secrecy | the same distribution                               *)
(*   | rand_content_trace R j, executed | trace secrecy |                     *)
(* | rand_observed_recovers | none, the statement is distribution-free        *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. As in row 7, the first four levels come from profile, *)
(* rand_exec_plug, rand_observed, rand_sample and rand_cut_distE.             *)
(* exec_joint_secrecy is stated at joint_view, an executed reader of          *)
(* rand_sample, over that same distribution, giving AnalysisBridged. The      *)
(* joint statement is proved as such and is not inferred from the two         *)
(* per-pile ones, and no alias flattens the two piles into one ten-seat       *)
(* coalition.                                                                 *)
(*                                                                            *)
(*     Row 11: ten-seat S_5 x S_5 instance, finite word inside the first pile *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | ten-seat two-pile S_5 x S_5 instance |            *)
(* | probability model    | the product of an arbitrary secret prior with the *)
(*                          uniform distribution on generator words of length *)
(*                          L, the cut being the word's evaluation in         *)
(*                          S_5 x S_5 |                                       *)
(* | profile alias        | S5x5Analysis.profile |                            *)
(* | execution alias      | S5x5Analysis.exec_plug |                          *)
(* | observed alias       | S5x5Analysis.observed |                           *)
(* | sample alias         | S5x5Analysis.word_sample at a secret prior and a  *)
(*                          word length; the row's typed model witness is     *)
(*                          S5x5Analysis.word_family |                        *)
(* | observers            | one first-pile position's endpoint distribution,  *)
(*                          the pushforward of the cut distribution along the *)
(*                          evaluation of a permutation at the ten-seat image *)
(*                          of that pile position, carrier 'I_10 |            *)
(* | distribution-to-observer bridges | S5x5Analysis.word_cut_distE |         *)
(* | bound or certificate | S5x5Analysis.word_pile1_bound |                   *)
(* | correctness theorem  | S5x5Analysis.observed_recovers, shared with row 9 *)
(*                          | *)
(* | security, leakage, mixing or limitation theorem | none |                 *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | S5x5Analysis.word_transfer_conditional, under the *)
(*                          premise below |                                   *)
(* | missing premise      | S5x5Analysis.word_missing_premise: a bound        *)
(*                          var_dist (sa_cut_dist (word_sample secretP L)) Q  *)
(*                          <= delta on the cut carrier {perm 'I_10} |        *)
(* | completion level     | Sampled |                                         *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status                                                        *)
(*     | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |                 *)
(* | typed row            | s5x5_row_pile1_word |                             *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | word_pile1_bound | the cut distribution of word_sample, named by         *)
(*   word_cut_distE | one first-pile position's endpoint distribution         *)
(*   | endpoint marginal mixing inside the first pile, against the uniform    *)
(*     distribution on that pile, conditional on s5_rayleigh_Q2_R |           *)
(*                                                                            *)
(* Level justification. word_sample is a SampleAdapter over exec_plug and     *)
(* word_cut_distE names its cut distribution, giving Sampled. The row is NOT  *)
(* AnalysisBridged, for the reason of row 8: the bound is about one           *)
(* position's endpoint distribution. No joint finite-word privacy theorem is  *)
(* claimed on this instance. The bound is conditional on s5_rayleigh_Q2_R.    *)
(*                                                                            *)
(*     Row 12: ten-seat S_5 x S_5 instance, finite word inside the second     *)
(*             pile                                                           *)
(*                                                                            *)
(* Every field is that of row 11 with the second pile in place of the first:  *)
(* the observer is one second-pile position's endpoint distribution, reached  *)
(* through the ten-seat image of that pile position, and the bound is         *)
(* S5x5Analysis.word_pile2_bound against the uniform distribution on the      *)
(* second pile. Transfer status NoModelComparison with the same missing       *)
(* premise, completion level Sampled, assumption status                       *)
(* AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R], typed row              *)
(* s5x5_row_pile2_word.                                                       *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | word_pile2_bound | the cut distribution of word_sample, named by         *)
(*   word_cut_distE | one second-pile position's endpoint distribution        *)
(*   | endpoint marginal mixing inside the second pile, against the uniform   *)
(*     distribution on that pile, conditional on s5_rayleigh_Q2_R |           *)
(*                                                                            *)
(*     Row 13: ten-seat S_5 x S_5 instance, first pile against global uniform *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | ten-seat two-pile S_5 x S_5 instance |            *)
(* | probability model    | the finite-word model of row 11 |                 *)
(* | profile alias        | S5x5Analysis.profile |                            *)
(* | execution alias      | S5x5Analysis.exec_plug |                          *)
(* | observed alias       | S5x5Analysis.observed |                           *)
(* | sample alias         | S5x5Analysis.word_sample; the row's typed model   *)
(*                          witness is S5x5Analysis.word_family, as in row    *)
(*                          11 |                                              *)
(* | observers            | one first-pile position's endpoint distribution,  *)
(*                          carrier 'I_10, now compared with the uniform      *)
(*                          distribution on all ten seats |                   *)
(* | distribution-to-observer bridges | S5x5Analysis.word_cut_distE |         *)
(* | bound or certificate | S5x5Analysis.word_pile1_bound, and the companion  *)
(*                          upper bound S5x5Analysis.word_seat_bound, which   *)
(*                          quantifies over all ten positions and whose       *)
(*                          leading summand one is the distance between a     *)
(*                          pile-uniform distribution and global uniform |    *)
(* | correctness theorem  | S5x5Analysis.observed_recovers, shared with row 9 *)
(*                          | *)
(* | security, leakage, mixing or limitation theorem                          *)
(*                        | S5x5Analysis.word_pile1_floor,                    *)
(*                          S5x5Analysis.word_pile1_floor_gt0, with the       *)
(*                          regime named by                                   *)
(*                          S5x5Analysis.word_positive_regime |               *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | S5x5Analysis.word_pile1_floor: a lower bound on   *)
(*                          the distance from global uniform, transported to  *)
(*                          this row's own observer by the reverse triangle   *)
(*                          inequality |                                      *)
(* | missing premise      | not applicable to the limitation, which is proved *)
(*                          rather than assumed; the absent premise of the    *)
(*                          POSITIVE direction remains the one of row 11 |    *)
(* | completion level     | Sampled |                                         *)
(* | transfer status      | NegativeTransfer |                                *)
(* | assumption status                                                        *)
(*     | AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] |                 *)
(* | typed row            | s5x5_row_pile1_limitation |                       *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | word_pile1_floor | the cut distribution of word_sample                   *)
(*   | one first-pile position's endpoint distribution                        *)
(*   | negative mixing result: the distance from global uniform is at least   *)
(*     one minus the pile mixing factor, conditional on s5_rayleigh_Q2_R |    *)
(* | word_pile1_floor_gt0 | the same distribution | the same observer         *)
(*   | negative mixing result in its non-vacuous regime, word length at least *)
(*     seventeen, conditional on s5_rayleigh_Q2_R |                           *)
(*                                                                            *)
(* Level justification. The row stays Sampled and does not reach              *)
(* AnalysisBridged. Its floors are stated at the sheet-endpoint reader of the *)
(* word-cut distribution, which is a pushforward of that distribution, and    *)
(* not at an interpreter-executed content observer of this instance: no       *)
(* reader equality carries them to one. The status is still NegativeTransfer, *)
(* because a theorem does transport an obstruction to the row's own observer; *)
(* the level and the status answer different questions. The result is a       *)
(* mixing limitation about the shuffle, not a privacy failure of the          *)
(* protocol, and it says nothing about any coalition.                         *)
(*                                                                            *)
(*     Row 14: ten-seat S_5 x S_5 instance, second pile against global        *)
(*             uniform                                                        *)
(*                                                                            *)
(* Every field is that of row 13 with the second pile in place of the first:  *)
(* the theorems are S5x5Analysis.word_pile2_floor and                         *)
(* S5x5Analysis.word_pile2_floor_gt0 at one second-pile position's endpoint   *)
(* distribution, with the same companion bounds, the same regime, completion  *)
(* level Sampled, transfer status NegativeTransfer, assumption status         *)
(* AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R] and typed row           *)
(* s5x5_row_pile2_limitation.                                                 *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | word_pile2_floor | the cut distribution of word_sample                   *)
(*   | one second-pile position's endpoint distribution                       *)
(*   | negative mixing result: the distance from global uniform is at least   *)
(*     one minus the pile mixing factor, conditional on s5_rayleigh_Q2_R |    *)
(* | word_pile2_floor_gt0 | the same distribution | the same observer         *)
(*   | negative mixing result in its non-vacuous regime, word length at least *)
(*     seventeen, conditional on s5_rayleigh_Q2_R |                           *)
(*                                                                            *)
(*     Row 15: four-seat abelian instance, secret recovery                    *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | four-seat abelian two-generator instance |        *)
(* | probability model    | none: the path is distribution-free |             *)
(* | profile alias        | AbelianAnalysis.profile |                         *)
(* | execution alias      | AbelianAnalysis.exec_plug |                       *)
(* | observed alias       | AbelianAnalysis.observed |                        *)
(* | sample alias         | none |                                            *)
(* | observers            | AbelianAnalysis.seat_endpoint : 'I_4, executed;   *)
(*                          AbelianAnalysis.verifier_endpoints : seq 'I_4;    *)
(*                          AbelianAnalysis.verifier_trace,                   *)
(*                          AbelianAnalysis.player_raw_trace : message lists, *)
(*                            navigation only, not random variables |         *)
(* | distribution-to-observer bridges | none: the path has no sample layer |  *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | AbelianAnalysis.exec_correct,                     *)
(*                          AbelianAnalysis.exec_recovers,                    *)
(*                          AbelianAnalysis.observed_recovers |               *)
(* | security, leakage, mixing or limitation theorem | none |                 *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | not applicable: the path names no model |         *)
(* | completion level     | Observed |                                        *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | abel_row_recovery |                               *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | the executed endpoint list | correctness, for every secret in 'I_4 and *)
(*     every cut in the generated group |                                     *)
(*                                                                            *)
(* Level justification. profile, exec_plug and observed give the first three  *)
(* levels; no sample adapter stands over this plug, the two shuffle models    *)
(* standing over the identity-content plug of rows 16 and 17.                 *)
(*                                                                            *)
(*     Row 16: four-seat abelian instance, identity card content              *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | four-seat abelian two-generator instance |        *)
(* | probability model    | none on this row: the run argument is the unit    *)
(*                          and carries no randomness |                       *)
(* | profile alias        | AbelianAnalysis.profile |                         *)
(* | execution alias      | AbelianAnalysis.shuffle_plug |                    *)
(* | observed alias       | AbelianAnalysis.shuffle_observed |                *)
(* | sample alias         | none on this row |                                *)
(* | observers            | AbelianAnalysis.endpoint_vector                   *)
(*                            : 4.-tuple 'I_4, the complete four-endpoint     *)
(*                            observation of a cut, injective on all of       *)
(*                            {perm 'I_4} by                                  *)
(*                            AbelianAnalysis.endpoint_vector_inj |           *)
(* | distribution-to-observer bridges | none on this row |                    *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | AbelianAnalysis.shuffle_recovers |                *)
(* | security, leakage, mixing or limitation theorem | none |                 *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | not applicable: this row makes no model claim,    *)
(*                          the models of the same plug being row 17's |      *)
(* | completion level     | Observed |                                        *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | abel_row_identity |                               *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | shuffle_recovers | none, the statement is distribution-free              *)
(*   | the executed endpoint list | correctness: the run decodes to the       *)
(*     constant abel_identity_recon_value at every cut in the generated       *)
(*     group. The plug deals identity card content and no secret, so this is  *)
(*     a constant-recovery statement and not an arbitrary-secret one |        *)
(*                                                                            *)
(* Level justification. The row is Observed: it names a profile, a plug and   *)
(* an observed execution and attaches no distribution of its own. The two     *)
(* adapters that stand over this same plug belong to row 17, where the        *)
(* probability lives.                                                         *)
(*                                                                            *)
(*     Row 17: four-seat abelian instance, fixed-length mixing limitation     *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | four-seat abelian two-generator instance |        *)
(* | probability model    | two models on the identity-content plug: the      *)
(*                          ideal one, uniform on the four-element generated  *)
(*                          group, and the actual one, the uniform            *)
(*                          distribution on generator words of length L + 1   *)
(*                          evaluated in that group |                         *)
(* | profile alias        | AbelianAnalysis.profile |                         *)
(* | execution alias      | AbelianAnalysis.shuffle_plug |                    *)
(* | observed alias       | AbelianAnalysis.shuffle_observed |                *)
(* | sample alias         | AbelianAnalysis.word_sample at word length L; the *)
(*                          row's typed model witness is the length-indexed   *)
(*                          AbelianAnalysis.word_family, and the ideal model  *)
(*                          stays the facade alias                            *)
(*                          AbelianAnalysis.ideal_sample |                    *)
(* | observers            | AbelianAnalysis.endpoint_vector                   *)
(*                            : 4.-tuple 'I_4, the complete four-endpoint     *)
(*                            executed observation, read on each model's own  *)
(*                            sample space |                                  *)
(* | distribution-to-observer bridges | AbelianAnalysis.actual_cut_distE,     *)
(*                          AbelianAnalysis.sample_reader_distE |             *)
(* | bound or certificate | none: the row states an exact distance, not a     *)
(*                          bound |                                           *)
(* | correctness theorem  | AbelianAnalysis.shuffle_recovers, shared with row *)
(*                          16 |                                              *)
(* | security, leakage, mixing or limitation theorem                          *)
(*                        | AbelianAnalysis.word_mixing_limitation, with its  *)
(*                          group form AbelianAnalysis.word_group_dist and    *)
(*                          its static form AbelianAnalysis.executed_distance *)
(*                          | *)
(* | final bridge theorem | AbelianAnalysis.word_mixing_limitation, the same  *)
(*                          statement as                                      *)
(*                          AbelianAnalysis.executed_observation_distance |   *)
(* | model transfer       | AbelianAnalysis.word_mixing_limitation: the       *)
(*                          comparison of the two models is carried to the    *)
(*                          executed observer, and it is negative |           *)
(* | missing premise      | not applicable: the comparison is proved, and its *)
(*                          conclusion excludes any bound below one |         *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | NegativeTransfer |                                *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | abel_row_limitation |                             *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | word_mixing_limitation | the two models' own sample distributions        *)
(*   | endpoint_vector, read through abel_sample_reader on each sample space, *)
(*     executed | negative mixing result: full-L1 distance exactly one at     *)
(*     every finite word length |                                             *)
(* | word_group_dist | the two cut distributions on the generated group       *)
(*   | none, the statement is about the distributions themselves              *)
(*   | negative mixing result, full-L1 distance one |                         *)
(* | executed_distance | the same two cut distributions                       *)
(*   | endpoint_vector | negative mixing result, full-L1 distance one |       *)
(*                                                                            *)
(* Level justification, stated explicitly because this row is a limitation    *)
(* row that DOES reach AnalysisBridged while the S_5 x S_5 limitation rows do *)
(* not. ideal_sample and word_sample are SampleAdapters over shuffle_plug and *)
(* actual_cut_distE names the second one's cut distribution, giving Sampled.  *)
(* word_mixing_limitation is stated at fdistmap of abel_sample_reader over    *)
(* sa_sampleP of those two adapters, that is at the adapters' own executed    *)
(* observation, so the theorem's distributions and observer are the row's     *)
(* own, giving AnalysisBridged. The theorem is a fixed-length mixing          *)
(* limitation about the shuffle. It is not a privacy failure, it is not an    *)
(* unqualified protocol failure, and the instance carries no privacy result   *)
(* at all, positive or negative.                                              *)
(*                                                                            *)
(*     Aliases carrying no capability yet                                     *)
(*                                                                            *)
(* These are public observers and correctness statements of the five facades  *)
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
(* | S5Analysis | profile_k, seat_endpoint, coalition_endpoints,              *)
(*                verifier_trace, verifier_endpoints, player_raw_trace,       *)
(*                rand_seat_endpoint, rand_coalition_endpoints,               *)
(*                rand_verifier_trace, rand_verifier_endpoints,               *)
(*                rand_player_raw_trace, exec_correct, exec_recovers,         *)
(*                rand_correct, rand_recovers, word_cut_imageE,               *)
(*                word_transfer_conditional |                                 *)
(* | S5x5Analysis | profile_k, seat_endpoint, coalition_endpoints,            *)
(*                  verifier_trace, verifier_endpoints, player_raw_trace,     *)
(*                  rand_seat_endpoint, rand_coalition_endpoints,             *)
(*                  rand_verifier_trace, rand_verifier_endpoints,             *)
(*                  rand_player_raw_trace, pile1_seats, pile2_seats,          *)
(*                  pile1_seat_view, pile2_seat_view, exec_correct,           *)
(*                  exec_recovers, rand_correct, rand_recovers,               *)
(*                  combine_not_injectiveE, word_transfer_conditional |       *)
(* | AbelianAnalysis | profile_k, seat_endpoint, verifier_trace,              *)
(*                     verifier_endpoints, player_raw_trace,                  *)
(*                     endpoint_vector_inj, exec_correct, exec_recovers |     *)
(*                                                                            *)
(*     Absent capabilities                                                    *)
(*                                                                            *)
(* No row is filled with a dummy theorem, an option-valued proof, an axiom or *)
(* a placeholder, no endpoint marginal bound is recorded as a privacy or      *)
(* security capability, and every path whose transfer status is               *)
(* NoModelComparison or StaticExecutedOnly names the premise it lacks.        *)
(*                                                                            *)
(* Five-card development. No transfer-layer result exists: section 7 of its   *)
(* facade carries typed status aliases and no theorem. The absent premise is  *)
(* the second hypothesis of var_dist_fdistmap_transfer, an equality of two    *)
(* reader pushforwards under an ideal distribution, which the development     *)
(* does not supply.                                                           *)
(*                                                                            *)
(* S_5 finite-word path (row 8). The absent premise is                        *)
(* S5Analysis.word_missing_premise, that is                                   *)
(* var_dist (sa_cut_dist (S5Analysis.word_sample secretP L)) Q <= delta on    *)
(* the cut carrier {perm 'I_5}, against a named reference distribution Q.     *)
(* S5Analysis.word_endpoint_bound bounds a pushforward on the carrier 'I_5    *)
(* instead, which does not discharge it. For Q the uniform distribution on the*)
(* generated group the premise is moreover UNSATISFIABLE at every delta below *)
(* one: every generator of this instance is a transposition, so a word of     *)
(* length L evaluates into the coset of the alternating subgroup determined   *)
(* by the parity of L, and the cut distribution has full-L1 distance one from *)
(* group uniform. That sign-coset confinement is the phenomenon row 17 proves *)
(* inside its own group; it is not formalized at S_5, and no theorem of this  *)
(* repository asserts it there.                                               *)
(*                                                                            *)
(* S_5 x S_5 finite-word paths (rows 11 to 14). The absent premise is the     *)
(* twin of the previous one on the carrier {perm 'I_10}, namely               *)
(* S5x5Analysis.word_missing_premise, that is                                 *)
(* var_dist (sa_cut_dist (S5x5Analysis.word_sample secretP L)) Q <= delta.    *)
(* It is unsatisfiable for Q the uniform distribution on the generated group  *)
(* for the same reason, every generator of this instance being a transposition*)
(* of the ten positions. The per-pile bounds of rows 11 and 12 are not        *)
(* affected: they are taken against the uniform distribution on one pile,     *)
(* which the confinement argument does not reach.                             *)
(******************************************************************************)

(******************************************************************************)
(*     The typed rows                                                         *)
(******************************************************************************)

(** AnalysisPathRow — one analysis path of the repository.
    Kind: interface.
    A constructor supplies the observed execution apr_observed of the path,
    which carries its profile and its execution plug as projections, the
    completion level apr_completion, the model slot apr_model, whose type
    AnalysisModelSlot makes a typed model-family witness mandatory at
    Sampled and AnalysisBridged and optional below, and the two remaining
    statuses apr_transfer and apr_assumptions. The record stores no theorem:
    theorems are facade aliases, pinned by spelled type in the checker
    below. *)
Record AnalysisPathRow := MkAnalysisPathRow {
  (* apr_observed is the executed run of the path together with its static
     observation and the value it recovers. *)
  apr_observed    : OE.ObservedExecution ;
  (* apr_completion is the level the path's theorems actually reach. *)
  apr_completion  : CompletionLevel ;
  (* apr_model is the path's typed model evidence: an AnalysisModelFamily
     over the row's own observed execution, mandatory at Sampled and
     AnalysisBridged, optional at the three lower levels. A parameterized
     model is carried as a family with its real index type, never as an
     empty slot. *)
  apr_model       : AnalysisModelSlot apr_observed apr_completion ;
  (* apr_transfer is the relation the path establishes between its executed
     model and an idealized one. *)
  apr_transfer    : TransferStatus ;
  (* apr_assumptions is the assumption status of the path's public results,
     the classical trio of the repository baseline excluded. *)
  apr_assumptions : AssumptionStatus ;
}.

(** pgl27_row_exact — row 1: the eight-card orbit instance under its exact
    uniform shuffle.
    @intent: the observed execution of that instance, its exact-uniform
    model family, and the statuses of row 1. *)
Definition pgl27_row_exact : AnalysisPathRow :=
  @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
    PGL27Analysis.exact_family StaticExecutedOnly BaselineClassicalOnly.

(** pgl27_row_word — row 2: the same instance under its two-hundred-letter
    word shuffle.
    @intent: the observed execution of that instance, the word model family
    indexed by the secret prior the row's theorems quantify over, and the
    statuses of row 2. *)
Definition pgl27_row_word : AnalysisPathRow :=
  @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
    PGL27Analysis.word_family IdealFinite BaselineClassicalOnly.

(** five_card_row_uniform — row 3: the five-card development under the
    uniform rotation cut.
    @intent: the observed execution of that development, its uniform model
    family, and the statuses of row 3. *)
Definition five_card_row_uniform : AnalysisPathRow :=
  @MkAnalysisPathRow FiveCardAnalysis.observed AnalysisBridged
    FiveCardAnalysis.uniform_family StaticExecutedOnly BaselineClassicalOnly.

(** five_card_row_biased — row 4: the same development under one biased cut.
    @intent: the observed execution of that development, the single-biased
    model family at bias one hundredth, the one member the repository fixes
    of the bias family the row's theorem quantifies over, and the statuses
    of row 4. *)
Definition five_card_row_biased : AnalysisPathRow :=
  @MkAnalysisPathRow FiveCardAnalysis.observed AnalysisBridged
    FiveCardAnalysis.biased_family StaticExecutedOnly BaselineClassicalOnly.

(** five_card_row_repeated — row 5: the same development under repeated
    biased cuts.
    @intent: the observed execution of that development, the seven-cut model
    family at bias one hundredth, and the statuses of row 5. *)
Definition five_card_row_repeated : AnalysisPathRow :=
  @MkAnalysisPathRow FiveCardAnalysis.observed Sampled
    FiveCardAnalysis.centi_family NoModelComparison BaselineClassicalOnly.

(** s5_row_det — row 6: the five-seat S_5 instance dealing a position.
    @intent: the deterministic observed execution of that instance and the
    statuses of row 6. The path has no sample layer, so the optional
    lower-level slot is empty. *)
Definition s5_row_det : AnalysisPathRow :=
  @MkAnalysisPathRow S5Analysis.observed Observed None
    NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder]).

(** s5_row_rand — row 7: the same instance dealing an additive sharing.
    @intent: the randomized observed execution of that instance, its
    randomized model family, and the statuses of row 7. *)
Definition s5_row_rand : AnalysisPathRow :=
  @MkAnalysisPathRow S5Analysis.rand_observed AnalysisBridged
    S5Analysis.rand_family StaticExecutedOnly
    (AcceptsAxioms [:: AxS5GroupOrder]).

(** s5_row_word — row 8: the same instance under a finite generator word.
    @intent: the deterministic observed execution the finite-word model
    stands over, the word model family indexed by a secret prior and a word
    length, and the statuses of row 8. *)
Definition s5_row_word : AnalysisPathRow :=
  @MkAnalysisPathRow S5Analysis.observed Sampled S5Analysis.word_family
    NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R]).

(** s5x5_row_det — row 9: the ten-seat S_5 x S_5 instance dealing a
    position.
    @intent: the deterministic observed execution of that instance and the
    statuses of row 9. *)
Definition s5x5_row_det : AnalysisPathRow :=
  @MkAnalysisPathRow S5x5Analysis.observed Observed None
    NoModelComparison (AcceptsAxioms [:: AxS5x5GroupOrder]).

(** s5x5_row_rand — row 10: the same instance dealing two pile sharings.
    @intent: the randomized observed execution of that instance, its product
    model family, and the statuses of row 10. *)
Definition s5x5_row_rand : AnalysisPathRow :=
  @MkAnalysisPathRow S5x5Analysis.rand_observed AnalysisBridged
    S5x5Analysis.rand_family StaticExecutedOnly
    (AcceptsAxioms [:: AxS5x5GroupOrder]).

(** s5x5_row_pile1_word — row 11: the first pile under a finite generator
    word.
    @intent: the deterministic observed execution the finite-word model
    stands over, the word model family shared by rows 11 to 14, and the
    statuses of row 11. *)
Definition s5x5_row_pile1_word : AnalysisPathRow :=
  @MkAnalysisPathRow S5x5Analysis.observed Sampled S5x5Analysis.word_family
    NoModelComparison (AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

(** s5x5_row_pile2_word — row 12: the second pile under a finite generator
    word.
    @intent: the same observed execution, the same shared word model family,
    and the statuses of row 12. *)
Definition s5x5_row_pile2_word : AnalysisPathRow :=
  @MkAnalysisPathRow S5x5Analysis.observed Sampled S5x5Analysis.word_family
    NoModelComparison (AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

(** s5x5_row_pile1_limitation — row 13: the first pile against global
    uniform.
    @intent: the same observed execution, the same shared word model family,
    and the statuses of row 13, whose transfer status is negative because a
    floor transports the obstruction to the row's own observer. *)
Definition s5x5_row_pile1_limitation : AnalysisPathRow :=
  @MkAnalysisPathRow S5x5Analysis.observed Sampled S5x5Analysis.word_family
    NegativeTransfer (AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

(** s5x5_row_pile2_limitation — row 14: the second pile against global
    uniform.
    @intent: the same observed execution, the same shared word model family,
    and the statuses of row 14. *)
Definition s5x5_row_pile2_limitation : AnalysisPathRow :=
  @MkAnalysisPathRow S5x5Analysis.observed Sampled S5x5Analysis.word_family
    NegativeTransfer (AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

(** abel_row_recovery — row 15: the four-seat abelian instance recovering a
    dealt secret.
    @intent: the secret-recovery observed execution of that instance and the
    statuses of row 15. *)
Definition abel_row_recovery : AnalysisPathRow :=
  @MkAnalysisPathRow AbelianAnalysis.observed Observed None
    NoModelComparison BaselineClassicalOnly.

(** abel_row_identity — row 16: the same instance dealing identity card
    content.
    @intent: the identity-content observed execution of that instance and
    the statuses of row 16. The two shuffle models of that plug belong to
    row 17. *)
Definition abel_row_identity : AnalysisPathRow :=
  @MkAnalysisPathRow AbelianAnalysis.shuffle_observed Observed None
    NoModelComparison BaselineClassicalOnly.

(** abel_row_limitation — row 17: the fixed-length mixing limitation of that
    instance.
    @intent: the identity-content observed execution, the length-indexed
    word model family the limitation is stated about, and the statuses of
    row 17. The ideal shuffle model stays a Models alias of the facade; the
    row's evidence is the actual model. *)
Definition abel_row_limitation : AnalysisPathRow :=
  @MkAnalysisPathRow AbelianAnalysis.shuffle_observed AnalysisBridged
    AbelianAnalysis.word_family NegativeTransfer BaselineClassicalOnly.

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

Timeout 60 Check (erefl : PGL27Analysis.word_transfer_status = IdealFinite).

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

(* --- 7 Transfer: the five-card facade carries no transfer theorem, so the
   two typed statuses are all there is to check; the PGL transfer aliases are
   checked above. --- *)

Timeout 60 Check
  (erefl : FiveCardAnalysis.exec_transfer_status = StaticExecutedOnly).

Timeout 60 Check
  (erefl : FiveCardAnalysis.repeated_transfer_status = NoModelComparison).

(******************************************************************************)
(*     The deterministic checker: five-seat S_5 instance                      *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (S5Analysis.profile : MonodromyProfile).

Timeout 60 Check (S5Analysis.profile_k : profile_k S5Analysis.profile = 5%N).

(* --- 2 Execution --- *)

Timeout 60 Check (S5Analysis.exec_plug : ExecutionPlug S5Analysis.profile).

Timeout 60 Check (S5Analysis.rand_exec_plug :
  ExecutionPlug S5Analysis.profile).

(* --- 3 Observers --- *)

Timeout 60 Check (S5Analysis.seat_endpoint :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.coalition_endpoints :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M S5Analysis.profile)).+1}).

Timeout 60 Check (S5Analysis.verifier_trace :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.verifier_endpoints :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.player_raw_trace :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.observed : OE.ObservedExecution).

Timeout 60 Check (S5Analysis.rand_seat_endpoint :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.rand_coalition_endpoints :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M S5Analysis.profile)).+1}).

Timeout 60 Check (S5Analysis.rand_content_trace :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI S5Analysis.profile)).+1),
    {RV (s5_models.s5_rand_sampleP R) -> 'I_5}).

Timeout 60 Check (S5Analysis.rand_verifier_trace :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.rand_verifier_endpoints :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.rand_player_raw_trace :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.rand_observed : OE.ObservedExecution).

(* --- 4 Models --- *)

Timeout 60 Check (S5Analysis.rand_sample :
  forall R : realType, SampleAdapter R S5Analysis.rand_exec_plug).

Timeout 60 Check (S5Analysis.word_sample :
  forall R : realType, R.-fdist 'I_5 -> forall L : nat,
    SampleAdapter R S5Analysis.exec_plug).

Timeout 60 Check (S5Analysis.rand_cut_distE :
  forall R : realType,
    sa_cut_dist (S5Analysis.rand_sample R) = fdist1 1%g).

Timeout 60 Check (S5Analysis.word_cut_distE :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat),
    sa_cut_dist (S5Analysis.word_sample secretP L)
    = rho_from_words L (pgg_raag_path.path_gen_tuple 3)).

Timeout 60 Check (S5Analysis.word_cut_imageE :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat),
    sa_cut_dist_image (S5Analysis.word_sample secretP L)
    = rho_from_words L (pgg_raag_path.path_gen_tuple 3)).

(* --- 5 Correctness --- *)

Timeout 60 Check (S5Analysis.exec_correct :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    [/\ (@exec_run S5Analysis.profile S5Analysis.exec_plug s w0 0).1
        = nseq (size (@exec_procs S5Analysis.profile S5Analysis.exec_plug
                        s w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints S5Analysis.profile S5Analysis.exec_plug s w0 0)
        = (pi_T' (mp_PI S5Analysis.profile)).+1
      & exec_decode S5Analysis.exec_plug
          (exec_endpoints_size (s5_exec.s5_exec_endpoints s w0)) = s]).

Timeout 60 Check (S5Analysis.exec_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (exec_endpoints_size (s5_exec.s5_exec_endpoints s w0)) = s).

Timeout 60 Check (S5Analysis.observed_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (OE.oe_endpoints_size S5Analysis.observed s w0) = s).

Timeout 60 Check (S5Analysis.rand_correct :
  forall (u : 'rV['Z_5]_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    [/\ (@exec_run S5Analysis.profile S5Analysis.rand_exec_plug u w0 0).1
        = nseq (size (@exec_procs S5Analysis.profile
                        S5Analysis.rand_exec_plug u w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints S5Analysis.profile S5Analysis.rand_exec_plug
                u w0 0)
        = (pi_T' (mp_PI S5Analysis.profile)).+1
      & exec_decode S5Analysis.rand_exec_plug
          (exec_endpoints_size (s5_exec.s5_rand_endpoints u w0))
        = s5_exec.s5_codec (s5_exec.s5_tape_secret u)]).

Timeout 60 Check (S5Analysis.rand_recovers :
  forall (u : 'rV['Z_5]_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.rand_exec_plug
      (exec_endpoints_size (s5_exec.s5_rand_endpoints u w0))
    = s5_exec.s5_codec (s5_exec.s5_tape_secret u)).

Timeout 60 Check (S5Analysis.rand_observed_recovers :
  forall (u : 'rV['Z_5]_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.rand_exec_plug
      (OE.oe_endpoints_size S5Analysis.rand_observed u w0)
    = s5_exec.s5_codec (s5_exec.s5_tape_secret u)).

(* --- 6 Security --- *)

Timeout 60 Check (S5Analysis.exec_trace_secrecy :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI S5Analysis.profile)).+1),
    `H( rsh_secret (@unif_randomized_sharing R 3 4)
      | S5Analysis.rand_content_trace R i)
    = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4))).

Timeout 60 Check (S5Analysis.exec_coalition_secrecy :
  forall (R : realType) (C : {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1}),
    (#|C| < 5)%N ->
    `I( rsh_secret (@unif_randomized_sharing R 3 4) ;
        @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
          (S5Analysis.rand_sample R) 0 C ) = 0 /\
    `H( rsh_secret (@unif_randomized_sharing R 3 4)
        | @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
            (S5Analysis.rand_sample R) 0 C )
      = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4))).

(* --- bound (endpoint marginal, not security) --- *)

Timeout 60 Check (S5Analysis.word_endpoint_bound :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat) (s : 'I_5),
    var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                (sa_cut_dist (S5Analysis.word_sample secretP L)))
             (fdist_uniform (card_ord 5))
    <= Num.sqrt 5%:R * (s5_mixing.s5_alpha_R R) ^+ L).

(* --- 7 Transfer --- *)

Timeout 60 Check (erefl : S5Analysis.det_transfer_status = NoModelComparison).

Timeout 60 Check
  (erefl : S5Analysis.rand_transfer_status = StaticExecutedOnly).

Timeout 60 Check (S5Analysis.rand_content_traceE :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI S5Analysis.profile)).+1),
    S5Analysis.rand_content_trace R i = s5_trace.s5_player_trace R i).

Timeout 60 Check (S5Analysis.rand_coalition_viewE :
  forall (R : realType) (C : {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1}),
    @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
      (S5Analysis.rand_sample R) 0 C
    = rsh_view (@unif_randomized_sharing R 3 4) C).

Timeout 60 Check (erefl : S5Analysis.word_transfer_status = NoModelComparison).

Timeout 60 Check (S5Analysis.word_missing_premise :
  forall R : realType, R.-fdist 'I_5 -> forall L : nat,
    R.-fdist {perm 'I_5} -> R -> Prop).

Timeout 60 Check (S5Analysis.word_transfer_conditional :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat)
    (Q : R.-fdist {perm 'I_5}) (delta : R) (B : finType)
    (fx fy : {perm 'I_5} -> B),
    S5Analysis.word_missing_premise secretP L Q delta ->
    fdistmap fx Q = fdistmap fy Q ->
    var_dist (fdistmap fx (sa_cut_dist (S5Analysis.word_sample secretP L)))
             (fdistmap fy (sa_cut_dist (S5Analysis.word_sample secretP L)))
    <= delta + delta).

(******************************************************************************)
(*     The deterministic checker: ten-seat S_5 x S_5 instance                 *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (S5x5Analysis.profile : MonodromyProfile).

Timeout 60 Check
  (S5x5Analysis.profile_k : profile_k S5x5Analysis.profile = 5%N).

(* --- 2 Execution --- *)

Timeout 60 Check (S5x5Analysis.exec_plug : ExecutionPlug S5x5Analysis.profile).

Timeout 60 Check (S5x5Analysis.rand_exec_plug :
  ExecutionPlug S5x5Analysis.profile).

(* --- 3 Observers --- *)

Timeout 60 Check (S5x5Analysis.seat_endpoint :
  ep_inputT S5x5Analysis.exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M S5x5Analysis.profile)).+1).

Timeout 60 Check (S5x5Analysis.coalition_endpoints :
  ep_inputT S5x5Analysis.exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M S5x5Analysis.profile)).+1}).

Timeout 60 Check (S5x5Analysis.verifier_trace :
  ep_inputT S5x5Analysis.exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M S5x5Analysis.profile)).+1)).

Timeout 60 Check (S5x5Analysis.verifier_endpoints :
  ep_inputT S5x5Analysis.exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M S5x5Analysis.profile)).+1).

Timeout 60 Check (S5x5Analysis.player_raw_trace :
  ep_inputT S5x5Analysis.exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M S5x5Analysis.profile)).+1)).

Timeout 60 Check (S5x5Analysis.observed : OE.ObservedExecution).

Timeout 60 Check (S5x5Analysis.rand_seat_endpoint :
  ep_inputT S5x5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M S5x5Analysis.profile)).+1).

Timeout 60 Check (S5x5Analysis.rand_coalition_endpoints :
  ep_inputT S5x5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M S5x5Analysis.profile)).+1}).

Timeout 60 Check (S5x5Analysis.rand_content_trace :
  forall (R : realType) (j : 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1),
    {RV (s5x5_models.s5x5_rand_sampleP R) -> 'I_10}).

Timeout 60 Check (S5x5Analysis.rand_verifier_trace :
  ep_inputT S5x5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M S5x5Analysis.profile)).+1)).

Timeout 60 Check (S5x5Analysis.rand_verifier_endpoints :
  ep_inputT S5x5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M S5x5Analysis.profile)).+1).

Timeout 60 Check (S5x5Analysis.rand_player_raw_trace :
  ep_inputT S5x5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5x5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M S5x5Analysis.profile)).+1)).

Timeout 60 Check (S5x5Analysis.rand_observed : OE.ObservedExecution).

Timeout 60 Check (S5x5Analysis.pile1_seats :
  {set 'I_5} -> {set 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1}).

Timeout 60 Check (S5x5Analysis.pile2_seats :
  {set 'I_5} -> {set 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1}).

Timeout 60 Check (S5x5Analysis.pile1_seat_view :
  forall R : realType,
    'I_5 -> {RV (s5x5_models.s5x5_rand_sampleP R) -> 'Z_5}).

Timeout 60 Check (S5x5Analysis.pile2_seat_view :
  forall R : realType,
    'I_5 -> {RV (s5x5_models.s5x5_rand_sampleP R) -> 'Z_5}).

Timeout 60 Check (S5x5Analysis.pile1_coalition_view :
  forall R : realType, {set 'I_5} ->
    {RV (s5x5_models.s5x5_rand_sampleP R) -> {ffun 'I_5 -> 'Z_5}}).

Timeout 60 Check (S5x5Analysis.pile2_coalition_view :
  forall R : realType, {set 'I_5} ->
    {RV (s5x5_models.s5x5_rand_sampleP R) -> {ffun 'I_5 -> 'Z_5}}).

Timeout 60 Check (S5x5Analysis.joint_view :
  forall R : realType, {set 'I_5} -> {set 'I_5} ->
    {RV (s5x5_models.s5x5_rand_sampleP R)
     -> ({ffun 'I_5 -> 'Z_5} * {ffun 'I_5 -> 'Z_5})%type}).

(* --- 4 Models --- *)

Timeout 60 Check (S5x5Analysis.rand_sample :
  forall R : realType, SampleAdapter R S5x5Analysis.rand_exec_plug).

Timeout 60 Check (S5x5Analysis.word_sample :
  forall R : realType, R.-fdist 'I_10 -> forall L : nat,
    SampleAdapter R S5x5Analysis.exec_plug).

Timeout 60 Check (S5x5Analysis.rand_cut_distE :
  forall R : realType,
    sa_cut_dist (S5x5Analysis.rand_sample R) = fdist1 1%g).

Timeout 60 Check (S5x5Analysis.word_cut_distE :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat),
    sa_cut_dist (S5x5Analysis.word_sample secretP L)
    = rho_from_words L pgg_s5x5.s5x5_gen_tuple).

(* --- 5 Correctness --- *)

Timeout 60 Check (S5x5Analysis.exec_correct :
  forall (s : 'I_10) (w0 : pgg_gT (mp_M S5x5Analysis.profile)),
    w0 \in pgg_G (mp_M S5x5Analysis.profile) ->
    [/\ (@exec_run S5x5Analysis.profile S5x5Analysis.exec_plug s w0 0).1
        = nseq (size (@exec_procs S5x5Analysis.profile S5x5Analysis.exec_plug
                        s w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints S5x5Analysis.profile S5x5Analysis.exec_plug
                s w0 0)
        = (pi_T' (mp_PI S5x5Analysis.profile)).+1
      & exec_decode S5x5Analysis.exec_plug
          (exec_endpoints_size (s5x5_exec.s5x5_exec_endpoints s w0)) = s]).

Timeout 60 Check (S5x5Analysis.exec_recovers :
  forall (s : 'I_10) (w0 : pgg_gT (mp_M S5x5Analysis.profile)),
    w0 \in pgg_G (mp_M S5x5Analysis.profile) ->
    exec_decode S5x5Analysis.exec_plug
      (exec_endpoints_size (s5x5_exec.s5x5_exec_endpoints s w0)) = s).

Timeout 60 Check (S5x5Analysis.observed_recovers :
  forall (s : 'I_10) (w0 : pgg_gT (mp_M S5x5Analysis.profile)),
    w0 \in pgg_G (mp_M S5x5Analysis.profile) ->
    exec_decode S5x5Analysis.exec_plug
      (OE.oe_endpoints_size S5x5Analysis.observed s w0) = s).

Timeout 60 Check (S5x5Analysis.rand_correct :
  forall (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT (mp_M S5x5Analysis.profile)),
    w0 \in pgg_G (mp_M S5x5Analysis.profile) ->
    [/\ (@exec_run S5x5Analysis.profile S5x5Analysis.rand_exec_plug
           uv w0 0).1
        = nseq (size (@exec_procs S5x5Analysis.profile
                        S5x5Analysis.rand_exec_plug uv w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints S5x5Analysis.profile
                S5x5Analysis.rand_exec_plug uv w0 0)
        = (pi_T' (mp_PI S5x5Analysis.profile)).+1
      & exec_decode S5x5Analysis.rand_exec_plug
          (exec_endpoints_size (s5x5_exec.s5x5_rand_endpoints uv w0))
        = s5x5_exec.s5x5_codec (s5x5_exec.s5x5_joint_tape_secret uv)]).

Timeout 60 Check (S5x5Analysis.rand_recovers :
  forall (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT (mp_M S5x5Analysis.profile)),
    w0 \in pgg_G (mp_M S5x5Analysis.profile) ->
    exec_decode S5x5Analysis.rand_exec_plug
      (exec_endpoints_size (s5x5_exec.s5x5_rand_endpoints uv w0))
    = s5x5_exec.s5x5_codec (s5x5_exec.s5x5_joint_tape_secret uv)).

Timeout 60 Check (S5x5Analysis.rand_observed_recovers :
  forall (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type)
    (w0 : pgg_gT (mp_M S5x5Analysis.profile)),
    w0 \in pgg_G (mp_M S5x5Analysis.profile) ->
    exec_decode S5x5Analysis.rand_exec_plug
      (OE.oe_endpoints_size S5x5Analysis.rand_observed uv w0)
    = s5x5_exec.s5x5_codec (s5x5_exec.s5x5_joint_tape_secret uv)).

Timeout 60 Check (S5x5Analysis.combine_not_injectiveE :
  @product_threshold.combine_secret 3 3 (@Ordinal 5 0 isT) (@Ordinal 5 2 isT)
  = @product_threshold.combine_secret 3 3 (@Ordinal 5 0 isT)
      (@Ordinal 5 0 isT)).

(* --- 6 Security --- *)

Timeout 60 Check (S5x5Analysis.exec_trace_secrecy :
  forall (R : realType) (j : 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1),
    `H( s5x5_trace.JointSecret R | S5x5Analysis.rand_content_trace R j )
    = `H `p_ (s5x5_trace.JointSecret R)).

Timeout 60 Check (S5x5Analysis.exec_p1_secrecy :
  forall (R : realType) (C1 : {set 'I_5}), (#|C1| < 5)%N ->
    `I( s5x5_trace.JointSecret R ;
        S5x5Analysis.pile1_coalition_view R C1 ) = 0 /\
    `H( s5x5_trace.JointSecret R | S5x5Analysis.pile1_coalition_view R C1 )
      = `H `p_ (s5x5_trace.JointSecret R)).

Timeout 60 Check (S5x5Analysis.exec_p2_secrecy :
  forall (R : realType) (C2 : {set 'I_5}), (#|C2| < 5)%N ->
    `I( s5x5_trace.JointSecret R ;
        S5x5Analysis.pile2_coalition_view R C2 ) = 0 /\
    `H( s5x5_trace.JointSecret R | S5x5Analysis.pile2_coalition_view R C2 )
      = `H `p_ (s5x5_trace.JointSecret R)).

Timeout 60 Check (S5x5Analysis.exec_joint_secrecy :
  forall (R : realType) (C1 C2 : {set 'I_5}),
    (#|C1| < 5)%N -> (#|C2| < 5)%N ->
    `I( s5x5_trace.JointSecret R ; S5x5Analysis.joint_view R C1 C2 ) = 0 /\
    `H( s5x5_trace.JointSecret R | S5x5Analysis.joint_view R C1 C2 )
      = `H `p_ (s5x5_trace.JointSecret R)).

(* --- bound (endpoint marginal, not security) --- *)

Timeout 60 Check (S5x5Analysis.word_pile1_bound :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
    var_dist (fdistmap (fun sigma : {perm 'I_10} =>
                          sigma (s5x5_mixing.widen5to10 s))
                (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
             (s5x5_mixing.fdist_uniform_pile1 R)
    <= Num.sqrt 5%:R * (s5x5_mixing.s5_lazy_alpha_R R) ^+ L).

Timeout 60 Check (S5x5Analysis.word_pile2_bound :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
    var_dist (fdistmap (fun sigma : {perm 'I_10} =>
                          sigma (s5x5_mixing.rshift5to10 s))
                (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
             (s5x5_mixing.fdist_uniform_pile2 R)
    <= Num.sqrt 5%:R * (s5x5_mixing.s5_lazy_alpha_R R) ^+ L).

Timeout 60 Check (S5x5Analysis.word_seat_bound :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_10),
    var_dist (fdistmap (fun sigma : {perm 'I_10} => sigma s)
                (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
             (fdist_uniform (card_ord 10))
    <= 1 + Num.sqrt 5%:R * (s5x5_mixing.s5_lazy_alpha_R R) ^+ L).

(* --- 7 Transfer --- *)

Timeout 60 Check
  (erefl : S5x5Analysis.det_transfer_status = NoModelComparison).

Timeout 60 Check
  (erefl : S5x5Analysis.rand_transfer_status = StaticExecutedOnly).

Timeout 60 Check (S5x5Analysis.rand_content_traceE :
  forall (R : realType) (j : 'I_(pi_T' (mp_PI S5x5Analysis.profile)).+1),
    S5x5Analysis.rand_content_trace R j = s5x5_trace.s5x5_player_trace R j).

Timeout 60 Check (S5x5Analysis.rand_pile1_seat_viewE :
  forall (R : realType) (j : 'I_5),
    S5x5Analysis.pile1_seat_view R j
    = (fun uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type =>
         rsh_share (s5x5_trace.rs1 R) j uv.1)).

Timeout 60 Check (S5x5Analysis.rand_pile2_seat_viewE :
  forall (R : realType) (j : 'I_5),
    S5x5Analysis.pile2_seat_view R j
    = (fun uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type =>
         rsh_share (s5x5_trace.rs2 R) j uv.2)).

Timeout 60 Check (S5x5Analysis.rand_pile1_viewE :
  forall (R : realType) (C1 : {set 'I_5}),
    S5x5Analysis.pile1_coalition_view R C1
    = (fun uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type =>
         rsh_view (s5x5_trace.rs1 R) C1 uv.1)).

Timeout 60 Check (S5x5Analysis.rand_pile2_viewE :
  forall (R : realType) (C2 : {set 'I_5}),
    S5x5Analysis.pile2_coalition_view R C2
    = (fun uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type =>
         rsh_view (s5x5_trace.rs2 R) C2 uv.2)).

Timeout 60 Check (S5x5Analysis.rand_joint_viewE :
  forall (R : realType) (C1 C2 : {set 'I_5})
    (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N),
    S5x5Analysis.joint_view R C1 C2
    = pgg_leakage_witness.lw_view
        (pgg_leakage_product.leakage_product
           (pgg_sharing_mechanism.mechanism_leakage
              (pgg_sharing_mechanism.Additive
                 (@unif_randomized_sharing R 3 4) HC1))
           (pgg_sharing_mechanism.mechanism_leakage
              (pgg_sharing_mechanism.Additive
                 (@unif_randomized_sharing R 3 4) HC2)))).

Timeout 60 Check
  (erefl : S5x5Analysis.pile1_word_transfer_status = NoModelComparison).

Timeout 60 Check
  (erefl : S5x5Analysis.pile2_word_transfer_status = NoModelComparison).

Timeout 60 Check (S5x5Analysis.word_missing_premise :
  forall R : realType, R.-fdist 'I_10 -> forall L : nat,
    R.-fdist {perm 'I_10} -> R -> Prop).

Timeout 60 Check (S5x5Analysis.word_transfer_conditional :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat)
    (Q : R.-fdist {perm 'I_10}) (delta : R) (B : finType)
    (fx fy : {perm 'I_10} -> B),
    S5x5Analysis.word_missing_premise secretP L Q delta ->
    fdistmap fx Q = fdistmap fy Q ->
    var_dist (fdistmap fx (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
             (fdistmap fy (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
    <= delta + delta).

Timeout 60 Check
  (erefl : S5x5Analysis.pile1_limitation_transfer_status = NegativeTransfer).

Timeout 60 Check
  (erefl : S5x5Analysis.pile2_limitation_transfer_status = NegativeTransfer).

Timeout 60 Check (S5x5Analysis.word_pile1_floor :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
    1 - Num.sqrt 5%:R * (s5x5_mixing.s5_lazy_alpha_R R) ^+ L
    <= var_dist (fdistmap (fun sigma : {perm 'I_10} =>
                             sigma (s5x5_mixing.widen5to10 s))
                   (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
                (fdist_uniform (card_ord 10))).

Timeout 60 Check (S5x5Analysis.word_pile2_floor :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
    1 - Num.sqrt 5%:R * (s5x5_mixing.s5_lazy_alpha_R R) ^+ L
    <= var_dist (fdistmap (fun sigma : {perm 'I_10} =>
                             sigma (s5x5_mixing.rshift5to10 s))
                   (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
                (fdist_uniform (card_ord 10))).

Timeout 60 Check (S5x5Analysis.word_positive_regime :
  forall (R : realType) (n : nat), (17 <= n)%N ->
    Num.sqrt 5%:R * (s5x5_mixing.s5_lazy_alpha_R R) ^+ n < 1).

Timeout 60 Check (S5x5Analysis.word_pile1_floor_gt0 :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
    (17 <= L)%N ->
    0 < var_dist (fdistmap (fun sigma : {perm 'I_10} =>
                              sigma (s5x5_mixing.widen5to10 s))
                    (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
                 (fdist_uniform (card_ord 10))).

Timeout 60 Check (S5x5Analysis.word_pile2_floor_gt0 :
  forall (R : realType) (secretP : R.-fdist 'I_10) (L : nat) (s : 'I_5),
    (17 <= L)%N ->
    0 < var_dist (fdistmap (fun sigma : {perm 'I_10} =>
                              sigma (s5x5_mixing.rshift5to10 s))
                    (sa_cut_dist (S5x5Analysis.word_sample secretP L)))
                 (fdist_uniform (card_ord 10))).

(******************************************************************************)
(*     The deterministic checker: four-seat abelian instance                  *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (AbelianAnalysis.profile : MonodromyProfile).

Timeout 60 Check
  (AbelianAnalysis.profile_k : profile_k AbelianAnalysis.profile = 4%N).

(* --- 2 Execution --- *)

Timeout 60 Check
  (AbelianAnalysis.exec_plug : ExecutionPlug AbelianAnalysis.profile).

Timeout 60 Check
  (AbelianAnalysis.shuffle_plug : ExecutionPlug AbelianAnalysis.profile).

(* --- 3 Observers --- *)

Timeout 60 Check (AbelianAnalysis.seat_endpoint :
  ep_inputT AbelianAnalysis.exec_plug ->
  pgg_gT (mp_M AbelianAnalysis.profile) -> nat ->
  'I_(pi_T' (mp_PI AbelianAnalysis.profile)).+1 ->
  'I_(pgg_N' (mp_M AbelianAnalysis.profile)).+1).

Timeout 60 Check
  (AbelianAnalysis.endpoint_vector : {perm 'I_4} -> 4.-tuple 'I_4).

Timeout 60 Check (AbelianAnalysis.verifier_trace :
  ep_inputT AbelianAnalysis.exec_plug ->
  pgg_gT (mp_M AbelianAnalysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M AbelianAnalysis.profile)).+1)).

Timeout 60 Check (AbelianAnalysis.verifier_endpoints :
  ep_inputT AbelianAnalysis.exec_plug ->
  pgg_gT (mp_M AbelianAnalysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M AbelianAnalysis.profile)).+1).

Timeout 60 Check (AbelianAnalysis.player_raw_trace :
  ep_inputT AbelianAnalysis.exec_plug ->
  pgg_gT (mp_M AbelianAnalysis.profile) -> nat ->
  'I_(pi_T' (mp_PI AbelianAnalysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M AbelianAnalysis.profile)).+1)).

Timeout 60 Check (AbelianAnalysis.observed : OE.ObservedExecution).

Timeout 60 Check (AbelianAnalysis.shuffle_observed : OE.ObservedExecution).

Timeout 60 Check (AbelianAnalysis.endpoint_vector_inj :
  injective AbelianAnalysis.endpoint_vector).

(* --- 4 Models --- *)

Timeout 60 Check (AbelianAnalysis.ideal_sample :
  forall R : realType, SampleAdapter R AbelianAnalysis.shuffle_plug).

Timeout 60 Check (AbelianAnalysis.word_sample :
  forall (R : realType) (L : nat),
    SampleAdapter R AbelianAnalysis.shuffle_plug).

Timeout 60 Check (AbelianAnalysis.actual_cut_distE :
  forall (R : realType) (L : nat),
    sa_cut_dist (AbelianAnalysis.word_sample R L)
    = abelian_models.abel_word_dist R L).

(* --- 5 Correctness --- *)

Timeout 60 Check (AbelianAnalysis.exec_correct :
  forall (s : 'I_4) (w0 : pgg_gT (mp_M AbelianAnalysis.profile)),
    w0 \in pgg_G (mp_M AbelianAnalysis.profile) ->
    [/\ (@exec_run AbelianAnalysis.profile AbelianAnalysis.exec_plug
           s w0 0).1
        = nseq (size (@exec_procs AbelianAnalysis.profile
                        AbelianAnalysis.exec_plug s w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints AbelianAnalysis.profile
                AbelianAnalysis.exec_plug s w0 0)
        = (pi_T' (mp_PI AbelianAnalysis.profile)).+1
      & exec_decode AbelianAnalysis.exec_plug
          (exec_endpoints_size (abelian_exec.abel_exec_endpoints s w0))
        = s]).

Timeout 60 Check (AbelianAnalysis.exec_recovers :
  forall (s : 'I_4) (w0 : pgg_gT (mp_M AbelianAnalysis.profile)),
    w0 \in pgg_G (mp_M AbelianAnalysis.profile) ->
    exec_decode AbelianAnalysis.exec_plug
      (exec_endpoints_size (abelian_exec.abel_exec_endpoints s w0)) = s).

Timeout 60 Check (AbelianAnalysis.observed_recovers :
  forall (s : 'I_4) (w0 : pgg_gT (mp_M AbelianAnalysis.profile)),
    w0 \in pgg_G (mp_M AbelianAnalysis.profile) ->
    exec_decode AbelianAnalysis.exec_plug
      (OE.oe_endpoints_size AbelianAnalysis.observed s w0) = s).

Timeout 60 Check (AbelianAnalysis.shuffle_recovers :
  forall (x : unit) (w0 : pgg_gT (mp_M AbelianAnalysis.profile)),
    w0 \in pgg_G (mp_M AbelianAnalysis.profile) ->
    exec_decode AbelianAnalysis.shuffle_plug
      (exec_endpoints_size (abelian_exec.abel_shuffle_endpoints x w0))
    = abelian_exec.abel_identity_recon_value).

(* --- 6 Security: the one result of this instance is negative --- *)

Timeout 60 Check (AbelianAnalysis.word_mixing_limitation :
  forall (R : realType) (L : nat),
    var_dist
      (fdistmap (@abelian_models.abel_sample_reader R
                   (AbelianAnalysis.word_sample R L))
                (sa_sampleP (AbelianAnalysis.word_sample R L)))
      (fdistmap (@abelian_models.abel_sample_reader R
                   (AbelianAnalysis.ideal_sample R))
                (sa_sampleP (AbelianAnalysis.ideal_sample R)))
    = 1).

(* --- 7 Transfer --- *)

Timeout 60 Check
  (erefl : AbelianAnalysis.det_transfer_status = NoModelComparison).

Timeout 60 Check
  (erefl : AbelianAnalysis.shuffle_transfer_status = NoModelComparison).

Timeout 60 Check
  (erefl : AbelianAnalysis.limitation_transfer_status = NegativeTransfer).

Timeout 60 Check (AbelianAnalysis.word_group_dist :
  forall (R : realType) (L : nat),
    var_dist (abelian_models.abel_word_dist R L)
             (abelian_models.abel_group_uniform R) = 1).

Timeout 60 Check (AbelianAnalysis.executed_distance :
  forall (R : realType) (L : nat),
    var_dist (fdistmap AbelianAnalysis.endpoint_vector
                (abelian_models.abel_word_dist R L))
             (fdistmap AbelianAnalysis.endpoint_vector
                (abelian_models.abel_group_uniform R))
    = 1).

Timeout 60 Check (AbelianAnalysis.sample_reader_distE :
  forall (R : realType) (sa : SampleAdapter R AbelianAnalysis.shuffle_plug),
    fdistmap (@abelian_models.abel_sample_reader R sa) (sa_sampleP sa)
    = fdistmap AbelianAnalysis.endpoint_vector (sa_cut_dist sa)).

Timeout 60 Check (AbelianAnalysis.executed_observation_distance :
  forall (R : realType) (L : nat),
    var_dist
      (fdistmap (@abelian_models.abel_sample_reader R
                   (AbelianAnalysis.word_sample R L))
                (sa_sampleP (AbelianAnalysis.word_sample R L)))
      (fdistmap (@abelian_models.abel_sample_reader R
                   (AbelianAnalysis.ideal_sample R))
                (sa_sampleP (AbelianAnalysis.ideal_sample R)))
    = 1).

(******************************************************************************)
(*     The deterministic checker: the seventeen typed rows                    *)
(*                                                                            *)
(* One Check per row against AnalysisPathRow, one erefl pin per status       *)
(* field, and one typed check on the model slot: a mandatory family at        *)
(* Sampled and AnalysisBridged, an optional one below. A row whose status or  *)
(* model witness is edited away from the table above fails at its own pin.    *)
(******************************************************************************)

Timeout 60 Check (pgl27_row_exact : AnalysisPathRow).
Timeout 60 Check (apr_model pgl27_row_exact
  : AnalysisModelFamily PGL27Analysis.observed).
Timeout 60 Check (erefl : apr_completion pgl27_row_exact = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer pgl27_row_exact = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions pgl27_row_exact = BaselineClassicalOnly).

Timeout 60 Check (pgl27_row_word : AnalysisPathRow).
Timeout 60 Check (apr_model pgl27_row_word
  : AnalysisModelFamily PGL27Analysis.observed).
Timeout 60 Check (erefl : apr_completion pgl27_row_word = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer pgl27_row_word = IdealFinite).
Timeout 60 Check
  (erefl : apr_assumptions pgl27_row_word = BaselineClassicalOnly).

Timeout 60 Check (five_card_row_uniform : AnalysisPathRow).
Timeout 60 Check (apr_model five_card_row_uniform
  : AnalysisModelFamily FiveCardAnalysis.observed).
Timeout 60 Check
  (erefl : apr_completion five_card_row_uniform = AnalysisBridged).
Timeout 60 Check
  (erefl : apr_transfer five_card_row_uniform = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions five_card_row_uniform = BaselineClassicalOnly).

Timeout 60 Check (five_card_row_biased : AnalysisPathRow).
Timeout 60 Check (apr_model five_card_row_biased
  : AnalysisModelFamily FiveCardAnalysis.observed).
Timeout 60 Check
  (erefl : apr_completion five_card_row_biased = AnalysisBridged).
Timeout 60 Check
  (erefl : apr_transfer five_card_row_biased = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions five_card_row_biased = BaselineClassicalOnly).

Timeout 60 Check (five_card_row_repeated : AnalysisPathRow).
Timeout 60 Check (apr_model five_card_row_repeated
  : AnalysisModelFamily FiveCardAnalysis.observed).
Timeout 60 Check (erefl : apr_completion five_card_row_repeated = Sampled).
Timeout 60 Check
  (erefl : apr_transfer five_card_row_repeated = NoModelComparison).
Timeout 60 Check
  (erefl : apr_assumptions five_card_row_repeated = BaselineClassicalOnly).

Timeout 60 Check (s5_row_det : AnalysisPathRow).
Timeout 60 Check (apr_model s5_row_det
  : option (AnalysisModelFamily S5Analysis.observed)).
Timeout 60 Check (erefl : apr_completion s5_row_det = Observed).
Timeout 60 Check (erefl : apr_transfer s5_row_det = NoModelComparison).
Timeout 60 Check
  (erefl : apr_assumptions s5_row_det = AcceptsAxioms [:: AxS5GroupOrder]).

Timeout 60 Check (s5_row_rand : AnalysisPathRow).
Timeout 60 Check (apr_model s5_row_rand
  : AnalysisModelFamily S5Analysis.rand_observed).
Timeout 60 Check (erefl : apr_completion s5_row_rand = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer s5_row_rand = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions s5_row_rand = AcceptsAxioms [:: AxS5GroupOrder]).

Timeout 60 Check (s5_row_word : AnalysisPathRow).
Timeout 60 Check (apr_model s5_row_word
  : AnalysisModelFamily S5Analysis.observed).
Timeout 60 Check (erefl : apr_completion s5_row_word = Sampled).
Timeout 60 Check (erefl : apr_transfer s5_row_word = NoModelComparison).
Timeout 60 Check (erefl : apr_assumptions s5_row_word
  = AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R]).

Timeout 60 Check (s5x5_row_det : AnalysisPathRow).
Timeout 60 Check (apr_model s5x5_row_det
  : option (AnalysisModelFamily S5x5Analysis.observed)).
Timeout 60 Check (erefl : apr_completion s5x5_row_det = Observed).
Timeout 60 Check (erefl : apr_transfer s5x5_row_det = NoModelComparison).
Timeout 60 Check (erefl : apr_assumptions s5x5_row_det
  = AcceptsAxioms [:: AxS5x5GroupOrder]).

Timeout 60 Check (s5x5_row_rand : AnalysisPathRow).
Timeout 60 Check (apr_model s5x5_row_rand
  : AnalysisModelFamily S5x5Analysis.rand_observed).
Timeout 60 Check (erefl : apr_completion s5x5_row_rand = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer s5x5_row_rand = StaticExecutedOnly).
Timeout 60 Check (erefl : apr_assumptions s5x5_row_rand
  = AcceptsAxioms [:: AxS5x5GroupOrder]).

Timeout 60 Check (s5x5_row_pile1_word : AnalysisPathRow).
Timeout 60 Check (apr_model s5x5_row_pile1_word
  : AnalysisModelFamily S5x5Analysis.observed).
Timeout 60 Check (erefl : apr_completion s5x5_row_pile1_word = Sampled).
Timeout 60 Check
  (erefl : apr_transfer s5x5_row_pile1_word = NoModelComparison).
Timeout 60 Check (erefl : apr_assumptions s5x5_row_pile1_word
  = AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

Timeout 60 Check (s5x5_row_pile2_word : AnalysisPathRow).
Timeout 60 Check (apr_model s5x5_row_pile2_word
  : AnalysisModelFamily S5x5Analysis.observed).
Timeout 60 Check (erefl : apr_completion s5x5_row_pile2_word = Sampled).
Timeout 60 Check
  (erefl : apr_transfer s5x5_row_pile2_word = NoModelComparison).
Timeout 60 Check (erefl : apr_assumptions s5x5_row_pile2_word
  = AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

Timeout 60 Check (s5x5_row_pile1_limitation : AnalysisPathRow).
Timeout 60 Check (apr_model s5x5_row_pile1_limitation
  : AnalysisModelFamily S5x5Analysis.observed).
Timeout 60 Check (erefl : apr_completion s5x5_row_pile1_limitation = Sampled).
Timeout 60 Check
  (erefl : apr_transfer s5x5_row_pile1_limitation = NegativeTransfer).
Timeout 60 Check (erefl : apr_assumptions s5x5_row_pile1_limitation
  = AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

Timeout 60 Check (s5x5_row_pile2_limitation : AnalysisPathRow).
Timeout 60 Check (apr_model s5x5_row_pile2_limitation
  : AnalysisModelFamily S5x5Analysis.observed).
Timeout 60 Check (erefl : apr_completion s5x5_row_pile2_limitation = Sampled).
Timeout 60 Check
  (erefl : apr_transfer s5x5_row_pile2_limitation = NegativeTransfer).
Timeout 60 Check (erefl : apr_assumptions s5x5_row_pile2_limitation
  = AcceptsAxioms [:: AxS5x5GroupOrder; AxRayleighQ2R]).

Timeout 60 Check (abel_row_recovery : AnalysisPathRow).
Timeout 60 Check (apr_model abel_row_recovery
  : option (AnalysisModelFamily AbelianAnalysis.observed)).
Timeout 60 Check (erefl : apr_completion abel_row_recovery = Observed).
Timeout 60 Check (erefl : apr_transfer abel_row_recovery = NoModelComparison).
Timeout 60 Check
  (erefl : apr_assumptions abel_row_recovery = BaselineClassicalOnly).

Timeout 60 Check (abel_row_identity : AnalysisPathRow).
Timeout 60 Check (apr_model abel_row_identity
  : option (AnalysisModelFamily AbelianAnalysis.shuffle_observed)).
Timeout 60 Check (erefl : apr_completion abel_row_identity = Observed).
Timeout 60 Check (erefl : apr_transfer abel_row_identity = NoModelComparison).
Timeout 60 Check
  (erefl : apr_assumptions abel_row_identity = BaselineClassicalOnly).

Timeout 60 Check (abel_row_limitation : AnalysisPathRow).
Timeout 60 Check (apr_model abel_row_limitation
  : AnalysisModelFamily AbelianAnalysis.shuffle_observed).
Timeout 60 Check (erefl : apr_completion abel_row_limitation = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer abel_row_limitation = NegativeTransfer).
Timeout 60 Check
  (erefl : apr_assumptions abel_row_limitation = BaselineClassicalOnly).

(******************************************************************************)
(*     The model families exercised at their index types                      *)
(*                                                                            *)
(* One application per parameterized family pins the section 5.2 index type  *)
(* (a wrong index type is a compile error at the pair), and one application  *)
(* at tt pins a unit family. The generic check below them establishes that   *)
(* every family's adapter is typed at the execution projected from its own   *)
(* row's observed execution, for every row and every family.                 *)
(******************************************************************************)

Timeout 60 Check (fun (R : realType) (p : R.-fdist bool) =>
  amf_sample (apr_model pgl27_row_word) R p).

Timeout 60 Check (fun (R : realType) (secretP : R.-fdist 'I_5) (L : nat) =>
  amf_sample (apr_model s5_row_word) R (secretP, L)).

Timeout 60 Check (fun (R : realType) (secretP : R.-fdist 'I_10) (L : nat) =>
  amf_sample (apr_model s5x5_row_pile1_word) R (secretP, L)).

Timeout 60 Check (fun (R : realType) (L : nat) =>
  amf_sample (apr_model abel_row_limitation) R L).

Timeout 60 Check (fun R : realType =>
  amf_sample (apr_model s5_row_rand) R tt).

Timeout 60 Check (fun (row : AnalysisPathRow)
    (fam : AnalysisModelFamily (apr_observed row)) (R : realType)
    (x : amf_index fam R) =>
  amf_sample fam R x
    : @SampleAdapter R _ (OE.oe_execution (apr_observed row))).

(******************************************************************************)
(*     Mutation guards: the states the dependent model slot must reject       *)
(*                                                                            *)
(* Request 5.3: a Sampled or AnalysisBridged row with no model witness, and  *)
(* a family over the wrong execution, are compile errors, demonstrated by    *)
(* Fail. The fourth requested mutation, an executed word theorem alias       *)
(* changed back to the cut-level type, is contingent on work package A and   *)
(* is recorded as unmet in the 2026-08-13 completion response.               *)
(******************************************************************************)

Fail Check (@MkAnalysisPathRow S5Analysis.observed Sampled None
  NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder])).

Fail Check (@MkAnalysisPathRow S5Analysis.observed Sampled tt
  NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder])).

Fail Check (@MkAnalysisPathRow S5Analysis.rand_observed AnalysisBridged None
  StaticExecutedOnly (AcceptsAxioms [:: AxS5GroupOrder])).

Fail Check (@MkAnalysisPathRow S5Analysis.observed Sampled
  S5x5Analysis.word_family NoModelComparison
  (AcceptsAxioms [:: AxS5GroupOrder])).

