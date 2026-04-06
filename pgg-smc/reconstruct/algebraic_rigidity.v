(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Algebraic Rigidity: One Algebraic Choice Determines Security + Threshold  *)
(*                                                                            *)
(* Given a monodromy representation with generators M, the algebraic          *)
(* structure determines:                                                      *)
(*   1. Complexity — search_space L <= |G| (from pgg_interface.v)            *)
(*   2. Security — var_dist(endpoint, uniform) <= epsilon (endpoint bound)   *)
(*   3. Threshold — gap <= 2*genus, with genus-0 -> gap=0 (covering_scheme)  *)
(*                                                                            *)
(* The key insight: all three are consequences of the single algebraic        *)
(* choice (G, rho, sigmas). No further degrees of freedom exist.             *)
(*                                                                            *)
(* Galois-theoretic interpretation:                                           *)
(*   The fiber at a branch point consists of roots of the minimal polynomial *)
(*   of K(C) over K(X). The monodromy group G permutes these roots,         *)
(*   making G the Galois group of the Galois closure. This connects PGG     *)
(*   to Galois theory of function fields: the algebraic choice (G, rho,     *)
(*   sigmas) determines the field extension K(C)/K(X) up to isomorphism.    *)
(*   Note: this is conceptual — field arithmetic on roots is irrelevant     *)
(*   to the permutation action that PGG uses.                                *)
(*                                                                            *)
(* Records:                                                                   *)
(*   SecurityWitness R M == packages the endpoint-level security guarantee    *)
(*   ThresholdWitness M  == packages the covering scheme + PGL hypothesis     *)
(*   AlgebraicRigidity R M == combines both into a unified witness            *)
(*                                                                            *)
(* Constructors:                                                              *)
(*   security_witness_fiber == SecurityWitness from fiber-counted epsilon      *)
(*     Accepts any epsilon + proof; instances use vm_compute/case analysis.   *)
(*     Applicable to: OC (eps=1), S5 (eps=6/5), Star (eps=2(m+1)/(m+3))   *)
(*   security_witness_endpoint_inj == for perm_endpoint-injective groups             *)
(*     Epsilon = 2*(N - Tg^L)/N. Applicable to: NCycle, Abelian, Monster     *)
(*                                                                            *)
(* Derived properties:                                                        *)
(*   ar_complexity      == search space bounded by |G|                        *)
(*   ar_tradeoff        == genus-0/bounded or genus>0/gap tradeoff           *)
(*   ar_search_gap_tradeoff == search space vs threshold gap                 *)
(*   ar_large_group_forces_gap == |G| > PGL -> genus > 0                    *)
(*   ar_gap_bound       == threshold gap <= 2*genus                          *)
(*   ar_protocol_correct == end-to-end protocol correctness                  *)
(*                                                                            *)
(* RAAG-specific derived properties:                                          *)
(*   ar_search_space_chain == search_space <= n_traces <= Tg^L               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_collusion_bound pgg_security_solver.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.

(******************************************************************************)
(*     Record Definitions                                                     *)
(******************************************************************************)

Section algebraic_rigidity_records.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Let N' := pgg_N' M.
Let G := pgg_G M.

Record SecurityWitness := MkSecurityWitness {
  sw_L : nat;
  sw_epsilon : R;
  sw_rho_dist : R.-fdist {perm 'I_N'.+1};
  sw_endpoint_bound :
    forall (s : 'I_N'.+1),
    (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) sw_rho_dist)
              (fdist_uniform (card_ord N'.+1)) <= sw_epsilon)%O
}.

Record ThresholdWitness := MkThresholdWitness {
  tw_covering : CoveringScheme M;
  tw_genus0_pgl :
    cd_genus (cs_data tw_covering) = 0 -> #|G| <= pgl_bound M
}.

Record AlgebraicRigidity := MkAlgebraicRigidity {
  ar_security : SecurityWitness;
  ar_threshold : ThresholdWitness
}.

End algebraic_rigidity_records.

Arguments SecurityWitness R M : clear implicits.
Arguments ThresholdWitness M : clear implicits.
Arguments AlgebraicRigidity R M : clear implicits.

(******************************************************************************)
(*     Fiber-Counted SecurityWitness Constructor                              *)
(*                                                                            *)
(* For groups where perm_endpoint is NOT injective on achievable(L), the direct      *)
(* endpoint bound is invalid. Instead, each instance proves its own           *)
(* var_dist bound by fiber counting (case analysis, vm_compute, or            *)
(* parametric algebra). The constructor accepts epsilon + proof directly.      *)
(*                                                                            *)
(* Applicable to: OC (eps=1), S5 (eps=6/5), Star (eps=2(m+1)/(m+3))       *)
(******************************************************************************)

Section fiber_security.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

Definition security_witness_fiber (L : nat)
    (Hlfree : @weval_inj M L)
    (epsilon : R)
    (Hbound : forall s : 'I_n'.+2,
      (var_dist (fdistmap (fun sigma : {perm 'I_n'.+2} => sigma s)
                         (rho_from_words L sigmas))
               (fdist_uniform (card_ord n'.+2)) <= epsilon)%O)
    : SecurityWitness R M :=
  @MkSecurityWitness R M L epsilon
    (rho_from_words L sigmas) Hbound.

End fiber_security.

(******************************************************************************)
(*     Direct Endpoint SecurityWitness Constructor                            *)
(*                                                                            *)
(* When perm_endpoint is injective on achievable(L) for each starting sheet s,       *)
(* the endpoint distribution is closer to uniform than the DPI bound gives.  *)
(* Epsilon = 2*(N - Tg^L)/N (denominator N, not N!).                         *)
(*                                                                            *)
(* Applicable to: Cyclic (Tg=1, perm_endpoint trivially injective),                 *)
(*                Abelian (Tg=2, N=4, perm_endpoint injective on achievable(1))     *)
(* NOT applicable to: Star, S5, OC, Monster (perm_endpoint not injective on         *)
(*                    achievable for all sheets)                              *)
(******************************************************************************)

Section direct_endpoint_security.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

Definition security_witness_endpoint_inj (L : nat)
    (Hlfree : @weval_inj M L)
    (Hinj_s : forall s : 'I_n'.+2,
      {in @achievable M L &,
       injective (fun sigma : {perm 'I_n'.+2} => sigma s)})
    : SecurityWitness R M :=
  @MkSecurityWitness R M L _
    (rho_from_words L sigmas)
    (var_dist_endpoint_direct Hlfree Hinj_s).

End direct_endpoint_security.

(******************************************************************************)
(*     Derived Properties                                                     *)
(******************************************************************************)

Section derived_properties.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Variable ar : AlgebraicRigidity R M.

Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(** Complexity: search space is bounded by |G| *)
Lemma ar_complexity (L : nat) : @search_space M L <= #|G|.
Proof. exact: search_space_leG. Qed.

(** Tradeoff: either genus-0 with bounded |G|, or positive genus with gap *)
Lemma ar_tradeoff :
  let cs := tw_covering (ar_threshold ar) in
  (cd_genus (cs_data cs) = 0 /\
   #|G| <= pgl_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@security_threshold_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_pgl M (ar_threshold ar))).
Qed.

(** Search-gap tradeoff: search space bounded or threshold has gap *)
Lemma ar_search_gap_tradeoff (L : nat) :
  let cs := tw_covering (ar_threshold ar) in
  (@search_space M L <= pgl_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@search_gap_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_pgl M (ar_threshold ar)) L).
Qed.

(** Large groups force positive genus *)
Lemma ar_large_group_forces_gap :
  let cs := tw_covering (ar_threshold ar) in
  pgl_bound M < #|G| ->
  0 < cd_genus (cs_data cs).
Proof.
move=> /=.
exact (@large_group_forces_gap M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_pgl M (ar_threshold ar))).
Qed.

(** Gap bound: threshold gap is bounded by twice the genus *)
Lemma ar_gap_bound :
  let cs := tw_covering (ar_threshold ar) in
  ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <= 2 * cd_genus (cs_data cs).
Proof. move=> /=. exact: gap_bound. Qed.

(** Protocol correctness: perm-compatible scheme + valid shares + G-stable starts *)
Lemma ar_protocol_correct (PI : PGGInterface M)
    (HT : ts_T' (cs_scheme (tw_covering (ar_threshold ar))) = pi_T' PI)
    (s : 'I_N) (P : pgg_gT M)
    (G_stable : forall g, g \in G ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1,
         @pgg_rho M g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i) =
         tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI))
              (cs_perm (tw_covering (ar_threshold ar)) g i)) :
  P \in G ->
  ts_valid (cs_scheme (tw_covering (ar_threshold ar))) s
          (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) ->
  pgg_recon_endpoints HT P = s.
Proof.
move=> PG Hvalid.
apply: (pgg_hidden_invariant_perm (perm := cs_perm (tw_covering (ar_threshold ar)))) => //.
exact: cs_perm_compatible.
Qed.

End derived_properties.

(******************************************************************************)
(*     RAAG-Specific Derived Properties                                       *)
(******************************************************************************)

Section raag_derived_properties.

Variable R : realType.
Variable M : RAAGType.
Variable ar : AlgebraicRigidity R M.

Let Tg := (@pgg_ngens' M).+1.

(** Search space chain: search_space <= n_traces <= Tg^L (RAAG-specific) *)
Lemma ar_search_space_chain (L : nat) :
  (@search_space M L <= @n_traces M L) && (@n_traces M L <= Tg ^ L).
Proof. exact: search_space_chain. Qed.

End raag_derived_properties.

(******************************************************************************)
(*     SecurityProfile: SecurityWitness + L* + nontriviality                  *)
(*                                                                            *)
(* A SecurityProfile bundles a SecurityWitness with:                          *)
(*   - sp_Lstar: the specific word length (turning point)                     *)
(*   - sp_nontrivial: epsilon < 2 (strictly better than trivial bound)        *)
(*                                                                            *)
(* Why < 2: The DPI epsilon is always < 2 when Tg^L >= 1 (trivially true).   *)
(* The threshold < 1 requires the direct endpoint bound which only some       *)
(* instances can provide. Using < 2 means ALL existing instances can build    *)
(* a SecurityProfile immediately.                                             *)
(*                                                                            *)
(* Why no monotonicity: weval_inj(L) does NOT imply weval_inj(L+1).          *)
(* OC has weval_inj(2) but not weval_inj(3) (generator cubes collide).       *)
(* So SecurityProfile only requires weval_inj at L*, not everywhere.          *)
(******************************************************************************)

Section security_profile.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.

Local Open Scope ring_scope.

Let eps_bound := (2%:R : R).

Record SecurityProfile := MkSecurityProfile {
  sp_Lstar : nat ;
  sp_witness : SecurityWitness R M ;
  sp_at_Lstar : sw_L sp_witness = sp_Lstar ;
  sp_nontrivial : is_true (Num.lt (sw_epsilon sp_witness) eps_bound)
}.

(* Constructor from AlgebraicRigidity, when epsilon < 2 can be proved *)
Definition ar_security_profile (ar : AlgebraicRigidity R M)
    (Hlt2 : is_true (Num.lt (sw_epsilon (ar_security ar)) eps_bound))
    : SecurityProfile :=
  @MkSecurityProfile
    (sw_L (ar_security ar))
    (ar_security ar)
    erefl
    Hlt2.

End security_profile.

Arguments SecurityProfile R M : clear implicits.

(******************************************************************************)
(*     CertifiedSolution: Bridge from computable solver to proof witness     *)
(*                                                                           *)
(*     Connects the nat-level SecurityParams (from dealer_solve/raag_template *)
(*     via vm_compute) to the proof-level SecurityWitness.                   *)
(*                                                                           *)
(*     Since the solver uses raag_fiber_eps_nat (same formula as the witness *)
(*     fiber counting), cs_eps_le is typically lexx (reflexivity) for all    *)
(*     RAAG instances.                                                       *)
(******************************************************************************)

Section certified_solution.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.

Local Open Scope ring_scope.

Record CertifiedSolution := MkCertifiedSolution {
  cs_params    : SecurityParams ;
  cs_witness   : SecurityWitness R M ;
  cs_L_eq      : sw_L cs_witness = sp_L cs_params ;
  cs_denom_pos : (0 < (sp_eps cs_params).2)%N ;
  cs_eps_le    : (sw_epsilon cs_witness <=
                  (sp_eps cs_params).1%:R / (sp_eps cs_params).2%:R)%O
}.

End certified_solution.

Arguments CertifiedSolution R M : clear implicits.

(******************************************************************************)
(*     Generic CertifiedSolution Constructor                                  *)
(*                                                                            *)
(* Any SecurityWitness with known rational epsilon gives a CertifiedSolution. *)
(* Works for ALL groups — RAAG and non-RAAG alike (Monster, Star, S5, etc.). *)
(*                                                                            *)
(* Architecture layers:                                                       *)
(*   Layer 1 (Computable — RAAG only):                                       *)
(*     RAAGDesc -> dealer_solve -> SecurityParams (uses vm_compute)           *)
(*   Layer 2 (Proof-level — ANY GeneratedMonodromyReprType):                  *)
(*     SecurityWitness -> certified_from_witness -> CertifiedSolution         *)
(*     AlgebraicRigidity + PGGInterface + G_stable -> ar_protocol_correct     *)
(******************************************************************************)

Section certified_from_witness.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.

Local Open Scope ring_scope.

Definition certified_from_witness
    (sw : SecurityWitness R M)
    (eps_n eps_d : nat) (Hd : (0 < eps_d)%N)
    (Hle : (sw_epsilon sw <= eps_n%:R / eps_d%:R)%O)
    : CertifiedSolution R M :=
  @MkCertifiedSolution R M
    (MkSP (@pgg_ngens' M).+1 (pgg_N' M).+1 (sw_L sw) (eps_n, eps_d))
    sw erefl Hd Hle.

End certified_from_witness.

(******************************************************************************)
(*     SecurityWitnessEx: Extended SecurityWitness with exact + bound         *)
(*                                                                            *)
(* The original SecurityWitness only stores an upper bound on var_dist.       *)
(* SecurityWitnessEx stores both the exact value and a (possibly looser)      *)
(* upper bound, with a consistency proof that exact <= bound.                 *)
(*                                                                            *)
(* A coercion swe_to_sw lets SecurityWitnessEx be used wherever               *)
(* SecurityWitness is expected, ensuring backward compatibility.              *)
(*                                                                            *)
(* Constructors:                                                              *)
(*   security_witness_exact == from exact computation (bound = exact)         *)
(*   security_witness_from_bound == from separate exact and bound proofs      *)
(******************************************************************************)

Section security_witness_extended.

Variable R : realType.
Variable M : GeneratedMonodromyReprType.
Let N' := pgg_N' M.

Record SecurityWitnessEx := MkSecurityWitnessEx {
  swe_L : nat ;
  swe_rho_dist : R.-fdist {perm 'I_N'.+1} ;

  (* Exact security value *)
  swe_exact_eps : R ;
  swe_exact :
    forall s : 'I_N'.+1,
    var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) swe_rho_dist)
             (fdist_uniform (card_ord N'.+1)) = swe_exact_eps ;

  (* Upper bound (may be looser — e.g., spectral/Pinsker) *)
  swe_bound_eps : R ;
  swe_bound :
    forall s : 'I_N'.+1,
    (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) swe_rho_dist)
              (fdist_uniform (card_ord N'.+1)) <= swe_bound_eps)%O ;

  (* Consistency *)
  swe_consistent : (swe_exact_eps <= swe_bound_eps)%O ;
}.

Definition swe_to_sw (swe : SecurityWitnessEx) : SecurityWitness R M :=
  @MkSecurityWitness R M (swe_L swe) (swe_bound_eps swe)
    (swe_rho_dist swe) (swe_bound swe).

Coercion swe_to_sw : SecurityWitnessEx >-> SecurityWitness.

(** Constructor from exact computation — fills both exact and bound *)
Definition security_witness_exact (L : nat)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (eps : R)
    (Hexact : forall s : 'I_N'.+1,
      var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
               (fdist_uniform (card_ord N'.+1)) = eps)
    : SecurityWitnessEx :=
  @MkSecurityWitnessEx L rho_dist eps Hexact eps
    (fun s => eq_ind_r (fun v => (v <= eps)%O)
                        (Order.POrderTheory.lexx eps) (Hexact s))
    (Order.POrderTheory.lexx eps).

(** Constructor from separate exact and bound proofs *)
Definition security_witness_from_bound (L : nat)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (exact_eps bound_eps : R)
    (Hexact : forall s : 'I_N'.+1,
      var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
               (fdist_uniform (card_ord N'.+1)) = exact_eps)
    (Hbound : forall s : 'I_N'.+1,
      (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
                (fdist_uniform (card_ord N'.+1)) <= bound_eps)%O)
    (Hconsist : (exact_eps <= bound_eps)%O)
    : SecurityWitnessEx :=
  @MkSecurityWitnessEx L rho_dist exact_eps Hexact bound_eps Hbound Hconsist.

End security_witness_extended.

Arguments SecurityWitnessEx R M : clear implicits.
Arguments swe_to_sw {R M} swe.
