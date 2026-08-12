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
(* The endpoint-level security guarantee is packed in two layers. The bound   *)
(* layer is always present. The certificate layer attaches optional exact     *)
(* and asymptotic evidence for the same shuffle distribution, leaving the     *)
(* bound unchanged.                                                          *)
(*                                                                            *)
(* Records:                                                                   *)
(*   SecurityExact rho == optional exact-equality carrier:                   *)
(*                         var_dist(rho, uniform) = se_eps                   *)
(*   SecurityAsymptotic == optional geometric-convergence certificate         *)
(*   ShuffleMarginalBound R M == the bound layer: sw_L, sw_bound_eps,         *)
(*                          sw_rho_dist and the per-position sw_bound         *)
(*   ShuffleCertificateBundle R M == the certificate layer: scb_bound with    *)
(*                          the optional scb_exact and scb_asymptotic         *)
(*   ThresholdWitness M  == packages the covering scheme + PGL hypothesis     *)
(*   AlgebraicRigidity R M == combines a bundle and a threshold witness       *)
(*                                                                            *)
(*   See dropout_witness.v for [DropoutWitness], the capability-side          *)
(*   record that complements the structural ThresholdWitness here.            *)
(*                                                                            *)
(* Constructors:                                                              *)
(*   shuffle_bundle_of_bound == a bound with neither certificate attached     *)
(*   security_witness_fiber == bound from fiber-counted epsilon               *)
(*     Accepts any epsilon + proof; instances use vm_compute/case analysis.   *)
(*     Applicable to: OC (eps=1), S5 (eps=6/5), Star (eps=2(m+1)/(m+3))   *)
(*   security_witness_endpoint_inj == for perm_endpoint-injective groups             *)
(*     Epsilon = 2*(N - Tg^L)/N. Applicable to: NCycle, Abelian, Monster     *)
(*   security_witness_from_bound == bound from an arbitrary epsilon proof     *)
(*   security_witness_with_exact == bundle with the exact certificate         *)
(*                                                                            *)
(* Derived properties:                                                        *)
(*   ar_complexity      == search space bounded by |G|                        *)
(*   ar_genus_gap_dichotomy        == genus-0/bounded or genus>0/gap tradeoff           *)
(*   ar_search_gap_dichotomy == search space vs threshold gap                 *)
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
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.
Let G := pgg_G M.

(** SecurityExact: an optional exact-equality carrier.                         *)
(* Parameterised by the distribution [rho] so that the exact-value proof is    *)
(* tied to the same distribution the bound of a ShuffleCertificateBundle      *)
(* is stated at. Constructed via MkSecurityExact; used via Some in scb_exact. *)
Record SecurityExact (rho : R.-fdist {perm 'I_N'.+1}) := MkSecurityExact {
  se_eps : R;
  se_exact :
    forall s : 'I_N'.+1,
    var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho)
             (fdist_uniform (card_ord N'.+1)) = se_eps
}.

(** SecurityAsymptotic: optional asymptotic convergence certificate.           *)
(* For group settings with a valid random walk (connected Schreier graph),     *)
(* the variational distance converges to 0 geometrically in L.                *)
(*                                                                             *)
(* This is None for:                                                           *)
(*   - Uniform dealing (no random walk, e.g., den Boer five-card)             *)
(*   - Disconnected Schreier graphs (e.g., cyclic/1-gen, abelian/disjoint)    *)
(*   - Instances where the spectral gap has not yet been formalized           *)
(*                                                                             *)
(* Mirrors SchreierCertificate (pgg_schreier.v) at the bundle level.          *)
(* Cannot reuse SchreierCertificate directly due to circular dependency:       *)
(*   pgg_schreier.v imports algebraic_rigidity.v.                              *)
(*                                                                             *)
(* sa_rho_L maps word length L to the endpoint distribution — typically        *)
(* instantiated as rho_from_words L sigmas, but kept abstract here to          *)
(* avoid requiring {perm 'I_N} typed generators (which Gen_PGGTypes has        *)
(* but general MonodromyReprType may not).                                     *)
(* sa_eps_inf is the constant variation-distance floor: the bound is        *)
(*   var_dist (sigma s) uniform <= sa_eps_inf + sqrt(N) * (1 - gap)^L      *)
(* For irreducible Schreier walks (e.g. S_5) sa_eps_inf = 0 and the bound  *)
(* decays to 0. For reducible walks (e.g. S_5 x S_5 with pile-disjoint     *)
(* generators) the actual stationary distribution is uniform on the orbit, *)
(* and the gap to fdist_uniform is the constant sa_eps_inf (1 in infotheo's *)
(* un-halved L^1 var_dist convention; 1/2 in standard TV).                  *)
Record SecurityAsymptotic := MkSecurityAsymptotic {
  sa_spectral_gap : R;
  sa_eps_inf : R;
  sa_gap_pos : (0 < sa_spectral_gap)%R;
  sa_gap_le1 : (sa_spectral_gap <= 1)%R;
  sa_eps_inf_ge0 : (0 <= sa_eps_inf)%R;
  sa_rho_L : nat -> R.-fdist {perm 'I_N'.+1};
  sa_convergence : forall (L : nat) (s : 'I_N'.+1),
    (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s)
                       (sa_rho_L L))
             (fdist_uniform (card_ord N'.+1))
    <= sa_eps_inf + Num.sqrt N'.+1%:R * (1 - sa_spectral_gap) ^+ L)%R
}.

(** ShuffleMarginalBound — the single-position marginal bound of a shuffle
    distribution against the uniform distribution on sheets.
    Kind: interface.
    A constructor supplies a finite-word length, a stated epsilon, the analyzed
    distribution on permutation images, and the per-position proof that the
    one-card pushforward of that distribution is within epsilon of uniform.
    The sw_ prefix abbreviates "shuffle witness bound"; the prefix is the
    historical one of the record this one replaces and is retained on all four
    fields. *)
Record ShuffleMarginalBound := MkShuffleMarginalBound {
  (* sw_L is the finite-word length the distribution is read at. It is the
     length consumed by the dealer bridge (pgg_dealer_bridge.v) and by the
     SecurityParams of a CertifiedSolution. *)
  sw_L : nat;
  (* sw_bound_eps is the stated full-L1 upper bound on one endpoint marginal.
     It is a per-position quantity, not a coalition-view distance. *)
  sw_bound_eps : R;
  (* sw_rho_dist is the analyzed distribution on permutation images. *)
  sw_rho_dist : R.-fdist {perm 'I_N'.+1};
  (* sw_bound proves the bound separately for each starting position s. The
     guarantee is the endpoint marginal at one position; it is neither
     coalition-view privacy nor protocol security. *)
  sw_bound :
    forall (s : 'I_N'.+1),
    (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) sw_rho_dist)
              (fdist_uniform (card_ord N'.+1)) <= sw_bound_eps)%O
}.

(** ShuffleCertificateBundle — a marginal bound together with the optional
    exact-equality and asymptotic-convergence certificates of the same shuffle
    distribution.
    Kind: interface.
    A constructor supplies a ShuffleMarginalBound and, indexed on that bound's
    own sw_rho_dist, an optional SecurityExact and an optional
    SecurityAsymptotic.
    The two optional slots record the mechanism of the bound: both Some for a
    random walk with exact counting, exact only for uniform dealing, and both
    None for a fiber-counted bound. *)
Record ShuffleCertificateBundle := MkShuffleCertificateBundle {
  (* scb_bound is the marginal bound the bundle is built on. It is the only
     always-present component; the two fields below are attachments. *)
  scb_bound : ShuffleMarginalBound;
  (* scb_exact is an optional closed-form equality var_dist ... = se_eps at
     sw_rho_dist scb_bound. Attaching or emptying it leaves scb_bound and its
     epsilon unchanged. *)
  scb_exact : option (SecurityExact (sw_rho_dist scb_bound));
  (* scb_asymptotic is an optional geometric-convergence certificate for the
     same group. Attaching or emptying it leaves scb_bound and its epsilon
     unchanged. *)
  scb_asymptotic : option SecurityAsymptotic
}.

(* The cs_gap field of [tw_covering] (ts_T <= ts_k + 2 * cd_genus,
   from cover_tradeoff.v:gap_bound) is a privacy-vs-reveal gap, not
   a dropout-tolerance budget. Reconstruction in every concrete
   threshold scheme used here consumes the FULL share tuple:
   - rs_massey_exact (rs_massey_bridge.v:194): RS gives ts_T = ts_k
     at genus 0, so the gap is zero;
   - shamir_exact (cover_genus0.v:179): same statement at the
     transported covering scheme;
   - ag_massey_gap (ag_massey_bridge.v:85): AG-Massey gives
     ts_T <= ts_k + 2g for genus g > 0 codes, but its ts_recon
     (massey_recon_tuple, massey.v:369) still takes a full tuple.
   Operationalising T - k as "any T - k missing shares can be
   tolerated" requires a partial-erasure decoder, which is left
   as future work; see [reconstruct/dropout_witness.v] for the
   [DropoutWitness] record that records such a decoder when one
   is constructed.

   ThresholdWitness is purely structural: it says the covering's
   parameters fit together legally. DropoutWitness is a capability
   claim: a specific decoder exists meeting a specific bound.
   Different kinds of obligations, even though both attach to the
   same CoveringScheme. *)
Record ThresholdWitness := MkThresholdWitness {
  tw_covering : CoveringScheme M;
  tw_genus0_klein :
    cd_genus (cs_data tw_covering) = 0 -> #|G| <= klein_genus0_bound M
}.

Record AlgebraicRigidity := MkAlgebraicRigidity {
  ar_security : ShuffleCertificateBundle;
  ar_threshold : ThresholdWitness
}.

End algebraic_rigidity_records.

Arguments SecurityExact {R} {M} rho.
Arguments SecurityAsymptotic {R} {M}.
(* Under Set Implicit Arguments the field scb_bound occurs in the type of
   scb_exact, so the bundle constructor would take it implicitly. The two
   constructor directives below restore the three- and four-explicit-argument
   shapes; the two record directives keep R and M explicit at the type. *)
Arguments MkShuffleMarginalBound {R M} _ _ _ _.
Arguments MkShuffleCertificateBundle {R M} _ _ _.
Arguments ShuffleMarginalBound R M : clear implicits.
Arguments ShuffleCertificateBundle R M : clear implicits.
Arguments ThresholdWitness M : clear implicits.
Arguments AlgebraicRigidity R M : clear implicits.

(** shuffle_bundle_of_bound — the bundle carrying a marginal bound and neither
    optional certificate.
    @intent: MkShuffleCertificateBundle at a bound with scb_exact and
    scb_asymptotic both None. *)
Definition shuffle_bundle_of_bound R M (b : ShuffleMarginalBound R M)
  : ShuffleCertificateBundle R M := MkShuffleCertificateBundle b None None.

(******************************************************************************)
(*     Fiber-Counted ShuffleMarginalBound Constructor                         *)
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

(** security_witness_fiber — the marginal bound of a pointwise fiber estimate.
    Kind: main.
    Why: packages the generic fiber-based var_dist bound used by the OC, S5 and
         Star instances, so callers only need to supply the epsilon estimate.
*)
Definition security_witness_fiber (L : nat)
    (Hlfree : @weval_inj M L)
    (epsilon : R)
    (Hbound : forall s : 'I_n'.+2,
      (var_dist (fdistmap (fun sigma : {perm 'I_n'.+2} => sigma s)
                         (rho_from_words L sigmas))
               (fdist_uniform (card_ord n'.+2)) <= epsilon)%O)
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L epsilon
    (rho_from_words L sigmas) Hbound.

End fiber_security.

(******************************************************************************)
(*     Direct Endpoint ShuffleMarginalBound Constructor                       *)
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

(** security_witness_endpoint_inj — direct endpoint witness under injectivity.
    Kind: main.
    Why: when perm_endpoint is injective on achievable(L), the epsilon bound
         improves to 2*(N - Tg^L)/N, handled by this specialized constructor.
*)
Definition security_witness_endpoint_inj (L : nat)
    (Hlfree : @weval_inj M L)
    (Hinj_s : forall s : 'I_n'.+2,
      {in @achievable M L &,
       injective (fun sigma : {perm 'I_n'.+2} => sigma s)})
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L _
    (rho_from_words L sigmas)
    (var_dist_endpoint_direct Hlfree Hinj_s).

End direct_endpoint_security.

(******************************************************************************)
(*     Convenience Constructors                                               *)
(*                                                                            *)
(* security_witness_from_bound: build a ShuffleMarginalBound from a bound.    *)
(*   Use this when only an upper bound on var_dist is available (e.g.,        *)
(*   spectral / Pinsker / DPI estimates).                                     *)
(*                                                                            *)
(* security_witness_with_exact: build a ShuffleCertificateBundle from a bound *)
(*   and an exact-equality proof (scb_exact := Some ...). Use this when a     *)
(*   closed-form var_dist equality is known alongside the bound.              *)
(******************************************************************************)

Section security_witness_constructors.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.

(** security_witness_from_bound — the marginal bound of an arbitrary epsilon
    proof.
    Kind: main.
    Why: convenience wrapper used when only spectral / Pinsker / DPI upper
         bounds are available.
*)
Definition security_witness_from_bound (L : nat)
    (eps : R)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (Hbound : forall s : 'I_N'.+1,
      (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
                (fdist_uniform (card_ord N'.+1)) <= eps)%O)
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L eps rho_dist Hbound.

(** security_witness_with_exact — the certificate bundle of a bound and an
    exact equality.
    Kind: main.
    Why: used when closed-form var_dist equalities are known (e.g., structured
         group orbits), filling scb_exact with the equality proof.
*)
Definition security_witness_with_exact (L : nat)
    (bound_eps : R)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (Hbound : forall s : 'I_N'.+1,
      (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
                (fdist_uniform (card_ord N'.+1)) <= bound_eps)%O)
    (exact_eps : R)
    (Hexact : forall s : 'I_N'.+1,
      var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
               (fdist_uniform (card_ord N'.+1)) = exact_eps)
    : ShuffleCertificateBundle R M :=
  @MkShuffleCertificateBundle R M
    (@MkShuffleMarginalBound R M L bound_eps rho_dist Hbound)
    (Some (@MkSecurityExact R M rho_dist exact_eps Hexact))
    None.

End security_witness_constructors.

(******************************************************************************)
(*     Derived Properties                                                     *)
(******************************************************************************)

Section derived_properties.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Variable ar : AlgebraicRigidity R M.

Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(** Complexity: search space is bounded by |G| *)
Lemma ar_complexity (L : nat) : @search_space M L <= #|G|.
Proof. exact: search_space_leG. Qed.

(** Tradeoff: either genus-0 with bounded |G|, or positive genus with gap *)
Lemma ar_genus_gap_dichotomy :
  let cs := tw_covering (ar_threshold ar) in
  (cd_genus (cs_data cs) = 0 /\
   #|G| <= klein_genus0_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@security_threshold_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_klein M (ar_threshold ar))).
Qed.

(** Search-gap tradeoff: search space bounded or threshold has gap *)
Lemma ar_search_gap_dichotomy (L : nat) :
  let cs := tw_covering (ar_threshold ar) in
  (@search_space M L <= klein_genus0_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@search_gap_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_klein M (ar_threshold ar)) L).
Qed.

(** ar_large_group_forces_gap — large monodromy groups force positive genus.
    Kind: main.
    Why: packages the "too many generators to fit in genus-zero" dichotomy as
         an AlgebraicRigidity-indexed consequence used by landscape tables.
    Naming: components describe the chain "AR + large group + forces + gap";
            this domain-level phrase is clearer than any shortened MathComp-
            suffix variant, so the 5-component name is retained intentionally.
*)
Lemma ar_large_group_forces_gap :
  let cs := tw_covering (ar_threshold ar) in
  klein_genus0_bound M < #|G| ->
  0 < cd_genus (cs_data cs).
Proof.
move=> /=.
exact (@large_group_forces_gap M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_klein M (ar_threshold ar))).
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
    (G_stable : forall g, g \in pgg_G M ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1,
         rp_content (cs_plug (tw_covering (ar_threshold ar)))
           (@pgg_rho M g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i)) =
         tnth [tuple rp_content (cs_plug (tw_covering (ar_threshold ar)))
                 (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
              | j < (ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1]
              (rp_monodromy (cs_plug (tw_covering (ar_threshold ar))) g i)) :
  P \in pgg_G M ->
  ts_valid (cs_scheme (tw_covering (ar_threshold ar))) s
          [tuple rp_content (cs_plug (tw_covering (ar_threshold ar)))
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
          | j < (ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1] ->
  pgg_recon_endpoints HT
    (rp_content (cs_plug (tw_covering (ar_threshold ar)))) P = s.
Proof.
move=> PG Hvalid.
apply: (pgg_recon_monodromy_correct
          (perm := rp_monodromy (cs_plug (tw_covering (ar_threshold ar)))));
  [exact: subxx | exact: G_stable | exact: PG | exact: Hvalid
  | exact: rp_recon_invariant].
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
(*     SecurityProfile: ShuffleMarginalBound + L* + nontriviality             *)
(*                                                                            *)
(* A SecurityProfile bundles a ShuffleMarginalBound with:                     *)
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
Variable M : MonodromyReprWithGeneratorType.

Local Open Scope ring_scope.

Let eps_bound := (2%:R : R).

Record SecurityProfile := MkSecurityProfile {
  sp_Lstar : nat ;
  sp_witness : ShuffleMarginalBound R M ;
  sp_at_Lstar : sw_L sp_witness = sp_Lstar ;
  sp_nontrivial : is_true (Num.lt (sw_bound_eps sp_witness) eps_bound)
}.

(* Constructor from AlgebraicRigidity, when epsilon < 2 can be proved *)
Definition ar_security_profile (ar : AlgebraicRigidity R M)
    (Hlt2 : is_true
      (Num.lt (sw_bound_eps (scb_bound (ar_security ar))) eps_bound))
    : SecurityProfile :=
  @MkSecurityProfile
    (sw_L (scb_bound (ar_security ar)))
    (scb_bound (ar_security ar))
    erefl
    Hlt2.

End security_profile.

Arguments SecurityProfile R M : clear implicits.

(******************************************************************************)
(*     CertifiedSolution: Bridge from computable solver to proof witness     *)
(*                                                                           *)
(*     Connects the nat-level SecurityParams (from dealer_solve/raag_template *)
(*     via vm_compute) to the proof-level ShuffleMarginalBound.              *)
(*                                                                           *)
(*     Since the solver uses raag_fiber_eps_nat (same formula as the witness *)
(*     fiber counting), cs_eps_le is typically lexx (reflexivity) for all    *)
(*     RAAG instances.                                                       *)
(******************************************************************************)

Section certified_solution.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Local Open Scope ring_scope.

Record CertifiedSolution := MkCertifiedSolution {
  cs_params    : SecurityParams ;
  cs_witness   : ShuffleMarginalBound R M ;
  cs_L_eq      : sw_L cs_witness = sp_L cs_params ;
  cs_denom_pos : (0 < (sp_eps cs_params).2)%N ;
  cs_eps_le    : (sw_bound_eps cs_witness <=
                  (sp_eps cs_params).1%:R / (sp_eps cs_params).2%:R)%O
}.

End certified_solution.

Arguments CertifiedSolution R M : clear implicits.

(******************************************************************************)
(*     Generic CertifiedSolution Constructor                                  *)
(*                                                                            *)
(* Any ShuffleMarginalBound with known rational epsilon gives a               *)
(* CertifiedSolution.                                                         *)
(* Works for ALL groups — RAAG and non-RAAG alike (Monster, Star, S5, etc.). *)
(*                                                                            *)
(* Architecture layers:                                                       *)
(*   Layer 1 (Computable — RAAG only):                                       *)
(*     RAAGDesc -> dealer_solve -> SecurityParams (uses vm_compute)           *)
(*   Layer 2 (Proof-level — ANY MonodromyReprWithGeneratorType):                  *)
(*     ShuffleMarginalBound -> certified_from_bound -> CertifiedSolution      *)
(*     AlgebraicRigidity + PGGInterface + G_stable -> ar_protocol_correct     *)
(******************************************************************************)

Section certified_from_bound.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Local Open Scope ring_scope.

(* R and M are inferable from the bound argument, so section discharge demotes
   them to implicit arguments; callers that pin the group write
   @certified_from_bound R M b .... *)

(** certified_from_bound — assemble a CertifiedSolution from a marginal bound.
    @intent: bundles the rational epsilon certificate together with the bound
    into a CertifiedSolution, the interface consumed by the certified
    security tables in pgg_protocol_landscape.v. *)
Definition certified_from_bound
    (b : ShuffleMarginalBound R M)
    (eps_n eps_d : nat) (Hd : (0 < eps_d)%N)
    (Hle : (sw_bound_eps b <= eps_n%:R / eps_d%:R)%O)
    : CertifiedSolution R M :=
  @MkCertifiedSolution R M
    (MkSP (@pgg_ngens' M).+1 (pgg_N' M).+1 (sw_L b) (eps_n, eps_d))
    b erefl Hd Hle.

End certified_from_bound.

(* Exact-equality evidence is carried by ShuffleCertificateBundle above,      *)
(* whose scb_exact field is an optional SecurityExact at the bound's own      *)
(* distribution. Build a ShuffleMarginalBound with                            *)
(* `security_witness_from_bound` and a ShuffleCertificateBundle with          *)
(* `security_witness_with_exact`.                                             *)
