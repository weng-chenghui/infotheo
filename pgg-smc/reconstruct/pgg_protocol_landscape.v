(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Protocol Parameter Landscape                                           *)
(*                                                                            *)
(* Architecture (two-phase pipeline):                                         *)
(*                                                                            *)
(*   Phase 1: DISCOVERY               Phase 2: CERTIFICATION                  *)
(*   (find L' for a group)            (prove both-sides at L')                *)
(*                                                                            *)
(*   SchreierCertificate                                                      *)
(*   {lambda_gap, convergence}                                                *)
(*          |                                                                 *)
(*          | eps(L) = sqrt(N)*(1-lam)^L                                      *)
(*          | monotone decreasing                                             *)
(*          v                                                                 *)
(*   Find smallest L' where           Instance construction at L':            *)
(*   eps(L') < target                                                         *)
(*          |                         1. Prove weval_inj(L')                  *)
(*          |   (or: vm_compute       2. Prove security bound at L':          *)
(*          |    fiber_eps_scan          - fiber counting, OR                  *)
(*          |    finds L' directly)      - endpoint_inj, OR                   *)
(*          |                            - from_entropy (Pinsker)             *)
(*          |                                    |                            *)
(*          +-----> L' -------->  SecurityWitness R M                         *)
(*                                {L', eps, rho_dist, bound}                  *)
(*                                       |                                    *)
(*                                       |    CoveringScheme M                *)
(*                                       |    {genus, gap, perm}              *)
(*                                       |         |                          *)
(*                                       |    ThresholdWitness M              *)
(*                                       |    {covering, genus0_pgl}          *)
(*                                       |         |                          *)
(*                                       v         v                          *)
(*                                AlgebraicRigidity R M                       *)
(*                                = MkAlgebraicRigidity sw tw                 *)
(*                                       |                                    *)
(*                           +-----------+-----------+                        *)
(*                           v           v           v                        *)
(*                     ar_genus_gap_dichotomy  ar_gap_bound  ar_protocol_correct         *)
(*                                       |                                    *)
(*                                       v                                    *)
(*                   LANDSCAPE (this file, from ar)                           *)
(*                   Security side:                                           *)
(*                   +-- ar_security_per_position  (var_dist <= eps)              *)
(*                   +-- ar_entropy             (H(P_s) from sw_rho_dist)     *)
(*                   +-- ar_entropy_gap         (D = log N - H)              *)
(*                   +-- ar_var_dist_from_entropy (Pinsker bridge)            *)
(*                   Threshold side:                                          *)
(*                   +-- ar_genus0_exact        (genus 0 -> T <= k)           *)
(*                   +-- ar_genus1_gap2         (genus 1 -> T <= k + 2)      *)
(*                   +-- ar_hurwitz             (genus >= 2 -> |G|<=84(g-1)) *)
(*                                                                            *)
(* Phase 1 tools: pgg_schreier.v (spectral gap), pgg_security_solver.v      *)
(*   (vm_compute scans), pgg_security_demo.v (convergence diagnostics)      *)
(* Phase 2 tools: algebraic_rigidity.v (SecurityWitness, AlgebraicRigidity) *)
(*   pgg_entropy_security.v (EntropyWitness, Pinsker bridge)                *)
(*   pgg_collusion_bound.v (rho_from_words, var_dist bounds)                *)
(*                                                                            *)
(* The 3-regime threshold landscape:                                          *)
(*                                                                            *)
(*   Covering genus | Threshold    | Group constraint  | Available to         *)
(*   ---------------+--------------+-------------------+--------------------  *)
(*   g = 0          | (k, k) exact | |G| <= PGL(2,N)   | Small groups only   *)
(*   g = 1          | (k, k+2)    | None              | Any group            *)
(*   g >= 2         | (k, k+2g)   | |G| <= 84(g-1)    | Growing with g      *)
(*                                                                            *)
(* Key insight: genus 1 is the universal fallback. Any group gets (k, k+2)   *)
(* threshold regardless of |G|. The worst-case threshold gap is 2.           *)
(*                                                                            *)
(* Sources:                                                                   *)
(*   Genus 0: |G| <= PGL(2,N) -- cover_genus0.v, klein_genus0_bound.v               *)
(*   Genus 1: no group bound -- Silverman, Arithmetic of Elliptic Curves,   *)
(*     Ch. III.4 (isogenies give arbitrarily large monodromy groups)         *)
(*   Genus >= 2: |G| <= 84(g-1) -- Hurwitz 1893, Miranda Thm V.1.3         *)
(*   Threshold gap: T <= k + 2g -- Goppa bound on AG codes, cs_gap          *)
(*   Security: eps from var_dist -- pgg_collusion_bound.v                   *)
(*   Entropy: H from fiber counts -- pgg_entropy_security.v                 *)
(*   Spectral: Schreier convergence -- pgg_schreier.v                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum ssralg.
From mathcomp Require Import boolp reals exp.
From infotheo Require Import realType_ext realType_ln fdist proba
                             variation_dist.
From infotheo Require Import divergence entropy pinsker.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj.
From pgg_smc Require Import pgg_collusion_bound pgg_entropy_security
                            pgg_schreier.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.

Import GRing.Theory Num.Theory.

(******************************************************************************)
(*     Section 1: Security from Group Choice                                  *)
(******************************************************************************)

Section security_from_group.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(** security_per_position — re-exports sw_bound at each secret sheet.
    Kind: example.
    Why: landscape-facing restatement of the SecurityWitness epsilon bound,
         pinning the dependency on sw for downstream callers.
*)
Lemma security_per_position (sw : SecurityWitness R M) (s : 'I_N) :
  (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s) (sw_rho_dist sw))
            (fdist_uniform (card_ord N)) <= sw_bound_eps sw)%O.
Proof. exact: sw_bound. Qed.

(** complexity_from_group — search space is bounded by the group order.
    Kind: example.
    Why: landscape-facing restatement of search_space_leG, used as the
         complexity axis of the security-vs-complexity tradeoff table.
*)
Lemma complexity_from_group (L : nat) : (@search_space M L <= #|G|)%N.
Proof. exact: search_space_leG. Qed.

End security_from_group.

(******************************************************************************)
(*     Section 2: Threshold from Covering Choice                              *)
(******************************************************************************)

Section threshold_from_covering.

Variable M : MonodromyReprWithGeneratorType.

Let G := pgg_G M.

(** genus0_option - genus-0 coverings give the exact threshold T <= k.
    Kind: main.
    Why: records the best-case threshold option for protocol designers.
*)
Theorem genus0_option (cs : CoveringScheme M) :
  cd_genus (cs_data cs) = 0 ->
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N.
Proof. exact: genus0_exact. Qed.

(** genus1_universal_option - genus-1 coverings force at most gap 2.
    Kind: main.
    Why: documents the universal genus-1 slot of the landscape, T <= k + 2.
*)
Theorem genus1_universal_option (cs : CoveringScheme M) :
  cd_genus (cs_data cs) = 1 ->
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2)%N.
Proof.
move=> Hg1.
have := cs_gap cs.
by rewrite Hg1 muln1.
Qed.

(** gap_from_genus - threshold gap is bounded by 2 * genus.
    Kind: main.
    Why: central inequality of the PGG landscape linking geometric genus to
    the protocol gap T - k.
*)
Theorem gap_from_genus (cs : CoveringScheme M) :
  (ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <= 2 * cd_genus (cs_data cs))%N.
Proof. exact: gap_bound. Qed.

End threshold_from_covering.

(******************************************************************************)
(*     Section 3: The Bridge -- |G| Constrains Covering Options              *)
(******************************************************************************)

Section group_constrains_covering.

Variable M : MonodromyReprWithGeneratorType.

Let G := pgg_G M.

(** genus0_requires_small_group - large groups cannot live on genus-0 coverings.
    Kind: helper.
    Why: contrapositive bridge from the PGL bound to strict positivity of
    genus, used to rule out exact thresholds when |G| is too large.
    Used by: landscape_tradeoff and ar_large_group_forces_genus.
*)
Lemma genus0_requires_small_group (cs : CoveringScheme M)
    (genus0_pgl : cd_genus (cs_data cs) = 0 -> (#|G| <= klein_genus0_bound M)%N) :
  (klein_genus0_bound M < #|G|)%N ->
  (0 < cd_genus (cs_data cs))%N.
Proof. exact: large_group_forces_gap genus0_pgl. Qed.

(** large_group_minimum_gap - large-group, genus-1 case yields gap 2.
    Kind: helper.
    Why: combines the large-group hypothesis with the genus-1 universal option
    to show the minimum achievable gap in that regime.
    Used by: landscape tabulations in the landscape_tradeoff theorem.
*)
Corollary large_group_minimum_gap (cs : CoveringScheme M)
    (genus0_pgl : cd_genus (cs_data cs) = 0 -> (#|G| <= klein_genus0_bound M)%N) :
  (klein_genus0_bound M < #|G|)%N ->
  cd_genus (cs_data cs) = 1 ->
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2)%N.
Proof.
move=> Hlarge Hg1.
exact: genus1_universal_option Hg1.
Qed.

(** landscape_tradeoff - the two-branch landscape trade-off between |G| and gap.
    Kind: main.
    Why: packages the headline result of the paper: either the covering is
    genus-0 with a small group and exact threshold, or the group is larger and
    the gap is paid for by strictly positive genus.
*)
Theorem landscape_tradeoff (cs : CoveringScheme M)
    (genus0_pgl : cd_genus (cs_data cs) = 0 -> (#|G| <= klein_genus0_bound M)%N) :
  (cd_genus (cs_data cs) = 0 /\
   (#|G| <= klein_genus0_bound M)%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N)
  \/
  ((0 < cd_genus (cs_data cs))%N /\
   (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs))%N).
Proof. exact: security_threshold_tradeoff genus0_pgl. Qed.

End group_constrains_covering.

(******************************************************************************)
(*     Section 4: Hurwitz Bound for g >= 2                                   *)
(******************************************************************************)

Section hurwitz.

Variable M : MonodromyReprWithGeneratorType.

Let G := pgg_G M.

(* Axiom: Hurwitz's automorphism theorem (1893).
   Source: Hurwitz, Math. Ann. 41 (1893), 403-442.
   Also: Miranda, "Algebraic Curves and Riemann Surfaces", Thm V.1.3. *)
Axiom hurwitz_bound :
  forall (cs : CoveringScheme M),
  (2 <= cd_genus (cs_data cs))%N ->
  (#|G| <= 84 * (cd_genus (cs_data cs) - 1))%N.

(** group_forces_minimum_genus - large groups force genus strictly above g.
    Kind: helper.
    Why: contrapositive of Hurwitz: if |G| exceeds 84(g-1) then the covering
    genus must strictly exceed g.
    Used by: higher_genus_landscape and AlgebraicRigidity-based analogs.
*)
Lemma group_forces_minimum_genus (cs : CoveringScheme M) (g : nat) :
  (2 <= g)%N ->
  (84 * (g - 1) < #|G|)%N ->
  (2 <= cd_genus (cs_data cs))%N ->
  (g < cd_genus (cs_data cs))%N.
Proof.
move=> Hg2 Hlarge Hge2.
have Hhur := hurwitz_bound Hge2.
case: (ltnP g (cd_genus (cs_data cs))) => // Hle.
have Hle' : (84 * (cd_genus (cs_data cs) - 1) <= 84 * (g - 1))%N.
  by rewrite leq_mul2l /= leq_sub2r.
by move: (leq_ltn_trans (leq_trans Hhur Hle') Hlarge); rewrite ltnn.
Qed.

(** higher_genus_landscape - combined gap and Hurwitz bound for genus >= 2.
    Kind: main.
    Why: joint statement capturing the simultaneous bound on protocol gap and
    group size in the high-genus regime of the landscape.
*)
Theorem higher_genus_landscape (cs : CoveringScheme M) :
  (2 <= cd_genus (cs_data cs))%N ->
  (ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <=
   2 * cd_genus (cs_data cs))%N /\
  (#|G| <= 84 * (cd_genus (cs_data cs) - 1))%N.
Proof.
move=> Hge2; split.
- exact: gap_bound.
- exact: hurwitz_bound Hge2.
Qed.

End hurwitz.

(******************************************************************************)
(*     Section 5: Protocol Correctness (Standalone)                          *)
(******************************************************************************)

Section protocol_correctness.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(** protocol_correct_unbundled - standalone protocol correctness statement.
    Kind: helper.
    Why: spells out correctness of the PGG protocol without bundling the
    SecurityWitness, CoveringScheme and PGGInterface into a single record,
    so that instance authors can quote it without the full bundle machinery.
    Used by: instance-level correctness proofs that assemble the bundle lazily.
*)
Lemma protocol_correct_unbundled
    (sw : SecurityWitness R M)
    (cs : CoveringScheme M)
    (PI : PGGInterface M)
    (HT : ts_T' (cs_scheme cs) = pi_T' PI)
    (s : 'I_N) (P : pgg_gT M)
    (G_stable : forall g, g \in pgg_G M ->
       forall i : 'I_(ts_T' (cs_scheme cs)).+1,
         rp_content (cs_plug cs)
           (@pgg_rho M g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i)) =
         tnth [tuple rp_content (cs_plug cs)
                 (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
              | j < (ts_T' (cs_scheme cs)).+1] (rp_monodromy (cs_plug cs) g i)) :
  P \in pgg_G M ->
  ts_valid (cs_scheme cs) s
          [tuple rp_content (cs_plug cs)
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
          | j < (ts_T' (cs_scheme cs)).+1] ->
  pgg_recon_endpoints HT (rp_content (cs_plug cs)) P = s.
Proof.
move=> PG Hvalid.
apply: (pgg_recon_monodromy_correct (perm := rp_monodromy (cs_plug cs)));
  [exact: subxx | exact: G_stable | exact: PG | exact: Hvalid
  | exact: rp_recon_invariant].
Qed.

End protocol_correctness.

(******************************************************************************)
(*     Section 6: Landscape from AlgebraicRigidity                           *)
(*                                                                            *)
(*   ar_security_per_position == epsilon bound for each sheet                    *)
(*   ar_genus0_exact       == genus 0 -> exact threshold (T <= k)            *)
(*   ar_genus1_gap2        == genus 1 -> gap <= 2 (T <= k + 2)              *)
(*   ar_hurwitz            == genus >= 2 -> gap <= 2g AND |G| <= 84(g-1)    *)
(******************************************************************************)

Section landscape_from_rigidity.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Variable ar : AlgebraicRigidity R M.

Let G := pgg_G M.
Let N := (pgg_N' M).+1.
Let cs := tw_covering (ar_threshold ar).

(** ar_security_per_position - per-sheet variational-distance epsilon bound.
    Kind: example.
    Why: entry in the landscape tabulation showing that AlgebraicRigidity
    implies the per-position security bound sw_bound.
*)
Lemma ar_security_per_position (s : 'I_N) :
  (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s)
                      (sw_rho_dist (ar_security ar)))
            (fdist_uniform (card_ord N))
   <= sw_bound_eps (ar_security ar))%O.
Proof. exact: sw_bound. Qed.

(** ar_genus0_exact - genus-0 exactness specialised to AlgebraicRigidity.
    Kind: example.
    Why: landscape-tabulation entry T <= k under genus 0, for AlgebraicRigidity.
*)
Lemma ar_genus0_exact :
  cd_genus (cs_data cs) = 0 ->
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N.
Proof. exact: genus0_exact. Qed.

(** ar_genus1_gap2 - genus-1 gap-2 bound specialised to AlgebraicRigidity.
    Kind: example.
    Why: landscape-tabulation entry T <= k + 2 under genus 1, for
    AlgebraicRigidity.
*)
Lemma ar_genus1_gap2 :
  cd_genus (cs_data cs) = 1 ->
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2)%N.
Proof.
move=> Hg1; have := cs_gap cs.
by rewrite Hg1 muln1.
Qed.

(** ar_hurwitz - Hurwitz-regime landscape entry for AlgebraicRigidity.
    Kind: example.
    Why: landscape-tabulation entry gap <= 2g combined with |G| <= 84(g-1)
    under genus >= 2, specialised to AlgebraicRigidity.
*)
Lemma ar_hurwitz :
  (2 <= cd_genus (cs_data cs))%N ->
  (ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <=
   2 * cd_genus (cs_data cs))%N /\
  (#|G| <= 84 * (cd_genus (cs_data cs) - 1))%N.
Proof. exact: higher_genus_landscape. Qed.

(** ar_large_group_forces_genus - large-group implication for AlgebraicRigidity.
    Kind: example.
    Why: landscape-tabulation entry recording that |G| > klein_genus0_bound forces
    strictly positive genus, specialised to AlgebraicRigidity.
    Naming: `large_group_forces_genus` is the canonical PGG-landscape slogan;
    the five-component name preserves the `ar_` namespace discriminator that
    separates this entry from the non-AR analogue.
*)
Lemma ar_large_group_forces_genus :
  (klein_genus0_bound M < #|G|)%N ->
  (0 < cd_genus (cs_data cs))%N.
Proof. exact: ar_large_group_forces_gap ar. Qed.

End landscape_from_rigidity.

(******************************************************************************)
(*     Section 7: Discovery Phase — Schreier Convergence Tools               *)
(*                                                                            *)
(* Documents the Schreier discovery pipeline (Phase 1).                       *)
(* Given a SchreierCertificate, the convergence rate determines L':           *)
(*   eps(L) = sqrt(N) * (1-lambda)^L                                         *)
(* Monotone decreasing — find first L where eps < target.                     *)
(* Already proved in pgg_schreier.v:                                         *)
(*   - schreier_epsilon_decreasing : eps monotone in L                        *)
(*   - security_monotone : var_dist at L2 bounded by eps(L1) when L1 <= L2  *)
(*   - security_witness_schreier : SecurityWitness from certificate at L     *)
(******************************************************************************)

Section discovery_phase.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.

(* The Schreier envelope: eps(L) = sqrt(N) * (1-lambda)^L.
   Monotone decreasing in L, so find the first L where eps < target.
   Two discovery methods:
   1. Analytic: solve sqrt(N) * r^L < target for L
      (e.g., Monster: sqrt(N) ~ 10^10, r ~ 0.9, target ~ 10^-6 → L' ~ 67)
   2. vm_compute: scan achievable(L) for increasing L
      (e.g., OC: scan L=1,2,... until fiber count shows acceptable eps)

   Method 1 uses SchreierCertificate (this section).
   Method 2 uses pgg_security_solver.v + pgg_security_demo.v. *)

(* Discovery is already complete — the tools are in pgg_schreier.v:
   - SchreierCertificate packages the spectral gap
   - schreier_epsilon computes the envelope at each L
   - schreier_epsilon_decreasing proves monotonicity
   - security_witness_schreier converts to SecurityWitness at chosen L'

   This section serves as documentation of the Phase 1 → Phase 2 interface:
   once L' is found, construct SecurityWitness and proceed to
   AlgebraicRigidity (Section 6) and certification (Section 8). *)

(* Envelope monotonicity — re-exported for landscape visibility *)
Lemma discovery_eps_monotone (sc : SchreierCertificate R m n' sigmas)
    (L1 L2 : nat) :
  (L1 <= L2)%N ->
  schreier_epsilon sc L2 <= schreier_epsilon sc L1.
Proof. exact: schreier_epsilon_decreasing. Qed.

(* SecurityWitness construction from discovery — re-exported *)
Lemma discovery_to_certification (sc : SchreierCertificate R m n' sigmas)
    (L : nat) (Hinj : @weval_inj (Gen_PGGTypes sigmas) L) :
  SecurityWitness R (Gen_PGGTypes sigmas).
Proof. exact: (security_witness_schreier sc Hinj). Defined.

End discovery_phase.

(******************************************************************************)
(*     Section 8: Certification Phase — Entropy View from AlgebraicRigidity  *)
(*                                                                            *)
(* The SecurityWitness inside ar carries sw_rho_dist — the endpoint          *)
(* distribution. Its Shannon entropy gives an information-theoretic view     *)
(* of the same security guarantee:                                           *)
(*   - ar_entropy s = H(P_s): bits of uncertainty at sheet s                 *)
(*   - ar_entropy_gap s = D(P_s || U_N): leakage in bits                   *)
(*   - ar_var_dist_from_entropy: Pinsker bridge (entropy -> var_dist)       *)
(*                                                                            *)
(* These are Phase 2 (certification) tools — they interpret the security    *)
(* bound that was already proved at the chosen L'.                           *)
(******************************************************************************)

Section entropy_view.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Variable ar : AlgebraicRigidity R M.

Let sw := ar_security ar.
Let N := (pgg_N' M).+1.

(* Endpoint distribution at sheet s, extracted from ar *)
Let P_s (s : 'I_N) : R.-fdist 'I_N :=
  fdistmap (fun sigma : {perm 'I_N} => sigma s) (sw_rho_dist sw).

(* Entropy of the endpoint distribution at sheet s *)
Definition ar_entropy (s : 'I_N) : R := `H (P_s s).

(* Entropy is at most log N (maximum = uniform) *)
Lemma ar_entropy_le_logN (s : 'I_N) :
  ar_entropy s <= log N%:R.
Proof.
rewrite /ar_entropy.
have Hcard : #|'I_N| = N by rewrite card_ord.
have -> : log N%:R = log #|'I_N|%:R :> R by rewrite Hcard.
exact: entropy_max.
Qed.

(* The entropy deficit equals the KL divergence (leakage in bits).
   D(P_s || U_N) = log N - H(P_s). *)
Lemma ar_entropy_gap (s : 'I_N) :
  log N%:R - ar_entropy s =
  D(P_s s || fdist_uniform (card_ord N)).
Proof.
rewrite /ar_entropy /entropy /div opprK.
have -> : log N%:R = \sum_(a in 'I_N) P_s s a * log N%:R.
  by rewrite -mulr_suml FDist.f1 mul1r.
rewrite -big_split /=.
apply: eq_bigr => a _.
rewrite addrC -mulrDr fdist_uniformE card_ord.
have [->|Hpos] := eqVneq (P_s s a) 0.
  by rewrite mul0r mul0r.
congr (_ * _).
have Hgt : (0 < P_s s a) by rewrite lt0r Hpos FDist.ge0.
rewrite logDiv ?Hgt ?invr_gt0 ?ltr0n //.
rewrite logV ?ltr0n //.
by rewrite opprK.
Qed.

(* Pinsker bridge: var_dist bounded by entropy gap.
   var_dist(P_s, U_N) <= sqrt(2 * (log N - H(P_s))) *)
(** ar_var_dist_from_entropy - Pinsker bridge from entropy gap to variational distance.
    Kind: example.
    Why: landscape-tabulation entry showing the entropy view reproduces the
    var-dist bound via Pinsker's inequality.
    Naming: the five-component name reflects the cross-domain identity
    `var_dist <- entropy`; both halves name independent quantities.
*)
Lemma ar_var_dist_from_entropy (s : 'I_N) :
  var_dist (P_s s) (fdist_uniform (card_ord N)) <=
  Num.sqrt (2%:R * (log N%:R - ar_entropy s)).
Proof.
rewrite ar_entropy_gap.
exact: (Pinsker_inequality_weak (dom_by_uniform (P_s s) (card_ord N))).
Qed.

End entropy_view.

(******************************************************************************)
(*     Section 9: Covering Decomposition — Orthogonal Security + Threshold   *)
(*                                                                            *)
(* The covering choice determines two orthogonal guarantees:                  *)
(*   1. Security (sw_bound): var_dist(P_s, U_N) <= epsilon          *)
(*   2. Threshold (cs_gap): T - k <= 2*genus                                *)
(* These come from independent aspects of the algebraic choice:              *)
(*   - Security from monodromy mixing (word length L, generator count Tg)    *)
(*   - Threshold from covering geometry (genus of the covering curve)        *)
(*                                                                            *)
(* Galois-theoretic remark:                                                   *)
(*   The covering C→X is a function field extension K(C)/K(X). The          *)
(*   monodromy group G is the Galois group of the Galois closure.            *)
(*   Genus 0 (P^1→P^1) specializes to Shamir: the RS code evaluates        *)
(*   polynomials at fiber points (= roots), recovering Lagrange              *)
(*   interpolation. See cover_genus0.v for the formal genus-0 instance.     *)
(*                                                                            *)
(*   Source: Chen-Cramer, CRYPTO 2006 (AG secret sharing over small fields) *)
(******************************************************************************)

Section covering_decomposition.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Variable ar : AlgebraicRigidity R M.

Let N := (pgg_N' M).+1.
Let cs := tw_covering (ar_threshold ar).
Let sw := ar_security ar.

(* The covering decomposition: security and threshold from one algebraic
   choice. The SecurityWitness gives the endpoint bound (security side),
   and the CoveringScheme gives the gap bound (threshold side). *)
Lemma ar_covering_decomposition :
  (forall s : 'I_N,
    (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s) (sw_rho_dist sw))
              (fdist_uniform (card_ord N)) <= sw_bound_eps sw)%O) /\
  (ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <=
   2 * cd_genus (cs_data cs))%N.
Proof. split; [exact: sw_bound | exact: gap_bound]. Qed.

(* Genus-0 specialization: when the covering has genus 0, the threshold
   is exact (T <= k), recovering Shamir's (k,k)-threshold. *)
Lemma ar_genus0_shamir :
  cd_genus (cs_data cs) = 0 ->
  (forall s : 'I_N,
    (var_dist (fdistmap (fun sigma : {perm 'I_N} => sigma s) (sw_rho_dist sw))
              (fdist_uniform (card_ord N)) <= sw_bound_eps sw)%O) /\
  (ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))%N.
Proof.
move=> Hg0; split.
- exact: sw_bound.
- exact: genus0_exact Hg0.
Qed.

End covering_decomposition.
