(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Security Solver: Computable Parameter Relationships                    *)
(*                                                                            *)
(* Given the endpoint-level security formula:                                 *)
(*   epsilon = 2 * (N - Tg^L) / N                                            *)
(*                                                                            *)
(* this file provides:                                                        *)
(*   - SecurityParams record: fully determined {Tg, N, L, epsilon} set        *)
(*   - epsilon_endpoint_rat: computable epsilon as rational (numerator/denom)  *)
(*   - Constraint/solve: given partial parameters, solve for the rest         *)
(*   - solve_L_aux: search for smallest L achieving target epsilon            *)
(*   - StarParams/star_solve: star-graph specific solver (m -> Tg=m+1, N=m+3)*)
(*   - SecurityProfile: wraps SecurityWitness with L* + nontriviality         *)
(*   - vm_compute demonstrations for all group families                       *)
(*                                                                            *)
(* Key design: two epsilon formulas:                                          *)
(*   - Injective groups: 2*(N-Tg^L)/N (direct endpoint bound)                *)
(*   - Non-injective groups: fiber-counted (per-group; see star/oc/s5_fiber)  *)
(* DPI-based formula 2*(N!-Tg^L)/N! has been REMOVED as too loose.           *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     SecurityParams: fully determined parameter set                         *)
(******************************************************************************)

Record SecurityParams := MkSP {
  sp_Tg : nat ;
  sp_N : nat ;
  sp_L : nat ;
  sp_eps : nat * nat   (* epsilon as numerator/denominator rational *)
}.

(* Consistency: the epsilon matches the endpoint formula 2*(N-Tg^L)/N *)
Definition sp_consistent (p : SecurityParams) : bool :=
  let (en, ed) := sp_eps p in
  (2 * (sp_N p - sp_Tg p ^ sp_L p) * ed == en * sp_N p)%N.

(******************************************************************************)
(*     Epsilon computation                                                    *)
(******************************************************************************)

(* Endpoint-level epsilon as rational: 2*(N - Tg^L) / N *)
Definition epsilon_endpoint_rat (Tg N L : nat) : nat * nat :=
  let tl := Tg ^ L in
  if (tl <= N)%N then (2 * (N - tl), N) else (0, 1).

(******************************************************************************)
(*     L* search: smallest L achieving target epsilon                         *)
(******************************************************************************)

(* Search for smallest L such that epsilon(L) <= eps_n/eps_d.
   i.e., 2*(N - Tg^L)/N <= eps_n/eps_d
   i.e., 2*(N - Tg^L) * eps_d <= eps_n * N *)
Fixpoint solve_L_aux (Tg N eps_n eps_d fuel L : nat) : option nat :=
  match fuel with
  | 0 => None
  | fuel'.+1 =>
    let er := epsilon_endpoint_rat Tg N L in
    if (er.1 * eps_d <= eps_n * er.2)%N then Some L
    else solve_L_aux Tg N eps_n eps_d fuel' L.+1
  end.

Definition solve_L (Tg N eps_n eps_d : nat) : option nat :=
  solve_L_aux Tg N eps_n eps_d 100 1.

(******************************************************************************)
(*     Constraint types and solver                                            *)
(******************************************************************************)

Inductive Constraint :=
| FixEps  (eps_n eps_d : nat) (Tg N : nat)  (* given epsilon, Tg, N -> solve L *)
| FixL    (L Tg N : nat)                     (* given L, Tg, N -> solve epsilon *)
| FixEpsTg (eps_n eps_d : nat) (Tg : nat)   (* given epsilon, Tg -> solve L, N *)
| FixEpsL  (eps_n eps_d : nat) (L N : nat)  (* given epsilon, L, N -> solve Tg *)
.

(* Single entry point *)
Definition solve (c : Constraint) : option SecurityParams :=
  match c with
  | FixL L Tg N =>
    let eps := epsilon_endpoint_rat Tg N L in
    Some (MkSP Tg N L eps)
  | FixEps eps_n eps_d Tg N =>
    match solve_L Tg N eps_n eps_d with
    | Some L => Some (MkSP Tg N L (epsilon_endpoint_rat Tg N L))
    | None => None
    end
  | _ => None  (* FixEpsTg, FixEpsL: under-determined without additional constraints *)
  end.

(******************************************************************************)
(*     Consistency proof                                                      *)
(******************************************************************************)

Lemma epsilon_endpoint_rat_consistent (Tg N L : nat) :
  let er := epsilon_endpoint_rat Tg N L in
  (Tg ^ L <= N)%N -> er = (2 * (N - Tg ^ L), N).
Proof. by rewrite /epsilon_endpoint_rat; move=> ->. Qed.

Lemma epsilon_endpoint_rat_sp_consistent Tg N L :
  let er := epsilon_endpoint_rat Tg N L in
  (2 * (N - Tg ^ L) * er.2 == er.1 * N)%N.
Proof.
rewrite /= /epsilon_endpoint_rat.
case: ifP => HtlN.
  by rewrite /= mulnC.
rewrite /=.
have /eqP -> : (N - Tg ^ L == 0)%N.
  by rewrite subn_eq0 ltnW // ltnNge HtlN.
by rewrite muln0 mul0n.
Qed.

Lemma sp_consistent_endpoint Tg N L :
  sp_consistent (MkSP Tg N L (epsilon_endpoint_rat Tg N L)).
Proof.
rewrite /sp_consistent /= /epsilon_endpoint_rat.
case: ifP => HtlN.
  by rewrite /= mulnC.
rewrite /=.
have /eqP -> : (N - Tg ^ L == 0)%N.
  by rewrite subn_eq0 ltnW // ltnNge HtlN.
by rewrite muln0 mul0n.
Qed.

Lemma solve_consistent c p : solve c = Some p -> sp_consistent p.
Proof.
case: c => [eps_n eps_d Tg N | L Tg N | eps_n eps_d Tg | eps_n eps_d L N] //=.
- (* FixEps *)
  case Heq : (solve_L Tg N eps_n eps_d) => [L|] //=.
  by case=> <-; exact: sp_consistent_endpoint.
- (* FixL *)
  by case=> <-; exact: sp_consistent_endpoint.
Qed.

(******************************************************************************)
(*     Star-graph specific solver                                             *)
(******************************************************************************)

(* Star-specific: m determines Tg = m+1, N = m+3 *)
Record StarParams := MkStarP {
  star_m : nat ;
  star_L : nat ;
  star_eps : nat * nat
}.

Definition star_to_generic (sp : StarParams) : SecurityParams :=
  MkSP (star_m sp + 1) (star_m sp + 3) (star_L sp) (star_eps sp).

Inductive StarConstraint :=
| Star_FixM  (m : nat)        (* given m -> default L=1, compute eps *)
| Star_FixML (m L : nat)      (* given m, L -> compute eps *)
.

Definition star_solve (c : StarConstraint) : option StarParams :=
  match c with
  | Star_FixML m L =>
    let eps := epsilon_endpoint_rat (m + 1) (m + 3) L in
    Some (MkStarP m L eps)
  | Star_FixM m =>
    let eps := epsilon_endpoint_rat (m + 1) (m + 3) 1 in
    Some (MkStarP m 1 eps)
  end.

(******************************************************************************)
(*     vm_compute demonstrations                                              *)
(******************************************************************************)

(* S5: L=1, Tg=4, N=5 -> eps = 2*(5-4)/5 = (2,5) *)
Eval vm_compute in solve (FixL 1 4 5).

(* Abelian: L=1, Tg=2, N=4 -> eps = 2*(4-2)/4 = (4,4) = 1 *)
Eval vm_compute in solve (FixL 1 2 4).

(* OC: L=2, Tg=2, N=4 -> eps = 2*(4-4)/4 = (0,4) = 0 *)
Eval vm_compute in solve (FixL 2 2 4).

(* Cyclic n=2: L=1, Tg=1, N=4 -> eps = 2*(4-1)/4 = (6,4) *)
Eval vm_compute in solve (FixL 1 1 4).

(* Cyclic n=3: L=1, Tg=1, N=5 -> eps = 2*(5-1)/5 = (8,5) *)
Eval vm_compute in solve (FixL 1 1 5).

(* S5: eps <= 1/2, Tg=4, N=5 -> L=? *)
Eval vm_compute in solve (FixEps 1 2 4 5).

(* Abelian: eps <= 1/2, Tg=2, N=4 -> L=? *)
Eval vm_compute in solve (FixEps 1 2 2 4).

(* Tg=1 degenerate: eps <= 1/2, Tg=1, N=4 -> None (1^L = 1 never helps) *)
Eval vm_compute in solve (FixEps 1 2 1 4).

(* Star-specific *)
Eval vm_compute in star_solve (Star_FixML 2 1).   (* m=2, L=1 -> eps *)
Eval vm_compute in star_solve (Star_FixML 2 2).   (* m=2, L=2 -> eps *)
Eval vm_compute in star_solve (Star_FixM 2).       (* m=2 default *)

(* Star m=10: Tg=11, N=13 *)
Eval vm_compute in star_solve (Star_FixML 10 1).

(******************************************************************************)
(*     Fiber-counted epsilon (TRUE endpoint epsilon for non-injective groups) *)
(******************************************************************************)

(* For groups where eval_s is NOT injective on achievable(L), the formula
   2*(N-Tg^L)/N is WRONG (underestimates). The true epsilon comes from
   the worst-case fiber distribution over all starting sheets. *)

(* Star(m) at L=1: true epsilon = 2(m+1)/(m+3) *)
Definition star_fiber_eps (m : nat) : nat * nat := (2 * (m + 1), m + 3).

(* OC at L=2: true epsilon = 1 (worst-case s=1; other sheets have 1/2) *)
Definition oc_fiber_eps : nat * nat := (1, 1).

(* S5 at L=1: true epsilon = 6/5 *)
Definition s5_fiber_eps : nat * nat := (6, 5).

(* Comparison: formula-based (wrong for non-injective) vs fiber-counted *)
Eval vm_compute in (epsilon_endpoint_rat 2 4 2, oc_fiber_eps).
(* = ((0,4), (1,1)) — formula says 0, fiber says 1. Formula is WRONG. *)

Eval vm_compute in (epsilon_endpoint_rat 4 5 1, s5_fiber_eps).
(* = ((2,5), (6,5)) — formula says 2/5, fiber says 6/5. Formula is WRONG. *)

Eval vm_compute in (epsilon_endpoint_rat 3 5 1, star_fiber_eps 2).
(* = ((4,5), (6,5)) — formula says 4/5, fiber says 6/5. Formula is WRONG. *)

Eval vm_compute in star_fiber_eps 5.   (* m=5: (12,8) = 3/2 *)
Eval vm_compute in star_fiber_eps 10.  (* m=10: (22,13) *)

(******************************************************************************)
(*     Epsilon comparison utilities                                           *)
(******************************************************************************)

(* Is epsilon < 2? (i.e., strictly better than trivial) *)
Definition eps_lt2 (er : nat * nat) : bool :=
  (er.1 < 2 * er.2)%N.

(* Is epsilon < 1? (i.e., d_TV < 1/2) *)
Definition eps_lt1 (er : nat * nat) : bool :=
  (er.1 < er.2)%N.

(* Is epsilon = 0? (perfect security) *)
Definition eps_eq0 (er : nat * nat) : bool :=
  (er.1 == 0)%N.

(* Demonstrations *)
Eval vm_compute in eps_lt2 (epsilon_endpoint_rat 4 5 1).   (* S5 L=1: true *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 4 5 1).   (* S5 L=1: true (2/5 < 1) *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 2 4 1).   (* Abelian L=1: false (4/4 = 1) *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 2 4 2).   (* OC L=2: true (0 < 1) *)
Eval vm_compute in eps_eq0 (epsilon_endpoint_rat 2 4 2).   (* OC L=2: true *)
Eval vm_compute in eps_lt2 (epsilon_endpoint_rat 1 4 1).   (* Cyclic N=4: true (6/4 < 2) *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 1 4 1).   (* Cyclic N=4: false *)

(******************************************************************************)
(*     SecurityProfile record                                                 *)
(*                                                                            *)
(*     Wraps a SecurityWitness with:                                          *)
(*       - L* (the specific length used)                                      *)
(*       - Nontriviality: epsilon < 2 (strictly better than trivial bound)    *)
(*                                                                            *)
(*     Note: epsilon < 2 means the security bound is nontrivial.              *)
(*     epsilon < 1 means d_TV < 1/2 (better than random guessing for the     *)
(*     adversary). Both are checkable via vm_compute on the rational form.    *)
(******************************************************************************)

(* SecurityProfile is parameterized; we define it in a Section.
   The actual record definition is in algebraic_rigidity.v alongside
   SecurityWitness, since it depends on realType and fdist. *)

(******************************************************************************)
(*     Nat-level word enumeration and fingerprinting                         *)
(*     (duplicated from pgg_weval_inj.v to keep solver dependency-free)      *)
(******************************************************************************)

Fixpoint enum_words (Tg L : nat) : seq (seq nat) :=
  match L with
  | 0 => [:: [::]]
  | L'.+1 =>
    flatten [seq map (cons i) (enum_words Tg L') | i <- iota 0 Tg]
  end.

Definition eval_word (gens : nat -> nat -> nat) (w : seq nat) (x : nat)
    : nat :=
  foldl (fun acc i => gens i acc) x w.

Definition word_fingerprint (N : nat) (gens : nat -> nat -> nat)
    (w : seq nat) : seq nat :=
  map (eval_word gens w) (iota 0 N).

Definition check_weval_inj (N Tg L : nat) (gens : nat -> nat -> nat)
    : bool :=
  uniq (map (word_fingerprint N gens) (enum_words Tg L)).

(******************************************************************************)
(*     GroupDesc: Nat-level description of a group by generators             *)
(*                                                                           *)
(*     Captures a group's generator structure at the nat level for           *)
(*     vm_compute.  Works for ANY group family (RAAG, cyclic, Monster, ...). *)
(*     The rd_comm field records commutativity relations between generators;  *)
(*     it is used only by RAAG-specific analyses (trace counting) and is     *)
(*     ignored by generic computations (achievable_fps, endpoint_count,      *)
(*     fiber_entropy_summary). Non-RAAG groups can set rd_comm to            *)
(*     fun _ _ => false (as cyclic_desc does).                               *)
(******************************************************************************)

Record GroupDesc := MkGroupDesc {
  gd_Tg   : nat ;                        (* number of generators *)
  gd_N    : nat ;                        (* number of sheets *)
  gd_comm : nat -> nat -> bool ;         (* commutativity relation *)
  gd_gens : nat -> nat -> nat ;          (* generator action: gens(i, x) *)
}.

Notation RAAGDesc := GroupDesc (only parsing).
Notation MkRAAGDesc := MkGroupDesc (only parsing).
Notation rd_Tg := gd_Tg (only parsing).
Notation rd_N := gd_N (only parsing).
Notation rd_comm := gd_comm (only parsing).
Notation rd_gens := gd_gens (only parsing).

(******************************************************************************)
(*     Known RAAG family descriptors                                         *)
(******************************************************************************)

(* Star(m): center (gen 0) + m leaves, Tg = m+1, N = m+3
   gen 0: swap(0, 1), gen i (i>0): swap(2, i+2) *)
Definition star_gens (i x : nat) : nat :=
  if i == 0 then
    if x == 0 then 1 else if x == 1 then 0 else x
  else
    if x == 2 then i + 2 else if x == i + 2 then 2 else x.

Definition star_comm' (m i j : nat) : bool :=
  ((i == 0) || (j == 0)) && (i != j).

Definition star_desc (m : nat) : GroupDesc :=
  MkGroupDesc m.+1 (m + 3) (star_comm' m) star_gens.

(* Path(n): adjacent transpositions, Tg = n+1, N = n+2
   gen i: swap(i, i+1) *)
Definition path_gens (i x : nat) : nat :=
  if x == i then i.+1 else if x == i.+1 then i else x.

Definition path_comm' (i j : nat) : bool :=
  (2 <= (maxn i j - minn i j)) && (i != j).

Definition path_desc (n : nat) : GroupDesc :=
  MkGroupDesc n.+1 (n + 2) path_comm' path_gens.

(* Disjoint(k): k disjoint transpositions, Tg = k, N = 2*k
   gen i: swap(2*i, 2*i+1), all generators commute *)
Definition disjoint_gens (i x : nat) : nat :=
  let a := 2 * i in
  if x == a then a.+1 else if x == a.+1 then a else x.

Definition disjoint_desc (k : nat) : GroupDesc :=
  MkGroupDesc k (2 * k) (fun i j : nat => i != j) disjoint_gens.

(* OC(k,p): k overlapping p-cycles, Tg = k, N = k + p - 1
   gen i: p-cycle on {i, ..., i+p-1} *)
Definition oc_gens (p i x : nat) : nat :=
  if (i <= x) && (x < i + p) then
    if x == i + p - 1 then i else x.+1
  else x.

Definition oc_comm' (p i j : nat) : bool :=
  (p <= maxn i j - minn i j) && (i != j).

Definition oc_desc (k p : nat) : GroupDesc :=
  MkGroupDesc k (k + p - 1) (oc_comm' p) (oc_gens p).

(* Cyclic(n): single n-cycle generator, Tg = 1, N = n
   gen 0: x -> (x+1) mod n *)
Definition cyclic_gens (n i x : nat) : nat :=
  if (i == 0) && (x < n) then
    if x.+1 < n then x.+1 else 0
  else x.

Definition cyclic_desc (n : nat) : GroupDesc :=
  MkGroupDesc 1 n (fun _ _ => false) (cyclic_gens n).

(******************************************************************************)
(*     Fiber-counted epsilon computation (fiber_eps_nat)                *)
(*                                                                           *)
(*     Computes worst-case var_dist(endpoint distribution, uniform)          *)
(*     over all starting sheets, using achievable set fingerprints.          *)
(*     var_dist convention: sum |P(x) - Q(x)| (range 0..2, no 1/2 factor). *)
(*                                                                           *)
(*     This single function replaces per-instance epsilon formulas           *)
(*     (star_fiber_eps, s5_fiber_eps, oc_fiber_eps) with a generic           *)
(*     computation applicable to any GroupDesc.                              *)
(******************************************************************************)

(* Achievable fingerprints: distinct word evaluations *)
Definition achievable_fps (desc : GroupDesc) (L : nat) : seq (seq nat) :=
  undup (map (word_fingerprint (rd_N desc) (rd_gens desc))
             (enum_words (rd_Tg desc) L)).

(* Count how many achievable elements map sheet s to endpoint x *)
Definition endpoint_count (fps : seq (seq nat)) (s x : nat) : nat :=
  count (fun fp => nth 0 fp s == x) fps.

(* Var_dist numerator for sheet s:
   sum_{x=0}^{N-1} |N * count(x) - total|
   where |a - b| = (a - b) + (b - a) in nat arithmetic *)
Definition vardist_num (fps : seq (seq nat)) (N s : nat) : nat :=
  let total := size fps in
  sumn [seq let c := endpoint_count fps s x in
            (N * c - total) + (total - N * c)
       | x <- iota 0 N].

(* Worst-case vardist numerator over all sheets *)
Definition worst_vardist (fps : seq (seq nat)) (N : nat) : nat :=
  foldr maxn 0 [seq vardist_num fps N s | s <- iota 0 N].

(* Reduce a fraction by GCD *)
Definition reduce_frac (n d : nat) : nat * nat :=
  match gcdn n d with
  | 0 => (0, 1)
  | g => (n %/ g, d %/ g)
  end.

(* fiber_eps_nat: worst-case endpoint var_dist as (numerator, denominator)
   Input: GroupDesc + L -> Output: worst-case (eps_num, eps_den) *)
Definition fiber_eps_nat (desc : GroupDesc) (L : nat) : nat * nat :=
  let fps := achievable_fps desc L in
  let N := rd_N desc in
  let total := size fps in
  if total == 0 then (0, 1)
  else reduce_frac (worst_vardist fps N) (N * total).

Notation raag_fiber_eps_nat := fiber_eps_nat (only parsing).

(******************************************************************************)
(*     SecuritySpec and GroupTemplate                                         *)
(*                                                                           *)
(*     SecuritySpec: dealer's partial specification (target epsilon, fix L).  *)
(*     GroupTemplate: a group family's solver (parameterized by desc).        *)
(*     group_template: generic template — star, path, disjoint, oc, cyclic   *)
(*       are all just different GroupDescs fed to the same solver logic.     *)
(******************************************************************************)

Record SecuritySpec := MkSecuritySpec {
  ss_target_eps : option (nat * nat) ;  (* upper bound on epsilon *)
  ss_L          : option nat ;          (* fix word length *)
}.

Record GroupTemplate := MkGroupTemplate {
  gt_Tg : nat ;
  gt_N  : nat ;
  gt_solve : SecuritySpec -> option SecurityParams ;
}.

Definition group_template (desc : GroupDesc) (default_L : nat)
    : GroupTemplate :=
  MkGroupTemplate (rd_Tg desc) (rd_N desc)
    (fun spec =>
      let L := match ss_L spec with
               | Some l => l
               | None => default_L
               end in
      if check_weval_inj (rd_N desc) (rd_Tg desc) L (rd_gens desc) then
        let eps := fiber_eps_nat desc L in
        match ss_target_eps spec with
        | Some target =>
            if (eps.1 * target.2 <= target.1 * eps.2)%N then
              Some (MkSP (rd_Tg desc) (rd_N desc) L eps)
            else None
        | None => Some (MkSP (rd_Tg desc) (rd_N desc) L eps)
        end
      else None).

Notation raag_template := group_template (only parsing).

(******************************************************************************)
(*     Named templates for known families                                    *)
(******************************************************************************)

Definition star_template (m : nat) := group_template (star_desc m) 1.
Definition path_template (n : nat) := group_template (path_desc n) 1.
Definition disjoint_template (k : nat) := group_template (disjoint_desc k) 1.
Definition oc_template (k p : nat) := group_template (oc_desc k p) (p - 1).
Definition cyclic_template (n : nat) := group_template (cyclic_desc n) 1.

(* Top-level dealer entry point *)
Definition dealer_solve (spec : SecuritySpec) (tmpl : GroupTemplate)
    : option SecurityParams := gt_solve tmpl spec.

(******************************************************************************)
(*     vm_compute demonstrations: dealer_solve                               *)
(******************************************************************************)

(* Star m=2: Tg=3, N=5, L=1, eps=6/5 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (star_template 2).

(* Path n=3 (= S5): Tg=4, N=5, L=1, eps=6/5 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (path_template 3).

(* Disjoint k=2 (= Abelian): Tg=2, N=4, L=1, eps=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (disjoint_template 2).

(* OC(2,3): Tg=2, N=4, L=2, eps=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (oc_template 2 3).

(* Cyclic n=4: Tg=1, N=4, L=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (cyclic_template 4).

(* Cyclic n=5: Tg=1, N=5, L=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (cyclic_template 5).

(* Star m=5: Tg=6, N=8 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (star_template 5).

(* With target epsilon: Star m=2 with target eps <= 6/5 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec (Some (6, 5)) None) (star_template 2).

(* With target epsilon: Star m=2 with target eps <= 1/2 -> None *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec (Some (1, 2)) None) (star_template 2).

(* Cyclic n=2 with target eps <= 0.01 -> None *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec (Some (1, 100)) None) (cyclic_template 2).

(******************************************************************************)
(*     vm_compute demonstrations: raw fiber epsilon                          *)
(******************************************************************************)

Eval vm_compute in fiber_eps_nat (star_desc 2) 1.   (* = (6, 5) *)
Eval vm_compute in fiber_eps_nat (path_desc 3) 1.   (* = (6, 5) *)
Eval vm_compute in fiber_eps_nat (oc_desc 2 3) 2.   (* = (1, 1) *)
Eval vm_compute in fiber_eps_nat (disjoint_desc 2) 1. (* = (1, 1) *)
Eval vm_compute in fiber_eps_nat (cyclic_desc 4) 1. (* = (3, 2) *)
Eval vm_compute in fiber_eps_nat (cyclic_desc 5) 1. (* = (8, 5) *)

(* Cross-check: star_fiber_eps matches fiber_eps_nat *)
Eval vm_compute in (star_fiber_eps 2, fiber_eps_nat (star_desc 2) 1).
Eval vm_compute in (s5_fiber_eps, fiber_eps_nat (path_desc 3) 1).

(* Larger examples *)
Eval vm_compute in fiber_eps_nat (star_desc 5) 1.   (* m=5: Tg=6, N=8 *)
Eval vm_compute in fiber_eps_nat (star_desc 10) 1.  (* m=10: Tg=11, N=13 *)

(******************************************************************************)
(*     Fiber entropy computation (nat-level approximation)                    *)
(*                                                                            *)
(*     Computes an integer proxy for entropy deficit:                         *)
(*       entropy_deficit_num = Σ_{c_x > 0} c_x * (c_x - 1)                  *)
(*     which is 0 iff all nonempty fibers have size 1 (= injective eval_s).  *)
(*     This is NOT the true entropy but a computable nat-level indicator of   *)
(*     fiber unevenness: 0 means all fibers are singletons (max entropy).    *)
(*                                                                            *)
(*     For true entropy, use the type-level fiber_entropy in                  *)
(*     pgg_entropy_security.v with real-valued log.                           *)
(******************************************************************************)

(* Fiber unevenness indicator for sheet s:
   Σ_{x} c_x * (c_x - 1) where c_x = endpoint_count fps s x.
   This is 0 iff all fibers are singletons (eval_s injective). *)
Definition fiber_unevenness (fps : seq (seq nat)) (N s : nat) : nat :=
  sumn [seq let c := endpoint_count fps s x in c * (c - 1)
       | x <- iota 0 N].

(* Worst-case fiber unevenness over all sheets *)
Definition worst_unevenness (fps : seq (seq nat)) (N : nat) : nat :=
  foldr maxn 0 [seq fiber_unevenness fps N s | s <- iota 0 N].

(* Is eval_s injective on achievable(L)? (all fibers are singletons) *)
Definition check_eval_s_inj (desc : GroupDesc) (L : nat) : bool :=
  let fps := achievable_fps desc L in
  worst_unevenness fps (rd_N desc) == 0.

(* Fiber entropy summary: (total, worst_unevenness, is_injective)
   - total = |achievable(L)| = Tg^L when weval_inj
   - worst_unevenness = 0 iff eval_s injective → H = log(total)
   - For exact H when unevenness > 0, use type-level fiber_entropy *)
Definition fiber_entropy_summary (desc : GroupDesc) (L : nat)
    : nat * nat * bool :=
  let fps := achievable_fps desc L in
  let total := size fps in
  let wu := worst_unevenness fps (rd_N desc) in
  (total, wu, wu == 0).

(******************************************************************************)
(*     vm_compute demonstrations: fiber entropy                              *)
(******************************************************************************)

(* Star m=2, L=1: unevenness > 0 (non-injective eval_s) *)
Eval vm_compute in fiber_entropy_summary (star_desc 2) 1.

(* Path n=3 (= S5), L=1: unevenness > 0 *)
Eval vm_compute in fiber_entropy_summary (path_desc 3) 1.

(* OC(2,3), L=2: unevenness > 0 *)
Eval vm_compute in fiber_entropy_summary (oc_desc 2 3) 2.

(* Disjoint k=2 (= Abelian), L=1: check if eval_s injective *)
Eval vm_compute in fiber_entropy_summary (disjoint_desc 2) 1.

(* Cyclic n=5, L=1: single generator *)
Eval vm_compute in fiber_entropy_summary (cyclic_desc 5) 1.

(* Cross-family comparison *)
Eval vm_compute in check_eval_s_inj (star_desc 2) 1.
Eval vm_compute in check_eval_s_inj (disjoint_desc 2) 1.
Eval vm_compute in check_eval_s_inj (cyclic_desc 5) 1.
