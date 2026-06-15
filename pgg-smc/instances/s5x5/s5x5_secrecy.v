(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5x5 instance view-level secrecy. The S_5 x S_5 scheme is the product of   *)
(* two 5-of-5 additive sharings (each at N' = 3, T' = 4). A coalition below    *)
(* the product threshold min(k1, k2) is sub-threshold on each component, so    *)
(* each component view is independent of that component's secret.              *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset bigop ssralg ssrnum reals zmodp.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_sharing_mechanism pgg_canonical_sharing.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section s5x5_secrecy.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.

(** s5x5_view_secrecy — each 5-of-5 component of the product scheme keeps its
    own secret position hidden from any sub-threshold coalition on that
    component.
    @main security: zero mutual information and unchanged conditional entropy on
    both components of the product sharing. *)
Lemma s5x5_view_secrecy (rs1 rs2 : RandomizedSharing P 3 4)
    (C1 C2 : {set 'I_5}) (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N) :
  (`I( lw_secret (mechanism_leakage (Additive rs1 HC1)) ;
       lw_view  (mechanism_leakage (Additive rs1 HC1)) ) = 0%R /\
   `H( lw_secret (mechanism_leakage (Additive rs1 HC1)) |
       lw_view  (mechanism_leakage (Additive rs1 HC1)) )
     = `H `p_ (lw_secret (mechanism_leakage (Additive rs1 HC1)))) /\
  (`I( lw_secret (mechanism_leakage (Additive rs2 HC2)) ;
       lw_view  (mechanism_leakage (Additive rs2 HC2)) ) = 0%R /\
   `H( lw_secret (mechanism_leakage (Additive rs2 HC2)) |
       lw_view  (mechanism_leakage (Additive rs2 HC2)) )
     = `H `p_ (lw_secret (mechanism_leakage (Additive rs2 HC2)))).
Proof. split; apply: leakage_of_view_indep; exact: lw_indep _. Qed.

(** s5x5_view_secrecy_concrete — the per-component S_5 x S_5 secrecy with the
    concrete uniform iid sampler on each component, no abstract sharing hypothesis.
    @main security: zero mutual information and unchanged conditional entropy on
    both uniform iid components. *)
Lemma s5x5_view_secrecy_concrete (C1 C2 : {set 'I_5})
    (HC1 : (#|C1| < 5)%N) (HC2 : (#|C2| < 5)%N) :
  (`I( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) ;
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) ) = 0%R /\
   `H( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) |
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)) )
     = `H `p_ (lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC1)))) /\
  (`I( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) ;
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) ) = 0%R /\
   `H( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) |
       lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)) )
     = `H `p_ (lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC2)))).
Proof. split; apply: leakage_of_view_indep; exact: lw_indep _. Qed.

End s5x5_secrecy.
