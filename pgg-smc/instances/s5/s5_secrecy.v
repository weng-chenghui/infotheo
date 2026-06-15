(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5 instance view-level secrecy. The S_5 scheme deals a secret position     *)
(* 'I_5 = 'Z_5 by a 5-of-5 additive sharing (N' = 3, so N = 5; T' = 4, so      *)
(* T = 5), the Additive mechanism. Any sub-threshold coalition view is         *)
(* independent of the secret. The concrete sampler and the executed-trace      *)
(* tie-in belong to the deferred operational layer.                            *)
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

Section s5_secrecy.
Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.

(** s5_view_secrecy — a sub-threshold coalition of the S_5 5-of-5 additive
    sharing learns nothing about the dealt position.
    @main security: zero mutual information and unchanged conditional entropy
    for any coalition below the threshold. *)
Lemma s5_view_secrecy (rs : RandomizedSharing P 3 4)
    (C : {set 'I_5}) (HC : (#|C| < 5)%N) :
  `I( lw_secret (mechanism_leakage (Additive rs HC)) ;
      lw_view  (mechanism_leakage (Additive rs HC)) ) = 0%R /\
  `H( lw_secret (mechanism_leakage (Additive rs HC)) |
      lw_view  (mechanism_leakage (Additive rs HC)) )
    = `H `p_ (lw_secret (mechanism_leakage (Additive rs HC))).
Proof. apply: leakage_of_view_indep; exact: lw_indep _. Qed.

(** s5_view_secrecy_concrete — the S_5 secrecy with the concrete uniform iid
    sampler, with no abstract sharing hypothesis.
    @main security: zero mutual information and unchanged conditional entropy for
    any sub-threshold coalition over the uniform iid 5-of-5 sharing. *)
Lemma s5_view_secrecy_concrete (C : {set 'I_5}) (HC : (#|C| < 5)%N) :
  `I( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) ;
      lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) ) = 0%R /\
  `H( lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) |
      lw_view  (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC)) )
    = `H `p_ (lw_secret (mechanism_leakage (Additive (@unif_randomized_sharing R 3 4) HC))).
Proof. apply: leakage_of_view_indep; exact: lw_indep _. Qed.

End s5_secrecy.
