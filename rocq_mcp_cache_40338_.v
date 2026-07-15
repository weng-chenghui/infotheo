From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba.
Require Import homomorphic_encryption.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.
Import GRing.Theory.
Import Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Set Primitive Projections.
Record dsdp_alice_setup {R : realType} {T : finType} (P : R.-fdist T)
       (p_minus_2 q_minus_2 n_relay : nat) := MkDsdpAliceSetup {
  s_enc_msg          : finType;
  s_Dk_a             : {RV P -> 'Z_(p_minus_2.+2 * q_minus_2.+2)};
  s_VarRV            : {RV P -> {ffun 'I_n_relay.+1 -> 'Z_(p_minus_2.+2 * q_minus_2.+2)}};
  s_R_relay          : 'I_n_relay.+1 -> {RV P -> 'Z_(p_minus_2.+2 * q_minus_2.+2)};
  s_E_relay          : 'I_n_relay.+1 -> {RV P -> s_enc_msg};
  s_CondRV           : {RV P -> ('Z_(p_minus_2.+2 * q_minus_2.+2) * 'Z_(p_minus_2.+2 * q_minus_2.+2) * {ffun 'I_n_relay.+1 -> 'Z_(p_minus_2.+2 * q_minus_2.+2)} * 'Z_(p_minus_2.+2 * q_minus_2.+2))};
  s_centropy_n       : `H(s_VarRV | s_CondRV) = log (((p_minus_2.+2 * q_minus_2.+2) ^ n_relay)%:R : R);
  s_Dk_a_indep       : forall (B : finType) (Y : {RV P -> B}), P |= s_Dk_a _|_ Y;
  s_R_indep          : P |= (fun t => [ffun i => s_R_relay i t]) _|_ [% s_VarRV, s_CondRV];
  s_E_indep          : P |= (fun t => [ffun i => s_E_relay i t]) _|_ [% s_VarRV, [% s_Dk_a, (fun t => [ffun i => s_R_relay i t]), s_CondRV]];
}.
Unset Primitive Projections.
