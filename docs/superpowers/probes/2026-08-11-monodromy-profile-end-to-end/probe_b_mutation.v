(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Mutation of probe P-B: bridge 1 across two carriers                        *)
(*                                                                            *)
(* This file is DELIBERATELY RED and must not compile. It pairs the PGL(2,7)  *)
(* interface, which has eight seats, with the five-card scheme, which has     *)
(* five shares, and asks for bridge 1 between them. If erefl were accepted    *)
(* here, the bridge would be carrying no information and the casts of         *)
(* probe_b_count_bridge.v would be vacuous.                                   *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgl27_group pgl27_profile.
From pgg_smc Require Import five_card_scheme_I5.

(** bad_players_bridge — bridge 1 between the PGL(2,7) interface and the
    five-card scheme.
    @intent: pi_T' pgl27_PI = ts_T' fcI_scheme, an equation between 7 and 4. *)
Definition bad_players_bridge : pi_T' pgl27_PI = ts_T' fcI_scheme := erefl.
