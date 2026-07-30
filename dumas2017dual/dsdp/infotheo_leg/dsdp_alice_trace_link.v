(**md**************************************************************************)
(* # DSDP corrupted-Alice secrecy at the executed piSMC trace                 *)
(*                                                                            *)
(* Documentation table completed in the final task.                           *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption dsdp_interface dsdp_program dsdp_pismc.
Require Import dsdp_alice_infotheo_secrecy.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope proc_scope.
Local Open Scope sproc_scope.

Section dsdp_run_traces_of_ops.

Variables (gmsgT gcipherT grandT gprivT gpubT : Type).

Local Notation gdata := ((gmsgT + gcipherT + gprivT + gpubT)%type).

Variable genc : gpubT -> gmsgT -> grandT -> gcipherT.
Variable gemul : gcipherT -> gcipherT -> gcipherT.
Variable gepow : gcipherT -> gmsgT -> gcipherT.
Variable gadd gsub gmul : gmsgT -> gmsgT -> gmsgT.
Variable gdec : gprivT -> gcipherT -> option gmsgT.

Definition gdp (x : gmsgT) : gdata := inl (inl (inl x)).
Definition gde (x : gcipherT) : gdata := inl (inl (inr x)).
Definition gdk (x : gprivT) : gdata := inl (inr x).

Definition gget_cipher (x : gdata) : option gcipherT :=
  if x is inl (inl (inr v)) then Some v else None.

Definition gRecv_dec (frm : nat) (dk : gprivT) (f : gmsgT -> proc gdata)
    : proc gdata :=
  Recv_param gdata (obind (gdec dk) \o gget_cipher) frm f.

Definition gRecv_enc (frm : nat) (f : gcipherT -> proc gdata) : proc gdata :=
  Recv_param gdata gget_cipher frm f.

Definition DSDP_Interface_of_ops : DSDP_Interface := {|
  di_msgT := gmsgT ;
  di_cipherT := gcipherT ;
  di_randT := grandT ;
  di_priv_keyT := gprivT ;
  di_pub_keyT := gpubT ;
  di_data := gdata ;
  di_data_of_plain := gdp ;
  di_data_of_cipher := gde ;
  di_data_of_priv_key := gdk ;
  di_data_of_pub_key := fun x => inr x ;
  di_get_cipher := gget_cipher ;
  di_encrypt := genc ;
  di_emul := gemul ;
  di_epow := gepow ;
  di_add := gadd ;
  di_sub := gsub ;
  di_mul := gmul ;
  di_Recv_dec := gRecv_dec ;
  di_Recv_enc := gRecv_enc |}.

Variables (gdka gdkb gdkc : gprivT).
Variable gek : party_id -> gpubT.
Variables (gv1 gv2 gv3 gu1 gu2 gu3 gr2 gr3 : gmsgT).
Variables (grb1 grb2 grc1 grc2 gra1 gra2 : grandT).
Variables (gm1 gm2 gm3 : gmsgT).

(* The four ciphertexts the run puts on the wire after the two openings. *)
Local Notation gCb :=
  (gemul (gepow (genc (gek Bob) gv2 grb1) gu2) (genc (gek Bob) gr2 gra1)).
Local Notation gCc3 :=
  (gemul (gepow (genc (gek Charlie) gv3 grc1) gu3)
         (genc (gek Charlie) gr3 gra2)).
Local Notation gCc := (gemul gCc3 (genc (gek Charlie) gm2 grb2)).
Local Notation gCa := (genc (gek Alice) gm3 grc2).

Hypothesis Hgb : gdec gdkb gCb = Some gm2.
Hypothesis Hgc : gdec gdkc gCc = Some gm3.
Hypothesis Hga : gdec gdka gCa = Some gm1.

Let gpalice :=
  @palice DSDP_Interface_of_ops gdec gek gdka gv1 gu1 gu2 gu3 gr2 gr3
          gra1 gra2.
Let gpbob := @pbob DSDP_Interface_of_ops gdec gek gdkb gv2 grb1 grb2.
Let gpcharlie := @pcharlie DSDP_Interface_of_ops gdec gek gdkc gv3 grc1 grc2.

Let gsaprocs : seq (aproc dsdp_dtype (di_data DSDP_Interface_of_ops)) :=
  [aprocs gpalice ; gpbob ; gpcharlie].

Definition gprocs : seq (proc (di_data DSDP_Interface_of_ops)) :=
  erase_aprocs gsaprocs.

(* The raw traces of the fifteen-round run. *)
Lemma dsdp_run_traces_of_ops_ok :
  (run_interp 15 gprocs).2 =
  [:: [:: gdp (gadd (gsub (gsub gm1 gr2) gr3) (gmul gu1 gv1));
          gde gCa;
          gde (genc (gek Charlie) gv3 grc1);
          gde (genc (gek Bob) gv2 grb1);
          gdp gr3; gdp gr2; gdp gu3; gdp gu2; gdp gu1; gdp gv1; gdk gdka];
      [:: gde gCc3; gde gCb; gdp gv2; gdk gdkb];
      [:: gde gCc; gdp gv3; gdk gdkc]].
Proof.
rewrite /run_interp.
have -> : (15 = 10 + 5)%N by [].
rewrite interp_fuelD.
move Ht: (interp 10 gprocs (nseq (size gprocs) [::])) => S.
vm_compute in Ht.
rewrite Hgb in Ht.
have -> : (5 = 2 + 3)%N by [].
rewrite interp_fuelD.
move Ht2: (interp 2 S.1 S.2) => S2.
rewrite -Ht in Ht2.
vm_compute in Ht2.
rewrite Hgc in Ht2.
have -> : (3 = 1 + 2)%N by [].
rewrite interp_fuelD.
move Ht3: (interp 1 S2.1 S2.2) => S3.
rewrite -Ht2 in Ht3.
vm_compute in Ht3.
rewrite Hga in Ht3.
rewrite -Ht3.
by vm_compute.
Qed.

End dsdp_run_traces_of_ops.

(* Keep every parameter of the generic run explicit, so that instantiations
   are positional and independent of implicit-argument inference. *)
Arguments gprocs : clear implicits.

Section dsdp_alice_trace_link.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType)
          (chcipher_of_cipher : cipher AHE -> t_cipher)
          (cipher_of_chcipher : t_cipher -> cipher AHE).
Hypothesis chcipher_of_cipherK :
  cancel chcipher_of_cipher cipher_of_chcipher.
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* Every party's public key is the one associated with its private key, so
   [dec_correct] fires by conversion and no key hypothesis is needed. *)
Definition pkey_of_dk (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

Let DI := Standard_DSDP_Interface AHE.

(* The finite image of the interpreter's data carrier: plaintexts kept,
   ciphertexts marshalled, both key sorts erased to marks.  Summand order
   mirrors [std_data]'s msgT + encT + privT + pubT. *)
Definition dsdp_trace_dataT : finType :=
  ((plain AHE + t_cipher) + unit + unit)%type.

Definition trace_data_of_di_data (x : di_data DI) : dsdp_trace_dataT :=
  match x with
  | inl (inl (inl m)) => inl (inl (inl m))
  | inl (inl (inr c)) => inl (inl (inr (chcipher_of_cipher c)))
  | inl (inr _) => inl (inr tt)
  | inr _ => inr tt
  end.

(* The single qualified reference in this file: the piSMC programs, not the
   same-named ones of dsdp_program.v. *)
Let decode : di_priv_keyT DI -> di_cipherT DI -> option (di_msgT DI) :=
  @dec AHE.

Variables (v2 v3 r2 r3 : plain AHE) (rb1 rc1 ra1 ra2 : rand AHE).

Let d := di_data_of_plain DI.
Let e := di_data_of_cipher DI.
Let kd := di_data_of_priv_key DI.

Let palice_inst :=
  @palice DI decode pkey_of_dk dk_a w_v1 w_u1 w_u2 w_u3 r2 r3 ra1 ra2.
Let pbob_inst := @pbob DI decode pkey_of_dk dk_b v2 rb1 (rand_of_renc w_rb2).
Let pcharlie_inst :=
  @pcharlie DI decode pkey_of_dk dk_c v3 rc1 (rand_of_renc w_rc2).

Definition dsdp_procs_std : seq (proc (di_data DI)) :=
  erase_aprocs [aprocs palice_inst ; pbob_inst ; pcharlie_inst].

Let M2 : plain AHE := v2 * w_u2 + r2.
Let M3 : plain AHE := v3 * w_u3 + r3 + (v2 * w_u2 + r2).

(* Bob opens Alice's first combine. *)
Lemma dec_combine_bob :
  dec dk_b (Emul (Epow (enc (pkey_of_dk Bob) v2 rb1) w_u2)
                 (enc (pkey_of_dk Bob) r2 ra1)) = Some M2.
Proof. by rewrite Epow_encE Emul_encE dec_correct. Qed.

(* Charlie opens Bob's forward. *)
Lemma dec_forward_charlie :
  dec dk_c (Emul (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) w_u3)
                       (enc (pkey_of_dk Charlie) r3 ra2))
                 (enc (pkey_of_dk Charlie) M2 (rand_of_renc w_rb2)))
  = Some M3.
Proof. by rewrite Epow_encE !Emul_encE dec_correct. Qed.

(* Alice opens Charlie's re-encryption. *)
Lemma dec_recrypt_alice :
  dec dk_a (enc (pkey_of_dk Alice) M3 (rand_of_renc w_rc2)) = Some M3.
Proof. exact: dec_correct. Qed.

Let procs_of_ops :=
  gprocs (plain AHE) (cipher AHE) (rand AHE) (priv_key AHE) (pub_key AHE)
         (@enc AHE) (@Emul AHE) (@Epow AHE)
         +%R (fun a b : plain AHE => a - b) *%R (@dec AHE)
         dk_a dk_b dk_c pkey_of_dk
         w_v1 v2 v3 w_u1 w_u2 w_u3 r2 r3
         rb1 (rand_of_renc w_rb2) rc1 (rand_of_renc w_rc2) ra1 ra2.

(* The abstract instance at the standard interface IS the standard
   instance. *)
Lemma dsdp_procs_stdE : dsdp_procs_std = procs_of_ops.
Proof. by []. Qed.

Lemma dsdp_run_traces_ok :
  (run_interp 15 dsdp_procs_std).2 =
  [:: [:: d (v3 * w_u3 + r3 + (v2 * w_u2 + r2) - r2 - r3 + w_u1 * w_v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * w_u3 + r3 + (v2 * w_u2 + r2)) (rand_of_renc w_rc2));
          e (enc (pkey_of_dk Charlie) v3 rc1);
          e (enc (pkey_of_dk Bob) v2 rb1);
          d r3; d r2; d w_u3; d w_u2; d w_u1; d w_v1; kd dk_a];
      [:: e (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) w_u3)
                  (enc (pkey_of_dk Charlie) r3 ra2));
          e (Emul (Epow (enc (pkey_of_dk Bob) v2 rb1) w_u2)
                  (enc (pkey_of_dk Bob) r2 ra1));
          d v2; kd dk_b];
      [:: e (Emul (Emul (Epow (enc (pkey_of_dk Charlie) v3 rc1) w_u3)
                        (enc (pkey_of_dk Charlie) r3 ra2))
                  (enc (pkey_of_dk Charlie) (v2 * w_u2 + r2)
                       (rand_of_renc w_rb2)));
          d v3; kd dk_c]].
Proof.
rewrite dsdp_procs_stdE /procs_of_ops; apply: dsdp_run_traces_of_ops_ok.
- exact: dec_combine_bob.
- exact: dec_forward_charlie.
- exact: dec_recrypt_alice.
Qed.

(* The same traces with every ciphertext normalised to a single encryption:
   a combine's randomness is the homomorphic combination of the randomness of
   its arguments. *)
Lemma dsdp_run_traces_encE :
  (run_interp 15 dsdp_procs_std).2 =
  [:: [:: d (v3 * w_u3 + r3 + (v2 * w_u2 + r2) - r2 - r3 + w_u1 * w_v1);
          e (enc (pkey_of_dk Alice)
                 (v3 * w_u3 + r3 + (v2 * w_u2 + r2)) (rand_of_renc w_rc2));
          e (enc (pkey_of_dk Charlie) v3 rc1);
          e (enc (pkey_of_dk Bob) v2 rb1);
          d r3; d r2; d w_u3; d w_u2; d w_u1; d w_v1; kd dk_a];
      [:: e (enc (pkey_of_dk Charlie) (v3 * w_u3 + r3)
                 (rand_mul (rand_pow rc1 w_u3) ra2));
          e (enc (pkey_of_dk Bob) (v2 * w_u2 + r2)
                 (rand_mul (rand_pow rb1 w_u2) ra1));
          d v2; kd dk_b];
      [:: e (enc (pkey_of_dk Charlie) (v3 * w_u3 + r3 + (v2 * w_u2 + r2))
                 (rand_mul (rand_mul (rand_pow rc1 w_u3) ra2)
                           (rand_of_renc w_rb2)));
          d v3; kd dk_c]].
Proof. by rewrite dsdp_run_traces_ok !Epow_encE !Emul_encE. Qed.

End dsdp_alice_trace_link.

(* Keep every parameter of the standard proc list explicit, so that the
   per-sample instantiation is positional and independent of
   implicit-argument inference. *)
Arguments dsdp_procs_std : clear implicits.

Section dsdp_alice_trace_rv.
Context {R : realType}.
Variables (AHE : AHEncType) (Renc : finType) (index_renc : nat).
Hypothesis card_renc : #|Renc| = index_renc.+1.
Variable rand_of_renc : Renc -> rand AHE.
Variables (t_cipher : finType) (chcipher_of_cipher : cipher AHE -> t_cipher).
Variables (w_v1 w_u1 w_u2 w_u3 : plain AHE).
Hypothesis w_u3_inj : injective (fun v : plain AHE => w_u3 * v).
Variables (dk_a dk_b dk_c : priv_key AHE).
Variables (w_rb2 w_rc2 : Renc).

(* The declarations discharged by the preceding section and by the leg take
   these parameters explicitly; the abbreviations pin them once. *)
Local Notation DI := (Standard_DSDP_Interface AHE).
Local Notation pkey_of_dk := (pkey_of_dk dk_a dk_b dk_c).
Local Notation dsdp_trace_dataT := (dsdp_trace_dataT AHE t_cipher).
Local Notation V2 := (V2 (R:=R) (AHE:=AHE) card_renc).
Local Notation V3 := (V3 (R:=R) (AHE:=AHE) card_renc).
Local Notation R2 := (R2 (R:=R) (AHE:=AHE) card_renc).
Local Notation R3 := (R3 (R:=R) (AHE:=AHE) card_renc).
Local Notation Rho2 := (Rho2 (R:=R) (AHE:=AHE) card_renc).
Local Notation Rho3 := (Rho3 (R:=R) (AHE:=AHE) card_renc).
Local Notation RA1 := (RA1 (R:=R) (AHE:=AHE) card_renc).
Local Notation RA2 := (RA2 (R:=R) (AHE:=AHE) card_renc).
Local Notation Sout :=
  (Sout (R:=R) (AHE:=AHE) card_renc w_v1 w_u1 w_u2 w_u3).
Local Notation AliceView_zero_prefix i :=
  (AliceView_zero_prefix (R:=R) (AHE:=AHE) card_renc rand_of_renc
     chcipher_of_cipher pkey_of_dk w_v1 w_u1 w_u2 w_u3 i).
Local Notation AliceView := (AliceView_zero_prefix 0).
Local Notation indcpa_fdist_epsilon :=
  (indcpa_fdist_epsilon (R:=R) (AHE:=AHE) card_renc rand_of_renc
     chcipher_of_cipher).
Local Notation hop0_reduction :=
  (hop0_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     chcipher_of_cipher pkey_of_dk w_v1 w_u1 w_u2 w_u3).
Local Notation hop1_reduction :=
  (hop1_reduction (R:=R) (AHE:=AHE) card_renc rand_of_renc
     chcipher_of_cipher pkey_of_dk w_v1 w_u1 w_u2 w_u3).

(* Alice's executed trace read off a value of her reduced view: the leaked
   output, Charlie's re-encryption of it, the two received ciphertexts, the
   two masks, the four weights, and the erased key mark. *)
Definition dsdp_trace_of_view (v : dsdp_alice_viewT AHE Renc t_cipher) :
    15.-bseq dsdp_trace_dataT :=
  [bseq inl (inl (inl v.1.1.2));
        inl (inl (inr (chcipher_of_cipher
          (enc (pkey_of_dk Alice)
               (v.1.1.2 - w_u1 * w_v1 + v.1.1.1.1.1 + v.1.1.1.1.2)
               (rand_of_renc w_rc2)))));
        inl (inl (inr v.2));
        inl (inl (inr v.1.2));
        inl (inl (inl v.1.1.1.1.2));
        inl (inl (inl v.1.1.1.1.1));
        inl (inl (inl w_u3)); inl (inl (inl w_u2));
        inl (inl (inl w_u1)); inl (inl (inl w_v1));
        inl (inr tt)].

(* The three piSMC programs at the coordinates of one sample. *)
Definition dsdp_procs_of_sample (s : dsdp_alice_sampleT AHE Renc) :
    seq (proc (di_data DI)) :=
  dsdp_procs_std AHE Renc rand_of_renc w_v1 w_u1 w_u2 w_u3 dk_a dk_b dk_c
    w_rb2 w_rc2 (V2 s) (V3 s) (R2 s) (R3 s) (rand_of_renc (Rho2 s))
    (rand_of_renc (Rho3 s)) (rand_of_renc (RA1 s)) (rand_of_renc (RA2 s)).

(* Fuel bounds the encoded trace, since encoding preserves length. *)
Let size_alice_trace (s : dsdp_alice_sampleT AHE Renc) :
  (size (map (trace_data_of_di_data chcipher_of_cipher)
           (nth [::] (run_interp 15 (dsdp_procs_of_sample s)).2 0)) <= 15)%N.
Proof. by rewrite size_map; exact: size_traces_nth. Qed.

(* Alice's encoded executed trace as a random variable on the sample
   space. *)
Definition AliceTrace :
    {RV (alice_sample_fdist (R:=R) AHE card_renc) ->
     15.-bseq dsdp_trace_dataT} :=
  fun s => Bseq (size_alice_trace s).

(* The leaked output the run computes is Alice's view slot. *)
Let Sout_runE (s : dsdp_alice_sampleT AHE Renc) :
  V3 s * w_u3 + R3 s + (V2 s * w_u2 + R2 s) - R2 s - R3 s + w_u1 * w_v1
  = Sout s.
Proof. by rewrite /Sout /comp_RV /dsdp_output /=; ring. Qed.

(* The plaintext Charlie re-encrypts is the leaked output net of Alice's own
   term and masks. *)
Let recrypt_plainE (s : dsdp_alice_sampleT AHE Renc) :
  V3 s * w_u3 + R3 s + (V2 s * w_u2 + R2 s)
  = Sout s - w_u1 * w_v1 + R2 s + R3 s.
Proof. by rewrite -Sout_runE; ring. Qed.

(* The trace the interpreter produces for Alice is the deterministic image of
   her reduced view. *)
Lemma dsdp_trace_of_viewE :
  AliceTrace = dsdp_trace_of_view `o AliceView.
Proof.
apply: boolp.funext => s; apply/val_inj.
rewrite /AliceTrace; move: (size_alice_trace s).
rewrite /dsdp_procs_of_sample dsdp_run_traces_ok.
by move=> ?; rewrite /= Sout_runE recrypt_plainE.
Qed.

(* The trace ladder: the leg's view ladder read as a trace. *)
Definition AliceTrace_zero_prefix (i : nat) :
    {RV (alice_sample_fdist (R:=R) AHE card_renc) ->
     15.-bseq dsdp_trace_dataT} :=
  dsdp_trace_of_view \o AliceView_zero_prefix i.

Notation AliceTrace_all_zero := (AliceTrace_zero_prefix 2).

(* A trace-level distinguisher read as a view-level one. *)
Definition distinguisher_of_trace
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
    plain AHE * plain AHE * dsdp_alice_viewT AHE Renc t_cipher -> bool :=
  fun y => D (y.1.1, y.1.2, dsdp_trace_of_view y.2).

(* A trace-level distinguishing probability is the view-level distinguishing
   probability of the lifted distinguisher. *)
Lemma trace_joint_PrE (i : nat)
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  Pr (`p_ [% V2, V3, AliceTrace_zero_prefix i]) [set x | D x]
  = Pr (`p_ [% V2, V3, AliceView_zero_prefix i])
       [set y | distinguisher_of_trace D y].
Proof.
rewrite /dist_of_RV.
have -> : ([% V2, V3, AliceTrace_zero_prefix i]
             : {RV _ -> (plain AHE * plain AHE
                         * 15.-bseq dsdp_trace_dataT)%type})
        = (fun y : (plain AHE * plain AHE
                    * dsdp_alice_viewT AHE Renc t_cipher)%type =>
             (y.1.1, y.1.2, dsdp_trace_of_view y.2))
            \o [% V2, V3, AliceView_zero_prefix i] by [].
rewrite -fdistmap_comp Pr_fdistmap_pre.
by apply: eq_bigl => t; rewrite !inE.
Qed.

(* Zeroing the Bob-key entry of the trace moves the distinguishing
   probability by the advantage of one explicit reduction against Bob's
   key. *)
Lemma hop0_trace_advantageE
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 0]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 1]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_dk Bob)
      (hop0_reduction (distinguisher_of_trace D)).
Proof. by rewrite !trace_joint_PrE; exact: hop0_advantageE. Qed.

(* Zeroing the Charlie-key entry does the same against Charlie's key. *)
Lemma hop1_trace_advantageE
    (D : plain AHE * plain AHE * 15.-bseq dsdp_trace_dataT -> bool) :
  `| Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 1]) [set x | D x]
     - Pr (`p_ [% V2, V3, AliceTrace_zero_prefix 2]) [set x | D x] |
  = indcpa_fdist_epsilon (pkey_of_dk Charlie)
      (hop1_reduction (distinguisher_of_trace D)).
Proof. by rewrite !trace_joint_PrE; exact: hop1_advantageE. Qed.

(* A predictor reading the all-zero trace matches Bob's input with
   probability at most one over the plaintext-space cardinality. *)
Lemma guess_trace_all_zero_le_invm
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE) :
  Pr (alice_sample_fdist (R:=R) AHE card_renc)
     [set t | (g `o AliceTrace_all_zero) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1.
Proof.
rewrite /AliceTrace_zero_prefix.
exact: (guess_all_zero_le_invm card_renc rand_of_renc chcipher_of_cipher
          pkey_of_dk w_v1 w_u1 w_u2 w_u3_inj (g \o dsdp_trace_of_view)).
Qed.

(* Every predictor reading the trace the interpreter produces for Alice
   matches Bob's input with probability at most one over the plaintext-space
   cardinality plus the real-or-zero advantages of the two per-hop
   reductions. *)
Theorem dsdp_alice_guess_fdist_trace_V2_real_le
    (g : 15.-bseq dsdp_trace_dataT -> plain AHE) :
  Pr (alice_sample_fdist (R:=R) AHE card_renc)
     [set t | (g `o AliceTrace) t == V2 t]
    <= (#|plain AHE|%:R : R)^-1
       + indcpa_fdist_epsilon (pkey_of_dk Bob)
           (hop0_reduction
              (distinguisher_of_guess (g \o dsdp_trace_of_view)))
       + indcpa_fdist_epsilon (pkey_of_dk Charlie)
           (hop1_reduction
              (distinguisher_of_guess (g \o dsdp_trace_of_view))).
Proof.
rewrite dsdp_trace_of_viewE.
exact: (dsdp_alice_guess_fdist_V2_real_le card_renc rand_of_renc
          chcipher_of_cipher pkey_of_dk w_v1 w_u1 w_u2 w_u3_inj
          (g \o dsdp_trace_of_view)).
Qed.

End dsdp_alice_trace_rv.
