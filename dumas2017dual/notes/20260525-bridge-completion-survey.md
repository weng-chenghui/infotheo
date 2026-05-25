# 2026-05-25 — Stage 0 survey: completing the SDistr→fdist bridge

Orchestrator run (`/rocq-orchestrator`) to complete the concrete application of
the bridge: feed the SSProve denotation of `game_enc_zero` through the joint
bridge and instantiate the abstract `fdist_game_enc_zero_joint`.

## Headline finding

The task is **not** a direct definitional identification. The bridge output and
the target Variable live in **different types**, and the instantiation site is
**outside** the main section. Verdict: requires a new modified-leak-code +
LosslessCode + joint-bridge composition (option (b), transport required).

## Type relationship (load-bearing)

```coq
(* line ~2352 *)
Definition alice_view : finType :=
  (Dk_a_carrier * plain AHE * plain AHE * plain AHE * plain AHE *
   plain AHE * plain AHE * plain AHE * plain AHE)%type.        (* 9-tuple *)

(* line ~2823 *)
Definition alice_view_joint : finType :=
  (alice_view * V_2_carrier * V_3_carrier)%type.               (* 11-tuple *)
```

- `bridge_enc_zero_to_fdist` (line ~2550) : `distr R alice_view → psum=1 →
  R.-fdist alice_view`.
- `bridge_alice_view_joint_to_fdist` (line ~3024) : `distr R alice_view_joint →
  psum=1 → R.-fdist alice_view_joint`.  **Already exists.**
- `Variable fdist_game_enc_zero_joint : R.-fdist alice_view_joint` (line ~3118).

So the joint-level bridge constructor is in place; the narrow-`alice_view` bridge
is the wrong target shape for the Variable.

## What is built vs missing

Built:
- `game_enc_zero_run_code : raw_code cipher_list` (line ~2680) = `resolve
  game_enc_zero (id_game_run, ...) tt`.
- `LosslessCode_game_enc_zero` (line ~2727): `psum (Pr_fst game_enc_zero_run_code)
  = 1`, proved via `Lossless_sample` / `LosslessOp_uniform` / `Lossless_put_ret`.
- `bridge_alice_view_joint_to_fdist` joint constructor.
- `bridge_psum_to_bigop`, `bridge_total_mass`, elementwise `…E` lemmas.

Missing:
- A **modified leak code** `raw_code alice_view_joint`: runs `game_enc_zero`'s
  body, samples / records V_2 and V_3, and returns the 11-tuple
  `(alice_view, v_2, v_3)` instead of the 4-tuple `cipher_list`.
- Its `LosslessCode` proof (should reuse the existing tactic pattern; same
  sampling structure plus the extra returns).
- The `Pr_fst (modified code)` → `bridge_alice_view_joint_to_fdist` application.
- The instantiation of `fdist_game_enc_zero_joint` from that — **at Task F,
  outside `Section dsdp_security_indcpa`** (the residual-joint section), because
  the Variable is used parametrically by 15 in-section declarations.

## Downstream dependents of the Variable (15)

Inside `Section dsdp_security_indcpa` (line 101 … End line 3540):
- 12 RV definitions `{RV fdist_game_enc_zero_joint -> _}`: `V_3, V_2, D_3, R_3,
  R_2, U_3, U_2, U_1, V_1, S, Dk_a, Z_rand` (lines ~3160–3360).
- `fdistmap V_2 / V_3 fdist_game_enc_zero_joint` (lines ~3397–3415).
- Hypotheses `V_2_uniform_hyp` (3434), `V_3_uniform_hyp` (3440); lemma
  `inde_V_2_V_3_Z_rand` (3516).

Converting `Variable → Definition` in place would force instantiating all 15 and
likely break section closure. The plan's design keeps the Variable abstract here
and instantiates downstream (Task F).

## `Pr_fst` / `LosslessCode` shapes

- `Pr_fst {T} (c : raw_code T) : distr R T` — needs resolved code, not a
  `package`. Use `game_enc_zero_run_code` (or its modified-return cousin).
- `LosslessCode c := psum (Pr_fst c) = 1` — exactly the `Hmass` the bridge wants.

## Design forks to settle in Brainstorm

1. **Leak-code shape.** How does the modified code obtain V_2, V_3 to return?
   `game_enc_zero` already samples `iV2`/`iV3` and stores V_2 in `V_2_cell`. The
   modified code must surface them in the return tuple. Faithfulness to the
   residual uniformity argument (`cPr_V2_V3_uniform_on_fiber_joint`) constrains
   the exact construction.
2. **Instantiation site.** New section `dsdp_security_indcpa_residual_joint`
   (Task F) vs extending an existing one. Where does the concrete
   `fdist_game_enc_zero_joint` definition live, and how do the in-section RV
   facts get transported to the concrete fdist.
3. **Reuse vs new.** Can the existing `LosslessCode_game_enc_zero` be reused, or
   does the return-shape change force a fresh lossless proof (extra
   `Lossless_sample` for the surfaced V_2/V_3)?

## Related

- `[[20260525-ssprove-infotheo-fdist-bridge]]` — the bridge explainer this run
  follows up on.
- `[[20260430-dsdp-unpredictability-entropy-audited-plan]]` — the Task 12/13/F
  split originates here.
