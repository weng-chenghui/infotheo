# Where the leaked output S is consumed by the adversary (auto-derived game)

Date: 2026-06-15

Answers a peer question: in the auto-derived DSDP output-channel game, where and how
does the scalar-product output S get consumed by the adversary?

## Short answer

S is consumed by the adversary at exactly one point, and it is not inside the derived
game. The derived game only produces S and exposes it. The consumption happens one layer
up, in the guessing challenger (`dsdp_security_indcpa_fiber.v:90`):

```
guessing_challenger
  view  ← call_run tt          (* id_game_run  -> the cipher-list view *)
  s     ← call_s_get tt        (* id_s_get     -> reads S_output_cell  *)   <-- S read here
  guess ← call_pred (view, s)  (* id_guess     -> predictor / adversary *)  <-- S consumed here
  v2    ← call_v2 tt           (* id_v2_get    -> reads V_2_cell        *)
  ret (guess == v2)            (* wins iff adversary's guess hits V_2   *)
```

The adversary is the opaque `predictor_guesser`. It receives S as the second coordinate
of its single input pair `(view, s)` and returns a guess of the hidden challenge secret
V_2. That `call_pred (view, s)` is the only place S leaves the game and enters adversary
code. Inside the game S is write-only: the auto-derivation emits one `GC_put_output` that
does `#put S_output_cell := chmsg(S)`, and the `id_s_get` oracle (`denote_s_get_body`,
`dsdp_game_code.v:499`) does nothing but `get S_output_cell`.

If one searches for an algebraic site where S is combined or decrypted by the adversary,
there is none. S is handed to the predictor as an opaque input. The whole analytic payload
is the proof that even with S in hand the predictor gains at most 1/m.

## Where S is born (the auto-derivation)

In `dsdp_game_symbolic.v`, the symbolic walk of corrupted Alice (`walk_obs palice_sym`)
reaches Alice's final `Ret (SD_plain s)` and emits a single `AO_recv_output S`, where
`S = g - r2 - r3 + u1*v1 = u1*v1 + u2*v2 + u3*v3` (`obs_of_procs_dsdp_leak_S`, line 458).
This is the only injection of the scalar product into the trace. `lower_obs` turns
`AO_recv_output S` into `GC_put_output S`, and the `gc_eq` reflection
(`dsdp_security_indcpa_fiber.v:531`) confirms the lowered output term is exactly
`u1*v1 + u2*v2 + u3*v3` in de Bruijn form.

Heap cells: `V_2_cell` is Location 8, `S_output_cell` is Location 9
(`dsdp_game_code.v:230,236`), bundled as `protocol_state`.

## Flow diagram of the analysis

```
================================================================================
  AUTO-DERIVATION  (program  ->  symbolic trace  ->  game_code  ->  SSProve pkg)
================================================================================

  palice/pbob/pcharlie            walk_obs palice_sym (corrupted Alice)
  (dsdp_program.v)        ─────►   emits the observation trace
                                   obs_of_procs_dsdp_leak_S
                                        |
        6x AO_sample (v2,v3,r2,r3, 2 hop rand)
        AO_put 10                 -- challenge secret  V_2
        2x AO_recv_hop            -- c2, c3 received
        2x AO_combine             -- a2, a3 homomorphic assemblies
        AO_recv_output S          -- S = u1*v1+u2*v2+u3*v3   <<< S BORN HERE
        AO_leak [102;103;100;101] -- the leaked cipher VIEW
                                        |
                                        v  lower_obs / denote_game_leak_S
                       ┌─────────────────────────────────────────────┐
                       │   zero_game_leak_S  /  real_game_leak_S        │
                       │   (writes two heap cells, exports 3 oracles)   │
                       │                                                │
                       │   GC_put         -> V_2_cell  (Loc 8)          │
                       │   GC_put_output  -> S_output_cell (Loc 9)      │
                       │   GC_ret         -> cipher-list view           │
                       │                                                │
                       │   id_game_run : unit -> ciphers   (the view)   │
                       │   id_s_get    : unit -> msg        (reads S)   │
                       │   id_v2_get   : unit -> msg        (reads V_2) │
                       └─────────────────────────────────────────────┘
                              |              |               |
                          view│         S ───┘           V_2 │
================================================================================
  GUESSING LAYER  (guessing_challenger ∘ par predictor game)
================================================================================
                              |              |               |
                              v              v               |
                       ┌────────────────────────────┐        |
                       │     predictor / adversary    │       |
                       │   call_pred (view, S) -> guess│  <<< S CONSUMED HERE
                       └────────────────────────────┘        |
                                     |  guess                 |
                                     v                        v
                              ┌────────────────────────────────┐
                              │   ret (guess == V_2) : bool      │
                              │   success = Pr[ guess == V_2 ]   │
                              └────────────────────────────────┘
================================================================================
  WHY S LEAKS AT MOST 1/m  (the analytic content, fiber file)
================================================================================

  view_marginal_indep        the cipher VIEW is secret-independent
  (line 949)                  (zero game encrypts 0; secrets touch only the two
                              dropped heap cells)  =>  view tells nothing of V_2
                                        |
                                        v
  guess_inner_kernel_z        guess marginal  =  guess_kernel(S)
  (line 1774)                 the (v2,v3)-dependence funnels through the ONE
                              scalar S = dsdp_output, nothing else
                                        |
                                        v
  guess_cinde_V2              guess  _|_  V_2  |  Sout
  (line 1871)                 (guess is conditionally independent of the
                              challenge given the leaked output S)
                                        |
                                        v
  guess_V2_cond_le            Pr[ V_2 = a | Sout = s ]  =  1/#|plain| = 1/m
  (line 1726)                 conditioned on S, V_2 is uniform: the fiber
                              dsdp_fiber_ring has a unique solution per v3
                              (u3 injective)
                                        |
                                        v
  cinde_diagonal_bound        Pr[ guess == V_2 ]  <=  1/m       (zero game)
   -> guess_fdist_success_le  (line 1906)
   -> connector guess_success_sdistr_eq_fdist  (SSProve <-> Infotheo)
   -> guess_sdistr_success_le (line 1922)
                                        |
                                        v
  guess_advantage_eq + _le    zero game  ->  real game  costs  2 * epsilon_cpa
  (lines 2000, 2017)          (the views differ only by Enc(0) vs real ciphertexts;
                              IND-CPA reduction distinguisher)
                                        |
                                        v
  ============================================================
   dsdp_alice_secrecy_leak_S   (line 2043)
     guess_sdistr_success_real  <=  1/m  +  2 * epsilon_cpa
  ============================================================
```

## One-sentence framing

The derived game treats S as a write-only output cell that the `id_s_get` oracle reads
back, and the adversary consumes S only as the second half of the pair `(view, S)` handed
to the predictor in `guessing_challenger`. Because the view is secret-independent
(`view_marginal_indep`), S is the sole secret-bearing channel, and the analysis proves the
guess is conditionally independent of V_2 given S (`guess_cinde_V2`), so that channel is
worth at most 1/m of guessing advantage, plus 2 * epsilon_cpa to swap the all-zero game
for the real one.

## Source map

- `dsdp_program.v` — palice/pbob/pcharlie; Alice's return is S = dsdp_output
- `dsdp_game_symbolic.v:458` — `obs_of_procs_dsdp_leak_S`, the `AO_recv_output S` step
- `dsdp_game_code.v:230,236` — `V_2_cell` / `S_output_cell` locations
- `dsdp_game_code.v:499` — `denote_s_get_body` (the id_s_get oracle: get S_output_cell)
- `dsdp_indcpa_security.v:421,435` — `real_game_leak_S` / `zero_game_leak_S`
- `dsdp_security_indcpa_fiber.v:90` — `guessing_challenger` (S consumed at call_pred)
- `dsdp_security_indcpa_fiber.v:949,1774,1871,1726,1906,1922,2000,2017,2043` — analysis chain
