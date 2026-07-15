# 2026-05-26 — Coding plan: trace-level connection between piSMC and SSProve

Proof-engineering memo (design only; NOT yet executed). Goal: connect the piSMC
interpreter and the SSProve game model **at the trace level** — show that both
produce the same trace (framing a), equivalently that the SSProve program uses the
trace the piSMC program yields after interpretation (framing b). This is the
tractable, Qed-able connection the thesis assumes is done when it writes the item-5
section. It is weaker than, and does NOT subsume, the distributional bridge
`game_real ≈₀ game_real_pismc` (see the caveat in §3).

Every code claim below is grounded in file:line.

## 0. Ground truth

**piSMC trace** (`smc/smc_interpreter.v`). `proc` is a 6-constructor inductive
(`Init|Send|Recv|Ret|Finish|Fail`, `:42-48`); `step` is deterministic given the
process list and party index (`:54-76`); `run_interp h procs := interp h procs
(nseq (size procs) [::])` (`:89`) and the trace type is `seq (seq data)` (one
`seq data` per party, head-first). Packaged form `interp_traces` with
`interp_traces_ok : map val (interp_traces h procs) = (run_interp h procs).2`
(`:514-528`). Pure Gallina, no probability — `du2002/spp_proof.v` proves its trace
facts by `reflexivity`/computation (`:106,:120`).

**du2002 proven precedent** (`du2002/spp_proof.v`). `scalar_product_uncurry`
(`:167-170`) is the deterministic trace map; `scalar_product_RV` (`:209-212`) is its
pushforward of the input RVs; `scalar_product_is_leakage_freeP` (`:458-466`, Qed)
levers `*_traces_ok` (computational trace equality) into the entropy proof. This is
"the trace gives the equation" already completed — on the **infotheo `fdist`** side.

**SSProve translator** (`smc/pismc_to_ssprove.v`). `code_of_proc : proc -> code …
(chList t_cipher)` (`:235-252`): `Send dst d k => code_of_send dst (data_to_cipher
d) (code_of_proc k)`, where `code_of_send dst v k = {code rest <- k ;; ret (v ::
rest)}` (`:124-131`) — so the return value is the cons-list of sent ciphertexts,
head = first send. `Ret` is discarded (`:240-246`); `Recv` becomes an oracle call
(`:142-151`). `translate_correct_marginal*` are `by []` (`:305-345`);
`pbob_head_send_eq`/`pcharlie_head_send_eq` prove only the **head** send.

**DSDP game** (`dumas2017dual/dsdp/ref/dsdp_security_indcpa_pismc.v`).
`game_real_pismc` (`:378-427`) samples 10 RVs, `#put`s `c2_cell`/`c3_cell`
(`:408-409`), links `dsdp_palice_code` with `dsdp_recv_oracle` (`:410-414`), returns
`alice_sends ++ [c2;c3]`. The admitted `Hypothesis game_real_eq_pismc : game_real ≈₀
game_real_pismc` (`:472`) is transported by `Pr_eq_of_game_real_eq_pismc` (`:498`);
shelved at "step 11 of ~30".

**Decisive SSProve finding.** An operational deterministic interpreter EXISTS:
`Run_aux (c : raw_code A) (seed : nat) (st) : option A`, `Run sample c seed`
(`pkg_interpreter.v:119-139`; dup `examples/Executor.v:135-155`). `seed : nat` is a
concrete random tape (`sampler` advances it; `chFin (n.+1) -> seed %% n.+1`);
`opr -> None` so oracles must be `code_link`-ed in first. `interpretation_test1`
(`Executor.v:255-260`, by `done`) shows `Run` equalities are provable by pure
computation. **CRITICAL NEGATIVE: no `Lemma`/`Theorem` anywhere in SSProve relates
`Run` to `repr`/`Pr`/`theta`/`AdvantageE`** (grep-verified). `Run` is an unverified
executor; `Pr`/`≈₀` are denotational via `repr` (`pkg_semantics.v:42-60`,
`pkg_advantage.v:60-99`).

## 1. The SSProve trace object

The returned `chList t_cipher` of `code_of_proc`, made computable by `Run`:

```coq
Definition ssprove_trace (p : proc) (oracle : raw_package) (seed : nat)
  : option (chList t_cipher) :=
  Run sampler (code_link (code_of_proc … p).(prog) oracle) seed.
```

`option` because `Run` is partial. `run_interp`'s `seq (seq data)` projects to one
party row; comparison is per-party, list-to-list, through an extractor
`data -> t_cipher`. (Sampled-values and raw-tape candidates rejected: no
first-class object, nothing on the piSMC side to compare to.)

## 2. The trace-equivalence theorem (framing a)

Generic headline lemma (the SSProve analogue of `scalar_product_uncurry`):

```coq
Theorem code_of_proc_Run_eq (p : proc) (oracle : raw_package) (seed : nat)
    (resp : seq t_cipher)                 (* oracle answers, in call order *)
    (Hpure : p does no #put/#get and oracle answers match resp) :
  Run sampler (code_link (code_of_proc … p).(prog) oracle) seed
  = Some (translate_sends p resp).
```

where `translate_sends : proc -> seq t_cipher -> chList t_cipher` is the
deterministic Gallina shadow of `code_of_proc`+`Run` (`Send d k => data_to_cipher d
:: translate_sends k resp`; `Recv f => translate_sends (f (cipher_to_data (head
resp))) (behead resp)`; `Init _ k => translate_sends k resp`; rest `[::]`).
Specialized to Alice it equals `(run_interp …).2`'s Alice-Send row mapped through
`dsdp_data_to_cipher`. Framing (b) is the same theorem read right-to-left.

## 3. Does trace-equality imply `≈₀`? NO — and this must be honest in the thesis

`≈₀` unfolds to `AdvantageE = 0` over the `repr`/`Pr` denotation; the trace theorem
lives in the `Run` world, which has **zero proven connection** to `repr`. So a
`Run`-trace Qed does NOT discharge `game_real_eq_pismc`. Bridging would need an
SSProve **operational-adequacy** lemma (`Run` agrees with `repr` as the
tape-evaluation of the sampling measure) — it does not exist and would itself be a
research contribution.

Mapping to the 4 soundness conditions: the trace theorem rigorously discharges
*observable-expressible* and *extractor-round-trip* (`chcipher_of_cipherK`,
`chmsg_of_msgK`, pismc.v:`70-73`) and witnesses *randomness-captured*; *fseparate*
is orthogonal. It does NOT reach the denotational identification of the two `repr`s.

**Why it is still worth proving:** it is a machine-checked *operational
faithfulness* statement — "the SSProve code Alice runs emits exactly the ciphertexts
the piSMC interpreter says she sends, for every tape and every Recv response" — which
closes the precise doubt a reader has on seeing `code_of_proc` discard `Ret` and
collapse `Recv_dec`→`Recv_enc`. It is independent of the IND-CPA reduction.

## 4. Proof strategy

**Strategy A (the trace theorem — tractable, recommended):**
1. Define `translate_sends` + a `Run_aux_bind` helper.
2. Prove `code_of_proc_Run_eq` by induction on `p`, `seed`/`resp`/`st` generalized.
   `Send`: `code_of_send` -> `bind` -> `Run_aux_bind` + IH. `Recv`: `opr` becomes
   `bind (resolve oracle …)` after `code_link`; consume the response stream.
   `Init`/`Ret`/`Finish`/`Fail`: definitional.
3. Specialize for Alice (`oracle := pack dsdp_recv_oracle`, `resp := [chcipher c2;
   chcipher c3; …]`); this extends head-faithfulness to the WHOLE list (the gap
   `pbob_head_send_eq` left).
4. **Hardest step (A4): the oracle `get`/`#put`.** `Run` starts from the default
   heap, so `dsdp_recv_oracle`'s `get c2_cell` misses the game-body `#put`s and the
   `None` fallback fires. Fixes: (A4a) `Run` the whole game body so `#put`s precede
   the link — needs `nat_ch`/`ch_nat` round-trip on `option t_cipher`, which only
   covers concrete carriers (abstract `t_cipher` defeats it); or (A4b) prove against
   a pure-responder oracle and separately show `dsdp_recv_oracle` post-`#put` is
   `Run`-equivalent to it (isolates one `nat_ch` lemma).
5. OOM caveat: `eapply`, never `apply:`, on `raw_package`/`code_link` goals; step
   `Run_aux` by `cbn`/compute, not `simpl` on the whole package.

**Strategy B (actually discharge `game_real_eq_pismc` — the separate hard chain):**
the shelved denotational route via `eq_rel_perf_ind_eq` (`pkg_rhl.v:653`):
`r_bind`/`r_uniform_bij` on the 10 shared samples, `r_put_lhs`/`r_put_rhs` on the
cells, and `translate_correct_marginal*` + `code_link_bind` to expose the same
Send-list as `game_real`'s inlined arithmetic. The `Run` trace theorem does NOT
shorten this (different semantic world).

## 5. Scope / risk

Strategy A: `translate_sends` + `Run_aux_bind` ~0.5d; the induction ~1–2d; A4 is the
swing factor (~1–2d if `t_cipher` concrete, possibly infeasible for abstract
`t_cipher` because `ch_nat`/`nat_ch` only cover concrete carriers). ~3–5 days total.
Hardest obstacle is A4 (a state-encoding problem, not a probability one). The trace
route is genuinely easier than the `≈₀` chain for *getting a rigorous model-connection
Qed*, but does NOT retire the Hypothesis (only Strategy B does, same difficulty).

## 6. Recommended concrete deliverable (fallback that dodges A4)

Instantiate the idealized AHE (`idealized_ahe`, imported `dsdp_pismc.v:8`) so
`t_cipher`/`t_msg` are concrete `choice_type`s `ch_nat` handles, then prove a
closed-form equality by `done`/`reflexivity` (à la `Executor.v:255-260` and
`spp_proof.v:106,120`):

```coq
Lemma alice_run_trace_concrete (seed : nat) (<concrete inputs>) :
  Run sampler (code_link (dsdp_palice_code <inputs>).(prog)
                         (pack (dsdp_recv_oracle_preloaded c2 c3))) seed
  = Some [:: chcipher_of_cipher (enc pk_b … ra1);
             chcipher_of_cipher (enc pk_c … ra2) ].
```

with `dsdp_recv_oracle_preloaded` having cells inhabited at definition time (default
heap suffices, dodging A4). Pair with the piSMC side
`sent_payloads (erase (palice …)) […] = [a1; a2]` (a `reflexivity` fact like
`smc_scalar_product_ok`). Together = framing (a) made concrete for DSDP-Alice, no
adequacy lemma, no abstract-carrier problem. This is the minimum rigorous bridge and
the recommended first deliverable.

## Related
- [[20260525-paper-adversary-model-view-as-input]] — the game model the bridge connects to.
- Coq: `smc/pismc_to_ssprove.v`, `smc/smc_interpreter.v`, `du2002/spp_proof.v`,
  `dumas2017dual/dsdp/ref/dsdp_security_indcpa_pismc.v`, SSProve `pkg_interpreter.v`.
- Thesis writing plan: `~/.claude/plans/transient-juggling-flurry.md` (rows 5-WRITE).
