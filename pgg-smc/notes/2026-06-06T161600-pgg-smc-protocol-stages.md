# piSMC Protocol Stages (pgg-smc)

Note date: 2026-06-06T161600
Revised: 2026-06-07 (as of commit `05c4b4f`) after the input-commitment
prologue (`dc8d251`) and the dealer-content layer (`7273373`) landed.

Traced from the session-typed program `protocol/card_exchange_pismc.v`, the
new prologue `protocol/pgg_input_commitment.v`, down through
`protocol/pgg_interface.v`, `protocol/pgg_program.v`, the threshold layer
`reconstruct/pgg_sharing_framework.v`, and the end-to-end dealer theorem
`reconstruct/pgg_dealer_bridge.v`.

The dealing protocol has **four** stages, not three. The named code phases
`split`/`compute`/`outcome` (`pgg_program.v:10-14`) cover stages 1 to 3;
stage 0 (dealer setup) is where the secret is actually split into shares and
the randomness is drawn. Since the `dc8d251` refactor there is also an
**optional** input-commitment prologue (Stage C) that prepends to the dealer
when input parties contribute committed card values; for the position-model
instances (no committed inputs) it degenerates definitionally to the plain
dealer and the wire is unchanged.

Pipeline: 0. Setup/Encode -> [C. Commit (optional)] -> 1. Split/Deal -> 2. Compute -> 3. Recover.

---

## Diagram (stages, actors, wire messages)

Process indices: dealer = 0, verifier = 1, player `i` = `i+2`; input parties
sit above the players (ids 4, 5, ... in the idealized M=2 demo). Wire payloads
are `DT_Hand` (a hand = seq of card positions), `DT_Idx` (a selection index),
and `DT_Sheet` (one card position, the `PGG_sheet` constructor).

```
 stage         input party        dealer (0)              player i (i+2)        verifier (1)
 ============================================================================================
 0 Setup            .         ts_encode s -> starts            .                    .          offline,
 (offline)          .         sample w : L.-tuple 'I_Tg        .                    .          no wire
                    .         word_eval w -> W = [:: g]        .                    .
 --------------------------------------------------------------------------------------------
 C Commit      pgg_commit v -- DT_Sheet --> prologue           .                    .          OPTIONAL;
 (optional,         .         recv one sheet per party,        .                    .          empty inputs
  online)           .         assemble committed -> W          .                    .          => no Stage C
 --------------------------------------------------------------------------------------------
 1 Deal             .         Deal<j> #hand_j -- DT_Hand --> recv my_hand           .
 (dealer)           .         hand_j = dealt_hand_content content W j
                    .         Announce<j> $P_idx -- DT_Idx --> recv shuffle_idx      .
 --------------------------------------------------------------------------------------------
 2 Compute          .                .            ep = nth my_hand shuffle_idx       .
 (each player)      .                .               (= compute P i)                 .
                    .                .            Reveal<verif> &ep -- DT_Sheet --> observe
 --------------------------------------------------------------------------------------------
 3 Recover          .                .                          .         Observe<j> &ep (x T) -> endpoints
 (verifier)         .                .                          .         ----- end of piSMC session -----
                    .                .                          .         ts_recon (cast endpoints) -> s
                    .                .                          .           (pure fn, OUTSIDE piSMC)
 ============================================================================================
```

The word table `W` is the single hand-off between setup and dealing. In the
plain protocol `W = [:: word_eval w]` is built offline in Stage 0; in the
committed protocol `W = assemble committed` is built online in Stage C from the
input parties' commits. Either way the dealer body of Stage 1 is identical,
and the player/verifier wire never sees the difference.

---

## 0. Setup (dealer, offline) -- the actual secret split + randomness

Header reference: `card_exchange_pismc.v:36-110` (esp. `:69` word-table
construction, `:268` "offline/setup phase").

1. Encode the secret into starting shares: `ts_encode s`
   (`pgg_sharing_framework.v:52`) turns secret `s` into the T-tuple of starting
   card positions `pi_starts` (`pgg_interface.v:381`). This is the genuine
   secret-into-shares split. `ts_encode_valid` (`pgg_sharing_framework.v:63`)
   guarantees a valid sharing.
2. Sample the shuffle: draw a word `w : L.-tuple 'I_Tg` uniformly from `Tg^L`.
3. Evaluate the word into one permutation: `word_eval w = \prod_i sigma_{w_i}`
   (`pgg_interface.v:163`). `exchange_dealer_from_words`
   (`card_exchange_pismc.v:285-287`) builds the lookup table `W = [:: word_eval w]`
   and feeds it to `exchange_dealer` with the identity content readout (`id`).
4. Correctness closed here: `dealer_encode_correct` (`pgg_dealer_bridge.v:90`)
   -- if starts come from `ts_encode s`, then reconstruction at the endpoints
   returns exactly `s`. The word-table variants are `dealer_words_correct`
   (`pgg_dealer_bridge.v:61`) and `dealer_words_epsilon_bound`
   (`pgg_dealer_bridge.v:79`).

## C. Commit (optional, online) -- input parties commit card values

File: `protocol/pgg_input_commitment.v`. A pre-dealing stage in which M input
parties each commit one card value (a position in `'I_N`) to the dealer; the
committed values are assembled into the dealer's word table `W` and the
unchanged `exchange_dealer` body then runs as in Stage 1.

1. Each input party sends its value: `pgg_commit i v`
   (`pgg_input_commitment.v:67`) is `SSend dealer_idx DT_Sheet (PGG_sheet v)`.
   The payload reuses `PGG_sheet`, so the commit rides the existing dealing
   alphabet (GATE 2: the den Boer `FCCommit` primitives over `fc_dtype` cannot
   be spliced into `pgg_dtype`; these wrappers are new over `pgg_dtype`).
2. The dealer collects them: `pgg_commit_prologue`
   (`pgg_input_commitment.v:97`) folds one `SRecv` over the input-party list,
   accumulating the committed values, then runs the continuation. The
   standalone receive is `pgg_recv_commit` (`pgg_input_commitment.v:79`).
3. Assemble and deal: `exchange_dealer_with_commit PI inputs assemble content
   players P_idx` (`pgg_input_commitment.v:126`) runs the prologue and then
   `exchange_dealer PI content players (assemble committed) P_idx`. The word
   table is `W = assemble committed`.
4. Degeneration: with no input parties the committed dealer is definitionally
   the plain dealer (`exchange_dealer_with_commit_nil`,
   `pgg_input_commitment.v:145`, proof `by []`). The position-model instances
   commit no inputs, so they keep the unchanged dealing program and every
   existing duality proof.
5. Duality discharged: `commit_recv_dual_2` (`:219`),
   `dealer_commit_input0_dual_2` (`:227`), `dealer_commit_input1_dual_2`
   (`:233`) certify by `native_compute` that the committed dealer is dual to
   each input party and that the dependent session environment threads
   correctly for a concrete two-input instance.

## 1. Split / Deal -- `exchange_dealer` (`card_exchange_pismc.v:221-233`)

Dealer role index = 0 (`dealer_idx`, line 133).

1. Build the permutation table: `perm_table W = [seq rho w | w <- W]`
   (`pgg_interface.v:446`).
2. Form each player's hand (column): `dealt_hand W i = [seq rho w (tnth starts i) | w <- W]`
   (`pgg_interface.v:454`).
3. Apply the content readout: the dealer now deals `dealt_hand_content content W j`
   (`card_exchange_pismc.v:200`, used at `:226`), where `content : 'I_N -> 'I_N`
   is applied to each card position. With `content = id` this is the plain
   `dealt_hand` (`dealt_hand_content_id`, `card_exchange_pismc.v:208`); the
   position-model instances and `exchange_dealer_from_words` all use `id`.
4. Deal the hands: ForList loop 1 (lines 225-227),
   `Deal<player_idx j> #(dealt_hand_content content W j)` sends each player its
   hand as a `DT_Hand` message.
5. Announce the selection: ForList loop 2 (lines 229-231),
   `Announce<player_idx j> $P_idx` tells each player which hand entry is live.
   Two loops keep the session type uniform (one data type per loop).

## 2. Compute -- `exchange_player` (`card_exchange_pismc.v:239-244`)

Player `i` sits at process index `i+2` (`player_idx`, line 139).

1. Receive inputs: `Receive<dealer_idx> #my_hand` then
   `Receive<dealer_idx> $shuffle_idx` (lines 241-242).
2. Look up the live endpoint: `nth ord0 my_hand shuffle_idx` (line 243), which
   equals `compute P i = rho P (tnth starts i)` (`pgg_interface.v:461`) by
   `compute_in_dealt_hand` (`pgg_interface.v:477`). Computation is just
   endpoint evaluation. (When `content <> id`, the looked-up value is the
   content readout of that endpoint.)
3. Reveal: `Reveal<verifier_idx> &(...)` (line 243) sends that single card
   position as a `DT_Sheet`. Players reveal only the selected endpoint, never
   the whole hand.

## 3. Recover -- `exchange_verifier` (`card_exchange_pismc.v:249-256`) + reconstruction

Verifier role index = 1 (`verifier_idx`, line 134).

1. Collect endpoints: ForList runs `Observe<player_idx j> &ep => Init (PGG_sheet ep)`
   for each player (lines 251-255), accumulating the T revealed positions, i.e.
   the `endpoints P` tuple (`pgg_interface.v:468`).
2. Reconstruct the secret: `ts_recon` on the T endpoints recovers `s`:
   `pgg_recon_endpoints P = ts_recon (cast endpoints)`
   (`pgg_sharing_framework.v:284`, via `pgg_recon` at `:280`).
   Meaning of recover depends on the scheme: polynomial interpolation (genus-0
   RS code), AG-code decoding (genus g), or sum-mod-N
   (`card_exchange_pismc.v:62-67`).
3. Why it works despite the shuffle: `ts_recon_perm_invariant`
   (`pgg_sharing_framework.v:125`) -- reconstruction is invariant under the
   coordinate permutation the shuffle induces. The shuffle decides which
   scrambling is applied, not the hidden value.
4. Caveat: this step is outside piSMC. The verifier's session program only
   collects the endpoints (line 253, `Init (PGG_sheet ep)`); `ts_recon` is a
   pure function applied afterward.

---

## Corrections to the three-stage impression

1. Add Stage 0 (Setup): the secret-into-shares split (`ts_encode`) and the
   random shuffle sampling (`word_eval`) both precede any messaging.
2. Add Stage C (Commit, optional): since `dc8d251` the dealer can be preceded
   by an input-commitment prologue; it degenerates away for instances with no
   committed inputs, so it does not change the four-stage spine.
3. "Split" is overloaded: the true secret-split is `ts_encode` in Stage 0; the
   code's `split` phase is the dealer dealing hands
   (`perm_table`/`dealt_hand`/`dealt_hand_content`) in Stage 1.
4. The dealer carries a content layer: `exchange_dealer` now takes
   `content : 'I_N -> 'I_N` and deals `dealt_hand_content content W j`; the
   plain protocol is the `content = id` special case.
5. "Computation" is exact: `compute = rho P (s_i)`, a per-player endpoint
   lookup.
6. "Recover" splits in two: the verifier's piSMC program only gathers the T
   endpoints; the `ts_recon` reconstruction runs outside the session program.

## Cross-cutting (not sequential stages)

- Session-type duality: every role pair checked dual by `native_compute`. The
  dealing phase is verified in `card_exchange_pismc.v` for the idealized 2-party
  instance (`pgg_idealized_duality`, `:297-436`) and the generic parameterized-N
  instance (`pgg_generated_duality`, `:442-517`). The commit prologue adds its
  own duality checks in `pgg_input_commitment.v:171-235`.
- Security analysis: collusion bound + Schreier spectral gap
  (`card_protocol.v:145-165`).
