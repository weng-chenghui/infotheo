# Completing `obs_of_procs`: a one-record facade for the DSDP IND-CPA secrecy derivation

Date: 2026-06-08

Status: design approved in brainstorming; ready for an implementation plan. Supersedes
the Phase-2 `obs_of_procs` sketch in `~/.claude/plans/swirling-whistling-kahn.md` and
the architecture note `20260605-symbolic-to-game-architecture.md` for the front-end
observer. Computational (IND-CPA / SSProve) leg only; the information-theoretic entropy
leg is untouched and independent.

---

## 1. Goal

Today the corrupted-Alice observation trace `dsdp_alice_obs`
(`dumas2017dual/dsdp/dsdp_game_symbolic.v:225`) is a hand-written `seq alice_obs`
literal whose only derived part is the two `AO_combine` payloads (pulled from
`dsdp_observed_combines`). The sample prefix, the `AO_put`, the two `AO_recv_hop`, and
the `AO_leak` are all hand-typed.

This work replaces the hand-written scaffold with a derivation. A generic observer
`obs_of_procs` walks the corrupted party's symbolic program and emits the whole trace:
the samples, the hops, the combines, and the leak. Every parameter that drives the
derivation, from the symbolic trace to the advantage bound, is centralized in a single
record `dsdp_indcpa_secrecy_problem`. One value of that record determines the real game,
the zero game, and the hop count; a second record carries the universally quantified
adversary and its well-formedness.

## 2. Decisions taken in brainstorming

1. **Derive structurally, declare thinly.** `obs_of_procs` derives the hops (party and
   secret read off the senders' first sends), the combines (the corrupted party's sends),
   and the sample set and order (collected from the walk's free variables). The challenge
   secret, the leak order, and the cardinalities are declared.
2. **Keep exact faithfulness.** `game_of_trace (obs_of_procs P) = gc_dsdp` stays a
   by-computation equality. It is the transport bridge to the proven bound, a total
   regression oracle on the whole derivation, and the only check that pins the de Bruijn
   semantics (which secret each ciphertext operates on). Relaxing it to "well-formed +
   two hops" would discard the strongest evidence the derivation is correct.
3. **Structural sample order, with a minimal `gc_dsdp` rebuild.** The sample order is
   first-appearance during the walk (name-independent), not a sort by name (which would
   rest on a naming coincidence). `gc_dsdp` is rebuilt to that order. The rebuild is two
   de Bruijn indices (see Section 7); the exact check guards it.
4. **One control record.** All derivation parameters live in `dsdp_indcpa_secrecy_problem`.
   The adversary cannot be a field of that record (the theorem quantifies over all
   adversaries), so it gets its own record `dsdp_indcpa_adversary P`, over which the
   theorem quantifies. Every well-formedness hypothesis is a field of one of the two
   records.
5. **Names follow MathComp style** (audited): `X_of_Y` conversions, `K`-suffix cancel
   companions, `card_<thing>` order, record-tag prefixes `sp_` / `adv_`, and `choice_`
   (the spelled-out `ch` of `chmsg`/`chcipher`) for the SSProve `choice_type` encodings.

## 3. Architecture and data flow

```
pbob_sym, pcharlie_sym ── first_send ─► dsdp_received_hop_ciphertexts : seq symbolic_data
                                         [ Enc(Bob,v2,rb1) ; Enc(Charlie,v3,rc1) ]   (= [ c2 ; c3 ])
                                                     │  populates the record field
                                                     ▼
 ┌──────────  Control record  dsdp_problem : dsdp_indcpa_secrecy_problem  (the facade)  ──────────┐
 │  declared:  sp_corrupted_party_program = palice_sym                                            │
 │             sp_received_hop_ciphertexts = [ c2 ; c3 ]   ·   sp_challenge_secret = v2           │
 │             sp_leak_order = combines ++ recvs                                                  │
 │             sp_card_plaintext = c_m   ·   sp_card_randomness = c_r                             │
 │  carried :  sp_enc_scheme = E : AHEncType (supplied directly, NOT via Standard_DSDP_Interface) │
 │             +  marshalling into the game's choice types                                        │
 └────────────────────────────────────────┬───────────────────────────────────────────────────────┘
                                           │  corrupted_view P := obs_of_procs P   (a projection)
                                           ▼
                    walk_obs : dual-purpose drive of the corrupted proc palice_sym
                    ├ each reception: read (party, secret) from the structured
                    │   incoming send → AO_recv_hop; thread an opaque fresh
                    │   HE_var name into the continuation (so combines name it)
                    ├ each send: AO_combine (fresh name) (payload term)
                    └ halt on the first unanswered reception (the decrypt-receive)
                                                     ▼
                    walk output = [ hop c2 ; hop c3 ; combine a1 ; combine a2 ]   (a1, a2 DERIVED)
                                                     │
            collect_samples (first-appearance; split value-vars from rand-slots
                              by syntactic position; dedup; split by c_m / c_r)
                values [v2;v3;u2;r2;u3;r3]   randomness [ra1;ra2]
                                                     ▼
   corrupted_view P = samples ++ [AO_put challenge] ++ walk output ++ [AO_leak (view)]
   ( dsdp_alice_obs := corrupted_view (dsdp_problem …) )
                                                     │
                    game_of_trace  (REUSE, unchanged)  ─►  game_code
                                                     ▼
   dsdp_faithful : game_of_trace (corrupted_view (dsdp_problem …)) = gc_dsdp …   [by []]
                                                     │
        denote_game + advantage_le  (uses E)  (REUSE, unchanged)  ─►  SSProve package
                                                     ▼
   generic  dsdp_indcpa_secrecy : AdvantageE (real_game P) (zero_game P) (adv_package Adv)
                                     <= (count_obs_hops (corrupted_view P))%:R * epsilon_cpa
   DSDP     dsdp_problem_secure  : AdvantageE (real_game …) (zero_game …) … <= 2 * epsilon_cpa
```

The corrupted party's program, the two interface instances (`Standard_DSDP_Interface`,
`Symbolic_DSDP_Interface`), and the entire back end (`game_of_trace`, `denote_game`,
`advantage_le`) are reused with no change.

## 4. The control record (the facade)

```coq
(* dsdp_indcpa_secrecy_problem — every input that drives the DSDP corrupted-view
   IND-CPA secrecy derivation, from the symbolic trace to the advantage bound. One
   value determines the real game, the zero game, and the hop count. *)
Record dsdp_indcpa_secrecy_problem := {

  (* ---- sample-domain sizes (shared by the symbolic trace and the game) ---- *)
  sp_card_plaintext  : nat ;   (* size of the plaintext-scalar sample space *)
  sp_card_randomness : nat ;   (* size of the encryption-randomness sample space *)
  (* NB: card_plaintext != card_randomness is NOT a field. The advantage bound never
     consumes it (the back end has no such hypothesis), and requiring it would exclude
     schemes whose plaintext and randomness domains have equal size. The denotation's
     sample routing is a semantic-fidelity concern, not a precondition of the theorem. *)

  (* ---- the corrupted-view model (the security question) ---- *)
  sp_corrupted_party_program : proc symbolic_data ;
    (* the corrupted party's protocol program at the symbolic interface;
       obs_of_procs walks it to read off what the party samples, receives,
       assembles, and leaks *)
  sp_received_hop_ciphertexts : seq symbolic_data ;
    (* the ciphertexts the corrupted party receives that carry other parties'
       secret inputs, in reception order; each is a sender's first send and
       becomes one IND-CPA hop. Supplying exactly these also fixes where the walk
       stops: the party's later decrypt-receive gets no response *)
  sp_challenge_secret : nat ;
    (* the name of the secret the game challenges; written to the challenge cell *)
  sp_leak_order : seq nat -> seq nat -> seq nat ;
    (* given the names of the ciphertexts the corrupted party ASSEMBLED and the
       names of those it RECEIVED, returns the ordered name list the game leaks *)

  (* ---- the concrete scheme the abstract game is denoted into ---- *)
  sp_enc_scheme : AHEncType ;
  sp_rand_carrier : finType ;
  sp_rand_carrier_card : #|sp_rand_carrier| = sp_card_randomness ;
  sp_rand_of_carrier : sp_rand_carrier -> rand sp_enc_scheme ;
  sp_choice_msg_type : choice_type ;
    (* the choice_type a plaintext is encoded as on the oracle interface *)
  sp_choice_cipher_type : choice_type ;
    (* the choice_type a ciphertext is encoded as; the type of each leaked slot *)
  sp_choice_msg_of_plain : plain sp_enc_scheme -> sp_choice_msg_type ;
  sp_plain_of_choice_msg : sp_choice_msg_type -> plain sp_enc_scheme ;
  sp_choice_msg_of_plainK : cancel sp_choice_msg_of_plain sp_plain_of_choice_msg ;
  sp_choice_cipher_of_cipher : cipher sp_enc_scheme -> sp_choice_cipher_type ;
  sp_cipher_of_choice_cipher : sp_choice_cipher_type -> cipher sp_enc_scheme ;
  sp_choice_cipher_of_cipherK :
    cancel sp_choice_cipher_of_cipher sp_cipher_of_choice_cipher ;
  sp_pub_key_of_party : party_id -> pub_key sp_enc_scheme ;
  sp_msg_of_index : 'I_sp_card_plaintext -> plain sp_enc_scheme ;
  sp_fallback_rand : rand sp_enc_scheme ;
    (* randomness returned by an out-of-range slot lookup; dead in a well-formed
       game (every slot is filled by a prior sample), present only for totality *)
}.
```

The scheme/marshalling block is exactly the parameter list of the current
`dsdp_advantage_derived` (`dsdp_game_symbolic.v:262`), with each abbreviated name
expanded and re-cast in `X_of_Y` / `K`-suffix form.

## 5. The adversary record and the theorem

```coq
(* dsdp_indcpa_adversary P — a distinguisher against problem P plus its
   well-formedness. The secrecy theorem quantifies over this record, so quantifying
   over it is quantifying over all valid adversaries. *)
Record dsdp_indcpa_adversary (P : dsdp_indcpa_secrecy_problem) := {
  adv_locations : Locations ;
  adv_package   : raw_package ;
  adv_valid : ValidPackage adv_locations (game_iface_P P) A_export adv_package ;
  adv_disjoint_from_protocol_state : fseparate adv_locations (protocol_state_P P) ;
  adv_disjoint_from_real_oracle : fseparate adv_locations (real_oracle_P P).(locs) ;
  adv_disjoint_from_zero_oracle : fseparate adv_locations (zero_oracle_P P).(locs) ;
}.

Definition corrupted_view (P : dsdp_indcpa_secrecy_problem) : seq alice_obs :=
  obs_of_procs (sp_corrupted_party_program P) (sp_received_hop_ciphertexts P)
    (sp_challenge_secret P) (sp_leak_order P)
    (sp_card_plaintext P) (sp_card_randomness P).
Definition game_of_problem (P) : game_code := game_of_trace (corrupted_view P).
Definition real_game (P) : raw_package :=
  denote_game (sp_rand_carrier_card P) (sp_rand_of_carrier P)
    (sp_choice_msg_of_plain P) (sp_choice_cipher_of_cipher P)
    (sp_pub_key_of_party P) (sp_msg_of_index P) (sp_fallback_rand P)
    (all_real (game_of_problem P)).
Definition zero_game (P) : raw_package := (* …same projections… *)
    denote_game … (all_zero (game_of_problem P)).

Theorem dsdp_indcpa_secrecy (P : dsdp_indcpa_secrecy_problem)
    (Adv : dsdp_indcpa_adversary P) :
  AdvantageE (real_game P) (zero_game P) (adv_package Adv)
    <= (count_obs_hops (corrupted_view P))%:R * epsilon_cpa.
```

`game_iface_P`, `protocol_state_P`, `real_oracle_P`, `zero_oracle_P` are thin projections
that apply the back end's `game_iface` / `protocol_state` / `oracle_real_pkg` /
`oracle_zero_pkg` to the fields of `P` (see the mapping table in the appendix). The `_P`
suffix avoids a name clash with the imported back-end globals `game_iface`/`protocol_state`.
The hop count is left inline as `count_obs_hops (corrupted_view P)` rather than given a new
name, because `count_hops` and `count_obs_hops` already exist with different argument types.

Two facts the adversarial Rocq audit established by compilation (both fixed in the plan):
(1) under `Set Primitive Projections`, every record field must be accessed as `P.(field)`,
not `field P` (the record argument is implicit for function-valued fields whose domain
mentions the record). (2) `dsdp_indcpa_secrecy` is proved GENERICALLY for any `P` via the
back end's `advantage_le` (bridging `count_obs_hops` to `size (hop_sites …)` then
`eapply advantage_le`), not via the `gc_dsdp`-specific `advantage_gc_dsdp` (which times out
under an abstract `P`). The DSDP `2 * epsilon_cpa` bound is the corollary at
`P := dsdp_problem …`.

## 6. Derivation internals

New definitions, in dependency order.

In `dumas2017dual/dsdp/dsdp_symbolic.v`:

- `pbob_sym`, `pcharlie_sym : proc symbolic_data` — Bob and Charlie at
  `Symbolic_DSDP_Interface`, erased (parallel to the existing `palice_sym:133`).
- `first_send : proc symbolic_data -> option symbolic_data` — runs an erased proc to
  its head `Send` and returns the payload. Same forcing of the HOAS continuation that
  `sent_payloads:107` already performs.
- `dsdp_received_hop_ciphertexts : seq symbolic_data` —
  `pmap first_send [:: pbob_sym ; pcharlie_sym]`, the structured secret-bearing
  receptions in reception order. Computes to
  `[:: SD_cipher (HE_enc 1 (HE_var 10) rb1) ; SD_cipher (HE_enc 2 (HE_var 11) rc1) ]`.

In `dumas2017dual/dsdp/dsdp_game_symbolic.v`:

- `walk_obs` — the dual-purpose drive. At each reception it pops the next structured
  response, reads `(party, secret)` off the `HE_enc party (HE_var secret) _`, emits
  `AO_recv_hop party secret result` with a freshly allocated `result` name, and recurses
  on the continuation fed the opaque `SD_cipher (HE_var result)`. At each send it emits
  `AO_combine (fresh name) payload`. It halts on the first unanswered reception. Because
  `symbolic_get_cipher` returns `Some` on both the structured and the opaque carrier, the
  corrupted proc takes the same branch either way, so the combine payloads stay
  byte-identical to today's `dsdp_observed_combines`.
- `collect_samples : seq alice_obs -> seq alice_obs` — scans the hop-and-combine output
  for free variables, splitting `HE_var` value names from `HE_enc` randomness slots by
  syntactic position, preserving first appearance, dedup. Emits `AO_sample_val` for the
  value names then `AO_sample_rnd` for the randomness slots.
- `obs_of_procs corrupt hop_sends challenge leak card_msg card_renc : seq alice_obs` —
  `collect_samples card_msg card_renc w ++ [:: AO_put challenge] ++ w ++
   [:: AO_leak (leak (combine_names w) (recv_names w))]`, where `w := walk_obs corrupt
   hop_sends 100`. It takes the loose symbolic arguments (not the record), so the projection
   `corrupted_view P` applies it to `P`'s symbolic fields and `dsdp_alice_obs` stays
   scheme-agnostic.
- `dsdp_problem (…) : dsdp_indcpa_secrecy_problem` — the DSDP instance, a record literal:
  `sp_corrupted_party_program := palice_sym`,
  `sp_received_hop_ciphertexts := dsdp_received_hop_ciphertexts`,
  `sp_challenge_secret := <first hop secret>`,
  `sp_leak_order := fun combines recvs => combines ++ recvs`, and the scheme block from
  the caller. `dsdp_alice_obs := corrupted_view (dsdp_problem …)` replaces the literal.

Reused unchanged: `game_of_trace:176`, `lower_obs:155`, `resolve_term:137`,
`count_obs_hops:120`, and the entire back end.

## 7. The `gc_dsdp` rebuild (computed evidence)

The structural sample order is first-appearance, value-vars then randomness-slots:
`[v2 ; v3 ; u2 ; r2 ; u3 ; r3]` then `[ra1 ; ra2]`. The current fixture
(`dsdp_game_code.v:923`) uses `[v2 ; v3 ; u2 ; u3 ; r2 ; r3]` then `[ra1 ; ra2]`.

The `GC_sample` prefix is textually unchanged: all six value samples are
`GC_sample card_plaintext`, so reordering them among themselves leaves the literal
`GC_sample card_plaintext (… ×6)` identical. Only the de Bruijn indices the two combines
use change, because the value stack is built in a different order. Tracing the stacks:

- value stack after the prefix, current: `r3@0 r2@1 u3@2 u2@3 v3@4 v2@5`
- value stack after the prefix, new:     `r3@0 u3@1 r2@2 u2@3 v3@4 v2@5`

So `u2@3`, `v3@4`, `v2@5`, `r3@0` are unchanged; `r2` moves `1→2` and `u3` moves `2→1`.
Pushing the two hops (`c2`, `c3`) and `a1` shifts uniformly, giving exactly two edits:

- `a1` (line 936): `HE_enc 1 (HE_var 3) 1` → `HE_enc 1 (HE_var 4) 1`   (`r2` index `3→4`)
- `a2` (line 938): `HE_epow (HE_var 1) (HE_var 5)` → `HE_epow (HE_var 1) (HE_var 4)`
  (`u3` index `5→4`)

The put, both hops, the randomness slots (`ra1@1`, `ra2@0`), and the leak
`[HE_var 1 ; HE_var 0 ; HE_var 3 ; HE_var 2]` are all unchanged. The prefix comment
updates from `iV2 iV3 iU2 iU3 iR2 iR3` to `iV2 iV3 iU2 iR2 iU3 iR3`. `dsdp_faithful`
fails to compile if either index is wrong, so the edit is machine-guarded.

The back end survives the reorder: `advantage_le` is generic over sample structure,
`denote_run` dispatches each `GC_sample` on its own cardinality, and
`all_real`/`all_zero`/the shims all derive from the same `gc`, so the canonical-sample-
order invariant holds. The reordered game is sampling-commutation-equivalent to the old
one, so the bound is unaffected.

## 8. Why faithfulness stays `by []`

`obs_of_procs P` reads only the early, non-dependent fields of `P` (the two cardinalities,
`sp_corrupted_party_program`, `sp_received_hop_ciphertexts`, `sp_challenge_secret`,
`sp_leak_order`). The scheme block is never touched by the trace synthesis. For the
concrete `dsdp_problem` literal those projections reduce, and `walk_obs` /
`collect_samples` / `game_of_trace` are first-order syntactic functions over
`he_term` / `game_code` / `seq` with no distribution or monad machinery (that lives in
`denote_*`, which is untouched). This is the same computational regime as the existing
`dsdp_observed_combines_eq` (`dsdp_symbolic.v:175`, closed `by []`). Fallback to
`vm_compute` / `native_compute` if `simpl` is slow; no axiom is introduced either way.

## 9. Derived-vs-declared ledger

| Part | Source |
|---|---|
| hop party tag + secret | derived (off the senders' structured first sends) |
| combine terms `a1, a2` | derived (the corrupted party's sends) |
| sample membership + order | derived (free vars of the walk; first-appearance, role-split) |
| truncation point | derived (response-stream length; halt on the decrypt-receive) |
| which receptions are hops | declared (`sp_received_hop_ciphertexts`) |
| challenge secret | declared (`sp_challenge_secret`) |
| leak order | declared (`sp_leak_order`); leak set derived |
| cardinalities | declared (`sp_card_plaintext`, `sp_card_randomness`) |

A strict gain over today, where the entire sample / put / hop / leak scaffold is a literal.

## 10. Files touched

- `dumas2017dual/dsdp/dsdp_symbolic.v` — add `pbob_sym`, `pcharlie_sym`, `first_send`,
  `dsdp_received_hop_ciphertexts`.
- `dumas2017dual/dsdp/dsdp_game_symbolic.v` — add the two records, `walk_obs`,
  `collect_samples`, `obs_of_procs`, the projections, `dsdp_problem`; redefine
  `dsdp_alice_obs := corrupted_view (dsdp_problem …)`; re-prove `dsdp_faithful`,
  `dsdp_obs_hops`, `dsdp_advantage_derived` (now `dsdp_indcpa_secrecy`).
- `dumas2017dual/dsdp/dsdp_game_code.v` — rebuild `gc_dsdp` (two indices + comments).

No interface, session-type, or protocol-proc changes. The information-theoretic entropy
leg (`dsdp_entropy.v`) is not touched and does not depend on any of this.

## 11. Verification

1. Per-file `coqc` in dependency order; full `make` after the change.
2. `dsdp_faithful : game_of_trace (corrupted_view (dsdp_problem …)) = gc_dsdp …` by
   computation; `dsdp_obs_hops : count_obs_hops (corrupted_view (dsdp_problem …)) = 2`.
3. `Print Assumptions dsdp_indcpa_secrecy` carries only the inherited
   `enc_ind_cpa_real_or_zero` / `epsilon_cpa` plus the standard SSProve/classical axioms;
   no new custom axioms.
4. A temporary regression `corrupted_view (dsdp_problem …) = <old hand-built
   dsdp_alice_obs>` by `native_compute`, to confirm the derivation reproduces the prior
   trace before the old literal is deleted.
5. Pre-commit `rocq-auditor` (Stage 2) on every modified file; `Naming:` lines for any
   lemma name with five or more underscore segments.

## 12. Risks

- **R1 (main): the `walk_obs` reduction.** The dual-purpose drive must reduce to the
  concrete trace for `dsdp_faithful`. Mitigation: same first-order regime as the existing
  `by []` combine derivation; `vm_compute` / `native_compute` fallback.
- **R2: the two rebuilt indices.** Guarded by `dsdp_faithful` (wrong indices do not
  compile).
- **R3: `first_send` over erased HOAS.** Runs the erased proc to its head `Send`; the
  same forcing `sent_payloads` already does and proves `by []`.

## 13. Out of scope

- Retiring `gc_dsdp` as an independent fixture (it stays, as the validated anchor).
- The information-theoretic secrecy leg (separate probability world; no shared artifact
  beyond the protocol program).
- Generalizing `obs_of_procs` past a single passive corruption, or past a leak that
  includes a decrypted value (the single-sort `he_term` / `HE_dec → 0` limit).

---

## Appendix: record field to back-end argument map

| record field | back-end use | current name |
|---|---|---|
| `sp_rand_carrier_card` | `denote_game`, `oracle_*_pkg` arg 1 | `renc_card` |
| `sp_rand_of_carrier` | `denote_game`, `oracle_*_pkg` arg 2 | `rand_of_renc` |
| `sp_choice_msg_of_plain` | `denote_game` arg 3 | `chmsg_of_msg` |
| `sp_plain_of_choice_msg` | `oracle_real_pkg` arg 3 | `msg_of_chmsg` |
| `sp_choice_cipher_of_cipher` | `denote_game`/`oracle_*` arg 4 | `chcipher_of_cipher` |
| `sp_cipher_of_choice_cipher` | bound proof | `cipher_of_chcipher` |
| `sp_choice_msg_of_plainK` | bound proof | `chmsg_of_msgK` |
| `sp_choice_cipher_of_cipherK` | bound proof | `chcipher_of_cipherK` |
| `sp_pub_key_of_party` | `denote_game`/`oracle_*` last arg | `pkey_of_party` |
| `sp_msg_of_index` | `denote_game` arg 6 | `msg_of_idx` |
| `sp_fallback_rand` | `denote_game` arg 7 | `rand0` |
| `sp_card_plaintext` | `gc_dsdp` sample cardinality | `card_msg` |
| `sp_card_randomness` | `gc_dsdp` sample cardinality | `card_renc` |

Real/zero oracle asymmetry: `oracle_real_pkg` arg 3 is `sp_plain_of_choice_msg` (the
`t_msg -> plain` decoder), but `oracle_zero_pkg` arg 3 is `sp_choice_msg_type` (the
choice_type itself), per `dsdp_advantage_derived:277,280`. The `real_oracle`/`zero_oracle`
projections must wire these asymmetrically.
