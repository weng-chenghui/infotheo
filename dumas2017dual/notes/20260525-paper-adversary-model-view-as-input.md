# 2026-05-25 — Paper exposition: the view-as-input adversary model and why it is sound

Academic-paper-style write-up of the corrupted-Alice guessing-game model adopted
in the view-as-input (1a) refactor, and the soundness argument. Written to the
message conventions (no em-dashes, semicolons, or aside-parentheses) so it can be
lifted into a paper draft.

Context: this is the model the 1a refactor implements to close the soundness hole
found in [[20260525-two-channel-secrecy-fiber-vs-indcpa]] (the old model let an
adversary suppress the secret sample and guess a predictable default, winning
with probability one). Scope of the refactor: [[20260525-view-as-input-refactor-scope]].

## Adversary model

We consider a static, semi-honest corruption of Alice. The adversary A is a
function from Alice's protocol view to a distribution over the message space,
written A : Y -> Δ(R), where Y is the transcript Alice legitimately observes
during one protocol run and R is the space in which the secret scalar V_2 lives,
with |R| = m. The game is run by a challenger. The challenger draws all protocol
randomness, including the secret V_2, executes the protocol to produce Alice's
view Y, hands Y to A, and receives a guess g = A(Y). The adversary wins if
g = V_2. The quantity we bound is Pr[A(Y) = V_2], universally over all A.

## Flow diagram

The "adversary" and "predictor" are the same entity at two levels: A : Y -> Δ(R)
is the abstract adversary, and the predictor (the closed
[package [interface] guesser_export]) is its SSProve realization.

```
  CHALLENGER             GAME                    ADVERSARY (= predictor)
  (boolean_shell)        (game_enc_zero)         A : Y → Δ(R)
  ═══════════════        ═══════════════         ═══════════════════════
        │                      │                          │
  (1)   │── run ──────────────►│                          │
        │                      │  sample V_2 ~ Unif(R)    │
        │                      │  store V_2, build        │
        │                      │  view Y (ciphers of 0)   │
        │◄──── view Y ─────────│                          │
        │                      │                          │
  (2)   │──────────── hand view Y ───────────────────────►│
        │                      │                          │  receive Y
        │                      │                          │  (use OR drop)
        │◄───────────── guess g ──────────────────────────│  g = A(Y)
        │                      │                          │
  (3)   │── read V_2 ─────────►│                          │
        │◄──── V_2 ────────────│                          │
        │                      │                          │
  (4)   │  output  (g == V_2)                             │
        ▼
   win  ⟺  g = V_2.        ∀ A :   Pr[win]  ≤  1/m + 2·ε

  ───────────────────────────────────────────────────────────────────
  SOUNDNESS, read off the flow:
  • Step (1) draws V_2 UNCONDITIONALLY, driven by the challenger,
    before the adversary acts. The adversary never controls whether
    the secret is sampled.
  • The adversary only RECEIVES the view Y at step (2). It may use Y
    or drop it. Dropping Y costs information. It cannot suppress V_2.
  • In game_enc_zero the view Y is independent of V_2 (ciphers of 0),
    and V_2 is uniform over R with |R| = m, so Pr[g = V_2] = 1/m for
    EVERY A. The two IND-CPA hops add 2·ε.  Hence ∀ A, Pr[win] ≤ 1/m + 2·ε.

  Contrast (the old, unsound flow): the adversary itself issued step (1)
  to pull its view, and that call was what sampled V_2. An adversary
  could skip step (1) entirely, leaving V_2 unsampled at its default,
  and guess that default to win with probability 1.
```

## Why the adversary receives its view as input

Two formulations are possible. In the first, the challenger generates the view
and passes it to the adversary as an argument. In the second, the adversary
actively queries an oracle to obtain its view, and that same query is what draws
the secret. We adopt the first, and it is the only sound choice for a guessing
game. The secret must be a fresh sample drawn by the challenger on every
execution, outside the adversary's control. If the secret were instead drawn
only as a side effect of the adversary querying for its view, an adversary could
simply decline to query. The secret would then never be drawn, and the guess
would be compared against a fixed default value that the adversary can predict
and name in advance. Such an adversary wins with probability one, and no secrecy
bound holds. The view-as-input formulation forecloses this. The secret is
sampled unconditionally by the challenger, and the adversary's only freedom is
whether to use or to ignore the view it is handed. Ignoring the view costs the
adversary information. It never lets the adversary suppress the secret.

## Why the bound is sound

The statement is universally quantified over all adversaries A, as a security
theorem must be. After the two IND-CPA transitions, the transcript Alice sees
consists of encryptions of zero, so the view Y is statistically independent of
V_2. Hence for every A the guess A(Y) is independent of V_2. Since V_2 is
uniform over R with |R| = m, we have Pr[A(Y) = V_2] = 1/m for every A. Returning
from the ideal transcript to the real transcript costs at most 2ε by the two
IND-CPA reductions, where ε bounds the IND-CPA advantage of the encryption
scheme. The end-to-end bound is therefore Pr[A wins] <= 1/m + 2ε for every A.
The universal quantifier is what makes this a secrecy guarantee. A bound proved
for a single fixed A would be an example, not a theorem.

## Why the IND-CPA swap is sound: the computational bridge

The flow above is the ideal endpoint, the game where the ciphers encrypt 0 and
the 1/m is information-theoretic. The reasonableness of the swap is the
computational bridge from the real game to that ideal one, and the view-as-input
flow is exactly what makes the bridge clean.

What the swap is. The real game hands the adversary a view Y_real containing
real encrypted contributions, Enc(pk_b, u_2*v_2 + ...) and so on. The ideal game
hands Y_zero containing Enc(pk_b, 0). The swap replaces the former with the
latter. Its soundness is the IND-CPA assumption, argued by reduction.

The reduction. Suppose some adversary A guessed V_2 noticeably better in the real
game than in the ideal game, i.e. Pr[A wins | real] - Pr[A wins | zero] > ε.
Build a reduction B against IND-CPA of the encryption scheme. B receives an
IND-CPA challenge ciphertext ct = Enc(pk_b, m_b) where m_0 is the real
contribution and m_1 = 0. B assembles Alice's view Y exactly as the challenger
would, but places ct in the slot being swapped, and runs g <- A(Y). B then
outputs the bit [g == V_2]. By construction that bit has distribution
Pr[A wins | real] when b = 0 and Pr[A wins | zero] when b = 1, so B distinguishes
the two encryptions with advantage > ε, contradicting IND-CPA. Hence the swap
changes A's success by at most ε. Two swaps, Bob's and Charlie's ciphertexts,
give the 2*ε.

Why the reduction is valid. The swapped ciphertexts are under pk_b / pk_c, keys
for which Alice holds no secret key. That is what makes IND-CPA applicable: the
adversary cannot decrypt them, so it cannot tell Enc(real) from Enc(0). Alice's
own decryptions, under her Dk_a, are of other slots and are simulated by B
without needing sk_b or sk_c.

Why view-as-input makes the reduction legitimate. The reduction works only
because A is a function of the view it is handed, A : Y -> Δ(R). That is what
lets B treat A as a black-box subroutine: B constructs the view with the
challenge ciphertext embedded, calls A on it, and reads the guess. B never needs
A's internals and never needs the secret key. It is the SAME A as in the
ideal-game flow, just placed in a different challenger.

```
  IND-CPA challenger            Reduction B                  Adversary A
  (scheme, key pk_b)            (our challenger,             (= predictor)
                                 instrumented)
  ──────────────────            ────────────────             ────────────
        │  ct = Enc(pk_b, m_b)        │                            │
        │ ───────────────────────────►│ build view Y with ct       │
        │                             │   in the swapped slot       │
        │                             │ ───────── hand Y ──────────►│
        │                             │ ◄───────── guess g ─────────│  g = A(Y)
        │                             │ output bit [g == V_2]       │
        │ ◄── that bit distinguishes m_0 from m_1 ──                │
```

In the old "adversary pulls its own view via an oracle" model the reduction
would have to intercept A's oracle queries and also manage the secret sampling,
the same entanglement that produced the soundness hole. View-as-input separates
"challenger builds the possibly-swapped view" from "adversary maps view to
guess," and the reduction lives entirely in the first half.

In the SSProve terms of the development. The distinguisher is boolean_shell ∘ A,
the challenger wrapping the adversary, whose output bit is the win indicator. The
swap soundness is exactly

  AdvantageE game_real game_enc_zero (boolean_shell ∘ A)  <=  2*ε

which [advantage_game_real_game_enc_zero] proves via the four-game hop chain,
each hop's ε supplied by the scheme's IND-CPA assumption
([enc_ind_cpa_real_or_zero]). Combined with the ideal-game 1/m:

  Pr[A wins | real]  <=  Pr[A wins | zero]  +  2*ε  <=  1/m + 2*ε,  for every A.

So the swap is justified because the challenger generates the view and can
therefore be re-used as an IND-CPA reduction that embeds a challenge ciphertext
into that view and runs the same A as a subroutine. The IND-CPA assumption caps
how much the swap can change A's win rate, which is the 2*ε. The 1/m is the
residue once the view carries no information about V_2 at all.

## Tightness

The bound is achieved. The adversary that ignores its view and outputs a
uniformly random element of R wins with probability exactly 1/m, matching the
ideal-world term. This shows the 1/m is intrinsic to the protocol and not an
artifact of a loose analysis.

## Connecting the model to the mechanization

In the formalized version the challenger is realized as a package that draws
V_2, produces the cipher view, and passes that view to the adversary, so the
adversary is structurally a closed function of the view and has no oracle access
by which it could read or pre-empt the secret. That ties the paper's
"view as input" wording to the soundness fix in the Coq development: the
predictor becomes a closed [package [interface] guesser_export] whose [id_guess]
takes the cipher view as an argument, and [boolean_shell] is the challenger that
samples V_2, runs [id_game_run] for the view, and hands the view to the
predictor.

## Conclusion

The challenger owns the view, so it can deliver either the real-cipher view or
the zero-cipher view to the same adversary. Replacing one ciphertext with an
encryption of zero shifts any efficient adversary's win probability by at most
ε, because that ciphertext lies under a key the adversary cannot decrypt. Two
such swaps move the win probability by at most 2ε. In the zero-cipher view the
secret is information-theoretically hidden, giving 1/m. So the real-world win
probability is at most 1/m + 2ε.

## Related

- [[20260525-two-channel-secrecy-fiber-vs-indcpa]] — the soundness hole this model fixes.
- [[20260525-view-as-input-refactor-scope]] — the refactor scope.
- [[20260525-pr-guess-enc-zero-direct-independence-plan]] — why the forall bound
  stays an assumption (SSProve absolute-Pr gap) even once it is sound.
