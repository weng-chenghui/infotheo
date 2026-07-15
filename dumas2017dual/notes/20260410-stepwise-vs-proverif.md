# 2026-04-10: DSDP Stepwise Formalization vs. ProVerif

## Comparison Table

| Dimension | DSDP Stepwise (Coq/MathComp) | ProVerif |
|---|---|---|
| **Protocol language** | `proc data`: `PInit`, `PSend`, `PRecv`, `PRet`, `PFinish`, `PFail` — first-order AST, no replication | Applied pi-calculus: `in(c,x)`, `out(c,M)`, `!P`, `new n` — higher-order, unbounded sessions via `!` |
| **Action granularity** | Fine-grained: `AEnc`, `ADec`, `AMul`, `APow`, `AAdd`, `ASend`, `ARet` — each crypto op is a separate transition | Coarse-grained: `out(c, senc(m,k))` bundles encryption + send into one step |
| **Program → transitions** | Protocol-specific compiler (`translate_raw`) pattern-matches proc AST to emit action list; proved equal to hand-written spec (`dsdp_raw_translate_eq`) | No separation — the pi-calculus process IS the execution; Horn clause resolution over-approximates all interleavings |
| **State model** | Explicit `sw_global_state = nat → sw_party_state` with `ps_plain : {fset msgT}`, `ps_cipher : {fset encT}`, `ps_priv`, `ps_ret` per party | No explicit state — knowledge is implicit in what the attacker can derive; over-approximated across all sessions |
| **Execution** | Deterministic `foldM sw_step` over flat action list; each step checks preconditions (cipher known, key present) | Non-deterministic process reduction; tool explores all reachable states via Horn clause saturation |
| **Crypto model** | Concrete algebra: `enc pk m r` is a real group/ring operation in MathComp; homomorphic properties (`AMul`, `APow`) are computed | Symbolic (Dolev-Yao): `senc`, `aenc` are uninterpreted function symbols; properties only via equational theory `sdec(senc(x,k),k) = x` |
| **Homomorphic encryption** | Native: `AMul c1 c2` computes `enc pk (m1+m2) (r1+r2)`; `APow c x` computes `enc pk (x*m) (x*r)` — ring laws apply | Must manually axiomatize: add equation `hmul(enc(m1,pk,r1), enc(m2,pk,r2)) = enc(m1+m2,pk,r1+r2)` — no native algebraic structure |
| **Correctness** | Proved: `foldM sw_step sw_init_state dsdp_n_program = Some g_final ∧ ret_of g_final alice = Σ u_i * v_i` | **Cannot prove** — ProVerif has no notion of "the protocol computes the correct output value" |
| **Security property** | Information-theoretic: `H(VarRV \| AliceView_n) = log(m^n_relay)` — exact conditional entropy bound | Symbolic: reachability (secrecy), correspondence (authentication), observational equivalence (privacy) |
| **Security model** | Honest-but-curious eavesdropper; entropy over concrete probability distributions | Active Dolev-Yao attacker controls network; can intercept/replay/inject (strictly stronger threat model) |
| **N-party** | Parametric: `n_relay : nat`, indexed by `'I_n_relay.+2` ordinals; single proof covers all N | Must enumerate parties or use `!` replication (no native `∀ i ∈ 1..n`); replication causes false attacks |
| **Soundness** | Full Coq kernel check — no false positives, no false negatives | Sound but incomplete — may report false attacks; never misses real attacks |
| **Automation** | Manual proof (~months); machine-checked | Push-button (~minutes); may need manual refinement for false attacks |
| **Termination** | Guaranteed (Coq proofs are total) | Not guaranteed (usually terminates in practice) |
| **Stateful protocols** | Natural: state is the core abstraction (`sw_global_state` threaded through `foldM`) | Difficult: stateful extensions exist but increase false attack rate |

### Summary of Trade-offs

| | DSDP Stepwise | ProVerif |
|---|---|---|
| **Proves correctness** | Yes | No |
| **Proves security** | Information-theoretic | Symbolic |
| **Handles HE natively** | Yes | No (must axiomatize) |
| **Parametric in N** | Yes | No |
| **Active attacker** | No (eavesdropper) | Yes (Dolev-Yao) |
| **Automation** | Manual | Automatic |
| **False positives** | None | Possible |

The tools are complementary, not competing. ProVerif handles active attackers and authentication automatically but cannot express computational correctness or information-theoretic entropy bounds. The DSDP formalization proves properties ProVerif structurally cannot (correctness, exact entropy), while ProVerif covers threat models the DSDP formalization does not address (active network attackers, replay attacks).

## Why ProVerif Cannot Prove Correctness

ProVerif's logic is built around **reachability queries**: "can the attacker learn secret `s`?" or "does event `e` always follow event `e'`?" These are yes/no questions about whether a state is reachable or a correspondence holds.

Correctness is a **quantitative, value-level** statement: "the protocol computes exactly `Σ u_i * v_i`." This requires:

1. **Concrete algebra** — ProVerif treats `enc`, `dec`, `mul` as uninterpreted symbols. It knows `dec(enc(m,k),k) = m` but cannot compute that `dec(enc(u*v, k), k) * dec(enc(u'*v', k), k)` equals `u*v + u'*v'` under a ring structure. There is no ring/group solver.

2. **Deterministic execution trace** — Correctness says "run these steps in order, get this value." ProVerif over-approximates by merging all possible interleavings into one Horn clause set. It loses track of which specific value arrives at which step.

3. **Equality of output to specification** — ProVerif can ask "is `x` secret?" but not "does `x` equal `f(inputs)`?" There is no query form for `output = Σ u_i * v_i`.

In short: ProVerif's query language asks about *security predicates* (reachable/unreachable, before/after), not *functional equations* (output = expected). The DSDP formalization needs both — `foldM sw_step` computes a concrete value and we prove it equals the dot product — which lives outside ProVerif's expressible properties.
