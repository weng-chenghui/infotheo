# Plan: add short pen-and-paper math to the blueprint nodes

Date: 2026-06-09
Status: PLAN ONLY (not executed). Awaiting go-ahead.

## Goal

Each definition/lemma/theorem node in `dumas2017dual/blueprint/src/content.tex`
currently carries prose only. Following the `mathcomp-qbs` blueprint
(`ch-giry.html`), keep the prose and add ONE short pen-and-paper math line per
node that states its formal content in concept notation, never Rocq code. The
Rocq identifier stays where it is, in the `\rocq{}` link. Blueprint-only: the
thesis chapters already develop the math in full, so nothing changes there.

## Style decision

- One compact statement per node, rendered as a single displayed line `\[ ... \]`
  for grammars and bounds, or inline `\(...\)` for trivial ones. Use `\(\)`/`\[\]`
  (the config sets `mathjax-dollars=False`).
- Pen-and-paper symbols only: $\sem{\cdot}$ denotation, $\AdvE$ advantage,
  $\epscpa$, homomorphic $\hadd$/$\hmul$, $\Enc$/$\Dec$, $\nhops$, grammars with
  `::=`. No Rocq identifiers inside math (those live in `\rocq{}`).
- Placement: append the math right after the existing prose sentence(s), before
  `\end{definition}` / `\end{...}`. Prose is untouched.

## Notation macros (append to `src/macros/common.tex`)

    \newcommand{\sem}[1]{[\![#1]\!]}        % denotation into SSProve
    \renewcommand{\AdvE}{\mathsf{Adv}}      % already defined; keep
    \newcommand{\Dec}{\mathsf{Dec}}
    \newcommand{\hadd}{\boxplus}            % homomorphic ciphertext add (Emul)
    \newcommand{\hmul}{\boxdot}             % homomorphic scalar action (Epow)
    \newcommand{\nhops}{\#\mathrm{hops}}
    \newcommand{\sites}{\mathrm{sites}}
    \newcommand{\gtrace}{\mathcal{G}}       % game_of_trace
    \newcommand{\view}{\mathrm{view}}
    \newcommand{\samples}{\mathrm{samples}}
    \newcommand{\walk}{\mathrm{walk}}
    \newcommand{\cat}{\mathbin{+\!\!+}}     % sequence append
    \newcommand{\Oreal}{\mathcal{O}_{\real}}
    \newcommand{\Ozero}{\mathcal{O}_{\zero}}

(`\Enc`, `\epscpa`, `\real`, `\zero` already exist in `common.tex`.)

## Per-node math (one line each)

Chapter 1 — symbolic protocol model
- def:symbolic_interface: `\[ d ::= \mathsf{plain}(t)\mid\mathsf{cipher}(t)\mid\mathsf{sk}(n)\mid\mathsf{pk}(n),\quad t\in\text{terms with }\Enc,\hadd,\hmul \]`
- def:palice_sym: inline signature only `\(P_A\)`, the corrupt program over symbolic data (no formula; it is a program).
- def:sender_programs: `\[ c_2=\Enc_{pk_B}(v_2),\quad c_3=\Enc_{pk_C}(v_3),\quad \text{challenge}=v_2 \]`
- lem:observed_combines: `\[ a_1=(u_2\hmul c_2)\hadd\Enc_{pk_B}(r_2),\qquad a_2=(u_3\hmul c_3)\hadd\Enc_{pk_C}(r_3) \]`
- def:received_hops: `\[ \rho=[\,c_2,\,c_3\,] \]`

Chapter 2 — deriving the corrupted view
- def:alice_obs: `\[ o ::= \mathsf{smp}_v(c,x)\mid\mathsf{smp}_r(c,x)\mid\mathsf{put}(x)\mid\mathsf{recv}(p,s,x)\mid\mathsf{comb}(x,e)\mid\mathsf{leak}(\bar x) \]`
- def:walk_obs: inline `\(\walk(p,\rho,n)\)`; on receiving $\Enc_p(s)$ it emits $\mathsf{recv}(p,s,n)$ and recurses at $n{+}1$.
- def:collect_samples: `\[ \samples(\tau)=[\,\mathsf{smp}_\bullet(c,x)\mid x\in\mathrm{fv}(\tau)\,]\ \text{in first-appearance order} \]`
- def:obs_of_procs: `\[ \mathrm{obs}(p,\rho,ch,\ell)=\samples(w)\cat[\mathsf{put}(ch)]\cat w\cat[\mathsf{leak}(\ell)],\quad w=\walk(p,\rho,100) \]`
- lem:obs_of_procs_dsdp: `\[ |\tau_{\mathrm{DSDP}}|=14:\ 8\ \mathsf{smp},\ \mathsf{put}(v_2),\ \mathsf{recv}(B,v_2),\mathsf{recv}(C,v_3),\ \mathsf{comb}(a_1),\mathsf{comb}(a_2),\ \mathsf{leak}(a_1,a_2,c_2,c_3) \]`
- def:dsdp_alice_obs: `\[ \tau_{\mathrm{DSDP}}=\mathrm{obs}(P_A,[c_2,c_3],v_2,\ \mathrm{comb}\cat\mathrm{recv}) \]`

Chapter 3 — lowering to game code
- def:embedding: `\[ t ::= x\mid k\mid\Enc(p,t,r)\mid\Dec(p,t)\mid t\hadd t\mid t\hmul t\mid t{+}t\mid t{-}t\mid t{\cdot}t \]` and `\[ g ::= \mathsf{smp}(c,g)\mid\mathsf{put}(t,g)\mid\mathsf{let}(t,g)\mid\mathsf{hop}(p,t,g)\mid\mathsf{ret}(\bar t) \]`
- def:resolve_term: `\[ \mathsf{res}_\Gamma(x)=\mathrm{idx}(x,\Gamma_v),\quad \mathsf{res}_\Gamma(\Enc(p,t,r))=\Enc(p,\mathsf{res}_\Gamma(t),\mathrm{idx}(r,\Gamma_r)) \]`
- def:lower_obs: inline `\(\mathsf{recv}\mapsto\mathsf{hop},\ \mathsf{comb}\mapsto\mathsf{let},\ \mathsf{leak}\mapsto\mathsf{ret}\)`.
- def:game_of_trace: `\[ \gtrace(\tau)=\mathrm{lower}(\varepsilon,\varepsilon,\tau) \]`
- def:count_hops: `\[ \nhops(\tau)=\#\{\mathsf{recv}\text{ before }\mathsf{leak}\},\quad \sites(g)=[0,\nhops(g)) \]`
- lem:count_hops_adequacy: `\[ \nhops(\gtrace(\tau))=\nhops(\tau) \]`

Chapter 4 — denotation into SSProve
- def:denote_game: `\[ \sem{\cdot}:\mathsf{game\_code}\to\mathsf{Package},\qquad \sem{t}_e\ \text{evaluates }t\text{ in environment }e \]`
- def:hybrid_endpoints: `\[ g^{(i)}\ \text{zeroes the first }i\text{ hops},\quad \mathrm{all\_real}=g^{(0)},\ \mathrm{all\_zero}=g^{(\nhops(g))} \]`

Chapter 5 — IND-CPA hybrid bound
- def:indcpa_assumption: `\[ \AdvE(\Oreal,\Ozero,A)\le\epscpa \]`
- def:denote_game_shim: inline `\(\mathrm{shim}_i(g)\)` routes hop $i$ through the oracle, inlines the rest.
- lem:hop_equiv: `\[ \sem{g^{(i)}}\approx\mathrm{shim}_i(g)\circ\mathcal{O}_b,\quad b\in\{\real,\zero\} \]`
- lem:advantage_hop: `\[ \AdvE(\sem{g^{(i)}},\sem{g^{(i+1)}},A)\le\epscpa \]`
- def:hybrid_ladder: `\[ \mathrm{ladder}(g)=[\,\sem{g^{(1)}},\dots,\sem{g^{(\nhops(g)-1)}}\,] \]`
- lem:advantage_sum_ladder_le: `\[ \text{a block of }n{+}1\text{ rungs}\ \le\ (n{+}1)\,\epscpa \]`
- thm:advantage_le: `\[ \AdvE(\sem{\mathrm{all\_real}(g)},\sem{\mathrm{all\_zero}(g)},A)\le|\sites(g)|\,\epscpa \]`

Chapter 6 — control record and generic theorem
- def:secrecy_problem: `\[ P=(\,p,\rho,ch,\ell,c_m,c_r\,;\ E,\ \mathit{marshalling}\,) \]`
- def:corrupted_view: `\[ \view(P)=\mathrm{obs}(P.p,P.\rho,P.ch,P.\ell) \]`
- def:games: `\[ \real(P)=\sem{\mathrm{all\_real}(\gtrace(\view(P)))}_E,\quad \zero(P)=\sem{\mathrm{all\_zero}(\cdots)}_E \]`
- def:adversary: inline `\(A\)` valid against $P$: typed by $P$'s interface, state-disjoint.
- thm:generic_secrecy: `\[ \AdvE(\real(P),\zero(P),A)\le\nhops(\view(P))\,\epscpa \]`

Chapter 7 — DSDP instance
- lem:dsdp_faithful: `\[ \gtrace(\tau_{\mathrm{DSDP}})=g_{\mathrm{DSDP}} \]`
- def:dsdp_problem: `\[ P_{\mathrm{DSDP}}=(P_A,[c_2,c_3],v_2,\ \mathrm{comb}\cat\mathrm{recv},c_m,c_r;\ E,\dots) \]`
- lem:dsdp_problem_hops: `\[ \nhops(\view(P_{\mathrm{DSDP}}))=2 \]`
- thm:dsdp_secure: `\[ \AdvE(\real(P_{\mathrm{DSDP}}),\zero(P_{\mathrm{DSDP}}),A)\le 2\,\epscpa \]`
- cor:dsdp_advantage_derived: inline, same bound $\le 2\,\epscpa$ over the loose arguments.

Chapter 8 — deferred legs
- thm:it_leg: `\[ \Pr[\,\text{guess }v_2\,]\le 1/m\ \text{at the all-zero endpoint} \]`
- thm:composition: `\[ \text{total advantage}\le 1/m + 2\,\epscpa \]`

## Mechanics

1. Append the macro block to `src/macros/common.tex`.
2. For each node, insert its math after the prose, before the environment's
   closing tag. Do not touch `\rocq{}`, `\rocqok`, `\uses{}`, or the prose.
3. Program nodes (palice_sym, walk_obs, lower_obs, denote_game_shim, adversary)
   take an inline phrase, not a display, since they are programs/processes
   without a single headline formula.

## Verification

1. `dumas2017dual/blueprint/make_blueprint.sh`; open the site and confirm MathJax
   renders every new `\(\)`/`\[\]` (check $\sem{\cdot}$, $\hadd$, $\hmul$,
   $\AdvE$, the grammars). Fix any unsupported macro (MathJax supports
   `\boxplus`, `\boxdot`, `[\![ ]\!]`, `\mathcal`, `\mathsf`, `\Pr`).
2. Grep the new math for Rocq identifiers (`game_of_trace`, `obs_of_procs`,
   `dsdp_*`, snake_case) and confirm none leaked into math mode; pen-and-paper
   names only.
3. Spot-check three nodes (a grammar, a bound, the DSDP capstone) against the
   Rocq statements to confirm the math says what the code proves.

## Out of scope

- No thesis changes (the thesis already carries the full math).
- No new prose; this only adds the math line per node.
- No change to the dependency graph, the `\rocq{}` links, or the figure.
