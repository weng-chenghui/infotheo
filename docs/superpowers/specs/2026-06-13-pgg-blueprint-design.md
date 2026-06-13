# PGG framework blueprint design

- Date: 2026-06-13
- Status: design approved in brainstorming (architecture, diagram, chapters, node manifest, naming audit all confirmed with the user).
- Scope: a `rocqblueprint` (LaTeX/plasTeX, modeled on `dumas2017dual/blueprint`) telling the story of the PGG MPC framework's modularity and den Boer's concrete instantiation, in two parts, with one architecture diagram and a faithful per-chapter node graph.

## 1. The story

The PGG framework runs a monodromy/threshold card protocol whose recovered secret lives in a starting layout, with the cut word as anonymizing randomness. Its guarantees are theorems quantified over interface records; an *instance* is a tuple of records filling those interfaces. The blueprint makes that modularity structural: **Part I** introduces every interface and every generic theorem with no instance named; **Part II** is pure instantiation, with den Boer as the worked end-to-end hero, kim2025 as the biased family exercising the anonymity interface, and S₅ / S₅×S₅ as the large groups the admissibility gate rejects as AG codes.

The headline contrast the blueprint sells: **the worked MPC (den Boer), its quantitative leakage analysis (kim2025), and the impossibility theorem (the S₅ no-go) are all entirely axiom-free**; only "these large groups exist as covers of the right genus" is taken as six cited classical axioms, confined to the S₅ / S₅×S₅ chapters.

## 2. Naming

Display names in this blueprint are the **post-rename targets** from `docs/superpowers/plans/2026-06-13-pgg-naming-rename.md` (the naming audit). Until that rename executes, each `\rocq{}` link anchor uses the *current* identifier per that plan's mapping (e.g. display `pgg_recon_monodromy_correct` links to the current `pgg_hidden_invariant_perm`; display `s5_gap_infeasible` links to `s5_wired_gap_impossible`). Node *statements* use pen-and-paper math via macros (no Rocq code in statement bodies), exactly as the reference blueprint does.

## 3. The architecture diagram

`fig:bp:modularity` — a fixed interface column (Part I) with den Boer's six instantiation arrows (Part II), the generic-theorem band beneath, and the AG-code admissibility gate sorting instances by the Klein cap. TikZ source (faithful: every node, arrow, and label):

```latex
\begin{figure}[t]
\centering
\begin{tikzpicture}[
  iface/.style={draw, rounded corners, align=center, inner sep=4pt, font=\small,
                text width=4.0cm, minimum height=0.7cm, fill=black!4},
  plug/.style={draw, rounded corners, align=center, inner sep=3pt, font=\footnotesize,
               text width=3.2cm, minimum height=0.6cm},
  band/.style={draw, rounded corners, align=center, inner sep=4pt, font=\footnotesize,
               text width=6.4cm, fill=black!3},
  verdict/.style={draw, rounded corners, align=center, inner sep=3pt, font=\footnotesize,
                  text width=4.2cm, minimum height=0.6cm},
  every path/.append style={-stealth, thick}, font=\small ]

% ---- Part I: the interface column ----
\node[iface] (mono)  at (0,9.0) {\textbf{MonodromyRepr} / PGGInterface\\ \scriptsize cut group $G$, starts $\pi$};
\node[iface] (ts)    at (0,7.5) {\textbf{ThresholdScheme}\\ \scriptsize share $\cdot$ reconstruct};
\node[iface] (plug)  at (0,6.0) {\textbf{ReconPlug}\\ \scriptsize reconstruction invariance};
\node[iface] (ie)    at (0,4.5) {\textbf{InputEncoding}\\ \scriptsize inputs $\mapsto$ layout};
\node[iface] (prof)  at (0,3.0) {\textbf{MonodromyProfile} $+$ SecurityWitness\\ \scriptsize anonymity $\varepsilon$};
\node[iface] (pismc) at (0,1.5) {\textbf{piSMC dealer} $+$ session types};

% ---- Part II: den Boer plugs ----
\node[plug] (fkim)  at (6.2,9.0) {$\mathtt{FiveCardKim\_M}$, $\pi=\mathrm{ord\_tuple}\,5$};
\node[plug] (fcs)   at (6.2,7.5) {$\mathtt{fcI\_scheme}$};
\node[plug] (fcp)   at (6.2,6.0) {$\mathtt{five\_card\_plug}$};
\node[plug] (dbe)   at (6.2,4.5) {$\mathtt{den\_boer\_encoding}$};
\node[plug] (dbp)   at (6.2,3.0) {$\mathtt{den\_boer\_profile}$ ($\varepsilon=0$)};
\node[plug] (dbd)   at (6.2,1.5) {$\mathtt{den\_boer\_dealer\_layout}$};

\draw (fkim) -- (mono);  \draw (fcs) -- (ts);    \draw (fcp) -- (plug);
\draw (dbe)  -- (ie);    \draw (dbp) -- (prof);  \draw (dbd) -- (pismc);

% ---- generic theorems band ----
\node[band] (gen) at (0,-0.2) {\textbf{generic theorems} (proven once):\\
  $\mathtt{pgg\_recon\_monodromy\_correct}$ $\cdot$ $\mathtt{recon\_from\_layout\_output}$\\
  $\cdot$ $\mathtt{ts\_private}$ $\cdot$ $\mathtt{sw\_bound}$ $\cdot$ session duality};
\draw (ts) -- (gen); \draw (plug) -- (gen); \draw (ie) -- (gen);
\draw (prof) -- (gen); \draw (pismc) -- (gen);

% ---- den Boer end-to-end ----
\node[band, text width=4.0cm, fill=black!1] (e2e) at (6.2,-0.2)
  {\textbf{den Boer end-to-end:}\\ recovers $a\wedge b$, $I(\text{inputs};\text{view}\mid\text{out})=0$,\\
   $\mathtt{leak\_k}$ ramp, duality};
\draw (dbd) -- (e2e); \draw (dbe) -- (e2e);

% ---- the AG-code gate ----
\node[band, text width=7.2cm] (gate) at (3.0,-2.2)
  {\textbf{AlgebraicRigidity gate} \;($\mathtt{ar\_large\_group\_forces\_gap}\cdot\mathtt{ar\_gap\_bound}$)\\
   Klein cap $|A_5|=60$ sorts instances by $|G|$};
\draw (gen) -- (gate);

\node[verdict, fill=green!8] (sharp) at (-0.3,-4.0)
  {$|G|\le 60$: genus-0 sharp\\ \textbf{den Boer} $C_5$, $|G|=5$ \;\ding{51} AG code};
\node[verdict, fill=red!6]  (nogo)  at (6.0,-4.0)
  {$|G|>60$: AG-code no-go\\ \textbf{s5} $|G|{=}120$ \ding{55}, \textbf{s5x5} $|G|{=}14400$ \ding{55}\\
   \scriptsize genus forced $>0$; s5 $\to$ Bring genus 4; gap vacuous};
\draw (gate) -- (sharp); \draw (gate) -- (nogo);

\draw[densely dashed, black!40, -] (-2.4,0.7) -- (8.0,0.7);
\node[font=\itshape\scriptsize, anchor=west] at (-2.4,1.0) {Part I: the framework (no instance named)};
\node[font=\itshape\scriptsize, anchor=west] at (-2.4,0.45) {Part II: instantiation};
\end{tikzpicture}
\caption{The PGG framework's modularity. The interface column (left, Part~I) names no
instance; an instance is exactly a tuple of arrows filling the six slots. den Boer
(right, Part~II) fills all six and inherits every generic theorem (band, centre):
reconstruction is monodromy-invariant, the input encoding's output is correct under
every cut, the scheme is threshold-private, and the dealing is anonymous. Its end-to-end
guarantees follow: the protocol recovers $a\wedge b$, input privacy is perfect
($I=0$), partial views leak along the $\mathtt{leak\_k}$ ramp, and the dealer is
session-dual. The admissibility gate (bottom) sorts monodromy groups by the Klein cap
$|A_5|=60$: small groups admit a sharp genus-0 AG code (den Boer's $C_5$, \ding{51}),
while large groups are forced off genus 0, where the threshold gap is vacuous, so they
are an AG-code no-go (s5, s5x5, \ding{55}). The genus and gap are the AG-code lens; the
\ding{51}/\ding{55} is the verdict.}
\label{fig:bp:modularity}
\end{figure}
```

(Requires `\usepackage{pifont}` for `\ding`. A PNG render is produced and visually verified before shipping.)

## 4. Part I — the framework (chapters, with display-name nodes)

**Ch 1 Introduction** — the five-card trick → the framework idea; `fig:bp:modularity`; the Part I/II roadmap. No formal nodes.

**Ch 2 The monodromy interface** — `PGGTypes`, `isMonodromyRepr`, `MonodromyReprType`, `hasGenerators`, `MonodromyReprWithGeneratorType`, `PGGInterface`, `pi_starts`, `pgg_rho`, `endpoint` (+`endpointM`, `endpoint1`), `pgg_dtype`, `pgg_data`, `word_eval`, `achievable`, `search_space`, `endpoints`.

**Ch 3 Sharing, reconstruction, the recon plug** — `ThresholdScheme` (`ts_valid`, `ts_recon`, `ts_correct`, `ts_private`, `ts_encode_valid`), `ts_recon_perm_invariant`, `pgg_recon`, `pgg_recon_endpoints`, **`pgg_recon_monodromy_correct`** (the generic recovery theorem), `ReconPlug`, `CoveringData`, `CoveringScheme`, `genus_from_hurwitz`, `cd_fully_ramified`.

**Ch 4 Input encoding** — `InputEncoding` (`ie_assemble`, `ie_output`, `ie_assemble_valid`, `ie_orbit`), `ie_output_correct`, `recon_from_layout`, `recon_from_layout_output`.

**Ch 5 Anonymity: profile and security witness** — `SecurityExact`, `SecurityAsymptotic`, `SecurityWitness`, `ThresholdWitness`, `AlgebraicRigidity`, the `security_witness_*` constructors, `MonodromyProfile`.

**Ch 6 The piSMC realization** — `exchange_dealer`, `exchange_player`, `exchange_verifier`, `exchange_dealer_from_words`, `pgg_commit_prologue`, `exchange_dealer_with_commit`, `exchange_dealer_with_commit_nil`, `channels_dual`, and the duality family (one node: the 18 `*_dual_2` / `*_dual_gen` lemmas).

**Ch 7 Admissibility: the algebraic-rigidity gate** — `pgl_bound`, `genus0_automorphism_bound`, `pgl_bound_unfold`, `ar_complexity`, **`ar_genus_gap_dichotomy`**, **`ar_search_gap_dichotomy`**, `ar_large_group_forces_gap`, `ar_gap_bound`, `ar_protocol_correct`, `ar_search_space_chain`.

## 5. Part II — the instances

**Ch 8 den Boer: the perfect five-card MPC (axiom-free)** — `fc_sigma`, `fcI_valid`, `fcI_recon`, `fcI_reconK`, `fcI_scheme`, `fc_content`, `FiveCardKim_M`, `FiveCardKim_PI`, `fcI_perm_compatible_kim`, `five_card_plug`, `den_boer_layout`, `den_boer_assemble_valid`, `den_boer_orbit`, `den_boer_orbit_perm`, `den_boer_encoding`; the privacy spine `Omega`, `P`, `Secret`, `ViewA`, `Inputs`, `H_secret`, `leak_k1`, `leak_k2_adj`, `leak_k2_dist2`, `leak_k3`, `leak_k4`, `leak_k5`, `den_boer_view_count_eq`, `den_boer_cinde`, **`den_boer_input_private`**; the operational spine **`den_boer_run_output`**, `den_boer_decode`, `den_boer_decodeK`, `den_boer_dealer_layout`, the four `den_boer_layout_*_dual`; the profile `den_boer_profile`, `den_boer_perfect`, `den_boer_run_k`, `FiveCardKim_Teq`, `FiveCardKim_G_stable`, `FiveCardKim_protocol_correct`, `den_boer_committed_protocol_correct`.

**Ch 9 The five-card family and biased anonymity (kim2025, axiom-free)** — `five_card_profile`, `kim_lambda2`, `kim_spectral_gap`, `kim_spectral_gap_pos`, `kim_spectral_convergence`, `kim_var_dist_exact`, `fc_kim_doubly_stochastic`, `fc_kim_schreier_cert`, `fc_kim_asymptotic`, `fc_kim_security_witness`, `kim_profile`, `kim_complexity`. den Boer is the `ε=0` member.

**Ch 10 The S₅ no-go: a representation-theoretic obstruction (axiom-free)** — the wired rep `rG_secret`, `e0`, `proj_share`, `perm_repr`, `rG`; the kernel fact **`perm_module_no_dim23`** with its machinery `tperm_diff`, `diff_actE`, `nonconst_diff_in`, `all_diff_in`, `rank4_of_diff`, `diff_basis_mx`; the reduction `proj_mxmodule`, `mxrank_proj_pred`, `e0_proj_share`, `proj_share_rank`, `secret_proj_comm`; the no-go `s5_no_secret_dim3`, `s5_no_secret_dim4`, **`s5_gap_window_infeasible`**, **`s5_gap_infeasible`**; the window `secret_inv_dim`, `inv_dim`, `feasible`, `gap_dim_window`; the char-5 contrast `maschke_ss`; the genus ladder `genus0_data`/`genus0_covering`/`shamir_exact`, `genus1_data`/`genus1_covering`/`elliptic_gap`/`higher_genus_covering`/`higher_genus_gap_bound`, `genus2_data`/`genus2_covering`/`genus2_gap`; `CombinatorialRigidity`, `cr_large_group_with_gap`.

**Ch 11 S₅×S₅ and the Klein-cap genus context** — s5: `M_s5`, `s5_group_order_eq`⚠, `s5_brings_covering`, `s5_brings_covering_realised`⚠, `s5_brings_covering_genus`, `s5_hurwitz`, `s5_genus0_pgl_bound`, `s5_cs_gap`, `s5_rigidity`, `s5_tradeoff`, `s5_complexity`, `s5_rayleigh_Q2_R`⚠, `s5_spectral_convergence_gap`, `s5_profile`, `s5_weval_inj1`; s5x5: `M_s5x5`, `s5x5_group_order_eq`⚠, `s5x5_group_order_bound`, `s5x5_hurwitz`, `s5x5_covering`, `s5x5_inverse_galois_realised`⚠, `s5x5_rigidity`, `s5x5_protocol_correct`, `s5x5_tradeoff`, `s5x5_nonabelian`, `s5x5_combinatorial_rigidity`, `s5x5_multi_data`, `s5x5_multi_realised`⚠, `mcd_total_genus_s5x5_E`, `mcd_max_genus_s5x5_E`, `s5x5_spectral_TV_bound`, `s5_lazy_rayleigh_Q2_R`, `s5x5_pile1_stab`, `s5x5_profile`.

**Closing — the modularity ledger** — a table: each interface slot (rows) × instance (columns), entry = the filling node or "—"; plus a "generic vs instance-specific" split and the axiom tally (den Boer/kim/no-go: 0; s5: 3; s5x5: 3).

## 6. Status coloring

Three node colors, like the reference's green / dark-green / blue-dashed: **defined** (`◇`, definitions/records), **proved** (`✓`, Qed lemmas/theorems), **justified axiom** (`⚠`, the six cited facts: `s5_group_order_eq`, `s5_brings_covering_realised`, `s5_rayleigh_Q2_R`, `s5x5_group_order_eq`, `s5x5_inverse_galois_realised`, `s5x5_multi_realised`). The dependency graph renders the ⚠ nodes dashed so the axiom boundary is visible at a glance.

## 7. Build and tooling

Modeled on `dumas2017dual/blueprint`. Location: `pgg-smc/blueprint/` (the project is not at the git root, so `make_blueprint.sh` calls `plastex -c plastex.cfg web.tex` directly, as the reference does).

- `src/web.tex` — `\documentclass{report}`, `\usepackage{blueprint}[showmore, dep_graph]`, `\usepackage{tikz,pifont}`, `\home`/`\github`/`\dochome{coqdoc}`, `\input{content}`.
- `src/macros/common.tex` — theorem environments + pen-and-paper macros (cut, monodromy $\rho$, layout, recon, genus, gap, $\varepsilon$, mutual information, AG-code).
- `src/content.tex` — the eleven chapters as nodes, each `\rocq{<logical module>.<decl>}` (anchors per §2), `\rocqok` / `\notready` for the ⚠ axioms, `\uses{...}` edges from the manifest's `\uses` column.
- `make_blueprint.sh` — (1) blueprint HTML + dep graph via plasTeX; (2) coqdoc for the referenced modules into `web/coqdoc/`. Module list for coqdoc: `pgg_interface`, `pgg_sharing_framework`, `covering_scheme`, `input_encoding`, `algebraic_rigidity`, `cover_tradeoff`, `pgg_monodromy_profile`, `card_exchange_pismc`, `pgg_input_commitment`, the denboer1989 set (`five_card_group`, `five_card_program`, `five_card_scheme_I5`, `five_card_kim`, `five_card_family`, `den_boer_encoding`, `den_boer_profile`, `den_boer_run`, `five_card_leakage`), `rigidity_kim_instance`, `s5_nogo`, `gap_dimension`, `invariant_profiler`, `combinatorial_rigidity`, `cover_genus0`/`1`/`2`, `rigidity_s5_instance`, `s5_mixing`, `s5_profile`, `rigidity_s5x5_instance`, `s5x5_mixing`, `s5x5_pile`, `s5x5_profile`.
- `README.md` — build/serve instructions (serve over `http://`, the dep graph uses in-browser WASM graphviz).

## 8. Files

| File | Content |
|---|---|
| `pgg-smc/blueprint/src/web.tex`, `plastex.cfg`, `macros/*`, `content.tex` | blueprint source (eleven chapters, the diagram, ~70 nodes) |
| `pgg-smc/blueprint/make_blueprint.sh` | one-command build (HTML + dep graph + coqdoc) |
| `pgg-smc/blueprint/README.md` | build/serve doc |
| `pgg-smc/blueprint/web/` (gitignored) | generated site |

## 9. Out of scope

The naming rename (deferred to `docs/superpowers/plans/2026-06-13-pgg-naming-rename.md`); the `pgl_bound` accuracy rename (separate decision); any change to source `.v` files (the blueprint is read-only over the code, linking via coqdoc).
