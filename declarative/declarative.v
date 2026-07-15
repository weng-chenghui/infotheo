(******************************************************************************)
(** * Declarative Protocol Specification: Elm-Architecture for Verified FSMs  *)
(**                                                                           *)
(** STATUS: Design document with example Rocq code. Not yet compilable.       *)
(**                                                                           *)
(** RUNNING EXAMPLE: N-party DSDP protocol (Alice's role).                    *)
(** The ideas here are protocol-generic, but we use DSDP throughout to        *)
(** keep the discussion concrete and grounded in real verification needs.     *)
(**                                                                           *)
(******************************************************************************)
(**                                                                           *)
(** * The Problem: Three Levels of Protocol Description                       *)
(**                                                                           *)
(**   Level 1 — Imperative: "do this, then that"                              *)
(**     Example: palice_n in dsdp_pismc.v                                     *)
(**     \pi{ Init (#dk, &v0) ;                                                *)
(**          ForList relays ... as j cont k =>                                *)
(**            Recv<(j.+1)> c => Send<(dest j)> $(...) ; k                    *)
(**          end ;                                                            *)
(**          Recv<(n_relay.+1)> #dk g => Ret &(...) }                         *)
(**     (+) Readable, close to protocol paper pseudocode                      *)
(**     (-) No FSM — must build one manually for progress/trace proofs        *)
(**                                                                           *)
(**   Level 2 — Raw FSM: "state S1 transitions to S2"                         *)
(**     Example: dsdp_fsm.v (~2200 lines)                                     *)
(**     Record phase_state with concrete process lists, trace fragments,      *)
(**     9 transition constructors, 9 step-correctness lemmas (~1000 lines)    *)
(**     (+) Explicit state machine for downstream proofs                      *)
(**     (-) Tedious, repetitive, must stay in sync with Level 1               *)
(**                                                                           *)
(**   Level 3 — Declarative: "at phase j, it looks like this"                 *)
(**     THIS FILE: ~30 lines of declarations, framework derives the rest     *)
(**     (+) Concise, maintainable, single source of truth                     *)
(**     (-) Requires a framework (the "architecture")                         *)
(**                                                                           *)
(** The Chlipala POPL'22 approach automates Level 1 → Level 2 (write         *)
(** imperative code, tactic derives FSM). But we want to skip both and        *)
(** write directly at Level 3 — declaring WHAT each state looks like,         *)
(** not HOW to get there.                                                     *)
(**                                                                           *)
(******************************************************************************)
(**                                                                           *)
(** * The Elm Architecture Analogy                                            *)
(**                                                                           *)
(** In Elm (and React), you never write imperative DOM mutations:             *)
(**                                                                           *)
(**   -- Elm: declarative                                                     *)
(**   type alias Model = { count : Int }                                      *)
(**   view model = text (String.fromInt model.count)                          *)
(**   update Increment model = { model | count = model.count + 1 }            *)
(**                                                                           *)
(**   -- vs. imperative DOM manipulation (what Elm hides):                    *)
(**   document.getElementById("counter").textContent = "5"                    *)
(**                                                                           *)
(** The Elm runtime (the "architecture") handles reconciliation:              *)
(**   old_view = view(old_model)                                              *)
(**   new_view = view(new_model)                                              *)
(**   patches  = diff(old_view, new_view)   <-- framework does this          *)
(**   apply(patches, real_dom)              <-- framework does this          *)
(**                                                                           *)
(** You declare "what it looks like" as a pure function of state.             *)
(** The framework derives the transitions (patches) automatically.            *)
(**                                                                           *)
(** For protocol verification, the analogy is:                                *)
(**                                                                           *)
(**   Elm concept        | Protocol verification equivalent                   *)
(**   -------------------|-----------------------------------------------     *)
(**   Model              | phase : the current protocol phase                 *)
(**   View               | trace_fragment : what this phase appends to trace  *)
(**   Update             | next_phase : the transition graph                  *)
(**   DOM reconciliation | step correctness: one_step_procs matches           *)
(**   Elm runtime        | THE FRAMEWORK (tactic / typeclass / reflection)    *)
(**                                                                           *)
(** What the architecture hides (the "DOM reconciliation" equivalent):        *)
(**   1. Process-list construction (concrete seq (proc data) per state)       *)
(**   2. Step correctness (one_step_procs on state S1 produces state S2)     *)
(**   3. Trace accumulation (trace = concat of fragments along path)          *)
(**                                                                           *)
(** These are exactly the ~2000 lines of boilerplate in dsdp_fsm.v.          *)
(**                                                                           *)
(******************************************************************************)
(**                                                                           *)
(** * Design                                                                  *)
(**                                                                           *)
(** The user writes three things:                                             *)
(**   1. Phase — an inductive type naming the protocol phases                 *)
(**   2. View  — a function mapping each phase to its observable snapshot     *)
(**   3. Update — a function mapping each phase to its successor(s)          *)
(**                                                                           *)
(** The framework derives everything else.                                    *)
(**                                                                           *)
(******************************************************************************)

(** For now we assume standard infotheo imports would go here.
    The code below is illustrative — it uses infotheo/MathComp types
    but is not yet wired to actual imports. *)

Section DSDP_Declarative_Example.

(** We assume the standard DSDP parameters are in scope. *)
Variables (n_relay : nat).
Variables (AHE : Type).  (* placeholder for AHEncType *)
Variables (msgT encT randT priv_keyT : Type).
Variables (dk : priv_keyT) (v0 : msgT).
Variables (u : nat -> msgT) (r : nat -> msgT) (rand_a : nat -> randT).
Variables (ek : nat -> Type).  (* placeholder for pub_key map *)
Variable data : Type.

(** Placeholder constructors — in the real version these come from
    dsdp_interface.v (di_d, di_e, di_priv_key). *)
Variables (d : msgT -> data) (e : encT -> data) (priv_key : priv_keyT -> data).

(** Placeholder HE operations — in the real version from
    homomorphic_encryption.v (Epow, Emul, enc). *)
Variables (alice_enc : nat -> encT).
Variables (chain_acc : nat -> msgT).
Variable concrete_val : msgT.
Variable fresh_rand : randT.

(******************************************************************************)
(** * Part 1: Phase — name the states                                        *)
(******************************************************************************)

(** This is the ONLY inductive the user writes. It names the phases of the
    protocol and their parameters. Compare with dsdp_fsm.v which needs
    8 Definitions (st_init1, st_init2, st_recv, ...) each bundling a
    concrete process list — here we just name them. *)

Inductive phase : Type :=
  | PhInit1                        (* Alice stores her private key *)
  | PhInit2                        (* Alice stores her plaintext *)
  | PhLoop (j : nat)               (* recv/send iteration j *)
  | PhDrain (j : nat)              (* draining relay j *)
  | PhTail (rr : randT)            (* waiting for final accumulated value *)
  | PhRet                          (* Alice returns the dot product *)
  | PhDone.                        (* terminal *)

(******************************************************************************)
(** * Part 2: View — what each phase looks like                              *)
(******************************************************************************)

(** The "view" function maps each phase to its observable snapshot: the trace
    fragment that this phase appends to Alice's trace. This is a pure
    function of the phase — no interpreter, no process lists, no continuations.

    Compare with dsdp_fsm.v where each state is a Record bundling:
      ps_procs  : seq (proc data)        — concrete process list
      ps_frag   : seq data               — trace fragment
      ps_frag_ok : proof they agree       — correctness proof
    Here we only declare ps_frag. The framework derives ps_procs and
    ps_frag_ok. *)

Definition trace_fragment (p : phase) : list data :=
  match p with
  | PhInit1    => priv_key dk :: nil
  | PhInit2    => d v0 :: nil
  | PhLoop j   => e (alice_enc j) :: nil
  | PhDrain _  => nil
  | PhTail rr  => e (alice_enc n_relay) :: nil  (* placeholder *)
  | PhRet      => d concrete_val :: nil
  | PhDone     => nil
  end.

(******************************************************************************)
(** * Part 3: Update — the transition graph                                  *)
(******************************************************************************)

(** The "update" function defines the successor of each phase. This is the
    transition graph — the ONLY place where control flow is specified.
    Returns None for the terminal state.

    Compare with dsdp_fsm.v's phase_trans inductive (9 constructors, ~20
    lines) plus 9 step_ok_* lemmas (~1000 lines). Here we just write the
    graph as a function. *)

Definition next_phase (p : phase) : option phase :=
  match p with
  | PhInit1    => Some PhInit2
  | PhInit2    => Some (PhLoop 0)
  | PhLoop j   =>
      if Nat.ltb (j + 1) (n_relay + 1) then
        Some (PhLoop (j + 1))
      else
        Some (PhDrain 0)
  | PhDrain j  =>
      if Nat.ltb (j + 1) n_relay then
        Some (PhDrain (j + 1))
      else
        Some (PhTail fresh_rand)
  | PhTail _   => Some PhRet
  | PhRet      => Some PhDone
  | PhDone     => None
  end.

(******************************************************************************)
(** * That's it. The user is done. ~30 lines of declarations.                *)
(**                                                                           *)
(** Everything below would be DERIVED BY THE FRAMEWORK.                      *)
(******************************************************************************)


(******************************************************************************)
(** * Part 4: What the framework derives (currently manual, ~2200 lines)     *)
(******************************************************************************)

(** ** 4a. Transition path — the sequence of phases from init to done.       *)
(**                                                                           *)
(** Derived by iterating next_phase from PhInit1.                            *)

Fixpoint transition_path (fuel : nat) (p : phase) : list phase :=
  match fuel with
  | O => p :: nil
  | S fuel' =>
      match next_phase p with
      | None => p :: nil
      | Some p' => p :: transition_path fuel' p'
      end
  end.

(** The full path for a DSDP execution with n_relay relays:
    PhInit1 → PhInit2 → PhLoop 0 → ... → PhLoop n_relay
    → PhDrain 0 → ... → PhDrain (n_relay-1) → PhTail rr
    → PhRet → PhDone *)

Definition full_path : list phase :=
  transition_path (4 * n_relay + 10) PhInit1.

(** ** 4b. Full trace — concatenation of trace fragments along the path.    *)

Definition full_trace : list data :=
  List.concat (List.map trace_fragment full_path).

(** ** 4c. Termination — the path reaches PhDone.                            *)
(**                                                                           *)
(** The framework would prove: for sufficient fuel, the last element of      *)
(** transition_path is PhDone. This replaces phase_terminates in             *)
(** dsdp_fsm.v (~100 lines). *)

(** ** 4d. Step correctness — one_step_procs matches transitions.            *)
(**                                                                           *)
(** THIS IS THE KEY PART THE ARCHITECTURE HIDES.                             *)
(**                                                                           *)
(** The framework needs to connect the declarative phase/view/update to the  *)
(** concrete smc_interpreter. For each transition p → next_phase p, it      *)
(** must show:                                                               *)
(**   one_step_procs (render p) = render (next_phase p)                      *)
(** where render : phase → seq (proc data) is a derived function that        *)
(** builds the concrete process list for each phase.                         *)
(**                                                                           *)
(** Three possible implementation strategies for the framework:              *)
(**                                                                           *)
(** Strategy A — Reflection (compute, don't prove):                          *)
(**   Encode the interpreter as a computable function. Verify each           *)
(**   transition by native_compute. This is how React works — it doesn't    *)
(**   prove the diff is correct, it computes it.                             *)
(**   (+) No manual proofs at all                                            *)
(**   (-) Only works for concrete n_relay (not parametric)                   *)
(**   (-) native_compute can be slow for large states                        *)
(**                                                                           *)
(** Strategy B — Typeclass dispatch:                                         *)
(**   Each phase registers a PhaseSpec instance containing the render        *)
(**   function and step-correctness proof. A generic lemma dispatches.       *)
(**                                                                           *)
(**   Class PhaseSpec (p : phase) := {                                        *)
(**     ps_render   : seq (proc data);                                       *)
(**     ps_step_ok  : next_phase p = Some p' ->                              *)
(**                   one_step_procs ps_render = render p';                   *)
(**   }.                                                                      *)
(**                                                                           *)
(**   The user never sees PhaseSpec — the framework auto-generates           *)
(**   instances from the imperative program (Level 1).                       *)
(**   (+) Works parametrically                                               *)
(**   (-) Still needs one proof per transition (but auto-generated)          *)
(**                                                                           *)
(** Strategy C — Tactic automation (Ltac2):                                  *)
(**   A tactic that, given the imperative program + phase/view/update        *)
(**   declarations, unfolds the interpreter at each phase and solves the     *)
(**   step-correctness goals by simpl + congruence.                          *)
(**   (+) Parametric, no instances to maintain                               *)
(**   (-) Tactic engineering effort, fragile if interpreter changes          *)
(**                                                                           *)
(** Strategy D — Hybrid (recommended):                                       *)
(**   Use reflection (native_compute) for concrete instantiations            *)
(**   (3-party, 4-party, 5-party) to validate the declarations, then        *)
(**   use typeclass dispatch for the parametric n-party proof.               *)
(**   This mirrors how the project already works: native_compute for         *)
(**   duality checking, manual proofs for n-party generalization.            *)
(**                                                                           *)
(******************************************************************************)


(******************************************************************************)
(** * Part 5: What we gain                                                   *)
(******************************************************************************)

(** Summary of lines saved (estimated):                                      *)
(**                                                                           *)
(**   Component                  | dsdp_fsm.v | Declarative  | Saved         *)
(**   --------------------------|-----------|-------------|-------           *)
(**   State definitions          |    240    |    7 (phase)|  233           *)
(**   Process-list construction  |    200    |    0 (derived)| 200          *)
(**   Trace fragment proofs      |     60    |    0 (derived)|  60          *)
(**   Transition inductive       |     20    |   20 (update)|   0           *)
(**   Step-correctness lemmas    |   1000    |    0 (derived)|1000          *)
(**   Dispatcher                 |     10    |    0 (derived)|  10          *)
(**   Progress + termination     |    150    |    0 (derived)| 150          *)
(**   NOP/size/wf lemmas         |    180    |    0 (derived)| 180          *)
(**   Helpers (from progress.v)  |    500    |    ? (shared) | ~300         *)
(**   View function              |      0    |   15         |  -15         *)
(**   --------------------------|-----------|-------------|-------           *)
(**   TOTAL                      |   ~2360   |   ~42        | ~2118        *)
(**                                                                           *)
(** More importantly, the declarations are the SINGLE SOURCE OF TRUTH.       *)
(** When the protocol changes (e.g., adding a new phase), you modify         *)
(** phase + trace_fragment + next_phase (~3 lines each) and the framework   *)
(** re-derives everything. No risk of FSM drifting out of sync.             *)

(******************************************************************************)
(** * Part 6: Open questions                                                 *)
(******************************************************************************)

(** Q1. How does the framework connect declarations to the interpreter?      *)
(**     The "render" function (phase → seq (proc data)) is the bridge.      *)
(**     It must be derived from the imperative program (palice_n) or         *)
(**     declared separately. If declared separately, we lose the single     *)
(**     source of truth. If derived, we need Chlipala-style compilation.    *)
(**     A possible middle ground: derive render once (manually or via       *)
(**     Chlipala), then use it as a fixed bridge for all future proofs.     *)
(**                                                                           *)
(** Q2. Can we handle n-party parametricity?                                 *)
(**     The phase type uses nat indices, not 'I_n. The framework must       *)
(**     handle the case where n_relay is universally quantified.             *)
(**     Strategy D (hybrid) sidesteps this for validation but not for       *)
(**     the final theorem.                                                   *)
(**                                                                           *)
(** Q3. How do downstream proofs (security, entropy) interact?              *)
(**     Security proofs in dsdp_security.v reason about specific phases     *)
(**     (e.g., "at PhLoop j, the ciphertext has distribution X").           *)
(**     Named phases (PhLoop j) are much better than opaque states          *)
(**     (Chlipala's approach). This is a key advantage of the declarative  *)
(**     style over Chlipala.                                                 *)
(**                                                                           *)
(** Q4. Is there a general-purpose version of this architecture?            *)
(**     The phase/view/update pattern is not DSDP-specific. Any protocol   *)
(**     that runs on the smc_interpreter could use the same framework.     *)
(**     The framework would be parameterized by the effect signature        *)
(**     (like Elm is parameterized by the Msg type).                        *)
(**                                                                           *)
(** Q5. Related work and prior art:                                          *)
(**                                                                           *)
(** [Elm] Evan Czaplicki. "Elm: Concurrent FRP for Functional GUIs."         *)
(**   Senior thesis (A.B.), Harvard University, 2012.                        *)
(**   The Elm Architecture (Model-View-Update) is the direct inspiration    *)
(**   for our phase/view/update pattern. The architecture guide:             *)
(**   https://guide.elm-lang.org/architecture/                               *)
(**                                                                           *)
(** [React] Jordan Walke et al. React: A JavaScript library for building    *)
(**   user interfaces. Facebook, 2013.                                       *)
(**   https://react.dev/                                                     *)
(**   Declarative UI with virtual DOM diffing. The "reconciliation"          *)
(**   (old view vs new view → minimal patches) is analogous to our          *)
(**   step-correctness derivation. No academic paper; the canonical          *)
(**   reference is the documentation.                                        *)
(**                                                                           *)
(** [Verdi] James R. Wilcox, Doug Woos, Pavel Panchekha, Zachary Tatlock,   *)
(**   Xi Wang, Michael D. Ernst, and Thomas Anderson.                        *)
(**   "Verdi: A Framework for Implementing and Formally Verifying            *)
(**   Distributed Systems."                                                  *)
(**   PLDI 2015, pp. 357-368. DOI: 10.1145/2737924.2737958                  *)
(**   Net handlers have signature                                            *)
(**     name -> name -> msg -> data -> (list output * data * list (name*msg))*)
(**   i.e., (src, dst, message, state) -> (outputs, new_state, outgoing).   *)
(**   Structurally similar to Elm's update (state + event -> new state +     *)
(**   effects), though richer (includes routing info). The framework         *)
(**   provides verified network semantics (reordering, duplication,          *)
(**   partitions).                                                           *)
(**                                                                           *)
(** [DISEL] Ilya Sergey, James R. Wilcox, and Zachary Tatlock.              *)
(**   "Programming and Proving with Distributed Protocols."                  *)
(**   POPL 2018, Article 28, pp. 1-30. DOI: 10.1145/3158116                 *)
(**   Protocols as state-transition systems with per-state coherence         *)
(**   predicates. You declare what each state "looks like" (invariant),      *)
(**   and send/recv are shown to preserve coherence. Closest to our          *)
(**   declarative vision among verified distributed systems frameworks.      *)
(**                                                                           *)
(** [Kami] Joonwon Choi, Muralidaran Vijayaraghavan, Benjamin Sherman,      *)
(**   Adam Chlipala, and Arvind.                                             *)
(**   "Kami: A Platform for High-Level Parametric Hardware Specification     *)
(**   and Its Modular Verification."                                         *)
(**   ICFP 2017, Article 24, pp. 1-30. DOI: 10.1145/3110268                 *)
(**   Hardware DSL in Coq using guarded atomic actions — you declare         *)
(**   rules (state + guard -> next state), the framework handles             *)
(**   scheduling and modular composition. Demonstrates the typeclass-        *)
(**   dispatch pattern (Strategy B) at scale.                                *)
(**                                                                           *)
(** [Statecharts] David Harel.                                               *)
(**   "Statecharts: A Visual Formalism for Complex Systems."                 *)
(**   Science of Computer Programming, 8(3):231-274, 1987.                   *)
(**   DOI: 10.1016/0167-6423(87)90035-9                                      *)
(**   Declarative state machine formalism with hierarchy, concurrency,       *)
(**   and history. The original "declare states, not transitions" idea.      *)
(**   XState (https://xstate.js.org/) is a modern JS implementation.        *)
(**                                                                           *)
(** [IronFleet] Chris Hawblitzel, Jon Howell, Manos Kapritsos,              *)
(**   Jacob R. Lorch, Bryan Parno, Michael L. Roberts, Srinath Setty,       *)
(**   and Brian Zill.                                                        *)
(**   "IronFleet: Proving Practical Distributed Systems Correct."            *)
(**   SOSP 2015, pp. 1-17. DOI: 10.1145/2815400.2815428                     *)
(**   Separates protocol layer (declarative state machine) from              *)
(**   implementation layer, with a refinement proof connecting them.         *)
(**   The two-layer architecture is relevant: our "phase/view/update"        *)
(**   would be the protocol layer, the smc_interpreter the implementation.  *)
(**                                                                           *)
(** [ITrees] Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur,         *)
(**   Gregory Malecha, Benjamin C. Pierce, and Steve Zdancewic.              *)
(**   "Interaction Trees: Representing Recursive and Impure Programs         *)
(**   in Coq."                                                               *)
(**   POPL 2020, Article 51, pp. 1-32. DOI: 10.1145/3371119                 *)
(**   Coinductive, monadic representation of effectful computations.         *)
(**   Still imperative in flavor (bind/trigger), but the framework           *)
(**   handles event-loop boilerplate. A possible substrate for               *)
(**   implementing the "render" bridge (Q1).                                 *)
(**                                                                           *)
(** [Chlipala] Mirai Ikebuchi, Andres Erbsen, and Adam Chlipala.            *)
(**   "Certifying Derivation of State Machines from Coroutines."             *)
(**   POPL 2022. DOI: 10.1145/3498685                                        *)
(**   Code: github.com/mit-plv/                                              *)
(**         certifying-derivation-of-state-machines-from-coroutines           *)
(**   Automates Level 1 -> Level 2 (imperative program -> FSM) via a Coq    *)
(**   tactic. Complementary to our approach: we could use their tactic       *)
(**   to derive the "render" function (Q1), then layer our declarative      *)
(**   phase/view/update on top.                                              *)
(**                                                                           *)
(******************************************************************************)


(******************************************************************************)
(** * Part 7: Literature Gap and Synthesis                                   *)
(******************************************************************************)

(** None of the cited works fully implements our vision. The gap:            *)
(**                                                                           *)
(**   DISEL  has (1) declare what each state looks like                       *)
(**          lacks (2) auto-derive transitions + correctness                  *)
(**                                                                           *)
(**   Chlipala has (2) auto-derive FSM from program                          *)
(**            lacks (1) declarative input (takes imperative, not views)      *)
(**                                                                           *)
(**   Kami    has (3) modular typeclass dispatch for parametric proofs        *)
(**          lacks (1) and (2) — you still write each rule manually          *)
(**                                                                           *)
(**   Verdi  has Elm-shaped handlers (msg -> state -> state * output)         *)
(**          lacks auto-derivation — you write handlers imperatively          *)
(**                                                                           *)
(**   IronFleet has two-layer separation (protocol SM / implementation)      *)
(**             lacks auto-derivation — you write both layers manually        *)
(**                                                                           *)
(** Our vision combines (1) + (2) + (3) into a single architecture:          *)
(**   - Declare states + views (DISEL-style)                                 *)
(**   - Auto-derive transitions + correctness (Chlipala-style)               *)
(**   - Modular, parametric dispatch (Kami-style)                             *)
(**                                                                           *)
(** This combination does not exist in the literature as of 2026.            *)
(**                                                                           *)
(** Below we show concretely how each building block would contribute        *)
(** to proving Alice's DSDP program, using the phase/view/update             *)
(** declarations from Parts 1-3.                                             *)
(******************************************************************************)


(******************************************************************************)
(** * Part 8: Building Block A — DISEL-style per-state predicates            *)
(******************************************************************************)

(** In DISEL, each protocol state has a "coherence predicate" that           *)
(** describes what the distributed state looks like when the protocol        *)
(** is in that state. The predicate is a Prop over the state's local         *)
(** variables.                                                               *)
(**                                                                           *)
(** For Alice's DSDP, we adapt this as a per-phase coherence record that     *)
(** bundles EVERYTHING the framework needs to know about a phase — but      *)
(** the user only fills in the declarative parts (view + invariant).         *)
(** The framework fills in the rest (process list, step proof).              *)

(** ** What the user writes (DISEL-inspired):                                *)

Record phase_coherence (p : phase) := PhaseCoherence {
  (** Declarative: what trace fragment this phase produces *)
  pc_fragment : list data;

  (** Declarative: what Alice "holds" at this phase — an invariant
      over the accumulated computation so far.
      E.g., at PhLoop j, Alice holds the partial chain:
        chain_acc j = ∏_{i<j} (u_{i+1} * v_relay_i + r_i)
      At PhRet, Alice holds the final dot product. *)
  pc_invariant : Prop;
}.

(** For Alice, the user instantiates this per phase: *)

(** At PhLoop j, Alice has just received ciphertext c_j from relay j+1
    and sent the masked value. Her trace records the encryption she sent.
    Her invariant says the chain accumulation is correct up to j. *)
(*
Definition pc_loop (j : nat) : phase_coherence (PhLoop j) := {|
  pc_fragment  := e (alice_enc j) :: nil;
  pc_invariant := chain_acc j = fold_left (fun acc i =>
                    acc * (u (i+1) * v_relay i + r i)) (seq 0 j) 1;
|}.
*)

(** At PhTail rr, Alice is waiting for the final decrypted value.
    Her trace records the re-encrypted accumulated chain.
    Her invariant says the full chain is correct. *)
(*
Definition pc_tail (rr : randT) : phase_coherence (PhTail rr) := {|
  pc_fragment  := e (enc ek_alice (chain_acc n_relay) rr) :: nil;
  pc_invariant := chain_acc n_relay =
                    fold_left (fun acc i =>
                      acc * (u (i+1) * v_relay i + r i)) (seq 0 n_relay.+1) 1;
|}.
*)

(** At PhRet, Alice computes the final dot product.
    Her trace records the plaintext result.
    Her invariant is the DSDP correctness theorem. *)
(*
Definition pc_ret : phase_coherence PhRet := {|
  pc_fragment  := d concrete_val :: nil;
  pc_invariant := concrete_val =
                    chain_acc n_relay - \sum_(j < n_relay.+1) r j + u ord0 * v0;
|}.
*)

(** KEY INSIGHT FROM DISEL: the invariant is the specification.              *)
(** The user declares WHAT is true at each phase, not HOW to prove it.      *)
(** The framework's job is to show that transitions preserve invariants     *)
(** — i.e., pc_invariant (PhLoop j) -> pc_invariant (PhLoop j.+1).         *)
(** This is exactly "coherence preservation" from DISEL.                    *)


(******************************************************************************)
(** * Part 9: Building Block B — Chlipala-style auto-derivation              *)
(******************************************************************************)

(** Chlipala's derive tactic compiles a free-monad program into a step       *)
(** function + equivalence proof. We repurpose this machinery differently:  *)
(** instead of compiling the full program, we use it to derive the           *)
(** "render" function that bridges declarations to the interpreter.          *)
(**                                                                           *)
(** The render function maps each phase to its concrete process list:        *)
(**   render : phase -> seq (proc data)                                      *)
(**                                                                           *)
(** This is the function we currently build by hand (~200 lines of           *)
(** recv_procs, send_procs, drain_procs, etc. in dsdp_fsm.v).               *)

(** ** Step 1: Compile palice_n once using Chlipala's tactic.                *)
(**                                                                           *)
(** This gives us:                                                           *)
(**   alice_state : Set           (opaque state type)                        *)
(**   alice_step  : step_type    (transition function)                       *)
(**   alice_equiv : equiv ...    (simulation proof)                          *)

(** ** Step 2: Build a bijection between our named phases and alice_state.  *)
(**                                                                           *)
(** We define:                                                               *)
(**   phase_to_state : phase -> alice_state                                   *)
(**   state_to_phase : alice_state -> phase                                   *)
(**                                                                           *)
(** and prove they are inverses. This is a ONE-TIME cost (~50 lines).       *)
(** After this, we never touch alice_state again — we reason about          *)
(** named phases everywhere.                                                 *)

(** ** Step 3: Derive render via the bijection.                              *)
(**                                                                           *)
(*
Definition render (p : phase) : seq (proc data) :=
  state_procs (phase_to_state p).
*)
(**                                                                           *)
(** where state_procs extracts the process list from the Chlipala-derived   *)
(** state. This is automatic — no manual process-list construction.         *)

(** ** Step 4: Derive step correctness for free.                             *)
(**                                                                           *)
(** For each transition p -> next_phase p, the proof obligation is:          *)
(**   one_step_procs (render p) = render (next_phase p)                      *)
(**                                                                           *)
(** This follows from:                                                       *)
(**   (a) Chlipala's equiv proof: alice_step simulates palice_n             *)
(**   (b) The bijection: phase_to_state commutes with transitions           *)
(**                                                                           *)
(** In pseudo-proof:                                                         *)
(*
Lemma step_ok (p : phase) (p' : phase) :
  next_phase p = Some p' ->
  one_step_procs (render p) = render p'.
Proof.
  intro Hnext.
  (* Translate to Chlipala's state machine *)
  rewrite /render.
  have := alice_equiv.  (* Chlipala's simulation proof *)
  (* The step function on alice_state matches one_step_procs *)
  (* The bijection maps next_phase to alice_step *)
  (* QED — no per-transition case analysis needed *)
Qed.
*)
(**                                                                           *)
(** This replaces ~1000 lines of manual step_ok_* lemmas with ~20 lines    *)
(** of bijection + generic step_ok.                                          *)
(**                                                                           *)
(** COMPARISON with pure Chlipala approach (dsdp_chlipala.v):               *)
(**   Pure Chlipala: opaque states, hard to use downstream                   *)
(**   Our hybrid:    named phases (from Part 1) + auto-derived render       *)
(**                  Best of both worlds.                                    *)


(******************************************************************************)
(** * Part 10: Building Block C — Kami-style typeclass dispatch               *)
(******************************************************************************)

(** Kami uses Coq typeclasses for modular rule composition: each hardware    *)
(** module registers its rules, and the framework composes them.             *)
(** We adapt this for PARAMETRIC phase proofs.                               *)
(**                                                                           *)
(** The problem: PhLoop j exists for every j < n_relay.+1. We need          *)
(** a proof of step correctness for EACH j, but the proof structure is      *)
(** the same — only the index changes. A typeclass lets us state this       *)
(** once and dispatch automatically.                                         *)

(** ** The typeclass: one instance per phase family *)

Class PhaseWF (p : phase) := {
  (** The process list for this phase *)
  pw_render    : list data;  (* placeholder for seq (proc data) *)

  (** Size is preserved *)
  pw_size      : length pw_render = n_relay + 2;

  (** Trace fragment matches the declaration *)
  pw_fragment  : trace_fragment p = pw_render;  (* simplified *)

  (** Invariant holds *)
  pw_invariant : True;  (* placeholder for pc_invariant *)
}.

(** ** Parametric instance for the loop family *)
(**                                                                           *)
(** One instance covers ALL PhLoop j simultaneously.                         *)
(** The proof is by induction on j — stated once, not per-j.                *)

(*
Instance PhaseWF_loop (j : nat) (Hj : j < n_relay + 1) :
    PhaseWF (PhLoop j) := {|
  pw_render    := render (PhLoop j);      (* from Chlipala bridge *)
  pw_size      := render_size (PhLoop j); (* generic lemma *)
  pw_fragment  := render_fragment_loop j Hj;
  pw_invariant := chain_acc_correct j Hj; (* by induction on j *)
|}.
*)

(** ** Parametric instance for the drain family *)

(*
Instance PhaseWF_drain (j : nat) (Hj : j < n_relay) :
    PhaseWF (PhDrain j) := {|
  pw_render    := render (PhDrain j);
  pw_size      := render_size (PhDrain j);
  pw_fragment  := render_fragment_drain j Hj;
  pw_invariant := drain_invariant j Hj;
|}.
*)

(** ** Fixed instances for non-parametric phases *)

(*
Instance PhaseWF_init1 : PhaseWF PhInit1 := {| ... |}.
Instance PhaseWF_init2 : PhaseWF PhInit2 := {| ... |}.
Instance PhaseWF_ret   : PhaseWF PhRet   := {| ... |}.
Instance PhaseWF_done  : PhaseWF PhDone  := {| ... |}.
*)

(** ** The master theorem: dispatch by typeclass resolution *)
(**                                                                           *)
(** Given PhaseWF for all phases, the trace theorem is generic:              *)

(*
Theorem full_trace_correct `{forall p, PhaseWF p} :
  full_trace = expected_alice_trace.
Proof.
  unfold full_trace, full_path, transition_path.
  (* At each step, typeclass resolution finds the PhaseWF instance,
     which provides pw_fragment. Concatenation is automatic. *)
  induction (transition_path ...) as [| p ps IH].
  - reflexivity.
  - simpl. rewrite (pw_fragment (H := _)). (* typeclass resolves *)
    f_equal. exact IH.
Qed.
*)

(** ** Why this matters for n-party parametricity:                           *)
(**                                                                           *)
(** Without typeclasses, the n-party trace theorem requires a manual case   *)
(** split on all ~8 phase families, with separate proofs for each.           *)
(** With typeclasses:                                                        *)
(**   - PhaseWF_loop covers all j < n_relay.+1 in ONE instance              *)
(**   - PhaseWF_drain covers all j < n_relay in ONE instance                *)
(**   - The master theorem doesn't case-split at all — it dispatches        *)
(**     via typeclass resolution                                             *)
(**   - When n_relay changes (or becomes universally quantified),            *)
(**     NOTHING changes — the instances are already parametric              *)
(**                                                                           *)
(** This is INSPIRED BY Kami's parametric hardware modules, where each      *)
(** module is a Gallina function taking parameters and returning a Modules  *)
(** value. Kami itself does NOT use Coq typeclasses — it uses plain         *)
(** functions and inductive types. We propose typeclasses as an             *)
(** IMPROVEMENT over Kami's approach for parametric dispatch.               *)


(******************************************************************************)
(** * Part 11: Putting It All Together — Alice's Proof Pipeline              *)
(******************************************************************************)

(** The full pipeline for Alice's DSDP protocol:                             *)
(**                                                                           *)
(** LAYER 1 (user writes, ~50 lines total):                                  *)
(**   - phase inductive (Part 1, ~7 lines)                                   *)
(**   - trace_fragment function (Part 2, ~12 lines)                          *)
(**   - next_phase function (Part 3, ~15 lines)                              *)
(**   - per-phase invariants (Part 8, ~15 lines)                             *)
(**                                                                           *)
(** LAYER 2 (one-time bridge, ~70 lines):                                    *)
(**   - Compile palice_n via Chlipala (Part 9 Step 1, ~10 lines)            *)
(**   - Build bijection phase <-> alice_state (Part 9 Step 2, ~50 lines)    *)
(**   - Define render via bijection (Part 9 Step 3, ~10 lines)              *)
(**                                                                           *)
(** LAYER 3 (framework derives, ~30 lines of generic lemmas):               *)
(**   - step_ok : generic, via Chlipala equiv (Part 9 Step 4, ~20 lines)    *)
(**   - PhaseWF instances : one per phase family (Part 10, ~10 lines)        *)
(**   - full_trace_correct : generic, via typeclass dispatch (~5 lines)      *)
(**                                                                           *)
(** TOTAL: ~150 lines, vs ~2200 lines in the current approach.              *)
(**                                                                           *)
(** The savings come from:                                                   *)
(**   - No manual process-list construction (render is derived)              *)
(**   - No per-transition step proofs (step_ok is generic)                   *)
(**   - No per-j case splits (typeclass dispatch is parametric)              *)
(**   - No trace accumulation boilerplate (master theorem is generic)        *)
(**                                                                           *)
(** When the protocol changes:                                               *)
(**   - Add/remove a constructor in phase (~1 line)                          *)
(**   - Add/remove a case in trace_fragment (~1 line)                        *)
(**   - Add/remove a case in next_phase (~2 lines)                           *)
(**   - Add a PhaseWF instance if it's a new parametric family (~5 lines)   *)
(**   - The Chlipala bridge auto-updates (re-run derive)                     *)
(**   - All downstream proofs (step_ok, full_trace_correct) stay unchanged   *)
(**                                                                           *)
(******************************************************************************)


(******************************************************************************)
(** * Part 12: Kami as Underlying Infrastructure — Assessment                 *)
(******************************************************************************)

(** Kami [Choi et al., ICFP 2017] provides a Coq framework for modular       *)
(** hardware verification. The question: can Kami serve as the underlying     *)
(** infrastructure for our declarative protocol framework?                    *)
(**                                                                           *)
(** Answer: CONCEPTUALLY YES, PRACTICALLY NO.                                *)
(** Kami's proof architecture is exactly right. Its domain-specific layers   *)
(** (hardware actions, bit-level types) are not.                             *)
(**                                                                           *)
(** ** What fits perfectly: Kami's proof architecture                         *)
(**                                                                           *)
(**   Kami concept               | Our equivalent                             *)
(**   --------------------------|------------------------------------------  *)
(**   traceRefines m1 m2 :=     | step correctness:                          *)
(**     every trace of m1 is    |   interpreter trace = declared trace       *)
(**     a trace of m2           |   (same trace-inclusion structure)         *)
(**                             |                                            *)
(**   ConcatMod m1 ++ m2 :=    | LAYER 1 ONLY (interpreter bridge):         *)
(**     parallel composition    |   party composition when connecting        *)
(**     with hidden internal    |   to smc_interpreter. Not used in the     *)
(**     method calls            |   core phase-oriented layer (Layer 0).    *)
(**                             |                                            *)
(**   Decomposition theorems := | LAYER 1 ONLY (interpreter bridge):         *)
(**     prove refinement of     |   prove interpreter correctness from      *)
(**     composed module from    |   per-party step proofs. Not used in     *)
(**     refinement of parts     |   the core phase-oriented layer.          *)
(**                             |                                            *)
(**   Behavior m s sig :=       | protocol behavior:                         *)
(**     trace = list of labels  |   trace = list of data fragments           *)
(**     from Multistep          |   from transition_path                     *)
(**     (list LabelT)           |   (list (list data))                       *)
(**                                                                           *)
(** The trace-inclusion refinement + decomposition pattern is EXACTLY what   *)
(** we need for "framework derives step correctness from declarations."      *)
(**                                                                           *)
(** ** Kami's core types (from github.com/mit-plv/kami)                      *)
(**                                                                           *)
(**   (* Module = registers + rules + methods *)                              *)
(**   Inductive Modules : Type :=                                             *)
(**   | Mod (regs : list RegInitT)                                            *)
(**         (rules : list (Attribute (Action Void)))                          *)
(**         (dms : list DefMethT) : Modules                                   *)
(**   | ConcatMod (m1 m2 : Modules) : Modules.                               *)
(**                                                                           *)
(**   (* Trace-inclusion refinement *)                                        *)
(**   Definition traceRefines p m1 m2 :=                                      *)
(**     forall s1 sig1, Behavior m1 s1 sig1 ->                                *)
(**       exists s2 sig2, Behavior m2 s2 sig2 /\                              *)
(**                       equivalentLabelSeq p sig1 sig2.                     *)
(**                                                                           *)
(**   (* Action = free monad over hardware primitives (10 constructors) *)    *)
(**   Inductive ActionT (lretT : Kind) : Type :=                              *)
(**   | MCall (meth : string) s :                                             *)
(**       Expr (arg s) -> (ty (ret s) -> ActionT lretT) -> ActionT lretT     *)
(**   | Let_ : Expr k -> (fullType k -> ActionT lretT) -> ActionT lretT     *)
(**   | ReadNondet : forall k, (fullType k -> ActionT lretT) -> ActionT ..  *)
(**   | ReadReg (r : string) : forall k,                                      *)
(**       (fullType k -> ActionT lretT) -> ActionT lretT                     *)
(**   | WriteReg (r : string) k :                                             *)
(**       Expr k -> ActionT lretT -> ActionT lretT                           *)
(**   | IfElse : Expr Bool -> ActionT k -> ActionT k ->                      *)
(**       (ty k -> ActionT lretT) -> ActionT lretT                           *)
(**   | Assert_ : Expr Bool -> ActionT lretT -> ActionT lretT               *)
(**   | Display : ... -> ActionT lretT -> ActionT lretT                     *)
(**   | Return : Expr lretT -> ActionT lretT.                                 *)
(**   (* Shown selectively; see Kami/Syntax.v for the full definition *)     *)
(**                                                                           *)
(** ** What does NOT fit: Kami's domain-specific layers                       *)
(**                                                                           *)
(**   Kami layer         | Problem for protocols                              *)
(**   -------------------|-----------------------------------------------    *)
(**   Kind system:       | Hardware-only: Bool, Bit n, Vector, Struct,       *)
(**   Bool, Bit n,       | Array. We need: finGroupType, zmodType,          *)
(**   Vector, Struct,    | AHEncType, 'Z_(p*q), ordinals, MathComp         *)
(**   Array               | algebraic types. Fundamentally incompatible.    *)
(**                      |                                                    *)
(**   State model:       | Flat string-keyed register map (RegsT).          *)
(**   RegsT = M.t (sigT  | We need: per-party structured state with        *)
(**   fullType)           | process lists, channel buffers, continuations.  *)
(**                      | Our state is tree-structured, not flat.           *)
(**                      |                                                    *)
(**   Communication:     | Synchronous MCall (atomic request-response).     *)
(**   MCall meth arg k   | We need: asynchronous message-passing with      *)
(**                      | buffered channels, non-blocking send/recv.       *)
(**                      | This is the BIGGEST gap.                         *)
(**                      |                                                    *)
(**   Dependencies:      | No MathComp. Uses Coq stdlib + own Lib/.        *)
(**                      | We need MathComp 2.x + infotheo + HB.           *)
(**                      | Targets Coq 8.12 (we use Rocq 9.0).             *)
(**                                                                           *)
(** ** Verdict: reimplement, don't reuse                                     *)
(**                                                                           *)
(** The right approach is to BUILD A NEW FRAMEWORK ("Kami for protocols")    *)
(** that reimplements Kami's proof architecture with our own domain layers:  *)
(**                                                                           *)
(**   Kami original          | Kami-for-protocols replacement                 *)
(**   ----------------------|--------------------------------------------   *)
(**   ActionT over           | ActionT over piSMC effects:                   *)
(**   MCall/ReadReg/WriteReg |   Send/Recv/Compute/Init/Ret                 *)
(**                          |                                               *)
(**   Kind = Bit n |         | Kind = MathComp types:                        *)
(**   Vector | Struct        |   finGroupType | zmodType | AHEncType |      *)
(**                          |   ordinal | seq | ffun                        *)
(**                          |                                               *)
(**   RegsT = string -> val  | PhaseState = global phase record:             *)
(**                          |   { ps_phase; ps_trace; ps_invariant }       *)
(**                          |                                               *)
(**   MCall (synchronous)    | Channel send/recv (asynchronous):            *)
(**                          |   Send ch msg | Recv ch (fun msg => ...)     *)
(**                          |                                               *)
(**   Modules = regs +       | Protocol = phase declarations +              *)
(**   rules + methods        |   views + transitions + invariants           *)
(**                          |                                               *)
(**   traceRefines           | traceRefines (REUSE AS-IS)                    *)
(**   (trace inclusion)      | Same definition, different label type        *)
(**                          |                                               *)
(**   Decomposition          | Decomposition (REUSE PROOF STRUCTURE)         *)
(**   theorems               | Same proof pattern, but used in the          *)
(**                          | INTERPRETER BRIDGE layer (Layer 1) only      *)
(**                          |                                               *)
(**   ConcatMod m1 ++ m2    | Party composition (INTERPRETER BRIDGE only)  *)
(**   (parallel + hiding)    | Same hiding semantics for channels.          *)
(**                          | Not needed in the core declarative layer.    *)
(**                                                                           *)
(** The conceptual debt to Kami is significant — their trace-inclusion       *)
(** refinement and simulation proof patterns are exactly right. But code     *)
(** reuse would be minimal because ActionT, Kind, and RegsT all need full  *)
(** replacement. Kami's parallel composition (ConcatMod) and decomposition  *)
(** theorems are party-oriented; in our framework these belong only to the  *)
(** optional interpreter bridge (Layer 1), not the core declarative layer.  *)
(**                                                                           *)
(** ** Concrete sketch: phase-oriented protocol specification               *)
(**                                                                           *)
(** The DSDP protocol as a declarative ProtoSpec (not per-party modules):   *)
(*
(* A protocol specification = phase + view + update + invariant *)
Record ProtoSpec := {
  ps_phase    : Type;                     (* the phase type *)
  ps_init     : ps_phase;                 (* initial phase *)
  ps_terminal : ps_phase -> bool;         (* is this phase terminal? *)
  ps_next     : ps_phase -> option ps_phase;  (* transition graph *)
  ps_fragment : ps_phase -> list data;    (* trace fragment per phase *)
  ps_invariant: ps_phase -> Prop;         (* what holds at each phase *)
}.

(* DSDP instantiation — the ENTIRE protocol spec *)
Definition dsdp_spec : ProtoSpec := {|
  ps_phase     := phase;                  (* from Part 1 *)
  ps_init      := PhInit1;
  ps_terminal  := fun p => match p with PhDone => true | _ => false end;
  ps_next      := next_phase;             (* from Part 3 *)
  ps_fragment  := trace_fragment;         (* from Part 2 *)
  ps_invariant := fun p =>                (* from Part 8 *)
    match p with
    | PhLoop j   => chain_acc_correct j
    | PhRet      => dot_product_correct
    | _          => True
    end;
|}.

(* The framework derives from ProtoSpec alone: *)

(* 1. Full trace = concatenation of fragments along the path *)
Theorem spec_trace (S : ProtoSpec) (fuel : nat) :
  full_trace S fuel = concat (map (ps_fragment S) (path S fuel)).

(* 2. Progress = non-terminal phases have a successor *)
Theorem spec_progress (S : ProtoSpec) (p : ps_phase S) :
  ps_terminal S p = false -> exists p', ps_next S p = Some p'.

(* 3. Termination = bounded fuel reaches terminal *)
Theorem spec_terminates (S : ProtoSpec) :
  exists fuel, ps_terminal S (iterate_next S fuel) = true.

(* 4. Invariant preservation = transition preserves invariants *)
Theorem spec_invariant_preserved (S : ProtoSpec) (p p' : ps_phase S) :
  ps_next S p = Some p' ->
  ps_invariant S p -> ps_invariant S p'.

(* All four theorems are GENERIC over any ProtoSpec.
   The user instantiates ProtoSpec (~30 lines for DSDP),
   the framework provides all four theorems. *)
*)
(**                                                                           *)
(** This sketch shows how Kami's proof ideas map to our phase-oriented core: *)
(**   - ProtoSpec replaces Modules (global phases, not per-party modules)    *)
(**   - ps_next replaces Rules (transition graph, not guarded actions)       *)
(**   - ps_fragment / ps_invariant are the declarative "view" (Parts 2, 8)  *)
(**   - traceRefines is reused: spec_trace proves the declared trace        *)
(**     matches the actual trace                                             *)
(**   - Kami's simulation pattern is reused: spec_invariant_preserved has    *)
(**     exactly the shape of Kami's forward simulation step                  *)
(**   - Kami's ConcatMod / decomposition are NOT used in this core layer —  *)
(**     they belong to the optional interpreter bridge (Layer 1) where      *)
(**     party-oriented reasoning is needed to connect to smc_interpreter    *)
(**                                                                           *)

(******************************************************************************)
(** * Part 13: What Kami Gives Us — Layer-by-Layer Assessment                *)
(******************************************************************************)

(** If we extend Kami's proof architecture for protocol verification,         *)
(** here is what each layer provides, what we build on top, and the          *)
(** estimated effort.                                                        *)
(**                                                                           *)
(**   Layer              | Kami provides             | We build on top        *)
(**                      | (reimplement for          |                        *)
(**                      | protocols)                |                        *)
(**   -------------------|---------------------------|----------------------  *)
(**   Trace semantics    | Behavior m s sig :=       | Replace LabelT         *)
(**                      | execution = list of       | (method calls/defs)    *)
(**                      | labels from Multistep.    | with protocol labels   *)
(**                      | Well-defined,             | (send/recv data on     *)
(**                      | compositional.            | channels).             *)
(**                      |                           | Definition is 1:1.     *)
(**                      |                           | Effort: LOW            *)
(**   -------------------|---------------------------|----------------------  *)
(**   Refinement         | traceRefines p m1 m2 :=   | Use directly:          *)
(**                      | every trace of impl is a  | traceRefines           *)
(**                      | trace of spec. This IS    | dsdp_interpreter       *)
(**                      | the correctness theorem   | dsdp_spec =            *)
(**                      | shape we need.            | "interpreter trace     *)
(**                      |                           | matches declared       *)
(**                      |                           | trace."                *)
(**                      |                           | Effort: VERY LOW       *)
(**   -------------------|---------------------------|----------------------  *)
(**   Parallel           | ConcatMod m1 ++ m2 :=    | INTERPRETER BRIDGE     *)
(**   composition        | merges modules, internal  | ONLY (Layer 1).        *)
(**                      | calls hidden from         | Alice ++ Relay_1 ++    *)
(**                      | observable trace.         | ... ++ Relay_n.        *)
(**                      |                           | Not needed in the core *)
(**                      |                           | phase-oriented layer.  *)
(**                      |                           | Effort: LOW            *)
(**                      |                           | (only if bridge needed)*)
(**   -------------------|---------------------------|----------------------  *)
(**   Decomposition      | Prove traceRefines        | INTERPRETER BRIDGE     *)
(**   theorems           | (m1 ++ m2) spec from      | ONLY (Layer 1).        *)
(**                      | per-component refinement. | Used to connect        *)
(**                      | Three variants:           | per-party process      *)
(**                      | Zero / One / Drop.        | lists to global phase  *)
(**                      |                           | declarations. Not      *)
(**                      |                           | needed in the core     *)
(**                      |                           | declarative layer.     *)
(**                      |                           | Effort: MEDIUM         *)
(**                      |                           | (only if bridge needed)*)
(**   -------------------|---------------------------|----------------------  *)
(**   Step semantics     | Step m o u l :=           | One interpreter step:  *)
(**                      | one atomic step: pick a   | pick the ready         *)
(**                      | rule, evaluate guard,     | process, execute one   *)
(**                      | execute action, produce   | send/recv, update      *)
(**                      | label. Deterministic      | channel buffers,       *)
(**                      | per-rule.                 | produce trace          *)
(**                      |                           | fragment.              *)
(**                      |                           | Effort: MEDIUM         *)
(**                      |                           | (new Step relation)    *)
(**   -------------------|---------------------------|----------------------  *)
(**   Module structure   | Mod regs rules dms :=     | ProtoMod phases view   *)
(**                      | flat list of registers +  | update inv :=          *)
(**                      | rules + methods.          | our declarative        *)
(**                      |                           | structure (Parts 1-3,  *)
(**                      |                           | 8). Shape changes but  *)
(**                      |                           | role is the same.      *)
(**                      |                           | Effort: MEDIUM         *)
(**                      |                           | (new record type)      *)
(**   -------------------|---------------------------|----------------------  *)
(**   Wellformedness     | WfMod :=                  | WfProto :=             *)
(**                      | no duplicate register/    | phase coverage (every  *)
(**                      | method names, type        | phase has a view),     *)
(**                      | consistency.              | channel compatibility  *)
(**                      |                           | (sends match recvs     *)
(**                      |                           | across parties),       *)
(**                      |                           | termination (path      *)
(**                      |                           | reaches Done).         *)
(**                      |                           | Effort: MEDIUM         *)
(**                      |                           | (new wellformedness)   *)
(**   -------------------|---------------------------|----------------------  *)
(**   Inlining / hiding  | inlineF :=                | Channel hiding: after  *)
(**                      | inlines method calls      | composing parties,     *)
(**                      | between submodules,       | all send/recv on       *)
(**                      | making them internal.     | internal channels are  *)
(**                      | wellHidden checks all     | hidden from observable *)
(**                      | internal calls resolved.  | trace. Only the "view" *)
(**                      |                           | (trace fragments)      *)
(**                      |                           | remain visible.        *)
(**                      |                           | Effort: LOW-MEDIUM     *)
(**   -------------------|---------------------------|----------------------  *)
(**   Simulation         | simulationZero,           | Per-phase step         *)
(**                      | simulation :=             | correctness: if        *)
(**                      | prove refinement via      | invariant holds at     *)
(**                      | forward simulation        | phase p and interp     *)
(**                      | relation. Reduces trace   | steps, then invariant  *)
(**                      | inclusion to per-step     | holds at next_phase p. *)
(**                      | invariant preservation.   | = DISEL's coherence    *)
(**                      |                           | preservation, with     *)
(**                      |                           | Kami's proof structure. *)
(**                      |                           | Effort: LOW            *)
(**                      |                           | (reuse proof pattern)  *)
(**   -------------------|---------------------------|----------------------  *)
(**   Notation / DSL     | Deep embedding: ActionT   | Deep embedding for     *)
(**                      | with PHOAS for variable   | protocol actions:      *)
(**                      | binding, Expr for         | Send ch expr,          *)
(**                      | expressions. Rich         | Recv ch (fun x => ...) *)
(**                      | notation for hardware     | Compute f, Init, Ret.  *)
(**                      | (LETN, ReadN, WriteN,     | Lighter than Kami      *)
(**                      | CallN).                   | (no bit-level ops).    *)
(**                      |                           | Effort: MEDIUM         *)
(**   -------------------|---------------------------|----------------------  *)
(**   Extraction         | Extracts to Bluespec /    | Not needed — we stay   *)
(**                      | Verilog via ppMod.        | in Rocq. Could extract *)
(**                      |                           | to executable protocol *)
(**                      |                           | simulators if desired. *)
(**                      |                           | Effort: N/A            *)
(**                                                                           *)
(** ** Summary                                                               *)
(**                                                                           *)
(**   5 layers are nearly free (trace, refinement, composition, hiding,      *)
(**     simulation pattern).                                                  *)
(**   4 layers need medium rework (step, module, wellformedness, notation).  *)
(**   1 layer is not needed (extraction).                                    *)
(**                                                                           *)
(** ** The structural win beyond boilerplate savings                          *)
(**                                                                           *)
(**   The key insight from Kami is not decomposition (which is party-         *)
(**   oriented and belongs to the interpreter bridge), but SIMULATION:       *)
(**   reduce trace inclusion to per-step invariant preservation.             *)
(**                                                                           *)
(**   Today (dsdp_progress.v, dsdp_fsm.v), we prove step correctness by    *)
(**   manually unfolding the interpreter at each of 9 transition types,     *)
(**   producing ~1000 lines of per-transition proofs.                        *)
(**                                                                           *)
(**   With Kami's simulation pattern, we would:                              *)
(**   1. Define a SIMULATION RELATION between global phases and              *)
(**      interpreter states (this is the "render" bijection from Part 9)    *)
(**   2. Prove ONE generic lemma: if the simulation relation holds at       *)
(**      phase p, and the interpreter steps, then it holds at                *)
(**      next_phase p                                                        *)
(**   3. The full trace theorem follows by induction on the phase path      *)
(**                                                                           *)
(**   The simulation relation is the bridge between the phase-oriented      *)
(**   core (Layer 0) and the interpreter (Layer 1). Everything above the    *)
(**   bridge — trace characterization, progress, termination, security,     *)
(**   entropy — works purely in terms of phases, never touching the         *)
(**   interpreter directly.                                                  *)
(**                                                                           *)
(******************************************************************************)


(******************************************************************************)
(** * Part 14: The Elm Architecture, Done Right                              *)
(******************************************************************************)

(** Parts 1-13 proposed a phase-oriented core. But the earlier discussion   *)
(** of "components + channels" (React-style local state machines composed   *)
(** by a scheduler) was WRONG. It overcomplicated things by treating        *)
(** parties as independent state machines that need synchronization.         *)
(**                                                                           *)
(** Both Elm and React use the same architecture: ONE global state store,   *)
(** ONE update function, events trigger transitions. Elm is just more       *)
(** principled about it. Let's follow Elm properly.                         *)
(**                                                                           *)
(** ** The Elm Architecture (correctly stated)                               *)
(**                                                                           *)
(**   State = { phase; trace; ... }        -- ONE global store              *)
(**   Event = MsgFrom j c | Computed v | ... -- what happened               *)
(**   update : Event -> State -> State     -- ONE pure function             *)
(**                                                                           *)
(**   The update function IS the protocol. Each event triggers exactly      *)
(**   one state transition. The trace is a FIELD in the state that gets     *)
(**   appended to at each transition. Not "interleaved from per-party       *)
(**   traces" — directly accumulated.                                       *)
(**                                                                           *)
(** ** Synchronization is just state transitions                             *)
(**                                                                           *)
(**   "Alice waits for relay j" is NOT blocking or channel synchronization. *)
(**   It is simply: relay j sends → MsgFrom event arrives → update fires   *)
(**   → state moves to next phase. Like pressing button 1 enables           *)
(**   button 2:                                                              *)
(**                                                                           *)
(**     State { phase = PhLoop 0 }                                           *)
(**       -- event: MsgFrom relay_0 ciphertext_0                             *)
(**     State { phase = PhLoop 1, trace = ... ++ [enc_0] }                   *)
(**       -- event: MsgFrom relay_1 ciphertext_1                             *)
(**     State { phase = PhLoop 2, trace = ... ++ [enc_0; enc_1] }            *)
(**       -- ...                                                             *)
(**       -- event: MsgFrom relay_n final_value                              *)
(**     State { phase = PhRet, trace = ... ++ [result] }                     *)
(**                                                                           *)
(**   Each event is like an Elm Msg. The update function pattern-matches    *)
(**   on (current phase, event) and produces the new state. No scheduler,  *)
(**   no channel resolution, no blocking — just a sequence of              *)
(**   event-triggered transitions.                                           *)
(**                                                                           *)
(** ** Components are VIEWS of the global state, not independent machines  *)
(**                                                                           *)
(**   In Elm/React, a "component" is a VIEW function that reads a slice    *)
(**   of the global state. It does NOT have its own state machine.          *)
(**                                                                           *)
(**   For DSDP:                                                              *)
(**   - Alice's "component" = a view that reads phase + trace              *)
(**   - Relay j's "component" = a view that reads phase (to know if it's   *)
(**     relay j's turn) + the relevant ciphertext                           *)
(**                                                                           *)
(**   There is ONE state, ONE update. Components are just lenses into it.  *)
(**   When we design Alice's behavior, we only look at the cases where     *)
(**   the event is relevant to Alice. When we design relay j's behavior,   *)
(**   we only look at the cases where the event is relevant to relay j.    *)
(**   But they all live in the SAME update function.                         *)
(**                                                                           *)
(** ** What this means for the framework                                    *)
(**                                                                           *)
(** The Elm-faithful model is simpler than both the "global phase"          *)
(** approach (Part 1-3) and the "components + channels" approach:           *)

(*
(* The FULL protocol state — one global store *)
Record protocol_state := {
  ps_phase : phase;
  ps_trace : list data;      (* accumulated — appended at each transition *)
  ps_acc   : msgT;           (* accumulated algebraic value *)
}.

(* Events — what triggers transitions *)
Inductive event :=
  | EvInit                           (* protocol starts *)
  | EvMsgFrom (src : nat) (c : encT) (* message arrives from party src *)
  | EvDecrypt (g : msgT)             (* decrypted value available *)
  | EvCompute (v : msgT).            (* local computation result *)

(* THE update function — one pure function, the whole protocol *)
Definition update (ev : event) (st : protocol_state) : protocol_state :=
  match ps_phase st, ev with
  | PhInit1, EvInit =>
      {| ps_phase := PhInit2;
         ps_trace := ps_trace st ++ [priv_key dk];
         ps_acc   := ps_acc st |}
  | PhInit2, EvInit =>
      {| ps_phase := PhLoop 0;
         ps_trace := ps_trace st ++ [d v0];
         ps_acc   := ps_acc st |}
  | PhLoop j, EvMsgFrom src c =>
      (* Alice receives ciphertext from relay j+1, sends masked value *)
      let enc_val := c ^h (u (j+1)) *h enc_pub_key (j+1) (r j) (rand_a j) in
      let next := if j + 1 <? n_relay + 1 then PhLoop (j + 1)
                  else PhDrain 0 in
      {| ps_phase := next;
         ps_trace := ps_trace st ++ [e enc_val];
         ps_acc   := ps_acc st |}
  | PhDrain j, EvMsgFrom src c =>
      (* Relay j forwards — no trace for Alice *)
      let next := if j + 1 <? n_relay then PhDrain (j + 1)
                  else PhTail fresh_rand in
      {| ps_phase := next;
         ps_trace := ps_trace st;
         ps_acc   := ps_acc st |}
  | PhTail rr, EvDecrypt g =>
      {| ps_phase := PhRet;
         ps_trace := ps_trace st ++ [e (alice_enc n_relay)];
         ps_acc   := g |}
  | PhRet, EvCompute v =>
      {| ps_phase := PhDone;
         ps_trace := ps_trace st ++ [d v];
         ps_acc   := v |}
  | _, _ =>
      st  (* no-op: event not relevant in this phase *)
  end.
*)

(** ** How this simplifies the framework                                    *)
(**                                                                           *)
(** With this model, the framework needs to provide:                         *)
(**                                                                           *)
(**   1. Given the update function, derive the PHASE SEQUENCE                *)
(**      (the sequence of events that drives the protocol to completion)     *)
(**                                                                           *)
(**   2. Given the phase sequence, the TRACE is directly read from          *)
(**      ps_trace of the final state — no concatenation, no interleaving,  *)
(**      it's already accumulated in the state.                              *)
(**                                                                           *)
(**   3. PROGRESS: for each non-Done phase, there exists an event that      *)
(**      moves the state forward. (Like: in this phase, the relevant        *)
(**      message WILL arrive because the protocol is well-formed.)          *)
(**                                                                           *)
(**   4. INVARIANT PRESERVATION: the update function preserves the          *)
(**      algebraic invariant (ps_acc tracks the correct accumulated value)  *)
(**                                                                           *)
(** ** Comparison: three iterations of the design                            *)
(**                                                                           *)
(**   Iteration 1 (Parts 1-3):                                               *)
(**     phase + trace_fragment + next_phase                                   *)
(**     Trace = concat of fragments. Simple but fragments are "detached"    *)
(**     from the state — the state doesn't accumulate them.                  *)
(**                                                                           *)
(**   Iteration 2 (discarded "components + channels"):                       *)
(**     Per-party components with local state machines, composed by a       *)
(**     scheduler that resolves channel dependencies.                        *)
(**     Overcomplicated. Neither Elm nor React works this way.              *)
(**                                                                           *)
(**   Iteration 3 (this Part, Elm-faithful):                                 *)
(**     ONE global state with trace as accumulated field.                    *)
(**     ONE update function triggered by events.                            *)
(**     Components = views (lenses) into the global state.                  *)
(**     No scheduler, no channels, no interleaving.                         *)
(**     The trace is ALREADY in the state when you reach PhDone.            *)
(**                                                                           *)
(** ** The layered architecture (revised)                                    *)
(**                                                                           *)
(**   LAYER 0 — Core (Elm Architecture, self-contained):                    *)
(**     protocol_state + event + update                                      *)
(**     → trace theorem : ps_trace of final state = expected trace          *)
(**     → progress      : non-Done phases have a valid next event           *)
(**     → termination   : bounded events reach PhDone                       *)
(**     → invariants    : update preserves algebraic correctness            *)
(**     NO interpreter, NO per-party reasoning, NO process lists.           *)
(**                                                                           *)
(**   LAYER 1 — Interpreter bridge (optional):                              *)
(**     render : phase → seq (proc data)                                    *)
(**     step_ok : interpreter step matches update for each event            *)
(**     Kami's simulation pattern lives HERE.                                *)
(**     Only needed to connect the Elm-style spec to smc_interpreter.       *)
(**                                                                           *)
(**   LAYER 2 — Downstream (consumes Layer 0 directly):                     *)
(**     security  : distributions of ps_trace at each phase                 *)
(**     entropy   : entropy of trace values                                  *)
(**     These NEVER touch the interpreter. They reason about update          *)
(**     and protocol_state directly.                                         *)
(**                                                                           *)
(** Layer 2 proofs (security, entropy) do not depend on Layer 1              *)
(** (interpreter bridge) at all. Security analysis works purely from the    *)
(** Elm-style spec, without ever mentioning process lists or the            *)
(** interpreter. The bridge is only needed for computational soundness:     *)
(** "the real execution matches the spec."                                   *)
(**                                                                           *)

(******************************************************************************)
(** * Part 15: How TEA Connects to Kami — And Where Kami Is Overkill         *)
(******************************************************************************)

(** ** The connection: TEA update branches ≈ Kami rules                      *)
(**                                                                           *)
(** A Kami rule is a guarded atomic action:                                   *)
(**   guard(state) → action(state) → new_state + observable_label           *)
(**                                                                           *)
(** One case of TEA's update function:                                       *)
(**   | (PhLoop j, EvMsgFrom src c) => { new_phase; new_trace; ... }        *)
(**                                                                           *)
(** Each (phase, event) branch CORRESPONDS TO a Kami rule whose guard       *)
(** checks phase = P /\ event = E. The encoding works because the guards   *)
(** are mutually exclusive (the phase is unique), so at most one rule is    *)
(** enabled at any time. This encodes determinism into Kami's               *)
(** nondeterministic framework.                                              *)
(**                                                                           *)
(** IMPORTANT: these are NOT identical. The differences:                      *)
(**   - Kami scheduling is INTERNAL: the module chooses which enabled rule   *)
(**     fires. TEA events come from OUTSIDE: the environment provides them. *)
(**     The correct Kami analog of an external event is a METHOD CALL        *)
(**     (externally invoked), not a scheduling choice (internally resolved). *)
(**   - Kami rules are nondeterministic (any enabled rule can fire).         *)
(**     TEA's update is deterministic (given state + event, the next state  *)
(**     is fully determined).                                                *)
(**   - Kami's ActionT is a free monad with side effects (register reads/   *)
(**     writes, method calls). TEA's update is a pure function.             *)
(**                                                                           *)
(** ** The precise mapping (corrected)                                       *)
(**                                                                           *)
(**   TEA                     | Kami                   | Role                 *)
(**   ------------------------|------------------------|--------------------  *)
(**   protocol_state          | RegsT (register map)   | Mutable state        *)
(**   event                   | External method call   | What triggers a step *)
(**                           | (NOT scheduling choice)|                      *)
(**   One branch of update    | One Rule with mutually | A single transition  *)
(**                           | exclusive guard        |                      *)
(**   ps_trace field appended | LabelT emitted         | Observable behavior  *)
(**   update (pure function)  | Module (nondeterministic| The spec            *)
(**                           | but encoded as determ.)|                      *)
(**   smc_interpreter         | Impl module            | The implementation   *)
(**   trace equality          | traceRefines           | Correctness          *)
(**   invariant preservation  | Forward simulation     | Proof method         *)
(**                                                                           *)
(** ** Trace inclusion degenerates to trace equality                          *)
(**                                                                           *)
(** Kami's traceRefines m1 m2 means: every trace of m1 is a trace of m2.    *)
(** This handles nondeterministic specs (which allow more behaviors than     *)
(** the implementation).                                                     *)
(**                                                                           *)
(** But our TEA spec is DETERMINISTIC: one global state, one update          *)
(** function, events in a fixed sequence. It produces exactly ONE trace.    *)
(** Similarly, the smc_interpreter is deterministic.                         *)
(**                                                                           *)
(** So trace inclusion from a deterministic implementation to a              *)
(** deterministic spec degenerates to trace EQUALITY. Kami's full            *)
(** nondeterministic trace-inclusion machinery is not exercised.             *)
(**                                                                           *)
(** ** Where Kami IS valuable: proof patterns we borrow                       *)
(**                                                                           *)
(** Kami contributes three things to our framework, as PROOF PATTERNS        *)
(** we borrow:                                                               *)
(**                                                                           *)
(** 1. TRACE SEMANTICS: Kami's Behavior/Multistep gives a rigorous           *)
(**    definition of "the trace of a module." We borrow this to define      *)
(**    "the trace of a protocol execution" — but our definition is          *)
(**    simpler (deterministic, so just iterate update).                      *)
(**                                                                           *)
(** 2. FORWARD SIMULATION: Kami's simulation reduces whole-trace             *)
(**    refinement to per-step invariant preservation. Since both sides      *)
(**    are deterministic, the simulation relation simplifies to a            *)
(**    function (the render function), and the proof obligation is a        *)
(**    COMMUTING DIAGRAM:                                                    *)
(**                                                                           *)
(*
(*    The commuting diagram:

         update ev
     p -----------> next_phase p
     |                   |
     | render             | render
     |                   |
     v                   v
     procs ---------> procs'
       one_step_procs

     Proof obligation: render (next_phase p) = one_step_procs (render p)
*)
*)
(**                                                                           *)
(**    This is exactly the step_ok lemma from Part 9, understood as a       *)
(**    degenerate case of Kami's relational simulation.                      *)
(**                                                                           *)
(**    HOWEVER: this commuting diagram is NOT trivial to prove. The         *)
(**    current dsdp_progress.v demonstrates why. The dsdp_inv invariant    *)
(**    (the simulation relation) describes what EVERY process in the        *)
(**    concrete process list holds at each phase:                            *)
(**                                                                           *)
(**      Inv_AR(j): Alice holds Send(j, alice_enc(j), continuation);       *)
(**                 relay j is at Recv; relays < j are at Finish;           *)
(**                 the frontier pair (j-2, j-1) is mid-handoff;           *)
(**                 relays > j are at initial relay_body state.             *)
(**                                                                           *)
(**    Each constructor of dsdp_inv pins down the nth element of the        *)
(**    process list for ALL n_relay+2 parties simultaneously, with          *)
(**    concrete algebraic values (alice_enc, chain_acc, term) baked in.     *)
(**                                                                           *)
(**    The step proof (dsdp_inv_step_*) then requires:                      *)
(**      1. Firing the matched Send/Recv pair (step_send_recv_match)        *)
(**      2. Computing the relay's output via HE homomorphism                *)
(**      3. Showing the new process list satisfies the next Inv             *)
(**                                                                           *)
(**    This is ~1000 lines of proof in dsdp_progress.v. The simulation     *)
(**    IS necessary — without it, you cannot know what the concrete        *)
(**    process list looks like after k steps, because each relay's          *)
(**    continuation depends on the algebraic value it received.             *)
(**                                                                           *)
(**    The TEA update function declares WHAT the protocol does at each      *)
(**    phase. The simulation proves that the interpreter ACTUALLY DOES IT.  *)
(**    These are different claims, and the gap between them is real work.   *)
(**                                                                           *)
(** 3. DECOMPOSITION (multi-party only): Kami's decomposition theorems      *)
(**    let you prove refinement of composed modules from parts. This is     *)
(**    only useful if we ever need to connect a multi-party composition     *)
(**    to the interpreter (Layer 1). For the core TEA layer (Layer 0),     *)
(**    decomposition is not needed.                                          *)
(**                                                                           *)
(** ** What the framework can and cannot automate                            *)
(**                                                                           *)
(** The TEA layer (Layer 0) gives us trace, progress, termination, and     *)
(** invariant theorems for FREE — these follow by structural induction     *)
(** on the update function with no domain knowledge.                        *)
(**                                                                           *)
(** The interpreter bridge (Layer 1) CANNOT be fully automated because:    *)
(**                                                                           *)
(**   - The concrete process list is a deeply nested data structure.        *)
(**     Each relay holds a continuation closure capturing values from       *)
(**     previous steps. The nth element depends on algebraic identities    *)
(**     (HE homomorphism: Epow + Emul laws).                               *)
(**                                                                           *)
(**   - The simulation invariant (dsdp_inv) is domain-specific: it         *)
(**     describes the "frontier" — the boundary between finished relays,   *)
(**     the active relay pair, and pending relays. This frontier sweeps     *)
(**     left-to-right as the protocol progresses. This structure is not    *)
(**     derivable from the TEA spec alone; it requires understanding the   *)
(**     relay chain topology.                                               *)
(**                                                                           *)
(**   - Each step proof requires symbolic evaluation: fire Send/Recv,      *)
(**     apply Emul_local, verify the new process list matches the next     *)
(**     Inv constructor. This is where the ~1000 lines live.               *)
(**                                                                           *)
(** What the framework CAN do is STRUCTURE this work:                       *)
(**   - The TEA spec defines the expected behavior (what SHOULD happen)    *)
(**   - The simulation relation (dsdp_inv) is the bridge                   *)
(**   - The proof obligation per step is clear: show the commuting         *)
(**     diagram holds                                                       *)
(**   - The framework provides the scaffolding; the user provides the      *)
(**     domain-specific algebraic reasoning                                  *)
(**                                                                           *)
(** This is analogous to Kami: Kami doesn't prove your hardware correct    *)
(** for free — it STRUCTURES the proof into per-rule obligations that     *)
(** the user discharges. Our framework does the same for protocols.        *)
(**                                                                           *)
(** ** Where Kami's specific machinery is more than needed                   *)
(**                                                                           *)
(** While simulation IS necessary, some of Kami's specific machinery is    *)
(** more than our deterministic protocol requires:                          *)
(**                                                                           *)
(**   - Nondeterministic rule scheduling: we never have multiple enabled    *)
(**     rules. Mutual exclusivity is an encoding artifact.                  *)
(**   - Label types (LabelT with defs/calls/annot): we just need           *)
(**     "list data" for the trace.                                          *)
(**   - Wellformedness (WfMod): checks for duplicate register names,       *)
(**     type consistency. Not relevant for our phase-oriented spec.        *)
(**                                                                           *)
(** ** The right tool for each layer                                         *)
(**                                                                           *)
(**   Layer 0 (core TEA spec):                                               *)
(**     PLAIN COQ. ProtoSpec record + induction on transition path.          *)
(**     No framework needed. spec_trace, spec_progress, spec_terminates,    *)
(**     spec_invariant_preserved are all provable by straightforward         *)
(**     induction on the event sequence.                                     *)
(**                                                                           *)
(**   Layer 1 (interpreter bridge):                                          *)
(**     SIMULATION IS REQUIRED. The render function maps phases to          *)
(**     concrete process lists. The simulation invariant (like dsdp_inv)    *)
(**     describes the full multi-party state at each phase. The proof       *)
(**     obligation per step is the commuting diagram. This is real work     *)
(**     (~1000 lines for DSDP) that requires domain-specific algebraic     *)
(**     reasoning. The framework structures it but cannot eliminate it.     *)
(**                                                                           *)
(**     What the framework DOES save:                                       *)
(**     - Process-list construction (~200 lines): derived from render       *)
(**     - Trace fragment proofs (~60 lines): follow from TEA spec          *)
(**     - Progress/termination (~250 lines): follow from TEA Layer 0       *)
(**     - NOP/size/wf lemmas (~180 lines): can be generic                  *)
(**     What remains:                                                       *)
(**     - Step-correctness proofs (~1000 lines): domain-specific,          *)
(**       cannot be eliminated, but better structured                       *)
(**                                                                           *)
(**   Layer 1+ (multi-party composition, if ever needed):                    *)
(**     KAMI-STYLE DECOMPOSITION. This is the one place where Kami's        *)
(**     full machinery genuinely helps.                                     *)
(**                                                                           *)
(** ** Summary: Kami's role, correctly scoped                                *)
(**                                                                           *)
(**   Kami provides PROOF PATTERNS that we borrow and adapt:                *)
(**     - Trace semantics → simplified to deterministic iteration           *)
(**     - Forward simulation → simplified to functional commuting diagram, *)
(**       but the per-step proofs are still substantial (~1000 lines)       *)
(**       because they require domain-specific algebraic reasoning          *)
(**     - Decomposition → deferred to optional multi-party layer           *)
(**                                                                           *)
(**   The core TEA layer (Layer 0) needs only plain Coq with MathComp.     *)
(**   The interpreter bridge (Layer 1) needs simulation — this is real     *)
(**   work that no framework can eliminate, but the TEA spec + simulation   *)
(**   pattern STRUCTURES it better than the current monolithic approach.    *)
(**   Kami's value is in the proof architecture (simulation + decomposition *)
(**   patterns), not as a code dependency.                                   *)
(**                                                                           *)

(******************************************************************************)
(** * Part 16: Open Question — What Automates Per-Step Proofs?               *)
(******************************************************************************)

(** The framework has three layers of automation:                             *)
(**                                                                           *)
(**   TEA (front-end DSL):                                                   *)
(**     User declares: phase, event, update, view.                           *)
(**     Gives: WHAT the protocol does — the spec.                            *)
(**     Automates: trace, progress, termination (Layer 0, by induction).    *)
(**                                                                           *)
(**   Kami patterns (proof structure):                                        *)
(**     User defines: simulation relation R (like dsdp_inv).                *)
(**     Gives: HOW to connect spec to interpreter.                           *)
(**     Automates: LIFTING per-step proofs to whole-trace refinement         *)
(**     (by the simulation theorem — essentially induction packaged         *)
(**     with the right invariant).                                           *)
(**                                                                           *)
(**   ??? (per-step automation):                                              *)
(**     The ~1000 lines of step-correctness proofs in dsdp_progress.v.      *)
(**     Each dsdp_inv_step_* lemma fires a Send/Recv pair, applies HE       *)
(**     homomorphism, and verifies the new process list matches the next    *)
(**     invariant constructor. This is the HARD part.                        *)
(**     WHAT AUTOMATES THIS?                                                 *)
(**                                                                           *)
(** The first two layers are understood. The third is the open question.     *)
(**                                                                           *)
(** ** The per-step proof, concretely                                        *)
(**                                                                           *)
(** Each step proof in dsdp_progress.v does:                                *)
(**   1. Look at the current invariant (e.g., Inv_AR j)                     *)
(**   2. Identify the matched Send/Recv pair in the process list            *)
(**   3. Fire step_send_recv_match — the interpreter executes the pair     *)
(**   4. The relay computes: Emul_local(received_cipher, enc(...))          *)
(**   5. Apply HE homomorphism laws (Epow_scalarM, Emul_addM) to show     *)
(**      the result equals the expected algebraic value                      *)
(**   6. Show the new process list satisfies the next invariant             *)
(**      (e.g., Inv_AS0 or Inv_ASj(j+1))                                   *)
(**                                                                           *)
(** Steps 1-3 are mechanical. Steps 4-6 require algebraic reasoning.        *)
(**                                                                           *)
(** ** Candidate approaches for automating step 4-6                          *)
(**                                                                           *)
(**   Approach A — Computational reflection (native_compute):               *)
(**     For CONCRETE n (3-party, 4-party, 5-party), just evaluate.          *)
(**     native_compute can verify each step by brute-force computation.     *)
(**     This is how duality checking already works (channels_dual by        *)
(**     native_compute in dsdp_pismc.v).                                    *)
(**     (+) Zero proof effort for concrete instances                         *)
(**     (-) Does NOT work for parametric n — the step function has a        *)
(**         universally quantified relay index                               *)
(**                                                                           *)
(**   Approach B — Tactic engineering (Ltac2):                               *)
(**     Write a tactic that: unfolds the process list, identifies the       *)
(**     Send/Recv pair, fires step_send_recv_match, applies HE lemmas,     *)
(**     and checks the result.                                               *)
(**     (+) Works for parametric n if the tactic is general enough          *)
(**     (-) Fragile: breaks when the interpreter or HE interface changes    *)
(**     (-) Essentially encodes the 1000 lines as tactic code — moves     *)
(**         complexity rather than eliminating it                            *)
(**                                                                           *)
(**   Approach C — Certified decision procedure:                             *)
(**     If the step proof obligation is decidable (which it may be, since   *)
(**     it reduces to algebraic identities over AHE), build a verified     *)
(**     checker in Coq that decides each step.                               *)
(**     (+) Fully automatic, works for parametric n                         *)
(**     (-) Heavy upfront investment to build and verify the checker        *)
(**     (-) Ties the framework to a specific algebraic theory               *)
(**                                                                           *)
(**   Approach D — TEA spec as proof oracle:                                *)
(**     The update function is COMPUTABLE. Given the current phase and      *)
(**     event, it tells you exactly what the next phase, trace fragment,    *)
(**     and algebraic value should be. Use this as a guide:                  *)
(**                                                                           *)
(**       1. Evaluate update(ev, current_state) → expected next state       *)
(**       2. Evaluate one_step_procs(render(phase)) → actual next procs    *)
(**       3. Show render(expected.phase) = actual next procs                *)
(**                                                                           *)
(**     The TEA spec NARROWS the proof: instead of discovering what the     *)
(**     next state should be (which dsdp_progress.v does from scratch       *)
(**     each time by unfolding the interpreter), you already KNOW the       *)
(**     answer from the spec. You just need to verify it matches.           *)
(**     (+) Reduces proof search to proof checking                          *)
(**     (-) Still need domain-specific algebraic verification (step 3)     *)
(**                                                                           *)
(**   Approach E — Hybrid (D + A):                                           *)
(**     Use the TEA spec as oracle (D) to generate proof obligations,      *)
(**     then discharge them by native_compute for concrete n (A).           *)
(**     For parametric n, the oracle-generated obligations are              *)
(**     UNIFORM — they all have the form:                                    *)
(**       enc(ek(j+1), u(j)*v(j) + r(j), rand(j))                          *)
(**       = Epow(enc(ek(j+1), v(j), r1(j)), u(j))                          *)
(**         * enc(ek(j+1), r(j), rand_a(j))                                 *)
(**     which is one application of the HE homomorphism.                    *)
(**     A single parametric lemma covers all j.                              *)
(**     (+) Concrete: fully automatic. Parametric: one lemma per            *)
(**         algebraic pattern, not one per transition.                       *)
(**     (-) Must identify and factor out the algebraic patterns             *)
(**                                                                           *)
(** ** The irreducible kernel                                                *)
(**                                                                           *)
(** No matter what approach, the following cannot be automated away:         *)
(**                                                                           *)
(**   For parametric n, someone must prove that the HE homomorphism         *)
(**   holds generically:                                                     *)
(**     Epow(enc(ek, v, r1), u) * enc(ek, r, rand)                         *)
(**       = enc(ek, u * v + r, ...)                                          *)
(**                                                                           *)
(**   This is one lemma (~20 lines), already proved as alice_enc_value     *)
(**   in dsdp_progress.v. It is the algebraic CORE of the protocol —       *)
(**   the reason DSDP computes a dot product.                                *)
(**                                                                           *)
(**   Everything else (firing Send/Recv, tracking the frontier, updating   *)
(**   the process list) is MECHANICAL consequence of this algebraic fact.   *)
(**   The question is whether a framework can reduce the ~1000 lines of    *)
(**   mechanical consequence to a small number of algebraic lemmas plus    *)
(**   automated scaffolding.                                                 *)
(**                                                                           *)
(** ** Summary: the three-layer automation picture                           *)
(**                                                                           *)
(**   Layer     | What         | Automated by       | Lines saved            *)
(**   ----------|--------------|--------------------|-----------             *)
(**   Layer 0   | Trace,       | TEA + plain Coq    | ~700 (progress,        *)
(**   (spec)    | progress,    | induction           | termination, trace,   *)
(**             | termination  |                     | NOP/size/wf)          *)
(**   ----------|--------------|--------------------|-----------             *)
(**   Layer 1   | Whole-trace  | Simulation theorem | ~10 (lifting)          *)
(**   (lifting) | refinement   | (Kami pattern)      |                       *)
(**   ----------|--------------|--------------------|-----------             *)
(**   Layer 1   | Per-step     | OPEN QUESTION       | ~1000 target          *)
(**   (steps)   | correctness  | Best candidate:     | Approach E could     *)
(**             |              | Hybrid (E) = TEA    | reduce to ~50 lines  *)
(**             |              | oracle + reflection | of algebraic lemmas  *)
(**             |              | + parametric lemmas |                       *)
(**   ----------|--------------|--------------------|-----------             *)
(**                                                                           *)
(**   If Approach E works, the total framework reduces DSDP verification    *)
(**   from ~2200 lines to ~80 lines (30 TEA spec + 50 algebraic core),     *)
(**   with the framework providing everything in between.                    *)
(**   This is the research question.                                         *)
(**                                                                           *)
(** ** What Kami automated in its original domain — and why we can't copy   *)
(**                                                                           *)
(** In hardware, Kami provides kinv_magic — a tactic pipeline that          *)
(** discharges per-rule simulation obligations automatically:               *)
(**   kinv_action_dest : destructure PHOAS actions into hypotheses          *)
(**   kregmap_red      : symbolically simplify register map lookups         *)
(**   kinv_constr      : apply constructors to build proof witnesses        *)
(**   kinv_eq          : solve map equality via reification (meqReify)      *)
(**   kinv_finish      : case-split on decidable equalities (weq, string_dec)*)
(**                                                                           *)
(** This works because hardware has three properties that protocols lack:   *)
(**                                                                           *)
(**   Property               | Hardware          | Protocols               *)
(**   -----------------------|-------------------|------------------------*)
(**   Equality decidability  | All types have    | Groups/rings: equality *)
(**                          | decidable eq      | is NOT decidable.      *)
(**                          | (weq for Bit n,   | Cannot auto-split      *)
(**                          | string_dec for    | "if g^x == g^y".       *)
(**                          | names). Tactics   |                        *)
(**                          | case-split freely.|                        *)
(**   -----------------------|-------------------|------------------------*)
(**   No induction within    | Each rule = one   | Protocol steps involve *)
(**   a step                 | clock cycle, no   | algebraic operations   *)
(**                          | loops. Per-step   | (HE homomorphism)      *)
(**                          | proofs = pure     | requiring algebraic    *)
(**                          | case analysis +   | lemmas, not just       *)
(**                          | equational rewrite| case analysis.         *)
(**   -----------------------|-------------------|------------------------*)
(**   Finite register state  | State = finite    | Process lists have     *)
(**                          | map, tactics can  | continuations capturing*)
(**                          | enumerate all     | symbolic algebraic     *)
(**                          | accesses.         | values — can't        *)
(**                          |                   | enumerate.             *)
(**                                                                           *)
(** kinv_magic solves hardware per-step goals because they are              *)
(** DECIDABLE CASE ANALYSIS over finite types. Our per-step goals are      *)
(** ALGEBRAIC IDENTITIES over infinite types — fundamentally harder.       *)
(**                                                                           *)
(** What transfers from Kami:                                                *)
(**   - Structural tactics (kmodular, kinline, kdecompose): domain-agnostic,*)
(**     handle module composition plumbing. These WOULD transfer.           *)
(**   - Simulation theorem (per-step → whole-trace): just induction,       *)
(**     domain-agnostic. WOULD transfer.                                    *)
(**   - kinv_eq (map equality via reification): PARTIALLY transfers for    *)
(**     process-list indexing goals, but not algebraic goals.               *)
(**                                                                           *)
(** What does NOT transfer:                                                  *)
(**   - kinv_finish (decidable case-splitting): our types lack decidable   *)
(**     equality in the algebraic domain.                                   *)
(**   - kinv_magic as a whole: the pipeline assumes per-step goals are     *)
(**     solvable by case analysis + rewriting. Ours require algebraic      *)
(**     reasoning (Epow_scalarM, Emul_addM).                               *)
(**                                                                           *)
(** The gap, precisely stated:                                               *)
(**   Kami:     per-step goal = decidable case analysis                      *)
(**            → kinv_magic solves it automatically                         *)
(**   Us:      per-step goal = algebraic identity (HE homomorphism)         *)
(**            → needs domain-specific lemmas (alice_enc_value etc.)        *)
(**                                                                           *)
(** This confirms that the right approach for protocols is NOT to copy     *)
(** kinv_magic, but to factor out the algebraic core (Approach E):          *)
(**   - The MECHANICAL parts (fire Send/Recv, update process list,          *)
(**     track frontier) CAN be automated by tactics or reflection           *)
(**   - The ALGEBRAIC parts (Epow + Emul = enc of dot product term)        *)
(**     CANNOT be automated — they are the irreducible domain-specific     *)
(**     kernel, already proved as alice_enc_value (~20 lines)              *)
(**   - The framework's job is to reduce ~1000 lines to: automated         *)
(**     mechanical scaffolding + a few algebraic lemmas                     *)
(**                                                                           *)
(** Proof effort comparison (Kami FIFO case study):                          *)
(**   ~180 lines spec → ~650 lines proof (3.6:1 ratio)                    *)
(**   Most effort on word-arithmetic lemmas (wminus_def, wplus_assoc)      *)
(**   Even Kami cannot fully automate bitvector arithmetic —               *)
(**   the 3.6:1 ratio is AFTER kinv_magic does its work.                   *)
(**   Our ratio target: ~30 lines TEA spec → ~80 lines proof (2.7:1)     *)
(**   — achievable IF the mechanical scaffolding is automated.             *)
(**                                                                           *)

(******************************************************************************)
(** * Part 17: Audit Corrections — What the DSL Actually Provides            *)
(******************************************************************************)

(** Parts 15-16 framed the DSL's value as "exposing decidability to enable  *)
(** automation." An audit revealed this framing is misleading. Here are     *)
(** the corrections and the sharpened understanding.                         *)
(**                                                                           *)
(** ** Correction 1: "decidable" is the wrong word                           *)
(**                                                                           *)
(** The DSDP protocol has DATA-OBLIVIOUS CONTROL FLOW: given phase index   *)
(** j, the next phase is computable without inspecting message contents.    *)
(** In palice_n (dsdp_pismc.v:296-311), the received ciphertext c is used  *)
(** as a VALUE input to the homomorphic computation (c ^h u *h enc(...)),   *)
(** but it does NOT determine control flow — Alice always sends to          *)
(** alice_send_dest(j) and continues with the next iteration regardless    *)
(** of what c contains.                                                     *)
(**                                                                           *)
(** "Decidable" in the formal sense means "given a phase, can we decide    *)
(** whether it has a successor?" — trivially true for any finitely-        *)
(** branching function. Not a distinguishing property. The correct term     *)
(** is data-oblivious or statically determined control flow.               *)
(**                                                                           *)
(** ** Correction 2: "entanglement" is the wrong diagnosis                   *)
(**                                                                           *)
(** The dsdp_inv constructors in dsdp_progress.v ALREADY structure          *)
(** control (constructor name Inv_AR/Inv_ASj/etc. + index j) separately    *)
(** from data (hypothesis fields specifying nth ps i = ...). The problem   *)
(** is not entanglement — it is LOW-LEVEL VERBOSITY. Each constructor      *)
(** carries 7-9 hypotheses specifying concrete process positions, many     *)
(** of which are boilerplate (size, wf, relay_at_body for future indices). *)
(** The representation is low-level (describing proc data terms), not      *)
(** conceptually confused.                                                   *)
(**                                                                           *)
(** ** Correction 3: TEA does not separate guards from actions               *)
(**                                                                           *)
(** In Kami, guards are boolean predicates evaluated at runtime to           *)
(** determine whether a rule fires; actions are register operations.        *)
(** In TEA, next_phase is a static total function — there are no guards.  *)
(** The TEA pattern is a simple FINITE AUTOMATON, not a guarded-action     *)
(** system. What TEA actually separates is STATE NAMING (the phase type)   *)
(** from STATE RENDERING (process lists). This is valuable but different   *)
(** from the Kami guard/action separation.                                  *)
(**                                                                           *)
(** ** Correction 4: alice_enc_value is not the only algebraic lemma        *)
(**                                                                           *)
(** The step proofs also need:                                               *)
(**   - Chain accumulation identity: Emul_local(alice_enc j, enc(ek,       *)
(**     chain_acc(j-1), rr)) = enc(ek, chain_acc(j), rr') — used at      *)
(**     every Inv_ASj and Inv_drain step                                    *)
(**   - dec_correct: decryption recovers the plaintext — used at           *)
(**     Inv_tail_to_ret                                                     *)
(**   - key_relay lookups: mapping relay indices to public keys            *)
(**                                                                           *)
(** The algebraic core is a small FAMILY of lemmas (3-5), not one lemma.  *)
(** All are parametric in j. The ~50 lines estimate for algebraic core    *)
(** in Part 16 is still reasonable but should say "family of lemmas"       *)
(** not "one lemma."                                                        *)
(**                                                                           *)
(** ** Correction 5: "expose decidability" is near-tautological             *)
(**                                                                           *)
(** The DSDP control flow is a simple linear chain with one loop — ANY    *)
(** representation exposes this. The real question is whether the DSL      *)
(** enables automation of STEP CORRECTNESS proofs (showing                  *)
(** one_step_procs(render(p)) = render(next_phase(p))), which are the     *)
(** 1000-line bulk. These proofs are about process-list manipulation       *)
(** (nth, set_nth, step_send_recv_match), not phase matching.              *)
(**                                                                           *)
(** ** What the DSL ACTUALLY provides (revised)                              *)
(**                                                                           *)
(** The DSL's value is NOT "exposing decidability." It is:                  *)
(**                                                                           *)
(** 1. ELIMINATING PROCESS-LIST BOILERPLATE (~1200 lines):                  *)
(**    The user never writes concrete seq (proc data) values, process-list *)
(**    construction functions, or size/wf preservation lemmas. These are   *)
(**    either derived from the TEA spec (via the render bridge) or made    *)
(**    unnecessary by reasoning at the phase level directly.               *)
(**                                                                           *)
(** 2. SINGLE SOURCE OF TRUTH:                                              *)
(**    When the protocol changes, the user modifies phase + update + view  *)
(**    (~3 lines each). No risk of the FSM drifting out of sync with the  *)
(**    imperative program, because the FSM is not a separate artifact —   *)
(**    it IS the spec.                                                      *)
(**                                                                           *)
(** 3. NAMED PHASES FOR DOWNSTREAM PROOFS:                                  *)
(**    Security and entropy proofs case-split on PhLoop j, PhTail, etc.   *)
(**    — meaningful names that correspond to protocol phases. Not opaque   *)
(**    process lists or auto-generated nested sum types. This is the       *)
(**    advantage over both the current approach (process lists) and         *)
(**    Chlipala (opaque states).                                            *)
(**                                                                           *)
(** 4. FACTORING THE PROOF OBLIGATION:                                      *)
(**    The TEA spec makes the step-correctness obligation EXPLICIT and     *)
(**    UNIFORM: for each phase p, show render(next_phase(p)) =            *)
(**    one_step_procs(render(p)). The user knows exactly what to prove.   *)
(**    In the current approach, the proof obligation is implicit — you    *)
(**    discover it by unfolding the interpreter, which is why each step   *)
(**    lemma is 100+ lines of "what IS the next state?"                   *)
(**                                                                           *)
(**    The TEA oracle (Approach D from Part 16) leverages this: you       *)
(**    already KNOW the answer, you just verify it. This reduces proof    *)
(**    SEARCH to proof CHECKING — not the same as full automation, but   *)
(**    a significant reduction in effort.                                   *)
(**                                                                           *)
(** ** The revised picture                                                   *)
(**                                                                           *)
(**   What the DSL gives:                                                    *)
(**     - Boilerplate elimination    (saves ~1200 lines)                    *)
(**     - Single source of truth     (prevents drift)                       *)
(**     - Named phases               (better downstream proofs)            *)
(**     - Explicit proof obligations  (search → checking)                  *)
(**                                                                           *)
(**   What the DSL does NOT give:                                            *)
(**     - Automatic step-correctness proofs (still ~1000 lines, but        *)
(**       better structured as uniform render-commuting-diagram             *)
(**       obligations, and narrowed by the TEA oracle)                      *)
(**     - Algebraic reasoning (3-5 HE lemmas, ~50 lines, irreducible)     *)
(**                                                                           *)
(**   The open research question (from Part 16) remains: can the ~1000    *)
(**   lines of step-correctness proofs be reduced further, e.g., by        *)
(**   Approach E (TEA oracle + native_compute for concrete n + parametric  *)
(**   algebraic lemmas for generic n)? The DSL makes this reduction        *)
(**   POSSIBLE by providing the oracle; whether it achieves it depends    *)
(**   on the framework engineering.                                         *)
(**                                                                           *)

(******************************************************************************)
(** * Part 18: Why Kami Automates and We Don't — The Real Answer             *)
(******************************************************************************)

(** Both Kami's parametric hardware and our parametric protocols have        *)
(** data-oblivious control flow and deterministic steps. Both are            *)
(** parametric (Kami: number of cores; us: n_relay). Yet Kami automates     *)
(** per-step proofs with kinv_magic. Why can't we?                          *)
(**                                                                           *)
(** ** The two-layer structure (same in both domains)                        *)
(**                                                                           *)
(**   Structural layer: "which slot was updated? does the index match?"     *)
(**     → automatable by rewriting + case splitting                         *)
(**   Domain layer:     "does the value satisfy the spec?"                   *)
(**     → domain-specific lemmas                                            *)
(**                                                                           *)
(** In Kami (hardware):                                                      *)
(**   Structural: map operations (reg_map[name] := val, lookup)             *)
(**   Automated by: kinv_magic (rewriting + reification)                    *)
(**   Domain residual: bitvector arithmetic (~650 lines for FIFO)           *)
(**                                                                           *)
(** In our protocols:                                                        *)
(**   Structural: process-list operations (nth, set_nth, step matching)     *)
(**   Automated by: NOTHING — no equivalent of kinv_magic exists            *)
(**   Domain residual: HE algebra (~50 lines of lemmas)                     *)
(**                                                                           *)
(** The difference is NOT that our problem is harder. It is that Kami       *)
(** invested in kinv_magic for their structural layer, and we have not      *)
(** built the equivalent for ours.                                           *)
(**                                                                           *)
(** ** What a protocol_inv_magic would need to handle                       *)
(**                                                                           *)
(** Analysis of actual step proofs (dsdp_inv_step_AR: ~336 lines):          *)
(**                                                                           *)
(**   Category              | % of proof | What it does                      *)
(**   ----------------------|------------|----------------------------------*)
(**   Structural/mechanical | ~75%       | nth_one_step rewriting,           *)
(**                         |            | size_one_step, proc_wf,          *)
(**                         |            | step_send_recv_match,            *)
(**                         |            | index case splits (j=0,1,>=2),   *)
(**                         |            | relay NOP verification           *)
(**   ----------------------|------------|----------------------------------*)
(**   Continuation structure| ~15%       | Unfolding relay_body,            *)
(**                         |            | alice_foldr_at, reasoning about  *)
(**                         |            | oapp/std_from_enc/f_inner,       *)
(**                         |            | function composition             *)
(**   ----------------------|------------|----------------------------------*)
(**   Algebraic/HE          | ~10%       | alice_enc_value, chain_acc,      *)
(**                         |            | Emul_addM, enc_curry_eq          *)
(**                                                                           *)
(** The structural 75% is what kinv_magic-style automation would target.    *)
(** The continuation 15% is protocol-specific but mechanical.               *)
(** The algebraic 10% is the irreducible domain kernel.                     *)
(**                                                                           *)
(** ** The pipeline (revised after audit)                                    *)
(**                                                                           *)
(** A realistic protocol_inv_magic would need 7 stages, not 5:              *)
(**                                                                           *)
(**   Stage            | Kami analog      | What it does                     *)
(**   -----------------|------------------|-------------------------------- *)
(**   pinv_step_dest   | kinv_action_dest | Identify the Send/Recv pair     *)
(**                    |                  | that fires; extract values      *)
(**   pinv_case_split  | (none — Kami     | Case split on phase index j     *)
(**                    | doesn't need it) | to determine which Inv          *)
(**                    |                  | constructor to target           *)
(**   pinv_nop         | (simpler in Kami | Prove non-participating         *)
(**                    | — per-register   | processes are stuck: their      *)
(**                    | independence)    | (step ps i).2 = false because  *)
(**                    |                  | index doesn't match. Requires  *)
(**                    |                  | ordinal arithmetic.            *)
(**   pinv_constr      | kinv_constr      | Apply the next Inv constructor  *)
(**                    |                  | + produce existential witnesses *)
(**   pinv_proclist_red| kregmap_red      | Simplify nth(one_step_procs,i)  *)
(**                    |                  | for each party i               *)
(**   pinv_cont        | (none — Kami     | Unfold relay_body,              *)
(**                    | has no closures) | alice_foldr_at; reason about   *)
(**                    |                  | continuation structure          *)
(**   pinv_finish      | kinv_finish      | Case-split on nat_dec for      *)
(**                    |                  | party index equality            *)
(**                                                                           *)
(** After all stages, the REMAINING goals would be:                          *)
(**   - 3-5 algebraic goals (HE homomorphism, chain accumulation,           *)
(**     decryption correctness): ~50 lines                                  *)
(**   - ~10-15 ordinal arithmetic goals (j+1 < n_relay, inordK,            *)
(**     prednK, ltn_eqF): ~30 lines                                        *)
(**   - Continuation-structure goals (f_inner/f_dec reconciliation):         *)
(**     ~20 lines                                                           *)
(**   Total residual: ~100 lines, vs ~1000 lines currently.                *)
(**                                                                           *)
(** ** The critical difference from Kami: cross-process dependencies        *)
(**                                                                           *)
(** In Kami, registers are INDEPENDENT: reading/writing reg_a does not      *)
(** affect reg_b. This means kinv_magic can reason about each register     *)
(** independently — kregmap_red simplifies one register at a time.         *)
(**                                                                           *)
(** In our protocol, processes are CROSS-DEPENDENT: Send at slot i          *)
(** targets Recv at slot j. The step function for slot i reads              *)
(** nth ps j (the destination's address). This creates cross-slot           *)
(** dependencies:                                                            *)
(**   - To prove process i stepped correctly, you must know what            *)
(**     process j holds (the Recv continuation)                             *)
(**   - To prove process j is now updated, you must know what process i    *)
(**     sent (the Send payload)                                             *)
(**   - To prove process k is unchanged (NOP), you must show its           *)
(**     index doesn't match any active Send/Recv pair                      *)
(**                                                                           *)
(** This means protocol_inv_magic must reason about ALL n+2 processes      *)
(** SIMULTANEOUSLY, not independently. This is a qualitative increase in   *)
(** tactic complexity compared to kinv_magic.                               *)
(**                                                                           *)
(** However, it is not insurmountable: at each phase, exactly ONE          *)
(** Send/Recv pair fires (the protocol is sequential). The tactic needs    *)
(** to identify this pair and show all other processes are NOPs. The        *)
(** NOP proofs are uniform: for process k, show k != sender AND            *)
(** k != receiver. This is ordinal arithmetic, not algebraic reasoning.   *)
(**                                                                           *)
(** ** Does protocol_inv_magic need the TEA DSL?                            *)
(**                                                                           *)
(** NO. The tactic could be built directly on the existing dsdp_inv         *)
(** structure, which already has:                                            *)
(**   - Named constructors (Inv_AR, Inv_ASj, etc.) for phase matching     *)
(**   - Per-slot hypotheses (nth ps i = ...) for process-list reasoning    *)
(**   - A uniform shape across constructors (size, wf, per-slot specs)    *)
(**                                                                           *)
(** The TEA DSL's value is in DECLARING protocols (reducing the 2200 lines *)
(** of dsdp_fsm.v). The automation of step proofs is a SEPARATE concern   *)
(** that depends on the process-list structure, not the declaration DSL.   *)
(**                                                                           *)
(** However, if both the TEA DSL AND protocol_inv_magic exist, they        *)
(** complement each other:                                                  *)
(**   - TEA DSL: user writes ~30 lines of declarations                     *)
(**   - render bridge: derived from declarations (~70 lines)               *)
(**   - protocol_inv_magic: automates step proofs, leaving ~100 lines      *)
(**     of algebraic + ordinal residuals                                    *)
(**   - Total: ~200 lines vs ~2200 lines currently                         *)
(**                                                                           *)
(** These are independent contributions that stack multiplicatively.        *)
(**                                                                           *)
(** ** Summary: the real answer                                              *)
(**                                                                           *)
(** Q: Why does Kami automate per-step proofs but we can't?                 *)
(** A: Both domains have the same two-layer structure (automatable          *)
(**    structural layer + domain-specific residual). The difference is:     *)
(**    (1) Kami built kinv_magic; we haven't built protocol_inv_magic.      *)
(**    (2) Our structural layer is harder (cross-process dependencies       *)
(**        vs independent registers), but not fundamentally so — the       *)
(**        protocol is sequential, so exactly one pair fires per step.     *)
(**                                                                           *)
(** The DSL and the tactic are SEPARATE contributions:                      *)
(**   - TEA DSL: saves ~1200 lines of declaration boilerplate              *)
(**   - protocol_inv_magic: saves ~900 lines of step-proof boilerplate     *)
(**   - Together: ~2100 lines saved, leaving ~100 lines of residual        *)
(**                                                                           *)
(******************************************************************************)


(******************************************************************************)
(** * Part 19: Generality — Any Deterministic Protocol on smc_interpreter   *)
(******************************************************************************)

(** The TEA DSL + protocol_inv_magic approach is NOT DSDP-specific.          *)
(** It generalizes to any deterministic protocol (or protocol with           *)
(** expandable branches) that runs on smc_interpreter.                       *)
(**                                                                           *)
(** ** What's generic (any protocol on smc_interpreter)                     *)
(**                                                                           *)
(** The TEA DSL layer targets PROTOCOL STRUCTURE, not DSDP algebra:         *)
(**   - phase: enumerate control points. Any protocol has them.             *)
(**   - event: what triggers transitions. Any protocol has message arrivals.*)
(**   - update: pure function, one case per (phase, event). Any             *)
(**     deterministic protocol can be written this way.                      *)
(**   - trace_fragment: observable at each phase. Protocol-specific          *)
(**     values, but the SHAPE is generic.                                    *)
(**                                                                           *)
(** The protocol_inv_magic tactic layer targets SMC_INTERPRETER TYPES:      *)
(**                                                                           *)
(**   Stage            | What it targets              | Protocol-specific?  *)
(**   -----------------|------------------------------|--------------------*)
(**   pinv_step_dest   | step_send_recv_match on      | No — proc has the  *)
(**                    | proc data (Send/Recv/Init/    | same constructors  *)
(**                    | Ret/Finish/Fail)              | for all protocols  *)
(**   pinv_case_split  | Phase index to choose next   | No — any protocol  *)
(**                    | invariant constructor         | has phase indices   *)
(**   pinv_nop         | (step ps i).2 = false when   | No — NOP is always *)
(**                    | index doesn't match           | "index mismatch"   *)
(**   pinv_proclist_red| nth (one_step_procs ps) i    | No — one_step_procs*)
(**                    | simplification                | is smc_interpreter *)
(**   pinv_constr      | Apply next Inv constructor   | No — any simulation*)
(**                    | + existential witnesses       | invariant has them *)
(**   pinv_cont        | Unfold continuations in      | No — all protocols *)
(**                    | proc data                     | use proc data      *)
(**   pinv_finish      | nat_dec on party indices     | No — party indices *)
(**                    |                               | are always nat     *)
(**                                                                           *)
(** Every stage targets smc_interpreter's types and operations. Nothing    *)
(** depends on HE, AHE, or DSDP's algebraic structure.                     *)
(**                                                                           *)
(** ** What's protocol-specific (only the algebraic residual)               *)
(**                                                                           *)
(** After protocol_inv_magic runs, the remaining goals are the              *)
(** DOMAIN-SPECIFIC ALGEBRAIC LEMMAS. These change per protocol:           *)
(**                                                                           *)
(**   Protocol            | Algebraic residual                              *)
(**   --------------------|----------------------------------------------  *)
(**   DSDP                | HE homomorphism: Epow(enc,u) * enc(ek,r,rand)  *)
(**                       | = enc(ek, u*v+r, ...) — dot product correct   *)
(**   Oblivious transfer  | RSA blinding: (m * r^e)^d / r = m             *)
(**                       | — sender can't learn receiver's choice         *)
(**   Secret sharing      | Lagrange interpolation: sum(l_i * s_i) = secret*)
(**                       | — shares reconstruct the secret                *)
(**   Garbled circuits    | Symmetric encryption:                           *)
(**                       | Dec(k, Enc(k, gate_output)) = gate_output     *)
(**                       | — gate evaluation is correct                   *)
(**   MPC (generic)       | Ring operations over secret-shared values      *)
(**                       | — computation preserves sharing                *)
(**                                                                           *)
(** Each protocol contributes ~50 lines of algebraic lemmas.               *)
(** Everything else (process-list manipulation, NOP verification, phase    *)
(** tracking, size/wf preservation) is the SAME structural work that       *)
(** protocol_inv_magic handles generically across all protocols.           *)
(**                                                                           *)
(** ** Branching protocols                                                   *)
(**                                                                           *)
(** For protocols with data-dependent branches (e.g., "if signature         *)
(** valid, accept; else abort"), expand branches into separate phase        *)
(** constructors:                                                            *)
(**                                                                           *)
(*
Inductive phase :=
  | ...
  | PhVerify (j : nat)        (* check signature *)
  | PhVerify_ok (j : nat)     (* branch: signature was valid *)
  | PhVerify_fail (j : nat)   (* branch: signature was invalid *)
  | ...

(* Branching next_phase returns a list of possible successors *)
Definition next_phases (p : phase) : list phase :=
  match p with
  | PhVerify j => [PhVerify_ok j; PhVerify_fail j]
  | PhVerify_ok j => [PhContinue (j + 1)]   (* deterministic after branch *)
  | PhVerify_fail j => [PhAbort]
  | _ => (* other deterministic cases *) ...
  end.

(* Each branch gets its own trace_fragment and update case *)
Definition trace_fragment (p : phase) : list data :=
  match p with
  | PhVerify_ok j => [d (verified_value j)]
  | PhVerify_fail j => [d abort_marker]
  | ...
  end.
*)
(**                                                                           *)
(** Each branch becomes a separate phase. The step proof for the branch    *)
(** point has TWO commuting-diagram obligations (one per successor) —      *)
(** but both use the same protocol_inv_magic stages. The algebraic         *)
(** residual for the branch is "signature_verify(sig, msg, pk) = true"    *)
(** or "= false" — domain-specific, like all algebraic residuals.         *)
(**                                                                           *)
(** ** The generality condition                                              *)
(**                                                                           *)
(** The approach works for any protocol that satisfies:                     *)
(**                                                                           *)
(**   1. Runs on smc_interpreter — uses proc data with                     *)
(**      Send / Recv / Init / Ret / Finish / Fail                          *)
(**                                                                           *)
(**   2. Enumerable phases — the control points can be named               *)
(**      (finitely or parametrically in some index like n_relay)            *)
(**                                                                           *)
(**   3. Branches are expandable — data-dependent branches become          *)
(**      separate phase constructors, one per case                          *)
(**                                                                           *)
(**   4. Terminates — bounded fuel reaches a terminal phase                *)
(**                                                                           *)
(** These are not restrictive. They describe exactly the class of           *)
(** protocols that smc_interpreter was designed for.                        *)
(**                                                                           *)
(** ** What would NOT work                                                   *)
(**                                                                           *)
(**   - Unbounded retries (e.g., "keep sending until ACK received"):       *)
(**     Phase space is not finite. Would need coinductive phases or         *)
(**     explicit fuel as a phase parameter. Possible but requires          *)
(**     extending the framework.                                            *)
(**                                                                           *)
(**   - Dynamic party sets (parties join/leave at runtime):                 *)
(**     Phase space depends on runtime configuration. The proc list        *)
(**     size changes dynamically. smc_interpreter itself does not           *)
(**     support this.                                                       *)
(**                                                                           *)
(**   - Truly probabilistic branching (not just "consider all cases"):     *)
(**     Needs probabilistic semantics (distributions over next states),    *)
(**     not deterministic update. The TEA model (one state -> one next     *)
(**     state per event) does not capture this. Would need a               *)
(**     probabilistic extension (probability monad in update).             *)
(**                                                                           *)
(** These are limitations of smc_interpreter itself, not of the TEA +      *)
(** protocol_inv_magic framework. A more expressive interpreter would      *)
(** enable a correspondingly more expressive framework.                    *)
(**                                                                           *)
(** ** The full generality picture                                           *)
(**                                                                           *)
(**   For any protocol P on smc_interpreter satisfying conditions 1-4:     *)
(**                                                                           *)
(**   User writes:                                                          *)
(**     - phase type for P              (~10 lines, protocol-specific)     *)
(**     - event type for P              (~5 lines, protocol-specific)      *)
(**     - update function for P         (~20 lines, protocol-specific)     *)
(**     - trace_fragment for P          (~10 lines, protocol-specific)     *)
(**     - algebraic lemmas for P        (~50 lines, protocol-specific)     *)
(**     Total: ~95 lines                                                    *)
(**                                                                           *)
(**   Framework provides (GENERIC, same for all protocols):                 *)
(**     - TEA Layer 0: trace, progress, termination, invariant theorems   *)
(**     - render bridge: derived from phase declarations                   *)
(**     - protocol_inv_magic: automates step-correctness proofs           *)
(**     - Residual ordinal/continuation goals: ~50 lines (partially       *)
(**       protocol-specific, partially generic patterns)                   *)
(**     Total framework-handled: ~2000+ lines                               *)
(**                                                                           *)
(**   The ratio: ~150 lines user-written per protocol vs ~2000+ lines     *)
(**   currently. The framework is a ONE-TIME investment that pays off      *)
(**   for every protocol built on smc_interpreter.                         *)
(**                                                                           *)
(******************************************************************************)


(******************************************************************************)
(** * Part 20: HB Mixin Interface for Pluggable Design                       *)
(******************************************************************************)

(** Following the existing project pattern (he_types.v → enc_dec.v →        *)
(** ahe_enc.v → ahe_monoid.v), where:                                       *)
(**   - HETypes (Record) bundles the type family                             *)
(**   - isEncDec (HB.mixin on HETypes) adds enc/dec + axioms                *)
(**   - isAHEnc (HB.mixin on HETypes of isEncDec) adds Emul/Epow + axioms  *)
(**                                                                           *)
(** We follow the same pattern: a Record bundles the types, then HB.mixin   *)
(** layers add operations + axioms. The interpreter bridge is a SEPARATE    *)
(** mixin that can be provided independently.                                *)

(** ** Layer 0: Protocol type bundle (plain Record, like HETypes)            *)

(*
Record ProtoTypes := MkProto {
  pt_data   : Type ;           (* data exchanged on channels *)
  pt_phase  : Type ;           (* control points *)
  pt_event  : Type ;           (* what triggers transitions *)
  pt_nparty : nat ;            (* number of parties *)
}.
*)

(** ** Layer 0: TEA spec mixin (on ProtoTypes, like isEncDec on HETypes)    *)
(**                                                                           *)
(** This is the CORE. It provides the update function, trace fragments,     *)
(** and axioms. Any protocol on any interpreter provides this.              *)

(*
HB.mixin Record isProtoSpec (PT : ProtoTypes) := {
  (* operations *)
  ps_init     : pt_phase PT ;
  ps_next     : pt_phase PT -> option (pt_phase PT) ;
  ps_frag     : pt_phase PT -> seq (pt_data PT) ;
  ps_update   : pt_event PT -> pt_phase PT -> pt_phase PT ;
  ps_terminal : pt_phase PT -> bool ;

  (* axioms *)
  ps_terminal_next :
    forall p, ps_terminal p = true -> ps_next p = None ;
  ps_progress :
    forall p, ps_terminal p = false ->
    exists p', ps_next p = Some p' ;
  ps_update_next :
    forall e p p', ps_next p = Some p' ->
    ps_update e p = p' ;   (* deterministic: event is determined by phase *)
}.

#[short(type=ProtoSpecType)]
HB.structure Definition ProtoSpec := { PT of isProtoSpec PT }.
*)

(** ** Layer 0+: Protocol invariant mixin (on ProtoTypes of isProtoSpec)    *)
(**                                                                           *)
(** OPTIONAL. Adds per-phase algebraic invariants. Like isAHEnc adds        *)
(** Emul/Epow on top of isEncDec.                                           *)

(*
HB.mixin Record hasProtoInvariant (PT : ProtoTypes) of isProtoSpec PT := {
  ps_inv : pt_phase PT -> Prop ;

  (* The key axiom: update preserves the invariant *)
  ps_inv_init : ps_inv ps_init ;
  ps_inv_step :
    forall p p', ps_next p = Some p' ->
    ps_inv p -> ps_inv p' ;
}.

#[short(type=ProtoInvType)]
HB.structure Definition ProtoInv := { PT of isProtoSpec PT & hasProtoInvariant PT }.
*)

(** ** Layer 1: Interpreter bridge mixins (pluggable by EXECUTION MODEL)    *)
(**                                                                           *)
(** Interpreters are classified by EXECUTION MODEL, not application domain: *)
(**                                                                           *)
(**   Execution model       | Description                | Current impl     *)
(**   ----------------------|----------------------------|------------------*)
(**   Synchronous sequential| One Send/Recv pair fires   | smc_interpreter  *)
(**   (SyncSeq)             | per step. Parties take     | from              *)
(**                         | turns. No buffering.       | smc_interpreter.v*)
(**   ----------------------|----------------------------|------------------*)
(**   Asynchronous buffered | Messages go to per-channel | (future)         *)
(**   (AsyncBuf)            | buffers. Parties step      |                  *)
(**                         | independently. Non-blocking|                  *)
(**                         | send, blocking recv.       |                  *)
(**   ----------------------|----------------------------|------------------*)
(**   Concurrent            | Multiple Send/Recv pairs   | (future)         *)
(**   interleaving (Conc)   | may fire in one step.      |                  *)
(**                         | Nondeterministic schedule. |                  *)
(**                                                                           *)
(** "SMC" (secure multi-party computation) is a PROTOCOL-LEVEL concept —   *)
(** what you compute. "SyncSeq" is an EXECUTION-MODEL concept — how the    *)
(** interpreter runs. These are orthogonal. Any MPC protocol could run on  *)
(** any execution model. The bridge connects a specific protocol to a      *)
(** specific execution model.                                               *)
(**                                                                           *)
(** Like isAHEnc depends on isEncDec (you need enc/dec before you can       *)
(** state homomorphism), bridge mixins depend on isProtoSpec (you need      *)
(** the spec before you can state that the interpreter matches it).        *)

(*
(* Bridge to synchronous sequential interpreter (smc_interpreter.v) *)
HB.mixin Record hasSyncSeqBridge (PT : ProtoTypes) of isProtoSpec PT := {
  render    : pt_phase PT -> seq (proc (pt_data PT)) ;
  render_size :
    forall p, size (render p) = pt_nparty PT ;
  render_wf :
    forall p, all_proc_wf (render p) ;
  render_init :
    render ps_init = initial_procs ;
  step_ok :
    forall p p', ps_next p = Some p' ->
    one_step_procs (render p) = render p' ;
  trace_ok :
    forall p, interp_trace (render p) = ps_frag p ;
}.

#[short(type=SyncSeqProtoType)]
HB.structure Definition SyncSeqProto :=
  { PT of isProtoSpec PT & hasSyncSeqBridge PT }.

(* Bridge to asynchronous buffered interpreter *)
HB.mixin Record hasAsyncBufBridge (PT : ProtoTypes) of isProtoSpec PT := {
  async_render  : pt_phase PT -> async_state (pt_data PT) ;
  async_step_ok :
    forall p p', ps_next p = Some p' ->
    async_step (async_render p) = async_render p' ;
  async_trace_ok :
    forall p, async_trace (async_render p) = ps_frag p ;
}.

#[short(type=AsyncBufProtoType)]
HB.structure Definition AsyncBufProto :=
  { PT of isProtoSpec PT & hasAsyncBufBridge PT }.

(* Bridge to concurrent interleaving interpreter *)
HB.mixin Record hasConcBridge (PT : ProtoTypes) of isProtoSpec PT := {
  conc_render   : pt_phase PT -> conc_state (pt_data PT) ;
  conc_step_ok  :
    forall p p', ps_next p = Some p' ->
    exists sched, conc_step sched (conc_render p) = conc_render p' ;
  conc_trace_ok :
    forall p, conc_trace (conc_render p) = ps_frag p ;
}.

#[short(type=ConcProtoType)]
HB.structure Definition ConcProto :=
  { PT of isProtoSpec PT & hasConcBridge PT }.
*)

(** ** The hierarchy diagram                                                 *)
(**                                                                           *)
(**   ProtoTypes (Record — bundles data/phase/event/nparty types)           *)
(**     |                                                                    *)
(**     +-- isProtoSpec (HB.mixin — TEA spec: next/frag/update/terminal)    *)
(**     |     |                                                              *)
(**     |     +-- hasProtoInvariant (HB.mixin — per-phase invariants)       *)
(**     |     |     → ProtoInvType                                          *)
(**     |     |                                                              *)
(**     |     +-- hasSyncSeqBridge (HB.mixin — sync sequential bridge)     *)
(**     |     |     → SyncSeqProtoType   (targets smc_interpreter.v)       *)
(**     |     |                                                              *)
(**     |     +-- hasAsyncBufBridge (HB.mixin — async buffered bridge)     *)
(**     |     |     → AsyncBufProtoType                                    *)
(**     |     |                                                              *)
(**     |     +-- hasConcBridge (HB.mixin — concurrent interleaving)       *)
(**     |           → ConcProtoType                                         *)
(**     |                                                                    *)
(**     +-- (future: hasProbSpec for probabilistic protocols)                *)
(**                                                                           *)
(** Compare with the existing HE hierarchy:                                  *)
(**                                                                           *)
(**   HETypes (Record — bundles plain/rand/cipher/key types)                *)
(**     |                                                                    *)
(**     +-- isEncDec (HB.mixin — enc/dec/pub_of_priv + dec_correct)        *)
(**     |     |                                                              *)
(**     |     +-- isAHEnc (HB.mixin — Emul/Epow + homomorphism axioms)     *)
(**     |           |                                                        *)
(**     |           +-- isAHEMonoid (HB.mixin — monoid structure)           *)
(**                                                                           *)
(** The pattern is identical: Record for types, layered HB.mixin for        *)
(** operations + axioms, with ORTHOGONAL mixins for PLUGGABLE features.    *)

(** ** Instances: protocol × interpreter combinations                       *)
(**                                                                           *)
(** The framework is a MATRIX: protocols on one axis, interpreters on the   *)
(** other. Each cell is an HB.instance. The spec (isProtoSpec) lives in    *)
(** the protocol row; the bridge (hasSyncSeqBridge etc.) lives in the cell.    *)
(**                                                                           *)
(**              | SyncSeq           | AsyncBuf          | (no interp)  *)
(**              | (smc_interp.v)    | (future)          |              *)
(**   -----------|-------------------|-------------------|------------- *)
(**   DSDP       | DSDP_on_SyncSeq   | (future)          | isProtoSpec  *)
(**   -----------|-------------------|-------------------|------------- *)
(**   Oblivious  | OT_on_SyncSeq     | OT_on_AsyncBuf    | isProtoSpec  *)
(**   Transfer   |                   |                   |              *)
(**   -----------|-------------------|-------------------|------------- *)
(**   Secret     | (future)          | SS_on_AsyncBuf    | isProtoSpec  *)
(**   Sharing    |                   |                   |              *)
(**                                                                           *)
(** The isProtoSpec column (rightmost) always exists — it IS the protocol. *)
(** Bridge columns are optional and independent. A protocol can have zero, *)
(** one, or multiple bridge instances for different interpreters.           *)

(** ** Example: DSDP on SyncSeq (smc_interpreter)                            *)

(*
(* Protocol types *)
Definition DSDP_Types (AHE : AHEncType) (n_relay : nat) : ProtoTypes := {|
  pt_data   := di_data (Standard_DSDP_Interface AHE) ;
  pt_phase  := dsdp_phase ;
  pt_event  := dsdp_event ;
  pt_nparty := n_relay.+2 ;
|}.

(* TEA spec — protocol-specific, interpreter-independent *)
HB.instance Definition DSDP_isProtoSpec
    (AHE : AHEncType) (n_relay : nat) :
    isProtoSpec (DSDP_Types AHE n_relay) := {|
  ps_init     := PhInit1 ;
  ps_next     := dsdp_next_phase ;
  ps_frag     := dsdp_trace_fragment ;
  ps_update   := dsdp_update ;
  ps_terminal := fun p => match p with PhDone => true | _ => false end ;
  (* axiom proofs: trivial by case analysis on phase *)
  ...
|}.

(* Bridge: DSDP × smc_interpreter *)
HB.instance Definition DSDP_on_SyncSeq
    (AHE : AHEncType) (n_relay : nat) :
    hasSyncSeqBridge (DSDP_Types AHE n_relay) := {|
  render      := dsdp_smc_render ;
  render_size := dsdp_smc_render_size ;
  render_wf   := dsdp_smc_render_wf ;
  render_init := dsdp_smc_render_init ;
  step_ok     := dsdp_smc_step_ok ;    (* ~1000 lines — the simulation *)
  trace_ok    := dsdp_smc_trace_ok ;
|}.
*)

(** ** Example: Oblivious Transfer on SyncSeq                               *)

(*
Definition OT_Types (n : nat) : ProtoTypes := {|
  pt_data   := ot_data ;
  pt_phase  := ot_phase ;    (* OT_Choose | OT_Send | OT_Reveal | OT_Done *)
  pt_event  := ot_event ;
  pt_nparty := 2 ;
|}.

(* TEA spec for OT — same mixin, different protocol *)
HB.instance Definition OT_isProtoSpec (n : nat) :
    isProtoSpec (OT_Types n) := {|
  ps_init     := OT_Choose ;
  ps_next     := ot_next_phase ;
  ps_frag     := ot_trace_fragment ;
  ...
|}.

(* Bridge: OT × smc_interpreter — same bridge mixin, different instance *)
HB.instance Definition OT_on_SyncSeq (n : nat) :
    hasSyncSeqBridge (OT_Types n) := {|
  render  := ot_smc_render ;
  step_ok := ot_smc_step_ok ;   (* OT-specific simulation *)
  ...
|}.
*)

(** ** Example: same protocol, different execution model                    *)

(*
(* Bridge: OT × async_interpreter — SAME spec, DIFFERENT bridge *)
HB.instance Definition OT_on_AsyncBuf (n : nat) :
    hasAsyncBufBridge (OT_Types n) := {|
  async_render  := ot_async_render ;
  async_step_ok := ot_async_step_ok ;  (* different simulation proof *)
  async_trace_ok := ot_async_trace_ok ;
|}.

(* Now OT_Types n has BOTH SyncSeqProtoType and AsyncBufProtoType structures.
   Security proofs (written against ProtoSpecType) work for both. *)
*)

(** ** Generic theorems: written once, work for all cells in the matrix    *)

(*
(* Security: works for ANY protocol, no interpreter needed *)
Section security_proof.
Variable PT : ProtoSpecType.

Theorem trace_security :
  forall p, ps_inv p -> secure (ps_frag p).
(* Proved ONCE. Works for DSDP, OT, secret sharing, ... *)
End security_proof.

(* Soundness for sync-sequential execution model *)
Section syncseq_soundness.
Variable PT : SyncSeqProtoType.

Theorem syncseq_computational_soundness :
  forall procs fuel,
  interp_comp procs fuel = done_procs ->
  secure (interp_full_trace procs).
Proof.
  (* Uses step_ok to transfer from sync-seq interpreter trace to
     spec trace, then applies trace_security from the spec layer.
     Proved ONCE. Works for DSDP-on-SyncSeq, OT-on-SyncSeq, ... *)
End syncseq_soundness.

(* Soundness for async-buffered execution model *)
Section asyncbuf_soundness.
Variable PT : AsyncBufProtoType.

Theorem asyncbuf_computational_soundness :
  forall st fuel,
  asyncbuf_run st fuel = done_state ->
  secure (asyncbuf_full_trace st).
Proof.
  (* Uses async_step_ok to transfer. Same pattern, different exec model.
     Proved ONCE. Works for OT-on-AsyncBuf, etc. *)
End asyncbuf_soundness.
*)

(** ** The pluggability in action                                           *)
(**                                                                           *)
(** The framework provides GENERIC theorems at three levels:                *)
(**                                                                           *)
(**   Level                | Parameterized by   | Works for                  *)
(**   ---------------------|--------------------|--------------------------  *)
(**   trace_security       | ProtoSpecType      | ALL protocols, no exec    *)
(**                        |                    | model needed               *)
(**   syncseq_soundness    | SyncSeqProtoType   | ALL protocols with a     *)
(**                        |                    | SyncSeq bridge            *)
(**   asyncbuf_soundness   | AsyncBufProtoType  | ALL protocols with an    *)
(**                        |                    | AsyncBuf bridge           *)
(**                                                                           *)
(** To add a NEW PROTOCOL: provide isProtoSpec instance (~30 lines).        *)
(** All generic theorems apply immediately.                                  *)
(**                                                                           *)
(** To add a NEW EXECUTION MODEL: define a new bridge mixin + soundness    *)
(** theorem. All existing protocols can then provide bridge instances.       *)
(**                                                                           *)
(** To connect protocol P to execution model E: provide one hasXBridge     *)
(** instance (the simulation proof). The generic soundness theorem          *)
(** applies immediately.                                                    *)
(**                                                                           *)
(** No existing proof is ever modified. This is the HB hierarchy at work.  *)
(**                                                                           *)
(******************************************************************************)

End DSDP_Declarative_Example.
