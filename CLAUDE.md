# Explaining Hyperproperty Violations

## Project Overview

This tool computes **actual causes** for counterexamples to hyperproperties described in HyperLTL. It extends Halpern and Pearl's definition of actual causality to sets of traces witnessing the violation of a HyperLTL formula, identifying which input events caused the violation.

Based on: Coenen et al., "Explaining Hyperproperty Violations", CAV 2022.

## Theoretical Background

### Hyperproperties and HyperLTL

- **Hyperproperties** are sets of sets of traces — they relate multiple computation traces to each other (unlike trace properties which reason about individual traces).
- **HyperLTL** extends LTL with explicit trace quantification (`forall pi. exists pi'. ...`).
- Systems are modeled as **Moore machines** `T = (S, s0, AP, delta, l)` where `AP = I ∪ O` (inputs and outputs).
- A **counterexample** to a universal HyperLTL formula `forall pi1...pik. psi` is a tuple of traces `Gamma = <t1,...,tk>` such that `Gamma, 0 |= neg psi`.

### Actual Causality (Halpern-Pearl, adapted)

A set of input events `C` is an **actual cause** for violation of `phi` on counterexample `Gamma` if:

1. **SAT**: `Gamma |= C` — the cause events are present in the counterexample.
2. **CF** (Counterfactual): There exists a contingency `W` (output events) and a non-empty `C' ⊆ C` such that `Gamma |= W` and `intervene(Gamma, C', W) |= phi` — flipping the cause (with contingency) resolves the violation.
3. **MIN**: `C` is minimal — no proper subset satisfies SAT and CF.

### Key Concepts

- **Events**: Tuples `<la, n, t>` — an atomic proposition `a` (positive or negated) at time `n` on trace `t`.
- **Input events** (exogenous) vs **output events** (endogenous).
- **Intervention**: Flipping input events in the cause `C` on the counterexample traces.
- **Contingencies**: Output events reset to their counterexample values in the counterfactual world, allowing to control for preempted causes. Implemented via **counterfactual automata**.
- **Counterfactual automaton** `T^C_pi`: A chain of copies of the original system encoding all possible counterfactual behaviors under arbitrary contingencies for trace `pi`.

### Algorithm (3 phases)

1. **Candidate cause computation** (over-approximation `C~`):
   - Analyze transitions taken during the counterexample using **unsatisfiable cores** of SAT formulas — finds inputs necessary for each transition.
   - Additionally use **alternating automata** analysis to find inputs appearing in the formula that affect satisfaction.
   - Result: `C~` is a superset of every actual cause (Proposition 2) and itself satisfies SAT and CF (Proposition 3).

2. **Minimality search** (Algorithm 1 — `ActualCause`):
   - Iterate over subsets of `C~` from smallest to largest.
   - For each candidate `C`: check if flipping all events in `C` resolves the violation (CF without contingency).
   - If not, compute contingencies (Algorithm 2 — `ComputeContingency`).
   - Return the first (smallest) subset satisfying CF.

3. **Contingency computation** (Algorithm 2):
   - Use the annotated run tree of the alternating automaton on the counterfactual trace to identify relevant output events.
   - Try subsets of these events first, then other output events.
   - For each candidate contingency, verify whether the modified trace satisfies `phi`.

### Complexity

Finding actual causes reduces to HyperLTL model checking with one additional quantifier alternation (Proposition 1). The tool restricts to the universal fragment to keep this practical.

## Architecture

```
explainhyper/
  explain_hyper.py   # Main entry point, ActualCause algorithm, cause verification
  formula.py         # Formula AST (LTL operators, Spot/MCHyper format conversion)
  trace.py           # Trace representation (prefix + lasso for omega-regular traces)
  parser.py          # CLI argument parsing
  translator.py      # Formula translation utilities
  operators.py       # Operator enum (ap, Not, X, G, F, U, R, W, Implies, Equiv, And, Or)
  highlighter.py     # Core: formula evaluation, explanation trees, cause negation, SAT-based minimization
  ltl2alt.py         # LTL to alternating automaton translation
  altautomaton.py    # Alternating automaton data structures (Node, Edge, Automaton)
  output.py          # JSON output formatting
examples/            # Benchmark instances (AIGER circuits, CEX files, DOT state machines)
```

## Key Functions

- `actual_causality(args)` — Main algorithm orchestrating candidate computation, minimality search, and cause verification.
- `minimality(i, cause, ...)` — Checks all subsets of size `i` for CF satisfaction.
- `check_formula(f, trace, ...)` — Evaluates an LTL formula on a finite (lasso-shaped) trace.
- `verify_cause()` — Validates that a computed cause actually resolves the violation.
- `Highlighter.run()` — Evaluates formula over traces with explanation tracking.
- `Highlighter.dot_minimization()` — SAT-based state machine minimization for candidate causes.
- `Highlighter.negate_cause()` — Flips cause events in traces to produce counterfactuals.

## Usage

```bash
cd examples
python ../explainhyper/explain_hyper.py \
  -aag <circuit.aag> \
  -cex <counterexample.cex> \
  -f "<HyperLTL formula in MCHyper format>" \
  -outName <output_prefix> \
  [-stateMachine <system.dot>]
```

### Output format
A cause is a tuple `(AP name, time step, truth value, trace index)`.

## Dependencies

- Python >= 3.7
- py-aiger, graphviz, pygraphviz, numpy, python-sat, satispy (installed via `pip install .`)
- [Spot](https://spot.lrde.epita.fr/) >= 2.10.4 (installed separately — LTL/automata library)

## Development Notes

- The HyperLTL-to-LTL reduction zips multiple traces into a single trace with renamed atomic propositions (e.g., `a_pi` becomes a distinct AP). This works due to HyperLTL's synchronous semantics.
- Finite trace model checking uses the linear algorithm of Finkbeiner & Sipma (2004) via alternating automata with backwards analysis.
- SAT solving (Glucose4 via PySAT) is used for: unsatisfiable core computation in candidate cause generation, and state machine minimization.
- Traces are in lasso form `t = u(v)^omega` matching MCHyper's output format.
