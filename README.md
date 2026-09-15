# Explaining Hyperproperty Violations

## Introduction

This python library computes explanations for counterexamples to hyperproperties described in the specification logic HyperLTL.
Hyperproperties relate multiple computation traces to each other. Model checkers for hyperproperties thus return, in case a system model violates the specification, a set of traces as a counterexample. Fixing the erroneous relations between traces in the system that led to the counterexample is a difficult manual effort that highly benefits from additional explanations.

## Requirements
- [Python](https://www.python.org) (tested with v3.7)
- [PyAiger](https://github.com/mvcisback/py-aiger) (tested with v6.1.23)
- [Graphviz](https://graphviz.org/) (tested with v2.42.2-5)
- [PyGraphviz](https://pygraphviz.github.io/) (tested with v1.9)
- [cvc5](https://cvc5.github.io/) (tested with v1.3.4)
- [spot](https://spot.lrde.epita.fr/) (tested with v2.10.4)

## Installation

To install the python package as well as the python requirements above, run:

```
git clone https://github.com/reactive-systems/explaining-hyperproperty-violations.git
cd explaining-hyperproperty-violations
pip install .
```

In addition to the python requirements above, the LTL, automata manipulation and model checking library [Spot](https://spot.lrde.epita.fr) is required. Please follow the [download and installation instructions](https://spot.lrde.epita.fr/install.html) on their website.

## Usage

The input is
- a HyperLTL specification as a string in the MCHyper (<https://github.com/reactive-systems/MCHyper>) format provided with `-f`
- system given as DOT (.dot) and Aiger (.aag) provided with `-stateMachine` and `-aag` respectively
- and a MCHyper counterexample (.cex) provided with `-cex`

The output is
- a cause explaining the hyperproperty violation
- and a set of all minimal causes.

Example data is provided in `/examples`. The examples are taking from the CAV'22 paper of the same name. In general, any MCHyper counter example file and every Aiger file and its .dot representation work (see [aiger2dot](https://github.com/arminbiere/aiger)).
```
cd examples
python ../explainhyper/explain_hyper.py -aag asymmetric_arbiter.aag -cex asymmetric_arbiter.cex -f "Forall (Forall (Implies (G (And (Eq (AP \"req_0\" 0) (AP \"req_0\" 1)) (Eq (AP \"req_1\" 0) (AP \"req_1\" 1)))) (G (And (Eq (AP \"grant_0\" 0) (AP \"grant_0\" 1)) (Eq (AP \"grant_1\" 0) (AP \"grant_1\" 1))))))" -outName "tmp" -stateMachine "asymmetric_arbiter.dot"
```

The command line output is structured as follows:
```
Size of the counter example:
Size of the formula:
Causes:
Time (in s) to compute this set of causes:
All minimal causes:
Number of minimal causes:
Time (in s) to compute all causes:
```
Where a cause is given as a tuple (name of AP, time step, truth value, trace belonging). For more information about notation and algorithmic details, please see the corresponding paper.

## Upgrades over the original CAV'22 artifact

This fork extends the original implementation. The changes below are ordered by
how much they affect results.

### Solver backend: SAT (PySAT/SATisPy) → SMT (cvc5)

Candidate-cause computation (the over-approximation `C~`) is the only phase that
calls a solver. It used to build propositional formulas *as text*, convert them
with `satispy.CnfFromString`, hash atomic proposition names to integer IDs by
string substitution, and feed integer clauses to PySAT's Glucose4. That pipeline
is now expressed directly against cvc5's term API in `explainhyper/highlighter.py`.

Why this matters beyond tidiness:

- **The old integer encoding was substitution-based and fragile.** AP names were
  mapped to IDs via `str.replace`, so an AP name that is a prefix of another
  (`up#1` inside `up#10`) could corrupt the clause text. cvc5 terms carry
  identity, so cores map back to `(AP, timestep, truth value, trace)` directly.
- **cvc5 is a superset of a SAT solver.** The encoding here is still purely
  propositional, so this change alone does *not* add expressiveness — but it is
  the prerequisite for representing non-Boolean (bitvector/integer) signals,
  which the AIGER-based model cannot express today.

Results are unchanged: across the nine bundled examples the computed cause sets
are identical (`asymmetric_arbiter` still yields its 24 minimal causes). Only the
*order* in which causes are reported differs, since a different solver returns
unsat cores in a different order.

### Bug fix: tautological transition guards erased all causes

A guard such as `up ∨ ¬up` (in `drone_example_1`) means "this transition accepts
any input", so it constrains nothing. The encoding asserts the *negation* of each
guard taken along the trace, and `¬(up ∨ ¬up)` is unsatisfiable on its own — it
made the whole query trivially unsat and hid every real cause. SATisPy happened to
silently drop such conjuncts; relying on that was accidental. Tautological guards
are now detected explicitly (with cvc5) and skipped. Without this fix
`drone_example_1` reports 0 causes instead of 7.

### Support for arbitrarily many trace quantifiers

The pipeline previously hard-coded two traces. Trace handling is now driven by
`num_traces` (derived from the quantifier prefix), so specifications with three or
more quantifiers work; see `examples/triple_forall` and `examples/triple_cause`.

### Cause verification and regression tests

`verify_cause` re-simulates the counterfactual for every reported minimal cause and
raises `CauseVerificationError` if flipping it does not actually resolve the
violation, so a wrong cause fails loudly instead of being printed. A pytest suite
covering formula/trace units plus end-to-end runs of every example lives in
`tests/` (`pytest tests/`; the `asymmetric_arbiter` cases are marked `slow`).

### Known issue: non-deterministic results with parallel transitions

When a state machine has **parallel edges between the same pair of states** — e.g.
`examples/leaky_mux`, where both `¬a∧¬sel` and `¬b∧sel` lead `state0 → state0` —
`AGraph.get_edge` returns an arbitrary one of them. The reported causes therefore
change between runs of the *same* command on the *same* input. This predates the
cvc5 migration and affects the original code identically (adding an unrelated
import to the PySAT version is enough to flip the outcome). Benchmarks whose DOT
model has parallel edges are not currently reproducible run to run.

## Further Usage

The library can be used on top of the existing Hyperproperty model checking tool MCHyper to provide meaningful explanations. The library is flexible enough to incorporate further development progress and support hyperproperty model checking tools developed in the future.

## How to cite
```
@inproceedings{explaining-hyperproperty-violations,
    title     = {Explaining Hyperproperty violations},
    author    = {Norine Coenen, Raimund Dachselt, Bernd Finkbeiner, Hadar Frenkel, Christopher Hahn, Tom Horak, Niklas Metzger, and Julian Siber},
    booktitle = {34th International Conference on Computer Aided Verification (CAV 2022), to appear},
    year      = {2022}
}
```
