# Prompt: build an independent cause verifier

Paste everything below the line into Claude Code, from the repository root.

---

## Task

Build `tools/verify_cause.py`: a **standalone oracle** that takes a cause reported by
`explainhyper/explain_hyper.py` and decides, independently, whether it really is an actual
cause under Definition 6 of Coenen et al., "Explaining Hyperproperty Violations" (CAV 2022).

This is a **verification tool, not a second implementation of the algorithm.** Its job is to
catch bugs in the existing tool. It is allowed to be slow, brute-force and obviously correct.
Prefer the dumbest implementation that is clearly right over anything clever.

## Hard independence constraints — these are the point of the exercise

A verifier that shares code with the thing it verifies cannot catch that code's bugs.

1. **Do not import anything from `explainhyper/`.** Not `highlighter`, not `ltl2alt`, not
   `altautomaton`, not `trace`, not `formula`, not `translator`, not `explain_hyper`, not
   `smv`. No exceptions. If you need something they do, reimplement it.
2. **Do not use alternating automata.** The tool evaluates LTL via Finkbeiner & Sipma's
   alternating-automaton backwards analysis. Use a different method (see below), so that a bug
   in that analysis is detectable.
3. **Do not use `spot`.** The tool uses it for formula manipulation; a shared misunderstanding
   of the formula would cancel out.
4. **Write your own AIGER simulator** (~40 lines: parse `aag`, evaluate AND gates in order,
   step the latches). Do not use `py-aiger`. The existing tool simulates with `py-aiger`, and
   a simulator-level disagreement is exactly the class of bug worth catching.
5. Standard library plus `pytest` only.

## What the existing tool produces (verified formats — do not guess)

Run from an example directory, e.g.:

```bash
cd examples/leaky_mux
python ../../explainhyper/explain_hyper.py -aag leaky_mux.aag -cex leaky_mux.cex \
  -f "<MCHyper formula>" -outName out -stateMachine leaky_mux.dot
```

**stdout** (parse these exact lines):

```
Size of the counter example (|Gamma|) is: 10
for trace 0: [('a', 0, 1, 0), ('sel', 0, 0, 0)]
for trace 1: []
All minimal causes (forall C): [[('a', 0, 1, 0)], [('sel', 0, 0, 0)]]
Number of minimal causes (# C): 2
```

A cause is a **list of events**; an event is the 4-tuple `(ap, timestep, truth_value, trace_id)`
where `truth_value` is `1`/`0`. `for trace N:` lines give the candidate set `C~`.

**`<outName>.json`** — the counterexample Γ and the formula:

```json
{
  "lassoStart": 1,
  "variables": {"a": {"type": "input"}, "sel": {"type": "input"},
                "out": {"type": "output"}, "state": {"type": "latch"}},
  "timesteps": [
     [ {"state": false, "out": true, "b": false, "a": true, "sel": true},
       {"state": false, "out": true, "b": false, "a": true, "sel": true} ]
  ],
  "plain": "(G(((a_0)<->(a_1))&((b_0)<->(b_1))))->(G((out_0)<->(out_1)))"
}
```

- `timesteps[t][i]` = the valuation at time `t` on trace `i`.
- `variables[name].type` ∈ `{input, output, latch}` — **inputs are exogenous, outputs
  endogenous**; causes may only contain inputs, contingencies only outputs.
- `lassoStart` = index where the loop begins; **`-1` means a flat finite trace** (HyperQB
  produces these) and there is no loop at all.
- `plain` = the **zipped LTL formula**: HyperLTL with quantifiers stripped and `_<traceid>`
  appended to each AP. Operators: `G F X U R W ! & | -> <->`. Parse this yourself.

## What to implement

### 1. A self-contained LTL evaluator over lasso words

Signature: `holds(formula, word, position) -> bool`, where `word` is `(prefix, loop)`.

Use **bounded unrolling with cycle detection**, not automata:

- If `lassoStart >= 0`, the word is `u·v^ω`. Evaluate recursively over positions, where
  position `n` past the end wraps to `lassoStart + (n - lassoStart) mod len(loop)`.
  For `G φ`: true iff φ holds at every position in `prefix + loop` (the loop covers all
  future positions, so checking one lap suffices). For `F φ`: true iff φ holds at some
  position in `prefix + loop`. For `φ U ψ`: unroll at most `len(prefix) + len(loop)`
  positions — longer is redundant on a lasso.
- If `lassoStart == -1`, the word is **finite**. You must support both readings, selected by
  a flag, because the tool has both:
  - `strong` (default): `G φ` at the horizon is **false**, `F φ` unwitnessed is false.
  - `weak`: the horizon means "nothing further observed" — `G φ` is **true** if φ held
    everywhere observed, `F φ` is false unless witnessed.
  Mirror the tool's `-finiteSemantics` flag. Record which was used in the output.

Write the evaluator against a small hand-checked truth table first (see Testing).

### 2. The system, simulated independently

Parse the `.aag` yourself and expose `step(latch_state, inputs) -> (outputs, next_latches)`.

AIGER ASCII format: header `aag M I L O A`; then `I` input literals; `L` latch lines
`current next [init]` (init defaults to 0); `O` output literals; `A` AND lines
`lhs rhs0 rhs1`; then a symbol table (`i0 name`, `l0 name`, `o0 name`). A literal is
`var*2`, odd means negated, `0` = false, `1` = true. AND lines are already topologically
ordered.

**Sanity gate before anything else:** replay Γ's input columns through your simulator and
check that the outputs and latches match `timesteps`. If they do not, stop and report
`SYSTEM_MISMATCH` — every later verdict would be meaningless.

### 3. Intervention and the counterfactual automaton (Definitions 4 and 5)

`intervene(Γ, C, W)`:

- For each event `(a, n, val, i)` in cause `C`: on trace `i` at time `n`, **flip** input `a`.
- Then re-simulate each trace from its initial state with the modified input sequence.
- For each event `(o, n, val, i)` in contingency `W`: after computing step `n` of trace `i`,
  **overwrite** output `o` to the value it had in the original Γ, and continue the simulation
  **from the state that overwrite implies**.

That last part is the subtle one and the most common place to get this wrong. Per Definition 4,
a contingency *changes the state of the system* and the run continues from the new state — the
resulting trace need **not** be a trace of the original system. The paper's Example 2 shows
exactly this: `t₂''` is not a trace of Fig. 1. Since the examples' states are uniquely labelled
by their outputs, overwriting output `o` at step `n` means the next step is computed from the
state whose label is the overwritten output set.

### 4. The three conditions (Definition 6)

Given Γ and a claimed cause `C`:

- **SAT**: `Γ ⊨ C` — every event in `C` matches Γ (right AP, right time, right value, right
  trace). Pure lookup against `timesteps`.
- **CF**: there exist a contingency `W ⊆ OE` with `Γ ⊨ W`, and a **non-empty** `C' ⊆ C`, such
  that `intervene(Γ, C', W) ⊨ φ`. Note it is the *un-negated* φ — the violation is repaired.
  Search `C'` over all non-empty subsets of `C`, and `W` over subsets of output events up to a
  size bound (`--max-contingency`, default 2; record the bound in the output, since "no
  contingency found" is only meaningful relative to it). `W = ∅` must be tried first.
- **MIN**: no **proper** subset of `C` satisfies SAT and CF. Enumerate all proper subsets and
  check. `|C|` is small, so this is cheap and must be exhaustive.

`C` is a valid actual cause iff all three hold.

### 5. Optional completeness check (`--check-completeness`)

Did the tool **miss** a cause? Enumerate every subset of the candidate set `C~` up to
`--max-cause-size`, test SAT ∧ CF ∧ MIN on each, and report any that qualify but are absent
from the tool's reported list. This is exponential; keep it opt-in and bounded.

## CLI

```
python tools/verify_cause.py --json out.json --aag leaky_mux.aag \
       [--causes "[[('a',0,1,0)],[('sel',0,0,0)]]" | --log run.log] \
       [--finite-semantics strong|weak] [--max-contingency N]
       [--check-completeness --max-cause-size N] [--csv report.csv]
```

Accept the causes either inline or by scraping a saved stdout log. Exit `0` if every claimed
cause verifies, `1` otherwise.

## Output

Per cause, print and write to CSV:

| column | meaning |
|---|---|
| `example`, `frontend` | provenance |
| `cause` | readable, e.g. `a@0=1(t0)` |
| `sat`, `cf`, `min` | `pass` / `fail` |
| `verdict` | `VALID` / `INVALID` |
| `why` | which condition failed and the concrete reason |
| `witness_subset`, `witness_contingency` | the `C'` and `W` that made CF succeed |
| `finite_semantics`, `max_contingency` | the settings the verdict is relative to |

Also emit a summary line: how many causes verified, how many failed, and whether Γ itself
satisfies ¬φ (if it does not, say so loudly — it means the "counterexample" is not one, which
is a defect in the instance rather than in the cause).

## Testing — the verifier must itself be tested

Put tests in `tests/test_verify_cause.py`. The verifier is worthless if it rubber-stamps.

1. **LTL evaluator truth table.** Hand-compute ~20 cases over tiny lassos: `G a` on
   `({a},)({a},)`, `F a` where `a` only in the loop, `a U b`, nesting, and the finite
   `strong`/`weak` split. Assert exact expected values.
2. **Simulator agreement.** For each example, replay Γ and assert zero mismatches against
   `timesteps`.
3. **Known-good.** The paper's Table 1 reports `Running example` → 2 causes,
   `¬hi⁰_t1, hi⁰_t2`. Assert both verify as `VALID`.
4. **Negative controls — the important ones.** Construct causes that must be rejected:
   - an event not in Γ (wrong truth value) → `SAT` must fail;
   - a superset of a known cause → `MIN` must fail;
   - an irrelevant input event that does not repair the violation → `CF` must fail.
   If any of these pass, the verifier is broken.
5. **Mutation test.** Deliberately corrupt a cause's timestep (`0` → `1`) and assert the
   verdict flips to `INVALID`.

## Known pitfalls, each of which has already bitten this project

- **Finite vs lasso semantics.** HyperQB counterexamples are flat (`lassoStart == -1`); under
  `strong`, `G` is false at the horizon and *nothing* verifies. Always report which semantics a
  verdict used. See `STAGE0-FINDING.md`.
- **Γ may not be a counterexample at all.** On several shipped examples the recorded
  counterexample does not satisfy ¬φ — e.g. `drone_example_2`'s traces differ on `bound`, so
  its antecedent `G(up₀=up₁ ∧ bound₀=bound₁)` is false and the implication holds. Check this
  first and report it separately; do not blame the cause.
- **Phantom APs.** Some formulas reference APs absent from the circuit (`running_example` uses
  `li`; `asymmetric_arbiter_19` uses `req_0` where the circuit has `req0`). Detect APs in
  `plain` that are missing from `variables` and **fail loudly** rather than silently treating
  them as false.
- **Causes contain only inputs; contingencies only outputs.** Validate against
  `variables[*].type` and reject malformed input rather than computing nonsense.
- **The last row of a lasso trace.** The tool's convention is that the final row duplicates the
  loop-back state. Check whether `timesteps` already has it dropped before indexing, and assert
  your reading against `lassoStart` and the simulator.
- **`C'` is a non-empty subset of `C`, not `C` itself.** CF quantifies existentially over
  `C' ⊆ C`; testing only `C' = C` is wrong and will wrongly reject valid causes.

## Acceptance

- `pytest tests/test_verify_cause.py -q` green, negative controls included.
- Runs over all 9 examples in `examples/` for every front end that produced causes.
- Zero imports from `explainhyper/`; verify with
  `grep -nE "^(from|import) (explainhyper|highlighter|ltl2alt|altautomaton|trace|formula|translator|aiger|spot)" tools/verify_cause.py` returning nothing.
- Report any cause that fails to verify as a **finding about the tool**, with the concrete
  witness, rather than adjusting the verifier until it agrees.
