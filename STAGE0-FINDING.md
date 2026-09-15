# Stage 0 finding: two semantics defects in the causality pipeline

**Date:** 2026-09-09 · **Status:** measured on all 9 runnable examples

Probe: wrap `check_formula` / `minimality` / `negate_cause`, run `actual_causality`
unmodified, write all artifacts to `tools/_metrics_out/`. Reproduce with

    conda activate hyper
    python tools/causality_metrics.py before              # all examples
    FINSEM=weak python tools/causality_metrics.py weak    # finite-weak semantics

## Baseline (before any change)

| example | orig is lasso | `check_formula(orig cex)` | \|C~\| | calls | `True` | cause sizes |
|---|---|---|---|---|---|---|
| running_example | no | **False** | 2 | 6 | 0 | [1] |
| security_in_and_out | yes | True | 8 | 24 | 0 | [1] |
| drone_example_1 | no | **False** | 7 | 21 | 0 | [1] |
| drone_example_2 | no | **False** | 3 | 9 | 0 | [1] |
| asymmetric_arbiter | yes | True | 24 | 72 | 0 | [1] |
| asymmetric_arbiter_19 | no | **False** | 10 | 30 | 0 | [1] |
| **triple_forall** | yes | True | 9 | 519 | **510** | **[9]** |
| simple_buffer | yes | True | 2 | 6 | 0 | [1] |
| leaky_mux | no | **False** | 2 | 6 | 0 | [1] |

`triple_forall` is the control. Its spec is `∀∀∀ G(¬(out₀∨out₁∨out₂))`, so the negation is
`F(out₀∨out₁∨out₂)` — an `F` formula with **no top-level `G`**. It is the only example whose
negated formula avoids the broken operator, and the only one that ran a real subset search.

## Defect 1 — counterfactuals were evaluated under different semantics than the original

`explain_hyper.py` built every counterfactual as `tr.Trace(); set_values(rows)` with no
`set_lasso`. `Trace.lasso` fell back to the class-level default `[]`, so `is_liveness()` was
`False` for counterfactuals even when the counterexample was a lasso.

Since `highlighter.run` only seeds accepting (`G`/`R`/`W`) nodes when the trace loops, and
`altautomaton.Node.get_result_at` returns `ff()` past the end, `G φ` is false at the horizon
and false everywhere by backward induction. The original and its counterfactuals were
therefore judged under two different logics.

**Fixed** by `make_counterfactual_trace`, which gives the counterfactual the same
prefix/lasso split and the same `TraceSemantics` as the counterexample it came from.
Effect on `security_in_and_out`: **8 singleton causes → 3 causes of size 2**, with a real
subset search (25–45 `True` verdicts, varying run to run — see the caveat below).

## Defect 2 — a flat counterexample is not recognised as a violation

For a trace with no loop, `check_formula(original counterexample)` returns **False** on 5 of
9 examples. The negated spec for `G A → G B` is `G A ∧ F ¬B`; the `G A` conjunct is
unsatisfiable on a finite trace, so the tool does not see its own counterexample as
violating. The **SAT** condition of the Halpern–Pearl definition fails before any causal
reasoning starts.

`TraceSemantics.FINITE_WEAK` reads the horizon as "nothing further observed" and seeds the
accepting nodes. Behind `-finiteSemantics weak` it repairs `running_example`
(`check_formula(orig)` False → **True**). Four examples — `drone_example_1`,
`drone_example_2`, `asymmetric_arbiter_19`, `leaky_mux` — **still** report False under
`weak` and need separate investigation: most likely their `F ¬B` witness or their `G A`
antecedent does not hold on the recorded prefix.

## Correction: `#causes == |C~|` is *not* by itself evidence of degeneracy

An earlier draft of this note treated every `#causes == |C~|` row as degenerate. That is too
strong. Instrumenting `asymmetric_arbiter` by flipped AP gives:

| flipped AP | counterfactuals | `check_formula` True |
|---|---|---|
| `req_0` | 36 | 0 |
| `req_1` | 30 | 0 |
| `tb_secret` | 6 | 0 |

Two different things are happening, and only one is a bug:

- Flipping `req_0`/`req_1` in **one** trace falsifies the antecedent `G(req equal)`, so the
  implication holds vacuously and the violation counts as "resolved". Whether that should
  qualify as a cause is a question about the paper's definition of `intervene(Γ, C′, W)`,
  **not** a code defect.
- Flipping `tb_secret` does not touch the antecedent, and genuinely resolves the grant
  divergence. `tb_secret` is the leaking input, so these singletons look like the
  semantically expected answer.

So `asymmetric_arbiter`'s 24 singletons survive the Defect-1 fix and may well be legitimate.
The claim that stands is narrower: **defects 1 and 2 are real, and 5 of 9 examples fail the
SAT condition outright.**

## Caveat: results are not run-to-run stable

`security_in_and_out` reported 25 `True` verdicts on one run and 45 on the next with
identical code. The cause *count* was stable at 3. This is the `AGraph.get_edge` parallel-edge
nondeterminism already recorded in README.md, and it means exact call counts cannot be used
as regression signals — only cause sets and cause counts.

## Changes made

- `explainhyper/trace.py` — instance attributes (was class-level mutable defaults),
  `TraceSemantics`, `accepting_holds_at_end()`, `latch_state_at()`, `detect_lasso()`.
- `explainhyper/highlighter.py:95` — gate on `accepting_holds_at_end()` instead of
  `is_liveness()`. Verified a strict no-op: metrics byte-identical before/after.
- `explainhyper/explain_hyper.py` — `make_counterfactual_trace()` (defect 1, on by default),
  `_finite_semantics()` + `-finiteSemantics` flag (defect 2, **off** by default).

Defaults reproduce historical behaviour except for defect 1, which changes
`security_in_and_out` from 8 causes to 3.
