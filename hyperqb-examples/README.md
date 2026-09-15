# HyperQB 2.0 reference examples

Fetched from https://github.com/HyperQB/HyperRUSTY (`benchmarks/`).
Reference material for evaluating HyperQB as a replacement front end for MCHyper.

Playground: https://hyperqb.egr.msu.edu/

**A formula with N quantifiers needs N model files** — paste the same model twice
for a 2-quantifier formula (CLI: `-n info.smv info.smv`).

| Folder | Logic | Settings | Expected |
|---|---|---|---|
| `infoflow/` | forall/forall, trivial | NuSMV, k=10, hpes | `sat` (smoke test only) |
| `noninterference/` | **forall/exists** | NuSMV, k=10, hpes, +counterexample | `NI_correct` holds, `NI_incorrect` violated |
| `verilog-divider/` | forall/forall | Verilog, top=`divider`, k=8, pes | `unsat` |

`NI_correct.smv` vs `NI_incorrect.smv` differ in exactly three lines:

    correct:    init(PIN_2):={1};  init(PIN_1):={1,0};  init(PIN_0):={1,0};
    incorrect:  init(PIN_2):={0};  init(PIN_1):={0};    init(PIN_0):={1};

The correct version leaves the low PIN bits nondeterministic, so a witness trace B
with a different PIN exists. The incorrect version fixes the secret to 001, so no
witness exists and the forall/exists property fails.

## Open questions to answer by running these

1. Does violation show up as `sat` or `unsat`? (docs are contradictory; Table 1 of
   the paper says NI_correct is OK and NI_incorrect is buggy — use that as ground truth)
2. Does Verilog input take `.v` or the Yosys script `.ys`?
3. Is the counterexample a lasso or a flat k-step prefix?
4. Does the counterexample include outputs, or only inputs?
5. Is there a copyable text form, or only the graphical view?
