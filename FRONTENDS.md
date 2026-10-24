# Running the three model-checker front ends

Every command here has been run and produced the output shown.

## Setup (once per shell)

```bash
conda activate hyper
cd examples/running_example
```

All three commands below use the **same** system, the **same** `-f`, and the
same DOT. Only `-frontend` changes.

```bash
F='Forall (Forall (G (Eq (AP "lo" 0) (AP "lo" 1))))'
```

Observational determinism: the low output `lo` must agree on any two runs. It
fails, because `lo` follows the high input `hi`.

---

## 1. MCHyper — the original path

```bash
python ../../explainhyper/explain_hyper.py \
  -frontend mchyper \
  -aag running_example.aag \
  -cex running_example.cex \
  -f "$F" \
  -outName /tmp/re_mc \
  -stateMachine running_example.dot
```

```
All minimal causes (forall C): [[('hi', 0, 0, 0)], [('hi', 0, 1, 1)]]
Number of minimal causes (# C): 2
```

`-frontend mchyper` is the default and can be omitted.

---

## 2. AutoHyper — lasso-shaped counterexample

Offline, against the recorded witness checked into the repo:

```bash
python ../../explainhyper/explain_hyper.py \
  -frontend autohyper \
  -aag running_example.aag \
  -autohyperWitness ../../tests/fixtures/autohyper/running_example_od.witness.txt \
  -f "$F" \
  -outName /tmp/re_ah \
  -stateMachine running_example.dot \
  -maxCauseSize 2
```

```
All minimal causes (forall C): [[('hi', 1, 0, 0)], [('hi', 1, 1, 1)],
                                [('hi', 0, 0, 0), ('hi', 0, 0, 1)]]
Number of minimal causes (# C): 3
```

To invoke AutoHyper live instead of reading the recorded run:

```bash
export PATH="$HOME/.dotnet:$PATH"
python ../../explainhyper/explain_hyper.py \
  -frontend autohyper \
  -aag running_example.aag \
  -autohyperBin "$HOME/opt/AutoHyper/app/AutoHyper.dll" \
  -autohyperSystem running_example.smv \
  -f "$F" -outName /tmp/re_ah -stateMachine running_example.dot -maxCauseSize 2
```

`-autohyperSystem` takes one file per quantifier; give it once and it is reused
for all of them.

---

## 3. HyperQB 2.0 — bounded, flat counterexample

```bash
python ../../explainhyper/explain_hyper.py \
  -frontend hyperqb \
  -aag running_example.aag \
  -hyperqbOutput ../../tests/fixtures/hyperqb/running_example_od.txt \
  -f "$F" \
  -outName /tmp/re_hq \
  -stateMachine running_example.dot \
  -finiteSemantics weak
```

```
All minimal causes (forall C): [[('hi', 0, 0, 1)], [('hi', 0, 1, 0), ('hi', 1, 1, 1)]]
Number of minimal causes (# C): 2
```

**`-finiteSemantics weak` is required.** HyperQB's traces are flat (no lasso).
Under the default `strong`, `G` is false at the horizon and the counterexample
is not recognised as a violation at all -- see STAGE0-FINDING.md. The front end
warns if you forget.

Live invocation:

```bash
export LD_LIBRARY_PATH=/tmp/z3-4.12.2-x64-glibc-2.31/bin:$LD_LIBRARY_PATH
python ../../explainhyper/explain_hyper.py \
  -frontend hyperqb \
  -aag running_example.aag \
  -hyperqbBin "$HOME/opt/HyperRUSTY/target/release/HyperRUSTY" \
  -hyperqbModel running_example.smv \
  -hyperqbK 4 -hyperqbSemantics pes \
  -f "$F" -outName /tmp/re_hq -stateMachine running_example.dot -finiteSemantics weak
```

---

## The same three on simple_buffer

`simple_buffer` is the smallest example (1 input, 1 latch, 1 output) and shows
the checker-dependence effect most clearly.

```bash
cd ../simple_buffer
F='Forall (Forall (G (Eq (AP "out" 0) (AP "out" 1))))'

python ../../explainhyper/explain_hyper.py -frontend mchyper \
  -aag simple_buffer.aag -cex simple_buffer.cex \
  -f "$F" -outName /tmp/sb_mc -stateMachine simple_buffer.dot

python ../../explainhyper/explain_hyper.py -frontend hyperqb \
  -aag simple_buffer.aag \
  -hyperqbOutput ../../tests/fixtures/hyperqb/simple_buffer_od.txt \
  -f "$F" -outName /tmp/sb_hq -stateMachine simple_buffer.dot -finiteSemantics weak

python ../../explainhyper/explain_hyper.py -frontend autohyper \
  -aag simple_buffer.aag \
  -autohyperWitness ../../tests/fixtures/autohyper/simple_buffer_od.witness.txt \
  -f "$F" -outName /tmp/sb_ah -stateMachine simple_buffer.dot -maxCauseSize 2
```

| front end | counterexample | causes |
|---|---|---|
| MCHyper | 2 steps, lasso | 2, each **1 event** |
| HyperQB | 5 steps, flat | 2, each **4 events** |
| AutoHyper | 15 steps, lasso | none of size <= 2 |

Same system, same property. The cause is the same story at three resolutions:
its size tracks the length of the counterexample, which is a property of the
model checker. See the discussion in STAGE0-FINDING.md.

---

## Toolchain (only needed for live invocation)

| tool | where | note |
|---|---|---|
| .NET 8 | `~/.dotnet` | `dotnet-install.sh --channel 8.0` |
| AutoHyper | `~/opt/AutoHyper/app` | needs `git submodule update --init`; `paths.json` points at conda spot |
| Rust | `~/.cargo` | rustup |
| HyperQB | `~/opt/HyperRUSTY/target/release/HyperRUSTY` | needs `LIBCLANG_PATH`, `Z3_SYS_Z3_HEADER`, and **Z3 built for glibc 2.31** (4.13's glibc-2.35 build will not link on Ubuntu 20.04) |

## Writing an SMV twin for a new example

AutoHyper and HyperQB need a NuSMV model; the `-aag` stays as the executable
model for counterfactual simulation. Two things to know:

- A **nondeterministic assignment is an input**: `init(hi) := {TRUE, FALSE};`
  with the same for `next`. AutoHyper requires `{TRUE,FALSE}`, not `{0,1}`.
- Prefer `case ... esac` with explicit `(x = TRUE)` comparisons over
  `!(a & b & c)`. HyperQB's dialect evaluated the negated-conjunction form
  differently from py-aiger; the front end's consistency check caught it, but
  it is easier to avoid.

The consistency check compares every value the checker reports against
simulating the `-aag`, and warns on the first disagreement. A clean run means
the two models agree step for step.
