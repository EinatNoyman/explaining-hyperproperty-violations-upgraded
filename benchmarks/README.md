# Benchmarks

## `hyperqb/` — the HyperQB 2.0 benchmark suite

Copied verbatim from the HyperQB 2.0 artifact:

- source: <https://github.com/HyperQB/HyperRUSTY> (`benchmarks/`)
- paper: Hsu, Rabizadeh, Rogale, Filippov, de Oliveira Batista, Bonakdarpour.
  *HyperQB 2.0: A Bounded Model Checker for Hyperproperties.* CAV 2026,
  LNCS 16682, pp. 511-525. <https://doi.org/10.1007/978-3-032-32519-8_26>
- Zenodo archive: <https://zenodo.org/records/20085800>
- case-study write-ups: <https://hyperqb.github.io/case-studies>
- licence: MIT, (c) 2025 Borzoo Bonakdarpour, Tzu-Han Hsu (see `hyperqb/LICENSE`)

441 files, ~43 MB. Nothing was modified; only `.DS_Store` was dropped.

### Layout, and how it maps onto the paper

| directory | paper | contents |
|---|---|---|
| `sync/` | **Table 1** — HyperLTL | 24 case studies, `0_infoflow` .. `23_lazy_list`, plus `AH_formulas` |
| `async/` | **Table 2** — A-HLTL | `1_acdb`, `2_concleaks`, `3_speculative`, `4_optimization`, `5_cache` |
| `loop_conditions/` | **Table 3** — programs with loops | `abp`, `cbf`, `gcw`, `mm`, `robust_path_planning`, `simple_loop` |
| `verilog/` | **Table 4** — hardware security | `LED`, `SPI`, `divider` (FPU), `bakery`, `ethernet` |
| `temp/` | — | scratch copies of some `sync/` cases; not referenced by the paper |

File counts: 176 `.smv`, 143 `.hq`, 51 `.v`, 12 `.aag`, 12 `.aig`, 7 `.ys`, 4 `.cex`.

### Size note

41 of the 43 MB sits in `verilog/`, in a few large derived artifacts — a 20 MB
`.mv`, a 7.5 MB `.blif`, plus `.aig`, `.pdf` and `.doc`. The models and formulas
themselves are about 1.8 MB. To keep only those:

```bash
find benchmarks/hyperqb -type f \
     ! -name '*.smv' ! -name '*.hq' ! -name '*.v' ! -name '*.ys' \
     ! -name 'LICENSE' -delete
find benchmarks/hyperqb -type d -empty -delete
```

### Coverage by our NuSMV interpreter

`explainhyper/smv.py` implements a deliberately small fragment. Against the
176 `.smv` models here:

| | count | share |
|---|---|---|
| parse OK | 90 | 51% |
| outside the supported fragment | 68 | 39% |
| other parse failure | 18 | 10% |

The gaps, in order of how many files they unlock:

| missing feature | files | difficulty |
|---|---|---|
| `mod` operator | 26 | easy |
| ranges not starting at 0 (`1..3`) | ~20 | easy |
| `*` (multiplication) | 8 | easy |
| `->` inside expressions | 2 | easy |
| arrays (`v[0]: 0..1`) | ~5 | harder |

Adding the four easy ones would take coverage from 51% to roughly 85%. Every
unsupported construct raises `SmvUnsupportedError` rather than being silently
mis-executed, so the 51% is a floor that can be trusted, not an estimate.

### Using one of these with this tool

The `-frontend hyperqb` and `-frontend autohyper` paths both take a NuSMV
model. They also need an `-aag` as the executable model for counterfactual
simulation, and a `-stateMachine` DOT for candidate causes -- see
`FRONTENDS.md`.
