#!/usr/bin/env python3
"""Compare the model checkers over the HyperQB benchmark suite. CSV + LaTeX.

Two independent comparisons, because they answer different questions:

  MODEL CHECKING -- how long does each checker take to decide each benchmark,
      and what verdict does it give? Invocations are lifted verbatim from the
      HyperQB authors' own run_*.sh (all five of them, 80 cases), so the
      comparison matches their published table rather than flags we invented.
      Note they use a *different* formula file for AutoHyper (AH_formulas/)
      because the syntaxes differ.

  CAUSALITY -- for the examples in this repo that have all the inputs, run the
      actual cause computation through each front end and report |C~|, the
      number and sizes of minimal causes, and the time.

The benchmark suite has .smv and .hq but no .aag and no .dot, so the causality
pipeline cannot run on it: it needs an executable model for counterfactual
simulation and a DOT transition system for candidate causes. That is why the
two comparisons cover different sets.

Output in --out (default tools/_bench_out/):

  checkers.csv     long:  one row per (benchmark, checker)
                          result | success | time_s | status | reason
  comparison.csv   wide:  one row per benchmark, checkers side by side,
                          plus `agree` (do the checkers concur?) and `fastest`
  causality.csv    long:  one row per (example, front end)
  results.json     everything, unformatted
  table_*.tex      the same two tables for Overleaf

`result` is the checker's verdict: **unsat means the property is violated**
(HyperQB is a bounded checker asking whether a violating unrolling exists).
`success` is whether the run decided at all -- a timeout or a crash is
success=no, and `reason` then says which.

Usage:
    python tools/run_benchmarks.py --light              # the fast cases
    python tools/run_benchmarks.py --timeout 1800       # everything
    python tools/run_benchmarks.py --only bakery,ni
    python tools/run_benchmarks.py --suites hltl_1,hltl_2
"""

import argparse
import csv
import json
import os
import re
import shlex
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(REPO, "explainhyper"))

DEFAULT_HQ_REPO = os.path.expanduser("~/opt/HyperRUSTY")
DEFAULT_OUT = os.path.join(HERE, "_bench_out")

# Cases the authors themselves exclude from the quick run.
HEAVY = {"bakery9", "bakery11", "rb1600", "rb3600", "sp400", "sp1600", "sp3600"}

# The authors' five driver scripts and the benchmark folder each one assumes.
# Every script hardcodes FOLDER at the top; we mirror it here rather than
# parsing it, so a case's paths resolve the same way they do upstream.
SUITES = (
    ("hltl_1", "run_hltl_1.sh", "benchmarks/sync/"),
    ("hltl_2", "run_hltl_2.sh", "benchmarks/sync/"),
    ("ahltl", "run_ahltl.sh", "benchmarks/async/"),
    ("loopcond", "run_loopcond.sh", "benchmarks/loop_conditions/"),
    ("verilog", "run_verilog.sh", "benchmarks/verilog/"),
)


# ---------------------------------------------------------------- extraction

_CASE = re.compile(r"^case_([a-z0-9_]+)\(\)\s*\{", re.M)
_NAME = re.compile(r'local case_name="([^"]+)"')
_TIMED = re.compile(r'time_run\s+"[^"]*"\s+"([A-Za-z_]+)"\s*\\?\s*\n\s*"(.*?)"', re.S)


def extract_cases(script_path, folder):
    """Parse one of the authors' run_*.sh into {case: {variant: argv}}."""
    with open(script_path) as handle:
        text = handle.read()
    starts = [(m.group(1), m.start()) for m in _CASE.finditer(text)]
    cases = {}
    for i, (key, start) in enumerate(starts):
        end = starts[i + 1][1] if i + 1 < len(starts) else len(text)
        body = text[start:end]
        name = _NAME.search(body)
        variants = {}
        for variant, command in _TIMED.findall(body):
            if variant.endswith("_witness"):
                continue                      # verification-only table
            command = command.replace("\\\n", " ").replace("${FOLDER}", folder)
            command = command.replace("${CARGO_BIN}", "<HYPERQB>")
            command = re.sub(r"\s+", " ", command).strip()
            variants[variant] = shlex.split(command)
        if variants:
            cases[key] = {"name": name.group(1) if name else key,
                          "variants": variants}
    return cases


# ------------------------------------------------------------------- running

def first_error_line(output):
    """The most informative single line of a failed run, for the CSV."""
    for pattern in (r"^.*\bpanicked at.*$", r"^.*\bERROR\b.*$", r"^.*\berror\b.*$",
                    r"^.*\bException\b.*$", r"^.*\bnot found\b.*$"):
        match = re.search(pattern, output, re.M)
        if match:
            return re.sub(r"\s+", " ", match.group(0)).strip()[:160]
    tail = [line for line in output.strip().splitlines() if line.strip()]
    return re.sub(r"\s+", " ", tail[-1]).strip()[:160] if tail else "no output"


def run(argv, timeout, cwd=None, env=None):
    """Run a command, returning (verdict, seconds, status, reason)."""
    started = time.monotonic()
    try:
        done = subprocess.run(argv, capture_output=True, text=True,
                              timeout=timeout, cwd=cwd, env=env)
    except subprocess.TimeoutExpired:
        return None, timeout, "TO", "timeout after %gs" % timeout
    except (OSError, MemoryError) as exc:
        return None, time.monotonic() - started, "ERR", "%s: %s" % (type(exc).__name__, exc)
    elapsed = time.monotonic() - started
    output = done.stdout + done.stderr
    match = re.search(r"^\s*result:\s*(sat|unsat|unknown)", output, re.M | re.I)
    if match is None:
        match = re.search(r"^\s*(SAT|UNSAT|UNKNOWN)\s*$", output, re.M)
    if match is None:
        # No verdict line at all: the run did not decide anything. Say why --
        # a missing QuAbS binary and a solver crash are very different results
        # and a bare ERR hides the difference.
        return None, elapsed, "ERR", first_error_line(output)
    return match.group(1).lower(), elapsed, "ok", ""


def checker_table(args, cases, env, suite=""):
    rows = []
    for key in sorted(cases):
        if args.only and not any(p in key for p in args.only):
            continue
        if args.light and key in HEAVY:
            continue
        entry = cases[key]
        if args.pairs_only and not {"SMT", "AH"} <= set(entry["variants"]):
            # AutoHyper has no variant upstream in the async, loop-condition or
            # Verilog suites, so only 35 of the 80 cases are head-to-head
            # comparable at all. Including the rest produces half-empty rows
            # that read as failures rather than as "not applicable".
            continue
        row = {"case": entry["name"], "key": key, "suite": suite}
        for variant, argv in sorted(entry["variants"].items()):
            if variant == "QBF" and not args.with_qbf:
                # Record it rather than dropping it. Several benchmarks are
                # QBF-only, and silently skipping them leaves a blank row that
                # is indistinguishable from a crash.
                row[variant] = {"verdict": None, "seconds": 0.0,
                                "status": "skipped",
                                "reason": "QBF backend not run; pass --with-qbf"}
                continue
            argv = list(argv)
            if argv[0] == "<HYPERQB>":
                argv[0] = args.hyperqb_bin
            elif "AutoHyper" in argv[0]:
                argv = ([args.dotnet, args.autohyper_dll]
                        if args.autohyper_dll else [argv[0]]) + argv[1:]
            # Repeat and take the median. Two identical passes earlier in this
            # project disagreed on how many cases timed out (20 vs 11), purely
            # from machine load, so a single sample is not a measurement.
            samples = []
            for _ in range(max(1, args.repeat)):
                verdict, seconds, status, reason = run(argv, args.timeout,
                                                       cwd=args.hyperqb_repo, env=env)
                samples.append((verdict, seconds, status, reason))
                if status != "ok":
                    break        # no point re-timing a timeout or a crash
            times = sorted(sample[1] for sample in samples)
            verdict, _, status, reason = samples[-1]
            seconds = times[len(times) // 2]
            row[variant] = {"verdict": verdict, "seconds": seconds,
                            "status": status, "reason": reason,
                            "runs": len(samples),
                            "t_min": min(times), "t_max": max(times)}
            print("  %-14s %-4s %-7s %8.2fs  %s"
                  % (entry["name"], variant, verdict or status, seconds,
                     reason if status != "ok" else ""))
        rows.append(row)
    return rows


# ----------------------------------------------------------------- causality

CAUSE_LINE = re.compile(r"^All minimal causes \(forall C\): (.*)$", re.M)
COUNT_LINE = re.compile(r"^Number of minimal causes \(# C\): (\d+)$", re.M)
CTILDE_LINE = re.compile(r"^for trace \d+: (\[.*\])$", re.M)

# explain_hyper.py prints these as a label line followed by the number on the
# next line (see explainhyper/explain_hyper.py: actual_causality/main). Each
# one isolates a phase of the run, so a frontend's checker-invocation time
# never gets silently folded into the causality algorithm's own time:
#   GAMMA     -- front end total: checker run (if live) + parse + simulate
#   CHECKER   -- just the model checker subprocess, i.e. time to find/refute
#                the counterexample; 0 for offline witnesses and for mchyper
#                (whose checker never runs inside this tool at all)
#   CTILDE    -- candidate-cause computation (unsat cores / DOT minimization)
#   SEARCH    -- the minimality search over subsets of C~
#   TOTAL     -- the whole actual_causality() call, timed by main()
GAMMA_LINE = re.compile(
    r"^Time to obtain the counterexample \(time\(Gamma\)\):\n([0-9.eE+-]+)", re.M)
CHECKER_LINE = re.compile(
    r"^Time spent in the model checker itself \(time\(checker\)\):\n([0-9.eE+-]+)", re.M)
CTILDE_TIME_LINE = re.compile(
    r"^Time to compute this set of causes \(time\(C tilde\)\):\n([0-9.eE+-]+)", re.M)
SEARCH_TIME_LINE = re.compile(
    r"^The time of the minimality search \(time\(search\)\):\n([0-9.eE+-]+)", re.M)
TOTAL_TIME_LINE = re.compile(
    r"^The time to compute all causes \(time\(forall C\)\) took: \n([0-9.eE+-]+)", re.M)


def causality_table(args, env):
    """Run the cause computation through every (front end, solver) pair that
    has its inputs. Two independent axes, crossed: the front end supplies the
    counterexample (mchyper/autohyper/hyperqb), the solver computes causes
    from it (cvc5/pysat, -solver). Both are plain explain_hyper.py flags, so
    pysat gets the same 3 front ends as cvc5 -- unlike diffing git commits,
    where the old PySAT code predates the front-end system entirely."""
    from conftest_formulas import FORMULAS

    rows = []
    examples = os.path.join(REPO, "examples")
    for name in sorted(os.listdir(examples)):
        directory = os.path.join(examples, name)
        if not os.path.isdir(directory) or name not in FORMULAS:
            continue
        if args.only and not any(p in name for p in args.only):
            continue
        aag = os.path.join(directory, name + ".aag")
        dot = os.path.join(directory, name + ".dot")
        cex = os.path.join(directory, name + ".cex")
        smv = os.path.join(directory, name + ".smv")
        if not (os.path.exists(aag) and os.path.exists(dot)):
            continue

        row = {"example": name}
        plans = []
        if os.path.exists(cex):
            plans.append(("mchyper", ["-frontend", "mchyper", "-cex", cex]))
        if os.path.exists(smv) and args.autohyper_dll:
            plans.append(("autohyper", [
                "-frontend", "autohyper", "-autohyperSystem", smv,
                "-autohyperBin", args.autohyper_dll,
                "-maxCauseSize", str(args.max_cause_size)]))
        if os.path.exists(smv) and os.path.exists(args.hyperqb_bin):
            plans.append(("hyperqb", [
                "-frontend", "hyperqb", "-hyperqbModel", smv,
                "-hyperqbBin", args.hyperqb_bin,
                "-hyperqbK", str(args.k), "-hyperqbSemantics", "pes",
                "-finiteSemantics", "weak",
                "-maxCauseSize", str(args.max_cause_size)]))

        for frontend, extra in plans:
            for solver in args.solvers:
                key = "%s+%s" % (frontend, solver)
                argv = [sys.executable, os.path.join(REPO, "explainhyper", "explain_hyper.py"),
                        "-aag", aag, "-f", FORMULAS[name],
                        "-outName", os.path.join(args.out, "%s_%s_%s" % (name, frontend, solver)),
                        "-stateMachine", dot, "-solver", solver] + extra
                note = ""
                started = time.monotonic()
                try:
                    done = subprocess.run(argv, capture_output=True, text=True,
                                          timeout=args.timeout, cwd=directory, env=env)
                    output, status = done.stdout + done.stderr, "ok"
                except subprocess.TimeoutExpired:
                    done, output, status = None, "", "TO"
                    note = "timeout after %gs" % args.timeout
                elapsed = time.monotonic() - started
                if status == "ok" and done.returncode != 0:
                    # explain_hyper exits 2 on FrontEndError with `error: <what>`.
                    # The message is often multi-line -- a FrontEndError that
                    # quotes the checker's own output puts the useful part on the
                    # *second* line -- so take the whole tail, not just line one.
                    match = re.search(r"^error: (.*)\Z", output, re.M | re.S)
                    status = "ERR"
                    note = (re.sub(r"\s+", " ", match.group(1)).strip()[:160] if match
                            else first_error_line(output))

                count = COUNT_LINE.search(output)
                causes = CAUSE_LINE.search(output)
                ctilde = sum(len(eval(m)) for m in CTILDE_LINE.findall(output)) or None
                sizes = None
                if causes:
                    try:
                        sizes = sorted({len(c) for c in eval(causes.group(1))}) or None
                    except Exception:
                        pass
                # A run can succeed and still find nothing. That is a result, not an
                # error, but it needs saying -- otherwise the CSV shows a blank that
                # looks like a crash. The usual reason is the cap.
                if status == "ok" and not sizes:
                    note = note or ("no cause of size <= %d" % args.max_cause_size)

                def grab(pattern):
                    m = pattern.search(output)
                    return float(m.group(1)) if m else None

                gamma_s = grab(GAMMA_LINE)
                checker_s = grab(CHECKER_LINE)
                ctilde_s = grab(CTILDE_TIME_LINE)
                search_s = grab(SEARCH_TIME_LINE)
                total_s = grab(TOTAL_TIME_LINE)
                # "time to find the counterexample": the checker's own decision
                # time when it actually ran inside this process (live AutoHyper/
                # HyperQB); otherwise gamma_s is just parse+simulate of an
                # already-produced witness/cex, which is not "finding" anything.
                counterexample_s = checker_s if checker_s else (
                    gamma_s if (gamma_s and checker_s is None) else 0.0)
                # "time to compute the cause, once Gamma is in hand": whatever
                # of the total wasn't spent obtaining Gamma. Falls back to the
                # wall-clock elapsed (includes process startup) if a run
                # crashed or timed out before printing its own timings.
                causality_s = ((total_s - gamma_s) if (total_s is not None and gamma_s is not None)
                              else None)

                row[key] = {"frontend": frontend, "solver": solver,
                           "ctilde": ctilde,
                           "causes": int(count.group(1)) if count else None,
                           "sizes": sizes, "seconds": elapsed,
                           "counterexample_s": counterexample_s,
                           "causality_s": causality_s,
                           # finer breakdown of causality_s, for results.json only:
                           # candidate-cause computation vs. the minimality search.
                           "ctilde_s": ctilde_s, "search_s": search_s,
                           "total_s": total_s if total_s is not None else elapsed,
                           "status": status, "note": note}
                print("  %-22s %-9s %-6s ctilde=%-5s causes=%-5s sizes=%-8s "
                      "cex=%6ss cause=%6ss total=%6ss %s%s"
                      % (name, frontend, solver, ctilde, count.group(1) if count else "-",
                         sizes,
                         ("%.2f" % counterexample_s) if counterexample_s is not None else "-",
                         ("%.2f" % causality_s) if causality_s is not None else "-",
                         ("%.2f" % elapsed),
                         "" if status == "ok" else status,
                         ("  " + note) if note else ""))
        if len(row) > 1:
            rows.append(row)
    return rows


# ----------------------------------------------------------------------- CSV

# The variant keys in the authors' scripts are terse; spell them out so the CSV
# is readable on its own, away from this script.
CHECKER_NAMES = {"SMT": "HyperQB-SMT", "QBF": "HyperQB-QBF", "AH": "AutoHyper"}


def write_csv(path, columns, rows):
    with open(path, "w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=columns, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)
    return path


def csv_checkers(rows):
    """Long format: one row per (benchmark, checker). The shape to pivot from."""
    out = []
    for row in rows:
        for variant in ("SMT", "QBF", "AH"):
            cell = row.get(variant)
            if cell is None:
                continue
            out.append({
                "suite": row.get("suite", ""),
                "benchmark": row["case"],
                "case_key": row["key"],
                "checker": CHECKER_NAMES.get(variant, variant),
                # result: what the checker decided. unsat == property violated.
                "result": cell["verdict"] or "",
                # success: did it decide at all, within the timeout?
                "success": "yes" if cell["status"] == "ok" else "no",
                "status": cell["status"],
                "time_s": ("" if cell["status"] == "skipped"
                           else "%.3f" % cell["seconds"]),
                "runs": cell.get("runs", ""),
                "t_min_s": ("%.3f" % cell["t_min"]) if "t_min" in cell else "",
                "t_max_s": ("%.3f" % cell["t_max"]) if "t_max" in cell else "",
                "reason": cell.get("reason", ""),
            })
    return out


def csv_comparison(rows):
    """Wide format: one row per benchmark, checkers side by side."""
    out = []
    for row in rows:
        record = {"suite": row.get("suite", ""), "benchmark": row["case"],
                  "case_key": row["key"]}
        verdicts = []
        for variant in ("SMT", "QBF", "AH"):
            cell = row.get(variant)
            name = CHECKER_NAMES.get(variant, variant)
            if cell is None:
                record["result_" + name] = ""
                record["time_s_" + name] = ""
                record["success_" + name] = ""
                continue
            record["result_" + name] = cell["verdict"] or cell["status"]
            record["time_s_" + name] = ("" if cell["status"] == "skipped"
                                        else "%.3f" % cell["seconds"])
            record["success_" + name] = "yes" if cell["status"] == "ok" else "no"
            if cell["verdict"]:
                verdicts.append(cell["verdict"])
        # Cross-validation: independent checkers on the same benchmark should
        # reach the same verdict. A "no" here is a bug in someone's tool.
        record["agree"] = ("" if len(verdicts) < 2
                           else "yes" if len(set(verdicts)) == 1 else "NO")
        times = [(row[v]["seconds"], CHECKER_NAMES.get(v, v))
                 for v in ("SMT", "QBF", "AH")
                 if row.get(v) and row[v]["status"] == "ok"]
        record["fastest"] = min(times)[1] if times else ""
        record["note"] = "" if times else "no checker decided this benchmark"

        # Head-to-head HyperQB(SMT) vs AutoHyper -- the actual point of a
        # two-way report. Only defined where both decided; a timeout has a
        # time but not a comparable one, so the ratio is left blank and the
        # winner recorded as the one that finished.
        smt, ah = row.get("SMT"), row.get("AH")
        ratio, winner, margin = "", "", ""
        if smt and ah:
            smt_ok, ah_ok = smt["status"] == "ok", ah["status"] == "ok"
            if smt_ok and ah_ok:
                winner = "HyperQB-SMT" if smt["seconds"] <= ah["seconds"] else "AutoHyper"
                if min(smt["seconds"], ah["seconds"]) > 0:
                    ratio = "%.2f" % (ah["seconds"] / smt["seconds"])
                    margin = "%.2f" % (max(smt["seconds"], ah["seconds"])
                                       / min(smt["seconds"], ah["seconds"]))
            elif smt_ok != ah_ok:
                winner = "HyperQB-SMT" if smt_ok else "AutoHyper"
                margin = "only one finished"
        record["ah_over_smt"] = ratio
        record["faster"] = winner
        record["margin"] = margin
        out.append(record)
    return out


def csv_causality(rows):
    """One row per (example, front end, solver): the cause computation, not
    the check. time_s is the same wall-clock total as before; counterexample_s
    and causality_s split it into 'time to obtain Gamma' and 'time to compute
    the cause from it' -- see the GAMMA_LINE/CHECKER_LINE comment above."""
    out = []
    for row in rows:
        for key, cell in row.items():
            if key == "example" or not isinstance(cell, dict) or "frontend" not in cell:
                continue
            out.append({
                "example": row["example"],
                "frontend": cell["frontend"],
                "solver": cell["solver"],
                # result: how many minimal causes were found, and of what size.
                "result": "" if cell["causes"] is None else cell["causes"],
                "cause_sizes": ";".join(map(str, cell["sizes"] or [])),
                "candidate_set_size": "" if cell["ctilde"] is None else cell["ctilde"],
                "success": "yes" if (cell["status"] == "ok" and cell["causes"]) else "no",
                "status": cell["status"],
                "time_s": "%.3f" % cell["seconds"],
                "counterexample_s": ("%.3f" % cell["counterexample_s"])
                                    if cell["counterexample_s"] is not None else "",
                "causality_s": ("%.3f" % cell["causality_s"])
                               if cell["causality_s"] is not None else "",
                "reason": cell.get("note", ""),
            })
    return out


CSV_CHECKER_COLUMNS = ["suite", "benchmark", "case_key", "checker",
                       "result", "success", "time_s", "status",
                       "runs", "t_min_s", "t_max_s", "reason"]
CSV_CAUSALITY_COLUMNS = ["example", "frontend", "solver", "result", "success",
                         "time_s", "counterexample_s", "causality_s",
                         "cause_sizes", "candidate_set_size", "status", "reason"]


def csv_comparison_columns(rows):
    names = [CHECKER_NAMES[v] for v in ("SMT", "QBF", "AH")]
    columns = ["suite", "benchmark", "case_key"]
    for name in names:
        columns += ["result_" + name, "success_" + name, "time_s_" + name]
    return columns + ["agree", "faster", "ah_over_smt", "margin",
                      "fastest", "note"]


# --------------------------------------------------------------------- LaTeX

def fmt_time(cell):
    if cell is None:
        return "--"
    if cell["status"] == "TO":
        return r"\to"
    if cell["status"] != "ok":
        return r"\err"
    return "%.2f" % cell["seconds"]


def fmt_verdict(cell):
    if cell is None or cell["verdict"] is None:
        return "--"
    return r"\unsat" if cell["verdict"] == "unsat" else r"\sat"


def agreement(rows):
    """Where both checkers decided, do they agree? A free cross-check."""
    both, same = 0, 0
    for row in rows:
        a, b = row.get("SMT"), row.get("AH")
        if a and b and a["verdict"] and b["verdict"]:
            both += 1
            same += (a["verdict"] == b["verdict"])
    return same, both


def latex_checkers(rows, timeout):
    out = [
        r"% Requires: \usepackage{booktabs}",
        r"\newcommand{\to}{\textsc{to}}",
        r"\newcommand{\err}{\textsc{err}}",
        r"\newcommand{\sat}{\textsc{sat}}",
        r"\newcommand{\unsat}{\textsc{unsat}}",
        r"",
        r"\begin{table}[t]",
        r"  \centering",
        r"  \caption{Model checking the HyperQB 2.0 benchmark suite. Verdict"
        r"  \unsat{} means the property is violated. Times are wall-clock"
        r"  seconds; \to{} is a timeout at %d\,s. Invocations are taken"
        r"  verbatim from the HyperQB authors' \texttt{run\_hltl\_1.sh}."
        r"  MCHyper is omitted: it is unmaintained and we could not build it,"
        r"  so only its pre-recorded counterexamples were available.}" % timeout,
        r"  \label{tab:checkers}",
        r"  \begin{tabular}{lcccc}",
        r"    \toprule",
        r"    & \multicolumn{2}{c}{HyperQB 2.0 (SMT)} & \multicolumn{2}{c}{AutoHyper} \\",
        r"    \cmidrule(lr){2-3}\cmidrule(lr){4-5}",
        r"    Benchmark & Verdict & Time (s) & Verdict & Time (s) \\",
        r"    \midrule",
    ]
    for row in rows:
        smt, ah = row.get("SMT"), row.get("AH")
        out.append(r"    %s & %s & %s & %s & %s \\"
                   % (row["case"].replace("_", r"\_"), fmt_verdict(smt),
                      fmt_time(smt), fmt_verdict(ah), fmt_time(ah)))
    same, both = agreement(rows)
    out += [r"    \bottomrule",
            r"  \end{tabular}",
            r"  \\[2pt]",
            r"  \footnotesize Where both checkers decided, the verdicts agree"
            r" in %d of %d cases." % (same, both),
            r"\end{table}"]
    return "\n".join(out)


def latex_causality(rows, max_cause_size):
    out = [
        r"\begin{table}[t]",
        r"  \centering",
        r"  \caption{Actual causes computed from each (front end, solver)"
        r"  pair. $|\tilde{C}|$ is the candidate set; sizes are the"
        r"  cardinalities of the minimal causes found. The front end supplies"
        r"  the counterexample (model-checker dependent); the solver computes"
        r"  causes from it (cvc5 vs.\ the original pysat backend). Cex (s) is"
        r"  time to obtain the counterexample, Cause (s) is time spent"
        r"  computing causes from it once obtained, Total (s) is both. The"
        r"  subset search is capped at size %d.}" % max_cause_size,
        r"  \label{tab:causality}",
        r"  \begin{tabular}{lllccccc}",
        r"    \toprule",
        r"    Example & Front end & Solver & $|\tilde{C}|$ & \#causes & Sizes"
        r" & Cex (s) & Cause (s) & Total (s) \\",
        r"    \midrule",
    ]
    for row in rows:
        first = True
        for key, cell in row.items():
            if key == "example" or not isinstance(cell, dict) or "frontend" not in cell:
                continue

            def fmt(seconds):
                if seconds is None:
                    return "--"
                return r"\to" if cell["status"] == "TO" else "%.2f" % seconds

            out.append(r"    %s & %s & %s & %s & %s & %s & %s & %s & %s \\" % (
                row["example"].replace("_", r"\_") if first else "",
                cell["frontend"], cell["solver"],
                cell["ctilde"] if cell["ctilde"] is not None else "--",
                cell["causes"] if cell["causes"] is not None else "--",
                ("$\\{%s\\}$" % ",".join(map(str, cell["sizes"])))
                if cell["sizes"] else "--",
                fmt(cell["counterexample_s"]), fmt(cell["causality_s"]),
                fmt(cell["seconds"])))
            first = False
        out.append(r"    \midrule")
    if out[-1] == r"    \midrule":
        out.pop()
    out += [r"    \bottomrule", r"  \end{tabular}", r"\end{table}"]
    return "\n".join(out)


# ---------------------------------------------------------------------- main

def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--hyperqb-repo", default=DEFAULT_HQ_REPO)
    parser.add_argument("--hyperqb-bin",
                        default=os.path.join(DEFAULT_HQ_REPO, "target/release/HyperRUSTY"))
    parser.add_argument("--autohyper-dll",
                        default=os.path.expanduser("~/opt/AutoHyper/app/AutoHyper.dll"))
    parser.add_argument("--dotnet", default=os.path.expanduser("~/.dotnet/dotnet"))
    parser.add_argument("--z3-lib", default="/tmp/z3-4.12.2-x64-glibc-2.31/bin")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--k", type=int, default=4, help="HyperQB unrolling bound")
    parser.add_argument("--max-cause-size", type=int, default=2)
    parser.add_argument("--solvers", type=lambda s: s.split(","), default=["cvc5", "pysat"],
                        help="causality solver backends to cross with every front end "
                             "(-solver on explain_hyper.py); default both cvc5,pysat. "
                             "pysat needs `pip install .[pysat]` (python-sat + satispy).")
    parser.add_argument("--only", type=lambda s: s.split(","), default=None)
    parser.add_argument("--light", action="store_true", help="skip the heavy cases")
    parser.add_argument("--repeat", type=int, default=1,
                        help="run each case N times and report the median time; "
                             "a single sample is noisy (default 1)")
    parser.add_argument("--pairs-only", action="store_true",
                        help="only cases the authors run on BOTH HyperQB and "
                             "AutoHyper (35 of 80) -- the head-to-head set")
    parser.add_argument("--suites", type=lambda s: s.split(","), default=None,
                        help="which of the authors' run_*.sh to use; default all: "
                             + ",".join(s[0] for s in SUITES))
    parser.add_argument("--with-qbf", action="store_true",
                        help="also run HyperQB's QBF backend; needs the quabs "
                             "binary in the HyperQB repo root and NuSMV on PATH")
    parser.add_argument("--out", default=DEFAULT_OUT)
    parser.add_argument("--skip-checkers", action="store_true")
    parser.add_argument("--skip-causality", action="store_true")
    args = parser.parse_args()

    # Must be absolute: the causality runs use cwd=<example dir>, so a
    # relative -outName would resolve against the example, not here.
    args.out = os.path.abspath(args.out)
    os.makedirs(args.out, exist_ok=True)
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = args.z3_lib + ":" + env.get("LD_LIBRARY_PATH", "")
    env["PATH"] = os.path.dirname(args.dotnet) + ":" + env["PATH"]
    env["PYTHONHASHSEED"] = "0"

    results = {"timeout": args.timeout, "checkers": [], "causality": []}

    if not args.skip_checkers:
        wanted = set(args.suites) if args.suites else {s[0] for s in SUITES}
        for suite, filename, folder in SUITES:
            if suite not in wanted:
                continue
            script = os.path.join(args.hyperqb_repo, filename)
            if not os.path.exists(script):
                print("no %s at %s; skipping that suite" % (filename, script))
                continue
            cases = extract_cases(script, folder)
            print("== model checking [%s]: %d cases ==" % (suite, len(cases)))
            results["checkers"] += checker_table(args, cases, env, suite=suite)

    if not args.skip_causality:
        print("== causality ==")
        results["causality"] = causality_table(args, env)

    with open(os.path.join(args.out, "results.json"), "w") as handle:
        json.dump(results, handle, indent=1)

    written = ["results.json"]
    if results["checkers"]:
        rows = csv_checkers(results["checkers"])
        write_csv(os.path.join(args.out, "checkers.csv"), CSV_CHECKER_COLUMNS, rows)
        wide = csv_comparison(results["checkers"])
        write_csv(os.path.join(args.out, "comparison.csv"),
                  csv_comparison_columns(wide), wide)
        with open(os.path.join(args.out, "table_checkers.tex"), "w") as handle:
            handle.write(latex_checkers(results["checkers"], args.timeout) + "\n")
        written += ["checkers.csv", "comparison.csv", "table_checkers.tex"]

        decided = [r for r in rows if r["success"] == "yes"]
        same, both = agreement(results["checkers"])
        disagree = [r["benchmark"] for r in wide if r["agree"] == "NO"]
        print("\n%d runs, %d decided, %d timed out, %d errored, %d skipped"
              % (len(rows), len(decided),
                 sum(r["status"] == "TO" for r in rows),
                 sum(r["status"] == "ERR" for r in rows),
                 sum(r["status"] == "skipped" for r in rows)))
        print("verdicts agree on %d of %d benchmarks decided by both checkers%s"
              % (same, both, (" -- DISAGREE: " + ", ".join(disagree)) if disagree else ""))

    if results["causality"]:
        rows = csv_causality(results["causality"])
        write_csv(os.path.join(args.out, "causality.csv"), CSV_CAUSALITY_COLUMNS, rows)
        with open(os.path.join(args.out, "table_causality.tex"), "w") as handle:
            handle.write(latex_causality(results["causality"], args.max_cause_size) + "\n")
        written += ["causality.csv", "table_causality.tex"]

    print("\nwrote %s/{%s}" % (args.out, ",".join(written)))


if __name__ == "__main__":
    main()
