#!/usr/bin/env python3
"""Compare actual causes across the three model checkers on the repo's examples.

The experiment
--------------
Same system, same formula, same causality algorithm. The ONLY thing that
varies is which model checker produced the counterexample Gamma. Halpern-Pearl
actual causality is defined relative to a counterexample -- cause(phi, T,
Gamma) -- so if different checkers return structurally different Gamma, the
computed causes can differ too. This script measures whether they do.

  MCHyper    reads examples/<name>/<name>.cex, the counterexample recorded in
             the original CAV'22 artifact. MCHyper itself is unmaintained and
             not installed here, so it is *replayed*, never run. That is sound
             for comparing causes (the .cex is a faithful recording of what the
             real tool produced) but it means MCHyper gets no checker runtime.
  AutoHyper  invoked live on <name>.smv; emits lasso-shaped counterexamples.
  HyperQB    invoked live on <name>.smv; emits flat k-step counterexamples.

The .smv files are generated from the .aag by tools/aag2smv.py and verified
equivalent by exhausting the reachable state space, so a difference in causes
cannot be blamed on the two encodings being different systems.

Reading the output
------------------
`result` is the set of minimal causes found, `cause_sizes` their cardinalities.
A blank result with status=ok is not a crash: it means no cause of size <=
--max-cause-size was found within the timeout. Both limits are recorded in
every row, because "no cause" is only meaningful relative to them.

The subset search is exponential in |C~|, so a cap is unavoidable. It is
applied EQUALLY to all three checkers -- an uncapped MCHyper against a capped
AutoHyper would manufacture a difference that is an artifact of the harness
rather than of the checkers. Where a known cause exceeds the cap the row is
flagged `cap_binding=yes`, so a missing result is never read as a real absence.

Usage:
    python tools/compare_causes.py
    python tools/compare_causes.py --only leaky_mux,simple_buffer
    python tools/compare_causes.py --max-cause-size 4 --timeout 1200
"""

import argparse
import ast
import csv
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(REPO, "explainhyper"))

CHECKERS = ("mchyper", "autohyper", "hyperqb")

# examples/running_example's shipped formula references the AP `li`, which does
# not exist in running_example.aag (its only input is `hi`). MCHyper tolerates
# this -- an AP that is never true makes `G(li_0 = li_1)` vacuously true, so the
# formula collapses to its consequent -- but AutoHyper and HyperQB both reject
# the undefined identifier outright. That asymmetry is a latent defect in the
# original artifact, surfaced only by swapping checkers.
#
# To compare all three on the same property we substitute the formula MCHyper
# was effectively evaluating: the consequent alone. This is a semantic no-op on
# this system, not a change of experiment -- but it IS a change from the shipped
# text, so every affected row is marked in the `formula` column.
FORMULA_OVERRIDES = {
    "running_example": (
        'Forall (Forall (G (And (Eq (AP "lo" 0) (AP "lo" 1)) '
        '(Eq (AP "ho" 0) (AP "ho" 1)))))'),
}

GAMMA_LINE = re.compile(r"^Size of the counter example \(\|Gamma\|\) is: (\d+)", re.M)
PHI_LINE = re.compile(r"^The size of the formula \(\|phi\|\) is (\d+)", re.M)
CTILDE_LINE = re.compile(r"^for trace (\d+): (\[.*\])$", re.M)
CAUSE_LINE = re.compile(r"^All minimal causes \(forall C\): (.*)$", re.M)
COUNT_LINE = re.compile(r"^Number of minimal causes \(# C\): (\d+)$", re.M)
TIME_CTILDE = re.compile(
    r"^Time to compute this set of causes \(time\(C tilde\)\):\s*\n([0-9.eE+-]+)", re.M)
TIME_GAMMA = re.compile(
    r"^Time to obtain the counterexample \(time\(Gamma\)\):\s*\n([0-9.eE+-]+)", re.M)
TIME_CHECKER = re.compile(
    r"^Time spent in the model checker itself \(time\(checker\)\):\s*\n([0-9.eE+-]+)", re.M)
TIME_SEARCH = re.compile(
    r"^The time of the minimality search \(time\(search\)\):\s*\n([0-9.eE+-]+)", re.M)
TIME_CAUSES = re.compile(
    r"^The time to compute all causes \(time\(forall C\)\) took:\s*\n([0-9.eE+-]+)", re.M)


def first_error_line(output):
    for pattern in (r"^error: (.*)\Z", r"^.*\bpanicked at.*$", r"^.*\bERROR\b.*$",
                    r"^.*\bTraceback\b.*$"):
        match = re.search(pattern, output, re.M | re.S)
        if match:
            text = match.group(1) if match.groups() else match.group(0)
            return re.sub(r"\s+", " ", text).strip()[:200]
    tail = [line for line in output.strip().splitlines() if line.strip()]
    return re.sub(r"\s+", " ", tail[-1]).strip()[:200] if tail else "no output"


def canonical(causes):
    """A cause list -> a hashable canonical form, so checkers can be compared.

    A cause is a set of events, and the algorithm's ordering is incidental, so
    both the events inside a cause and the causes themselves are sorted.
    """
    return tuple(sorted(tuple(sorted(tuple(event) for event in cause))
                        for cause in causes))


def render_cause(cause):
    """One cause -> `a@0=1(t0) & sel@0=0(t0)`, readable in a spreadsheet."""
    return " & ".join(
        "%s@%s=%s(t%s)" % (ap, step, value, trace) for (ap, step, value, trace) in cause)


def discover(examples_dir, only):
    """Examples that have everything the comparison needs."""
    found = []
    for name in sorted(os.listdir(examples_dir)):
        directory = os.path.join(examples_dir, name)
        if not os.path.isdir(directory):
            continue
        if only and not any(pattern in name for pattern in only):
            continue
        paths = {kind: os.path.join(directory, "%s.%s" % (name, kind))
                 for kind in ("aag", "cex", "dot", "smv")}
        # Both are hard requirements: .aag is the executable model used to
        # recompute outputs for counterfactuals, and without .dot no candidate
        # causes are computed at all and every run would report zero.
        if not (os.path.exists(paths["aag"]) and os.path.exists(paths["dot"])):
            continue
        found.append((name, directory, paths))
    return found


def build_argv(args, name, paths, checker, formula):
    common = [
        sys.executable, os.path.join(REPO, "explainhyper", "explain_hyper.py"),
        "-aag", paths["aag"],
        "-f", formula,
        "-stateMachine", paths["dot"],
        "-outName", os.path.join(args.out, "%s_%s" % (name, checker)),
        "-maxCauseSize", str(args.max_cause_size),
        "-frontend", checker,
    ]
    if checker == "mchyper":
        if not os.path.exists(paths["cex"]):
            return None, "no .cex recorded for this example"
        return common + ["-cex", paths["cex"]], None
    if not os.path.exists(paths["smv"]):
        return None, "no .smv model (generate with tools/aag2smv.py)"
    if checker == "autohyper":
        if not os.path.exists(args.autohyper_dll):
            return None, "AutoHyper not installed at %s" % args.autohyper_dll
        return common + ["-autohyperSystem", paths["smv"],
                         "-autohyperBin", args.autohyper_dll], None
    if checker == "hyperqb":
        if not os.path.exists(args.hyperqb_bin):
            return None, "HyperQB not installed at %s" % args.hyperqb_bin
        return common + ["-hyperqbModel", paths["smv"],
                         "-hyperqbBin", args.hyperqb_bin,
                         "-hyperqbK", str(args.k),
                         "-hyperqbSemantics", args.semantics,
                         # HyperQB counterexamples are flat, so `G` is false at
                         # the horizon under the default strong semantics and
                         # the violation would not register at all.
                         "-finiteSemantics", "weak"], None
    return None, "unknown checker"


def run_one(args, name, directory, paths, checker, formula, env):
    argv, skip = build_argv(args, name, paths, checker, formula)
    record = {"example": name, "checker": checker,
              "max_cause_size": args.max_cause_size, "timeout_s": args.timeout}
    if argv is None:
        record.update(status="skipped", success="no", reason=skip)
        return record

    started = time.monotonic()
    try:
        done = subprocess.run(argv, capture_output=True, text=True,
                              timeout=args.timeout, cwd=directory, env=env)
        output = done.stdout + done.stderr
        status = "ok" if done.returncode == 0 else "ERR"
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + (exc.stderr or "") if isinstance(
            exc.stdout, str) else ""
        status = "TO"
    wall = time.monotonic() - started

    with open(os.path.join(args.out, "%s_%s.log" % (name, checker)), "w") as handle:
        handle.write(output)

    reason = ""
    if status == "ERR":
        reason = first_error_line(output)
    elif status == "TO":
        reason = "timeout after %gs" % args.timeout

    gamma = GAMMA_LINE.search(output)
    phi = PHI_LINE.search(output)
    count = COUNT_LINE.search(output)
    causes, ctilde = None, None

    ctilde_matches = CTILDE_LINE.findall(output)
    if ctilde_matches:
        try:
            ctilde = sum(len(ast.literal_eval(block)) for _, block in ctilde_matches)
        except (ValueError, SyntaxError):
            ctilde = None
    if CAUSE_LINE.search(output):
        try:
            causes = ast.literal_eval(CAUSE_LINE.search(output).group(1))
        except (ValueError, SyntaxError):
            causes = None

    sizes = sorted({len(cause) for cause in causes}) if causes else []
    if status == "ok" and not causes:
        reason = reason or ("no cause of size <= %d" % args.max_cause_size)

    time_ctilde = TIME_CTILDE.search(output)
    time_causes = TIME_CAUSES.search(output)
    time_gamma = TIME_GAMMA.search(output)
    time_checker = TIME_CHECKER.search(output)
    time_search = TIME_SEARCH.search(output)

    def seconds(match):
        return ("%.3f" % float(match.group(1))) if match else ""

    record.update(
        status=status,
        success="yes" if (status == "ok" and causes) else "no",
        gamma_size=int(gamma.group(1)) if gamma else "",
        formula_size=int(phi.group(1)) if phi else "",
        candidate_set_size="" if ctilde is None else ctilde,
        num_causes=int(count.group(1)) if count else "",
        cause_sizes=";".join(map(str, sizes)),
        causes=" | ".join(render_cause(cause) for cause in (causes or [])),
        # The time is split in three, so the cost of obtaining Gamma (which
        # depends on the model checker) is not mixed into the algorithm's:
        #   time_gamma_s    obtaining Gamma = checker + parsing + simulation
        #   time_checker_s  the model-checker process alone (0 for MCHyper, which is replayed)
        #   time_ctilde_s   candidate causes C~
        #   time_search_s   minimality search over subsets of C~
        # time_causes_s is the whole run of the causality code, Gamma included.
        time_gamma_s=seconds(time_gamma),
        time_checker_s=seconds(time_checker),
        time_ctilde_s=seconds(time_ctilde),
        time_search_s=seconds(time_search),
        time_causes_s=seconds(time_causes),
        wall_s="%.3f" % wall,
        reason=reason,
    )
    record["_causes"] = causes
    return record


SUMMARY_COLUMNS = [
    "example", "checker", "num_causes", "cause_sizes", "causes",
    "wall_s", "time_gamma_s", "time_checker_s", "time_ctilde_s", "time_search_s",
    "time_causes_s",
    "success", "status", "gamma_size", "candidate_set_size", "formula_size",
    "max_cause_size", "timeout_s", "cap_binding", "formula", "reason",
]

DETAIL_COLUMNS = ["example", "checker", "cause_index", "size", "cause",
                  "ap", "time_step", "truth_value", "trace"]


def detail_rows(records):
    """One row per EVENT, so `all causes` is fully machine-readable."""
    rows = []
    for record in records:
        for index, cause in enumerate(record.get("_causes") or []):
            for (ap, step, value, trace) in cause:
                rows.append({
                    "example": record["example"], "checker": record["checker"],
                    "cause_index": index, "size": len(cause),
                    "cause": render_cause(cause),
                    "ap": ap, "time_step": step,
                    "truth_value": value, "trace": trace,
                })
    return rows


def comparison_rows(records):
    """Wide: one row per example, the three checkers side by side."""
    by_example = {}
    for record in records:
        by_example.setdefault(record["example"], {})[record["checker"]] = record

    rows = []
    for example in sorted(by_example):
        entry = by_example[example]
        row = {"example": example}
        shapes = {}
        for checker in CHECKERS:
            record = entry.get(checker)
            if record is None:
                continue
            row["causes_" + checker] = record.get("causes", "")
            row["sizes_" + checker] = record.get("cause_sizes", "")
            row["n_" + checker] = record.get("num_causes", "")
            row["gamma_" + checker] = record.get("gamma_size", "")
            row["wall_s_" + checker] = record.get("wall_s", "")
            for part in ("gamma", "ctilde", "search"):
                row["t_%s_%s" % (part, checker)] = record.get("time_%s_s" % part, "")
            if record.get("_causes"):
                shapes[checker] = canonical(record["_causes"])
        # The headline question: with everything else held fixed, do the
        # checkers agree on the causes?
        row["checkers_compared"] = len(shapes)
        if len(shapes) < 2:
            row["same_causes"] = ""
        elif len(set(shapes.values())) == 1:
            row["same_causes"] = "yes"
        else:
            row["same_causes"] = "NO"
        rows.append(row)
    return rows


def comparison_columns():
    columns = ["example"]
    for checker in CHECKERS:
        columns += ["n_" + checker, "sizes_" + checker, "gamma_" + checker,
                    "wall_s_" + checker, "t_gamma_" + checker,
                    "t_ctilde_" + checker, "t_search_" + checker,
                    "causes_" + checker]
    return columns + ["checkers_compared", "same_causes"]


def write_csv(path, columns, rows):
    with open(path, "w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=columns, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--examples", default=os.path.join(REPO, "examples"))
    parser.add_argument("--out", default=os.path.join(HERE, "_cause_out"))
    parser.add_argument("--only", type=lambda s: s.split(","), default=None)
    parser.add_argument("--checkers", type=lambda s: s.split(","), default=list(CHECKERS))
    parser.add_argument("--max-cause-size", type=int, default=3,
                        help="cap on |C| in the subset search; applied equally "
                             "to every checker (default 3)")
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--k", type=int, default=6, help="HyperQB unrolling bound")
    parser.add_argument("--semantics", default="pes",
                        choices=("pes", "opt", "hpes", "hopt"))
    parser.add_argument("--autohyper-dll",
                        default=os.path.expanduser("~/opt/AutoHyper/app/AutoHyper.dll"))
    parser.add_argument("--hyperqb-bin",
                        default=os.path.expanduser("~/opt/HyperRUSTY/target/release/HyperRUSTY"))
    parser.add_argument("--dotnet", default=os.path.expanduser("~/.dotnet/dotnet"))
    parser.add_argument("--z3-lib", default="/tmp/z3-4.12.2-x64-glibc-2.31/bin")
    parser.add_argument("--no-overrides", action="store_true",
                        help="use each example's shipped formula verbatim, even "
                             "where it references a nonexistent AP")
    args = parser.parse_args()

    args.out = os.path.abspath(args.out)
    os.makedirs(args.out, exist_ok=True)

    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = args.z3_lib + ":" + env.get("LD_LIBRARY_PATH", "")
    env["PATH"] = os.path.dirname(args.dotnet) + os.pathsep + env["PATH"]
    env["PYTHONHASHSEED"] = "0"          # reproducible artifacts

    from conftest_formulas import FORMULAS

    # Preflight: explain_hyper runs as a subprocess under THIS interpreter, so a
    # Python without the dependencies produces one identical ImportError per
    # (example, checker) -- 27 tracebacks and a CSV of nothing. Check once and
    # say which interpreter is wrong, rather than failing 27 times in a row.
    probe = subprocess.run(
        [sys.executable, "-c", "import aiger, spot, pygraphviz, cvc5"],
        capture_output=True, text=True)
    if probe.returncode != 0:
        missing = probe.stderr.strip().splitlines()[-1] if probe.stderr else "unknown"
        print("error: this Python cannot run the causality pipeline.\n"
              "  interpreter: %s\n"
              "  %s\n\n"
              "Use the environment that has the dependencies, e.g.\n"
              "  /home/einat/miniconda/envs/hyper/bin/python %s ...\n"
              "or `conda activate hyper` first."
              % (sys.executable, missing, os.path.relpath(__file__, os.getcwd())))
        return 1

    found = discover(args.examples, args.only)
    if not found:
        print("no examples with both .aag and .dot under %s" % args.examples)
        return 1

    print("comparing %d example(s) x %d checker(s), cap |C| <= %d, timeout %ds\n"
          % (len(found), len(args.checkers), args.max_cause_size, args.timeout))

    records = []
    for name, directory, paths in found:
        if name not in FORMULAS:
            print("  %-22s SKIP (no formula recorded)" % name)
            continue
        formula = FORMULAS[name]
        label = "shipped"
        if not args.no_overrides and name in FORMULA_OVERRIDES:
            formula = FORMULA_OVERRIDES[name]
            label = "corrected (shipped formula references a nonexistent AP)"
        for checker in args.checkers:
            record = run_one(args, name, directory, paths, checker, formula, env)
            record["formula"] = label
            records.append(record)
            print("  %-22s %-10s n=%-4s sizes=%-8s |G|=%-4s %8ss  %s%s"
                  % (name, checker, record.get("num_causes", "-") or "-",
                     record.get("cause_sizes") or "-",
                     record.get("gamma_size", "-") or "-",
                     record.get("wall_s", "-"),
                     record["status"],
                     ("  " + record["reason"]) if record.get("reason") else ""))

    # Flag rows where the cap could have hidden a real cause, so an empty
    # result is never mistaken for a proven absence.
    for record in records:
        ctilde = record.get("candidate_set_size")
        binding = (isinstance(ctilde, int) and ctilde > args.max_cause_size
                   and not record.get("_causes"))
        record["cap_binding"] = "yes" if binding else "no"

    wide = comparison_rows(records)
    write_csv(os.path.join(args.out, "causes_summary.csv"), SUMMARY_COLUMNS, records)
    write_csv(os.path.join(args.out, "causes_detail.csv"), DETAIL_COLUMNS,
              detail_rows(records))
    write_csv(os.path.join(args.out, "causes_comparison.csv"),
              comparison_columns(), wide)
    with open(os.path.join(args.out, "causes.json"), "w") as handle:
        json.dump([{k: v for k, v in r.items() if k != "_causes"} for r in records],
                  handle, indent=1)

    compared = [row for row in wide if row["checkers_compared"] >= 2]
    differing = [row["example"] for row in wide if row["same_causes"] == "NO"]
    print("\n%d run(s): %d produced causes, %d found none, %d failed"
          % (len(records),
             sum(r["success"] == "yes" for r in records),
             sum(r["success"] == "no" and r["status"] == "ok" for r in records),
             sum(r["status"] in ("ERR", "TO", "skipped") for r in records)))
    print("%d example(s) had >=2 checkers produce causes; causes DIFFER on %d: %s"
          % (len(compared), len(differing), ", ".join(differing) or "-"))
    capped = [r["example"] + "/" + r["checker"] for r in records
              if r["cap_binding"] == "yes"]
    if capped:
        print("cap |C| <= %d may hide causes for: %s"
              % (args.max_cause_size, ", ".join(capped)))
    print("\nwrote %s/{causes_summary.csv,causes_detail.csv,"
          "causes_comparison.csv,causes.json}" % args.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
