"""AutoHyper front end.

AutoHyper (Beutner & Finkbeiner, TACAS'23) is an explicit-state automata-based
checker, complete for arbitrary quantifier alternation. With ``--witness`` it
prints concrete **lasso-shaped** paths -- counterexamples for a leading
``forall*`` block. A lasso is exactly what the causality algorithm wants, so
this front end sidesteps the finite-trace gap a bounded checker runs into
(STAGE0-FINDING.md).

Invocation::

    AutoHyper [--nusmv|--exp|--bp] [--witness] <system>... <formula>

one system per quantifier; "the i-th quantifier is resolved on the i-th
system". ``UNSAT`` means the property is violated.

Witness format, recorded from a real run (tests/fixtures/autohyper/)::

    ======= Witnesses =======
    A: ({"secret":false, "state":false} {"secret":true, ...}) ({"secret":false, ...})
    B: (...) (...)
    =========================

    UNSAT

One line per path variable; two parenthesised groups, the prefix then the
repeating lasso; each state a set of name/value pairs. Only the *input* columns
are used -- outputs and latches are recomputed by simulating the -aag model,
which is also what makes the reported latch values a free consistency check.
"""

import os
import re
import subprocess
import time

import aiger
from translator import Translator

from . import _formula, _sim
from .base import FrontEnd, FrontEndError, FrontEndResult, Option, build_trace, opt, register

_WITNESS_BLOCK = re.compile(r"=+\s*Witnesses\s*=+(.*?)^=====+", re.S | re.M)
_PATH_LINE = re.compile(r"^\s*([A-Za-z][A-Za-z0-9_]*)\s*:\s*(.+)$", re.M)
_GROUP = re.compile(r"\(([^()]*)\)")
_STATE = re.compile(r"\{([^{}]*)\}")
_ASSIGN = re.compile(r'"([^"]+)"\s*:\s*(true|false)')
_VERDICT = re.compile(r"^\s*(SAT|UNSAT|UNKNOWN)\s*$", re.M)


def parse_state(text):
    return {name: value == "true" for name, value in _ASSIGN.findall(text)}


def parse_witness(text):
    """AutoHyper stdout -> (verdict, {path_var: (prefix_states, lasso_states)}).

    Raises FrontEndError rather than returning something half-parsed: a silently
    dropped state would shift every timestep and produce plausible-looking but
    wrong causes.
    """
    verdict_match = _VERDICT.search(text)
    if verdict_match is None:
        raise FrontEndError(
            "no SAT/UNSAT verdict in AutoHyper output:\n%s" % text.strip()[:500])
    verdict = verdict_match.group(1).lower()

    block = _WITNESS_BLOCK.search(text)
    paths = {}
    if block is not None:
        for name, body in _PATH_LINE.findall(block.group(1)):
            groups = _GROUP.findall(body)
            if len(groups) != 2:
                raise FrontEndError(
                    "expected a prefix and a lasso group for path %r, found %d"
                    % (name, len(groups)))
            prefix, lasso = ([parse_state(s) for s in _STATE.findall(g)] for g in groups)
            if not lasso:
                raise FrontEndError("path %r has an empty lasso" % name)
            paths[name] = (prefix, lasso)
    return verdict, paths


@register
class AutoHyperFrontEnd(FrontEnd):
    name = "autohyper"
    summary = "AutoHyper counterexample (lasso-shaped --witness output)."

    # -aag is a common flag (parser.py): the executable model that
    # get_circuit_outputs re-simulates when computing counterfactuals.
    requires = ("aag",)

    options = (
        Option("-autohyperBin", "autohyperBin", default="AutoHyper",
               help="AutoHyper executable, or the .dll to run under dotnet"),
        Option("-autohyperSystem", "autohyperSystem", nargs="+",
               help="one system file per quantifier; the i-th quantifier is "
                    "resolved on the i-th system"),
        Option("-autohyperMode", "autohyperMode", default="nusmv",
               choices=("nusmv", "exp", "bp"),
               help="system encoding, passed as --nusmv/--exp/--bp"),
        Option("-autohyperWitness", "autohyperWitness",
               help="parse this recorded --witness output instead of invoking "
                    "AutoHyper (offline; no binary needed)"),
    )

    def validate(self, args):
        super(AutoHyperFrontEnd, self).validate(args)
        recorded = getattr(args, "autohyperWitness", None)
        systems = getattr(args, "autohyperSystem", None)
        if not recorded and not systems:
            raise FrontEndError(
                "front end 'autohyper' needs either -autohyperSystem (to run "
                "AutoHyper) or -autohyperWitness (to parse a recorded run)")
        if not getattr(args, "stateMachine", None):
            print("warning: no -stateMachine given; without a DOT transition "
                  "system no candidate causes can be computed and the run will "
                  "report zero causes.")

    def render_formula(self, mchyper_text, aps):
        return _formula.AutoHyperRenderer().render(mchyper_text)

    def _run(self, args, num_traces):
        """Invoke AutoHyper and return its stdout."""
        systems = list(opt(args, self.options[1]) or [])
        if len(systems) == 1 and num_traces > 1:
            systems = systems * num_traces          # same system for every quantifier
        if len(systems) != num_traces:
            raise FrontEndError(
                "the formula has %d quantifiers but %d system file(s) were given"
                % (num_traces, len(systems)))

        formula_path = args.outName + ".autohyper.hq"
        with open(formula_path, "w") as handle:
            handle.write(self.render_formula(args.f, None))

        binary = opt(args, self.options[0])
        command = (["dotnet", binary] if binary.endswith(".dll") else [binary])
        command += ["--" + opt(args, self.options[2]), "--witness"] + systems + [formula_path]

        try:
            started = time.time()
            done = subprocess.run(command, capture_output=True, text=True)
            self.checker_seconds = time.time() - started
        except OSError as exc:
            raise FrontEndError("could not run AutoHyper (%s): %s" % (binary, exc))
        output = done.stdout + done.stderr
        with open(args.outName + ".autohyper.log", "w") as handle:
            handle.write(output)
        if "ERROR" in output and "Witnesses" not in output:
            raise FrontEndError("AutoHyper failed:\n%s" % output.strip()[:800])
        return output

    def load(self, args):
        # Ordering is fixed: the system must be loaded before the formula can be
        # rendered, because the sugar handlers expand against real signal names.
        circuit = aiger.load(args.aag)
        negate, f, fold, num_traces = Translator.mchyper_pipeline(args.f, circuit)

        recorded = getattr(args, "autohyperWitness", None)
        if recorded:
            with open(recorded) as handle:
                output = handle.read()
        else:
            output = self._run(args, num_traces)

        verdict, paths = parse_witness(output)
        if verdict == "sat":
            raise FrontEndError(
                "AutoHyper reports SAT: the property holds, so there is no "
                "counterexample to explain.")
        if len(paths) < num_traces:
            raise FrontEndError(
                "the formula has %d quantifiers but the witness has %d path(s): %s"
                % (num_traces, len(paths), sorted(paths)))

        inputs = set(circuit.inputs)
        input_rows, lasso_start, reported = [], None, []
        for tid in range(num_traces):
            prefix, lasso = paths[_formula.PATH_IDS[tid]]
            # Repeat the first lasso state at the end. The pipeline's Trace
            # convention is that the final row is the loop-back duplicate and
            # gets dropped (see base.build_trace), which is how MCHyper's
            # counterexamples are shaped; AutoHyper's are not, so add it.
            states = prefix + lasso + [lasso[0]]
            lasso_start = len(prefix)
            rows = []
            for state in states:
                rows.append({name: bool(value) for name, value in state.items()
                             if name in inputs})
            input_rows.append(rows)
            if tid == 0:
                reported = [
                    {Translator.filter_out_spot_syntax_from_APs(k) + "_0": v
                     for k, v in state.items()}
                    for state in states]

        traces, all_aps, circuit = _sim.simulate_inputs(
            args, f, circuit, num_traces, input_rows)

        mismatches = _sim.check_reported_values(reported, traces)
        if mismatches:
            print("warning: %d value(s) reported by AutoHyper disagree with "
                  "simulating -aag; the two models may not be the same system. "
                  "First: %s" % (len(mismatches), mismatches[0]))

        trace = build_trace(traces, lasso_start, args)
        return FrontEndResult(
            traces=traces, lasso_start=lasso_start, all_aps=all_aps,
            system=circuit, num_traces=num_traces, negate=negate, f=f, fold=fold,
            trace=trace, diagnostics={"verdict": verdict, "mismatches": len(mismatches),
                         "checker_s": getattr(self, "checker_seconds", 0.0)})
