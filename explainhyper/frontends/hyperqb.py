"""HyperQB 2.0 front end.

HyperQB is a *bounded* model checker: it unrolls the system to depth k and asks
Z3 (or QuAbS) whether a violation exists within k steps.

    hyperqb (-n|-v) <model>... -f <formula.hq> -k <int> -s <pes|opt|hpes|hopt> [-c]

One model file per quantifier. ``result: unsat`` means the property is
*violated*, and ``-c`` then prints the counterexample.

Counterexample format, recorded from a real run
(tests/fixtures/hyperqb/divider_excerpt.txt)::

    State 0:
      rst_0_A = true
      s_input_b_ack_0_A = #b1
      a_0_A = #x3e900000
      ...
    State 1:
      ...

Lines are ``<signal>_<timestep>_<pathid> = <value>``, values are ``true`` /
``false`` / ``#b<bits>`` / ``#x<hex>``.

Two properties of the format matter here:

* It is a **partial model** -- variables the solver never constrained are
  simply absent. That does not hurt: only the input columns are read, an unset
  input defaults to false, and outputs and latches are recomputed by
  simulating the -aag model.
* It is **flat**. There is no lasso, so ``lasso_start`` is always -1, which
  walks straight into Defect 2 of STAGE0-FINDING.md -- on a finite trace `G` is
  false at the horizon, so the negated specification cannot hold and the
  counterexample is not even recognised as a violation. This front end warns
  that ``-finiteSemantics weak`` is wanted. It deliberately does **not**
  override the flag: that is a semantic choice for the user to make, and
  STAGE0 records that `weak` does not repair every case.
"""

import re
import subprocess
import time

import aiger
from translator import Translator

from . import _formula, _sim
from .base import FrontEnd, FrontEndError, FrontEndResult, Option, build_trace, opt, register

_VERDICT = re.compile(r"^\s*result:\s*(sat|unsat|unknown)", re.M | re.I)
_STATE_HEADER = re.compile(r"^State\s+(\d+)\s*:\s*$", re.M)
# Split greedily from the right: signal names contain underscores and digits
# (`s_input_b_ack`, `PIN_0`), so only the trailing `_<digits>_<UPPER>` is
# structure. Anything else is part of the name.
_ASSIGN = re.compile(
    r"^\s+(?P<sig>.+)_(?P<t>\d+)_(?P<path>[A-Z][A-Za-z0-9]*)\s*=\s*(?P<val>\S+)\s*$", re.M)


def parse_value(token):
    """A HyperQB value literal -> list of bits, least-significant first."""
    if token in ("true", "false"):
        return [token == "true"]
    if token.startswith("#b"):
        digits = token[2:]
        if not digits or any(c not in "01" for c in digits):
            raise FrontEndError("malformed binary literal %r" % token)
        return [c == "1" for c in reversed(digits)]
    if token.startswith("#x"):
        digits = token[2:]
        try:
            value = int(digits, 16)
        except ValueError:
            raise FrontEndError("malformed hex literal %r" % token)
        width = 4 * len(digits)
        return [bool((value >> b) & 1) for b in range(width)]
    raise FrontEndError("unrecognised value literal %r" % token)


def parse_counterexample(text):
    """HyperQB stdout -> (verdict, k, {(signal, timestep, path): bits}).

    Raises rather than skipping anything it cannot read: a silently dropped
    assignment would shift a timestep and yield plausible but wrong causes.
    """
    verdict_match = _VERDICT.search(text)
    if verdict_match is None:
        raise FrontEndError(
            "no `result:` line in HyperQB output:\n%s" % text.strip()[:500])
    verdict = verdict_match.group(1).lower()

    states = [int(n) for n in _STATE_HEADER.findall(text)]
    values = {}
    for match in _ASSIGN.finditer(text):
        key = (match.group("sig"), int(match.group("t")), match.group("path"))
        values[key] = parse_value(match.group("val"))

    if states and sorted(states) != list(range(len(states))):
        raise FrontEndError("State blocks are not 0..k: %s" % states)
    return verdict, (max(states) if states else -1), values


@register
class HyperQbFrontEnd(FrontEnd):
    name = "hyperqb"
    summary = "HyperQB 2.0 counterexample (bounded, flat k-step trace)."

    # -aag is a common flag (parser.py): the executable model that
    # get_circuit_outputs re-simulates when computing counterfactuals.
    requires = ("aag",)

    options = (
        Option("-hyperqbBin", "hyperqbBin", default="hyperqb",
               help="hyperqb executable (default: hyperqb on PATH)"),
        Option("-hyperqbModel", "hyperqbModel", nargs="+",
               help="one model file per quantifier (-n SMV / -v Yosys build script)"),
        Option("-hyperqbK", "hyperqbK", help="bounded unrolling depth (-k)"),
        Option("-hyperqbSemantics", "hyperqbSemantics", default="pes",
               choices=("pes", "opt", "hpes", "hopt"),
               help="bounded-semantics mode passed as -s; pes is the bug-hunting one"),
        Option("-hyperqbTop", "hyperqbTop", help="top module name, Verilog only (-t)"),
        Option("-hyperqbVerilog", "hyperqbVerilog", default=False,
               help="pass the models with -v (Yosys build scripts) instead of -n"),
        Option("-hyperqbOutput", "hyperqbOutput",
               help="parse this recorded hyperqb output instead of invoking it "
                    "(offline; no binary needed)"),
    )

    def validate(self, args):
        super(HyperQbFrontEnd, self).validate(args)
        recorded = getattr(args, "hyperqbOutput", None)
        models = getattr(args, "hyperqbModel", None)
        if not recorded and not models:
            raise FrontEndError(
                "front end 'hyperqb' needs either -hyperqbModel (to run HyperQB) "
                "or -hyperqbOutput (to parse a recorded run)")
        if not recorded and not getattr(args, "hyperqbK", None):
            raise FrontEndError("front end 'hyperqb' needs -hyperqbK (the unrolling bound)")
        if getattr(args, "finiteSemantics", "strong") != "weak":
            print("warning: HyperQB counterexamples are flat (no lasso). Under the "
                  "default -finiteSemantics strong, `G` is false at the horizon and "
                  "the counterexample will not register as a violation at all. "
                  "Consider -finiteSemantics weak. See STAGE0-FINDING.md.")
        if not getattr(args, "stateMachine", None):
            print("warning: no -stateMachine given; without a DOT transition system "
                  "no candidate causes can be computed and the run reports zero causes.")

    def render_formula(self, mchyper_text, aps):
        return _formula.HyperQbRenderer().render(mchyper_text)

    def _run(self, args, num_traces):
        models = list(opt(args, self.options[1]) or [])
        if len(models) == 1 and num_traces > 1:
            models = models * num_traces
        if len(models) != num_traces:
            raise FrontEndError(
                "the formula has %d quantifiers but %d model file(s) were given"
                % (num_traces, len(models)))

        formula_path = args.outName + ".hq"
        with open(formula_path, "w") as handle:
            handle.write(self.render_formula(args.f, None))

        flag = "-v" if opt(args, self.options[5]) else "-n"
        command = [opt(args, self.options[0]), flag] + models + [
            "-f", formula_path,
            "-k", str(opt(args, self.options[2])),
            "-s", str(opt(args, self.options[3])), "-c"]
        top = opt(args, self.options[4])
        if top:
            command += ["-t", str(top)]

        try:
            started = time.time()
            done = subprocess.run(command, capture_output=True, text=True)
            self.checker_seconds = time.time() - started
        except OSError as exc:
            raise FrontEndError("could not run HyperQB: %s" % exc)
        output = done.stdout + done.stderr
        with open(args.outName + ".hyperqb.log", "w") as handle:
            handle.write(output)
        return output

    def load(self, args):
        # Load the system first: the formula cannot be rendered before it,
        # because the sugar handlers expand against real signal names.
        circuit = aiger.load(args.aag)
        negate, f, fold, num_traces = Translator.mchyper_pipeline(args.f, circuit)

        recorded = getattr(args, "hyperqbOutput", None)
        if recorded:
            with open(recorded) as handle:
                output = handle.read()
        else:
            output = self._run(args, num_traces)

        verdict, k, values = parse_counterexample(output)
        if verdict == "sat":
            raise FrontEndError(
                "HyperQB reports sat: the property holds within the bound, so "
                "there is no counterexample to explain.")
        if verdict == "unknown":
            raise FrontEndError("HyperQB could not decide the instance (unknown).")
        if k < 0:
            raise FrontEndError(
                "HyperQB reported a violation but printed no counterexample; "
                "the -c flag is required.")

        inputs = set(circuit.inputs)
        input_rows, reported = [], []
        for tid in range(num_traces):
            path = _formula.PATH_IDS[tid]
            rows = []
            for timestep in range(k + 1):
                row = {}
                for name in inputs:
                    bits = values.get((name, timestep, path))
                    # A partial model simply omits what the solver did not
                    # constrain; an unset input is free, so take it as false.
                    row[name] = bool(bits[0]) if bits else False
                rows.append(row)
            input_rows.append(rows)
            if tid == 0:
                reported = [
                    {Translator.filter_out_spot_syntax_from_APs(sig) + "_0": bits[0]
                     for (sig, t, p), bits in values.items()
                     if t == timestep and p == path and len(bits) == 1}
                    for timestep in range(k + 1)]

        traces, all_aps, circuit = _sim.simulate_inputs(
            args, f, circuit, num_traces, input_rows)

        mismatches = _sim.check_reported_values(reported, traces)
        if mismatches:
            print("warning: %d value(s) reported by HyperQB disagree with simulating "
                  "-aag; the two models may not be the same system. First: %s"
                  % (len(mismatches), mismatches[0]))

        # Flat: no loop was reported, so the trace is finite by construction.
        lasso_start = -1
        trace = build_trace(traces, lasso_start, args)
        return FrontEndResult(
            traces=traces, lasso_start=lasso_start, all_aps=all_aps, system=circuit,
            num_traces=num_traces, negate=negate, f=f, fold=fold, trace=trace,
            diagnostics={"verdict": verdict, "k": k, "mismatches": len(mismatches),
                         "checker_s": getattr(self, "checker_seconds", 0.0)})
