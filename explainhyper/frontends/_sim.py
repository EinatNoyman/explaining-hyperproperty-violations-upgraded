"""Shared simulation core.

A front end delivers per-trace *input* sequences plus a loop point. Everything
else -- outputs, latch values, the AP partition, the augmented counterexample
file -- is derived by simulating the system, exactly as the MCHyper path has
always done. This module holds that derivation so every front end shares one
implementation.
"""

from formula import formula as spot
from translator import Translator


def get_circuit_outputs(circuit, inputs):
    """Run `inputs` through the system, returning per-timestep valuations.

    `inputs` is a list of dicts (one per timestep) mapping input name -> bool.
    Each returned dict holds that step's inputs, outputs and latch values.

    This is the intervention semantics of the causality definition: after an
    input is flipped, the resulting outputs have to be *recomputed*, not read
    off the counterexample. `circuit` is any SystemModel -- a py-aiger circuit
    or an smv.SmvModel.
    """
    output_list = []
    simulator = circuit.simulator()
    next(simulator)
    output_list = [{} for i in range(len(inputs)+1)]
    for timestep in range(len(inputs)):
        result = simulator.send(inputs[timestep])
        output_list[timestep] = {**output_list[timestep], **inputs[timestep], **result[0]}
        output_list[timestep+1] = {**output_list[timestep+1], **result[1]}
    return output_list[:len(inputs)]


def partition_and_relabel(args, circuit):
    """Sanitise every signal name and split them into [inputs, outputs, latches].

    Names are filtered through the same mangling the formula translation uses,
    so an AP in the trace matches an AP in the formula. Also writes the
    relabelled model next to the other artifacts.
    """
    all_inputs, all_outputs, all_latches = set(), set(), set()
    for x in set(circuit.inputs):
        all_inputs.add(Translator.filter_out_spot_syntax_from_APs(x))
        circuit = circuit.relabel('input', {x: Translator.filter_out_spot_syntax_from_APs(x)})
    for x in set(circuit.outputs):
        all_outputs.add(Translator.filter_out_spot_syntax_from_APs(x))
        circuit = circuit.relabel('output', {x: Translator.filter_out_spot_syntax_from_APs(x)})
    for x in set(circuit.latches):
        all_latches.add(Translator.filter_out_spot_syntax_from_APs(x))
        circuit = circuit.relabel('latch', {x: Translator.filter_out_spot_syntax_from_APs(x)})
    circuit.write(args.outName + "-aag.aag")
    return [all_inputs, all_outputs, all_latches], circuit


def write_augmented_cex(args, f, traces):
    """Emit <outName>.cex in the same shape the MCHyper path produces."""
    with open(args.outName + ".cex", "w") as handle:
        handle.write("FORM: " + spot.formula(f).to_str() + "\n")
        handle.write("VAR: " + "\n")
        for timestep, row in enumerate(traces):
            for ap in sorted(row):
                handle.write("%s@%d=1\n" % (ap, timestep))


def simulate_inputs(args, f, circuit, num_traces, input_rows):
    """Turn per-trace input sequences into the pipeline's trace representation.

    `input_rows[tid][t]` is a dict of input name -> bool. Returns the same
    `(traces, all_aps, circuit)` shape the MCHyper path builds, with `traces`
    a list indexed by timestep holding the APs true at that step, each suffixed
    with its trace id.
    """
    all_aps, circuit = partition_and_relabel(args, circuit)

    per_trace = []
    for tid in range(num_traces):
        rows = get_circuit_outputs(circuit, input_rows[tid])
        per_trace.append(Translator.ap_list_to_trace(rows, str(tid)))

    length = min(len(t) for t in per_trace) if per_trace else 0
    traces = []
    for timestep in range(length):
        combined = []
        for tid in range(num_traces):
            combined.extend(per_trace[tid][timestep])
        traces.append(combined)

    write_augmented_cex(args, f, traces)
    return traces, all_aps, circuit


def check_reported_values(reported, traces, warn=None):
    """Compare values a checker reported against what simulation produced.

    A checker that reports outputs or registers gives us a free consistency
    check: if its model and the `-aag` model are not the same system, the
    causes computed here are for the wrong machine. Returns the list of
    mismatches; the caller decides how loudly to complain.
    """
    mismatches = []
    for timestep, expected in enumerate(reported):
        if timestep >= len(traces):
            break
        actual = set(traces[timestep])
        for ap, value in expected.items():
            if bool(value) != (ap in actual):
                mismatches.append((ap, timestep, bool(value), ap in actual))
    if mismatches and warn is not None:
        warn(mismatches)
    return mismatches
