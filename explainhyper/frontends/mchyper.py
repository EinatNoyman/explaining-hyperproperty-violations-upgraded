"""MCHyper front end -- the original path.

MCHyper self-composes an AIGER circuit and hands it to ABC. It emits a
lasso-shaped counterexample as a flat list of ``signal_traceid@timestep=0|1``
lines, marking the loop point with ``I:remember_state@t=1``.

The code here is the pre-refactor implementation, moved verbatim so the
extraction is behaviour-preserving.
"""

import re

import aiger
from formula import formula as spot
from translator import Translator

from .base import FrontEnd, FrontEndResult, Option, build_trace, register


def write_outputs(list_outputs, dict_outputs_list, traces, current_time_step, augmented_cex, num_traces):
    # handle outputs for all traces
    for trace_id in range(num_traces):
        for output in list_outputs:
            trace_string = Translator.filter_out_spot_syntax_from_APs(output)
            output_string = trace_string + "_" + str(trace_id) + "@" + str(current_time_step)
            if (dict_outputs_list[trace_id][output]):
                traces[current_time_step].append(trace_string + "_" + str(trace_id))
                truth_value_string = "=1\n"
            else:
                truth_value_string = "=0\n"
            augmented_cex.write(output_string + truth_value_string)
    return traces


def store_inputs(name_string, trace_id_string, truth_value, circuit, dict_inputs_list):
    # update and return the input dicts with the respective truth values so the right values are used for simulation of this time step
    if (name_string in circuit.inputs):
        trace_id = int(trace_id_string)
        dict_inputs_list[trace_id][name_string] = truth_value
    return dict_inputs_list


def simulate_circuit(args, f, circuit, num_traces): # f only because it will be written into the augmented cex file
    # regular expressions recognizing the different kinds of lines in the cex file (using raw strings)
    inputs = set(circuit.inputs)
    all_inputs = set()
    empty_line = re.compile(r"^$")
    value = re.compile(r"([^:@=]+)_(\d+)@(\d+)=([01])")
    remember_state = re.compile(r"I:remember_state@(\d+)=([01])")
    input_expression = re.compile(r"I:\w*")
    sink = re.compile(r"sink@\d+=[01]")
    init = re.compile(r"init@\d+=[01]")
    entered_lasso = re.compile(r"entered_lasso@\d+=[01]")
    latch_expression = re.compile(r"^L(_MH)?:\w*")
    latch_copy = re.compile(r"l\d+_copy@\d+=[01]")
    comment = re.compile(r"^#")

    # read cex file and simulate circuit to obtain the outputs and build the counterexample traces
    traces = [[]] # list of lists of APs holding at the different time steps for all traces
    lasso_start = -1
    current_time_step = 0

    # open provided cex file and create augmented cex file
    cex = open(args.cex, "r")
    augmented_cex = open(args.outName + ".cex", "w")
    augmented_cex.write("FORM: " + spot.formula(f).to_str() + "\n")
    augmented_cex.write("VAR: " + "\n")

    # create N simulators to simulate the circuit using the inputs for all traces from the cex file
    sims = []
    for i in range(num_traces):
        sim = circuit.simulator()
        next(sim)
        sims.append(sim)

    # create N dictionaries to collect the input values for stepwise simulation
    dict_inputs_list = [{}.fromkeys(circuit.inputs) for _ in range(num_traces)]

    # get ordered list of outputs to ensure deterministic behavior when writing to the augmented cex file
    dict_outputs = {}.fromkeys(circuit.outputs)
    list_outputs = sorted(list(dict_outputs.keys()))
    # go over every line in cex and (modify if needed and) put relevant ones in augmented_cex
    for line in cex:
        # empty line at the end of the cex file
        if (empty_line.match(line) or comment.match(line)):
            # simulate behavior from last time step for all traces
            dict_outputs_list = [sims[i].send(dict_inputs_list[i])[0] for i in range(num_traces)]
            traces = write_outputs(list_outputs, dict_outputs_list, traces, current_time_step, augmented_cex, num_traces)
            continue
        # identify allowed variable assignments (inputs, latches?)
        if (value.match(line)):
            match = value.match(line)
            name_string = match.group(1)
            trace_id_string = match.group(2)
            time_step = int(match.group(3))
            truth_value = int(match.group(4))
            # check if this is a new time step
            if (time_step == current_time_step + 1):
                traces.append([])
                # simulate behavior from last time step for all traces
                dict_outputs_list = [sims[i].send(dict_inputs_list[i])[0] for i in range(num_traces)]
                traces = write_outputs(list_outputs, dict_outputs_list, traces, current_time_step, augmented_cex, num_traces)
                dict_inputs_list = store_inputs(name_string, trace_id_string, truth_value, circuit, dict_inputs_list)
                current_time_step += 1
            else:
                dict_inputs_list = store_inputs(name_string, trace_id_string, truth_value, circuit, dict_inputs_list)
            # add value to traces
            ap_string = Translator.filter_out_spot_syntax_from_APs(name_string) + "_" + trace_id_string
            if (truth_value):
                traces[time_step].append(ap_string)
            augmented_cex.write(ap_string + "@" + str(time_step) + "=" + str(truth_value) + "\n")
            continue
        # identify nondeterministically chosen remember_state input
        if (remember_state.match(line)):
            match = remember_state.match(line)
            if (lasso_start == -1):
                truth_value = match.group(2)
                if (truth_value == "1"):
                    time_step = match.group(1)
                    lasso_start = int(time_step)
            augmented_cex.write(line)
            continue
        if (input_expression.match(line) or sink.match(line) or init.match(line) or latch_copy.match(line) or latch_expression.match(line) or comment.match(line) or entered_lasso.match(line)):
            continue
        else:
            augmented_cex.write("Error: Some line from the counterexample file is not handled correctly!\n")
            print("Error: " + line)
    cex.close()
    augmented_cex.close()
    for x in inputs:
        all_inputs.add(Translator.filter_out_spot_syntax_from_APs(x))
        circuit = circuit.relabel('input', {x: Translator.filter_out_spot_syntax_from_APs(x)})
    outputs = set(circuit.outputs)
    all_outputs = set()
    for x in outputs:
        all_outputs.add(Translator.filter_out_spot_syntax_from_APs(x))
        circuit = circuit.relabel('output', {x: Translator.filter_out_spot_syntax_from_APs(x)})
    latches = set(circuit.latches)
    all_latches = set()
    for x in latches:
        all_latches.add(Translator.filter_out_spot_syntax_from_APs(x))
        circuit = circuit.relabel('latch', {x: Translator.filter_out_spot_syntax_from_APs(x)})
    circuit.write(args.outName + "-aag.aag")
    all_aps = [all_inputs, all_outputs, all_latches]
    return (traces, lasso_start, all_aps, circuit)


@register
class MCHyperFrontEnd(FrontEnd):
    name = "mchyper"
    summary = "MCHyper counterexample (AIGER circuit + .cex). The original path."

    # -aag is a common flag (parser.py): the executable model that
    # get_circuit_outputs re-simulates when computing counterfactuals.
    requires = ("aag",)

    options = (
        Option("-cex", "cex", required=True,
               help="the MCHyper counterexample file to be processed"),
    )

    def validate(self, args):
        super(MCHyperFrontEnd, self).validate(args)

    def load(self, args):
        # load circuit to use for simulation and formula transformation
        circuit = aiger.load(args.aag)

        # transform formula to spot input format and check if it is universal or existential
        (negate, f, fold, num_traces) = Translator.mchyper_pipeline(args.f, circuit)

        # simulate circuit to recover outputs and generate the augmented cex file
        (traces, lasso_start, all_aps, circuit) = simulate_circuit(args, f, circuit, num_traces)
        trace = build_trace(traces, lasso_start, args)

        return FrontEndResult(
            traces=traces,
            lasso_start=lasso_start,
            all_aps=all_aps,
            system=circuit,
            num_traces=num_traces,
            negate=negate,
            f=f,
            fold=fold,
            trace=trace,
        )
