import parser
import aiger
import re
from trace import Trace as tr
from formula import formula as spot
import ltl2alt
import trace as tr
import highlighter
from translator import Translator
import output as out
import time
import itertools


class CauseVerificationError(Exception):
    pass


def smaller_combinations(cause):
    smaller_causes = []
    for i in range(len(cause)):
        smaller_causes.append(cause[0:i] + cause[i+1:len(cause)])
    return smaller_causes

def findsubsets(l,n):
    return list(itertools.combinations(l, n))
        
def highlight(f, trace, args, original_formula):
    transformer = ltl2alt.Ltl2Alt()
    aut = transformer.transform(spot.formula(f))
    aut.preprocess(trace.get_length())
    high = highlighter.Highlighter(aut, trace)
    high.run(original_formula)
    return high

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
    num_all = len(all_inputs) + len(all_outputs) + len(all_latches)
    all_aps = [all_inputs, all_outputs, all_latches]
    return (traces, lasso_start, all_aps, circuit)

def get_circuit_outputs(circuit, inputs):
    output_list = []
    simulator = circuit.simulator()
    next(simulator)
    output_list = [{} for i in range(len(inputs)+1)]
    for timestep in range(len(inputs)):
        current = {}
        result = simulator.send(inputs[timestep])
        output_list[timestep] = {**output_list[timestep] , **inputs[timestep], **result[0]}
        output_list[timestep+1] = {**output_list[timestep+1] , **result[1]}
    return output_list[:len(inputs)]


def _finite_semantics(args):
    """End-of-trace semantics for a counterexample with no detected loop.

    Defaults to FINITE_STRONG, which reproduces the historical behaviour
    exactly. Pass `-finiteSemantics weak` to treat the horizon as
    "nothing further observed" instead.
    """
    choice = getattr(args, "finiteSemantics", "strong")
    return tr.TraceSemantics.FINITE_WEAK if choice == "weak" else tr.TraceSemantics.FINITE_STRONG


def make_counterfactual_trace(rows, original_trace, lasso_start, all_aps, num_traces):
    """Build a counterfactual Trace that is evaluated under the same semantics
    as the counterexample it was derived from.

    An intervention flips input values; it does not change the shape of the
    trace. So a counterfactual of a lasso counterexample is itself a lasso with
    the same loop point, and gets the same prefix/lasso split.

    This used to be `tr.Trace(); set_values(rows)` with no `set_lasso`, so every
    counterfactual fell back to finite semantics while the original was
    evaluated as omega-regular. Because `G` is unsatisfiable on a finite trace
    (`highlighter.run` only seeds accepting nodes when the trace loops),
    `check_formula` then returned False for every candidate and the minimality
    search accepted the first subset it enumerated. See STAGE0-FINDING.md.

    `loop_closed` reports whether the latch valuation actually still loops at
    `lasso_start`; a False here means the flip broke the cycle and the lasso
    reading is an approximation.
    """
    counterfactual = tr.Trace(original_trace.semantics)
    latch_aps = all_aps[2] if len(all_aps) > 2 else set()
    loop_closed = None
    if lasso_start is not None and 0 <= lasso_start < len(rows):
        counterfactual.set_values(rows[:lasso_start])
        counterfactual.set_lasso(rows[lasso_start:])
        detected = tr.detect_lasso(rows, latch_aps, num_traces)
        loop_closed = (detected == lasso_start)
    else:
        counterfactual.set_values(rows)
    return counterfactual, loop_closed


def run_preprocess(args):
    # load circuit to use for simulation and formula transformation
    circuit = aiger.load(args.aag)

    # transform formula to spot input format and check if it is universal or existential
    (negate, f, num_traces) = Translator.mchyper_to_spot(args.f, circuit)
    f = spot.formula_from_spot(f)
    fold = Translator.equivalence_normal_form(f)
    f = Translator.formula_without_syntactic_sugar(fold)
    f = Translator.negative_normal_form(f)
    # simulate circuit to recover outputs and generate the augmented cex file
    (traces, lasso_start, all_aps, circuit) = simulate_circuit(args, f, circuit, num_traces)
    trace = tr.Trace()
    if (lasso_start == -1):
        trace.set_values(traces)
        # A trace with no detected loop is finite. Under FINITE_STRONG (the
        # historical default) `G phi` is false at the horizon and therefore
        # false everywhere, so the negated specification -- which for
        # `G A -> G B` is `G A & F !B` -- can never hold and the counterexample
        # is not even recognised as a violation. FINITE_WEAK reads the horizon
        # as "no violation observed within the bound" instead. See
        # STAGE0-FINDING.md.
        trace.set_semantics(_finite_semantics(args))
    else:
        trace.set_values(traces[:lasso_start])
        trace.set_lasso(traces[lasso_start:len(traces)-1])
    list = []
    if args.stateMachine:
        list, _, _ = highlighter.Highlighter.dot_minimization(args.stateMachine, trace, args.outName, all_aps, num_traces)
    dict = out.trace_to_json(all_aps, trace, args.outName, lasso_start, list, num_traces)
    if (negate):
        f = Translator.negate(f, True)
    high = highlight(f, trace, args, fold)
    high.annotate_original_formula(fold)
    out.to_json(high, args.outName, negate, dict, num_traces)
    return high

def check_formula(f, trace, args, fold, all_aps, lasso_start, num_traces=2):
    high = highlight(f, trace, args, fold)
    high.annotate_original_formula(fold)
    dict = out.trace_to_json(all_aps, trace, args.outName, lasso_start, [], num_traces)
    out.to_json(high, args.outName, False, dict, num_traces)
    if any(high.aut.get_init_node().reason_array[0]): #check if there was a reason for the init node to be true
        return True
    else:
        return False

def minimality(i, cause, original_trace, f, fold, args, circuit, all_aps, lasso_start, num_traces):
    subsets = findsubsets(cause,i)
    for subset in subsets:
        current_cause_candidate_size_i = []
        for c in subset:
            current_cause_candidate_size_i.append(c)
        # split causes by trace ID
        cause_lists = [[] for _ in range(num_traces)]
        for c in current_cause_candidate_size_i:
            (x,y,z,tra) = c
            cause_lists[tra].append(c)
        counterfactuals = highlighter.Highlighter.negate_cause(cause_lists, original_trace, all_aps, num_traces)
        # simulate each trace and combine
        trace_outputs = []
        for tid in range(num_traces):
            t = get_circuit_outputs(circuit, counterfactuals[tid])
            trace_outputs.append(Translator.ap_list_to_trace(t, str(tid)))
        trace = []
        for time in range(len(trace_outputs[0])):
            combined = []
            for tid in range(num_traces):
                combined.extend(trace_outputs[tid][time])
            trace.append(combined)
        counterfactual, _ = make_counterfactual_trace(trace, original_trace, lasso_start, all_aps, num_traces)
        if not (check_formula(f, counterfactual, args, fold, all_aps, lasso_start, num_traces)):
            return current_cause_candidate_size_i
    return []

def verify_cause(cause, original_trace, f, fold, args, circuit, all_aps, lasso_start, num_traces):
    """Verify that a cause actually resolves the violation.
    Raises CauseVerificationError if the cause is invalid."""
    cause_lists = [[] for _ in range(num_traces)]
    for c in cause:
        (x, y, z, tra) = c
        cause_lists[tra].append(c)
    counterfactuals = highlighter.Highlighter.negate_cause(cause_lists, original_trace, all_aps, num_traces)
    trace_outputs = []
    for tid in range(num_traces):
        t = get_circuit_outputs(circuit, counterfactuals[tid])
        trace_outputs.append(Translator.ap_list_to_trace(t, str(tid)))
    trace = []
    for time in range(len(trace_outputs[0])):
        combined = []
        for tid in range(num_traces):
            combined.extend(trace_outputs[tid][time])
        trace.append(combined)
    counterfactual, _ = make_counterfactual_trace(trace, original_trace, lasso_start, all_aps, num_traces)
    if check_formula(f, counterfactual, args, fold, all_aps, lasso_start, num_traces):
        raise CauseVerificationError(
            f"Invalid cause detected: {cause}\n"
            f"Flipping these inputs does NOT resolve the violation."
        )

def check_minimality(certain_elements_0, certain_elements_1, candidate_list_0, candidate_list_1, original_trace, f, fold, args, circuit, all_aps):
    print("ALL APS: "+str(all_aps))
    print("CLIST0: "+ str(candidate_list_0))
    if len(candidate_list_0) == 0 and len(candidate_list_1) == 0:
        return []
    result = False
    print("smaller combinations")
    print(smaller_combinations(candidate_list_0))
    for element in smaller_combinations(candidate_list_0):
        x, counterfactual_0, counterfactual_1 = highlighter.Highlighter.negate_cause(candidate_list_0,candidate_list_1, original_trace, all_aps)
        print("here")
        trace0 = get_circuit_outputs(circuit, counterfactual_0 )
        trace1 = get_circuit_outputs(circuit, counterfactual_1 )
        trace0 = Translator.ap_list_to_trace(trace0, "0")
        trace1 = Translator.ap_list_to_trace(trace1, "1")
        trace = []
        for time in range(len(trace0)):
            trace.append(trace0[time] + trace1[time])
        counterfactual = tr.Trace()
        counterfactual.set_values(trace)
        if (check_formula(f, counterfactual, args, fold)):
            # negation of smaller cause does not satisfy the formula
            print("Candidate cause " + str(element + candidate_list_1) + "was not a smaller element")
            liste = [x for x in element if x not in candidate_list_1]
            certain_elements_0 = certain_elements_0.append(liste[0])
            return check_minimality(certain_elements_0, certain_elements_1, element, candidate_list_1, original_trace, f, fold, args, circuit, all_aps) 
        else:
            print("Candidate cause " + str(element + candidate_list_1) + "was not a smaller element")
            print("The element "+  str(set(candidate_list_0) - (set(element))) + " is not part of the cause")
            
    for element in smaller_combinations(candidate_list_1):
        x, counterfactual_0, counterfactual_1 = highlighter.Highlighter.negate_cause(candidate_list_0, element, original_trace, all_aps)
        trace0 = get_circuit_outputs(circuit, counterfactual_0 + certain_elements_0)
        trace1 = get_circuit_outputs(circuit, counterfactual_1 + certain_elements_1)
        trace0 = Translator.ap_list_to_trace(trace0, "0")
        trace1 = Translator.ap_list_to_trace(trace1, "1")
        trace = []
        for time in range(len(trace0)):
            trace.append(trace0[time] + trace1[time])
        counterfactual = tr.Trace()
        counterfactual.set_values(trace)
        if (check_formula(f, counterfactual, args, fold)):
            # negation of smaller cause does not satisfy the formula
            liste = [x for x in element if x not in candidate_list_1]
            certain_elements_1 = certain_elements_1.append(liste[0])
            return check_minimality(certain_elements_0, certain_elements_1, candidate_list_0, element, original_trace, f, fold, args, circuit, all_aps)
        else:
            print("Candidate cause " + str(element + candidate_list_1) + "was not a smaller element")
    return candidate_list_0, candidate_list_1

def actual_causality(args):
    # load circuit to use for simulation and formula transformation
    circuit = aiger.load(args.aag)

    # start time to compute cause set (C tilde)
    start = time.time()
    (negate, f, num_traces) = Translator.mchyper_to_spot(args.f, circuit)
    f = spot.formula_from_spot(f)
    fold = Translator.equivalence_normal_form(f)
    f = Translator.formula_without_syntactic_sugar(fold)
    f = Translator.negative_normal_form(f)
    (traces, lasso_start, all_aps, circuit) = simulate_circuit(args, f, circuit, num_traces)
    trace = tr.Trace()
    if (lasso_start == -1):
        trace.set_values(traces)
        # A trace with no detected loop is finite. Under FINITE_STRONG (the
        # historical default) `G phi` is false at the horizon and therefore
        # false everywhere, so the negated specification -- which for
        # `G A -> G B` is `G A & F !B` -- can never hold and the counterexample
        # is not even recognised as a violation. FINITE_WEAK reads the horizon
        # as "no violation observed within the bound" instead. See
        # STAGE0-FINDING.md.
        trace.set_semantics(_finite_semantics(args))
    else:
        trace.set_values(traces[:lasso_start])
        trace.set_lasso(traces[lasso_start:len(traces)-1])
    list = []
    candidate_lists = [[] for _ in range(num_traces)]
    counterfactuals = [[] for _ in range(num_traces)]
    if args.stateMachine:
        list, counterfactuals, candidate_lists = highlighter.Highlighter.dot_minimization(args.stateMachine, trace, args.outName, all_aps, num_traces)
    dict = out.trace_to_json(all_aps, trace, args.outName, lasso_start, list, num_traces)
    if (negate):
        f = Translator.negate(f, True)
    end = time.time()
    #cause set (C tilde) computation done

    #call to highlight before prints to print size of formula in order
    high = highlight(f, trace, args, fold)
    print("The size of the formula (|phi|) is " + str(high.aut.counter))

    print("C tilde:")
    for tid in range(num_traces):
        print("for trace " + str(tid) + ": " + str(candidate_lists[tid]))
    print("Cause syntax: (AP, Time step, Truth value, Trace belonging)")
    print("Time to compute this set of causes (time(C tilde)):")
    print(end-start)

    #continue compute minimal causes and check counterfactuals
    high.annotate_original_formula(fold)
    out.to_json(high, args.outName, negate, dict, num_traces)
    # simulate counterfactual for each trace and combine
    trace_outputs = []
    for tid in range(num_traces):
        t = get_circuit_outputs(circuit, counterfactuals[tid])
        trace_outputs.append(Translator.ap_list_to_trace(t, str(tid)))
    original_trace = trace
    trace = []
    for timee in range(len(trace_outputs[0])):
        combined = []
        for tid in range(num_traces):
            combined.extend(trace_outputs[tid][timee])
        trace.append(combined)
    counterfactual, _ = make_counterfactual_trace(trace, original_trace, lasso_start, all_aps, num_traces)
    high = highlight(f, counterfactual, args, fold)
    total_cause = []
    for tid in range(num_traces):
        total_cause.extend(candidate_lists[tid])

    #start iteratively calling sat solver to compute all minimal causes
    print("Computing all minimal causes now...")
    all_minimal_causes = []
    counter = 1
    while total_cause:
        max_length = len(total_cause)
        while minimality(counter, total_cause, original_trace, f, fold, args, circuit, all_aps, lasso_start, num_traces):
            minimal_cause = minimality(counter, total_cause, original_trace, f, fold, args, circuit, all_aps, lasso_start, num_traces)
            all_minimal_causes.append(minimal_cause)
            verify_cause(minimal_cause, original_trace, f, fold, args, circuit, all_aps, lasso_start, num_traces)
            for (ap,t,b,tra) in minimal_cause:
                total_cause.remove((ap,t,b,tra))
        if counter >= max_length:
            break
        counter = counter + 1
    print("All minimal causes (forall C): "+str(all_minimal_causes))
    print("Number of minimal causes (# C): "+str(len(all_minimal_causes)))
    return high

def main():
    # parse arguments
    args = parser.parse_arguments()
    # preprocess cex (simulate circuit to compute outputs and cleanup cex file) and compute highlighting information
    start = time.time()
    # run cause computation
    high = actual_causality(args)
    end  = time.time()
    print("The time to compute all causes (time(forall C)) took: ")
    print(end - start)
    return

if __name__ == "__main__":
    main()