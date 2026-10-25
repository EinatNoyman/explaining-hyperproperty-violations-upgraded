import parser
import sys
import aiger
import re
from formula import formula as spot
import ltl2alt
import trace as tr
import highlighter
from translator import Translator
import output as out
import frontends
import time
import itertools
import math

# Re-exported so that `explain_hyper.simulate_circuit(args, f, circuit, num_traces)`
# keeps working -- tests call it directly with that exact signature.
from frontends.mchyper import simulate_circuit, store_inputs, write_outputs
from frontends._sim import get_circuit_outputs


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

def load_frontend(args):
    """Dispatch to the selected model-checker front end.

    `-frontend` is read with getattr so the integration tests, which build
    `args` as a bare SimpleNamespace field by field, keep defaulting to
    mchyper without having to know the flag exists.
    """
    name = getattr(args, "frontend", "mchyper")
    front = frontends.get(name)
    front.validate(args)
    return front.load(args)



def simulate_until_loop(circuit, inputs, loop_inputs):
    """Run `inputs`, then repeat `loop_inputs` until the run itself loops.

    Returns `(rows, loop_start)`: one dict per step holding that step's inputs,
    outputs and latch values (latches are the state *entering* the step, so
    row 0 carries none -- the same convention as `get_circuit_outputs`), and
    the index at which `rows` starts repeating forever.

    The system is deterministic, so once a lap of `loop_inputs` starts in a
    state that an earlier lap also started in, everything from that earlier
    lap on repeats. There are finitely many states, so this terminates.
    """
    simulator = circuit.simulator()
    next(simulator)
    rows, latches = [], {}

    def step(inp):
        nonlocal latches
        outputs, next_latches = simulator.send(inp)
        rows.append({**latches, **inp, **outputs})
        latches = next_latches

    for inp in inputs:
        step(inp)
    lap_starts = {}
    while True:
        state = tuple(sorted(latches.items()))
        if state in lap_starts:
            return rows, lap_starts[state]
        lap_starts[state] = len(rows)
        for inp in loop_inputs:
            step(inp)


def simulate_counterfactual(circuit, cf_inputs, orig_inputs, lasso_start, num_traces):
    """The zipped rows of intervene(Gamma, C) and their loop point (-1 if finite).

    `cf_inputs[tid]` is trace tid's recorded input sequence with the cause
    flipped; `orig_inputs[tid]` the same sequence unflipped.

    A cause event <a, n, t> names one position. On a lasso counterexample
    u.v^omega the intervention therefore changes that single occurrence and
    leaves every later lap of v as it was, and the counterfactual is whatever
    the system then does -- which need not loop at `lasso_start` any more, and
    whose loop can differ per trace. Two shortcuts used to stand in for this,
    both wrong (see tools/verify_cause.py):

      * re-simulating only the recorded rows and declaring rows[lasso_start:]
        the loop even when the run does not return to that state, and
      * thereby applying a flip inside the loop on *every* lap, i.e. flipping
        infinitely many events instead of one.
    """
    if lasso_start is None or lasso_start < 0:
        per_trace = [Translator.ap_list_to_trace(get_circuit_outputs(circuit, cf_inputs[tid]), str(tid))
                     for tid in range(num_traces)]
        return [[ap for tid in range(num_traces) for ap in per_trace[tid][t]]
                for t in range(len(per_trace[0]))], -1

    runs = [simulate_until_loop(circuit, cf_inputs[tid], orig_inputs[tid][lasso_start:])
            for tid in range(num_traces)]
    # Zip into one lasso: the longest prefix, and a loop as long as the least
    # common multiple of the individual loops.
    prefix = max(start for _, start in runs)
    period = 1
    for rows, start in runs:
        length = len(rows) - start
        period = period * length // math.gcd(period, length)

    def row_at(rows, start, n):
        if n < len(rows):
            return rows[n]
        return rows[start + (n - start) % (len(rows) - start)]

    zipped = []
    for n in range(prefix + period):
        combined = []
        for tid, (rows, start) in enumerate(runs):
            combined.extend(Translator.ap_list_to_trace([row_at(rows, start, n)], str(tid))[0])
        zipped.append(combined)
    return zipped, prefix


def make_counterfactual_trace(rows, original_trace, lasso_start):
    """A Trace over `rows`, evaluated under the counterexample's semantics.

    `lasso_start` is the counterfactual's *own* loop point, as computed by
    `simulate_counterfactual` -- not the counterexample's.
    """
    counterfactual = tr.Trace(original_trace.semantics)
    if lasso_start is not None and 0 <= lasso_start < len(rows):
        counterfactual.set_values(rows[:lasso_start])
        counterfactual.set_lasso(rows[lasso_start:])
    else:
        counterfactual.set_values(rows)
    return counterfactual


def counterfactual_for(cause, original_trace, circuit, all_aps, lasso_start, num_traces):
    """The Trace of intervene(Gamma, cause, {})."""
    cause_lists = [[] for _ in range(num_traces)]
    for c in cause:
        cause_lists[c[3]].append(c)
    cf_inputs = highlighter.Highlighter.negate_cause(cause_lists, original_trace, all_aps, num_traces)
    orig_inputs = cf_inputs
    if lasso_start is not None and lasso_start >= 0:
        orig_inputs = highlighter.Highlighter.negate_cause(
            [[] for _ in range(num_traces)], original_trace, all_aps, num_traces)
    rows, cf_lasso_start = simulate_counterfactual(circuit, cf_inputs, orig_inputs, lasso_start, num_traces)
    return make_counterfactual_trace(rows, original_trace, cf_lasso_start)


def run_preprocess(args):
    # ask the selected model-checker front end for the counterexample and the
    # system it runs on
    res = load_frontend(args)
    negate, f, fold = res.negate, res.f, res.fold
    num_traces, lasso_start, all_aps = res.num_traces, res.lasso_start, res.all_aps
    circuit, trace = res.system, res.trace

    list = []
    if args.stateMachine:
        list, _, _ = highlighter.Highlighter.dot_minimization(
            args.stateMachine, trace, args.outName, all_aps, num_traces,
            solver=getattr(args, "solver", "cvc5"))
    dict = out.trace_to_json(all_aps, trace, args.outName, lasso_start, list, num_traces)
    if (negate):
        f = Translator.negate(f, True)
    high = highlight(f, trace, args, fold)
    high.annotate_original_formula(fold)
    out.to_json(high, args.outName, negate, dict, num_traces)
    return high

def check_formula(f, trace, args, fold, all_aps, lasso_start, num_traces=2):
    """Does `f` hold at position 0 of `trace`?

    This used to also rewrite <outName>.json on every call, so after a run the
    file held whichever counterfactual was evaluated last rather than the
    counterexample. It now only evaluates; the JSON is written once, for Gamma.
    """
    high = highlight(f, trace, args, fold)
    return bool(any(high.aut.get_init_node().reason_array[0]))

def minimality(i, cause, original_trace, f, fold, args, circuit, all_aps, lasso_start, num_traces, found=()):
    """The first size-`i` subset of `cause` that is a minimal cause, or [].

    `f` is the specification phi: a subset qualifies when its counterfactual
    satisfies phi (CF, with the empty contingency) and it contains no
    already-found cause (MIN). Callers search sizes in increasing order and
    pass every cause found so far, so "contains no found cause" is exactly
    "no proper subset is a cause".
    """
    found_sets = [set(c) for c in found]
    for subset in findsubsets(cause, i):
        if any(fs <= set(subset) for fs in found_sets):
            continue
        counterfactual = counterfactual_for(subset, original_trace, circuit, all_aps, lasso_start, num_traces)
        if check_formula(f, counterfactual, args, fold, all_aps, lasso_start, num_traces):
            return list(subset)
    return []

def verify_cause(cause, original_trace, f, fold, args, circuit, all_aps, lasso_start, num_traces):
    """Verify that a cause actually resolves the violation.

    `f` is the specification phi. Raises CauseVerificationError unless the
    counterfactual satisfies it."""
    counterfactual = counterfactual_for(cause, original_trace, circuit, all_aps, lasso_start, num_traces)
    if not check_formula(f, counterfactual, args, fold, all_aps, lasso_start, num_traces):
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
    # Three phases are timed separately, so the cost of obtaining Gamma (a
    # property of the model checker) is not mixed into the cost of the
    # causality algorithm itself:
    #   time(Gamma)  front end: model checker run + parse + simulation
    #   time(C tilde) candidate causes (unsat cores / DOT minimisation)
    #   time(search) the minimality search over subsets of C tilde
    gamma_start = time.time()

    # ask the selected model-checker front end for the counterexample and the
    # system it runs on
    res = load_frontend(args)
    gamma_end = time.time()
    # start time to compute cause set (C tilde)
    start = time.time()
    negate, f, fold = res.negate, res.f, res.fold
    num_traces, lasso_start, all_aps = res.num_traces, res.lasso_start, res.all_aps
    circuit, trace = res.system, res.trace

    state_list = []
    candidate_lists = [[] for _ in range(num_traces)]
    if args.stateMachine:
        state_list, _, candidate_lists = highlighter.Highlighter.dot_minimization(
            args.stateMachine, trace, args.outName, all_aps, num_traces,
            solver=getattr(args, "solver", "cvc5"))
    dict = out.trace_to_json(all_aps, trace, args.outName, lasso_start, state_list, num_traces)
    # `phi` is the specification, `f` its negation: Gamma is a counterexample
    # when it satisfies f, and an intervention repairs it when the
    # counterfactual satisfies phi. On a finite trace under strong semantics
    # these are NOT complements -- both can be false -- so the repair check
    # must evaluate phi itself, never "not f".
    if (negate):
        phi = f
        f = Translator.negate(f, True)
    else:
        phi = Translator.negate(f, True)
    end = time.time()
    #cause set (C tilde) computation done

    #call to highlight before prints to print size of formula in order
    high = highlight(f, trace, args, fold)
    print("The size of the formula (|phi|) is " + str(high.aut.counter))
    if not any(high.aut.get_init_node().reason_array[0]):
        print("WARNING: the counterexample does not satisfy the negated specification "
              "under the selected semantics, so it is not a counterexample and the "
              "causes below are not meaningful. (For a flat trace, see -finiteSemantics.)")

    print("C tilde:")
    for tid in range(num_traces):
        print("for trace " + str(tid) + ": " + str(candidate_lists[tid]))
    print("Cause syntax: (AP, Time step, Truth value, Trace belonging)")
    print("Time to obtain the counterexample (time(Gamma)):")
    print(gamma_end - gamma_start)
    print("Time spent in the model checker itself (time(checker)):")
    print(res.diagnostics.get("checker_s", 0.0))
    print("Time to compute this set of causes (time(C tilde)):")
    print(end-start)

    #continue compute minimal causes and check counterfactuals
    high.annotate_original_formula(fold)
    out.to_json(high, args.outName, negate, dict, num_traces)
    original_trace = trace
    total_cause = []
    for tid in range(num_traces):
        total_cause.extend(candidate_lists[tid])

    print("Computing all minimal causes now...")
    search_start = time.time()
    # Subsets of C~ are tried from smallest to largest. A subset is a cause if
    # its counterfactual satisfies phi and it contains no smaller cause. Events
    # of a found cause stay available: causes may overlap, and removing them
    # (as this loop used to) silently skipped every cause sharing an event
    # with one found earlier.
    #
    # The subset search is exponential in |C~|, and |C~| grows with the length
    # of the counterexample -- which is a property of the model checker, not of
    # the system. AutoHyper's witnesses are far longer than MCHyper's for the
    # same property, so a cap is sometimes the difference between a result and
    # no result. Default None keeps the exhaustive behaviour.
    max_cause_size = getattr(args, "maxCauseSize", None)
    all_minimal_causes = []
    size = 1
    while size <= len(total_cause):
        # an event that is a cause on its own cannot be part of a larger one
        events = [e for e in total_cause if [e] not in all_minimal_causes]
        found_sets = [set(c) for c in all_minimal_causes]
        if all(any(fs <= set(s) for fs in found_sets) for s in findsubsets(events, size)):
            break                         # every remaining subset contains a cause
        if max_cause_size is not None and size > int(max_cause_size):
            print("stopping at cause size %s (-maxCauseSize); larger causes "
                  "were not searched" % max_cause_size)
            break
        for subset in findsubsets(events, size):
            if any(fs <= set(subset) for fs in found_sets):
                continue                  # not minimal
            counterfactual = counterfactual_for(subset, original_trace, circuit, all_aps,
                                                lasso_start, num_traces)
            if check_formula(phi, counterfactual, args, fold, all_aps, lasso_start, num_traces):
                minimal_cause = list(subset)
                verify_cause(minimal_cause, original_trace, phi, fold, args, circuit, all_aps, lasso_start, num_traces)
                all_minimal_causes.append(minimal_cause)
        size = size + 1
    print("The time of the minimality search (time(search)):")
    print(time.time() - search_start)
    print("All minimal causes (forall C): "+str(all_minimal_causes))
    print("Number of minimal causes (# C): "+str(len(all_minimal_causes)))
    return high


def main():
    # parse arguments
    args = parser.parse_arguments()
    # preprocess cex (simulate circuit to compute outputs and cleanup cex file) and compute highlighting information
    start = time.time()
    # run cause computation
    try:
        high = actual_causality(args)
    except frontends.FrontEndError as exc:
        # a front end refusing the arguments is a usage error, not a crash
        sys.stderr.write("error: %s\n" % exc)
        sys.exit(2)
    end  = time.time()
    print("The time to compute all causes (time(forall C)) took: ")
    print(end - start)
    return

if __name__ == "__main__":
    main()