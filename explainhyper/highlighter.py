import sys
from formula import formula as spot
from operators import op
import spot as spot_old
import altautomaton as alt
from translator import Translator
import trace
import output
import pygraphviz as viz
import cvc5
from cvc5 import Kind
import re


def _get_atom(term_manager, cache, name):
    """Returns the (cached) cvc5 boolean constant for a given 'ap#timestep' name.
    cvc5's mkConst creates a fresh symbol on every call even for the same name,
    so callers must share one cache to get back the same Term for the same name."""
    if name not in cache:
        cache[name] = term_manager.mkConst(term_manager.getBooleanSort(), name)
    return cache[name]


def _literal_term(term_manager, cache, literal, term_to_info):
    """Builds the cvc5 term for a trace assumption literal ('ap#t' or the
    negated '¬ap#t'), and records (ap_name, timestep, polarity) so the term
    can be mapped back to a cause tuple once it comes back in an unsat core."""
    negated = literal.startswith("¬")
    raw = literal[1:] if negated else literal
    ap_name, ts_str = raw.split("#")
    atom = _get_atom(term_manager, cache, raw)
    term = term_manager.mkTerm(Kind.NOT, atom) if negated else atom
    term_to_info[term] = (ap_name, int(ts_str), 0 if negated else 1)
    return term


def _edge_literal_term(term_manager, cache, literal, timestep):
    """Builds the term for one literal of a DOT edge guard, which may carry an
    inline negation (e.g. '¬req_0'). The atom must be shared with the trace
    assumptions, so the '¬' becomes a NOT term rather than part of the name."""
    negated = literal.startswith("¬")
    raw = literal[1:] if negated else literal
    atom = _get_atom(term_manager, cache, raw + "#" + str(timestep))
    return term_manager.mkTerm(Kind.NOT, atom) if negated else atom


def _edge_label_term(term_manager, cache, label, timestep):
    """cvc5-Term equivalent of the old string-based and/or chain built from a
    DOT edge label: a left-to-right fold over the label's ∧/∨-separated
    literals (no operator precedence), matching the original semantics."""
    label = label.replace(" ", "")
    parts = re.split('∧|∨', label)
    delims = re.findall('∧|∨', label)
    term = _edge_literal_term(term_manager, cache, parts[0], timestep)
    for op_char, part in zip(delims, parts[1:]):
        nxt = _edge_literal_term(term_manager, cache, part, timestep)
        kind = Kind.AND if op_char == '∧' else Kind.OR
        term = term_manager.mkTerm(kind, term, nxt)
    return term


def _build_wp_term(term_manager, cache, edgelist):
    """cvc5 equivalent of the old build_wp_from_edges: conjunction, over every
    edge taken by the trace, of the negation of that edge's transition guard."""
    conjuncts = []
    for timestep, edge in enumerate(edgelist):
        guard = _edge_label_term(term_manager, cache, edge.attr['label'], timestep)
        negated_guard = term_manager.mkTerm(Kind.NOT, guard)
        # A tautological guard (e.g. 'up ∨ ¬up') means the transition accepts any
        # input, so it constrains nothing. Conjoining its negation would make the
        # whole query unsat on its own and mask every real cause.
        if cvc5.Solver(term_manager).checkSatAssuming(negated_guard).isUnsat():
            continue
        conjuncts.append(negated_guard)
    if not conjuncts:
        return term_manager.mkTrue()
    if len(conjuncts) == 1:
        return conjuncts[0]
    return term_manager.mkTerm(Kind.AND, *conjuncts)


class Highlighter:
    aut = None
    trace = None


    def __init__(self, automaton, trace):
        self.aut = automaton
        self.trace = trace

    def run(self, orig_formula):
        for node in reversed(self.aut.get_nodes()):
            f = spot.formula(node.label)
            if node.is_original():
                if node.is_accepting() and self.trace.accepting_holds_at_end():#TODO:EVALUATE FORMULA IF NOT TRUE
                    if self.is_true(int(node.get_label().to_str())):
                        node.set_array_at(self.trace.get_length()-1, spot.tt())
                if f._is(op.ap):
                    if f.to_str() in self.trace.value_at(self.trace.get_length()-1):
                        node.set_array_at(self.trace.get_length()-1, spot.tt())
                    else:
                        node.set_array_at(self.trace.get_length()-1, spot.ff())
        for i in range(self.trace.get_length()-1, -1, -1):
            for node in reversed(self.aut.get_nodes()):
                self.eval_orig(node, i)
            for node in reversed(self.aut.get_nodes()):
                self.eval_new(node, i)
        self.explanation_tree()




    def is_true(self, formula):
        if isinstance(formula, int):
            if formula == 0:
                return False
            if formula == 1:
                return True
        return spot_old.formula(formula.to_str())._is(spot_old.op_tt)

    def eval_orig(self, node, index):
        if node.get_result_at(index) != spot.ff():
            return
        if (node.is_original()):
            aps = self.trace.value_at(index)
            f = node.label
            nu = self.trace.value_at(index)
            if f._is(op.X) or f._is(op.tt) or f._is(op.ff): #This has the assumption of only one edge. always sat?
                node.set_array_at(index, node.get_outgoing_edges()[0].get_targets()[0].get_result_at(index + 1))
                if self.is_true(node.get_result_at(index)):
                    node.set_reason_at(index, {node.get_outgoing_edges()[0].get_targets()[0] : index+1})
            if f._is(op.ap):
                if f.to_str() in nu:
                    node.set_array_at(index,spot.tt())
                else:
                    node.set_array_at(index, spot.ff())
            if f._is(op.Not):
                if f[0].to_str() in nu:
                    node.set_array_at(index, spot.ff())
                else:
                    node.set_array_at(index, spot.tt())

    def eval_new(self, node, index):
        if not node.is_original():
            reason = []
            or_list = []
            for edge in node.get_outgoing_edges():
                and_list = []
                for target in edge.get_targets():
                    and_list.append(target.get_result_at(index))
                or_list.append(spot.And(and_list))
                if self.is_true(spot.And(and_list)):
                    reason.append(edge)
            node.set_array_at(index, spot.Or(or_list))
            if self.is_true(spot.Or(or_list)):
                reasons = {}
                #for x in reason:
                    #for n in x.get_targets():
                for n in reason[0].get_targets():
                        reasons[n] = index
                node.set_reason_at(index, reasons)

    def print_result_array(self):
        for node in self.aut.get_nodes():
            print("Node %s has values: %s" %(node.get_label().to_str(),node.result_array))
            for n in node.result_array:
                print(n.to_str())
            print("Node %s, %s has reasons: %s" % (node.get_label().to_str(), node, node.reason_array))


    def output_table_json(self):
        for n in self.aut.get_nodes():
            for i in range(len(n.result_array)):
                n.set_result_at(i, n.get_result_at(i).to_str())
        output.dump_json(self.aut)

    #Changes aut to deepcopy that is stripped to the explanation tree!!
    def explanation_tree(self):
        for node in self.aut.get_nodes():
            for i in range(self.trace.get_length()):
                node.set_array_at(i, 0)
        init = self.aut.get_init_node()
        self.explanation_tree_rec(init, 0)

    def explanation_tree_rec(self, node, at):
        node.set_array_at(at, 1)
        reason_dict = node.get_reason_at(at)
        for n, value in reason_dict.items():
           self.explanation_tree_rec(n, value)

    def formula_for_node(string):
        string = Translator.filter_out_spot_syntax_from_APs(string.replace(" ", ""))
        aplist = string.split(";")
        andlist = []
        for ap in aplist:
            value = ap.split("=")
            if ap:
                if value[1] == '0':
                    andlist.append(spot.formula("!" + value[0].replace('\'', '"')))
                else:
                    andlist.append(spot.formula(value[0].replace('\'', '"')))
        return spot.And(andlist)

    def state_eval(nu, f):
        f = spot_old.formula(f.to_str())
        if f._is(spot_old.op_tt) or f._is(spot_old.op_ff):
            return f
        if f._is(spot_old.op_ap):
            if f.to_str() in nu:
                return spot.tt()
            if f.to_str().replace("\"", "") in nu:
                return spot.tt()
            else:
                return spot.ff()
        if f._is(spot_old.op_And):
            list = []
            for child in f:
                list.append(Highlighter.state_eval(nu, child))
            return spot.And(list)
        if f._is(spot_old.op_Not):
            return spot.Not(Highlighter.state_eval(nu, f[0]))
        else:
            return f

    def dot_minimization(filename, trace, outName, all_aps, num_traces):
        number_of_all_aps = len(list(all_aps[0])) + len(list(all_aps[1])) + len(list(all_aps[2]))
        print("Size of the counter example (|Gamma|) is: " + str(number_of_all_aps * trace.get_length()))

        in_graph = viz.AGraph(filename)
        out_graph = viz.AGraph(directed=True, strict=False)
        new_edges = []
        node_formula_map = {}
        string_int_map = {}
        i = 0
        num_nodes = len(in_graph.nodes())

        #read the dot file with the lts
        for n in in_graph.nodes():
            formula = Highlighter.formula_for_node(n)
            node_formula_map[i] = formula
            out_graph.add_node(i, label=n.attr['label'])
            string_int_map[n] = i
            i = i + 1
        for e in in_graph.edges():
            newlist = []
            newlist.append(string_int_map[e[0]])
            newlist.append(string_int_map[e[1]])
            out_graph.add_edge(string_int_map[e[0]],string_int_map[e[1]], label=e.attr['label'])
            new_edges.append(tuple(newlist))
        with open(outName + ".dot", "w") as file:
           file.write(str(out_graph))

        #split the atomic propositions according to the traces
        tracemaps = [[] for n in range(num_traces)]
        trace_dicts = [{} for _ in range(num_traces)]
        for k in range(trace.get_length()):
            trace_sets = [set() for _ in range(num_traces)]
            current_values = trace.value_at(k)
            for ap in current_values:
                parts = ap.rsplit("_", 1)
                if len(parts) == 2 and parts[1].isdigit():
                    tid = int(parts[1])
                    if tid < num_traces:
                        trace_sets[tid].add(parts[0])
            for tid in range(num_traces):
                test = False
                for j in range(num_nodes):
                    if spot_old.formula(Highlighter.state_eval(trace_sets[tid], node_formula_map[j]).to_str()) == spot_old.formula.tt().to_str():
                        tracemaps[tid].append(j)
                        test = True
                        break
                if not test:
                    t = ""
                    for x in trace_sets[tid]:
                        t = t + x
                    tracemaps[tid].append(t)
                trace_dicts[tid][k] = trace_sets[tid]

        #compute edgelists from nodes in tracemap
        edgelists = [[] for _ in range(num_traces)]
        for tid in range(num_traces):
            for node_cur, node_suc in zip(tracemaps[tid], tracemaps[tid][1:]):
                edgelists[tid].append(out_graph.get_edge(node_cur, node_suc))

        #build wp models via sat solving
        #filter for inputs
        input_aps = all_aps[0]
        trace_true_inputs = [{} for _ in range(num_traces)]
        trace_false_inputs = [{} for _ in range(num_traces)]
        for tid in range(num_traces):
            for timestep in range(trace.get_length()):
                intersection = trace_dicts[tid][timestep].intersection(input_aps)
                difference = input_aps.difference(trace_dicts[tid][timestep])
                h_inter = set()
                h_difference = set()
                for l in intersection:
                    h_inter.add(l+"#"+str(timestep))
                for l in difference:
                    h_difference.add(l+"#"+str(timestep))
                trace_true_inputs[tid][timestep] = h_inter
                trace_false_inputs[tid][timestep] = h_difference

        true_inputs = [set() for _ in range(num_traces)]
        false_inputs = [set() for _ in range(num_traces)]
        for tid in range(num_traces):
            true_input_list = []
            for timestep in range(trace.get_length()):
                true_input_list.append(trace_true_inputs[tid][timestep])
            true_inputs[tid] = set().union(*true_input_list)
            false_input_list = []
            for timestep in range(trace.get_length()):
                append_not_set = set()
                for s in trace_false_inputs[tid][timestep]:
                    append_not_set.add("¬"+s)
                false_input_list.append(append_not_set)
            false_inputs[tid] = set().union(*false_input_list)

        ##Collect the trace's input literals (all true inputs and false inputs)
        wp_traces = []
        for tid in range(num_traces):
            wp_traces.append(list(true_inputs[tid].union(false_inputs[tid])))

        #build the solver query per trace and extract unsat cores with cvc5
        all_candidate_lists = []
        all_counterfactuals = []
        for tid in range(num_traces):
            term_manager = cvc5.TermManager()
            solver = cvc5.Solver(term_manager)
            solver.setOption("produce-unsat-cores", "true")
            solver.setOption("incremental", "true")

            atom_cache = {}
            term_to_info = {}

            #the negated transition guards along the trace are the hard constraint
            solver.assertFormula(_build_wp_term(term_manager, atom_cache, edgelists[tid]))

            #the trace's own input valuation enters as retractable assumptions
            assumptions = [
                _literal_term(term_manager, atom_cache, literal, term_to_info)
                for literal in wp_traces[tid]
            ]

            #repeatedly extract a core and drop it, until the rest is satisfiable
            new_candidate_list = []
            while assumptions:
                if not solver.checkSatAssuming(*assumptions).isUnsat():
                    break
                core = [t for t in solver.getUnsatCore() if t in term_to_info]
                if not core:
                    break
                for term in core:
                    ap_name, timestep, truth_value = term_to_info[term]
                    new_candidate_list.append((ap_name, timestep, truth_value, tid))
                assumptions = [a for a in assumptions if a not in core]

            #compute new input set where candidate elements are flipped
            tmp_true = set(true_inputs[tid])
            tmp_false = set(false_inputs[tid])
            for (ap,t,b,tr) in new_candidate_list:
                if (b == 0):
                    tmp_false.remove(("¬"+ap+"#"+str(t)))
                    tmp_true.add((ap+"#"+str(t)))
                else:
                    tmp_true.remove((ap+"#"+str(t)))
                    tmp_false.add(("¬"+ap+"#"+str(t)))
            flipped_inputs = tmp_true.union(tmp_false)

            list_of_inputap_to_bool = []
            for timestep in range(trace.get_length()):
                list_of_inputap_to_bool.append({})
            for ap in flipped_inputs:
                split = ap.split("#")
                timestep = split[1]
                ap_raw = split[0]
                if ap_raw.startswith("¬"):
                    list_of_inputap_to_bool[int(timestep)][ap_raw.replace("¬","")] = 0
                else:
                    list_of_inputap_to_bool[int(timestep)][ap_raw] = 1

            all_candidate_lists.append(new_candidate_list)
            all_counterfactuals.append(list_of_inputap_to_bool)

        return tracemaps, all_counterfactuals, all_candidate_lists

    # negate the cause and flip them accordingly in the trace
    # cause_lists: list of N cause lists, one per trace
    def negate_cause(cause_lists, trace, all_aps, num_traces):
        # split trace APs by trace ID
        trace_dicts = [{} for _ in range(num_traces)]
        for k in range(trace.get_length()):
            trace_sets = [set() for _ in range(num_traces)]
            current_values = trace.value_at(k)
            for ap in current_values:
                parts = ap.rsplit("_", 1)
                if len(parts) == 2 and parts[1].isdigit():
                    tid = int(parts[1])
                    if tid < num_traces:
                        trace_sets[tid].add(parts[0])
            for tid in range(num_traces):
                trace_dicts[tid][k] = trace_sets[tid]

        input_aps = all_aps[0]

        # compute true/false inputs for each trace
        true_inputs = [set() for _ in range(num_traces)]
        false_inputs = [set() for _ in range(num_traces)]
        for tid in range(num_traces):
            true_input_list = []
            false_input_list = []
            for timestep in range(trace.get_length()):
                intersection = trace_dicts[tid][timestep].intersection(input_aps)
                difference = input_aps.difference(trace_dicts[tid][timestep])
                h_inter = set()
                h_difference = set()
                for l in intersection:
                    h_inter.add(l+"#"+str(timestep))
                for l in difference:
                    h_difference.add(l+"#"+str(timestep))
                true_input_list.append(h_inter)
                append_not_set = set()
                for s in h_difference:
                    append_not_set.add("¬"+s)
                false_input_list.append(append_not_set)
            true_inputs[tid] = set().union(*true_input_list)
            false_inputs[tid] = set().union(*false_input_list)

        # compute new input set for each trace where candidate elements are flipped
        all_counterfactuals = []
        for tid in range(num_traces):
            tmp_true = set(true_inputs[tid])
            tmp_false = set(false_inputs[tid])
            for (ap,t,b,tr) in cause_lists[tid]:
                if (b == 0):
                    tmp_false.remove(("¬"+ap+"#"+str(t)))
                    tmp_true.add((ap+"#"+str(t)))
                else:
                    tmp_true.remove((ap+"#"+str(t)))
                    tmp_false.add(("¬"+ap+"#"+str(t)))
            flipped_inputs = tmp_true.union(tmp_false)

            list_of_inputap_to_bool = []
            for timestep in range(trace.get_length()):
                list_of_inputap_to_bool.append({})
            for ap in flipped_inputs:
                split = ap.split("#")
                timestep = split[1]
                ap_raw = split[0]
                if ap_raw.startswith("¬"):
                    list_of_inputap_to_bool[int(timestep)][ap_raw.replace("¬","")] = 0
                else:
                    list_of_inputap_to_bool[int(timestep)][ap_raw] = 1
            all_counterfactuals.append(list_of_inputap_to_bool)

        return all_counterfactuals


    # We assume the original formula to be in ENF! negations only in front of equiv, implication or ap
    def annotate_original_formula(self, orig_formula):
        init_node = self.aut.get_init_node()
        self.help_annotate(init_node, orig_formula)
    #Follows the original formula to insert a mapping from the NNF formula to the original formula as additional edges
    #in the automaton. For the equivalence case, two of the 4 subformulas are chosen.
    def help_annotate(self, node, orig_formula):
        formula = node.get_label()
        node.set_original_formula(orig_formula)
        edgelist = self.aut.get_outgoing_formula_edges(node)
        if not edgelist:
            return
        if not orig_formula:
            return
        if (orig_formula._is(op.Implies)) or (orig_formula._is(op.nImplies)):
            if formula._is(op.Or):
                self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
                self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
                self.help_annotate(edgelist[1].get_targets()[0], orig_formula[1])
                self.aut.create_original_formula_edge(node, [edgelist[1].get_targets()[0]])
                return
            if formula._is(op.And):
                self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
                self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
                self.help_annotate(edgelist[0].get_targets()[1], orig_formula[1])
                self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[1]])
                return
            print("Unreachable code")
            return
        if (orig_formula._is(op.Equiv)) or (orig_formula._is(op.nEquiv)):
            if formula._is(op.Or):
                l_edgelist = self.aut.get_outgoing_formula_edges(edgelist[0].get_targets()[0])  # depends on negation previously
                r_edgelist = self.aut.get_outgoing_formula_edges(edgelist[1].get_targets()[0])
                childll = l_edgelist[0].get_targets()[0]
                childlr = l_edgelist[0].get_targets()[1]
                childrl = r_edgelist[0].get_targets()[0]
                childrr = r_edgelist[0].get_targets()[1]# introduce significace of not here!
                self.aut.join_highlights_subtrees(childll, childrl)
                self.aut.join_highlights_subtrees(childlr, childrr)
                self.help_annotate(childll, orig_formula[0])
                self.help_annotate(childlr, orig_formula[1])
                self.aut.create_original_formula_edge(node, [childll])
                self.aut.create_original_formula_edge(node, [childlr])
                return
            if formula._is(op.And):
                l_edgelist = self.aut.get_outgoing_formula_edges(edgelist[0].get_targets()[0])  # depends on negation previously
                r_edgelist = self.aut.get_outgoing_formula_edges(edgelist[0].get_targets()[1])
                childll = l_edgelist[0].get_targets()[0]
                childlr = l_edgelist[1].get_targets()[0]
                childrl = r_edgelist[0].get_targets()[0]
                childrr = r_edgelist[1].get_targets()[0]  # introduce significace of not here!
                self.aut.join_highlights_subtrees(childll, childrl)
                self.aut.join_highlights_subtrees(childlr, childrr)
                self.help_annotate(childll, orig_formula[0])
                self.help_annotate(childlr, orig_formula[1])
                self.aut.create_original_formula_edge(node, [childll])
                self.aut.create_original_formula_edge(node, [childlr])
                return
            print("Unreachable code")
            return
        if formula._is(op.And):
            edge = edgelist[0].get_targets()
            i = 0
            for e in edge:
                self.help_annotate(e, orig_formula[i])
                self.aut.create_original_formula_edge(node, [e])
                i = i + 1
            return
        if formula._is(op.Or):
            i = 0
            for e in edgelist:
                self.help_annotate(e.get_targets()[0], orig_formula[i])
                self.aut.create_original_formula_edge(node, [e.get_targets()[0]])
                i = i + 1
            return
        if formula._is(op.ap) or formula._is(op.tt) or formula._is(op.ff):
            return
        if formula._is(op.Not):
            print("formula (not original) is Not")
            return
        if formula._is(op.X):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            return
        if formula._is(op.U):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            self.help_annotate(edgelist[1].get_targets()[0], orig_formula[1])
            self.aut.create_original_formula_edge(node, [edgelist[1].get_targets()[0]])
            return
        if formula._is(op.R):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            self.help_annotate(edgelist[1].get_targets()[0], orig_formula[1])
            self.aut.create_original_formula_edge(node, [edgelist[1].get_targets()[0]])
            return
        if formula._is(op.G):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            return
        if formula._is(op.F):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            return
        else:
            print("This state should not be reached.")
            print(formula.to_str())
            sys.exit()