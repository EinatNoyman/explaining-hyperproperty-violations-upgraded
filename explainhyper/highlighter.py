import sys
from formula import formula as spot
from operators import op
import spot as spot_old
import altautomaton as alt
from translator import Translator
import trace
import output
import pygraphviz as viz
from satispy import CnfFromString
from pysat.solvers import Glucose4, Lingeling, Minisat22
from pysat.formula import CNF
import re

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
                if node.is_accepting() and self.trace.is_liveness():#TODO:EVALUATE FORMULA IF NOT TRUE
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

        ##Build sat formula from trace inputs as string (all true inputs and false inputs)
        wp_traces = []
        for tid in range(num_traces):
            wp_traces.append("&".join(list(true_inputs[tid].union(false_inputs[tid]))))

        ##Build sat formula from edge labels (negated) for each trace
        def build_wp_from_edges(edgelist):
            timestep = 0
            wp_help = edgelist[0].attr['label'].replace(" ","")
            wp_list = re.split('∧|∨', wp_help)
            wp = wp_list[0] + "#" + "0"
            index = 1
            for el in wp_help[1:]:
                if el == '∧':
                    wp = wp + " & " + wp_list[index] + "#" + str(timestep)
                    index = index + 1
                elif el == '∨':
                    wp = wp + " | " + wp_list[index] + "#" + str(timestep)
                    index = index + 1
            wp = "(¬(" + wp + "))"
            timestep = 1
            for edge in edgelist[1:]:
                wp_help = edge.attr['label'].replace(" ","")
                wp_list = re.split('∧|∨', wp_help)
                wp_1 = "(¬(" + wp_list[0] + "#" + str(timestep)
                index = 1
                for el in wp_help[1:]:
                    if el == '∧':
                        wp_1 = wp_1 + " & " + wp_list[index] + "#" + str(timestep)
                        index = index + 1
                    elif el == '∨':
                        wp_1 = wp_1 + " | " + wp_list[index] + "#" + str(timestep)
                        index = index + 1
                wp = wp + " & " + wp_1 + "))"
                timestep = timestep + 1
            return wp

        wp_formulas = []
        for tid in range(num_traces):
            wp_formulas.append(build_wp_from_edges(edgelists[tid]))

        #construct cnf, build solvers, solve for each trace
        all_candidate_lists = []
        all_counterfactuals = []
        for tid in range(num_traces):
            cnf_wp, aps_wp = CnfFromString.create(wp_formulas[tid].replace("¬","-"))
            cnf_wp_trace, aps_trace = CnfFromString.create(wp_traces[tid])
            aps_combined = {**aps_wp, **aps_trace}

            cnf_wp = str(cnf_wp).replace("¬","-")
            cnf_wp_trace = str(cnf_wp_trace).replace("¬","-")

            #construct a unique mapping from ap to int
            ap_to_int_map = {}
            index = 1
            for ap in aps_combined:
                if ap not in ap_to_int_map.keys():
                    ap_to_int_map[ap.replace("¬","")] = index
                    index = index + 1

            #for every ap in cnf, convert to int according to map
            for ap in aps_combined:
                cnf_wp = cnf_wp.replace(ap.replace("¬",""),str(ap_to_int_map[ap.replace("¬","")]))

            # build sat solver
            solver = Glucose4()

            #split clauses
            cnf_wp = cnf_wp.replace(" ","")
            clause_list = cnf_wp.split("&")
            split_clause_list = []
            cnf_wp_trace = cnf_wp_trace.replace(" ", "").replace("(","").replace(")","")
            cnf_wp_trace_split = cnf_wp_trace.split("&")

            for c in clause_list:
                c = c.replace("(","").replace(")","")
                c = c.split('|')
                int_c = list(map(int,c))
                split_clause_list.append(int_c)
            for c in split_clause_list:
                solver.add_clause(c)

            #get trace as cnf and int encoded
            cnf_trace_encoded = []
            for c in cnf_wp_trace_split:
                if c.startswith("-"):
                    cnf_trace_encoded.append(ap_to_int_map[c.replace("-","")]*-1)
                else:
                    cnf_trace_encoded.append(ap_to_int_map[c.replace("-","")])

            #try to solve and get unsat core
            assumpt = cnf_trace_encoded
            core_list = []
            while (solver.solve(assumptions = assumpt) != True):
                core = solver.get_core()
                core_list.append(core)
                map(lambda x: x*-1,core)
                deleted = [item for item in assumpt if item not in core]
                assumpt = deleted
            solver.delete()

            ## reconstruct aps X timestep:
            candidate_list = []
            for cl in core_list:
                candidate = []
                for c in cl:
                    ap = list(ap_to_int_map.keys())[list(ap_to_int_map.values()).index(abs(c))]
                    ap_split_timestep = ap.split('#')
                    if (c < 0):
                        candidate.append((ap_split_timestep[0],int(ap_split_timestep[1]),0,tid))
                    else:
                        candidate.append((ap_split_timestep[0],int(ap_split_timestep[1]),1,tid))
                candidate_list.append(candidate)

            #flatten candidate list
            new_candidate_list = []
            for lst in candidate_list:
                for elm in lst:
                    new_candidate_list.append(elm)

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