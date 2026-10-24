"""Tests for tools/verify_cause.py, the independent cause oracle.

A verifier that accepts everything is worthless, so most of these tests are
negative controls: causes that must be rejected, and must be rejected for the
right reason. Everything here runs on files committed under examples/ (or
built in tmp_path), never on generated run directories.
"""

import json
import os
import re
import sys

import pytest

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "tools"))

import verify_cause as v  # noqa: E402

EXAMPLES = os.path.join(REPO, "examples")

RUNNING_PHI = "G(((lo_0)<->(lo_1))&((ho_0)<->(ho_1)))"


def make_instance(tmp_path, aag, cex, plain, semantics="strong"):
    """An Instance built only from a circuit, a cex and a formula."""
    aig = v.Aiger(aag)
    _, _, remember, _ = v.read_cex(cex, aig)
    variables = {}
    for kind, names in (("input", aig.inputs), ("output", aig.outputs), ("latch", aig.latches)):
        for n in names:
            variables[n] = {"type": kind}
    path = tmp_path / "instance.json"
    path.write_text(json.dumps({"variables": variables,
                                "lassoStart": -1 if remember is None else remember,
                                "timesteps": [], "plain": plain}))
    return v.Instance(str(path), aag, cex, semantics)


def example(name):
    return (os.path.join(EXAMPLES, name, name + ".aag"),
            os.path.join(EXAMPLES, name, name + ".cex"))


# --------------------------------------------------------------------------
# 1. LTL evaluator truth table (hand-computed)
# --------------------------------------------------------------------------

A, B, E = {"a_0"}, {"b_0"}, set()
AB = {"a_0", "b_0"}

TRUTH_TABLE = [
    # (formula, prefix, loop, position, semantics, expected)
    ("G a_0", [A], [A], 0, "strong", True),
    ("G a_0", [A], [E], 0, "strong", False),
    ("F a_0", [E], [A], 0, "strong", True),        # a only in the loop
    ("F a_0", [A], [E], 0, "strong", True),
    ("F a_0", [A], [E], 1, "strong", False),       # a never comes back
    ("a_0 U b_0", [A, A], [B], 0, "strong", True),
    ("a_0 U b_0", [A, E], [B], 0, "strong", False),  # a breaks before b
    ("a_0 U b_0", [], [A], 0, "strong", False),    # b never arrives
    ("a_0 W b_0", [], [A], 0, "strong", True),     # ... but W tolerates that
    ("b_0 R a_0", [], [A], 0, "strong", True),
    ("b_0 R a_0", [A], [E], 0, "strong", False),
    ("G F a_0", [E], [E, A], 0, "strong", True),
    ("F G a_0", [A], [A, E], 0, "strong", False),
    ("F G a_0", [E], [A], 0, "strong", True),
    ("X a_0", [E], [A], 0, "strong", True),
    ("X a_0", [], [A, E], 1, "strong", True),      # wraps to the loop start
    ("X X a_0", [E, A], [E], 0, "strong", False),
    ("G (a_0 -> X b_0)", [], [A, B], 0, "strong", True),
    ("G (a_0 <-> b_0)", [AB, E], [AB], 0, "strong", True),
    ("!G a_0", [A], [A, E], 0, "strong", True),
    ("G (!a_0 | F b_0)", [A], [E, B], 0, "strong", True),
    # finite words: the strong / weak split
    ("G a_0", [A, A], [], 0, "strong", False),
    ("G a_0", [A, A], [], 0, "weak", True),
    ("G a_0", [A, E], [], 0, "weak", False),
    ("F a_0", [E, E], [], 0, "strong", False),
    ("F a_0", [E, E], [], 0, "weak", False),
    ("F a_0", [E, A], [], 0, "weak", True),
    ("!G a_0", [A], [], 0, "strong", False),       # NNF: F !a, unwitnessed
    ("!G a_0", [A], [], 0, "weak", False),
    ("!F a_0", [E], [], 0, "strong", False),       # NNF: G !a, false at horizon
    ("!F a_0", [E], [], 0, "weak", True),
    ("X a_0", [E], [], 0, "weak", False),          # X is strong at the end
    ("a_0 U b_0", [A, A], [], 0, "weak", False),
    ("b_0 R a_0", [A], [], 0, "strong", False),
    ("b_0 R a_0", [A], [], 0, "weak", True),
    ("(G a_0) -> (G b_0)", [AB, A], [], 0, "weak", False),
    ("(G a_0) -> (G b_0)", [AB, E], [], 0, "weak", True),
]


@pytest.mark.parametrize("formula,prefix,loop,pos,sem,expected", TRUTH_TABLE)
def test_ltl_truth_table(formula, prefix, loop, pos, sem, expected):
    assert v.holds(formula, (prefix, loop), pos, sem) is expected


def test_ltl_negation_is_complementary_on_lassos():
    word = ([A, E], [B, AB, E])
    for f in ["G a_0", "F b_0", "a_0 U b_0", "b_0 R a_0", "a_0 W b_0", "G F a_0", "X X b_0"]:
        for pos in range(5):
            assert v.holds(f, word, pos) != v.holds("!(%s)" % f, word, pos), (f, pos)


def test_ltl_letters_may_be_dicts():
    assert v.holds("G a_0", ([{"a_0": True}], [{"a_0": True, "b_0": False}]))


def test_parser_handles_tool_output():
    f = v.parse_formula("G((!(out_0))&(!(out_1))&(!(out_2)))")
    assert v.formula_aps(f) == {"out_0", "out_1", "out_2"}
    f = v.parse_formula("(G(((req_0_0)<->(req_0_1))))->(G((grant_0_0)<->(grant_0_1)))")
    assert v.formula_aps(f) == {"req_0_0", "req_0_1", "grant_0_0", "grant_0_1"}
    with pytest.raises(v.VerifierError):
        v.parse_formula("G(a_0 <-> )")
    with pytest.raises(v.VerifierError):
        v.parse_formula("G(nosuffix)")


# --------------------------------------------------------------------------
# 2. Simulator agreement
# --------------------------------------------------------------------------

AGREEING = ["asymmetric_arbiter", "asymmetric_arbiter_19", "drone_example_1",
            "drone_example_2", "running_example", "security_in_and_out",
            "simple_buffer", "triple_forall"]


@pytest.mark.parametrize("name", AGREEING)
def test_simulator_replays_recorded_cex(tmp_path, name):
    aag, cex = example(name)
    inst = make_instance(tmp_path, aag, cex, "true")   # the gate runs in the constructor
    assert inst.replayed_rows >= 2


def test_simulator_matches_hand_evaluation():
    aig = v.Aiger(example("simple_buffer")[0])      # out = state, state' = secret
    s = aig.initial_state()
    outs, s = aig.step(s, {"secret": True})
    assert outs == {"out": False} and s == {"state": True}
    outs, s = aig.step(s, {"secret": False})
    assert outs == {"out": True} and s == {"state": False}


def test_leaky_mux_circuit_disagrees_with_its_cex(tmp_path):
    # A real defect in the shipped instance: leaky_mux.aag drives both the
    # latch and `out` from literal 13 = !(b & sel); the mux itself (literal 15)
    # is dead logic. The recorded cex's latch values follow a real mux.
    aag, cex = example("leaky_mux")
    with pytest.raises(v.VerifierError) as err:
        make_instance(tmp_path, aag, cex, "true")
    assert err.value.code == "SYSTEM_MISMATCH"


def test_lasso_duplicate_last_row_is_dropped(tmp_path):
    aag, cex = example("security_in_and_out")
    inst = make_instance(tmp_path, aag, cex, "(G((li_0)<->(li_1)))->(G((lo_0)<->(lo_1)))")
    assert inst.lasso_start == 3
    assert inst.rows == 5                       # the cex has 6 rows; row 5 repeats row 3's state
    assert "dropped" in inst.lasso_rows


# --------------------------------------------------------------------------
# 3. Known-good: the paper's running example (Table 1: 2 causes)
# --------------------------------------------------------------------------

@pytest.fixture
def running(tmp_path):
    # MCHyper's running-example cex is flat (2 rows, no lasso). phi = G(...)
    # can only *hold* on a finite word under the weak reading, so the paper's
    # causes are checked under weak semantics.
    aag, cex = example("running_example")
    return make_instance(tmp_path, aag, cex, RUNNING_PHI, "weak")


def test_running_example_gamma_is_a_counterexample(running):
    assert running.gamma_violates


@pytest.mark.parametrize("cause", [[("hi", 0, 0, 0)], [("hi", 0, 1, 1)]])
def test_running_example_paper_causes_valid(running, cause):
    rec = running.verify(cause, 2)
    assert rec["verdict"] == "VALID", rec
    assert (rec["sat"], rec["cf"], rec["min"]) == ("pass", "pass", "pass")
    assert rec["witness_contingency"] == "{}"


def test_running_example_completeness(running):
    candidates = [("hi", 0, 0, 0), ("hi", 0, 1, 1), ("hi", 1, 0, 0), ("hi", 1, 0, 1)]
    missed = running.missed_causes(candidates, [[("hi", 0, 0, 0)], [("hi", 0, 1, 1)]], 2, 2)
    assert missed == []


def test_running_example_strong_semantics_rejects_everything(tmp_path):
    # Documented pitfall: under strong finite semantics G is false at the
    # horizon, so no counterfactual can satisfy phi and nothing verifies.
    aag, cex = example("running_example")
    inst = make_instance(tmp_path, aag, cex, RUNNING_PHI, "strong")
    rec = inst.verify([("hi", 0, 0, 0)], 2)
    assert rec["verdict"] == "INVALID" and rec["cf"] == "fail"


# --------------------------------------------------------------------------
# 4. Negative controls
# --------------------------------------------------------------------------

def test_event_not_in_gamma_fails_sat(running):
    rec = running.verify([("hi", 0, 1, 0)], 2)       # Gamma has hi_0@0 = 0
    assert rec["sat"] == "fail" and rec["verdict"] == "INVALID"
    assert "Gamma has hi=0" in rec["why"]


def test_event_past_finite_horizon_fails_sat(running):
    rec = running.verify([("hi", 7, 0, 0)], 2)
    assert rec["sat"] == "fail" and "past the end" in rec["why"]


def test_superset_of_cause_fails_min(running):
    rec = running.verify([("hi", 0, 0, 0), ("hi", 0, 1, 1)], 2)
    assert rec["sat"] == "pass" and rec["cf"] == "pass"
    assert rec["min"] == "fail" and rec["verdict"] == "INVALID"
    assert "MIN" in rec["why"]


def test_cf_quantifies_over_proper_subsets(running):
    # Flipping both hi@0 events swaps the two traces, so they still differ:
    # C' = C does not repair. C' = {hi@0(t0)} does, so CF holds -- and then
    # MIN fails, because that C' is itself a smaller cause.
    cause = [("hi", 0, 0, 0), ("hi", 0, 1, 1)]
    assert running.repairs(cause, ()) is None
    rec = running.verify(cause, 2)
    assert rec["cf"] == "pass" and rec["witness_subset"] in ("{hi@0=0(t0)}", "{hi@0=1(t1)}")
    assert rec["min"] == "fail"


def test_irrelevant_input_fails_cf(running):
    # hi at the last step only affects the state after the horizon.
    rec = running.verify([("hi", 1, 0, 0)], 2)
    assert rec["sat"] == "pass"
    assert rec["cf"] == "fail" and rec["verdict"] == "INVALID"


def test_output_event_is_rejected_as_malformed(running):
    rec = running.verify([("lo", 0, 0, 0)], 2)
    assert rec["verdict"] == "INVALID" and "MALFORMED" in rec["why"]


def test_nonexistent_trace_is_rejected(running):
    rec = running.verify([("hi", 0, 0, 5)], 2)
    assert rec["verdict"] == "INVALID" and rec["sat"] == "fail"


def test_unclosed_loop_is_not_mistaken_for_a_lasso(tmp_path):
    # simple_buffer: out(t+1) = secret(t), and secret is 1 forever on trace 0.
    # Flipping secret@0 once cannot make the outputs agree: from position 2
    # on, out_0 = 1 and out_1 = 0. A verifier that re-reads the recorded rows
    # as a lasso without checking that the loop closes would accept this.
    aag, cex = example("simple_buffer")
    inst = make_instance(tmp_path, aag, cex, "G((out_0)<->(out_1))")
    assert inst.lasso_start == 1 and inst.gamma_violates
    rec = inst.verify([("secret", 0, 1, 0)], 2)
    assert rec["cf"] == "fail" and rec["verdict"] == "INVALID"


def test_phantom_ap_fails_loudly(tmp_path):
    aag, cex = example("asymmetric_arbiter_19")         # circuit has req0, not req_0
    with pytest.raises(v.VerifierError) as err:
        make_instance(tmp_path, aag, cex, "G((req_0_0)<->(req_0_1))")
    assert err.value.code == "PHANTOM_AP"


def test_gamma_that_is_not_a_counterexample_is_reported(tmp_path):
    # drone_example_2's traces differ on `bound`, so the antecedent is false
    # and the implication holds: Gamma is not a counterexample.
    aag, cex = example("drone_example_2")
    phi = ("(G(((up_0)<->(up_1))&((bound_0)<->(bound_1))))->"
           "(G(((increase_0)<->(increase_1))&((emergency_0)<->(emergency_1))))")
    inst = make_instance(tmp_path, aag, cex, phi, "weak")
    assert not inst.gamma_violates
    assert inst.verify([("up", 1, 1, 1)], 2)["verdict"] == "UNDEFINED"


# --------------------------------------------------------------------------
# 5. Mutation
# --------------------------------------------------------------------------

@pytest.mark.parametrize("cause", [("hi", 0, 0, 0), ("hi", 0, 1, 1)])
def test_mutating_the_timestep_flips_the_verdict(running, cause):
    assert running.verify([cause], 2)["verdict"] == "VALID"
    ap, _, _, tid = cause
    mutated = (ap, 1, int(running.value_at(ap, 1, tid)), tid)   # keep SAT true
    assert running.verify([mutated], 2)["verdict"] == "INVALID"


# --------------------------------------------------------------------------
# Contingencies (Definition 4): a preemption scenario
# --------------------------------------------------------------------------
# Suzy (s) and Billy (b) both throw at t=0. Suzy's hit (sh) lands at t=1;
# Billy hits (bh) only if Suzy did not. Either hit breaks the bottle at t=2.
#   latches: lsh' = s ; lbh' = b & !s ; lbr' = lsh | lbh
#   outputs: sh = lsh ; bh = lbh ; broken = lbr

PREEMPTION_AAG = """aag 7 2 3 3 2
2
4
6 2
8 12
10 15
6
8
10
12 4 3
14 7 9
i0 s
i1 b
l0 lsh
l1 lbh
l2 lbr
o0 sh
o1 bh
o2 broken
"""

PREEMPTION_CEX = "".join("s_0@%d=%d\nb_0@%d=%d\n" % (t, t == 0, t, t == 0) for t in range(3))


@pytest.fixture
def preemption(tmp_path):
    (tmp_path / "p.aag").write_text(PREEMPTION_AAG)
    (tmp_path / "p.cex").write_text(PREEMPTION_CEX)
    return make_instance(tmp_path, str(tmp_path / "p.aag"), str(tmp_path / "p.cex"),
                         "G(!(broken_0))", "weak")


def test_preemption_gamma(preemption):
    assert preemption.gamma_violates
    assert preemption.value_at("broken", 2, 0) is True
    assert preemption.value_at("bh", 1, 0) is False


def test_preempting_cause_needs_a_contingency(preemption):
    without = preemption.verify([("s", 0, 1, 0)], 0)
    assert without["cf"] == "fail"                    # Billy's throw would take over
    rec = preemption.verify([("s", 0, 1, 0)], 2)
    assert rec["verdict"] == "VALID", rec
    assert "bh@1=0(t0)" in rec["witness_contingency"]


def test_preempted_event_is_not_a_cause(preemption):
    rec = preemption.verify([("b", 0, 1, 0)], 2)
    assert rec["cf"] == "fail" and rec["verdict"] == "INVALID"


def test_overdetermined_pair_is_not_minimal(preemption):
    rec = preemption.verify([("s", 0, 1, 0), ("b", 0, 1, 0)], 2)
    assert rec["min"] == "fail" and rec["verdict"] == "INVALID"


# --------------------------------------------------------------------------
# Independence
# --------------------------------------------------------------------------

def test_verifier_shares_no_code_with_the_tool():
    src = open(os.path.join(REPO, "tools", "verify_cause.py"), encoding="utf-8").read()
    forbidden = re.compile(r"^\s*(from|import)\s+(explainhyper|highlighter|ltl2alt|altautomaton|"
                           r"trace|formula|translator|aiger|spot|smv|output)\b", re.M)
    assert not forbidden.findall(src)
    assert "sys.path" not in src
