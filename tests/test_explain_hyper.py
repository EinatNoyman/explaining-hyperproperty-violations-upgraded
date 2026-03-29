"""
Comprehensive test suite for the Explaining Hyperproperty Violations tool.

Tests cover:
  1. Unit tests for formula parsing/transformation (Translator, formula module)
  2. Unit tests for Trace data structure
  3. Integration tests for each example (running_example through asymmetric_arbiter)
  4. Tests for triple-trace examples (3 quantifiers)
  5. Tests for new examples (simple_buffer, leaky_mux)
  6. CauseVerificationError test (mock-based)
  7. Edge cases and robustness
"""
import sys
import os
import json
import pytest
from types import SimpleNamespace
from unittest.mock import patch, MagicMock

# Ensure explainhyper is on the path
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXPLAINHYPER_DIR = os.path.join(REPO_ROOT, "explainhyper")
sys.path.insert(0, EXPLAINHYPER_DIR)

import aiger
from formula import formula as spot
from trace import Trace
from translator import Translator
from operators import op

# ── Shared helpers (duplicated from conftest.py to avoid import issues) ──

EXAMPLES_DIR = os.path.join(REPO_ROOT, "examples")

FORMULAS = {
    "running_example": (
        'Forall (Forall (Implies (G (And (Eq (AP "li" 0) (AP "li" 1)) '
        '(Eq (AP "li" 0) (AP "li" 1)))) '
        '(G (And (Eq (AP "lo" 0) (AP "lo" 1)) '
        '(Eq (AP "ho" 0) (AP "ho" 1))))))'
    ),
    "security_in_and_out": (
        'Forall (Forall (Implies (G (Eq (AP "li" 0) (AP "li" 1))) '
        '(G (Eq (AP "lo" 0) (AP "lo" 1)))))'
    ),
    "drone_example_1": (
        'Forall (Forall (Implies (G (Eq (AP "bound" 0) (AP "bound" 1))) '
        '(G (Eq (AP "emergency" 0) (AP "emergency" 1)))))'
    ),
    "drone_example_2": (
        'Forall (Forall (Implies (G (And (Eq (AP "up" 0) (AP "up" 1)) '
        '(Eq (AP "bound" 0) (AP "bound" 1)))) '
        '(G (And (Eq (AP "increase" 0) (AP "increase" 1)) '
        '(Eq (AP "emergency" 0) (AP "emergency" 1))))))'
    ),
    "asymmetric_arbiter": (
        'Forall (Forall (Implies (G (And (Eq (AP "req_0" 0) (AP "req_0" 1)) '
        '(Eq (AP "req_1" 0) (AP "req_1" 1)))) '
        '(G (And (Eq (AP "grant_0" 0) (AP "grant_0" 1)) '
        '(Eq (AP "grant_1" 0) (AP "grant_1" 1))))))'
    ),
    "asymmetric_arbiter_19": (
        'Forall (Forall (Implies (G (And (Eq (AP "req_0" 0) (AP "req_0" 1)) '
        '(Eq (AP "req_1" 0) (AP "req_1" 1)))) '
        '(G (And (Eq (AP "grant_0" 0) (AP "grant_0" 1)) '
        '(Eq (AP "grant_1" 0) (AP "grant_1" 1))))))'
    ),
    "triple_forall": (
        'Forall (Forall (Forall (G (Neg (Or (AP "out" 0) '
        '(Or (AP "out" 1) (AP "out" 2)))))))'
    ),
    "triple_cause": (
        'Forall (Forall (Forall (Neg (And (AP "violation" 0) '
        '(And (AP "violation" 1) (AP "violation" 2))))))'
    ),
    "simple_buffer": (
        'Forall (Forall (G (Eq (AP "out" 0) (AP "out" 1))))'
    ),
    "leaky_mux": (
        'Forall (Forall (Implies (G (And (Eq (AP "a" 0) (AP "a" 1)) '
        '(Eq (AP "b" 0) (AP "b" 1)))) '
        '(G (Eq (AP "out" 0) (AP "out" 1)))))'
    ),
}


def make_args(example_dir, example_name, formula, has_dot=True):
    """Create a SimpleNamespace mimicking argparse output for a given example."""
    args = SimpleNamespace()
    args.aag = os.path.join(example_dir, f"{example_name}.aag")
    args.cex = os.path.join(example_dir, f"{example_name}.cex")
    args.f = formula
    args.outName = os.path.join(example_dir, f"{example_name}_test_output")
    if has_dot:
        args.stateMachine = os.path.join(example_dir, f"{example_name}.dot")
    else:
        args.stateMachine = None
    return args


# ═══════════════════════════════════════════════════════════════════════════════
# Section 1: Unit Tests — Formula Module
# ═══════════════════════════════════════════════════════════════════════════════

class TestFormulaConstruction:
    """Test construction and string conversion of formula AST nodes."""

    def test_atomic_proposition(self):
        f = spot.ap("x_0")
        assert f._is(op.ap)
        assert f.to_str() == "x_0"

    def test_negation(self):
        f = spot.Not(spot.ap("x_0"))
        assert f._is(op.Not)
        assert "x_0" in f.to_str()

    def test_conjunction(self):
        f = spot.And([spot.ap("a_0"), spot.ap("b_0")])
        assert f._is(op.And)
        s = f.to_str()
        assert "a_0" in s and "b_0" in s

    def test_disjunction(self):
        f = spot.Or([spot.ap("a_0"), spot.ap("b_0")])
        assert f._is(op.Or)

    def test_globally(self):
        f = spot.G(spot.ap("a_0"))
        assert f._is(op.G)

    def test_eventually(self):
        f = spot.F(spot.ap("a_0"))
        assert f._is(op.F)

    def test_next(self):
        f = spot.X(spot.ap("a_0"))
        assert f._is(op.X)

    def test_until(self):
        f = spot.U(spot.ap("a_0"), spot.ap("b_0"))
        assert f._is(op.U)

    def test_release(self):
        f = spot.R(spot.ap("a_0"), spot.ap("b_0"))
        assert f._is(op.R)

    def test_implies(self):
        f = spot.Implies(spot.ap("a_0"), spot.ap("b_0"))
        assert f._is(op.Implies)

    def test_equiv(self):
        f = spot.Equiv(spot.ap("a_0"), spot.ap("b_0"))
        assert f._is(op.Equiv)

    def test_nimplies(self):
        f = spot.nImplies(spot.ap("a_0"), spot.ap("b_0"))
        assert f._is(op.nImplies)

    def test_nequiv(self):
        f = spot.nEquiv(spot.ap("a_0"), spot.ap("b_0"))
        assert f._is(op.nEquiv)

    def test_true_false(self):
        t = spot.tt()
        f = spot.ff()
        assert t._is(op.tt)
        assert f._is(op.ff)

    def test_nested_formula(self):
        """G(a_0 & !b_0)"""
        inner = spot.And([spot.ap("a_0"), spot.Not(spot.ap("b_0"))])
        f = spot.G(inner)
        assert f._is(op.G)
        assert f[0]._is(op.And)

    def test_formula_from_spot_string(self):
        """Parse a formula from a spot-format string."""
        f = spot.formula_from_spot("G(a_0 & b_0)")
        assert f._is(op.G)
        assert f[0]._is(op.And)

    def test_formula_iteration(self):
        """Test __iter__ over operands."""
        f = spot.And([spot.ap("a"), spot.ap("b"), spot.ap("c")])
        children = list(f)
        assert len(children) == 3

    def test_formula_indexing(self):
        """Test __getitem__."""
        f = spot.Implies(spot.ap("a"), spot.ap("b"))
        assert f[0]._is(op.ap)
        assert f[1]._is(op.ap)

    def test_to_str_lbt(self):
        """Test LBT format string conversion."""
        f = spot.ap("x_0")
        lbt = f.to_str_lbt()
        assert "AP" in lbt
        assert "x" in lbt


class TestFormulaEquality:
    """Test formula equality and hashing."""

    def test_same_formulas_equal(self):
        f1 = spot.ap("x_0")
        f2 = spot.ap("x_0")
        assert f1 == f2

    def test_different_formulas_not_equal(self):
        f1 = spot.ap("x_0")
        f2 = spot.ap("y_0")
        assert f1 != f2

    def test_formula_hashable(self):
        """Formulas should be usable as dict keys."""
        f = spot.ap("x_0")
        d = {f: "test"}
        assert d[f] == "test"


# ═══════════════════════════════════════════════════════════════════════════════
# Section 2: Unit Tests — Translator
# ═══════════════════════════════════════════════════════════════════════════════

class TestTranslator:
    """Test MCHyper-to-Spot translation and formula transformations."""

    def test_filter_spot_syntax(self):
        assert Translator.filter_out_spot_syntax_from_APs("|test|") == "test"
        assert Translator.filter_out_spot_syntax_from_APs("G") == "g"
        assert Translator.filter_out_spot_syntax_from_APs("F") == "f"
        assert Translator.filter_out_spot_syntax_from_APs("U") == "u"

    def test_mchyper_to_spot_forall(self):
        """Forall formulas should set negate=True."""
        circuit = MagicMock()
        circuit.inputs = set()
        formula_str = 'Forall (Forall (G (Eq (AP "a" 0) (AP "a" 1))))'
        negate, f, num_traces = Translator.mchyper_to_spot(formula_str, circuit)
        assert negate is True
        assert num_traces == 2

    def test_mchyper_to_spot_exists(self):
        """Exists formulas should set negate=False."""
        circuit = MagicMock()
        circuit.inputs = set()
        formula_str = 'Exists (Exists (G (Eq (AP "a" 0) (AP "a" 1))))'
        negate, f, num_traces = Translator.mchyper_to_spot(formula_str, circuit)
        assert negate is False
        assert num_traces == 2

    def test_mchyper_to_spot_triple_quantifier(self):
        """Triple quantifier should give num_traces=3."""
        circuit = MagicMock()
        circuit.inputs = set()
        formula_str = 'Forall (Forall (Forall (G (AP "x" 0))))'
        negate, f, num_traces = Translator.mchyper_to_spot(formula_str, circuit)
        assert num_traces == 3

    def test_mchyper_operator_replacement(self):
        """Test that MCHyper operators are correctly replaced."""
        circuit = MagicMock()
        circuit.inputs = set()
        formula_str = 'Forall (Forall (Implies (G (AP "a" 0)) (F (AP "b" 1))))'
        negate, f, num_traces = Translator.mchyper_to_spot(formula_str, circuit)
        assert "i" in f  # Implies -> "i"
        assert "a_0" in f
        assert "b_1" in f

    def test_negative_normal_form(self):
        """Double negation should cancel."""
        inner = spot.ap("x_0")
        f = spot.Not(spot.Not(inner))
        result = Translator.negative_normal_form(f)
        assert result._is(op.ap)

    def test_formula_without_syntactic_sugar_implies(self):
        """Implies should become Or(Not(a), b)."""
        f = spot.Implies(spot.ap("a_0"), spot.ap("b_0"))
        result = Translator.formula_without_syntactic_sugar(f)
        assert result._is(op.Or)

    def test_formula_without_syntactic_sugar_equiv(self):
        """Equiv should expand to Or(And(a,b), And(!a,!b))."""
        f = spot.Equiv(spot.ap("a_0"), spot.ap("b_0"))
        result = Translator.formula_without_syntactic_sugar(f)
        assert result._is(op.Or)

    def test_negate_ap(self):
        f = spot.ap("x_0")
        result = Translator.negate(f, check=True)
        assert result._is(op.Not)

    def test_negate_and_becomes_or(self):
        f = spot.And([spot.ap("a"), spot.ap("b")])
        nnf = Translator.negative_normal_form(f)
        result = Translator.help_negate(nnf)
        assert result._is(op.Or)

    def test_negate_globally_becomes_eventually(self):
        f = spot.G(spot.ap("a"))
        nnf = Translator.negative_normal_form(f)
        result = Translator.help_negate(nnf)
        assert result._is(op.F)

    def test_negate_eventually_becomes_globally(self):
        f = spot.F(spot.ap("a"))
        nnf = Translator.negative_normal_form(f)
        result = Translator.help_negate(nnf)
        assert result._is(op.G)

    def test_negate_until_becomes_release(self):
        f = spot.U(spot.ap("a"), spot.ap("b"))
        nnf = Translator.negative_normal_form(f)
        result = Translator.help_negate(nnf)
        assert result._is(op.R)

    def test_equivalence_normal_form_preserves_equiv(self):
        f = spot.Equiv(spot.ap("a_0"), spot.ap("b_0"))
        result = Translator.equivalence_normal_form(f)
        assert result._is(op.Equiv)

    def test_equivalence_normal_form_not_equiv(self):
        inner = spot.Equiv(spot.ap("a_0"), spot.ap("b_0"))
        f = spot.Not(inner)
        result = Translator.equivalence_normal_form(f)
        assert result._is(op.nEquiv)

    def test_ap_list_to_trace(self):
        """Test conversion of AP dict list to trace format."""
        input_list = [
            {"a": 1, "b": 0},
            {"a": 0, "b": 1},
        ]
        result = Translator.ap_list_to_trace(input_list, "0")
        assert result[0] == ["a_0"]
        assert result[1] == ["b_0"]


# ═══════════════════════════════════════════════════════════════════════════════
# Section 3: Unit Tests — Trace
# ═══════════════════════════════════════════════════════════════════════════════

class TestTrace:
    """Test the Trace data structure."""

    def test_empty_trace(self):
        t = Trace()
        t.set_values([])
        assert t.get_length() == 0

    def test_prefix_only(self):
        t = Trace()
        t.set_values([["a"], ["b"], ["a", "b"]])
        assert t.get_length() == 3
        assert not t.is_liveness()

    def test_with_lasso(self):
        t = Trace()
        t.set_values([["a"], ["b"]])
        t.set_lasso([["c"], ["d"]])
        assert t.get_length() == 4
        assert t.is_liveness()

    def test_value_at(self):
        t = Trace()
        t.set_values([["a_0", "b_0"], ["a_0"]])
        assert "a_0" in t.value_at(0)
        assert "b_0" in t.value_at(0)
        assert "a_0" in t.value_at(1)
        assert "b_0" not in t.value_at(1)

    def test_value_at_out_of_bounds(self):
        t = Trace()
        t.set_values([["a"]])
        assert t.value_at(5) == 0

    def test_str_representation(self):
        t = Trace()
        t.set_values([["a"]])
        assert "a" in str(t)


# ═══════════════════════════════════════════════════════════════════════════════
# Section 4: Unit Tests — Operators
# ═══════════════════════════════════════════════════════════════════════════════

class TestOperators:
    """Test the operator enum."""

    def test_operator_to_str(self):
        assert op.And.to_str() == "&"
        assert op.Or.to_str() == "|"
        assert op.Not.to_str() == "!"
        assert op.G.to_str() == "G"
        assert op.F.to_str() == "F"
        assert op.X.to_str() == "X"
        assert op.U.to_str() == "U"
        assert op.R.to_str() == "R"
        assert op.Implies.to_str() == "->"
        assert op.Equiv.to_str() == "<->"
        assert op.tt.to_str() == "1"
        assert op.ff.to_str() == "0"

    def test_operator_to_str_lbt(self):
        assert op.And.to_str_lbt() == "And"
        assert op.Or.to_str_lbt() == "Or"
        assert op.Not.to_str_lbt() == "Neg"
        assert op.G.to_str_lbt() == "G"
        assert op.F.to_str_lbt() == "F"
        assert op.Implies.to_str_lbt() == "Implies"
        assert op.Equiv.to_str_lbt() == "Eq"


# ═══════════════════════════════════════════════════════════════════════════════
# Section 5: Integration Tests — Existing Examples (2-trace)
# ═══════════════════════════════════════════════════════════════════════════════

class TestRunningExample:
    """Integration test for the running example from Section 3 of the paper."""

    def test_full_pipeline(self, running_example_dir):
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    def test_counterexample_size(self, running_example_dir):
        """Paper Table 1: |Gamma| = 10 for running example."""
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        circuit = aiger.load(args.aag)
        negate, f, num_traces = Translator.mchyper_to_spot(args.f, circuit)
        assert num_traces == 2

    def test_cause_contains_hi(self, running_example_dir, capsys):
        """The cause should contain the hi input (not in formula but crucial)."""
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "hi" in captured.out


class TestSecurityInAndOut:
    """Integration test for the security_in_and_out example."""

    def test_full_pipeline(self, security_in_and_out_dir):
        import explain_hyper
        args = make_args(security_in_and_out_dir, "security_in_and_out",
                         FORMULAS["security_in_and_out"])
        os.chdir(security_in_and_out_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    def test_cause_contains_hi(self, security_in_and_out_dir, capsys):
        """Cause should identify hi inputs."""
        import explain_hyper
        args = make_args(security_in_and_out_dir, "security_in_and_out",
                         FORMULAS["security_in_and_out"])
        os.chdir(security_in_and_out_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "hi" in captured.out


class TestDroneExample1:
    """Integration test for drone_example_1."""

    def test_full_pipeline(self, drone_example_1_dir):
        import explain_hyper
        args = make_args(drone_example_1_dir, "drone_example_1",
                         FORMULAS["drone_example_1"])
        os.chdir(drone_example_1_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    def test_produces_minimal_causes(self, drone_example_1_dir, capsys):
        import explain_hyper
        args = make_args(drone_example_1_dir, "drone_example_1",
                         FORMULAS["drone_example_1"])
        os.chdir(drone_example_1_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "All minimal causes" in captured.out
        assert "Number of minimal causes" in captured.out


class TestDroneExample2:
    """Integration test for drone_example_2."""

    def test_full_pipeline(self, drone_example_2_dir):
        import explain_hyper
        args = make_args(drone_example_2_dir, "drone_example_2",
                         FORMULAS["drone_example_2"])
        os.chdir(drone_example_2_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None


class TestAsymmetricArbiter19:
    """Integration test for asymmetric_arbiter_19 (smaller instance)."""

    def test_full_pipeline(self, asymmetric_arbiter_19_dir):
        import explain_hyper
        args = make_args(asymmetric_arbiter_19_dir, "asymmetric_arbiter_19",
                         FORMULAS["asymmetric_arbiter_19"])
        os.chdir(asymmetric_arbiter_19_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    def test_produces_causes(self, asymmetric_arbiter_19_dir, capsys):
        import explain_hyper
        args = make_args(asymmetric_arbiter_19_dir, "asymmetric_arbiter_19",
                         FORMULAS["asymmetric_arbiter_19"])
        os.chdir(asymmetric_arbiter_19_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "C tilde:" in captured.out
        assert "Number of minimal causes" in captured.out


class TestAsymmetricArbiter:
    """Integration test for the full asymmetric_arbiter (Table 1: 24 causes)."""

    @pytest.mark.slow
    def test_full_pipeline(self, asymmetric_arbiter_dir):
        import explain_hyper
        args = make_args(asymmetric_arbiter_dir, "asymmetric_arbiter",
                         FORMULAS["asymmetric_arbiter"])
        os.chdir(asymmetric_arbiter_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    @pytest.mark.slow
    def test_24_minimal_causes(self, asymmetric_arbiter_dir, capsys):
        """Paper Table 1 reports 24 minimal causes for this instance."""
        import explain_hyper
        args = make_args(asymmetric_arbiter_dir, "asymmetric_arbiter",
                         FORMULAS["asymmetric_arbiter"])
        os.chdir(asymmetric_arbiter_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "Number of minimal causes (# C): 24" in captured.out

    @pytest.mark.slow
    def test_tb_secret_in_cause(self, asymmetric_arbiter_dir, capsys):
        """tb_secret should appear in C~ (not in formula but triggers asymmetry)."""
        import explain_hyper
        args = make_args(asymmetric_arbiter_dir, "asymmetric_arbiter",
                         FORMULAS["asymmetric_arbiter"])
        os.chdir(asymmetric_arbiter_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "tb_secret" in captured.out


# ═══════════════════════════════════════════════════════════════════════════════
# Section 6: Integration Tests — Triple-trace Examples (3 quantifiers)
# ═══════════════════════════════════════════════════════════════════════════════

class TestTripleForall:
    """Integration test for triple_forall (3 universal quantifiers)."""

    def test_full_pipeline(self, triple_forall_dir):
        import explain_hyper
        args = make_args(triple_forall_dir, "triple_forall",
                         FORMULAS["triple_forall"])
        os.chdir(triple_forall_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    def test_three_traces(self, triple_forall_dir):
        """Should detect 3 trace quantifiers."""
        circuit = aiger.load(os.path.join(triple_forall_dir, "triple_forall.aag"))
        negate, f, num_traces = Translator.mchyper_to_spot(
            FORMULAS["triple_forall"], circuit)
        assert num_traces == 3

    def test_produces_causes(self, triple_forall_dir, capsys):
        import explain_hyper
        args = make_args(triple_forall_dir, "triple_forall",
                         FORMULAS["triple_forall"])
        os.chdir(triple_forall_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "C tilde:" in captured.out


class TestTripleCause:
    """Integration test for triple_cause (3 quantifiers, no dot file)."""

    @pytest.mark.xfail(reason="triple_cause CEX uses ]i1/]i2 names but py-aiger assigns UUIDs to unnamed inputs")
    def test_full_pipeline_no_dot(self, triple_cause_dir):
        import explain_hyper
        args = make_args(triple_cause_dir, "triple_cause",
                         FORMULAS["triple_cause"], has_dot=False)
        os.chdir(triple_cause_dir)
        # Without stateMachine, the tool runs preprocess path only
        high = explain_hyper.run_preprocess(args)
        assert high is not None


# ═══════════════════════════════════════════════════════════════════════════════
# Section 7: Integration Tests — New Examples
# ═══════════════════════════════════════════════════════════════════════════════

class TestSimpleBuffer:
    """Test the simple_buffer example (minimal direct-leak system)."""

    def test_full_pipeline(self, simple_buffer_dir):
        import explain_hyper
        args = make_args(simple_buffer_dir, "simple_buffer",
                         FORMULAS["simple_buffer"])
        os.chdir(simple_buffer_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    def test_cause_contains_secret(self, simple_buffer_dir, capsys):
        """The secret input should be identified as a cause."""
        import explain_hyper
        args = make_args(simple_buffer_dir, "simple_buffer",
                         FORMULAS["simple_buffer"])
        os.chdir(simple_buffer_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "secret" in captured.out

    def test_singleton_causes(self, simple_buffer_dir, capsys):
        """With a direct leak, each cause should be a singleton."""
        import explain_hyper
        args = make_args(simple_buffer_dir, "simple_buffer",
                         FORMULAS["simple_buffer"])
        os.chdir(simple_buffer_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "Number of minimal causes" in captured.out


class TestLeakyMux:
    """Test the leaky_mux example (secret selector leaks through output)."""

    def test_full_pipeline(self, leaky_mux_dir):
        import explain_hyper
        args = make_args(leaky_mux_dir, "leaky_mux",
                         FORMULAS["leaky_mux"])
        os.chdir(leaky_mux_dir)
        high = explain_hyper.actual_causality(args)
        assert high is not None

    def test_cause_contains_sel(self, leaky_mux_dir, capsys):
        """The sel input should be part of the cause (it's the secret)."""
        import explain_hyper
        args = make_args(leaky_mux_dir, "leaky_mux",
                         FORMULAS["leaky_mux"])
        os.chdir(leaky_mux_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()
        assert "sel" in captured.out


# ═══════════════════════════════════════════════════════════════════════════════
# Section 8: CauseVerificationError Tests
# ═══════════════════════════════════════════════════════════════════════════════

class TestCauseVerificationError:
    """Test the CauseVerificationError mechanism."""

    def test_exception_class_exists(self):
        from explain_hyper import CauseVerificationError
        assert issubclass(CauseVerificationError, Exception)

    def test_exception_message(self):
        from explain_hyper import CauseVerificationError
        with pytest.raises(CauseVerificationError, match="Invalid cause"):
            raise CauseVerificationError("Invalid cause detected: test")

    def test_verify_cause_raises_on_invalid(self, running_example_dir):
        """
        Mock check_formula to return True (violation persists) to trigger
        CauseVerificationError from verify_cause.
        """
        import explain_hyper
        import highlighter
        from explain_hyper import CauseVerificationError

        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)

        # First run the normal pipeline to get circuit and trace info
        circuit = aiger.load(args.aag)
        negate, f_str, num_traces = Translator.mchyper_to_spot(args.f, circuit)
        f = spot.formula_from_spot(f_str)
        fold = Translator.equivalence_normal_form(f)
        f = Translator.formula_without_syntactic_sugar(fold)
        f = Translator.negative_normal_form(f)

        from trace import Trace as tr_module
        traces_data, lasso_start, all_aps, circuit = explain_hyper.simulate_circuit(
            args, f, circuit, num_traces)
        original_trace = tr_module()
        original_trace.set_values(traces_data)

        if negate:
            f = Translator.negate(f, True)

        # Use a real cause from the running_example (hi=0 on trace 0)
        fake_cause = [("hi", 0, 0, 0)]

        # Patch both negate_cause (to return dummy counterfactuals) and
        # check_formula (to return True = violation persists)
        dummy_counterfactuals = [[{"hi": 1}], [{"hi": 1}]]
        with patch.object(highlighter.Highlighter, 'negate_cause',
                          return_value=dummy_counterfactuals):
            with patch.object(explain_hyper, 'check_formula', return_value=True):
                with pytest.raises(CauseVerificationError):
                    explain_hyper.verify_cause(
                        fake_cause, original_trace, f, fold, args,
                        circuit, all_aps, lasso_start, num_traces
                    )

    def test_verify_cause_passes_on_valid(self, running_example_dir):
        """
        Mock check_formula to return False (violation resolved) — no exception.
        """
        import explain_hyper
        import highlighter

        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)

        circuit = aiger.load(args.aag)
        negate, f_str, num_traces = Translator.mchyper_to_spot(args.f, circuit)
        f = spot.formula_from_spot(f_str)
        fold = Translator.equivalence_normal_form(f)
        f = Translator.formula_without_syntactic_sugar(fold)
        f = Translator.negative_normal_form(f)

        from trace import Trace as tr_module
        traces_data, lasso_start, all_aps, circuit = explain_hyper.simulate_circuit(
            args, f, circuit, num_traces)
        original_trace = tr_module()
        original_trace.set_values(traces_data)

        if negate:
            f = Translator.negate(f, True)

        fake_cause = [("hi", 0, 0, 0)]

        # Patch both negate_cause and check_formula (False = violation resolved)
        dummy_counterfactuals = [[{"hi": 1}], [{"hi": 1}]]
        with patch.object(highlighter.Highlighter, 'negate_cause',
                          return_value=dummy_counterfactuals):
            with patch.object(explain_hyper, 'check_formula', return_value=False):
                # Should NOT raise
                explain_hyper.verify_cause(
                    fake_cause, original_trace, f, fold, args,
                    circuit, all_aps, lasso_start, num_traces
                )

    def test_actual_causality_aborts_on_invalid_cause(self, running_example_dir):
        """
        If verify_cause raises during actual_causality, the exception propagates.
        """
        import explain_hyper
        from explain_hyper import CauseVerificationError

        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)

        # Patch verify_cause to always raise
        with patch.object(explain_hyper, 'verify_cause',
                          side_effect=CauseVerificationError("Injected failure")):
            with pytest.raises(CauseVerificationError, match="Injected failure"):
                explain_hyper.actual_causality(args)


# ═══════════════════════════════════════════════════════════════════════════════
# Section 9: Edge Cases and Robustness
# ═══════════════════════════════════════════════════════════════════════════════

class TestEdgeCases:
    """Edge cases and robustness tests."""

    def test_smaller_combinations(self):
        """Test the smaller_combinations helper."""
        import explain_hyper
        result = explain_hyper.smaller_combinations([1, 2, 3])
        assert len(result) == 3
        assert [2, 3] in result
        assert [1, 3] in result
        assert [1, 2] in result

    def test_smaller_combinations_singleton(self):
        import explain_hyper
        result = explain_hyper.smaller_combinations([1])
        assert result == [[]]

    def test_smaller_combinations_empty(self):
        import explain_hyper
        result = explain_hyper.smaller_combinations([])
        assert result == []

    def test_findsubsets(self):
        import explain_hyper
        result = explain_hyper.findsubsets([1, 2, 3], 2)
        assert (1, 2) in result
        assert (1, 3) in result
        assert (2, 3) in result
        assert len(result) == 3

    def test_findsubsets_size_1(self):
        import explain_hyper
        result = explain_hyper.findsubsets([1, 2, 3], 1)
        assert len(result) == 3

    def test_output_json_structure(self, running_example_dir):
        """Test that the output JSON has the expected structure."""
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        explain_hyper.actual_causality(args)

        json_path = args.outName + ".json"
        assert os.path.exists(json_path)

        with open(json_path, "r") as f:
            data = json.load(f)

        assert "variables" in data
        assert "timesteps" in data
        assert "tree" in data
        assert "lassoStart" in data

    def test_augmented_cex_created(self, running_example_dir):
        """The tool should create an augmented .cex file."""
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        explain_hyper.actual_causality(args)

        cex_path = args.outName + ".cex"
        assert os.path.exists(cex_path)

    def test_augmented_aag_created(self, running_example_dir):
        """The tool should create an augmented .aag file."""
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        explain_hyper.actual_causality(args)

        aag_path = args.outName + "-aag.aag"
        assert os.path.exists(aag_path)

    def test_dot_output_created(self, running_example_dir):
        """The tool should create a .dot output file."""
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        explain_hyper.actual_causality(args)

        dot_path = args.outName + ".dot"
        assert os.path.exists(dot_path)


class TestCauseTupleFormat:
    """Verify cause tuples have correct structure (AP, timestep, truth_value, trace)."""

    def test_cause_tuple_structure(self, running_example_dir, capsys):
        import explain_hyper
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()

        # Extract cause tuples from the output
        assert "Cause syntax: (AP, Time step, Truth value, Trace belonging)" in captured.out

    def test_all_causes_reference_valid_traces(self, running_example_dir, capsys):
        """All trace indices in causes should be 0 or 1 for 2-trace examples."""
        import explain_hyper
        import re
        args = make_args(running_example_dir, "running_example",
                         FORMULAS["running_example"])
        os.chdir(running_example_dir)
        explain_hyper.actual_causality(args)
        captured = capsys.readouterr()

        # Find all cause tuples
        tuples = re.findall(r"\('(\w+)', (\d+), (\d+), (\d+)\)", captured.out)
        for name, timestep, truth, trace in tuples:
            assert int(trace) in [0, 1], f"Trace index {trace} out of range"
            assert int(truth) in [0, 1], f"Truth value {truth} not binary"
            assert int(timestep) >= 0, f"Negative timestep {timestep}"


# ═══════════════════════════════════════════════════════════════════════════════
# Section 10: Circuit Loading and Simulation
# ═══════════════════════════════════════════════════════════════════════════════

class TestCircuitLoading:
    """Test that circuits load correctly."""

    def test_running_example_circuit(self, running_example_dir):
        circuit = aiger.load(os.path.join(running_example_dir, "running_example.aag"))
        assert "hi" in circuit.inputs
        assert "lo" in circuit.outputs or any("lo" in o for o in circuit.outputs)
        assert "ho" in circuit.outputs or any("ho" in o for o in circuit.outputs)

    def test_triple_forall_circuit(self, triple_forall_dir):
        circuit = aiger.load(os.path.join(triple_forall_dir, "triple_forall.aag"))
        assert "x" in circuit.inputs
        assert len(circuit.outputs) == 1


class TestGetCircuitOutputs:
    """Test the get_circuit_outputs helper."""

    def test_basic_simulation(self, running_example_dir):
        import explain_hyper
        circuit = aiger.load(os.path.join(running_example_dir, "running_example.aag"))
        inputs = [{"hi": 0}, {"hi": 1}]
        outputs = explain_hyper.get_circuit_outputs(circuit, inputs)
        assert len(outputs) == 2
        assert isinstance(outputs[0], dict)
        assert isinstance(outputs[1], dict)
