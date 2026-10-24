"""Tests for the NuSMV parser and interpreter (explainhyper/smv.py)."""

import itertools
import os
import sys

import pytest

TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(TESTS_DIR)
EXPLAINHYPER_DIR = os.path.join(REPO, "explainhyper")
if EXPLAINHYPER_DIR not in sys.path:
    sys.path.insert(0, EXPLAINHYPER_DIR)

import aiger
import smv

BENCH = os.path.join(REPO, "hyperqb-examples")
EXAMPLES = os.path.join(REPO, "examples")
SIMPLE_BUFFER_SMV = os.path.join(EXAMPLES, "simple_buffer", "simple_buffer.smv")
SIMPLE_BUFFER_AAG = os.path.join(EXAMPLES, "simple_buffer", "simple_buffer.aag")


class TestExpressions:
    def parse(self, text):
        return smv._ExprParser(smv.tokenize(text)).parse()

    @pytest.mark.parametrize("text,expected", [
        ("1 + 2", 3),
        ("3 - 1", 2),
        ("TRUE & FALSE", 0),
        ("TRUE | FALSE", 1),
        ("!TRUE", 0),
        ("2 = 2", 1),
        ("2 != 2", 0),
        ("1 < 2", 1),
        ("2 <= 2", 1),
        ("3 > 4", 0),
        ("3 >= 3", 1),
        ("(1 + 1) = 2", 1),
    ])
    def test_evaluation(self, text, expected):
        assert smv.evaluate(self.parse(text), {}) == expected

    def test_identifier_lookup(self):
        assert smv.evaluate(self.parse("x + 1"), {"x": 4}) == 5

    def test_case_picks_the_first_true_branch(self):
        node = self.parse("case x = 1 : 10; TRUE : 20; esac")
        assert smv.evaluate(node, {"x": 1}) == 10
        assert smv.evaluate(node, {"x": 9}) == 20

    def test_case_without_a_match_is_an_error(self):
        node = self.parse("case x = 1 : 10; esac")
        with pytest.raises(smv.SmvError):
            smv.evaluate(node, {"x": 9})

    def test_singleton_set_is_deterministic(self):
        assert smv.evaluate(self.parse("{5}"), {}) == 5

    def test_multi_set_is_a_choice(self):
        assert smv.evaluate(self.parse("{0,1,2}"), {}) == {0, 1, 2}

    def test_nondeterminism_detection(self):
        assert smv.is_nondeterministic(self.parse("{0,1}"))
        assert not smv.is_nondeterministic(self.parse("{1}"))
        assert smv.is_nondeterministic(self.parse("case x=1 : {1,2}; TRUE : 0; esac"))
        assert not smv.is_nondeterministic(self.parse("case x=1 : 1; TRUE : 0; esac"))


class TestUnsupported:
    """Constructs outside the fragment must fail loudly, never mis-execute."""

    @pytest.mark.parametrize("text", [
        "MODULE main VAR x : boolean; TRANS next(x) = x;",
        "MODULE main VAR x : boolean; INVAR x;",
        "MODULE main VAR x : array 0..3 of boolean;",
        "MODULE other VAR x : boolean;",
    ])
    def test_rejected(self, text):
        with pytest.raises(smv.SmvUnsupportedError):
            smv.parse_smv(text)

    def test_non_zero_based_range_rejected(self):
        with pytest.raises(smv.SmvUnsupportedError):
            smv.parse_smv("MODULE main VAR x : 1..3;")


class TestBenchmarkModels:
    def test_infoflow_parses(self):
        m = smv.load(os.path.join(BENCH, "infoflow", "info.smv"))
        assert m.program.var_order == ["PC_line", "NUM", "p2.pc"]
        assert m.outputs == ["halt"]            # a DEFINE here

    def test_infoflow_program_counter_counts_up(self):
        m = smv.load(os.path.join(BENCH, "infoflow", "info.smv"))
        sim = m.simulator(); next(sim)
        seen = []
        for _ in range(8):
            _, nxt = sim.send({ap: False for ap in m.inputs})
            seen.append(sum(1 << b for b in range(3) if nxt["p2.pc_b%d" % b]))
        assert seen == [1, 2, 3, 4, 5, 6, 6, 6]

    def test_nondeterministic_assignments_become_inputs(self):
        """init(PIN_*) := {1,0} is a free choice, i.e. an input.

        This is exactly what separates the two NI models: the incorrect one
        pins the secret to a single value, so it has no free input at all.
        """
        correct = smv.load(os.path.join(BENCH, "noninterference", "NI_correct.smv"))
        incorrect = smv.load(os.path.join(BENCH, "noninterference", "NI_incorrect.smv"))
        assert correct.inputs == ["PIN_0", "PIN_1"]
        assert incorrect.inputs == []

    def test_multithreaded_model_runs_to_halt(self):
        m = smv.load(os.path.join(BENCH, "noninterference", "NI_incorrect.smv"))
        sim = m.simulator(); next(sim)
        halted_at = None
        for step in range(60):
            _, nxt = sim.send({})
            if nxt["halt"] and halted_at is None:
                halted_at = step
        assert halted_at == 15


class TestAgreesWithAiger:
    """The gate for this stage: SmvModel must be a drop-in for a py-aiger
    circuit, because get_circuit_outputs re-simulates through that interface
    and that re-simulation is the intervention semantics."""

    def test_same_signal_partition(self):
        circuit = aiger.load(SIMPLE_BUFFER_AAG)
        model = smv.load(SIMPLE_BUFFER_SMV)
        assert sorted(model.inputs) == sorted(circuit.inputs)
        assert sorted(model.latches) == sorted(circuit.latches)
        assert sorted(model.outputs) == sorted(circuit.outputs)

    def test_exhaustive_step_for_step_equivalence(self):
        circuit = aiger.load(SIMPLE_BUFFER_AAG)
        model = smv.load(SIMPLE_BUFFER_SMV)
        for seq in itertools.product([False, True], repeat=7):
            a = circuit.simulator(); next(a)
            s = model.simulator(); next(s)
            for bit in seq:
                assert a.send({"secret": bit}) == s.send({"secret": bit}), seq


class TestSystemModelPlumbing:
    def test_relabel_renames_aps(self):
        model = smv.load(SIMPLE_BUFFER_SMV)
        renamed = model.relabel("output", {"out": "OUT"})
        assert renamed.outputs == ["OUT"]
        assert model.outputs == ["out"]          # original untouched

    def test_write_round_trips(self, tmp_path):
        model = smv.load(SIMPLE_BUFFER_SMV)
        target = str(tmp_path / "copy.smv")
        model.write(target)
        assert smv.load(target).program.var_order == model.program.var_order

    def test_width_encoding_matches_aiger_naming(self):
        """Width 1 keeps the bare name so names stay comparable with AIGER."""
        assert smv._ap_names("x", 1) == ["x"]
        assert smv._ap_names("x", 3) == ["x_b0", "x_b1", "x_b2"]
