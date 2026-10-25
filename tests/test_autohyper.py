"""Tests for the AutoHyper front end.

All offline: they parse a witness recorded from a real AutoHyper run
(tests/fixtures/autohyper/) rather than invoking the binary, so the suite
never depends on .NET or spot being installed.
"""

import os
import sys
from types import SimpleNamespace

import pytest

TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(TESTS_DIR)
EXPLAINHYPER_DIR = os.path.join(REPO, "explainhyper")
for _d in (EXPLAINHYPER_DIR, TESTS_DIR):
    if _d not in sys.path:
        sys.path.insert(0, _d)

import frontends
from conftest import FORMULAS
from frontends import _formula
from frontends.autohyper import parse_state, parse_witness

FIXTURES = os.path.join(TESTS_DIR, "fixtures", "autohyper")
WITNESS = os.path.join(FIXTURES, "simple_buffer_od.witness.txt")
SIMPLE_BUFFER = os.path.join(REPO, "examples", "simple_buffer")


def read_witness():
    with open(WITNESS) as handle:
        return handle.read()


class TestWitnessParser:
    def test_verdict_unsat_means_violated(self):
        verdict, _ = parse_witness(read_witness())
        assert verdict == "unsat"

    def test_one_path_per_quantifier(self):
        _, paths = parse_witness(read_witness())
        assert sorted(paths) == ["A", "B"]

    def test_prefix_and_lasso_are_separated(self):
        _, paths = parse_witness(read_witness())
        prefix, lasso = paths["A"]
        assert len(prefix) == 8 and len(lasso) == 7

    def test_state_values(self):
        assert parse_state('"secret":false, "state":true') == {
            "secret": False, "state": True}

    def test_missing_verdict_is_an_error(self):
        with pytest.raises(frontends.FrontEndError):
            parse_witness("======= Witnesses =======\nA: ({}) ({})\n=========")

    def test_a_path_without_two_groups_is_an_error(self):
        text = "======= Witnesses =======\nA: ({\"x\":true})\n=========\n\nUNSAT\n"
        with pytest.raises(frontends.FrontEndError):
            parse_witness(text)


class TestFormulaRendering:
    """`-f` stays the single source of truth; AutoHyper gets its own syntax.

    The expected strings below were accepted by a real AutoHyper 8.0 build and
    produced the witness in the fixture.
    """

    def test_simple_buffer(self):
        rendered = _formula.AutoHyperRenderer().render(FORMULAS["simple_buffer"])
        assert rendered.strip() == (
            'forall A. forall B.\n'
            'G (({"out"_A} <-> {"out"_B}))')

    def test_implication_and_three_quantifiers(self):
        assert '->' in _formula.AutoHyperRenderer().render(FORMULAS["security_in_and_out"])
        assert 'forall C.' in _formula.AutoHyperRenderer().render(FORMULAS["triple_forall"])

    def test_hyperqb_dialect_differs(self):
        rendered = _formula.HyperQbRenderer().render(FORMULAS["simple_buffer"])
        assert "out[A]" in rendered and "Forall A ." in rendered


class TestValidation:
    def test_needs_a_system_or_a_recorded_witness(self):
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("autohyper").validate(
                SimpleNamespace(aag="x", stateMachine="y"))
        assert "autohyperSystem" in str(exc.value)

    def test_recorded_witness_is_enough(self):
        frontends.get("autohyper").validate(
            SimpleNamespace(aag="x", stateMachine="y", autohyperWitness=WITNESS))


class TestLoad:
    def args(self, tmp_path):
        return SimpleNamespace(
            aag=os.path.join(SIMPLE_BUFFER, "simple_buffer.aag"),
            f=FORMULAS["simple_buffer"],
            outName=str(tmp_path / "out"),
            stateMachine=os.path.join(SIMPLE_BUFFER, "simple_buffer.dot"),
            autohyperWitness=WITNESS)

    def test_produces_a_lasso_trace(self, tmp_path):
        res = frontends.get("autohyper").load(self.args(tmp_path))
        assert res.lasso_start == 8
        assert res.trace.is_liveness()
        assert res.num_traces == 2

    def test_signal_partition_matches_the_aiger_model(self, tmp_path):
        res = frontends.get("autohyper").load(self.args(tmp_path))
        assert res.all_aps == [{"secret"}, {"out"}, {"state"}]

    def test_reported_values_agree_with_simulating_the_aag(self, tmp_path):
        """The consistency check that guards against -aag and the checker's
        model being different systems."""
        res = frontends.get("autohyper").load(self.args(tmp_path))
        assert res.diagnostics["mismatches"] == 0

    def test_sat_verdict_is_refused(self, tmp_path):
        recorded = str(tmp_path / "sat.txt")
        with open(recorded, "w") as handle:
            handle.write("======= Witnesses =======\n=========\n\nSAT\n")
        args = self.args(tmp_path)
        args.autohyperWitness = recorded
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("autohyper").load(args)
        assert "property holds" in str(exc.value)
