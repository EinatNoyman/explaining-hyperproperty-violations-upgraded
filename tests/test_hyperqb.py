"""Tests for the HyperQB 2.0 front end.

The parser is exercised against `tests/fixtures/hyperqb/divider_excerpt.txt`,
a trimmed excerpt of real playground output (see that directory's README).
Using real text matters here: the name-splitting rule -- only a trailing
`_<digits>_<UPPER>` is structure, everything before it is the signal name --
is exactly what a written spec gets wrong.
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
from frontends.hyperqb import parse_counterexample, parse_value

FIXTURE = os.path.join(TESTS_DIR, "fixtures", "hyperqb", "divider_excerpt.txt")
SIMPLE_BUFFER = os.path.join(REPO, "examples", "simple_buffer")


def fixture_text():
    with open(FIXTURE) as handle:
        return handle.read()


def bits(token):
    return "".join("1" if b else "0" for b in parse_value(token))


class TestValueDecoding:
    @pytest.mark.parametrize("token,lsb_first", [
        ("true", "1"),
        ("false", "0"),
        ("#b1", "1"),
        ("#b0", "0"),
        ("#b1010100101", "1010010101"),   # reversed: the literal is MSB-first
        ("#x3", "1100"),
        ("#xf", "1111"),
    ])
    def test_decoding(self, token, lsb_first):
        assert bits(token) == lsb_first

    def test_hex_width_is_four_bits_per_digit(self):
        assert len(parse_value("#x3e900000")) == 32

    @pytest.mark.parametrize("token", ["#b", "#b12", "#xzz", "maybe"])
    def test_malformed_literals_are_rejected(self, token):
        with pytest.raises(frontends.FrontEndError):
            parse_value(token)


class TestCounterexampleParser:
    def test_verdict_and_bound(self):
        verdict, k, _ = parse_counterexample(fixture_text())
        assert verdict == "unsat"        # unsat means violated
        assert k == 2

    def test_both_paths_present(self):
        _, _, values = parse_counterexample(fixture_text())
        assert sorted({p for _, _, p in values}) == ["A", "B"]

    @pytest.mark.parametrize("signal", [
        "s_input_b_ack", "s_output_z_stb", "a_e", "input_b_stb", "state_var"])
    def test_signal_names_keep_their_underscores(self, signal):
        """Only the trailing `_<t>_<PATH>` is structure."""
        _, _, values = parse_counterexample(fixture_text())
        assert any(s == signal for s, _, _ in values), signal

    def test_partial_model_is_not_an_error(self):
        """HyperQB omits variables it never constrained."""
        _, _, values = parse_counterexample(fixture_text())
        assert ("input_b", 0, "A") in values
        assert ("input_b", 1, "A") not in values

    def test_wide_values_decode_to_full_width(self):
        _, _, values = parse_counterexample(fixture_text())
        assert len(values[("a", 0, "A")]) == 32

    def test_missing_result_line_is_an_error(self):
        with pytest.raises(frontends.FrontEndError):
            parse_counterexample("State 0:\n  x_0_A = true\n")

    def test_non_contiguous_state_blocks_are_an_error(self):
        text = "result: unsat.\n\nState 0:\n  x_0_A = true\n\nState 7:\n  x_7_A = true\n"
        with pytest.raises(frontends.FrontEndError) as exc:
            parse_counterexample(text)
        assert "0..k" in str(exc.value)


class TestFormulaRendering:
    def test_hq_dialect(self):
        """This exact text was accepted by a real HyperQB 2.0 build and
        produced tests/fixtures/hyperqb/simple_buffer_od.txt."""
        rendered = _formula.HyperQbRenderer().render(FORMULAS["simple_buffer"])
        assert rendered.strip() == ("Forall A . Forall B .\n"
                                    "G ((out[A] = out[B]))")

    def test_quantifier_spacing_differs_between_dialects(self):
        """HyperQB's grammar needs a space before the dot; AutoHyper's does
        not. Getting this wrong is a hard parse error, not a warning."""
        assert "Forall A ." in _formula.HyperQbRenderer().render(FORMULAS["simple_buffer"])
        assert "forall A." in _formula.AutoHyperRenderer().render(FORMULAS["simple_buffer"])

    def test_negation_uses_tilde(self):
        rendered = _formula.HyperQbRenderer().render(FORMULAS["triple_forall"])
        assert "~" in rendered and "Forall C ." in rendered


class TestValidation:
    def base(self, **kw):
        args = dict(aag="x", stateMachine="y", finiteSemantics="weak")
        args.update(kw)
        return SimpleNamespace(**args)

    def test_needs_a_model_or_a_recorded_run(self):
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("hyperqb").validate(self.base())
        assert "hyperqbModel" in str(exc.value)

    def test_running_needs_a_bound(self):
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("hyperqb").validate(self.base(hyperqbModel=["m.smv"]))
        assert "hyperqbK" in str(exc.value)

    def test_recorded_run_is_enough(self):
        frontends.get("hyperqb").validate(self.base(hyperqbOutput=FIXTURE))

    def test_warns_when_semantics_left_strong(self, capsys):
        """Flat traces + FINITE_STRONG = the counterexample does not even
        register as a violation (STAGE0-FINDING.md)."""
        frontends.get("hyperqb").validate(
            SimpleNamespace(aag="x", stateMachine="y", hyperqbOutput=FIXTURE))
        assert "finiteSemantics weak" in capsys.readouterr().out


class TestLoad:
    """Against a complete, unedited local HyperQB run on simple_buffer
    (tests/fixtures/hyperqb/simple_buffer_od.txt), whose formula was itself
    produced by HyperQbRenderer from the same -f s-expression."""

    REAL = os.path.join(TESTS_DIR, "fixtures", "hyperqb", "simple_buffer_od.txt")

    def args(self, tmp_path, recorded=None):
        return SimpleNamespace(
            aag=os.path.join(SIMPLE_BUFFER, "simple_buffer.aag"),
            f=FORMULAS["simple_buffer"],
            outName=str(tmp_path / "out"),
            stateMachine=os.path.join(SIMPLE_BUFFER, "simple_buffer.dot"),
            hyperqbOutput=recorded or self.REAL, finiteSemantics="weak")

    def test_produces_a_flat_trace(self, tmp_path):
        res = frontends.get("hyperqb").load(self.args(tmp_path))
        assert res.lasso_start == -1          # bounded checkers give no loop
        assert not res.trace.is_liveness()
        assert res.diagnostics["k"] == 4

    def test_signal_partition_matches_the_aiger_model(self, tmp_path):
        res = frontends.get("hyperqb").load(self.args(tmp_path))
        assert res.all_aps == [{"secret"}, {"out"}, {"state"}]

    def test_reported_state_agrees_with_simulating_the_aag(self, tmp_path):
        """HyperQB reports `state`; simulating the AIGER model from its
        `secret` choices must reproduce it. Guards against the SMV model and
        the -aag model being different systems."""
        res = frontends.get("hyperqb").load(self.args(tmp_path))
        assert res.diagnostics["mismatches"] == 0

    def test_inputs_drive_the_simulation(self, tmp_path):
        """out at t+1 is secret at t, so the traces diverge from step 1."""
        res = frontends.get("hyperqb").load(self.args(tmp_path))
        assert "out_0" in res.traces[1] and "out_1" not in res.traces[1]

    def test_partial_model_is_tolerated(self, tmp_path):
        """State 4 of the real fixture omits `secret` entirely."""
        res = frontends.get("hyperqb").load(self.args(tmp_path))
        assert len(res.traces) == 5

    def test_sat_verdict_is_refused(self, tmp_path):
        args = self.args(tmp_path)
        recorded = tmp_path / "sat.txt"
        recorded.write_text("result: sat.\n")
        args.hyperqbOutput = str(recorded)
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("hyperqb").load(args)
        assert "property holds" in str(exc.value)

    def test_violation_without_a_counterexample_is_refused(self, tmp_path):
        args = self.args(tmp_path)
        recorded = tmp_path / "nocex.txt"
        recorded.write_text("result: unsat.\n")
        args.hyperqbOutput = str(recorded)
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("hyperqb").load(args)
        assert "-c" in str(exc.value)
