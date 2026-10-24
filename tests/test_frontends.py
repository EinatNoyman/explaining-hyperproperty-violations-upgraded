"""Tests for the pluggable model-checker front ends (frontends/)."""

import os
import sys
from types import SimpleNamespace

import pytest

TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
EXPLAINHYPER_DIR = os.path.join(os.path.dirname(TESTS_DIR), "explainhyper")
for _d in (EXPLAINHYPER_DIR, TESTS_DIR):
    if _d not in sys.path:
        sys.path.insert(0, _d)

import aiger
import frontends
from conftest import FORMULAS
from formula import formula as spot
from translator import Translator

EXAMPLES = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")


class TestRegistry:
    def test_all_three_registered(self):
        assert frontends.names() == ["mchyper", "autohyper", "hyperqb"]

    def test_get_returns_instance(self):
        assert frontends.get("mchyper").name == "mchyper"

    def test_unknown_name_lists_alternatives(self):
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("nope")
        assert "mchyper" in str(exc.value)

    def test_every_front_end_has_a_summary(self):
        for name, summary in frontends.summaries():
            assert summary, name

    def test_option_flags_are_unique(self):
        flags = [o.flag for _, o in frontends.all_options()]
        assert len(flags) == len(set(flags))


class TestValidation:
    """Requirements are enforced by the front end, never by argparse, so that
    selecting one checker does not make another's flags mandatory."""

    def test_mchyper_needs_aag(self):
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("mchyper").validate(SimpleNamespace(cex="x"))
        assert "-aag" in str(exc.value)

    def test_mchyper_needs_cex(self):
        with pytest.raises(frontends.FrontEndError) as exc:
            frontends.get("mchyper").validate(SimpleNamespace(aag="x"))
        assert "-cex" in str(exc.value)

    def test_mchyper_accepts_both(self):
        frontends.get("mchyper").validate(SimpleNamespace(aag="x", cex="y"))

    def test_every_front_end_implements_load(self):
        """All three are implemented; none should fall through to the base
        class NotImplementedError."""
        for name in frontends.names():
            assert type(frontends.get(name)).load is not frontends.FrontEnd.load


class TestMchyperPipeline:
    """The formula chain used to be copy-pasted in four places. These lock the
    single implementation to the strings the four copies produced."""

    GOLDEN = {
        "simple_buffer": (
            True, 2,
            "G(((out_0)&(out_1))|((!(out_0))&(!(out_1))))",
            "G((out_0)<->(out_1))",
        ),
        "security_in_and_out": (
            True, 2,
            "(F(((!(li_0))|(!(li_1)))&((li_0)|(li_1))))|(G(((lo_0)&(lo_1))|((!(lo_0))&(!(lo_1)))))",
            "(G((li_0)<->(li_1)))->(G((lo_0)<->(lo_1)))",
        ),
        "triple_forall": (
            True, 3,
            "G((!(out_0))&(!(out_1))&(!(out_2)))",
            "G((!(out_0))&(!(out_1))&(!(out_2)))",
        ),
    }

    @pytest.mark.parametrize("name", sorted(GOLDEN))
    def test_golden(self, name):
        circuit = aiger.load(os.path.join(EXAMPLES, name, name + ".aag"))
        negate, f, fold, num_traces = Translator.mchyper_pipeline(FORMULAS[name], circuit)
        exp_negate, exp_num, exp_f, exp_fold = self.GOLDEN[name]
        assert (negate, num_traces) == (exp_negate, exp_num)
        assert f.to_str() == exp_f
        assert fold.to_str() == exp_fold

    def test_matches_the_manual_chain(self):
        """mchyper_pipeline must stay equivalent to spelling the chain out."""
        circuit = aiger.load(os.path.join(EXAMPLES, "simple_buffer", "simple_buffer.aag"))
        text = FORMULAS["simple_buffer"]

        negate, f, fold, num_traces = Translator.mchyper_pipeline(text, circuit)

        m_negate, m_f, m_num = Translator.mchyper_to_spot(text, circuit)
        m_f = spot.formula_from_spot(m_f)
        m_fold = Translator.equivalence_normal_form(m_f)
        m_f = Translator.negative_normal_form(
            Translator.formula_without_syntactic_sugar(m_fold))

        assert (negate, num_traces) == (m_negate, m_num)
        assert f.to_str() == m_f.to_str()
        assert fold.to_str() == m_fold.to_str()


class TestAtomRenderer:
    """`-f` is the single source of truth; each checker renders its own syntax."""

    def test_default_atom_is_the_internal_spot_naming(self):
        assert Translator.default_atom("req_0", "1") == "req_0_1"

    def test_custom_atom_is_threaded_through_the_sugar(self):
        circuit = aiger.load(
            os.path.join(EXAMPLES, "simple_buffer", "simple_buffer.aag"))
        rendered = Translator.handle_SameState(
            "0", "1", circuit, atom=lambda n, t: '{"%s"_%s}' % (n, "AB"[int(t)]))
        assert '{"state"_A}' in rendered and '{"state"_B}' in rendered

    def test_quantifier_prefix(self):
        assert Translator.quantifier_prefix("Forall (Exists (Forall (X)))") == [
            "Forall", "Exists", "Forall"]
