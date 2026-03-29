"""
Shared fixtures and configuration for the test suite.
"""
import sys
import os
import pytest
from types import SimpleNamespace

# Add the explainhyper module to the path
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXPLAINHYPER_DIR = os.path.join(REPO_ROOT, "explainhyper")
EXAMPLES_DIR = os.path.join(REPO_ROOT, "examples")

sys.path.insert(0, EXPLAINHYPER_DIR)


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


# ── Example directories ──

@pytest.fixture
def running_example_dir():
    return os.path.join(EXAMPLES_DIR, "running_example")

@pytest.fixture
def security_in_and_out_dir():
    return os.path.join(EXAMPLES_DIR, "security_in_and_out")

@pytest.fixture
def drone_example_1_dir():
    return os.path.join(EXAMPLES_DIR, "drone_example_1")

@pytest.fixture
def drone_example_2_dir():
    return os.path.join(EXAMPLES_DIR, "drone_example_2")

@pytest.fixture
def asymmetric_arbiter_dir():
    return os.path.join(EXAMPLES_DIR, "asymmetric_arbiter")

@pytest.fixture
def asymmetric_arbiter_19_dir():
    return os.path.join(EXAMPLES_DIR, "asymmetric_arbiter_19")

@pytest.fixture
def triple_forall_dir():
    return os.path.join(EXAMPLES_DIR, "triple_forall")

@pytest.fixture
def triple_cause_dir():
    return os.path.join(EXAMPLES_DIR, "triple_cause")

@pytest.fixture
def simple_buffer_dir():
    return os.path.join(EXAMPLES_DIR, "simple_buffer")

@pytest.fixture
def leaky_mux_dir():
    return os.path.join(EXAMPLES_DIR, "leaky_mux")


# ── Formulas (MCHyper format) ──

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
