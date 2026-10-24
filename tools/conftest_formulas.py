"""MCHyper formulas for the bundled examples.

Mirrored from tests/conftest.py so tools/ does not depend on pytest's
sys.path handling. Keep in sync.
"""

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
