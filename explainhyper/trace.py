from enum import Enum


class TraceSemantics(Enum):
    """How the end of a trace is treated when evaluating temporal operators.

    The alternating-automaton evaluation walks time backwards and reads
    ``ff()`` past the last index (``altautomaton.Node.get_result_at``). Nodes
    flagged *accepting* -- the ``true`` self-loop nodes that ``ltl2alt`` creates
    for G, R and W -- therefore need an explicit seed at the final index, or
    ``G phi`` is false at the horizon and, by backward induction, false
    everywhere. This enum says whether to plant that seed.

    AUTO           seed iff the trace has a lasso. Historical behaviour.
    LASSO          seed. The trace is genuinely omega-regular.
    FINITE_WEAK    seed. "No violation observed within the bound" -- the
                   reading that matches a bounded model checker's verdict.
    FINITE_STRONG  do not seed. G/R/W are false at the horizon.
    """

    AUTO = "auto"
    LASSO = "lasso"
    FINITE_WEAK = "finite-weak"
    FINITE_STRONG = "finite-strong"


def latch_state_at(row, latch_aps, num_traces):
    """The latch valuation of one trace row, as a frozenset of ``ap_tid`` names.

    ``row`` is a list of AP names true at that time step, each suffixed with a
    trace id (``state0_1``). Only names whose stem is in ``latch_aps`` are kept,
    so inputs and outputs do not affect state identity.
    """
    if not row:
        return frozenset()
    state = set()
    for ap in row:
        parts = ap.rsplit("_", 1)
        if len(parts) == 2 and parts[1].isdigit() and parts[0] in latch_aps:
            state.add(ap)
    return frozenset(state)


def detect_lasso(rows, latch_aps, num_traces):
    """Index at which ``rows`` starts looping, or -1 if it does not.

    Returns the smallest ``i >= 1`` whose latch valuation equals that of the
    final row. The system is deterministic, so equal latch valuations under the
    same continuation means the suffix repeats.

    ``i = 0`` is excluded on purpose: ``get_circuit_outputs`` merges next-state
    latch values into step ``t+1``, so step 0 carries no latch entries at all
    and would spuriously match any all-false state.
    """
    if len(rows) < 2 or not latch_aps:
        return -1
    last = latch_state_at(rows[-1], latch_aps, num_traces)
    for i in range(1, len(rows) - 1):
        if latch_state_at(rows[i], latch_aps, num_traces) == last:
            return i
    return -1


class Trace:
    def __init__(self, semantics=TraceSemantics.AUTO):
        # Instance attributes. These used to be class-level mutable defaults,
        # which meant a Trace that never had set_lasso called on it silently
        # shared the class-level empty list.
        self.prefix = []
        self.lasso = []
        self.semantics = semantics

    def get_length(self):
        return len(self.prefix) + len(self.lasso)

    def value_at(self, x):
        full_trace = self.prefix + self.lasso
        if len(full_trace)-1 < x:
            return 0
        return full_trace[x]

    def is_liveness(self):
        return len(self.lasso) > 0

    def accepting_holds_at_end(self):
        """Whether accepting (G/R/W) nodes are seeded true at the last index."""
        if self.semantics is TraceSemantics.AUTO:
            return self.is_liveness()
        if self.semantics is TraceSemantics.LASSO:
            return self.is_liveness()
        return self.semantics is TraceSemantics.FINITE_WEAK

    def set_values(self, param):
        self.prefix = param

    def set_lasso(self, lasso):
        self.lasso = lasso

    def set_semantics(self, semantics):
        self.semantics = semantics

    def __str__(self) -> str:
        return str(self.prefix + self.lasso)
