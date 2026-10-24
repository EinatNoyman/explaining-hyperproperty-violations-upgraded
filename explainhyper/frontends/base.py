"""Core types for model-checker front ends.

A *front end* answers one question: given the arguments, what counterexample
are we explaining, and on what system?

The key observation that keeps this small: the causality pipeline never runs a
model checker. It consumes a counterexample that a checker already produced.
And of everything the old `simulate_circuit` returned, only the per-trace
**input sequences** and the **loop point** actually came from the checker --
outputs and latches are recomputed by simulating the system. So a front end's
job reduces to:

    produce N input valuation sequences + a lasso point,

and everything else is derived exactly as before.

Consequences worth knowing:

* A checker that reports a *partial* model (HyperQB leaves variables
  unconstrained where it did not care) is fine -- unset inputs default to
  false and the rest is simulated.
* Where a checker *does* report outputs or registers, they should be
  cross-checked against the simulated values and a mismatch warned about. That
  is the only cheap defence against the checker's model and the simulated
  model being different systems.
"""

from dataclasses import dataclass, field

import trace as tr


class FrontEndError(Exception):
    """A front end cannot proceed with the arguments it was given."""


class SystemModel(object):
    """The surface the causality pipeline needs from an executable system.

    This is a *documented duck type*, not a base class -- a py-aiger circuit
    satisfies it today with no adapter, and nothing inherits from it. Listing
    it here is what makes it possible to drop in a NuSMV or Verilog model
    later without touching a single call site.

    Required attributes:
        inputs, outputs, latches
            Name collections. Must support iteration, ``in``, and
            ``sorted(list(...))``.

    Required methods:
        simulator()
            Returns a generator. The caller does ``next(sim)`` once, then
            ``sim.send({name: bool})`` per step, receiving
            ``(outputs_dict, next_latches_dict)``.
        relabel(kind, mapping)
            ``kind`` in {'input', 'output', 'latch'}. Returns a *new* model.
        write(path)
            Serialise the model to disk.
    """


@dataclass(frozen=True)
class Option:
    """One command-line option contributed by a front end.

    ``required`` is enforced by :meth:`FrontEnd.validate`, never by argparse --
    otherwise selecting one front end would make another's flags mandatory.
    """

    flag: str
    dest: str
    default: object = None
    choices: object = None
    nargs: object = None
    required: bool = False
    help: str = ""


@dataclass
class FrontEndResult:
    """Exactly what the rest of the pipeline consumes. Nothing more."""

    traces: list          # list[timestep] -> list["<ap>_<traceid>"] true then
    lasso_start: int      # -1 when no loop was detected
    all_aps: list         # EXACTLY 3 sets: [inputs, outputs, latches]
    system: object        # a SystemModel
    num_traces: int
    negate: bool
    f: object             # desugared, negation-normal-form formula
    fold: object          # pre-desugaring form, for display and annotation
    trace: object         # the built trace.Trace
    diagnostics: dict = field(default_factory=dict)


def opt(args, option):
    """Read a front-end option defensively.

    Every front-end option MUST be read through this. The integration tests
    build ``args`` as a bare ``SimpleNamespace`` field by field, so any
    unguarded attribute read would break all of them at once.
    """
    return getattr(args, option.dest, option.default)


def finite_semantics(args):
    """End-of-trace semantics for a counterexample with no detected loop.

    Defaults to FINITE_STRONG, which reproduces the historical behaviour
    exactly. Pass `-finiteSemantics weak` to treat the horizon as
    "nothing further observed" instead.
    """
    choice = getattr(args, "finiteSemantics", "strong")
    return tr.TraceSemantics.FINITE_WEAK if choice == "weak" else tr.TraceSemantics.FINITE_STRONG


def build_trace(traces, lasso_start, args):
    """Build the Trace from raw rows plus a loop point.

    Identical for every front end, so it lives here rather than being
    duplicated per checker.
    """
    trace = tr.Trace()
    if lasso_start == -1:
        trace.set_values(traces)
        # A trace with no detected loop is finite. Under FINITE_STRONG (the
        # historical default) `G phi` is false at the horizon and therefore
        # false everywhere, so the negated specification -- which for
        # `G A -> G B` is `G A & F !B` -- can never hold and the counterexample
        # is not even recognised as a violation. FINITE_WEAK reads the horizon
        # as "no violation observed within the bound" instead. See
        # STAGE0-FINDING.md.
        trace.set_semantics(finite_semantics(args))
    else:
        trace.set_values(traces[:lasso_start])
        trace.set_lasso(traces[lasso_start:len(traces) - 1])
    return trace


class FrontEnd(object):
    """Base class for a model-checker front end.

    Subclasses set :attr:`name`, :attr:`summary` and :attr:`options`, then
    implement :meth:`load`.

    **Ordering constraint on load().** ``Translator.mchyper_to_spot`` queries
    the system's ``inputs``/``outputs``/``latches`` while expanding formula
    sugar, so the formula cannot be rendered before the system is loaded.
    Every implementation must follow:

        load system -> render formula -> run checker -> parse -> simulate
    """

    name = ""
    summary = ""
    options = ()
    #: names of *common* args (declared by parser.py, not by a front end) that
    #: this front end cannot work without, e.g. "aag" for the executable model
    requires = ()

    def validate(self, args):
        """Raise :class:`FrontEndError` if the arguments are unusable.

        The default enforces ``Option.required``. Override to add
        cross-argument checks, then call ``super().validate(args)``.
        """
        missing = [o.flag for o in self.options if o.required and opt(args, o) in (None, "")]
        missing += ["-" + name for name in self.requires
                    if getattr(args, name, None) in (None, "")]
        if missing:
            raise FrontEndError(
                "front end %r requires: %s" % (self.name, ", ".join(missing)))

    def load(self, args):
        raise NotImplementedError

    def render_formula(self, mchyper_text, aps):
        """Translate the MCHyper s-expression into this checker's syntax.

        `-f` stays the single source of truth for the property; each front end
        renders it into whatever its checker accepts. The default returns the
        text unchanged, which is right for MCHyper itself.
        """
        return mchyper_text


# --------------------------------------------------------------------------
# Registry
#
# It lives here rather than in __init__ so that a front-end module can do
# `from .base import register` without importing the partially-initialised
# package it is itself being imported from.
# --------------------------------------------------------------------------

_REGISTRY = {}
_FLAGS = {}


def register(cls):
    """Class decorator that adds a front end to the registry."""
    if not cls.name:
        raise RuntimeError("front end %r has no name" % cls)
    if cls.name in _REGISTRY:
        raise RuntimeError("duplicate front end %r" % cls.name)
    for option in cls.options:
        previous = _FLAGS.get(option.flag)
        if previous is not None and previous.dest != option.dest:
            raise RuntimeError(
                "flag %s means %r in one front end and %r in %r"
                % (option.flag, previous.dest, option.dest, cls.name))
        _FLAGS[option.flag] = option
    _REGISTRY[cls.name] = cls
    return cls


def names():
    """Registered front-end names, in registration order."""
    return list(_REGISTRY)


def get(name):
    """Instantiate a front end by name."""
    if name not in _REGISTRY:
        raise FrontEndError(
            "unknown model checker %r; available: %s" % (name, ", ".join(names())))
    return _REGISTRY[name]()


def summaries():
    """[(name, summary), ...] for help text."""
    return [(n, cls.summary) for n, cls in _REGISTRY.items()]


def all_options():
    """[(owner_name, Option), ...] so the CLI can declare every flag.

    A flag shared by several front ends (``-aag``) is reported once, under the
    first front end that claimed it.
    """
    seen = set()
    result = []
    for n, cls in _REGISTRY.items():
        for o in cls.options:
            if o.flag in seen:
                continue
            seen.add(o.flag)
            result.append((n, o))
    return result
