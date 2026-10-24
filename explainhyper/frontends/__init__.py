"""Model-checker front ends.

Adding a checker is three steps:

    1. write ``frontends/<name>.py`` with a ``FrontEnd`` subclass
    2. decorate the class with ``@register`` (from ``.base``)
    3. add it to the import list at the bottom of this file

Registration is explicit rather than a directory scan on purpose: a scan makes
``--help`` ordering nondeterministic and turns an import error in one front end
into a silent "that checker just isn't there".

Note on imports: modules inside this package use *relative* imports for each
other (``from .base import ...``) and *absolute* imports for the flat modules
they share with the rest of the tool (``import trace``, ``from translator
import Translator``), because sys.path[0] is explainhyper/.
"""

from .base import (
    FrontEnd,
    FrontEndError,
    FrontEndResult,
    Option,
    SystemModel,
    all_options,
    build_trace,
    finite_semantics,
    get,
    names,
    opt,
    register,
    summaries,
)

# Registration happens on import. This is the one line you edit to add a checker.
from . import mchyper, autohyper, hyperqb  # noqa: E402,F401
