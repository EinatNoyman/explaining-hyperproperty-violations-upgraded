import argparse

import frontends


def parse_arguments(argv=None):
    parser = argparse.ArgumentParser(
        description="Compute actual causes for a HyperLTL counterexample.")

    parser.add_argument('-frontend', required=False, default='mchyper',
                        choices=frontends.names(),
                        help="which model checker produced the counterexample "
                             "(default: mchyper)")

    # Common arguments. -aag is no longer required=True here: whether a run needs
    # it depends on the front end, so the requirement is enforced by
    # FrontEnd.validate() instead. Every existing invocation behaves the same --
    # the error message and exit code 2 are preserved below. -cex is not common
    # at all: it is MCHyper's, and that front end declares it.
    parser.add_argument('-aag', required=False,
                        help='the aiger file containing the system circuit; also the '
                             'executable model used for counterfactual simulation')
    parser.add_argument('-f', required=True, help='the formula that was model checked, '
                                                  'in MCHyper s-expression syntax')
    parser.add_argument('-outName', required=True, help='name of output file (without file ending)')
    parser.add_argument('-stateMachine', required=False, help='The state machine that is debugged(with file ending)')
    parser.add_argument('-maxCauseSize', required=False, default=None, type=int,
                        help="Stop the minimality search at causes of this size. The "
                             "search is exponential in |C~|, which grows with the length "
                             "of the counterexample; different model checkers return very "
                             "different lengths for the same property. Default: unbounded.")
    parser.add_argument('-finiteSemantics', required=False, default='strong', choices=['strong', 'weak'],
                        help="How to treat the end of a counterexample that has no detected loop. "
                             "'strong' (default) reproduces the historical behaviour, under which G is "
                             "false at the horizon. 'weak' reads the horizon as 'nothing further "
                             "observed' and lets G hold. See STAGE0-FINDING.md.")

    # Front ends contribute their own flags, grouped so --help stays readable.
    groups = {}
    for owner, option in frontends.all_options():
        if owner not in groups:
            summary = dict(frontends.summaries()).get(owner, "")
            groups[owner] = parser.add_argument_group("%s front end" % owner, summary)
        kwargs = {'dest': option.dest, 'default': option.default, 'help': option.help}
        if option.choices is not None:
            kwargs['choices'] = list(option.choices)
        if option.nargs is not None:
            kwargs['nargs'] = option.nargs
        groups[owner].add_argument(option.flag, **kwargs)

    args = parser.parse_args(argv)

    # Per-front-end requirements. parser.error() keeps the usage banner and the
    # exit code 2 that argparse's own required=True produced.
    try:
        frontends.get(args.frontend).validate(args)
    except frontends.FrontEndError as exc:
        parser.error(str(exc))
    return args
