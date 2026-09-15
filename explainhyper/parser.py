import argparse

def parse_arguments():
    parser = argparse.ArgumentParser(description='Clean up counterexample and add output values. Generates a new augmented counterexample file.')
    parser.add_argument('-cex', required=True, help='the counterexample file to be processed')
    parser.add_argument('-aag', required=True, help='the aiger file containing the system circuit') 
    parser.add_argument('-f', required=True, help='the formula that was model checked')
    parser.add_argument('-outName', required=True, help='name of output file (without file ending)')
    parser.add_argument('-stateMachine', required=False, help='The state machine that is debugged(with file ending)')
    parser.add_argument('-finiteSemantics', required=False, default='strong', choices=['strong', 'weak'],
                        help="How to treat the end of a counterexample that has no detected loop. "
                             "'strong' (default) reproduces the historical behaviour, under which G is "
                             "false at the horizon. 'weak' reads the horizon as 'nothing further "
                             "observed' and lets G hold. See STAGE0-FINDING.md.")
    args = parser.parse_args()
    return args