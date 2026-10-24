#!/usr/bin/env python3
"""Translate an AIGER (.aag) circuit into an equivalent NuSMV (.smv) model.

Why this exists: the causality tool's three front ends do not read the same
file. MCHyper's counterexamples were produced on the .aag; AutoHyper and
HyperQB read NuSMV. To compare causes across all three checkers on the repo's
own examples, each example needs both encodings of *the same system* -- and
"the same" has to be provable, not assumed. A hand-written twin is exactly
where a silent semantic difference creeps in, and then the comparison measures
"different model" while claiming to measure "different checker".

So this translation is mechanical and structure-preserving:

    AIGER input       -> a free boolean VAR (nondeterministic init and next);
                         a nondeterministic assignment IS an input
    AIGER latch       -> a boolean VAR with init(.) and next(.)
    AIGER AND gate    -> one DEFINE, emitted in AIGER's own topological order
    AIGER output      -> one DEFINE

One AIGER line becomes one SMV line, so there is no room for a transcription
mistake to hide. Verify the result with --verify, which simulates both
encodings over *every* input sequence (these models are tiny -- the largest is
2^7 input/latch combinations) and compares outputs and latches step for step.

AIGER literal encoding: an even literal is a variable, an odd literal is that
variable negated, literal 0 is FALSE and 1 is TRUE.

Usage:
    python tools/aag2smv.py examples/leaky_mux/leaky_mux.aag
    python tools/aag2smv.py examples/*/[a-z]*.aag --verify --steps 10
"""

import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(REPO, "explainhyper"))


class AagError(Exception):
    pass


# ------------------------------------------------------------------ parsing

class Aag(object):
    """A parsed AIGER file in ASCII (.aag) form."""

    def __init__(self, inputs, latches, outputs, ands, names):
        self.inputs = inputs      # [literal]
        self.latches = latches    # [(current_literal, next_literal, init)]
        self.outputs = outputs    # [literal]
        self.ands = ands          # [(lhs, rhs0, rhs1)]
        self.names = names        # {"i0": name, "l0": name, "o0": name}


def parse_aag(path):
    with open(path) as handle:
        lines = [line.rstrip("\n") for line in handle]
    if not lines or not lines[0].startswith("aag "):
        raise AagError("%s is not an ASCII AIGER file (no `aag` header)" % path)

    header = lines[0].split()
    if len(header) < 6:
        raise AagError("malformed header: %r" % lines[0])
    _, max_var, n_in, n_latch, n_out, n_and = header[:6]
    n_in, n_latch, n_out, n_and = int(n_in), int(n_latch), int(n_out), int(n_and)

    cursor = 1

    def take(count):
        nonlocal cursor
        block = lines[cursor:cursor + count]
        if len(block) != count:
            raise AagError("%s: expected %d more lines" % (path, count))
        cursor += count
        return block

    inputs = [int(line.split()[0]) for line in take(n_in)]

    latches = []
    for line in take(n_latch):
        parts = line.split()
        if len(parts) == 2:
            # No initial value given. AIGER's default is 0.
            latches.append((int(parts[0]), int(parts[1]), 0))
        elif len(parts) == 3:
            latches.append((int(parts[0]), int(parts[1]), int(parts[2])))
        else:
            raise AagError("%s: malformed latch line %r" % (path, line))

    outputs = [int(line.split()[0]) for line in take(n_out)]

    ands = []
    for line in take(n_and):
        parts = line.split()
        if len(parts) != 3:
            raise AagError("%s: malformed AND line %r" % (path, line))
        ands.append(tuple(int(p) for p in parts))

    names = {}
    for line in lines[cursor:]:
        if not line or line == "c":
            break
        match = re.match(r"^([ilo])(\d+)\s+(.+)$", line)
        if match:
            names["%s%s" % (match.group(1), match.group(2))] = match.group(3).strip()

    return Aag(inputs, latches, outputs, ands, names)


# ----------------------------------------------------------------- naming

def sanitize(name):
    """An AIGER signal name -> a legal SMV identifier.

    AIGER allows `state[0]`; SMV does not. The pipeline already strips
    brackets when it builds AP names, so `state[0]` -> `state0` keeps the SMV
    variable and the AP name in agreement.
    """
    cleaned = re.sub(r"[^A-Za-z0-9_]", "", name.replace("[", "").replace("]", ""))
    if not cleaned:
        raise AagError("signal name %r has no usable characters" % name)
    if not re.match(r"^[A-Za-z_]", cleaned):
        cleaned = "s_" + cleaned
    return cleaned


# NuSMV keywords that must never be emitted as a variable name. `in` is a real
# hazard: examples/triple_cause has an AIGER input literally called `in`.
RESERVED = {
    "MODULE", "VAR", "IVAR", "ASSIGN", "DEFINE", "INIT", "TRANS", "INVAR",
    "SPEC", "LTLSPEC", "CTLSPEC", "FAIRNESS", "JUSTICE", "COMPASSION",
    "case", "esac", "init", "next", "in", "union", "xor", "xnor", "mod",
    "TRUE", "FALSE", "boolean", "array", "of", "self", "process",
}


def build_name_table(aag):
    """{variable index -> SMV identifier} for inputs, latches and AND gates."""
    table, used = {}, set()

    def claim(preferred, index):
        name = sanitize(preferred)
        if name in RESERVED or name.lower() in {r.lower() for r in RESERVED}:
            name = name + "_sig"
        base, counter = name, 2
        while name in used:
            name = "%s_%d" % (base, counter)
            counter += 1
        used.add(name)
        table[index] = name
        return name

    for position, literal in enumerate(aag.inputs):
        claim(aag.names.get("i%d" % position, "i%d" % position), literal >> 1)
    for position, (current, _, _) in enumerate(aag.latches):
        claim(aag.names.get("l%d" % position, "l%d" % position), current >> 1)
    # AND gates are internal; name them after their literal so the SMV reads
    # back against the .aag line by line.
    for lhs, _, _ in aag.ands:
        claim("g%d" % lhs, lhs >> 1)
    return table


# ---------------------------------------------------------------- emission

def literal_expr(literal, table):
    """An AIGER literal -> an SMV boolean expression (names only, no inlining)."""
    if literal == 0:
        return "FALSE"
    if literal == 1:
        return "TRUE"
    index = literal >> 1
    if index not in table:
        raise AagError("literal %d refers to undefined variable %d" % (literal, index))
    name = table[index]
    return ("(!%s)" % name) if (literal & 1) else name


def inline_expr(literal, gates, table):
    """An AIGER literal -> a fully parenthesised SMV expression.

    AND gates are substituted inline rather than emitted as DEFINEs, so that
    the SMV model exposes *exactly* the signals the AIGER exposes: inputs,
    latches, and the declared outputs. That matters for more than tidiness --
    `_sim.check_reported_values` compares every value a checker reports against
    the simulated circuit, and treats an AP it cannot find as a mismatch. An
    internal gate name present in only one of the two encodings would therefore
    show up as a spurious divergence and mask a real one.

    AIGER is a DAG, so inlining duplicates shared subterms. Measured over all
    the repo's examples the worst case is 342 nodes (asymmetric_arbiter), so
    there is no blow-up to guard against here. A gate unreachable from any
    output or latch simply disappears, which also drops the dead gates Yosys
    leaves behind.
    """
    if literal == 0:
        return "FALSE"
    if literal == 1:
        return "TRUE"
    index = literal >> 1
    negated = literal & 1
    if index in gates:
        rhs0, rhs1 = gates[index]
        text = "(%s & %s)" % (inline_expr(rhs0, gates, table),
                              inline_expr(rhs1, gates, table))
        return ("(!%s)" % text) if negated else text
    if index not in table:
        raise AagError("literal %d refers to undefined variable %d" % (literal, index))
    name = table[index]
    return ("(!%s)" % name) if negated else name


def to_smv(aag, source_name="", gates_as_defines=False):
    table = build_name_table(aag)
    input_names = [table[literal >> 1] for literal in aag.inputs]
    latch_names = [table[current >> 1] for current, _, _ in aag.latches]
    gates = {lhs >> 1: (rhs0, rhs1) for lhs, rhs0, rhs1 in aag.ands}

    def expr(literal):
        if gates_as_defines:
            return literal_expr(literal, table)
        return inline_expr(literal, gates, table)

    out = []
    out.append("-- NuSMV twin of %s, generated by tools/aag2smv.py."
               % (source_name or "an AIGER circuit"))
    out.append("-- DO NOT EDIT BY HAND: regenerate instead, so that the two")
    out.append("-- encodings cannot drift apart. Equivalence to the .aag is")
    out.append("-- checked exhaustively by `aag2smv.py --verify`.")
    out.append("--")
    if not gates_as_defines:
        out.append("-- AND gates are inlined, so this model exposes exactly the")
        out.append("-- signals the AIGER exposes: no internal gate names leak in.")
        out.append("--")
    out.append("-- A free input is written as a nondeterministic assignment:")
    out.append("-- in NuSMV, nondeterministic choice IS an input. AutoHyper")
    out.append("-- requires {TRUE, FALSE} for a boolean, not {0,1}.")
    if input_names:
        out.append("--")
        out.append("-- inputs : %s" % ", ".join(input_names))
    if latch_names:
        out.append("-- latches: %s" % ", ".join(latch_names))
    out.append("MODULE main")

    out.append("VAR")
    for name in latch_names:
        out.append("  %s : boolean;" % name)
    for name in input_names:
        out.append("  %s : boolean;" % name)

    out.append("ASSIGN")
    for (current, next_literal, init) in aag.latches:
        name = table[current >> 1]
        if init not in (0, 1):
            # init == current literal means "uninitialised" in the AIGER spec.
            raise AagError(
                "latch %s has a non-constant initial value (%d); not supported"
                % (name, init))
        out.append("  init(%s) := %s;" % (name, "TRUE" if init == 1 else "FALSE"))
        out.append("  next(%s) := %s;" % (name, expr(next_literal)))
    if latch_names and input_names:
        out.append("")
    for name in input_names:
        out.append("  init(%s) := {TRUE, FALSE};" % name)
        out.append("  next(%s) := {TRUE, FALSE};" % name)

    define_lines = []
    if gates_as_defines:
        # AIGER emits AND gates so that both operands are already defined;
        # keeping that order means the DEFINE block needs no reordering.
        for (lhs, rhs0, rhs1) in aag.ands:
            define_lines.append("  %s := %s & %s;" % (
                table[lhs >> 1], literal_expr(rhs0, table), literal_expr(rhs1, table)))
    for position, literal in enumerate(aag.outputs):
        output_name = sanitize(aag.names.get("o%d" % position, "o%d" % position))
        define_lines.append("  %s := %s;" % (output_name, expr(literal)))
    if define_lines:
        out.append("DEFINE")
        out.extend(define_lines)

    return "\n".join(out) + "\n"


# ------------------------------------------------------------ verification

def verify(aag_path, smv_path, steps, quiet=False):
    """Simulate both encodings over EVERY input sequence and compare.

    Returns (checked_sequences, [mismatch, ...]). An empty mismatch list is a
    proof of equivalence for traces up to `steps` long, not a spot check --
    these models are small enough to enumerate exhaustively.
    """
    import itertools

    import aiger
    import smv as smv_module

    circuit = aiger.load(aag_path)
    model = smv_module.load(smv_path)

    circuit_inputs = sorted(circuit.inputs)
    model_inputs = sorted(model.inputs)
    # Input names must be *identical*, not merely corresponding: the front ends
    # look an input up by its AIGER name when reading a checker's counterexample.
    if circuit_inputs != model_inputs:
        return 0, ["input sets differ: aag=%s smv=%s" % (circuit_inputs, model_inputs)]

    # Latch and output names legitimately differ -- `state[0]` is not a legal
    # SMV identifier and becomes `state0` -- so compare through the same
    # mapping the emitter used rather than comparing dictionaries directly.
    aag = parse_aag(aag_path)
    table = build_name_table(aag)
    rename = {}
    for position, (current, _, _) in enumerate(aag.latches):
        rename[aag.names.get("l%d" % position, "l%d" % position)] = table[current >> 1]
    for position in range(len(aag.outputs)):
        original = aag.names.get("o%d" % position, "o%d" % position)
        rename[original] = sanitize(original)

    def translate(values):
        return {rename.get(key, key): value for key, value in values.items()}

    width = len(circuit_inputs)
    valuations = [dict(zip(circuit_inputs, bits))
                  for bits in itertools.product([False, True], repeat=width)]

    def advance(path):
        """Fresh pair of simulators, replayed along `path`."""
        circuit_sim = circuit.simulator()
        next(circuit_sim)
        model_sim = model.simulator()
        next(model_sim)
        for assignment in path:
            circuit_sim.send(dict(assignment))
            model_sim.send(dict(assignment))
        return circuit_sim, model_sim

    # Exhaust the *reachable state space* rather than input sequences of some
    # fixed length. Both machines are deterministic and start in the same
    # state, so if they agree on the outputs and the successor of every
    # (reachable state, input) pair, they are equivalent for every input and
    # every trace length -- a proof, not a bound. It is also far cheaper:
    # at most 2^latches * 2^inputs pairs (128 for the largest example here)
    # instead of 2^(inputs*steps) sequences.
    mismatches = []
    queue = [()]
    seen = set()
    checked = 0
    while queue and len(mismatches) < 3:
        path = queue.pop(0)
        for assignment in valuations:
            circuit_sim, model_sim = advance(path)
            circuit_out, circuit_next = circuit_sim.send(dict(assignment))
            model_out, model_next = model_sim.send(dict(assignment))
            circuit_out = translate(circuit_out)
            circuit_next = translate(circuit_next)
            checked += 1
            where = "after %d step(s), inputs=%s" % (
                len(path), {k: v for k, v in sorted(assignment.items())})
            if circuit_out != model_out:
                mismatches.append("%s: outputs aag=%s smv=%s"
                                  % (where, circuit_out, model_out))
                continue
            if circuit_next != model_next:
                mismatches.append("%s: next state aag=%s smv=%s"
                                  % (where, circuit_next, model_next))
                continue
            key = tuple(sorted(model_next.items()))
            if key not in seen:
                seen.add(key)
                queue.append(path + (assignment,))
    return checked, mismatches


# -------------------------------------------------------------------- main

def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("aag", nargs="+", help="AIGER .aag file(s) to translate")
    parser.add_argument("-o", "--out",
                        help="output path (default: alongside the .aag, same stem)")
    parser.add_argument("--verify", action="store_true",
                        help="exhaustively simulate both encodings and compare")
    parser.add_argument("--steps", type=int, default=6,
                        help="trace length to enumerate when verifying")
    parser.add_argument("--stdout", action="store_true",
                        help="print instead of writing")
    parser.add_argument("--gates", action="store_true",
                        help="emit each AND gate as its own DEFINE instead of "
                             "inlining it; readable, but leaks internal signal "
                             "names the AIGER does not have")
    parser.add_argument("--force", action="store_true",
                        help="overwrite an existing .smv that was not generated "
                             "by this script")
    args = parser.parse_args()

    failures = 0
    for aag_path in args.aag:
        try:
            aag = parse_aag(aag_path)
            text = to_smv(aag, os.path.basename(aag_path), args.gates)
        except AagError as exc:
            print("%s: ERROR %s" % (aag_path, exc))
            failures += 1
            continue

        if args.stdout:
            print(text)
            continue

        smv_path = args.out or os.path.splitext(aag_path)[0] + ".smv"
        if os.path.exists(smv_path) and not args.force:
            with open(smv_path) as handle:
                existing = handle.read()
            if "generated by tools/aag2smv.py" not in existing:
                print("%s: SKIP (hand-written .smv present; use --force to replace)"
                      % smv_path)
                continue
        with open(smv_path, "w") as handle:
            handle.write(text)

        note = ""
        if args.verify:
            checked, mismatches = verify(aag_path, smv_path, args.steps)
            if mismatches:
                note = "  MISMATCH after %d pairs: %s" % (checked, mismatches[0])
                failures += 1
            else:
                note = "  verified: %d (state,input) pairs exhausted, identical" % checked
        print("%s -> %s%s" % (aag_path, smv_path, note))

    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
