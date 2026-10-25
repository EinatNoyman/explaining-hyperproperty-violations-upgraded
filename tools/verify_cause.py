#!/usr/bin/env python3
"""Independent oracle for the actual causes reported by explainhyper/explain_hyper.py.

Decides, by brute force, whether a reported cause C is an actual cause under
Definition 6 of Coenen et al., "Explaining Hyperproperty Violations" (CAV'22):

  SAT  Gamma |= C
  CF   exists W subset OE with Gamma |= W, |W| <= --max-contingency, and a
       non-empty C' subset C, such that intervene(Gamma, C', W) |= phi
  MIN  no non-empty proper subset of C satisfies SAT and CF

Independence from the tool is the point, so this file shares no code with it:
no import from explainhyper/, no alternating automata, no spot, no py-aiger.
LTL is evaluated by direct recursion over the positions of a lasso word, and
the system is simulated by a small AIGER interpreter written here.

Where Gamma comes from
----------------------
The tool rewrites <outName>.json on *every* call to check_formula, so after a
run the file holds the last counterfactual it tried, not Gamma. Gamma is
therefore rebuilt from the input columns of a .cex (pass --cex; the tool writes
<outName>.cex for every front end) and re-simulated here. The JSON is used only
for `variables`, `lassoStart` and the formula `plain`. Without --cex the
JSON's timesteps are taken as Gamma, and the sanity gate will say if that is
wrong.

Semantics choices (all recorded in the output)
----------------------------------------------
* Formulas are put into negation normal form before evaluation. On infinite
  words this changes nothing. On finite words it is what makes `strong` and
  `weak` well defined, because under `strong` phi and !phi can both be false.
* Finite words (lassoStart == -1), past the last position:
    X, F, U   false under both readings
    G, R, W   false under `strong`, true under `weak`
  This mirrors the tool's -finiteSemantics flag.
* An event <a, n, t> refers to the single position n. On a lasso, flipping it
  changes that one occurrence only, and the counterfactual is re-simulated
  until its own lasso closes.
* A contingency event <o, n, t> overwrites output o at step n with its Gamma
  value. The run then continues from a reachable state whose output label equals
  the overwritten output valuation. If several states carry that label, each is
  tried (CF is existential). If the current state already has it, nothing changes.

Exit status: 0 if every claimed cause is VALID, 1 if any is not, 2 if the
verifier could not run at all (SYSTEM_MISMATCH, phantom APs, unreadable input).
"""

import argparse
import ast
import csv
import itertools
import json
import os
import re
import sys
from math import comb, gcd


class VerifierError(Exception):
    """The instance cannot be verified at all (as opposed to a cause failing)."""

    def __init__(self, code, message):
        super().__init__("%s: %s" % (code, message))
        self.code = code


# --------------------------------------------------------------------------
# Names
# --------------------------------------------------------------------------

def mangle(name):
    """The tool's AP-name sanitisation, restated so names line up with its output.

    Strips `| < > [ ] * ! &` and lower-cases the LTL operator letters G F U W R.
    """
    for ch in "|<>[]*!&":
        name = name.replace(ch, "")
    for up in "GFUWR":
        name = name.replace(up, up.lower())
    return name


def split_ap(zipped):
    """'req_0_1' -> ('req_0', 1)."""
    m = re.match(r"^(.+)_(\d+)$", zipped)
    if not m:
        raise VerifierError("BAD_FORMULA", "AP %r has no _<traceid> suffix" % zipped)
    return m.group(1), int(m.group(2))


# --------------------------------------------------------------------------
# LTL: parser, NNF, evaluator
# --------------------------------------------------------------------------
# AST: ('true',) ('false',) ('ap', name) ('!', f) ('&', f, g) ('|', f, g)
#      ('->', f, g) ('<->', f, g) ('X', f) ('G', f) ('F', f)
#      ('U', f, g) ('R', f, g) ('W', f, g)
# NNF adds ('nap', name) and uses only true false ap nap & | X U R.

_TOKEN = re.compile(r"\s*(<->|->|[()!&|]|[A-Za-z_][A-Za-z0-9_.]*)")


def _tokenize(text):
    tokens, pos = [], 0
    text = text.strip()
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if not m:
            raise VerifierError("BAD_FORMULA", "cannot tokenize %r at %d" % (text, pos))
        tok = m.group(1)
        pos = m.end()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", tok):
            if tok in ("true", "1"):
                tokens.append("true")
            elif tok in ("false", "0"):
                tokens.append("false")
            elif tok in ("U", "R", "W"):
                tokens.append(tok)
            elif re.fullmatch(r"[GFX]+", tok):
                tokens.extend(tok)            # 'GF' is G F
            elif re.fullmatch(r".+_\d+", tok):
                tokens.append(("ap", tok))
            else:
                raise VerifierError("BAD_FORMULA", "unknown token %r" % tok)
        else:
            tokens.append(tok)
        while pos < len(text) and text[pos].isspace():
            pos += 1
    return tokens


def parse_formula(text):
    """Parse the zipped LTL formula in the JSON's `plain` field."""
    tokens = _tokenize(text)
    pos = [0]

    def peek():
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def take(expected=None):
        tok = peek()
        if tok is None or (expected is not None and tok != expected):
            raise VerifierError("BAD_FORMULA", "expected %r, got %r in %r" % (expected, tok, text))
        pos[0] += 1
        return tok

    def implication():                    # lowest, right-associative
        left = disjunction()
        if peek() in ("->", "<->"):
            op = take()
            return (op, left, implication())
        return left

    def disjunction():
        left = conjunction()
        while peek() == "|":
            take()
            left = ("|", left, conjunction())
        return left

    def conjunction():
        left = binary_temporal()
        while peek() == "&":
            take()
            left = ("&", left, binary_temporal())
        return left

    def binary_temporal():                # right-associative
        left = unary()
        if peek() in ("U", "R", "W"):
            op = take()
            return (op, left, binary_temporal())
        return left

    def unary():
        tok = peek()
        if tok in ("!", "G", "F", "X"):
            take()
            return (tok, unary())
        if tok == "(":
            take()
            inner = implication()
            take(")")
            return inner
        if tok in ("true", "false"):
            take()
            return (tok,)
        if isinstance(tok, tuple):
            take()
            return tok
        raise VerifierError("BAD_FORMULA", "unexpected %r in %r" % (tok, text))

    result = implication()
    if peek() is not None:
        raise VerifierError("BAD_FORMULA", "trailing %r in %r" % (peek(), text))
    return result


def formula_aps(f):
    if f[0] in ("ap", "nap"):
        return {f[1]}
    out = set()
    for sub in f[1:]:
        out |= formula_aps(sub)
    return out


def nnf(f, neg=False):
    op = f[0]
    if op == "true":
        return ("false",) if neg else f
    if op == "false":
        return ("true",) if neg else f
    if op == "ap":
        return ("nap", f[1]) if neg else f
    if op == "nap":
        return ("ap", f[1]) if neg else f
    if op == "!":
        return nnf(f[1], not neg)
    if op in ("&", "|"):
        flip = {"&": "|", "|": "&"}[op] if neg else op
        return (flip, nnf(f[1], neg), nnf(f[2], neg))
    if op == "->":
        return nnf(("|", ("!", f[1]), f[2]), neg)
    if op == "<->":
        a, b = f[1], f[2]
        return nnf(("|", ("&", a, b), ("&", ("!", a), ("!", b))), neg)
    if op == "X":
        return ("X", nnf(f[1], neg))
    if op == "G":                         # G a = false R a
        return nnf(("R", ("false",), f[1]), neg)
    if op == "F":                         # F a = true U a
        return nnf(("U", ("true",), f[1]), neg)
    if op == "U":
        if neg:
            return ("R", nnf(f[1], True), nnf(f[2], True))
        return ("U", nnf(f[1]), nnf(f[2]))
    if op == "R":
        if neg:
            return ("U", nnf(f[1], True), nnf(f[2], True))
        return ("R", nnf(f[1]), nnf(f[2]))
    if op == "W":                         # a W b = b R (a | b)
        return nnf(("R", f[2], ("|", f[1], f[2])), neg)
    raise VerifierError("BAD_FORMULA", "unknown operator %r" % (op,))


def holds(formula, word, position=0, semantics="strong"):
    """Does `formula` hold at `position` of `word`?

    `word` is (prefix, loop): two lists of letters, each letter a set (or dict
    name -> bool) of the zipped APs true there. A non-empty loop means the
    infinite word prefix . loop^omega; an empty loop means the finite word
    `prefix`, read under `semantics` ('strong' or 'weak').
    """
    if isinstance(formula, str):
        formula = parse_formula(formula)
    if semantics not in ("strong", "weak"):
        raise ValueError("semantics must be 'strong' or 'weak'")
    prefix, loop = word
    letters = []
    for letter in list(prefix) + list(loop):
        if isinstance(letter, dict):
            letter = {k for k, v in letter.items() if v}
        letters.append(frozenset(letter))
    n = len(letters)
    loop_start = len(prefix) if loop else -1
    if n == 0:
        raise ValueError("empty word")
    if position >= n:
        if loop_start < 0:
            raise ValueError("position %d is past the end of a finite word" % position)
        position = loop_start + (position - loop_start) % len(loop)

    def succ(i):                          # None = past the horizon
        if i + 1 < n:
            return i + 1
        return loop_start if loop_start >= 0 else None

    horizon_r = (semantics == "weak")     # value of R (hence G, W) past the end
    f = nnf(formula)
    memo = {}                             # keyed by id(); f keeps every node alive

    def ev(g, i):
        key = (id(g), i)
        if key in memo:
            return memo[key]
        op = g[0]
        if op == "true":
            r = True
        elif op == "false":
            r = False
        elif op == "ap":
            r = g[1] in letters[i]
        elif op == "nap":
            r = g[1] not in letters[i]
        elif op == "&":
            r = ev(g[1], i) and ev(g[2], i)
        elif op == "|":
            r = ev(g[1], i) or ev(g[2], i)
        elif op == "X":
            j = succ(i)
            r = False if j is None else ev(g[1], j)
        elif op == "U":                   # walk forward; at most one lap
            r, j, seen = None, i, set()
            while j is not None and j not in seen:
                seen.add(j)
                if ev(g[2], j):
                    r = True
                    break
                if not ev(g[1], j):
                    r = False
                    break
                j = succ(j)
            if r is None:
                r = False                 # horizon reached, or cycle without b
        elif op == "R":
            r, j, seen = None, i, set()
            while j is not None and j not in seen:
                seen.add(j)
                if not ev(g[2], j):
                    r = False
                    break
                if ev(g[1], j):
                    r = True
                    break
                j = succ(j)
            if r is None:
                r = horizon_r if j is None else True   # b held around the whole cycle
        else:
            raise VerifierError("BAD_FORMULA", "operator %r not in NNF" % (op,))
        memo[key] = r
        return r

    return ev(f, position)


# --------------------------------------------------------------------------
# AIGER (ASCII) simulator
# --------------------------------------------------------------------------

class Aiger:
    def __init__(self, path):
        with open(path, encoding="utf-8") as fh:
            lines = [ln.rstrip("\r\n") for ln in fh]
        header = lines[0].split()
        if header[0] != "aag":
            raise VerifierError("BAD_AAG", "%s is not an ASCII AIGER file" % path)
        M, I, L, O, A = (int(x) for x in header[1:6])
        if any(int(x) for x in header[6:]):
            raise VerifierError("BAD_AAG", "AIGER 1.9 sections (B C J F) unsupported")
        k = 1
        self.input_lits = [int(lines[k + j].split()[0]) for j in range(I)]
        k += I
        self.latch_defs = []              # (current lit, next lit, init)
        for j in range(L):
            parts = [int(x) for x in lines[k + j].split()]
            init = parts[2] if len(parts) > 2 else 0
            if init not in (0, 1):
                raise VerifierError("BAD_AAG", "latch %d is uninitialised" % j)
            self.latch_defs.append((parts[0], parts[1], init))
        k += L
        self.output_lits = [int(lines[k + j].split()[0]) for j in range(O)]
        k += O
        self.ands = [tuple(int(x) for x in lines[k + j].split()) for j in range(A)]
        k += A
        names = {"i": ["i%d" % j for j in range(I)],
                 "l": ["l%d" % j for j in range(L)],
                 "o": ["o%d" % j for j in range(O)]}
        for line in lines[k:]:
            if line.startswith("c"):
                break
            m = re.match(r"^([ilo])(\d+) (.+)$", line)
            if m:
                names[m.group(1)][int(m.group(2))] = mangle(m.group(3))
        self.inputs, self.latches, self.outputs = names["i"], names["l"], names["o"]
        self.max_var = M

    def initial_state(self):
        return {name: bool(init) for name, (_, _, init) in zip(self.latches, self.latch_defs)}

    def step(self, latch_state, inputs):
        """(outputs, next latch state) for one step from `latch_state` under `inputs`."""
        val = {0: False}
        for name, lit in zip(self.inputs, self.input_lits):
            val[lit >> 1] = bool(inputs[name])
        for name, (lit, _, _) in zip(self.latches, self.latch_defs):
            val[lit >> 1] = bool(latch_state[name])

        def lit_value(lit):
            if (lit >> 1) not in val:
                raise VerifierError("BAD_AAG", "literal %d used before it is defined" % lit)
            return val[lit >> 1] ^ bool(lit & 1)

        for lhs, r0, r1 in self.ands:
            val[lhs >> 1] = lit_value(r0) and lit_value(r1)
        outputs = {name: lit_value(lit) for name, lit in zip(self.outputs, self.output_lits)}
        nxt = {name: lit_value(d[1]) for name, d in zip(self.latches, self.latch_defs)}
        return outputs, nxt

    def all_input_valuations(self):
        for bits in itertools.product((False, True), repeat=len(self.inputs)):
            yield dict(zip(self.inputs, bits))

    def reachable_states(self):
        start = self.initial_state()
        key = lambda s: tuple(s[n] for n in self.latches)
        seen, todo = {key(start): start}, [start]
        while todo:
            s = todo.pop()
            for inp in self.all_input_valuations():
                _, nxt = self.step(s, inp)
                if key(nxt) not in seen:
                    seen[key(nxt)] = nxt
                    todo.append(nxt)
        return [seen[k] for k in sorted(seen)]


# --------------------------------------------------------------------------
# Traces
# --------------------------------------------------------------------------
# A simulated trace is (prefix_rows, loop_rows); each row is a dict with keys
# 'in', 'out', 'latch' (each name -> bool). loop_rows == [] means finite.

class InputWord:
    """Per-trace input sequence: finite list, or lasso prefix . loop^omega."""

    def __init__(self, prefix, loop):
        self.prefix, self.loop = list(prefix), list(loop)

    def __len__(self):
        return len(self.prefix) + len(self.loop)

    def is_lasso(self):
        return bool(self.loop)

    def at(self, n):
        if n < len(self.prefix):
            return self.prefix[n]
        if not self.loop:
            return None                   # past the end of a finite word
        return self.loop[(n - len(self.prefix)) % len(self.loop)]


def simulate(aig, word, flips=(), contingency=None, label_index=None):
    """All traces obtainable by running `word` with `flips` and `contingency`.

    flips:        iterable of (input name, position) to negate once.
    contingency:  dict position -> {output name: value to force}.
    Returns a list of (prefix_rows, loop_rows, choices), one per way of
    resolving an ambiguous contingency state jump.
    """
    flips = set(flips)
    contingency = contingency or {}
    touched = [n for _, n in flips] + list(contingency)
    horizon = max([len(word.prefix)] + [n + 1 for n in touched])
    if not word.is_lasso():
        horizon = len(word)

    results = []

    def run(t, state, rows, choices):
        if t == horizon:
            if word.is_lasso():
                finish_lasso(state, rows, choices)
            else:
                results.append((rows, [], choices))
            return
        inp = dict(word.at(t))
        for name, n in flips:
            if n == t:
                inp[name] = not inp[name]
        outs, nxt = aig.step(state, inp)
        if t in contingency:
            target = dict(outs)
            target.update(contingency[t])
            if target == outs:
                candidates = [state]
            else:
                key = tuple(sorted(target.items()))
                candidates = [s for s in label_index.get((key, tuple(sorted(inp.items()))), [])]
            for s in candidates:
                o2, n2 = aig.step(s, inp)
                assert o2 == target
                note = choices if s is state else choices + [(t, dict(s))]
                run(t + 1, n2, rows + [{"in": inp, "out": o2, "latch": dict(s)}], note)
            return
        run(t + 1, nxt, rows + [{"in": inp, "out": outs, "latch": dict(state)}], choices)

    def finish_lasso(state, rows, choices):
        # Unmodified laps of the loop from `horizon` on, until a lap starts in
        # a state already seen at a lap start: deterministic system, same
        # inputs, so from there the run repeats.
        lap = len(word.loop)
        lap_inputs = [word.at(horizon + r) for r in range(lap)]
        starts, laps = [], []
        key = lambda s: tuple(sorted(s.items()))
        while key(state) not in starts:
            starts.append(key(state))
            lap_rows = []
            for inp in lap_inputs:
                outs, nxt = aig.step(state, inp)
                lap_rows.append({"in": dict(inp), "out": outs, "latch": dict(state)})
                state = nxt
            laps.append(lap_rows)
        j = starts.index(key(state))
        prefix = rows + [r for l in laps[:j] for r in l]
        loop = [r for l in laps[j:] for r in l]
        results.append((prefix, loop, choices))

    run(0, aig.initial_state(), [], [])
    return results


def build_label_index(aig):
    """(output valuation, input valuation) -> reachable states with that label."""
    index = {}
    for s in aig.reachable_states():
        for inp in aig.all_input_valuations():
            outs, _ = aig.step(s, inp)
            key = (tuple(sorted(outs.items())), tuple(sorted(inp.items())))
            index.setdefault(key, []).append(s)
    return index


def zip_traces(traces):
    """Zip per-trace (prefix, loop) rows into one word of sets of 'ap_tid'."""
    lassos = [bool(loop) for _, loop in traces]
    if any(lassos) and not all(lassos):
        raise VerifierError("INTERNAL", "mixed finite and lasso traces")

    def letter(row, tid):
        out = set()
        for part in ("in", "out", "latch"):
            out |= {"%s_%d" % (k, tid) for k, v in row[part].items() if v}
        return out

    if not all(lassos):
        length = len(traces[0][0])
        assert all(len(p) == length for p, _ in traces)
        return [set().union(*(letter(traces[t][0][i], t) for t in range(len(traces))))
                for i in range(length)], []
    p = max(len(prefix) for prefix, _ in traces)
    period = 1
    for _, loop in traces:
        period = period * len(loop) // gcd(period, len(loop))

    def row_at(trace, n):
        prefix, loop = trace
        if n < len(prefix):
            return prefix[n]
        return loop[(n - len(prefix)) % len(loop)]

    word = [set().union(*(letter(row_at(traces[t], n), t) for t in range(len(traces))))
            for n in range(p + period)]
    return word[:p], word[p:]


# --------------------------------------------------------------------------
# Loading Gamma
# --------------------------------------------------------------------------

_CEX_LINE = re.compile(r"^(?P<name>[^@:\s]+)_(?P<tid>\d+)@(?P<t>\d+)=(?P<v>[01])\s*$")
_REMEMBER = re.compile(r"^I:remember_state@(\d+)=1\s*$")


def read_cex(path, aig):
    """(per-trace recorded values, num rows, lasso start from remember_state, only_ones)."""
    recorded = {}
    max_t, remember = -1, None
    only_ones = True
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            m = _REMEMBER.match(line)
            if m and remember is None:
                remember = int(m.group(1))
            m = _CEX_LINE.match(line.strip())
            if not m:
                continue
            name = mangle(m.group("name"))
            if name not in aig.inputs + aig.outputs + aig.latches:
                continue
            tid, t, v = int(m.group("tid")), int(m.group("t")), m.group("v") == "1"
            if not v:
                only_ones = False
            recorded.setdefault(tid, {}).setdefault(t, {})[name] = v
            max_t = max(max_t, t)
    return recorded, max_t + 1, remember, only_ones


class Instance:
    """Gamma, the system and the formula, after the sanity gate."""

    def __init__(self, json_path, aag_path, cex_path=None, semantics="strong",
                 formula=None):
        with open(json_path, encoding="utf-8") as fh:
            data = json.load(fh)
        self.aig = Aiger(aag_path)
        self.semantics = semantics
        self.notes = []
        self.var_types = {k: v["type"] for k, v in data["variables"].items()}
        for kind, names in (("input", self.aig.inputs), ("output", self.aig.outputs),
                            ("latch", self.aig.latches)):
            for name in names:
                if self.var_types.get(name, kind) != kind:
                    raise VerifierError("SYSTEM_MISMATCH", "%s is a %s in the circuit but a %s in the JSON"
                                        % (name, kind, self.var_types[name]))
        self.plain = formula if formula is not None else data["plain"]
        self.phi = parse_formula(self.plain)
        lasso_start = int(data["lassoStart"])

        # Number of traces: highest trace id in the formula.
        tids = set()
        phantom = []
        for ap in sorted(formula_aps(self.phi)):
            name, tid = split_ap(ap)
            tids.add(tid)
            if name not in self.var_types or name not in self.aig.inputs + self.aig.outputs + self.aig.latches:
                phantom.append(ap)
        if phantom:
            raise VerifierError("PHANTOM_AP", "formula %r references %s, absent from the circuit "
                                "(circuit signals: %s)" % (self.plain, ", ".join(phantom),
                                ", ".join(self.aig.inputs + self.aig.outputs + self.aig.latches)))
        self.k = max(tids) + 1 if tids else 1

        # Input columns and the values to check the simulation against.
        if cex_path:
            recorded, rows, remember, only_ones = read_cex(cex_path, self.aig)
            if remember is not None and remember != lasso_start:
                raise VerifierError("SYSTEM_MISMATCH", "cex remember_state says the loop starts at %d, "
                                    "JSON lassoStart says %d" % (remember, lasso_start))
            if not recorded and rows <= 0:
                raise VerifierError("BAD_CEX", "%s holds no values for this circuit" % cex_path)
            self.k = max([self.k] + [t + 1 for t in recorded])
            if only_ones:
                # Rows in which nothing is true leave no line at all, so trailing
                # all-false rows are invisible in the cex. The JSON keeps the length.
                rows = max(rows, len(data["timesteps"]))
            columns = []
            for tid in range(self.k):
                col = []
                for t in range(rows):
                    vals = recorded.get(tid, {}).get(t, {})
                    col.append({n: vals.get(n, False) for n in self.aig.inputs})
                columns.append(col)
            if only_ones:                 # absent means false for every signal
                for tid in range(self.k):
                    for t in range(rows):
                        slot = recorded.setdefault(tid, {}).setdefault(t, {})
                        for n in self.aig.outputs + self.aig.latches:
                            slot.setdefault(n, False)
            source = "cex-ones" if only_ones else "cex"
        else:
            steps = data["timesteps"]
            rows = len(steps)
            self.k = max(self.k, len(steps[0]))
            columns = [[{n: bool(steps[t][tid][n]) for n in self.aig.inputs} for t in range(rows)]
                       for tid in range(self.k)]
            recorded = {tid: {t: {n: bool(steps[t][tid][n]) for n in self.aig.outputs + self.aig.latches
                                  if n in steps[t][tid]}
                              for t in range(rows)} for tid in range(self.k)}
            source = "json"
        self.gamma_source = source

        # Replay the full recorded rows and compare.
        mismatches = []
        sims = []
        for tid in range(self.k):
            state, sim = self.aig.initial_state(), []
            for t in range(rows):
                outs, nxt = self.aig.step(state, columns[tid][t])
                sim.append((outs, state, nxt))
                for name, value in recorded.get(tid, {}).get(t, {}).items():
                    mine = outs.get(name, state.get(name))
                    if name in self.aig.inputs:
                        continue
                    if source != "cex" and t == 0 and name in self.aig.latches:
                        continue  # the tool never writes latch values into row 0
                    if mine != value:
                        mismatches.append("%s@%d(t%d): recorded %d, simulated %d"
                                          % (name, t, tid, value, mine))
                state = nxt
            sims.append(sim)
        if mismatches:
            raise VerifierError("SYSTEM_MISMATCH", "%d disagreement(s) replaying Gamma, e.g. %s"
                                % (len(mismatches), "; ".join(mismatches[:5])))
        self.replayed_rows = rows

        # Where does the loop close? The tool's convention is that the final
        # recorded row repeats the loop-start state; then that row is dropped.
        if lasso_start >= 0:
            key = lambda s: tuple(sorted(s.items()))
            dup = all(key(sims[t][rows - 1][1]) == key(sims[t][lasso_start][1]) for t in range(self.k)) \
                and rows - 1 > lasso_start
            closes = all(key(sims[t][rows - 1][2]) == key(sims[t][lasso_start][1]) for t in range(self.k))
            if dup:
                rows -= 1
                self.lasso_rows = "last row repeats loop-start state; dropped"
            elif closes:
                self.lasso_rows = "loop closes after the last row"
            else:
                raise VerifierError("SYSTEM_MISMATCH", "lassoStart=%d but the simulated run does not "
                                    "return to that state" % lasso_start)
            self.words = [InputWord(columns[t][:lasso_start], columns[t][lasso_start:rows])
                          for t in range(self.k)]
        else:
            self.lasso_rows = "finite (lassoStart=-1)"
            self.words = [InputWord(columns[t][:rows], []) for t in range(self.k)]
        self.lasso_start = lasso_start
        self.rows = rows

        gamma = [simulate(self.aig, w)[0][:2] for w in self.words]
        self.gamma_traces = gamma
        self.gamma_word = zip_traces(gamma)
        self.gamma_violates = holds(("!", self.phi), self.gamma_word, 0, semantics)
        self.gamma_satisfies = holds(self.phi, self.gamma_word, 0, semantics)

        # Diagnostic only: does the JSON's timesteps actually hold Gamma?
        self.json_vs_gamma = None
        if source != "json":
            diff = 0
            steps = data["timesteps"]
            for t in range(min(len(steps), self.rows)):
                for tid in range(min(self.k, len(steps[t]))):
                    for name in self.aig.inputs + self.aig.outputs:
                        if name in steps[t][tid] and bool(steps[t][tid][name]) != \
                                self.value_at(name, t, tid):
                            diff += 1
            self.json_vs_gamma = diff
            if len(steps) != self.rows:
                self.notes.append("JSON has %d timesteps, Gamma has %d rows" % (len(steps), self.rows))

        self._label_index = None
        self._repair_cache = {}

    # -- Gamma lookups ----------------------------------------------------

    def row(self, tid, n):
        prefix, loop = self.gamma_traces[tid]
        if n < len(prefix):
            return prefix[n]
        if not loop:
            return None
        return loop[(n - len(prefix)) % len(loop)]

    def value_at(self, name, n, tid):
        r = self.row(tid, n)
        if r is None:
            return None
        for part in ("in", "out", "latch"):
            if name in r[part]:
                return r[part][name]
        return None

    def label_index(self):
        if self._label_index is None:
            self._label_index = build_label_index(self.aig)
        return self._label_index

    # -- Definition 6 -----------------------------------------------------

    def check_event(self, ev, want_kind):
        """None if `ev` is a well-formed event of `want_kind` holding in Gamma, else why not."""
        if not (isinstance(ev, tuple) and len(ev) == 4):
            return "MALFORMED: %r is not (ap, time, value, trace)" % (ev,)
        ap, n, v, tid = ev
        kind = self.var_types.get(ap)
        if kind is None:
            return "MALFORMED: %s is not a signal of the system" % ap
        if kind != want_kind:
            return "MALFORMED: %s is an %s; causes may contain only inputs" % (ap, kind)
        if v not in (0, 1) or not isinstance(n, int) or n < 0 or not isinstance(tid, int):
            return "MALFORMED: bad time/value/trace in %r" % (ev,)
        if not 0 <= tid < self.k:
            return "%s: trace %d does not exist (Gamma has %d traces)" % (fmt_event(ev), tid, self.k)
        actual = self.value_at(ap, n, tid)
        if actual is None:
            return "%s: time %d is past the end of finite Gamma (%d rows)" % (fmt_event(ev), n, self.rows)
        if int(actual) != v:
            return "%s: Gamma has %s=%d at time %d on trace %d" % (fmt_event(ev), ap, int(actual), n, tid)
        return None

    def sat(self, cause):
        for ev in cause:
            why = self.check_event(ev, "input")
            if why:
                return False, why
        return True, ""

    def output_events(self):
        horizon = len(self.gamma_traces[0][0]) + len(self.gamma_traces[0][1])
        horizon = max(horizon, max(len(p) + len(l) for p, l in self.gamma_traces))
        events = []
        for tid in range(self.k):
            for n in range(horizon):
                for o in self.aig.outputs:
                    events.append((o, n, int(self.value_at(o, n, tid)), tid))
        return events

    def repairs(self, cprime, w):
        """Is phi satisfied by some resolution of intervene(Gamma, C', W)?"""
        key = (frozenset(cprime), frozenset(w))
        if key in self._repair_cache:
            return self._repair_cache[key]
        result = None
        per_trace = []
        for tid in range(self.k):
            flips = [(ap, n) for ap, n, _, t in cprime if t == tid]
            cont = {}
            for o, n, v, t in w:
                if t == tid:
                    cont.setdefault(n, {})[o] = bool(v)
            needs_states = bool(cont)
            per_trace.append(simulate(self.aig, self.words[tid], flips, cont,
                                      self.label_index() if needs_states else None))
        for combo in itertools.product(*per_trace):
            word = zip_traces([(p, l) for p, l, _ in combo])
            if holds(self.phi, word, 0, self.semantics):
                result = [c for _, _, c in combo]
                break
        self._repair_cache[key] = result
        return result

    def cf(self, cause, max_contingency):
        """(witness C', witness W, state jumps) or None."""
        cause = list(cause)
        subsets = [c for size in range(1, len(cause) + 1)
                   for c in itertools.combinations(cause, size)]
        for cp in subsets:                # W = {} first
            r = self.repairs(cp, ())
            if r is not None:
                return cp, (), r
        if max_contingency <= 0:
            return None
        oe = self.output_events()
        for size in range(1, max_contingency + 1):
            for w in itertools.combinations(oe, size):
                for cp in subsets:
                    r = self.repairs(cp, w)
                    if r is not None:
                        return cp, w, r
        return None

    def verify(self, cause, max_contingency):
        cause = tuple(tuple(e) if isinstance(e, (list, tuple)) else e for e in cause)
        rec = {"cause": fmt_cause(cause), "sat": "fail", "cf": "fail", "min": "fail",
               "verdict": "INVALID", "why": "", "witness_subset": "", "witness_contingency": ""}
        if not cause:
            rec["why"] = "MALFORMED: empty cause"
            return rec
        if len(set(cause)) != len(cause):
            rec["why"] = "MALFORMED: duplicate events"
            return rec
        ok, why = self.sat(cause)
        if not ok:
            rec["why"] = "SAT: " + why
            return rec
        rec["sat"] = "pass"
        reasons = []
        hit = self.cf(cause, max_contingency)
        if hit:
            rec["cf"] = "pass"
            cp, w, jumps = hit
            rec["witness_subset"] = fmt_cause(cp)
            rec["witness_contingency"] = fmt_cause(w) if w else "{}"
            if any(jumps):
                rec["witness_contingency"] += " state jumps " + str(
                    [(t, n, sorted(k for k, v in s.items() if v)) for t, j in enumerate(jumps) for n, s in j])
        else:
            reasons.append("CF: no non-empty C' of %s with |W|<=%d makes phi hold (%d C' x %d W tried)"
                           % (fmt_cause(cause), max_contingency, 2 ** len(cause) - 1,
                              1 + sum(comb(len(self.output_events()), s)
                                      for s in range(1, max_contingency + 1))))
        smaller = None
        for size in range(1, len(cause)):
            for d in itertools.combinations(cause, size):
                h = self.cf(d, max_contingency)
                if h:
                    smaller = (d, h)
                    break
            if smaller:
                break
        if smaller:
            d, (cp, w, _) = smaller
            reasons.append("MIN: proper subset %s already satisfies SAT and CF (C'=%s, W=%s)"
                           % (fmt_cause(d), fmt_cause(cp), fmt_cause(w) if w else "{}"))
        else:
            rec["min"] = "pass"
        if rec["cf"] == "pass" and rec["min"] == "pass":
            rec["verdict"] = "VALID"
        rec["why"] = "; ".join(reasons)
        if not self.gamma_violates:
            rec["verdict"] = "UNDEFINED"
            rec["why"] = ("Gamma does not satisfy !phi under %s semantics, so it is not a counterexample "
                          "and Definition 6 does not apply. [%s]" % (self.semantics, rec["why"] or "SAT/CF/MIN pass"))
        return rec

    def missed_causes(self, candidates, reported, max_size, max_contingency):
        reported = {frozenset(tuple(e) for e in c) for c in reported}
        missed = []
        for size in range(1, max_size + 1):
            for c in itertools.combinations(candidates, size):
                if frozenset(c) in reported:
                    continue
                if not self.sat(c)[0] or not self.cf(c, max_contingency):
                    continue
                if any(self.cf(d, max_contingency) for s in range(1, size)
                       for d in itertools.combinations(c, s)):
                    continue
                missed.append(c)
        return missed


def fmt_event(ev):
    try:
        ap, n, v, t = ev
        return "%s@%s=%s(t%s)" % (ap, n, v, t)
    except (TypeError, ValueError):
        return repr(ev)


def fmt_cause(cause):
    return "{" + ", ".join(fmt_event(e) for e in cause) + "}"


# --------------------------------------------------------------------------
# Reading the tool's output
# --------------------------------------------------------------------------

def parse_log(path):
    """(causes, candidate set C~) from a saved stdout of explain_hyper.py."""
    with open(path, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    causes = re.findall(r"^All minimal causes \(forall C\): (.*)$", text, re.M)
    if not causes:
        raise VerifierError("BAD_LOG", "%s has no 'All minimal causes' line" % path)
    candidates = []
    for _, lst in re.findall(r"^for trace (\d+): (\[.*\])$", text, re.M):
        candidates.extend(ast.literal_eval(lst))
    return ast.literal_eval(causes[-1]), candidates


FIELDS = ["example", "frontend", "cause", "sat", "cf", "min", "verdict", "why",
          "witness_subset", "witness_contingency", "finite_semantics", "max_contingency",
          "gamma_violates", "lasso"]


def run_one(json_path, aag_path, cex_path, causes, candidates, semantics, max_contingency,
            check_completeness=False, max_cause_size=2, example="", frontend="", out=sys.stdout):
    """Verify every cause of one run. Returns (rows, missed, instance-or-error string)."""
    base = {"example": example, "frontend": frontend, "finite_semantics": semantics,
            "max_contingency": max_contingency}
    try:
        inst = Instance(json_path, aag_path, cex_path, semantics)
    except VerifierError as e:
        print("[%s/%s] %s" % (example, frontend, e), file=out)
        row = dict(base, cause="*", sat="", cf="", min="", verdict=e.code, why=str(e),
                   witness_subset="", witness_contingency="", gamma_violates="", lasso="")
        return [row], [], e
    lasso = "lasso@%d (%s)" % (inst.lasso_start, inst.lasso_rows) if inst.lasso_start >= 0 \
        else "finite, %d rows" % inst.rows
    print("[%s/%s] Gamma from %s: %d traces, %s; semantics=%s" % (
        example, frontend, inst.gamma_source, inst.k, lasso, semantics), file=out)
    if inst.json_vs_gamma:
        print("  note: the JSON's timesteps differ from Gamma in %d cells (the tool overwrites "
              "<outName>.json with each counterfactual it checks)" % inst.json_vs_gamma, file=out)
    for note in inst.notes:
        print("  note: " + note, file=out)
    if not inst.gamma_violates:
        print("  !!! GAMMA IS NOT A COUNTEREXAMPLE: Gamma does not satisfy !phi under %s semantics "
              "(phi itself %s). This is a defect in the instance, not in any cause." % (
                  semantics, "holds" if inst.gamma_satisfies else "does not hold either"), file=out)
    rows = []
    for cause in causes:
        rec = inst.verify(cause, max_contingency)
        rec.update(base, gamma_violates="yes" if inst.gamma_violates else "NO", lasso=lasso)
        rows.append(rec)
        print("  %-8s %-40s sat=%s cf=%s min=%s %s%s" % (
            rec["verdict"], rec["cause"], rec["sat"], rec["cf"], rec["min"],
            ("W'=" + rec["witness_subset"] + " W=" + rec["witness_contingency"] + " ") if rec["cf"] == "pass" else "",
            ("| " + rec["why"]) if rec["why"] else ""), file=out)
    missed = []
    if check_completeness:
        missed = inst.missed_causes(candidates, causes, max_cause_size, max_contingency)
        print("  completeness (|C|<=%d over %d candidates): %s" % (
            max_cause_size, len(candidates),
            "none missed" if not missed else "MISSED " + ", ".join(fmt_cause(m) for m in missed)), file=out)
    return rows, missed, inst


def summarize(rows, out=sys.stdout):
    counts = {}
    for r in rows:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    print("SUMMARY: %s" % ", ".join("%s=%d" % kv for kv in sorted(counts.items())), file=out)
    return counts


def write_csv(path, rows):
    with open(path, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def infer_provenance(json_path):
    stem = os.path.splitext(os.path.basename(json_path))[0]
    m = re.match(r"^(.*)_(mchyper|autohyper|hyperqb)$", stem)
    return (m.group(1), m.group(2)) if m else (stem, "")


def batch(run_dir, examples_dir, semantics, max_contingency, check_completeness, max_cause_size):
    """Verify every run in `run_dir` (as written by tools/compare_causes.py)."""
    rows, failed_setup = [], 0
    for log in sorted(os.listdir(run_dir)):
        m = re.match(r"^(.*)_(mchyper|autohyper|hyperqb)\.log$", log)
        if not m:
            continue
        example, frontend = m.groups()
        try:
            causes, candidates = parse_log(os.path.join(run_dir, log))
        except VerifierError:
            continue                      # the run crashed or found no counterexample
        stem = os.path.join(run_dir, "%s_%s" % (example, frontend))
        if not causes and not check_completeness:
            continue
        sem = semantics
        if sem == "auto":                 # what tools/compare_causes.py passed
            sem = "weak" if frontend == "hyperqb" else "strong"
        r, _, err = run_one(stem + ".json", os.path.join(examples_dir, example, example + ".aag"),
                            stem + ".cex", causes, candidates, sem, max_contingency,
                            check_completeness, max_cause_size, example, frontend)
        rows.extend(r)
        if isinstance(err, VerifierError):
            failed_setup += 1
    return rows, failed_setup


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--json", help="<outName>.json written by explain_hyper.py")
    p.add_argument("--aag", help="the system's .aag (the original, not the tool's -aag.aag)")
    p.add_argument("--cex", help="<outName>.cex written by the tool (source of Gamma; recommended)")
    src = p.add_mutually_exclusive_group()
    src.add_argument("--causes", help='inline, e.g. "[[(\'a\',0,1,0)],[(\'sel\',0,0,0)]]"')
    src.add_argument("--log", help="saved stdout of explain_hyper.py")
    p.add_argument("--finite-semantics", default="strong", choices=["strong", "weak", "auto"],
                   help="reading of a finite Gamma; 'auto' (batch only) = weak for hyperqb, else strong")
    p.add_argument("--max-contingency", type=int, default=2)
    p.add_argument("--check-completeness", action="store_true")
    p.add_argument("--max-cause-size", type=int, default=2)
    p.add_argument("--csv")
    p.add_argument("--example", default=None)
    p.add_argument("--frontend", default=None)
    p.add_argument("--run-dir", help="verify every <example>_<frontend> run in this directory")
    p.add_argument("--examples-dir", default=os.path.join(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), "examples"))
    a = p.parse_args(argv)

    if a.run_dir:
        rows, failed = batch(a.run_dir, a.examples_dir, a.finite_semantics, a.max_contingency,
                             a.check_completeness, a.max_cause_size)
    else:
        if not (a.json and a.aag and (a.causes or a.log)):
            p.error("--json, --aag and one of --causes/--log are required (or use --run-dir)")
        if a.finite_semantics == "auto":
            p.error("--finite-semantics auto is only meaningful with --run-dir")
        candidates = []
        if a.log:
            causes, candidates = parse_log(a.log)
        else:
            causes = ast.literal_eval(a.causes)
        example, frontend = infer_provenance(a.json)
        rows, _, err = run_one(a.json, a.aag, a.cex, causes, candidates, a.finite_semantics,
                               a.max_contingency, a.check_completeness, a.max_cause_size,
                               a.example if a.example is not None else example,
                               a.frontend if a.frontend is not None else frontend)
        failed = 1 if isinstance(err, VerifierError) else 0
    counts = summarize(rows)
    if a.csv:
        write_csv(a.csv, rows)
    if failed:
        return 2
    return 0 if all(r["verdict"] == "VALID" for r in rows) else 1


if __name__ == "__main__":
    sys.exit(main())
