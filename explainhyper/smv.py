"""A NuSMV parser and interpreter, exposing the SystemModel surface.

Why this exists
---------------
AutoHyper and HyperQB take NuSMV models, but the causality pipeline needs an
*executable* system: `get_circuit_outputs` re-simulates after flipping inputs,
and that re-simulation IS the intervention semantics of the Halpern-Pearl
definition. A counterexample alone is not enough. Until now the only executable
model was a py-aiger circuit.

The mapping that makes this work
--------------------------------
NuSMV has no notion of "input". But it does have *nondeterministic assignment*:

    init(PIN_1) := {1,0};        next(NUM) := {0,1,2,3};

A nondeterministic choice is exactly a free input -- the environment picks.
So:

    inputs   variables whose init or next is nondeterministic
    latches  every declared VAR (the state)
    outputs  DEFINE entries (derived signals)

and `simulator().send({ap: bool})` supplies the choices, mirroring py-aiger's
`(outputs, next_latches)` protocol so no call site has to change.

Bit encoding mirrors AIGER: a `boolean` is one AP under its own name; a
`0..N` variable becomes ceil(log2(N+1)) APs `<var>_b0` (LSB) .. `<var>_b<w-1>`.
A width-1 range keeps the bare name, so names stay comparable with the
AIGER-derived ones.

Supported fragment
------------------
Deliberately small, and anything outside it raises SmvUnsupportedError rather
than being silently mis-executed:

    yes   single MODULE main; VAR with boolean and 0..N; ASSIGN with
          init()/next(); case..esac; DEFINE; operators = != < <= > >= & | ! +
          - and TRUE/FALSE; set literals {a,b,..}
    no    module instantiation, arrays, word[n], symbolic enums, TRANS/INIT/
          INVAR/FAIRNESS, mod, bit operations
"""

import re


class SmvError(Exception):
    """The model could not be parsed or executed."""


class SmvUnsupportedError(SmvError):
    """The model uses a NuSMV construct outside the supported fragment."""


# --------------------------------------------------------------------------
# Tokenizer
# --------------------------------------------------------------------------

_TOKEN = re.compile(r"""
      (?P<ws>\s+)
    | (?P<comment>--[^\n]*)
    | (?P<num>\d+)
    | (?P<id>[A-Za-z_][A-Za-z0-9_.]*)
    | (?P<op><->|->|!=|<=|>=|:=|\.\.|[=<>&|!+\-*/(){}:;,])
""", re.VERBOSE)

_KEYWORDS = {"MODULE", "VAR", "ASSIGN", "DEFINE", "case", "esac", "init",
             "next", "TRUE", "FALSE", "boolean"}
_REJECT = {"TRANS": "TRANS", "INIT": "INIT constraints", "INVAR": "INVAR",
           "FAIRNESS": "FAIRNESS", "JUSTICE": "JUSTICE", "mod": "the mod operator",
           "array": "arrays", "word": "word types", "process": "processes"}


def tokenize(text):
    tokens, pos = [], 0
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if not m:
            raise SmvError("cannot tokenize at offset %d: %r" % (pos, text[pos:pos + 20]))
        pos = m.end()
        kind = m.lastgroup
        if kind in ("ws", "comment"):
            continue
        value = m.group()
        if kind == "id" and value in _REJECT:
            raise SmvUnsupportedError("%s is not supported" % _REJECT[value])
        tokens.append((kind, value))
    tokens.append(("eof", ""))
    return tokens


# --------------------------------------------------------------------------
# Expressions
#
# AST nodes are tuples so they are cheap to compare in tests:
#   ('num', n) ('id', name) ('not', e) ('bin', op, l, r)
#   ('case', [(cond, val), ...]) ('set', [e, ...])
# --------------------------------------------------------------------------

_PRECEDENCE = [("|",), ("&",), ("=", "!=", "<", "<=", ">", ">="), ("+", "-")]


class _ExprParser:
    def __init__(self, tokens, pos=0):
        self.tokens, self.pos = tokens, pos

    def peek(self):
        return self.tokens[self.pos]

    def take(self, expected=None):
        kind, value = self.tokens[self.pos]
        if expected is not None and value != expected:
            raise SmvError("expected %r, found %r" % (expected, value))
        self.pos += 1
        return value

    def parse(self, level=0):
        if level == len(_PRECEDENCE):
            return self.parse_unary()
        node = self.parse(level + 1)
        while self.peek()[1] in _PRECEDENCE[level]:
            op = self.take()
            node = ("bin", op, node, self.parse(level + 1))
        return node

    def parse_unary(self):
        kind, value = self.peek()
        if value == "!":
            self.take()
            return ("not", self.parse_unary())
        if value == "-":
            self.take()
            return ("bin", "-", ("num", 0), self.parse_unary())
        return self.parse_atom()

    def parse_atom(self):
        kind, value = self.peek()
        if value == "(":
            self.take("(")
            node = self.parse()
            self.take(")")
            return node
        if value == "{":
            self.take("{")
            items = []
            while self.peek()[1] != "}":
                items.append(self.parse())
                if self.peek()[1] == ",":
                    self.take(",")
            self.take("}")
            return ("set", items)
        if value == "case":
            self.take("case")
            branches = []
            while self.peek()[1] != "esac":
                cond = self.parse()
                self.take(":")
                branches.append((cond, self.parse()))
                self.take(";")
            self.take("esac")
            return ("case", branches)
        if kind == "num":
            return ("num", int(self.take()))
        if value in ("TRUE", "FALSE"):
            return ("num", 1 if self.take() == "TRUE" else 0)
        if kind == "id":
            return ("id", self.take())
        raise SmvError("unexpected token %r" % value)


# --------------------------------------------------------------------------
# Evaluation
#
# Everything is an int; TRUE/FALSE are 1/0. That is enough for this fragment
# and avoids a bool/int type split that NuSMV itself is loose about.
# --------------------------------------------------------------------------

def evaluate(node, env):
    """Evaluate an expression. Returns an int, or a set of ints for a choice."""
    kind = node[0]
    if kind == "num":
        return node[1]
    if kind == "id":
        name = node[1]
        if name not in env:
            raise SmvError("undefined identifier %r" % name)
        value = env[name]
        return value() if callable(value) else value
    if kind == "not":
        return 0 if evaluate(node[1], env) else 1
    if kind == "set":
        values = set()
        for item in node[1]:
            values.add(evaluate(item, env))
        return values if len(values) > 1 else values.pop()
    if kind == "case":
        for cond, value in node[1]:
            if evaluate(cond, env):
                return evaluate(value, env)
        raise SmvError("no case branch matched and there is no TRUE fallback")
    if kind == "bin":
        op, left, right = node[1], evaluate(node[2], env), evaluate(node[3], env)
        if isinstance(left, set) or isinstance(right, set):
            raise SmvUnsupportedError("a nondeterministic set inside an operator")
        if op == "&":  return 1 if (left and right) else 0
        if op == "|":  return 1 if (left or right) else 0
        if op == "=":  return 1 if left == right else 0
        if op == "!=": return 1 if left != right else 0
        if op == "<":  return 1 if left < right else 0
        if op == "<=": return 1 if left <= right else 0
        if op == ">":  return 1 if left > right else 0
        if op == ">=": return 1 if left >= right else 0
        if op == "+":  return left + right
        if op == "-":  return left - right
        raise SmvUnsupportedError("operator %r" % op)
    raise SmvError("unknown node %r" % (node,))


def is_nondeterministic(node):
    """Whether any reachable branch of `node` can yield a choice."""
    if node[0] == "set":
        return len(node[1]) > 1
    if node[0] == "case":
        return any(is_nondeterministic(v) for _, v in node[1])
    return False


# --------------------------------------------------------------------------
# Parsing a whole model
# --------------------------------------------------------------------------

class SmvProgram(object):
    def __init__(self):
        self.var_order = []      # declaration order
        self.ranges = {}         # name -> (lo, hi)
        self.init = {}           # name -> expr
        self.next = {}           # name -> expr
        self.defines = []        # [(name, expr)] in declaration order


def parse_smv(text):
    tokens = tokenize(text)
    program = SmvProgram()
    i = 0

    def value_at(k):
        return tokens[k][1]

    if value_at(i) != "MODULE":
        raise SmvError("expected MODULE at the start of the model")
    i += 1
    module_name = tokens[i][1]
    if module_name != "main":
        raise SmvUnsupportedError(
            "only a single `MODULE main` is supported, found %r" % module_name)
    i += 1

    section = None
    while value_at(i) != "":
        token = value_at(i)
        if token in ("VAR", "ASSIGN", "DEFINE"):
            section = token
            i += 1
            continue
        if token == "MODULE":
            raise SmvUnsupportedError("more than one MODULE is not supported")

        if section == "VAR":
            name = value_at(i); i += 1
            if value_at(i) != ":":
                raise SmvError("expected ':' after VAR %r" % name)
            i += 1
            if value_at(i) == "boolean":
                program.ranges[name] = (0, 1); i += 1
            elif tokens[i][0] == "num":
                lo = int(value_at(i)); i += 1
                if value_at(i) != "..":
                    raise SmvUnsupportedError(
                        "only `boolean` and `lo..hi` variable types are supported")
                i += 1
                hi = int(value_at(i)); i += 1
                if lo != 0:
                    raise SmvUnsupportedError(
                        "ranges must start at 0, found %d..%d for %r" % (lo, hi, name))
                program.ranges[name] = (lo, hi)
            else:
                raise SmvUnsupportedError(
                    "unsupported type for %r: %r" % (name, value_at(i)))
            program.var_order.append(name)
            if value_at(i) == ";":
                i += 1
            continue

        if section in ("ASSIGN", "DEFINE"):
            if token in ("init", "next"):
                kind = token; i += 1
                if value_at(i) != "(":
                    raise SmvError("expected '(' after %s" % kind)
                i += 1
                name = value_at(i); i += 1
                if value_at(i) != ")":
                    raise SmvError("expected ')' after %s(%s" % (kind, name))
                i += 1
            else:
                kind, name = "define", token
                i += 1
            if value_at(i) != ":=":
                raise SmvError("expected ':=' in assignment to %r" % name)
            i += 1
            parser = _ExprParser(tokens, i)
            expr = parser.parse()
            i = parser.pos
            if value_at(i) == ";":
                i += 1
            if kind == "init":
                program.init[name] = expr
            elif kind == "next":
                program.next[name] = expr
            else:
                program.defines.append((name, expr))
            continue

        raise SmvError("unexpected token %r outside any section" % token)

    if not program.var_order:
        raise SmvError("the model declares no variables")
    return program


# --------------------------------------------------------------------------
# The executable model
# --------------------------------------------------------------------------

def _width(lo, hi):
    return max(1, int(hi).bit_length())


def _ap_names(name, width):
    """Bit APs for a variable. Width 1 keeps the bare name, matching AIGER."""
    if width == 1:
        return [name]
    return ["%s_b%d" % (name, bit) for bit in range(width)]


class SmvModel(object):
    """A parsed NuSMV model that satisfies the SystemModel duck type."""

    def __init__(self, program, source="", relabelling=None):
        self.program = program
        self.source = source
        self._widths = {n: _width(*program.ranges[n]) for n in program.var_order}
        self._relabel = dict(relabelling or {})

        # A variable is caller-driven when its init or its next can branch.
        self._init_free = {n: n in program.init and is_nondeterministic(program.init[n])
                           for n in program.var_order}
        self._next_free = {n: (n not in program.next) or is_nondeterministic(program.next[n])
                           for n in program.var_order}

        self._input_vars = [n for n in program.var_order
                            if self._init_free[n] or self._next_free[n]]
        # A variable the caller drives at *every* step carries no state of its
        # own -- it is a pure input, exactly like an AIGER input, and must not
        # appear among the latches or `detect_lasso` would fold input values
        # into state identity and never find a loop.
        self._latch_vars = [n for n in program.var_order
                            if not (self._init_free[n] and self._next_free[n])]
        # Pure inputs: free at every step. Their value at time t is whatever the
        # caller supplies at time t, so they are refreshed before each step
        # rather than carried over from the previous next-state.
        self._pure_inputs = [n for n in program.var_order
                             if self._init_free[n] and self._next_free[n]]
        self._define_names = [n for n, _ in program.defines]

    # -- naming -----------------------------------------------------------
    def _aps(self, name, width=None):
        width = self._widths.get(name, 1) if width is None else width
        return [self._relabel.get(ap, ap) for ap in _ap_names(name, width)]

    @property
    def inputs(self):
        return [ap for n in self._input_vars for ap in self._aps(n)]

    @property
    def latches(self):
        return [ap for n in self._latch_vars for ap in self._aps(n)]

    @property
    def outputs(self):
        # DEFINEs are boolean-valued in this fragment: one AP each.
        return [self._relabel.get(n, n) for n in self._define_names]

    # -- encoding ---------------------------------------------------------
    def _encode(self, name, value):
        width = self._widths[name]
        aps = self._aps(name, width)
        return {aps[b]: bool((int(value) >> b) & 1) for b in range(width)}

    def _decode(self, name, supplied):
        width = self._widths[name]
        aps = self._aps(name, width)
        value = 0
        for b in range(width):
            if supplied.get(aps[b]):
                value |= 1 << b
        lo, hi = self.program.ranges[name]
        return min(max(value, lo), hi)

    # -- execution --------------------------------------------------------
    def _env(self, state):
        env = dict(state)
        for name, expr in self.program.defines:
            env[name] = (lambda e=expr, v=env: evaluate(e, v))
        return env

    def _resolve(self, expr, env, name, supplied, free):
        """Value of `expr`, taking the caller's choice where it is free."""
        if free:
            return self._decode(name, supplied)
        value = evaluate(expr, env)
        if isinstance(value, set):
            raise SmvError("unexpected nondeterminism assigning %r" % name)
        return value

    def simulator(self):
        """Generator matching py-aiger: next(sim), then sim.send(inputs)."""
        supplied = yield
        state = {}
        for name in self.program.var_order:
            expr = self.program.init.get(name)
            if expr is None or self._init_free[name]:
                state[name] = self._decode(name, supplied)
            else:
                value = evaluate(expr, {})
                state[name] = value.pop() if isinstance(value, set) else value

        while True:
            env = self._env(state)
            out = {}
            for name, expr in self.program.defines:
                out[self._relabel.get(name, name)] = bool(evaluate(expr, env))

            nxt_state = {}
            for name in self.program.var_order:
                nxt_state[name] = self._resolve(
                    self.program.next.get(name), env, name, supplied,
                    self._next_free[name])

            # Only real latches are reported as next-state. Pure inputs are
            # tracked internally (a next() expression may reference them) but
            # emitting them would put input values into the state, which is not
            # what py-aiger does and would corrupt loop detection.
            nxt_aps = {}
            for name in self._latch_vars:
                nxt_aps.update(self._encode(name, nxt_state[name]))

            supplied = yield (out, nxt_aps)
            state = nxt_state
            for name in self._pure_inputs:
                state[name] = self._decode(name, supplied)

    # -- SystemModel plumbing ---------------------------------------------
    def relabel(self, kind, mapping):
        if kind not in ("input", "output", "latch"):
            raise SmvError("unknown relabel kind %r" % kind)
        merged = dict(self._relabel)
        merged.update(mapping)
        return SmvModel(self.program, self.source, merged)

    def write(self, path):
        with open(path, "w") as handle:
            handle.write(self.source)


def load(path):
    with open(path) as handle:
        text = handle.read()
    return SmvModel(parse_smv(text), text)
