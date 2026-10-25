"""MCHyper s-expression -> another checker's formula syntax.

`-f` stays the single source of truth for the property. The internal engine
consumes it through Translator.mchyper_pipeline; a front end that must hand the
formula to an external checker renders it here instead.

Rendering from the *s-expression* rather than from the spot output is
deliberate: the spot form is prefix-notation and already desugared, whereas the
s-expression still has the structure (`Implies`, `Eq`, the quantifier prefix)
that other checkers want to see.
"""

import re

PATH_IDS = "ABCDEFGH"

_TOKEN = re.compile(r'\(|\)|"[^"]*"|[^\s()]+')

_QUANTIFIERS = ("Forall", "Exists")


class FormulaError(Exception):
    pass


def tokenize(text):
    return _TOKEN.findall(text)


def parse(text):
    """MCHyper s-expression -> (quantifiers, body).

    Body nodes: ('ap', name, trace_id) | ('const', 0|1) | (op, [child, ...]).
    """
    tokens = tokenize(text)
    pos = [0]

    def peek():
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def take():
        tok = peek()
        if tok is None:
            raise FormulaError("unexpected end of formula")
        pos[0] += 1
        return tok

    def node():
        tok = take()
        if tok == "(":
            inner = node()
            while peek() == ")":
                take()
                return inner
            # several children inside one paren group
            children = [inner]
            while peek() != ")":
                children.append(node())
            take()
            return children[0] if len(children) == 1 else ("seq", children)
        if tok == "AP":
            name = take().strip('"')
            return ("ap", name, take())
        if tok == "Const":
            return ("const", 1 if take() == "True" else 0)
        if tok in ("Neg", "G", "F", "X"):
            return (tok, [node()])
        if tok in ("And", "Or", "Implies", "Eq", "Neq", "Until", "Release", "WUntil"):
            return (tok, [node(), node()])
        raise FormulaError("unsupported token %r" % tok)

    quantifiers = []
    while True:
        while peek() == "(":
            take()
        if peek() in _QUANTIFIERS:
            quantifiers.append(take())
            continue
        break
    # rewind one '(' so the body parser sees a balanced expression
    pos[0] -= 1
    if pos[0] < 0 or tokens[pos[0]] != "(":
        pos[0] += 1
    body = node()
    if not quantifiers:
        raise FormulaError("formula has no trace quantifier")
    return quantifiers, body


class Renderer(object):
    """Base renderer. Subclasses define the surface syntax of one checker."""

    quantifier = {"Forall": "forall", "Exists": "exists"}
    #: how one quantifier is spelled; HyperQB's grammar wants a space before
    #: the dot ("Forall A ."), AutoHyper's does not ("forall A.")
    quantifier_format = "%s %s."
    unary = {"Neg": "!", "G": "G ", "F": "F ", "X": "X "}
    binary = {"And": "&", "Or": "|", "Implies": "->", "Until": "U",
              "Release": "R", "WUntil": "W"}

    def atom(self, name, trace_id):
        raise NotImplementedError

    def equality(self, left, right):
        raise NotImplementedError

    def render(self, text):
        quantifiers, body = parse(text)
        prefix = " ".join(
            self.quantifier_format % (self.quantifier[q], PATH_IDS[i])
            for i, q in enumerate(quantifiers))
        return "%s\n%s\n" % (prefix, self.expr(body))

    def expr(self, node):
        kind = node[0]
        if kind == "ap":
            return self.atom(node[1], int(node[2]))
        if kind == "const":
            return "true" if node[1] else "false"
        if kind in self.unary:
            return "%s(%s)" % (self.unary[kind], self.expr(node[1][0]))
        if kind in ("Eq", "Neq"):
            left, right = node[1]
            rendered = self.equality(left, right)
            return "!(%s)" % rendered if kind == "Neq" else rendered
        if kind in self.binary:
            left, right = node[1]
            return "(%s %s %s)" % (self.expr(left), self.binary[kind], self.expr(right))
        raise FormulaError("cannot render node %r" % (kind,))


class AutoHyperRenderer(Renderer):
    """AutoHyper syntax: atoms are `{"name"_A}`, equality is `<->`."""

    def atom(self, name, trace_id):
        return '{"%s"_%s}' % (name, PATH_IDS[trace_id])

    def equality(self, left, right):
        return "(%s <-> %s)" % (self.expr(left), self.expr(right))


class HyperQbRenderer(Renderer):
    """HyperQB .hq syntax: atoms are `name[A]`, equality is `=`, negation `~`."""

    quantifier = {"Forall": "Forall", "Exists": "Exists"}
    quantifier_format = "%s %s ."
    unary = {"Neg": "~", "G": "G ", "F": "F ", "X": "X "}

    def atom(self, name, trace_id):
        return "%s[%s]" % (name, PATH_IDS[trace_id])

    def equality(self, left, right):
        return "(%s = %s)" % (self.expr(left), self.expr(right))
