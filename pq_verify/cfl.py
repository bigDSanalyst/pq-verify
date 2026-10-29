"""The CFL front end (docs/CFL.md).

A specification in CFL is lexed and parsed strictly, its meaning checked,
and each required property turned into a first-order obligation. An
obligation is decided two ways that must agree: evaluated on the finite
model the specification defines, and encoded as a QBF over that model and
decided, with a checked certificate, by the DQBF stage (docs/DQBF.md). Each
property is routed to an engine by its parsed field, and dispatched to its
registered check (pq_verify.core).
"""

import itertools
import re

from . import dqbf as _dqbf


class CFLError(ValueError):
    """Text that is not CFL, or a specification that does not mean
    anything. messages holds every problem found, each with its line and
    column."""

    def __init__(self, messages):
        if isinstance(messages, str):
            messages = [messages]
        self.messages = list(messages)
        super().__init__("; ".join(self.messages))


def _at(line, col, msg):
    return f"line {line}, column {col}: {msg}"


# ---- lexer ---------------------------------------------------------------

KEYWORDS = frozenset({"CONTEXT", "DEFINE", "REQUIRE", "property"})
_PUNCT = frozenset("(){}<>:;,")
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


class Token:
    """kind is KEYWORD, IDENT, STRING, EOF, or the punctuation character."""

    __slots__ = ("kind", "value", "line", "col")

    def __init__(self, kind, value, line, col):
        self.kind, self.value, self.line, self.col = kind, value, line, col

    def __repr__(self):
        return f"Token({self.kind}, {self.value!r}, {self.line}:{self.col})"

    def describe(self):
        if self.kind == "EOF":
            return "the end of the specification"
        if self.kind == "STRING":
            return f'the string "{self.value}"'
        return f"'{self.value}'"


def lex(text):
    """The tokens of text, each with its line and column, ending in EOF.
    A character CFL does not define is an error, not a skip."""
    toks, i, line, col, n = [], 0, 1, 1, len(text)
    while i < n:
        ch = text[i]
        if ch == "\n":
            i, line, col = i + 1, line + 1, 1
        elif ch in " \t\r":
            i, col = i + 1, col + 1
        elif text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            col += j - i
            i = j
        elif ch in _PUNCT:
            toks.append(Token(ch, ch, line, col))
            i, col = i + 1, col + 1
        elif ch == '"':
            j = i + 1
            while j < n and text[j] not in '"\n':
                j += 1
            if j >= n or text[j] != '"':
                raise CFLError(_at(line, col, "a string is not closed on its line"))
            value = text[i + 1:j]
            if "\\" in value:
                raise CFLError(_at(line, col, "a backslash in a string: CFL strings "
                                              "have no escapes"))
            toks.append(Token("STRING", value, line, col))
            col += j + 1 - i
            i = j + 1
        else:
            m = _IDENT.match(text, i)
            if not m:
                raise CFLError(_at(line, col, f"unexpected character {ch!r}"))
            w = m.group()
            toks.append(Token("KEYWORD" if w in KEYWORDS else "IDENT", w, line, col))
            col += len(w)
            i = m.end()
    toks.append(Token("EOF", "", line, col))
    return toks


# ---- syntax ----------------------------------------------------------------

class Define:
    """DEFINE property <name> { key: "value"; ... }; attrs is a list of
    (key, value, line, col)."""

    def __init__(self, name, line, col, attrs):
        self.name, self.line, self.col, self.attrs = name, line, col, attrs

    def shape(self):
        return ("DEFINE", self.name, tuple((k, v) for k, v, _, _ in self.attrs))


class Require:
    """REQUIRE level { name, ... }; names is a list of (name, line, col)."""

    def __init__(self, level, line, col, names):
        self.level, self.line, self.col, self.names = level, line, col, names

    def shape(self):
        return ("REQUIRE", self.level, tuple(n for n, _, _ in self.names))


class Context:
    def __init__(self, name, line, col, items):
        self.name, self.line, self.col, self.items = name, line, col, items

    @property
    def defines(self):
        return [it for it in self.items if isinstance(it, Define)]

    @property
    def requires(self):
        return [it for it in self.items if isinstance(it, Require)]

    def shape(self):
        return (self.name, tuple(it.shape() for it in self.items))


class Spec:
    def __init__(self, contexts):
        self.contexts = contexts

    def shape(self):
        """The specification without positions: equal for equal ASTs."""
        return tuple(c.shape() for c in self.contexts)


class _Parser:
    def __init__(self, toks):
        self.toks, self.i = toks, 0

    def peek(self):
        return self.toks[self.i]

    def take(self, kind, what, value=None):
        tok = self.peek()
        if tok.kind != kind or (value is not None and tok.value != value):
            raise CFLError(_at(tok.line, tok.col, f"expected {what}, found {tok.describe()}"))
        self.i += 1
        return tok

    def spec(self):
        contexts = []
        while self.peek().kind != "EOF":
            contexts.append(self.context())
        return Spec(contexts)

    def context(self):
        kw = self.take("KEYWORD", "CONTEXT", "CONTEXT")
        self.take("(", "'('")
        name = self.take("IDENT", "a context name")
        self.take(")", "')'")
        self.take("{", "'{'")
        items = []
        while True:
            tok = self.peek()
            if tok.kind == "KEYWORD" and tok.value == "DEFINE":
                items.append(self.define())
            elif tok.kind == "KEYWORD" and tok.value == "REQUIRE":
                items.append(self.require())
            elif tok.kind == "}":
                self.i += 1
                return Context(name.value, kw.line, kw.col, items)
            else:
                raise CFLError(_at(tok.line, tok.col, f"expected DEFINE, REQUIRE or '}}' "
                                                      f"in context {name.value}, found "
                                                      f"{tok.describe()}"))

    def define(self):
        kw = self.take("KEYWORD", "DEFINE", "DEFINE")
        self.take("KEYWORD", "'property'", "property")
        self.take("<", "'<'")
        name = self.take("IDENT", "a property name")
        self.take(">", "'>'")
        self.take("{", "'{'")
        attrs = []
        while self.peek().kind != "}":
            key = self.take("IDENT", "an attribute name or '}'")
            self.take(":", "':'")
            value = self.take("STRING", "a string")
            self.take(";", "';'")
            attrs.append((key.value, value.value, key.line, key.col))
        self.i += 1
        return Define(name.value, kw.line, kw.col, attrs)

    def require(self):
        kw = self.take("KEYWORD", "REQUIRE", "REQUIRE")
        level = self.take("IDENT", "a level")
        self.take("{", "'{'")
        names = []
        if self.peek().kind != "}":
            while True:
                t = self.take("IDENT", "a property name")
                names.append((t.value, t.line, t.col))
                if self.peek().kind != ",":
                    break
                self.i += 1
        self.take("}", "',' or '}'")
        return Require(level.value, kw.line, kw.col, names)


def parse(text):
    """The AST of a CFL specification (docs/CFL.md); CFLError on anything the
    grammar does not define, with its line and column."""
    return _Parser(lex(text)).spec()


def to_text(spec):
    """The specification printed back as CFL: parse(to_text(s)) has the
    shape of s."""
    out = []
    for ctx in spec.contexts:
        out.append(f"CONTEXT ( {ctx.name} ) {{")
        for it in ctx.items:
            if isinstance(it, Define):
                attrs = " ".join(f'{k}: "{v}";' for k, v, _, _ in it.attrs)
                out.append(f"  DEFINE property <{it.name}> {{ {attrs} }}")
            else:
                out.append(f"  REQUIRE {it.level} {{ {', '.join(n for n, _, _ in it.names)} }}")
        out.append("}")
    return "\n".join(out) + "\n"


# ---- meaning ---------------------------------------------------------------

#: A property's field names the algebra its check runs in, and so its engine.
FIELDS = {"Z_3329": "Zq", "Z_8380417": "Zq32", "GF2": "GF2", "cubic": "cubic",
          "conformity": "conformity", "period": "period"}
#: The constraint types each engine decides.
TYPES = {"Zq": ("linear",), "Zq32": ("linear",), "GF2": ("linear",),
         "cubic": ("cubic",), "conformity": ("dynamical",),
         "period": ("algebraic", "rank", "residue")}
ATTRIBUTES = ("type", "field")
LEVELS = ("Full",)


class Property:
    """A checked property: context, name, type, field, the engine its field
    routes to, whether its context requires it, and where it is defined."""

    def __init__(self, context, name, type_, field, engine, required, line, col):
        self.context, self.name, self.type, self.field = context, name, type_, field
        self.engine, self.required, self.line, self.col = engine, required, line, col

    @property
    def key(self):
        return f"{self.context}.{self.name}"

    def __repr__(self):
        return (f"Property({self.key}, {self.type}, {self.field} -> {self.engine}"
                f"{', required' if self.required else ''})")


def check(spec):
    """The properties of a parsed specification, checked (docs/CFL.md): unique
    names, exactly the attributes type and field, a known field and a type
    its engine decides, and REQUIRE naming only properties its context
    defines. CFLError lists every problem."""
    errors, props, first = [], [], {}
    for ctx in spec.contexts:
        if ctx.name in first:
            errors.append(_at(ctx.line, ctx.col, f"context {ctx.name} is defined again "
                                                 f"(first at line {first[ctx.name]})"))
        first.setdefault(ctx.name, ctx.line)
        defined, mine = {}, []
        for d in ctx.defines:
            where = f"{ctx.name}.{d.name}"
            if d.name in defined:
                errors.append(_at(d.line, d.col, f"{where} is defined again (first at "
                                                 f"line {defined[d.name]})"))
            defined.setdefault(d.name, d.line)
            attrs = {}
            for k, v, l, c in d.attrs:
                if k not in ATTRIBUTES:
                    errors.append(_at(l, c, f"{where}: unknown attribute {k}; a property "
                                            f"has {' and '.join(ATTRIBUTES)}"))
                elif k in attrs:
                    errors.append(_at(l, c, f"{where}: {k} is given again"))
                else:
                    attrs[k] = (v, l, c)
            missing = [k for k in ATTRIBUTES if k not in attrs]
            if missing:
                errors.append(_at(d.line, d.col, f"{where} has no {' or '.join(missing)}"))
            engine = None
            if "field" in attrs:
                fv, fl, fc = attrs["field"]
                engine = FIELDS.get(fv)
                if engine is None:
                    errors.append(_at(fl, fc, f'{where}: unknown field "{fv}"; the fields '
                                              f'are {", ".join(FIELDS)}'))
            if engine and "type" in attrs:
                tv, tl, tc = attrs["type"]
                if tv not in TYPES[engine]:
                    errors.append(_at(tl, tc, f'{where}: the {attrs["field"][0]} engine '
                                              f'decides {" and ".join(TYPES[engine])} '
                                              f'constraints, not "{tv}"'))
            mine.append(Property(ctx.name, d.name, attrs.get("type", (None,))[0],
                                 attrs.get("field", (None,))[0], engine, False,
                                 d.line, d.col))
        required = set() if ctx.requires else set(defined)
        for rq in ctx.requires:
            if rq.level not in LEVELS:
                errors.append(_at(rq.line, rq.col, f"REQUIRE {rq.level}: the only level "
                                                   f"is {', '.join(LEVELS)}"))
            listed = set()
            for nm, l, c in rq.names:
                if nm not in defined:
                    errors.append(_at(l, c, f"REQUIRE names {nm}, which {ctx.name} "
                                            f"does not define"))
                elif nm in listed:
                    errors.append(_at(l, c, f"REQUIRE names {nm} again"))
                listed.add(nm)
            required |= set(defined) if not rq.names else listed & set(defined)
        for p in mine:
            p.required = p.name in required
        props += mine
    if errors:
        raise CFLError(errors)
    return props


def route(prop):
    """The engine a property's parsed field routes it to."""
    return FIELDS[prop.field]


# ---- first-order logic -----------------------------------------------------
# Formulas are tuples: ("pred", name, terms), ("not", f), ("and", f, ...),
# ("or", f, ...), ("implies", a, b), ("forall", var, f), ("exists", var, f);
# a term is ("var", name) or ("const", value).

def var(name):
    return ("var", name)


def const(value):
    return ("const", value)


def pred(name, *terms):
    return ("pred", name, tuple(terms))


def show(f):
    """f in the usual notation."""
    op = f[0]
    if op == "pred":
        args = ", ".join(t[1] if t[0] == "var" else f'"{t[1]}"' for t in f[2])
        return f"{f[1]}({args})"
    if op == "not":
        return "¬" + show(f[1])
    if op in ("and", "or"):
        sym = " ∧ " if op == "and" else " ∨ "
        return "(" + sym.join(show(g) for g in f[1:]) + ")"
    if op == "implies":
        return f"({show(f[1])} → {show(f[2])})"
    q = "∀" if op == "forall" else "∃"
    return f"{q}{f[1]} {show(f[2])}"


def free_vars(f):
    op = f[0]
    if op == "pred":
        return {t[1] for t in f[2] if t[0] == "var"}
    if op in ("forall", "exists"):
        return free_vars(f[2]) - {f[1]}
    out = set()
    for g in f[1:]:
        out |= free_vars(g)
    return out


def _nnf(f, neg=False):
    """f, or its negation, with no implication and negation only on
    predicates."""
    op = f[0]
    if op == "pred":
        return ("not", f) if neg else f
    if op == "not":
        return _nnf(f[1], not neg)
    if op == "implies":
        return _nnf(("or", ("not", f[1]), f[2]), neg)
    if op in ("and", "or"):
        dual = {"and": "or", "or": "and"}[op] if neg else op
        return (dual,) + tuple(_nnf(g, neg) for g in f[1:])
    if op in ("forall", "exists"):
        q = {"forall": "exists", "exists": "forall"}[op] if neg else op
        return (q, f[1], _nnf(f[2], neg))
    raise ValueError(f"not a formula: {f!r}")


def _rename_apart(f, used, env):
    """f with each bound variable renamed to a name not in used (which
    grows); env maps names in scope to their new names."""
    op = f[0]
    if op == "pred":
        return ("pred", f[1], tuple(("var", env.get(t[1], t[1])) if t[0] == "var" else t
                                    for t in f[2]))
    if op in ("forall", "exists"):
        new, k = f[1], 1
        while new in used:
            new, k = f"{f[1]}{k}", k + 1
        used.add(new)
        return (op, new, _rename_apart(f[2], used, {**env, f[1]: new}))
    return (op,) + tuple(_rename_apart(g, used, env) for g in f[1:])


def _pull(f):
    """(prefix, matrix) of a negation normal form whose bound variables are
    distinct and free nowhere, so every quantifier can move to the front."""
    op = f[0]
    if op in ("pred", "not"):
        return [], f
    if op in ("forall", "exists"):
        pre, m = _pull(f[2])
        return [(op, f[1])] + pre, m
    prefix, parts = [], []
    for g in f[1:]:
        pre, m = _pull(g)
        prefix += pre
        parts.append(m)
    return prefix, (op,) + tuple(parts)


def prenex(f):
    """(prefix, matrix): f in prenex normal form, equivalent to f over every
    nonempty domain. prefix is a list of (quantifier, variable), the matrix
    is quantifier-free with negation only on predicates."""
    return _pull(_rename_apart(_nnf(f), set(free_vars(f)), {}))


def from_prenex(prefix, matrix):
    for q, v in reversed(prefix):
        matrix = (q, v, matrix)
    return matrix


def evaluate(f, domain, rels, env=None):
    """f's truth in a finite model: domain a nonempty list, rels a dict from
    predicate name to the set of argument tuples where it holds."""
    env = env or {}
    op = f[0]
    if op == "pred":
        try:
            args = tuple(env[t[1]] if t[0] == "var" else t[1] for t in f[2])
        except KeyError as e:
            raise ValueError(f"variable {e.args[0]} is free") from None
        return args in rels.get(f[1], ())
    if op == "not":
        return not evaluate(f[1], domain, rels, env)
    if op == "and":
        return all(evaluate(g, domain, rels, env) for g in f[1:])
    if op == "or":
        return any(evaluate(g, domain, rels, env) for g in f[1:])
    if op == "implies":
        return (not evaluate(f[1], domain, rels, env)) or evaluate(f[2], domain, rels, env)
    if op == "forall":
        return all(evaluate(f[2], domain, rels, {**env, f[1]: d}) for d in domain)
    if op == "exists":
        return any(evaluate(f[2], domain, rels, {**env, f[1]: d}) for d in domain)
    raise ValueError(f"not a formula: {f!r}")


# ---- obligations as first-order formulas, and their model -------------------

def obligation(prop):
    """The first-order obligation of a property: every context with its
    context's name has a property with its name, in its field, verified."""
    c, p = var("c"), var("p")
    return ("forall", "c", ("implies", pred("Ctx", c, const(prop.context)),
                            ("exists", "p", ("and", pred("Prop", c, p, const(prop.name)),
                                             pred("Field", p, const(prop.field)),
                                             pred("Verified", p)))))


def model(props, verified):
    """The finite model a checked specification defines: its contexts and
    properties as the domain, and the relations Ctx, Prop, Field and
    Verified, the last from the set of verified property keys."""
    contexts = []
    for p in props:
        if ("context", p.context) not in contexts:
            contexts.append(("context", p.context))
    elems = {p.key: ("property", p.context, p.name) for p in props}
    rels = {"Ctx": {(c, c[1]) for c in contexts},
            "Prop": {(("context", p.context), elems[p.key], p.name) for p in props},
            "Field": {(elems[p.key], p.field) for p in props},
            "Verified": {(elems[p.key],) for p in props if p.key in verified}}
    return contexts + list(elems.values()), rels


# ---- a closed formula over a finite model, as a QBF ------------------------

def to_qbf(f, domain, rels):
    """A closed formula over a finite model as a QBF, written as a DQBF in
    which each existential depends on the universals before it (docs/CFL.md).
    Each variable of f's prenex form becomes k bits, k enough for the
    domain; a code past the domain is no element, so universals are
    restricted to the domain and existentials must choose in it. Each
    atom's truth table over its variables' bits, and each connective, is
    defined by a fresh existential (Tseitin), which depends on every
    universal. True iff f holds in the model. Returns (dqbf, bits), bits
    mapping each variable of the prefix to its bit names."""
    if not domain:
        raise ValueError("an empty domain")
    prefix, matrix = prenex(f)
    if free_vars(from_prenex(prefix, matrix)):
        raise ValueError("the formula is not closed")
    n = len(domain)
    k = max(1, (n - 1).bit_length())
    q = _dqbf.DQBF()
    bits, univ = {}, []
    for quant, v in prefix:
        names = [f"{v}.{i}" for i in range(k)]
        bits[v] = names
        if quant == "forall":
            q.forall(*names)
            univ += names
        else:
            for b in names:
                q.exists(b, list(univ))
    count = [0]

    def fresh():
        count[0] += 1
        name = f"t{count[0]}"
        q.exists(name, list(q.universals))
        return name

    def codes(vs):
        """Every assignment of codes to vs: (dict var -> code, the literals
        that hold exactly there)."""
        for combo in itertools.product(range(1 << k), repeat=len(vs)):
            lits = []
            for v, code in zip(vs, combo):
                lits += [(b, bool(code >> i & 1)) for i, b in enumerate(bits[v])]
            yield dict(zip(vs, combo)), lits

    def table(vs, truth):
        """A fresh t with t <-> truth(code of each v), clause by clause:
        at each assignment of the bits, t takes truth's value."""
        t = fresh()
        for env, lits in codes(vs):
            q.clause([(b, not val) for b, val in lits] + [(t, truth(env))])
        return t

    def atom(a):
        vs = sorted({x[1] for x in a[2] if x[0] == "var"})

        def truth(env):
            if any(env[v] >= n for v in vs):
                return False
            args = tuple(domain[env[x[1]]] if x[0] == "var" else x[1] for x in a[2])
            return args in rels.get(a[1], ())
        return table(vs, truth)

    def gate(op, ins):
        t = fresh()
        if op == "and":
            for x, pos in ins:
                q.clause([(t, False), (x, pos)])
            q.clause([(t, True)] + [(x, not pos) for x, pos in ins])
        else:
            q.clause([(t, False)] + list(ins))
            for x, pos in ins:
                q.clause([(t, True), (x, not pos)])
        return t

    def encode(g):
        """(name, positive): a literal equal to g's truth."""
        if g[0] == "pred":
            return atom(g), True
        if g[0] == "not":
            x, pos = encode(g[1])
            return x, not pos
        return gate(g[0], [encode(h) for h in g[1:]]), True

    def in_domain(v):
        return table([v], lambda env: env[v] < n), True

    # The matrix, relativized to the domain from the innermost variable out.
    lit = encode(matrix)
    for quant, v in reversed(prefix):
        d = in_domain(v)
        if quant == "forall":
            lit = (gate("or", [(d[0], not d[1]), lit]), True)
        else:
            lit = (gate("and", [d, lit]), True)
    q.clause([lit])
    return q, bits


def decide(f, domain, rels, gf2=None):
    """f over the finite model, decided twice: evaluated directly, and as a
    QBF by the DQBF stage with its certificate checked. (truth, decision);
    a disagreement is a CertificateError."""
    direct = evaluate(f, domain, rels)
    q, _ = to_qbf(f, domain, rels)
    d = _dqbf.decide(q, gf2)
    if d.truth is not None and d.truth != direct:
        raise _dqbf.CertificateError(f"the QBF of {show(f)} was decided {d.truth}, "
                                     f"but the formula is {direct} on the model")
    return direct, d
