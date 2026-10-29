"""Dependency QBF (DQBF), decided exactly, with certificates.

docs/DQBF.md is the specification. A DQBF  forall U  exists x_1(D_1) ... x_m(D_m).
phi  is true when there are Skolem functions f_i of the universals in D_i
that make phi hold for every assignment of U. Two procedures decide it:

* phi a conjunction of XOR constraints: affine Skolem functions, which are
  complete there, as the solutions of a linear system over GF(2), solved on
  pq-verify's GF(2) engine when it fits. True comes with the functions, false
  with a set of the system's equations that sum to 0 = 1.
* phi with clauses: universal expansion to CNF, each constraint over the
  universals it reads, and a CDCL solver that logs every clause it learns.
  True comes with the Skolem functions as truth tables, false with a RUP
  proof. Used while the expansion has at most MAX_EXPANSION variables and
  clauses together.

Every answer is verified by a checker here that does not use the solver or
the engine, and an answer the checker rejects raises CertificateError: it is
a defect, never a result. Anything else is CANNOT VERIFY (truth None).
"""

import ctypes
import itertools
import re

MAX_EXPANSION = 1 << 18        # variables + clauses of an expansion
MAX_CONFLICTS = 200_000        # CDCL conflicts before CANNOT VERIFY


class DQBFError(ValueError):
    """A malformed formula or module."""


class CertificateError(RuntimeError):
    """A solver or engine answer that its certificate check rejected."""


class DQBF:
    """forall U exists x_1(D_1) ... exists x_m(D_m). phi, with phi a
    conjunction of XOR constraints and clauses. Variables are declared before
    they are used, and an existential's dependencies are declared universals."""

    def __init__(self):
        self.universals = []            # names, in declaration order
        self.uset = set()
        self.existentials = {}          # name -> frozenset of universals
        self.order = []                 # existential names, in order
        self.xors = []                  # (frozenset of names, parity)
        self.clauses = []               # tuples of (name, positive)

    def forall(self, *names):
        for n in names:
            self._new(n)
            self.universals.append(n)
            self.uset.add(n)
        return self

    def exists(self, name, deps=()):
        deps = frozenset(deps)
        bad = deps - self.uset
        if bad:
            raise DQBFError(f"{name} depends on {', '.join(sorted(bad))}: "
                            f"not a declared universal")
        self._new(name)
        self.existentials[name] = deps
        self.order.append(name)
        return self

    def xor(self, names, parity):
        """The sum of names mod 2 is parity; a name twice cancels."""
        if parity not in (0, 1) or isinstance(parity, bool):
            raise DQBFError(f"parity {parity!r} is not 0 or 1")
        odd = set()
        for n in names:
            self._known(n)
            odd ^= {n}
        self.xors.append((frozenset(odd), parity))
        return self

    def clause(self, lits):
        """At least one of lits, each (name, positive), holds."""
        lits = tuple((n, bool(pos)) for n, pos in lits)
        for n, _ in lits:
            self._known(n)
        self.clauses.append(lits)
        return self

    def deps(self, x):
        """x's dependencies, in universal order."""
        return [u for u in self.universals if u in self.existentials[x]]

    def reads(self, names):
        """The universals a constraint over names depends on, in universal
        order: its own and its existentials' dependencies."""
        s = set(names) & self.uset
        for v in names:
            if v in self.existentials:
                s |= self.existentials[v]
        return [u for u in self.universals if u in s]

    @property
    def num_vars(self):
        return len(self.universals) + len(self.order)

    def _new(self, n):
        if not isinstance(n, str) or not n:
            raise DQBFError(f"variable name {n!r}")
        if n in self.uset or n in self.existentials:
            raise DQBFError(f"{n} is declared twice")

    def _known(self, n):
        if n not in self.uset and n not in self.existentials:
            raise DQBFError(f"{n} is not declared")


class Decision:
    """truth is True, False, or None (CANNOT VERIFY). certificate is what the
    checker verified: affine Skolem functions {x: (constant, universals)}, a
    refutation (indices of equations of the Skolem system), Skolem truth
    tables {x: {bits of x's dependencies: value}}, or a RUP proof. engine is
    what found it: libpqv_gf2, elimination or cdcl."""

    def __init__(self, truth, method, certificate, detail, engine=None):
        self.truth = truth
        self.method = method
        self.certificate = certificate
        self.detail = detail
        self.engine = engine

    def __repr__(self):
        return f"Decision({self.truth}, {self.method!r}, {self.detail!r})"


def route(f):
    """The procedure that decides f: 'affine-skolem' for an XOR matrix,
    'expansion' for one with clauses whose expansion is within
    MAX_EXPANSION, and 'cannot-verify' otherwise."""
    if not f.clauses:
        return "affine-skolem"
    nv, nc = expansion_size(f)
    return "expansion" if nv + nc <= MAX_EXPANSION else "cannot-verify"


def decide(f, gf2=None, max_conflicts=MAX_CONFLICTS):
    """Decide f, with its certificate checked. gf2 is pq-verify's GF(2)
    engine (bound), used for the Skolem system when it fits."""
    method = route(f)
    if method == "affine-skolem":
        return _decide_affine(f, gf2)
    # The XOR constraints alone first: without Skolem functions for them, f
    # has none, and the refutation is short and found in polynomial time.
    unknowns, eqs = skolem_system(f)
    status, out = _eliminate(len(unknowns), eqs)
    if status == "unsat":
        if not check_refutation(f, out):
            raise CertificateError("the refutation of the XOR constraints "
                                   "fails the check")
        return Decision(False, "affine-skolem", out,
                        f"the XOR constraints alone have no Skolem functions: "
                        f"{len(out)} equation{'s' if len(out) != 1 else ''} of "
                        f"their Skolem system sum to 0 = 1", "elimination")
    if method == "expansion":
        return _decide_expansion(f, max_conflicts)
    nv, nc = expansion_size(f)
    return Decision(None, None, None,
                    f"CANNOT VERIFY: the expansion would have {nv} variables and "
                    f"up to {nc} clauses; the limit is {MAX_EXPANSION} together")


# ---- XOR matrices: affine Skolem functions --------------------------------

def skolem_system(f):
    """The linear system over GF(2) whose solutions are the affine Skolem
    functions of f's XOR constraints (docs/DQBF.md): (unknowns, equations).
    unknowns[k] is (x, None), x's constant, or (x, u), x's coefficient of
    u; an equation is (frozenset of unknown indices, rhs). The checker
    builds it again from the formula, so it is a function of f alone."""
    unknowns, index = [], {}
    for x in f.order:
        index[(x, None)] = len(unknowns)
        unknowns.append((x, None))
        for u in f.deps(x):
            index[(x, u)] = len(unknowns)
            unknowns.append((x, u))
    eqs = []
    for names, p in f.xors:
        exist = [x for x in f.order if x in names]
        univ = names & f.uset
        eqs.append((frozenset(index[(x, None)] for x in exist), p))
        for u in f.reads(names):
            eqs.append((frozenset(index[(x, u)] for x in exist
                                  if u in f.existentials[x]),
                        1 if u in univ else 0))
    return unknowns, eqs


def _eliminate(n, eqs):
    """Gaussian elimination over GF(2), keeping which equations each row is
    the sum of. ('sat', solution), free unknowns 0, or ('unsat', the sorted
    indices of equations that sum to 0 = 1)."""
    pivots = {}                          # lowest bit -> (mask, rhs, provenance)
    for k, (lhs, rhs) in enumerate(eqs):
        mask = 0
        for v in lhs:
            mask |= 1 << v
        prov = 1 << k
        while mask:
            low = mask & -mask
            if low not in pivots:
                break
            pm, pr, pp = pivots[low]
            mask ^= pm
            rhs ^= pr
            prov ^= pp
        if mask:
            pivots[mask & -mask] = (mask, rhs, prov)
        elif rhs:
            return "unsat", [i for i in range(k + 1) if prov >> i & 1]
    sol = [0] * n
    for low in sorted(pivots, reverse=True):
        mask, rhs, _ = pivots[low]
        rest, val = mask ^ low, rhs
        while rest:
            b = rest & -rest
            val ^= sol[b.bit_length() - 1]
            rest ^= b
        sol[low.bit_length() - 1] = val
    return "sat", sol


def _engine_solve(gf2, n, eqs):
    """The Skolem system on libpqv_gf2: ('sat', solution) or ('unsat',
    None); None if it does not fit the engine."""
    from .core import GF2S, GF2R, EngineInputError
    if n == 0:
        return None
    s, r = GF2S(), GF2R()
    try:
        gf2.gf2_init(ctypes.byref(s), n)
        for lhs, rhs in eqs:
            idx = sorted(lhs)
            arr = (ctypes.c_int * max(len(idx), 1))(*idx)
            gf2.gf2_add_xor(ctypes.byref(s), arr, len(idx), rhs)
    except EngineInputError:
        return None
    gf2.gf2_solve(ctypes.byref(s), ctypes.byref(r))
    if r.satisfiable:
        return "sat", [r.assignment[i] & 1 for i in range(n)]
    return "unsat", None


def _decide_affine(f, gf2):
    unknowns, eqs = skolem_system(f)
    engine = _engine_solve(gf2, len(unknowns), eqs) if gf2 is not None else None
    if engine is not None and engine[0] == "sat":
        where, (status, out) = "libpqv_gf2", engine
    else:
        where, (status, out) = "elimination", _eliminate(len(unknowns), eqs)
        if engine is not None and status == "sat":
            raise CertificateError("libpqv_gf2 called a solvable Skolem system "
                                   "unsatisfiable")
        if engine is not None:
            where = "libpqv_gf2 and elimination"
    if status == "sat":
        skolem = {x: [0, set()] for x in f.order}
        for (x, u), bit in zip(unknowns, out):
            if bit and u is None:
                skolem[x][0] = 1
            elif bit:
                skolem[x][1].add(u)
        skolem = {x: (c, frozenset(lin)) for x, (c, lin) in skolem.items()}
        if not check_affine(f, skolem):
            raise CertificateError(f"the Skolem functions from {where} fail "
                                   f"the check")
        return Decision(True, "affine-skolem", skolem,
                        f"affine Skolem functions, {len(unknowns)} unknowns, "
                        f"{len(eqs)} equations", where)
    if not check_refutation(f, out):
        raise CertificateError("the refutation fails the check")
    eqn = "1 equation of the Skolem system is" if len(out) == 1 else \
        f"{len(out)} equations of the Skolem system sum to"
    return Decision(False, "affine-skolem", out,
                    f"{eqn} 0 = 1: no affine Skolem functions, so none", where)


def check_affine(f, skolem):
    """True iff f has no clauses, skolem gives every existential x an affine
    function (constant, set of universals with coefficient 1) of its own
    dependencies only, and every XOR constraint holds identically after
    substitution: its constant and every coefficient vanish."""
    if f.clauses or not isinstance(skolem, dict) or set(skolem) != set(f.existentials):
        return False
    for x, fx in skolem.items():
        if not isinstance(fx, tuple) or len(fx) != 2:
            return False
        c, lin = fx
        if (c not in (0, 1) or isinstance(c, bool)
                or not isinstance(lin, (set, frozenset))
                or not lin <= f.existentials[x]):
            return False
    for names, p in f.xors:
        const, lin = p, set()
        for v in names:
            if v in f.uset:
                lin ^= {v}
            else:
                const ^= skolem[v][0]
                lin ^= skolem[v][1]
        if const or lin:
            return False
    return True


def check_refutation(f, rows):
    """True iff rows are distinct equations of the Skolem system of f's XOR
    constraints, built again here from the formula, whose sum is 0 = 1. f
    is then false: with clauses too, since they only add constraints."""
    _, eqs = skolem_system(f)
    if (not isinstance(rows, list) or not rows
            or any(type(k) is not int or not 0 <= k < len(eqs) for k in rows)
            or len(set(rows)) != len(rows)):
        return False
    lhs, rhs = set(), 0
    for k in rows:
        lhs ^= eqs[k][0]
        rhs ^= eqs[k][1]
    return not lhs and rhs == 1


# ---- clauses: universal expansion ------------------------------------------

def _xor_cost(k):
    """(fresh variables, clauses) of _xor_cnf for k variables."""
    if k > 3:
        return k - 2, 4 * (k - 2) + 2
    return 0, (1 << (k - 1)) if k else 1


def expansion_size(f):
    """(variables, at most this many clauses) of f's expansion, counted
    without building it."""
    nv = sum(1 << len(f.existentials[x]) for x in f.order)
    nc = 0
    for names, _ in f.xors:
        inst = 1 << len(f.reads(names))
        fresh, cls = _xor_cost(sum(1 for v in names if v in f.existentials))
        nv += inst * fresh
        nc += inst * cls
    for lits in f.clauses:
        nc += 1 << len(f.reads([v for v, _ in lits]))
    return nv, nc


def _xor_cnf(vs, parity, fresh):
    """Clauses for sum(vs) mod 2 == parity: the 2^(k-1) clauses that forbid
    each wrong assignment for k <= 3, a Tseitin chain for more."""
    def lit(v, val):                    # the literal that is false when v == val
        return -v if val else v
    if not vs:
        return [[]] if parity else []
    if len(vs) <= 3:
        return [[lit(v, b) for v, b in zip(vs, bits)]
                for bits in itertools.product((0, 1), repeat=len(vs))
                if sum(bits) % 2 != parity]
    out, t = [], vs[0]
    for v in vs[1:-1]:
        n = fresh()                     # n = t xor v
        out += [[lit(t, a), lit(v, b), lit(n, c)]
                for a, b, c in itertools.product((0, 1), repeat=3) if c != a ^ b]
        t = n
    out += [[lit(t, a), lit(vs[-1], b)]
            for a, b in itertools.product((0, 1), repeat=2) if a ^ b != parity]
    return out


def expand(f):
    """The universal expansion of f to CNF (docs/DQBF.md): (number of variables,
    clauses, copies). copies[(x, tau)] is the variable for x's Skolem function
    on tau, the bits of x's dependencies in universal order. Each constraint
    is instantiated once per assignment of the universals it reads, which
    gives the same clauses as once per assignment of all of them. A
    function of f alone: the RUP checker builds it again."""
    deps = {x: f.deps(x) for x in f.order}
    copies, top = {}, [0]
    for x in f.order:
        for tau in itertools.product((0, 1), repeat=len(deps[x])):
            top[0] += 1
            copies[(x, tau)] = top[0]

    def fresh():
        top[0] += 1
        return top[0]

    def instances(names):
        reads = f.reads(names)
        for bits in itertools.product((0, 1), repeat=len(reads)):
            rho = dict(zip(reads, bits))
            yield rho, lambda x: copies[(x, tuple(rho[u] for u in deps[x]))]

    cnf = []
    for names, p in f.xors:
        exist = [x for x in f.order if x in names]
        univ = names & f.uset
        for rho, var in instances(names):
            cnf += _xor_cnf([var(x) for x in exist],
                            p ^ (sum(rho[u] for u in univ) & 1), fresh)
    for lits in f.clauses:
        for rho, var in instances([v for v, _ in lits]):
            out, satisfied = set(), False
            for v, pos in lits:
                if v in f.uset:
                    satisfied |= rho[v] == pos
                else:
                    out.add(var(v) if pos else -var(v))
            if not satisfied and not any(-l in out for l in out):
                cnf.append(sorted(out, key=abs))
    return top[0], cnf, copies


def _decide_expansion(f, max_conflicts):
    nv, cnf, copies = expand(f)
    sat, out = _CDCL(nv, cnf).solve(max_conflicts)
    if sat is None:
        return Decision(None, "expansion", None,
                        f"CANNOT VERIFY: no answer within {max_conflicts} "
                        f"conflicts; expansion {nv} variables, {len(cnf)} clauses",
                        "cdcl")
    if sat:
        tables = {x: {} for x in f.order}
        for (x, tau), v in copies.items():
            tables[x][tau] = 1 if out[v] else 0
        if not check_tables(f, tables):
            raise CertificateError("the Skolem tables from the expansion fail "
                                   "the check")
        return Decision(True, "expansion", tables,
                        f"Skolem tables checked on every assignment; expansion "
                        f"{nv} variables, {len(cnf)} clauses", "cdcl")
    if not check_expansion_refutation(f, out):
        raise CertificateError("the RUP proof fails the check")
    return Decision(False, "expansion", out,
                    f"RUP proof of {len(out)} clauses checked; expansion {nv} "
                    f"variables, {len(cnf)} clauses", "cdcl")


def check_tables(f, tables):
    """True iff tables give every existential a total function of its own
    dependencies, and every constraint of f holds, evaluated from the
    formula, for every assignment of the universals it reads: and so for
    every assignment of all of them."""
    if not isinstance(tables, dict) or set(tables) != set(f.existentials):
        return False
    deps = {x: f.deps(x) for x in f.order}
    for x in f.order:
        t = tables[x]
        if (not isinstance(t, dict)
                or set(t) != set(itertools.product((0, 1), repeat=len(deps[x])))
                or any(type(v) is not int or v not in (0, 1) for v in t.values())):
            return False

    def always(names, holds):
        reads = f.reads(names)
        for bits in itertools.product((0, 1), repeat=len(reads)):
            rho = dict(zip(reads, bits))
            val = {v: rho[v] if v in f.uset
                   else tables[v][tuple(rho[u] for u in deps[v])] for v in names}
            if not holds(val):
                return False
        return True

    for names, p in f.xors:
        if not always(names, lambda val: sum(val.values()) % 2 == p):
            return False
    for lits in f.clauses:
        if not always({v for v, _ in lits},
                      lambda val: any(val[v] == pos for v, pos in lits)):
            return False
    return True


def check_expansion_refutation(f, proof):
    """True iff proof is a RUP refutation of f's universal expansion, built
    again here from the formula."""
    nv, cnf, _ = expand(f)
    return check_rup(nv, cnf, proof)


def check_rup(nv, clauses, proof):
    """True iff proof is a list of clauses over variables 1..nv, each of
    which follows by unit propagation from the clauses and the proof clauses
    before it, and whose last is the empty clause.

    The assignment that unit propagation forces from the clauses alone (the
    top level) is kept from one lemma to the next and extended as clauses are
    added; it is closed under propagation, so a lemma's check propagates only
    from the negation of its own literals, and is undone after. Which
    clauses propagation looks at is decided by two watched literals per
    clause; whether a clause is unit or conflicting is decided by reading all
    of it, so the watches can make the check slower or faster but never
    accept what unit propagation does not derive."""
    if (not isinstance(proof, list) or not proof
            or not all(isinstance(c, (list, tuple)) for c in proof) or proof[-1]):
        return False
    val = [0] * (nv + 1)                 # +1 true, -1 false, 0 unassigned
    trail, db, watch = [], [], {}
    top_conflict = [False]

    def assign(l):
        val[l if l > 0 else -l] = 1 if l > 0 else -1
        trail.append(l)

    def propagate(stack):
        """Unit propagation from the assigned literals in stack, newest
        first; True on a conflict."""
        while stack:
            fl = -stack.pop()            # the literal that just became false
            ws = watch.get(fl)
            if not ws:
                continue
            keep, k, n = [], 0, len(ws)
            while k < n:
                i = ws[k]
                k += 1
                c = db[i]
                if c[0] == fl:
                    c[0], c[1] = c[1], fl
                if c[1] != fl:
                    raise RuntimeError("RUP checker: a clause in the wrong watch list")
                o = c[0]
                ov = val[o] if o > 0 else -val[-o]
                if ov == 1:
                    keep.append(i)
                    continue
                for j in range(2, len(c)):
                    x = c[j]
                    if (val[x] if x > 0 else -val[-x]) != -1:
                        c[1], c[j] = x, fl
                        watch.setdefault(x, []).append(i)
                        break
                else:                    # every literal but o is false
                    keep.append(i)
                    if ov == -1:
                        keep.extend(ws[k:])
                        watch[fl] = keep
                        return True
                    assign(o)
                    stack.append(o)
            watch[fl] = keep
        return False

    def add(c):
        """c joins the clauses; the top level is extended if it is unit."""
        if top_conflict[0]:
            return
        c = list(dict.fromkeys(c))
        lits = set(c)
        if any(-x in lits for x in c):
            return                       # a tautology never propagates
        if any((val[x] if x > 0 else -val[-x]) == 1 for x in c):
            return                       # satisfied at the top level, for good
        free = [x for x in c if (val[x] if x > 0 else -val[-x]) == 0]
        if not free:
            top_conflict[0] = True
        elif len(free) == 1:
            assign(free[0])
            if propagate([free[0]]):
                top_conflict[0] = True
        else:
            rest = [x for x in c if x != free[0] and x != free[1]]
            db.append([free[0], free[1]] + rest)
            for x in free[:2]:
                watch.setdefault(x, []).append(len(db) - 1)

    def well_formed(c):
        return all(type(l) is int and l != 0 and abs(l) <= nv for l in c)

    for c in clauses:
        c = list(c)
        if not well_formed(c):
            return False
        add(c)
    for lemma in proof:
        lemma = list(lemma)
        if not well_formed(lemma):
            return False
        if not top_conflict[0]:
            mark, ok, stack = len(trail), False, []
            for l in lemma:
                v = val[l] if l > 0 else -val[-l]
                if v == 1:               # its negation conflicts at once
                    ok = True
                    break
                if v == 0:
                    assign(-l)
                    stack.append(-l)
            if not ok:
                ok = propagate(stack)
            for l in trail[mark:]:
                val[l if l > 0 else -l] = 0
            del trail[mark:]
            if not ok:
                return False
        add(lemma)
    return True


class _VarHeap:
    """The unassigned variables, a max-heap on activity, with positions, so
    that a decision and a bump are O(log n)."""

    def __init__(self, act, n):
        self.act = act
        self.h = list(range(1, n + 1))
        self.pos = [-1] + list(range(n))

    def __bool__(self):
        return bool(self.h)

    def _up(self, i):
        h, pos, act = self.h, self.pos, self.act
        v = h[i]
        a = act[v]
        while i:
            parent = (i - 1) >> 1
            pv = h[parent]
            if act[pv] >= a:
                break
            h[i] = pv
            pos[pv] = i
            i = parent
        h[i] = v
        pos[v] = i

    def _down(self, i):
        h, pos, act = self.h, self.pos, self.act
        n, v = len(h), h[i]
        a = act[v]
        while True:
            c = 2 * i + 1
            if c >= n:
                break
            if c + 1 < n and act[h[c + 1]] > act[h[c]]:
                c += 1
            if act[h[c]] <= a:
                break
            h[i] = h[c]
            pos[h[i]] = i
            i = c
        h[i] = v
        pos[v] = i

    def push(self, v):
        if self.pos[v] < 0:
            self.h.append(v)
            self.pos[v] = len(self.h) - 1
            self._up(len(self.h) - 1)

    def pop(self):
        h = self.h
        v = h[0]
        last = h.pop()
        self.pos[v] = -1
        if h:
            h[0] = last
            self.pos[last] = 0
            self._down(0)
        return v

    def bumped(self, v):
        if self.pos[v] >= 0:
            self._up(self.pos[v])


class _CDCL:
    """A conflict-driven clause-learning SAT solver that logs every clause it
    learns, so that an answer of unsatisfiable is a RUP proof: two watched
    literals, first-UIP learning with minimization, activity-ordered
    decisions with phase saving, Luby restarts. Its answers are checked, not
    trusted."""

    def __init__(self, nv, clauses):
        self.nv = nv
        self.clauses = []
        self.watch = {}
        self.val = [0] * (nv + 1)        # +1 true, -1 false, 0 unassigned
        self.level = [0] * (nv + 1)
        self.reason = [None] * (nv + 1)
        self.trail = []
        self.lim = []                    # trail length at each decision
        self.activity = [0.0] * (nv + 1)
        self.heap = _VarHeap(self.activity, nv)
        self.phase = [False] * (nv + 1)
        self.inc = 1.0
        self.proof = []
        self.qhead = 0
        self.empty = False
        self.units = []
        for c in clauses:
            c = sorted(set(c), key=abs)
            if any(-l in c for l in c):
                continue
            if not c:
                self.empty = True
            elif len(c) == 1:
                self.units.append(c[0])
            else:
                self._attach(c)

    def _attach(self, c):
        i = len(self.clauses)
        self.clauses.append(c)
        self.watch.setdefault(c[0], []).append(i)
        self.watch.setdefault(c[1], []).append(i)
        return i

    def _value(self, l):
        v = self.val[abs(l)]
        return v if l > 0 else -v

    def _enqueue(self, l, reason):
        v = abs(l)
        self.val[v] = 1 if l > 0 else -1
        self.level[v] = len(self.lim)
        self.reason[v] = reason
        self.trail.append(l)

    def _propagate(self):
        """Unit propagation: the index of a conflicting clause, or None.
        Each clause watches its first two literals; a clause is visited when
        one of them becomes false, and either finds another literal to watch
        or is unit (or conflicting) in the other."""
        val, clauses, watch, trail = self.val, self.clauses, self.watch, self.trail
        level, reason = self.level, self.reason
        while self.qhead < len(trail):
            false_lit = -trail[self.qhead]
            self.qhead += 1
            ws = watch.get(false_lit)
            if not ws:
                continue
            keep, k, n = [], 0, len(ws)
            while k < n:
                i = ws[k]
                k += 1
                c = clauses[i]
                if c[0] == false_lit:
                    c[0] = c[1]
                    c[1] = false_lit
                first = c[0]
                fv = val[first] if first > 0 else -val[-first]
                if fv == 1:
                    keep.append(i)
                    continue
                for j in range(2, len(c)):
                    x = c[j]
                    if (val[x] if x > 0 else -val[-x]) != -1:
                        c[1] = x
                        c[j] = false_lit
                        lst = watch.get(x)
                        if lst is None:
                            watch[x] = [i]
                        else:
                            lst.append(i)
                        break
                else:
                    keep.append(i)
                    if fv == -1:
                        keep.extend(ws[k:])
                        watch[false_lit] = keep
                        return i
                    v = first if first > 0 else -first
                    val[v] = 1 if first > 0 else -1
                    level[v] = len(self.lim)
                    reason[v] = i
                    trail.append(first)
            watch[false_lit] = keep
        return None

    def _analyze(self, ci):
        """The first-UIP clause of the conflict, minimized, and the level to
        go back to. Its literals are all false now; the first is the one at
        this level."""
        seen, rest, counter = set(), [], 0
        lvl = len(self.lim)
        c, idx, p = self.clauses[ci], len(self.trail) - 1, None
        while True:
            for q in c:
                v = abs(q)
                if q == p or v in seen or self.level[v] == 0:
                    continue
                seen.add(v)
                self._bump(v)
                if self.level[v] == lvl:
                    counter += 1
                else:
                    rest.append(q)
            while abs(self.trail[idx]) not in seen:
                idx -= 1
            p = self.trail[idx]
            idx -= 1
            seen.discard(abs(p))
            counter -= 1
            if counter == 0:
                break
            c = self.clauses[self.reason[abs(p)]]
        # A literal whose reason's other literals are all in the clause or
        # at level 0 follows from them: drop it. What is left is still RUP.
        kept = []
        for q in rest:
            r = self.reason[abs(q)]
            if r is None or any(x != -q and abs(x) not in seen and self.level[abs(x)]
                                for x in self.clauses[r]):
                kept.append(q)
        learned = [-p] + kept
        back = 0
        if kept:
            j = max(range(1, len(learned)), key=lambda t: self.level[abs(learned[t])])
            learned[1], learned[j] = learned[j], learned[1]
            back = self.level[abs(learned[1])]
        self.inc *= 1.05
        return learned, back

    def _bump(self, v):
        self.activity[v] += self.inc
        if self.activity[v] > 1e100:
            for i in range(len(self.activity)):
                self.activity[i] *= 1e-100
            self.inc *= 1e-100
        self.heap.bumped(v)

    def _backtrack(self, lvl):
        if len(self.lim) <= lvl:
            return
        cut = self.lim[lvl]
        for l in self.trail[cut:]:
            v = abs(l)
            self.phase[v] = l > 0
            self.val[v] = 0
            self.reason[v] = None
            self.heap.push(v)
        del self.trail[cut:]
        del self.lim[lvl:]
        self.qhead = len(self.trail)

    def _pick(self):
        while self.heap:
            v = self.heap.pop()
            if self.val[v] == 0:
                return v
        return 0

    @staticmethod
    def _luby(i):
        """The i-th term (from 1) of 1, 1, 2, 1, 1, 2, 4, 1, ..."""
        while True:
            k = i.bit_length()
            if i == (1 << k) - 1:
                return 1 << (k - 1)
            i -= (1 << (k - 1)) - 1

    def solve(self, max_conflicts=MAX_CONFLICTS):
        """(True, model), model[v] a bool for every variable; (False, proof);
        or (None, None) after max_conflicts conflicts."""
        if self.empty:
            self.proof.append([])
            return False, self.proof
        for u in self.units:
            x = self._value(u)
            if x == -1:
                self.proof.append([])
                return False, self.proof
            if x == 0:
                self._enqueue(u, None)
        restarts, since, total = 1, 0, 0
        budget = 100 * self._luby(restarts)
        while True:
            ci = self._propagate()
            if ci is not None:
                if not self.lim:
                    self.proof.append([])
                    return False, self.proof
                total += 1
                since += 1
                if total > max_conflicts:
                    return None, None
                learned, back = self._analyze(ci)
                self.proof.append(list(learned))
                self._backtrack(back)
                if len(learned) == 1:
                    self._enqueue(learned[0], None)
                else:
                    self._enqueue(learned[0], self._attach(learned))
                continue
            if since >= budget:
                restarts += 1
                since = 0
                budget = 100 * self._luby(restarts)
                self._backtrack(0)
                continue
            v = self._pick()
            if v == 0:
                return True, [None] + [self.val[i] == 1 for i in range(1, self.nv + 1)]
            self.lim.append(len(self.trail))
            self._enqueue(v if self.phase[v] else -v, None)


# ---- an independent check for small formulas --------------------------------

def brute_force(f, max_slots=16):
    """f's truth by trying every choice of Skolem functions on every
    assignment of all the universals: independent of both decision
    procedures, for tests and the self-suite. Only for tiny formulas: the
    choices number 2^(sum over x of 2^|D_x|)."""
    deps = {x: f.deps(x) for x in f.order}
    slots = [(x, tau) for x in f.order
             for tau in itertools.product((0, 1), repeat=len(deps[x]))]
    if len(slots) > max_slots or len(f.universals) > max_slots:
        raise DQBFError("too large to enumerate")
    sigmas = [dict(zip(f.universals, bits))
              for bits in itertools.product((0, 1), repeat=len(f.universals))]
    for bits in itertools.product((0, 1), repeat=len(slots)):
        table = dict(zip(slots, bits))
        if all(_holds(f, s, table, deps) for s in sigmas):
            return True
    return False


def _holds(f, sigma, table, deps):
    val = dict(sigma)
    for x in f.order:
        val[x] = table[(x, tuple(sigma[u] for u in deps[x]))]
    return (all(sum(val[v] for v in names) % 2 == p for names, p in f.xors)
            and all(any(val[v] == pos for v, pos in lits) for lits in f.clauses))


# ---- the Phase 4b module format ---------------------------------------------

_ATTRS = {"module": {"name"}, "vars": set(), "constraints": set(),
          "forall": {"vars"}, "exists": {"vars", "deps"},
          "xor": {"id", "parity"}, "or": {"id"}}
_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*\Z")


def parse_module(text):
    """A DQBF module in the Phase 4b XML format, parsed strictly: (name,
    DQBF). Anything the format does not define is a DQBFError, among them an
    unknown element or attribute, an <exists> without deps (deps="" for
    none), an undeclared variable, a dependency on a variable that is not
    universal, a parity other than 0 or 1, and a DOCTYPE."""
    import xml.etree.ElementTree as ET
    if re.search(r"<!\s*(DOCTYPE|ENTITY)", text, re.I):
        raise DQBFError("a DOCTYPE or ENTITY declaration is not allowed")
    try:
        root = ET.fromstring(text)
    except ET.ParseError as e:
        raise DQBFError(f"not well-formed XML: {e}") from None

    def check(el, children):
        extra = set(el.attrib) - _ATTRS.get(el.tag, set())
        if extra:
            raise DQBFError(f"<{el.tag}> has unknown attribute "
                            f"{', '.join(sorted(extra))}")
        if not children and len(el):
            raise DQBFError(f"<{el.tag}> has child elements")
        if children and (el.text or "").strip():
            raise DQBFError(f"text {el.text.strip()!r} in <{el.tag}>")
        for c in el:
            if (c.tail or "").strip():
                raise DQBFError(f"text {c.tail.strip()!r} after <{c.tag}>")

    def names(el, attr):
        out = el.get(attr, "").split()
        for n in out:
            if not _NAME.match(n):
                raise DQBFError(f"{n!r} is not a variable name")
        return out

    if root.tag != "module":
        raise DQBFError(f"the root element is <{root.tag}>, not <module>")
    check(root, True)
    name = root.get("name", "")
    if not name:
        raise DQBFError("<module> has no name")
    f, seen, ids = DQBF(), [], set()
    for part in root:
        if part.tag not in ("vars", "constraints") or part.tag in seen:
            raise DQBFError(f"unexpected <{part.tag}> in <module>")
        if part.tag == "constraints" and "vars" not in seen:
            raise DQBFError("<constraints> before <vars>")
        seen.append(part.tag)
        check(part, True)
        allowed = ("forall", "exists") if part.tag == "vars" else ("xor", "or")
        for el in part:
            if el.tag not in allowed:
                raise DQBFError(f"unexpected <{el.tag}> in <{part.tag}>")
            check(el, False)
            if el.tag in ("forall", "exists"):
                if (el.text or "").strip():
                    raise DQBFError(f"text {el.text.strip()!r} in <{el.tag}>")
                vs = names(el, "vars")
                if not vs:
                    raise DQBFError(f"<{el.tag}> declares no variables")
                if el.tag == "forall":
                    f.forall(*vs)
                    continue
                if "deps" not in el.attrib:
                    raise DQBFError(f"<exists vars=\"{' '.join(vs)}\"> has no deps "
                                    f"(deps=\"\" for none)")
                for v in vs:
                    f.exists(v, names(el, "deps"))
                continue
            cid = el.get("id")
            if cid is not None:
                if cid in ids:
                    raise DQBFError(f"constraint id {cid!r} is used twice")
                ids.add(cid)
            toks = (el.text or "").split()
            if not toks:
                raise DQBFError(f"<{el.tag}> has no variables")
            if el.tag == "xor":
                parity = el.get("parity")
                if parity not in ("0", "1"):
                    raise DQBFError(f"<xor> parity {parity!r} is not 0 or 1")
                f.xor(toks, int(parity))
            else:
                lits = []
                for t in toks:
                    v = t[1:] if t.startswith("!") else t
                    if not _NAME.match(v):
                        raise DQBFError(f"{t!r} is not a literal")
                    lits.append((v, not t.startswith("!")))
                f.clause(lits)
    if "vars" not in seen:
        raise DQBFError("<module> has no <vars>")
    return name, f
