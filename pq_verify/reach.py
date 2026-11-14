"""
pq_verify.reach -- static call-graph reachability over a compiled library.

This refines ct_audit's integer-division listing. That listing names every
function of the library that contains an integer division (an instruction, or
a call to a division routine), because division latency is operand-dependent
on many cores -- KyberSlash was a division on a secret polynomial, reachable
from Decaps. But the listing is flat: a division in key generation, or in
dead code, is listed exactly like one on the secret path. This module asks the
narrower question a timing reviewer actually has: of those functions, which are
reachable from the audited secret-input entry points (Encaps and Decaps for a
KEM, Sign for a signature)?

The call graph is read from `objdump -d`'s own symbol annotations: every call
or branch whose target the disassembler names -- a direct call, a PLT stub, a
tail jump -- is an edge. What it cannot name, a call through a register (a
function pointer, a C++ vtable, a PLT slot resolved at run time), is no edge.
So the reachable set is a LOWER BOUND: a division reported reachable really is
reachable, but one reported "not reached" may still be reached through a
pointer at run time. The caller is told whether the reachable code contains any
such unresolved call, so "not reached" is never read as "cannot happen". This
is a review pointer, not a verdict -- memcheck cannot see instruction timing,
and a division on public data is harmless even when it is on the secret path.

Nothing is executed; objdump only disassembles. The arch-specific mnemonics
mirror ct_audit.DIVISION_INSNS (x86, x86-64, ARM, AArch64, RISC-V).
"""
import re

# Mnemonics that transfer control out of a function: calls, and branches
# (including an unconditional tail `jmp`/`b` to another symbol). A conditional
# branch almost always targets a label inside the same function and is dropped
# by the self-edge test below, so sweeping them all in costs nothing and keeps
# the rare conditional tail-call as a real edge. Keyed by ELF machine number.
_EDGE = {
    3:   re.compile(r"call|callq|jmpq?|j[a-z]+"),            # x86
    62:  re.compile(r"call|callq|jmpq?|j[a-z]+"),            # x86-64
    183: re.compile(r"bl?|b\.[a-z]+|c?bn?z|tbn?z|br|blr"),  # AArch64
    40:  re.compile(r"bl?x?|b[a-z]{2}"),                    # ARM
    243: re.compile(r"jal?|jalr|call|tail|b[a-z]*z?"),      # RISC-V
}
# Of those, the ones that are calls. A call mnemonic with no named target is a
# call through a pointer the disassembler could not resolve -- the reason a
# reachable set built from named edges is only a lower bound. `bl`/`jal` always
# name their target, so they never count here; `blr`/`jalr`/`call *reg` do.
_CALL = {
    3:   re.compile(r"call|callq"),
    62:  re.compile(r"call|callq"),
    183: re.compile(r"bl|blr"),
    40:  re.compile(r"bl|blx|bx"),
    243: re.compile(r"jal|jalr|call|tail"),
}

_HEADER = re.compile(r"^[0-9a-f]+ <(?P<name>.+)>:$")
_INSN = re.compile(r"^\s+[0-9a-f]+:\s+(?P<mnem>[a-z][a-z0-9.]*)\s*(?P<rest>.*)$")
_TARGET = re.compile(r"<(?P<sym>[^>]+)>")


def _normalize(sym):
    """A call target or function header as a graph node: drop objdump's `@plt`
    stub marker and any `+0xNN`/`-0xNN` offset, so `call <foo@plt>`,
    `<foo+0x4>` and the function `<foo>` are the one node `foo`. A compiler
    clone suffix (`foo.constprop.0`) is part of the symbol and is kept, so the
    node matches ct_audit's division listing, which keys on the same name."""
    sym = sym.split("@", 1)[0]
    sym = re.split(r"[+-]0x", sym, maxsplit=1)[0]
    return sym


def call_graph(disassembly, machine):
    """({caller: {callee, ...}}, {caller: indirect_call_count}) from objdump -d
    text. Edges are named direct calls and tail branches; the second dict
    counts the calls through a register that could not be named."""
    edge_mn, call_mn = _EDGE.get(machine), _CALL.get(machine)
    if edge_mn is None:
        return {}, {}
    edges, indirect = {}, {}
    fn = None
    for line in disassembly.splitlines():
        h = _HEADER.match(line)
        if h:
            fn = _normalize(h.group("name"))
            edges.setdefault(fn, set())
            continue
        if fn is None:
            continue
        m = _INSN.match(line)
        if not m:
            continue
        mnem, rest = m.group("mnem"), m.group("rest")
        if not edge_mn.fullmatch(mnem):
            continue
        # objdump writes the target before any `#` comment; a rip-relative or
        # GOT load carries an unrelated `<...>` in that comment, so read only
        # the part before it. An x86 indirect operand begins with `*`.
        pre = rest.split("#", 1)[0]
        if "*" in pre:
            if call_mn and call_mn.fullmatch(mnem):
                indirect[fn] = indirect.get(fn, 0) + 1
            continue
        t = _TARGET.search(pre)
        if t:
            tgt = _normalize(t.group("sym"))
            if tgt and tgt != fn:
                edges[fn].add(tgt)
        elif call_mn and call_mn.fullmatch(mnem):
            # a call whose target objdump did not name: a register target.
            indirect[fn] = indirect.get(fn, 0) + 1
    return edges, indirect


def reachable(edges, roots):
    """The set of functions reachable from `roots` over `edges`, roots
    included. A root absent from `edges` (no body in this library) seeds
    nothing and is the caller's to notice."""
    seen, stack = set(), []
    for r in roots:
        if r in edges and r not in seen:
            seen.add(r)
            stack.append(r)
    while stack:
        for g in edges.get(stack.pop(), ()):
            if g not in seen:
                seen.add(g)
                stack.append(g)
    return seen


def classify(disassembly, machine, entries, divisions):
    """Split the division listing by reachability from the secret-input entry
    points. Returns None when it cannot be computed (no listing, no entries, an
    architecture whose call mnemonics are unknown). Otherwise:

        reachable_divisions  {function: count} -- the subset of `divisions`
                             reachable from `entries` through named calls
        entries              the entry symbols found with a body in the library
        entries_missing      entry symbols with no body (reachability from them
                             is unknown, so the result is a lower bound)
        reached_functions    size of the reachable set, for context
        indirect_calls       calls through a pointer inside reachable code, the
                             reason "not reached" is not "cannot be reached"
        complete             True only when every entry was found and the
                             reachable code makes no unresolved indirect call;
                             then "not reached" is exact for this binary
    """
    if divisions is None or not entries or machine not in _EDGE:
        return None
    edges, indirect = call_graph(disassembly, machine)
    norm = [_normalize(e) for e in entries]
    present = [e for e in norm if e in edges]
    missing = [e for e, n in zip(entries, norm) if n not in edges]
    seen = reachable(edges, present)
    reached = {fn: c for fn, c in divisions.items() if _normalize(fn) in seen}
    ind = sum(n for fn, n in indirect.items() if fn in seen)
    return {
        "reachable_divisions": reached,
        "entries": present,
        "entries_missing": missing,
        "reached_functions": len(seen),
        "indirect_calls": ind,
        "complete": not missing and ind == 0,
    }
