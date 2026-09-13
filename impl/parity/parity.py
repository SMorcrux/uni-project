#!/usr/bin/env python3
"""
Usage:
    python3 parity.py PROGRAM.txt [--domain disjunctive|pointwise] [--quiet] [--no-invariants]

Comments (lines starting with # or //) are ignored

The program parses the text into a CFG (class Program),
then walks along the graph and analyzes the program.
Since the ATF is monotonic and there's finitely many states, it must terminate. 

Exit code: 0 if every assertion is verified, 1 if some assertion may be violated, 2 on usage error.
"""
import sys
import re
import itertools
from collections import defaultdict, deque

# ---------------------------------------------------------------------------
#  Base partition and helper arithmetic
# ---------------------------------------------------------------------------
Z, E, O = 'Z', 'E', 'O'
B = (Z, E, O)                       # fixed order used for tuples/pretty printing
BSET = frozenset(B)

def beta(k):
    """Abstraction of a concrete natural number."""
    if k == 0:
        return Z
    return E if k % 2 == 0 else O

SUCC = {Z: (O,), E: (O,), O: (E,)}          # abstraction of  n + 1
PRED = {Z: (Z,), E: (O,), O: (Z, E)}        # abstraction of  n - 1  (0 - 1 = 0)

def is_even(b):
    return b in (Z, E)

def is_odd(b):
    return b == O

# ---------------------------------------------------------------------------
#  Program representation / parsing
# ---------------------------------------------------------------------------
TOKEN_RE = re.compile(r':=|!=|=|\(|\)|\?|\+|-|[A-Za-z0-9_]+')

class Edge:
    __slots__ = ('src', 'cmd', 'dst', 'text', 'line')
    def __init__(self, src, cmd, dst, text, line):
        self.src, self.cmd, self.dst, self.text, self.line = src, cmd, dst, text, line

class Program:
    def __init__(self, variables, edges):
        self.vars = variables
        self.edges = edges
        self.nodes = []
        seen = set()
        for e in edges:
            for n in (e.src, e.dst):
                if n not in seen:
                    seen.add(n)
                    self.nodes.append(n)
        incoming = {n: 0 for n in self.nodes}
        for e in edges:
            incoming[e.dst] += 1
        # The entry node is the source of the first edge in the file (this coincides with the
        # unique node without incoming edges when simplifying assumption 1 holds, and is the
        # natural choice when the entry is also a loop head).
        self.entry = edges[0].src
        self.dangling = [n for n in self.nodes if incoming[n] == 0 and n != self.entry]
        self.succs = defaultdict(list)
        for e in edges:
            self.succs[e.src].append(e)

def parse_command(tokens, variables, text):
    """Return a tuple describing the command."""
    t = tokens
    if t == ['skip']:
        return ('skip',)
    if len(t) >= 3 and t[1] == ':=':
        x = t[0]
        rhs = t[2:]
        if x not in variables:
            raise SyntaxError("unknown variable %r in %r" % (x, text))
        if rhs == ['?']:
            return ('havoc', x)
        if len(rhs) == 1:
            if rhs[0].isdigit():
                return ('const', x, int(rhs[0]))
            if rhs[0] in variables:
                return ('copy', x, rhs[0])
        if len(rhs) == 3 and rhs[0] in variables and rhs[1] in '+-' and rhs[2] == '1':
            return ('inc' if rhs[1] == '+' else 'dec', x, rhs[0])
        raise SyntaxError("cannot parse assignment %r" % text)
    if t[0] == 'assume':
        e = [tok for tok in t[1:] if tok not in '()']
        if e == ['TRUE']:
            return ('assume', ('true',))
        if e == ['FALSE']:
            return ('assume', ('false',))
        if len(e) == 3 and e[0] in variables and e[1] in ('=', '!='):
            if e[2].isdigit():
                return ('assume', ('cmpk', e[1] == '=', e[0], int(e[2])))
            if e[2] in variables:
                return ('assume', ('cmpv', e[1] == '=', e[0], e[2]))
        raise SyntaxError("cannot parse assume %r" % text)
    if t[0] == 'assert':
        # sequence of parenthesised conjunctions of atomic predicates
        disj, cur, depth = [], None, 0
        for tok in t[1:]:
            if tok == '(':
                depth += 1
                cur = []
            elif tok == ')':
                depth -= 1
                if cur is None:
                    raise SyntaxError("unbalanced parentheses in %r" % text)
                disj.append(tuple(cur))
                cur = None
            else:
                if cur is None:
                    raise SyntaxError("atomic predicate outside parentheses in %r" % text)
                cur.append(tok)
        if depth != 0 or cur is not None:
            raise SyntaxError("unbalanced parentheses in %r" % text)
        conjs = []
        for c in disj:
            atoms = []
            if len(c) % 2 != 0:
                raise SyntaxError("cannot parse assertion %r" % text)
            for i in range(0, len(c), 2):
                if c[i] not in ('EVEN', 'ODD') or c[i + 1] not in variables:
                    raise SyntaxError("bad atomic predicate %r in %r" % (c[i:i + 2], text))
                atoms.append((c[i], c[i + 1]))
            conjs.append(tuple(atoms))
        return ('assert', tuple(conjs))
    raise SyntaxError("cannot parse command %r" % text)

def parse_program(src):
    lines = [l.strip() for l in src.splitlines()]
    lines = [(i + 1, l) for i, l in enumerate(lines) if l and not l.startswith('#') and not l.startswith('//')]
    if not lines:
        raise SyntaxError("empty program")
    variables = lines[0][1].split()
    edges = []
    for lineno, l in lines[1:]:
        toks = TOKEN_RE.findall(l)
        if len(toks) < 3:
            raise SyntaxError("line %d: cannot parse edge %r" % (lineno, l))
        src_l, dst_l, cmd_toks = toks[0], toks[-1], toks[1:-1]
        cmd = parse_command(cmd_toks, variables, l)
        edges.append(Edge(src_l, cmd, dst_l, l, lineno))
    return Program(variables, edges)

# ---------------------------------------------------------------------------
#  Abstract domains.  An element of the disjunctive domain is a frozenset of
#  tuples over B (one entry per program variable, in declaration order).
#  An element of the pointwise domain is a tuple of frozensets over B.
# ---------------------------------------------------------------------------
class DisjunctiveDomain:
    """P(Var -> B): sets of 'parity vectors'.  Join = union, bottom = empty set."""
    name = 'disjunctive'

    def __init__(self, variables):
        self.vars = variables
        self.idx = {v: i for i, v in enumerate(variables)}

    def top(self):
        return frozenset(itertools.product(B, repeat=len(self.vars)))

    def bottom(self):
        return frozenset()

    def join(self, a, b):
        return a | b

    def leq(self, a, b):
        return a <= b

    def is_bottom(self, a):
        return not a

    # --- transfer functions -------------------------------------------------
    def transfer(self, cmd, s):
        """Returns (new_state, list_of_warnings)."""
        kind = cmd[0]
        if kind == 'skip':
            return s, []
        if kind == 'havoc':
            i = self.idx[cmd[1]]
            return frozenset(t[:i] + (b,) + t[i + 1:] for t in s for b in B), []
        if kind == 'const':
            i, b = self.idx[cmd[1]], beta(cmd[2])
            return frozenset(t[:i] + (b,) + t[i + 1:] for t in s), []
        if kind == 'copy':
            i, j = self.idx[cmd[1]], self.idx[cmd[2]]
            return frozenset(t[:i] + (t[j],) + t[i + 1:] for t in s), []
        if kind in ('inc', 'dec'):
            i, j = self.idx[cmd[1]], self.idx[cmd[2]]
            f = SUCC if kind == 'inc' else PRED
            return frozenset(t[:i] + (b,) + t[i + 1:] for t in s for b in f[t[j]]), []
        if kind == 'assume':
            return frozenset(t for t in s if self.sat_expr(cmd[1], t)), []
        if kind == 'assert':
            bad = [t for t in s if not self.sat_assert(cmd[1], t)]
            good = frozenset(t for t in s if self.sat_assert(cmd[1], t))
            warnings = []
            if bad:
                warnings.append("assertion may be violated; counter-example parity vectors: "
                                + ", ".join(self.fmt_tuple(t) for t in sorted(bad)[:4])
                                + (" ..." if len(bad) > 4 else ""))
            # Assertions are checked but not used as assumptions, so that a failing
            # assertion never masks a later one (this is sound: s is a superset of good).
            return s, warnings
        raise ValueError(kind)

    def sat_expr(self, e, t):
        """Does the abstract vector t possibly satisfy boolean expression e?  (must be
        an over-approximation: keep t whenever some concrete state in gamma(t) satisfies e)"""
        k = e[0]
        if k == 'true':
            return True
        if k == 'false':
            return False
        if k == 'cmpk':
            _, eq, x, K = e
            bx, bk = t[self.idx[x]], beta(K)
            if eq:
                return bx == bk           # x = K  possible iff same class
            # x != K : impossible only when both are the singleton class {0}
            return not (bx == Z and bk == Z)
        if k == 'cmpv':
            _, eq, x, y = e
            bx, by = t[self.idx[x]], t[self.idx[y]]
            if eq:
                return bx == by
            return not (bx == Z and by == Z)
        raise ValueError(k)

    def sat_assert(self, conjs, t):
        for conj in conjs:
            ok = True
            for (p, x) in conj:
                b = t[self.idx[x]]
                if (p == 'EVEN' and not is_even(b)) or (p == 'ODD' and not is_odd(b)):
                    ok = False
                    break
            if ok:
                return True
        return False

    # --- pretty printing ------------------------------------------------------
    def fmt_tuple(self, t):
        return "(" + ", ".join("%s:%s" % (v, b) for v, b in zip(self.vars, t)) + ")"

    def fmt(self, s):
        if not s:
            return "BOTTOM (unreachable)"
        n = len(s)
        # also print a pointwise summary, which is easier to read
        summary = []
        for i, v in enumerate(self.vars):
            cls = sorted({t[i] for t in s}, key=B.index)
            summary.append("%s in {%s}" % (v, ",".join(cls)))
        if n == 3 ** len(self.vars):
            return "TOP (%d vectors)" % n
        body = "{" + ", ".join(self.fmt_tuple(t) for t in sorted(s)) + "}" if n <= 12 else "(%d vectors)" % n
        return "%s   pointwise: %s" % (body, "; ".join(summary))


class PointwiseDomain(DisjunctiveDomain):
    """Var -> P(B): the non-relational product lattice.  Transfer functions are the best
    transformers of this domain, computed by (i) concretising an element to the set of
    vectors it denotes, (ii) applying the exact disjunctive transformer, (iii) re-abstracting
    (projecting each variable).  This is exactly alpha o f o gamma."""
    name = 'pointwise'

    def top(self):
        return tuple(BSET for _ in self.vars)

    def bottom(self):
        return tuple(frozenset() for _ in self.vars)

    def join(self, a, b):
        return tuple(x | y for x, y in zip(a, b))

    def leq(self, a, b):
        return all(x <= y for x, y in zip(a, b))

    def is_bottom(self, a):
        return any(not x for x in a)

    def expand(self, a):
        if self.is_bottom(a):
            return frozenset()
        return frozenset(itertools.product(*a))

    def collapse(self, s):
        if not s:
            return self.bottom()
        return tuple(frozenset(t[i] for t in s) for i in range(len(self.vars)))

    def transfer(self, cmd, a):
        s, w = DisjunctiveDomain.transfer(self, cmd, self.expand(a))
        return self.collapse(s), w

    def fmt(self, a):
        if self.is_bottom(a):
            return "BOTTOM (unreachable)"
        return "; ".join("%s in {%s}" % (v, ",".join(sorted(c, key=B.index))) for v, c in zip(self.vars, a))

# ---------------------------------------------------------------------------
#  Chaotic iteration
# ---------------------------------------------------------------------------
def analyze(prog, dom):
    state = {n: dom.bottom() for n in prog.nodes}
    state[prog.entry] = dom.top()          # variables hold arbitrary naturals initially
    work = deque([prog.entry])
    inwork = {prog.entry}
    iterations = 0
    while work:
        n = work.popleft()
        inwork.discard(n)
        for e in prog.succs[n]:
            iterations += 1
            new, _ = dom.transfer(e.cmd, state[n])
            joined = dom.join(state[e.dst], new)
            if not dom.leq(joined, state[e.dst]):
                state[e.dst] = joined
                if e.dst not in inwork:
                    inwork.add(e.dst)
                    work.append(e.dst)
    # final pass: collect warnings at the fixpoint
    warnings = []
    for e in prog.edges:
        _, w = dom.transfer(e.cmd, state[e.src])
        for msg in w:
            warnings.append((e, msg))
    return state, warnings, iterations

def main(argv):
    args = [a for a in argv if not a.startswith('--')]
    opts = [a for a in argv if a.startswith('--')]
    if len(args) != 1:
        print(__doc__)
        return 2
    domain_name = 'disjunctive'
    for o in opts:
        if o.startswith('--domain='):
            domain_name = o.split('=', 1)[1]
        elif o not in ('--quiet', '--no-invariants'):
            print("unknown option", o)
            return 2
    quiet = '--quiet' in opts
    show_inv = '--no-invariants' not in opts and not quiet
    with open(args[0]) as f:
        prog = parse_program(f.read())
    for n in prog.dangling:
        print("WARNING: node %s has no incoming edges and is not the entry node %s; "
              "the edges leaving it are unreachable (typo in a label?)" % (n, prog.entry))
    if domain_name == 'disjunctive':
        dom = DisjunctiveDomain(prog.vars)
    elif domain_name == 'pointwise':
        dom = PointwiseDomain(prog.vars)
    else:
        print("unknown domain", domain_name)
        return 2
    state, warnings, iterations = analyze(prog, dom)
    print("Parity analysis of %s  (domain: %s, %d variables, %d nodes, %d edges, entry %s)" %
          (args[0], dom.name, len(prog.vars), len(prog.nodes), len(prog.edges), prog.entry))
    if show_inv:
        print("\nInvariants at the fixpoint (%d edge evaluations):" % iterations)
        for n in prog.nodes:
            print("  %-6s %s" % (n + ':', dom.fmt(state[n])))
    print()
    if warnings:
        for e, msg in warnings:
            print("WARNING line %d [%s %s %s]: %s" % (e.line, e.src, ' '.join(e.text.split()[1:-1]), e.dst, msg))
        print("\nRESULT: %d assertion(s) could NOT be verified." % len(warnings))
        return 1
    n_assert = sum(1 for e in prog.edges if e.cmd[0] == 'assert')
    vacuous = sum(1 for e in prog.edges if e.cmd[0] == 'assert' and dom.is_bottom(state[e.src]))
    if vacuous:
        print("NOTE: %d assertion(s) lie on unreachable edges and hold vacuously." % vacuous)
    print("RESULT: VERIFIED - all %d assertion(s) hold on every execution." % n_assert)
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
