import sys
import re
import itertools
from collections import defaultdict, deque

# ---------------------------------------------------------------------------
#  Abstract lengths
# ---------------------------------------------------------------------------
L1, LO, LE = '1', 'O', 'E'          # 1 step / odd >= 3 steps / even >= 2 steps
ORDER = (L1, LO, LE)
ONE = frozenset([L1])
ADD_TABLE = {(L1, L1): LE, (L1, LO): LE, (L1, LE): LO,
             (LO, L1): LE, (LO, LO): LE, (LO, LE): LO,
             (LE, L1): LO, (LE, LO): LO, (LE, LE): LE}
MINUS_ONE = {LO: frozenset([LE]), LE: frozenset([L1, LO])}   # l - 1 for l in {O, E}
PARITY = {L1: 1, LO: 1, LE: 0}                               # parity of the number of steps

def ladd(a, b):
    return frozenset(ADD_TABLE[(x, y)] for x in a for y in b)

def lparity(a):
    """Parity (0/1) of the number of steps if determined by the label, else None."""
    ps = {PARITY[x] for x in a}
    return ps.pop() if len(ps) == 1 else None

def lfmt(a):
    return "|".join(x for x in ORDER if x in a)

# ---------------------------------------------------------------------------
#  Shape graphs
# ---------------------------------------------------------------------------
class MemoryError_(Exception):
    pass

class ShapeGraph:
    """Mutable working representation.  env: var -> node id or None.
    succ: node -> (node id or None, label).  gpred: set of node ids."""
    __slots__ = ('env', 'succ', 'gpred', 'fresh')

    def __init__(self, variables):
        self.env = {v: None for v in variables}
        self.succ = {}
        self.gpred = set()
        self.fresh = 0

    def copy(self):
        g = ShapeGraph.__new__(ShapeGraph)
        g.env = dict(self.env)
        g.succ = dict(self.succ)
        g.gpred = set(self.gpred)
        g.fresh = self.fresh
        return g

    def new_node(self, target=None, label=ONE):
        n = self.fresh
        self.fresh += 1
        self.succ[n] = (target, label)
        return n

    def vars_of(self, n):
        return sorted(v for v, m in self.env.items() if m == n)

    def pred_of(self, n):
        """The node whose summary edge targets n (at most one in a well-formed graph)."""
        for m, (t, _) in self.succ.items():
            if t == n:
                return m
        return None

    def reaches(self, a, b):
        """Is node b reachable from node a in >= 0 steps?"""
        while a is not None:
            if a == b:
                return True
            a = self.succ[a][0]
        return False

    def path_labels(self, a, b):
        """Labels of the edges on the path from a to b (a reaches b)."""
        out = []
        while a != b:
            t, l = self.succ[a]
            out.append(l)
            a = t
        return out

    # -- normalisation ------------------------------------------------------
    def normalize(self):
        """Remove nodes no variable points to: merge them into the summary edge of their
        predecessor, or (if they are garbage) drop them and mark their target."""
        changed = True
        while changed:
            changed = False
            for n in list(self.succ):
                if any(m == n for m in self.env.values()):
                    continue
                t, l = self.succ[n]
                p = self.pred_of(n)
                if p is not None:
                    pt, pl = self.succ[p]
                    self.succ[p] = (t, ladd(pl, l))
                else:
                    # n is unreachable; its (anonymous) chain still points to t
                    if t is not None:
                        self.gpred.add(t)
                del self.succ[n]
                self.gpred.discard(n)
                changed = True

    def set_var(self, x, target):
        self.env[x] = target
        self.normalize()

    # -- canonical form ------------------------------------------------------
    def key(self):
        name = {n: tuple(self.vars_of(n)) for n in self.succ}
        env = tuple(name[m] if m is not None else None for m in (self.env[v] for v in sorted(self.env)))
        edges = tuple(sorted((name[n], name[t] if t is not None else None, tuple(sorted(l)), n in self.gpred)
                             for n, (t, l) in self.succ.items()))
        return (env, edges)

    # -- printing -------------------------------------------------------------
    def fmt(self):
        heads = [n for n in self.succ if self.pred_of(n) is None]
        heads.sort(key=lambda n: self.vars_of(n))
        chains = []
        for h in heads:
            parts = []
            n = h
            while n is not None:
                lab = "{" + ",".join(self.vars_of(n)) + "}" + ("*" if n in self.gpred else "")
                parts.append(lab)
                t, l = self.succ[n]
                parts.append("-%s->" % lfmt(l))
                n = t
            parts.append("NULL")
            chains.append(" ".join(parts))
        nulls = sorted(v for v, m in self.env.items() if m is None)
        s = "; ".join(chains) if chains else "(empty heap)"
        if nulls:
            s += "   NULL: " + ",".join(nulls)
        return s

# ---------------------------------------------------------------------------
#  Atomic predicates, three-valued  (True / False / None = unknown)
# ---------------------------------------------------------------------------
def eval_atom(g, atom):
    k = atom[0]
    if k == 'true':
        return True
    if k == 'false':
        return False
    if k == 'isnull':            # x = NULL / x != NULL
        _, eq, x = atom
        return (g.env[x] is None) == eq
    if k == 'eqv':               # x = y / x != y
        _, eq, x, y = atom
        return (g.env[x] == g.env[y]) == eq
    if k == 'eqn':               # x = y.n / x != y.n
        _, eq, x, y = atom
        u = g.env[y]
        if u is None:
            raise MemoryError_("dereference of NULL pointer %s in predicate" % y)
        t, l = g.succ[u]
        if g.env[x] != t:
            r = False
        elif l == ONE:
            r = True
        elif L1 not in l:
            r = False
        else:
            return None
        return r == eq
    if k in ('ls', 'nols', 'odd', 'even'):
        _, x, y = atom
        a, b = g.env[x], g.env[y]
        ls = a is not None and b is not None and g.reaches(a, b)
        if k == 'ls':
            return ls
        if k == 'nols':
            return not ls
        if not ls:
            return False
        par = 0
        for l in g.path_labels(a, b):
            p = lparity(l)
            if p is None:
                return None
            par ^= p
        nodes_parity = (par + 1) % 2        # #nodes = #steps + 1
        return nodes_parity == (1 if k == 'odd' else 0)
    raise ValueError(k)

def and3(vals):
    if any(v is False for v in vals):
        return False
    if all(v is True for v in vals):
        return True
    return None

def or3(vals):
    if any(v is True for v in vals):
        return True
    if all(v is False for v in vals):
        return False
    return None

def eval_orc(g, conjs):
    return or3([and3([eval_atom(g, a) for a in conj]) for conj in conjs])

def split_labels(g):
    """All refinements of g in which every summary edge carries a singleton label."""
    nodes = list(g.succ)
    choices = [sorted(g.succ[n][1], key=ORDER.index) for n in nodes]
    for combo in itertools.product(*choices):
        h = g.copy()
        for n, c in zip(nodes, combo):
            h.succ[n] = (h.succ[n][0], frozenset([c]))
        yield h

def filter_graphs(g, conjs):
    """Split g into (graphs satisfying conjs, graphs violating conjs).  The truth value
    of every atomic predicate is definite in a graph with singleton labels, so the split
    loses no precision."""
    r = eval_orc(g, conjs)
    if r is True:
        return [g], []
    if r is False:
        return [], [g]
    good, bad = [], []
    for h in split_labels(g):
        (good if eval_orc(h, conjs) else bad).append(h)
    return good, bad

# ---------------------------------------------------------------------------
#  Transfer functions: graph -> (list of graphs, list of error messages)
# ---------------------------------------------------------------------------
def transfer(cmd, g):
    kind = cmd[0]
    if kind == 'skip':
        return [g], []
    if kind == 'null':
        h = g.copy(); h.set_var(cmd[1], None)
        return [h], []
    if kind == 'copy':
        h = g.copy(); h.set_var(cmd[1], g.env[cmd[2]])
        return [h], []
    if kind == 'new':
        h = g.copy()
        h.set_var(cmd[1], h.new_node(None, ONE))
        return [h], []
    if kind == 'load':                      # x := y.n
        x, y = cmd[1], cmd[2]
        u = g.env[y]
        if u is None:
            return [], ["NULL dereference: %s is NULL in '%s := %s.n'" % (y, x, y)]
        t, l = g.succ[u]
        out = []
        if L1 in l:                          # y.n is exactly t
            h = g.copy()
            h.succ[u] = (t, ONE)
            h.set_var(x, t)
            out.append(h)
        for c in (LO, LE):
            if c in l:                       # materialise the cell right after y
                h = g.copy()
                w = h.new_node(t, MINUS_ONE[c])
                h.succ[u] = (w, ONE)
                h.set_var(x, w)
                out.append(h)
        return out, []
    if kind == 'store':                     # x.n := y
        x, y = cmd[1], cmd[2]                # y is None for  x.n := NULL
        u = g.env[x]
        if u is None:
            return [], ["NULL dereference: %s is NULL in '%s.n := %s'" % (x, x, y or 'NULL')]
        t = g.env[y] if y is not None else None
        # (1) detach the old successor chain of u
        ot, ol = g.succ[u]
        detached = []
        if ot is None:
            h = g.copy(); h.succ[u] = (None, ONE); detached.append(h)
        else:
            if L1 in ol:                     # u.n was exactly ot: ot simply loses its predecessor
                h = g.copy(); h.succ[u] = (None, ONE); detached.append(h)
            if ol - ONE:                     # anonymous cells between u and ot become garbage, still pointing to ot
                h = g.copy(); h.succ[u] = (None, ONE); h.gpred.add(ot); detached.append(h)
        if t is None:
            return detached, []
        # (2) attach: check sharing and acyclicity, then add the edge
        out, errors = [], []
        for h in detached:
            if h.pred_of(t) is not None or t in h.gpred:
                errors.append("sharing: the cell pointed to by %s is already pointed to by an n-field ('%s.n := %s')" % (y, x, y))
                continue
            if h.reaches(t, u):
                errors.append("cycle: %s reaches %s, so '%s.n := %s' closes a cycle" % (y, x, x, y))
                continue
            h.succ[u] = (t, ONE)
            out.append(h)
        return out, errors
    if kind == 'assume':
        try:
            good, _ = filter_graphs(g, cmd[1])
        except MemoryError_ as e:
            return [], ["NULL dereference in assume: %s" % e]
        return good, []
    if kind == 'assert':
        try:
            good, bad = filter_graphs(g, cmd[1])
        except MemoryError_ as e:
            return [], ["NULL dereference in assert: %s" % e]
        errors = []
        if bad:
            errors.append("assertion may be violated, e.g. in state  " + bad[0].fmt())
        # Assertions are checked but deliberately not used as assumptions: every graph
        # (satisfying or not) flows on, so a failing assertion never masks a later one.
        return good + bad, errors
    raise ValueError(kind)

# ---------------------------------------------------------------------------
#  Parsing
# ---------------------------------------------------------------------------
TOKEN_RE = re.compile(r':=|!=|=|\(|\)|[A-Za-z0-9_]+(?:\.n)?')

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
                    seen.add(n); self.nodes.append(n)
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

def parse_atom(toks, variables, text):
    """b ::= x = NULL | x != NULL | x = y | x != y | x = y.n | x != y.n
            | LS x y | NOLS x y | ODD x y | EVEN x y | TRUE | FALSE"""
    if toks == ['TRUE']:
        return ('true',)
    if toks == ['FALSE']:
        return ('false',)
    if len(toks) == 3 and toks[0] in ('LS', 'NOLS', 'ODD', 'EVEN'):
        if toks[1] in variables and toks[2] in variables:
            return (toks[0].lower(), toks[1], toks[2])
    if len(toks) == 3 and toks[0] in variables and toks[1] in ('=', '!='):
        eq = toks[1] == '='
        r = toks[2]
        if r == 'NULL':
            return ('isnull', eq, toks[0])
        if r in variables:
            return ('eqv', eq, toks[0], r)
        if r.endswith('.n') and r[:-2] in variables:
            return ('eqn', eq, toks[0], r[:-2])
    raise SyntaxError("cannot parse predicate %r in %r" % (' '.join(toks), text))

def parse_command(t, variables, text):
    if t == ['skip']:
        return ('skip',)
    if len(t) == 3 and t[1] == ':=':
        lhs, rhs = t[0], t[2]
        if lhs in variables:
            if rhs == 'NULL':
                return ('null', lhs)
            if rhs == 'new':
                return ('new', lhs)
            if rhs in variables:
                return ('copy', lhs, rhs)
            if rhs.endswith('.n') and rhs[:-2] in variables:
                return ('load', lhs, rhs[:-2])
        if lhs.endswith('.n') and lhs[:-2] in variables:
            if rhs in variables:
                return ('store', lhs[:-2], rhs)
            if rhs == 'NULL':
                return ('store', lhs[:-2], None)
        raise SyntaxError("cannot parse assignment %r" % text)
    if t[0] == 'assume':
        e = [tok for tok in t[1:] if tok not in '()']
        return ('assume', ((parse_atom(e, variables, text),),))
    if t[0] == 'assert':
        disj, cur = [], None
        for tok in t[1:]:
            if tok == '(':
                if cur is not None:
                    raise SyntaxError("nested parentheses in %r" % text)
                cur = []
            elif tok == ')':
                if cur is None:
                    raise SyntaxError("unbalanced parentheses in %r" % text)
                disj.append(cur); cur = None
            else:
                if cur is None:
                    raise SyntaxError("atomic predicate outside parentheses in %r" % text)
                cur.append(tok)
        if cur is not None:
            raise SyntaxError("unbalanced parentheses in %r" % text)
        conjs = []
        for c in disj:
            atoms, i = [], 0
            while i < len(c):
                if c[i] in ('LS', 'NOLS', 'ODD', 'EVEN'):
                    atoms.append(parse_atom(c[i:i + 3], variables, text)); i += 3
                elif c[i] in ('TRUE', 'FALSE'):
                    atoms.append(parse_atom(c[i:i + 1], variables, text)); i += 1
                else:
                    atoms.append(parse_atom(c[i:i + 3], variables, text)); i += 3
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
        cmd = parse_command(toks[1:-1], variables, l)
        # 'x.n := NULL' is represented as a store of the NULL variable
        edges.append(Edge(toks[0], cmd, toks[-1], l, lineno))
    return Program(variables, edges)

# ---------------------------------------------------------------------------
#  Abstract state = set of canonical shape graphs (dict key -> graph)
# ---------------------------------------------------------------------------
def transfer_state(cmd, state):
    out, errors = {}, []
    for g in state.values():
        gs, errs = transfer(cmd, g)
        for h in gs:
            out.setdefault(h.key(), h)
        for msg in errs:
            if msg not in errors:
                errors.append(msg)
    if len(errors) > 1 and cmd[0] == 'assert':
        errors = [errors[0] + "   (%d violating shape graphs in total)" % len(errors)]
    return out, errors

def analyze(prog):
    init = ShapeGraph(prog.vars)             # all variables are NULL initially
    state = {n: {} for n in prog.nodes}
    state[prog.entry] = {init.key(): init}
    work = deque([prog.entry]); inwork = {prog.entry}
    evals = 0
    while work:
        n = work.popleft(); inwork.discard(n)
        for e in prog.succs[n]:
            evals += 1
            new, _ = transfer_state(e.cmd, state[n])
            dst = state[e.dst]
            changed = False
            for k, g in new.items():
                if k not in dst:
                    dst[k] = g; changed = True
            if changed and e.dst not in inwork:
                inwork.add(e.dst); work.append(e.dst)
    errors = []
    for e in prog.edges:
        _, errs = transfer_state(e.cmd, state[e.src])
        for msg in errs:
            errors.append((e, msg))
    return state, errors, evals

def fmt_state(st):
    if not st:
        return "BOTTOM (unreachable)"
    gs = sorted(st.values(), key=lambda g: g.fmt())
    if len(gs) == 1:
        return gs[0].fmt()
    return "%d graphs:\n" % len(gs) + "\n".join("            " + g.fmt() for g in gs)

def main(argv):
    if len(argv) != 1:
        print(__doc__); return 2
    
    with open(argv[0]) as f:
        prog = parse_program(f.read())
    for n in prog.dangling:
        print("WARNING: node %s has no incoming edges and is not the entry node %s; "
              "the edges leaving it are unreachable (typo in a label?)" % (n, prog.entry))
    
    state, errors, evals = analyze(prog)
    
    print("Shape analysis of %s  (%d variables, %d nodes, %d edges, entry %s)" %
          (argv[0], len(prog.vars), len(prog.nodes), len(prog.edges), prog.entry))
    
    total = sum(len(s) for s in state.values())
    print("\nInvariants at the fixpoint (%d edge evaluations, %d shape graphs in total)." % (evals, total))
    print("Notation: {vars}* marks a cell pointed to by the n-field of a garbage cell; "
          "-1-> one step, -O-> odd (>=3) steps, -E-> even (>=2) steps, -1|O-> one or odd steps.")
    for n in prog.nodes:
        print("  %-6s %s" % (n + ':', fmt_state(state[n])))
    print()
    
    if errors:
        for e, msg in errors:
            print("ERROR line %d [%s %s %s]: %s" % (e.line, e.src, ' '.join(e.text.split()[1:-1]), e.dst, msg))
        print("\nRESULT: %d problem(s) found." % len(errors))
        return 1
    
    n_assert = sum(1 for e in prog.edges if e.cmd[0] == 'assert')
    vacuous = sum(1 for e in prog.edges if e.cmd[0] == 'assert' and not state[e.src])
    if vacuous:
        print("NOTE: %d assertion(s) lie on unreachable edges and hold vacuously." % vacuous)
    print("RESULT: VERIFIED - memory safe, no cycles, no sharing, and all %d assertion(s) hold." % n_assert)
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))