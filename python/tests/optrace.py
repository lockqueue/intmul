"""AST-rewriting operation tracer (rewrite the operators, not the calls).

Every inline integer operator of the traced subnlogn modules -- ``* // % ** << >> + - & | ^``,
augmented assignments, and the calls ``divmod pow int str format Fraction`` -- is rewritten at import
time into a call of a recording wrapper that computes the same value and, whenever an int operand or
the int result exceeds 64 bits, records the site (module, enclosing function, line, operator), the
operand sizes and the multiplier-hierarchy stage active at that moment (``Hierarchy._run`` is wrapped
to maintain a stage stack).  A call/return trace cannot see inline operators; this one sees every
operator of the traced source.

Not traced (class D: table precomputation): the certified-table modules
(certified, certcore, rigorous), the network data package ``net`` (compile-time exact matrices) and the
instrumentation.  ``SOURCE_PATCHES`` (module -> [(old, new)]) lets a test inject a canary into the
traced copy without touching the repository.

Usage (a fresh interpreter): ``install(patches)`` BEFORE the first ``import subnlogn``; run the route;
``report()`` returns the JSON-able site table.  ``tests/optrace_run.py`` does exactly that.
"""

from __future__ import annotations

import ast
import builtins
import copy
import importlib.abc
import importlib.machinery
import operator
import sys
from fractions import Fraction

WORD = 64
SKIP = ("subnlogn.certified", "subnlogn.certcore", "subnlogn.rigorous", "subnlogn.net",
        "subnlogn.instrument")
BINOPS = {ast.Mult: ("*", operator.mul), ast.FloorDiv: ("//", operator.floordiv),
          ast.Mod: ("%", operator.mod), ast.Pow: ("**", operator.pow),
          ast.LShift: ("<<", operator.lshift), ast.RShift: (">>", operator.rshift),
          ast.Add: ("+", operator.add), ast.Sub: ("-", operator.sub),
          ast.BitAnd: ("&", operator.and_), ast.BitOr: ("|", operator.or_),
          ast.BitXor: ("^", operator.xor)}
CALLS = {"divmod", "pow", "int", "str", "format", "Fraction"}
#: operators whose cost is superlinear when BOTH operands are long (schoolbook product/division)
SUPERLINEAR = {"*", "//", "%", "**", "divmod()", "pow()"}

SITES: list[tuple[str, str, int, str, str]] = []     # sid -> (module, function, line, op, expression text)
SITE_FN: list = []                                    # sid -> callable for binops
STATS: dict[int, list[int]] = {}                      # sid -> [count, max_min_bits, max_bits, n_super, n_super_basic]
STAGE: list[str] = []
PATCHES: dict[str, list[tuple[str, str]]] = {}


def _record(sid: int, la: int, lb: int, lr: int) -> None:
    st = STATS.get(sid)
    if st is None:
        st = STATS[sid] = [0, 0, 0, 0, 0]
    st[0] += 1
    mn = la if la < lb else lb
    if mn > st[1]:
        st[1] = mn
    mx = max(la, lb, lr)
    if mx > st[2]:
        st[2] = mx
    if mn > WORD and SITES[sid][3] in SUPERLINEAR:
        if STAGE and STAGE[-1] == "basic":
            st[4] += 1
        else:
            st[3] += 1


def _bits(v) -> int:
    return v.bit_length() if type(v) is int else 0


def __optrace_bin__(sid, a, b):
    r = SITE_FN[sid](a, b)
    if type(a) is int or type(b) is int:
        la, lb, lr = _bits(a), _bits(b), _bits(r)
        if la > WORD or lb > WORD or lr > WORD:
            _record(sid, la, lb, lr)
    return r


def __optrace_call__(sid, fn, *args, **kw):
    r = fn(*args, **kw)
    ints = [x for x in args if type(x) is int]
    if ints or type(r) is int:
        la = _bits(ints[0]) if ints else 0
        lb = _bits(ints[1]) if len(ints) > 1 else 0
        lr = _bits(r) if type(r) is int else max((_bits(x) for x in r), default=0) \
            if isinstance(r, tuple) else 0
        if la > WORD or lb > WORD or lr > WORD:
            _record(sid, la, lb, lr)
    return r


class _Rewriter(ast.NodeTransformer):
    def __init__(self, module: str):
        self.module = module
        self.scope = ["<module>"]

    def _site(self, node, op: str, fn=None, text: str = "") -> int:
        # ``text`` = ast.unparse of the ORIGINAL node (taken before the children are rewritten): it identifies the
        # site independently of line numbers, so the guard's allowlist is per site, not per function
        SITES.append((self.module, ".".join(self.scope[1:]) or "<module>", node.lineno, op, text))
        SITE_FN.append(fn)
        return len(SITES) - 1

    def _scoped(self, node, name: str):
        self.scope.append(name)
        self.generic_visit(node)
        self.scope.pop()
        return node

    def visit_FunctionDef(self, node):
        return self._scoped(node, node.name)

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_ClassDef(self, node):
        return self._scoped(node, node.name)

    def visit_Lambda(self, node):
        return self._scoped(node, "<lambda>")

    def visit_BinOp(self, node):
        text = ast.unparse(node)
        self.generic_visit(node)
        spec = BINOPS.get(type(node.op))
        if spec is None:
            return node
        sid = self._site(node, spec[0], spec[1], text)
        return ast.copy_location(ast.Call(ast.Name("__optrace_bin__", ast.Load()),
                                          [ast.Constant(sid), node.left, node.right], []), node)

    def visit_AugAssign(self, node):
        text = ast.unparse(node)
        self.generic_visit(node)
        spec = BINOPS.get(type(node.op))
        if spec is None:
            return node
        sid = self._site(node, spec[0], spec[1], text)
        load = copy.deepcopy(node.target)
        for sub in ast.walk(load):
            if hasattr(sub, "ctx"):
                sub.ctx = ast.Load()
        value = ast.Call(ast.Name("__optrace_bin__", ast.Load()), [ast.Constant(sid), load, node.value], [])
        return ast.copy_location(ast.Assign([node.target], value), node)

    def visit_Call(self, node):
        text = ast.unparse(node)
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id in CALLS:
            sid = self._site(node, node.func.id + "()", None, text)
            return ast.copy_location(ast.Call(ast.Name("__optrace_call__", ast.Load()),
                                              [ast.Constant(sid), node.func] + node.args, node.keywords),
                                     node)
        return node


class _Loader(importlib.abc.Loader):
    def __init__(self, fullname: str, path: str):
        self.fullname, self.path = fullname, path

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        with open(self.path, encoding="utf-8") as fh:
            src = fh.read()
        for old, new in PATCHES.get(self.fullname, ()):
            if src.count(old) != 1:
                raise AssertionError(f"optrace patch for {self.fullname} must match once: {old!r}")
            src = src.replace(old, new)
        tree = ast.fix_missing_locations(_Rewriter(self.fullname).visit(ast.parse(src, self.path)))
        exec(compile(tree, self.path, "exec"), module.__dict__)


class _Finder(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path, target=None):
        if not (fullname == "subnlogn" or fullname.startswith("subnlogn.")) or fullname.startswith(SKIP):
            return None
        spec = importlib.machinery.PathFinder.find_spec(fullname, path)
        if spec is not None and spec.origin and spec.origin.endswith(".py"):
            spec.loader = _Loader(fullname, spec.origin)
        return spec


def install(patches: dict | None = None) -> None:
    """Install the rewriting importer; must run before ``subnlogn`` is first imported."""
    if any(m == "subnlogn" or m.startswith("subnlogn.") for m in sys.modules):
        raise RuntimeError("optrace.install must run before subnlogn is imported")
    PATCHES.update(patches or {})
    builtins.__optrace_bin__ = __optrace_bin__
    builtins.__optrace_call__ = __optrace_call__
    sys.meta_path.insert(0, _Finder())
    import subnlogn.hierarchy as H                       # noqa: E402  (traced copy)
    orig = H.Hierarchy._run

    def _run(self, stage, *args):
        STAGE.append(stage)
        try:
            return orig(self, stage, *args)
        finally:
            STAGE.pop()
    H.Hierarchy._run = _run


def report() -> list[dict]:
    out = []
    for sid, st in sorted(STATS.items()):
        mod, fn, line, op, expr = SITES[sid]
        out.append({"module": mod, "function": fn, "line": line, "op": op, "expr": expr, "count": st[0],
                    "max_min_bits": st[1], "max_bits": st[2], "superlinear": st[3],
                    "superlinear_in_basic": st[4]})
    return out


__all__ = ["install", "report", "SUPERLINEAR", "WORD", "Fraction"]
