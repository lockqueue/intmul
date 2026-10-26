"""Call-form arithmetic lint: the operator tracer (tests/optrace.py) and the
call/return trace see inline operators and calls, but not multiplication through CALLS -- ``operator.mul``,
dunder methods (``x.__mul__(y)``), ``math.prod``, ``functools.reduce`` with a multiplying function, ``pow``,
``__import__``, ``getattr(x, "__mul__")``.  This test parses every data-path module (the traced set of
tests/optrace.py: subnlogn minus the class-D table modules, the network data package and the instrumentation) and
forbids those forms, except at the sites listed below, each with its reason (per site: module, enclosing
function, expression text -- not per function).  The canaries N1 (``__import__("operator").mul``) and N2
(``Xi.__mul__(F_im)``) are injected into a copy of the source and must be flagged.

Import aliases are resolved: ``import operator as op`` ... ``op.mul``, ``from math import prod as
_fold`` ... ``_fold(...)``, ``from functools import reduce as fold``, ``from builtins import pow as p``, at module
level or inside functions; a forbidden function used as a VALUE (``map(_fold, rows)``, ``f = math.prod``) is flagged
too.  Deliberate obfuscation (assignment chains, computed attribute names) is outside this regression guard's
threat model."""

import ast
import os

import pytest

import subnlogn

PKG = os.path.dirname(os.path.abspath(subnlogn.__file__))
SKIP_PREFIXES = ("certified", "certcore", "rigorous", "net/", "instrument")
ARITH_DUNDERS = {"__mul__", "__rmul__", "__imul__", "__pow__", "__rpow__", "__ipow__", "__floordiv__",
                 "__rfloordiv__", "__mod__", "__rmod__", "__divmod__", "__rdivmod__", "__truediv__",
                 "__rtruediv__", "__matmul__"}
OPERATOR_ARITH = {"mul", "imul", "pow", "ipow", "floordiv", "ifloordiv", "mod", "imod", "truediv", "itruediv",
                  "matmul"}
#: qualified names of call-form arithmetic functions (after import-alias resolution)
FORBIDDEN_QUAL = ({"math.prod", "math.pow", "builtins.pow", "builtins.__import__"}
                  | {f"operator.{f}" for f in OPERATOR_ARITH})

#: allowed call-form arithmetic, PER SITE: (module, enclosing function, expression text) -> reason
ALLOW = {
    ('subnlogn.ring', 'normalized_ring_product', 'operator.mul'):
        'unit-test default of the `mul` parameter; the pipeline passes ctx.product_mul (unit-test fallback only)',
    ('subnlogn.stream', 'Shape.volume', 'prod(self.lengths)'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'Shape.stride', 'prod(self.lengths[self.index(name) + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'Shape.split', 'prod((p.length for p in parts))'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'Shape.join', 'prod((self.fields[i].length for i in idx))'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'specialize', 'pow(c.denominator, -1, Q)'):
        'index arithmetic: modular inverse modulo a small radix',
    ('subnlogn.stream', '_region_permute', 'prod(lens[:lo])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', '_region_permute', 'prod(lens[hi + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'digit_pair_perm', 'prod(lens[:i1])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'digit_pair_perm', 'prod(lens[i1 + 1:i2])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'digit_pair_perm', 'prod(lens[i2 + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'split_map_merge', 'prod(lens[:i])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'split_map_merge', 'prod(lens[i + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'row_split', 'prod(lens[:i])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'row_split', 'prod(lens[i + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'row_merge', 'prod(lens[:i])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'row_merge', 'prod(lens[i + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'controlled_shift', 'prod(lens[:it])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'controlled_shift', 'prod(lens[it + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'controlled_shift', 'prod(lens[ic + 1:it])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', '_unit_permute', 'prod(lens[:it])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', '_unit_permute', 'prod(lens[it + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', '_unit_permute', 'pow(c, -1, Q)'):
        'index arithmetic: modular inverse modulo a small radix',
    ('subnlogn.stream', 'pad_rows', 'prod(lens[:i])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'pad_rows', 'prod(lens[i + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'unpad_rows', 'prod(lens[:i])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.stream', 'unpad_rows', 'prod(lens[i + 1:])'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.tables', 'closure_gamma', 'pow(a_hat, L)'):
        "D/E: closure method='exact', the test oracle (never selected on the data path)",
    ('subnlogn.bridge.precision', 'certify_bridge_precision', 'prod(t)'):
        'index arithmetic: product of shape lengths (small integers)',
    ('subnlogn.m6.lemma13', 'row_add_lemma13', 'prod(shape.lengths)'):
        'index arithmetic: product of shape lengths (small integers)',
}


def data_path_modules():
    for root, _, files in os.walk(PKG):
        for f in sorted(files):
            if not f.endswith(".py"):
                continue
            rel = os.path.relpath(os.path.join(root, f), PKG).replace(os.sep, "/")
            if rel.startswith(SKIP_PREFIXES):
                continue
            yield "subnlogn." + rel[:-3].replace("/", ".").removesuffix(".__init__"), os.path.join(root, f)


def import_bindings(tree) -> dict:
    """Local name -> qualified name for every absolute import anywhere in the module: ``import operator
    as op`` binds op -> operator; ``from math import prod as _fold`` binds _fold -> math.prod; ``from math import prod``
    binds prod -> math.prod.  Package-relative imports are skipped (they cannot reach the standard library)."""
    bind = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                if a.asname:
                    bind[a.asname] = a.name
        elif isinstance(node, ast.ImportFrom) and node.module and not node.level:
            for a in node.names:
                bind[a.asname or a.name] = f"{node.module}.{a.name}"
    return bind


class _Lint(ast.NodeVisitor):
    def __init__(self, module: str, bind: dict | None = None):
        self.module, self.scope, self.found = module, [], []
        self.bind = bind or {}
        self.callees: set[int] = set()          # ids of Call.func nodes (flagged, if at all, as the call)

    def _qual(self, node):
        """Qualified name of a Name/Attribute chain with import aliases resolved (None if not a plain chain)."""
        if isinstance(node, ast.Name):
            return self.bind.get(node.id, node.id)
        if isinstance(node, ast.Attribute):
            base = self._qual(node.value)
            return f"{base}.{node.attr}" if base else None
        return None

    def _fn(self) -> str:
        return ".".join(self.scope) or "<module>"

    def _flag(self, node, why: str):
        self.found.append((self.module, self._fn(), ast.unparse(node), why, node.lineno))

    def _scoped(self, node):
        self.scope.append(node.name)
        self.generic_visit(node)
        self.scope.pop()

    visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = _scoped

    def visit_ImportFrom(self, node):
        if node.module == "operator" and any(a.name in OPERATOR_ARITH for a in node.names):
            self._flag(node, "from operator import <arithmetic>")
        self.generic_visit(node)

    def visit_Attribute(self, node):
        if node.attr in ARITH_DUNDERS:
            self._flag(node, "arithmetic dunder")
        elif isinstance(node.value, ast.Name) and self._qual(node.value) == "operator" and node.attr in OPERATOR_ARITH:
            self._flag(node, "operator.<arithmetic>")            # literal `operator` or an alias (`op.mul`)
        elif id(node) not in self.callees and self._qual(node) in FORBIDDEN_QUAL:
            self._flag(node, "call-form arithmetic function used as a value")
        self.generic_visit(node)

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load) and id(node) not in self.callees and node.id in self.bind \
                and self.bind[node.id] in FORBIDDEN_QUAL:
            self._flag(node, f"import alias of {self.bind[node.id]} used as a value")

    def visit_Call(self, node):
        f = node.func
        self.callees.add(id(f))
        name = f.id if isinstance(f, ast.Name) else f.attr if isinstance(f, ast.Attribute) else None
        qn = self._qual(f)
        if name == "__import__" or qn == "builtins.__import__":
            self._flag(node, "__import__")
        elif name == "pow" or qn in ("builtins.pow", "math.pow"):
            self._flag(node, "pow()")
        elif name == "prod" or qn == "math.prod":
            self._flag(node, "math.prod")
        elif (name == "reduce" or qn == "functools.reduce") and node.args and _multiplies(node.args[0], self.bind):
            self._flag(node, "reduce with a multiplying function")
        elif name == "getattr" and len(node.args) > 1 and isinstance(node.args[1], ast.Constant) \
                and node.args[1].value in ARITH_DUNDERS:
            self._flag(node, "getattr of an arithmetic dunder")
        elif isinstance(f, ast.Name) and qn in FORBIDDEN_QUAL:
            self._flag(node, f"{qn} called through an import alias")
        self.generic_visit(node)


def _multiplies(fn, bind: dict | None = None) -> bool:
    if isinstance(fn, ast.Attribute) and fn.attr in OPERATOR_ARITH | ARITH_DUNDERS:
        return True
    if isinstance(fn, ast.Name) and (fn.id in OPERATOR_ARITH or (bind or {}).get(fn.id) in FORBIDDEN_QUAL):
        return True
    return isinstance(fn, ast.Lambda) and any(isinstance(n, ast.BinOp) and isinstance(n.op, (
        ast.Mult, ast.Pow, ast.FloorDiv, ast.Mod, ast.MatMult)) for n in ast.walk(fn.body))


def lint_all(module: str, src: str) -> list:
    """Every call-form arithmetic site of a module (import aliases resolved), allowlisted or not."""
    tree = ast.parse(src)
    v = _Lint(module, import_bindings(tree))
    v.visit(tree)
    return v.found


def lint_source(module: str, src: str) -> list:
    return [x for x in lint_all(module, src) if (x[0], x[1], x[2]) not in ALLOW]


def test_no_call_form_arithmetic_in_the_data_path():
    bad = []
    for module, path in data_path_modules():
        with open(path, encoding="utf-8") as fh:
            bad += lint_source(module, fh.read())
    assert bad == [], "\n".join(f"{m}:{fn}:{ln} {why}: {txt}" for m, fn, txt, why, ln in bad)


def test_every_allowlisted_site_exists():
    """Stale allowlist entries are errors too (the allowlist is per site)."""
    seen = set()
    for module, path in data_path_modules():
        with open(path, encoding="utf-8") as fh:
            seen |= {(m, fn, txt) for m, fn, txt, _, _ in lint_all(module, fh.read())}
    assert set(ALLOW) <= seen, set(ALLOW) - seen


CANARIES = {
    # N1: a word-scale solver product through an attribute call
    "N1_operator_mul_via_import": ("subnlogn.solver", "solver.py",
                                   "shr(mul(mu, v), q) for v in y_re",
                                   "shr(__import__('operator').mul(mu, v), q) for v in y_re"),
    # N2: a packed product through a dunder call
    "N2_dunder_mul": ("subnlogn.kronecker", "kronecker.py",
                      "pii = unpack(mul(Xi, F_im), nout, B)", "pii = unpack(Xi.__mul__(F_im), nout, B)"),
    "math_prod_on_records": ("subnlogn.synthetic", "synthetic.py",
                             "nr.append(shr(mul(a, wr) - mul(b, wi), q))",
                             "nr.append(shr(prod((a, wr)) - mul(b, wi), q))"),
}


@pytest.mark.parametrize("canary", sorted(CANARIES))
def test_canaries_are_flagged(canary):
    module, rel, old, new = CANARIES[canary]
    with open(os.path.join(PKG, rel), encoding="utf-8") as fh:
        src = fh.read()
    assert src.count(old) == 1, "canary snippet is stale"
    assert lint_source(module, src) == []
    assert lint_source(module, src.replace(old, new)) != [], "canary not flagged"


#: import-alias forms; each probe must be flagged
ALIAS_PROBES = {
    "N4b_prod_alias": "from math import prod as _fold\ndef f(mu, v):\n    return _fold((mu, v))\n",
    "operator_module_alias": "import operator as op\ndef f(a, b):\n    return op.mul(a, b)\n",
    "operator_alias_as_value": "import operator as op\ndef f(xs, ys):\n    return list(map(op.mul, xs, ys))\n",
    "from_operator_alias_call": "from operator import mul as m\ndef f(a, b):\n    return m(a, b)\n",
    "reduce_alias_lambda": "from functools import reduce as fold\ndef f(xs):\n    return fold(lambda a, b: a * b, xs)\n",
    "reduce_alias_operator_alias": ("import functools as ft\nimport operator as op\n"
                                    "def f(xs):\n    return ft.reduce(op.mul, xs)\n"),
    "prod_alias_as_value": "from math import prod as _fold\ndef f(rows):\n    return list(map(_fold, rows))\n",
    "math_prod_as_value": "import math\nfold = math.prod\n",
    "math_module_alias_prod": "import math as m\ndef f(a, b):\n    return m.prod((a, b))\n",
    "pow_alias": "from builtins import pow as _p\ndef f(a):\n    return _p(a, 2)\n",
    "local_import_alias": "def f(mu, v):\n    from math import prod as _fold\n    return _fold((mu, v))\n",
}

#: ordinary code that must stay clean (no over-flagging)
CLEAN_PROBES = {
    "routed_mul_parameter": "def f(mul, a, b):\n    return mul(a, b)\n",
    "relative_import": "from .context import Ctx\ndef f(ctx: Ctx, a, b):\n    return ctx.word_mul(a, b)\n",
    "math_isqrt": "import math\ndef f(n):\n    return math.isqrt(n)\n",
    "operator_itemgetter": "import operator as op\nkey = op.itemgetter(0)\n",
}


@pytest.mark.parametrize("probe", sorted(ALIAS_PROBES))
def test_import_aliases_are_resolved(probe):
    assert lint_source("probe", ALIAS_PROBES[probe]) != [], f"{probe} not flagged"


@pytest.mark.parametrize("probe", sorted(CLEAN_PROBES))
def test_clean_code_is_not_flagged(probe):
    assert lint_source("probe", CLEAN_PROBES[probe]) == []


#: canaries N4b, N4c, N4d through an import alias, as injected into the real solver: (old, new) edits of
#: subnlogn/solver.py.  N4c/N4d also keep the routed call and discard its result (so word.call is unchanged); the
#: alias makes them visible to the lint.
_IMP = ("from typing import Callable\n", "from typing import Callable; from math import prod as _fold\n")
ALIAS_CANARIES = {
    "N4b": [_IMP, ("b_re = [shr(mul(mu, v), q) for v in y_re]", "b_re = [shr(_fold((mu, v)), q) for v in y_re]")],
    "N4c": [_IMP, ("b_re = [shr(mul(mu, v), q) for v in y_re]",
                   "b_re = [shr((mul(mu, v), _fold((mu, v)))[1], q) for v in y_re]")],
    "N4d": [_IMP, ("b_im = [shr(mul(mu, v), q) for v in y_im]",
                   "b_im = [shr((mul(mu, v), _fold((mu, v)))[1], q) for v in y_im]")],
    "operator_alias": [("from typing import Callable\n", "from typing import Callable; import operator as op\n"),
                       ("b_re = [shr(mul(mu, v), q) for v in y_re]", "b_re = [shr(op.mul(mu, v), q) for v in y_re]")],
}


@pytest.mark.parametrize("canary", sorted(ALIAS_CANARIES))
def test_alias_canaries_are_flagged(canary):
    with open(os.path.join(PKG, "solver.py"), encoding="utf-8") as fh:
        src = fh.read()
    assert lint_source("subnlogn.solver", src) == []
    for old, new in ALIAS_CANARIES[canary]:
        assert src.count(old) == 1, "canary snippet is stale"
        src = src.replace(old, new)
    assert lint_source("subnlogn.solver", src) != [], "canary not flagged"
