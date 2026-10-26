"""Must-fail mutant tests: four partial silent shortcuts that survived the suite while the path checks
asserted only "> 0":

    A31  the Prop 14 network runs only for the FIRST Bluestein chunk-round layer of a context, the base case after
    A32  the Walsh middle uses the network engine only for the first middle call of a context
    A35  BasicMul replaced by Python's * (its stage counter still incremented)
    A36  Lemma 13's chunk exchanges run Lemma 12 on the bit network only in the first row addition of an engine

Each mutant is applied IN MEMORY only (never written to the worktree): the function's source is rewritten with
one asserted ``str.replace`` and compiled into a copy of its module's namespace, and every loaded module
attribute bound to the original function is patched with ``monkeypatch`` (restored after the test).  Under the
mutant the products stay exact, and the strengthened exact-count assertion of the test that pins the path must
fail with its "exact path count" message.

A32's source line changed since the mutant was first recorded (``mul=ctx.word_mul()`` was added to the WalshCtx
call); the patch below applies the same condition to the current line.

Three further canaries are named mutants here too:

    N1  a word-scale solver product by an attribute call, ``__import__("operator").mul(mu, v)`` (solver.py)
    N2  a packed product of spread_row by a dunder call, ``Xi.__mul__(F_im)`` (kronecker.py)
    N3  the Bluestein input chirp products written inline (bluestein.tensor_positive_dft)

N1 and N3 bypass Ctx.word_mul: the python-mode oracle runs the same mutated code, so the stage identity of
tests/hierarchy_exact.py cannot see them; the independent structural model of the word products (word.call,
tests/path_model.py) catches them in python mode and in hierarchy mode.  N2 bypasses Ctx.product_mul and is caught
by the closed form of the packed products (the Multiply1 calls).
"""

import inspect
import random
import sys
import textwrap

import pytest

import subnlogn.hierarchy as hierarchy
import subnlogn.kronecker as kronecker
import subnlogn.m6.engine as engine
import subnlogn.middle3.bluestein as bluestein
import subnlogn.solver as solver
import subnlogn.walsh.fft as walsh_fft

# (module, function or Class.method, old snippet, new snippet) -- snippets of the dedented source
MUTANTS = {
    "N1": (solver, "cyclic_solve", "b_re = [shr(mul(mu, v), q) for v in y_re]",
           'b_re = [shr(__import__("operator").mul(mu, v), q) for v in y_re]'),
    "N2": (kronecker, "spread_row", "pii = unpack(mul(Xi, F_im), nout, B)",
           "pii = unpack(Xi.__mul__(F_im), nout, B)"),
    "N3": (bluestein, "tensor_positive_dft",
           "x0 = [trunc_cmul(xr, xi, ar, ai, p, wmul) for (xr, xi), (ar, ai) in zip(x, a)]",
           "x0 = [(shr_trunc(xr * ar - xi * ai, p), shr_trunc(xr * ai + xi * ar, p)) for (xr, xi), (ar, ai) in "
           "zip(x, a)]"),
    "A31": (bluestein, "prop14_layer",
            '        ctx.inst.hit("prop14.network_layer")\n        return simultaneous_H0_network(',
            '        ctx.inst.hit("prop14.network_layer")\n'
            '        if ctx.inst.counts.get("prop14.network_layer", 0) > 1:\n'
            '            from ..m6.prop14 import simultaneous_H0_base\n'
            '            return simultaneous_H0_base(recs, sel_bits, scale, p, truncate, K=K, rho=rho,'
            ' check_disk=truncate)\n'
            '        return simultaneous_H0_network('),
    "A32": (walsh_fft, "walsh_middle_dft",
            "engine=walsh_engine(ctx, geom.d),",
            'engine=walsh_engine(ctx, geom.d) if ctx.inst.counts.get("bridge.middle", 0) == 0 else None,'),
    "A35": (hierarchy, "Hierarchy.basic_mul",
            '    return self._run("basic", basic_schedule(), None, a, b)\n',
            '    self.inst.hit("hierarchy.basic")\n    return a * b\n'),
    "A36": (engine, "make_engine",
            "    def row_add(arr, rows, nb, dst, src, z, K, rho):\n"
            "        return row_add_lemma13(arr, rows, nb, dst, src, z, K, rho, bad_set=policy.bad_set,\n"
            "                               swap=swap, inst=inst)\n",
            "    calls = [0]\n\n    def row_add(arr, rows, nb, dst, src, z, K, rho):\n        calls[0] += 1\n"
            "        return row_add_lemma13(arr, rows, nb, dst, src, z, K, rho, bad_set=policy.bad_set,\n"
            "                               swap=swap if calls[0] == 1 else None, inst=inst)\n"),
}


def mutate(monkeypatch, name: str):
    """Apply mutant ``name`` in memory; returns the mutated function."""
    module, qual, old, new = MUTANTS[name]
    owner = module
    *outer, attr = qual.split(".")
    for part in outer:
        owner = getattr(owner, part)
    orig = getattr(owner, attr)
    src = textwrap.dedent(inspect.getsource(orig))
    assert src.count(old) == 1, f"mutant {name}: snippet not found exactly once in {qual}"
    ns = dict(vars(module))
    exec(compile(src.replace(old, new), module.__file__, "exec"), ns)
    mutant = ns[attr]
    assert mutant is not orig
    monkeypatch.setattr(owner, attr, mutant)
    for mod in list(sys.modules.values()):              # names imported elsewhere (e.g. test modules)
        for key, val in list(vars(mod).items()) if mod is not None else []:
            if val is orig and mod is not owner:
                monkeypatch.setattr(mod, key, mutant)
    return mutant


def test_every_mutant_applies():
    """Each snippet occurs exactly once in the current source (a stale mutant would silently test nothing)."""
    for name, (module, qual, old, _) in MUTANTS.items():
        obj = module
        for part in qual.split("."):
            obj = getattr(obj, part)
        assert textwrap.dedent(inspect.getsource(obj)).count(old) == 1, name


def test_A31_partial_prop14_fallback_is_caught(monkeypatch):
    """test_m7_end_to_end's random-seed network shape: 12 network layers expected, the mutant runs 1."""
    import test_m7_end_to_end as e2e
    mutate(monkeypatch, "A31")
    with pytest.raises(AssertionError, match="exact path count (m6|lemma13)"):
        e2e.test_random_seeds_network_shape(0)


def test_A32_partial_walsh_fallback_is_caught(monkeypatch):
    """test_walsh_e2e's exact Walsh products: the second middle call of the context loses its network layers."""
    import test_walsh_e2e as we
    mutate(monkeypatch, "A32")
    rng = random.Random(32)
    pairs = [(rng.getrandbits(90) | (1 << 89), rng.getrandbits(90))]
    with pytest.raises(AssertionError, match="exact path count (m6|lemma13)"):
        we.middle_products_exact(4, "walsh", "network", pairs)


def test_A35_basic_mul_bypass_is_caught(monkeypatch):
    """BasicMul's internal FFT counters: both the direct BasicMul test and the per-call check inside Multiply1."""
    import test_m7_dispatch as dispatch
    import test_path_counts as counts
    mutate(monkeypatch, "A35")
    with pytest.raises(AssertionError, match="exact path count"):
        dispatch.test_basic_mul_is_a_single_base_fft()
    with pytest.raises(AssertionError, match="exact path count"):         # e.g. basefft.butterfly 0 != 160
        counts.basic_mul_in_multiply1_case(monkeypatch)


def test_A36_partial_lemma12_swaps_is_caught(monkeypatch):
    """The mutation-sensitivity engine test: three row additions, Lemma 12 network calls 24 expected, the mutant makes 8."""
    import test_regression_mutants as sa
    mutate(monkeypatch, "A36")
    with pytest.raises(AssertionError, match="exact path count (interchange|lemma13)"):
        sa.test_engine_lemma13_swaps_use_the_bit_network()


def test_N1_word_product_by_attribute_call_is_caught(monkeypatch, basic_mul_stub):
    """N1: one solver product per forward cycle bypasses Ctx.word_mul.  Python mode: the end-to-end test's
    word.call (bridge deconvolution) falls short of the structural model.  Hierarchy mode: the oracle W and the
    Multiply1 calls drop together (the stage identity still holds), but word.call of the deep-2D route does not."""
    import test_m7_end_to_end as e2e
    import test_products as tp
    mutate(monkeypatch, "N1")
    with pytest.raises(AssertionError, match="exact path count word.call"):
        e2e.test_random_seeds_network_shape(0)
    with pytest.raises(AssertionError, match="exact path count word.call"):
        tp._deep2d_hierarchy_product(monkeypatch, basic_mul_stub)


def test_N2_packed_product_by_dunder_call_is_caught(monkeypatch, basic_mul_stub):
    """N2: one of the four packed products of every spread block bypasses Ctx.product_mul: the Multiply1 calls
    fall short of the closed form of the packed products (stage identity, tests/hierarchy_exact.py)."""
    import test_products as tp
    mutate(monkeypatch, "N2")
    with pytest.raises(AssertionError, match="exact path count hierarchy.multiply1"):
        tp._deep2d_hierarchy_product(monkeypatch, basic_mul_stub)


def test_N3_inline_chirp_products_are_caught(monkeypatch):
    """N3 (the operator guard's line-level allowlist is the other check): R chirp products computed inline
    leave word.call 4 R short per Bluestein middle call."""
    import test_m7_end_to_end as e2e
    mutate(monkeypatch, "N3")
    with pytest.raises(AssertionError, match="exact path count word.call"):
        e2e.test_random_seeds_network_shape(0)
