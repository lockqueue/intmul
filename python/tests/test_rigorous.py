"""Tests for subnlogn.rigorous (MS Lemma 2.2 (i)-(iv) with exact integer interval arithmetic) and for the
switch of subnlogn.certcore / subnlogn.certified to it (backend="exact", the default).

mpmath appears here only as a high-precision ORACLE (P + 200 bits) and as the cross-check backend.
"""

import ast
import pathlib
import random
import time
from fractions import Fraction

import mpmath
import pytest
from hypothesis import given, settings, strategies as st
from mpmath import iv, mp, mpf

from subnlogn import certcore as K
from subnlogn import certified as C
from subnlogn import rigorous as RG

HI = 200


def contains(lo, hi, P, x, width=None):
    """lo 2^-P <= x <= hi 2^-P for the mpmath real x (computed with >= P + 150 correct bits)."""
    X = mp.ldexp(x, P)
    ok = lo <= X <= hi
    return ok and (width is None or hi - lo <= width)


# ------------------------------------------------------------------------------------------ constants
@pytest.mark.parametrize("P", [0, 1, 2, 3, 7, 10, 53, 64, 100, 257, 1000, 3000])
def test_constants_fixed_scales(P):
    """MS Lemma 2.2(i): Machin pi, the ln 2 series, and 2/sqrt(pi) (exact isqrt) enclose the constants."""
    with mp.workprec(P + HI):
        assert contains(*RG.pi_interval(P), P, mp.pi, 2)
        assert contains(*RG.ln2_interval(P), P, mp.ln2, 2)
        assert contains(*RG.two_over_sqrt_pi_interval(P), P, 2 / mp.sqrt(mp.pi), 3)


@settings(max_examples=60)
@given(st.integers(0, 2500))
def test_constants_random_scales(P):
    with mp.workprec(P + HI):
        assert contains(*RG.pi_interval(P), P, mp.pi, 2)
        assert contains(*RG.ln2_interval(P), P, mp.ln2, 2)


# ------------------------------------------------------------------------------------------ exp
@settings(max_examples=300)
@given(st.integers(0, 400), st.integers(0, 800), st.data())
def test_exp_point_encloses(Pin, P, data):
    """MS Lemma 2.2(iii): reduction by ln 2 and a Taylor series with explicit remainder; width <= 2."""
    X = data.draw(st.integers(-(90 << Pin), 6 << Pin))
    lo, hi = RG.exp_point(X, Pin, P)
    with mp.workprec(P + Pin + HI):
        assert contains(lo, hi, P, mp.exp(mp.ldexp(X, -Pin)), 2)


@settings(max_examples=100)
@given(st.integers(0, 300), st.integers(0, 500), st.data())
def test_exp_interval_monotone(Pin, P, data):
    a = data.draw(st.integers(-(40 << Pin), 2 << Pin))
    b = data.draw(st.integers(a, a + (1 << Pin)))
    lo, hi = RG.exp_interval(a, b, Pin, P)
    with mp.workprec(P + Pin + HI):
        for X in (a, b, (a + b) // 2):
            assert contains(lo, hi, P, mp.exp(mp.ldexp(X, -Pin)))


@pytest.mark.parametrize("k,prec", [(-91, 45), (-384, 87), (-384, 88)])
def test_known_mpmath_exp_misses_handled_without_widening(k, prec):
    """The cases where mpmath 1.3.0's iv.exp(k/64) misses the true value by one ulp (they motivated the
    2^11-ulp widening of the mpmath backend) are enclosed by the exact backend with width <= 1 unit."""
    lo, hi = RG.exp_point(k, 6, prec)
    with mp.workprec(prec + HI):
        e = mp.exp(mpf(k) / 64)
        assert contains(lo, hi, prec, e, 1)
        old = iv.prec
        try:
            iv.prec = prec
            raw = iv.exp(iv.mpf(k) / 64)
        finally:
            iv.prec = old
        if mpmath.__version__ == "1.3.0":
            assert not raw.a <= e <= raw.b          # the documented mpmath behaviour (pinned version)


def test_exp_edge_cases():
    assert RG.exp_point(0, 0, 50) == (1 << 50, 1 << 50) and RG.exp_point(0, 77, 0) == (1, 1)
    t0 = time.time()
    assert RG.exp_point(-10 ** 9, 0, 100) == (0, 1)                 # huge negative argument
    assert RG.exp_point(-(10 ** 30) << 64, 64, 3000) == (0, 1)
    assert time.time() - t0 < 0.5
    with mp.workprec(800):
        for P in (10, 100, 500):                                     # around the cutoff -(P+2) ln 2
            X0 = int(mp.floor(-(P + 2) * mp.ln2 * 2 ** 40))
            for X in (X0 - 3, X0 - 1, X0, X0 + 1, X0 + 3):
                assert contains(*RG.exp_point(X, 40, P), P, mp.exp(mp.ldexp(X, -40)), 2)
        for X, Pin, P in [(1, 500, 300), (-1, 500, 300), (200, 0, 50), (-1, 0, 0), (5, 1, 3)]:
            assert contains(*RG.exp_point(X, Pin, P), P, mp.exp(mp.ldexp(X, -Pin)), 2)
    lo, hi = RG.exp_point(200, 0, 50)                                # e^200: exact big integers, no overflow
    assert hi - lo <= 2 and lo.bit_length() == 339


# ------------------------------------------------------------------------------------------ sin / cos
@settings(max_examples=300)
@given(st.integers(-10 ** 9, 10 ** 9), st.integers(1, 10 ** 6), st.integers(0, 600))
def test_sincos_pi_encloses(n, d, P):
    """MS Lemma 2.2(iv): exact reduction of the rational f to [0, 1/4], interval argument pi f,
    monotonicity and alternating Taylor series; width <= 2."""
    (cl, ch), (sl, sh) = RG.sincos_pi(Fraction(n, d), P)
    with mp.workprec(P + HI + 40):
        x = mpf(n) / d
        assert contains(cl, ch, P, mp.cospi(x), 2) and contains(sl, sh, P, mp.sinpi(x), 2)


def test_sincos_pi_exact_points_and_edges():
    for f, cs in [(0, (1, 0)), (Fraction(1, 2), (0, 1)), (1, (-1, 0)), (Fraction(3, 2), (0, -1)),
                  (2, (1, 0)), (Fraction(-1, 2), (0, -1)), (Fraction(7, 2), (0, -1)), (-3, (-1, 0))]:
        for P in (0, 5, 200):
            c, s = RG.sincos_pi(f, P)
            assert c == (cs[0] << P, cs[0] << P) and s == (cs[1] << P, cs[1] << P)
    with mp.workprec(600):
        for P in (100, 300):
            for f in (Fraction(1, 4), Fraction(3, 4), Fraction(1, 1 << 40), 1 - Fraction(1, 1 << 40),
                      Fraction(1, 1 << 300), Fraction((1 << 30) - 1, 1 << 30), Fraction(1, 3), Fraction(-7, 6)):
                c, s = RG.sincos_pi(f, P)
                x = mpf(f.numerator) / f.denominator
                assert contains(*c, P, mp.cospi(x), 2) and contains(*s, P, mp.sinpi(x), 2)


# ------------------------------------------------------------------------------------------ sqrt, *, /
@settings(max_examples=200)
@given(st.integers(0, 300), st.integers(0, 300), st.integers(0, 1 << 200), st.integers(0, 1 << 60))
def test_sqrt_interval(Pin, P, lo, wd):
    a, b = RG.sqrt_interval(lo, lo + wd, Pin, P)
    with mp.workprec(Pin + P + 400):
        for v in (lo, lo + wd):
            assert contains(a, b, P, mp.sqrt(mp.ldexp(v, -Pin)))
    assert RG.sqrt_interval(9 << 20, 9 << 20, 20, 10) == (3 << 10, 3 << 10)    # exact squares stay exact
    assert RG.isqrt_ceil(0) == 0 and RG.isqrt_ceil(10) == 4 and RG.isqrt_ceil(16) == 4


@settings(max_examples=200)
@given(st.integers(-(1 << 80), 1 << 80), st.integers(0, 1 << 40), st.integers(-(1 << 80), 1 << 80),
       st.integers(0, 1 << 40), st.integers(0, 120), st.data())
def test_mul_div_interval(a0, aw, b0, bw, P, data):
    A, B = (a0, a0 + aw), (b0, b0 + bw)
    x = Fraction(data.draw(st.integers(A[0], A[1])), 1 << P)
    y = Fraction(data.draw(st.integers(B[0], B[1])), 1 << P)
    lo, hi = RG.mul_interval(A, B, P)
    assert Fraction(lo, 1 << P) <= x * y <= Fraction(hi, 1 << P)
    if B[0] > 0:
        lo, hi = RG.div_interval(A, B, P)
        assert Fraction(lo, 1 << P) <= x / y <= Fraction(hi, 1 << P)
    else:
        with pytest.raises(ZeroDivisionError):
            RG.div_interval(A, (0, 1), P)


def test_rigorous_module_is_pure_integer():
    """No mpmath, no floats, no true division in subnlogn/rigorous.py (only int, Fraction, isqrt)."""
    tree = ast.parse(pathlib.Path(RG.__file__).read_text())
    for node in ast.walk(tree):
        assert not (isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)))
        assert not isinstance(node, ast.Div)
        assert not (isinstance(node, ast.Name) and node.id in ("float", "complex"))
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            mods = [a.name for a in node.names] + [getattr(node, "module", None) or ""]
            assert not any(m and ("mpmath" in m or m in ("cmath", "numpy", "decimal")) for m in mods)
    with pytest.raises(ValueError):
        RG.pi_interval(-1)


# ------------------------------------------------------------------------------------------ certified switch
@pytest.fixture
def no_mpmath(monkeypatch):
    """Make every mpmath entry point of certcore / certified unusable, and clear the table caches."""
    for mod in (C, K):
        monkeypatch.setattr(mod, "iv", None)
    for name in ("_pi", "_ln2", "_exp", "_iv_dyadic", "_iv_ball"):
        for mod in (C, K):
            if hasattr(mod, name):
                monkeypatch.setattr(mod, name, None)
    C._cos_sin_octant.cache_clear()
    C._a_ball.cache_clear()
    C._root_table_cached.cache_clear()
    yield


def test_exact_backend_never_touches_mpmath(no_mpmath):
    """The default (exact) backend computes every table without any mpmath call."""
    assert C.unit_root(3, 1024, 333) and C.unit_root(5, 16, 41)
    assert C.G_alpha(Fraction(1, 3), 9, 157) > 0
    sc = C.solver_coeffs(5, 16, 40, 211)
    assert sc.forward
    h = C.folded_kernel(Fraction(5, 16), 16, 60, 30, 177)
    h0 = C.folded_kernel(Fraction(3, 8), 8, 40, 20, 99, 0)
    assert len(h) == 16 and len(h0) == 8
    lo, hi = K._erf_point(12345, 20)
    assert 0 <= lo <= hi
    C._phase_table_cached.cache_clear()
    C._disk_octant.cache_clear()
    assert len(C.phase_table(64, 97)) == 128
    with pytest.raises((TypeError, AttributeError)):  # the cross-check backend really is disabled here
        C.unit_root(3, 1024, 334, backend="mpmath")


def test_backend_argument_validation():
    for bad in [lambda: C.unit_root(1, 8, 10, backend="iv"), lambda: C.G_alpha(Fraction(1, 2), 9, 10, backend=""),
                lambda: C.solver_coeffs(0, 4, 8, 10, backend="float"),
                lambda: C.folded_kernel(Fraction(1, 2), 4, 5, 8, 10, backend="x"),
                lambda: C.alpha_iv(20, 100, backend="nope"), lambda: C.phase_table(4, 10, backend="iv")]:
        with pytest.raises(ValueError):
            bad()
    assert C.BACKENDS == ("exact", "mpmath")


@settings(max_examples=150)
@given(st.integers(-(1 << 40), 1 << 40), st.integers(0, 16), st.integers(0, 400))
def test_unit_root_backends_agree(num, k, q):
    """Correct rounding makes the value unique: the exact and mpmath backends must agree."""
    assert C.unit_root(num, 1 << k, q) == C.unit_root(num, 1 << k, q, backend="mpmath")


@settings(max_examples=60)
@given(st.integers(-3000, 3000), st.integers(1, 1000), st.integers(8, 2000), st.integers(0, 400))
def test_G_alpha_backends_agree(p, d, w, q):
    xi = Fraction(p, d)
    assert C.G_alpha(xi, w, q) == C.G_alpha(xi, w, q, backend="mpmath")


@settings(max_examples=60)
@given(st.integers(1, 8), st.data(), st.integers(8, 2000), st.integers(8, 400))
def test_solver_coeffs_backends_agree(k, data, w, q):
    t = 1 << k
    u = data.draw(st.integers(0, t - 1))
    assert C.solver_coeffs(u, t, w, q) == C.solver_coeffs(u, t, w, q, backend="mpmath")


dyadics = st.integers(1, 12).flatmap(lambda k: st.integers(1, (1 << k) - 1).map(lambda j: Fraction(j, 1 << k)))


@settings(max_examples=50)
@given(dyadics, st.integers(1, 7).map(lambda k: 1 << k), st.integers(0, 80), st.integers(8, 400),
       st.integers(1, 300), st.sampled_from([-1, 0, 1]))
def test_folded_kernel_backends_agree(delta, t, m, w, q, carrier):
    assert C.folded_kernel(delta, t, m, w, q, carrier) == C.folded_kernel(delta, t, m, w, q, carrier,
                                                                         backend="mpmath")


@pytest.mark.parametrize("r,p", [(1, 5), (2, 30), (8, 64), (64, 100), (256, 61)])
def test_phase_table_backends_agree(r, p):
    """The disk-grid phase table (truncation toward zero, decided like Q_p) is unique too."""
    assert C.phase_table(r, p) == C.phase_table(r, p, backend="mpmath")


def test_alpha_iv_backends():
    with mp.workprec(500):
        al = 2 * mp.sqrt(20 * mp.ln2 / mp.pi)
        for backend in C.BACKENDS:
            a = C.alpha_iv(20, 300, backend=backend)
            assert a.a <= al <= a.b and a.b - a.a < mp.ldexp(1, -280)


@settings(max_examples=60)
@given(st.integers(20, 500), st.data())
def test_exact_enclosures_are_tighter(P, data):
    """No 2^10-ulp slack: the exact erf enclosure is never wider than the mpmath-backed one, and both
    contain erf (oracle)."""
    X = data.draw(st.integers(0, 6 << P))
    e_lo, e_hi = K._erf_point(X, P)
    m_lo, m_hi = K._erf_point(X, P, "mpmath")
    with mp.workprec(P + HI):
        ref = mp.erf(mp.ldexp(X, -P))
        assert contains(e_lo, e_hi, P, ref) and contains(m_lo, m_hi, P, ref)
    assert e_hi - e_lo <= m_hi - m_lo


def test_realistic_table_sizes_agree_and_timing():
    """Representative 2D table sizes: identical values, exact backend within a small factor of mpmath."""
    cases = [(Fraction(5, 16), 128, 400, 200, 400), (Fraction(1, 1024), 8, 200, 100, 300),
             (Fraction(4095, 4096), 2, 60, 30, 200)]
    for delta, t, m, w, q in cases:
        t0 = time.time()
        a = C.folded_kernel(delta, t, m, w, q)
        t1 = time.time()
        b = C.folded_kernel(delta, t, m, w, q, backend="mpmath")
        t2 = time.time()
        assert a == b
        assert t1 - t0 < 20 * (t2 - t1) + 0.5
    rng = random.Random(5)
    for _ in range(20):
        u, q = rng.randrange(128), rng.randrange(100, 400)
        assert C.solver_coeffs(u, 128, 200, q) == C.solver_coeffs(u, 128, 200, q, backend="mpmath")
