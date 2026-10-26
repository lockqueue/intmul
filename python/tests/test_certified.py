"""Tests for subnlogn.certified: correctly rounded certified tables.

Sources: MS Lemma 2.2 (lem:elementary), Def. 2.1, eq. (ghat), §6.1 filter objects; r2 §4.3-4.7,
§8 (negative half-bin drop-in), r3 eq. (4.10), r1 §10.5 (folding-sign check), r2 (4.22) (Poisson).
Every value is compared with plain mpmath at precision q + 200: |n 2^-q - x| <= 2^-q/2 and n is
the integer nearest to 2^q x (correct rounding).
"""

from fractions import Fraction
from math import ceil

import mpmath
import pytest
from hypothesis import assume, given, settings, strategies as st
from mpmath import iv, mp, mpf

from subnlogn import certcore as K
from subnlogn import certified as C
from subnlogn.certified import (
    G_alpha, SolverCoeffs, alpha_iv, correctly_rounded, folded_kernel, solver_coeffs, unit_root,
)
from subnlogn.fixedpoint import from_fraction

HI = 200  # extra bits of the mpmath references


@pytest.fixture(autouse=True)
def _no_fallback():
    """Fail loudly if any faithful-rounding fallback happened."""
    yield
    assert C.fallback_events() == [], f"certified fallback taken: {C.fallback_events()}"


# ----------------------------------------------------------------------------------------------
# mpmath references
# ----------------------------------------------------------------------------------------------


def nearest(x, q):
    """The integer nearest to 2^q x (x an mpmath real with >= q + 150 correct bits)."""
    y = mp.ldexp(x, q)
    fl = int(mp.floor(y))
    fr = y - fl
    assert abs(fr - mpf(1) / 2) > mp.ldexp(1, -100), "reference too close to a rounding tie"
    return fl + int(fr > mpf(1) / 2)


def assert_cr(n, x, q):
    """n == Q_q(x): within half an ulp of x and the nearest integer to 2^q x."""
    assert abs(n - mp.ldexp(x, q)) <= mpf(1) / 2 + mp.ldexp(1, -100)
    assert n == nearest(x, q)


def mp_G(xi, w):
    """G_alpha(xi), MS eq. (ghat), with the erfc form for |xi| > 1/2 (no cancellation)."""
    a = 2 * mp.sqrt(w * mp.ln2)
    x = abs(mpf(xi.numerator) / xi.denominator)
    if x > mpf(1) / 2:
        return (mp.erfc(a * (x - mpf(1) / 2)) - mp.erfc(a * (x + mpf(1) / 2))) / 2
    return (mp.erf(a * (x + mpf(1) / 2)) + mp.erf(a * (mpf(1) / 2 - x))) / 2


def mp_g0(s, w):
    """Unmodulated sinc-Gaussian g0(s) = sinc(s) e^{-pi s^2/alpha^2} (MS eq. (sinc-gauss))."""
    return mp.sincpi(s) * mp.exp(-s * s * mp.pi ** 2 / (4 * w * mp.ln2))


def mp_fold(delta, t, m, w, carrier):
    """Direct folding of the modulated kernel: h(d) = sum_{|e|<=m, e=d mod t} g(e + delta)."""
    dl = mpf(delta.numerator) / delta.denominator
    h = [mp.mpc(0)] * t
    for e in range(-m, m + 1):
        s = e + dl
        h[e % t] += mp.expjpi(carrier * s / t) * mp_g0(s, w)
    return h


def check_fold(delta, t, m, w, q, carrier):
    got = folded_kernel(delta, t, m, w, q, carrier)
    assert len(got) == t and all(type(a) is int and type(b) is int for a, b in got)
    with mp.workprec(q + HI):
        for d, z in enumerate(mp_fold(delta, t, m, w, carrier)):
            assert_cr(got[d][0], z.real, q)
            assert_cr(got[d][1], z.imag, q)
    return got


dyadics = st.integers(0, 10).flatmap(
    lambda k: st.integers(0, (1 << k) - 1).map(lambda j: Fraction(j, 1 << k)))
pow2 = st.integers(1, 6).map(lambda k: 1 << k)


# ----------------------------------------------------------------------------------------------
# correctly_rounded, Ziv refinement and the recorded fallback
# ----------------------------------------------------------------------------------------------


@given(st.integers(-10 ** 30, 10 ** 30), st.integers(1, 10 ** 12), st.integers(0, 120))
def test_correctly_rounded_rationals(p, d, q):
    y = Fraction(p, d) * 2 ** (q + 1)
    assume(not (y.denominator == 1 and y.numerator % 2))  # iv results are not exact: no ties
    assert correctly_rounded(lambda prec: iv.mpf(p) / d, q) == from_fraction(Fraction(p, d), q)
    assert correctly_rounded(lambda prec: Fraction(p, d), q) == from_fraction(Fraction(p, d), q)


def test_correctly_rounded_ties_and_exact_points():
    for x, q, n in [(Fraction(5, 2), 0, 2), (Fraction(7, 2), 0, 4), (Fraction(-5, 2), 0, -2),
                    (Fraction(3, 8), 2, 2), (Fraction(1, 8), 2, 0), (Fraction(-3, 8), 2, -2)]:
        assert correctly_rounded(lambda prec: x, q) == n  # exact points decide ties
        assert correctly_rounded(lambda prec: mpf(x.numerator) / x.denominator, q) == n
        assert correctly_rounded(lambda prec: (x.numerator << 3, x.numerator << 3,
                                               3 + x.denominator.bit_length() - 1), q) == n
    assert correctly_rounded(lambda prec: iv.mpf(3) / 4, 0) == 1  # iv point, not a tie


def test_correctly_rounded_transcendental():
    for q in (0, 1, 10, 100, 500):
        with mp.workprec(q + HI):
            assert_cr(correctly_rounded(lambda prec: iv.pi, q), mp.pi, q)
            assert_cr(correctly_rounded(lambda prec: iv.exp(iv.mpf(-7) / 3), q), mp.exp(-mpf(7) / 3), q)


def test_ziv_refines_near_a_tie():
    q, k = 20, 12345
    x = Fraction(2 * k + 1, 1 << (q + 1)) + Fraction(1, 1 << (q + 100))  # just above a tie
    precs = []

    def enc(prec):  # width 2^-prec around x: decidable only once prec > q + 100
        precs.append(prec)
        P = prec + 2
        c = from_fraction(x, P)
        return (c - 4, c + 4, P)
    assert correctly_rounded(enc, q) == k + 1
    assert precs == [q + 64, q + 128]


def test_vector_ziv_keeps_decided_values():
    calls = []

    def enc(prec):
        calls.append(prec)
        P = prec + 4
        hard = Fraction(1, 2) + Fraction(1, 1 << 90)  # needs ~90 bits
        c = from_fraction(hard, P)
        return [(1 << P, 1 << P, P), (c - 2, c + 2, P)]
    assert K._ziv(enc, 0, 2, ("test", ())) == [1, 1]
    assert calls == [64, 128]


def test_forced_fallback_is_faithful_and_recorded():
    q, k = 10, 77
    x0 = Fraction(2 * k + 1, 1 << (q + 1))  # a rounding tie

    def straddle(prec):  # always straddles the tie, width 2^-(prec+7)
        P = prec + 8
        c = from_fraction(x0, P)
        return (c - 1, c + 1, P)
    with pytest.warns(C.CertifiedFallbackWarning):
        n = correctly_rounded(straddle, q)
    assert abs(Fraction(n, 1 << q) - x0) < Fraction(1, 1 << q)
    ev = C.fallback_events()
    assert len(ev) == 1 and ev[0][0] == "correctly_rounded" and ev[0][2] == q
    C.reset_fallback_events()
    assert C.fallback_events() == []
    with pytest.raises(ArithmeticError):  # too wide even at the cap: no certified answer
        correctly_rounded(lambda prec: (-(1 << prec), 1 << prec, prec), q)
    assert C.fallback_events() == []
    assert C.prec_cap(10) == 10 + 4096 and C.prec_cap(1000) == 8000


def test_iv_precision_is_restored():
    old = iv.prec
    iv.prec = 77
    try:
        unit_root(3, 16, 50)
        G_alpha(Fraction(1, 3), 9, 50)
        solver_coeffs(1, 4, 9, 50)
        folded_kernel(Fraction(1, 4), 4, 5, 9, 50)
        a = alpha_iv(20, 300)
        correctly_rounded(lambda prec: iv.pi, 40)
        assert iv.prec == 77
    finally:
        iv.prec = old
    with mp.workprec(400):
        al = 2 * mp.sqrt(20 * mp.ln2 / mp.pi)
        assert a.a <= al <= a.b and a.b - a.a < mp.ldexp(1, -280)


def test_input_validation():
    for bad in [lambda: unit_root(1, 6, 10), lambda: unit_root(1, 8, -1),
                lambda: solver_coeffs(4, 4, 8, 10), lambda: solver_coeffs(0, 3, 8, 10),
                lambda: folded_kernel(Fraction(1, 3), 4, 5, 8, 10),
                lambda: folded_kernel(Fraction(1), 4, 5, 8, 10),
                lambda: folded_kernel(Fraction(1, 2), 6, 5, 8, 10),
                lambda: folded_kernel(Fraction(1, 2), 4, 5, 8, 10, carrier=2),
                lambda: G_alpha(Fraction(1, 2), 0, 10)]:
        with pytest.raises(ValueError):
            bad()


# ----------------------------------------------------------------------------------------------
# unit_root
# ----------------------------------------------------------------------------------------------


def test_unit_root_exact_quarter_turns(monkeypatch):
    monkeypatch.setattr(C, "iv", None)  # exact values must not touch interval arithmetic
    monkeypatch.setattr(K, "iv", None)
    for k in range(0, 21):
        den = 1 << k
        for q in (0, 7, 300):
            one = 1 << q
            for j in range(-9, 9):
                if (j * den) % 4:
                    continue
                exp = [(one, 0), (0, one), (-one, 0), (0, -one)][j % 4]
                assert unit_root(j * den // 4, den, q) == exp


@given(st.integers(-(1 << 50), 1 << 50), st.integers(0, 20), st.integers(0, 300))
def test_unit_root_vs_mpmath(num, k, q):
    den = 1 << k
    c, s = unit_root(num, den, q)
    with mp.workprec(q + HI):
        x = mpf(2 * num) / den
        assert_cr(c, mp.cospi(x), q)
        assert_cr(s, mp.sinpi(x), q)
    assert unit_root(-num, den, q) == (c, -s)
    assert unit_root(num + 3 * den, den, q) == (c, s)


def test_unit_root_tables():
    q = 120
    for r in (2, 8, 64):  # twist roots e^{pi i k/r} (MS §2.2(b))
        with mp.workprec(q + HI):
            for k in range(r):
                c, s = unit_root(k, 2 * r, q)
                assert_cr(c, mp.cospi(mpf(k) / r), q)
                assert_cr(s, mp.sinpi(mpf(k) / r), q)


# ----------------------------------------------------------------------------------------------
# G_alpha and the solver coefficients
# ----------------------------------------------------------------------------------------------


@settings(max_examples=40)
@given(st.integers(-3000, 3000), st.integers(1, 1000), st.integers(8, 2000), st.integers(0, 400))
def test_G_alpha_vs_mpmath(p, d, w, q):
    xi = Fraction(p, d)
    n = G_alpha(xi, w, q)
    with mp.workprec(q + HI):
        assert_cr(n, mp_G(xi, w), q)
    assert G_alpha(-xi, w, q) == n


def test_G_alpha_partition_of_unity_and_endpoints():
    q = 300
    for w in (8, 30, 500):
        for xi in (Fraction(0), Fraction(1, 7), Fraction(1, 2), Fraction(5, 6)):
            tot = sum(G_alpha(xi - k, w, q) for k in range(-4, 5))
            assert abs(tot - (1 << q)) <= 5  # sum_m G(xi - m) = 1 (r2 (4.4)), 9 roundings
        with mp.workprec(q + HI):  # G(1/2) = erf(a)/2 (r2 §4.4)
            assert_cr(G_alpha(Fraction(1, 2), w, q), mp.erf(2 * mp.sqrt(w * mp.ln2)) / 2, q)


def check_solver(u, t, w, q):
    sc = solver_coeffs(u, t, w, q)
    assert isinstance(sc, SolverCoeffs) and all(type(v) is int for v in (sc.c0, sc.c1, sc.mu, sc.a))
    y = Fraction(2 * u + 1, 2 * t)
    with mp.workprec(q + HI):
        c0, c1 = mp_G(y, w), mp_G(y - 1, w)
        M = max(c0, c1)
        assert_cr(sc.c0, c0, q)
        assert_cr(sc.c1, c1, q)
        assert_cr(sc.mu, 1 / M, q)
        assert_cr(sc.a, min(c0, c1) / M, q)
    assert sc.forward == (u < t // 2)
    return sc


@settings(max_examples=40)
@given(st.integers(1, 8), st.data(), st.integers(8, 2000), st.integers(8, 300))
def test_solver_coeffs_vs_mpmath(k, data, w, q):
    t = 1 << k
    check_solver(data.draw(st.integers(0, t - 1)), t, w, q)


@pytest.mark.parametrize("t,w", [(2, 8), (4, 8), (8, 12), (16, 40), (32, 64), (16, 350),
                                 (128, 200)])
def test_dropin_constants(t, w):
    """r2 §8 constants: M > 0.49999999, |c0 - c1| >= 7/(4t) (r3 (4.10)), forward iff u < t/2,
    omitted alias Psi = 1 - c0 - c1 < 0.120 2^-w (erfc form r2 (4.5)); c1(u) = c0(t-1-u);
    the stored ratio obeys r2 (4.16)."""
    q = w + 48
    ulp = Fraction(1, 1 << q)
    res = [check_solver(u, t, w, q) for u in range(t)]
    for u, sc in enumerate(res):
        c0, c1 = sc.c0 * ulp, sc.c1 * ulp
        assert max(c0, c1) - ulp / 2 > Fraction(49999999, 10 ** 8)
        assert abs(c0 - c1) - ulp >= Fraction(7, 4 * t)
        assert sc.forward == (u < t // 2)
        assert 0 < sc.a <= (1 << q) - (1 << q) // (2 * t)  # r2 (4.16): a <= 1 - 1/(2t)
        mirror = res[t - 1 - u]
        assert (sc.c1, sc.mu, sc.a, sc.forward) == (mirror.c0, mirror.mu, mirror.a, not mirror.forward)
        with mp.workprec(q + HI):
            a, y = 2 * mp.sqrt(w * mp.ln2), mpf(2 * u + 1) / (2 * t)
            psi = (mp.erfc(a * (y + mpf(1) / 2)) + mp.erfc(a * (mpf(3) / 2 - y))) / 2
            assert psi < mpf(0.120) * mp.ldexp(1, -w)
            assert abs(1 - mpf(c0.numerator) / c0.denominator
                       - mpf(c1.numerator) / c1.denominator - psi) <= mp.ldexp(1, -q)


# ----------------------------------------------------------------------------------------------
# folded_kernel
# ----------------------------------------------------------------------------------------------


@settings(max_examples=50)
@given(dyadics, pow2, st.integers(0, 40), st.integers(8, 300), st.integers(1, 200),
       st.sampled_from([-1, 0, 1]))
def test_folded_kernel_vs_direct_folding(delta, t, m, w, q, carrier):
    check_fold(delta, t, m, w, q, carrier)


def test_folded_kernel_identity_row(monkeypatch):
    monkeypatch.setattr(C, "iv", None)  # the delta = 0 row is exact: no interval arithmetic
    monkeypatch.setattr(K, "iv", None)
    for t, m, carrier in [(2, 0, -1), (4, 3, 0), (16, 40, 1), (128, 7, -1)]:
        for q in (0, 9, 400):
            assert folded_kernel(Fraction(0), t, m, 50, q, carrier) == [(1 << q, 0)] + [(0, 0)] * (t - 1)


def test_folded_kernel_carrier_zero_real_and_conjugate_symmetry():
    for delta, t, m, w, q in [(Fraction(1, 2), 4, 30, 8, 80), (Fraction(3, 32), 64, 50, 100, 150),
                              (Fraction(7, 8), 2, 12, 20, 60)]:
        assert all(im == 0 for _, im in check_fold(delta, t, m, w, q, 0))
        neg = folded_kernel(delta, t, m, w, q, -1)
        pos = folded_kernel(delta, t, m, w, q, 1)
        assert pos == [(re, -im) for re, im in neg]


def test_folded_kernel_empty_classes_exact_zero():
    got = check_fold(Fraction(1, 4), 64, 5, 30, 100, -1)  # t > 2m + 1
    for d in range(6, 64 - 5):
        assert got[d] == (0, 0)


@pytest.mark.parametrize("delta,t,m,w,q", [
    (Fraction(5, 16), 128, 400, 200, 400),   # representative 2D sizes
    (Fraction(1, 16), 16, 300, 350, 350),
    (Fraction(3, 4), 64, 500, 2000, 600),    # largest w, q, m in scope: no taps skipped
    (Fraction(1, 1024), 8, 200, 100, 300),   # tiny delta: sinc(delta)/delta cancellation
    (Fraction(3, 8), 128, 150, 200, 400),    # skipped taps hit only some residue classes
    (Fraction(4095, 4096), 2, 60, 30, 200),  # delta near 1: sin(pi delta), cos(pi delta/2) small
])
def test_folded_kernel_realistic_sizes(delta, t, m, w, q):
    check_fold(delta, t, m, w, q, -1)


@pytest.mark.parametrize("t", [2, 4])
def test_folding_sign_check(t):
    """r1 §10.5: direct folding of e^{-pi i s/t} g0(s) == formula r1 (4.3); periodizing g0 first
    and multiplying by the carrier afterwards is wrong."""
    delta, m, w, q = Fraction(1, 2), 50, 8, 60
    got = check_fold(delta, t, m, w, q, -1)  # agrees with direct folding
    with mp.workprec(q + HI):
        dl, wrong_by = mpf(1) / 2, mpf(0)
        for a in range(t):
            alt = sum((-1) ** abs(l) * mp_g0(a + dl - l * t, w)
                      for l in range(-m, m + 1) if abs(a - l * t) <= m)
            per = sum(mp_g0(a + dl - l * t, w) for l in range(-m, m + 1) if abs(a - l * t) <= m)
            ph = mp.expjpi(-(a + dl) / t)
            assert_cr(got[a][0], (ph * alt).real, q)  # r1 (4.3)
            assert_cr(got[a][1], (ph * alt).imag, q)
            wrong_by = max(wrong_by, abs(ph * per - mpf(got[a][0]) / 2 ** q - 1j * mpf(got[a][1]) / 2 ** q))
        assert wrong_by > mpf(1) / 100


@pytest.mark.parametrize("delta,t,w,q", [(Fraction(1, 2), 4, 8, 60), (Fraction(3, 8), 8, 12, 80),
                                         (Fraction(1, 16), 16, 30, 100), (Fraction(5, 8), 2, 9, 60)])
def test_poisson_multipliers(delta, t, w, q):
    """r2 (4.22): the unnormalized DFT of the untruncated folded kernel has modulus <= 1; more
    precisely sum_a H(a) e^{-2 pi i a u/t} = sum_mu G((u+1/2)/t - mu) e^{2 pi i delta (u/t - mu)},
    whose mu = 0, 1 terms carry exactly the solver coefficients c0, c1 (r2 (8.2))."""
    with mp.workprec(q + HI):
        al = 2 * mp.sqrt(w * mp.ln2 / mp.pi)
        m = int(mp.ceil(al * mp.sqrt((q + 20) * mp.ln2 / mp.pi))) + 2  # tail < 2^-(q+20)
    H = folded_kernel(delta, t, m, w, q, -1)
    ulp = Fraction(1, 1 << q)
    with mp.workprec(q + HI):
        dl = mpf(delta.numerator) / delta.denominator
        Hmp = mp_fold(delta, t, m, w, -1)
        for u in range(t):
            dft = sum((mpf(re) + 1j * mpf(im)) / 2 ** q * mp.expjpi(-2 * mpf(a * u) / t)
                      for a, (re, im) in enumerate(H))
            dft_hp = sum(Hmp[a] * mp.expjpi(-2 * mpf(a * u) / t) for a in range(t))
            assert abs(dft_hp) <= 1 + mp.ldexp(1, -q - 10)
            assert abs(dft) <= 1 + t * mpf(ulp.numerator) / ulp.denominator
            sc = solver_coeffs(u, t, w, q)
            two = (mpf(sc.c0) + mpf(sc.c1) * mp.expjpi(-2 * dl)) / 2 ** q * mp.expjpi(2 * dl * u / t)
            assert abs(dft - two) <= mpf(0.120) * mp.ldexp(1, -w) + (t + 2) * mp.ldexp(1, -q)
            full = sum(mp_G(Fraction(2 * u + 1, 2 * t) - k, w) * mp.expjpi(2 * dl * (mpf(u) / t - k))
                       for k in range(-4, 6))
            assert abs(dft_hp - full) <= mp.ldexp(1, -q - 10)


# ----------------------------------------------------------------------------------------------
# internals: the erf enclosure
# ----------------------------------------------------------------------------------------------


@settings(max_examples=80)
@given(st.integers(20, 700), st.data())
def test_erf_point_enclosure(P, data):
    """_erf_point encloses erf(X 2^-P) tightly, across the series and the large-argument regime."""
    zmax = int(ceil(1.2 * (0.6932 * (P + 2)) ** 0.5)) + 1
    X = data.draw(st.integers(0, zmax << P))
    lo, hi = K._erf_point(X, P)
    with mp.workprec(P + HI):
        e = mp.erf(mp.ldexp(X, -P)) * mp.ldexp(1, P)
        assert lo <= e <= hi
    assert hi - lo <= 8


# ----------------------------------------------------------------------------------------------
# internals: every enclosure contains the exact value (rigor, independent of the rounding test)
# ----------------------------------------------------------------------------------------------


def assert_contains(encl, x, width_bits=None):
    lo, hi, P = encl
    X = mp.ldexp(x, P)
    assert lo <= X <= hi
    if width_bits is not None:
        assert hi - lo <= 1 << width_bits


@settings(max_examples=40)
@given(dyadics.filter(bool), pow2, st.integers(0, 60), st.integers(8, 400), st.integers(20, 200),
       st.sampled_from([-1, 0, 1]), st.booleans())
def test_fold_enclosure_contains_exact_value(delta, t, m, w, prec, carrier, early):
    """With ``early`` the tap cutoff is forced at tail <= 2^-(prec/3): the geometric tail bound
    (and its per-class bookkeeping) must still enclose the exact truncated folded sum."""
    encl = C._fold_enclosure(delta, t, m, w, carrier, prec, prec // 3 if early else None)
    P = encl[0][2]
    with mp.workprec(P + 100):
        for d, z in enumerate(mp_fold(delta, t, m, w, carrier)):
            assert_contains(encl[2 * d], z.real, None if early else P - prec)
            assert_contains(encl[2 * d + 1], z.imag, None if early else P - prec)


@pytest.mark.parametrize("t,m", [(8, 60), (128, 20), (16, 37)])
def test_fold_enclosure_forced_tail(t, m):
    """Deterministic forced-cutoff cases: skipped taps cover all classes (t=8) or only some."""
    delta, w, prec = Fraction(1, 2), 8, 100
    encl = C._fold_enclosure(delta, t, m, w, -1, prec, 30)
    full = C._fold_enclosure(delta, t, m, w, -1, prec)
    P = encl[0][2]
    with mp.workprec(P + 100):
        for d, z in enumerate(mp_fold(delta, t, m, w, -1)):
            assert_contains(encl[2 * d], z.real)
            assert_contains(encl[2 * d + 1], z.imag)
    assert any(e[1] - e[0] > f[1] - f[0] for e, f in zip(encl, full))  # the cutoff was taken


@settings(max_examples=40)
@given(st.integers(-3000, 3000), st.integers(1, 1000), st.integers(8, 2000), st.integers(10, 300))
def test_G_enclosure_contains_exact_value(p, d, w, prec):
    encl = C._G_enclosure(Fraction(p, d), w, prec)
    with mp.workprec(encl[2] + 100):
        assert_contains(encl, mp_G(Fraction(p, d), w), encl[2] - prec)


@settings(max_examples=30)
@given(st.integers(1, 8), st.data(), st.integers(8, 2000), st.integers(10, 300))
def test_solver_enclosure_contains_exact_values(k, data, w, prec):
    t = 1 << k
    u = data.draw(st.integers(0, t - 1))
    fwd, encl = C._solver_enclosure(u, t, w, prec)
    assert fwd == (u < t // 2)
    y = Fraction(2 * u + 1, 2 * t)
    with mp.workprec(encl[0][2] + 100):
        c0, c1 = mp_G(y, w), mp_G(y - 1, w)
        M = max(c0, c1)
        for e, x in zip(encl, (c0, c1, 1 / M, min(c0, c1) / M)):
            assert_contains(e, x, e[2] - prec + 2)


# ----------------------------------------------------------------------------------------------
# mpmath's iv.exp is accurate but not strictly outward-rounded (regression for the widening)
# ----------------------------------------------------------------------------------------------


@pytest.mark.parametrize("k,prec", [(-91, 45), (-384, 87), (-384, 88)])
def test_widening_covers_mpmath_exp_misses(k, prec):
    """libmpi.mpi_exp rounds a prec + 14 bit approximation in the requested direction, so for these
    (found by search) the raw interval iv.exp(k/64) misses the true value by one ulp.  The widened
    primitive certcore._exp and the widened grid conversion certcore._iv_dyadic both contain it."""
    old = iv.prec
    try:
        iv.prec = prec
        x = iv.mpf(k) / 64
        raw, wide = iv.exp(x), K._exp(x)
    finally:
        iv.prec = old
    with mp.workprec(prec + HI):
        e = mp.exp(mpf(k) / 64)
        if mpmath.__version__ == "1.3.0":
            assert not raw.a <= e <= raw.b  # the documented mpmath behaviour (pinned version)
        assert wide.a <= e <= wide.b
        for P in (prec - 16, prec, prec + 8):
            for I in (raw, wide):
                lo, hi = K._iv_dyadic(I, P, prec)
                assert lo <= mp.ldexp(e, P) <= hi


def test_widened_constants_and_slack():
    """Widened pi, ln 2 contain the true constants with ~2^11 relative ulps of margin, and the
    conversion slack is at least one unit and 2^10 ulps at the endpoint's magnitude."""
    old = iv.prec
    try:
        for prec in (30, 64, 200, 1000):
            iv.prec = prec
            for I, ref in ((K._pi(), mp.pi), (K._ln2(), mp.ln2)):
                with mp.workprec(prec + HI):
                    v = ref()
                    assert I.a <= v <= I.b
                    assert v - I.a > mp.ldexp(v, 9 - prec) and I.b - v > mp.ldexp(v, 9 - prec)
    finally:
        iv.prec = old
    one = (0, 1, 0, 1)  # the mpf 1.0
    assert K._slack(one, 100, 116) == 1 and K._slack(one, 100, 100) == 1 << 12
    assert K._slack((0, 0, 0, 0), 50, 60) == 1
