"""Tests for subnlogn.fixedpoint (manuscript Def. 2.1, eq. (quant-err), §2.1 primitives)."""

from fractions import Fraction

from hypothesis import given, strategies as st

from subnlogn.fixedpoint import (
    Rounding, shr_half_even, shr_half_up, shr_trunc, div_half_even, div_half_up, div_trunc,
    cmul, rcmul, csquare, rd, rm, to_fraction, from_fraction, QUANT_COMPLEX_UP, FxVec,
    sup_norm_sq,
)

ints = st.integers(min_value=-(1 << 300), max_value=1 << 300)
shifts = st.integers(min_value=0, max_value=200)


def nearest_set(x: Fraction) -> set[int]:
    """All integers at minimal distance from x."""
    f = x.numerator // x.denominator
    cands = [f - 1, f, f + 1, f + 2]
    dmin = min(abs(Fraction(c) - x) for c in cands)
    return {c for c in cands if abs(Fraction(c) - x) == dmin}


@given(ints, shifts)
def test_shr_half_even_is_nearest_ties_even(n, s):
    x = Fraction(n, 1 << s)
    got = shr_half_even(n, s)
    ns = nearest_set(x)
    assert got in ns
    if len(ns) == 2:
        assert got % 2 == 0


@given(ints, shifts)
def test_shr_half_up(n, s):
    x = Fraction(n, 1 << s)
    got = shr_half_up(n, s)
    assert got in nearest_set(x)
    if len(nearest_set(x)) == 2:
        assert got == max(nearest_set(x))


@given(ints, shifts)
def test_shr_trunc(n, s):
    x = Fraction(n, 1 << s)
    got = shr_trunc(n, s)
    assert abs(Fraction(got)) <= abs(x) < abs(Fraction(got)) + 1


@given(ints, st.integers(min_value=-(1 << 200), max_value=1 << 200).filter(lambda d: d != 0))
def test_divisions(num, den):
    x = Fraction(num, den)
    assert div_half_even(num, den) in nearest_set(x)
    ns = nearest_set(x)
    if len(ns) == 2:
        assert div_half_even(num, den) % 2 == 0
        assert div_half_up(num, den) == max(ns)
    else:
        assert div_half_up(num, den) in ns
    t = div_trunc(num, den)
    assert abs(Fraction(t)) <= abs(x) < abs(Fraction(t)) + 1


def test_negative_shift_is_exact():
    assert shr_half_even(5, -3) == 40
    assert shr_half_up(-5, -2) == -20
    assert shr_trunc(-5, 0) == -5


@given(ints, ints, ints, ints, st.integers(min_value=0, max_value=120))
def test_cmul_error_bound(ar, ai, br, bi, q):
    """|RM_q(a,b) - ab| <= sqrt(2)/2 2^-q (eq. quant-err)."""
    cr, ci = cmul(ar, ai, br, bi, q)
    exact_r = Fraction(ar * br - ai * bi, 1 << (2 * q))
    exact_i = Fraction(ar * bi + ai * br, 1 << (2 * q))
    er = to_fraction(cr, q) - exact_r
    ei = to_fraction(ci, q) - exact_i
    assert abs(er) <= Fraction(1, 2) / (1 << q)
    assert abs(ei) <= Fraction(1, 2) / (1 << q)
    assert er * er + ei * ei <= (QUANT_COMPLEX_UP / (1 << q)) ** 2


@given(ints, ints, ints, st.integers(min_value=0, max_value=120))
def test_rcmul_and_csquare(a, br, bi, q):
    cr, ci = rcmul(a, br, bi, q)
    assert abs(to_fraction(cr, q) - Fraction(a * br, 1 << (2 * q))) <= Fraction(1, 2 << q)
    assert abs(to_fraction(ci, q) - Fraction(a * bi, 1 << (2 * q))) <= Fraction(1, 2 << q)
    sr, si = csquare(br, bi, q)
    assert (sr, si) == cmul(br, bi, br, bi, q)
    assert rm(a, br, q) == shr_half_even(a * br, q)


@given(ints, st.integers(min_value=1, max_value=1 << 100), st.integers(min_value=0, max_value=100))
def test_rd(z, d, q):
    got = rd(z, d, q)
    exact = Fraction(z, d)  # (z 2^-q) / (d 2^-q)
    assert abs(to_fraction(got, q) - exact) <= Fraction(1, 2 << q)


@given(st.fractions(), st.integers(min_value=0, max_value=80))
def test_from_fraction(x, q):
    n = from_fraction(x, q)
    assert abs(to_fraction(n, q) - x) <= Fraction(1, 2 << q)


def test_rounding_enum_dispatch():
    assert Rounding.HALF_EVEN.shr(3, 1) == 2   # 1.5 -> 2 (even)
    assert Rounding.HALF_EVEN.shr(5, 1) == 2   # 2.5 -> 2 (even)
    assert Rounding.HALF_UP.shr(5, 1) == 3
    assert Rounding.HALF_UP.shr(-5, 1) == -2   # -2.5 -> -2 (toward +inf)
    assert Rounding.TRUNC.shr(-5, 1) == -2
    assert Rounding.HALF_EVEN.div(7, 2) == 4


def test_fxvec_roundtrip():
    v = FxVec([1, -3, 8], [0, 5, -7], 4)
    w = v.rescaled(6)
    assert w.re == [4, -12, 32] and w.q == 6
    assert w.rescaled(4) == v
    assert v.max_coord_bits() == 4
    assert v.sup_norm_sq() == sup_norm_sq(v.re, v.im, 4) == Fraction(64 + 49, 256)
