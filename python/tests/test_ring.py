"""Tests for subnlogn.ring: monomial shifts (SPEC §5.4; Pr L3000-3005) and Lemma 17 (SPEC §5.5-§5.6;
Pr L3047-3220): streaming signed packing, centered extraction and the normalized ring product,
compared with exact oracles (Python-int evaluation Σ u_j 2^{4pj}, naive negacyclic Gaussian-integer
product followed by truncation toward zero)."""

import operator
from math import isqrt

import pytest
from hypothesis import given, settings, strategies as st

from subnlogn.fixedpoint import shr_trunc
from subnlogn.ring import (
    centered_extract, in_disk, monomial_shift, normalized_ring_product, pack_blocks, pack_to_int,
)

# ----------------------------------------------------------------------------------------------
# oracles (tests only)
# ----------------------------------------------------------------------------------------------


def negacyclic(f, g):
    """Exact product in Z[i][y]/(y^r + 1) (naive O(r^2))."""
    r = len(f)
    H = [[0, 0] for _ in range(r)]
    for j1, (a, b) in enumerate(f):
        for j2, (c, e) in enumerate(g):
            j, sgn = j1 + j2, 1
            if j >= r:
                j, sgn = j - r, -1
            H[j][0] += sgn * (a * c - b * e)
            H[j][1] += sgn * (a * e + b * c)
    return [tuple(z) for z in H]


def oracle_product(f, g, p):
    """Q_p(f g / r): truncation toward zero of the exact numerators H_j / 2^{p + l}."""
    l = len(f).bit_length() - 1
    return [(shr_trunc(x, p + l), shr_trunc(y, p + l)) for x, y in negacyclic(f, g)]


def naive_monomial(z, E):
    """y^E z by multiplying with the monomial (-1)^floor(E/r) y^(E mod r)."""
    r = len(z)
    mono = [(0, 0)] * r
    mono[E % r] = (-1 if (E // r) % 2 else 1, 0)
    return negacyclic(mono, z)


def disk_point(p):
    """Strategy for a numerator pair on the disk grid 2^-p."""
    lim = 1 << p
    return st.integers(-lim, lim).flatmap(
        lambda a: st.integers(-isqrt(lim * lim - a * a), isqrt(lim * lim - a * a)).map(lambda b: (a, b)))


# ----------------------------------------------------------------------------------------------
# monomial shift
# ----------------------------------------------------------------------------------------------


@pytest.mark.parametrize("r", [1, 2, 4, 8, 16])
def test_monomial_shift_all_exponents(r):
    z = [(3 * k + 1, -(k * k) - 2) for k in range(r)]
    for E in list(range(-3 * r, 3 * r + 1)) + [r, 2 * r - 1, -r, -(2 * r - 1), 10 ** 9 + 7, -10 ** 9]:
        got = monomial_shift(z, E)
        assert got == naive_monomial(z, E)
        assert sorted(max(abs(a), abs(b)) for a, b in got) == sorted(max(abs(a), abs(b)) for a, b in z)
    assert monomial_shift(z, r) == [(-a, -b) for a, b in z]
    assert monomial_shift(z, 2 * r) == z and monomial_shift(z, 0) == z


@given(st.integers(0, 6), st.data())
def test_monomial_shift_group_law_and_isometry(l, data):
    r = 1 << l
    z = data.draw(st.lists(st.tuples(st.integers(-10 ** 6, 10 ** 6), st.integers(-10 ** 6, 10 ** 6)),
                           min_size=r, max_size=r))
    E1, E2 = data.draw(st.integers(-10 ** 6, 10 ** 6)), data.draw(st.integers(-10 ** 6, 10 ** 6))
    assert monomial_shift(monomial_shift(z, E1), E2) == monomial_shift(z, E1 + E2)
    assert monomial_shift(monomial_shift(z, E1), -E1) == z
    w = monomial_shift(z, E1)
    assert max(a * a + b * b for a, b in w) == max(a * a + b * b for a, b in z)  # isometry
    assert w == naive_monomial(z, E1)


# ----------------------------------------------------------------------------------------------
# Lemma 17: packing and extraction
# ----------------------------------------------------------------------------------------------


@given(st.integers(2, 64), st.integers(1, 40), st.data())
def test_pack_blocks_and_pack_to_int(p, n, data):
    lim = 1 << p
    u = data.draw(st.lists(st.integers(-lim, lim), min_size=n, max_size=n))
    oracle = sum(uj << (4 * p * j) for j, uj in enumerate(u))
    blocks, g = pack_blocks(u, p)
    B0 = 1 << (4 * p)
    assert all(0 <= d < B0 for d in blocks) and g in (-1, 0)
    assert sum(d << (4 * p * j) for j, d in enumerate(blocks)) + g * (B0 ** n) == oracle
    assert (g == -1) == (oracle < 0)
    assert pack_to_int(u, p) == oracle


def test_pack_extremes():
    p = 5
    lim = 1 << p
    for u in ([lim] * 7, [-lim] * 7, [0] * 7, [-lim] + [0] * 6, [0] * 6 + [-1], [lim, -lim] * 4,
              [-1] * 7, [1] + [-lim] * 6):
        oracle = sum(uj << (4 * p * j) for j, uj in enumerate(u))
        assert pack_to_int(u, p) == oracle
    with pytest.raises(AssertionError):
        pack_blocks([lim + 1], p)


@given(st.integers(1, 40), st.integers(1, 30), st.data())
def test_centered_extract_roundtrip(p, J, data):
    """Centred digits in [-B0/2, B0/2), top digit |h_{J-1}| < B0/4 so that |Z| < B0^J/2 fits in J
    signed blocks (the lemma pads h_{J-1} = 0 and has |h_j| <= 2^{3p}, Pr L3126-3128, (31))."""
    half = 1 << (4 * p - 1)
    h = data.draw(st.lists(st.integers(-half, half - 1), min_size=J - 1, max_size=J - 1))
    h.append(data.draw(st.integers(-(half >> 1) + 1, (half >> 1) - 1)))
    Z = sum(hj << (4 * p * j) for j, hj in enumerate(h))
    assert centered_extract(Z, J, p) == h


def test_centered_extract_negative_and_carry_cases():
    p, J = 3, 6
    half = 1 << (4 * p - 1)
    for h in ([-1, 0, 0, 0, 0, 0], [0] * 5 + [-1], [-half] * (J - 1) + [0], [half - 1] * (J - 1) + [0],
              [-half, half - 1] * 2 + [-half, 0], [0] * J, [5, -7, 0, 0, -half, 0],
              [-half] * (J - 1) + [-(half >> 1) + 1], [half - 1] * (J - 1) + [(half >> 1) - 1]):
        Z = sum(hj << (4 * p * j) for j, hj in enumerate(h))
        assert centered_extract(Z, J, p) == h
    with pytest.raises(AssertionError):  # does not fit in J signed blocks
        centered_extract(1 << (4 * p * J - 1), J, p)


# ----------------------------------------------------------------------------------------------
# Lemma 17: normalized ring product
# ----------------------------------------------------------------------------------------------


def check_product(f, g, p):
    r = len(f)
    calls = []

    def counting_mul(x, y):
        assert x >= 0 and y >= 0  # absolute values go to the independent multiplier
        calls.append((x, y))
        return x * y
    got = normalized_ring_product(f, g, p, r, counting_mul)
    assert got == oracle_product(f, g, p)
    assert len(calls) == 4
    assert all(in_disk(a, b, p) for a, b in got)
    return got


@pytest.mark.parametrize("l", [1, 2, 3, 4, 6])
def test_normalized_product_extremes(l):
    r = 1 << l
    for p in (l + 1, 20, 64):
        one = 1 << p
        cases = [
            ([(one, 0)] * r, [(one, 0)] * r),
            ([(-one, 0)] * r, [(one, 0)] * r),
            ([(0, one)] * r, [(0, -one)] * r),
            ([(-one, 0)] * r, [(0, -one)] * r),                              # all-negative
            ([(0, 0)] * r, [(one, 0)] * r),                                  # zeros
            ([((-1) ** k * one, 0) for k in range(r)], [(0, (-1) ** (k // 2) * one) for k in range(r)]),
            ([(0, 0)] * (r - 1) + [(-one, 0)], [(0, 0)] * (r - 1) + [(0, -one)]),  # negative tops
            ([(-(isqrt(one * one // 2)), -(isqrt(one * one // 2)))] * r, [(one, 0)] + [(0, 0)] * (r - 1)),
        ]
        for f, g in cases:
            check_product(f, g, p)


@settings(max_examples=60)
@given(st.sampled_from([1, 2, 3, 4, 6]), st.data())
def test_normalized_product_random(l, data):
    r = 1 << l
    p = data.draw(st.sampled_from([l + 1, 20, 64]))
    f = data.draw(st.lists(disk_point(p), min_size=r, max_size=r))
    g = data.draw(st.lists(disk_point(p), min_size=r, max_size=r))
    check_product(f, g, p)


@settings(max_examples=40)
@given(st.integers(1, 5), st.data())
def test_normalized_product_any_precision(l, data):
    r = 1 << l
    p = data.draw(st.integers(l + 1, 90))
    f = data.draw(st.lists(disk_point(p), min_size=r, max_size=r))
    g = data.draw(st.lists(disk_point(p), min_size=r, max_size=r))
    got = check_product(f, g, p)
    # contraction: ||Q_p(fg/r)|| <= ||f|| ||g|| (Pr L3189-3191), here in squared numerators
    nf, ng = max(a * a + b * b for a, b in f), max(a * a + b * b for a, b in g)
    assert max(a * a + b * b for a, b in got) << (4 * p) <= nf * ng << (2 * p) or nf * ng == 0


def test_normalized_product_hypotheses_asserted():
    one = 1 << 4
    ok = [(one, 0)] * 4
    with pytest.raises(AssertionError):
        normalized_ring_product(ok, ok, 2, 4)  # l = 2 is not < p = 2
    with pytest.raises(AssertionError):
        normalized_ring_product([(one, 1)] + ok[1:], ok, 4, 4)  # off the disk
    with pytest.raises(AssertionError):
        normalized_ring_product(ok[:3], ok[:3], 4, 3)  # r not a power of two
    with pytest.raises(AssertionError):
        normalized_ring_product([(1, 0)], [(1, 0)], 4, 1)  # l = 0
    assert normalized_ring_product(ok, ok, 4, 4, operator.mul) == oracle_product(ok, ok, 4)
