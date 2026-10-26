"""Tests for subnlogn.bridge.geometry: the exact index geometry of the d-dimensional bridge.

Sources: r2 = bridge derivation r2 (Thm 1, §3.1-§3.4, §4.5), r3 = bridge derivation r3
(§2.1, §3.1-§3.4), MS = the companion manuscript [MS] (thm:poisson, listing l.737-738).
"""

import ast
import dataclasses
import itertools
import math
import pathlib
from fractions import Fraction

import pytest
from hypothesis import given, strategies as st

from subnlogn.bridge import geometry as geometry_module
from subnlogn.bridge.geometry import BridgeGeometry, balanced_factors
from subnlogn.schedule import split_2d


@st.composite
def geometries(draw, max_d=5, max_K=12):
    """Random small geometries, d = 1..max_d, each t_i in {2, 4, 8, 16}, R <= 2^max_K."""
    d = draw(st.integers(1, max_d))
    budget = max_K - d
    exps = []
    for _ in range(d):
        extra = draw(st.integers(0, min(3, budget)))
        budget -= extra
        exps.append(1 + extra)
    return BridgeGeometry(tuple(1 << e for e in exps))


@st.composite
def geom_and_index(draw, max_K=12):
    g = draw(geometries(max_K=max_K))
    return g, draw(st.integers(0, g.R - 1))


@st.composite
def geom_axis_index(draw, max_K=12):
    """A geometry with d >= 2, an axis h in 2..d and an index k."""
    g = draw(geometries(max_K=max_K).filter(lambda g: g.d >= 2))
    return g, draw(st.integers(2, g.d)), draw(st.integers(0, g.R - 1))


SMALL = [(2,), (8,), (2, 2), (2, 4), (4, 2), (8, 4), (2, 2, 2), (2, 4, 8), (8, 2, 4), (4, 4, 4),
         (2, 2, 2, 2), (2, 8, 2, 4), (2, 2, 2, 2, 2), (4, 2, 2, 2, 2), (2, 2, 2, 2, 16)]


# ------------------------------------------------------------------------------------ place values
@given(geometries())
def test_place_values(g):
    """r2 Thm 1 / r3 §2.1: A_1 = 1, A_{h+1} = A_h t_h, A_{d+1} = R = 2^K, Q_h = R/(A_h t_h),
    Q_d = 1, q_h = R/A_h, Q_h = q_{h+1}."""
    assert g.d == len(g.t) and g.R == math.prod(g.t) == 1 << g.K
    assert g.A(1) == 1 and g.A(g.d + 1) == g.R
    for h in range(1, g.d + 1):
        assert g.tt(h) == g.t[h - 1]
        assert g.A(h + 1) == g.A(h) * g.tt(h)
        assert g.Q(h) * g.A(h) * g.tt(h) == g.R
        assert g.q(h) * g.A(h) == g.R
        assert g.Q(h) == g.q(h + 1)
    assert g.Q(g.d) == 1 and g.q(1) == g.R and g.q(g.d + 1) == 1
    for v in [g.d, g.R, g.K] + [g.A(h) for h in range(1, g.d + 2)]:
        assert type(v) is int


# ------------------------------------------------------------------------------ digit bijections
@pytest.mark.parametrize("t", SMALL)
def test_digits_index_bijection_exhaustive(t):
    """j = sum_i j_i A_i with j_1 least significant (r2 §3.1); numerical order is the lexicographic
    order of (j_d, ..., j_1) (r3 §3.1)."""
    g = BridgeGeometry(t)
    all_digits = [g.digits(j) for j in range(g.R)]
    assert all(g.index(c) == j for j, c in enumerate(all_digits))
    assert len(set(all_digits)) == g.R
    assert all(0 <= ci < ti for c in all_digits for ci, ti in zip(c, g.t))
    assert all_digits == sorted(all_digits, key=lambda c: c[::-1])
    for c in itertools.product(*[range(ti) for ti in g.t]):
        assert g.digits(g.index(c)) == c


@pytest.mark.parametrize("t", SMALL)
def test_phi_bijection_exhaustive(t):
    """Phi(u) = sum u_i Q_i is a bijection onto 0..R-1, u_d least significant; numerical frequency
    order is the lexicographic order of (u_1, ..., u_d) (r2 §3.2 after (3.7); r3 (3.2))."""
    g = BridgeGeometry(t)
    us = list(itertools.product(*[range(ti) for ti in g.t]))     # lexicographic in (u_1..u_d)
    assert [g.phi(u) for u in us] == list(range(g.R))
    for k in range(g.R):
        u = g.phi_inv(k)
        assert g.phi(u) == k
        assert u == tuple(g.u_digit(h, k) for h in range(1, g.d + 1))


@given(geom_and_index())
def test_phi_and_digits_roundtrip(gk):
    g, k = gk
    assert g.phi(g.phi_inv(k)) == k and g.index(g.digits(k)) == k
    assert g.phi_inv(g.phi(g.digits(k))) == g.digits(k)
    assert sum(ui * g.Q(i + 1) for i, ui in enumerate(g.phi_inv(k))) == k


# ------------------------------------------------------------------------------ fractional shifts
@given(geom_axis_index())
def test_delta_definition_and_congruences(ghk):
    """delta_h(j) = (sum_{i<h} j_i A_i)/A_h (r2 §3.1) satisfies r2 (3.5): j/(A_h t_h) = (j_h+delta_h)/t_h
    and j/A_h = delta_h (mod 1), and r3 §3.2: j_h + delta_h = j/A_h - t_h floor(j/A_{h+1})."""
    g, h, j = ghk
    jd = g.digits(j)
    dl = g.delta(h, j)
    assert isinstance(dl, Fraction)
    assert dl == Fraction(sum(jd[i] * g.A(i + 1) for i in range(h - 1)), g.A(h))
    assert 0 <= dl < 1
    jh, Ah, th = jd[h - 1], g.A(h), g.tt(h)
    assert (Fraction(j, Ah * th) - (jh + dl) / th).denominator == 1
    assert (Fraction(j, Ah) - dl).denominator == 1
    assert jh + dl == Fraction(j, Ah) - th * (j // g.A(h + 1))
    # only the lower digits matter: changing digits >= h leaves delta_h unchanged
    other = list(jd)
    for i in range(h - 1, g.d):
        other[i] = (other[i] + 1) % g.t[i]
    assert g.delta(h, g.index(other)) == dl


@given(geom_and_index(max_K=10), st.data())
def test_lemma_A_phase_identity(gj, data):
    """The exact phase computation of Lemma A (r2 (3.4)-(3.6), r3 §3.2): for all j, u and integer m_h,
    j_1 u_1/t_1 + sum_{h>=2} (j_h + delta_h)(u_h/t_h - m_h) = j (Phi(u) - sum_h m_h q_h) / R  (mod 1)."""
    g, j = gj
    u = tuple(data.draw(st.integers(0, ti - 1)) for ti in g.t)
    m = {h: data.draw(st.integers(-4, 4)) for h in range(2, g.d + 1)}
    jd = g.digits(j)
    lhs = Fraction(jd[0] * u[0], g.t[0])
    for h in range(2, g.d + 1):
        lhs += (jd[h - 1] + g.delta(h, j)) * (Fraction(u[h - 1], g.tt(h)) - m[h])
    rhs = Fraction(j * (g.phi(u) - sum(m[h] * g.q(h) for h in m)), g.R)
    assert (lhs - rhs).denominator == 1


# ------------------------------------------------------------------------------ alias shifts
@given(geom_axis_index(), st.integers(-9, 9))
def test_alias_shift_changes_only_lower_digits(ghk, m):
    """r2 (3.8) / r3 §3.3: subtracting m q_h leaves u_h, ..., u_d unchanged and changes only digits
    u_i with i < h; the high part V = (k - k mod q_h)/q_h (the digits u_1..u_{h-1}, u_{h-1} least
    significant) moves to V - m mod A_h."""
    g, h, k = ghk
    k2 = (k - m * g.q(h)) % g.R
    u, u2 = g.phi_inv(k), g.phi_inv(k2)
    assert u2[h - 1:] == u[h - 1:]
    assert k2 % g.q(h) == k % g.q(h)
    assert k2 // g.q(h) == (k // g.q(h) - m) % g.A(h)
    V = 0
    for i in range(h - 1):
        V = V * g.t[i] + u[i]
    assert V == k // g.q(h)


@given(geom_axis_index())
def test_higher_shift_can_change_u_h(ghk):
    """Converse used in r2 §3.3 ("a shift from A_{h+1} can change u_h"): for h < d, subtracting
    q_{h+1} = Q_h decrements u_h (mod t_h)."""
    g, h, k = ghk
    if h == g.d:
        return
    k2 = (k - g.q(h + 1)) % g.R
    assert g.u_digit(h, k2) == (g.u_digit(h, k) - 1) % g.tt(h)


# ------------------------------------------------------------------------------ cycles and lines
@pytest.mark.parametrize("t", SMALL)
def test_cycles(t):
    """Cycles of B_h (r2 §4.5, spec §7.7): k = v q_h + s; length A_h (even for h >= 2); the
    predecessor of v is v - 1 (mod A_h), i.e. k - q_h mod R; u_h..u_d are constant on each cycle and
    the cycles are exactly the classes of k mod q_h."""
    g = BridgeGeometry(t)
    for h in range(1, g.d + 1):
        cyc = g.cycles(h)
        assert len(cyc) == g.q(h)
        assert sorted(k for c in cyc for k in c) == list(range(g.R))
        for s, c in enumerate(cyc):
            assert len(c) == g.A(h)
            if h >= 2:
                assert len(c) % 2 == 0
            for v, k in enumerate(c):
                assert k % g.q(h) == s and k // g.q(h) == v
                assert (k - g.q(h)) % g.R == c[v - 1]
            tails = {g.phi_inv(k)[h - 1:] for k in c}
            assert len(tails) == 1
            assert len({g.u_digit(h, k) for k in c}) == 1


@pytest.mark.parametrize("t", SMALL)
def test_line_indices(t):
    """Storage lines along axis h (r2 §3.1, r3 §3.1): partition of 0..R-1 into R/t_h lines of t_h
    entries; along a line only digit c_h changes, taking the values 0..t_h-1 in order."""
    g = BridgeGeometry(t)
    for h in range(1, g.d + 1):
        lines = g.line_indices(h)
        assert len(lines) == g.R // g.tt(h)
        assert sorted(k for ln in lines for k in ln) == list(range(g.R))
        bases = [ln[0] for ln in lines]
        assert bases == sorted(bases)
        for ln in lines:
            assert len(ln) == g.tt(h)
            base = g.digits(ln[0])
            assert base[h - 1] == 0
            for c, k in enumerate(ln):
                dk = g.digits(k)
                assert dk[h - 1] == c
                assert dk[:h - 1] + dk[h:] == base[:h - 1] + base[h:]
            assert ln[0] % g.A(h) == sum(base[i] * g.A(i + 1) for i in range(h - 1))
            if h >= 2:
                assert g.delta(h, ln[0]) == Fraction(ln[0] % g.A(h), g.A(h))


@pytest.mark.parametrize("t", SMALL)
def test_storage_to_freq(t):
    """perm[sum u_i A_i] = Phi(u) (r2 (3.7), r3 (3.5)/(3.7)); freq_to_storage is its inverse."""
    g = BridgeGeometry(t)
    perm, inv = g.storage_to_freq(), g.freq_to_storage()
    assert sorted(perm) == list(range(g.R))
    for s in range(g.R):
        assert perm[s] == g.phi(g.digits(s))
        assert inv[perm[s]] == s


# ------------------------------------------------------------------------------ explicit cases
@pytest.mark.parametrize("t1,r", [(2, 2), (2, 4), (4, 4), (4, 8), (8, 8), (8, 16)])
def test_d2_reproduces_manuscript(t1, r):
    """d = 2 is the manuscript's thm:poisson: j = j_1 + t_1 j_2, shift j_1/t_1 (eq. u-ideal),
    k = u_2 + r u_1, aliases u_2 + r((u_1 - m) mod t_1) (eq. poisson-bridge)."""
    g = BridgeGeometry((t1, r))
    R = t1 * r
    assert g.R == R and g.q(2) == r and g.Q(1) == r and g.Q(2) == 1
    for j1, j2 in itertools.product(range(t1), range(r)):
        j = g.index((j1, j2))
        assert j == j1 + t1 * j2
        assert g.delta(2, j) == Fraction(j1, t1)
    perm = g.storage_to_freq()
    for u1, u2 in itertools.product(range(t1), range(r)):
        k = g.phi((u1, u2))
        assert k == u2 + r * u1
        assert perm[u1 + t1 * u2] == u2 + r * u1
        for m in range(-3, 4):
            assert (k - m * g.q(2)) % R == u2 + r * ((u1 - m) % t1)


def test_d3_example_r2_section_3_4():
    """The explicit d = 3, t = (2,2,2) check (r2 §3.4, r3 §3.4)."""
    g = BridgeGeometry((2, 2, 2))
    assert (g.R, g.A(2), g.A(3)) == (8, 2, 4)
    assert all(g.index((a, b, c)) == a + 2 * b + 4 * c for a, b, c in itertools.product(range(2), repeat=3))
    assert g.digits(3) == (1, 1, 0)
    assert g.delta(2, 3) == Fraction(1, 2) and g.delta(3, 3) == Fraction(3, 4)
    assert all(g.phi(u) == 4 * u[0] + 2 * u[1] + u[2] for u in itertools.product(range(2), repeat=3))
    assert g.phi((1, 0, 1)) == 5 and (g.q(2), g.q(3)) == (4, 2)
    aliases = {(m2, m3): (5 - m2 * g.q(2) - m3 * g.q(3)) % 8 for m2 in (0, 1) for m3 in (0, 1)}
    assert aliases == {(0, 0): 5, (1, 0): 1, (0, 1): 3, (1, 1): 7}           # r2 (3.10) table
    # r3 §3.4: the h = 3 shift sends 0 -> 6 -> 4 -> 2 -> 0 and changes u_2
    orbit = [0]
    for _ in range(4):
        orbit.append((orbit[-1] - g.q(3)) % 8)
    assert orbit == [0, 6, 4, 2, 0]
    assert g.u_digit(2, 0) == 0 and g.u_digit(2, 6) == 1 and g.phi_inv(6) == (1, 1, 0)
    assert g.cycles(3) == [[0, 2, 4, 6], [1, 3, 5, 7]] and g.cycles(2) == [[0, 4], [1, 5], [2, 6], [3, 7]]


# ------------------------------------------------------------------------------ balanced factors
def test_balanced_factors_all_small():
    """r2 Thm 3 / r3 §2.1: r = 2^ceil(K/d), t_i in {r/2, r}, prod = 2^K, t_d = r, sorted, all >= 2;
    d = 2 is the manuscript split (listing l.737-738, schedule.split_2d).  All 1 <= d <= K <= 30."""
    for K in range(1, 31):
        for d in range(1, K + 1):
            t = balanced_factors(K, d)
            r = 1 << -(-K // d)
            assert len(t) == d and math.prod(t) == 1 << K
            assert all(ti in (r // 2, r) and ti >= 2 for ti in t)
            assert t[-1] == r and list(t) == sorted(t)
            assert sum(1 for ti in t if ti == r // 2) == d * -(-K // d) - K
            assert BridgeGeometry(t).K == K
        k1, k2 = split_2d(K)
        if K >= 2:
            assert balanced_factors(K, 2) == (1 << k1, 1 << k2) == (1 << (K // 2), 1 << ((K + 1) // 2))


def test_balanced_factors_rejects():
    for K in range(0, 31):
        for d in range(K + 1, 32):
            with pytest.raises(ValueError):
                balanced_factors(K, d)
    for bad in [(5, 0), (5, -1)]:
        with pytest.raises(ValueError):
            balanced_factors(*bad)
    with pytest.raises(TypeError):
        balanced_factors(5.0, 2)


# ------------------------------------------------------------------------------ validation
@pytest.mark.parametrize("bad", [(), (1,), (3,), (2, 6), (0,), (-2,), (2.0,), (True, 2), ("2",), (2, 12)])
def test_rejects_bad_axes(bad):
    with pytest.raises(ValueError):
        BridgeGeometry(bad)


def test_rejects_bad_arguments_and_is_frozen():
    g = BridgeGeometry([2, 4, 2])
    assert g.t == (2, 4, 2) and g == BridgeGeometry((2, 4, 2)) and hash(g) == hash(BridgeGeometry((2, 4, 2)))
    assert g != BridgeGeometry((2, 2, 4))
    with pytest.raises(dataclasses.FrozenInstanceError):
        g.t = (2, 2)
    for call in [lambda: g.tt(0), lambda: g.tt(4), lambda: g.A(5), lambda: g.Q(4), lambda: g.q(0),
                 lambda: g.delta(1, 3), lambda: g.delta(4, 3), lambda: g.delta(2, 16), lambda: g.digits(-1),
                 lambda: g.digits(16), lambda: g.index((0, 4, 0)), lambda: g.index((0, 0)),
                 lambda: g.phi((2, 0, 0)), lambda: g.phi_inv(16), lambda: g.u_digit(2, 16),
                 lambda: g.cycles(0), lambda: g.line_indices(4), lambda: g.u_digit(True, 1)]:
        with pytest.raises(ValueError):
            call()
    with pytest.raises(TypeError):
        BridgeGeometry("22")


def test_geometry_module_has_no_floating_point():
    """Exactness rule: no float literals, no true division, no float()/math in geometry.py."""
    tree = ast.parse(pathlib.Path(geometry_module.__file__).read_text())
    for node in ast.walk(tree):
        assert not (isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)))
        assert not isinstance(node, ast.Div)
        assert not (isinstance(node, ast.Name) and node.id in ("float", "complex", "math"))
        assert not isinstance(node, (ast.Import, ast.ImportFrom)) or all(
            a.name not in ("math", "cmath", "numpy", "mpmath") for a in node.names)
