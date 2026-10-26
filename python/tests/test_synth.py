"""M3: Lemma 16 layout L and synthetic transforms with direct layers (SPEC §5.2, §5.3, §5.11)."""

import random
from fractions import Fraction

import pytest

import path_model as PM
from subnlogn.middle3.layout import layout_plan, chunk_slots
from subnlogn.middle3.synth import Synth, monomial_shift


def test_layout_preprint_example():
    """Pr L2910-2928: l = 6, K = 2, one long then one short axis."""
    plan = layout_plan((64, 32), 6, 2)
    assert (plan.b, plan.q) == (1, 2)
    assert plan.order == [(0, 5), (0, 0), (1, 0), (0, 4), (0, 3), (1, 4), (1, 3), (0, 2), (0, 1),
                          (1, 2), (1, 1)]
    assert chunk_slots(0, 1, 6, 2) == [(0, 4), (0, 3)]


@pytest.mark.parametrize("t,ell,K", [((4,), 2, 1), ((8, 4), 3, 1), ((8, 8, 4), 3, 2), ((16, 8, 16), 4, 2),
                                     ((32, 16), 5, 3), ((64, 32), 6, 2)])
def test_layout_is_permutation_and_inverse(t, ell, K):
    plan = layout_plan(t, ell, K)
    f, g = plan.address_map(), plan.address_map(inverse=True)
    assert sorted(f) == list(range(1 << plan.n))
    assert all(g[f[x]] == x for x in range(1 << plan.n))
    assert len([m for m in plan.moves if m[0] == "xchg"]) <= len(t) * plan.q - 1


def monomial_naive(re, im, E):
    r = len(re)
    out_re, out_im = [0] * r, [0] * r
    for k in range(r):
        e = (k + E) % (2 * r)
        sgn = -1 if e >= r else 1
        out_re[e % r] += sgn * re[k]
        out_im[e % r] += sgn * im[k]
    return out_re, out_im


@pytest.mark.parametrize("r", [1, 2, 4, 8])
def test_monomial_shift_all_exponents(r):
    rng = random.Random(r)
    re = [rng.randint(-9, 9) for _ in range(r)]
    im = [rng.randint(-9, 9) for _ in range(r)]
    for E in list(range(-3 * r, 3 * r + 1)) + [r, 2 * r - 1, -r, -(2 * r - 1)]:
        assert monomial_shift(re, im, E) == monomial_naive(re, im, E)


def _digits(x, t):
    out = []
    for ti in reversed(t):
        out.append(x % ti)
        x //= ti
    return tuple(reversed(out))


def _addr(dg, t):
    x = 0
    for d_, ti in zip(dg, t):
        x = x * ti + d_
    return x


def _rev(v, a):
    return int(format(v, f"0{a}b")[::-1], 2) if a else 0


def naive_LBF(recs, t, r, sy):
    """Exact L·B·F_t^- z: numerators at scale +lg M, positions L(B(j))."""
    M = 1
    for ti in t:
        M *= ti
    out = [None] * M
    for j in range(M):
        jd = _digits(j, t)
        acc_re, acc_im = [0] * r, [0] * r
        for k in range(M):
            kd = _digits(k, t)
            E = -sum((2 * r // ti) * a * b for ti, a, b in zip(t, jd, kd))
            sr, si = monomial_shift(recs[k][0], recs[k][1], E)
            acc_re = [u + v for u, v in zip(acc_re, sr)]
            acc_im = [u + v for u, v in zip(acc_im, si)]
        bj = _addr(tuple(_rev(jv, ti.bit_length() - 1) for jv, ti in zip(jd, t)), t)
        out[sy.fwd_map[bj]] = (acc_re, acc_im)
    return out


SHAPES = [((4,), 2, 1), ((2,), 2, 1), ((4, 2), 2, 1), ((8, 4), 3, 1), ((8, 8), 3, 2), ((4, 4, 4), 3, 1),
          ((8, 16), 4, 2), ((16,), 4, 3)]


@pytest.mark.parametrize("t,ell,K", SHAPES)
def test_forward_exact_counterpart(t, ell, K):
    """truncate=False forward == L·B·F_t^- (bit-exact)."""
    r = 1 << ell
    sy = Synth(t, ell, K)
    rng = random.Random(hash((t, ell, K)) & 0xffff)
    p = 12
    recs = [([rng.randint(-(1 << p), 1 << p) for _ in range(r)], [rng.randint(-(1 << p), 1 << p) for _ in range(r)])
            for _ in range(sy.plan.address_map().__len__())]
    got, scale = sy.forward(recs, p, p, truncate=False)
    want = naive_LBF(recs, t, r, sy)                       # scale p + n
    sw = p + sy.n
    assert scale >= sw
    assert got == [([v << (scale - sw) for v in re], [v << (scale - sw) for v in im]) for re, im in want]


@pytest.mark.parametrize("t,ell,K", SHAPES)
def test_opposite_after_forward_is_identity_over_M(t, ell, K):
    r = 1 << ell
    sy = Synth(t, ell, K)
    rng = random.Random(7 + ell)
    p = 10
    M = 1 << sy.n
    recs = [([rng.randint(-(1 << p), 1 << p) for _ in range(r)], [rng.randint(-(1 << p), 1 << p) for _ in range(r)])
            for _ in range(M)]
    f, s1 = sy.forward(recs, p, p, truncate=False)
    g, s2 = sy.opposite(f, s1, p, truncate=False)
    for (gr, gi), (xr, xi) in zip(g, recs):
        # g = x / M  <=>  g_num * 2^-s2 = x_num * 2^-p / 2^n
        assert gr == [v << (s2 - p - sy.n) for v in xr] and gi == [v << (s2 - p - sy.n) for v in xi]


@pytest.mark.parametrize("t,ell,K", SHAPES)
def test_truncated_error_and_disk(t, ell, K):
    """Each procedure: error < sqrt(2) l 2^-p, disk-grid outputs (Lemma 16; reading R5)."""
    r = 1 << ell
    sy = Synth(t, ell, K)
    rng = random.Random(99 + ell)
    p = 30
    M = 1 << sy.n
    lim = (1 << p) * 7 // 10
    recs = [([rng.randint(-lim, lim) for _ in range(r)], [rng.randint(-lim, lim) for _ in range(r)])
            for _ in range(M)]
    for direction in ("forward", "opposite"):
        fn = getattr(sy, direction)
        got, s = fn(recs, p, p, truncate=True)
        ex, se = fn(recs, p, p, truncate=False)
        assert s == p
        worst = Fraction(0)
        for (gr, gi), (er, ei) in zip(got, ex):
            for a, b, c, d in zip(gr, gi, er, ei):
                assert a * a + b * b <= 1 << (2 * p)          # disk grid
                dr = Fraction(a, 1 << p) - Fraction(c, 1 << se)
                di = Fraction(b, 1 << p) - Fraction(d, 1 << se)
                worst = max(worst, dr * dr + di * di)
        assert worst < 2 * ell * ell * Fraction(1, 1 << (2 * p))   # (sqrt2 l 2^-p)^2


@pytest.mark.parametrize("t,ell,K", SHAPES)
def test_layer_paths_agree_bit_for_bit(t, ell, K):
    """Chunk rounds via the Prop 14 base case (identity (18)) == the direct H0 layer (SPEC §5.11)."""
    from subnlogn.m6.prop14 import hadamard_direct
    r = 1 << ell
    rng = random.Random(5 * ell + len(t))
    p = 24
    a = Synth(t, ell, K)
    b = Synth(t, ell, K, layer=hadamard_direct)
    M = 1 << a.n
    lim = (1 << p) * 7 // 10
    recs = [([rng.randint(-lim, lim) for _ in range(r)], [rng.randint(-lim, lim) for _ in range(r)])
            for _ in range(M)]
    assert a.forward(recs, p, p) == b.forward(recs, p, p)
    assert a.opposite(recs, p, p) == b.opposite(recs, p, p)


@pytest.mark.parametrize("t,ell,K", [((4, 4, 4), 2, 1), ((8, 16), 4, 1), ((8, 16), 4, 2), ((16, 8), 4, 3),
                                     ((8, 8, 8), 3, 2), ((4, 2, 4), 2, 1), ((8, 8), 3, 1)])
def test_layout_executed_by_lemma3_moves_and_lemma12_exchanges(t, ell, K):
    """SPEC §5.2: L and L^{-1} executed on the record stream by the plan's Lemma 3 single-digit moves
    and chunk exchanges (Lemma 12 via swap_via_lemma12 on B1, and the bitwise base case) equal the index
    maps exactly.  Only the shapes with q = floor((l-1)/K) >= 2 and D >= 2 have chunk exchanges (here
    (8, 16), l = 4, K = 1: three exchanges, and (8, 8), l = 3, K = 1: one); every exchange is counted.  K-bit
    chunks reach the bit network only for K >= 4 (l >= 9 for an exchange, >= 2^18 records), so the network
    path of Lemma 12 is exercised in tests/test_bridge_movement.py and tests/test_m6_acceptance.py instead."""
    from subnlogn.instrument import Instrument
    from subnlogn.interchange import InterchangePolicy
    from subnlogn.m6.lemma13 import bitwise_swap, swap_via_lemma12
    from subnlogn.middle3.layout import execute_layout, layout_plan, permute_records
    from subnlogn.net import compile_network
    from subnlogn.net.fixtures import fixture_B1
    plan = layout_plan(t, ell, K)
    n_x = sum(1 for m in plan.moves if m[0] == "xchg")
    assert n_x == PM.layout_exchanges(len(t), ell, K)            # independent SPEC §5.2 scan
    recs = [("rec", i) for i in range(1 << plan.n)]
    for base in (bitwise_swap, swap_via_lemma12(compile_network(fixture_B1()), InterchangePolicy())):
        calls = []

        def swap(stream, shape, a, b, inst=None, base=base):
            calls.append((a, b))
            return base(stream, shape, a, b, inst)

        inst = Instrument()
        f = execute_layout(plan, recs, swap, inst=inst)
        assert f == permute_records(recs, plan.address_map())
        assert execute_layout(plan, f, swap, inverse=True, inst=inst) == recs
        assert inst.counts["layout.executed"] == 2 and len(calls) == 2 * n_x
    assert (n_x > 0) == ((t, ell, K) in (((8, 16), 4, 1), ((8, 8), 3, 1)))
