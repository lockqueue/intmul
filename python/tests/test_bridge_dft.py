"""M2: the d-dimensional bridge DFT (d = 2..5) with the direct middle tensor DFT, against the
naive exact oracle, within the Lemma C budget (r3 (2.3)-(2.4)); chronological deconvolution
order; and exact end-to-end products with the bridge inside the multiplier."""

import random
from fractions import Fraction

import pytest

import path_model as PM
from conftest import make_ctx
from oracle import OracleDFT, sqrt_upper
from subnlogn.bridge.bridge_dft import bridge_certificate, bridge_dft, bridge_geometry
from subnlogn.bridge.deconv import deconv_axis
from subnlogn.bridge.middle import middle_dft
from subnlogn.bridge.spread import spread_axis
from subnlogn.fixedpoint import FxVec
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import test_schedule


def _inputs(kind, R, p, rng):
    q = p + 2
    big = (1 << (q + p)) * 7 // 10
    if kind == "random_max":
        return [rng.randint(-big, big) for _ in range(R)], [rng.randint(-big, big) for _ in range(R)]
    if kind == "random_small":
        return [rng.randint(-8, 8) for _ in range(R)], [rng.randint(-8, 8) for _ in range(R)]
    if kind == "impulse":
        re = [0] * R
        re[rng.randrange(R)] = big
        return re, [0] * R
    if kind == "constant":
        return [big] * R, [big] * R
    if kind == "alternating":
        return [big * (-1) ** j for j in range(R)], [0] * R
    if kind == "zero":
        return [0] * R, [0] * R
    raise ValueError(kind)


CASES = [(d, K, "r2") for d in (2, 3, 4, 5) for K in range(d, 9) if K >= d]
CASES += [(d, K, "r3") for d in (2, 3, 4, 5) for K in (d, 7)]


@pytest.mark.parametrize("d,K,profile", CASES)
def test_bridge_matches_oracle(d, K, profile):
    """Final error within the contract 2^-p max(1,||x||) and the certificate, under the faithful
    r2 Thm 2 constants (default) and the r3 (2.3) profile."""
    R = 1 << K
    p = max(8, K) + 4
    rng = random.Random(100 * d + K)
    sched = test_schedule(bridge_d=d).with_(bridge_constants=profile)
    for kind in ("random_max", "impulse", "alternating", "random_small", "zero"):
        re, im = _inputs(kind, R, p, rng)
        ctx = make_ctx(sched, capture=True)
        z = bridge_dft(ctx, FxVec(re, im, p + 2), R, p, d)
        P, w, m, geom = ctx.capture["bridge_params"]
        e = ctx.capture["bridge_e"]
        A = max(Fraction(1), sqrt_upper(FxVec(re, im, p + 2).sup_norm_sq()))
        cert = bridge_certificate(geom, p, P, w, 1 << e, A)
        orc = OracleDFT(re, im, p + 2, p)
        err = sqrt_upper(orc.error_sq_vs(z.re, z.im, z.q))
        assert err <= cert.contract + orc.err, (d, K, kind)
        assert err <= cert.total + orc.err, (d, K, kind)


@pytest.mark.parametrize("d,K,profile", [(2, 4, "r2"), (3, 5, "r2"), (4, 6, "r2"), (5, 7, "r2"),
                                         (3, 8, "r2"), (2, 4, "r3"), (4, 6, "r3")])
def test_bridge_pre_rounding_certificate(d, K, profile):
    """Measured normalized-domain error (oracle at P + 2K + 64 bits) <= the Lemma C certificate."""
    R = 1 << K
    p = max(8, K) + 2
    rng = random.Random(7 * d + K)
    re, im = _inputs("random_max", R, p, rng)
    ctx = make_ctx(test_schedule(bridge_d=d).with_(bridge_constants=profile), capture=True)
    bridge_dft(ctx, FxVec(re, im, p + 2), R, p, d)
    P, w, m, geom = ctx.capture["bridge_params"]
    e = ctx.capture["bridge_e"]
    Zn = ctx.capture["bridge_Znorm"]
    A = max(Fraction(1), sqrt_upper(FxVec(re, im, p + 2).sup_norm_sq()))
    cert = bridge_certificate(geom, p, P, w, 1 << e, A)
    orc = OracleDFT(re, im, p + 2, P)
    pre = sqrt_upper(orc.error_sq_vs(Zn.re, Zn.im, Zn.q - e))
    assert pre <= cert.pre_rounding + orc.err


def _pipeline(ctx, x, geom, p, order):
    """Bridge steps composed by hand, with a selectable deconvolution order (test only)."""
    P, w, m = ctx.schedule.bridge_params(p, geom.K, geom.d)
    q = P + 2
    U = FxVec([v << (q - x.q) for v in x.re], [v << (q - x.q) for v in x.im], q)
    for h in range(geom.d, 1, -1):
        U = spread_axis(ctx, U, geom, h, m, w)
    Yst = middle_dft(ctx, U, geom, P)
    perm = geom.storage_to_freq()
    yr, yi = [0] * geom.R, [0] * geom.R
    for s, k in enumerate(perm):
        yr[k], yi[k] = Yst.re[s], Yst.im[s]
    Y = FxVec(yr, yi, q)
    for h in order:
        Y = deconv_axis(ctx, Y, geom, h, w)
    return Y


@pytest.mark.parametrize("d,K", [(3, 4), (3, 6), (4, 6)])
def test_chronological_order_matters(d, K):
    """Lemma A: invert B_2 first, ..., B_d last; the reversed order generally fails."""
    R = 1 << K
    p = 10
    geom = bridge_geometry(K, d)
    rng = random.Random(K)
    re = [rng.randint(-(1 << 12), 1 << 12) for _ in range(R)]
    im = [rng.randint(-(1 << 12), 1 << 12) for _ in range(R)]
    ctx = make_ctx(test_schedule(bridge_d=d))
    x = FxVec(re, im, p + 2)
    orc = OracleDFT(re, im, p + 2, p)
    good = _pipeline(ctx, x, geom, p, range(2, d + 1))
    bad = _pipeline(ctx, x, geom, p, range(d, 1, -1))
    eg = sqrt_upper(orc.error_sq_vs(good.re, good.im, good.q))
    eb = sqrt_upper(orc.error_sq_vs(bad.re, bad.im, bad.q))
    assert eg < Fraction(1, 1 << 40)
    assert eb > Fraction(1, 1 << 8)


@pytest.mark.parametrize("d", [2, 3, 4, 5])
def test_multiply_with_bridge(d):
    """Exact products with the d-axis bridge; every size here has K0 >= d, so no clamping."""
    rng = random.Random(d)
    sched = test_schedule(bridge_d=d)
    ctx = make_ctx(sched)
    pairs = []
    for n in (60, 300, 1200):
        assert root_parameters(n)[2] >= d
        ones = (1 << n) - 1
        cases = [(rng.getrandbits(n) | 1 << (n - 1), rng.getrandbits(n)), (ones, ones),
                 (int("10" * (n // 2), 2), ones), (rng.getrandbits(n), rng.getrandbits(max(1, n // 9))),
                 (0, ones)]
        for a, b in cases:
            assert multiply(a, b, ctx) == a * b, (d, n)
        pairs += cases
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())      # exact counts
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    assert exp["bridge.d_clamped"] == 0 and exp["bridge.dft"] == 2 * len(pairs)


def test_multiply_bridge_size_forced_clamp():
    """Size-forced fallback: for K0 < d the bridge dimension is clamped to min(d, K0) (and K0 = 1
    uses the 2D FastDFT leaf); recorded as bridge.d_clamped (FAITHFULNESS M2)."""
    sched = test_schedule(bridge_d=5)
    ctx = make_ctx(sched)
    pairs = [(13, 11), ((1 << 20) - 3, (1 << 19) + 5), (1, 1)]
    for a, b in pairs:
        assert multiply(a, b, ctx) == a * b
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())      # exact counts
    PM.assert_exact(ctx.inst.counts, exp, ["bridge.dft", "bridge.d_clamped", "bridge.fallback_2d", "multiply.call"])
    assert exp["bridge.d_clamped"] == 2 and exp["bridge.fallback_2d"] == 4      # K0 = 4 clamps; K0 = 1 -> 2D


@pytest.mark.slow
@pytest.mark.parametrize("d", [2, 3, 4, 5])
def test_multiply_with_bridge_large(d):
    rng = random.Random(10 + d)
    ctx = make_ctx(test_schedule(bridge_d=d))
    assert root_parameters(10000)[2] >= d
    for n in (10000, 100000):
        a, b = rng.getrandbits(n), rng.getrandbits(n)
        assert multiply(a, b, ctx) == a * b
        ones = (1 << n) - 1
        assert multiply(ones, ones, ctx) == ones * ones


def test_trunc_rounding_rejected_by_front_end():
    """The certificates assume nearest rounding (stage-check observation); TRUNC is rejected."""
    from subnlogn.fixedpoint import FxVec, Rounding
    from subnlogn.fastdft2d import fast_dft
    for sched in (test_schedule(bridge_d=2, rounding=Rounding.TRUNC),):
        ctx = make_ctx(sched)
        with pytest.raises(ValueError):
            bridge_dft(ctx, FxVec([0] * 16, [0] * 16, 14), 16, 12, 2)
    ctx = make_ctx(test_schedule(rounding=Rounding.TRUNC))
    with pytest.raises(ValueError):
        fast_dft(ctx, FxVec([0] * 16, [0] * 16, 14), 16, 12)
