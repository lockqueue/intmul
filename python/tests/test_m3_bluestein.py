"""M3 (SPEC §5.7-5.10, §5.12): Proposition 18, the coefficient twist, the Bluestein positive tensor
DFT with direct layers, and the bridge with the "bluestein" middle backend."""

import random
from fractions import Fraction

import mpmath
import pytest

import path_model as PM
from conftest import make_ctx
from oracle import OracleDFT, sqrt_upper
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.fixedpoint import FxVec
from subnlogn.middle3.bluestein import complex_convolution, tensor_positive_dft
from subnlogn.middle3.prop18 import normalized_ring_convolution
from subnlogn.middle3.synth import Synth, monomial_shift
from subnlogn.multiply import multiply
from subnlogn.schedule import test_schedule

SQRT2_UP = Fraction(141422, 100000)


def _mixed(x, t):
    out = []
    for ti in reversed(t):
        out.append(x % ti)
        x //= ti
    return tuple(reversed(out))


def _rand_disk(rng, n, p, frac=Fraction(6, 10)):
    lim = int(frac * (1 << p) / Fraction(14143, 10000))
    return [(rng.randint(-lim, lim), rng.randint(-lim, lim)) for _ in range(n)]


def naive_ring_conv(f, g, t, r):
    """Exact (f * g): cyclic over the record axes t, negacyclic in y.  Records (re list, im list)
    of integer numerators; the result numerators have scale 2p."""
    M = len(f)
    out = [([0] * r, [0] * r) for _ in range(M)]
    for a in range(M):
        ad = _mixed(a, t)
        for b in range(M):
            bd = _mixed(b, t)
            kd = tuple((x + y) % ti for x, y, ti in zip(ad, bd, t))
            k = 0
            for v, ti in zip(kd, t):
                k = k * ti + v
            fr, fi = f[a]
            gr, gi = g[b]
            acc_r, acc_i = out[k]
            for i in range(r):
                for j in range(r):
                    e = i + j
                    sgn = -1 if e >= r else 1
                    acc_r[e % r] += sgn * (fr[i] * gr[j] - fi[i] * gi[j])
                    acc_i[e % r] += sgn * (fr[i] * gi[j] + fi[i] * gr[j])
    return out


@pytest.mark.parametrize("t,ell", [((4,), 2), ((2,), 2), ((4, 2), 2), ((8,), 3), ((4, 8), 3)])
def test_prop18_against_exact(t, ell):
    r = 1 << ell
    p = 24
    rng = random.Random(len(t) * 10 + ell)
    sy = Synth(t, ell, 1)
    M = 1 << sy.n
    f = [tuple(map(list, zip(*_rand_disk(rng, r, p)))) for _ in range(M)]
    g = [tuple(map(list, zip(*_rand_disk(rng, r, p)))) for _ in range(M)]
    h, mM = normalized_ring_convolution(f, g, sy, p)
    assert mM == sy.n
    ex = naive_ring_conv(f, g, t, r)           # scale 2p; target (f*g)/(rM)
    worst = Fraction(0)
    for (hr, hi), (er, ei) in zip(h, ex):
        for a, b, c, d in zip(hr, hi, er, ei):
            dr = Fraction(a, 1 << p) - Fraction(c, (r * M) << (2 * p))
            di = Fraction(b, 1 << p) - Fraction(d, (r * M) << (2 * p))
            worst = max(worst, dr * dr + di * di)
    bound = SQRT2_UP * M * (3 * ell + 1) / (1 << p)
    assert worst < bound * bound
    # omitting the x M must fail (it is not a no-op)
    worst_noM = Fraction(0)
    for (hr, hi), (er, ei) in zip(h, ex):
        for a, c in zip(hr, er):
            dr = Fraction(a >> mM, 1 << p) - Fraction(c, (r * M) << (2 * p))
            worst_noM = max(worst_noM, dr * dr)
    if M > 1 and any(c for rec in ex for c in rec[0]):
        assert worst_noM > bound * bound


def tensor_dft_mp(x, t, p, sign=+1):
    """High-precision positive (sign=+1) normalized tensor DFT in tensor order (test oracle)."""
    R = len(x)
    with mpmath.workprec(p + 80):
        xs = [mpmath.mpc(a, b) / mpmath.mpf(2) ** p for a, b in x]
        out = []
        for u in range(R):
            ud = _mixed(u, t)
            acc = mpmath.mpc(0)
            for j in range(R):
                jd = _mixed(j, t)
                ph = sum(Fraction(a * b, ti) for a, b, ti in zip(ud, jd, t))
                acc += xs[j] * mpmath.expj(sign * 2 * mpmath.pi * ph)
            out.append(acc / R)
        return out


def _max_err(got, exact, p):
    with mpmath.workprec(p + 80):
        return max(abs(mpmath.mpc(a, b) / mpmath.mpf(2) ** p - e) for (a, b), e in zip(got, exact))


@pytest.mark.parametrize("t", [(4, 4), (2, 4), (4, 4, 4), (2, 2, 4), (8, 8), (4, 8, 8)])
@pytest.mark.parametrize("kind", ["random", "impulse", "ones"])
def test_tensor_positive_dft(t, kind):
    """Bluestein (SPEC §5.9): error < (E_ring + 22) 2^-p, E_ring = sqrt2 M (3l + 1)."""
    p = 40
    R = 1
    for ti in t:
        R *= ti
    r = t[-1]
    ell = r.bit_length() - 1
    M = R // r
    rng = random.Random(R + len(kind))
    if kind == "random":
        x = _rand_disk(rng, R, p)
    elif kind == "impulse":
        x = [(0, 0)] * R
        x[rng.randrange(R)] = ((1 << p) * 6 // 10, 0)
    else:
        x = [((1 << p) * 4 // 10, (1 << p) * 4 // 10)] * R
    got = tensor_positive_dft(x, t, p)
    exact = tensor_dft_mp(x, t, p)
    err = _max_err(got, exact, p)
    bound = (1.41422 * M * (3 * ell + 1) + 22) * 2.0 ** (-p)
    assert err < bound
    assert all(a * a + b * b < (Fraction(701, 1000) ** 2) * (1 << (2 * p)) for a, b in got)


def test_unbarred_kernel_fails():
    """The kernel must be conj(a) (reading R2): using a itself gives a wrong transform."""
    from subnlogn.middle3 import bluestein as B
    t, p = (4, 4), 40
    rng = random.Random(3)
    x = _rand_disk(rng, 16, p)
    exact = tensor_dft_mp(x, t, p)
    orig = B.complex_convolution

    def unbarred(f, g, *args, **kw):
        return orig([(a, -b) for a, b in f], g, *args, **kw)    # undo the bar: kernel = a
    B.complex_convolution = unbarred
    try:
        bad = B.tensor_positive_dft(x, t, p)
    finally:
        B.complex_convolution = orig
    assert _max_err(bad, exact, p) > 1e-3


@pytest.mark.parametrize("d,K", [(2, 4), (2, 6), (3, 6), (4, 8), (3, 7)])
def test_bridge_with_bluestein_middle(d, K):
    """Bridge (r2 profile) with the M3 Bluestein middle: final error within the contract."""
    R = 1 << K
    p = max(8, K) + 2
    rng = random.Random(d * 100 + K)
    q = p + 2
    big = (1 << (q + p)) * 7 // 10
    re = [rng.randint(-big, big) for _ in range(R)]
    im = [rng.randint(-big, big) for _ in range(R)]
    sched = test_schedule(bridge_d=d).with_(bridge_middle="bluestein")
    ctx = make_ctx(sched)
    z = bridge_dft(ctx, FxVec(re, im, q), R, p, d)
    assert ctx.inst.counts["bluestein.tensor_dft"] == 1
    orc = OracleDFT(re, im, q, p)
    err = sqrt_upper(orc.error_sq_vs(z.re, z.im, z.q))
    A = max(Fraction(1), sqrt_upper(FxVec(re, im, q).sup_norm_sq()))
    assert err <= A / (1 << p) + orc.err


@pytest.mark.parametrize("d,K", [(2, 4), (3, 6), (4, 8)])
def test_bridge_bluestein_certificate(d, K):
    """Pre-rounding error (oracle at P + 2K + 64 bits) <= bridge_certificate with the Bluestein
    middle term (E_ring + 22) 2^-p_fft (SPEC §5.9-5.10)."""
    from subnlogn.bridge.bridge_dft import bridge_certificate
    R = 1 << K
    p = max(8, K) + 2
    rng = random.Random(d * 7 + K)
    q = p + 2
    big = (1 << (q + p)) * 7 // 10
    re = [rng.randint(-big, big) for _ in range(R)]
    im = [rng.randint(-big, big) for _ in range(R)]
    ctx = make_ctx(test_schedule(bridge_d=d).with_(bridge_middle="bluestein"), capture=True)
    bridge_dft(ctx, FxVec(re, im, q), R, p, d)
    P, w, m, geom = ctx.capture["bridge_params"]
    e = ctx.capture["bridge_e"]
    A = max(Fraction(1), sqrt_upper(FxVec(re, im, q).sup_norm_sq()))
    cert = bridge_certificate(geom, p, P, w, 1 << e, A, middle_backend="bluestein")
    orc = OracleDFT(re, im, q, P)
    Zn = ctx.capture["bridge_Znorm"]
    pre = sqrt_upper(orc.error_sq_vs(Zn.re, Zn.im, Zn.q - e))
    assert pre <= cert.pre_rounding + orc.err


@pytest.mark.parametrize("d", [2, 3])
def test_multiply_with_bluestein_bridge(d):
    rng = random.Random(40 + d)
    sched = test_schedule(bridge_d=d).with_(bridge_middle="bluestein")
    ctx = make_ctx(sched)
    pairs = []
    for n in (80, 400):
        a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)
        assert multiply(a, b, ctx) == a * b
        ones = (1 << n) - 1
        assert multiply(ones, ones, ctx) == ones * ones
        pairs += [(a, b), (ones, ones)]
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())     # exact: M3 base layers
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    assert exp["bluestein.tensor_dft"] == exp["bridge.dft"] == 2 * len(pairs) and exp["m6.layer.network"] == 0


def naive_cyclic_conv(f, g, t):
    """(f * g)/T cyclic in all d axes, exact (numerators of f g at scale 2p; caller divides)."""
    R = len(f)
    out = [(0, 0)] * R
    acc = [[0, 0] for _ in range(R)]
    for a in range(R):
        ad = _mixed(a, t)
        fr, fi = f[a]
        if not (fr or fi):
            continue
        for b in range(R):
            bd = _mixed(b, t)
            k = 0
            for x, y, ti in zip(ad, bd, t):
                k = k * ti + (x + y) % ti
            gr, gi = g[b]
            acc[k][0] += fr * gr - fi * gi
            acc[k][1] += fr * gi + fi * gr
    return [tuple(v) for v in acc]


@pytest.mark.parametrize("t", [(4, 4), (2, 4), (4, 4, 4), (8, 8)])
def test_complex_convolution_twist(t):
    """SPEC §5.8: M_C(f, g) = (f * g)/T (cyclic in all axes, T = R) within (E_ring + 12) 2^-p;
    the twist x_d -> zeta y turns the cyclic last axis into the negacyclic ring (wrap signs)."""
    p = 36
    R = 1
    for ti in t:
        R *= ti
    r = t[-1]
    ell = r.bit_length() - 1
    M = R // r
    rng = random.Random(R * 3)
    f = _rand_disk(rng, R, p, Fraction(7, 10))
    g = _rand_disk(rng, R, p, Fraction(7, 10))
    sy = Synth(tuple(t[:-1]), ell, 1)
    got = complex_convolution(f, g, t, p, sy)
    ex = naive_cyclic_conv(f, g, t)
    worst = Fraction(0)
    for (a, b), (c, d) in zip(got, ex):
        dr = Fraction(a, 1 << p) - Fraction(c, R << (2 * p))
        di = Fraction(b, 1 << p) - Fraction(d, R << (2 * p))
        worst = max(worst, dr * dr + di * di)
    bound = (SQRT2_UP * M * (3 * ell + 1) + 12) / (1 << p)
    assert worst < bound * bound


@pytest.mark.parametrize("d,K", [(2, 4), (2, 5), (3, 6), (4, 8), (3, 7)])
def test_bluestein_middle_matches_direct_middle(d, K):
    """PLAN M3 acceptance: the Bluestein tensor DFT matches the direct one within the sum of the
    two stated bounds ((E_ring + 22) 2^-q and the error analysis, §M2.2)."""
    from subnlogn.bridge.bridge_dft import bridge_geometry
    from subnlogn.bridge.middle import direct_middle_dft
    from subnlogn.middle3.bluestein import bluestein_middle_dft
    geom = bridge_geometry(K, d)
    R = geom.R
    q = 60
    P = q - 2
    rng = random.Random(d * 31 + K)
    lim = (1 << q) // 12                      # inside the 1/8 disk
    re = [rng.randint(-lim, lim) for _ in range(R)]
    im = [rng.randint(-lim, lim) for _ in range(R)]
    U = FxVec(re, im, q)
    ctx = make_ctx(test_schedule(bridge_d=d))
    a = bluestein_middle_dft(ctx, U, geom, P)
    b = direct_middle_dft(ctx, U, geom, P)
    r = geom.tt(d)
    ell = r.bit_length() - 1
    eb = (SQRT2_UP * (R // r) * (3 * ell + 1) + 22) / (1 << q)
    qm = P + geom.K + ctx.schedule.bridge_mid_guard
    ed = Fraction(216, 100) * geom.K / (1 << qm) + Fraction(70711, 100000) / (1 << q)
    worst = max(Fraction((x - y) ** 2 + (u - v) ** 2, 1 << (2 * q))
                for x, y, u, v in zip(a.re, b.re, a.im, b.im))
    assert worst <= (eb + ed) ** 2


@pytest.mark.slow
@pytest.mark.parametrize("d,n", [(2, 10000), (3, 10000), (4, 10000), (2, 100000), (3, 100000)])
def test_multiply_with_bluestein_bridge_large(d, n):
    rng = random.Random(n + d)
    ctx = make_ctx(test_schedule(bridge_d=d).with_(bridge_middle="bluestein"))
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)
    assert multiply(a, b, ctx) == a * b
    ones = (1 << n) - 1
    assert multiply(ones, ones, ctx) == ones * ones
    assert ctx.inst.counts["bridge.d_clamped"] == 0
