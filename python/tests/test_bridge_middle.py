"""The direct middle tensor DFT (M2 reference backend) against a high-precision tensor-DFT oracle:
measured error <= the derived bound 2.16 K 2^{-q_m} max(1, ||U||) + sqrt(2)/2 2^{-q}
(the error analysis, §M2.2), for d = 2..5."""

import random
from fractions import Fraction

import mpmath
import pytest

from conftest import make_ctx
from oracle import log2_frac, sqrt_upper
from subnlogn.bridge.bridge_dft import bridge_geometry
from subnlogn.bridge.middle import direct_middle_dft
from subnlogn.fixedpoint import FxVec
from subnlogn.schedule import test_schedule


def tensor_dft_oracle(re, im, q, geom, Qo):
    """Per-axis naive DFT in exact integers with roots on 2^-Qo; returns numerators at scale Qo and
    a rigorous error bound (each axis adds <= 2 * max|value| 2^-Qo + 2^-Qo)."""
    sh = Qo - q
    ar = [v << sh for v in re]
    ai = [v << sh for v in im]
    m = max([abs(v) for v in re] + [abs(v) for v in im] + [1 << q])
    err = Fraction(0)
    for h in range(1, geom.d + 1):
        t = geom.tt(h)
        with mpmath.workprec(Qo + 64):
            wr = [int(mpmath.nint(mpmath.cos(2 * mpmath.pi * k / t) * mpmath.mpf(2) ** Qo)) for k in range(t)]
            wi = [int(mpmath.nint(mpmath.sin(2 * mpmath.pi * k / t) * mpmath.mpf(2) ** Qo)) for k in range(t)]
        for line in geom.line_indices(h):
            xr = [ar[i] for i in line]
            xi = [ai[i] for i in line]
            for u, i in enumerate(line):
                sr = si = 0
                for c in range(t):
                    k = (c * u) % t
                    sr += xr[c] * wr[k] - xi[c] * wi[k]
                    si += xr[c] * wi[k] + xi[c] * wr[k]
                # divide by t * 2^Qo, round to scale Qo (exact half-even)
                den = t << Qo
                ar[i] = (2 * sr + den) // (2 * den)
                ai[i] = (2 * si + den) // (2 * den)
        err += Fraction(4 * m, 1 << (q + Qo)) + Fraction(2, 1 << Qo)
    return ar, ai, err


@pytest.mark.parametrize("d,K", [(2, 2), (2, 5), (3, 3), (3, 6), (4, 4), (4, 7), (5, 5), (5, 7)])
def test_direct_middle_dft_bound(d, K):
    geom = bridge_geometry(K, d)
    R = geom.R
    P = 40 + K
    q = P + 2
    rng = random.Random(d * 100 + K)
    ctx = make_ctx(test_schedule(bridge_d=d))
    qm = P + K + ctx.schedule.bridge_mid_guard
    for scale_bits in (0, K // 2 + 1):
        lim = 1 << (q + scale_bits)
        re = [rng.randint(-lim, lim) for _ in range(R)]
        im = [rng.randint(-lim, lim) for _ in range(R)]
        out = direct_middle_dft(ctx, FxVec(re, im, q), geom, P)
        Qo = qm + K + 64
        orr, ori, oerr = tensor_dft_oracle(re, im, q, geom, Qo)
        worst = 0
        sh = Qo - q
        for a, b, c, e in zip(out.re, out.im, orr, ori):
            dr, di = (a << sh) - c, (b << sh) - e
            worst = max(worst, dr * dr + di * di)
        meas = sqrt_upper(Fraction(worst, 1 << (2 * Qo)))
        M = max(Fraction(1), sqrt_upper(FxVec(re, im, q).sup_norm_sq()))
        bound = Fraction(216, 100) * K * M / (1 << qm) + Fraction(70711, 100000) / (1 << q)
        assert meas <= bound + oerr, (d, K, log2_frac(meas), log2_frac(bound))
