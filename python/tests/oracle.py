"""Test-only oracle: the naive normalized DFT (F_R x)_u = (1/R) sum_j x_j e^{2 pi i j u/R}
(MS eq. (dft-1d)) in exact integer arithmetic at precision Q >= p + 2 lg R + 64.

Roots are computed with plain mpmath at Q + 64 bits and rounded to the 2^-Q grid; this is
deliberately independent of subnlogn.certified.  Error: every root has |W_k - w^k| <= 2^-Q
(rounding 2^-Q/2 per coordinate plus mpmath error << 2^-Q), so
|oracle_u - (F_R x)_u| <= (1/R) sum_j |x_j| 2^-Q <= ||x||_inf 2^-Q.
"""

from __future__ import annotations

from fractions import Fraction

import mpmath

_root_cache: dict[tuple[int, int], tuple[list[int], list[int]]] = {}


def roots(R: int, Q: int) -> tuple[list[int], list[int]]:
    key = (R, Q)
    if key not in _root_cache:
        re, im = [], []
        with mpmath.workprec(Q + 64):
            for k in range(R):
                th = 2 * mpmath.pi * k / R
                re.append(int(mpmath.nint(mpmath.cos(th) * mpmath.mpf(2) ** Q)))
                im.append(int(mpmath.nint(mpmath.sin(th) * mpmath.mpf(2) ** Q)))
        _root_cache[key] = (re, im)
    return _root_cache[key]


class OracleDFT:
    """Exact-integer naive DFT.  ``value(u)`` is (re, im) numerators at scale ``self.scale``."""

    def __init__(self, re: list[int], im: list[int], q_in: int, p: int, extra: int = 64):
        R = len(re)
        self.R = R
        K = R.bit_length() - 1
        self.K = K
        self.Q = p + 2 * K + extra
        self.scale = q_in + self.Q + K
        wr, wi = roots(R, self.Q)
        half = R // 2
        out_re, out_im = [], []
        for u in range(R):
            # group by k = j u mod R using w^{k + R/2} = -w^k (exact signed sums), then R/2 products
            if R == 1:
                out_re.append(re[0] << self.Q)
                out_im.append(im[0] << self.Q)
                continue
            cr = [0] * half
            ci = [0] * half
            for j in range(R):
                k = (j * u) % R
                if k >= half:
                    cr[k - half] -= re[j]
                    ci[k - half] -= im[j]
                else:
                    cr[k] += re[j]
                    ci[k] += im[j]
            sr = 0
            si = 0
            for k in range(half):
                a, b = cr[k], ci[k]
                if a or b:
                    sr += a * wr[k] - b * wi[k]
                    si += a * wi[k] + b * wr[k]
            out_re.append(sr)
            out_im.append(si)
        self.re = out_re
        self.im = out_im
        # rigorous oracle error bound: ||x||_inf 2^-Q  (we use max|coord| * sqrt2 <= 2 max|coord|)
        m = max([abs(v) for v in re] + [abs(v) for v in im] + [0])
        self.err = Fraction(2 * m, 1 << (q_in + self.Q))

    def error_sq_vs(self, re: list[int], im: list[int], q: int) -> Fraction:
        """max_u |z_u - oracle_u|^2 for z on scale q (exact rational)."""
        S = self.scale
        worst = Fraction(0)
        if q <= S:
            sh = S - q
            for a, b, c, d in zip(re, im, self.re, self.im):
                dr = (a << sh) - c
                di = (b << sh) - d
                v = dr * dr + di * di
                if v > worst:
                    worst = v
            return Fraction(worst, 1 << (2 * S))
        sh = q - S
        for a, b, c, d in zip(re, im, self.re, self.im):
            dr = a - (c << sh)
            di = b - (d << sh)
            v = dr * dr + di * di
            if v > worst:
                worst = v
        return Fraction(worst, 1 << (2 * q))


def log2_frac(x: Fraction) -> float:
    """Display helper (non-authoritative): log2 of a positive rational."""
    import math
    if x == 0:
        return float("-inf")
    return math.log2(x.numerator) - math.log2(x.denominator)


def sqrt_upper(x: Fraction) -> Fraction:
    """A rational upper bound for sqrt(x) (for comparing errors with bounds exactly)."""
    import math
    if x == 0:
        return Fraction(0)
    # sqrt(n/d) <= (isqrt(n*d*4^k)+1) / (d*2^k)
    k = 64
    n, d = x.numerator, x.denominator
    return Fraction(math.isqrt(n * d << (2 * k)) + 1, d << k)
