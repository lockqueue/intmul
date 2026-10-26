"""Unconditionally rigorous enclosures of the elementary constants and functions used by the certified
tables (MS Lemma 2.2 ``lem:elementary`` (i)-(iv)): only exact integer arithmetic.  No floats, no mpmath.

An enclosure of a real x at scale P is a pair of Python ints (lo, hi) with lo 2^-P <= x <= hi 2^-P.
Every step rounds outward explicitly (floor for lower ends, ceiling for upper ends, both exact integer
operations), and every truncated series carries an explicit remainder bound:

* :func:`pi_interval`  -- Machin, pi/4 = 4 atan(1/5) - atan(1/239); the atan series alternate with
  decreasing terms, so |tail| <= first omitted term (MS Lemma 2.2(i)).
* :func:`ln2_interval` -- ln 2 = 2 sum_k 1/((2k+1) 3^(2k+1)); positive terms with ratio < 1/9, so the tail
  is at most 9/8 of the first omitted term (MS Lemma 2.2(i)).
* :func:`exp_point`, :func:`exp_interval` -- x = m ln 2 - r with an integer m and an interval r, then
  e^x = 2^m e^{-r}; e^{-r} decreases in r, so the two endpoints of r bound it; each endpoint by its Taylor
  series with the Lagrange remainder e^max(0,y) |y|^(k+1)/(k+1)!; an interval argument is handled by
  monotonicity (MS Lemma 2.2(iii)).  Arguments below -(P+2) ln 2 return [0, 1] (0 < e^x < 2^-(P+2)).
* :func:`sincos_pi` -- cos(pi f), sin(pi f) for an EXACT rational f: f is reduced exactly to [0, 1/4]; there
  x = pi f lies in an interval, sin increases and cos decreases on [0, pi/2], and each endpoint is bounded
  by the alternating Taylor series (|tail| <= first omitted term) (MS Lemma 2.2(iv)).
* :func:`sqrt_interval` -- exact integer square roots of the rescaled endpoints (MS Lemma 2.2(ii)).

Each term of a series is enclosed exactly by chained floors / ceilings: for positive integers
floor(floor(a/b)/c) = floor(a/(bc)) and likewise for ceilings, so the lower and upper term sequences are the
floor and ceiling of the exact terms (or bound them, after multiplications by positive enclosed factors).
Internal work uses P + guard bits, guard > lg(number of roundings) + 2, so the returned widths are a few
units.  Constants are cached by scale (rounded up to a multiple of 64) and moved down outward.
"""

from __future__ import annotations

import functools
from fractions import Fraction
from math import isqrt

__all__ = ["pi_interval", "ln2_interval", "exp_point", "exp_interval", "sincos_pi", "sqrt_interval",
           "isqrt_ceil", "two_over_sqrt_pi_interval", "mul_interval", "div_interval", "rescale"]


def _cdiv(a: int, b: int) -> int:
    """ceil(a / b) for an int a and b > 0 (exact)."""
    return -((-a) // b)


def _shr_floor(a: int, s: int) -> int:
    """floor(a 2^-s); an exact left shift when s < 0."""
    return a >> s if s >= 0 else a << -s


def _shr_ceil(a: int, s: int) -> int:
    """ceil(a 2^-s); an exact left shift when s < 0."""
    return -((-a) >> s) if s >= 0 else a << -s


def rescale(lo: int, hi: int, P_from: int, P_to: int) -> tuple[int, int]:
    """Outward conversion of [lo, hi] 2^-P_from to scale 2^-P_to (exact when P_to >= P_from)."""
    s = P_from - P_to
    return _shr_floor(lo, s), _shr_ceil(hi, s)


def _guard(P: int) -> int:
    """Guard bits for a series at scale P: > lg(number of floor/ceiling roundings) + 2 (at most ~P terms)."""
    return max(P, 1).bit_length() + 8


def _up64(n: int) -> int:
    return -(-n // 64) * 64


def _check_scale(P: int) -> None:
    if not isinstance(P, int) or isinstance(P, bool) or P < 0:
        raise ValueError(f"scale P must be an int >= 0, got {P!r}")


# -- pi and ln 2 (MS Lemma 2.2(i)). ---------------------------------------------------------------


def _atan_inv(x: int, W: int) -> tuple[int, int]:
    """[lo, hi] 2^-W containing atan(1/x) for an integer x >= 2: partial sums of the alternating series
    sum_k (-1)^k / ((2k+1) x^(2k+1)) with each term enclosed by its exact floor / ceiling, plus the
    remainder bound |tail| <= first omitted term (terms decrease)."""
    x2 = x * x
    plo, phi = (1 << W) // x, _cdiv(1 << W, x)          # floor / ceil of 2^W / x^(2k+1)
    slo = shi = 0
    k = 0
    while True:
        d = 2 * k + 1
        tlo, thi = plo // d, _cdiv(phi, d)
        if k & 1:
            slo, shi = slo - thi, shi - tlo
        else:
            slo, shi = slo + tlo, shi + thi
        plo, phi = plo // x2, _cdiv(phi, x2)
        k += 1
        nxt = _cdiv(phi, 2 * k + 1)                     # >= the first omitted term
        if nxt <= 1:
            return slo - nxt, shi + nxt


@functools.lru_cache(maxsize=64)
def _pi_fixed(W: int) -> tuple[int, int]:
    a_lo, a_hi = _atan_inv(5, W)
    b_lo, b_hi = _atan_inv(239, W)
    return 16 * a_lo - 4 * b_hi, 16 * a_hi - 4 * b_lo   # pi = 16 atan(1/5) - 4 atan(1/239)


def pi_interval(P: int) -> tuple[int, int]:
    """[lo, hi] 2^-P containing pi, hi - lo <= 2 (MS Lemma 2.2(i): Machin's formula)."""
    _check_scale(P)
    W = _up64(P + _guard(P))
    return rescale(*_pi_fixed(W), W, P)


@functools.lru_cache(maxsize=64)
def _ln2_fixed(W: int) -> tuple[int, int]:
    """2 sum_k 1/((2k+1) 3^(2k+1)) at scale 2^-W: exact floor/ceiling terms; once the next term is <= 1
    unit, the tail (ratio < 1/9, so <= 9/8 of that term) adds at most 2 units to the upper sum."""
    plo, phi = (1 << W) // 3, _cdiv(1 << W, 3)          # floor / ceil of 2^W / 3^(2k+1)
    slo = shi = 0
    k = 0
    while True:
        d = 2 * k + 1
        slo, shi = slo + plo // d, shi + _cdiv(phi, d)
        plo, phi = plo // 9, _cdiv(phi, 9)
        k += 1
        if _cdiv(phi, 2 * k + 1) <= 1:
            return 2 * slo, 2 * (shi + 2)


def ln2_interval(P: int) -> tuple[int, int]:
    """[lo, hi] 2^-P containing ln 2, hi - lo <= 2 (MS Lemma 2.2(i))."""
    _check_scale(P)
    W = _up64(P + _guard(P))
    return rescale(*_ln2_fixed(W), W, P)


# -- exp (MS Lemma 2.2(iii)). ----------------------------------------------------------------------


_HALVINGS = 8   # e^y = (e^(y/2^8))^(2^8): fewer series terms; 8 squarings cost 8 extra guard bits


def _exp_small(Y: int, W: int) -> tuple[int, int]:
    """[lo, hi] 2^-W containing e^y for the exact y = Y 2^-W, |y| <= 1.

    With h = _HALVINGS and W' = W + h + 4: z = y/2^h = (Y 2^4) 2^-W' exactly; the Taylor partial sums of
    e^z have their term magnitudes |z|^k/k! enclosed by floor / ceiling recurrences and the Lagrange
    remainder |R_k| <= e^max(0,z) |z|^(k+1)/(k+1)! <= 3 T_k/(k+1) once T_k <= 1 unit; then h squarings of the
    positive enclosure (floor / ceiling) give e^y = (e^z)^(2^h); each squaring at most doubles the relative
    width, which the h + 4 extra bits absorb."""
    one = 1 << W
    if Y == 0:
        return one, one
    a = -Y if Y < 0 else Y
    if a > one:
        raise ValueError("_exp_small needs |y| <= 1")
    h = _HALVINGS
    Wp = W + h + 4
    a <<= 4                                    # |z| = a 2^-Wp
    tlo = thi = slo = shi = 1 << Wp
    k = 0
    while True:
        k += 1
        den = k << Wp
        tlo, thi = (tlo * a) // den, _cdiv(thi * a, den)
        if Y < 0 and k & 1:
            slo, shi = slo - thi, shi - tlo
        else:
            slo, shi = slo + tlo, shi + thi
        if thi <= 1 and k >= 2:
            rem = _cdiv(3 * thi, k + 1)
            slo, shi = slo - rem, shi + rem
            break
    for _ in range(h):                         # (e^z)^2, positive: floor / ceiling of the squares
        slo, shi = (slo * slo) >> Wp, _cdiv(shi * shi, 1 << Wp)
    return slo >> (h + 4), _cdiv(shi, 1 << (h + 4))


def exp_point(X: int, Pin: int, P: int) -> tuple[int, int]:
    """[lo, hi] 2^-P containing exp(X 2^-Pin) (exact dyadic argument; MS Lemma 2.2(iii)).

    Reduction x = m ln 2 - r with m = round(x / ln 2) and r in [r_lo, r_hi] from :func:`ln2_interval`;
    e^x = 2^m e^{-r}.  e^{-r} <= e^{-r_lo} <= E_hi, and e^{-r} >= e^{-r_hi} >= E_lo (1 - (r_hi - r_lo))
    (e^{-d} >= 1 - d), with [E_lo, E_hi] from :func:`_exp_small`; then one outward shift by m.  The
    working scale keeps P + m + guard bits, so the width is a few units for every argument.
    exp(0) = 1 exactly; x < -(P+2) ln 2 gives [0, 1]."""
    _check_scale(P)
    _check_scale(Pin)
    if X == 0:
        return 1 << P, 1 << P
    base = max(P, Pin)
    W = base + _guard(base) + (abs(X) >> Pin).bit_length() + 2
    if X > 0:                                     # e^x ~ 2^m, m <= 1.5 x: keep P + m bits of e^{-r}
        W += (3 * (X >> Pin)) // 2 + 2
    Llo, Lhi = ln2_interval(W)
    Xw = X << (W - Pin)
    if Xw < -(P + 2) * Lhi:                       # x < -(P+2) ln 2: 0 < e^x < 2^-(P+2)
        return 0, 1
    m = (2 * Xw + Llo) // (2 * Llo)               # ~ round(x / ln 2); any integer m is valid
    rlo, rhi = (m * Llo - Xw, m * Lhi - Xw) if m >= 0 else (m * Lhi - Xw, m * Llo - Xw)
    Elo, Ehi = _exp_small(-rlo, W)
    elo = Elo - _cdiv(Elo * (rhi - rlo), 1 << W)
    s = W - P - m
    return max(_shr_floor(elo, s), 0), _shr_ceil(Ehi, s)


def exp_interval(lo: int, hi: int, Pin: int, P: int) -> tuple[int, int]:
    """[lo', hi'] 2^-P containing exp(x) for every x in [lo, hi] 2^-Pin (exp is increasing)."""
    return exp_point(lo, Pin, P)[0], exp_point(hi, Pin, P)[1]


# -- sin and cos of rational multiples of pi (MS Lemma 2.2(iv)). ----------------------------------


def _sincos_small(X: int, W: int) -> tuple[tuple[int, int], tuple[int, int]]:
    """((clo, chi), (slo, shi)) 2^-W containing cos x and sin x for the exact x = X 2^-W in [0, 1].

    One pass over the terms x^k/k! (magnitudes enclosed by floor / ceiling recurrences): odd k feed the
    sine series, even k the cosine series, with alternating signs.  Both series have decreasing terms for
    x <= 1, so each |tail| is at most its first omitted term, which is <= x^(k+1)/(k+1)! <= T_k; we stop
    once T_k <= 1 unit (and k >= 2)."""
    one = 1 << W
    if X == 0:
        return (one, one), (0, 0)
    if not 0 < X <= one:
        raise ValueError("_sincos_small needs 0 <= x <= 1")
    tlo = thi = clo = chi = one
    slo = shi = 0
    k = 0
    while True:
        k += 1
        den = k << W
        tlo, thi = (tlo * X) // den, _cdiv(thi * X, den)
        neg = (k >> 1) & 1                       # sign (-1)^floor(k/2) of the k-th term
        if k & 1:
            slo, shi = (slo - thi, shi - tlo) if neg else (slo + tlo, shi + thi)
        else:
            clo, chi = (clo - thi, chi - tlo) if neg else (clo + tlo, chi + thi)
        if thi <= 1 and k >= 2:
            return (clo - thi, chi + thi), (slo - thi, shi + thi)


def sincos_pi(f, P: int) -> tuple[tuple[int, int], tuple[int, int]]:
    """((clo, chi), (slo, shi)) 2^-P containing cos(pi f) and sin(pi f) for an exact rational f
    (MS Lemma 2.2(iv)).  Exact reduction: f mod 2; f >= 1 negates both; f > 1/2 maps to 1 - f (negates
    cos); f > 1/4 maps to 1/2 - f (swaps cos and sin).  For f in (0, 1/4], x = pi f lies in
    [x_lo, x_hi] = [floor(pi_lo f), ceil(pi_hi f)] <= 0.79 < pi/2, where sin increases and cos decreases:
    sin x in [sin x_lo, sin x_lo + (x_hi - x_lo)], cos x in [cos x_lo - (x_hi - x_lo), cos x_lo] (derivatives
    bounded by 1), with cos x_lo, sin x_lo from :func:`_sincos_small`.  Quarter turns are exact points."""
    _check_scale(P)
    f = Fraction(f) % 2
    cs, ss, swap = 1, 1, False
    if f >= 1:
        f, cs, ss = f - 1, -cs, -ss
    if f > Fraction(1, 2):
        f, cs = 1 - f, -cs
    if f > Fraction(1, 4):
        f, swap = Fraction(1, 2) - f, True
    if f == 0:
        c, s = (1 << P, 1 << P), (0, 0)
    else:
        W = P + _guard(P)
        plo, phi = pi_interval(W)
        xlo, xhi = (plo * f.numerator) // f.denominator, _cdiv(phi * f.numerator, f.denominator)
        (clo, chi), (slo, shi) = _sincos_small(xlo, W)
        D = xhi - xlo                            # |sin'|, |cos'| <= 1 on [x_lo, x_hi]
        c = rescale(clo - D, chi, W, P)          # cos decreasing: cos x in [cos x_hi, cos x_lo]
        s = rescale(slo, shi + D, W, P)          # sin increasing: sin x in [sin x_lo, sin x_hi]
    if swap:
        c, s = s, c
    if cs < 0:
        c = (-c[1], -c[0])
    if ss < 0:
        s = (-s[1], -s[0])
    return c, s


# -- square roots, products, quotients (MS Lemma 2.2(ii)). ----------------------------------------


def isqrt_ceil(n: int) -> int:
    """ceil(sqrt(n)) for an int n >= 0 (exact)."""
    r = isqrt(n)
    return r if r * r == n else r + 1


def sqrt_interval(lo: int, hi: int, Pin: int, P: int) -> tuple[int, int]:
    """[lo', hi'] 2^-P containing sqrt(x) for every x in [lo, hi] 2^-Pin, lo >= 0: the endpoints are
    rescaled outward to 2^-2P and their exact integer square roots taken (sqrt is increasing)."""
    if lo < 0:
        raise ValueError("sqrt_interval needs lo >= 0")
    s = Pin - 2 * P
    return isqrt(_shr_floor(lo, s)), isqrt_ceil(_shr_ceil(hi, s))


def mul_interval(a: tuple[int, int], b: tuple[int, int], P: int) -> tuple[int, int]:
    """[lo, hi] 2^-P containing x y for x in a 2^-P and y in b 2^-P (any signs; floor / ceiling)."""
    pr = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(pr) >> P, _shr_ceil(max(pr), P)


def div_interval(a: tuple[int, int], b: tuple[int, int], P: int) -> tuple[int, int]:
    """[lo, hi] 2^-P containing x / y for x in a 2^-P and y in b 2^-P with b[0] > 0 (floor / ceiling)."""
    if b[0] <= 0:
        raise ZeroDivisionError("div_interval needs a positive divisor interval")
    lo = (a[0] << P) // (b[1] if a[0] >= 0 else b[0])
    hi = _cdiv(a[1] << P, b[0] if a[1] >= 0 else b[1])
    return lo, hi


@functools.lru_cache(maxsize=64)
def _tsp_fixed(W: int) -> tuple[int, int]:
    plo, phi = pi_interval(2 * W)
    slo, shi = sqrt_interval(plo, phi, 2 * W, W)        # sqrt(pi) at scale 2^-W
    return (2 << (2 * W)) // shi, _cdiv(2 << (2 * W), slo)


def two_over_sqrt_pi_interval(P: int) -> tuple[int, int]:
    """[lo, hi] 2^-P containing 2/sqrt(pi) (pi from :func:`pi_interval`, exact isqrt, exact division)."""
    _check_scale(P)
    W = _up64(P + _guard(P))
    return rescale(*_tsp_fixed(W), W, P)
