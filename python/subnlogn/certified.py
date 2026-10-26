"""Certified, correctly rounded table entries (manuscript §2.2 ``sec:tables``, Lemma 2.2).

Contract
--------
Every public table function returns grid numerators n = Q_q(x) = round-half-even(2^q x)
(Def. 2.1 ``def:grid``; :func:`subnlogn.fixedpoint.shr_half_even`) of the exact real x, i.e. the
*correctly rounded* value.  This is stronger than the 2^-s accuracy of Lemma 2.2
(``lem:elementary``) and than the faithful rounding rule of S1 §7.5.  Returned
values are exact Python ints; there is no floating point anywhere.

Sources: MS = the companion manuscript [MS]; r1, r2, r3 = the authors' bridge derivations r1, r2, r3.

Error argument (why the outputs are the correctly rounded values)
----------------------------------------------------------------
1. *Enclosure.*  For a working precision prec we compute integers lo <= hi and a scale P with
   lo 2^-P <= x <= hi 2^-P.  With the default ``backend="exact"`` this is **unconditionally rigorous:
   only exact integer arithmetic** (no floating point, no mpmath, no assumption about any library):

   * :mod:`subnlogn.rigorous` for the elementary constants and functions (MS Lemma 2.2 (i)-(iv)):
     pi by Machin's formula and ln 2 by its 3^-(2k+1) series, each with an explicit remainder; exp of
     an exact dyadic by reduction x = m ln 2 - r, a Taylor series of e^{-r} with the Lagrange remainder
     and outward shifts, interval arguments by monotonicity; cos and sin of EXACT rational multiples of
     pi (every use here: twists, roots of unity, sin(pi delta), the carrier phase pi delta/t) by exact
     reduction to [0, 1/4], an interval argument pi f, monotonicity on [0, pi/2] and alternating
     series; square roots by exact integer square roots.  Every rounding is an explicit floor or
     ceiling.
   * The cross-check ``backend="mpmath"`` uses ``mpmath.iv`` for these instead: rigorous only given
     that mpmath's elementary functions are accurate to < 2^10 ulps (directed rounding is not relied
     upon: libmpi.mpi_exp and the constants round a prec + 14 or prec + 20 bit approximation in the
     requested direction and can miss by one ulp, e.g. exp(-91/64) at 45 bits, exp(-6) at 87 and 88
     bits), hence widened by 2^11 relative ulps (:func:`subnlogn.certcore._widen`) and converted
     outward by max(1 unit, 2^10 ulps) (``certcore._iv_dyadic``).  The two backends return identical
     values (the correctly rounded value is unique); the tests assert this on many random inputs.
   * exact integer arithmetic with directed rounding for everything else: floor/ceiling
     sequences for positive series, and midpoint-radius balls (m +- r) 2^-P with the product rule
     |xy - m1 m2 2^-2P| <= (|m1| r2 + |m2| r1 + r1 r2) 2^-2P plus one ulp for each floor.
   * explicit bounds for every truncated infinite sum: the positive erf series of Lemma 2.2(v)
     stops once the term ratio is <= 1/2 and adds the geometric tail bound (<= the last term);
     for large arguments erf(z) in [1 - e^{-z^2}/(z sqrt(pi)), 1]; skipped Gaussian taps of a
     folded filter are covered by sum_{e' >= e} |kappa_e'| <= |kappa_e| / (1 - beta_e), where
     beta_e = e^{-pi(2|s_e| + 1)/alpha^2} is the (decreasing) ratio of consecutive Gaussians.
2. *Decision.*  RHE(y) = round-half-even(y) is monotone, so if RHE(2^q lo 2^-P) equals
   RHE(2^q hi 2^-P) = n then RHE(2^q x) = n for the unknown x in between.  The test is exact
   (integer shifts), ties included.  Exact dyadic values (cos 0, quarter turns, the delta = 0
   identity filter, the carrier = 0 imaginary parts, empty residue classes) are produced as exact
   points, so they are decided immediately.
3. *Ziv refinement.*  If the two ends round differently, the guard (prec = q + guard, initially
   64) is doubled and the enclosure recomputed, up to the cap prec <= max(8 q, q + 4096)
   (:func:`prec_cap`).  At the cap we fall back to *faithful* rounding: if the enclosure has
   width <= 2^-(q+4), its midpoint is rounded, so |n 2^-q - x| <= 2^-q/2 + 2^-(q+5) < 2^-q
   (S1 §7.5).  Each fallback is recorded in :data:`FALLBACK_EVENTS` and announced
   by a :class:`CertifiedFallbackWarning`; a wider enclosure raises ArithmeticError.  For the
   transcendental values tabulated here a fallback has never been observed.

The backend is an explicit keyword argument of every public table function (default "exact"); there is
no global switch.  With the mpmath backend (and in :func:`correctly_rounded` when a caller passes iv
intervals) the iv working precision is saved and restored around every use (mpmath 1.3.0's ``iv`` has
no ``workprec``), so no global precision leaks between calls.  Pure-function caches
(``functools.lru_cache``) hold only constants keyed by exact parameters (and the backend).  The
enclosure core (balls, erf, Ziv, the fallback record, the mpmath conversions) is
:mod:`subnlogn.certcore`; its public names are re-exported here.
"""

from __future__ import annotations

import functools
import warnings
from dataclasses import dataclass
from fractions import Fraction
from math import gcd

from mpmath import iv

from . import rigorous as RG
from .checks import require
from .certcore import (  # noqa: F401  (re-exported public API)
    BACKENDS, FALLBACK_EVENTS, CertifiedFallbackWarning, _IV_EXTRA, _ball_down, _bmul, _check_backend,
    _check_pow2, _check_q, _erf_ball, _exp, _iv_ball, _iv_dyadic, _ivprec, _ln2, _pi, _scale, _ziv,
    correctly_rounded, fallback_events, prec_cap, reset_fallback_events,
)

__all__ = [
    "correctly_rounded", "unit_root", "G_alpha", "SolverCoeffs", "solver_coeffs",
    "folded_kernel", "alpha_iv", "prec_cap", "CertifiedFallbackWarning", "FALLBACK_EVENTS",
    "fallback_events", "reset_fallback_events", "phase_table", "chirp_index", "BACKENDS",
]


def _ball(iv_pair: tuple[int, int]) -> tuple[int, int]:
    """The ball (mid, rad) at the same scale containing the integer interval [lo, hi]."""
    lo, hi = iv_pair
    mid = (lo + hi) >> 1
    return mid, hi - mid


def _ceil_div(a: int, b: int) -> int:
    """ceil(a / b) for b > 0 (exact)."""
    return -((-a) // b)


# -- Roots of unity. -------------------------------------------------------------------------------


@functools.lru_cache(maxsize=1 << 16)
def _cos_sin_octant(hn: int, hd: int, q: int, backend: str = "exact") -> tuple[int, int]:
    """(Q_q cos 2 pi h, Q_q sin 2 pi h) for h = hn/hd in (0, 1/8] (Ziv).  Backend "exact": both enclosed
    by :func:`subnlogn.rigorous.sincos_pi` (2h is an exact rational); "mpmath": iv cos/sin."""
    def enc(prec):
        P = prec + 4
        if backend == "exact":
            (clo, chi), (slo, shi) = RG.sincos_pi(Fraction(2 * hn, hd), P)
            return [(clo, chi, P), (slo, shi, P)]
        wp = P + _IV_EXTRA
        with _ivprec(wp):
            th = 2 * _pi() * hn / hd
            c, s = iv.cos(th), iv.sin(th)
        return [_iv_dyadic(c, P, wp) + (P,), _iv_dyadic(s, P, wp) + (P,)]
    c, s = _ziv(enc, q, 2, ("unit_root", (hn, hd)))
    return c, s


def unit_root(num: int, den: int, q: int, *, backend: str = "exact") -> tuple[int, int]:
    """(Q_q cos(2 pi num/den), Q_q sin(2 pi num/den)) for a power of two ``den`` and any int
    ``num``: the twist roots zeta^k = e^{pi i k/r} = unit_root(k, 2r, q) of MS §2.2(b) and the
    base-FFT twiddles e^{2 pi i k/R} of MS §2.2(d).

    Exact reduction: num mod den, then the quarter turn and the octant (cos/sin swap), which
    commute with Q_q because RHE is odd.  Quarter turns are exact points; the remaining angle
    2 pi h, h in (0, 1/8], is enclosed (``backend``, module docstring) and decided by Ziv."""
    _check_pow2(den, "den", 1)
    _check_q(q)
    _check_backend(backend)
    one = 1 << q
    quarter, rem = divmod(4 * (num % den), den)  # angle = quarter pi/2 + 2 pi rem/(4 den)
    if rem == 0:
        return ((one, 0), (0, one), (-one, 0), (0, -one))[quarter]
    if 2 * rem <= den:  # rem/(4 den) <= 1/8
        g = gcd(rem, 4 * den)
        c, s = _cos_sin_octant(rem // g, 4 * den // g, q, backend)
    else:  # complementary angle pi/2 - phi: cos and sin swap
        g = gcd(den - rem, 4 * den)
        s, c = _cos_sin_octant((den - rem) // g, 4 * den // g, q, backend)
    return ((c, s), (-s, c), (-c, -s), (s, -c))[quarter]


@functools.lru_cache(maxsize=1 << 16)
def _disk_octant(hn: int, hd: int, p: int, backend: str = "exact") -> tuple[int, int]:
    """Disk-preserving numerators (trunc 2^p cos 2 pi h, trunc 2^p sin 2 pi h), h = hn/hd in (0, 1/8].

    SPEC §5.9 ``disk_round``: per component take the lower endpoint of a rigorous enclosure if it is
    >= 0 (the upper one if <= 0, else 0) and truncate toward zero to 2^-p.  The enclosure is refined
    (guard 64, 128, ... up to :func:`prec_cap`) until both endpoints truncate alike, so the result
    is Q_p of the exact value, |component| <= true |component|, error < 2^-p per component.  If
    still undecided at the cap, ``disk_round`` of the final enclosure is used (spec-compliant:
    error < width + 2^-p with width <= 2^-(p+2), so < 2 2^-p in modulus) and recorded."""
    g, cap = 64, prec_cap(p)
    while True:
        P = min(p + g, cap)
        if backend == "exact":
            encl = list(RG.sincos_pi(Fraction(2 * hn, hd), P))
        else:
            wp = P + _IV_EXTRA
            with _ivprec(wp):
                th = 2 * _pi() * hn / hd
                encl = [_iv_dyadic(iv.cos(th), P, wp), _iv_dyadic(iv.sin(th), P, wp)]
        sh = P - p
        rounded = [lo >> sh if lo >= 0 else -((-hi) >> sh) if hi <= 0 else 0 for lo, hi in encl]
        decided = all((lo >= 0 and lo >> sh == hi >> sh) or (hi <= 0 and (-hi) >> sh == (-lo) >> sh)
                      for lo, hi in encl)
        if decided:
            return rounded[0], rounded[1]
        if P >= cap:
            break
        g *= 2
    if any((hi - lo) << (p + 2) > 1 << P for lo, hi in encl):
        raise ArithmeticError(f"phase_table: enclosure of cos/sin(2 pi {hn}/{hd}) too wide at the cap")
    FALLBACK_EVENTS.append(("phase_table", (hn, hd), p))
    warnings.warn(f"certified.phase_table({hn}/{hd}): truncation undecided at prec {cap}; "
                  f"disk_round of the enclosure used (error < 2 2^-p)", CertifiedFallbackWarning)
    return rounded[0], rounded[1]


@functools.lru_cache(maxsize=256)
def _phase_table_cached(r: int, p: int, backend: str = "exact") -> tuple:
    one = 1 << p
    out = []
    for k in range(2 * r):  # angle 2 pi k/(2r) = quarter pi/2 + 2 pi rem/(8r)
        quarter, rem = divmod(4 * k, 2 * r)
        if rem == 0:
            out.append(((one, 0), (0, one), (-one, 0), (0, -one))[quarter])
            continue
        if rem <= r:  # rem/(8r) <= 1/8
            gg = gcd(rem, 8 * r)
            c, s = _disk_octant(rem // gg, 8 * r // gg, p, backend)
        else:  # complementary angle: cos and sin swap
            gg = gcd(2 * r - rem, 8 * r)
            s, c = _disk_octant((2 * r - rem) // gg, 8 * r // gg, p, backend)
        z = ((c, s), (-s, c), (-c, -s), (s, -c))[quarter]
        require(z[0] * z[0] + z[1] * z[1] <= 1 << (2 * p), "phase left the disk (SPEC §5.9 phase_table)")
        out.append(z)
    return tuple(out)


def phase_table(r: int, p: int, *, backend: str = "exact") -> list[tuple[int, int]]:
    """Disk-grid phase table theta[k] ~ zeta^k = e^{pi i k/r}, k = 0..2r-1, numerators on 2^-p
    (SPEC §5.9 ``phase_table``/``disk_round``; Pr §9.4 L4308-4309: disk-grid approximations of
    zeta^{+-k} with error < 2 2^-p, "the exponential routine uses denominator 2r"; §9.5 L4360).

    Each component is the truncation toward zero of the exact component (:func:`_disk_octant`), so
    |component| <= |true component|, re^2 + im^2 <= 2^{2p} exactly (asserted) and the error is
    < sqrt(2) 2^-p < 2 2^-p.  Quarter turns (k a multiple of r/2) are exact; the octant reduction
    makes every circle symmetry exact: theta[k + r] = -theta[k], theta[2r - k] = conj(theta[k]),
    so theta^-_k = theta[(2r - k) mod 2r] = conj(theta[k]).  r is a power of two, p >= 1."""
    _check_pow2(r, "r", 1)
    _check_backend(backend)
    if not isinstance(p, int) or p < 1:
        raise ValueError(f"p must be an int >= 1, got {p!r}")
    return list(_phase_table_cached(r, p, backend))


def chirp_index(j, t, r: int) -> int:
    """E_j = sum_i j_i^2 (r/t_i) mod 2r, so that a_j = exp(pi i sum_i j_i^2/t_i) = zeta^{E_j} =
    theta[E_j] (SPEC §5.9 ``chirp_index``, reading R2 with s_i = 1 and a := e^{+pi i sum j^2/t}; the
    preprint's numerator -sum s_i j_i^2 (r/t_i) mod 2r, Pr L4344-4352, is that of conj(a)).  Each
    t_i must divide r (SPEC: t_i in {r/2, r}, so r/t_i in {1, 2}); for even t_i, E_j depends only
    on j_i mod t_i."""
    j, t = tuple(j), tuple(t)
    if len(j) != len(t) or any(ti < 1 or r % ti for ti in t):
        raise ValueError(f"need len(j) == len(t) and every t_i | r: j={j}, t={t}, r={r}")
    return sum(ji * ji * (r // ti) for ji, ti in zip(j, t)) % (2 * r)


# -- alpha and the passband function G_alpha. ---------------------------------------------------


def alpha_iv(w: int, prec: int, *, backend: str = "exact"):
    """The iv interval alpha = 2 sqrt(w ln 2 / pi) at working precision ``prec`` (MS Thm 5.1
    ``thm:deconv``: pi alpha^2 = 4 w ln 2).  ``iv.prec`` is restored afterwards.  Backend "exact":
    enclosed with :mod:`subnlogn.rigorous` at scale 2^-(prec+8); only the exact dyadic endpoints are
    converted (outward) to the returned iv interval."""
    _check_backend(backend)
    if backend == "exact":
        P = prec + 8
        L = RG.ln2_interval(P)
        v = RG.div_interval((w * L[0], w * L[1]), RG.pi_interval(P), P)
        lo, hi = RG.sqrt_interval(v[0], v[1], P, P)
        with _ivprec(prec):
            a, b = iv.ldexp(iv.mpf(2 * lo), -P), iv.ldexp(iv.mpf(2 * hi), -P)
            return iv.mpf([a.a, b.b])
    with _ivprec(prec):
        return 2 * iv.sqrt(w * _ln2() / _pi())


@functools.lru_cache(maxsize=256)
def _a_ball(w: int, P: int, backend: str = "exact") -> tuple[int, int]:
    """Ball for a = sqrt(pi) alpha = 2 sqrt(w ln 2) at scale 2^-P (MS eq. (ghat)).  Backend "exact":
    ln 2 from :func:`subnlogn.rigorous.ln2_interval` at scale 2^-2P and exact integer square roots."""
    if backend == "exact":
        Llo, Lhi = RG.ln2_interval(2 * P)
        lo, hi = RG.sqrt_interval(w * Llo, w * Lhi, 2 * P, P)
        return _ball((2 * lo, 2 * hi))
    with _ivprec(P + _IV_EXTRA):
        return _iv_ball(2 * iv.sqrt(w * _ln2()), P, P + _IV_EXTRA)


def _G_enclosure(xi: Fraction, w: int, prec: int, backend: str = "exact") -> tuple[int, int, int]:
    """[lo, hi] 2^-(P+1) containing G_alpha(xi) = (erf(a(xi+1/2)) - erf(a(xi-1/2)))/2."""
    P = prec + 8
    am, ar = _a_ball(w, P, backend)
    n, d = abs(xi.numerator), xi.denominator  # G_alpha is even
    Alo, Ahi = _erf_ball(*_scale(am, ar, 2 * n + d, 2 * d), P, backend)
    Blo, Bhi = _erf_ball(*_scale(am, ar, 2 * n - d, 2 * d), P, backend)
    return Alo - Bhi, Ahi - Blo, P + 1


def G_alpha(xi: Fraction, w: int, q: int, *, backend: str = "exact") -> int:
    """Q_q(G_alpha(xi)) with G_alpha(xi) = (1/2)[erf(a(xi + 1/2)) - erf(a(xi - 1/2))],
    a = sqrt(pi) alpha = 2 sqrt(w ln 2), alpha = 2 sqrt(w ln 2/pi): the continuous Fourier
    transform g-hat of the sinc-Gaussian kernel, MS eq. (ghat) (Thm 4.1 ``thm:poisson``),
    r2 eq. (4.3).  ``xi`` is an exact rational; w >= 1 (the lemmas use w >= 8)."""
    xi = Fraction(xi)
    _check_q(q)
    _check_backend(backend)
    if not isinstance(w, int) or w < 1:
        raise ValueError(f"w must be an int >= 1, got {w!r}")
    return _ziv(lambda prec: [_G_enclosure(xi, w, prec, backend)], q, 1, ("G_alpha", (xi, w)))[0]


# -- Column solver coefficients of the negative half-bin drop-in. ----------------------------------


@dataclass(frozen=True)
class SolverCoeffs:
    """Correctly rounded solver scalars of one column (r2 (8.2), (4.15)-(4.16)); grid 2^-q.

    ``c0`` = Q_q(c_0), ``c1`` = Q_q(c_1), ``mu`` = Q_q(1/M), ``a`` = Q_q(min/max) with
    M = max(c_0, c_1); ``forward`` = (c_0 > c_1) selects the forward sweep (r2 §4.6)."""

    c0: int
    c1: int
    mu: int
    a: int
    forward: bool


def _solver_enclosure(u: int, t: int, w: int, prec: int, backend: str = "exact"):
    """(forward or None, enclosures of c0, c1, 1/M, min/max) from three erf balls.

    With y = (2u+1)/(2t): c0 = G(y) = (E_A - E_B)/2, c1 = G(1 - y) = (E_C + E_B)/2 where
    E_A = erf(a(y + 1/2)), E_B = erf(a(y - 1/2)), E_C = erf(a(3/2 - y)); c0 - c1 is enclosed
    directly as (E_A - E_C)/2 - E_B.  Quotients use floor/ceiling of exact integer divisions."""
    P = prec + 8
    am, ar = _a_ball(w, P, backend)
    Alo, Ahi = _erf_ball(*_scale(am, ar, 2 * u + 1 + t, 2 * t), P, backend)
    Blo, Bhi = _erf_ball(*_scale(am, ar, 2 * u + 1 - t, 2 * t), P, backend)
    Clo, Chi = _erf_ball(*_scale(am, ar, 3 * t - 2 * u - 1, 2 * t), P, backend)
    P1 = P + 1  # halves are exact at scale 2^-(P+1)
    c0, c1 = (Alo - Bhi, Ahi - Blo), (Clo + Blo, Chi + Bhi)
    Dlo, Dhi = Alo - Chi - 2 * Bhi, Ahi - Clo - 2 * Blo
    if Dlo <= 0 <= Dhi:
        return None, None
    fwd = Dlo > 0
    (Mlo, Mhi), (mlo, mhi) = (c0, c1) if fwd else (c1, c0)
    if Mlo <= 0:
        return None, None
    one2 = 1 << (2 * P1)
    mu = (one2 // Mhi, -((-one2) // Mlo), P1)
    ratio = ((max(mlo, 0) << P1) // Mhi, -((-(mhi << P1)) // Mlo), P1)
    return fwd, [c0 + (P1,), c1 + (P1,), mu, ratio]


def solver_coeffs(u: int, t: int, w: int, q: int, *, backend: str = "exact") -> SolverCoeffs:
    """Column solver scalars of the 2D / per-axis negative half-bin drop-in (r2 §8 eq. (8.2),
    §4.5-4.6 eqs. (4.15)-(4.16); MS §2.2(c), eq. (c0-c1) with the half-bin shift):
    y = (u + 1/2)/t, c0 = G_alpha(y), c1 = G_alpha(y - 1), M = max(c0, c1), a = min/max in (0, 1).

    Returns Q_q of c0, c1, 1/M and a, each from the exact real value (not from rounded ones),
    and forward = (c0 > c1), decided rigorously and checked against u < t/2 (r2 §8;
    |c0 - c1| >= 7/(4t), r3 eq. (4.10)).  t is a power of two >= 2 and 0 <= u < t."""
    _check_pow2(t, "t", 2)
    _check_q(q)
    _check_backend(backend)
    if not isinstance(u, int) or not 0 <= u < t:
        raise ValueError(f"need 0 <= u < t, got u={u!r}, t={t}")
    if not isinstance(w, int) or w < 1:
        raise ValueError(f"w must be an int >= 1, got {w!r}")
    state: dict = {}

    def enc(prec):
        fwd, encl = _solver_enclosure(u, t, w, prec, backend)
        if fwd is None:  # sign of c0 - c1 not yet separated: [-1, 1] is never decided
            return [(-(1 << (prec + 9)), 1 << (prec + 9), prec + 9)] * 4
        state["forward"] = fwd
        return encl

    vals = _ziv(enc, q, 4, ("solver_coeffs", (u, t, w)))
    if "forward" not in state:
        raise ArithmeticError(f"solver_coeffs{(u, t, w)}: sign of c0 - c1 undecided at the cap")
    if state["forward"] != (2 * u < t):
        raise ArithmeticError(f"solver_coeffs{(u, t, w)}: c0 > c1 must hold iff u < t/2 (r2 §8)")
    return SolverCoeffs(vals[0], vals[1], vals[2], vals[3], state["forward"])


# -- Folded modulated sinc-Gaussian filters. -------------------------------------------------------


def _root_table(t: int, P: int, backend: str = "exact") -> list:
    """Balls ((cos pi d/t), (sin pi d/t)) at scale 2^-P for d = 0..t-1; d = 0, t/2 exact.  Cached
    at the precision P' = P rounded up to a multiple of 64, then moved down by :func:`_ball_down`."""
    P64 = -(-P // 64) * 64
    return [tuple(_ball_down(m, r, P64 - P) for m, r in cs) for cs in _root_table_cached(t, P64, backend)]


@functools.lru_cache(maxsize=64)
def _root_table_cached(t: int, P: int, backend: str = "exact") -> tuple:
    """The table of :func:`_root_table` at scale 2^-P (backend "exact": :func:`subnlogn.rigorous.
    sincos_pi` of the exact rational d/t; "mpmath": iv cos/sin; symmetry for d > t/2)."""
    h, one = t // 2, 1 << P
    tab: list = [None] * t
    tab[0], tab[h] = ((one, 0), (0, 0)), ((0, 0), (one, 0))
    if backend == "exact":
        for d in range(1, h):
            c, s = RG.sincos_pi(Fraction(d, t), P)
            tab[d] = (_ball(c), _ball(s))
    else:
        wp = P + _IV_EXTRA
        with _ivprec(wp):
            pi = _pi()
            for d in range(1, h):
                th = pi * d / t
                tab[d] = (_iv_ball(iv.cos(th), P, wp), _iv_ball(iv.sin(th), P, wp))
    for d in range(h + 1, t):  # cos(pi - x) = -cos x, sin(pi - x) = sin x
        (cm, cr), s = tab[t - d]
        tab[d] = ((-cm, cr), s)
    return tuple(tab)


def _sweep(Am, Ar, tail, t, P, K, e, step, count, D, g, b, q2, alt, neg, stop) -> None:
    """Accumulate the real class sums A_d += sign * sigma^l * gamma_e / |e + delta| over the taps
    e, e + step, ... (``count`` of them); |e + delta| = D 2^-K with D += 2^K per step.

    gamma_e = e^{-pi s_e^2/alpha^2} by the ball recurrence gamma <- gamma beta, beta <- beta q2
    (q2 = e^{-2 pi/alpha^2}).  When the rigorous bound |term| / (1 - beta_first) of all
    remaining taps is <= ``stop`` ulps, they are skipped and that bound is added to the radius of
    every class they would hit (sum_{e'>=e} gamma_e'/|s_e'| <= gamma_e/|s_e| / (1 - beta_e))."""
    gm, gr = g
    bm, br = b
    qm, qr = q2
    one = 1 << P
    den = one - bm - br
    inv = -((-one) // den) if den > 0 else 0  # >= 1/(1 - beta) >= 1/(1 - beta_e)
    dD = 1 << K
    for i in range(count):
        tm = (gm << K) // D
        tr = ((gr << K) // D) + 2
        if inv and (tm + tr) * inv <= stop:
            T, left = (tm + tr) * inv, count - i
            hit = range(t) if left >= t else {(e + step * k) % t for k in range(left)}
            for c in hit:
                tail[c] += T
            return
        c = e % t
        if alt and (e // t) & 1:
            tm = -tm
        if neg:
            tm = -tm
        Am[c] += tm
        Ar[c] += tr
        nr = ((gm * br + bm * gr + gr * br) >> P) + 2
        gm, gr = (gm * bm) >> P, nr
        nr = ((bm * qr + qm * br + br * qr) >> P) + 2
        bm, br = (bm * qm) >> P, nr
        e += step
        D += dD


def _fold_constants_exact(j: int, K: int, t: int, w: int, carrier: int, P: int) -> list:
    """Balls at scale 2^-P of sin(pi delta)/pi, e^{-lam delta^2}, e^{-lam (2 delta + 1)},
    e^{-lam (1 - delta)^2}, e^{-lam (3 - 2 delta)}, e^{-2 lam} and, with a carrier, cos and sin of
    pi delta/t, for delta = j 2^-K in (0, 1) and lam = pi/alpha^2 = pi^2/(4 w ln 2): exact integer interval
    arithmetic only (:mod:`subnlogn.rigorous`), at 16 guard bits, then outward to balls."""
    P2 = P + 16
    Pi, L = RG.pi_interval(P2), RG.ln2_interval(P2)
    lam = RG.div_interval(RG.mul_interval(Pi, Pi, P2), (4 * w * L[0], 4 * w * L[1]), P2)
    delta = Fraction(j, 1 << K)
    out = [RG.div_interval(RG.sincos_pi(delta, P2)[1], Pi, P2)]
    D = 1 << K
    for num, den in ((j * j, D * D), (2 * j + D, D), ((D - j) ** 2, D * D), (3 * D - 2 * j, D), (2, 1)):
        # -lam num/den lies in [-ceil(lam_hi num/den), -floor(lam_lo num/den)] 2^-P2 (num, den > 0)
        out.append(RG.exp_interval(-_ceil_div(lam[1] * num, den), -((lam[0] * num) // den), P2, P2))
    if carrier:
        out += list(RG.sincos_pi(delta / t, P2))
    return [_ball(RG.rescale(lo, hi, P2, P)) for lo, hi in out]


def _fold_enclosure(delta: Fraction, t: int, m: int, w: int, carrier: int, prec: int,
                    stop_rel: int | None = None, backend: str = "exact") -> list:
    """Enclosures [Re h(0), Im h(0), Re h(1), ...] of the folded modulated kernel, delta in (0,1).

    With delta = j 2^-K, s_e = e + delta, lambda = pi/alpha^2 and sin(pi s_e) = (-1)^e sin(pi delta):
      h(d) = e^{c pi i (d + delta)/t} (-1)^d (sin(pi delta)/pi) A_d,
      A_d = sum_{l: |d + l t| <= m} sigma^l e^{-lambda s^2}/s,  s = d + l t + delta,
    with sigma = -1 for carrier c = +-1 (the carrier e^{c pi i e/t} flips sign under e -> e + t:
    the modulated kernel is folded, r2 §4.7, r1 (4.3)) and sigma = +1 for c = 0; (-1)^e = (-1)^d
    as t is even.  ``stop_rel`` (tests only) forces the tap cutoff at tail <= 2^-stop_rel."""
    j, K = delta.numerator, delta.denominator.bit_length() - 1
    W = 2 * m + 1
    P = prec + K + W.bit_length() + w.bit_length() + 12
    if backend == "exact":
        balls = _fold_constants_exact(j, K, t, w, carrier, P)
    else:
        _check_backend(backend)
        wp = P + _IV_EXTRA
        with _ivprec(wp):
            pi = _pi()
            lam = pi * pi / (4 * w * _ln2())  # pi / alpha^2
            dl = iv.ldexp(iv.mpf(j), -K)
            vals = [iv.sin(pi * dl) / pi, _exp(-lam * dl * dl), _exp(-lam * (2 * dl + 1)),
                    _exp(-lam * (1 - dl) ** 2), _exp(-lam * (3 - 2 * dl)), _exp(-2 * lam)]
            if carrier:
                vals += [iv.cos(pi * dl / t), iv.sin(pi * dl / t)]
        balls = [_iv_ball(v, P, wp) for v in vals]
    (Sm, Sr), g0, b0, g1, b1, q2, *rot = balls
    Am, Ar, tail = [0] * t, [0] * t, [0] * t
    stop = 1 << (W.bit_length() + w.bit_length())  # tail <= stop ulps << 2^(P - prec)
    if stop_rel is not None:
        stop = 1 << max(0, P - stop_rel)
    alt = carrier != 0
    _sweep(Am, Ar, tail, t, P, K, 0, 1, m + 1, j, g0, b0, q2, alt, False, stop)
    _sweep(Am, Ar, tail, t, P, K, -1, -1, m, (1 << K) - j, g1, b1, q2, alt, True, stop)
    roots = _root_table(t, P, backend) if carrier else None
    out: list = []
    for d in range(t):
        am, ar = Am[d], Ar[d] + tail[d]
        if am == 0 and ar == 0:  # no tap in this residue class: exactly zero
            out += [(0, 0, P), (0, 0, P)]
            continue
        Bm, Br = _bmul(Sm, Sr, am, ar, P)
        if d & 1:
            Bm = -Bm
        if not carrier:
            out += [(Bm - Br, Bm + Br, P), (0, 0, P)]
            continue
        (cm, cr), (sm, sr) = roots[d]
        (xm, xr), (ym, yr) = rot
        u1, u2 = _bmul(cm, cr, xm, xr, P), _bmul(sm, sr, ym, yr, P)
        v1, v2 = _bmul(sm, sr, xm, xr, P), _bmul(cm, cr, ym, yr, P)
        Rm, Rr = _bmul(Bm, Br, u1[0] - u2[0], u1[1] + u2[1], P)  # cos(pi (d + delta)/t)
        Im, Ir = _bmul(Bm, Br, v1[0] + v2[0], v1[1] + v2[1], P)  # sin(pi (d + delta)/t)
        if carrier < 0:
            Im = -Im
        out += [(Rm - Rr, Rm + Rr, P), (Im - Ir, Im + Ir, P)]
    return out


def folded_kernel(delta: Fraction, t: int, m: int, w: int, q: int,
                  carrier: int = -1, *, backend: str = "exact") -> list[tuple[int, int]]:
    """The guarded folded filter table of MS §6.1 (d) (``lem:filter-norms``), for the modulated
    kernel of r2 eq. (8.1) folded modulo t (r2 §4.7, r1 eq. (4.3)): for d = 0..t-1 return
    (Q_q Re h(d), Q_q Im h(d)) with

      h(d) = sum_{|e| <= m, e = d (mod t)} kappa_e,   kappa_e = g(e + delta)   (MS §6.1 (a), (c)),
      g(s) = e^{carrier pi i s/t} sinc(s) e^{-pi s^2/alpha^2},  sinc(0) = 1,
      alpha = 2 sqrt(w ln 2/pi).

    carrier = -1 is the negative half-bin carrier (r2 Repair A), 0 the published real kernel
    (MS eq. (sinc-gauss)), +1 only for tests.  delta = j/2^k in [0, 1) is a dyadic Fraction,
    t a power of two >= 2 (smaller or larger than 2m + 1).  delta = 0 gives the exact identity
    filter h = (1, 0, ..., 0).  Each tap sum is enclosed rigorously (see :func:`_fold_enclosure`,
    :func:`_sweep`) and rounded once, correctly (module docstring)."""
    delta = Fraction(delta)
    _check_pow2(t, "t", 2)
    _check_q(q)
    if not 0 <= delta < 1 or delta.denominator & (delta.denominator - 1):
        raise ValueError(f"delta must be a dyadic rational in [0, 1), got {delta!r}")
    if not isinstance(m, int) or m < 0:
        raise ValueError(f"m must be an int >= 0, got {m!r}")
    if not isinstance(w, int) or w < 1:
        raise ValueError(f"w must be an int >= 1, got {w!r}")
    if carrier not in (-1, 0, 1):
        raise ValueError(f"carrier must be -1, 0 or +1, got {carrier!r}")
    _check_backend(backend)
    if delta == 0:  # sinc vanishes at the nonzero integers; kappa_0 = g(0) = 1 exactly
        return [(1 << q, 0)] + [(0, 0)] * (t - 1)
    vals = _ziv(lambda prec: _fold_enclosure(delta, t, m, w, carrier, prec, None, backend), q, 2 * t,
                ("folded_kernel", (delta, t, m, w, carrier)))
    return [(vals[2 * d], vals[2 * d + 1]) for d in range(t)]
