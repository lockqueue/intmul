"""Rigorous enclosure core of the certified tables; the contract and the full error argument are
in :mod:`subnlogn.certified` (MS Lemma 2.2 ``lem:elementary``, Def. 2.1).

Contents: integer ball helpers, a rigorous erf (MS Lemma 2.2(v)), the rounding decision, and Ziv's
strategy with the recorded faithful fallback (:func:`_ziv`, :func:`correctly_rounded`).  The elementary
constants and functions come from a *backend*: ``"exact"`` (default) uses :mod:`subnlogn.rigorous`, which
is unconditionally rigorous: only exact integer arithmetic; ``"mpmath"`` (a cross-check only) uses the
widened mpmath.iv primitives :func:`_pi`, :func:`_ln2`, :func:`_exp` and the outward conversion
:func:`_iv_dyadic`, rigorous only if mpmath is accurate to < 2^10 ulps.  The backend is an explicit
argument of every function; there is no global switch.
"""

from __future__ import annotations

import warnings
from contextlib import contextmanager
from fractions import Fraction
from typing import Callable

from mpmath import iv
from mpmath.libmp import from_man_exp, fzero

from . import rigorous as RG
from .fixedpoint import shr_half_even

__all__ = ["correctly_rounded", "prec_cap", "CertifiedFallbackWarning", "FALLBACK_EVENTS",
           "fallback_events", "reset_fallback_events", "BACKENDS"]

#: Enclosure backends: "exact" (subnlogn.rigorous, default) and "mpmath" (cross-check only).
BACKENDS = ("exact", "mpmath")


def _check_backend(backend: str) -> None:
    if backend not in BACKENDS:
        raise ValueError(f"backend must be one of {BACKENDS}, got {backend!r}")

_IV_EXTRA = 16  # extra iv bits beyond the integer scale P of an enclosure
_IV_SLACK = 10  # mpmath's elementary functions: assumed accurate to < 2^_IV_SLACK ulps

#: Faithful-rounding fallbacks taken so far: (function name, arguments, q).  Should stay empty.
FALLBACK_EVENTS: list[tuple[str, tuple, int]] = []


class CertifiedFallbackWarning(UserWarning):
    """Ziv refinement hit :func:`prec_cap`; a faithfully (not correctly) rounded value was used."""


def fallback_events() -> list[tuple[str, tuple, int]]:
    """A copy of :data:`FALLBACK_EVENTS`."""
    return list(FALLBACK_EVENTS)


def reset_fallback_events() -> None:
    """Clear :data:`FALLBACK_EVENTS`."""
    FALLBACK_EVENTS.clear()


def prec_cap(q: int) -> int:
    """The Ziv cap on the working precision: prec <= max(8 q, q + 4096)."""
    return max(8 * q, q + 4096)


@contextmanager
def _ivprec(prec: int):
    """Run a block at iv working precision ``prec``; restore the previous precision after."""
    old = iv.prec
    iv.prec = prec
    try:
        yield
    finally:
        iv.prec = old


def _widen(I):
    """The positive iv interval I times [1 - 2^(_IV_SLACK+1-p), 1 + 2^(_IV_SLACK+1-p)], p = iv.prec:
    covers an error < 2^_IV_SLACK ulps of an accurate but not outward-rounded mpmath result."""
    k = iv.prec - _IV_SLACK - 1
    return I * iv.make_mpf((from_man_exp((1 << k) - 1, -k), from_man_exp((1 << k) + 1, -k)))


def _pi():
    return _widen(iv.pi)


def _ln2():
    return _widen(iv.ln2)


def _exp(x):
    return _widen(iv.exp(x))


# -- Exact conversions and the rounding decision. --------------------------------------------------


def _mpf_scaled(t: tuple, P: int, up: bool) -> int:
    """floor (``up`` False) or ceiling (``up`` True) of x 2^P, exactly, for a raw mpf tuple."""
    sign, man, exp, _ = t
    if not man:
        if t == fzero:
            return 0
        raise ArithmeticError("non-finite interval endpoint")
    if sign:
        man = -man
    e = exp + P
    if e >= 0:
        return man << e
    return -((-man) >> -e) if up else man >> -e


def _slack(t: tuple, P: int, wp: int) -> int:
    """Units of 2^-P covering 2^_IV_SLACK ulps (wp bits) of the mpf endpoint t; at least 1."""
    s = t[2] + t[3] + _IV_SLACK + 1 - wp + P if t[1] else 0  # |t| < 2^(exp + bc)
    return 1 << s if s > 0 else 1


def _iv_dyadic(I, P: int, wp: int) -> tuple[int, int]:
    """Integers (lo, hi) with [lo, hi] 2^-P containing the iv interval I computed at working
    precision wp: exact floor / ceiling of the endpoints, then outward by :func:`_slack`."""
    a, b = I._mpi_
    return (_mpf_scaled(a, P, False) - _slack(a, P, wp),
            _mpf_scaled(b, P, True) + _slack(b, P, wp))


def _iv_ball(I, P: int, wp: int) -> tuple[int, int]:
    """A ball (mid, rad) at scale 2^-P containing the iv interval I (see :func:`_iv_dyadic`)."""
    lo, hi = _iv_dyadic(I, P, wp)
    mid = (lo + hi) >> 1
    return mid, hi - mid


def _to_dyadic(x, prec: int) -> tuple[int, int, int]:
    """Normalise an enclosure (iv interval computed at precision prec, exact mpf / int / Fraction
    point, or (lo, hi, P)) to (lo, hi, P), outward at scale P = prec + 8 unless a triple."""
    if isinstance(x, tuple):
        return x
    P = prec + 8
    if hasattr(x, "_mpi_"):
        return _iv_dyadic(x, P, prec) + (P,)
    if hasattr(x, "_mpf_"):
        return _mpf_scaled(x._mpf_, P, False), _mpf_scaled(x._mpf_, P, True), P
    x = Fraction(x)
    num = x.numerator << P
    return num // x.denominator, -((-num) // x.denominator), P


def _decide(lo: int, hi: int, P: int, q: int) -> int | None:
    """RHE(2^q x) if it is the same for every x in [lo, hi] 2^-P, else None (monotonicity)."""
    n = shr_half_even(lo, P - q)
    return n if n == shr_half_even(hi, P - q) else None


def _ziv(enclose_vec: Callable[[int], list], q: int, count: int, label: tuple,
         guard: int = 64) -> list[int]:
    """Ziv's strategy for ``count`` values at once: decide each from ``enclose_vec(prec)``, doubling
    the guard for undecided ones up to :func:`prec_cap`, then the recorded faithful fallback."""
    out: list[int | None] = [None] * count
    g, cap = max(1, guard), prec_cap(q)
    while True:
        prec = min(q + g, cap)
        encl = enclose_vec(prec)
        for i in range(count):
            if out[i] is None:
                out[i] = _decide(*encl[i], q)
        if None not in out:
            return out  # type: ignore[return-value]
        if prec >= cap:
            break
        g *= 2
    for i in range(count):
        if out[i] is None:
            lo, hi, P = encl[i]
            if P < q or (hi - lo) << (q + 4) > (1 << P):
                raise ArithmeticError(f"{label[0]}{label[1]}: enclosure wider than 2^-(q+4) "
                                      f"at the precision cap {cap}")
            out[i] = shr_half_even(lo + hi, P + 1 - q)  # midpoint: error < 2^-q (faithful)
    FALLBACK_EVENTS.append((label[0], label[1], q))
    warnings.warn(f"certified.{label[0]}{label[1]}: Ziv cap prec={cap} reached at q={q}; "
                  f"faithful rounding used (error < 2^-q)", CertifiedFallbackWarning,
                  stacklevel=3)
    return out  # type: ignore[return-value]


def correctly_rounded(enclose: Callable[[int], object], q: int, guard: int = 64) -> int:
    """Return Q_q(x) = round-half-even(2^q x) (MS Def. 2.1) for the real x enclosed by
    ``enclose(prec)``: an ``mpmath.iv`` interval containing x computed at working precision
    ``prec`` (exact points as int / Fraction / mpf and integer triples (lo, hi, P) meaning
    [lo, hi] 2^-P are accepted too).  ``iv.prec`` is set to ``prec`` during the call and restored.
    iv results are treated as accurate to 2^10 ulps, not as outward-rounded (:func:`_iv_dyadic`),
    so exact ties must be passed as exact points; an ``enclose`` whose cancellation amplifies the
    error of mpmath's exp / pi / ln 2 should use the widened ones (:func:`_exp`, :func:`_pi`).

    Certified evaluation (MS Lemma 2.2 ``lem:elementary``, made adaptive): Ziv's strategy with
    prec = q + guard, guard doubled until both ends round alike (then the answer is exact by
    monotonicity of RHE), capped at :func:`prec_cap` with the recorded faithful fallback."""
    _check_q(q)

    def enc(prec):
        with _ivprec(prec):
            return [_to_dyadic(enclose(prec), prec)]
    name = getattr(enclose, "__qualname__", repr(enclose))
    return _ziv(enc, q, 1, ("correctly_rounded", (name,)), guard)[0]


def _check_pow2(v: int, name: str, least: int) -> None:
    if not isinstance(v, int) or v < least or v & (v - 1):
        raise ValueError(f"{name} must be a power of two >= {least}, got {v!r}")


def _check_q(q: int) -> None:
    if not isinstance(q, int) or q < 0:
        raise ValueError(f"q must be an int >= 0, got {q!r}")


# -- Integer balls and erf. ----------------------------------------------------------------------


def _scale(m: int, r: int, num: int, den: int) -> tuple[int, int]:
    """Ball (m +- r) times the exact rational num/den (den > 0); floor adds < 1 ulp; exact 0."""
    return ((m * num) // den, (r * abs(num) + den - 1) // den + 1) if num else (0, 0)


def _ball_down(m: int, r: int, sh: int) -> tuple[int, int]:
    """The ball (m +- r) 2^-(P+sh) at scale 2^-P: floor the midpoint (< 1 ulp), ceil the radius;
    exact when the ball is an exact point on the coarser grid."""
    if r == 0 and m & ((1 << sh) - 1) == 0:
        return m >> sh, 0
    return m >> sh, -((-r) >> sh) + 1


def _bmul(m1: int, r1: int, m2: int, r2: int, P: int) -> tuple[int, int]:
    """Ball product at scale 2^-P: floor of the midpoint product, radius rounded up (+1 ulp)."""
    return (m1 * m2) >> P, ((abs(m1) * r2 + abs(m2) * r1 + r1 * r2) >> P) + 2


def _erf_point(X: int, P: int, backend: str = "exact") -> tuple[int, int]:
    """(lo, hi) with lo 2^-P <= erf(x) <= hi 2^-P for the exact dyadic x = X 2^-P >= 0.

    MS Lemma 2.2(v): erf(x) = (2/sqrt(pi)) e^{-x^2} Sigma, Sigma = sum_n T_n, T_0 = x,
    T_n = T_{n-1} 2x^2/(2n+1) > 0, summed with floor (lower) and ceiling (upper) sequences at
    scale 2^-P2; once the next ratio 2x^2/(2n+3) <= 1/2 and T_n <= 1 ulp, the tail
    sum_{k>n} T_k <= T_n is added to the upper sum.  Large x (:func:`_erf_one`): erfc(x) <=
    e^{-x^2}/(x sqrt(pi)) <= 2^-(P+2) (x > 0), so erf(x) in [1 - 2^-P, 1].  The factor
    F = (2/sqrt(pi)) e^{-x^2} is enclosed by :func:`subnlogn.rigorous.exp_point` and
    :func:`subnlogn.rigorous.two_over_sqrt_pi_interval` (backend "exact") or by widened mpmath.iv."""
    if X <= 0:
        return 0, 0
    one, XX = 1 << P, X * X
    if _erf_one(X, P):
        return one - 1, one
    P2 = P + 2 * ((XX >> (2 * P)) + P + 8).bit_length() + 8
    sh = 2 * P - P2
    if sh >= 0:
        Wlo, Whi = (2 * XX) >> sh, -((-2 * XX) >> sh)  # 2x^2 at scale 2^-P2
    else:
        Wlo = Whi = (2 * XX) << -sh
    lim = 1 << P2
    Tlo = Thi = X << (P2 - P)
    Slo = Shi = Tlo
    n = 0
    while True:
        n += 1
        d = 2 * n + 1
        Tlo = ((Tlo * Wlo) >> P2) // d
        Thi = -((-((Thi * Whi + lim - 1) >> P2)) // d)
        Slo += Tlo
        Shi += Thi
        if Thi <= 1 and 2 * Whi <= (d + 2) * lim:
            Shi += Thi  # geometric tail: ratios <= 1/2 from here on
            break
    PF = P2 + max(0, Shi.bit_length() - P2)  # F ~ 2^-(integer bits of Sigma): keep P2 bits of F
    if backend == "exact":
        Q = PF + 8
        Elo, Ehi = RG.exp_point(-XX, 2 * P, Q)
        Tlo, Thi = RG.two_over_sqrt_pi_interval(Q)
        Flo, Fhi = RG.rescale((Elo * Tlo) >> Q, -((-(Ehi * Thi)) >> Q), Q, PF)
    else:
        _check_backend(backend)
        with _ivprec(P2 + 2 * _IV_EXTRA):
            F = 2 * _exp(-iv.ldexp(iv.mpf(XX), -2 * P)) / iv.sqrt(_pi())
        Flo, Fhi = _iv_dyadic(F, PF, P2 + 2 * _IV_EXTRA)
    s = P2 + PF - P
    lo = (Flo * Slo) >> s
    hi = -((-(Fhi * Shi)) >> s)
    return max(lo, 0), min(hi, one)


def _erf_one(X: int, P: int) -> bool:
    """x = X 2^-P >= 1 and x^2 >= 0.6932 (P+2) >= (P+2) ln 2, so 1 - erf(x) <= 2^-(P+2)."""
    return X >= (1 << P) and 10000 * X * X >= (6932 * (P + 2)) << (2 * P)


def _erf_ball(zm: int, zr: int, P: int, backend: str = "exact") -> tuple[int, int]:
    """(lo, hi) 2^-P containing erf(z) for every z in the ball (zm +- zr) 2^-P: erf at the exact
    midpoint plus the Lipschitz bound |erf'| <= 2/sqrt(pi) < 1.1284, or [1 - 2^-P, 1] when the
    whole ball is saturated (erf increasing); erf is odd."""
    if _erf_one(abs(zm) - zr, P):
        lo, hi = (1 << P) - 1, 1 << P
    else:
        lo, hi = _erf_point(abs(zm), P, backend)
        lip = (zr * 11284 + 9999) // 10000
        lo, hi = lo - lip, hi + lip
    return (-hi, -lo) if zm < 0 else (lo, hi)
