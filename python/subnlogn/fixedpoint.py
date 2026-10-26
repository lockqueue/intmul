"""Exact dyadic fixed-point arithmetic.

Implements the grids, the rounding map and the rounded primitives of the manuscript
(the companion manuscript [MS]), Section 2.1:

* Definition 2.1 (``def:grid``): grids  R~_q = {2^-q a : a in Z},  C~_q = {2^-q (a + i b)}.
* Eq. (quant-err): |Q_q(x) - x| <= 1/2 2^-q (real),  |Q_q(z) - z| <= sqrt(2)/2 2^-q (complex).
* "Rounded Arithmetic Primitives": RM_q(a, b) = Q_q(a b),  RD_q(z, d) = Q_q(z / d).

Representation
--------------
A real number on R~_q is the Python ``int`` ``a`` (its numerator); the scale ``q`` (number of
fractional bits) is carried by the caller.  A complex number on C~_q is a pair of ints ``(a, b)``
meaning (a + i b) 2^-q.  Arrays of complex grid points are two parallel lists ``re``, ``im``
sharing one scale.  There is no floating point anywhere in this module.

Every function below is exact except the explicitly named rounding steps; each docstring states
the error of the step it performs.

Rounding modes
--------------
``Rounding.HALF_EVEN``  Q_q of Definition 2.1: nearest grid point, ties to the even numerator.
                        This is the authoritative mode (``Schedule.rounding`` defaults to it).
``Rounding.HALF_UP``    nearest, ties toward +infinity: floor(x 2^q + 1/2).  This is ``rnd_shr``
                        of the C reference (reference_intmul_fastdft.c:215).  Same error bound.
``Rounding.TRUNC``      toward zero.  Error < 2^-q per real coordinate; never increases |x|.
                        Only used where a source explicitly asks for truncation.

Both nearest modes satisfy eq. (quant-err); they differ only on exact ties.
"""

from __future__ import annotations

import enum
from fractions import Fraction
from typing import Callable

__all__ = [
    "Rounding",
    "shr_half_even",
    "shr_half_up",
    "shr_trunc",
    "div_half_even",
    "div_half_up",
    "div_trunc",
    "rescale",
    "rm",
    "cmul",
    "rcmul",
    "csquare",
    "rd",
    "to_fraction",
    "from_fraction",
    "QUANT_REAL",
    "QUANT_COMPLEX_UP",
    "cabs2_fraction",
    "sup_norm_sq",
    "FxVec",
]

# ----------------------------------------------------------------------------------------------
# Error constants (multiples of 2^-q).
# ----------------------------------------------------------------------------------------------

#: Real nearest rounding error |Q_q(x) - x| <= QUANT_REAL * 2^-q  (eq. quant-err).
QUANT_REAL = Fraction(1, 2)
#: Rational upper bound for sqrt(2)/2 (complex nearest rounding, eq. quant-err):
#: 0.70711^2 = 0.5000045521 > 1/2.
QUANT_COMPLEX_UP = Fraction(70711, 100000)


# ----------------------------------------------------------------------------------------------
# Scale changes:  n 2^-(q+s)  ->  2^-q round(n 2^-s).
# ----------------------------------------------------------------------------------------------


def shr_half_even(n: int, s: int) -> int:
    """Return round(n / 2^s), nearest with ties to even (Q of Def. 2.1).  Error <= 1/2 (units of
    the result).  For s <= 0 the result is the exact left shift n * 2^-s."""
    if s <= 0:
        return n << -s
    q = n >> s
    r = n & ((1 << s) - 1)
    h = 1 << (s - 1)
    if r > h or (r == h and q & 1):
        return q + 1
    return q


def shr_half_up(n: int, s: int) -> int:
    """Return floor(n / 2^s + 1/2) (the C reference ``rnd_shr``).  Error <= 1/2."""
    if s <= 0:
        return n << -s
    return (n + (1 << (s - 1))) >> s


def shr_trunc(n: int, s: int) -> int:
    """Return n / 2^s truncated toward zero.  Error < 1; never increases |n / 2^s|."""
    if s <= 0:
        return n << -s
    if n >= 0:
        return n >> s
    return -((-n) >> s)


def div_half_even(num: int, den: int) -> int:
    """Return round(num / den), nearest with ties to even, for den != 0 (exact integer division
    with remainder, as in RD_q of §2.1).  Error <= 1/2."""
    if den < 0:
        num, den = -num, -den
    q, r = divmod(num, den)
    two_r = r << 1
    if two_r > den or (two_r == den and q & 1):
        return q + 1
    return q


def div_half_up(num: int, den: int) -> int:
    """Return floor(num / den + 1/2), den != 0.  Error <= 1/2."""
    if den < 0:
        num, den = -num, -den
    return ((num << 1) + den) // (den << 1)


def div_trunc(num: int, den: int) -> int:
    """Return num / den truncated toward zero, den != 0.  Error < 1."""
    q = abs(num) // abs(den)
    return q if (num >= 0) == (den > 0) else -q


class Rounding(enum.Enum):
    """Explicit rounding mode.  ``shr`` rounds a right shift, ``div`` rounds a division."""

    HALF_EVEN = "half_even"
    HALF_UP = "half_up"
    TRUNC = "trunc"

    @property
    def shr(self) -> Callable[[int, int], int]:
        return _SHR[self]

    @property
    def div(self) -> Callable[[int, int], int]:
        return _DIV[self]


_SHR = {
    Rounding.HALF_EVEN: shr_half_even,
    Rounding.HALF_UP: shr_half_up,
    Rounding.TRUNC: shr_trunc,
}
_DIV = {
    Rounding.HALF_EVEN: div_half_even,
    Rounding.HALF_UP: div_half_up,
    Rounding.TRUNC: div_trunc,
}


def rescale(n: int, q_from: int, q_to: int, shr: Callable[[int, int], int] = shr_half_even) -> int:
    """Move the grid value n 2^-q_from to the grid 2^-q_to.  Exact if q_to >= q_from (sign
    extension / zero fill, as in eq. (record-width)); otherwise one rounding, error <= 1/2 2^-q_to
    for the nearest modes."""
    return shr(n, q_from - q_to)


# ----------------------------------------------------------------------------------------------
# Rounded products and quotients (§2.1 "Rounded Arithmetic Primitives").
# ----------------------------------------------------------------------------------------------


def rm(a: int, b: int, q: int, shr: Callable[[int, int], int] = shr_half_even) -> int:
    """RM_q(a, b) for reals a, b on R~_q: exact integer product at scale 2q, one rounding to q.
    Error <= 1/2 2^-q."""
    return shr(a * b, q)


def cmul(ar: int, ai: int, br: int, bi: int, q: int,
         shr: Callable[[int, int], int] = shr_half_even) -> tuple[int, int]:
    """RM_q(a, b) for complex a, b on C~_q: 4 exact integer products, 2 additions, one rounding per
    coordinate from scale 2q to q.  Error <= sqrt(2)/2 2^-q."""
    return shr(ar * br - ai * bi, q), shr(ar * bi + ai * br, q)


def rcmul(a: int, br: int, bi: int, q: int,
          shr: Callable[[int, int], int] = shr_half_even) -> tuple[int, int]:
    """RM_q(a, b) for real a on R~_q and complex b on C~_q: 2 exact integer products, one rounding
    per coordinate.  Error <= sqrt(2)/2 2^-q."""
    return shr(a * br, q), shr(a * bi, q)


def csquare(ar: int, ai: int, q: int,
            shr: Callable[[int, int], int] = shr_half_even, mul=None) -> tuple[int, int]:
    """RM_q(a, a) for complex a (the pointwise square of Thm 7.1, step 2).  Error <= sqrt(2)/2 2^-q.
    ``mul``: the word-scale multiplier (``Ctx.word_mul``); None = Python's ``*``."""
    if mul is None:
        return shr(ar * ar - ai * ai, q), shr((ar * ai) << 1, q)
    return shr(mul(ar, ar) - mul(ai, ai), q), shr(mul(ar, ai) << 1, q)


def rd(z: int, d: int, q: int, div: Callable[[int, int], int] = div_half_even) -> int:
    """RD_q(z, d) = Q_q(z / d) for reals z, d on R~_q, d != 0: the numerator of z is scaled by 2^q
    and divided exactly with remainder by the numerator of d.  Error <= 1/2 2^-q."""
    return div(z << q, d)


# ----------------------------------------------------------------------------------------------
# Exact rational views (for tests, tables and error bookkeeping; never floats).
# ----------------------------------------------------------------------------------------------


def to_fraction(a: int, q: int) -> Fraction:
    """The exact rational value a 2^-q."""
    return Fraction(a, 1 << q) if q >= 0 else Fraction(a << -q)


def from_fraction(x: Fraction | int, q: int, div: Callable[[int, int], int] = div_half_even) -> int:
    """Q_q(x) for an exact rational x: one rounding, error <= 1/2 2^-q (nearest modes)."""
    x = Fraction(x)
    if q >= 0:
        return div(x.numerator << q, x.denominator)
    return div(x.numerator, x.denominator << -q)


def cabs2_fraction(re: int, im: int, q: int) -> Fraction:
    """|z|^2 exactly, for z = (re + i im) 2^-q."""
    return Fraction(re * re + im * im, 1 << (2 * q))


def sup_norm_sq(re: list[int], im: list[int], q: int) -> Fraction:
    """max_j |z_j|^2 exactly (the square of ||z||_inf with the complex modulus, §2.1)."""
    m = 0
    for a, b in zip(re, im):
        v = a * a + b * b
        if v > m:
            m = v
    return Fraction(m, 1 << (2 * q))


class FxVec:
    """A vector of complex grid points (re[j] + i im[j]) 2^-q.  Thin container used at API
    boundaries; hot loops work on the ``re``/``im`` lists directly."""

    __slots__ = ("re", "im", "q")

    def __init__(self, re: list[int], im: list[int], q: int):
        if len(re) != len(im):
            raise ValueError("re/im length mismatch")
        self.re = re
        self.im = im
        self.q = q

    def __len__(self) -> int:
        return len(self.re)

    @classmethod
    def zeros(cls, n: int, q: int) -> "FxVec":
        return cls([0] * n, [0] * n, q)

    def copy(self) -> "FxVec":
        return FxVec(list(self.re), list(self.im), self.q)

    def rescaled(self, q_to: int, shr: Callable[[int, int], int] = shr_half_even) -> "FxVec":
        """Exact if q_to >= q, else one rounding per coordinate (error <= sqrt(2)/2 2^-q_to)."""
        s = self.q - q_to
        return FxVec([shr(a, s) for a in self.re], [shr(b, s) for b in self.im], q_to)

    def fractions(self) -> list[tuple[Fraction, Fraction]]:
        return [(to_fraction(a, self.q), to_fraction(b, self.q)) for a, b in zip(self.re, self.im)]

    def sup_norm_sq(self) -> Fraction:
        return sup_norm_sq(self.re, self.im, self.q)

    def max_coord_bits(self) -> int:
        """max over coordinates of |numerator|.bit_length() (record-height monitoring)."""
        m = 0
        for a in self.re:
            m = max(m, abs(a).bit_length())
        for b in self.im:
            m = max(m, abs(b).bit_length())
        return m

    def __eq__(self, other: object) -> bool:
        return (isinstance(other, FxVec) and self.q == other.q and self.re == other.re
                and self.im == other.im)

    def __repr__(self) -> str:
        return f"FxVec(n={len(self)}, q={self.q})"
