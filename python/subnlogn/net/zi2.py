"""Exact Gaussian dyadic numbers Z[i, 1/2] -- the scalar domain "ZI2" of the complex network.

SPEC §2.1 (domain "ZI2"), §2.3 and reading R3 (a = (1+i)/2, b = (1-i)/2) [Pr L1173-1210]: every entry of C_U and of
its inverse is a Gaussian integer divided by 2^m, so arrays over Z[i, 1/2] are preserved.  No floats, no sqrt(2).
"""

from __future__ import annotations

from fractions import Fraction


class ZI2:
    """The exact value (re + i*im) / 2**k with integers re, im and k >= 0, kept normalized.

    Normalization (k minimal): k == 0 or (re | im) is odd.  Equality and hashing use the normalized triple, so two
    ZI2 values are equal iff they are equal as complex numbers.  SPEC §1.5 (dyadic complex numbers), §2.1 ("ZI2").
    """

    __slots__ = ("re", "im", "k")

    def __init__(self, re: int = 0, im: int = 0, k: int = 0):
        if not (isinstance(re, int) and isinstance(im, int) and isinstance(k, int)):
            raise TypeError("ZI2 components must be ints")
        if k < 0:
            re, im, k = re << (-k), im << (-k), 0
        while k > 0 and not ((re | im) & 1):
            re >>= 1
            im >>= 1
            k -= 1
        if re == 0 and im == 0:
            k = 0
        object.__setattr__(self, "re", re)
        object.__setattr__(self, "im", im)
        object.__setattr__(self, "k", k)

    def __setattr__(self, name, value):
        raise AttributeError("ZI2 is immutable")

    # -- conversion ------------------------------------------------------------------------------------------------
    @staticmethod
    def of(x) -> "ZI2":
        """Convert an int, a dyadic Fraction or a ZI2 into a ZI2 (SPEC §2.1: gate entries lie in Z[i, 1/2])."""
        if isinstance(x, ZI2):
            return x
        if isinstance(x, bool):
            x = int(x)
        if isinstance(x, int):
            return ZI2(x, 0, 0)
        if isinstance(x, Fraction):
            d = x.denominator
            if d & (d - 1):
                raise ValueError(f"{x} is not dyadic")
            return ZI2(x.numerator, 0, d.bit_length() - 1)
        raise TypeError(f"cannot convert {type(x).__name__} to ZI2")

    def real_imag(self) -> tuple[Fraction, Fraction]:
        """(Re, Im) as exact Fractions."""
        return Fraction(self.re, 1 << self.k), Fraction(self.im, 1 << self.k)

    # -- arithmetic ------------------------------------------------------------------------------------------------
    def __add__(self, o):
        o = ZI2.of(o)
        k = max(self.k, o.k)
        return ZI2((self.re << (k - self.k)) + (o.re << (k - o.k)), (self.im << (k - self.k)) + (o.im << (k - o.k)), k)

    __radd__ = __add__

    def __neg__(self):
        return ZI2(-self.re, -self.im, self.k)

    def __sub__(self, o):
        return self + (-ZI2.of(o))

    def __rsub__(self, o):
        return ZI2.of(o) - self

    def __mul__(self, o):
        o = ZI2.of(o)
        return ZI2(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re, self.k + o.k)

    __rmul__ = __mul__

    def times_i(self) -> "ZI2":
        """Multiplication by i: (a + ib) i = -b + ia (exact)."""
        return ZI2(-self.im, self.re, self.k)

    def i_power(self, e: int) -> "ZI2":
        """Multiplication by i**e for any integer e (e taken mod 4)."""
        z = self
        for _ in range(e % 4):
            z = z.times_i()
        return z

    def half(self) -> "ZI2":
        """Exact halving z/2."""
        return ZI2(self.re, self.im, self.k + 1)

    def conj(self) -> "ZI2":
        """Complex conjugate."""
        return ZI2(self.re, -self.im, self.k)

    def is_zero(self) -> bool:
        """True iff the value is 0."""
        return self.re == 0 and self.im == 0

    # -- comparison ------------------------------------------------------------------------------------------------
    def __eq__(self, o):
        try:
            o = ZI2.of(o)
        except (TypeError, ValueError):
            return NotImplemented
        return (self.re, self.im, self.k) == (o.re, o.im, o.k)

    def __hash__(self):
        return hash((self.re, self.im, self.k))

    def __repr__(self):
        return f"ZI2({self.re}, {self.im}, {self.k})"


ZERO = ZI2(0)
ONE = ZI2(1)
I_UNIT = ZI2(0, 1)
#: a = (1 + i)/2 and b = (1 - i)/2 of (13)-(14), reading R3: C = HSH = aI + bX [Pr L1180-1204].
A_COEF = ZI2(1, 1, 1)
B_COEF = ZI2(1, -1, 1)


def i_pow(e: int) -> ZI2:
    """i**e as an exact ZI2 (e any integer)."""
    return (ONE, I_UNIT, ZI2(-1), ZI2(0, -1))[e % 4]
