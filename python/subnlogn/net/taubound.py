"""Log bounds and the exact tau test of the triple-network certificates (SPEC §2.7 step 7) [Pr L1335-1357].

``log_bound(m, "crude")`` is the preprint's integer bound max(20, bitlen m) >= ln m [Pr L1340-1341];
``log_bound(m, "sharp")`` is the upper end of the certified rational enclosure ``ln_enclosure(m)`` (rigorous ln 2 from
``subnlogn.rigorous`` plus an exact atanh series with an explicit tail bound; no floats).  ``tau_test`` decides
eta 2^tau_exp >= L exactly, which certifies s/W < m^tau for tau = 1 - 2^-tau_exp.
"""

from __future__ import annotations

from fractions import Fraction

from .triple import TripleParams


def _dec(x, digits: int = 7) -> str:
    """A rational as a decimal string rounded UP at ``digits`` places (ints unchanged)."""
    x = Fraction(x)
    if x.denominator == 1:
        return str(x.numerator)
    q = -((-x.numerator * 10 ** digits) // x.denominator)
    sign = "-" if q < 0 else ""
    q = abs(q)
    return f"{sign}{q // 10 ** digits}.{q % 10 ** digits:0{digits}d}"


def ln_enclosure(m: int, P: int = 96) -> tuple[Fraction, Fraction]:
    """Certified rational enclosure lo <= ln m <= hi (integer m >= 1), no floats: ln m = k ln 2 + ln r with k the
    integer nearest log2 m (r = m / 2^k in [2^-1/2, 2^1/2)), ln 2 from ``rigorous.ln2_interval(P)`` (MS Lemma
    2.2(i)), ln r = 2 atanh(y) = 2 sum_j y^(2j+1)/(2j+1), y = (r - 1)/(r + 1), |y| < 0.18, summed exactly until
    the geometric tail bound 2|y|^(2n+1) / ((2n+1)(1 - y^2)) is below 2^-(P+4); all remaining terms have the sign
    of y, so the partial sum is one end of the enclosure and partial sum +- tail the other."""
    from ..rigorous import ln2_interval
    if not isinstance(m, int) or m < 1:
        raise ValueError("ln_enclosure needs an integer m >= 1")
    k = m.bit_length() - 1                      # 2^k <= m < 2^(k+1)
    if m * m >= 1 << (2 * k + 1):               # m >= 2^(k + 1/2): round up so that r < 2^(1/2)
        k += 1
    r = Fraction(m, 1 << k)
    y = (r - 1) / (r + 1)
    y2, t, S, n = y * y, y, Fraction(0), 0
    eps = Fraction(1, 1 << (P + 4))
    while True:
        S += t / (2 * n + 1)
        n += 1
        t *= y2                                 # t = y^(2n+1)
        tail = 2 * abs(t) / ((2 * n + 1) * (1 - y2))
        if tail < eps:
            break
    lnr = 2 * S
    lo2, hi2 = ln2_interval(P)
    ln2_lo, ln2_hi = Fraction(lo2, 1 << P), Fraction(hi2, 1 << P)
    lo = k * ln2_lo + (lnr if y >= 0 else lnr - tail)
    hi = k * ln2_hi + (lnr + tail if y >= 0 else lnr)
    return lo, hi


def log_bound(m: int, mode: str = "crude"):
    """An upper bound L >= log m.  'crude' (default; the preprint's argument [Pr L1340-1341]): m < 2^bitlen(m)
    and log 2 < 1 give the integer L = max(20, bitlen(m)) (20 for m = 10^6).  'sharp': the certified rational
    upper end of ``ln_enclosure(m)`` (ln 10^6 < 13.8155106, below SPEC_WALSH §1.3's 14)."""
    if mode == "crude":
        return max(20, m.bit_length())
    if mode == "sharp":
        return ln_enclosure(m)[1]
    raise ValueError(f"log_bound mode must be 'crude' or 'sharp', not {mode!r}")


def tau_test(p: TripleParams, tau_exp: int, mode: str = "crude") -> tuple[bool, Fraction]:
    """(passes, margin) of the exact test eta 2^tau_exp >= L, i.e. (W m - s) 2^tau_exp >= L W m, which certifies
    s/W < m^tau for tau = 1 - 2^-tau_exp: m^tau = m exp(-2^-tau_exp ln m) > m (1 - 2^-tau_exp ln m)
    >= m (1 - 2^-tau_exp L) >= m (1 - eta) = s/W (e^-y > 1 - y for y > 0) [Pr L1335-1357]; margin = eta 2^tau_exp
    - L (exact)."""
    sav = p.W * p.m - p.s
    eta = Fraction(sav, p.W * p.m)
    margin = eta * 2 ** tau_exp - log_bound(p.m, mode)
    return (sav > 0 and margin >= 0), margin
