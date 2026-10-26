"""Theorem-mode shape, cutoffs and the faithful dispatcher's decision (SPEC §6.1-§6.2; Pr (38),
L3878-3915; BR2 Thm 3 and (2.16)).

Fixed rationals of the printed theorem schedule (SPEC §6.1): beta = 1/2, delta = 1/16,
tau = sigma = 1 - 2^-50, c = 2^-56, lambda = 1 - 2^-52, lambda' = 1 - 2^-54, eps = 2^-75, C1 = 20,
kappa = 2^-182.  ``theorem_shape`` uses exact integer comparisons only: d = floor(K^eps) is the
largest d with d^(1/eps) <= K, decided by exponentiation by squaring that stops as soon as the
running power exceeds the bound (no floats, never a huge power).  d >= 2 needs K >= 2^(2^75), so
at every physically possible size the shape is None and the dispatcher runs the 2D fallback
(SPEC §6.4) -- a property of the schedule, not a shortcut.  The cutoff of SPEC §6.2 needs the
preprint's tape constant P_tape, which is not supplied; the cutoff certificate is therefore
absent (``cutoff_certificate() is None``) and is never fabricated.

Parameter rows (:class:`ParameterRow`): the printed row of SPEC §6.1 (Bluestein middle) and the two Walsh rows of
SPEC_WALSH §1.3 (kappa = 2^-47 and 2^-46, Walsh middle; SPEC_WALSH §9.1 faithful retuned schedule).  A row fixes the
shape exponents (eps, c) used by ``theorem_shape``, the Prop 14 policy exponents (beta, C1; the policy presets
``m6.policy.LAYER_WALSH_47`` / ``LAYER_WALSH_46``) and the certificate data (tau, sigma, lambda, lambda', kappa).
With the Walsh rows d >= 2 needs K >= 2^21 (eps = 1/21) or K >= 2^15 (eps = 1/15); the cutoff certificate is
absent for every row, so the dispatcher falls back at every size.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from .checks import require

__all__ = ["THEOREM_CONSTANTS", "ParameterRow", "XI", "ROW_PRINTED", "ROW_WALSH_47", "ROW_WALSH_46",
           "THEOREM_ROWS", "pow_le", "floor_rational_power", "TheoremShape", "theorem_shape",
           "cutoff_certificate", "theorem_mode_shape"]

THEOREM_CONSTANTS = {
    "beta": Fraction(1, 2), "delta": Fraction(1, 16), "tau": 1 - Fraction(1, 2 ** 50),
    "sigma": 1 - Fraction(1, 2 ** 50), "c": Fraction(1, 2 ** 56), "lambda": 1 - Fraction(1, 2 ** 52),
    "lambda_p": 1 - Fraction(1, 2 ** 54), "eps": Fraction(1, 2 ** 75), "C1": 20,
    "kappa": Fraction(1, 2 ** 182),
}


@dataclass(frozen=True)
class ParameterRow:
    """One parameter row of the theorem schedule (SPEC §6.1 printed row; SPEC_WALSH §1.3 Walsh rows): the middle it
    runs, the shape exponents (eps, c) of ``theorem_shape``, the Prop 14 policy exponents (beta, C1) and the
    certificate data (tau, sigma, lam = lambda, lam_p = lambda', kappa; delta is the printed 1/16 in every row,
    SPEC §6.1: the Walsh rows only change eps, c, beta, C1 and the certificate data)."""

    name: str
    middle: str
    eps: Fraction
    c: Fraction
    beta: Fraction
    C1: int
    tau: Fraction
    sigma: Fraction
    lam: Fraction
    lam_p: Fraction
    kappa: Fraction
    delta: Fraction = Fraction(1, 16)


#: xi = 2^-42 of SPEC_WALSH §1.3.
XI = Fraction(1, 2 ** 42)

ROW_PRINTED = ParameterRow(
    name="printed", middle="bluestein", eps=Fraction(1, 2 ** 75), c=Fraction(1, 2 ** 56), beta=Fraction(1, 2),
    C1=20, tau=1 - Fraction(1, 2 ** 50), sigma=1 - Fraction(1, 2 ** 50), lam=1 - Fraction(1, 2 ** 52),
    lam_p=1 - Fraction(1, 2 ** 54), kappa=Fraction(1, 2 ** 182))
ROW_WALSH_47 = ParameterRow(
    name="walsh47", middle="walsh", eps=Fraction(1, 21), c=XI / 4, beta=Fraction(1, 8), C1=20,
    tau=1 - 4 * XI, sigma=1 - XI, lam=1 - 7 * XI / 8, lam_p=1 - 3 * XI / 4, kappa=Fraction(1, 2 ** 47))
ROW_WALSH_46 = ParameterRow(
    name="walsh46", middle="walsh", eps=Fraction(1, 15), c=XI / 256, beta=Fraction(1, 64), C1=14,
    tau=1 - 4 * XI, sigma=1 - XI, lam=1 - 63 * XI / 64, lam_p=1 - 31 * XI / 32, kappa=Fraction(1, 2 ** 46))

#: The rows by name (``Schedule.theorem_row``).
THEOREM_ROWS = {row.name: row for row in (ROW_PRINTED, ROW_WALSH_47, ROW_WALSH_46)}


def pow_le(base: int, exp: int, bound: int) -> bool:
    """base**exp <= bound for integers base >= 1, exp >= 0, bound >= 0, by binary exponentiation
    that stops as soon as a partial power exceeds the bound (all factors are >= 1, so every partial
    product is a lower bound of the result).  Cost O(log bound) multiplications for base >= 2."""
    if base < 1 or exp < 0:
        raise ValueError("pow_le needs base >= 1 and exp >= 0")
    if base == 1 or exp == 0:
        return 1 <= bound
    result, sq, e = 1, base, exp
    while True:
        if e & 1:
            result *= sq
            if result > bound:
                return False
        e >>= 1
        if not e:
            return True
        sq *= sq
        if sq > bound:                      # a remaining set bit would multiply by >= sq
            return False


def floor_rational_power(K: int, eps: Fraction) -> int:
    """The largest integer d >= 1 with d <= K^eps, i.e. d^b <= K^a for eps = a/b (exact)."""
    eps = Fraction(eps)
    if K < 1 or not 0 < eps <= 1:
        raise ValueError("floor_rational_power needs K >= 1 and 0 < eps <= 1")
    a, b = eps.numerator, eps.denominator
    bound = K ** a
    lo, hi = 1, 2
    while pow_le(hi, b, bound):             # exponential search, then bisection
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if pow_le(mid, b, bound):
            lo = mid
        else:
            hi = mid
    return lo


@dataclass(frozen=True)
class TheoremShape:
    d: int
    ell: int
    r: int
    t: tuple[int, ...]
    chunk_bits: int


def theorem_shape(K_root: int, eps: Fraction = THEOREM_CONSTANTS["eps"],
                  c: Fraction = THEOREM_CONSTANTS["c"]) -> TheoremShape | None:
    """SPEC §6.1 ``theorem_shape``: d = floor(K^eps); None if d < 2; ell = ceil(K/d), r = 2^ell,
    short = d ell - K axes of length r/2 first, then d - short of length r (t_d = r), chunk_bits =
    floor(d^c).  The Walsh rows pass their own (eps, c) (SPEC_WALSH §9.1)."""
    d = floor_rational_power(K_root, eps)
    if d < 2:
        return None
    ell = -(-K_root // d)
    r = 1 << ell
    short = d * ell - K_root
    t = (r // 2,) * short + (r,) * (d - short)
    prod = 1
    for ti in t:
        prod *= ti
    require(prod == 1 << K_root and t[-1] == r, "theorem shape needs prod t_i = 2^K and t_d = r (SPEC §6.1)")
    return TheoremShape(d, ell, r, t, floor_rational_power(d, c))


def cutoff_certificate():
    """SPEC §6.2: the cutoff K_* = ceil(max{4096, P_tape, (4 C0)^(1/(1-20 eps)), 2^((64/(eps c))^2),
    2^(2/eps), 2^(2/(1-eps(1+c)))}) needs the preprint's tape constant P_tape, which the inputs do
    not supply (BR2 threshold qualification).  No certificate exists, so None is returned; theorem
    mode is never entered on an uncertified cutoff."""
    return None


def theorem_mode_shape(K_root: int, row: ParameterRow = ROW_PRINTED) -> TheoremShape | None:
    """The shape theorem mode would run under the parameter row ``row``, or None (fallback): theorem mode is entered
    only if ``theorem_shape(K_root, row.eps, row.c)`` returns a shape AND the cutoff certificate exists (SPEC §6.2;
    SPEC_WALSH §9.1 for the Walsh rows)."""
    shape = theorem_shape(K_root, row.eps, row.c)
    if shape is None or cutoff_certificate() is None:
        return None
    return shape
