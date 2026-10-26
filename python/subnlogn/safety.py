"""Runtime safety net (an end-to-end consistency check): an end-to-end consistency check of every product.

NOT part of the algorithm.  The certified recovery check of :func:`subnlogn.multiply.multiply`
(|v_j - c_j| <= eps_cert = 3.19/128, MS Thm 7.1 part 1) sees only the transform outputs; a fault
downstream of it (a wrong coefficient handed to the carry pass, a broken carry or concatenation)
would return a wrong product silently.  This module checks the returned product against the
operands modulo a few fixed word-size moduli,

    prod = a * b  (mod m)   for m in SAFETY_MODULI = (2^64 - 1, 2^64 - 59, 2^64 - 83, 2^64 - 95, 2^61 - 1),

using only O(n)-time reductions of the long operands by one word-size modulus each (a mod m,
b mod m, prod mod m) and one word-size product per modulus -- never a long product, so the check
is independent of every multiplication routine of the package and costs O(n) per modulus.

Detection guarantee (deterministic).  The moduli are pairwise coprime: 2^64 - 1 = 3 * 5 * 17 * 257 *
641 * 65537 * 6700417 has no factor above 2^23, the other four are primes above 2^60 (certified by a
deterministic Miller-Rabin test in tests/test_safety_net.py).  Their product M exceeds 2^316, so a
wrong product P' != P passes only if M divides P' - P: every error of absolute value < 2^316 is
detected, and so is every error k * 2^j with 0 < |k| < 2^61 (each modulus is odd and does not divide
k), in particular any change of a single radix-2^b digit or coefficient.  The moduli are fixed
(reproducible runs); they are unrelated to the algorithm's radix 2^b and to its internal moduli.

On by default (``Ctx.safety_net``), counted as ``safety.residue_check``; a failure raises
:class:`SafetyNetError` (an explicit raise, active under ``python -O`` as well).
"""

from __future__ import annotations

__all__ = ["SAFETY_MODULI", "SafetyNetError", "check_product"]

#: Fixed word-size moduli of the safety net (pairwise coprime; product > 2^316; see module doc).
SAFETY_MODULI = ((1 << 64) - 1, (1 << 64) - 59, (1 << 64) - 83, (1 << 64) - 95, (1 << 61) - 1)


class SafetyNetError(AssertionError):
    """The returned product disagrees with the operands modulo a safety-net modulus."""


def check_product(a: int, b: int, prod: int, inst=None, moduli: tuple[int, ...] = SAFETY_MODULI) -> None:
    """Raise :class:`SafetyNetError` unless ``prod = a * b (mod m)`` for every m in ``moduli``
    (a, b, prod non-negative).  Cost: three O(n) single-modulus reductions and one word-size product
    per modulus; no long multiplication (module doc)."""
    for m in moduli:
        if (a % m) * (b % m) % m != prod % m:
            raise SafetyNetError(f"product fails the safety-net residue check modulo {m} "
                                 "(runtime safety net; not part of the algorithm)")
    if inst is not None:
        inst.hit("safety.residue_check")
