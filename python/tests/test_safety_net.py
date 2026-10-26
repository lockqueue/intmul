"""Runtime safety net: every product returned by ``multiply`` is checked against the
operands modulo fixed word-size moduli (subnlogn.safety).  Not part of the algorithm; on by default,
counted, and it catches a tampered coefficient that the certified recovery check cannot see (the
tamper happens after recovery)."""

import random

import pytest

import subnlogn.multiply as mm
from subnlogn.context import Ctx
from subnlogn.multiply import multiply
from subnlogn.safety import SAFETY_MODULI, SafetyNetError, check_product
from subnlogn.schedule import faithful_schedule, test_policy, test_schedule


def _is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 3.3 * 10^24 (bases 2..37)."""
    bases = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    if n < 2:
        return False
    for p in bases:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d, s = d // 2, s + 1
    for a in bases:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def test_moduli_certificate():
    """2^64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417; the other moduli are primes above 2^60;
    pairwise coprime with product above 2^316 (the module's detection guarantee)."""
    f = [3, 5, 17, 257, 641, 65537, 6700417]
    prod = 1
    for x in f:
        assert _is_prime(x)
        prod *= x
    assert SAFETY_MODULI[0] == prod == (1 << 64) - 1
    for m in SAFETY_MODULI[1:]:
        assert _is_prime(m) and m > 1 << 60
    from math import gcd
    M = 1
    for i, m in enumerate(SAFETY_MODULI):
        for m2 in SAFETY_MODULI[i + 1:]:
            assert gcd(m, m2) == 1
        M *= m
    assert M > 1 << 316


def test_check_product_accepts_and_rejects():
    rng = random.Random(1)
    for n in (1, 64, 65, 1000, 5000):
        a, b = rng.getrandbits(n), rng.getrandbits(n)
        check_product(a, b, a * b)
        for k, j in ((1, 0), (5, n), (-3, max(0, 2 * n - 3)), (1, 7 * n // 4)):
            wrong = a * b + k * (1 << j)
            if wrong >= 0:
                with pytest.raises(SafetyNetError):
                    check_product(a, b, wrong)


@pytest.mark.parametrize("which", ["faithful", "test_policy3", "test2d"])
def test_on_by_default_and_counted(which):
    sch = {"faithful": faithful_schedule(), "test_policy3": test_policy(3),
           "test2d": test_schedule(base_threshold=2)}[which]
    ctx = Ctx(schedule=sch)
    assert ctx.safety_net is True
    rng = random.Random(2)
    a, b = rng.getrandbits(700), rng.getrandbits(650)
    assert multiply(a, b, ctx) == a * b
    assert ctx.inst.counts["safety.residue_check"] == ctx.inst.counts["multiply.call"] == 1


@pytest.mark.parametrize("which", ["faithful", "test_policy3"])
@pytest.mark.parametrize("delta", [1, 5, -3])
def test_tampered_coefficient_is_caught(monkeypatch, which, delta):
    """Tamper demo: shift one recovered coefficient (after the certified recovery check) by
    +1, +5 or -3.  The safety net raises; with it switched off the wrong product comes back."""
    sch = faithful_schedule() if which == "faithful" else test_policy(3)
    orig = mm.carry_propagate

    def tampered(coeffs, b):
        c = list(coeffs)
        j = len(c) // 3
        c[j] += delta
        assert c[j] >= 0                                    # random operands: c_j is large
        return orig(c, b)

    monkeypatch.setattr(mm, "carry_propagate", tampered)
    rng = random.Random(3)
    a, b = rng.getrandbits(900) | (1 << 899), rng.getrandbits(900) | (1 << 899)
    with pytest.raises(SafetyNetError):
        multiply(a, b, Ctx(schedule=sch))
    off = Ctx(schedule=sch, safety_net=False)
    assert multiply(a, b, off) != a * b                    # the tamper is real
    assert off.inst.counts.get("safety.residue_check", 0) == 0
