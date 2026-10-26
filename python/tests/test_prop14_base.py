"""Prop 14 base case (SPEC §4.7, §4.9): H0^{tD} = b^D S_D C^{tD} S_D (18) followed by one Q_p equals
the direct tensor of H0 butterflies followed by one Q_p -- bit-exact, not a tolerance."""

import random

import pytest

from subnlogn.m6.prop14 import hadamard_direct, simultaneous_H0_base


@pytest.mark.parametrize("nbits,D,r", [(1, 1, 2), (2, 2, 1), (3, 3, 4), (4, 2, 2), (5, 5, 2), (6, 4, 1),
                                       (6, 6, 2), (7, 3, 4)])
def test_identity_18_bit_exact(nbits, D, r):
    rng = random.Random(nbits * 10 + D)
    p = 20
    lim = (1 << p) * 7 // 10
    M = 1 << nbits
    recs = [([rng.randint(-lim, lim) for _ in range(r)], [rng.randint(-lim, lim) for _ in range(r)])
            for _ in range(M)]
    sel = rng.sample(range(nbits), D)
    a, sa = simultaneous_H0_base(recs, sel, p, p)
    b, sb = hadamard_direct(recs, sel, p, p)
    assert (a, sa) == (b, sb)
    ea, s1 = simultaneous_H0_base(recs, sel, p, p, truncate=False)
    eb, s2 = hadamard_direct(recs, sel, p, p, truncate=False)
    # exact values agree (scales may differ by the b^D bookkeeping)
    for (xr, xi), (yr, yi) in zip(ea, eb):
        assert [v << s2 for v in xr] == [v << s1 for v in yr]
        assert [v << s2 for v in xi] == [v << s1 for v in yi]
    for re, im in a:                                       # disk grid output
        assert all(u * u + v * v <= 1 << (2 * p) for u, v in zip(re, im))
