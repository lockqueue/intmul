"""Lemma 16's positional layout L pinned against an independent transcription of its proof (mutant
M23: the bottom prefix slots listed for h = 0..b-1 instead of h = b-1..0 survived both suites, because the layout
tests only used shapes with b <= 1, where that list has at most one h).

The transcription below follows Pr L2878-2909 sentence by sentence (the plain-text rendering of [OAI26], checked
against openai_below_nlogn_layout.txt), with the preprint's 1-based axis numbers; it shares no code with
:mod:`subnlogn.middle3.layout` or :func:`subnlogn.walsh.positional.compile_layout`, which are compared with it on an
exhaustive grid (l <= 9, D <= 3) and 400 random shapes (l <= 40, D <= 8), many with b >= 2.
"""

import random

import pytest

from subnlogn.m6.lemma13 import bitwise_swap
from subnlogn.middle3.layout import execute_layout, layout_plan
from subnlogn.walsh.positional import compile_layout


def transcribe_layout(a, ell, K):
    """Pr L2878-2909 with 1-based axes i = 1..D (a = (a_1, ..., a_D), a_i = log2 t_i in {l - 1, l}).  Returns
    (b, q, initial, listed, exchanges, final): the slot orders before and after L, the prefix list in listing order
    and the chunk exchanges as pairs of chunk positions (0-based, left to right)."""
    D = len(a)
    # "Call an axis long if a_i = l and short if a_i = l - 1."
    assert all(x in (ell, ell - 1) for x in a) and 1 <= K <= ell - 1
    # "Name the original bit slots of axis i by (i, h), a_i - 1 >= h >= 0.  Initially these slots are in axis order
    #  and, within each axis, in decreasing h."
    initial = []
    for i in range(1, D + 1):
        h = a[i - 1] - 1
        while h >= 0:
            initial.append((i, h))
            h -= 1
    # "Put b = (l - 1) mod K, q = floor((l - 1)/K)."
    b, q = (ell - 1) % K, (ell - 1) // K
    # "First list (i, l - 1) for the length-2^l axes in increasing i.  Then list (i, h) for h = b - 1, ..., 0, and
    #  within each h in increasing i; this second list is empty if b = 0."
    listed = [(i, ell - 1) for i in range(1, D + 1) if a[i - 1] == ell]
    h = b - 1
    while h >= 0:
        for i in range(1, D + 1):
            listed.append((i, h))
        h -= 1
    # "Move each listed slot immediately after the prefix already formed, leaving all other slots in their relative
    #  order."  "There are at most D(b + 1) listed slots."
    assert len(listed) <= D * (b + 1)
    moved = set(listed)
    rest = [s for s in initial if s not in moved]
    # "The part of each axis left outside the prefix now consists of q consecutive K-bit chunks.  Number the axes by
    #  i and their chunks, from high to low, by j."
    chunk = {}
    for i in range(1, D + 1):
        mine = [s for s in rest if s[0] == i]
        assert len(mine) == q * K and [s[1] for s in mine] == sorted((s[1] for s in mine), reverse=True)
        for j in range(1, q + 1):
            chunk[(i, j)] = mine[(j - 1) * K: j * K]
    # "The remaining physical order changes from (1,1), (1,2), ..., (1,q), (2,1), ..., (D,q) to (1,1), (2,1), ...,
    #  (D,1), (1,2), ..., (D,q).  To obtain this order, scan its target positions from left to right.  At each
    #  position except the last, exchange the chunk currently there with the required chunk if they differ."
    current = [(i, j) for i in range(1, D + 1) for j in range(1, q + 1)]
    target = [(i, j) for j in range(1, q + 1) for i in range(1, D + 1)]
    exchanges = []
    for k in range(len(target) - 1):
        if current[k] != target[k]:
            other = current.index(target[k])
            current[k], current[other] = current[other], current[k]
            exchanges.append((k, other))
    assert current == target and len(exchanges) <= max(D * q - 1, 0)    # "at most Dq - 1 exchanges"
    final = listed + [s for c in target for s in chunk[c]]
    return b, q, initial, listed, exchanges, final


def transcribed_address(x, a, final):
    """L(x): "a record at address x moves to address Lx" -- the address bits travel with their named slots.  The
    address is the axis indices u_1, ..., u_D written left to right (u_1 most significant, SPEC §1.7), slot (i, h)
    being bit h of u_i, and the physical order ``final`` lists the slots from the most significant bit."""
    u = []
    for ai in reversed(a):
        u.append(x & ((1 << ai) - 1))
        x >>= ai
    u.reverse()
    y = 0
    for i, h in final:
        y = (y << 1) | ((u[i - 1] >> h) & 1)
    return y


def zero_based(slots):
    return [(i - 1, h) for i, h in slots]


def check_shape(a, ell, K, maps):
    """Compare layout_plan (orders, moves, address maps if ``maps``) and compile_layout with the transcription."""
    b, q, initial, listed, exchanges, final = transcribe_layout(a, ell, K)
    plan = layout_plan(tuple(1 << x for x in a), ell, K)
    assert (plan.b, plan.q, plan.n) == (b, q, sum(a))
    assert plan.order0 == zero_based(initial) and plan.order == zero_based(final)
    base = len(listed)
    assert plan.moves == [("prefix", s, k) for k, s in enumerate(zero_based(listed))] + \
        [("xchg", base + k * K, base + m * K, K) for k, m in exchanges]
    L, _, _, new, bw, qw = compile_layout(list(a), ell, K)
    assert (bw, qw) == (b, q) and new == {s: k for k, s in enumerate(zero_based(final))}
    assert L == [final.index(s) for s in initial]
    if maps:
        f, g = plan.address_map(), plan.address_map(inverse=True)
        for x in range(1 << plan.n):
            assert f[x] == transcribed_address(x, a, final)
            assert g[f[x]] == x
    return b


def test_preprint_examples():
    """The preprint's illustration (l = 6, K = 2, one long and one short axis, Pr L2910-2914) and two b >= 2 shapes
    worked by hand from the text: l = 7, K = 4 (b = 2, q = 1) and l = 9, K = 3 with three axes (b = 2, q = 2;
    three chunk exchanges)."""
    *_, final = transcribe_layout((6, 5), 6, 2)
    assert final == [(1, 5), (1, 0), (2, 0), (1, 4), (1, 3), (2, 4), (2, 3), (1, 2), (1, 1), (2, 2), (2, 1)]
    b, q, _, listed, ex, final = transcribe_layout((7, 6), 7, 4)
    assert (b, q, ex) == (2, 1, []) and listed == [(1, 6), (1, 1), (2, 1), (1, 0), (2, 0)]
    assert final[5:] == [(1, 5), (1, 4), (1, 3), (1, 2), (2, 5), (2, 4), (2, 3), (2, 2)]
    b, q, _, listed, ex, final = transcribe_layout((9, 8, 9), 9, 3)
    assert (b, q, ex) == (2, 2, [(1, 2), (2, 4), (3, 4)])
    assert listed == [(1, 8), (3, 8), (1, 1), (2, 1), (3, 1), (1, 0), (2, 0), (3, 0)]
    assert final[8:] == [(1, 7), (1, 6), (1, 5), (2, 7), (2, 6), (2, 5), (3, 7), (3, 6), (3, 5),
                         (1, 4), (1, 3), (1, 2), (2, 4), (2, 3), (2, 2), (3, 4), (3, 3), (3, 2)]
    for a, ell, K in (((6, 5), 6, 2), ((7, 6), 7, 4), ((9, 8, 9), 9, 3), ((7,), 7, 4), ((6,), 7, 4)):
        check_shape(a, ell, K, maps=sum(a) <= 13)


def test_layout_grid_against_transcription():
    """Every shape with 2 <= l <= 9, 1 <= K <= l - 1, D <= 3 axes and every long/short pattern (504 shapes, 98 of
    them with b >= 2); full address maps L and L^-1 wherever n = sum a_i <= 12 (190 shapes, 19 with b >= 2)."""
    count = b2 = mapped_b2 = 0
    for ell in range(2, 10):
        for K in range(1, ell):
            for D in range(1, 4):
                for mask in range(1 << D):
                    a = tuple(ell - ((mask >> i) & 1) for i in range(D))
                    maps = sum(a) <= 12
                    b = check_shape(a, ell, K, maps)
                    count += 1
                    b2 += b >= 2
                    mapped_b2 += b >= 2 and maps
    assert (count, b2, mapped_b2) == (504, 98, 19)


def test_layout_random_shapes_against_transcription():
    """400 random shapes: l <= 40, D <= 8, random K and long/short pattern (212 with b >= 2, 156 with chunk
    exchanges); address maps where n <= 12."""
    rng = random.Random(16)
    b2 = 0
    for _ in range(400):
        ell = rng.randint(2, 40)
        K = rng.randint(1, ell - 1)
        a = tuple(ell - rng.randint(0, 1) for _ in range(rng.randint(1, 8)))
        b2 += check_shape(a, ell, K, maps=sum(a) <= 12) >= 2
    assert b2 >= 200


@pytest.mark.parametrize("a,ell,K", [((7, 6), 7, 4), ((6, 5, 6), 6, 3), ((9, 8), 9, 3)])
def test_executed_layout_matches_transcription(a, ell, K):
    """execute_layout (Lemma 3 prefix moves, chunk exchanges by the bitwise base case) moves the record at x to the
    transcribed L(x), and back, on b >= 2 shapes (with two chunk exchanges at l = 9, K = 3)."""
    *_, exchanges, final = transcribe_layout(a, ell, K)
    plan = layout_plan(tuple(1 << x for x in a), ell, K)
    recs = list(range(1 << plan.n))
    out = execute_layout(plan, recs, bitwise_swap)
    assert all(out[transcribed_address(x, a, final)] == x for x in recs)
    assert execute_layout(plan, out, bitwise_swap, inverse=True) == recs
    assert (len(exchanges) > 0) == (a == (9, 8))
