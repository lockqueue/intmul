"""SPEC_WALSH §8 W-T4 (positional maps) and W-T5 (layout compile); SPEC_WALSH §4, R5 §7.2."""

from collections import Counter

import pytest
from hypothesis import given, settings, strategies as st

import path_model as PM
from subnlogn.m6.policy import LAYER_TEST
from subnlogn.middle3.layout import layout_plan
from subnlogn.walsh.gadget import WalshCtx
from subnlogn.walsh.positional import (
    apply_positional_oracle, compile_layout, compose, cycles, elementary_cnot, execute_positional_map, inverse,
    make_slices, move_address_bits, two_involutions,
)
from walsh_helpers import RNG, engine, fresh_inst, rand_disk


def maps_for(m0, rng):
    """Identity, a transposition, odd and even cycles, a cross-slice swap, the full reversal, a random map."""
    ident = list(range(m0))
    out = [ident]
    if m0 >= 2:
        t = list(ident)
        t[0], t[m0 - 1] = t[m0 - 1], t[0]
        out.append(t)
        rev = ident[::-1]
        out.append(rev)
        cyc = ident[1:] + ident[:1]                                   # one m0-cycle (odd or even length)
        out.append(cyc)
    if m0 >= 5:
        c3 = list(ident)
        c3[0], c3[2], c3[4] = 2, 4, 0                                 # 3-cycle
        out.append(c3)
    if m0 >= 4:
        c2 = list(ident)
        c2[1], c2[3] = 3, 1
        c2[0], c2[2] = 2, 0                                           # two disjoint transpositions
        out.append(c2)
    rnd = list(ident)
    rng.shuffle(rnd)
    out.append(rnd)
    return out


@pytest.mark.parametrize("m0", [1, 2, 3, 4, 5, 6, 7, 8])
@pytest.mark.parametrize("h,d", [(1, 2), (2, 3), (3, 4), (1, 4), (2, 2)])
def test_positional_maps_base_engine(m0, h, d):
    rng = RNG(m0 * 31 + h * 7 + d)
    z = rand_disk(m0, 1, 8, rng)
    inst = fresh_inst()
    w = WalshCtx(d=d, h=h, inst=inst)
    for dest in maps_for(m0, rng):
        assert execute_positional_map(z, dest, 8, w) == apply_positional_oracle(z, dest)
    if m0 < h:                                                     # no chunk: every target is a leftover
        assert inst.counts["walsh.slice_batch"] == 0


@pytest.mark.parametrize("m0,h,d", [(5, 1, 2), (6, 2, 3), (7, 2, 3), (8, 3, 4)])
def test_positional_maps_network_engine(m0, h, d):
    rng = RNG(m0)
    z = rand_disk(m0, 2, 10, rng)
    inst = fresh_inst()
    w = WalshCtx(d=d, h=h, engine=engine("network", d, inst=inst), inst=inst)
    maps = maps_for(m0, rng)[1:4]
    for dest in maps:
        assert execute_positional_map(z, dest, 10, w) == apply_positional_oracle(z, dest)
    # exact counts (exact count; path_model): CNOT batches per slice group, 6 Prop 14 layers each
    eng = PM.Eng(PM.nets()["C1"], d, LAYER_TEST, h, row_add="direct")
    exp = sum((PM.positional_map(dest, h, d, eng) for dest in maps), Counter())
    keys = [k for k in PM.PATH_KEYS if k.startswith(("walsh.", "m6."))]
    PM.assert_exact(inst.counts, exp, keys)
    assert exp["walsh.slice_batch"] > 0 and exp["m6.layer.network"] == 6 * exp["walsh.slice_batch"]


@settings(max_examples=60)
@given(st.integers(1, 10).flatmap(lambda n: st.permutations(list(range(n)))))
def test_two_involutions_factorization(dest):
    I0, I1 = two_involutions(list(dest))
    assert compose(I1, I0) == list(dest)
    assert compose(I0, I0) == list(range(len(dest))) == compose(I1, I1)
    assert sorted(x for c in cycles(list(dest)) for x in c) == list(range(len(dest)))
    for x in range(1 << len(dest)):
        assert move_address_bits(move_address_bits(x, I0), I1) == move_address_bits(x, list(dest))


def test_three_cnot_swap_and_leftovers():
    """Each swap = a ^= b, b ^= a, a ^= b (three elementary CNOTs), positions from the MSB."""
    m0 = 5
    z = rand_disk(m0, 1, 6, RNG(3))
    for a, b in ((0, 4), (1, 2), (3, 4)):
        y = elementary_cnot(z, b, a, m0)
        y = elementary_cnot(y, a, b, m0)
        y = elementary_cnot(y, b, a, m0)
        dest = list(range(m0))
        dest[a], dest[b] = b, a
        assert y == apply_positional_oracle(z, dest)


def test_make_slices_counts():
    for m0 in range(1, 12):
        for h in (1, 2, 3):
            for d in (2, 3, 4):
                slices, slice_of, left = make_slices(m0, h, d)
                J = m0 // h
                assert len(slices) == h * (-(-J // d)) <= m0 // d + h          # (7.5)
                assert sorted(slice_of) == list(range(J * h)) and left == list(range(J * h, m0))
                assert all(1 <= s.D <= d for s in slices)


@pytest.mark.parametrize("t,ell,h", [((4, 4, 4), 2, 1), ((16, 8), 4, 2), ((32, 16), 5, 2), ((8, 4, 8), 3, 1)])
def test_compile_layout_matches_layout_plan(t, ell, h):
    """W-T5: L equals SPEC §5.2's final arrangement; U = B^-1 L^-1 (and != L^-1 B^-1 at (16,8,16))."""
    widths = [x.bit_length() - 1 for x in t]
    L, B, U, new, b, q = compile_layout(widths, ell, h)
    plan = layout_plan(t, ell, h)
    assert plan.pos == new and (b, q) == (plan.b, plan.q)
    assert L == [new[s] for s in plan.order0]
    assert U == compose(inverse(B), inverse(L))
    if t == (16, 8):
        assert U != compose(inverse(L), inverse(B))
    # executed by CNOT stages, L reproduces the layout's record permutation
    m0 = sum(widths)
    z = rand_disk(m0, 1, 8, RNG(m0))
    w = WalshCtx(d=len(t) + 1, h=h)
    moved = execute_positional_map(z, L, 8, w)
    amap = plan.address_map()
    ref = [None] * len(z)
    for x, rec in enumerate(z):
        ref[amap[x]] = rec
    assert moved == ref
