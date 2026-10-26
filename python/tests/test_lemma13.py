"""Lemma 13 (packed selected-bit addition) and its exceptional repair: integer model brute force, the
stream procedure on complete rectangles, the cnet adapter, the Lemma 12 swap adapter.

Sources: SPEC §4.1, §4.2, §4.3, §4.11 (first bullet); Pr = the plain-text rendering of [OAI26]
L1928-2151 (Lemma 13, (20)-(24) and the repair L2065-2143).
"""

import itertools
import random

import pytest
from hypothesis import given, settings, strategies as st

import path_model as PM
from subnlogn.instrument import Instrument
from subnlogn.m6 import lemma13 as L13
from subnlogn.m6.cnet import _row_add_direct
from subnlogn.m6.policy import LAYER_TEST
from subnlogn.stream import Field, Shape, address_of, index_of

ORDERS = list(itertools.permutations("xyz"))


def bad_fn(mode, K, f, rho):
    if mode == "eq23":
        return lambda x, y, z: L13.is_bad(y, z, K, f, rho)
    return lambda x, y, z: not L13.all_segments_safe(x, y, z, K, f, rho)


# ------------------------------------------------------------------------------------ integer model
MODEL_CASES = [(2, 1, 0), (2, 2, 0), (2, 2, 1), (3, 1, 0), (2, 3, 0), (2, 3, 1), (2, 3, 2), (3, 2, 0), (3, 2, 1)]
SAFE_COUNTS = {}            # (f, K, rho) -> |B| of safe_segments, filled by the brute force (reported)


@pytest.mark.parametrize("f,K,rho", MODEL_CASES)
def test_integer_model_brute_force(f, K, rho):
    """SPEC §4.2 claims [Pr L2061-2101]: S0 is a bijection of [2^L]^3 with S0_inverse its inverse; for BOTH
    bad sets S0 == T0 off B, B is T0-invariant and S0(B) = B, i.e. T0 S0^{-1} permutes B; (23) gives
    B = the whole rectangle for K <= 5; safe_segments gives |B| = 1536 of 4096 at (f, K) = (2, 2)."""
    n = 1 << (f * K)
    triples = list(itertools.product(range(n), repeat=3))
    img = [L13.S0(*t, K, f, rho) for t in triples]
    assert len(set(img)) == n ** 3
    assert all(L13.S0_inverse(*s, K, f, rho) == t for s, t in zip(img, triples))
    for mode in L13.BAD_SETS:
        bad = bad_fn(mode, K, f, rho)
        B = {t for t in triples if bad(*t)}
        for t, s in zip(triples, img):
            if t not in B:
                assert s == L13.T0(*t, K, f, rho)
            assert (L13.T0(*t, K, f, rho) in B) == (t in B)
        assert {s for t, s in zip(triples, img) if t in B} == B
        if mode == "eq23":
            assert len(B) == n ** 3                                    # K <= 5: interval in (23) empty
        else:
            assert 0 < len(B) < n ** 3
            SAFE_COUNTS[(f, K, rho)] = len(B)
    if (f, K) == (2, 2):
        assert SAFE_COUNTS[(f, K, rho)] == 1536 and n ** 3 == 4096     # SPEC §4.2 record


def _lines_int(u, w, c):
    """The eight lines (20) on integers (no modulus), with the per-step trajectory."""
    v = {"y": u, "z": w}
    traj = [(u, w)]
    for tgt, oth, sgn, par in L13.ROTATIONS:
        if c and (v[oth] % 2) == par:
            v[tgt] += sgn
        traj.append((v["y"], v["z"]))
    return traj


def test_parity_cycling_and_displacement():
    """SPEC §4.1 'Why it works' [Pr L1998-2034]: with c = 1 the first four lines induce the cycle
    (00 01 10) on the parity corners of every square {2a, 2a+1} x {2b, 2b+1}, the last four (01 10 11);
    the output is (u + c(1 - 2(u mod 2)), w) (also for negative u), and each coordinate moves by <= 4."""
    for a in range(-3, 4):
        for b in range(-3, 4):
            for pu, pw in itertools.product((0, 1), repeat=2):
                u, w = 2 * a + pu, 2 * b + pw
                for c in (0, 1):
                    traj = _lines_int(u, w, c)
                    assert traj[-1] == (u + c * (1 - 2 * (u % 2)), w)
                    assert max(abs(p - u) for p, _ in traj) <= 4 and max(abs(q - w) for _, q in traj) <= 4
                    if c == 0:
                        assert set(traj) == {(u, w)}
                    else:
                        first = {(0, 0): (0, 1), (0, 1): (1, 0), (1, 0): (0, 0), (1, 1): (1, 1)}[(pu, pw)]
                        assert traj[4] == (2 * a + first[0], 2 * b + first[1])
                        second = {(0, 1): (1, 0), (1, 0): (1, 1), (1, 1): (0, 1), (0, 0): (0, 0)}[first]
                        assert traj[8] == (2 * a + second[0], 2 * b + second[1])


@settings(max_examples=300)
@given(st.integers(0, (1 << 9) - 1), st.integers(0, (1 << 9) - 1), st.integers(0, (1 << 9) - 1),
       st.integers(0, 2))
def test_integer_model_sampled_f3_K3(x, y, z, rho):
    """(f, K) = (3, 3): 2^27 triples is too many for brute force, so sample (Pr L2061-2101)."""
    f, K = 3, 3
    s = L13.S0(x, y, z, K, f, rho)
    assert L13.S0_inverse(*s, K, f, rho) == (x, y, z)
    t = L13.T0(x, y, z, K, f, rho)
    assert L13.is_bad(y, z, K, f, rho)                                   # K = 3 <= 5: always bad
    safe = L13.all_segments_safe(x, y, z, K, f, rho)
    assert safe == L13.all_segments_safe(*t, K, f, rho)                 # T0-invariant
    if safe:
        assert s == t                                                    # S0 = T0 off B


def test_rotations_are_eq20():
    """SPEC §1.3 R4 / §4.1: the eight lines in the order of (20) [Pr L1979-1997]."""
    assert L13.ROTATIONS == [("y", "z", -1, 0), ("z", "y", -1, 0), ("y", "z", +1, 0), ("z", "y", +1, 0),
                             ("z", "y", +1, 1), ("y", "z", +1, 1), ("z", "y", -1, 1), ("y", "z", -1, 1)]
    assert L13.rotation_offset(0b1011, 0b0001, 1, 3, 1, 0) == 0b0001      # only j_0 (j_2 is the top bit)
    assert L13.rotation_offset(0b1111, 0b0000, 0, 3, 1, 0) == 0b0011


# ------------------------------------------------------------------------------------ stream procedure
SPECTATORS = [(1, 1, 1, 1), (2, 1, 3, 1), (1, 3, 1, 2), (2, 2, 1, 1), (1, 1, 2, 3), (3, 1, 1, 2)]


def rectangle(order, L, spect):
    fs = [Field("N0", spect[0])]
    for i, c in enumerate(order):
        fs += [Field(c, 1 << L, 2), Field(f"N{i + 1}", spect[i + 1])]
    return Shape(tuple(fs), 1)


def check_rectangle(f, K, rho, order, spect, mode, swap=None):
    """Run Lemma 13 on the complete rectangle with record IDs as payloads and check every record's final
    position: only y_{j_i} ^= x_{j_i} (0 <= i < f) changes."""
    L = f * K
    sh = rectangle(order, L, spect)
    inst = Instrument()
    out, sh2 = L13.packed_selected_add(list(range(sh.volume)), sh, {c: c for c in "xyz"}, K, f, rho,
                                       bad_set=mode, swap=swap, inst=inst)
    assert sh2 == sh
    mask = sum(1 << (rho + i * K) for i in range(f))
    for i in range(sh.volume):
        a = address_of(sh, i)
        a["y"] ^= a["x"] & mask
        assert out[index_of(sh, a)] == i
    c = inst.counts
    assert c["lemma13.call"] == 1 and c["lemma13.top_xor"] == 1
    assert c["lemma13.rotation"] == (8 if f > 1 else 0)
    assert c.get("lemma13.swap", 0) == expected_swaps(f, order)
    return sh.volume, c


def expected_swaps(f: int, order) -> int:
    """Exchanges of one Lemma 13 call (SPEC §4.1; exact count): f = 1 none; else each of the eight
    lines (20) brings its target (y: four lines, z: four lines) to the physically rightmost chunk position by an
    exchange and back, so 8 [y not rightmost] + 8 [z not rightmost].  ``order`` = physical order, MSB first."""
    smin = {0: 2 - order.index("y"), 1: 2 - order.index("x"), 2: 2 - order.index("z")}   # dst, src, z
    one = PM.lemma13_row_add(PM.Eng(None, 2, LAYER_TEST, 1), smin, 0, 1, 2, f)
    assert one["lemma13.swap"] == (0 if f == 1 else 8 * (order[-1] != "y") + 8 * (order[-1] != "z"))
    return one["lemma13.swap"]


FAST_FK = [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (3, 1)]


@pytest.mark.parametrize("mode", L13.BAD_SETS)
@pytest.mark.parametrize("order", ORDERS)
@pytest.mark.parametrize("f,K", FAST_FK)
def test_packed_selected_add_exhaustive(f, K, order, mode):
    """SPEC §4.11 first bullet: f in {1,2,3}, K in {1,2,3} (f K <= 4), all rho < K, all six physical
    orders, spectators before/between/after, record IDs as payloads, both bad sets; (23) marks every record
    for K <= 5 while safe_segments takes the good path for some records."""
    good_path = False
    for rho in range(K):
        spect = SPECTATORS[(rho + ORDERS.index(order) + 3 * f) % len(SPECTATORS)]
        if f * K == 4:
            spect = tuple(min(s, 2) for s in spect)
        V, c = check_rectangle(f, K, rho, order, spect, mode)
        if f == 1:
            assert c["lemma13.bad_records"] == 0 and c["lemma13.rotation"] == 0
        elif mode == "eq23":
            assert c["lemma13.bad_records"] == V and c["lemma13.sort"] == 1 and c["lemma13.reinsert"] == 1
        else:
            good_path |= c["lemma13.bad_records"] < V
    if f > 1 and mode == "safe_segments":
        assert good_path


@pytest.mark.slow
@pytest.mark.parametrize("mode", L13.BAD_SETS)
@pytest.mark.parametrize("order", ORDERS)
@pytest.mark.parametrize("f,K", [(2, 3), (3, 2)])
def test_packed_selected_add_exhaustive_L6(f, K, order, mode):
    for rho in range(K):
        check_rectangle(f, K, rho, order, (1, 1, 1, 1) if rho else (1, 2, 1, 1), mode)


def test_swap_counts_follow_the_rightmost_rule():
    """Target already rightmost: no swap; otherwise two (bring and undo): <= 16 swaps in total [Pr L2084-2104]."""
    for order, swaps in [(("x", "z", "y"), 8), (("y", "x", "z"), 8), (("y", "z", "x"), 16)]:
        _, c = check_rectangle(2, 1, 0, order, (1, 1, 1, 1), "eq23")
        assert c["lemma13.swap"] == swaps


# ------------------------------------------------------------------------------------ cnet adapter
@st.composite
def slot_layouts(draw, fk=((1, 1), (1, 2), (2, 1), (2, 2), (3, 1)), max_bits=13):
    """Three disjoint slot fields at random gaps, roles and bit-list orders; nb <= max_bits keeps the
    arrays small (<= 3 * 2^13 records)."""
    f, K = draw(st.sampled_from(fk))
    rho = draw(st.integers(0, K - 1))
    L = f * K
    budget = max(0, max_bits - 3 * L)
    gaps = []
    for _ in range(4):
        g = draw(st.integers(0, min(2, budget)))
        budget -= g
        gaps.append(g)
    nb = 3 * L + sum(gaps)
    bases, pos = [], gaps[0]
    for i in range(3):
        bases.append(pos)
        pos += L + gaps[i + 1]
    roles = draw(st.permutations([0, 1, 2]))                    # which field is dst / src / z
    perm = draw(st.permutations(list(range(f))))                 # slot bit lists in any (consistent) order
    slots = [[bases[r] + rho + j * K for j in perm] for r in roles]
    rows = draw(st.integers(1, 3))
    return f, K, rho, nb, rows, slots


@settings(max_examples=40)
@given(slot_layouts(), st.sampled_from(L13.BAD_SETS), st.integers(0, 10 ** 6))
def test_row_add_lemma13_equals_direct(layout, mode, seed):
    """SPEC §4.3: one row addition = ONE Lemma 13 call (x = src slot, y = dst slot, z = a third slot);
    equals the address permutation of cnet._row_add_direct on random payloads [Pr L2152-2165]."""
    f, K, rho, nb, rows, (dst, src, z) = layout
    rng = random.Random(seed)
    arr = [(rng.getrandbits(16), rng.getrandbits(16)) for _ in range(rows << nb)]
    inst = Instrument()
    got = L13.row_add_lemma13(arr, rows, nb, dst, src, z, K, rho, bad_set=mode, inst=inst)
    assert got == _row_add_direct(arr, dst, src)
    assert inst.counts["lemma13.call"] == 1


@pytest.mark.slow
@pytest.mark.parametrize("mode", L13.BAD_SETS)
def test_row_add_lemma13_f3_K2(mode):
    """f = 3, K = 2 (L = 6, 2^18 records per row): the largest adapter case."""
    rng = random.Random(3)
    rows, nb, K, rho = 1, 18, 2, 1
    dst, src, z = [12 + rho + 2 * j for j in (2, 0, 1)], [0 + rho + 2 * j for j in (2, 0, 1)], \
        [6 + rho + 2 * j for j in range(3)]
    arr = [rng.getrandbits(8) for _ in range(rows << nb)]
    inst = Instrument()
    assert L13.row_add_lemma13(arr, rows, nb, dst, src, z, K, rho, bad_set=mode, inst=inst) == \
        _row_add_direct(arr, dst, src)
    c = inst.counts
    assert c["lemma13.call"] == 1 and c["lemma13.rotation"] == 8
    assert c["lemma13.swap"] == 16                         # x = src is physically rightmost: all 8 lines exchange
    assert c["lemma13.sort"] == 1 and c["lemma13.reinsert"] == 1
    assert c["lemma13.bad_records"] == (rows << nb) if mode == "eq23" else c["lemma13.bad_records"] > 0


def test_row_add_lemma13_validation():
    arr = list(range(1 << 6))
    for bad in [lambda: L13.row_add_lemma13(arr, 1, 6, [0], [1], [2, 3], 1, 0),           # f mismatch
                lambda: L13.row_add_lemma13(arr, 1, 6, [0], [0], [2], 1, 0),              # overlapping slots
                lambda: L13.row_add_lemma13(arr, 1, 6, [0, 2], [3, 5], [4, 6], 2, 0),     # outside nb
                lambda: L13.row_add_lemma13(arr, 1, 6, [0, 3], [4, 5], [1, 2], 1, 0),     # not rho + iK
                lambda: L13.row_add_lemma13(arr, 2, 6, [0], [1], [2], 1, 0)]:             # wrong length
        with pytest.raises(ValueError):
            bad()
    sh = rectangle("xyz", 2, (1, 1, 1, 1))
    for kw in [dict(K=2, f=1, rho=2), dict(K=1, f=2, rho=0, bad_set="nope")]:
        with pytest.raises(ValueError):
            L13.packed_selected_add(list(range(sh.volume)), sh, {c: c for c in "xyz"}, **kw)
    with pytest.raises(ValueError):
        L13.packed_selected_add(list(range(sh.volume)), sh, {"x": "x", "y": "y", "z": "y"}, 1, 2, 0)


@pytest.mark.parametrize("entry,new", [(0, ("y", "z", +1, 0)), (4, ("z", "y", +1, 0)), (7, ("y", "z", -1, 0))])
def test_corrupted_rotation_is_detected(monkeypatch, entry, new):
    """Negative test: with one ROTATIONS entry corrupted the good-address path (safe_segments) no longer
    equals T0, so either the keys == holes assertion fires or the result differs from the direct row
    addition.  (With (23) at K <= 5 every record is repaired from the same model, which would hide it.)"""
    rot = list(L13.ROTATIONS)
    rot[entry] = new
    monkeypatch.setattr(L13, "ROTATIONS", rot)
    rng = random.Random(entry)
    f, K, rho, nb, rows = 2, 2, 0, 12, 2
    dst, src, z = [8, 10], [0, 2], [4, 6]
    arr = [rng.getrandbits(20) for _ in range(rows << nb)]
    try:
        got = L13.row_add_lemma13(arr, rows, nb, dst, src, z, K, rho, bad_set="safe_segments")
    except AssertionError:
        return
    assert got != _row_add_direct(arr, dst, src)


# ------------------------------------------------------------------------------------ Lemma 12 swaps
@pytest.mark.parametrize("order,rho", [(("y", "x", "z"), 1), (("z", "y", "x"), 0)])
def test_swap_via_lemma12_network_path(order, rho):
    """L = 4 >= 4 (f = 2, K = 2): the chunk exchanges run M5's Lemma 12 through the bit network B1
    (counter interchange.lemma12_network_call), on record IDs with the permutation applied to the records
    (DEVIATIONS D12); identical to the bitwise default (SPEC §3.8, §4.10, §4.11 last bullet)."""
    from subnlogn.interchange import InterchangePolicy
    from subnlogn.net import compile_network
    from subnlogn.net.fixtures import fixture_B1
    swap = L13.swap_via_lemma12(compile_network(fixture_B1()), InterchangePolicy())
    f, K = 2, 2
    sh = rectangle(order, f * K, (1, 1, 1, 1))
    recs = [("rec", i) for i in range(sh.volume)]
    inst = Instrument()
    got, _ = L13.packed_selected_add(recs, sh, {c: c for c in "xyz"}, K, f, rho, swap=swap, inst=inst)
    ref, _ = L13.packed_selected_add(recs, sh, {c: c for c in "xyz"}, K, f, rho)
    assert got == ref
    swaps = expected_swaps(f, order)                       # exact: one Lemma 12 call per exchange,
    assert inst.counts["lemma13.swap"] == swaps == (8 if order[-1] != "x" else 16)   # each one Prop 11 call
    assert inst.counts["interchange.lemma12_network_call"] == swaps * PM.l12_calls(4, PM.nets()["B1"]) == swaps
    V, _ = check_rectangle(f, K, rho, order, (1, 1, 1, 1), "safe_segments", swap=swap)
    assert V == 4096
