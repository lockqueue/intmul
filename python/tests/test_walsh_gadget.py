"""SPEC_WALSH §8 W-T1 (identities), W-T2 (selective gadget through the real Prop 14), W-T3 (CNOT batches);
SPEC_WALSH §2-§3, R5 (7.1)-(7.4)."""

from collections import Counter
from fractions import Fraction
from itertools import combinations

import pytest

import path_model as PM
from subnlogn.m6.policy import LAYER_TEST
from subnlogn.walsh.gadget import WalshCtx, cnot_batch, lift, selective_walsh
from subnlogn.walsh.positional import Slice, make_slices
from walsh_helpers import (
    H0, I2, RNG, S, address_permute, diag, engine, exact_H, fresh_inst, kron_bits, mat_mul, rand_disk, scal,
    to_frac,
)

ONE_I = (Fraction(1, 4), Fraction(1, 4))   # (1 + i)/4


def mpow(A, n):
    out = A
    for _ in range(n - 1):
        out = mat_mul(out, A)
    return out


# ----------------------------------------------------------------------------------------------
# W-T1: identities, exact Gaussian rationals
# ----------------------------------------------------------------------------------------------


def test_identities_2x2():
    assert mat_mul(H0, H0) == scal((Fraction(1, 2), Fraction(0)), I2)
    assert mpow(H0, 3) == scal((Fraction(1, 2), Fraction(0)), H0)                       # H0^3 = H0/2
    assert mpow(mat_mul(H0, S), 3) == scal(ONE_I, I2)                                    # (H0 S)^3 = (1+i)/4 I


@pytest.mark.parametrize("D", [1, 2, 3, 4])
def test_selective_identity_all_subsets(D):
    """(H_all S_U)^3 = 2^-s ((1+i)/4)^q H_T for every T (R5 (7.3)-(7.4))."""
    H_all = kron_bits([H0] * D)
    for s in range(D + 1):
        for T in combinations(range(D), s):
            U = [j for j in range(D) if j not in T]
            S_U = diag([(Fraction(1), Fraction(0)) if sum((x >> j) & 1 for j in U) % 4 == 0 else
                        [(Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)), (Fraction(-1), Fraction(0)),
                         (Fraction(0), Fraction(-1))][sum((x >> j) & 1 for j in U) % 4] for x in range(1 << D)])
            lhs = mpow(mat_mul(H_all, S_U), 3)
            c = (Fraction(1, 2 ** s), Fraction(0))
            for _ in range(D - s):
                c = (c[0] * ONE_I[0] - c[1] * ONE_I[1], c[0] * ONE_I[1] + c[1] * ONE_I[0])
            H_T = kron_bits([H0 if j in T else I2 for j in range(D)])
            assert lhs == scal(c, H_T)


@pytest.mark.parametrize("D", [2, 3, 4, 5])
def test_cnot_identity(D):
    """CNOT^(tensor s) = 2^s H_T CZ H_T for disjoint pairs (R5 (7.2)), several pair sets per D."""
    rng = RNG(D)
    for _ in range(4):
        pos = list(range(D))
        rng.shuffle(pos)
        s = rng.randint(1, D // 2)
        pairs = [(pos[2 * i], pos[2 * i + 1]) for i in range(s)]      # (control, target)
        T = [t for _, t in pairs]
        H_T = kron_bits([H0 if j in T else I2 for j in range(D)])
        CZ = diag([(Fraction((-1) ** sum(((x >> c) & (x >> t)) & 1 for c, t in pairs)), Fraction(0))
                   for x in range(1 << D)])
        rhs = scal((Fraction(2 ** s), Fraction(0)), mat_mul(mat_mul(H_T, CZ), H_T))
        n = 1 << D
        Z = (Fraction(0), Fraction(0))
        perm = [[Z] * n for _ in range(n)]
        for x in range(n):
            y = x
            for c, t in pairs:
                y ^= ((x >> c) & 1) << t
            perm[y][x] = (Fraction(1), Fraction(0))
        assert rhs == perm


# ----------------------------------------------------------------------------------------------
# W-T2: the selective gadget through the real Prop 14 (fixture C1, forced batching)
# ----------------------------------------------------------------------------------------------


def run_gadget(D, h, m0, rho, wanted_sets, kind, r=1, d=None):
    rng = RNG(D * 100 + m0)
    d = d or D
    sl = Slice(m0, 0, D, h, rho)
    inst = fresh_inst()
    w = WalshCtx(d=d, h=h, engine=engine(kind, d, inst=inst), inst=inst)
    p = 12
    ps = p + 8 * d
    z = rand_disk(m0, r, p, rng)
    zl = lift(z, 8 * d)
    for T in wanted_sets:
        out = selective_walsh(zl, sl, T, ps, w)
        ref = exact_H(to_frac(z, p), [m0 - 1 - j for j in T])
        assert to_frac(out, ps) == ref
    return inst


@pytest.mark.parametrize("kind", ["base", "network"])
@pytest.mark.parametrize("D", [1, 2, 3, 4])
def test_selective_gadget_all_subsets(kind, D):
    sl_pos = Slice(D, 0, D, 1, 0).positions
    subsets = [list(T) for s in range(D + 1) for T in combinations(sl_pos, s)]
    inst = run_gadget(D, 1, D, 0, subsets, kind, r=2)
    c = inst.counts
    assert c["walsh.gadget"] == len(subsets) and c["walsh.exact_boundary"] == 3 * len(subsets)
    assert c["walsh.gadget.s0"] == 1 and c["walsh.gadget.s_full"] == 1
    # exact: q = D - s unwanted positions, odd for the subsets of size s with D - s odd; three full
    # Prop 14 layers per gadget, each through the engine of ``kind`` (path_model; CCtx oracle for P_M)
    odd = sum(1 for T in subsets if (D - len(T)) % 2)
    assert c["walsh.gadget.q_odd"] == odd and c.get("walsh.gadget.q_even", 0) == len(subsets) - odd
    _exact_layers(c, kind, D, 1, D, 3 * len(subsets))


def _exact_layers(c, kind, D, h, d, n_layers):
    """n_layers Prop 14 layers on D chunks of width h through the engine of ``kind`` (exact, path_model)."""
    exp = Counter()
    if kind == "network":
        layer = PM.prop14_layer(PM.Eng(PM.nets()["C1"], d, LAYER_TEST, h, row_add="direct"), D)
        exp = Counter({k: n_layers * v for k, v in layer.items() if k not in ("m6.rows.padded", "m6.rows.removed")})
    PM.assert_exact(c, exp, ["m6.layer.network", "m6.c_power.network", "m6.c_power.leaf", "m6.row_add.direct",
                             "m6.phase_edge.nonzero", "m6.gate"])
    return exp


def test_selective_gadget_h2_offset_and_suffix():
    """h = 2 chunks, offset rho = 1, slice followed by a suffix bit (m0 = 7)."""
    sl = Slice(7, 0, 3, 2, 1)
    pos = sl.positions
    inst = run_gadget(3, 2, 7, 1, [[], pos, [pos[0]], [pos[1], pos[2]]], "network", r=1)
    assert inst.counts["walsh.gadget"] == 4 and inst.counts["m6.layer.network"] == 12   # 3 layers per gadget
    assert _exact_layers(inst.counts, "network", 3, 2, 3, 12)["m6.c_power.network"] == 12


@pytest.mark.slow
def test_selective_gadget_two_network_levels():
    """D = 9: two network levels (forced batching: one 9-piece)."""
    pos = Slice(9, 0, 9, 1, 0).positions
    inst = run_gadget(9, 1, 9, 0, [[], pos, pos[:4], pos[1::2]], "network")
    assert _exact_layers(inst.counts, "network", 9, 1, 9, 3 * 4)["m6.c_power.network"] == 12 * (1 + 13)


# ----------------------------------------------------------------------------------------------
# W-T3: CNOT batches
# ----------------------------------------------------------------------------------------------


def cnot_ref(z, pairs, m0):
    def f(x):
        y = x
        for c, t in pairs:
            y ^= ((x >> (m0 - 1 - c)) & 1) << (m0 - 1 - t)
        return y
    return address_permute(z, f)


@pytest.mark.parametrize("kind", ["base", "network"])
@pytest.mark.parametrize("r", [1, 2])
def test_cnot_batches_m0_7_h2_d3(kind, r):
    """m0 = 7, h = 2, d = 3: slices [1,3,5] (rho 0) and [0,2,4] (rho 1), leftover position 6.  Controls
    on unwanted selected positions, the other offset's bits and the leftover."""
    m0, h, d, p = 7, 2, 3, 10
    slices, slice_of, left = make_slices(m0, h, d)
    assert left == [6] and [s.positions for s in slices] == [[1, 3, 5], [0, 2, 4]]
    rng = RNG(r)
    inst = fresh_inst()
    w = WalshCtx(d=d, h=h, engine=engine(kind, d, inst=inst), inst=inst)
    z = rand_disk(m0, r, p, rng)
    cases = [(slices[0], [(6, 1)]),                       # control on the leftover
             (slices[0], [(3, 1), (6, 5)]),               # control on an unwanted selected position
             (slices[0], [(0, 1), (2, 3), (4, 5)]),       # controls on the other offset, s = D
             (slices[1], [(5, 0), (6, 4)]),
             (slices[1], [(1, 2)])]
    for sl, pairs in cases:
        out = cnot_batch(z, pairs, sl, p, w)
        assert out == cnot_ref(z, pairs, m0)
    assert inst.counts["walsh.slice_batch"] == len(cases) and inst.counts["walsh.cz_scan"] == len(cases)


def test_cnot_batch_prefix_and_suffix_controls():
    """m0 = 7, h = 1, d = 3: the middle group's slice [3, 4, 5] with controls in the prefix (0..2) and
    the suffix (6)."""
    m0, p = 7, 9
    slices, _, _ = make_slices(m0, 1, 3)
    sl = slices[1]
    assert sl.positions == [3, 4, 5] and sl.A == 8 and sl.S == 2
    z = rand_disk(m0, 2, p, RNG(9))
    inst = fresh_inst()
    w = WalshCtx(d=3, h=1, engine=engine("network", 3, inst=inst), inst=inst)
    for pairs in ([(0, 3), (6, 5)], [(2, 4)], [(1, 3), (0, 4), (6, 5)]):
        assert cnot_batch(z, pairs, sl, p, w) == cnot_ref(z, pairs, m0)
    assert inst.counts["walsh.slice_batch"] == 3 and inst.counts["m6.layer.network"] == 3 * 6


def test_cnot_batch_rejects_bad_pairs():
    sl = Slice(7, 0, 3, 2, 0)
    w = WalshCtx(d=3, h=2)
    z = rand_disk(7, 1, 8, RNG(1))
    for bad in ([(1, 1)], [(0, 1), (1, 3)], [(0, 1), (0, 3)], [(3, 6)], [(0, 2)], [(9, 1)]):
        with pytest.raises(ValueError):
            cnot_batch(z, bad, sl, 8, w)
    assert cnot_batch(z, [], sl, 8, w) is z
