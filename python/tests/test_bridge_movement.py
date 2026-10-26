"""Bridge address movements by Lemma 12 (SPEC §7.2, SPEC_WALSH §6.3; subnlogn.bridge.movement): oracles for
swap_axes / expose_axis / reverse_axes with unequal widths, and bit-exact equality of the bridge DFT and of
products under bridge_movement="lemma12" and the "index" reference mode."""

import random

import pytest

import path_model as PM
from conftest import make_ctx
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.bridge.geometry import BridgeGeometry, balanced_factors
from subnlogn.bridge.movement import (Mover, axis, axis_lines, expose_axis, map_axis_blocks, restore_axis,
                                      reverse_axes, storage_shape, storage_to_tensor, swap_axes, tensor_shape,
                                      tensor_to_storage)
from subnlogn.fixedpoint import FxVec
from subnlogn.instrument import Instrument
from subnlogn.interchange import InterchangePolicy
from subnlogn.multiply import multiply, root_parameters
from subnlogn.net import compile_network
from subnlogn.net.fixtures import fixture_B1, fixture_B2q5
from subnlogn.schedule import Schedule, test_policy, test_schedule
from subnlogn.stream import address_of, index_of

GEOMS = [(4, 8), (8, 16), (16, 16), (2, 2, 4), (4, 8, 8), (4, 4, 8, 8), (2, 2, 2, 2, 4)]


def _mover(net=None, inst=None):
    return Mover(net or compile_network(fixture_B1()), InterchangePolicy(), inst)


def _oracle(arr, old, new):
    """Same logical address (axis -> digit) in the new physical layout."""
    return [arr[index_of(old, address_of(new, p))] for p in range(new.volume)]


@pytest.mark.parametrize("t", GEOMS)
def test_swap_expose_reverse_against_index_oracles(t):
    g = BridgeGeometry(t)
    sh = storage_shape(g)
    rng = random.Random(len(t) * 31 + t[-1])
    re = [rng.getrandbits(24) - (1 << 23) for _ in range(g.R)]
    im = [rng.getrandbits(24) - (1 << 23) for _ in range(g.R)]
    mv = _mover()
    for a, b in [(axis(g.d), axis(1)), (axis(1), axis(g.d))] + ([(axis(2), axis(g.d))] if g.d > 2 else []):
        (r2, i2), sh2 = swap_axes([re, im], sh, a, b, mv)
        assert sh2.names[sh.index(a)] == b and sh2.length(a) == g.tt(a[1])
        assert r2 == _oracle(re, sh, sh2) and i2 == _oracle(im, sh, sh2)
    (r3, i3), sh3 = reverse_axes([re, im], sh, mv)
    assert sh3.names == tensor_shape(g).names and r3 == _oracle(re, sh, sh3)
    perm = g.storage_to_freq()                       # = the tensor index map = Phi
    assert all(r3[perm[s]] == re[s] and i3[perm[s]] == im[s] for s in range(g.R))
    (r4, i4), sh4 = reverse_axes([r3, i3], sh3, mv)
    assert (r4, i4) == (re, im) and sh4.names == sh.names
    for h in range(1, g.d + 1):
        (r5, i5), sh5, partner = expose_axis([re, im], sh, h, mv)
        assert sh5.names[-1] == axis(h) and r5 == _oracle(re, sh, sh5) and i5 == _oracle(im, sh, sh5)
        assert (partner is None) == (h == 1)
        (r6, i6), sh6 = restore_axis([r5, i5], sh5, h, partner, mv)
        assert (r6, i6) == (re, im) and sh6.names == sh.names and sh6.lengths == sh.lengths


def test_swap_with_q5_network():
    """The movement is generic over the bit network: B2q5 (q_radix = 5) gives the same permutation.  With t =
    (32, 32) both exchanges go through their bit network (at (8, 16) neither would: base cases only)."""
    g = BridgeGeometry((32, 32))
    a = list(range(g.R))
    i1, i2 = Instrument(), Instrument()
    (x,), _ = reverse_axes([a], storage_shape(g), _mover(inst=i1))
    (y,), _ = reverse_axes([a], storage_shape(g), _mover(compile_network(fixture_B2q5()), inst=i2))
    assert x == y
    # exact: one exchange of two 5-bit axes = one Prop 11 call per base-m piece with j >= 1
    b1, b2q5 = PM.nets()["B1"], PM.nets()["B2q5"]
    assert i1.counts["interchange.lemma12_network_call"] == PM.l12_calls(5, b1) == 1
    assert i2.counts["interchange.lemma12_network_call"] == PM.l12_calls(5, b2q5) == 1


@pytest.mark.parametrize("t", GEOMS)
def test_axis_blocks_equal_lines(t):
    """Each exposed contiguous block is one line along axis h, in increasing j_h (= line_indices order), and the
    block digits decode the other axes (hence delta_h from the original lower digits)."""
    g = BridgeGeometry(t)
    vals = list(range(g.R))
    for h in range(1, g.d + 1):
        lines = {tuple(sorted((i + 1, c) for i, c in enumerate(g.digits(ln[0])) if i + 1 != h)): ln
                 for ln in g.line_indices(h)}
        seen = []

        def fn(digits, block, h=h):
            ln = lines[tuple(sorted(digits.items()))]
            assert block == [vals[i] for i in ln]
            seen.append(tuple(ln))
            return (block,)
        out = map_axis_blocks([vals], storage_shape(g), h, _mover(), fn)
        assert out == [vals] and sorted(seen) == sorted(tuple(ln) for ln in lines.values())


@pytest.mark.parametrize("t", [(4, 8), (16, 16), (2, 2, 4), (4, 8, 8), (2, 2, 2, 2, 4)])
def test_schedule_dispatch_modes_agree(t):
    g = BridgeGeometry(t)
    rng = random.Random(t[0] + len(t))
    re = [rng.getrandbits(20) for _ in range(g.R)]
    im = [rng.getrandbits(20) for _ in range(g.R)]
    res = {}
    for mode in ("index", "lemma12"):
        ctx = make_ctx(test_schedule(bridge_d=g.d).with_(bridge_movement=mode))
        tr, ti = storage_to_tensor(ctx, re, im, g)
        br, bi = tensor_to_storage(ctx, tr, ti, g)
        assert list(br) == re and list(bi) == im
        lines = [axis_lines(ctx, re, im, g, h, lambda dg, vr, vi: ([x * (1 + sum(dg.values())) + k
                                                                     for k, x in enumerate(vr)], vi[::-1]))
                 for h in range(1, g.d + 1)]
        res[mode] = (list(tr), list(ti), [tuple(map(list, x)) for x in lines])
        if mode == "lemma12":       # exact: d//2 per reversal (two), one expose + restore per axis h >= 2
            assert ctx.inst.counts["bridge.axis_swap"] == 2 * (g.d // 2) + 2 * (g.d - 1)
    assert res["index"] == res["lemma12"]


CASES = [(2, 4), (2, 5), (2, 8), (3, 6), (3, 7), (4, 5), (4, 8), (5, 6), (5, 10)]


@pytest.mark.parametrize("middle", ["direct", "bluestein", "walsh"])
@pytest.mark.parametrize("d,K", CASES)
def test_bridge_dft_lemma12_equals_index(middle, d, K):
    """SPEC §7.2 movements by Lemma 12 change no value: bridge_dft is bit-identical in both modes (spreading
    exposures, the middles' storage <-> tensor reversals, and the storage -> frequency reversal of step 4)."""
    R, p = 1 << K, max(8, K) + 4
    q = p + 2
    rng = random.Random(1000 * d + K + len(middle))
    big = (1 << (q + p)) * 7 // 10
    re = [rng.randint(-big, big) for _ in range(R)]
    im = [rng.randint(-big, big) for _ in range(R)]
    outs = {}
    for mode in ("index", "lemma12"):
        ctx = make_ctx(test_schedule(bridge_d=d).with_(bridge_middle=middle, bridge_movement=mode))
        outs[mode] = bridge_dft(ctx, FxVec(re, im, q), R, p, d)
        c = ctx.inst.counts
        if mode == "lemma12":
            n_mid = 2 * (d // 2) if middle != "direct" else 2 * (d - 1)
            assert c["bridge.axis_swap"] == 2 * (d - 1) + n_mid + d // 2
            exp = PM.bridge_transform(K, d, middle, movement=True, bitnet=PM.nets()["B1"])   # exact
            PM.assert_exact(c, exp, ["bridge.axis_swap", "bridge.axis_expose", "bridge.axis_reverse",
                                     "interchange.lemma12_network_call", "bridge.dft", "bridge.middle"])
            assert (exp["interchange.lemma12_network_call"] > 0) == (min(balanced_factors(K, d)) >= 16)
        else:
            assert c.get("bridge.axis_swap", 0) == 0
    assert outs["index"] == outs["lemma12"]


def test_network_calls_d2_K8():
    """t = (16, 16): every exchange of two 4-bit axes calls the bit network (SPEC §3.10: u = 4 is the smallest
    width that does); 5 exchanges per bridge DFT with the Bluestein middle."""
    ctx = make_ctx(test_schedule(bridge_d=2).with_(bridge_middle="bluestein", bridge_movement="lemma12"))
    R, p = 256, 12
    rng = random.Random(8)
    x = FxVec([rng.randint(-2 ** 20, 2 ** 20) for _ in range(R)], [0] * R, p + 2)
    bridge_dft(ctx, x, R, p, 2)
    c = ctx.inst.counts
    assert c["bridge.axis_swap"] == 5 and c["bridge.axis_expose"] == 1 and c["bridge.axis_reverse"] == 3
    assert c["interchange.lemma12_network_call"] == 5


def test_schedule_switch_defaults():
    assert Schedule(name="x").bridge_movement == "index"
    assert test_policy(3).bridge_movement == "lemma12"
    assert test_policy(3, bridge_movement="index").bridge_movement == "index"
    with pytest.raises(ValueError):
        ctx = make_ctx(test_schedule(bridge_d=2).with_(bridge_movement="tape"))
        storage_to_tensor(ctx, [0] * 4, [0] * 4, BridgeGeometry((2, 2)))


def _n_for_K(K: int) -> int:
    return next(n for n in range(65, 40000) if root_parameters(n)[2] == K)


@pytest.mark.parametrize("d,K", [(2, 8), (3, 6), (4, 8)])
def test_products_exact_with_lemma12_movements(d, K):
    """Exact products through test_policy shapes (bridge_movement = "lemma12" is test_policy's default)."""
    n = _n_for_K(K)
    rng = random.Random(d * K)
    ctx = make_ctx(test_policy(d))
    pairs = [(rng.getrandbits(n) | 1 << (n - 1), rng.getrandbits(n)), ((1 << n) - 1, (1 << n) - 1)]
    for a, b in pairs:
        assert multiply(a, b, ctx) == a * b
    exp = PM.multiply_counts(test_policy(d), PM.bit_lengths(pairs), PM.nets())      # exact
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    assert (exp["interchange.lemma12_network_call"] > 0) == (min(balanced_factors(K, d)) >= 16)
    ref = make_ctx(test_policy(d, bridge_movement="index"))
    assert multiply(rng.getrandbits(n), 7, ref) >= 0 and ref.inst.counts.get("bridge.axis_swap", 0) == 0
