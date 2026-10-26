"""Network regression tests: Lemma 13 with a non-total exceptional set, the eq. (23) constants, theorem batching
through Lemma 13.

Sources: Pr = the plain-text rendering of [OAI26], Lemma 13 L1928-2151 ((20) L1979-1997, (22) L2050-2061,
(23) L2065-2067); SPEC §4.1-§4.3, §4.6; DEVIATIONS D11, D12 (Dev-5 safe segments).
"""

import random
from fractions import Fraction

import pytest

from conftest import make_ctx
from subnlogn.instrument import Instrument
from subnlogn.m6 import lemma13 as L13
from subnlogn.m6.engine import compiled_fixture, make_engine
from subnlogn.m6.policy import LayerPolicy, batch_plan
from subnlogn.m6.prop14 import hadamard_direct, simultaneous_H0
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import test_policy
from subnlogn.stream import Field, Shape, address_of, index_of

_CACHE: dict = {}

# ---------------------------------------------------------------------------------------------- integer model
# Pr (20), transcribed from the preprint text (u = the y segment, w = the z segment, c = the selected x bit):
#   (1) u <- u - c[w = 0]  (2) w <- w - c[u = 0]  (3) u <- u + c[w = 0]  (4) w <- w + c[u = 0]
#   (5) w <- w + c[u = 1]  (6) u <- u + c[w = 1]  (7) w <- w - c[u = 1]  (8) u <- u - c[w = 1]   (parities mod 2)
PR20 = [("y", "z", -1, 0), ("z", "y", -1, 0), ("y", "z", +1, 0), ("z", "y", +1, 0),
        ("z", "y", +1, 1), ("y", "z", +1, 1), ("z", "y", -1, 1), ("y", "z", -1, 1)]


def s0_model(x: int, y: int, z: int, f: int, K: int, rho: int) -> tuple[int, int, int]:
    """S0 by Pr (22): every line updates its target chunk by eps * sum_{i <= f-2} 2^{j_i} [x_{j_i} = 1][o_{j_i} = b]
    mod 2^L (o = the other chunk, j_i = rho + i K), every predicate on the current values (independent of
    subnlogn.m6.lemma13)."""
    mod = 1 << (f * K)
    v = {"y": y, "z": z}
    for tgt, oth, eps, b in PR20:
        off = 0
        for i in range(f - 1):
            j = rho + i * K
            if (x >> j) & 1 and ((v[oth] >> j) & 1) == b:
                off += 1 << j
        v[tgt] = (v[tgt] + eps * off) % mod
    return x, v["y"], v["z"]


def _rectangle(order: str, L: int, spect: tuple[int, int, int, int]) -> Shape:
    fs = [Field("s0", spect[0])]
    for i, c in enumerate(order):
        fs += [Field(c, 1 << L, 2), Field(f"s{i + 1}", spect[i + 1])]
    return Shape(tuple(fs), 1)


@pytest.mark.parametrize("f,K,rho,order,spect", [(3, 1, 0, "xyz", (2, 1, 1, 1)), (2, 2, 1, "zxy", (1, 2, 1, 1)),
                                                 (2, 1, 0, "yzx", (1, 1, 1, 3))])
def test_rotation_stage_matches_the_integer_model_with_nontotal_B(monkeypatch, f, K, rho, order, spect):
    """With the Dev-5 exceptional set (non-total here: 37.5-75% of the rectangle) the state after the eight
    rotations and their chunk swaps, before the repair, places every record exactly at S0 of its address by the
    independent model of Pr (20)/(22); the records outside B are not touched by the repair, so their final positions
    (the Lemma 13 contract y_j ^= x_j) come from the rotation stage alone."""
    captured = {}
    orig = L13.repair_exceptional

    def spy(stream, shape, names, K_, f_, rho_, bad_set="eq23", inst=None):
        captured["mid"] = list(stream)
        return orig(stream, shape, names, K_, f_, rho_, bad_set, inst)

    monkeypatch.setattr(L13, "repair_exceptional", spy)
    sh = _rectangle(order, f * K, spect)
    V = sh.volume
    inst = Instrument()
    out, _ = L13.packed_selected_add(list(range(V)), sh, {c: c for c in "xyz"}, K, f, rho,
                                     bad_set="safe_segments", inst=inst)
    mid = captured["mid"]
    good = 0
    mask = sum(1 << (rho + i * K) for i in range(f))
    for i in range(V):
        a = address_of(sh, i)
        _, y1, z1 = s0_model(a["x"], a["y"], a["z"], f, K, rho)
        assert mid[index_of(sh, dict(a, y=y1, z=z1))] == i                     # rotation stage == model S0
        b = dict(a, y=a["y"] ^ (a["x"] & mask))
        assert out[index_of(sh, b)] == i                                       # Lemma 13 contract
        if L13.all_segments_safe(a["x"], a["y"], a["z"], K, f, rho):
            good += 1
            assert y1 ^ (a["x"] & (1 << (rho + (f - 1) * K))) == b["y"] and z1 == a["z"]   # S0 = T0 off B
    c = inst.counts
    assert c["lemma13.call_f2plus"] == 1 and c["lemma13.records_f2plus"] == V and c["lemma13.rotation"] == 8
    assert 0 < c["lemma13.bad_records"] == V - good < V and c["lemma13.repair_partial"] == 1


def test_rotation_stage_model_detects_a_reversed_line_order(monkeypatch):
    """The comparison above has teeth: reversing the order of the eight lines (model and stream consistent, so the
    repair and the final contract still hold under (23)) moves the intermediate state away from S0."""
    monkeypatch.setattr(L13, "ROTATIONS", L13.ROTATIONS[::-1])
    f, K, rho = 3, 1, 0
    sh = _rectangle("xyz", f * K, (1, 1, 1, 1))
    captured = {}
    orig = L13.repair_exceptional
    monkeypatch.setattr(L13, "repair_exceptional", lambda s, *a, **k: captured.setdefault("mid", list(s)) and
                        orig(s, *a, **k))
    L13.packed_selected_add(list(range(sh.volume)), sh, {c: c for c in "xyz"}, K, f, rho, bad_set="eq23")
    mid = captured["mid"]
    moved = sum(1 for i in range(sh.volume)
                if mid[index_of(sh, dict(address_of(sh, i), **dict(zip("yz", s0_model(
                    *(address_of(sh, i)[c] for c in "xyz"), f, K, rho)[1:]))))] != i)
    assert moved > 0


# ---------------------------------------------------------------------------------------------- eq. (23)
def _with_segment_guards(gs, lows, K, rho, top):
    """Chunk value with used segment i = 2 g_i + a_i at bits rho + i K and ``top`` above the last segment."""
    v = top << (rho + len(gs) * K)
    for i, (g, a) in enumerate(zip(gs, lows)):
        v |= ((g << 1) | a) << (rho + i * K)
    return v


@pytest.mark.parametrize("K", [6, 7, 9])
@pytest.mark.parametrize("f", [2, 3])
def test_eq23_constants_pinned(K, f):
    """Pr (23): an address is in B iff some used guard value g (in y or z) fails 10 <= g <= 2^(K-1) - 11.  At
    K >= 6 the interval is nonempty; the boundary values 9, 10, 2^(K-1) - 11, 2^(K-1) - 10 are checked in every
    used segment of y and of z (f >= 2), so a shifted constant (e.g. 10 -> 9) is caught."""
    hi = (1 << (K - 1)) - 11
    rng = random.Random(K * 10 + f)
    nseg = f - 1
    for rho in sorted({0, K - 1}):
        for g, expect in ((9, True), (10, False), (hi, False), (hi + 1, True)):
            for i in range(nseg):
                for which in "yz":
                    gs = [rng.randint(10, hi) for _ in range(nseg)]
                    gs[i] = g
                    lows = [rng.randrange(2) for _ in range(nseg)]
                    v = _with_segment_guards(gs, lows, K, rho, rng.getrandbits(K - rho))
                    w = _with_segment_guards([rng.randint(10, hi) for _ in range(nseg)], lows, K, rho,
                                             rng.getrandbits(K - rho))
                    y, z = (v, w) if which == "y" else (w, v)
                    assert L13.is_bad(y, z, K, f, rho) is expect, (K, f, rho, g, i, which)


def test_eq23_at_f1_and_small_K():
    """f = 1 has no used guard segment, so is_bad is False everywhere (B is empty; Lemma 13 is the final XOR);
    for f >= 2 and K <= 5 the interval of (23) is empty and every address is bad (DEVIATIONS D12)."""
    rng = random.Random(1)
    for K in (1, 2, 5, 6, 8):
        for _ in range(50):
            y, z = rng.getrandbits(K), rng.getrandbits(K)
            assert L13.is_bad(y, z, K, 1, rng.randrange(K)) is False
    for K in (1, 2, 3, 4, 5):
        for f in (2, 3):
            for _ in range(20):
                y, z = rng.getrandbits(f * K), rng.getrandbits(f * K)
                assert L13.is_bad(y, z, K, f, rng.randrange(K)) is True


# ---------------------------------------------------------------------------------------------- theorem batching
def test_theorem_batching_beta_one_eighth_d13_through_lemma13():
    """The W-T12 policy beta = 1/8 at d = 13 (theorem batching q0 = 6, pieces 3 + 3 + 1, the network at
    e = 3) with the faithful basis changes: make_engine (Lemma 13 for every P_M row addition, swaps on B1); equals
    the independent tensor H0 + one Q_p.  The forced_q0 = 4 variant (one 9-piece, f = 3) runs through Lemma 13 in
    tests/test_m6_acceptance.py::test_theorem_batching_forced_q0_through_lemma13."""
    pol = LayerPolicy(beta=Fraction(1, 8), mode="test", guard="compiled")
    net = compiled_fixture("C1", _CACHE)
    assert (batch_plan(13, 13, 1, net, pol).q0, batch_plan(13, 13, 1, net, pol).pieces) == (6, (3, 3, 1))
    D, p = 13, 10
    rng = random.Random(1)
    recs = [([rng.randint(-(1 << p) // 2, (1 << p) // 2)], [rng.randint(-(1 << p) // 2, (1 << p) // 2)])
            for _ in range(1 << D)]
    sel = list(range(D))
    inst = Instrument()
    eng = make_engine(net, 13, pol, net_bit=compiled_fixture("B1", _CACHE), inst=inst)
    out, sc = simultaneous_H0(recs, sel, p, p, eng, K=1, rho=0)
    ref, _ = hadamard_direct(recs, sel, p, p)
    assert sc == p and out == ref
    c = inst.counts
    assert c["m6.c_power.network"] == 2 and c["m6.batch.preprocessed_chunks"] == 6
    assert c["m6.row_add.lemma13"] == c["lemma13.call"] > 0 and c.get("m6.row_add.direct", 0) == 0


# ---------------------------------------------------------------------------------------------- end to end (slow)
SAFE_SEGMENTS_TEST = LayerPolicy(mode="test", leaf="count", guard="compiled", batching="forced",
                                 bad_set="safe_segments")


@pytest.mark.slow
def test_nontotal_exceptional_set_end_to_end():
    """A real product through test_policy(10) (SPEC §6.3 shape K0 = 11, t = (2, ..., 2, 4), layer D = 9,
    one 9-piece at the top node) with the Dev-5 exceptional set (DEVIATIONS D12; LayerPolicy.bad_set =
    "safe_segments"): Lemma 13 runs with f = 3 (K = 1, L = 3: eight rotations, chunk exchanges by Lemma 12 on the
    radix-3 path -- the slot padded to [3^2], Proposition 11 at k = 0 -- and the repair), and at every such call B is
    neither empty nor the whole rectangle.  At K = 1 the Dev-5 good set is exactly "all used controls 0", where
    S0 = T0 = identity for any line order, so this test exercises the rotation stage but cannot observe it; the rotation
    stage is verified by test_rotation_stage_matches_the_integer_model_with_nontotal_B.
    (The default eq. (23) makes B the whole rectangle at K = 1.)"""
    n = 7000
    assert root_parameters(n)[2] == 11
    ctx = make_ctx(test_policy(10, layer=SAFE_SEGMENTS_TEST))
    rng = random.Random(7000)
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    assert c["bridge.dft"] > 0 and c.get("bridge.d_clamped", 0) == 0 and c["m6.c_power.network"] > 0
    assert c["lemma13.call_f2plus"] > 0 and c["m6.row_add.lemma13"] == c["lemma13.call"]
    assert 0 < c["lemma13.bad_records"] < c["lemma13.records_f2plus"]
    assert c["lemma13.repair_partial"] == c["lemma13.call_f2plus"]          # every f >= 2 call: B non-total
