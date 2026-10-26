"""Big-integer sites: where long integers may live on the data path, and the route tests.

1. One smallest-size product per route in products="hierarchy" mode (the faithful algorithm, SPEC §6.5):
   exact, and Python's * never multiplied two operands beyond word scale (python.big_product == 0; the
   Ctx.product_mul rule: min(operand bits) > 64 and max(operand bits) > 4 p_level), with the route's
   packed products actually sent to the hierarchy -- counted EXACTLY (exact counts; tests/hierarchy_exact.py):
   Multiply1 calls = packed products (closed form) + word products above 64 bits (python-mode oracle), every
   Multiply1 product's BasicMul calls by a closed form or the python-mode replay, the route's path counters by
   tests/path_model.py.
2. The M6 gate entries multiplied into guarded records by ``m6.cnet._mul_zi2`` are word-size constants.
3. Dynamic cross-check of the site table: under a call/return trace, integers beyond word scale occur only
   in the functions the allow-list permits (routed products, linear scans, table precomputation).
"""

import random

import pytest

import hierarchy_exact as HE
import path_model as PM
from subnlogn.context import WORD_BITS, Ctx
from subnlogn.multiply import multiply
from subnlogn.schedule import test_policy, test_schedule


def _hierarchy_product(schedule, bits: int, seed: int, stub, monkeypatch, replay="all"):
    """One exact product of two random ``bits``-bit operands (top bits set) in hierarchy mode, with the
    Multiply1 -> BasicMul stage isolated by ``stub`` (the conftest ``basic_mul_stub`` fixture; bridge routes: a
    full cascade takes hours in Python); the real BasicMul is verified on every operand-size pair
    the stub absorbed (compositional verification).  Exact counts: the stage identity of
    tests/hierarchy_exact.py -- with ``replay`` a sample size, the replay class is replayed on that many Multiply1
    products (the fast bridge routes; their full replay is the slow test below) -- and every path counter of the
    route (tests/path_model.py: PATH_KEYS, and the 2D FastDFT's nodes and leaves)."""
    rec = HE.Multiply1Recorder(monkeypatch, stub)
    rng = random.Random(seed)
    a = rng.getrandbits(bits) | (1 << (bits - 1))
    b = rng.getrandbits(bits) | (1 << (bits - 1))
    ctx = Ctx(schedule=schedule, products="hierarchy")
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    exp, res = HE.assert_stage_isolated(c, schedule, [(a, b)], rec, stub, replay)
    route = PM.multiply_counts(schedule, PM.bit_lengths([(a, b)]), PM.nets())
    PM.assert_exact(c, route + HE.lower_stage_counts(rec), PM.PATH_KEYS + ("fastdft.node", "fastdft.leaf"))
    assert exp["kron.product"] > 0 and stub.calls == res["total"] > 0 and stub.verify_real_basic_mul() > 0
    return route


# -- 1. routes in hierarchy mode -----------------------------------------------------------------------


def test_route_2d_fallback_forced_recursion(basic_mul_stub, monkeypatch):
    """2D FastDFT (M1) with forced recursion: Kronecker row spreads and word-scale products by Multiply1;
    Multiply1 -> BasicMul isolated here (the full cascade, ~30 s, is
    test_products::test_hierarchy_mode_2d_full_cascade)."""
    exp = _hierarchy_product(test_schedule(base_threshold=2), 40, 11, basic_mul_stub, monkeypatch)
    assert exp["fastdft.node"] > 0 and exp["bridge.dft"] == 0


def test_route_bridge_direct(basic_mul_stub, monkeypatch):
    """Bridge + direct middle (M2 reference backend): spreading overlap-add by Multiply1, address
    movements by Lemma 12; Multiply1 -> BasicMul isolated (stub), BasicMul verified per size pair."""
    exp = _hierarchy_product(test_policy(3, middle="direct"), 30, 12, basic_mul_stub, monkeypatch, replay=8)
    assert exp["bridge.dft"] == exp["bridge.middle"] == 2 and exp["prop18.ring_product"] == 0
    assert exp["bridge.axis_swap"] > 0


def test_route_bridge_walsh_network(basic_mul_stub, monkeypatch):
    """Bridge + Walsh middle + network engine (Lemma 13 basis changes) at 50 bits (chunk rounds through
    the complex network; the positional maps are trivial at this shape); BasicMul stage isolated."""
    exp = _hierarchy_product(test_policy(4, middle="walsh"), 50, 13, basic_mul_stub, monkeypatch, replay=8)
    assert exp["bridge.middle"] == 2 and exp["walsh.chunk_round"] > 0 and exp["bridge.axis_swap"] > 0
    assert exp["m6.layer.network"] > 0 and exp["m6.row_add.lemma13"] > 0


@pytest.mark.slow
@pytest.mark.parametrize("schedule,bits,seed", [(test_policy(3, middle="direct"), 30, 12),
                                                (test_policy(4, middle="walsh"), 50, 13)], ids=["direct", "walsh"])
def test_route_bridge_basic_calls_replayed_in_full(schedule, bits, seed, basic_mul_stub, monkeypatch):
    """The two fast bridge routes with EVERY Multiply1 product of the replay class replayed (~10 s and ~40 s)."""
    assert _hierarchy_product(schedule, bits, seed, basic_mul_stub, monkeypatch)["bridge.dft"] == 2


@pytest.mark.slow
def test_route_bridge_walsh_network_positional(basic_mul_stub, monkeypatch):
    """As above at 100 bits: nontrivial positional maps, i.e. CNOT batches through the selective Walsh
    gadget (lift by 8d bits, the scalar 2^(s+3k+e), lossless lowering); BasicMul stage isolated."""
    exp = _hierarchy_product(test_policy(4, middle="walsh"), 100, 14, basic_mul_stub, monkeypatch)
    assert exp["walsh.slice_batch"] > 0 and exp["m6.layer.network"] > 0


@pytest.mark.slow
def test_route_bridge_bluestein_network(basic_mul_stub, monkeypatch):
    """Bridge + Bluestein middle + network engine: Lemma 17 ring products of Proposition 18 and the
    spreading overlap-add by Multiply1 at 50 bits; BasicMul stage isolated."""
    exp = _hierarchy_product(test_policy(4), 50, 15, basic_mul_stub, monkeypatch)
    assert exp["prop18.ring_product"] > 0 and exp["prop14.network_layer"] > 0
    assert exp["m6.row_add.lemma13"] > 0 and exp["bridge.axis_swap"] > 0


# -- 2. gate entries of the M6 engine ------------------------------------------------------------------


@pytest.mark.parametrize("name", ["C1", "C2", "B1", "B2", "B2q5"])
def test_gate_entries_are_word_size_constants(name):
    """cnet._apply_gate multiplies guarded records by the gate entries z = (a + i b)/2^k: for every
    network the engine can load (SPEC §2.5 fixtures) a, b in {-1, 0, 1} and k = 0, i.e. the products
    are sign changes (scalar times a word-size constant, class C).  Bit networks XOR records."""
    from subnlogn.m6.engine import compiled_fixture
    net = compiled_fixture(name)
    entries = [z for g in net.gates for row in g.matrix for z in row]
    assert entries
    for z in entries:
        if net.domain == "ZI2":
            assert z.k == 0 and abs(z.re) <= 1 and abs(z.im) <= 1
            assert max(abs(z.re), abs(z.im), z.k).bit_length() <= WORD_BITS
        else:
            assert int(z) in (0, 1)


# -- 3. dynamic cross-check: long integers only where the allow-list permits them ----------------------------


def _traced_product(schedule, bits: int, seed: int):
    from longint_trace import LongIntTrace
    rng = random.Random(seed)
    a = rng.getrandbits(bits) | (1 << (bits - 1))
    b = rng.getrandbits(bits) | (1 << (bits - 1))
    ctx = Ctx(schedule=schedule, products="hierarchy")
    with LongIntTrace() as tr:
        out = multiply(a, b, ctx)
    assert out == a * b and ctx.inst.counts.get("python.big_product", 0) == 0
    return tr


def test_long_integers_only_in_allowlisted_functions_2d(basic_mul_stub):
    """Under a call/return trace, with the Multiply1 -> BasicMul stage isolated (the
    real BasicMul verified per operand-size pair), every subnlogn function that held an integer of more than
    T = 4 max(q) bits (q over the level chain: the word-scale bound) is one the allow-list permits to hold
    long integers (tests/longint_trace.py ALLOWED_LONG: classes A, C, D), and the packed integers of
    the Kronecker spreads and of the root packing are seen."""
    from subnlogn.multiply import root_parameters
    sch = test_schedule(base_threshold=2)
    _, _, _, R0, p0 = root_parameters(40)
    T = 4 * max(max(lv.q_child, lv.q_b) for lv in sch.chain(R0, p0))
    tr = _traced_product(sch, 40, 17)
    assert tr.unlisted(T) == {}
    assert {"kronecker.py:pack", "kronecker.py:unpack", "bits.py:int_to_digits"} <= set(tr.above(T))
    assert basic_mul_stub.verify_real_basic_mul() > 0


@pytest.mark.slow
@pytest.mark.parametrize("schedule,bits,expect", [
    (test_policy(3, middle="direct"), 30, "kronecker.py:spread_row"),
    (test_policy(4, middle="walsh"), 50, "kronecker.py:spread_row"),
    (test_policy(4), 50, "ring.py:centered_extract"),
], ids=["direct", "walsh", "bluestein"])
def test_long_integers_only_in_allowlisted_functions_bridge(schedule, bits, expect, basic_mul_stub):
    """The same for the bridge routes with T = 4 (P + 2) (the bridge record grid; ring products run at
    p = P + 2); the Multiply1 -> BasicMul stage is isolated (runtime cost) and the real BasicMul is
    verified per size pair."""
    from subnlogn.multiply import root_parameters
    _, _, K0, _, p0 = root_parameters(bits)
    P, _, _ = schedule.bridge_params(p0, K0, min(schedule.bridge_d, K0))
    tr = _traced_product(schedule, bits, 18)
    assert tr.unlisted(4 * (P + 2)) == {}
    assert expect in tr.above(4 * (P + 2))
    assert basic_mul_stub.verify_real_basic_mul() > 0
