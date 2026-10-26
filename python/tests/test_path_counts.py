"""Exact path counts for the hierarchy stages and the independent model itself.

* BasicMul is really reached and really runs its FFT: one Multiply1 call (products="hierarchy")
  whose leaf has q_b = 64 sends every butterfly product with a 65-bit operand to BasicMul; EVERY BasicMul call is
  checked for its own internal counters (one two-call root, two base radix-2 FFTs of K0 R0/2 butterflies, no node,
  no packed product, no lower stage), and the number of calls is pinned twice -- by the closed form 6 R0 - 8 and by
  an independent oracle run (the same Multiply1 product in products="python", whose counter
  "python.word_product_over_64" counts exactly the word products with an operand above 64 bits).
* Multiply1 calls of a stage-isolated hierarchy run (BasicMul replaced by an exact counting stub, so that no
  cascade below Multiply1 runs): every packed product (closed form: 4 per overlap-add block, 4 per Lemma 17 ring
  product) plus every word product above 64 bits (oracle: the same product in python mode) is one Multiply1
  call; the stub calls equal the word products above 64 bits of those Multiply1 calls (oracle: each Multiply1
  product replayed in python mode).  2D at 40 bits is fast; bridge shapes are slow.
* The model reproduces the measured pristine counts (and differs from the four partial-fallback mutants').
"""

import random
from collections import Counter

import pytest

import path_model as PM
import subnlogn.hierarchy as hierarchy
from subnlogn.context import Ctx
from subnlogn.m6.policy import LAYER_TEST
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import test_policy, test_schedule


def _record_basic(monkeypatch):
    """Wrap the CURRENT Hierarchy.basic_mul: record (a, b, counter deltas of the call).  BasicMul calls nothing
    below it, so every counter increment during the call belongs to it."""
    inner, calls = hierarchy.Hierarchy.basic_mul, []

    def recording(self, a, b):
        before = Counter(self.inst.counts)
        out = inner(self, a, b)
        calls.append((a, b, Counter(self.inst.counts) - before))
        return out
    monkeypatch.setattr(hierarchy.Hierarchy, "basic_mul", recording)
    return calls


def basic_mul_in_multiply1_case(monkeypatch, n: int = 600, seed: int = 600):
    """One Multiply1 product of two n-bit operands (faithful 2D stage: a leaf of R0 = 256, q_b = 64) with every
    BasicMul call checked exactly; returns the list of recorded calls."""
    calls = _record_basic(monkeypatch)
    rng = random.Random(seed)
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n) | (1 << (n - 1))
    h = hierarchy.Hierarchy()
    assert h.multiply1(a, b) == a * b
    _, _, K0, R0, p0 = root_parameters(n)
    assert (p0 + K0 + 16, R0) == (64, 256)                    # q_b = 64: only +-2^64 twiddle parts exceed 64 bits
    keys = sorted(set(PM.basic_mul_counts(1 << 64, 1)) | set(PM.BASIC_ZERO_KEYS))
    for x, y, delta in calls:                                 # BasicMul's internal FFT, call by call
        PM.assert_exact(delta, PM.basic_mul_counts(x, y), keys)
    oracle = Ctx(schedule=h.multiply1_schedule, products="python")
    assert multiply(a, b, oracle) == a * b
    want = oracle.inst.counts["python.word_product_over_64"]
    # closed form: per transform w^0 = 2^64 in every block of every stage (R0 - 1 times) and w^(R0/4) = -i 2^64 in
    # every block of the stages s >= 2 (R0/2 - 1 times), two real products each; random data stay below 2^64
    assert want == 2 * 2 * ((R0 - 1) + (R0 // 2 - 1)) == 6 * R0 - 8
    PM.assert_exact(Counter({"hierarchy.basic": len(calls)}), Counter({"hierarchy.basic": want}))
    total = sum((PM.basic_mul_counts(x, y) for x, y, _ in calls), Counter())
    leaf = Counter({"multiply.call": 1, "fastdft.leaf": 2, "basefft.butterfly": K0 * R0, "hierarchy.multiply1": 1,
                    "word.call": PM.multiply_counts(h.multiply1_schedule, [n])["word.call"]})
    PM.assert_exact(h.inst.counts, total + leaf, ["multiply.call", "fastdft.leaf", "basefft.butterfly",
                                                    "hierarchy.basic", "hierarchy.multiply1", "fastdft.node",
                                                    "word.call"])
    return calls


def test_basic_mul_runs_its_fft_inside_multiply1(monkeypatch):
    """Multiply1's word products above 64 bits go to BasicMul, and BasicMul is one two-call root with two
    base radix-2 FFTs (SPEC §6.5, MS Lemma 6.5), exactly, for every one of its 1528 calls (~1.2 s)."""
    assert len(basic_mul_in_multiply1_case(monkeypatch)) == 1528


def _stub_basic(monkeypatch):
    """BasicMul replaced by an exact counting stub (stage isolation; the BasicMul stage itself is checked above)."""
    calls = []

    def stub(self, a, b):
        self.inst.hit("hierarchy.basic")
        calls.append((a, b))
        return a * b
    monkeypatch.setattr(hierarchy.Hierarchy, "basic_mul", stub)
    return calls


def stage_isolated_case(monkeypatch, sched, bits: int, seed: int, replay: bool = True):
    """One hierarchy-mode product with BasicMul stubbed: hierarchy.multiply1 == packed products (closed form,
    path_model) + word products above 64 bits (python-mode oracle of the same product); with ``replay`` the stub
    calls == the word products above 64 bits of every Multiply1 product (each replayed in python mode)."""
    stub_calls = _stub_basic(monkeypatch)
    m1_inner, m1_calls = hierarchy.Hierarchy.multiply1, []

    def m1(self, a, b):
        m1_calls.append((a, b))
        return m1_inner(self, a, b)
    monkeypatch.setattr(hierarchy.Hierarchy, "multiply1", m1)
    rng = random.Random(seed)
    a, b = rng.getrandbits(bits) | (1 << (bits - 1)), rng.getrandbits(bits) | (1 << (bits - 1))
    ctx = Ctx(schedule=sched, products="hierarchy")
    assert multiply(a, b, ctx) == a * b
    oracle = Ctx(schedule=sched, products="python")
    assert multiply(a, b, oracle) == a * b
    exp = PM.multiply_counts(sched, [bits], PM.nets())
    packed = exp["kron.product"] + 4 * exp["prop18.ring_product"]
    c = ctx.inst.counts
    PM.assert_exact(c, {"hierarchy.multiply1": packed + oracle.inst.counts["python.word_product_over_64"],
                        "kron.product": exp["kron.product"], "prop18.ring_product": exp["prop18.ring_product"],
                        "python.big_product": 0, "python.word_product_over_64": 0})
    assert len(m1_calls) == c["hierarchy.multiply1"]
    if replay:
        want = 0
        for x, y in m1_calls:
            o = Ctx(schedule=hierarchy.Hierarchy().multiply1_schedule, products="python")
            assert multiply(x, y, o) == x * y
            assert o.inst.counts.get("kron.product", 0) == 0          # faithful 2D stage: leaves at these sizes
            want += o.inst.counts.get("python.word_product_over_64", 0)
        PM.assert_exact(c, {"hierarchy.basic": want})
        assert len(stub_calls) == want
    return c


def test_multiply1_calls_2d_stage_isolated(monkeypatch):
    """Deep 2D at 40 bits (the feasible full-hierarchy size; stubbed here: ~3 s instead of ~1 min)."""
    c = stage_isolated_case(monkeypatch, test_schedule(base_threshold=2), 40, 11)
    assert c["hierarchy.multiply1"] > c["kron.product"] > 0 and c["hierarchy.basic"] > 0


@pytest.mark.slow
@pytest.mark.parametrize("middle,d,bits", [("bluestein", 4, 50), ("walsh", 4, 50), ("direct", 3, 30)])
def test_multiply1_calls_bridge_stage_isolated(monkeypatch, middle, d, bits):
    """Bridge shapes (full hierarchy: hours): every packed overlap-add and Lemma 17 product and every word product
    above 64 bits is one Multiply1 call, exactly; the stub calls are replayed (Bluestein ~70 s)."""
    c = stage_isolated_case(monkeypatch, test_policy(d, middle=middle), bits, bits)
    assert c["hierarchy.multiply1"] > 0 and (c["prop18.ring_product"] > 0) == (middle == "bluestein")


def test_model_reproduces_the_pristine_counts():
    """path_model gives the measured pristine counts (measured once on the pristine code): one 300-bit
    product through test_policy(4) -- Bluestein: 6 network layers, 360 Lemma 13 calls (mutant A31: 1, 60); Walsh:
    158 layers, 134 network nodes, 8040 Lemma 13 calls (A32: 79, 67, 4020); BasicMul on 65, 300, 2000 bits: 3 roots,
    5664 butterflies (A35: 0, 0); the mutant engine: 8 Lemma 12 network calls per row addition (A36: 8 in
    total for two)."""
    nets = PM.nets()
    blue = PM.multiply_counts(test_policy(4), [300], nets)
    assert (blue["m6.layer.network"], blue["lemma13.call"], blue["bridge.middle"]) == (6, 360, 2)
    walsh = PM.multiply_counts(test_policy(4, middle="walsh"), [300], nets)
    assert (walsh["m6.layer.network"], walsh["m6.c_power.network"], walsh["lemma13.call"]) == (158, 134, 8040)
    rng = random.Random(1)
    basic = sum((PM.basic_mul_counts(rng.getrandbits(n), rng.getrandbits(n)) for n in (65, 300, 2000)), Counter())
    assert (basic["multiply.call"], basic["basefft.butterfly"]) == (3, 5664)
    one = PM.lemma13_row_add(PM.Eng(nets["C1"], 2, LAYER_TEST, 2, nets["B1"]), {0: 9, 1: 5, 2: 1}, 0, 1, 2, 2)
    assert one["interchange.lemma12_network_call"] == 8
