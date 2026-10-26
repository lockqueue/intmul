"""Exact Multiply1 / BasicMul call counts of hierarchy-mode runs (exact counts for the hierarchy;
SPEC §6.5; MS Thm 7.1 part 3).  Not part of the library.

Identity, per hierarchy stage S calling the next stage S' (the improved multiplier or Multiply2 -> Multiply1;
Multiply1 -> BasicMul):

    calls of S'  =  P  +  W
    P = the packed products of S: 4 per overlap-add block (Kronecker row spreads, the bridge's spreading) and
        4 per Lemma 17 ring product -- closed form (tests/path_model.py, ``multiply_counts``);
    W = the word products of S with an operand above 64 bits (Ctx.word_mul) -- an independent oracle run: the
        same product with products="python", whose counter "python.word_product_over_64" applies the same
        64-bit rule on the same (exact, hence identical) intermediate values.

The word products of every stage are also counted exactly (Ctx.word_mul's "word.call") against the independent
structural model of tests/path_model.py (root squares, twists, solver, leaf butterflies; the bridge's deconvolution
and middle products), per Multiply1 product and in total: W itself comes from an oracle that
runs the same code, so a product that bypasses the multiplier would change W and the next stage's calls equally.

For a Multiply1 product whose root is a leaf with internal precision q_b <= 63, W = 0 and P = 0 by a closed form
(every twiddle and data component has modulus <= sqrt(2) 2^q_b < 2^64; the root's pointwise squares are on the
coarser grid q0 < q_b); otherwise the python-mode oracle replays that Multiply1 product.  BasicMul is the bottom
stage (schoolbook by specification): it calls nothing.
"""

from __future__ import annotations

from collections import Counter

import path_model as PM

__all__ = ["Multiply1Recorder", "stage_expected", "multiply1_basic_calls", "check_basic_calls",
           "lower_stage_counts", "assert_stage_isolated", "check_word_calls"]


def _bits(a: int, b: int) -> int:
    return max(abs(a).bit_length(), abs(b).bit_length(), 1)


def stage_expected(sched, pairs, nets=None) -> Counter:
    """Expected calls of the next stage made by one stage running ``multiply(a, b)`` for every pair under
    ``sched``: "next" = P + W (module docstring), with "kron.product" and "prop18.ring_product" (closed form) and
    "oracle.word_over_64" (W) reported separately."""
    from subnlogn.context import Ctx
    from subnlogn.multiply import multiply
    nets = PM.nets() if nets is None else nets
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), nets)
    W = 0
    for a, b in pairs:
        oracle = Ctx(schedule=sched, products="python", safety_net=False)
        assert multiply(a, b, oracle) == a * b
        W += oracle.inst.counts.get("python.word_product_over_64", 0)
    P = exp["kron.product"] + 4 * exp["prop18.ring_product"]
    return Counter({"next": P + W, "kron.product": exp["kron.product"],
                    "prop18.ring_product": exp["prop18.ring_product"], "oracle.word_over_64": W})


def multiply1_basic_calls(a: int, b: int, sched) -> tuple[int, bool]:
    """(BasicMul calls made by the Multiply1 product a * b under ``sched``, replayed?): 0 by the closed form for
    n <= mul_direct_bits (the listing's direct product) or a leaf root with q_b <= 63; else P + W by the
    python-mode replay of that product (module docstring)."""
    n = _bits(a, b)
    if n <= sched.mul_direct_bits:
        return 0, False
    b_ = max(4, n.bit_length() - 1)
    K0 = PM.root_K0(n, sched.min_root_exponent)
    p0 = 2 * b_ + 2 * K0 + 6                                  # listing L712
    lv = sched.level(1 << K0, p0)
    if lv.leaf and lv.q_b <= 63:
        return 0, False
    return stage_expected(sched, [(a, b)])["next"], True


class Multiply1Recorder:
    """Wrap the CURRENT Hierarchy.multiply1 (monkeypatch): record every call's operands and the number of BasicMul
    calls made inside it (the ``stub``'s call counter, or the "hierarchy.basic" counter for the real BasicMul), and
    in ``words`` the word products (Ctx.word_mul calls, "word.call") made inside it."""

    def __init__(self, monkeypatch, stub=None):
        from subnlogn.hierarchy import Hierarchy
        inner, self.calls, self.words, self.stub = Hierarchy.multiply1, [], [], stub

        def recording(h, x, y):
            before, w0 = self._basic(h), h.inst.counts.get("word.call", 0)
            out = inner(h, x, y)
            self.calls.append((x, y, self._basic(h) - before, h.multiply1_schedule))
            self.words.append(h.inst.counts.get("word.call", 0) - w0)
            return out
        monkeypatch.setattr(Hierarchy, "multiply1", recording)

    def _basic(self, h) -> int:
        return self.stub.calls if self.stub is not None else h.inst.counts.get("hierarchy.basic", 0)


def check_basic_calls(rec: Multiply1Recorder, replay="all") -> Counter:
    """Every recorded Multiply1 call made exactly the BasicMul calls of :func:`multiply1_basic_calls`: the
    closed-form class (0 calls) is checked for EVERY call; the replay class is replayed for every call
    (``replay="all"``) or, to keep the fast suite cheap, for a deterministic sample of at most ``replay`` calls
    evenly spaced in call order (first and last included; the others are counted as "unchecked").  Returns
    Counter(total = BasicMul calls attributed to Multiply1 calls, closed, replayed, unchecked)."""
    out, heavy = Counter(), []
    for i, (x, y, got, sched) in enumerate(rec.calls):
        out["total"] += got
        n = _bits(x, y)
        b_ = max(4, n.bit_length() - 1)
        K0 = PM.root_K0(n, sched.min_root_exponent)
        lv = sched.level(1 << K0, 2 * b_ + 2 * K0 + 6)
        if n <= sched.mul_direct_bits or (lv.leaf and lv.q_b <= 63):
            key = "BasicMul calls of a closed-form Multiply1 product"
            PM.assert_exact({key: got}, {key: 0}, [key])
            out["closed"] += 1
        else:
            heavy.append(i)
    if replay == "all" or len(heavy) <= replay:
        pick = heavy
    else:
        pick = sorted({heavy[(j * (len(heavy) - 1)) // (replay - 1)] for j in range(replay)})
    for i in pick:
        x, y, got, sched = rec.calls[i]
        want, _ = multiply1_basic_calls(x, y, sched)
        key = "BasicMul calls of a replayed Multiply1 product"
        PM.assert_exact({key: got}, {key: want}, [key])
    out["replayed"] = len(pick)
    out["unchecked"] = len(heavy) - len(pick)
    return out


def lower_stage_counts(rec: Multiply1Recorder) -> Counter:
    """The counters the recorded Multiply1 products add to the shared Instrument (tests/path_model.py's model of
    each product under its schedule: the listing's direct product, or the dispatcher's 2D fallback with its
    FastDFT nodes, leaves and butterflies); BasicMul (real or stub) adds its own on top."""
    out = Counter()
    for x, y, _, sched in rec.calls:
        out.update(PM.multiply_counts(sched, [_bits(x, y)]))
    return out


def assert_stage_isolated(counts, sched, pairs, rec: Multiply1Recorder, stub=None, replay="all") -> tuple:
    """The whole identity for one hierarchy-mode context that ran ``multiply(a, b)`` for every pair under
    ``sched`` (the improved multiplier or a 2D route; BasicMul real or the conftest stub): hierarchy.multiply1 = P
    + W exactly (closed form + oracle), kron.product and prop18.ring_product by the closed form, no Python
    product beyond word scale, every Multiply1 call recorded, every BasicMul call made inside a Multiply1 call and
    equal per call to the closed form or the replay (:func:`check_basic_calls`), and hierarchy.word_product = W +
    the BasicMul calls (all Multiply1 roots are leaves: no packed products below).  Returns (expected, result)."""
    exp = stage_expected(sched, pairs)
    PM.assert_exact(counts, {"hierarchy.multiply1": exp["next"], "kron.product": exp["kron.product"],
                             "prop18.ring_product": exp["prop18.ring_product"], "python.big_product": 0,
                             "python.word_product_over_64": 0})
    key = "recorded Multiply1 calls"
    PM.assert_exact({key: len(rec.calls)}, {key: exp["next"]}, [key])
    res = check_basic_calls(rec, replay)
    basic = stub.calls if stub is not None else counts.get("hierarchy.basic", 0)
    PM.assert_exact({"BasicMul calls": basic}, {"BasicMul calls": res["total"]}, ["BasicMul calls"])
    PM.assert_exact(counts, {"hierarchy.word_product": exp["oracle.word_over_64"] + basic})
    check_word_calls(counts, sched, pairs, rec, stub)
    return exp, res


def check_word_calls(counts, sched, pairs, rec: Multiply1Recorder, stub=None) -> int:
    """The word products against the independent STRUCTURAL model (tests/path_model.py), with
    BasicMul contributing none (the stub, or no BasicMul call): every Multiply1 product made exactly its model's
    word.call (its root's pointwise squares and leaf butterflies), and the context's word.call = the top stage's
    model + the Multiply1 products'.  A product that bypasses Ctx.word_mul changes both the measured count and the
    python-mode oracle W, so only this model catches it.  Returns the top stage's modelled word products."""
    basic = stub.calls if stub is not None else counts.get("hierarchy.basic", 0)
    top = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())["word.call"]
    if stub is None and basic:
        return top                    # the real BasicMul adds its own: the full-cascade tests check the aggregate
    lower = 0
    for (x, y, _, msched), got in zip(rec.calls, rec.words):
        want = PM.multiply_counts(msched, [_bits(x, y)])["word.call"]
        PM.assert_exact({"word.call of a Multiply1 product": got}, {"word.call of a Multiply1 product": want},
                        ["word.call of a Multiply1 product"])
        lower += want
    PM.assert_exact(counts, {"word.call": top + lower})
    return top
