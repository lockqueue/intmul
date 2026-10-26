"""Stage isolation of the multiplier hierarchy for tests and the hierarchy pass (for runtime reasons;
compositional verification).  Not part of the library."""

from __future__ import annotations


class BasicMulStub:
    """Stage isolation for hierarchy-mode tests (runtime cost): an EXACT stand-in for BasicMul that
    counts its calls and the largest operand.  With word-scale products routed (Ctx.word_mul), every
    packed product above ~1000 bits makes Multiply1 call BasicMul once per butterfly product (0.8 ms
    each; a bridge product in full hierarchy mode takes hours in Python).  Tests of the bridge families
    therefore run the improved multiplier and the REAL Multiply1 (every packed and word product of the
    top level goes to it, and it routes its own products) with only the Multiply1 -> BasicMul calls
    stubbed; BasicMul itself is verified separately (tests/test_m7_dispatch.py, exact internal counters),
    and full-cascade runs cover the 2D families.  The library has no shortcut:
    this stub exists only in the test harness."""

    def __init__(self, real=None):
        self.real = real                                  # the genuine Hierarchy.basic_mul
        self.calls = 0
        self.max_bits = 0
        self.pairs: dict[tuple[int, int], int] = {}      # (bits of a, bits of b) -> calls

    def __call__(self, hierarchy, a: int, b: int) -> int:
        self.calls += 1
        la, lb = a.bit_length(), b.bit_length()
        self.max_bits = max(self.max_bits, la, lb)
        self.pairs[(la, lb)] = self.pairs.get((la, lb), 0) + 1
        return a * b

    def verify_real_basic_mul(self, limit: int = 400, seed: int = 0) -> int:
        """Compositional check: run the REAL BasicMul on every distinct operand-
        size pair the stub absorbed (or, beyond ``limit`` pairs, on a stratified sample that keeps the
        smallest and largest pair of every 8-bit size bucket), on random signed operands of exactly those
        bit lengths, and assert the product and BasicMul's internal counters exactly: one Multiply call,
        two leaf transforms of length R0 (K0 R0/2 butterflies each), no FastDFT node, no packed product,
        no python big product.  Returns the number of pairs checked."""
        import random
        from subnlogn.hierarchy import Hierarchy
        from subnlogn.multiply import root_parameters
        pairs = sorted(self.pairs)
        if len(pairs) > limit:
            buckets: dict[tuple[int, int], list] = {}
            for pr in pairs:
                buckets.setdefault((pr[0] // 8, pr[1] // 8), []).append(pr)
            pairs = sorted({x for v in buckets.values() for x in (v[0], v[-1])})
        rng = random.Random(seed)
        for la, lb in pairs:
            h = Hierarchy()
            a = (rng.getrandbits(la - 1) | (1 << (la - 1))) if la else 0
            b = (rng.getrandbits(lb - 1) | (1 << (lb - 1))) if lb else 0
            a, b = (-a if rng.random() < 0.5 else a), (-b if rng.random() < 0.5 else b)
            assert self.real(h, a, b) == a * b, (la, lb)
            c = h.inst.counts
            n = max(la, lb, 1)
            if n <= 64:                                  # never routed (Ctx.word_mul keeps these inline)
                continue
            _, _, K0, R0, _ = root_parameters(n)
            assert (c["hierarchy.basic"], c["multiply.call"], c["fastdft.leaf"]) == (1, 1, 2), (la, lb, dict(c))
            assert c["basefft.butterfly"] == 2 * K0 * (R0 // 2), (la, lb)
            assert c.get("fastdft.node", 0) == c.get("kron.product", 0) == c.get("python.big_product", 0) == 0
        return len(pairs)

