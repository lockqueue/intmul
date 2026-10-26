"""Tape-faithful routing of the 2D fallback against the RAM index maps: MS Lemma 2.4 ``lem:routing``
(transposes, odd-stride routing; subnlogn/routing.py), the synthetic FFT's bit reversal and stage
splits (Lemma 2.5 proof), and BaseRadix2FFT's bit reversal and stage splits (MS L693, L821).  Under
schedule.routing = "tape" (default) vs "index" (oracle): bit-identical outputs, identical captured
intermediates, and the pass counts of the proofs (k1 passes per transpose, k1 merge passes per
odd-stride route, k1 bit-reversal passes and k1 stages per G_t1, K passes and K stages per leaf)."""

import random
from collections import Counter

import pytest
from hypothesis import given, settings, strategies as st

from conftest import make_ctx
from subnlogn.basefft import base_radix2_fft, bit_reverse_perm
from subnlogn.fastdft2d import fast_dft
from subnlogn.fixedpoint import FxVec, Rounding
from subnlogn.instrument import Instrument
from subnlogn.multiply import multiply, root_parameters
from subnlogn.routing import (bit_reverse_tape, index_columns_to_rows, index_odd_stride_route,
                              index_rows_to_columns, odd_stride_route_tape, transpose_columns_to_rows,
                              transpose_rows_to_columns)
from subnlogn.schedule import Schedule, faithful_schedule, test_schedule
from subnlogn.synthetic import odd_stride_route, synthetic_fft, synthetic_fft_tape
from subnlogn.tables import leaf_tables

SHAPES = [(1 << k1, 1 << k2) for k2 in range(7) for k1 in range(k2 + 1)]      # all t1 | r <= 64


def _routing(counts) -> dict:
    return {k: v for k, v in counts.items() if k.startswith("routing.") and v}


def _non_routing(counts) -> dict:
    """Counters other than routing passes; table-generation counters ("tables.*") are dropped too,
    because they depend on the shared table cache (only the first run of a pair builds the tables)."""
    return {k: v for k, v in counts.items() if not k.startswith(("routing.", "tables."))}


class Opaque:
    """A payload that refuses to be decoded: comparisons, hashing and arithmetic raise."""

    __slots__ = ("tag",)

    def __init__(self, tag):
        self.tag = tag

    def _no(self, *a):
        raise AssertionError("routing decoded a record")

    __eq__ = __ne__ = __lt__ = __le__ = __gt__ = __ge__ = __hash__ = __bool__ = __int__ = _no


def _payloads(rng, n):
    """Random (re, im) records with repeated values (so a value-based shortcut would be caught by the
    identity checks below)."""
    return [(rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(n)]


def _same_objects(a, b):
    return len(a) == len(b) and all(x is y for x, y in zip(a, b))


# ------------------------------------------------------------------------------------ Lemma 2.4 (i)
@pytest.mark.parametrize("t1,r", SHAPES)
def test_transposes_against_index_maps(t1, r):
    """Lemma 2.4(i) both ways, k1 passes each, equal to the index maps (the same objects moved)."""
    rng = random.Random(t1 * 1000 + r)
    recs = _payloads(rng, t1 * r)
    k1 = t1.bit_length() - 1
    inst = Instrument()
    cols = transpose_rows_to_columns(recs, t1, r, inst)
    assert _same_objects(cols, index_rows_to_columns(recs, t1, r))
    assert inst.counts["routing.transpose_pass"] == k1
    rows = transpose_columns_to_rows(cols, t1, r, inst)
    assert _same_objects(rows, recs)                                 # the reverse passes invert
    assert _same_objects(transpose_columns_to_rows(recs, t1, r), index_columns_to_rows(recs, t1, r))
    assert inst.counts["routing.transpose_pass"] == 2 * k1
    assert inst.counts["routing.merge_pass"] == 0


# ------------------------------------------------------------------------------------ Lemma 2.4 (ii)
@pytest.mark.parametrize("t1,r", SHAPES)
def test_odd_stride_route_against_index_maps(t1, r):
    """Lemma 2.4(ii): transpose, tag scan, k1 merge passes == synthetic.odd_stride_route (the index map
    of today's FastDFT) and the flat index oracle."""
    rng = random.Random(t1 * 7919 + r)
    C_re = [[rng.randint(-9, 9) for _ in range(r)] for _ in range(t1)]
    C_im = [[rng.randint(-9, 9) for _ in range(r)] for _ in range(t1)]
    recs = [rec for v1 in range(t1) for rec in zip(C_re[v1], C_im[v1])]
    inst = Instrument()
    out = odd_stride_route_tape(recs, t1, r, inst)
    assert _same_objects(out, index_odd_stride_route(recs, t1, r))
    cols_re, cols_im = odd_stride_route(C_re, C_im, t1, r)
    assert [[a for a, _ in out[u2 * t1:(u2 + 1) * t1]] for u2 in range(r)] == cols_re
    assert [[b for _, b in out[u2 * t1:(u2 + 1) * t1]] for u2 in range(r)] == cols_im
    k1 = t1.bit_length() - 1
    assert inst.counts["routing.merge_pass"] == k1 and inst.counts["routing.transpose_pass"] == k1
    assert inst.counts["routing.tag_scan"] == 1


def test_records_stay_opaque():
    """Only tags and counters are inspected: payloads whose comparison, hashing or arithmetic raises
    are routed unchanged (identity preserved) by all three procedures."""
    for t1, r in [(8, 8), (4, 16), (16, 32)]:
        recs = [Opaque(i) for i in range(t1 * r)]
        assert _same_objects(transpose_rows_to_columns(recs, t1, r), index_rows_to_columns(recs, t1, r))
        assert _same_objects(transpose_columns_to_rows(recs, t1, r), index_columns_to_rows(recs, t1, r))
        assert _same_objects(odd_stride_route_tape(recs, t1, r), index_odd_stride_route(recs, t1, r))


@pytest.mark.parametrize("t1,r,n", [(3, 6, 18), (2, 6, 12), (4, 2, 8), (2, 4, 7), (0, 4, 0)])
def test_hypotheses_enforced(t1, r, n):
    """Lemma 2.4's hypotheses: powers of two t1 | r and t1 r records."""
    recs = list(range(n))
    for fn in (transpose_rows_to_columns, transpose_columns_to_rows, odd_stride_route_tape):
        with pytest.raises(ValueError):
            fn(recs, t1, r)


@settings(max_examples=40)
@given(st.integers(0, 7), st.integers(0, 7), st.randoms(use_true_random=False))
def test_property_routing(k1, dk, rnd):
    """Property: for random shapes t1 = 2^k1 | r = 2^(k1 + dk) <= 2^14 records, the tape procedures equal
    the index maps and the two transposes are mutually inverse."""
    if k1 + dk > 7:
        k1, dk = k1 % 4, dk % 4
    t1, r = 1 << k1, 1 << (k1 + dk)
    recs = [object() for _ in range(t1 * r)]
    rnd.shuffle(recs)
    cols = transpose_rows_to_columns(recs, t1, r)
    assert _same_objects(cols, index_rows_to_columns(recs, t1, r))
    assert _same_objects(transpose_columns_to_rows(cols, t1, r), recs)
    assert _same_objects(odd_stride_route_tape(recs, t1, r), index_odd_stride_route(recs, t1, r))


# ------------------------------------------------------------------------------------ bit reversal
@pytest.mark.parametrize("unit", [1, 3])
def test_bit_reverse_tape(unit):
    """k split-and-concatenate passes == the bit-reversal index map, for units of 1 record (leaf) and of
    several records (synthetic FFT polynomials); the same objects are moved; one counter hit per pass."""
    for k in range(11):
        recs = [object() for _ in range(unit << k)]
        inst = Instrument()
        out = bit_reverse_tape(recs, k, unit, inst, "routing.leaf_bitrev_pass")
        rev = bit_reverse_perm(k) if k else [0]
        exp = [None] * len(recs)
        for j in range(1 << k):
            exp[rev[j] * unit:(rev[j] + 1) * unit] = recs[j * unit:(j + 1) * unit]
        assert _same_objects(out, exp) and inst.counts["routing.leaf_bitrev_pass"] == k
    with pytest.raises(ValueError):
        bit_reverse_tape(list(range(6)), 2, 1)


# ------------------------------------------------------------------------------------ synthetic FFT
@pytest.mark.parametrize("t1,r", SHAPES)
def test_synthetic_fft_tape_against_index(t1, r):
    """G_{t1} by the Lemma 2.5 tape procedure == synthetic_fft (index access), bit for bit; k1 passes
    and k1 stage splits; the same butterfly count."""
    rng = random.Random(t1 * 31 + r)
    big = 1 << 30
    P_re = [[rng.randint(-big, big) for _ in range(r)] for _ in range(t1)]
    P_im = [[rng.randint(-big, big) for _ in range(r)] for _ in range(t1)]
    shr = Rounding.HALF_EVEN.shr
    a, b = Instrument(), Instrument()
    assert synthetic_fft_tape(P_re, P_im, r // t1, shr, b) == synthetic_fft(P_re, P_im, r // t1, shr, a)
    k1 = t1.bit_length() - 1
    assert b.counts["routing.syn_bitrev_pass"] == b.counts["routing.syn_stage_split"] == k1
    assert a.counts["synfft.butterfly"] == b.counts["synfft.butterfly"]


# ------------------------------------------------------------------------------------ leaf FFT
@pytest.mark.parametrize("K", list(range(13)))
def test_leaf_tape_against_index(K):
    """BaseRadix2FFT with the tape realization (K-pass bit reversal, per-stage half-block splits with
    the contiguous stage-s twiddle lists) == the index variant bit for bit, at three precisions."""
    R = 1 << K
    sched = test_schedule(base_threshold=R)
    for p in (8, 20, 41):
        lv = sched.level(R, p)
        q = p + 2
        rng = random.Random(K * 100 + p)
        big = (1 << (q + p)) * 7 // 10
        re = [rng.randint(-big, big) for _ in range(R)]
        im = [rng.randint(-big, big) for _ in range(R)]
        res = {}
        for mode in ("index", "tape"):
            ctx = make_ctx(sched.with_(routing=mode), monitor=True)
            res[mode] = (base_radix2_fft(ctx, re, im, lv), ctx.inst)
        (oi, ii), (ot, it) = res["index"], res["tape"]
        assert ot == oi and it.heights == ii.heights and _non_routing(it.counts) == _non_routing(ii.counts)
        exp = {"routing.leaf_bitrev_pass": K, "routing.leaf_stage_split": K} if K else {}
        assert _routing(it.counts) == exp


def test_leaf_stage_twiddle_lists():
    """Table (d) stage lists: stage s holds Q(e^{2 pi i u 2^(K-s)/R}), u < 2^(s-1), contiguous; R - 1
    entries in total (MS §2.2 (d))."""
    ctx = make_ctx(test_schedule(base_threshold=1024), tables_dict={})
    for K in range(11):
        lv = ctx.schedule.level(1 << K, 20)
        tab = leaf_tables(ctx, lv)
        assert len(tab.stages) == K and sum(len(a) for a, _ in tab.stages) == (1 << K) - 1
        for s, (a, b) in enumerate(tab.stages, start=1):
            assert a == tab.tw_re[::1 << (K - s)][:1 << (s - 1)]
            assert b == tab.tw_im[::1 << (K - s)][:1 << (s - 1)]


# ------------------------------------------------------------------------------------ FastDFT
def _expected_passes(sched: Schedule, R: int, p: int) -> dict:
    """Routing counters of one FastDFT call: each node at depth d (prod_{e<d} t1_e of them) with
    k1 = chain[d].k1 does the de-interleave, the transpose inside the odd-stride route and the output
    transpose (3 k1 passes), one tag scan, k1 merge passes, and its synthetic FFT does k1 bit-reversal
    passes and k1 stage splits; each leaf of length 2^K > 1 does K bit-reversal passes and K stages."""
    exp: Counter = Counter()
    nodes = 1
    for lv in sched.chain(R, p):
        if lv.leaf:
            if lv.K:
                exp["routing.leaf_bitrev_pass"] += nodes * lv.K
                exp["routing.leaf_stage_split"] += nodes * lv.K
            break
        exp["routing.transpose_pass"] += nodes * 3 * lv.k1
        exp["routing.tag_scan"] += nodes
        exp["routing.merge_pass"] += nodes * lv.k1
        exp["routing.syn_bitrev_pass"] += nodes * lv.k1
        exp["routing.syn_stage_split"] += nodes * lv.k1
        nodes *= lv.t1
    return {k: v for k, v in exp.items() if v}


def _twice(d: dict) -> dict:
    return {k: 2 * v for k, v in d.items()}


def _run_both(sched: Schedule, R: int, p: int, seed: int):
    rng = random.Random(seed)
    q = p + 2
    big = (1 << (q + p)) * 7 // 10
    x = FxVec([rng.randint(-big, big) for _ in range(R)], [rng.randint(-big, big) for _ in range(R)], q)
    out = {}
    for mode in ("index", "tape"):
        ctx = make_ctx(sched.with_(routing=mode), capture=True)
        z = fast_dft(ctx, x, R, p)
        out[mode] = (z, ctx.capture, ctx.inst.counts)
    return out


@pytest.mark.parametrize("R,bt", [(4, 2), (8, 2), (16, 2), (32, 2), (64, 2), (128, 2), (256, 2),
                                  (1024, 2), (256, 16), (512, 8), (64, 4)])
def test_fastdft_tape_equals_index(R, bt):
    """FastDFT under routing="tape" equals routing="index" bit for bit: output, every captured
    intermediate (U_rows, V_rows, Y_cols, Zcomp, level) and every non-routing counter; the routing
    counters equal the proof's pass counts."""
    sched = test_schedule(base_threshold=bt)
    p = max(8, R.bit_length() - 1) + 12
    res = _run_both(sched, R, p, seed=R + 31 * bt)
    (zi, ci, ni), (zt, ct, nt) = res["index"], res["tape"]
    assert zt == zi
    assert set(ct) == set(ci) and all(ct[k] == ci[k] for k in ci), sorted(k for k in ci if ct[k] != ci[k])
    assert _non_routing(nt) == _non_routing(ni) and not _routing(ni)
    assert _routing(nt) == _expected_passes(sched, R, p)


@pytest.mark.parametrize("R,p", [(512, 9), (1024, 10)])
def test_fastdft_faithful_schedule_tape_equals_index(R, p):
    """The faithful schedule at sizes where it recurses by itself (R > 4 p^2)."""
    sched = faithful_schedule()
    assert not sched.level(R, p).leaf
    res = _run_both(sched, R, p, seed=R)
    assert res["tape"][0] == res["index"][0] and res["tape"][1] == res["index"][1]
    assert _routing(res["tape"][2]) == _expected_passes(sched, R, p)


def test_routing_is_the_default_and_validated():
    assert Schedule(name="x").routing == "tape" and faithful_schedule().routing == "tape"
    assert test_schedule().routing == "tape"
    with pytest.raises(ValueError):
        Schedule(name="x", routing="ram")


# ------------------------------------------------------------------------------------ multiply
def _multiply_both(sched: Schedule, n: int, seed: int, pairs: int = 2):
    rng = random.Random(seed)
    for _ in range(pairs):
        a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)
        res = {}
        for mode in ("index", "tape"):
            ctx = make_ctx(sched.with_(routing=mode))
            prod = multiply(a, b, ctx)
            res[mode] = (prod, ctx.inst.notes, ctx.inst.counts)
        (pi, mi, ni), (pt, mt, nt) = res["index"], res["tape"]
        assert pi == pt == a * b
        assert mi == mt                                              # identical recovery margins
        assert _non_routing(nt) == _non_routing(ni) and not _routing(ni)
    return nt


@pytest.mark.parametrize("n", [100, 1000, 4000])
def test_multiply_deep_tape_equals_index(n):
    """multiply under the forced-deep test schedule: identical products, recovery margins (so the
    transforms were bit-identical) and non-routing counters; two transforms' worth of routing passes."""
    sched = test_schedule(base_threshold=2)
    counts = _multiply_both(sched, n, seed=n)
    _, _, K0, R0, p0 = root_parameters(n)
    assert _routing(counts) == _twice(_expected_passes(sched, R0, p0))


@pytest.mark.parametrize("n", [10 ** 4, 10 ** 5])
def test_multiply_faithful_tape_equals_index(n):
    """Faithful schedule at 10^4 and 10^5 bits: R0 <= 4 p0^2 (2^11 vs 4 54^2, 2^14 vs 4 66^2), so each
    transform is a single leaf: only the leaf's routing runs (K0 bit-reversal passes and K0 stages
    per transform); the faithful 2D recursion starts at K0 = 15 (n ~ 1.39 10^5, slow test below)."""
    counts = _multiply_both(faithful_schedule(), n, seed=n, pairs=1)
    _, _, K0, R0, p0 = root_parameters(n)
    assert _routing(counts) == {"routing.leaf_bitrev_pass": 2 * K0, "routing.leaf_stage_split": 2 * K0}


def test_multiply_deep_1e4_tape_equals_index():
    """10^4 bits under the forced-deep test schedule (routing at every node of 4 levels)."""
    sched = test_schedule(base_threshold=2)
    counts = _multiply_both(sched, 10 ** 4, seed=10 ** 4, pairs=1)
    _, _, K0, R0, p0 = root_parameters(10 ** 4)
    assert _routing(counts) == _twice(_expected_passes(sched, R0, p0))


@pytest.mark.slow
@pytest.mark.parametrize("which,n", [("deep", 10 ** 5), ("faithful", 140000)])
def test_multiply_large_tape_equals_index(which, n):
    """10^5 bits under the deep test schedule (routing at every node), and the faithful schedule at
    n = 140000 (K0 = 15, R0 = 32768 > 4 p0^2 = 19600), where it recurses by itself: its top node routes
    32768 records per transform (t1 = 128, r = 256)."""
    sched = faithful_schedule() if which == "faithful" else test_schedule(base_threshold=2)
    counts = _multiply_both(sched, n, seed=n, pairs=1)
    _, _, K0, R0, p0 = root_parameters(n)
    exp = _expected_passes(sched, R0, p0)
    assert _routing(counts) == _twice(exp)
    if (which, n) == ("faithful", 140000):
        assert not sched.level(R0, p0).leaf and exp["routing.merge_pass"] == 7
