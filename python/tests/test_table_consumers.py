"""Consumer-side table tests.

Every table entry a consumer reads is captured AT THE CONSUMER, during a real transform, by wrapping the name the
consumer looks up (``fastdft2d.level_tables_2d``, ``fastdft2d.twist_rows`` / ``spread_row`` / ``cyclic_solve``,
``basefft._stages_tape`` / ``leaf_tables``, ``bridge.spread.bridge_filter`` / ``spread_row``,
``bridge.deconv.bridge_solver_tuple`` / ``cyclic_solve``, ``bridge.middle._axis_twiddles``,
``middle3.bluestein._tables``, ``walsh.fft.phase_table``), and compared with a value computed HERE, independently of
``subnlogn.certified``, with mpmath at q + 128 bits:

- correctly rounded tables (MS Def. 2.1: Q_q = nearest, ties to even, of 2^q x): the 2D leaf twiddles
  Q_{q_b}(e^{2 pi i u / 2^s}) as the stage-s lists the leaf replays and as the index-routing list (MS §2.2 (d),
  L693), the 2D twist roots Q_q(e^{pi i k / r}) (MS §2.2 (b)), the folded modulated filter taps of Step 1 and of the
  bridge spreads (MS §6.1 (a)-(d); r2 (8.1), §4.7: h(d) = sum_{|e| <= m, e = d mod t} g(e + delta),
  g(s) = e^{-pi i s/t} sinc(s) e^{-pi s^2/alpha^2}, alpha^2 = 4 w ln 2 / pi), the solver scalars c0, c1, mu, a-hat
  (r2 (8.2), (4.15)-(4.16): c0 = G((u+1/2)/t), c1 = G((u+1/2)/t - 1), G(xi) = (erf(a(xi+1/2)) - erf(a(xi-1/2)))/2,
  a = 2 sqrt(w ln 2), mu = Q(1/max), a-hat = Q(min/max)) and the direct middle's twiddles Q_{q_m}(e^{2 pi i k/t});
- the Kronecker-packed filters: exactly sum_b tap_b 2^{b B} (MS Lemma 6.2);
- the closure gamma-hat (documented rounding: br_r2 (4.21) truncated powering, not correct rounding): within
  (1/2 + 2^-10) units of the exact rational 1/(1 - rho-hat^L) (r2 (4.17) with v = 2^-q, SPEC v1.2 §5.10), and equal to
  an independent transcription of the (4.21) recipe;
- the disk phase tables (documented rounding: truncation toward zero per component, SPEC §5.9 ``disk_round``) of the
  Bluestein middle (chirp and twists) and of the Walsh last-axis twiddles.
"""

import random
from fractions import Fraction
from types import SimpleNamespace

import mpmath
import pytest
from mpmath import mp, mpf

from subnlogn import basefft, fastdft2d
from subnlogn.bridge import deconv as bdeconv
from subnlogn.bridge import middle as bmiddle
from subnlogn.bridge import spread as bspread
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.context import Ctx
from subnlogn.fixedpoint import FxVec
from subnlogn.middle3 import bluestein
from subnlogn.schedule import faithful_schedule, test_schedule
from subnlogn.walsh import fft as wfft

GUARD = 128                       # mpmath working precision: q + GUARD bits


# -- independent rounding of high-precision values -------------------------------------------------------------


def _decided(frac) -> None:
    """The working precision decides the rounding: the scaled value is not within 2^-64 of a decision point."""
    if frac != 0 and abs(frac - mpf(1) / 2) < mpmath.ldexp(1, -64):
        raise AssertionError("rounding undecided at this working precision")


def rhe(x, q: int) -> int:
    """Q_q(x) as a numerator: round half to even of 2^q x (MS Def. 2.1)."""
    y = mpmath.ldexp(x, q)
    n = int(mpmath.floor(y))
    frac = y - n
    _decided(frac)
    if frac > mpf(1) / 2 or (frac == mpf(1) / 2 and n & 1):
        n += 1
    return n


def trunc0(x, p: int) -> int:
    """Truncation toward zero of 2^p x (SPEC §1.4 Q_p, §5.9 disk_round)."""
    y = mpmath.ldexp(x, p)
    n = int(mpmath.floor(abs(y)))
    frac = abs(y) - n
    if frac != 0 and (frac < mpmath.ldexp(1, -64) or 1 - frac < mpmath.ldexp(1, -64)):
        raise AssertionError("truncation undecided at this working precision")
    return -n if y < 0 else n


# -- independent table values ----------------------------------------------------------------------------------


def unit_root(num: int, den: int, q: int) -> tuple[int, int]:
    """Q_q(e^{2 pi i num/den})."""
    with mp.workprec(q + GUARD):
        h = mpf(2 * num) / den
        return rhe(mpmath.cospi(h), q), rhe(mpmath.sinpi(h), q)


def disk_phase(k: int, r: int, p: int) -> tuple[int, int]:
    """Component-wise truncation toward zero of 2^p e^{pi i k/r}."""
    with mp.workprec(p + GUARD):
        h = mpf(k) / r
        return trunc0(mpmath.cospi(h), p), trunc0(mpmath.sinpi(h), p)


def folded_taps(delta: Fraction, t: int, m: int, w: int, q: int, carrier: int = -1):
    """(Q_q Re h(d), Q_q Im h(d)) for d < t, h(d) = sum_{|e| <= m, e = d mod t} g(e + delta) (MS §6.1 (c); r2 (8.1),
    §4.7), summed term by term."""
    with mp.workprec(q + GUARD):
        alpha2 = 4 * w * mpmath.log(2) / mpmath.pi
        dl = mpf(delta.numerator) / delta.denominator
        acc = [[mpf(0), mpf(0)] for _ in range(t)]
        for e in range(-m, m + 1):
            s = e + dl
            sinc = mpf(1) if s == 0 else mpmath.sinpi(s) / (mpmath.pi * s)
            g = mpmath.expjpi(carrier * s / t) * sinc * mpmath.exp(-mpmath.pi * s * s / alpha2)
            acc[e % t][0] += g.real
            acc[e % t][1] += g.imag
        return [(rhe(a, q), rhe(b, q)) for a, b in acc]


def filter_layout(h, t: int, m: int):
    """MS §6.1 (d) / Thm 6.3 storage: W = 2m + 1 <= t: f_b = h((m - b) mod t), offset m; else f_a = h((-a) mod t),
    offset 0.  Returns (taps_re, taps_im, offset)."""
    W = 2 * m + 1
    idx = [(m - b) % t for b in range(W)] if W <= t else [(-a) % t for a in range(t)]
    return tuple(h[i][0] for i in idx), tuple(h[i][1] for i in idx), (m if W <= t else 0)


def solver_scalars(u: int, t: int, w: int, q: int):
    """(Q c0, Q c1, Q 1/M, Q min/max, forward) of r2 (8.2), (4.15)-(4.16)."""
    with mp.workprec(q + GUARD):
        a = 2 * mpmath.sqrt(w * mpmath.log(2))
        G = lambda xi: (mpmath.erf(a * (xi + mpf(1) / 2)) - mpmath.erf(a * (xi - mpf(1) / 2))) / 2  # noqa: E731
        y = (mpf(u) + mpf(1) / 2) / t
        c0, c1 = G(y), G(y - 1)
        M, mn = max(c0, c1), min(c0, c1)
        return rhe(c0, q), rhe(c1, q), rhe(1 / M, q), rhe(mn / M, q), c0 > c1


def clog2(x: int) -> int:
    """ceil(lg x) for x >= 1 by doubling."""
    k, v = 0, 1
    while v < x:
        v, k = 2 * v, k + 1
    return k


def closure_421(a_hat: int, L: int, q: int, t: int) -> int:
    """br_r2 §4.6 (4.21) with P -> q (SPEC v1.2 §5.10): binary powering of a-hat 2^-q truncated at
    Q = q + ceil(lg L) + 2 ceil(lg 4t) + 10, guarded division at scale Q, one final nearest rounding to q."""
    Q = q + clog2(L) + 2 * clog2(4 * t) + 10
    base, acc, e = a_hat << (Q - q), 1 << Q, L
    while e:
        if e % 2:
            acc = (acc * base) >> Q
        e //= 2
        if e:
            base = (base * base) >> Q
    g = (1 << (2 * Q)) // ((1 << Q) - acc)
    s = Q - q
    n, rem = g >> s, g & ((1 << s) - 1)
    half = 1 << (s - 1)
    return n + 1 if rem > half or (rem == half and n & 1) else n


def check_solver_tuple(st, u: int, t: int, L: int, w: int, q: int) -> None:
    """``st`` has the fields the consumer reads (mu, rho, gamma, forward) and, for a stored SolverTuple, c0 and c1."""
    c0, c1, mu, a, fwd = solver_scalars(u, t, w, q)
    assert (st.mu, st.rho, st.forward) == (mu, -a, fwd), (u, t, L, w, q)
    if hasattr(st, "c0"):
        assert (st.c0, st.c1) == (c0, c1), (u, t, L, w, q)
    exact = 1 / (1 - Fraction(a, 1 << q) ** L)                  # r2 (4.17) target, from the STORED rho-hat
    assert abs(Fraction(st.gamma, 1 << q) - exact) <= (Fraction(1, 2) + Fraction(1, 1024)) / (1 << q)
    assert st.gamma == closure_421(a, L, q, t)


def packed(taps, B: int) -> int:
    """Pack_B(taps) = sum_b taps_b 2^{b B} (MS eq. (pack-def))."""
    return sum(v << (b * B) for b, v in enumerate(taps))


class Recorder:
    """Wrap names a consumer looks up and log (args, kwargs, result) of every call."""

    def __init__(self, monkeypatch):
        self.monkeypatch = monkeypatch

    def wrap(self, module, name: str) -> list:
        orig, log = getattr(module, name), []

        def wrapper(*args, **kwargs):
            out = orig(*args, **kwargs)
            log.append((args, kwargs, out))
            return out

        self.monkeypatch.setattr(module, name, wrapper)
        return log


def _input(R: int, p: int, seed: int) -> FxVec:
    rng = random.Random(seed)
    big = (1 << (2 * p + 2)) * 7 // 10                   # ||x|| close to 2^p on C~_{p+2}
    return FxVec([rng.randint(-big, big) for _ in range(R)], [rng.randint(-big, big) for _ in range(R)], p + 2)


# -- 2D FastDFT ------------------------------------------------------------------------------------------------


def check_leaf_stages(K: int, qb: int, stages) -> int:
    """MS L693 / §2.2 (d): stage s replays (Q_{q_b}(e^{2 pi i u/2^s}))_{u < 2^(s-1)}."""
    assert len(stages) == K
    for s in range(1, K + 1):
        expect = [unit_root(u, 1 << s, qb) for u in range(1 << (s - 1))]
        assert (list(stages[s - 1][0]), list(stages[s - 1][1])) == \
            ([c for c, _ in expect], [d for _, d in expect]), (K, qb, s)
    return (1 << K) - 1


def test_2d_node_tables_as_consumed(monkeypatch):
    """test_schedule(base_threshold=16), R = 256, p = 16: one node (t1 = r = 16, W > r: folded filters) over leaves of
    R = 16 at p_child.  Twist roots, filter taps and packed filters, solver tuples and gamma-hat as the node reads
    them, and the leaves' stage-s twiddle lists."""
    rec = Recorder(monkeypatch)
    tabs = rec.wrap(fastdft2d, "level_tables_2d")
    twists = rec.wrap(fastdft2d, "twist_rows")
    spreads = rec.wrap(fastdft2d, "spread_row")
    solves = rec.wrap(fastdft2d, "cyclic_solve")
    leaves = rec.wrap(basefft, "_stages_tape")
    R, p = 256, 16
    ctx = Ctx(schedule=test_schedule(base_threshold=16), tables={})
    fastdft2d.fast_dft(ctx, _input(R, p, 1), R, p)
    (_, lv), _, _ = tabs[0]
    assert len(tabs) == 1 and not lv.leaf
    q, r, t1 = lv.q_child, lv.r, lv.t1
    zeta = [unit_root(k, 2 * r, q) for k in range(r)]           # zeta-bar_k = Q_q(e^{pi i k/r})
    assert len(twists) == 2
    for (args, _, _) in twists:                                 # pre- and post-twist read the same roots
        assert (list(args[2]), list(args[3]), args[4]) == ([c for c, _ in zeta], [s for _, s in zeta], q)
    assert len(spreads) == t1
    for j1, (args, _, _) in enumerate(spreads):                 # Step 1 row j1: delta = j1/t1
        f_re, f_im, F_re, F_im, offset, B = args[2:8]
        h = folded_taps(Fraction(j1, t1), r, lv.m1, lv.p_work, q) if j1 else [(1 << q, 0)] + [(0, 0)] * (r - 1)
        assert (f_re, f_im, offset) == filter_layout(h, r, lv.m1), j1
        assert B == lv.B_slot and F_re == packed(f_re, B) and F_im == packed(f_im, B)
    assert len(solves) == r
    for u2, (args, _, _) in enumerate(solves):                  # Step 3 column u2: cycle length L = t1
        mu, rho, gamma, fwd = args[2:6]
        assert len(args[0]) == t1 and args[6] == q
        consumed = SimpleNamespace(mu=mu, rho=rho, gamma=gamma, forward=fwd)   # exactly what the solver reads
        check_solver_tuple(consumed, u2, r, t1, lv.p_work, q)
    assert len(leaves) == t1                                    # t1 child leaves of length r
    n = 0
    for key in {(args[3], args[4]) for args, _, _ in leaves}:
        stages = next(args[6] for args, _, _ in leaves if (args[3], args[4]) == key)
        n += check_leaf_stages(*key, stages)
    assert n == r - 1


def test_2d_faithful_leaf_twiddles_both_routings(monkeypatch):
    """faithful_schedule(), R = 256, p = 10 (a leaf: R <= 4p^2), q_b = p + K + 16: the stage lists the tape leaf
    replays and the tw list the index leaf reads (stride R/2^s), both from the consumer's lookups."""
    rec = Recorder(monkeypatch)
    stages_log = rec.wrap(basefft, "_stages_tape")
    tabs = rec.wrap(basefft, "leaf_tables")
    R, p = 256, 10
    for routing in ("tape", "index"):
        ctx = Ctx(schedule=faithful_schedule().with_(routing=routing), tables={})
        fastdft2d.fast_dft(ctx, _input(R, p, 2), R, p)
    (args, _, _), = stages_log
    K, qb = args[3], args[4]
    assert (K, qb) == (8, p + 8 + 16)
    check_leaf_stages(K, qb, args[6])
    tab = tabs[-1][2]                                           # the index run's table object
    expect = [unit_root(k, R, qb) for k in range(R // 2)]
    assert (tab.tw_re, tab.tw_im) == ([c for c, _ in expect], [s for _, s in expect])


# -- bridge ---------------------------------------------------------------------------------------------------


def _bridge_run(monkeypatch, d: int, K: int, p: int, middle: str, seed: int) -> dict:
    rec = Recorder(monkeypatch)
    logs = {"filters": rec.wrap(bspread, "bridge_filter"), "spreads": rec.wrap(bspread, "spread_row"),
            "tuples": rec.wrap(bdeconv, "bridge_solver_tuple"), "solves": rec.wrap(bdeconv, "cyclic_solve"),
            "twiddles": rec.wrap(bmiddle, "_axis_twiddles"), "blue": rec.wrap(bluestein, "_tables"),
            "walsh": rec.wrap(wfft, "phase_table")}
    sched = test_schedule(bridge_d=d).with_(bridge_middle=middle, bridge_movement="lemma12")
    ctx = Ctx(schedule=sched, tables={}, capture={})
    bridge_dft(ctx, _input(1 << K, p, seed), 1 << K, p, d)
    logs["params"] = ctx.capture["bridge_params"]
    return logs


def check_bridge_spreads_and_solvers(logs) -> None:
    filters = {}
    for args, _, f in logs["filters"]:                          # every (delta, t, m, w, q) the spreads looked up
        delta, t, m, w, q = args[1:6]
        key = (delta, t, m, w, q)
        if key not in filters:
            h = folded_taps(delta, t, m, w, q) if delta else [(1 << q, 0)] + [(0, 0)] * (t - 1)
            filters[key] = filter_layout(h, t, m)
        assert (f.taps_re, f.taps_im, f.offset) == filters[key], key
    taps = {(fr, fi) for fr, fi, _ in filters.values()}
    assert logs["spreads"]
    for args, _, _ in logs["spreads"]:                          # what each line's overlap-add multiplies by
        f_re, f_im, F_re, F_im, _, B = args[2:8]
        assert (f_re, f_im) in taps and F_re == packed(f_re, B) and F_im == packed(f_im, B)
    tuples = set()
    for args, _, st in logs["tuples"]:
        u, t, L, w, q = args[1:6]
        check_solver_tuple(st, u, t, L, w, q)
        tuples.add((st.mu, st.rho, st.gamma, st.forward))
    assert logs["solves"]
    for args, _, _ in logs["solves"]:                           # what each deconvolution cycle reads
        assert tuple(args[2:6]) in tuples


def test_bridge_direct_tables_as_consumed(monkeypatch):
    """Bridge d = 2, K = 6 (t = (8, 8)), p = 10, direct middle, Lemma 12 movements: folded filters (all 8 shifts),
    packed filters at the overlap-add, axis solver tuples with gamma-hat (L = A_2 = 8), and the direct middle's
    twiddles Q_{q_m}(e^{2 pi i k/8}) (the base FFT of the bridge)."""
    logs = _bridge_run(monkeypatch, 2, 6, 10, "direct", 3)
    check_bridge_spreads_and_solvers(logs)
    assert logs["twiddles"]
    for args, _, (tw_re, tw_im) in logs["twiddles"]:
        t, qm = args[1], args[2]
        expect = [unit_root(k, t, qm) for k in range(max(1, t // 2))]
        assert (tw_re, tw_im) == ([c for c, _ in expect], [s for _, s in expect]), (t, qm)
    assert {args[1] for args, _, _ in logs["twiddles"]} == {8}


@pytest.mark.parametrize("middle", ["bluestein", "walsh"])
def test_bridge_phase_tables_as_consumed(monkeypatch, middle):
    """Bridge d = 2, K = 4 (t = (4, 4)), p = 10: the Bluestein chirp/twist table and the Walsh last-axis twiddle table
    (one 2r-entry disk table each, p_fft = q), plus that run's filters and solver tuples."""
    logs = _bridge_run(monkeypatch, 2, 4, 10, middle, 4)
    check_bridge_spreads_and_solvers(logs)
    P = logs["params"][0]
    tables = logs["blue" if middle == "bluestein" else "walsh"]
    assert tables
    for args, _, th in tables:
        r, pp = args[0], args[1]
        assert (r, pp) == (4, P + 2)
        assert list(th) == [disk_phase(k, r, pp) for k in range(2 * r)]
