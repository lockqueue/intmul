"""SPEC_WALSH §8 W-T6 (last-axis FFT), W-T7 (combined twiddle), W-T8 (bit-exact vs a slow named-slot
oracle), W-T9 (exact mode = exact DFT over Z[i,1/2]), W-T10 (three-way cross-check with logged errors)."""

from fractions import Fraction
from math import prod

import pytest
from mpmath import mp, mpc, mpf

import path_model as PM
from conftest import make_ctx
from subnlogn.bridge.geometry import BridgeGeometry
from subnlogn.bridge.middle import MIDDLE_BACKENDS, direct_middle_dft
from subnlogn.certified import phase_table
from subnlogn.fixedpoint import FxVec, shr_trunc
from subnlogn.m6.policy import LAYER_TEST
from subnlogn.middle3.bluestein import bluestein_middle_dft
from subnlogn.schedule import test_schedule
from subnlogn.walsh.fft import last_axis_fft, tensor_fft_walsh, twiddle_index, walsh_middle_dft
from subnlogn.walsh.gadget import WalshCtx
from subnlogn.walsh.positional import compile_layout, inverse
from walsh_helpers import RNG, engine, fresh_inst, rand_disk, to_frac

# ----------------------------------------------------------------------------------------------
# exact / high-precision references
# ----------------------------------------------------------------------------------------------


def exact_dft_fourth_roots(vals, t):
    """Exact normalized positive tensor DFT over Z[i,1/2] for t_i in {1, 2, 4} (tensor order)."""
    strides, s = [], 1
    for ti in reversed(t):
        strides.append(s)
        s *= ti
    strides.reverse()
    R = s
    dig = [[(idx // st) % ti for st, ti in zip(strides, t)] for idx in range(R)]
    out = []
    for j in range(R):
        ar = ai = Fraction(0)
        for k in range(R):
            e = sum((4 // ti) * a * b for a, b, ti in zip(dig[j], dig[k], t)) % 4
            vr, vi = vals[k]
            for _ in range(e):
                vr, vi = -vi, vr
            ar += vr
            ai += vi
        out.append((ar / R, ai / R))
    return out


def mp_tensor_dft(vals, t, prec):
    """Separable high-precision positive tensor DFT (tensor order), vals: list of (Fraction, Fraction)."""
    with mp.workprec(prec):
        cur = [mpc(mpf(a.numerator) / a.denominator, mpf(b.numerator) / b.denominator) for a, b in vals]
        strides, s = [], 1
        for ti in reversed(t):
            strides.append(s)
            s *= ti
        strides.reverse()
        for ti, st in zip(t, strides):
            w = [mp.expjpi(mpf(2 * k) / ti) for k in range(ti)]
            nxt = list(cur)
            for base in range(len(cur)):
                if (base // st) % ti:
                    continue
                line = [cur[base + c * st] for c in range(ti)]
                for jj in range(ti):
                    nxt[base + jj * st] = sum(line[c] * w[(jj * c) % ti] for c in range(ti)) / ti
            cur = nxt
        return cur


def recs_to_vals(recs, scale):
    return [v for rec in to_frac(recs, scale) for v in rec]


# ----------------------------------------------------------------------------------------------
# W-T6
# ----------------------------------------------------------------------------------------------


@pytest.mark.parametrize("r", [2, 4, 8, 16, 32])
def test_last_axis_fft(r):
    p, ell = 24, r.bit_length() - 1
    th = phase_table(r, p)
    rng = RNG(r)
    for _ in range(3):
        rec = rand_disk(0, r, p, rng, frac=3)[0]
        vals = list(zip((Fraction(a, 1 << p) for a in rec[0]), (Fraction(b, 1 << p) for b in rec[1])))
        if r <= 4:                                                    # exact mode: literally the DFT
            ex = last_axis_fft(rec[0], rec[1], p, th, truncate=False)
            assert to_frac([ex], p + ell)[0] == exact_dft_fourth_roots(vals, (r,))
        got = last_axis_fft(rec[0], rec[1], p, th)
        ref = mp_tensor_dft(vals, (r,), p + 80)
        with mp.workprec(p + 80):
            err = max(abs(mpc(mpf(a) / 2 ** p, mpf(b) / 2 ** p) - z) for a, b, z in zip(got[0], got[1], ref))
            assert err < 6 * ell * mpf(2) ** -p


# ----------------------------------------------------------------------------------------------
# W-T7
# ----------------------------------------------------------------------------------------------


@pytest.mark.parametrize("t,h", [((4, 4, 4, 4), 1), ((16, 8, 16), 2), ((32, 16, 32), 2)])
def test_combined_twiddle_index(t, h):
    r = t[-1]
    ell = r.bit_length() - 1
    widths = [x.bit_length() - 1 for x in t[:-1]]
    m0 = sum(widths)
    L, B, U, new, b, q = compile_layout(widths, ell, h)
    ebit = {s: m0 - 1 - pos for s, pos in new.items()}
    orig = {}
    k = 0
    for i, a in enumerate(widths):
        for v in range(a - 1, -1, -1):
            orig[(i, v)] = m0 - 1 - k
            k += 1
    Li = inverse(L)
    th = phase_table(r, 30)
    one = 1 << 30
    hits = 0
    for h0 in range(ell - 1, -1, -1):
        axes = [i for i, a in enumerate(widths) if h0 < a]
        for addr in range(1 << m0):
            x = 0                                                   # original address of the record now at addr
            for pos in range(m0):
                x |= ((addr >> (m0 - 1 - pos)) & 1) << (m0 - 1 - Li[pos])
            direct = 0
            for i in axes:
                bi = (x >> orig[(i, h0)]) & 1
                ki = sum(((x >> orig[(i, v)]) & 1) << v for v in range(h0))
                direct += (2 * r // (1 << (h0 + 1))) * bi * ki
            idx = twiddle_index(addr, h0, axes, ell, ebit)
            assert idx == direct % (2 * r)
            if idx % (r // 2) == 0:
                hits += 1
                assert th[idx] in ((one, 0), (0, one), (-one, 0), (0, -one))
    assert hits > 0


# ----------------------------------------------------------------------------------------------
# W-T8: bit-exact against a slow named-slot oracle (no L, dense H per round, same table and Q_p)
# ----------------------------------------------------------------------------------------------


def oracle_walsh(recs, t, p):
    r = t[-1]
    ell = r.bit_length() - 1
    widths = [x.bit_length() - 1 for x in t[:-1]]
    m0 = sum(widths)
    th = phase_table(r, p)
    out = []
    for re, im in recs:                                            # last axis, same protocol
        ar, ai = list(re), list(im)
        for v in range(ell - 1, -1, -1):
            u = 1 << (v + 1)
            for base in range(0, r, u):
                for k in range(u // 2):
                    i0, i1 = base + k, base + k + u // 2
                    sr, si = shr_trunc(ar[i0] + ar[i1], 1), shr_trunc(ai[i0] + ai[i1], 1)
                    dr, di = shr_trunc(ar[i0] - ar[i1], 1), shr_trunc(ai[i0] - ai[i1], 1)
                    tr, ti = th[(2 * r // u) * k % (2 * r)]
                    ar[i0], ai[i0] = sr, si
                    ar[i1], ai[i1] = shr_trunc(dr * tr - di * ti, p), shr_trunc(dr * ti + di * tr, p)
        rev = [int(format(j, f"0{ell}b")[::-1], 2) for j in range(r)]
        out.append(([ar[rev[j]] for j in range(r)], [ai[rev[j]] for j in range(r)]))
    orig, k = {}, 0
    for i, a in enumerate(widths):
        for v in range(a - 1, -1, -1):
            orig[(i, v)] = m0 - 1 - k
            k += 1
    for h0 in range(ell - 1, -1, -1):                              # record axes on the original slots
        axes = [i for i, a in enumerate(widths) if h0 < a]
        if not axes:
            continue
        for i in axes:
            mb = 1 << orig[(i, h0)]
            for x in range(len(out)):
                if not x & mb:
                    (a_r, a_i), (b_r, b_i) = out[x], out[x | mb]
                    out[x] = ([u + v for u, v in zip(a_r, b_r)], [u + v for u, v in zip(a_i, b_i)])
                    out[x | mb] = ([u - v for u, v in zip(a_r, b_r)], [u - v for u, v in zip(a_i, b_i)])
        s = len(axes)
        out = [([shr_trunc(v, s) for v in re], [shr_trunc(v, s) for v in im]) for re, im in out]
        nxt = []
        for x, (re, im) in enumerate(out):
            idx = 0
            for i in axes:
                if (x >> orig[(i, h0)]) & 1:
                    idx += (2 * r >> (h0 + 1)) * sum(((x >> orig[(i, v)]) & 1) << v for v in range(h0))
            tr, ti = th[idx % (2 * r)]
            nxt.append(([shr_trunc(a * tr - b * ti, p) for a, b in zip(re, im)],
                        [shr_trunc(a * ti + b * tr, p) for a, b in zip(re, im)]))
        out = nxt
    fin = [None] * len(out)                                        # direct per-axis bit reversal
    for x, rec in enumerate(out):
        y = 0
        for (i, v), eb in orig.items():
            y |= ((x >> eb) & 1) << orig[(i, widths[i] - 1 - v)]
        fin[y] = rec
    return fin


@pytest.mark.parametrize("t,h,kind", [((2, 2, 2, 4), 1, "base"), ((4, 4, 4, 4), 1, "base"),
                                      ((4, 4, 4, 4), 1, "network"), ((16, 8, 16), 2, "base"),
                                      pytest.param((32, 16, 32), 2, "base", marks=pytest.mark.slow),
                                      pytest.param((2,) * 9 + (4,), 1, "network", marks=pytest.mark.slow)])
def test_walsh_middle_bit_exact(t, h, kind):
    r, p = t[-1], 20
    m0 = sum(x.bit_length() - 1 for x in t[:-1])
    recs = rand_disk(m0, r, p, RNG(m0 + r), frac=8)
    inst = fresh_inst()
    w = WalshCtx(d=len(t), h=h, engine=engine(kind, len(t), inst=inst), inst=inst)
    out, scale = tensor_fft_walsh(recs, t, p, w)
    assert scale == p and out == oracle_walsh(recs, t, p)
    exp = walsh_exact(inst, t, h, kind)
    assert exp["walsh.chunk_round"] > 0 and exp["walsh.positional_map"] == 2
    assert (exp["m6.layer.network"] > 0) == (kind == "network")


def walsh_exact(inst, t, h, kind):
    """Exact counts of one tensor_fft_walsh (exact count; path_model): positional maps, CNOT batches, leftover
    CNOTs, chunk and prefix rounds, and every Prop 14 layer through the engine of ``kind`` (the unit tests'
    network engine is CCtx with the address-permutation oracle for P_M, SPEC §4.3)."""
    eng = PM.Eng(PM.nets()["C1"], len(t), LAYER_TEST, h, row_add="direct") if kind == "network" else None
    exp = PM.walsh_middle(t, h, eng)
    del exp["bridge.middle"]
    keys = [k for k in PM.PATH_KEYS if k.startswith(("walsh.", "m6.", "lemma13."))]
    PM.assert_exact(inst.counts, exp, keys)
    return exp


# ----------------------------------------------------------------------------------------------
# W-T9: exact mode
# ----------------------------------------------------------------------------------------------


@pytest.mark.parametrize("t", [(4, 4), (2, 2, 2, 4), (4, 4, 4, 4)])
@pytest.mark.parametrize("kind", ["base", "network"])
def test_walsh_exact_mode_is_the_exact_dft(t, kind):
    r, p = t[-1], 14
    m0 = sum(x.bit_length() - 1 for x in t[:-1])
    recs = rand_disk(m0, r, p, RNG(len(t)), frac=8)
    inst = fresh_inst()
    w = WalshCtx(d=len(t), h=1, engine=engine(kind, len(t), inst=inst), inst=inst)
    out, scale = tensor_fft_walsh(recs, t, p, w, truncate=False)
    assert recs_to_vals(out, scale) == exact_dft_fourth_roots(recs_to_vals(recs, p), t)
    exp = walsh_exact(inst, t, 1, kind)
    assert (exp["m6.layer.network"] > 0) == (kind == "network")
    assert exp["walsh.chunk_round"] + exp["walsh.prefix_round"] > 0      # rounds without axes are skipped


# ----------------------------------------------------------------------------------------------
# W-T10: three-way cross-check (Walsh, Bluestein, direct) against the exact DFT, errors logged
# ----------------------------------------------------------------------------------------------


def storage_input(geom, q, kind, rng):
    R = geom.R
    lim = (1 << q) // 12                                             # ||x|| <= 1/8 (componentwise / 12)
    if kind == "random":
        re = [rng.randint(-lim, lim) for _ in range(R)]
        im = [rng.randint(-lim, lim) for _ in range(R)]
    elif kind == "impulse":
        re, im = [0] * R, [0] * R
        re[rng.randrange(R)] = lim
    else:
        re, im = [lim] * R, [-lim // 2] * R
    return FxVec(re, im, q)


def storage_reference(geom, U, prec):
    """Exact DFT in the storage layout via the tensor-order reference."""
    t = tuple(geom.t)
    strides, s = [], 1
    for ti in reversed(t):
        strides.append(s)
        s *= ti
    strides.reverse()
    to_tensor = [sum(c * st for c, st in zip(geom.digits(j), strides)) for j in range(geom.R)]
    vals = [None] * geom.R
    for j, tj in enumerate(to_tensor):
        vals[tj] = (Fraction(U.re[j], 1 << U.q), Fraction(U.im[j], 1 << U.q))
    ref = mp_tensor_dft(vals, t, prec)
    return [ref[to_tensor[j]] for j in range(geom.R)]


@pytest.mark.parametrize("t,h", [((2, 2, 2, 4), 1), ((4, 4, 4, 4), 1), ((16, 8, 16), 2)])
@pytest.mark.parametrize("inp", ["random", "impulse", "constant"])
def test_three_way_cross_check(t, h, inp, record_property):
    geom = BridgeGeometry(t)
    d, R, r = geom.d, geom.R, t[-1]
    ell, M = r.bit_length() - 1, geom.R // r
    P = 40
    q = P + 2
    ctx = make_ctx(test_schedule(bridge_d=d).with_(chunk_bits=h))
    U = storage_input(geom, q, inp, RNG(R))
    ref = storage_reference(geom, U, q + 80)
    outs = {"walsh": walsh_middle_dft(ctx, U, geom, P), "bluestein": bluestein_middle_dft(ctx, U, geom, P),
            "direct": direct_middle_dft(ctx, U, geom, P)}
    with mp.workprec(q + 80):
        u = mpf(2) ** -q
        qm = P + geom.K + ctx.schedule.bridge_mid_guard
        bounds = {"walsh": 12 * ell * u, "bluestein": (mp.sqrt(2) * M * (3 * ell + 1) + 22) * u,
                  "direct": 2.16 * geom.K * mpf(2) ** -qm + mp.sqrt(2) / 2 * u}
        errs = {}
        for name, Y in outs.items():
            errs[name] = max(abs(mpc(mpf(a) / 2 ** q, mpf(b) / 2 ** q) - z) for a, b, z in zip(Y.re, Y.im, ref))
            assert errs[name] < bounds[name], (name, errs[name] / u, bounds[name] / u)
            record_property(f"{name}_err_ulps", float(errs[name] / u))
            record_property(f"{name}_bound_ulps", float(bounds[name] / u))
        for a in outs:
            for b in outs:
                dmax = max(abs(mpc(x1 - x2, y1 - y2)) for x1, y1, x2, y2 in
                           zip(outs[a].re, outs[a].im, outs[b].re, outs[b].im)) * u
                assert dmax <= bounds[a] + bounds[b]
        print(f"W-T10 t={t} input={inp}: walsh {float(errs['walsh'] / u):.3f} ulp (bound 12*ell = {12 * ell}), "
              f"bluestein {float(errs['bluestein'] / u):.3f} (bound {float(bounds['bluestein'] / u):.1f}), "
              f"direct {float(errs['direct'] / u):.3f} (bound {float(bounds['direct'] / u):.3f})")
    assert "walsh" in MIDDLE_BACKENDS
