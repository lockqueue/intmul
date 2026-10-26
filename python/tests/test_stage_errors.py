"""Stage-wise measured-vs-bound verification of the production pipelines (M1 2D FastDFT, M2 bridge),
with the mpmath model as the oracle for every intermediate quantity (tests/stage_checks.py).

Sources: MS thm:spread (spread-err), thm:twisted, lem:forward proof; r2 (4.20), §8; r3 (4.16), (4.21),
(5.4), §5.7; the error analysis.  The fast part covers small sizes; bigger cases are slow-marked.
"""

import random
from fractions import Fraction

import pytest
from mpmath import mp, mpc

import bridge_model as bm
import stage_checks as sc
from conftest import make_ctx
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.bridge.geometry import BridgeGeometry
from subnlogn.fastdft2d import fast_dft
from subnlogn.fixedpoint import FxVec
from subnlogn.schedule import test_schedule


def _assert_all_ok(results, expected_checks):
    assert results, "no stage results"
    names = {r.check for r in results}
    for c in expected_checks:
        assert any(n.startswith(c) for n in names), (c, names)
    bad = [(r.case, r.check, r.log2_ratio) for r in results if not r.ok]
    assert not bad, bad


M1_EXPECTED = ["(a) ", "(a') ", "(b1) ", "(b1') ", "(b2) ", "(b) ", "(b') ", "(c0) ", "(c1) ", "(c) ", "(d) ",
               "(e) ", "(e') "]
M2_EXPECTED = ["(a) ", "(a') ", "(m) ", "(b) ", "(c) stage h=2", "(c') stage h=2", "(d) ", "(e) ", "(e') "]


@pytest.mark.parametrize("kind", sc.KINDS)
@pytest.mark.parametrize("name,R,p", sc.M1_FAST)
def test_m1_stage_errors(name, R, p, kind, tables):
    """M1 at depth 0: (a) spread vs MS (spread-err) with complex taps, (b1) twisted reduction,
    (b2) child contract, (b) Steps 1-2 <= 9 r u A, (c0)/(c1)/(c) the three certificate terms
    (aliases, Steps 1-2 after deconvolution, solver r2 (4.20) with the true c0, c1), (d) the total."""
    res = sc.m1_checks(sc.m1_schedules()[name], R, p, kind, seed=R + p, tables=tables)
    _assert_all_ok(res, M1_EXPECTED)


@pytest.mark.parametrize("kind", sc.KINDS)
@pytest.mark.parametrize("d,K", sc.M2_FAST)
def test_m2_stage_errors(d, K, kind, tables):
    """M2 on x' = x/X: (a) spread <= 16 d (P+1) G eta (r3 (5.4)), (m) direct middle DFT, (b) aliases
    <= 0.120 (d-1) 2^-w (r3 (4.16)), (c) every deconvolution stage <= 32 t_h^2 2^-P max(1, |Y|)
    (r3 (4.21)) against the exact B_h^{-1} of the computed stage input, (d) total <= certificate."""
    res = sc.m2_checks(d, K, sc.m2_p(K), kind, seed=100 * d + K, tables=tables)
    _assert_all_ok(res, M2_EXPECTED + [f"(c) stage h={h}" for h in range(2, d + 1)])


@pytest.mark.parametrize("d,K", [(2, 4), (3, 4)])
def test_m2_stage_errors_r2_constants(d, K, tables):
    """The same stage checks under r2's constants (w = p + K + ceil(lg d) + 20, r2 (2.8)-(2.9))."""
    res = sc.m2_checks(d, K, sc.m2_p(K), "random_max", seed=7, tables=tables, constants="r2")
    _assert_all_ok(res, M2_EXPECTED)


@pytest.mark.slow
@pytest.mark.parametrize("kind", sc.KINDS)
@pytest.mark.parametrize("name,R,p", sc.M1_SLOW)
def test_m1_stage_errors_large(name, R, p, kind, tables):
    _assert_all_ok(sc.m1_checks(sc.m1_schedules()[name], R, p, kind, seed=R + p, tables=tables), M1_EXPECTED)


@pytest.mark.slow
@pytest.mark.parametrize("kind", sc.KINDS)
@pytest.mark.parametrize("d,K", sc.M2_SLOW)
def test_m2_stage_errors_large(d, K, kind, tables):
    _assert_all_ok(sc.m2_checks(d, K, sc.m2_p(K), kind, seed=100 * d + K, tables=tables), M2_EXPECTED)


# ------------------------------------------------------------------------------ oracle self-checks
@pytest.mark.parametrize("t1,r", [(2, 2), (2, 4), (4, 4), (4, 8)])
def test_twisted_reduction_identity(t1, r):
    """MS Thm 3.1 in exact arithmetic: the child DFTs of V° = twisted_reduction(U) routed by
    u1 = (2 u2 - 1) v1 mod t1 give F_{t1,r} U, so V° is the right reference for check (b1)."""
    with bm.precision():
        g = BridgeGeometry((t1, r))
        U = bm.random_vector(t1 * r, seed=t1 * r)
        V = sc.twisted_reduction([[U[j1 + t1 * k] for k in range(r)] for j1 in range(t1)], t1, r)
        Y = bm.tensor_dft(g, U)
        for v1 in range(t1):
            C = bm.dft(V[v1])
            for u2 in range(r):
                assert abs(C[u2] - Y[u2 + r * (((2 * u2 - 1) * v1) % t1)]) < mp.mpf(10) ** -60


def test_alias_error_matches_direct_difference():
    """The telescoping alias formula (sc.alias_error) equals the direct difference F_t U° - B..B F_R x
    wherever the latter is resolvable (here sqrt(pi) alpha = 8, so the aliases are ~1e-5..1e-17)."""
    with bm.precision():
        alpha = 8 / mp.sqrt(mp.pi)
        for t in [(2, 4), (4, 2, 2), (2, 2, 2, 2)]:
            g = BridgeGeometry(t)
            x = bm.random_vector(g.R, seed=g.R)
            Z = bm.dft(x)
            direct = [a - b for a, b in zip(bm.lemma_A_lhs(g, x, alpha), bm.apply_chain(
                [bm.alias_op(g, h, alpha, retain={0, 1}) for h in range(2, g.d + 1)], Z))]
            tele = sc.alias_error(g, Z, alpha)
            assert bm.max_abs_diff(direct, tele) < mp.mpf(10) ** -60
            assert bm.norm_inf(tele) > mp.mpf(10) ** -20


def test_checks_have_teeth(tables):
    """A wrong reference violates the bounds by far: U° with the positive carrier (check (a)), and the
    solver stage compared against the inverse of the wrong axis (check (c))."""
    lv_case = sc.m1_checks(sc.m1_schedules()["bt2"], 16, 10, "random_max", seed=1, tables=tables)
    assert all(r.ok for r in lv_case)
    sched = test_schedule(base_threshold=2)
    R, p = 16, 10
    re, im = sc.make_input("random_max", R, p, random.Random(1))
    ctx = make_ctx(sched, capture=True)
    fast_dft(ctx, FxVec(re, im, p + 2), R, p)
    lv = ctx.capture["level"]
    g = BridgeGeometry((lv.t1, lv.r))
    with mp.workprec(200):
        x = sc.mpc_list(re, im, p + 2)
        alpha = bm.alpha_from_w(lv.p_work)
        Ur, Ui = ctx.capture["U_rows"]
        Uh = [None] * R
        for j1 in range(lv.t1):
            for k2 in range(lv.r):
                Uh[j1 + lv.t1 * k2] = mpc(mp.ldexp(Ur[j1][k2], -lv.q_child), mp.ldexp(Ui[j1][k2], -lv.q_child))
        wrong = bm.spread(g, x, alpha, +1, sc.model_radius(alpha, 200))
        bound = (Fraction(lv.W_tilde, 4) + Fraction(1, 10) + Fraction(1, 5)) * 2 ** p / Fraction(1 << lv.p_child)
        assert bm.max_abs_diff(Uh, wrong) > 1000 * bm.to_mpf(bound)
    d, K = 3, 4
    ctx = make_ctx(test_schedule(bridge_d=d), capture=True)
    re, im = sc.make_input("random_max", 1 << K, 10, random.Random(2))
    bridge_dft(ctx, FxVec(re, im, 12), 1 << K, 10, d)
    P, w, m, geom = ctx.capture["bridge_params"]
    with mp.workprec(P + 64):
        alpha = bm.alpha_from_w(w)
        ym = ctx.capture["bridge_Ymid"]
        Ym = sc.mpc_list(ym.re, ym.im, P + 2)
        y2 = ctx.capture["bridge_Ydeconv"][2]
        Y2 = sc.mpc_list(y2.re, y2.im, P + 2)
        good = bm.max_abs_diff(Y2, bm.deconvolve_axis(geom, 2, alpha, Ym))
        bad = bm.max_abs_diff(Y2, bm.deconvolve_axis(geom, 3, alpha, Ym))
        lim = 32 * geom.tt(2) ** 2 * mp.ldexp(1, -P) * 2
        assert good <= lim < bad


# ------------------------------------------------------------------------------ capture plumbing
@pytest.mark.parametrize("R,p", [(16, 10), (64, 12)])
def test_capture_does_not_change_fastdft(R, p, tables):
    """Capturing is passive: identical outputs with capture None and enabled; Zcomp rounds to the
    output, and V-hat / Y-hat are related by the routing of the child outputs."""
    sched = test_schedule(base_threshold=2)
    re, im = sc.make_input("random_max", R, p, random.Random(R))
    a = fast_dft(make_ctx(sched), FxVec(re, im, p + 2), R, p)
    ctx = make_ctx(sched, capture=True)
    b = fast_dft(ctx, FxVec(re, im, p + 2), R, p)
    assert (a.re, a.im) == (b.re, b.im)
    cap = ctx.capture
    lv = cap["level"]
    assert set(cap) >= {"U_rows", "V_rows", "Y_cols", "Zcomp", "level"}
    assert len(cap["U_rows"][0]) == lv.t1 and len(cap["U_rows"][0][0]) == lv.r
    assert len(cap["Y_cols"][0]) == lv.r and len(cap["Y_cols"][0][0]) == lv.t1
    up = lv.q_child - (p + 2)
    zc = cap["Zcomp"]
    assert [ctx.shr(v, up) for v in zc.re] == b.re and [ctx.shr(v, up) for v in zc.im] == b.im
    v1 = 1 % lv.t1
    child = fast_dft(make_ctx(sched), FxVec(cap["V_rows"][0][v1], cap["V_rows"][1][v1], lv.q_child),
                     lv.r, lv.p_child, depth=1)
    for u2 in range(lv.r):
        u1 = ((2 * u2 - 1) * v1) % lv.t1
        assert cap["Y_cols"][0][u2][u1] == child.re[u2] and cap["Y_cols"][1][u2][u1] == child.im[u2]


@pytest.mark.parametrize("d,K", [(2, 4), (4, 5)])
def test_capture_does_not_change_bridge(d, K, tables):
    sched = test_schedule(bridge_d=d)
    R, p = 1 << K, max(8, K) + 2
    re, im = sc.make_input("random_max", R, p, random.Random(K))
    a = bridge_dft(make_ctx(sched), FxVec(re, im, p + 2), R, p, d)
    ctx = make_ctx(sched, capture=True)
    b = bridge_dft(ctx, FxVec(re, im, p + 2), R, p, d)
    assert (a.re, a.im) == (b.re, b.im)
    cap = ctx.capture
    assert set(cap) >= {"bridge_U", "bridge_Ymid", "bridge_Ydeconv", "bridge_Znorm", "bridge_e", "bridge_params"}
    assert sorted(cap["bridge_Ydeconv"]) == list(range(2, d + 1))
    assert cap["bridge_Ydeconv"][d] is cap["bridge_Znorm"]
