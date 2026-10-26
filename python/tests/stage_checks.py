"""Stage-wise measured-vs-bound checks of the production pipelines -- TESTS ONLY, non-authoritative.

M1 = subnlogn.fastdft2d.fast_dft at depth 0 (2D FastDFT, negative half-bin drop-in);
M2 = subnlogn.bridge.bridge_dft (d-dimensional bridge, direct middle tensor DFT).

The production call runs once with ``ctx.capture`` enabled (capture keys: see the module docstrings of
fastdft2d and bridge_dft).  Every exact intermediate quantity is recomputed independently with the
mpmath model (tests/bridge_model.py) at about 64 bits beyond the working precision (relative to the
data scale), with the kernel truncated only where its tail is below 2^-(prec): U° (untruncated folded
modulated kernel), F_{t1,r} U°, the exact twisted reduction V°, F_r V-hat, F_t U-hat, the exact inverses
B_h^{-1} with the TRUE c0, c1, and F_R x.  Each check is a :class:`StageResult` (measured, bound).

Sources: MS = the companion manuscript [MS] (thm:spread eq. (spread-err), thm:twisted,
lem:forward and its proof); r2 = bridge derivation r2 ((4.20), §8); r3 = bridge derivation r3
((4.16), (4.21), (5.4), §5.7); the error analysis (certificates; M2.2 direct middle bound).
"""

from __future__ import annotations

import math
import random
from dataclasses import dataclass
from fractions import Fraction

from mpmath import mp, mpc, mpf

import bridge_model as bm
from oracle import sqrt_upper
from subnlogn.bridge.bridge_dft import bridge_certificate, bridge_dft
from subnlogn.bridge.geometry import BridgeGeometry
from subnlogn.context import Ctx
from subnlogn.fastdft2d import certificate_2d, fast_dft
from subnlogn.fixedpoint import FxVec
from subnlogn.schedule import faithful_schedule, test_schedule

SQRT2_8_UP = Fraction(17678, 100000)          # > sqrt(2)/8
SQRT2_UP = Fraction(99, 70)                   # > sqrt(2)


@dataclass
class StageResult:
    pipeline: str          # "M1" or "M2"
    case: str
    check: str
    measured: mpf
    bound: mpf
    source: str
    note: str = ""

    @property
    def ok(self) -> bool:
        return self.measured <= self.bound

    @property
    def log2_ratio(self) -> float:
        """log2(measured / bound), display only (-inf for an exact zero)."""
        if self.measured == 0:
            return float("-inf")
        return float(mp.log(self.measured, 2) - mp.log(self.bound, 2))


# ----------------------------------------------------------------------------------- helpers
def make_input(kind: str, R: int, p: int, rng: random.Random) -> tuple[list[int], list[int]]:
    """Numerators on C~_{p+2} with ||x|| <= 2^p (the FastDFT / bridge precondition)."""
    q = p + 2
    big = (1 << (q + p)) * 7 // 10
    if kind == "random_max":
        return [rng.randint(-big, big) for _ in range(R)], [rng.randint(-big, big) for _ in range(R)]
    if kind == "random_small":                       # ||x|| < 1, so A = 1 dominates
        s = 1 << (q - 1)
        return [rng.randint(-s, s) for _ in range(R)], [rng.randint(-s, s) for _ in range(R)]
    if kind == "impulse":
        re = [0] * R
        re[rng.randrange(R)] = big
        return re, [0] * R
    if kind == "alternating":
        return [big * (-1) ** j for j in range(R)], [big * (-1) ** (j // 2) for j in range(R)]
    raise ValueError(kind)


def mpc_list(re, im, q: int) -> list:
    """Exact conversion of numerators at scale q to mpc (exact when prec >= their bit length)."""
    return [mpc(mp.ldexp(a, -q), mp.ldexp(b, -q)) for a, b in zip(re, im)]


def fr(v) -> mpf:
    return bm.to_mpf(v) if isinstance(v, (Fraction, int)) else v


def rounding_note(rounding: Fraction, bound: Fraction, name: str) -> str:
    """Share of a bound taken by its final-rounding term.  A nearest rounding to a grid attains its worst
    case sqrt(2)/2 ulp exactly when both coordinates of some entry sit at a tie, so such a bound is sharp."""
    return (f"the final-rounding term {name} is {float(rounding / bound):.6f} of the bound; it is attained "
            "when both coordinates of an entry are at an exact rounding tie (|err| = sqrt(2)/2 ulp)")


def model_radius(alpha, bits: int) -> int:
    """Smallest spatial radius M with total omitted kernel mass folded_tail_bound(1, alpha, M) <= 2^-bits."""
    M = max(8, int(mp.ceil(alpha * mp.sqrt(bits * mp.ln2 / mp.pi))))
    while bm.folded_tail_bound(1, alpha, M) > mp.ldexp(1, -bits):
        M += 1
    return M


def twisted_reduction(U_rows: list, t1: int, r: int) -> list:
    """Exact V°[v1][k] = conj(zeta^k) Q°_{v1,k}, Q°_{v1}(y) = (1/t1) sum_{j1} y^{2 nu j1 v1} P°_{j1}(y)
    mod (y^r + 1), P°_{j1,k} = zeta^k U°_{j1,k}, zeta = e^{pi i/r}, nu = r/t1 (MS Thm 3.1 steps 1-3,
    eq. (syn-fft)); the signed shift uses y^r = -1 directly (independent of subnlogn.synthetic)."""
    nu = r // t1
    zeta = [mp.expjpi(bm.to_mpf(Fraction(k, r))) for k in range(r)]
    P = [[zeta[k] * U_rows[j1][k] for k in range(r)] for j1 in range(t1)]
    V = []
    for v1 in range(t1):
        Qv = [mpc(0)] * r
        for j1 in range(t1):
            delta = 2 * nu * j1 * v1
            for j in range(r):
                e = j + delta
                Qv[e % r] += P[j1][j] if (e // r) % 2 == 0 else -P[j1][j]
        V.append([mp.conj(zeta[k]) * Qv[k] / t1 for k in range(r)])
    return V


def alias_error(geom: BridgeGeometry, Z: list, alpha) -> list:
    """(A_2...A_d - B_2...B_d) Z by the telescoping identity sum_h B_2..B_{h-1} (A_h - B_h) A_{h+1}..A_d Z
    (r3 (4.16) proof).  Only the small tail coefficients enter A_h - B_h, so the result is accurate
    relative to its own size (a direct difference F_t U° - B...Z would sit at the 2^-prec noise floor)."""
    hs = list(range(2, geom.d + 1))
    A = {h: bm.alias_op(geom, h, alpha) for h in hs}
    B = {h: bm.alias_op(geom, h, alpha, retain={0, 1}) for h in hs}
    T = {h: bm.alias_op(geom, h, alpha, retain=set(range(-6, 7)) - {0, 1}) for h in hs}
    total = [mpc(0)] * geom.R
    for h in hs:
        term = bm.apply_chain([B[i] for i in hs if i < h] + [T[h]] + [A[i] for i in hs if i > h], Z)
        total = [a + b for a, b in zip(total, term)]
    return total


# ----------------------------------------------------------------------------------- M1
def m1_checks(sched, R: int, p: int, kind: str = "random_max", seed: int = 0,
              tables: dict | None = None) -> list[StageResult]:
    """Depth-0 stage checks of fast_dft (2D, negative carrier); see the module docstring."""
    rng = random.Random(seed)
    re, im = make_input(kind, R, p, rng)
    xf = FxVec(re, im, p + 2)
    ctx = Ctx(schedule=sched, tables={} if tables is None else tables, capture={})
    zout = fast_dft(ctx, xf, R, p)
    cap = ctx.capture
    if "level" not in cap:
        raise ValueError("the depth-0 node is a leaf: no stages to check")
    lv = cap["level"]
    t1, r, P, w, q = lv.t1, lv.r, lv.p_child, lv.p_work, lv.q_child
    geom = BridgeGeometry((t1, r))
    nx = sqrt_upper(xf.sup_norm_sq())                 # rational upper bound for ||x||
    A = max(Fraction(1), nx)
    u = Fraction(1, 1 << P)
    cert = certificate_2d(lv, A)
    bt = sched.base_threshold
    case = f"{sched.name}{'' if bt is None else f' bt={bt}'} R={R} p={p} {kind}"
    out = []

    def add(check, measured, bound, source, note=""):
        out.append(StageResult("M1", case, check, measured, fr(bound), source, note))

    with mp.workprec(max(160, P + p + 64)):
        x = mpc_list(re, im, p + 2)
        alpha = bm.alpha_from_w(w)
        U0 = bm.spread(geom, x, alpha, -1, model_radius(alpha, P + p + 64))      # storage j1 + t1 k2
        Ur, Ui = cap["U_rows"]
        Uh = [None] * R
        for j1 in range(t1):
            for k2 in range(r):
                Uh[j1 + t1 * k2] = mpc(mp.ldexp(Ur[j1][k2], -q), mp.ldexp(Ui[j1][k2], -q))
        ea = bm.max_abs_diff(Uh, U0)
        add("(a) spread |U^ - U°|", ea, (Fraction(lv.W_tilde, 4) + Fraction(1, 10)) * u * nx + SQRT2_8_UP * u,
            "MS (spread-err), complex taps 2^-P/4 (r2 §8)")
        add("(a') spread, coarse", ea, 2 * r * u * A, "MS (spread-err) 2 r 2^-P A")
        # (b1) twisted reduction U -> V, (b2) children, (b) routed Y-hat vs Y° = F_{t1,r} U°
        V0 = twisted_reduction([[U0[j1 + t1 * k2] for k2 in range(r)] for j1 in range(t1)], t1, r)
        Vr, Vi = cap["V_rows"]
        Vh = [mpc_list(Vr[v1], Vi[v1], q) for v1 in range(t1)]
        add("(b1) twisted reduction |V^ - V°|", max(bm.max_abs_diff(a, b) for a, b in zip(Vh, V0)),
            Fraction(7, 2) * r * u * A, "MS lem:forward proof, Step 2c (budgeted as 7 r u A)")
        add("(b1') child inputs |V^|", max(bm.norm_inf(v) for v in Vh), 2 * r * A,
            "MS lem:forward proof: child precondition |V^| <= 2 r A")
        Cr, Ci = cap["Y_cols"]
        Yh = [None] * R                                                            # frequency u2 + r u1
        for u2 in range(r):
            for u1 in range(t1):
                Yh[u2 + r * u1] = mpc(mp.ldexp(Cr[u2][u1], -q), mp.ldexp(Ci[u2][u1], -q))
        worst = None
        for v1 in range(t1):
            C = [Yh[u2 + r * (((2 * u2 - 1) * v1) % t1)] for u2 in range(r)]
            e = bm.max_abs_diff(C, bm.dft(Vh[v1]))
            b = fr(u) * max(mpf(1), bm.norm_inf(Vh[v1]))
            if worst is None or e / b > worst[0] / worst[1]:
                worst = (e, b)
        add("(b2) child contract |C^ - F_r V^| (worst v1)", worst[0], worst[1],
            "MS (inductive-bound) at depth 1: 2^-p_child max(1, |V^|)")
        Y0 = bm.tensor_dft(geom, U0)
        add("(b) Steps 1-2 |Y^ - F_{t1,r} U°|", bm.max_abs_diff(Yh, Y0), 9 * r * u * A,
            "MS lem:forward proof: 9 r u A")
        MY = max(mpf(1), bm.norm_inf(Yh))
        add("(b') M_Y = max(1, |Y^|)", MY, 2 * A, "MS lem:forward proof: M_Y <= 2A")
        # Step 3: Z = F_R x, Z* = B^-1 Y°, Z† = B^-1 Y^ (true c0, c1), Z^comp
        Z = bm.dft(x)
        Zstar_minus_Z = bm.deconvolve_axis(geom, 2, alpha, alias_error(geom, Z, alpha))
        add("(c0) aliases |Z* - Z|", bm.norm_inf(Zstar_minus_Z), cert.alias,
            "cert: 0.120 r 2^-w A (Thm 5.1(1), r2 §8)")
        Zstar = [a + b for a, b in zip(Z, Zstar_minus_Z)]
        Zdag = bm.deconvolve_axis(geom, 2, alpha, Yh)
        add("(c1) Steps 1-2 after deconv |Z† - Z*|", bm.max_abs_diff(Zdag, Zstar), cert.steps12,
            "cert: 9 r^2 u A (MS lem:forward, r2 §8)")
        zc = cap["Zcomp"]
        Zc = mpc_list(zc.re, zc.im, zc.q)
        add("(c) solver |Z^comp - B^-1 Y^|", bm.max_abs_diff(Zc, Zdag), fr(32 * r * r * u) * MY,
            "r2 (4.20): 32 r^2 2^-P M_Y")
        add("(d) total pre-rounding |Z^comp - F_R x|", bm.max_abs_diff(Zc, Z), cert.pre_rounding,
            "certificate_2d pre-rounding")
        ef = bm.max_abs_diff(mpc_list(zout.re, zout.im, p + 2), Z)
        add("(e) final output |Z^ - F_R x|", ef, cert.total, "certificate_2d total = pre + sqrt2/8 2^-p",
            rounding_note(cert.final_rounding, cert.total, "sqrt2/8 2^-p"))
        add("(e') final output vs contract", ef, cert.contract, "MS (inductive-bound): 2^-p A")
    return out


# ----------------------------------------------------------------------------------- M2
def m2_checks(d: int, K: int, p: int, kind: str = "random_max", seed: int = 0,
              tables: dict | None = None, constants: str = "r3") -> list[StageResult]:
    """Stage checks of bridge_dft on the normalized input x' = x/X; see the module docstring."""
    R = 1 << K
    rng = random.Random(seed)
    re, im = make_input(kind, R, p, rng)
    xf = FxVec(re, im, p + 2)
    sched = test_schedule(bridge_d=d).with_(bridge_constants=constants)
    ctx = Ctx(schedule=sched, tables={} if tables is None else tables, capture={})
    zout = bridge_dft(ctx, xf, R, p, d)
    cap = ctx.capture
    P, w, m, geom = cap["bridge_params"]
    e = cap["bridge_e"]
    q = P + 2
    A = max(Fraction(1), sqrt_upper(xf.sup_norm_sq()))
    cert = bridge_certificate(geom, p, P, w, 1 << e, A, sched.bridge_mid_guard)
    Q = R // geom.tt(1)
    kq = Q.bit_length() - 1
    G = Fraction(1 << (kq // 2)) * (SQRT2_UP if kq % 2 else 1)     # >= sqrt(Q), as in the certificate
    eta = Fraction(1, 1 << P)
    case = f"d={d} t={geom.t} p={p} P={P} {kind}"
    out = []

    def add(check, measured, bound, source, note=""):
        out.append(StageResult("M2", case, check, measured, fr(bound), source, note))

    with mp.workprec(max(160, P + K + 64)):
        xn = mpc_list(re, im, p + 2 + e)                                  # x' = x / 2^e
        alpha = bm.alpha_from_w(w)
        U0 = bm.spread(geom, xn, alpha, -1, model_radius(alpha, P + K + 64))
        bu = cap["bridge_U"]
        Uh = mpc_list(bu.re, bu.im, q)
        add("(a) spread |U^ - U°|", bm.max_abs_diff(Uh, U0), cert.spread, "r3 (5.4): 16 d (P+1) G eta")
        add("(a') |U^| <= 2G", bm.norm_inf(Uh), 2 * G, "r3 (5.4)")
        ym = cap["bridge_Ymid"]
        Ym = mpc_list(ym.re, ym.im, q)
        add("(m) middle |Y^mid - F_t U^|", bm.max_abs_diff(Ym, bm.tensor_dft(geom, Uh)), cert.middle,
            "ERROR_ANALYSIS M2.2: 2.16 K 2^-qm max(1,2G) + sqrt2/2 2^-q",
            rounding_note(Fraction(70711, 100000) / (1 << q), cert.middle, "sqrt2/2 2^-q"))
        Z = bm.dft(xn)
        add("(b) aliases |F_t U° - B_2..B_d F_R x'|", bm.norm_inf(alias_error(geom, Z, alpha)), cert.alias,
            "r3 (4.16): 0.120 (d-1) 2^-w")
        Yin = Ym
        for h in range(2, geom.d + 1):
            yo = cap["bridge_Ydeconv"][h]
            Yout = mpc_list(yo.re, yo.im, q)
            exact = bm.deconvolve_axis(geom, h, alpha, Yin)
            nin = bm.norm_inf(Yin)
            add(f"(c) stage h={h} solver |Y_h - B_h^-1 Y_(h-1)|", bm.max_abs_diff(Yout, exact),
                32 * geom.tt(h) ** 2 * fr(eta) * max(mpf(1), nin), "r3 (4.21) / r2 (4.20): 32 t_h^2 2^-P max(1,|Y|)")
            add(f"(c') stage h={h} input |Y_(h-1)| <= 2", nin, 2, "r3 §5.7 intermediate-norm induction")
            Yin = Yout
        zn = cap["bridge_Znorm"]
        add("(d) total normalized |Z^ - F_R x'|", bm.max_abs_diff(mpc_list(zn.re, zn.im, q), Z), cert.norm,
            "bridge_certificate.norm = Q(spread+middle+alias) + solver")
        ef = bm.max_abs_diff(mpc_list(zout.re, zout.im, p + 2), [v * (1 << e) for v in Z])
        add("(e) final output |Z^ - F_R x|", ef, cert.total, "bridge_certificate.total = X norm + sqrt2/8 2^-p",
            rounding_note(cert.total - cert.pre_rounding, cert.total, "sqrt2/8 2^-p"))
        add("(e') final output vs contract", ef, cert.contract, "r3 (2.4): 2^-p A")
    return out


# ----------------------------------------------------------------------------------- case lists
def m1_schedules():
    return {"bt2": test_schedule(base_threshold=2), "bt8": test_schedule(base_threshold=8),
            "bt16": test_schedule(base_threshold=16), "faithful": faithful_schedule()}


M1_FAST = [("bt2", 4, 10), ("bt2", 16, 10), ("bt2", 32, 12), ("bt2", 64, 14), ("bt8", 64, 12),
           ("bt16", 128, 12)]
M1_SLOW = [("bt2", 256, 16), ("bt16", 256, 16), ("bt2", 512, 20), ("faithful", 512, 9)]
M2_FAST = [(2, 4), (2, 6), (3, 3), (3, 5), (4, 4), (4, 6), (5, 5), (5, 6)]
M2_SLOW = [(2, 8), (3, 7), (3, 8), (4, 8), (5, 7), (5, 8)]
KINDS = ["random_max", "random_small", "impulse", "alternating"]


def m2_p(K: int) -> int:
    return max(8, K) + 2
