"""FastDFT: the recursive 2D algorithm of the manuscript with the negative half-bin carrier
drop-in (M1).  Implements the listing of MS §7.1 (``FastDFT``, lines 728-762) and Lemma 6.5
``lem:forward``, with the changes of r2 §8 ("The 2D drop-in"):

* kernel  g(s) = e^{-pi i s/r} sinc(s) e^{-pi s^2/alpha^2}, folded modulo r as a complex kernel;
* column coefficients c0 = G((u2 + 1/2)/r), c1 = G((u2 + 1/2)/r - 1) (never equal);
* one uniform cyclic solver on EVERY column; the Nyquist alternating sum, its stack entries,
  ``NyquistSolve`` and erratum #4 (gamma-hat undefined at Nyquist) are deleted.

Contract (MS eq. (inductive-bound)): for x on C~_{p+2}^R with ||x||_inf <= 2^p and p >= max(8, K)
the output Z-hat on C~_{p+2}^R satisfies ||Z-hat - F_R x||_inf <= 2^-p max(1, ||x||_inf).

Routing (``schedule.routing``): with "tape" (default, the faithful algorithm) the Step 1
de-interleave and the final transpose to natural frequency order are Lemma 2.4(i)'s k1 passes, Step
2e is Lemma 2.4(ii)'s transpose + tag scan + k1 merge passes (:mod:`subnlogn.routing`), Step 2b is
the tape procedure of Lemma 2.5's proof (:func:`subnlogn.synthetic.synthetic_fft_tape`) and the
leaves run BaseRadix2FFT's split passes (:mod:`subnlogn.basefft`), all on (re, im) records; "index"
keeps the RAM index maps as the oracle (DEVIATIONS D2).  Both give bit-identical arrays.

With ``ctx.capture`` a dict, the depth-0 call stores (scale q = q_child): ``U_rows`` (spread array
U-hat[j1][k2]), ``V_rows`` (child inputs V-hat[v1][k2]), ``Y_cols`` (routed child outputs
Y-hat[u2][u1]), ``Zcomp`` (pre-rounding output, natural order u2 + r u1) and ``level``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from .basefft import base_radix2_fft
from .checks import require
from .fixedpoint import FxVec, Rounding
from .kronecker import spread_row
from .routing import odd_stride_route_tape, transpose_columns_to_rows
from .schedule import Level2D
from .solver import cyclic_solve
from .synthetic import odd_stride_route, synthetic_fft, synthetic_fft_tape, twist_rows
from .tables import level_tables_2d

__all__ = ["fast_dft", "Certificate2D", "certificate_2d"]


def fast_dft(ctx, x: FxVec, R: int, p: int, depth: int = 0) -> FxVec:
    """F_R x (positive normalized DFT, MS eq. (dft-1d)) by the listing's FastDFT (see module doc).

    ``x`` must be on C~_{p+2} (``x.q == p + 2``); the result is on C~_{p+2}."""
    if x.q != p + 2:
        raise ValueError(f"input must be on C~_(p+2): q={x.q}, p={p}")
    if len(x) != R:
        raise ValueError("length mismatch")
    if depth == 0 and ctx.schedule.rounding is Rounding.TRUNC:
        raise ValueError("the front end uses nearest rounding (MS Def. 2.1); its error certificates "
                         "assume it (TRUNC would need doubled constants)")
    lv = ctx.schedule.level(R, p, depth)
    inst = ctx.inst
    inst.height(f"d{depth}.input", x.re, x.im)
    if lv.leaf:
        re, im = base_radix2_fft(ctx, x.re, x.im, lv)
        return FxVec(re, im, p + 2)
    inst.hit("fastdft.node")
    shr = ctx.shr
    tab = level_tables_2d(ctx, lv)
    t1, r, q = lv.t1, lv.r, lv.q_child
    up = q - (p + 2)

    # Step 1: row spreading (MS Thm 6.3; drop-in complex folded kernel).  Row j1 is the stride-t1
    # de-interleave x(j1 + t1 j2) (Lemma 2.4(i)), moved exactly to C~_q.
    routing = ctx.schedule.routing
    rows = _deinterleave(x, t1, r, routing, inst)
    U_re, U_im = [], []
    for j1 in range(t1):
        v_re = [a << up for a in rows[j1][0]]
        v_im = [a << up for a in rows[j1][1]]
        require(_input_precondition(v_re, v_im, q + p),
                "FastDFT precondition ||x||_inf <= 2^p violated (MS Thm 6.3)")
        f = tab.filters[j1]
        ur, ui = spread_row(v_re, v_im, f.taps_re, f.taps_im, tab.packed_re[j1], tab.packed_im[j1],
                            f.offset, lv.B_slot, q, shr, ctx.product_mul(q), inst)
        U_re.append(ur)
        U_im.append(ui)
    inst.hit("spread.row", t1)
    inst.height(f"d{depth}.spread", *U_re, *U_im)

    # Step 2a-2c: pre-twist, synthetic FFT G_{t1} over C[y]/(y^r+1), post-twist (MS Thm 3.1).
    P_re, P_im = twist_rows(U_re, U_im, tab.zeta_re, tab.zeta_im, q, shr, conjugate=False,
                            mul=ctx.word_mul())
    inst.hit("twist.pre", t1 * r)
    syn = synthetic_fft_tape if routing == "tape" else synthetic_fft      # Lemma 2.5 tape passes
    Q_re, Q_im = syn(P_re, P_im, lv.nu, shr, inst)
    V_re, V_im = twist_rows(Q_re, Q_im, tab.zeta_re, tab.zeta_im, q, shr, conjugate=True,
                            mul=ctx.word_mul())
    inst.hit("twist.post", t1 * r)
    inst.height(f"d{depth}.child_in", *V_re, *V_im)

    # Step 2d: t1 recursive calls at length r and precision p_child (q = p_child + 2).
    C_re, C_im = [], []
    for v1 in range(t1):
        c = fast_dft(ctx, FxVec(V_re[v1], V_im[v1], q), r, lv.p_child, depth + 1)
        C_re.append(c.re)
        C_im.append(c.im)

    # Step 2e: odd-stride routing u1 = (2 u2 - 1) v1 mod t1 into columns (MS eq. (odd-perm)).
    cols_re, cols_im = _route_children(C_re, C_im, t1, r, routing, inst)
    inst.hit("route.oddstride")

    # Depth-0 intermediates for the stage-wise error checks (tests/stage_checks.py), all on scale q.
    # References only (none of these lists is mutated later); nothing happens when capture is None.
    capture = ctx.capture if (ctx.capture is not None and depth == 0) else None
    if capture is not None:
        capture["U_rows"] = (U_re, U_im)          # spread array U-hat[j1][k2]           (Step 1)
        capture["V_rows"] = (V_re, V_im)          # child inputs V-hat[v1][k2]           (Step 2c)
        capture["Y_cols"] = (cols_re, cols_im)    # routed child outputs Y-hat[u2][u1]   (Step 2e)

    # Step 3: uniform cyclic solve on every column (drop-in), quantize to C~_{p+2}, transpose to
    # natural order u = u2 + r u1 (Lemma 2.4(i)).
    out_re = [0] * R
    out_im = [0] * R
    zc_re = [0] * R if capture is not None else None
    zc_im = [0] * R if capture is not None else None
    colmajor = []                                  # tape: solved records in column-major (u2, u1)
    for u2 in range(r):
        st = tab.solver[u2]
        z_re, z_im = cyclic_solve(cols_re[u2], cols_im[u2], st.mu, st.rho, st.gamma, st.forward,
                                  q, shr, inst, hkey=f"d{depth}.solver", mul=ctx.word_mul())
        if routing == "tape":
            for u1 in range(t1):
                rec = (shr(z_re[u1], up), shr(z_im[u1], up))
                # with capture on, the pre-rounding values ride along as extra payload fields
                colmajor.append(rec if capture is None else rec + (z_re[u1], z_im[u1]))
            continue
        for u1 in range(t1):                       # routing == "index": the RAM index map
            out_re[u2 + r * u1] = shr(z_re[u1], up)
            out_im[u2 + r * u1] = shr(z_im[u1], up)
            if capture is not None:
                zc_re[u2 + r * u1] = z_re[u1]
                zc_im[u2 + r * u1] = z_im[u1]
    if routing == "tape":                          # (u2, u1) -> u = u2 + r u1 (Lemma 2.4(i), MS L493)
        nat = transpose_columns_to_rows(colmajor, t1, r, inst)
        out_re = [rec[0] for rec in nat]
        out_im = [rec[1] for rec in nat]
        if capture is not None:
            zc_re = [rec[2] for rec in nat]
            zc_im = [rec[3] for rec in nat]
    if capture is not None:
        capture["Zcomp"] = FxVec(zc_re, zc_im, q)
        capture["level"] = lv
    return FxVec(out_re, out_im, p + 2)


def _input_precondition(v_re: list[int], v_im: list[int], e: int) -> bool:
    """Runtime check (class E, not an algorithm step): |x_j|^2 <= 2^(2e) for every entry, the complex modulus of
    MS's input hypothesis ||x||_inf <= 2^p at scale q (e = q + p).  Exact: components <= 2^(e-1) imply
    the bound (cheap prefilter, no products); otherwise the squared moduli are compared with 2^(2e)."""
    half = 1 << (e - 1)
    if max(max(map(abs, v_re), default=0), max(map(abs, v_im), default=0)) <= half:
        return True
    lim2 = 1 << (2 * e)
    return all(a * a + b * b <= lim2 for a, b in zip(v_re, v_im))


def _deinterleave(x: FxVec, t1: int, r: int, routing: str, inst) -> list:
    """Step 1's de-interleave of x (indexed j = j1 + t1 j2, i.e. column-major (j2, j1)) into the t1
    rows (x(j1 + t1 j2))_{j2} (MS L197, L620; Lemma 2.4(i)).  "tape": the k1 reverse transpose passes
    on the records (x.re[j], x.im[j]); "index": the index map (oracle, DEVIATIONS D2).  Returns the
    rows as [(re list, im list)]."""
    if routing == "index":
        return [([x.re[j1 + t1 * j2] for j2 in range(r)], [x.im[j1 + t1 * j2] for j2 in range(r)])
                for j1 in range(t1)]
    recs = transpose_columns_to_rows(list(zip(x.re, x.im)), t1, r, inst)
    rows = []
    for j1 in range(t1):
        row = recs[j1 * r:(j1 + 1) * r]
        rows.append(([a for a, _ in row], [b for _, b in row]))
    return rows


def _route_children(C_re: list, C_im: list, t1: int, r: int, routing: str, inst):
    """Step 2e (MS Thm 3.1 step 5, eq. (odd-perm), L201): Y[u1][u2] = C_{v1}[u2] with
    u1 = (2 u2 - 1) v1 mod t1, returned column-major as cols[u2][u1].  "tape": Lemma 2.4(ii)
    (transpose, tag scan, k1 merge passes) on the records (re, im) of the child outputs in natural
    row order; "index": :func:`subnlogn.synthetic.odd_stride_route` (oracle, DEVIATIONS D2)."""
    if routing == "index":
        return odd_stride_route(C_re, C_im, t1, r)
    recs = []
    for v1 in range(t1):
        recs.extend(zip(C_re[v1], C_im[v1]))
    routed = odd_stride_route_tape(recs, t1, r, inst)
    cols_re, cols_im = [], []
    for u2 in range(r):
        col = routed[u2 * t1:(u2 + 1) * t1]
        cols_re.append([a for a, _ in col])
        cols_im.append([b for _, b in col])
    return cols_re, cols_im


# ----------------------------------------------------------------------------------------------
# Error certificate (MS Lemma 6.5 with the drop-in constants of r2 §8).
# ----------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Certificate2D:
    """Bounds (exact rationals, in absolute units) for one top-level FastDFT call.

    ``pre_rounding`` bounds ||Z^comp - F_R x||_inf (before the final quantization to C~_{p+2});
    ``total`` adds the final rounding sqrt(2)/8 2^-p; ``contract`` = 2^-p max(1, ||x||)."""

    alias: Fraction
    steps12: Fraction
    solver: Fraction
    final_rounding: Fraction
    pre_rounding: Fraction
    total: Fraction
    contract: Fraction


def certificate_2d(lv: Level2D, A: Fraction) -> Certificate2D:
    """Drop-in error envelope (r2 §8): with A = max(1, ||x||_inf), u = 2^-P (P = p_child),
    ||B^{-1}|| <= r, alias Psi < 0.120 2^-w (w = p_work), Steps 1-2 RHS error 9 r u A
    (MS Lemma 6.5 proof), solver 32 r^2 u M_Y with M_Y <= 2A:

        ||Z^comp - F_R x|| <= 0.120 r 2^-w A + 9 r^2 u A + 64 r^2 u A,

    then + sqrt(2)/8 2^-p (final rounding; rational upper bound 0.17678).  At a leaf: Lemma 6.5's
    2.16 K 2^{-q_b} A, then the same final rounding."""
    p = lv.p
    final = Fraction(17678, 100000) / (1 << p)
    contract = A / (1 << p)
    if lv.leaf:
        pre = Fraction(216, 100) * lv.K * A / (1 << lv.q_b)
        return Certificate2D(Fraction(0), pre, Fraction(0), final, pre, pre + final, contract)
    r = lv.r
    u = Fraction(1, 1 << lv.p_child)
    alias = Fraction(120, 1000) * r * A / (1 << lv.p_work)
    steps12 = 9 * r * r * u * A
    solver = 64 * r * r * u * A
    pre = alias + steps12 + solver
    return Certificate2D(alias, steps12, solver, final, pre, pre + final, contract)
