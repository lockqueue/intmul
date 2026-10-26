"""Component tests for M1: Kronecker packing (MS Lemma 6.2), row spreading (Thm 6.3),
negacyclic shifts and the Synthetic FFT (Lemma 2.5), twisted duality (Thm 3.1), odd-stride routing,
and the uniform cyclic solver (drop-in, r2 (4.20))."""

import random
from fractions import Fraction

import mpmath
import pytest
from hypothesis import given, strategies as st

from subnlogn.fixedpoint import shr_half_even, to_fraction
from subnlogn.kronecker import pack, unpack, spread_row
from subnlogn.synthetic import nega_shift, synthetic_fft, odd_stride_route, twist_rows
from subnlogn.solver import cyclic_solve
from subnlogn.tables import filter_row, solver_tuple, closure_gamma, twist_roots
from subnlogn import certified


# ---------------------------------------------------------------- Kronecker (Lemma 6.2)

@given(st.integers(min_value=4, max_value=80), st.data())
def test_pack_unpack_roundtrip(B, data):
    m = data.draw(st.integers(min_value=1, max_value=40))
    lim = (1 << (B - 1)) - 1
    cs = data.draw(st.lists(st.integers(min_value=-lim, max_value=lim), min_size=m, max_size=m))
    T = pack(cs, B)
    assert T == sum(c << (i * B) for i, c in enumerate(cs))
    assert unpack(T, m, B) == cs


def test_unpack_boundary_coefficients():
    B = 8
    cs = [127, -127, 127, -127, 0, -1, 1, 127]
    assert unpack(pack(cs, B), len(cs), B) == cs


@pytest.mark.parametrize("r,m1", [(8, 3), (8, 20), (16, 7), (32, 15), (4, 30)])
def test_spread_row_matches_direct_correlation(r, m1):
    """Thm 6.3: overlap-add + Kronecker == exact cyclic correlation with the folded filter,
    accumulated exactly at scale 2q and rounded once (bit-identical)."""
    rng = random.Random(r * 1000 + m1)
    q, w, p = 40, 30, 10
    delta = Fraction(rng.randrange(8), 8)
    f = filter_row(delta, r, m1, w, q)
    h = certified.folded_kernel(delta, r, m1, w, q)
    Wt = len(f.taps_re)
    B = 2 * q + p + Wt.bit_length() + 4
    vr = [rng.randint(-(1 << (q + p)), 1 << (q + p)) for _ in range(r)]
    vi = [rng.randint(-(1 << (q + p)), 1 << (q + p)) for _ in range(r)]
    ur, ui = spread_row(vr, vi, f.taps_re, f.taps_im, pack(f.taps_re, B), pack(f.taps_im, B),
                        f.offset, B, q, shr_half_even)
    for k in range(r):
        ar = ai = 0
        for j in range(r):
            hr, hi = h[(j - k) % r]
            ar += vr[j] * hr - vi[j] * hi
            ai += vr[j] * hi + vi[j] * hr
        assert ur[k] == shr_half_even(ar, q)
        assert ui[k] == shr_half_even(ai, q)


# ---------------------------------------------------------------- negacyclic shifts

@given(st.integers(min_value=0, max_value=5), st.integers(min_value=-200, max_value=200))
def test_nega_shift_is_multiplication_by_y_power(k, s):
    r = 1 << k
    rng = random.Random(k * 7919 + s)
    b = [rng.randint(-50, 50) for _ in range(r)]
    got = nega_shift(b, s % (2 * r))
    exp = [0] * r
    for j, v in enumerate(b):
        e = (j + s) % (2 * r)
        if e >= r:
            exp[e - r] -= v
        else:
            exp[e] += v
    assert got == exp


# ---------------------------------------------------------------- Synthetic FFT (Lemma 2.5)

@pytest.mark.parametrize("t1,r", [(2, 2), (2, 4), (4, 4), (4, 8), (8, 8), (8, 16), (16, 16)])
def test_synthetic_fft_against_exact(t1, r):
    rng = random.Random(t1 * 131 + r)
    q = 30
    nu = r // t1
    Pr = [[rng.randint(-(1 << q), 1 << q) for _ in range(r)] for _ in range(t1)]
    Pi = [[rng.randint(-(1 << q), 1 << q) for _ in range(r)] for _ in range(t1)]
    Qr, Qi = synthetic_fft(Pr, Pi, nu, shr_half_even)
    k1 = t1.bit_length() - 1
    bound = Fraction(k1, 2) * 2 / (1 << q)   # per-coordinate <= k1 * (1/2) 2^-q (coordinatewise)
    for v1 in range(t1):
        er = [Fraction(0)] * r
        ei = [Fraction(0)] * r
        for j1 in range(t1):
            sr = nega_shift(Pr[j1], (2 * nu * j1 * v1) % (2 * r))
            si = nega_shift(Pi[j1], (2 * nu * j1 * v1) % (2 * r))
            for k in range(r):
                er[k] += Fraction(sr[k], t1 << q)
                ei[k] += Fraction(si[k], t1 << q)
        for k in range(r):
            assert abs(to_fraction(Qr[v1][k], q) - er[k]) <= bound
            assert abs(to_fraction(Qi[v1][k], q) - ei[k]) <= bound


@pytest.mark.parametrize("t1,r", [(2, 2), (2, 4), (4, 4), (4, 8), (8, 16)])
def test_twisted_duality_theorem(t1, r):
    """MS Thm 3.1: pre-twist, G_{t1}, post-twist, F_r per row and odd-stride routing give
    F_{t1,r} U.  Run the integer pipeline at q = 200 and compare with a high-precision 2D DFT."""
    rng = random.Random(t1 * 31 + r)
    q = 200
    Ur = [[rng.randint(-(1 << q), 1 << q) for _ in range(r)] for _ in range(t1)]
    Ui = [[rng.randint(-(1 << q), 1 << q) for _ in range(r)] for _ in range(t1)]
    zr, zi = twist_roots(r, q)
    Pr, Pi = twist_rows(Ur, Ui, zr, zi, q, shr_half_even, conjugate=False)
    Qr, Qi = synthetic_fft(Pr, Pi, r // t1, shr_half_even)
    Vr, Vi = twist_rows(Qr, Qi, zr, zi, q, shr_half_even, conjugate=True)
    with mpmath.workprec(400):
        Cr, Ci = [], []
        for v1 in range(t1):
            row = [mpmath.mpc(Vr[v1][k], Vi[v1][k]) / mpmath.mpf(2) ** q for k in range(r)]
            out = [sum(row[k] * mpmath.expj(2 * mpmath.pi * k * u / r) for k in range(r)) / r
                   for u in range(r)]
            Cr.append([int(mpmath.nint(mpmath.re(z) * 2 ** q)) for z in out])
            Ci.append([int(mpmath.nint(mpmath.im(z) * 2 ** q)) for z in out])
        cols_r, cols_i = odd_stride_route(Cr, Ci, t1, r)
        for u1 in range(t1):
            for u2 in range(r):
                exact = sum(mpmath.mpc(Ur[j1][j2], Ui[j1][j2])
                            * mpmath.expj(2 * mpmath.pi * (j1 * u1 / t1 + j2 * u2 / r))
                            for j1 in range(t1) for j2 in range(r)) / (t1 * r) / mpmath.mpf(2) ** q
                got = mpmath.mpc(cols_r[u2][u1], cols_i[u2][u1]) / mpmath.mpf(2) ** q
                assert abs(got - exact) < mpmath.mpf(2) ** (-q + 8)


def test_odd_stride_route_is_bijection():
    for t1, r in [(2, 2), (4, 8), (8, 8), (16, 32)]:
        Cr = [[v1 * r + u2 for u2 in range(r)] for v1 in range(t1)]
        cols, _ = odd_stride_route(Cr, Cr, t1, r)
        for u2 in range(r):
            assert sorted(cols[u2]) == sorted(v1 * r + u2 for v1 in range(t1))
            for u1 in range(t1):
                v1 = (cols[u2][u1] - u2) // r
                assert u1 == ((2 * u2 - 1) * v1) % t1


# ---------------------------------------------------------------- solver (r2 (4.20))

def _G(x, w):
    a = 2 * mpmath.sqrt(w * mpmath.log(2))
    return (mpmath.erf(a * (x + mpmath.mpf(1) / 2)) - mpmath.erf(a * (x - mpmath.mpf(1) / 2))) / 2


def _exact_solve(Y, u, t, w):
    """B^{-1} Y for (BZ)_i = c0 Z_i + c1 Z_{i-1} with the TRUE c0, c1 (closed form r3 (4.11)-(4.12))."""
    L = len(Y)
    y = (mpmath.mpf(u) + mpmath.mpf(1) / 2) / t
    c0, c1 = _G(y, w), _G(y - 1, w)
    if c0 > c1:
        rho = -c1 / c0
        return [sum(rho ** s * Y[(v - s) % L] for s in range(L)) / (c0 * (1 - rho ** L))
                for v in range(L)]
    rho = -c0 / c1
    return [sum(rho ** s * Y[(v + 1 + s) % L] for s in range(L)) / (c1 * (1 - rho ** L))
            for v in range(L)]


@pytest.mark.parametrize("t,L", [(2, 2), (2, 64), (4, 8), (8, 8), (8, 256), (16, 4), (64, 32),
                                 (16, 128)])
@pytest.mark.parametrize("kind", ["alternating", "constant", "impulse", "random"])
def test_cyclic_solver_error_bound(t, L, kind):
    P = 60
    q = P + 2
    w = 40
    rng = random.Random(hash((t, L, kind)) & 0xffff)
    with mpmath.workprec(4 * q):
        for u in sorted({0, t // 2 - 1, t // 2, t - 1, rng.randrange(t)}):
            if kind == "alternating":
                Y = [mpmath.mpc((-1) ** v, 0) for v in range(L)]
            elif kind == "constant":
                Y = [mpmath.mpc(1, 1) / 2 for _ in range(L)]
            elif kind == "impulse":
                Y = [mpmath.mpc(1 if v == 3 % L else 0, 0) for v in range(L)]
            else:
                Y = [mpmath.mpc(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(L)]
            yr = [int(mpmath.nint(mpmath.re(z) * 2 ** q)) for z in Y]
            yi = [int(mpmath.nint(mpmath.im(z) * 2 ** q)) for z in Y]
            Yq = [mpmath.mpc(a, b) / mpmath.mpf(2) ** q for a, b in zip(yr, yi)]
            st_ = solver_tuple(u, t, L, w, q)
            zr, zi = cyclic_solve(yr, yi, st_.mu, st_.rho, st_.gamma, st_.forward, q, shr_half_even)
            ex = _exact_solve(Yq, u, t, w)
            ymax = max(1, max(abs(z) for z in Yq))
            err = max(abs(mpmath.mpc(a, b) / mpmath.mpf(2) ** q - e) for a, b, e in zip(zr, zi, ex))
            bound = 32 * t * t * mpmath.mpf(2) ** (-P) * ymax
            assert err <= bound, (u, float(err), float(bound))


def test_closure_gamma_exact_oracle():
    """The exact-rational oracle (method="exact") is correctly rounded: error <= 1/2 2^-q."""
    q = 50
    a_hat = (3 << q) // 7
    for L in (2, 4, 16, 64):
        g = closure_gamma(a_hat, L, q, method="exact")
        exact = 1 / (1 - Fraction(a_hat, 1 << q) ** L)
        assert abs(Fraction(g, 1 << q) - exact) <= Fraction(1, 2 << q)


def test_closure_gamma_powering_meets_4_17():
    """Default closure: br_r2 (4.21) truncated binary powering at Q = q + ceil(lg L) + 2 ceil(lg 4t)
    + 10, guarded division, one rounding.  Within (4.17) (|err| <= 2^-q; proved (1/2 + 2^-10) 2^-q)
    of the exact 1/(1 - rho-hat^L), and within one unit of the exact oracle, for random stored a-hat
    up to the (4.16) limit 1 - 1/(2t), short and very long cycles."""
    from subnlogn.tables import closure_guard
    rng = random.Random(417)
    diffs = 0
    cases = 0
    for q in (20, 62, 130):
        for t in (2, 4, 16, 128, 1024):
            amax = ((2 * t - 1) << q) // (2 * t)              # floor((1 - 1/(2t)) 2^q)
            for L in (2, 4, 10, 64, 1000, 2 ** 12, 2 ** 20):
                for a_hat in (0, 1, amax, amax - 1, rng.randrange(amax + 1), rng.randrange(amax + 1)):
                    g = closure_gamma(a_hat, L, q, t)
                    exact = 1 / (1 - Fraction(a_hat, 1 << q) ** L) if L <= 4096 else None
                    if exact is not None:
                        err = abs(Fraction(g, 1 << q) - exact)
                        assert err <= (Fraction(1, 2) + Fraction(1, 1 << 10)) / (1 << q), (q, t, L, a_hat)
                        ge = closure_gamma(a_hat, L, q, method="exact")
                        assert abs(g - ge) <= 1
                        diffs += g != ge
                        cases += 1
    assert closure_guard(64, 16, 62) == 62 + 6 + 12 + 10
    assert cases > 400 and diffs <= cases // 10                 # 1-unit differences are rare


@pytest.mark.parametrize("t,L", [(4, 8), (8, 64), (16, 16), (64, 128)])
def test_gamma_from_stored_rho_vs_exact_rho(t, L):
    """D5: gamma-hat from the stored rho-hat (r2 (4.17), used here) vs from the exact rho (r3 (4.18),
    spec r1 §7.7).  Both solutions lie within 32 t^2 2^-P max(1,||Y||) of B^{-1} Y."""
    P = 60
    q = P + 2
    w = 40
    rng = random.Random(t * L)
    with mpmath.workprec(4 * q):
        for u in (0, t // 2 - 1, t // 2, t - 1):
            Y = [mpmath.mpc(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(L)]
            yr = [int(mpmath.nint(mpmath.re(z) * 2 ** q)) for z in Y]
            yi = [int(mpmath.nint(mpmath.im(z) * 2 ** q)) for z in Y]
            Yq = [mpmath.mpc(a, b) / mpmath.mpf(2) ** q for a, b in zip(yr, yi)]
            st_ = solver_tuple(u, t, L, w, q)
            y = (mpmath.mpf(u) + mpmath.mpf(1) / 2) / t
            c0, c1 = _G(y, w), _G(y - 1, w)
            a_exact = min(c0, c1) / max(c0, c1)
            g_exact = int(mpmath.nint(2 ** q / (1 - a_exact ** L)))
            ex = _exact_solve(Yq, u, t, w)
            bound = 32 * t * t * mpmath.mpf(2) ** (-P) * max(1, max(abs(z) for z in Yq))
            for g in (st_.gamma, g_exact):
                zr, zi = cyclic_solve(yr, yi, st_.mu, st_.rho, g, st_.forward, q, shr_half_even)
                err = max(abs(mpmath.mpc(a, b) / mpmath.mpf(2) ** q - e) for a, b, e in zip(zr, zi, ex))
                assert err <= bound
