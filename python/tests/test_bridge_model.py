"""Tests of the high-precision mpmath model of bridge Lemmas A and B (tests/bridge_model.py).

Sources: r2 = bridge derivation r2, r3 = bridge derivation r3, spec = implementer spec S1,
MS = the companion manuscript [MS].  Everything runs at bridge_model.DPS = 80 digits.
"""

from fractions import Fraction

import pytest
from hypothesis import given, settings, strategies as st
from mpmath import mp, mpc, mpf

import bridge_model as bm
from subnlogn.bridge.geometry import BridgeGeometry


@pytest.fixture(autouse=True)
def _model_precision():
    with bm.precision():
        yield


def tol(e: int = 40) -> mpf:
    return mpf(10) ** -e


def a8() -> mpf:
    """alpha with sqrt(pi) alpha = 8 (r2 §3.4 and §10.1; w = 23 lies in r2 Thm 1's interval)."""
    return 8 / mp.sqrt(mp.pi)


def unit(R: int, k: int) -> list:
    return [mpc(1) if i == k else mpc(0) for i in range(R)]


# ============================================================================ (a) Lemma A
LEMMA_A_GEOMS = [(2, 2), (2, 4), (4, 2), (2, 8), (8, 2), (4, 4), (4, 8), (8, 4), (2, 16), (16, 2), (2, 32),
                 (8, 8), (2, 2, 2), (2, 4, 2), (4, 2, 2), (2, 2, 8), (8, 2, 2), (2, 8, 2), (4, 4, 4),
                 (2, 4, 8), (8, 4, 2), (2, 2, 2, 2), (2, 4, 2, 4), (4, 2, 2, 2), (2, 2, 2, 8), (8, 2, 2, 2),
                 (2, 2, 4, 4), (2, 2, 2, 2, 2), (2, 2, 2, 2, 4), (4, 2, 2, 2, 2), (2, 4, 2, 2, 2),
                 (2, 2, 2, 4, 2)]


def alpha_choice(i: int) -> mpf:
    return [a8(), bm.alpha_from_w(8), bm.alpha_from_w(30), mpf(5) / 2][i % 4]


@pytest.mark.parametrize("carrier", [-1, 0, 1])
@pytest.mark.parametrize("i,t", list(enumerate(LEMMA_A_GEOMS)))
def test_lemma_A_identity(i, t, carrier):
    """r2 (2.2) / r3 (3.7): F_t S_2 ... S_d x = A_2 A_3 ... A_d F_R x (A_d acts first) for random complex x;
    any Schwartz kernel works (carriers -1, 0, +1); aliases |m| <= 6, spatial folding |s| <= 60."""
    g = BridgeGeometry(t)
    alpha = alpha_choice(i)
    assert bm.folded_tail_bound(2, alpha, 60) < tol(100)
    x = bm.random_vector(g.R, seed=10 * i + carrier)
    lhs = bm.lemma_A_lhs(g, x, alpha, carrier)
    rhs = bm.lemma_A_rhs(g, x, alpha, carrier, mmax=6)
    assert bm.max_abs_diff(lhs, rhs) < tol(40)


@pytest.mark.parametrize("t", [(2, 4), (2, 2, 4), (4, 2, 2, 2), (2, 2, 2, 2, 2)])
def test_lemma_A_per_axis_kernels(t):
    """The proof of r2 §3.2 / r3 §3.2 is per axis: arbitrary per-axis Schwartz kernels g_h (here
    fractional carriers and per-axis alpha_h, as r3 (2.2) allows) still give r2 (3.7)."""
    g = BridgeGeometry(t)
    carriers = [Fraction(0)] + [Fraction((-1) ** h, h + 1) for h in range(2, g.d + 1)]
    alphas = [a8()] + [bm.alpha_from_w(8 + 4 * h) for h in range(2, g.d + 1)]
    x = bm.random_vector(g.R, seed=99)
    assert bm.max_abs_diff(bm.lemma_A_lhs(g, x, alphas, carriers), bm.lemma_A_rhs(g, x, alphas, carriers)) < tol(40)


@st.composite
def small_geometries(draw):
    d = draw(st.integers(2, 4))
    exps = [1] * d
    for _ in range(draw(st.integers(0, 5 - d))):
        exps[draw(st.integers(0, d - 1))] += 1
    return BridgeGeometry(tuple(1 << e for e in exps))


@settings(max_examples=12)
@given(small_geometries(), st.sampled_from([-1, 0, 1, Fraction(1, 3)]), st.integers(0, 10 ** 6))
def test_lemma_A_random_geometries(g, carrier, seed):
    """r2 (2.2) on random geometries R <= 32, random carriers and inputs."""
    x = bm.random_vector(g.R, seed)
    alpha = bm.alpha_from_w(8 + seed % 40)
    assert bm.max_abs_diff(bm.lemma_A_lhs(g, x, alpha, carrier), bm.lemma_A_rhs(g, x, alpha, carrier)) < tol(40)


@pytest.mark.parametrize("t", [(2, 2, 2), (2, 4, 2), (4, 2, 2, 2), (2, 2, 2, 2, 2)])
def test_operator_order_reproduces_poisson_sum(t):
    """r2 §3.3 / r3 §3.3: expanding A_2 A_3 ... A_d evaluates each coefficient of A_h at the unshifted
    u_h (shifts from indices < h leave u_h alone), so the composed truncated chain equals the direct
    multi-index sum r2 (3.7) term by term; the reversed chain A_d ... A_2 does not."""
    g = BridgeGeometry(t)
    alpha = bm.alpha_from_w(8)
    Z = bm.random_vector(g.R, seed=7)
    for carrier in (-1, 0):
        direct = bm.alias_sum(g, Z, alpha, carrier, mmax=2)
        ops = [bm.alias_op(g, h, alpha, carrier, mmax=2) for h in range(2, g.d + 1)]
        assert bm.max_abs_diff(bm.apply_chain(ops, Z), direct) < tol(60)
        assert bm.max_abs_diff(bm.apply_chain(ops[::-1], Z), direct) > tol(3)


def test_exact_inputs_accepted_and_floats_rejected():
    """Model inputs are exact: ints, Fractions, mpf, mpc; Python floats are refused (bridge_model.to_mpf)."""
    g = BridgeGeometry((2, 2))
    xs = [Fraction(1, 3), 2, mpf(1) / 7, mpc(0, 1)]
    U = bm.spread(g, xs, a8())
    assert bm.max_abs_diff(U, bm.spread(g, [bm.to_mpc(v) for v in xs], a8())) == 0
    assert bm.max_abs_diff(bm.tensor_dft(g, xs), bm.tensor_dft_direct(g, [bm.to_mpc(v) for v in xs])) < tol(70)
    with pytest.raises(TypeError):
        bm.to_mpf(0.5)
    with pytest.raises(TypeError):
        bm.G(0.25, a8())
    with mp.workdps(15), pytest.raises(RuntimeError):
        bm.G(Fraction(1, 4), mpf(2))


@pytest.mark.parametrize("t", [(2, 2, 2), (4, 2, 4), (2, 2, 2, 2), (2, 4, 2, 2, 2)])
def test_chronological_spread_is_product_formula(t):
    """r2 (3.2) / r3 (3.1): spreading in chronological order d, ..., 2 (lower digits still original)
    equals the explicit product formula; spreading in ascending order (h = 2 first, using the digits
    then present) does not, and breaks Lemma A; so does reversing the alias operators (r2 §3.3).  The
    separable tensor DFT equals its defining multi-sum."""
    g = BridgeGeometry(t)
    alpha = a8()
    x = bm.random_vector(g.R, seed=3)
    U = bm.spread(g, x, alpha)
    assert bm.max_abs_diff(U, bm.spread_explicit(g, x, alpha)) < tol(60)
    assert bm.max_abs_diff(bm.tensor_dft(g, U), bm.tensor_dft_direct(g, U)) < tol(60)
    U_asc = bm.spread(g, x, alpha, order="ascending")
    assert bm.max_abs_diff(U_asc, U) > tol(2)
    rhs = bm.lemma_A_rhs(g, x, alpha)
    assert bm.max_abs_diff(bm.tensor_dft(g, U_asc), rhs) > tol(2)
    assert bm.max_abs_diff(bm.lemma_A_rhs(g, x, alpha, reverse=True), rhs) > tol(2)


@pytest.mark.parametrize("t1,r", [(2, 2), (2, 4), (4, 4), (4, 8)])
def test_d2_is_manuscript_poisson_identity(t1, r):
    """MS thm:poisson in its own 2D indexing, U°_{j1,k2} = sum_{j2} x(j1 + t1 j2) h^{(j1)}_{(j2-k2) mod r}
    with shift j1/t1 (eq. u-ideal), and (F_{t1,r} U°)_{u1,u2} = sum_m ghat(u2/r - m) (F_R x)_{u2 + r((u1-m)
    mod t1)} (eq. poisson-bridge); for the real kernel (carrier 0) and the r2 §8 drop-in (carrier -1,
    ghat(xi) = G(xi + 1/(2r)))."""
    R, alpha = t1 * r, a8()
    x = bm.random_vector(R, seed=t1 + r)
    Z = bm.dft(x)
    w1, w2 = [mp.expjpi(mpf(2 * v) / t1) for v in range(t1)], [mp.expjpi(mpf(2 * v) / r) for v in range(r)]
    for carrier in (0, -1):
        U = []
        for j1 in range(t1):
            H = bm.folded(Fraction(j1, t1), r, alpha, carrier)
            U.append([mp.fsum(x[j1 + t1 * j2] * H[(j2 - k2) % r] for j2 in range(r)) for k2 in range(r)])
        for u1 in range(t1):
            for u2 in range(r):
                lhs = mp.fsum(U[j1][k2] * w1[(j1 * u1) % t1] * w2[(k2 * u2) % r]
                              for j1 in range(t1) for k2 in range(r)) / R
                rhs = mp.fsum(bm.ghat(Fraction(u2, r) - m, r, alpha, carrier) * Z[u2 + r * ((u1 - m) % t1)]
                              for m in range(-6, 7))
                assert abs(lhs - rhs) < tol(40)


def _spec_fold(delta, t, alpha, carrier, m):
    """spec §7.3, transcribed: W = 2m+1; if W <= t: H[a] = g(m - a + delta), offset m; else
    H[(-e) % t] += g(e + delta) for |e| <= m, offset 0."""
    H = [mpc(0)] * t
    if 2 * m + 1 <= t:
        for a in range(2 * m + 1):
            H[a] = bm.kernel(m - a + delta, t, alpha, carrier)
        return H, m
    for e in range(-m, m + 1):
        H[(-e) % t] += bm.kernel(e + delta, t, alpha, carrier)
    return H, 0


@pytest.mark.parametrize("t,m", [(2, 3), (4, 3), (8, 3), (16, 3), (8, 4), (32, 5)])
def test_spec_7_3_fold_matches_r2_line_operation(t, m):
    """spec §7.3's two folding branches plus cyclic convolution and output offset reproduce the r2 (3.1)
    line operation U_k = sum_j x_j sum_{|e| <= m, e = j - k (mod t)} g(e + delta) (spatial truncation
    |e| <= m as in r2 §4.7, (4.23))."""
    alpha, delta = a8(), Fraction(3, 8)
    x = bm.random_vector(t, seed=t * m)
    H, off = _spec_fold(delta, t, alpha, -1, m)
    conv = [mp.fsum(x[j] * H[(n - j) % t] for j in range(t)) for n in range(t)]
    for k in range(t):
        ref = mp.fsum(x[j] * bm.kernel(e + delta, t, alpha, -1)
                      for j in range(t) for e in range(-m, m + 1) if (e - (j - k)) % t == 0)
        assert abs(conv[(k + off) % t] - ref) < tol(60)


# ============================================================================ (b) explicit d = 3
def test_d3_explicit_check_r2_section_3_4():
    """r2 §3.4 (and r3 §3.4): t = (2,2,2), x = e_3, u = (1,0,1), k = 5, sqrt(pi) alpha = 8."""
    g, alpha = BridgeGeometry((2, 2, 2)), a8()
    x = unit(8, 3)
    Z = bm.dft(x)
    assert bm.max_abs_diff(Z, [mp.expjpi(mpf(6 * k) / 8) / 8 for k in range(8)]) < tol(70)
    k = g.phi((1, 0, 1))
    assert k == 5
    for src, ratio in [(1, -1), (3, 1j), (7, -1j)]:                  # the r2 alias table
        assert abs(Z[src] / Z[5] - ratio) < tol(70)
    c0, c1 = bm.G(Fraction(1, 4), alpha), bm.G(Fraction(3, 4), alpha)
    coeff = lambda h, u, m: bm.alias_coeff(g, h, u, m, alpha)
    assert (coeff(2, 0, 0), coeff(2, 0, 1)) == (c0, c1)                # axis 2 uses (c0, c1)
    assert (coeff(3, 1, 0), coeff(3, 1, 1)) == (c1, c0)                # axis 3 uses (c1, c0)
    s, D = c0 + c1, c0 - c1
    Y311 = D / (8 * mp.sqrt(2)) * (s + 1j * D)                         # r2 (3.11)
    B = [bm.alias_op(g, h, alpha, retain={0, 1}) for h in (2, 3)]
    assert abs(bm.apply_chain(B, Z)[5] - Y311) < tol(70)
    assert 0 < 1 - s < mpf("2e-17") and abs(D - mpf("0.9953222650189527")) < mpf("1e-16")
    assert abs(Y311 - mpc("0.087975", "0.087563")) < mpf("1e-6")
    full = bm.lemma_A_rhs(g, x, alpha)[5]
    assert mpf("1e-19") < abs(full - Y311) < mpf("3e-18")             # "less than 3e-18"
    assert abs(bm.lemma_A_lhs(g, x, alpha)[5] - full) < tol(40)
    # r3 §3.4: both sides equal e^{7 pi i/4}/8 sum ghat_2(-m2) ghat_3(1/2 - m3) (-1)^m2 i^m3
    r3 = mp.expjpi(mpf(7) / 4) / 8 * mp.fsum(
        bm.ghat(-m2, 2, alpha) * bm.ghat(Fraction(1, 2) - m3, 2, alpha) * (-1) ** m2 * mpc(0, 1) ** m3
        for m2 in range(-6, 7) for m3 in range(-6, 7))
    assert abs(r3 - full) < tol(60)
    # direct spreading: U_{1,k2,k3} = sum g(3/2 - k2 - 2 l2) g(3/4 - k3 - 2 l3), U_{0,k2,k3} = 0
    U = bm.spread(g, x, alpha)
    for k2 in range(2):
        for k3 in range(2):
            ref = (mp.fsum(bm.kernel(Fraction(3, 2) - k2 - 2 * l, 2, alpha) for l in range(-30, 31))
                   * mp.fsum(bm.kernel(Fraction(3, 4) - k3 - 2 * l, 2, alpha) for l in range(-30, 31)))
            assert abs(U[g.index((1, k2, k3))] - ref) < tol(60) and U[g.index((0, k2, k3))] == 0


def test_d3_noncommutativity():
    """r2 §3.4 / r3 §3.4: for Z = e_6, (B_2 B_3 Z)_0 = c_{2,0}(0) c_{3,1}(0) but
    (B_3 B_2 Z)_0 = c_{3,1}(0) c_{2,0}(1) (r3: the h = 3 shift 0 -> 6 changes u_2); they differ, so
    B_2 B_3 != B_3 B_2, and reversing the operator order breaks Lemma A."""
    g, alpha = BridgeGeometry((2, 2, 2)), a8()
    B2, B3 = (bm.alias_op(g, h, alpha, retain={0, 1}) for h in (2, 3))
    c = lambda h, m, u: bm.alias_coeff(g, h, u, m, alpha)
    v23, v32 = bm.apply_chain([B2, B3], unit(8, 6))[0], bm.apply_chain([B3, B2], unit(8, 6))[0]
    assert abs(v23 - c(2, 0, 0) * c(3, 1, 0)) < tol(70) and abs(v32 - c(3, 1, 0) * c(2, 0, 1)) < tol(70)
    c0, c1 = bm.G(Fraction(1, 4), alpha), bm.G(Fraction(3, 4), alpha)
    assert (c(2, 0, 0), c(3, 1, 0), c(2, 0, 1)) == (c0, c1, c1)
    assert abs(v23 - v32) > mpf("2e-3")
    M23, M32 = B2.matrix() * B3.matrix(), B3.matrix() * B2.matrix()
    assert max(abs(M23[i, j] - M32[i, j]) for i in range(8) for j in range(8)) > mpf("2e-3")
    x = bm.random_vector(8, seed=5)
    lhs = bm.lemma_A_lhs(g, x, alpha)
    assert bm.max_abs_diff(lhs, bm.lemma_A_rhs(g, x, alpha)) < tol(40)
    assert bm.max_abs_diff(lhs, bm.lemma_A_rhs(g, x, alpha, reverse=True)) > tol(2)


# ============================================================================ (c) deconvolution order
DECONV_GEOMS = [(2, 2), (4, 8), (2, 2, 2), (2, 4, 4), (4, 2, 8), (2, 2, 2, 2), (4, 2, 2, 4), (2, 2, 2, 2, 2),
                (2, 2, 4, 2, 2)]


@pytest.mark.parametrize("w", [8, 16])
@pytest.mark.parametrize("t", DECONV_GEOMS)
def test_chronological_deconvolution(t, w):
    """r2 (2.6)-(2.7), (3.9): with Y = F_t U, applying B_2^{-1}, then B_3^{-1}, ..., then B_d^{-1}
    recovers Z = F_R x within ||(B_2..B_d)^{-1}|| sum_h ||A_h - B_h|| ||Z|| (telescoping
    A_2..A_d - B_2..B_d = sum_h B_2..B_{h-1} (A_h - B_h) A_{h+1}..A_d, ||A_h|| = 1, ||B_h|| <= 1), where
    ||A_h - B_h|| = max_u Psi((u + 1/2)/t_h) < 0.120 2^-w.  It inverts B_2 ... B_d exactly; for d >= 3
    the reversed order does neither."""
    g, alpha = BridgeGeometry(t), bm.alpha_from_w(w)
    x = bm.random_vector(g.R, seed=w + g.R)
    Z = bm.dft(x)
    Y = bm.lemma_A_lhs(g, x, alpha)
    err = bm.max_abs_diff(bm.deconvolve(g, Y, alpha), Z)
    inv_norm = bm.chain_inverse_norm(g, alpha)
    tails = [max(bm.omitted_mass(Fraction(2 * u + 1, 2 * g.tt(h)), alpha) for u in range(g.tt(h)))
             for h in range(2, g.d + 1)]
    assert all(tl < mpf("0.120") * mpf(2) ** -w for tl in tails)
    assert tails == [bm.alias_tail_norm(g.tt(h), alpha) for h in range(2, g.d + 1)]
    bound = inv_norm * mp.fsum(tails) * bm.norm_inf(Z)
    assert bound * mpf(10) ** -4 < err <= bound
    assert inv_norm <= mpf(g.R) / g.t[0]                                              # r2 (2.6)
    assert err < mpf("0.120") * (g.d - 1) * g.R / g.t[0] * mpf(2) ** -w * bm.norm_inf(x)  # r2 (2.7)
    YB = bm.apply_chain([bm.alias_op(g, h, alpha, retain={0, 1}) for h in range(2, g.d + 1)], Z)
    assert bm.max_abs_diff(bm.deconvolve(g, YB, alpha), Z) < tol(60)
    if g.d >= 3:
        assert bm.max_abs_diff(bm.deconvolve(g, YB, alpha, order="reversed"), Z) > tol(3)
        assert bm.max_abs_diff(bm.deconvolve(g, Y, alpha, order="reversed"), Z) > 100 * bound


@pytest.mark.parametrize("t", [(2, 2, 2), (2, 4, 8), (4, 2, 2, 2), (2, 2, 2, 2, 2)])
def test_chain_inverse_norm(t):
    """r2 (2.6), (4.14): ||(B_2..B_d)^{-1}|| <= prod_h max_u 1/|c0 - c1| <= prod_h 4t_h/7 <= R/t_1;
    noncommutativity does not affect the estimate."""
    g = BridgeGeometry(t)
    for alpha in (bm.alpha_from_w(8), a8()):
        prod = mpf(1)
        for h in range(2, g.d + 1):
            th = g.tt(h)
            prod *= max(1 / abs(c0 - c1) for c0, c1 in (bm.retained_coeffs(th, u, alpha) for u in range(th)))
        n = bm.chain_inverse_norm(g, alpha)
        assert n <= prod * (1 + tol(60))
        assert prod <= mpf(4) ** (g.d - 1) * g.R / g.t[0] / mpf(7) ** (g.d - 1) <= mpf(g.R) / g.t[0]


# ============================================================================ (d) Lemma B constants
def test_partition_of_unity_and_operator_norms():
    """r2 (4.4): sum_m G(xi - m) = 1, hence ||A_h||_inf = 1, ||B_h||_inf <= 1 and ||A_h - B_h||_inf =
    max_u Psi((u + 1/2)/t_h) (r2 (2.4), (4.5))."""
    for alpha in (bm.alpha_from_w(8), a8()):
        for xi in [Fraction(0), Fraction(1, 3), Fraction(1, 2), Fraction(7, 8), Fraction(-5, 4), Fraction(1, 1024)]:
            assert abs(mp.fsum(bm.G(xi - m, alpha) for m in range(-40, 41)) - 1) < tol(70)
        for t in [(2, 4, 2), (4, 4)]:
            g = BridgeGeometry(t)
            for h in range(2, g.d + 1):
                assert abs(bm.alias_op(g, h, alpha, mmax=8).norm_inf() - 1) < tol(70)
                assert bm.alias_op(g, h, alpha, retain={0, 1}).norm_inf() <= 1
                tail = bm.alias_op(g, h, alpha, retain=set(range(-8, 9)) - {0, 1}).norm_inf()  # A_h - B_h
                assert abs(tail - bm.alias_tail_norm(g.tt(h), alpha)) < tol(70)


def test_omitted_mass_is_the_dropped_alias_mass():
    """r2 (4.1)/(4.5), r3 (4.1): Psi(y) = sum_{m not in {0,1}} G(y - m) = 1 - c0 - c1 for every real y."""
    for alpha in (bm.alpha_from_w(8), a8(), bm.alpha_from_w(64)):
        for y in [Fraction(-1, 4), Fraction(1, 16), Fraction(1, 2), Fraction(31, 32), Fraction(5, 3)]:
            psi = bm.omitted_mass(y, alpha)
            direct = mp.fsum(bm.G(y - m, alpha) for m in range(-40, 41) if m not in (0, 1))
            assert abs(direct - psi) <= tol(70) * psi
            assert abs(1 - bm.G(y, alpha) - bm.G(y - 1, alpha) - psi) < tol(75)


W_LIST = [8, 9, 10, 12, 16, 23, 32, 64, 128, 256]
T_ALL_U = [2, 4, 8, 16, 32, 64]
T_EDGE_U = [128, 1024, 2 ** 14, 2 ** 20]


@pytest.mark.parametrize("w", W_LIST)
def test_lemma_B_constants_negative_carrier(w):
    """Repaired Lemma B for alpha = f 2 sqrt(w ln2/pi), f = 1 and f = 2 (both ends of r2 Thm 1's interval):
    omitted alias Psi < 0.120 2^-w (r2 (4.6), r3 (4.5)); passband M >= erf(a)/2 >= 1/2 - 0.060 2^-4w
    > 0.49999999 (r2 (4.8), r3 (4.6)); |c0 - c1| >= 7/(4t) (r3 (4.10)) > 1.47/t (r2 (4.10)); so
    ||B^{-1}||_inf = 1/|c0 - c1| <= 4t/7 <= t (r3 §4.5, r2 (4.13)); c0 > c1 iff u < t/2 (r2 §8, spec §7.7).
    For large t only the extreme samples (stopband) and the two samples next to the crossing are checked
    (Psi is convex and symmetric on [0, 1], |c0 - c1| increases away from the crossing: r2 §4.3-4.4)."""
    bound, half = mpf("0.120") * mpf(2) ** -w, mpf(1) / 2
    for f in (1, 2):
        alpha = bm.alpha_from_w(w, f)
        a = mp.sqrt(mp.pi) * alpha
        assert mp.erf(a) / 2 >= half - mpf("0.060") * mpf(2) ** (-4 * w)
        for t in T_ALL_U + T_EDGE_U:
            for u in (range(t) if t in T_ALL_U else (0, t // 2 - 1, t // 2, t - 1)):
                c0, c1 = bm.retained_coeffs(t, u, alpha)
                assert bm.omitted_mass(Fraction(2 * u + 1, 2 * t), alpha) < bound
                assert max(c0, c1) >= mp.erf(a) / 2 * (1 - tol(70)) and max(c0, c1) > mpf("0.49999999")
                assert (c0 > c1) == (u < t // 2)
                gap = abs(c0 - c1)
                assert gap >= mpf(7) / (4 * t) and gap > mpf("1.47") / t
                assert 1 / gap <= mpf(4 * t) / 7 <= t
    psi0 = bm.omitted_mass(0, bm.alpha_from_w(w))                                    # r2 (4.6) chain
    s = mp.sqrt(mp.pi * w * mp.ln2)
    assert psi0 <= mpf(2) ** -w / (2 * s) + mpf(2) ** (-9 * w) / (6 * s) < bound


R2_TABLE_10_1 = {  # t: (c_large, c_small, |c0 - c1|, ||B^{-1}||) for sqrt(pi) alpha = 8, u = t/2 - 1
    2: ("0.997661132509", "0.002338867491", "0.995322265019", "1.0046997"),
    4: ("0.921350396475", "0.078649603525", "0.842700792950", "1.1866608"),
    8: ("0.760249938907", "0.239750061093", "0.520499877813", "1.92123004"),
    16: ("0.638163195084", "0.361836804916", "0.276326390168", "3.61890878"),
    64: ("0.535215989", "0.464784011", "0.070431978", "14.1981"),
    1024: ("0.502203854351", "0.497796145649", "0.004407708703", "226.875247"),
}


def _matches(value, s: str) -> bool:
    return abs(value - mpf(s)) <= mpf(10) ** -len(s.split(".")[1])


@pytest.mark.parametrize("t", sorted(R2_TABLE_10_1))
def test_inverse_norm_independent_of_cycle_length(t):
    """r2 §4.5 (4.13), r3 §4.5, r2 §10.1 and §10.5: ||B^{-1}||_inf = 1/|c0 - c1| <= 4t/7 for every even
    cycle length (closed-form rows at L = 2, 8, 512, 2^20 and 6, 10); the alternating RHS Y_v = (-1)^v,
    an eigenvector with eigenvalue c0 - c1, attains it (explicit sweeps at L = 2, 8, 512; L = 2^20 in
    the slow test); r2 §10.1 table values."""
    for alpha in (a8(), bm.alpha_from_w(8)):
        for u in (t // 2 - 1, t // 2):
            c0, c1 = bm.retained_coeffs(t, u, alpha)
            inv = 1 / abs(c0 - c1)
            assert inv <= mpf(4 * t) / 7
            for L in (2, 8, 512, 2 ** 20, 6, 10):
                assert abs(bm.cyclic_inverse_norm(c0, c1, L) - inv) < tol(60) * inv
            for L in (2, 8, 512):
                Zs = bm.cyclic_solve(c0, c1, [mpc((-1) ** v) for v in range(L)])
                assert bm.max_abs_diff(Zs, [(-1) ** v / (c0 - c1) for v in range(L)]) < tol(60) * inv
                assert abs(bm.norm_inf(Zs) - inv) < tol(60) * inv
    c0, c1 = bm.retained_coeffs(t, t // 2 - 1, a8())
    for value, s in zip((c0, c1, c0 - c1, 1 / (c0 - c1)), R2_TABLE_10_1[t]):
        assert _matches(value, s)


@pytest.mark.parametrize("L", [2, 4, 8, 16])
def test_cyclic_solve_matches_dense_inverse(L):
    """r2 (4.12)-(4.13), r3 (4.11): the two-pass sweep equals the dense solve in both branches (forward
    c0 > c1; backward c1 > c0 with the one-position RHS shift, spec §7.7), and every row of the dense
    inverse has absolute sum exactly 1/|c0 - c1|."""
    t, alpha = 8, bm.alpha_from_w(8)
    for u in (0, 3, 4, 7):
        c0, c1 = bm.retained_coeffs(t, u, alpha)
        B = mp.matrix(L, L)
        for v in range(L):
            B[v, v] += c0
            B[v, (v - 1) % L] += c1
        Y = bm.random_vector(L, seed=L + u)
        Zd = mp.lu_solve(B, mp.matrix(Y))
        assert bm.max_abs_diff(bm.cyclic_solve(c0, c1, Y), [Zd[v] for v in range(L)]) < tol(60)
        Binv = mp.inverse(B)
        for v in range(L):
            assert abs(mp.fsum(abs(Binv[v, s]) for s in range(L)) - 1 / abs(c0 - c1)) < tol(60)


@settings(max_examples=25)
@given(st.integers(1, 20), st.fractions(Fraction(1, 100), 1, max_denominator=1000),
       st.fractions(Fraction(1, 100), 1, max_denominator=1000), st.integers(0, 10 ** 6))
def test_cyclic_solve_random(half_L, c0, c1, seed):
    """r2 (4.12): B(cyclic_solve(c0, c1, Y)) = Y for random even L and coefficients, both branches."""
    if c0 == c1:
        return
    L = 2 * half_L
    c0, c1 = bm.to_mpf(c0), bm.to_mpf(c1)
    Y = bm.random_vector(L, seed)
    Zs = bm.cyclic_solve(c0, c1, Y)
    scale = 1 / abs(c0 - c1)
    assert bm.max_abs_diff([c0 * Zs[v] + c1 * Zs[v - 1] for v in range(L)], Y) < tol(60) * scale
    assert bm.norm_inf(Zs) <= scale * bm.norm_inf(Y) * (1 + tol(60))


def test_real_kernel_is_singular_at_nyquist():
    """Nyquist singularity of the real kernel (r2 §4): for a real kernel (carrier 0), c0 = c1 at u = t/2, so the
    two-term cyclic system is singular; the negative carrier never has c0 = c1 (r2 §8)."""
    alpha = bm.alpha_from_w(16)
    for t in (2, 8, 64):
        c0, c1 = bm.retained_coeffs(t, t // 2, alpha, carrier=0)
        assert c0 == c1
        with pytest.raises(ZeroDivisionError):
            bm.cyclic_solve(c0, c1, [mpc(1)] * 4)
        assert all(bm.retained_coeffs(t, u, alpha)[0] != bm.retained_coeffs(t, u, alpha)[1] for u in range(t))


def test_endpoint_stopband_r2_10_2():
    """r2 §10.2: sqrt(pi) alpha = 8 (w = 23), t = 8, u = 0, y = 1/16."""
    c0, c1 = bm.retained_coeffs(8, 0, a8())
    psi = bm.omitted_mass(Fraction(1, 16), a8())
    assert _matches(c0, "0.999999628352506") and abs(c1 - mpf("3.7154918617e-7")) < mpf("1e-17")
    assert abs(psi - mpf("9.8308022e-11")) < mpf("1e-17") and abs(1 - c0 - c1 - psi) < tol(70)
    assert abs(mpf("0.120") * mpf(2) ** -23 - mpf("1.4305115e-8")) < mpf("1e-15") and psi < mpf("0.120") * mpf(2) ** -23


def test_positive_carrier_counterexample_r2_10_3():
    """r2 §4.1 and §10.3, r3 §4.1: positive carrier, t = 2, u = 0 (y = -1/4), alpha = 2 sqrt(w ln2/pi):
    omitted mass ~1.24e-6 at w = 64 versus 0.120 2^-64 ~ 6.51e-21; the ratio diverges with w
    (Theta(w^-1/2 2^{-w/4}) by r2 (4.2)).  Also the p = 64 table (bridge synthesis
    item 2: max over u of the omitted alias, in units of 2^-64)."""
    alpha = bm.alpha_from_w(64)
    c0, c1 = bm.retained_coeffs(2, 0, alpha, carrier=1)
    psi = bm.omitted_mass(Fraction(-1, 4), alpha)
    assert abs(1 - c0 - c1 - psi) < tol(70) and abs(psi - mpf("1.24077e-6")) < mpf("1e-11")
    assert abs(mpf("0.120") * mpf(2) ** -64 - mpf("6.51e-21")) < mpf("1e-23")
    assert psi > mpf(10) ** 14 * mpf("0.120") * mpf(2) ** -64
    ratios = []
    for w in (64, 128, 256):
        p = bm.omitted_mass(Fraction(-1, 4), bm.alpha_from_w(w))
        assert p >= mp.erfc(mp.sqrt(w * mp.ln2) / 2) / 2                       # r2 (4.2)
        ratios.append(p / (mpf("0.120") * mpf(2) ** -w))
    assert ratios[1] > mpf(10) ** 13 * ratios[0] and ratios[2] > mpf(10) ** 26 * ratios[1]
    table = {4: ("1.5e7", "5e-13"), 8: ("1564", "3e-7"), 64: ("0.17", "0.01")}
    for t, (pos, neg) in table.items():
        mpos = max(bm.omitted_mass(Fraction(2 * u - 1, 2 * t), alpha) for u in range(t)) * mpf(2) ** 64
        mneg = max(bm.omitted_mass(Fraction(2 * u + 1, 2 * t), alpha) for u in range(t)) * mpf(2) ** 64
        assert abs(mpos / mpf(pos) - 1) < mpf("0.03") and abs(mneg / mpf(neg) - 1) < mpf("0.06")


@pytest.mark.parametrize("w", [8, 16, 64])
def test_positive_carrier_repaired_r3(w):
    """r3 (2.2), (4.3)-(4.10): the positive carrier with alpha = (2t/(t-1)) sqrt(w ln2/pi) satisfies
    Psi < 0.120 2^-w, M > 0.49999999 and |c0 - c1| >= 7/(4t) at all samples y = (u - 1/2)/t."""
    for t in (2, 4, 8, 16, 64):
        alpha = bm.alpha_from_w(w, Fraction(t, t - 1))
        for u in range(t):
            c0, c1 = bm.retained_coeffs(t, u, alpha, carrier=1)
            assert bm.omitted_mass(Fraction(2 * u - 1, 2 * t), alpha) < mpf("0.120") * mpf(2) ** -w
            assert max(c0, c1) > mpf("0.49999999") and abs(c0 - c1) >= mpf(7) / (4 * t)


@pytest.mark.slow
def test_alternating_rhs_cycle_length_2_pow_20():
    """r2 §10.1 with an explicit sweep at L = 2^20 (slow): the solution is (-1)^v/(c0 - c1)."""
    for t in (8, 1024):
        c0, c1 = bm.retained_coeffs(t, t // 2 - 1, a8())
        with mp.workdps(40):
            c0, c1 = +c0, +c1                                  # round to the working precision
            Zs = bm.cyclic_solve(c0, c1, [mpf((-1) ** v) for v in range(2 ** 20)])
            assert max(abs(z * (c0 - c1) - (-1) ** v) for v, z in enumerate(Zs)) < mpf(10) ** -30
