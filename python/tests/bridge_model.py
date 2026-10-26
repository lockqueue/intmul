"""High-precision mpmath model of bridge Lemmas A and B -- TESTS ONLY, non-authoritative.

Not collected by pytest and not part of the package.  Everything is a direct, deliberately naive
transcription of the write-ups, so that it can be checked line by line:

* r2 = bridge derivation r2: Theorem 1 (2.1)-(2.7); §3 Lemma A (3.1)-(3.11); §4 Lemma B
  (4.1)-(4.14); §8 2D drop-in; §10 numerical checks.
* r3 = bridge derivation r3: §3 Lemma A (3.1)-(3.7) (same conventions; Phi, s_h = q_h); §4 Lemma B.
* spec = implementer spec S1 §7.2, §7.3, §7.7.   MS = our manuscript, thm:poisson, eq. (ghat).

Conventions.  Positive normalized DFTs: (F_R x)_u = (1/R) sum_j x_j e^{2 pi i j u / R}.  Continuous
Fourier transform ghat(xi) = int g(s) e^{-2 pi i xi s} ds (MS eq. (ghat)), for which the Poisson formula
r2 (3.3) holds without evenness.  d-dimensional arrays are flat lists in the storage order of
subnlogn.bridge.geometry (index sum_i c_i A_i, c_1 least significant); ``tensor_dft`` returns the 1D
frequency order k = Phi(u).  ``alpha`` and ``carrier`` may be scalars or per-axis sequences (entry h-1
for axis h); carriers are ints or Fractions (carrier -1 = the repaired negative half-bin kernel).

Precision.  Every function computes in the *current* mpmath context; wrap calls in
``with precision():`` (DPS = 80 digits).  Functions refuse to run below MIN_PREC bits, so that a
forgotten context cannot silently produce 53-bit results.
"""

from __future__ import annotations

import itertools
import math
import random
from fractions import Fraction

from mpmath import mp, mpc, mpf

from subnlogn.bridge.geometry import BridgeGeometry

DPS = 80
MIN_PREC = 160


def precision(dps: int = DPS):
    """Context manager setting the model's working precision (mpmath ``workdps``)."""
    return mp.workdps(dps)


def _need_precision() -> None:
    if mp.prec < MIN_PREC:
        raise RuntimeError(f"bridge_model needs mp.prec >= {MIN_PREC} bits (have {mp.prec}); "
                           "wrap the call in `with bridge_model.precision():`")


def to_mpf(v) -> mpf:
    """int / Fraction / mpf -> mpf (a Fraction is rounded once).  Floats are rejected on purpose."""
    if isinstance(v, Fraction):
        return mpf(v.numerator) / v.denominator
    if isinstance(v, (int, mpf)) and not isinstance(v, bool):
        return mpf(v)
    raise TypeError(f"exact value expected (int, Fraction or mpf), got {type(v).__name__}")


def to_mpc(v) -> mpc:
    """mpc passes through; int / Fraction / mpf -> real mpc (mpmath cannot convert a Fraction itself)."""
    return v if isinstance(v, mpc) else mpc(to_mpf(v))


def _axis(v, h: int):
    """Per-axis parameter: v[h-1] for a sequence, v itself for a scalar."""
    return v[h - 1] if isinstance(v, (tuple, list)) else v


def random_vector(R: int, seed: int, bits: int = 20) -> list:
    """Deterministic complex test vector, components (a + i b) 2^-bits with |a|, |b| <= 2^bits."""
    rng = random.Random(seed)
    one = 1 << bits
    return [mpc(mpf(rng.randint(-one, one)) / one, mpf(rng.randint(-one, one)) / one) for _ in range(R)]


def norm_inf(X) -> mpf:
    return max(abs(v) for v in X)


def max_abs_diff(X, Y) -> mpf:
    assert len(X) == len(Y)
    return max(abs(a - b) for a, b in zip(X, Y))


# ----------------------------------------------------------------------------- kernel and its FT
def G(xi, alpha) -> mpf:
    """G_alpha(xi) = (1/2)[erf(a(xi + 1/2)) - erf(a(xi - 1/2))], a = sqrt(pi) alpha: the Fourier transform
    of sinc(s) e^{-pi s^2/alpha^2} (MS eq. (ghat); r2 (4.3); r3 §4).  Even in xi; evaluated via erfc for
    |xi| > 1/2, so tails keep full relative precision."""
    _need_precision()
    x = abs(to_mpf(xi))
    a = mp.sqrt(mp.pi) * to_mpf(alpha)
    half = mpf(1) / 2
    if x <= half:
        return (mp.erf(a * (x + half)) + mp.erf(a * (half - x))) / 2
    return (mp.erfc(a * (x - half)) - mp.erfc(a * (x + half))) / 2


_G_CACHE: dict = {}


def ghat(xi, t: int, alpha, carrier=-1) -> mpf:
    """FT of :func:`kernel`: ghat(xi) = G_alpha(xi - carrier/(2t)).  carrier = -1 gives
    ghat_h(xi) = G_alpha(xi + 1/(2 t_h)) (r2 display after (2.1); r3 (2.1)); +1 is the refuted positive
    carrier (r2 §4.1, r3 (2.2)); 0 is the manuscript's real kernel (MS eq. (ghat))."""
    shift = Fraction(carrier) / (2 * t)
    if isinstance(xi, (int, Fraction)):
        key = (Fraction(xi) - shift, to_mpf(alpha), mp.prec)
        if key not in _G_CACHE:
            _G_CACHE[key] = G(key[0], alpha)
        return _G_CACHE[key]
    return G(to_mpf(xi) - to_mpf(shift), alpha)


def kernel(s, t: int, alpha, carrier=-1) -> mpc:
    """g(s) = e^{carrier pi i s/t} sinc(s) e^{-pi s^2/alpha^2}, sinc(s) = sin(pi s)/(pi s)
    (r2 (2.1) for carrier -1; r3 (2.1)-(2.2); MS eq. (sinc-gauss) for carrier 0).  For rational s the
    phase argument carrier*s/t is formed exactly."""
    _need_precision()
    sm = to_mpf(s)
    env = mp.sincpi(sm) * mp.exp(-mp.pi * sm * sm / to_mpf(alpha) ** 2)
    c = Fraction(carrier)
    if c == 0:
        return mpc(env)
    ph = to_mpf(c * Fraction(s) / t) if isinstance(s, (int, Fraction)) else to_mpf(c) * sm / t
    return mp.expjpi(ph) * env


_FOLD_CACHE: dict = {}


def folded(delta, t: int, alpha, carrier=-1, M: int = 60) -> list:
    """One period [H_delta(0), ..., H_delta(t-1)] of the folded filter H_delta(a) = sum_l g(a + delta - l t)
    (r2 (3.1); r3 §3.1), t-periodic in the integer a.  The *modulated* kernel is folded (r2 §4.7: the
    carrier is antiperiodic under s -> s - t).  Terms with |a + delta - l t| > M are dropped; the dropped
    part of each tap is below :func:`folded_tail_bound`."""
    delta, c = Fraction(delta), Fraction(carrier)
    key = (delta, t, to_mpf(alpha), c, M, mp.prec)
    if key not in _FOLD_CACHE:
        out = []
        for a in range(t):
            z = a + delta
            ls = range(math.ceil((z - M) / t), math.floor((z + M) / t) + 1)
            out.append(mp.fsum(kernel(z - l * t, t, alpha, c) for l in ls))
        _FOLD_CACHE[key] = out
    return _FOLD_CACHE[key]


def folded_tail_bound(t: int, alpha, M: int) -> mpf:
    """2 e^{-pi M^2/alpha^2} / (pi M (1 - e^{-2 pi M t/alpha^2})) >= the dropped part of a folded tap
    (|g(s)| <= e^{-pi s^2/alpha^2}/(pi |s|); dropped points lie beyond +-M with spacing t)."""
    a2 = to_mpf(alpha) ** 2
    return 2 * mp.exp(-mp.pi * M * M / a2) / (mp.pi * M * (1 - mp.exp(-2 * mp.pi * M * t / a2)))


# ----------------------------------------------------------------------------- spreading (Lemma A)
def spread(geom: BridgeGeometry, x, alpha, carrier=-1, M: int = 60, order: str = "chronological") -> list:
    """U = S_2 S_3 ... S_d x (r2 §3.1, r3 (3.1), spec §7.2): axes in chronological order h = d, ..., 2;
        (S_h X)_{.., k_h, ..} = sum_{j_h} X_{.., j_h, ..} H_{h, delta_h}(j_h - k_h),
    with delta_h = geom.delta(h, base) from the lower digits of the line's base -- still the original
    j_1..j_{h-1}, since those axes are not spread yet.  order="ascending" (h = 2, ..., d, using the digits
    then present) violates r2 (3.2); it exists only as a negative test."""
    hs = {"chronological": range(geom.d, 1, -1), "ascending": range(2, geom.d + 1)}[order]
    X = [to_mpc(v) for v in x]
    assert len(X) == geom.R
    for h in hs:
        th = geom.tt(h)
        Y = [None] * geom.R
        for line in geom.line_indices(h):
            H = folded(geom.delta(h, line[0]), th, _axis(alpha, h), _axis(carrier, h), M)
            for kh in range(th):
                Y[line[kh]] = mp.fsum(X[line[jh]] * H[(jh - kh) % th] for jh in range(th))
        X = Y
    return X


def spread_explicit(geom: BridgeGeometry, x, alpha, carrier=-1, M: int = 60) -> list:
    """r2 (3.2) / r3 (3.1) evaluated directly:
    U_k = sum_{j : j_1 = k_1} x_j prod_{h=2}^d H_{h, delta_h(j)}(j_h - k_h)."""
    out = []
    for kidx in range(geom.R):
        kd = geom.digits(kidx)
        terms = []
        for j in range(geom.R):
            jd = geom.digits(j)
            if jd[0] != kd[0]:
                continue
            term = to_mpc(x[j])
            for h in range(2, geom.d + 1):
                th = geom.tt(h)
                H = folded(geom.delta(h, j), th, _axis(alpha, h), _axis(carrier, h), M)
                term *= H[(jd[h - 1] - kd[h - 1]) % th]
            terms.append(term)
        out.append(mp.fsum(terms))
    return out


# ----------------------------------------------------------------------------- DFTs
def _roots(n: int) -> list:
    """e^{2 pi i r/n}, r = 0..n-1, with exact rational arguments."""
    return [mp.expjpi(to_mpf(Fraction(2 * r, n))) for r in range(n)]


def dft(x) -> list:
    """(F_R x)_u = (1/R) sum_j x_j e^{2 pi i j u/R}: the positive normalized DFT (r2 Input 1; MS)."""
    _need_precision()
    R = len(x)
    w = _roots(R)
    return [mp.fsum(x[j] * w[(j * u) % R] for j in range(R)) / R for u in range(R)]


def tensor_dft(geom: BridgeGeometry, U) -> list:
    """(F_t U)_u = (1/R) sum_c U_c e^{2 pi i sum_i c_i u_i / t_i} over all d axes, axis 1 included
    (r2 (3.4), r3 (3.4)); computed axis by axis in storage order, returned in 1D frequency order:
    out[Phi(u)] = (F_t U)_u (r3 (3.7): "tensor frequencies are identified through Phi")."""
    _need_precision()
    X = [to_mpc(v) for v in U]
    for h in range(1, geom.d + 1):
        th = geom.tt(h)
        w = _roots(th)
        Y = [None] * geom.R
        for line in geom.line_indices(h):
            for uh in range(th):
                Y[line[uh]] = mp.fsum(X[line[c]] * w[(c * uh) % th] for c in range(th)) / th
        X = Y
    out = [None] * geom.R
    for s, k in enumerate(geom.storage_to_freq()):
        out[k] = X[s]
    return out


def tensor_dft_direct(geom: BridgeGeometry, U) -> list:
    """Same as :func:`tensor_dft` by the defining multi-sum (phases reduced exactly mod 1)."""
    _need_precision()
    R = geom.R
    digs = [geom.digits(s) for s in range(R)]
    out = [None] * R
    for us in range(R):
        u = digs[us]
        terms = []
        for c, cd in enumerate(digs):
            ph = sum((Fraction(ci * ui, ti) for ci, ui, ti in zip(cd, u, geom.t)), Fraction(0)) % 1
            terms.append(U[c] * mp.expjpi(to_mpf(2 * ph)))
        out[geom.phi(u)] = mp.fsum(terms) / R
    return out


# ----------------------------------------------------------------------------- alias operators
def alias_coeff(geom: BridgeGeometry, h: int, u: int, m: int, alpha, carrier=-1) -> mpf:
    """a_h(u, m) = ghat_h(u/t_h - m) (r2 (3.8), r3 (3.6)); for carrier -1 this is
    G_alpha((u + 1/2)/t_h - m) (r2 (2.3)).  c_0 = a_h(u, 0), c_1 = a_h(u, 1) (r2 (4.5), spec §7.7)."""
    th = geom.tt(h)
    return ghat(Fraction(u, th) - m, th, _axis(alpha, h), _axis(carrier, h))


class AliasOp:
    """Sparse R x R operator: (A Z)_k = sum over (src, coeff) in rows[k] of coeff * Z[src]."""

    def __init__(self, R: int, rows: list):
        self.R, self.rows = R, rows

    def __call__(self, Z) -> list:
        return [mp.fsum(c * Z[s] for s, c in row) for row in self.rows]

    def matrix(self):
        Mx = mp.matrix(self.R, self.R)
        for k, row in enumerate(self.rows):
            for s, c in row:
                Mx[k, s] += c
        return Mx

    def norm_inf(self) -> mpf:
        """max_k sum_s |A_{k s}| (coefficients of equal src merged first)."""
        best = mpf(0)
        for row in self.rows:
            merged: dict = {}
            for s, c in row:
                merged[s] = merged.get(s, 0) + c
            best = max(best, mp.fsum(abs(c) for c in merged.values()))
        return best


def alias_op(geom: BridgeGeometry, h: int, alpha, carrier=-1, retain=None, mmax: int = 6) -> AliasOp:
    """A_h of r2 (2.3)/(3.8), r3 (3.6), truncated to |m| <= mmax (retain=None), or B_h (retain={0, 1};
    r2 Thm 1); any finite set of m may be retained:
        (A_h Z)_k = sum_m ghat_h(u_h(k)/t_h - m) Z_{(k - m q_h) mod R}."""
    ms = sorted(retain) if retain is not None else list(range(-mmax, mmax + 1))
    th, qh, R = geom.tt(h), geom.q(h), geom.R
    coeff = {(u, m): alias_coeff(geom, h, u, m, alpha, carrier) for u in range(th) for m in ms}
    rows = [tuple(((k - m * qh) % R, coeff[geom.u_digit(h, k), m]) for m in ms) for k in range(R)]
    return AliasOp(R, rows)


def apply_chain(ops, Z) -> list:
    """Right-to-left composition: apply_chain([P_2, ..., P_d], Z) = P_2 P_3 ... P_d Z, so the LAST
    operator acts first (r2 (2.2): A_2 A_3 ... A_d F_R x, A_d acting first)."""
    for op in reversed(ops):
        Z = op(Z)
    return Z


def alias_sum(geom: BridgeGeometry, Z, alpha, carrier=-1, mmax: int = 2) -> list:
    """r2 (3.7) / r3 (3.5) as a direct multi-index sum over m = (m_2..m_d) in [-mmax, mmax]^{d-1}:
    Y_k = sum_m [prod_{h>=2} ghat_h(u_h(k)/t_h - m_h)] Z_{(k - sum_h m_h q_h) mod R}, k = Phi(u)."""
    hs = range(2, geom.d + 1)
    ms = range(-mmax, mmax + 1)
    a = {(h, u, m): alias_coeff(geom, h, u, m, alpha, carrier) for h in hs for u in range(geom.tt(h)) for m in ms}
    out = []
    for k in range(geom.R):
        u = geom.phi_inv(k)
        terms = []
        for mv in itertools.product(ms, repeat=geom.d - 1):
            c = mpf(1)
            for h, m in zip(hs, mv):
                c *= a[h, u[h - 1], m]
            terms.append(c * Z[(k - sum(m * geom.q(h) for h, m in zip(hs, mv))) % geom.R])
        out.append(mp.fsum(terms))
    return out


def lemma_A_lhs(geom, x, alpha, carrier=-1, M: int = 60, order: str = "chronological") -> list:
    """F_t S_2 ... S_d x, in 1D frequency order (left side of r2 (2.2) / r3 (3.7))."""
    return tensor_dft(geom, spread(geom, x, alpha, carrier, M, order))


def lemma_A_rhs(geom, x, alpha, carrier=-1, mmax: int = 6, reverse: bool = False) -> list:
    """A_2 A_3 ... A_d F_R x (right side of r2 (2.2) / r3 (3.7)); reverse=True computes the wrong order
    A_d ... A_2 F_R x (A_2 acting first)."""
    ops = [alias_op(geom, h, alpha, carrier, None, mmax) for h in range(2, geom.d + 1)]
    return apply_chain(ops[::-1] if reverse else ops, dft(x))


# ----------------------------------------------------------------------------- deconvolution (Lemma B)
def _forward_sweep(b, rho) -> list:
    """Z_v = b_v + rho Z_{v-1} on Z/LZ: prefix pass P = sum_{s<L} rho^s b_{L-1-s}, closure
    Z_{L-1} = P / (1 - rho^L), second pass (r2 §4.6 steps 1-4; spec §7.7 solve_forward_cycle)."""
    L = len(b)
    P = b[0]
    for i in range(1, L):
        P = b[i] + rho * P
    Z = [None] * L
    Z[L - 1] = prev = P / (1 - rho ** L)
    for i in range(L - 1):
        Z[i] = prev = b[i] + rho * prev
    return Z


def cyclic_solve(c0, c1, Y) -> list:
    """Solve c0 Z_v + c1 Z_{v-1} = Y_v on Z/LZ (r2 (4.12), r3 §4.5), exactly up to working precision.
    |c0| > |c1|: rho = -c1/c0, Z_v = Y_v/c0 + rho Z_{v-1} (closed form r3 (4.11)).
    |c1| > |c0|: rho = -c0/c1, Z_v - rho Z_{v+1} = Y_{v+1}/c1, solved by the forward sweep on the
    reversed cycle with the one-position RHS shift (spec §7.7, steps 1-4).  |c0| = |c1| is singular."""
    L = len(Y)
    if abs(c0) > abs(c1):
        return _forward_sweep([y / c0 for y in Y], -c1 / c0)
    if abs(c1) > abs(c0):
        W = _forward_sweep([Y[(L - i) % L] / c1 for i in range(L)], -c0 / c1)
        return [W[L - 1 - v] for v in range(L)]
    raise ZeroDivisionError("|c0| = |c1|: singular cyclic system (the Nyquist column of a real kernel)")


def deconvolve_axis(geom: BridgeGeometry, h: int, alpha, Y, carrier=-1) -> list:
    """B_h^{-1} Y, cycle by cycle: cycles k = v q_h + s of length A_h, coefficients
    c0 = a_h(u_h, 0), c1 = a_h(u_h, 1) constant on each cycle (r2 §4.5, spec §7.7)."""
    out = [None] * geom.R
    for cyc in geom.cycles(h):
        u = geom.u_digit(h, cyc[0])
        c0 = alias_coeff(geom, h, u, 0, alpha, carrier)
        c1 = alias_coeff(geom, h, u, 1, alpha, carrier)
        for k, z in zip(cyc, cyclic_solve(c0, c1, [Y[k] for k in cyc])):
            out[k] = z
    return out


def deconvolve(geom: BridgeGeometry, Y, alpha, carrier=-1, order: str = "chronological") -> list:
    """(B_2 B_3 ... B_d)^{-1} Y = B_d^{-1} ... B_2^{-1} Y: solves applied in chronological order
    2, 3, ..., d (r2 (3.9), r3 §3.3).  order="reversed" applies d, ..., 2 (wrong; negative test)."""
    hs = {"chronological": range(2, geom.d + 1), "reversed": range(geom.d, 1, -1)}[order]
    for h in hs:
        Y = deconvolve_axis(geom, h, alpha, Y, carrier)
    return Y


def chain_inverse_norm(geom: BridgeGeometry, alpha, carrier=-1) -> mpf:
    """||(B_2 ... B_d)^{-1}||_inf from its columns (B_2 ... B_d)^{-1} e_k (r2 (2.6), (4.14))."""
    R = geom.R
    rowsum = [mpf(0)] * R
    for k in range(R):
        col = deconvolve(geom, [mpc(1) if i == k else mpc(0) for i in range(R)], alpha, carrier)
        for i in range(R):
            rowsum[i] += abs(col[i])
    return max(rowsum)


# ----------------------------------------------------------------------------- Lemma B constants
def alpha_from_w(w: int, factor=1) -> mpf:
    """alpha = factor * 2 sqrt(w ln 2 / pi): r2 Thm 1 admits factor in [1, 2]; r3 (2.1) uses factor 1;
    the repaired positive carrier r3 (2.2) uses factor t/(t-1)."""
    _need_precision()
    return to_mpf(Fraction(factor)) * 2 * mp.sqrt(w * mp.ln2 / mp.pi)


def retained_coeffs(t: int, u: int, alpha, carrier=-1) -> tuple:
    """(c0, c1) = (G(y), G(y - 1)) with y = u/t - carrier/(2t); y = (u + 1/2)/t for carrier -1
    (r2 (4.5), (8.2); spec §7.7)."""
    return ghat(Fraction(u, t), t, alpha, carrier), ghat(Fraction(u, t) - 1, t, alpha, carrier)


def omitted_mass(y, alpha) -> mpf:
    """Psi(y) = (1/2) erfc(a(y + 1/2)) + (1/2) erfc(a(3/2 - y)), a = sqrt(pi) alpha: the exact alias mass
    sum_{m not in {0,1}} G_alpha(y - m) dropped by B_h (r2 (4.1), (4.5); r3 (4.1))."""
    _need_precision()
    y, a = to_mpf(y), mp.sqrt(mp.pi) * to_mpf(alpha)
    return (mp.erfc(a * (y + mpf(1) / 2)) + mp.erfc(a * (mpf(3) / 2 - y))) / 2


def alias_tail_norm(t: int, alpha, carrier=-1) -> mpf:
    """||A_h - B_h||_inf = max_u Psi(y_u), y_u = u/t - carrier/(2t) (= (u + 1/2)/t for carrier -1): every
    row of A_h - B_h holds the dropped coefficients G(y_u - m), m not in {0, 1}, all positive
    (r2 (2.4), (4.5)-(4.6); r3 (4.5))."""
    return max(omitted_mass(Fraction(u, t) - Fraction(carrier) / (2 * t), alpha) for u in range(t))


def cyclic_inverse_norm(c0, c1, L: int) -> mpf:
    """||B^{-1}||_inf for (B Z)_v = c0 Z_v + c1 Z_{v-1} on Z/LZ, L even (r2 §4.5, (4.13); r3 (4.11)):
    every row of B^{-1} is gamma rho^s / M (s = 0..L-1, rho = -q, q = min/M, M = max(c0, c1),
    gamma = 1/(1 - rho^L)), so its absolute sum is S_L gamma / M with S_L = sum_{s<L} q^s.  S_L and q^L
    are computed by doubling (S_2n = S_n (1 + q^n)) for L a power of two, else by direct summation --
    deliberately NOT through S_L = (1 - q^L)/(1 - q), so that the L-independence (= 1/|c0 - c1|, the
    cancellation r2 (4.19)) is a genuine check."""
    _need_precision()
    M = max(c0, c1)
    q = min(c0, c1) / M
    if L & (L - 1) == 0:
        S, qn, n = mpf(1), q, 1                      # S = S_n, qn = q^n
        while n < L:
            S, qn, n = S * (1 + qn), qn * qn, 2 * n
    else:
        S, qn = mp.fsum(q ** s for s in range(L)), q ** L
    return S / ((1 - qn) * M)
