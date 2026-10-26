"""Lemma 16 synthetic transforms over R_r = C[y]/(y^r + 1) with DIRECT layers (SPEC §5.3, §5.11;
Pr (27)-(29), L2698-2805, L2936-3035).

Data: M = prod_i t_i records (D = d - 1 axes), each a polynomial of degree < r stored as two lists
(re, im) of integer numerators; the whole array shares one scale (fractional bits).  Record index
x is its n-bit address (physical bit position 0 = most significant, see :mod:`.layout`).

Forward procedure, exact counterpart L·B·F_t^- (F_t^- = tensor of (F_t^- z)_j = (1/t) sum_k
w_t^{-jk} z_k, w_t = y^{2r/t}; B = per-axis bit reversal; L = the layout):
    apply L;  for h = l-1, l-2, ..., 0:  x <- Q_p(J_E H_h x)
Opposite procedure, exact counterpart F_t^+·B^{-1}·L^{-1}:
    for h = 0, 1, ..., l-1:  x <- Q_p(H_h J_E^{-1} x);  apply L^{-1}
H_h = tensor over the participating axes (long axes only at h = l-1, all axes for h <= l-2;
[Pr L2936-2939]) of H0 = (1/2)[[1, 1], [1, -1]] on slot (i, h); J_E multiplies each record by
y^E, E = -sum_i (2r/u_i) b_i k_i mod 2r (eq. (29)), u_i = 2^{h+1}, b_i = the branch bit in slot
(i, h), k_i = sum_{v<h} 2^v x_v from the still unprocessed lower slots.  Q_p truncates every real
and imaginary numerator toward zero to the grid 2^-p (SPEC §1.4): exactly one truncation per round.

M3 "direct layer" mode (SPEC §5.11): the chunk rounds (b <= h <= l-2), which the full algorithm
sends to Proposition 14, use the Prop 14 base case -- individual exact H0 factors on the selected
bits followed by one Q_p -- so every round computes the same Q_p(J_E H x) (J_E commutes with Q_p,
Pr L3006-3012).  With ``truncate=False`` no rounding happens (the exact counterpart; test oracle).
Error of each procedure < sqrt(2) l 2^-p with disk-grid outputs (Lemma 16; reading R5).
"""

from __future__ import annotations

from ..checks import require
from ..fixedpoint import shr_trunc
from .layout import LayoutPlan, execute_layout, layout_plan, permute_records

__all__ = ["monomial_shift", "synthetic_forward", "synthetic_opposite", "Synth"]


def monomial_shift(re: list[int], im: list[int], E: int) -> tuple[list[int], list[int]]:
    """y^E z mod (y^r + 1) for any integer E (Pr L3000-3005; SPEC §5.4): split before r - s,
    tail first with negation, then the common sign (-1)^e, where E = e r + s, 0 <= s < r."""
    r = len(re)
    e, s = divmod(E, r)
    if s:
        re = [-v for v in re[r - s:]] + re[:r - s]
        im = [-v for v in im[r - s:]] + im[:r - s]
    if e & 1:
        re = [-v for v in re]
        im = [-v for v in im]
    return re, im


class Synth:
    """Precomputed address data of the synthetic transforms for axes t, l = lg r, chunk width K.

    ``layer(recs, sel_bits, scale, p, truncate) -> (recs, scale)`` is the Proposition 14 call used
    in the chunk rounds; the default is its base case (individual exact C kernels via identity
    (18), then one Q_p; SPEC §4.9, §5.11).  The M6 network layer plugs in here and must agree bit
    for bit."""

    def __init__(self, t: tuple[int, ...], ell: int, K: int, layer=None, movement=None, inst=None):
        self.t = tuple(t)
        self.D = len(t)
        self.ell = ell
        self.r = 1 << ell
        self.K = K
        self.a = [ti.bit_length() - 1 for ti in t]
        self.plan: LayoutPlan = layout_plan(self.t, ell, K)
        self.n = self.plan.n
        pos = self.plan.pos
        # bit index (from the LSB of the address) of named slot (i, v) after L
        self.bit = {s: self.n - 1 - pos[s] for s in pos}
        self.fwd_map = self.plan.address_map()
        self.inv_map = self.plan.address_map(inverse=True)
        if layer is None:
            from ..m6.prop14 import simultaneous_H0_base
            layer = simultaneous_H0_base
        self.layer = layer
        # ``movement``: None = L and L^{-1} as index maps (M3 mode, DEVIATIONS D9); a chunk-exchange
        # callable (Lemma 12, ``m6.lemma13.swap_via_lemma12``) = execute the plan's Lemma 3 moves and
        # Lemma 12 exchanges on the record stream (SPEC §5.2; ``layout.execute_layout``).
        self.movement = movement
        self.inst = inst

    def chunk_rho(self, h: int) -> int:
        """Selected offset rho (from the chunk's LSB) of slot h in its K-bit chunk: chunk j covers
        h = l-2-(j-1)K down to l-1-jK in decreasing physical order (SPEC §5.2), so
        rho = h - (l - 1 - jK); checked against the layout for every axis."""
        j = (self.ell - 2 - h) // self.K + 1
        low = self.ell - 1 - j * self.K
        rho = h - low
        require(all(self.bit[(i, h)] - self.bit[(i, low)] == rho for i in range(self.D)),
                "chunk offset rho disagrees with the layout (SPEC §5.2)")
        return rho

    def _layer(self, recs, h, axes, scale, p, truncate):
        """One Prop 14 call on the chunk round at position h: the D selected bits are physical
        chunks (i, j) of the layout, consecutive across axes (SPEC §4.0, §5.3)."""
        sel = [self.bit[(i, h)] for i in axes]
        return self.layer(recs, sel, scale, p, truncate, K=self.K, rho=self.chunk_rho(h))

    def is_chunk_round(self, h: int) -> bool:
        """Rounds on the q K remaining chunks (b <= h <= l-2) use Proposition 14 (SPEC §5.3)."""
        return self.plan.b <= h <= self.ell - 2

    def axes(self, h: int) -> list[int]:
        """Participating axes of the round at named position h [Pr L2936-2939]."""
        return [i for i in range(self.D) if self.a[i] > h]

    def exponent(self, x: int, h: int, axes: list[int]) -> int:
        """E of eq. (29) for the record at address x (after L) in the round at position h."""
        E = 0
        sh = self.ell - h            # 2r / u = 2r / 2^{h+1} = r / 2^h = 2^{l-h}
        for i in axes:
            if (x >> self.bit[(i, h)]) & 1:
                k = 0
                for v in range(h):
                    k |= ((x >> self.bit[(i, v)]) & 1) << v
                E -= k << sh
        return E % (2 * self.r)

    def _hadamard(self, recs, h, axes):
        """Exact unnormalized tensor butterfly on the slots (i, h), i in axes: the numerators of
        2^{D'} H x (so the scale grows by D' = len(axes)).  One pass per axis bit."""
        out = list(recs)
        for i in axes:
            m = 1 << self.bit[(i, h)]
            for x in range(len(out)):
                if not x & m:
                    (ar, ai), (br, bi) = out[x], out[x | m]
                    out[x] = ([u + v for u, v in zip(ar, br)], [u + v for u, v in zip(ai, bi)])
                    out[x | m] = ([u - v for u, v in zip(ar, br)], [u - v for u, v in zip(ai, bi)])
        return out

    def forward(self, recs, scale: int, p: int, truncate: bool = True):
        """Forward procedure (module docstring).  Input numerators at ``scale`` (= p for the
        algorithm); returns (records, scale') with scale' = p if truncating."""
        recs = self._apply_L(recs, inverse=False)
        for h in range(self.ell - 1, -1, -1):
            axes = self.axes(h)
            if self.is_chunk_round(h):
                # layer returns Q_p(H x); then J_E (J_E Q_p(Hx) = Q_p(J_E H x), Pr L3006-3010)
                recs, scale = self._layer(recs, h, axes, scale, p, truncate)
                recs = [monomial_shift(re, im, self.exponent(x, h, axes)) for x, (re, im) in enumerate(recs)]
            else:
                # prefix rounds: individual exact H0 factors, the monomial, one Q_p (Pr L2976-2986)
                recs = self._hadamard(recs, h, axes)
                scale += len(axes)
                recs = [monomial_shift(re, im, self.exponent(x, h, axes)) for x, (re, im) in enumerate(recs)]
                if truncate:
                    recs, scale = _truncate(recs, scale, p), p
        return recs, scale

    def opposite(self, recs, scale: int, p: int, truncate: bool = True):
        """Opposite procedure (module docstring): consumes the retained order L·B."""
        for h in range(self.ell):
            axes = self.axes(h)
            recs = [monomial_shift(re, im, -self.exponent(x, h, axes)) for x, (re, im) in enumerate(recs)]
            if self.is_chunk_round(h):
                recs, scale = self._layer(recs, h, axes, scale, p, truncate)
            else:
                recs = self._hadamard(recs, h, axes)
                scale += len(axes)
                if truncate:
                    recs, scale = _truncate(recs, scale, p), p
        return self._apply_L(recs, inverse=True), scale

    def _apply_L(self, recs, inverse: bool):
        """L (forward) or L^{-1} (end of the opposite procedure) on the complete record list."""
        if self.movement is None:
            return permute_records(recs, self.inv_map if inverse else self.fwd_map)
        return execute_layout(self.plan, recs, self.movement, inverse=inverse, inst=self.inst)


def _truncate(recs, scale: int, p: int):
    """Q_p: truncate every real and imaginary numerator toward zero from ``scale`` to p."""
    s = scale - p
    if s == 0:
        return recs
    return [([shr_trunc(v, s) for v in re], [shr_trunc(v, s) for v in im]) for re, im in recs]


def synthetic_forward(recs, t, ell, K, p, truncate=True):
    """Convenience wrapper: forward procedure on grid-p records (exact counterpart L·B·F_t^-)."""
    return Synth(t, ell, K).forward(recs, p, p, truncate)


def synthetic_opposite(recs, t, ell, K, p, truncate=True):
    """Convenience wrapper: opposite procedure (exact counterpart F_t^+·B^{-1}·L^{-1})."""
    return Synth(t, ell, K).opposite(recs, p, p, truncate)
