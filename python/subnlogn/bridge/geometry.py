"""Exact index geometry of the d-dimensional fractional-shift bridge (bridge Lemma A conventions).

Pure ``int`` / ``fractions.Fraction``; no floating point anywhere.  Sources:

* **r2**   = bridge derivation r2: Theorem 1, §3.1-§3.4 (Lemma A), §4.5 (cycles of B_h).
* **r3**   = bridge derivation r3: §2.1, §3.1-§3.4 (Lemma A in the Phi / s_h notation).
* **spec** = implementer spec S1: §7.1 (mixed-radix indices), §7.7 (cycles).
* **MS**   = the companion manuscript [MS]: Thm ``thm:poisson`` (the case d = 2) and the
  listing lines 737-738 (the 2D split).

Notation (1-based in h, exactly as in the write-ups; r2 Theorem 1, r3 §2.1)::

    t_1, ..., t_d   axis lengths, each an even power of two (2, 4, 8, ...)
    R   = prod_i t_i = 2^K
    A_h = prod_{i<h} t_i                  h = 1..d+1;  A_1 = 1, A_{d+1} = R
    Q_h = R / (A_h t_h) = R / A_{h+1}     frequency place value, h = 1..d;  Q_d = 1
    q_h = R / A_h                         alias shift of A_h and B_h (r2 (2.3); r3 calls it s_h)

* spatial index      j = sum_i j_i A_i, j_1 least significant           (r2 §3.1, r3 §3.1)
* fractional shift   delta_h(j) = (sum_{i<h} j_i A_i) / A_h, h >= 2      (r2 §3.1, r3 §3.1)
* frequency map      Phi(u) = k(u) = sum_i u_i Q_i, u_d least significant (r2 Thm 1, r3 (3.2))

Storage convention (fixed for the whole bridge): every d-dimensional array (spatial input,
spread array, tensor-frequency output) is a flat list indexed by sum_i c_i A_i with c_1 least
significant (c_i = j_i, k_i or u_i).  The tensor DFT output stored at position sum_i u_i A_i is the
1D frequency Phi(u), in which u_1 is the MOST significant digit (:meth:`BridgeGeometry.storage_to_freq`).
For d = 2 this is the manuscript's layout: j = j_1 + t_1 j_2 and Phi(u) = u_2 + r u_1 with r = t_2
(MS ``thm:poisson``, eq. (poisson-bridge)).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Sequence

__all__ = ["BridgeGeometry", "balanced_factors"]


def _is_axis_length(v: object) -> bool:
    """True iff v is an int (not bool) that is a power of two >= 2 (r2 Thm 1: "even power of two")."""
    return isinstance(v, int) and not isinstance(v, bool) and v >= 2 and (v & (v - 1)) == 0


@dataclass(frozen=True)
class BridgeGeometry:
    """Index geometry of the bridge with axis lengths ``t = (t_1, ..., t_d)`` (r2 Thm 1, r3 §2.1).

    ``t[0]`` is t_1 (the axis that is never spread), ``t[d-1]`` is t_d (spread first).  Each t_i
    must be a power of two >= 2; d >= 1 is accepted (d = 1 is the trivial bridge F_t = F_R; the
    bridge proper has d >= 2).  ``d``, ``R`` and ``K = lg R`` are attributes; ``A(h)``, ``Q(h)``,
    ``q(h)`` and ``tt(h)`` take the 1-based axis number h.  Equality and hashing depend on ``t`` only.
    """

    t: tuple[int, ...]
    d: int = field(init=False, compare=False)
    R: int = field(init=False, compare=False)
    K: int = field(init=False, compare=False)
    _A: tuple[int, ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if isinstance(self.t, (str, bytes)):
            raise TypeError("t must be a sequence of ints")
        t = tuple(self.t)
        if not t:
            raise ValueError("BridgeGeometry needs d >= 1 axes")
        for i, v in enumerate(t):
            if not _is_axis_length(v):
                raise ValueError(f"t_{i + 1} = {v!r} is not a power of two >= 2")
        t = tuple(int(v) for v in t)
        A = [1]
        for v in t:
            A.append(A[-1] * v)
        object.__setattr__(self, "t", t)
        object.__setattr__(self, "_A", tuple(A))          # _A[h-1] = A_h, h = 1..d+1
        object.__setattr__(self, "d", len(t))
        object.__setattr__(self, "R", A[-1])
        object.__setattr__(self, "K", A[-1].bit_length() - 1)

    # ------------------------------------------------------------------ validation helpers
    def _h(self, h: int, lo: int, hi: int, what: str) -> int:
        if not (isinstance(h, int) and not isinstance(h, bool) and lo <= h <= hi):
            raise ValueError(f"{what}: axis h = {h!r} outside {lo}..{hi} (d = {self.d})")
        return h

    def _k(self, k: int, what: str) -> int:
        if not (isinstance(k, int) and not isinstance(k, bool) and 0 <= k < self.R):
            raise ValueError(f"{what}: index {k!r} outside 0..{self.R - 1}")
        return k

    def _digits_ok(self, c: Sequence[int], what: str) -> tuple[int, ...]:
        c = tuple(c)
        if len(c) != self.d:
            raise ValueError(f"{what}: expected {self.d} digits, got {len(c)}")
        for i, (ci, ti) in enumerate(zip(c, self.t)):
            if not (isinstance(ci, int) and not isinstance(ci, bool) and 0 <= ci < ti):
                raise ValueError(f"{what}: digit {i + 1} = {ci!r} outside 0..{ti - 1}")
        return c

    # ------------------------------------------------------------------ place values
    def tt(self, h: int) -> int:
        """t_h, h = 1..d (r2 Thm 1)."""
        return self.t[self._h(h, 1, self.d, "tt") - 1]

    def A(self, h: int) -> int:
        """A_h = prod_{i<h} t_i, h = 1..d+1; A_1 = 1, A_{d+1} = R (r2 Thm 1, r3 §2.1)."""
        return self._A[self._h(h, 1, self.d + 1, "A") - 1]

    def Q(self, h: int) -> int:
        """Q_h = R / (A_h t_h) = R / A_{h+1}, h = 1..d: place value of u_h in Phi (r2 Thm 1; r3 (3.2)).
        Q_d = 1 and Q_h = q_{h+1}."""
        return self.R // self._A[self._h(h, 1, self.d, "Q")]

    def q(self, h: int) -> int:
        """q_h = R / A_h, h = 1..d+1: the alias shift k -> k - m q_h of A_h, B_h (r2 Thm 1, (2.3);
        r3 (3.6) calls it s_h).  q_1 = R (a trivial shift), q_{d+1} = 1, and q_h = Q_{h-1}."""
        return self.R // self._A[self._h(h, 1, self.d + 1, "q") - 1]

    # ------------------------------------------------------------------ spatial digits
    def digits(self, j: int) -> tuple[int, ...]:
        """(j_1, ..., j_d) with j = sum_i j_i A_i, 0 <= j_i < t_i, j_1 least significant
        (r2 §3.1, r3 §3.1, spec §7.1).  Used for every storage index (c_i = j_i, k_i or u_i)."""
        self._k(j, "digits")
        return tuple((j // self._A[i]) % self.t[i] for i in range(self.d))

    def index(self, digits: Sequence[int]) -> int:
        """sum_i c_i A_i: the inverse of :meth:`digits` (r2 §3.1, r3 §3.1)."""
        c = self._digits_ok(digits, "index")
        return sum(ci * Ai for ci, Ai in zip(c, self._A))

    def delta(self, h: int, j: int) -> Fraction:
        """delta_h(j) = (sum_{i<h} j_i A_i) / A_h = (j mod A_h) / A_h in [0, 1), h = 2..d
        (r2 §3.1; r3 §3.1).  It depends only on the lower digits j_1..j_{h-1} and satisfies
        r2 (3.5): j/(A_h t_h) = (j_h + delta_h)/t_h and j/A_h = delta_h (mod 1); r3 §3.2:
        j_h + delta_h = j/A_h - t_h floor(j/A_{h+1})."""
        self._h(h, 2, self.d, "delta")
        self._k(j, "delta")
        Ah = self._A[h - 1]
        return Fraction(j % Ah, Ah)

    # ------------------------------------------------------------------ frequency map Phi
    def phi(self, u: Sequence[int]) -> int:
        """Phi(u) = k(u) = sum_i u_i Q_i: mixed radix with u_d least and u_1 most significant
        (r2 Thm 1 and §3.2 after (3.7); r3 (3.2)).  A bijection onto 0..R-1."""
        c = self._digits_ok(u, "phi")
        return sum(ui * (self.R // self._A[i + 1]) for i, ui in enumerate(c))

    def phi_inv(self, k: int) -> tuple[int, ...]:
        """(u_1, ..., u_d) with Phi(u) = k (r2 §3.2, r3 (3.2))."""
        self._k(k, "phi_inv")
        return tuple((k // (self.R // self._A[i + 1])) % self.t[i] for i in range(self.d))

    def u_digit(self, h: int, k: int) -> int:
        """u_h(k): digit h of k under Phi, = floor(k / Q_h) mod t_h (r2 (2.3), (3.8); r3 §3.3)."""
        self._h(h, 1, self.d, "u_digit")
        self._k(k, "u_digit")
        return (k // (self.R // self._A[h])) % self.t[h - 1]

    # ------------------------------------------------------------------ cycles and lines
    def cycles(self, h: int) -> list[list[int]]:
        """The cycles of A_h / B_h (r2 §4.5, spec §7.7): for s in range(q_h), the list
        [v q_h + s for v in range(A_h)].  Each has length A_h (not t_h); the predecessor of
        v q_h + s is (v q_h + s - q_h) mod R (cyclically, v - 1 mod A_h).  u_h, ..., u_d are constant
        on each cycle, because subtracting m q_h only changes digits u_i with i < h (r2 (3.8))."""
        self._h(h, 1, self.d, "cycles")
        qh, Ah = self.R // self._A[h - 1], self._A[h - 1]
        return [[v * qh + s for v in range(Ah)] for s in range(qh)]

    def line_indices(self, h: int) -> list[list[int]]:
        """Storage lines along axis h (the lines spread by S_h, r2 §3.1, r3 §3.1; or transformed by
        the axis-h DFT): one list [base + c_h A_h for c_h in range(t_h)] per base with c_h = 0, bases
        in increasing order.  The lines partition 0..R-1; the lower digits c_1..c_{h-1} of the base
        are base mod A_h."""
        self._h(h, 1, self.d, "line_indices")
        Ah, th = self._A[h - 1], self.t[h - 1]
        Ah1 = Ah * th
        return [[hi * Ah1 + lo + c * Ah for c in range(th)]
                for hi in range(self.R // Ah1) for lo in range(Ah)]

    def storage_to_freq(self) -> list[int]:
        """perm with perm[sum_i u_i A_i] = Phi(u) = sum_i u_i Q_i: the tensor-DFT output stored at
        position s is the 1D frequency perm[s] (r2 (3.7), r3 (3.5), (3.7) "tensor frequencies are
        identified through Phi").  Reorder with ``out[perm[s]] = Y[s]``.  For d = 2 this is the
        transpose u_1 + t_1 u_2 -> u_2 + r u_1 (MS eq. (poisson-bridge))."""
        R, d, A, t = self.R, self.d, self._A, self.t
        Qs = [R // A[i + 1] for i in range(d)]
        return [sum(((s // A[i]) % t[i]) * Qs[i] for i in range(d)) for s in range(R)]

    def freq_to_storage(self) -> list[int]:
        """The inverse permutation of :meth:`storage_to_freq`: inv[Phi(u)] = sum_i u_i A_i."""
        perm = self.storage_to_freq()
        inv = [0] * self.R
        for s, k in enumerate(perm):
            inv[k] = s
        return inv


def balanced_factors(K: int, d: int) -> tuple[int, ...]:
    """Balanced factorization of R = 2^K into d axes (r2 Theorem 3; r3 §2.1; spec §7.1):
    r = 2^ceil(K/d), every t_i in {r/2, r}, prod t_i = 2^K, and t_d = r ("choose a length-r axis
    as axis d").  The axes are ordered t_1 <= ... <= t_d (the d*ceil(K/d) - K short axes first).
    For d = 2 this is (2^floor(K/2), 2^ceil(K/2)), the manuscript's split (listing lines 737-738).
    Requires d >= 1 and K >= d (so that every t_i >= 2); raises ValueError otherwise."""
    for name, v in (("K", K), ("d", d)):
        if not isinstance(v, int) or isinstance(v, bool):
            raise TypeError(f"{name} must be an int, got {v!r}")
    if d < 1:
        raise ValueError(f"balanced_factors: need d >= 1, got d = {d}")
    if K < d:
        raise ValueError(f"balanced_factors: need K >= d so that all t_i >= 2 (K = {K}, d = {d})")
    e = -(-K // d)                 # ceil(K/d) >= 1
    n_short = d * e - K            # 0 <= n_short < d; if n_short > 0 then e >= 2
    return (1 << (e - 1),) * n_short + (1 << e,) * (d - n_short)
