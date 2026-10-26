"""The triple networks for general h as a LAZY descriptor (SPEC §2.4) [Pr L596-756, L816-1167, L1173-1310].

``TripleNetwork(h, kind)`` (kind 'bit' or 'complex'; h >= 7, h != 9 for bit) yields on demand: closed-form parameters,
role names <-> ids, gates (schedule (2) with its gate grouping, stage 2 = inverse schedule with the logical banks
exchanged, physical touch order Y-side, Y-center, X-side, X-center, Y-center, Y-side, X-center, X-side = reading R1),
their sparse scalar rows, symbolic labels (table (6)), terminal labels, the route / route signs / endpoint corrections
(Prop 7, Prop 8) and edge classes (Lemma 6 table).  Nothing of size m x m or W is ever materialized here.

Enumeration (a Completion: any fixed bijection works if used consistently).  Triples T are ranked lexicographically
(``combinations(range(h), 3)``).  Data roles: X[a] = rank(a), Y[a] = N + rank(a), rank(a) = (r1 v + r2) v + r3.
Scratch roles of the invocation (stage j, other coordinates fixed) come after, invocation-major: sides A[S, T] (S =
logical target triple, T = logical source triple, ordered neighbor pairs: rank(S) z + nbr_rank(S, T)), then centers
C_0..C_{h-1}, then Cstar (complex).  Gates: stage-major, then invocation, then time r = 0..7, then the gate's bank
triple; per invocation 4v + 4 gates (side times 0, 2, 5, 7 have one gate per bank triple; center times 1, 3, 4, 6 one
gate on the whole bank and all centers).  Invocations of one stage act on disjoint roles, so their order is irrelevant.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb

from ..checks import require
from .errors import NotAdmissible
from .model import SOURCE
from .symbolic import FULL, LINE, PERP, SymFrame, SymLabel, ZERO_LABEL, FULL_LABEL
from .zi2 import ZI2

FORWARD = ("-J", "-R", "+V", "+G", "+R", "+J", "-G", "-V")
#: -(k - 1)/2 * sign for |S cap T| = k in {0, 2} (complex side-injection coefficients) [Pr L649-656].
_HALF = {(k, sg): ZI2.of(Fraction(-(k - 1), 2)) * sg for k in (0, 2) for sg in (1, -1)}
#: Stage 2: time r uses the inverse of forward row 7 - r (reverse order, negated update) [Pr L922-924].
INVERSE = tuple(("+" if FORWARD[7 - r][0] == "-" else "-") + FORWARD[7 - r][1] for r in range(8))
#: Physical bank touched at each time in every stage (reading R1; table (6)).
BANK = ("Y", "Y", "X", "X", "Y", "Y", "X", "X")
GROUP = ("side", "center", "side", "center", "center", "side", "center", "side")
X_TIMES, Y_TIMES = (2, 3, 6, 7), (0, 1, 4, 5)
SIDE_TIMES, CENTER_TIMES = (0, 2, 5, 7), (1, 3, 4, 6)


#: Provenance of q_radix for the bit triple network.
Q_RADIX_PROVENANCE = "certified: the two independent enumerations agree; brute-force-confirmed at h <= 12"


def check_admissible(h: int, kind: str) -> None:
    """SPEC §2.4: integer h >= 7; h != 9 for the bit network (x^T (I - J/9) y is singular at h = 9)."""
    if kind not in ("bit", "complex"):
        raise NotAdmissible(f"kind must be 'bit' or 'complex', not {kind!r}")
    if not isinstance(h, int) or h < 7:
        raise NotAdmissible("the triple construction needs an integer h >= 7")
    if kind == "bit" and h == 9:
        raise NotAdmissible("h = 9: the rational form I - J/9 is singular")


@dataclass(frozen=True)
class TripleParams:
    """Closed forms of SPEC §2.4 [Pr L606-617, L633, L729-756, (7), (9), Prop 8]."""

    h: int
    kind: str
    v: int
    N: int
    m: int
    I: int
    z: int
    c: int
    W: int
    L: int
    s: int

    @property
    def saving(self) -> int:
        """W m - s, with its sign (negative = no saving; SPEC §2.7 step 7; h = 100 is THE real
        network, other h are informational)."""
        return self.W * self.m - self.s

    @property
    def eta(self) -> Fraction:
        """eta = (W m - s) / (W m) exactly [Pr L1316-1333]."""
        return Fraction(self.saving, self.W * self.m)


def triple_params(h: int, kind: str) -> TripleParams:
    """T = combinations(range(h), 3), v = C(h,3), N = v^3, m = h^3, I = 3v^2, z_b = 3C(h-3,2),
    z_c = C(h-3,3) + 3(h-3), c_b = h, c_c = h+1, W = 2N + I(vz + c), L = I c h, s_b = W m - N + 2L,
    s_c = W m - 2N + 2L (SPEC §2.4)."""
    check_admissible(h, kind)
    v = comb(h, 3)
    N, m, I = v ** 3, h ** 3, 3 * v * v
    z = 3 * comb(h - 3, 2) if kind == "bit" else comb(h - 3, 3) + 3 * (h - 3)
    c = h if kind == "bit" else h + 1
    W = 2 * N + I * (v * z + c)
    L = I * c * h
    s = W * m - N + 2 * L if kind == "bit" else W * m - 2 * N + 2 * L
    return TripleParams(h=h, kind=kind, v=v, N=N, m=m, I=I, z=z, c=c, W=W, L=L, s=s)


# ----------------------------------------------------------------------------------------------- combinatorics
@lru_cache(maxsize=1 << 20)
def rank_comb(cmb, n: int) -> int:
    """Lexicographic rank of a sorted k-subset of range(n) among combinations(range(n), k) (pure, cached)."""
    k = len(cmb)
    return comb(n, k) - 1 - sum(comb(n - 1 - x, k - i) for i, x in enumerate(cmb))


@lru_cache(maxsize=1 << 20)
def unrank_comb(r: int, n: int, k: int) -> tuple[int, ...]:
    """Inverse of ``rank_comb`` (pure, cached)."""
    out, x = [], 0
    for i in range(k):
        while comb(n - 1 - x, k - 1 - i) <= r:
            r -= comb(n - 1 - x, k - 1 - i)
            x += 1
        out.append(x)
        x += 1
    return tuple(out)


@dataclass(frozen=True)
class GateInfo:
    """Decoded gate id: stage j (1..3), invocation (local index and the fixed triples {coordinate: triple}), time r,
    index within the time slot, the operation of schedule (2) (or its inverse at stage 2), the physical bank, the
    group ('side' or 'center') and, for side gates, the gate's bank triple."""

    gid: int
    stage: int
    inv: int
    fixed: tuple
    time: int
    idx: int
    op: str
    bank: str
    group: str
    triple: tuple | None


class TripleNetwork:
    """Lazy descriptor of the bit or complex triple network for ground-set size h (SPEC §2.4)."""

    def __init__(self, h: int, kind: str):
        self.params = p = triple_params(h, kind)
        self.h, self.kind = h, kind
        self.v, self.N, self.m, self.W, self.z, self.c = p.v, p.N, p.m, p.W, p.z, p.c
        self.s = p.s
        self.n_inv_roles = p.v * p.z + p.c
        self.gates_per_inv = 4 * p.v + 4
        self.n_gates = p.I * self.gates_per_inv
        self.SINK = self.n_gates
        self._slot = (p.v, 1, p.v, 1, 1, p.v, 1, p.v)
        self._off = tuple(sum(self._slot[:r]) for r in range(8))
        self._z0 = comb(h - 3, 3)          # complex: neighbors with |S cap T| = 0 come first

    domain = property(lambda self: "F2" if self.kind == "bit" else "ZI2")

    @property
    def q_radix(self):
        """The fixed odd prime of Lemma 10 / Prop 11 for the BIT network (SPEC §3.2): 5, since every frame and every
        Lemma 9 factor (SPEC §3.1 pivot rule, physical lexicographic order) lies in Z[1/6] with unit diagonals, so
        S(h) = {2, 3} (provenance in :attr:`q_radix_provenance`).  None for the complex network (no
        radix-q address arithmetic).  Never needed at feasible sizes."""
        return 5 if self.kind == "bit" else None

    @property
    def q_radix_provenance(self) -> str:
        """Where q_radix = 5 comes from."""
        if self.kind != "bit":
            return "not applicable (complex network)"
        return Q_RADIX_PROVENANCE

    # ------------------------------------------------------------------------------------------- triples, neighbors
    def triple(self, r: int) -> tuple[int, int, int]:
        """The r-th triple of [h] in lexicographic order (T = combinations(range(h), 3), SPEC §2.4) [Pr L619]."""
        return unrank_comb(r, self.h, 3)

    def triple_rank(self, T) -> int:
        """Lexicographic rank of the triple T (SPEC §2.4)."""
        return rank_comb(tuple(T), self.h)

    def is_neighbor(self, S, T) -> bool:
        """|S cap T| = 1 (bit); S != T, |S cap T| in {0, 2} (complex) [Pr L642-649]."""
        k = len(set(S) & set(T))
        return k == 1 if self.kind == "bit" else (tuple(S) != tuple(T) and k in (0, 2))

    def _outside(self, S):
        return [x for x in range(self.h) if x not in S]

    def nbr_rank(self, S, T) -> int:
        """Rank of the neighbor T of S in [0, z): bit: (index of the common element) * C(h-3, 2) + rank of T - S
        among 2-subsets of [h] - S; complex: |S cap T| = 0 first (rank of T among 3-subsets of [h] - S), then
        |S cap T| = 2: C(h-3, 3) + (index of the dropped element of S) * (h-3) + (index of the new element)."""
        S, T = tuple(S), tuple(T)
        out = self._outside(S)
        pos = {x: i for i, x in enumerate(out)}
        common = [x for x in T if x in S]
        new = [pos[x] for x in T if x not in S]
        n = self.h - 3
        if self.kind == "bit":
            require(len(common) == 1, "bit-network neighbors share exactly one element (SPEC §2.7)")
            return S.index(common[0]) * comb(n, 2) + rank_comb(tuple(new), n)
        if not common:
            return rank_comb(tuple(new), n)
        require(len(common) == 2, "complex-network neighbors share zero or two elements (SPEC §2.7)")
        dropped = next(i for i, x in enumerate(S) if x not in T)
        return self._z0 + dropped * n + new[0]

    def nbr_unrank(self, S, r: int) -> tuple[int, int, int]:
        """Inverse of ``nbr_rank``."""
        S = tuple(S)
        out = self._outside(S)
        n = self.h - 3
        if self.kind == "bit":
            i, rr = divmod(r, comb(n, 2))
            a, b = unrank_comb(rr, n, 2)
            return tuple(sorted((S[i], out[a], out[b])))
        if r < self._z0:
            return tuple(out[x] for x in unrank_comb(r, n, 3))
        d, o = divmod(r - self._z0, n)
        return tuple(sorted([x for i, x in enumerate(S) if i != d] + [out[o]]))

    # ------------------------------------------------------------------------------------------- roles
    def data_rank(self, a) -> int:
        """rank of a = (T1, T2, T3) in T^3."""
        r1, r2, r3 = (self.triple_rank(T) for T in a)
        return (r1 * self.v + r2) * self.v + r3

    def data_unrank(self, r: int) -> tuple:
        """Inverse of ``data_rank``: the address a = (T1, T2, T3) in T^3 of the data banks [Pr L619-620]."""
        r, r3 = divmod(r, self.v)
        r1, r2 = divmod(r, self.v)
        return tuple(self.triple(x) for x in (r1, r2, r3))

    @staticmethod
    def _others(j: int) -> tuple[int, int]:
        return tuple(k for k in (1, 2, 3) if k != j)

    def inv_index(self, j: int, fixed: dict) -> int:
        """Global invocation index (j - 1) v^2 + r_k1 v + r_k2 for the fixed coordinates k1 < k2 (k != j)."""
        k1, k2 = self._others(j)
        return (j - 1) * self.v ** 2 + self.triple_rank(fixed[k1]) * self.v + self.triple_rank(fixed[k2])

    def inv_decode(self, inv: int) -> tuple[int, dict]:
        """Inverse of ``inv_index``: (stage j, {coordinate: fixed triple}) of an invocation [Pr L629-633]."""
        j, loc = divmod(inv, self.v ** 2)
        r1, r2 = divmod(loc, self.v)
        k1, k2 = self._others(j + 1)
        return j + 1, {k1: self.triple(r1), k2: self.triple(r2)}

    def _scratch_base(self, inv: int) -> int:
        return 2 * self.N + inv * self.n_inv_roles

    def role_id(self, name) -> int:
        """('X', a) | ('Y', a) | ('A', j, fixed, S, T) | ('C', j, fixed, i) | ('Cstar', j, fixed); ``fixed`` = dict
        or tuple of (coordinate, triple) pairs for the two coordinates != j."""
        kind = name[0]
        if kind in ("X", "Y"):
            return (0 if kind == "X" else self.N) + self.data_rank(name[1])
        j, fixed = name[1], dict(name[2])
        base = self._scratch_base(self.inv_index(j, fixed))
        if kind == "A":
            S, T = name[3], name[4]
            if not self.is_neighbor(S, T):
                raise ValueError("side wires join neighboring triples")
            return base + self.triple_rank(S) * self.z + self.nbr_rank(S, T)
        if kind == "C":
            return base + self.v * self.z + name[3]
        if kind == "Cstar" and self.kind == "complex":
            return base + self.v * self.z + self.h
        raise ValueError(f"unknown role {name!r}")

    def role_name(self, rid: int):
        """Inverse of ``role_id`` (``fixed`` returned as a sorted tuple of pairs)."""
        if not 0 <= rid < self.W:
            raise ValueError("role id out of range")
        if rid < 2 * self.N:
            return ("X" if rid < self.N else "Y", self.data_unrank(rid % self.N))
        inv, loc = divmod(rid - 2 * self.N, self.n_inv_roles)
        j, fixed = self.inv_decode(inv)
        fx = tuple(sorted(fixed.items()))
        if loc < self.v * self.z:
            rs, rn = divmod(loc, self.z)
            S = self.triple(rs)
            return ("A", j, fx, S, self.nbr_unrank(S, rn))
        i = loc - self.v * self.z
        return ("C", j, fx, i) if i < self.h else ("Cstar", j, fx)

    def data_role(self, bank: str, j: int, fixed: dict, T) -> int:
        """The data role of ``bank`` whose coordinate j is T and whose other coordinates are ``fixed``."""
        a = tuple(T if k == j else fixed[k] for k in (1, 2, 3))
        return (0 if bank == "X" else self.N) + self.data_rank(a)

    # ------------------------------------------------------------------------------------------- gates
    def gate_id(self, j: int, fixed: dict, time: int, idx: int = 0) -> int:
        """Global id of the gate at stage j, invocation ``fixed``, time r of schedule (2), slot index ``idx`` (the
        rank of the gate's bank triple for side gates, 0 for center gates) [Pr L676-706, L922-924]."""
        return self.inv_index(j, fixed) * self.gates_per_inv + self._off[time] + idx

    def gate_info(self, gid: int) -> GateInfo:
        """Decode a gate id: stage, invocation, time, operation of schedule (2) (inverse row 7 - r at stage 2),
        physical bank (reading R1), group and bank triple [Pr L676-706, L922-939]."""
        inv, loc = divmod(gid, self.gates_per_inv)
        j, fixed = self.inv_decode(inv)
        r = max(t for t in range(8) if self._off[t] <= loc)
        idx = loc - self._off[r]
        op = (FORWARD if j != 2 else INVERSE)[r]
        triple = self.triple(idx) if GROUP[r] == "side" else None
        return GateInfo(gid=gid, stage=j, inv=inv, fixed=tuple(sorted(fixed.items())), time=r, idx=idx, op=op,
                        bank=BANK[r], group=GROUP[r], triple=triple)

    def _coef(self, sign: int, val=1):
        if self.kind == "bit":
            return 1
        return ZI2.of(val) * sign

    def gate_roles(self, gid: int) -> tuple[int, ...]:
        """Roles of the gate in its fixed order: side gate [data, A wires in neighbor-rank order]; center gate
        [the whole bank in triple-rank order, C_0..C_{h-1}, (Cstar)]."""
        g = self.gate_info(gid)
        fixed = dict(g.fixed)
        base = self._scratch_base(g.inv)
        if g.group == "side":
            T = g.triple
            data = self.data_role(g.bank, g.stage, fixed, T)
            if g.op[1] == "J":     # per target S = T: A[S, T'] for T' ~ S (contiguous)
                sides = [base + g.idx * self.z + r for r in range(self.z)]
            else:                  # per source T: A[S, T] for S ~ T
                sides = []
                for r in range(self.z):
                    S = self.nbr_unrank(T, r)
                    sides.append(base + self.triple_rank(S) * self.z + self.nbr_rank(S, T))
            return (data,) + tuple(sides)
        bank = tuple(self.data_role(g.bank, g.stage, fixed, self.triple(r)) for r in range(self.v))
        centers = tuple(base + self.v * self.z + i for i in range(self.c))
        return bank + centers

    def gate_row(self, gid: int, out_role: int) -> dict:
        """The scalar row of ``out_role`` at gate ``gid``: {input role: coefficient} (saved inputs), exactly the maps
        V (copy), G (gather), R (scatter), J (side injection) of SPEC §2.4 with the sign of the schedule entry
        [Pr L642-706].  Raises ValueError if the gate does not touch ``out_role``."""
        g = self.gate_info(gid)
        sign = 1 if g.op[0] == "+" else -1
        letter = g.op[1]
        fixed = dict(g.fixed)
        base = self._scratch_base(g.inv)
        one = self._coef(1)
        name = self.role_name(out_role)
        row = {out_role: one}
        if g.group == "side":
            T = g.triple
            data = self.data_role(g.bank, g.stage, fixed, T)
            if out_role == data:
                if letter == "J":      # tgt_S += sign * sum_{T' ~ S} jcoef(S, T') A[S, T']   (S = T here)
                    for r in range(self.z):
                        row[base + g.idx * self.z + r] = self._side_coef(r, sign)
                return row
            if name[0] != "A" or name[1] != g.stage or dict(name[2]) != fixed or \
                    (letter == "J" and name[3] != T) or (letter == "V" and name[4] != T):
                raise ValueError("role not touched by this gate")
            if letter == "V":          # A[S, T] += sign * src_T
                row[data] = self._coef(sign)
            return row
        loc = out_role - base - self.v * self.z
        if name[0] == g.bank and all(name[1][k - 1] == fixed[k] for k in fixed):
            if letter == "R":          # tgt_S += sign * sum_{i in S} C_i  |  sign * (sum_{i in S} C_i - Cstar) / 2
                S = name[1][g.stage - 1]
                half = Fraction(1, 2) if self.kind == "complex" else 1
                for i in S:
                    row[base + self.v * self.z + i] = self._coef(sign, half)
                if self.kind == "complex":
                    row[base + self.v * self.z + self.h] = self._coef(sign, -half)
            return row
        if not (name[0] in ("C", "Cstar") and 0 <= loc < self.c):
            raise ValueError("role not touched by this gate")
        if letter == "G":              # C_i += sign * sum_{T ni i} src_T ; Cstar += sign * sum_T src_T
            cf = self._coef(sign)
            stride = self.v ** (3 - g.stage)
            b0 = self.data_role(g.bank, g.stage, fixed, (0, 1, 2)) - self.triple_rank((0, 1, 2)) * stride
            if loc == self.h:
                for r in range(self.v):
                    row[b0 + r * stride] = cf
            else:
                others = [e for e in range(self.h) if e != loc]
                for x, y in combinations(others, 2):
                    row[b0 + rank_comb(tuple(sorted((loc, x, y))), self.h) * stride] = cf
        return row

    def _side_coef(self, r: int, sign: int):
        """Coefficient of the r-th side wire A[S, T] in the J row of tgt_S: 1 (bit); -(|S cap T| - 1)/2 (complex),
        where neighbor ranks r < C(h-3, 3) are exactly the |S cap T| = 0 neighbors (``nbr_rank``)."""
        if self.kind == "bit":
            return 1
        k = 0 if r < self._z0 else 2
        return _HALF[(k, sign)]

    def gate_rows(self, gid: int) -> tuple[tuple[tuple[int, object], ...], ...]:
        """All rows of the gate as sparse tuples of (local input index, coefficient), in ``gate_roles`` order."""
        roles = self.gate_roles(gid)
        pos = {r: i for i, r in enumerate(roles)}
        return tuple(tuple(sorted((pos[k], cf) for k, cf in self.gate_row(gid, r).items())) for r in roles)

    # ------------------------------------------------------------------------------------------- labels
    def stage_label(self, j: int, fixed: dict, time: int, t=None) -> SymLabel:
        """Table (6) label at stage j and time r, tensored by Q (SPEC §2.4) [Pr L875-975]: A = F^(j-1),
        P = <t_a1 (x) .. (x) t_a(j-1)>, B = P^perp in A = sum_k (LINE(a1)..LINE(a(k-1)), PERP(ak), F..F),
        Q = <t_a(j+1) (x) .. (x) t_a3>; t = the gate's physical bank triple."""
        P = tuple(LINE(fixed[k]) for k in range(1, j))
        A = tuple(FULL for _ in range(1, j))
        B = [tuple(LINE(fixed[i]) for i in range(1, k)) + (PERP(fixed[k]),) + (FULL,) * (j - 1 - k)
             for k in range(1, j)]
        Q = tuple(LINE(fixed[k]) for k in range(j + 1, 4))
        if time == 0:
            S = [b + (LINE(t),) for b in B]
        elif time in (1, 4):
            S = [b + (FULL,) for b in B]
        elif time == 2:
            S = [b + (FULL,) for b in B] + [P + (LINE(t),)]
        elif time == 5:
            S = [b + (FULL,) for b in B] + [P + (PERP(t),)]
        else:
            S = [A + (FULL,)]
        return SymLabel.of(s + Q for s in S)

    def gate_label(self, gid: int) -> SymLabel:
        """The common label of gate ``gid`` (table (6), tensored by Q) [Pr L942-977]."""
        g = self.gate_info(gid)
        return self.stage_label(g.stage, dict(g.fixed), g.time, g.triple)

    def source_frame(self, rid: int) -> SymFrame:
        """X_a: U_a (bit matrix -P_{U_a}); Y_a and scratch: 0 [Pr L857-868, L1128]."""
        if rid < self.N:
            a = self.data_unrank(rid)
            return SymFrame(-1 if self.kind == "bit" else 1, SymLabel(((LINE(a[0]), LINE(a[1]), LINE(a[2])),)))
        return SymFrame(1, ZERO_LABEL)

    def sink_frame(self, rid: int) -> SymFrame:
        """X_a and scratch: the full space; Y_a: U_a^perp [Pr L857-868]."""
        if self.N <= rid < 2 * self.N:
            a = self.data_unrank(rid - self.N)
            return SymFrame(1, SymLabel(((PERP(a[0]), FULL, FULL), (LINE(a[0]), PERP(a[1]), FULL),
                                         (LINE(a[0]), LINE(a[1]), PERP(a[2])))))
        return SymFrame(1, FULL_LABEL)

    def frame_at(self, rid: int, vertex: int) -> SymFrame:
        """Symbolic frame at a vertex of role ``rid``: source, gate label, or sink (SPEC §2.1-2.4)."""
        if vertex == SOURCE:
            return self.source_frame(rid)
        if vertex == self.SINK:
            return self.sink_frame(rid)
        return SymFrame(1, self.gate_label(vertex))

    # ------------------------------------------------------------------------------------------- terminals
    def route(self, rid: int) -> int:
        """rho: X_a <-> Y_a, scratch fixed [Pr L1130, L1275]."""
        if rid < self.N:
            return rid + self.N
        if rid < 2 * self.N:
            return rid - self.N
        return rid

    def route_sign(self, rid: int) -> int:
        """Complex: X_a -> Y_a +1, Y_a -> X_a -1, scratch +1; bit: all +1 [Pr L1275-1278]."""
        return -1 if (self.kind == "complex" and self.N <= rid < 2 * self.N) else 1

    def _ua_support(self, a) -> tuple[int, ...]:
        h = self.h
        return tuple(sorted((i1 * h + i2) * h + i3 for i1 in a[0] for i2 in a[1] for i3 in a[2]))

    def pre_zmask(self, rid: int) -> tuple[int, ...]:
        """Complex: Z on supp(u_a) (27 coordinates) in every column at input X_a [Pr L1304-1306]."""
        return self._ua_support(self.data_unrank(rid)) if (self.kind == "complex" and rid < self.N) else ()

    def post_zmask(self, rid: int) -> tuple[int, ...]:
        """Complex: the same Z pattern at physical output Y_a."""
        if self.kind == "complex" and self.N <= rid < 2 * self.N:
            return self._ua_support(self.data_unrank(rid - self.N))
        return ()

    def post_ipow(self, rid: int) -> int:
        """Complex: i^(27 f) once at physical output Y_a (wt(u_a) = 27) [Pr L1287-1307]."""
        return 27 if (self.kind == "complex" and self.N <= rid < 2 * self.N) else 0

    # ------------------------------------------------------------------------------------------- vertices / edges
    def vertices(self, rid: int) -> tuple[int, ...]:
        """(SOURCE, gates in time order, SINK): data wires 12 gates (4 per stage), scratch wires 4."""
        name = self.role_name(rid)
        out = [SOURCE]
        if name[0] in ("X", "Y"):
            a = name[1]
            times = X_TIMES if name[0] == "X" else Y_TIMES
            for j in (1, 2, 3):
                fixed = {k: a[k - 1] for k in (1, 2, 3) if k != j}
                T = a[j - 1]
                for r in times:
                    out.append(self.gate_id(j, fixed, r, self.triple_rank(T) if GROUP[r] == "side" else 0))
        elif name[0] == "A":
            j, fixed, S, T = name[1], dict(name[2]), name[3], name[4]
            tY, tX = (S, T) if j != 2 else (T, S)
            for r, t in zip(SIDE_TIMES, (tY, tX, tY, tX)):
                out.append(self.gate_id(j, fixed, r, self.triple_rank(t)))
        else:
            j, fixed = name[1], dict(name[2])
            for r in CENTER_TIMES:
                out.append(self.gate_id(j, fixed, r, 0))
        out.append(self.SINK)
        return tuple(out)

    def edge_class(self, rid: int, k: int) -> tuple:
        """(stage, wire, edge) of the k-th edge of a role, named as in the Lemma 6 table."""
        name = self.role_name(rid)
        if name[0] in ("X", "Y"):
            if k == 12:
                return (3, name[0], "last->sink")
            j, i = divmod(k, 4)
            times = X_TIMES if name[0] == "X" else Y_TIMES
            prev = "in" if i == 0 else str(times[i - 1])
            return (j + 1, name[0], f"{prev}->{times[i]}")
        wire = "side" if name[0] == "A" else "center"
        times = SIDE_TIMES if wire == "side" else CENTER_TIMES
        if k == 4:
            return (name[1], "scratch", "last->sink")
        prev = "source" if k == 0 else str(times[k - 1])
        return (name[1], wire, f"{prev}->{times[k]}")

    def sym_edges(self, rid: int):
        """[(tail, head, tail_frame, head_frame, edge_class)] for every edge of role ``rid``."""
        vs = self.vertices(rid)
        frames = [self.frame_at(rid, v) for v in vs]
        return [(vs[k], vs[k + 1], frames[k], frames[k + 1], self.edge_class(rid, k)) for k in range(len(vs) - 1)]

    # ------------------------------------------------------------------------------------------- small-h dense views
    def dense(self):
        """Dense frames for spot checks (only m <= 1000; see ``triple_dense.DenseTriple``)."""
        from .triple_dense import DenseTriple
        return DenseTriple(self)

    def validate_sample(self, per_stage: int = 1, seed: int = 0, **kw) -> dict:
        """Run the SPEC §2.6 per-edge / per-route checks on a random sample of roles (``triple_dense``)."""
        from .triple_dense import validate_sample
        return validate_sample(self, per_stage, seed, **kw)

    # ------------------------------------------------------------------------------------------- orbit representatives
    def representative_triples(self):
        """T0 = (0,1,2) and one neighbor of T0 per neighbor type: bit (2,3,4) (|S cap T| = 1); complex (3,4,5)
        (|S cap T| = 0) and (0,1,3) (|S cap T| = 2), with the per-triple neighbor counts."""
        T0 = (0, 1, 2)
        if self.kind == "bit":
            return T0, (((2, 3, 4), self.z),)
        return T0, (((3, 4, 5), comb(self.h - 3, 3)), ((0, 1, 3), 3 * (self.h - 3)))

    def representatives(self):
        """One role per orbit of (S_h)^3 (acting on the three ground sets; it preserves roles, gates, labels and
        both forms, hence ranks), with the orbit size: X and Y data wires (N each); per stage: center C_0
        (v^2 h), Cstar (complex, v^2), one side wire per neighbor type (v^2 * v * z_type).  Sizes sum to W."""
        T0, nbrs = self.representative_triples()
        a0 = (T0, T0, T0)
        out = [(self.role_id(("X", a0)), self.N, "X data"), (self.role_id(("Y", a0)), self.N, "Y data")]
        v2 = self.v ** 2
        for j in (1, 2, 3):
            fixed = tuple((k, T0) for k in (1, 2, 3) if k != j)
            out.append((self.role_id(("C", j, fixed, 0)), v2 * self.h, f"stage {j} center"))
            if self.kind == "complex":
                out.append((self.role_id(("Cstar", j, fixed)), v2, f"stage {j} Cstar"))
            for T, cnt in nbrs:
                k = len(set(T0) & set(T))
                out.append((self.role_id(("A", j, fixed, T0, T)), v2 * self.v * cnt, f"stage {j} side |S^T|={k}"))
        return out
