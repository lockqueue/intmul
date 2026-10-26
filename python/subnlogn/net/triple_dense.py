"""Dense materialization of SMALL triple networks (m = h^3 <= 1000, e.g. h in {7, 8, 10}) for spot checks.

SPEC §2.4 (last paragraph: dense frames for small h), §2.6 run on a sample of roles, §2.7 step 10.  Frames are built
from the symbolic labels with factor projections computed independently of the cell calculus (generic
P_U = V (V^T G0 V)^{-1} V^T G0 on token bases; binary label bases by tensor products of token bases).  Exact ranks of
the bit edge matrices A = M_head - M_tail use the exact idempotent certificate: if (cA)^2 = cA for c in {1, -1, 1/2}
(checked exactly by packed integer products), then rank_Q(A) = trace(cA); otherwise fraction-free elimination.
"""

from __future__ import annotations

import random
from dataclasses import dataclass
from fractions import Fraction
from math import lcm

from . import f2
from .errors import NotAnInterface
from .model import SOURCE, compile_bit_edge, compile_phase_edge, zmask_int
from .qmatrix import rank_Q
from .symbolic import SymFrame, edge_calculus, generic_projection_Q, token_basis_F2, token_basis_Q
from .triple import TripleNetwork
from .validate import check_bit_edge, check_phase_edge, check_phase_route
from .zi2 import ZI2

DENSE_MAX_M = 1000


def _pack(row, w: int) -> int:
    """sum_j row[j] 2^(w j) (exact; injective on entries with |x| < 2^(w-1))."""
    bias = 1 << (w - 1)
    nb = w // 8
    raw = int.from_bytes(b"".join((x + bias).to_bytes(nb, "little") for x in row), "little")
    return raw - int.from_bytes(bias.to_bytes(nb, "little") * len(row), "little")


def exact_rank_scaled(D: int, X) -> tuple[int, str]:
    """Exact rank_Q of A = X / D (X an integer matrix): idempotent certificate (cA)^2 = cA, c in {1, -1, 1/2},
    verified row by row with packed integer products, then rank = trace(cA); else fraction-free elimination."""
    m = len(X)
    mx = max((abs(x) for r in X for x in r), default=0)
    if mx == 0:
        return 0, "zero"
    w = max((m * mx * mx).bit_length(), (2 * D * mx).bit_length()) + 2
    w = (w + 7) // 8 * 8
    packed = [_pack(r, w) for r in X]
    sq = []
    for r in X:
        acc = 0
        for k, a in enumerate(r):
            if a:
                acc += a * packed[k]
        sq.append(acc)
    tr = sum(X[i][i] for i in range(m))
    for lam, c in ((D, Fraction(1)), (-D, Fraction(-1)), (2 * D, Fraction(1, 2))):
        if all(s == lam * p for s, p in zip(sq, packed)):
            r = c * Fraction(tr, D)
            if r.denominator != 1 or not 0 <= r <= m:
                raise AssertionError("idempotent with non-integral trace")
            return int(r), "idempotent-trace"
    return rank_Q(X), "elimination"


class DenseTriple:
    """Dense frames of a small ``TripleNetwork`` (per-instance caches keyed by exact tokens / vertices)."""

    def __init__(self, tn: TripleNetwork):
        if tn.m > DENSE_MAX_M:
            raise ValueError(f"dense materialization only for m <= {DENSE_MAX_M} (m = {tn.m})")
        self.tn, self.h, self.m = tn, tn.h, tn.m
        self._fq: dict = {}
        self._fb: dict = {}
        self._frames: dict = {}
        self._q: dict = {}

    # ------------------------------------------------------------------------------------------- factor level
    def factor_Q(self, tok):
        """(d, integer h x h matrix) with P_token = matrix / d (generic projection formula)."""
        if tok not in self._fq:
            P = generic_projection_Q(token_basis_Q(tok, self.h), self.h)
            d = 1
            for r in P:
                for x in r:
                    d = lcm(d, x.denominator)
            self._fq[tok] = (d, [[int(x * d) for x in r] for r in P])
        return self._fq[tok]

    def factor_F2(self, tok) -> tuple[int, ...]:
        """A binary basis of the factor token (cached)."""
        if tok not in self._fb:
            self._fb[tok] = token_basis_F2(tok, self.h)
        return self._fb[tok]

    # ------------------------------------------------------------------------------------------- frames
    def bit_frame(self, fr: SymFrame):
        """(D, X) with M = sign * sum_summands P_U1 (x) P_U2 (x) P_U3 = X / D (Prop 7 matrices) [Pr L1127-1129]."""
        h, m = self.h, self.m
        parts = []
        for s in fr.label.summands:
            (d1, A1), (d2, A2), (d3, A3) = (self.factor_Q(t) for t in s)
            A23 = [[a * b for a in r2 for b in r3] for r2 in A2 for r3 in A3]
            X = [[a * b for a in A1[i1] for b in A23[i23]] for i1 in range(h) for i23 in range(h * h)]
            parts.append((d1 * d2 * d3, X))
        D = 1
        for d, _ in parts:
            D = lcm(D, d)
        out = [[0] * m for _ in range(m)]
        for d, X in parts:
            f = fr.sign * (D // d)
            for i in range(m):
                oi, xi = out[i], X[i]
                for j in range(m):
                    if xi[j]:
                        oi[j] += f * xi[j]
        return D, out

    def label_basis(self, fr: SymFrame) -> tuple[int, ...]:
        """A basis of the binary label: tensor products of token bases, summand by summand (independence checked)."""
        out = []
        for s in fr.label.summands:
            B1, B2, B3 = (self.factor_F2(t) for t in s)
            out += [f2.tensor3(a, b, c, self.h) for a in B1 for b in B2 for c in B3]
        out = tuple(out)
        if not f2.is_independent(out):
            raise NotAnInterface("label summands are not independent (sum not direct)")
        return out

    def frame(self, rid: int, vertex: int):
        """Dense frame at a vertex of role ``rid`` (gate frames cached per gate)."""
        key = vertex if vertex not in (SOURCE, self.tn.SINK) else (rid, vertex)
        if key not in self._frames:
            fr = self.tn.frame_at(rid, vertex)
            self._frames[key] = self.bit_frame(fr) if self.tn.kind == "bit" else self.label_basis(fr)
        return self._frames[key]

    # ------------------------------------------------------------------------------------------- edges
    def bit_edge_matrix(self, Ft, Fh):
        """A_e = M_head - M_tail as (D, X) with A_e = X / D (SPEC §2.2)."""
        (Dt, Xt), (Dh, Xh) = Ft, Fh
        D = lcm(Dt, Dh)
        ft, fh = D // Dt, D // Dh
        return D, [[fh * a - ft * b for a, b in zip(rh, rt)] for rh, rt in zip(Xh, Xt)]

    def edge_rank(self, rid: int, tail: int, head: int) -> tuple[int, str]:
        """Exact dense rank (bit) or residual dimension (complex; labels checked nested) of one edge."""
        Ft, Fh = self.frame(rid, tail), self.frame(rid, head)
        if self.tn.kind == "bit":
            return exact_rank_scaled(*self.bit_edge_matrix(Ft, Fh))
        if not (f2.is_subspace(Ft, Fh) or f2.is_subspace(Fh, Ft)):
            raise NotAnInterface(f"dense labels not nested on role {rid} edge {tail}->{head}")
        return abs(len(Fh) - len(Ft)), "residual-dimension"

    def to_qmatrix(self, F):
        """The dense bit frame (D, X) as an exact QMatrix X / D (cached per frame object)."""
        key = id(F)
        hit = self._q.get(key)
        if hit is None or hit[0] is not F:
            D, X = F
            hit = (F, tuple(tuple(Fraction(x, D) for x in r) for r in X))
            self._q[key] = hit
        return hit[1]


# ----------------------------------------------------------------------------------------------- sampling
def sample_roles(tn: TripleNetwork, per_stage: int = 1, seed: int = 0) -> list[int]:
    """Random roles: per_stage random X and Y data roles, and per stage, per_stage random invocations each giving a
    random center, Cstar (complex) and one random side wire of every neighbor type."""
    rng = random.Random(seed)
    trip = lambda: tn.triple(rng.randrange(tn.v))  # noqa: E731
    out = []
    for _ in range(per_stage):
        a = (trip(), trip(), trip())
        out += [tn.role_id(("X", a)), tn.role_id(("Y", a))]
    for j in (1, 2, 3):
        for _ in range(per_stage):
            fixed = tuple((k, trip()) for k in (1, 2, 3) if k != j)
            out.append(tn.role_id(("C", j, fixed, rng.randrange(tn.h))))
            if tn.kind == "complex":
                out.append(tn.role_id(("Cstar", j, fixed)))
            S = trip()
            types = {}
            for r in range(tn.z):
                T = tn.nbr_unrank(S, r)
                types.setdefault(len(set(S) & set(T)), []).append(T)
            for k in sorted(types):
                out.append(tn.role_id(("A", j, fixed, S, rng.choice(types[k]))))
    return out


@dataclass(frozen=True)
class SpotRow:
    """One edge of a sampled role: class, symbolic (cell calculus) rank/dim, dense exact rank/dim, method."""

    role: int
    edge_class: tuple
    symbolic: int
    dense: int
    method: str


def dense_spot_check(tn: TripleNetwork, per_stage: int = 1, seed: int = 0, dt: DenseTriple | None = None):
    """SPEC §2.7 step 10: dense frames for random roles, exact ranks of every edge, compared with the cell calculus
    (raises NotAnInterface on any mismatch); returns the rows."""
    dt = dt or DenseTriple(tn)
    rows = []
    for rid in sample_roles(tn, per_stage, seed):
        for tail, head, ft, fh, cls in tn.sym_edges(rid):
            res = edge_calculus(tn.h, tn.kind, ft, fh)
            sym = res.bit_rank if tn.kind == "bit" else res.dim
            dense, how = dt.edge_rank(rid, tail, head)
            if dense != sym:
                raise NotAnInterface(f"role {tn.role_name(rid)} edge {cls}: dense rank {dense} != symbolic {sym}")
            rows.append(SpotRow(rid, cls, sym, dense, how))
    return rows


def validate_sample(tn: TripleNetwork, per_stage: int = 1, seed: int = 0, lemma9_max_rank: int | None = None,
                    dt: DenseTriple | None = None, roles=None) -> dict:
    """Run the per-edge and per-route checks of ``net.validate`` (SPEC §2.6 items 3, 5, 6) on the dense edges of a
    random sample of roles.  Bit edges of rank <= lemma9_max_rank (default 2h) get the full Lemma 9 factorization and
    ``check_bit_edge``; the others get the exact rank only.  ``roles`` overrides the random sample.  Returns
    counts."""
    dt = dt or DenseTriple(tn)
    m = tn.m
    cap = 2 * tn.h if lemma9_max_rank is None else lemma9_max_rank
    counts = {"edges": 0, "lemma9": 0, "routes": 0}
    roles = sample_roles(tn, per_stage, seed) if roles is None else roles
    for rid in roles:
        vs = tn.vertices(rid)
        for tail, head in zip(vs, vs[1:]):
            Ft, Fh = dt.frame(rid, tail), dt.frame(rid, head)
            if tn.kind == "bit":
                r, _ = dt.edge_rank(rid, tail, head)
                if r <= cap:
                    Mt, Mh = dt.to_qmatrix(Ft), dt.to_qmatrix(Fh)
                    check_bit_edge(compile_bit_edge(rid, tail, head, Mt, Mh), Mt, Mh, m)
                    counts["lemma9"] += 1
            else:
                e = compile_phase_edge(rid, tail, head, Ft, Fh, m)
                check_phase_edge(e, Ft, Fh, m, method="quadratic" if m > 10 else "auto")
            counts["edges"] += 1
        o = tn.route(rid)
        Fsrc, Fsnk = dt.frame(rid, SOURCE), dt.frame(o, tn.SINK)
        if tn.kind == "bit":
            D, X = dt.bit_edge_matrix(Fsrc, Fsnk)        # M_sink(rho(w)) - M_source(w)
            if any(X[i][j] != (D if i == j else 0) for i in range(m) for j in range(m)):
                raise NotAnInterface(f"role {rid}: endpoint identity (11) fails")
        else:
            check_phase_route(Fsrc, Fsnk, zmask_int(tn.pre_zmask(rid)), zmask_int(tn.post_zmask(o)),
                              tn.post_ipow(o), m, f"route {rid} -> {o}", method="quadratic" if m > 10 else "auto")
        counts["routes"] += 1
    return counts


# ----------------------------------------------------------------------------------------------- scalar execution
def _rand_value(tn, rng):
    if tn.kind == "bit":
        return rng.getrandbits(1)
    return ZI2(rng.randint(-7, 7), rng.randint(-7, 7), rng.randint(0, 2))


def _apply_gate(tn, vals, gid):
    roles = tn.gate_roles(gid)
    rows = tn.gate_rows(gid)
    old = [vals[r] for r in roles]
    for r, row in zip(roles, rows):
        if tn.kind == "bit":
            acc = 0
            for l, cf in row:
                acc ^= old[l] & cf
        else:
            acc = ZI2(0)
            for l, cf in row:
                acc = acc + cf * old[l]
        vals[r] = acc


def invocation_roles(tn: TripleNetwork, j: int, fixed: dict):
    """(X bank, Y bank, scratch roles) of one invocation."""
    X = [tn.data_role("X", j, fixed, tn.triple(r)) for r in range(tn.v)]
    Y = [tn.data_role("Y", j, fixed, tn.triple(r)) for r in range(tn.v)]
    base = 2 * tn.N + tn.inv_index(j, fixed) * tn.n_inv_roles
    return X, Y, list(range(base, base + tn.n_inv_roles))


def run_invocation(tn: TripleNetwork, j: int, fixed: dict, seed: int = 0) -> None:
    """Execute the 4v + 4 gates of one invocation on random scalars (random scratch values): Lemma 5 per stage,
    y += x at stages 1, 3 and x -= y at stage 2, every scratch value restored [Pr L708-726]."""
    rng = random.Random(seed)
    X, Y, scr = invocation_roles(tn, j, fixed)
    vals = {r: _rand_value(tn, rng) for r in X + Y + scr}
    before = dict(vals)
    g0 = tn.inv_index(j, fixed) * tn.gates_per_inv
    for gid in range(g0, g0 + tn.gates_per_inv):
        _apply_gate(tn, vals, gid)
    for x, y in zip(X, Y):
        if j == 2:
            want_x = (before[x] ^ before[y]) if tn.kind == "bit" else before[x] - before[y]
            ok = vals[x] == want_x and vals[y] == before[y]
        else:
            want_y = (before[y] ^ before[x]) if tn.kind == "bit" else before[y] + before[x]
            ok = vals[y] == want_y and vals[x] == before[x]
        if not ok:
            raise NotAnInterface(f"stage {j} invocation does not realize the Lemma 5 update")
    if any(vals[r] != before[r] for r in scr):
        raise NotAnInterface(f"stage {j} invocation does not restore its scratch values")


def run_full_scalar(tn: TripleNetwork, seed: int = 0) -> None:
    """Execute EVERY gate of the network on random scalars and check (X_a, Y_a) -> (-Y_a, X_a), scratch restored
    (Lemma 5; slow: O(total gate size))."""
    rng = random.Random(seed)
    vals = [_rand_value(tn, rng) for _ in range(tn.W)]
    before = list(vals)
    for gid in range(tn.n_gates):
        _apply_gate(tn, vals, gid)
    for w in range(tn.W):
        want = before[w] if tn.route_sign(w) == 1 else -before[w]
        if tn.kind == "bit":
            want = before[w]
        if vals[tn.route(w)] != want:
            raise NotAnInterface(f"role {w}: scalar route fails")
