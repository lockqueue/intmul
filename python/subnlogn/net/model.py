"""Finite networks as data: Gate, Network, BitEdge, PhaseEdge, and ``compile_network``.

SPEC §2.1 [Pr L619-623, L762-809, L1436-1464].  A network is a chronological list of gates on W roles; each gate
combines the values of its roles from SAVED inputs (``new[k] = sum_l matrix[k][l] * old[l]``) and carries ONE frame
shared by every incidence.  ``compile_network`` derives, for every role w, its vertex list
``[SOURCE, gates touching w in time order, SINK]`` and one edge per consecutive pair:

* bit networks (domain "F2"): frames are rational m x m matrices M_v (D_v = Phi_{M_v}); a ``BitEdge`` stores
  A_e = M_head - M_tail, rank_Q(A_e) and its Lemma 9 factorization (SPEC §2.2, §3.1);
* complex networks (domain "ZI2"): frames are nondegenerate F2 labels U (D_v = C_U); a ``PhaseEdge`` stores the
  direction, an orthonormal residual basis, the eps signs, the basis extension M and ``reduce_ops`` (SPEC §2.3).

Frame invariant (5): the stored array at vertex v is D_v(logical array); the physical input is NOT pre-transformed;
the net operator is D_out S_Omega D_in^{-1}; a signed route w -> rho(w) applies eps_w D_sink(rho(w)) D_source(w)^{-1}.
Downstream (M5 Prop 11/Lemma 12, M6 Lemma 13/Prop 14) consumes ``CompiledNetwork`` generically.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from . import f2
from .errors import NotAnInterface
from .qmatrix import Bruhat, QMatrix, forbidden_integers, least_odd_prime_avoiding, lower_bruhat_factors, qmat, sub

#: Vertex id of every role's source (SPEC §2.1: -1 = source, len(gates) = sink).
SOURCE = -1

DOMAINS = ("F2", "ZI2")


@dataclass(frozen=True)
class Gate:
    """One gate: distinct roles in a fixed order, a len(roles)^2 scalar matrix (out = matrix @ saved_in) over the
    network's domain (F2: ints 0/1; ZI2: ``ZI2``/int/dyadic Fraction), and ONE frame shared by all its incidences
    (bit: rational m x m QMatrix; complex: F2 label = tuple of m-bit ints).  SPEC §2.1 [Pr L620-623, L766-769]."""

    roles: tuple[int, ...]
    matrix: tuple[tuple, ...]
    frame: object


@dataclass(frozen=True)
class Network:
    """A finite network (SPEC §2.1).

    ``source[w]``/``sink[w]``: frame at role w's source / sink (sink = physical output wire w).  ``route[w]``: the
    value entering role w leaves at output role route[w]; ``route_sign[w]`` = eps_w (all +1 over F2).
    Complex only: ``pre_zmask[w]`` = coordinates where Z is applied (every column) at input role w; ``post_zmask[o]``
    and ``post_ipow[o]`` = Z mask and the exponent of the once-per-role phase i^(post_ipow[o] * f) at output role o
    (f = number of columns).  ``None`` means no corrections.
    """

    domain: str
    m: int
    roles: tuple
    gates: tuple[Gate, ...]
    source: tuple
    sink: tuple
    route: tuple[int, ...]
    route_sign: tuple[int, ...]
    pre_zmask: tuple | None = None
    post_zmask: tuple | None = None
    post_ipow: tuple | None = None

    @property
    def W(self) -> int:
        """Number of roles (wires), scratch roles included."""
        return len(self.roles)

    @property
    def SINK(self) -> int:
        """Vertex id of every role's sink: len(gates)."""
        return len(self.gates)


@dataclass(frozen=True)
class BitEdge:
    """Edge of a bit network (SPEC §2.1): A = M_head - M_tail, rank = rank_Q(A), A = E1 Pi E2 (Lemma 9) with the
    ones of Pi at ``pivots`` in elimination order; E1inv, E2inv the inverse factors.  Vertex ids: -1 = source,
    len(gates) = sink."""

    role: int
    tail: int
    head: int
    A: QMatrix
    rank: int
    E1: QMatrix
    E2: QMatrix
    E1inv: QMatrix
    E2inv: QMatrix
    pivots: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class PhaseEdge:
    """Edge of a complex network (SPEC §2.1, §2.3): direction +1 (tail subset head), -1 (head subset tail), 0
    (equal); ``basis`` = orthonormal basis v_1..v_rho of the orthogonal residual (m-bit ints); ``eps`` = directional
    signs; ``M_cols`` = columns of an invertible M whose first rho columns are the basis; ``reduce_ops`` = row
    additions (dst, src) reducing M to I, chronological.  C_head C_tail^{-1} = prod_j C_{v_j}^{eps_j}
    = P_M (prod_j C_{e_j}^{eps_j}) P_M^{-1} (Prop 8, (16)) [Pr L1221-1256, L1818-1852]."""

    role: int
    tail: int
    head: int
    direction: int
    basis: tuple[int, ...]
    eps: tuple[int, ...]
    M_cols: tuple[int, ...]
    reduce_ops: tuple[tuple[int, int], ...]

    @property
    def rank(self) -> int:
        """rho_edge = dim of the residual (a residual dimension, not a matrix rank; SPEC §2.3)."""
        return len(self.basis)


Edge = BitEdge | PhaseEdge


# ----------------------------------------------------------------------------------------------- vertices and frames
def role_vertices(net: Network) -> tuple[tuple[int, ...], ...]:
    """For every role: (SOURCE, gates touching it in time order, SINK) [Pr L621-622; SPEC §2.1]."""
    touches: list[list[int]] = [[SOURCE] for _ in range(net.W)]
    for g, gate in enumerate(net.gates):
        for w in gate.roles:
            touches[w].append(g)
    return tuple(tuple(t + [net.SINK]) for t in touches)


def frame_at(net: Network, w: int, vertex: int):
    """D_v at vertex ``vertex`` of role w: source frame, gate frame, or sink frame."""
    if vertex == SOURCE:
        return net.source[w]
    if vertex == net.SINK:
        return net.sink[w]
    return net.gates[vertex].frame


def zmask_int(entry) -> int:
    """A Z-mask entry (tuple of label coordinates, or an int bit mask, or None) as an int bit mask."""
    if entry is None:
        return 0
    if isinstance(entry, int):
        return entry
    return f2.vec(entry)


# ----------------------------------------------------------------------------------------------- edge compilation
def compile_bit_edge(role: int, tail: int, head: int, M_tail, M_head) -> BitEdge:
    """A_e = M_head - M_tail, its exact rank and Lemma 9 factorization (SPEC §2.2, §3.1) [Pr L1442-1449]."""
    A = sub(qmat(M_head), qmat(M_tail))
    f: Bruhat = lower_bruhat_factors(A, check=len(A) <= 64)
    return BitEdge(role=role, tail=tail, head=head, A=A, rank=f.rank, E1=f.E1, E2=f.E2, E1inv=f.E1inv,
                   E2inv=f.E2inv, pivots=f.pivots)


def compile_phase_edge(role: int, tail: int, head: int, U_tail, U_head, m: int) -> PhaseEdge:
    """Nested labels U_tail, U_head: residual E = complement of the smaller inside the larger, an orthonormal basis
    (Lemma 6), eps by the popcount rule, M and reduce_ops (SPEC §2.3, §4.3) [Pr L1231-1256, L1818-1877]."""
    sub_th, sub_ht = f2.is_subspace(U_tail, U_head), f2.is_subspace(U_head, U_tail)
    if sub_th and sub_ht:
        direction, small, large = 0, U_tail, U_head
    elif sub_th:
        direction, small, large = 1, U_tail, U_head
    elif sub_ht:
        direction, small, large = -1, U_head, U_tail
    else:
        raise NotAnInterface(f"role {role}: labels at vertices {tail} -> {head} are not nested")
    if not (f2.is_independent(U_tail) and f2.is_independent(U_head)):
        raise NotAnInterface(f"role {role}: label basis at vertex {tail} or {head} is not independent")
    residual = f2.perp_within(small, large) if direction else ()
    basis = f2.orthonormal_basis(residual)
    eps = f2.eps_signs(basis, direction)
    M_cols = f2.extend_basis(basis, m)
    return PhaseEdge(role=role, tail=tail, head=head, direction=direction, basis=basis, eps=eps, M_cols=M_cols,
                     reduce_ops=f2.reduce_ops(M_cols, m))


@dataclass(frozen=True)
class CompiledNetwork:
    """A network with its derived vertex lists, edges, s = sum of edge ranks and (bit) the prime q_radix.

    Interface used by M5/M6 (SPEC §3.6, §4.5): ``m``, ``W``, ``q``, ``gates``, ``route``, ``route_sign``,
    ``pre_zmask``/``post_zmask``/``post_ipow``, ``edge(w, tail, head)``; the frame invariant of SPEC §2.1 applies.
    """

    net: Network
    vertices: tuple[tuple[int, ...], ...]
    edges: tuple[tuple, ...]
    s: int
    q: int | None
    _index: dict = field(init=False, compare=False, hash=False, repr=False)

    def __post_init__(self):
        object.__setattr__(self, "_index", {(e.role, e.tail, e.head): e for es in self.edges for e in es})

    domain = property(lambda self: self.net.domain)
    m = property(lambda self: self.net.m)
    W = property(lambda self: self.net.W)
    gates = property(lambda self: self.net.gates)
    route = property(lambda self: self.net.route)
    route_sign = property(lambda self: self.net.route_sign)
    pre_zmask = property(lambda self: self.net.pre_zmask)
    post_zmask = property(lambda self: self.net.post_zmask)
    post_ipow = property(lambda self: self.net.post_ipow)
    SINK = property(lambda self: self.net.SINK)

    def edge(self, w: int, tail: int, head: int):
        """The edge of role w from vertex ``tail`` to vertex ``head`` (consecutive on w)."""
        try:
            return self._index[(w, tail, head)]
        except KeyError:
            raise KeyError(f"role {w} has no edge {tail} -> {head}") from None

    def frame(self, w: int, vertex: int):
        """D_v of role w at ``vertex``."""
        return frame_at(self.net, w, vertex)

    @property
    def all_edges(self) -> tuple:
        """Every edge, role by role."""
        return tuple(e for es in self.edges for e in es)


def compile_network(net: Network, prime: bool = True) -> CompiledNetwork:
    """Derive vertex lists and edges (SPEC §2.1), s = sum of ranks / residual dimensions, and for bit networks
    q_radix = least odd prime avoiding the forbidden integers (SPEC §3.2) unless ``prime`` is False.

    Raises NotAnInterface when an edge cannot be compiled (e.g. non-nested or degenerate labels)."""
    if net.domain not in DOMAINS:
        raise NotAnInterface(f"unknown domain {net.domain!r}")
    if not (len(net.source) == len(net.sink) == net.W):
        raise NotAnInterface("every role needs a source and a sink frame")
    vertices = role_vertices(net)
    edges = []
    for w, vs in enumerate(vertices):
        es = []
        for t, h in zip(vs, vs[1:]):
            Ft, Fh = frame_at(net, w, t), frame_at(net, w, h)
            if net.domain == "F2":
                es.append(compile_bit_edge(w, t, h, Ft, Fh))
            else:
                es.append(compile_phase_edge(w, t, h, Ft, Fh, net.m))
        edges.append(tuple(es))
    s = sum(e.rank for es in edges for e in es)
    q = None
    if net.domain == "F2" and prime:
        frames = list(net.source) + list(net.sink) + [g.frame for g in net.gates]
        q = least_odd_prime_avoiding(forbidden_integers(frames, [e for es in edges for e in es]))
    return CompiledNetwork(net=net, vertices=vertices, edges=tuple(edges), s=s, q=q)
