"""The interchange recursion of the preprint's §4: Lemma 10 (one rational matrix shear), Proposition 11
(power-width interchange with rows) and Lemma 12 (arbitrary widths, binary chunks, widths differing
by one), generic over any compiled bit network (SPEC §3.4-§3.8).

Sources: Pr = the plain-text rendering of [OAI26] (line numbers), SPEC = the internal implementation specification.

Every data movement goes through the primitive set of :mod:`subnlogn.stream` (Lemmas 3-4; RAM
backend D2).  The network is any :class:`subnlogn.net.CompiledNetwork` with domain F2 (fixtures B1/B2,
or a certified real network): its ``m``, ``W``, ``q`` (q_radix), ``gates``, ``route``, ``SINK``,
``s`` and ``edge(w, tail, head)`` (BitEdge with the Lemma 9 factors) are read; nothing about a
particular network is hard-coded.  Payload records are ints (gates XOR them, Pr L1484).

Policy (SPEC §6.3 TestPolicy fields; Dev-6): any object with ``lemma12_min_e`` (radix-q widths
below it are swapped digitwise; 0 keeps only the rho >= e rule of Pr L1592-1593) and
``lemma12_min_u`` (binary widths below it are swapped bitwise).  :func:`theorem_policy` routes every
call to base cases without touching the network (real networks are never materialized).

Instrumentation (optional :class:`subnlogn.instrument.Instrument`): "interchange.prop11_node",
"interchange.child_call" (and a note ("interchange.node", (k, children, s)) per Prop 11 node; the
code asserts children == s), "interchange.rank0_edge", "interchange.row_pad"/"row_unpad",
"interchange.range_pad"/"range_unpad", "interchange.lemma12_split" (row-field path taken),
"interchange.lemma12_network_call" (Prop 11 calls with k >= 1 issued by Lemma 12),
"interchange.prop11_leaf", "interchange.digitwise_swap".
"""

from __future__ import annotations

from dataclasses import dataclass
from math import prod

from .checks import require
from .net import SOURCE
from .net.qmatrix import specialize
from .stream import (
    Field, Shape, controlled_add, controlled_shift, digit_move, digit_swap, negate_field, pad_ranges,
    pad_rows, row_merge, row_split, unit_scale, unpad_ranges, unpad_rows, xor_reduce,
)

__all__ = ["InterchangePolicy", "theorem_policy", "lower_change", "matrix_shear", "power_swap",
           "swap_q_chunks", "swap_bit_chunks"]


@dataclass(frozen=True)
class InterchangePolicy:
    """Base-case rules of Lemma 12 (SPEC §6.3 ``TestPolicy`` fields ``lemma12_min_e``, ``lemma12_min_u``;
    Dev-6: the preprint leaves "a bounded remaining set of widths" open, Pr L1592-1593)."""

    lemma12_min_e: int = 2
    lemma12_min_u: int = 1


def theorem_policy() -> InterchangePolicy:
    """Theorem mode at every feasible size: every chunk swap is a base case (bitwise / digitwise), so
    a real network (W, m astronomically large) is never materialized (SPEC §3.11, §6.2)."""
    return InterchangePolicy(lemma12_min_e=1 << 62, lemma12_min_u=1 << 62)


def _hit(inst, name: str, n: int = 1) -> None:
    if inst is not None:
        inst.hit(name, n)


def _ilog_ceil(base: int, x: int) -> int:
    """Least k >= 0 with base**k >= x (integer comparisons only, SPEC §6.1)."""
    k, p = 0, 1
    while p < x:
        p *= base
        k += 1
    return k


# -- Lemma 10 ---------------------------------------------------------------------------------------


def lower_change(stream: list, shape: Shape, fields, E, Q: int, inst=None) -> tuple[list, Shape]:
    """Lower-triangular coordinate change f <- E f over Z/Q (SPEC §3.4; Pr L1404-1409): coordinates are
    updated in DESCENDING physical order, so the earlier coordinates used as controls still hold their
    original values; coordinate i is multiplied by its diagonal unit E_ii (Lemma 4 unit scaling) and
    then shifted by sum_{j<i} E_ij f_j (Lemma 4 controlled shift; controls precede the target)."""
    m = len(fields)
    for i in range(m):
        if any(E[i][j] != 0 for j in range(i + 1, m)):
            raise ValueError("lower_change: matrix is not lower triangular")
    for i in reversed(range(m)):
        if specialize(E[i][i], Q) != 1 % Q:
            stream, shape = unit_scale(stream, shape, fields[i], E[i][i], Q, inst)
        coefs = [(fields[j], specialize(E[i][j], Q)) for j in range(i)]
        coefs = [(f, a) for f, a in coefs if a]
        if coefs:
            cs = tuple(a for _, a in coefs)
            stream, shape = controlled_shift(stream, shape, fields[i], [f for f, _ in coefs],
                                             lambda *v, cs=cs: sum(a * x for a, x in zip(cs, v)), inst)
    return stream, shape


def matrix_shear(stream: list, shape: Shape, H, D, edge, net, row_field, k_child: int, policy,
                 inst=None) -> tuple[list, Shape, int]:
    """Lemma 10 (Pr L1375-1412; SPEC §3.5): the address permutation (H, D) -> (H + A D, D) over Z/q^b,
    A = edge.A = E1 Pi E2 (Lemma 9), H = (H_1..H_m) all before D = (D_1..D_m).  Transform D by E2 and H
    by E1^-1, realize each one (i, j) of Pi as H_i <- H_i + D_j by D_j <- D_j + H_i, interchange
    (H_i, D_j) (the ONLY recursive call: :func:`power_swap` at level k_child), D_j <- H_i - D_j; then
    transform H by E1 and D by E2^-1.  Exactly edge.rank interchanges; rank-0 edges do nothing.
    Returns (stream, shape, number of child interchanges)."""
    if edge.rank == 0:
        _hit(inst, "interchange.rank0_edge")
        return stream, shape, 0
    Q = shape.length(H[0])
    if any(shape.length(f) != Q for f in list(H) + list(D)):
        raise ValueError("matrix_shear: all fields must range over the same [q^b]")
    stream, shape = lower_change(stream, shape, D, edge.E2, Q, inst)
    stream, shape = lower_change(stream, shape, H, edge.E1inv, Q, inst)
    for i, j in edge.pivots:
        stream, shape = controlled_add(stream, shape, D[j], H[i], 1, inst)
        stream, shape = power_swap(stream, shape, H[i], D[j], net, row_field, k_child, policy, inst)
        stream, shape = negate_field(stream, shape, D[j], Q, inst)
        stream, shape = controlled_add(stream, shape, D[j], H[i], 1, inst)
    stream, shape = lower_change(stream, shape, H, edge.E1, Q, inst)
    stream, shape = lower_change(stream, shape, D, edge.E2inv, Q, inst)
    return stream, shape, len(edge.pivots)


# -- Proposition 11 ---------------------------------------------------------------------------------


def _apply_gate_f2(roles: list, gate) -> None:
    """Execute a gate pointwise at matching addresses of its role streams (Pr L1484): every output is
    computed from the SAVED inputs, out_k = XOR_{l : matrix[k][l] = 1} in_l (SPEC §2.1)."""
    saved = [roles[w] for w in gate.roles]
    new = []
    for k in range(len(gate.roles)):
        sel = [saved[l] for l, c in enumerate(gate.matrix[k]) if int(c) % 2]
        if len(sel) == 1 and sel[0] is saved[k]:
            new.append(saved[k])
        elif sel:
            new.append(xor_reduce(sel))
        else:
            new.append([0] * len(saved[k]))
    for k, w in enumerate(gate.roles):
        roles[w] = new[k]


def power_swap(stream: list, shape: Shape, Hc, Dc, net, row_field, k: int, policy=None,
               inst=None) -> tuple[list, Shape]:
    """Proposition 11 (Pr L1465-1520; SPEC §3.6): interchange the two disjoint radix-q chunks Hc, Dc of
    e = m^k digits (Hc before Dc), given a row field before both whose length is divisible by W^k;
    any prefix, gap and suffix fields are spectators.

    k = 0: one Lemma 3 digit swap.  k > 0: split each chunk into m subfields of b = e/m digits;
    D <- D - H; split rows cyclically into W role streams (row r = W g + w -> role w); along every role
    apply Phi_{A_e} on each edge by :func:`matrix_shear` (recursive interchanges at level k - 1) and
    execute every gate pointwise; merge row g of output role rho(w) back to row W g + w (undoing the
    route); then D <- H - D.  No source frame is applied at entry: the logical input is
    Phi_{-M_in}(physical) by definition (Pr L1488-1490), and by (11) every original row, scratch rows
    included, gets H <- H + D (Pr L1490-1497).  Exactly s child interchanges (asserted)."""
    fH, fD = shape.field(Hc), shape.field(Dc)
    q, m, W = net.q, net.m, net.W
    e = m ** k
    if not (fH.radix == fD.radix == q and fH.length == fD.length == q ** e):
        raise ValueError(f"power_swap: chunks must be radix-{q} fields of {e} digits")
    iR, iH, iD = shape.index(row_field), shape.index(Hc), shape.index(Dc)
    if not iR < iH < iD:
        raise ValueError("power_swap: the row field must precede both chunks, Hc before Dc")
    if shape.length(row_field) % (W ** k):
        raise ValueError(f"power_swap: row count {shape.length(row_field)} not divisible by W^{k}")
    if k == 0:
        _hit(inst, "interchange.prop11_leaf")
        return digit_swap(stream, shape, Hc, Dc, inst)
    b = e // m
    Q = q ** b
    Hn, Dn = [(Hc, "s", i) for i in range(m)], [(Dc, "s", i) for i in range(m)]
    shape = shape.split(Hc, [Field(n, Q, q) for n in Hn]).split(Dc, [Field(n, Q, q) for n in Dn])
    for i in range(m):
        stream, shape = controlled_add(stream, shape, Dn[i], Hn[i], -1, inst)  # D <- D - H
    roles, rshape = row_split(stream, shape, row_field, W, inst)
    vertex, children = [SOURCE] * W, 0

    def shear(w: int, head: int) -> None:
        nonlocal rshape, children
        new, sh, n = matrix_shear(roles[w], rshape, Hn, Dn, net.edge(w, vertex[w], head), net, row_field,
                                  k - 1, policy, inst)
        if sh != rshape:
            raise AssertionError("power_swap: a matrix shear changed the role shape")
        roles[w], children, vertex[w] = new, children + n, head

    for g, gate in enumerate(net.gates):
        for w in gate.roles:
            shear(w, g)
        _apply_gate_f2(roles, gate)
    for w in range(W):
        shear(w, net.SINK)
    if children != net.s:
        raise AssertionError(f"Prop 11 node made {children} child calls, expected s = {net.s}")
    _hit(inst, "interchange.prop11_node")
    _hit(inst, "interchange.child_call", children)
    if inst is not None:
        inst.note("interchange.node", (k, children, net.s))
    stream, shape = row_merge(roles, rshape, row_field, net.route, inst)
    for i in range(m):  # D <- H - D
        stream, shape = negate_field(stream, shape, Dn[i], Q, inst)
        stream, shape = controlled_add(stream, shape, Dn[i], Hn[i], 1, inst)
    shape = shape.join(Hn, Hc, q).join(Dn, Dc, q)
    return stream, shape.replace_field(Hc, valid=fH.valid).replace_field(Dc, valid=fD.valid)


# -- Lemma 12 ---------------------------------------------------------------------------------------


def _swap_digitwise(stream: list, shape: Shape, Hc, Dc, inst=None) -> tuple[list, Shape]:
    """Base case: interchange corresponding digits one pair at a time (Lemma 3 swaps, Pr L1592-1593)."""
    fH, fD = shape.field(Hc), shape.field(Dc)
    if fH.radix is None or fH.radix != fD.radix or fH.length != fD.length:
        raise ValueError("digitwise swap needs equal digit groups")
    _hit(inst, "interchange.digitwise_swap")
    n = fH.digits
    if n == 0:
        return stream, shape
    Hn, Dn = [(Hc, "d", t) for t in range(n)], [(Dc, "d", t) for t in range(n)]
    shape = shape.split_digits(Hc, Hn).split_digits(Dc, Dn)
    for t in range(n):
        stream, shape = digit_swap(stream, shape, Hn[t], Dn[t], inst)
    shape = shape.join(Hn, Hc, fH.radix).join(Dn, Dc, fD.radix)
    return stream, shape.replace_field(Hc, valid=fH.valid).replace_field(Dc, valid=fD.valid)


def swap_q_chunks(stream: list, shape: Shape, Hc, Dc, net, policy, inst=None) -> tuple[list, Shape]:
    """Lemma 12 for two radix-q chunks of e digits (Pr L1581-1660; SPEC §3.7), Hc before Dc, arbitrary
    prefix, gap and suffix.  k = least k with m^k >= e, rho = least rho with q^(2 rho) >= W^k; if
    e < policy.lemma12_min_e or rho >= e the e digit pairs are swapped individually.  Otherwise, with
    field orders (h+, h-, g, d+, d-): exchange the high rho digits pairwise, move the later high part
    (now h+) just after d+, join (d+, h+) into a row field of q^(2 rho) >= W^k rows, pad it with zero
    rows to R' = W^k ceil(R / W^k) within every prefix, write e - rho = sum_j a_j m^j and interchange the
    matching pieces of width m^j (a_j of each, most significant first) by Prop 11, assert and delete the
    padded rows, and move h+ back just before h- (undoing only the join)."""
    fH, fD = shape.field(Hc), shape.field(Dc)
    if fH.radix is None or fH.radix != fD.radix or fH.length != fD.length:
        raise ValueError("swap_q_chunks needs two radix chunks of equal width")
    if not shape.index(Hc) < shape.index(Dc):
        raise ValueError("swap_q_chunks: Hc must precede Dc")
    q, e = fH.radix, fH.digits
    if e == 0:
        return stream, shape
    if e < policy.lemma12_min_e:
        return _swap_digitwise(stream, shape, Hc, Dc, inst)
    m, W = net.m, net.W
    k = _ilog_ceil(m, e)
    rho, Wk = 0, W ** k
    while q ** (2 * rho) < Wk:
        rho += 1
    if rho >= e or rho == 0:  # rho = 0 only for e = 1 (k = 0): one digit swap, no rows needed
        return _swap_digitwise(stream, shape, Hc, Dc, inst)
    if q != net.q:
        raise ValueError(f"swap_q_chunks: chunk radix {q} differs from the network's q_radix {net.q}")
    _hit(inst, "interchange.lemma12_split")
    Hhi, Dhi = [(Hc, "hi", t) for t in range(rho)], [(Dc, "hi", t) for t in range(rho)]
    Hlo, Dlo = (Hc, "lo"), (Dc, "lo")
    low = q ** (e - rho)
    shape = shape.split(Hc, [Field(n, q, q) for n in Hhi] + [Field(Hlo, low, q)])
    shape = shape.split(Dc, [Field(n, q, q) for n in Dhi] + [Field(Dlo, low, q)])
    for t in range(rho):  # (h+, h-, g, d+, d-) -> (d+, h-, g, h+, d-)
        stream, shape = digit_swap(stream, shape, Hhi[t], Dhi[t], inst)
    for t in range(rho):  # -> (d+, h+, h-, g, d-)
        stream, shape = digit_move(stream, shape, Dhi[t], shape.index(Hhi[-1]) + 1 + t, inst)
    row = (Hc, "row")
    R = q ** (2 * rho)
    Rp = Wk * (-(-R // Wk))
    shape = shape.join(Hhi + Dhi, row)
    if Rp != R:
        stream, shape = pad_rows(stream, shape, row, Rp, 0, inst)
        _hit(inst, "interchange.row_pad")
    pieces = []  # base-m digits of e - rho, widths m^j, most significant first
    for j in range(k, -1, -1):
        pieces += [j] * (((e - rho) // m ** j) % m)
    require(sum(m ** j for j in pieces) == e - rho, "base-m pieces must sum to e - rho (Lemma 12, Pr L1581-1660)")
    Hp, Dp = [(Hc, "pc", i) for i in range(len(pieces))], [(Dc, "pc", i) for i in range(len(pieces))]
    shape = shape.split(Hlo, [Field(n, q ** m ** j, q) for n, j in zip(Hp, pieces)])
    shape = shape.split(Dlo, [Field(n, q ** m ** j, q) for n, j in zip(Dp, pieces)])
    for i, j in enumerate(pieces):  # -> (d+, h+, d-, g, h-)
        if j:
            _hit(inst, "interchange.lemma12_network_call")
        stream, shape = power_swap(stream, shape, Hp[i], Dp[i], net, row, j, policy, inst)
    shape = shape.join(Hp, Hlo, q).join(Dp, Dlo, q)
    if Rp != R:
        stream, shape = unpad_rows(stream, shape, row, R, 0, inst)
        _hit(inst, "interchange.row_unpad")
    shape = shape.split(row, [Field(n, q, q) for n in Hhi + Dhi])
    for t in range(rho):  # -> (d+, d-, g, h+, h-)
        stream, shape = digit_move(stream, shape, Dhi[t], shape.index(Dlo) - 1, inst)
    shape = shape.join(Hhi + [Hlo], Hc, q).join(Dhi + [Dlo], Dc, q)
    return stream, shape.replace_field(Hc, valid=fH.valid).replace_field(Dc, valid=fD.valid)


def _swap_equal_bits(stream: list, shape: Shape, Hc, Dc, net, policy, inst=None) -> tuple[list, Shape]:
    """Equal binary widths u (Pr L1669-1677; SPEC §3.8): bitwise if u < policy.lemma12_min_u; else pad
    both ranges [2^u] -> [q^e] (zero where EITHER coordinate is invalid), :func:`swap_q_chunks`, and
    delete every record with an invalid coordinate (asserted zero; the genuine set is preserved)."""
    fH, fD = shape.field(Hc), shape.field(Dc)
    u = fH.digits
    if u == 0:
        return stream, shape
    if u < policy.lemma12_min_u:
        return _swap_digitwise(stream, shape, Hc, Dc, inst)
    q = net.q
    e = _ilog_ceil(q, 2 ** u)
    stream, shape = pad_ranges(stream, shape, [Field(Hc, q ** e, q), Field(Dc, q ** e, q)], 0, inst)
    _hit(inst, "interchange.range_pad")
    stream, shape = swap_q_chunks(stream, shape, Hc, Dc, net, policy, inst)
    stream, shape = unpad_ranges(stream, shape, [Hc, Dc], 0, (fH, fD), inst)
    _hit(inst, "interchange.range_unpad")
    return stream, shape


def swap_bit_chunks(stream: list, shape: Shape, Hc, Dc, net, policy, inst=None) -> tuple[list, Shape]:
    """Lemma 12 for binary chunks (Pr L1561-1580, L1669-1692; SPEC §3.8): the address permutation
    (p, h, g, d, z) -> (p, d, g, h, z) for binary fields Hc (u_H bits) before Dc (u_D bits),
    |u_H - u_D| <= 1, any prefix p, gap g, suffix z (payload B = 1 allowed).  Field names stay with
    the physical positions (the first position afterwards holds the D coordinate, with D's width).

    Widths differing by one: the leading bit of the longer chunk is the extra bit;
    (h0, H, g, D) -> (h0, D, g, H) -> (D, g, h0, H) or (H, g, d0, D) -> (d0, H, g, D) -> (d0, D, g, H):
    one equal-width interchange and one single-bit move; g stays between the full chunks."""
    fH, fD = shape.field(Hc), shape.field(Dc)
    if fH.radix not in (2, None) or fD.radix not in (2, None):
        raise ValueError("swap_bit_chunks needs binary fields")
    uH, uD = _ilog_ceil(2, fH.length), _ilog_ceil(2, fD.length)
    if fH.length != 2 ** uH or fD.length != 2 ** uD or abs(uH - uD) > 1:
        raise ValueError("swap_bit_chunks: widths must be powers of two differing by at most one bit")
    if not shape.index(Hc) < shape.index(Dc):
        raise ValueError("swap_bit_chunks: Hc must precede Dc")
    shape = shape.replace_field(Hc, radix=2).replace_field(Dc, radix=2)
    if uH == uD:
        return _swap_equal_bits(stream, shape, Hc, Dc, net, policy, inst)
    if uH > uD:  # (h0, H, g, D) -> (h0, D, g, H) -> (D, g, h0, H)
        h0, Hr = (Hc, "x0"), (Hc, "rest")
        shape = shape.split(Hc, [Field(h0, 2, 2), Field(Hr, 2 ** uD, 2)])
        stream, shape = _swap_equal_bits(stream, shape, Hr, Dc, net, policy, inst)
        stream, shape = digit_move(stream, shape, h0, shape.index(Dc) - 1, inst)
        return stream, shape.rename(Hr, Hc).join([h0, Dc], Dc, 2)
    d0, Dr = (Dc, "x0"), (Dc, "rest")  # (H, g, d0, D) -> (d0, H, g, D) -> (d0, D, g, H)
    shape = shape.split(Dc, [Field(d0, 2, 2), Field(Dr, 2 ** uH, 2)])
    stream, shape = digit_move(stream, shape, d0, shape.index(Hc), inst)
    stream, shape = _swap_equal_bits(stream, shape, Hc, Dr, net, policy, inst)
    return stream, shape.join([d0, Hc], (Hc, "joined"), 2).rename((Hc, "joined"), Hc).rename(Dr, Dc)
