"""C^{tensor e} through the complex network, phase edges, batching and the network version of the
Proposition 14 layer (SPEC §4.4-§4.8; Pr (13)-(18), (25), L1799-1887, L2183-2595).

Array model (RAM backend, DEVIATIONS D2): ``arr`` is a flat list of ring records (re list, im list)
of integer numerators in the GUARDED format: one common scale G = p + Delta (SPEC §1.5, §4.8).  The
flat index is ``row * 2^nb + addr``: a row field precedes the nb address bits of a row (SPEC §1.7),
so the flat order is the lexicographic stream order.  A layer acts on D consecutive K-bit physical
chunks of the record address with selected offset rho (SPEC §4.0): chunk lists are kept in
PHYSICAL order (most significant first; SPEC v1.1.1), and bit positions count from the LSB.

Batching (SPEC §4.6, Pr L2228-2242): the address is [P] x [2^K]^D x [S].  Theorem batching applies C
individually on the q0 most significant chunks, joins them into the row index (they "remain a
complete consecutive address block before all the remaining chunks", Pr L2237-2239) and pads the
rows with zero rows to a multiple of W^k0 within each preceding prefix: the flat index becomes
(prefix * row_pad + u) * 2^nb + addr with nb = lg S + (D - q0) K, so splitting the combined row
coordinate by W is the per-prefix split of Pr L2244-2245.  Forced batching (Dev-4) inserts a unit
row field after the prefix instead.  Pieces: base-m pieces of the remaining chunks, most
significant first.  Padded rows are asserted zero and removed only after all pieces completed.

Exactness: every halving is a right shift of a numerator that must be even (the guard reserves
the zero bits; asserted, "every halving discards only zeros", SPEC §4.8), and gate entries in
Z[i, 1/2] multiply by a Gaussian integer and then halve exactly.  No rounding happens anywhere
inside the recursion (Pr L1865-1870); Proposition 14 truncates once at the very end.

Basis changes P_M use row additions on addresses (SPEC §4.3).  With ``CCtx.row_add = None`` they
are applied as the address permutation (test oracle); the faithful path runs one Lemma 13 call per
row addition (x = slot src, y = slot dst, z = a third slot), plugged in through ``CCtx.row_add``.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace

from .policy import LAYER_TEST, LayerPolicy, base_m_pieces, batch_plan, is_leaf, layer_delta

__all__ = ["CCtx", "c_single", "c_power_exact", "batched_c_layer", "base_m_pieces",
           "simultaneous_H0_network", "chunk_geometry"]


@dataclass
class CCtx:
    """Explicit context of the network engine (SPEC §4.0: d, net_cx, policy, Delta, row field; no
    global state).  ``K``/``rho`` (chunk width, selected offset) and ``nb`` (address bits per row)
    are set per layer call."""

    net: object                     # CompiledNetwork over ZI2 (validated)
    d: int                          # dimension parameter of Prop 14 (leaf rule, q0, k0, Delta)
    policy: LayerPolicy = LAYER_TEST
    K: int = 1
    rho: int = 0
    nb: int = 0
    row_add: object = None          # callable(arr, rows, nb, dst, src, z, K, rho) -> arr, or None
    bound: int = 0                  # |numerator| < bound: the allocated guarded format (0 = unset)
    inst: object = None             # optional Instrument: counts mirrored as "m6.<key>"
    counts: dict = field(default_factory=dict)

    def hit(self, k: str, n: int = 1) -> None:
        self.counts[k] = self.counts.get(k, 0) + n
        if self.inst is not None:
            self.inst.hit("m6." + k, n)


def _half(v: int) -> int:
    if v & 1:
        raise AssertionError("guarded format exhausted: a halving would discard a 1 bit (SPEC §4.8)")
    return v >> 1


def _mul_zi2(re: list[int], im: list[int], z) -> tuple[list[int], list[int]]:
    """Exact product of a record by z = (a + i b)/2^k in Z[i, 1/2] (halvings asserted exact)."""
    a, b, k = z.re, z.im, z.k
    nr = [x * a - y * b for x, y in zip(re, im)]
    ni = [x * b + y * a for x, y in zip(re, im)]
    if k:
        m = (1 << k) - 1
        if any(v & m for v in nr) or any(v & m for v in ni):
            raise AssertionError("guarded format exhausted in a gate product (SPEC §4.8)")
        nr = [v >> k for v in nr]
        ni = [v >> k for v in ni]
    return nr, ni


def _ipow(rec, k: int):
    re, im = rec
    k %= 4
    if k == 0:
        return re, im
    if k == 1:
        return [-v for v in im], list(re)
    if k == 2:
        return [-v for v in re], [-v for v in im]
    return list(im), [-v for v in re]


def c_single(arr: list, bit: int, ctx: CCtx | None = None) -> None:
    """One exact C kernel on an address bit, in place (eq. (25)): (u, v) -> ((s+t)/2, (s-t)/2),
    s = u + v, t = i (u - v)."""
    m = 1 << bit
    for x in range(len(arr)):
        if x & m:
            continue
        (ur, ui), (vr, vi) = arr[x], arr[x | m]
        sr = [a + b for a, b in zip(ur, vr)]
        si = [a + b for a, b in zip(ui, vi)]
        tr = [b - a for a, b in zip(ui, vi)]
        ti = [a - b for a, b in zip(ur, vr)]
        arr[x] = ([_half(a + b) for a, b in zip(sr, tr)], [_half(a + b) for a, b in zip(si, ti)])
        arr[x | m] = ([_half(a - b) for a, b in zip(sr, tr)], [_half(a - b) for a, b in zip(si, ti)])
    if ctx is not None:
        ctx.hit("c_single")


def _zparity(arr: list, bits: list[int]) -> None:
    """Multiply the record at x by (-1)^{sum of x's bits at ``bits``} (Z on those bits), in place."""
    for x in range(len(arr)):
        if sum((x >> b) & 1 for b in bits) & 1:
            re, im = arr[x]
            arr[x] = ([-v for v in re], [-v for v in im])


def _row_add_direct(arr: list, dst_bits: list[int], src_bits: list[int]) -> list:
    """dst <- dst xor src on every column, as the address permutation (P_M row addition)."""
    out = [None] * len(arr)
    for x in range(len(arr)):
        y = x
        for d, s in zip(dst_bits, src_bits):
            if (x >> s) & 1:
                y ^= 1 << d
        out[y] = arr[x]
    return out


def _row_addition(arr: list, rows: int, slots: list[list[int]], dst: int, src: int,
                  ctx: CCtx) -> list:
    """Slot dst <- dst xor src in every column (SPEC §4.3): one Lemma 13 call with x = slot src,
    y = slot dst, z = the first other slot (needs m >= 3), or the address permutation (oracle)."""
    if ctx.row_add is None:
        ctx.hit("row_add.direct")
        return _row_add_direct(arr, slots[dst], slots[src])
    z = next((h for h in range(len(slots)) if h not in (dst, src)), None)
    if z is None:
        raise ValueError("Lemma 13 needs a third slot (m >= 3, SPEC §4.3)")
    ctx.hit("row_add.lemma13")
    return ctx.row_add(arr, rows, ctx.nb, slots[dst], slots[src], slots[z], ctx.K, ctx.rho)


def _phase_edge(arr: list, rows: int, edge, slots: list[list[int]], f: int, ctx: CCtx) -> list:
    """C_V C_U^{-1} on f columns (SPEC §4.4): P_{M^{-1}}, kernels C_{e_h}^{eps_h}, P_M."""
    if not edge.basis:
        ctx.hit("phase_edge.zero")
        return arr
    ctx.hit("phase_edge.nonzero")
    for dst, src in edge.reduce_ops:                         # P_{M^{-1}}
        arr = _row_addition(arr, rows, slots, dst, src, ctx)
    for h, eps in enumerate(edge.eps):
        if eps == 1:
            c_power_exact(arr, rows, slots[h], ctx)
        else:                                                # (C^{-1})^{tf} = (-i)^f Z^tf C^tf Z^tf
            ctx.hit("phase_edge.inverse_kernel")
            _zparity(arr, slots[h])
            c_power_exact(arr, rows, slots[h], ctx)
            _zparity(arr, slots[h])
            for x in range(len(arr)):
                arr[x] = _ipow(arr[x], -f)
    for dst, src in reversed(edge.reduce_ops):               # P_M
        arr = _row_addition(arr, rows, slots, dst, src, ctx)
    return arr


def c_power_exact(arr: list, rows: int, sel: list[int], ctx: CCtx) -> None:
    """C^{tensor e} on the e selected bits ``sel`` of every row, in place (SPEC §4.5)."""
    e = len(sel)
    net = ctx.net
    m, W = net.m, net.W
    if is_leaf(e, ctx.d, ctx.policy) or e % m:              # SPEC §4.0/§4.5 leaf rule
        ctx.hit("c_power.leaf")
        for b in sel:
            c_single(arr, b, ctx)
        return
    ctx.hit("c_power.network")
    if rows % W:
        raise AssertionError("row count must be divisible by W (padding, SPEC §4.6)")
    f = e // m
    slots = [sel[h * f:(h + 1) * f] for h in range(m)]
    A = 1 << ctx.nb
    g_rows = rows // W
    roles = [[arr[(W * g + w) * A + a] for g in range(g_rows) for a in range(A)] for w in range(W)]
    if net.pre_zmask is not None:
        for w in range(W):
            coords = net.pre_zmask[w]
            if coords:
                ctx.hit("zmask.pre")
                _zparity(roles[w], [b for h in coords for b in slots[h]])
    vertex = [-1] * W
    for gidx, gate in enumerate(net.gates):
        for w in gate.roles:
            edge = net.edge(w, vertex[w], gidx)
            if vertex[w] == -1 and edge.basis:
                ctx.hit("phase_edge.source_correction")     # first edge leaves the source frame
            roles[w] = _phase_edge(roles[w], g_rows, edge, slots, f, ctx)
            vertex[w] = gidx
        _apply_gate(roles, gate, ctx.bound)
        ctx.hit("gate")
    for w in range(W):
        edge = net.edge(w, vertex[w], net.SINK)
        if edge.basis:
            ctx.hit("phase_edge.sink_correction")           # last edge enters the sink frame
        roles[w] = _phase_edge(roles[w], g_rows, edge, slots, f, ctx)
    for o in range(W):
        if net.post_zmask is not None and net.post_zmask[o]:
            ctx.hit("zmask.post")
            _zparity(roles[o], [b for h in net.post_zmask[o] for b in slots[h]])
        if net.post_ipow is not None and net.post_ipow[o]:
            ctx.hit("ipow.post")
            k = net.post_ipow[o] * f
            roles[o] = [_ipow(rec, k) for rec in roles[o]]
    for w in range(W):
        if net.route_sign[w] == -1:
            ctx.hit("route_sign")
            o = net.route[w]
            roles[o] = [([-v for v in re], [-v for v in im]) for re, im in roles[o]]
    for w in range(W):                                      # row g of output role rho(w) -> row W g + w
        src = roles[net.route[w]]
        for g in range(g_rows):
            base = (W * g + w) * A
            for a in range(A):
                arr[base + a] = src[g * A + a]


def _apply_gate(roles: list, gate, bound: int = 0) -> None:
    """new[k] = sum_l matrix[k][l] * saved[l] at every (local row, address), exact (SPEC §2.1).
    ``bound`` > 0 asserts every output numerator fits the allocated guarded format (SPEC §4.8:
    "every intermediate fits the allocated format", checked mode)."""
    rs = gate.roles
    n = len(roles[rs[0]])
    for i in range(n):
        saved = [roles[w][i] for w in rs]
        for k, w in enumerate(rs):
            acc_r = acc_i = None
            for l, z in enumerate(gate.matrix[k]):
                if z.is_zero():
                    continue
                pr, pi = _mul_zi2(saved[l][0], saved[l][1], z)
                if acc_r is None:
                    acc_r, acc_i = pr, pi
                else:
                    acc_r = [a + b for a, b in zip(acc_r, pr)]
                    acc_i = [a + b for a, b in zip(acc_i, pi)]
            if acc_r is None:
                r = len(saved[0][0])
                acc_r, acc_i = [0] * r, [0] * r
            elif bound and any(not -bound < v < bound for v in acc_r + acc_i):
                raise AssertionError("guarded format exceeded by a gate output (SPEC §4.8)")
            roles[w][i] = (acc_r, acc_i)


def chunk_geometry(sel: list[int], K: int, rho: int) -> tuple[list[int], int]:
    """Physical chunk order (most significant first) of the selected bits and lg S, checking that
    they are D consecutive K-bit chunks with offset rho (SPEC §4.0: a complete rectangle
    [A] x [2^K]^D x [S] of physical chunks)."""
    if not 0 <= rho < K:
        raise ValueError("selected offset rho must satisfy 0 <= rho < K")
    chunks = sorted(sel, reverse=True)
    lsb = [b - rho for b in chunks]
    if any(lsb[i] - lsb[i + 1] != K for i in range(len(lsb) - 1)) or (lsb and lsb[-1] < 0):
        raise ValueError("the selected bits must sit at offset rho in D consecutive K-bit chunks")
    return chunks, (lsb[-1] if lsb else 0)


def batched_c_layer(arr: list, sel: list[int], ctx: CCtx) -> list:
    """C^{tensor D} on the D selected chunks of a complete array (SPEC §4.6; Pr L2228-2342), exact.

    ``arr`` is indexed by the record address (n bits); ``sel`` are the selected bit positions
    (offset ctx.rho in consecutive ctx.K-bit chunks).  Policy-driven: theorem batching (q0 leading
    chunks individually, then joined into the row index, rows padded to a multiple of W^k0 within
    each prefix; D <= q0: individual kernels only) or forced batching (unit row field, Dev-4)."""
    net, K = ctx.net, ctx.K
    D = len(sel)
    n = len(arr).bit_length() - 1
    if 1 << n != len(arr):
        raise ValueError("the layer needs a complete array of 2^n records")
    chunks, lo = chunk_geometry(sel, K, ctx.rho)
    plan = batch_plan(D, ctx.d, K, net, ctx.policy)
    if plan.individual:                                     # §4.9 base case (D <= q0)
        ctx.hit("batch.individual")
        for b in chunks:
            c_single(arr, b, ctx)
        return arr
    q0 = plan.q0
    for b in chunks[:q0]:                                   # preprocessing [Pr L2236-2237]
        c_single(arr, b, ctx)
    if q0:
        ctx.hit("batch.preprocessed_chunks", q0)
    nb = lo + (D - q0) * K                                  # per-row address: rest chunks + suffix
    top = lo + D * K
    if top > n:
        raise ValueError("selected chunks exceed the record address")
    P = 1 << (n - top)                                      # preceding prefix [Pr L2240]
    A = 1 << nb
    blk, pad = plan.row_len * A, (plan.row_pad - plan.row_len) * A
    r = len(arr[0][0]) if arr else 0
    zero = ([0] * r, [0] * r)
    big = []
    for pf in range(P):                                     # zero rows within each prefix
        big.extend(arr[pf * blk:(pf + 1) * blk])
        big.extend([zero] * pad)
    if pad:
        ctx.hit("rows.padded", P * pad)
    rows = P * plan.row_pad
    lctx = replace(ctx, nb=nb)
    pos = q0
    for size in plan.pieces:                                # most significant piece first
        c_power_exact(big, rows, chunks[pos:pos + size], lctx)
        pos += size
    out = []
    for pf in range(P):                                     # assert zero, then delete [Pr L2286-2288]
        base = pf * (blk + pad)
        for rec in big[base + blk:base + blk + pad]:
            if any(rec[0]) or any(rec[1]):
                raise AssertionError("padded rows must stay zero (SPEC §4.6)")
        out.extend(big[base:base + blk])
    if pad:
        ctx.hit("rows.removed", P * pad)
    return out


def simultaneous_H0_network(recs: list, sel_bits: list[int], scale: int, p: int, ctx: CCtx, *,
                            K: int = 1, rho: int = 0, truncate: bool = True,
                            exact_boundary: bool = False, check_disk: bool = True):
    """Proposition 14 through the complex network (SPEC §4.7): lift to the guarded format, S_D,
    batched C^{tensor D}, S_D, (-i/2)^t, b if D is odd, then exactly one Q_p.  Same contract as
    :func:`subnlogn.m6.prop14.simultaneous_H0_base` and bit-identical to it.  Returns
    (records, scale'): scale' = p if truncating, else the exact guarded scale G = scale + Delta."""
    from .prop14 import finish_layer, mul_i_power_by_positions, times_i_power
    D = len(sel_bits)
    delta = layer_delta(ctx.net, D, ctx.d, K, ctx.policy)
    G = scale + delta
    # allocated format: G = p + Delta fractional bits, Delta + 3 integer/sign bits (SPEC §4.7)
    ctx = replace(ctx, K=K, rho=rho, nb=0, bound=1 << (G + delta + 2))
    ctx.hit("layer.network")
    arr = [([v << delta for v in re], [v << delta for v in im]) for re, im in recs]
    arr = mul_i_power_by_positions(arr, sel_bits)
    arr = batched_c_layer(arr, sel_bits, ctx)
    arr = mul_i_power_by_positions(arr, sel_bits)
    t, odd = divmod(D, 2)
    arr = [times_i_power(re, im, -t) for re, im in arr]
    arr = [([_halvek(v, t) for v in re], [_halvek(v, t) for v in im]) for re, im in arr]
    if odd:
        nxt = []
        for re, im in arr:
            ir, ii = times_i_power(re, im, 1)
            nxt.append(([_half(a - c) for a, c in zip(re, ir)], [_half(a - c) for a, c in zip(im, ii)]))
        arr = nxt
    return finish_layer(arr, G, p, truncate=truncate, exact_boundary=exact_boundary,
                        check_disk=check_disk)


def _halvek(v: int, k: int) -> int:
    if k == 0:
        return v
    if v & ((1 << k) - 1):
        raise AssertionError("guarded format exhausted in (-i/2)^t (SPEC §4.8)")
    return v >> k
