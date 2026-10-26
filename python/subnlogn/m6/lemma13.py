"""Lemma 13: packed selected-bit addition on one rectangle, with the exceptional-set repair
(SPEC §4.1, §4.2, §4.3; Pr = [OAI26] plain text L1928-2151).

Rectangle [N0] x [2^L]_chi1 x [N1] x [2^L]_chi2 x [N2] x [2^L]_chi3 x [N3] of records, (chi1, chi2, chi3)
a permutation of the chunk names (x, y, z), L = f K, 0 <= rho < K; selected positions j_i = rho + i K,
counted from the least significant bit of a chunk value (Pr L1937-1949).  Effect: y_{j_i} ^= x_{j_i}
(0 <= i < f); x, every other bit of y, ALL of z, the spectators and the payloads are unchanged.

Procedure (SPEC §4.1 pseudocode, Pr L2034-2147):
1. if f > 1, the eight lines (20) as packed cyclic shifts (22) of whole chunks (Lemma 4,
   :func:`subnlogn.stream.controlled_shift`), each after bringing its target to the physically rightmost
   of the three chunk positions with a value exchange ``swap`` (Lemma 12 / SPEC §3.8; default: L
   Lemma 3 bit swaps, Dev-6) and undoing that exchange afterwards; their composition is S0;
2. the repair: the records at addresses of the exceptional set B (eq. (23), or the test-only Dev-5
   "safe_segments" set) are extracted with destination ranks of T0 S0^{-1}, the bank alone is sorted by a
   stable LSD binary radix sort, keys == holes is asserted, and the records are reinserted; this makes
   the whole map T0 (Pr L2104-2143);
3. the Lemma 3 XOR of the omitted top selected position j_{f-1} (Pr L2144-2148).
f = 1: S0 = T0 = identity, B is empty, only step 3 runs.

Integer model (exact, used by the repair and the tests): :func:`S0`, :func:`S0_inverse`, :func:`T0`,
:func:`rotation_offset` (22), :func:`is_bad` (23), :func:`all_segments_safe` (Dev-5).  RAM backend: every
stream step is an index map (DEVIATIONS D2 / Dev-7); no floats anywhere.
"""

from __future__ import annotations

from math import prod

from ..checks import require
from ..stream import Field, Shape, controlled_shift, digit_pair_perm, digit_swap

__all__ = ["ROTATIONS", "BAD_SETS", "rotation_offset", "is_bad", "all_segments_safe", "S0", "S0_inverse",
           "T0", "bitwise_swap", "swap_via_lemma12", "repair_exceptional", "packed_selected_add",
           "row_add_lemma13"]

#: The eight lines (20) in chronological order [Pr L1979-1997; SPEC §1.3 R4, §4.1]: (target, other, sign,
#: parity) means target <- target + sign * c * [other = parity (mod 2)], with u = y and w = z segments and
#: the control c = the selected bit of x.
ROTATIONS = [("y", "z", -1, 0), ("z", "y", -1, 0), ("y", "z", +1, 0), ("z", "y", +1, 0),
             ("z", "y", +1, 1), ("y", "z", +1, 1), ("z", "y", -1, 1), ("y", "z", -1, 1)]

#: Exceptional-set modes (SPEC §4.0 LayerPolicy.bad_set): the literal (23) and the test-only Dev-5 variant.
BAD_SETS = ("eq23", "safe_segments")


def _hit(inst, name: str, n: int = 1) -> None:
    if inst is not None:
        inst.hit(name, n)


# -- integer model ------------------------------------------------------------------------------------


def rotation_offset(xv: int, ov: int, parity: int, f: int, K: int, rho: int) -> int:
    """Eq. (22) [Pr L2050-2061; SPEC §4.1]: sum_{i=0}^{f-2} 2^{j_i} [x_{j_i} = 1][o_{j_i} = parity],
    j_i = rho + i K.  Reads only the two control chunks (x and the line's other chunk), never the target,
    so every line is a bijection of the rectangle."""
    off = 0
    for i in range(f - 1):
        j = rho + i * K
        if (xv >> j) & 1 and ((ov >> j) & 1) == parity:
            off |= 1 << j
    return off


def _lines(vals: dict, lines, mult: int, f: int, K: int, rho: int) -> None:
    mod = 1 << (f * K)
    for tgt, oth, sgn, par in lines:
        vals[tgt] = (vals[tgt] + mult * sgn * rotation_offset(vals["x"], vals[oth], par, f, K, rho)) % mod


def S0(x: int, y: int, z: int, K: int, f: int, rho: int) -> tuple[int, int, int]:
    """The composition S0 of the eight packed lines (20)/(22), each modulo 2^L, L = f K, every predicate
    on the CURRENT values [Pr L1977-1978, L2061-2064; SPEC §4.1]: the integer model of step 1."""
    v = {"x": x, "y": y, "z": z}
    _lines(v, ROTATIONS, 1, f, K, rho)
    return v["x"], v["y"], v["z"]


def S0_inverse(x: int, y: int, z: int, K: int, f: int, rho: int) -> tuple[int, int, int]:
    """S0^{-1}: the eight lines in reverse order with negated offsets, each mask computed from the CURRENT
    state of the reversed computation [Pr L2116-2118; SPEC §4.2].  Since a line never changes its two
    controls, its current controls equal those it saw going forward, so this is the exact inverse."""
    v = {"x": x, "y": y, "z": z}
    _lines(v, ROTATIONS[::-1], -1, f, K, rho)
    return v["x"], v["y"], v["z"]


def T0(x: int, y: int, z: int, K: int, f: int, rho: int) -> tuple[int, int, int]:
    """The ideal map T0: y_{j_i} ^= x_{j_i} for 0 <= i <= f - 2, all other coordinates fixed
    [Pr L2071-2074; SPEC §4.2]."""
    mask = sum(1 << (rho + i * K) for i in range(f - 1))
    return x, y ^ (x & mask), z


def is_bad(yv: int, zv: int, K: int, f: int, rho: int) -> bool:
    """Eq. (23) [Pr L2065-2067; SPEC §4.2]: some used guard value g (the K - 1 bits above the low bit of
    segment i < f - 1, in y or in z) fails 10 <= g <= 2^{K-1} - 11.  For f >= 2 and K <= 5 the interval is
    empty and every address is bad (SPEC §4.2 "Small K (settled)"); for f = 1 no guard segment is used and the
    result is False (the repair is not run at f = 1)."""
    m = (1 << K) - 1
    hi = (1 << (K - 1)) - 11
    for i in range(f - 1):
        j = rho + i * K
        for val in (yv, zv):
            g = ((val >> j) & m) >> 1
            if not 10 <= g <= hi:
                return True
    return False


def _segment_safe(g: int, w: int, K: int) -> bool:
    """Dev-5 (SPEC §4.2): with the control c = 1, the guard g of the y segment and the whole z segment w
    fixed, the eight integer lines (20) keep both integers in [0, 2^K) at every step, for both low bits
    a in {0, 1} of the y segment u = 2g + a."""
    top = 1 << K
    for a in (0, 1):
        v = {"y": 2 * g + a, "z": w}
        for tgt, oth, sgn, par in ROTATIONS:
            if (v[oth] & 1) == par:
                v[tgt] += sgn
                if not 0 <= v[tgt] < top:
                    return False
    return True


def all_segments_safe(xv: int, yv: int, zv: int, K: int, f: int, rho: int) -> bool:
    """Dev-5 'safe_segments' good set (SPEC §4.2, test-only): every used segment i < f - 1 is safe,
    i.e. its control x_{j_i} is 0 or :func:`_segment_safe` holds for (guard of y_i, z_i).  The set is
    T0-invariant (T0 flips only a_i) and no carry crosses a segment on it, so S0 = T0 there."""
    m = (1 << K) - 1
    for i in range(f - 1):
        j = rho + i * K
        if (xv >> j) & 1 and not _segment_safe(((yv >> j) & m) >> 1, (zv >> j) & m, K):
            return False
    return True


# -- stream steps ---------------------------------------------------------------------------------------


def _bit_names(name, L: int) -> list:
    return [("_l13bit", name, k) for k in range(L)]          # most significant bit first


def _check_chunk(shape: Shape, name, L: int) -> Field:
    fld = shape.field(name)
    if fld.radix != 2 or fld.length != 1 << L or fld.valid is not None:
        raise ValueError(f"Lemma 13: chunk {name!r} must be an unpadded binary field of length 2^{L}")
    return fld


def bitwise_swap(stream: list, shape: Shape, name_a, name_b, inst=None) -> tuple[list, Shape]:
    """Exchange the VALUES of two equal-width binary fields (the record at (..a=u..b=v..) moves to
    (..a=v..b=u..), field order unchanged) by L Lemma 3 single-bit swaps after the descriptor-only
    split into bits: what Lemma 12's swap_bit_chunks does below policy.lemma12_min_u
    (SPEC §3.8, Dev-6; Pr L1669-1692, L2084-2093)."""
    fa = shape.field(name_a)
    L = fa.length.bit_length() - 1
    _check_chunk(shape, name_a, L)
    _check_chunk(shape, name_b, L)
    if L == 0:
        return list(stream), shape
    na, nb = _bit_names(name_a, L), _bit_names(name_b, L)
    sh = shape.split_digits(name_a, na).split_digits(name_b, nb)
    for k in range(L):
        stream, sh = digit_swap(stream, sh, na[k], nb[k], inst)
    sh = sh.join(na, name_a, radix=2).join(nb, name_b, radix=2)
    if sh.fields != shape.fields:
        raise AssertionError("bitwise_swap must restore the field descriptors")
    return stream, shape


def swap_via_lemma12(net_bit, policy):
    """A ``swap`` callable for :func:`packed_selected_add` that runs M5's Lemma 12 for binary chunks,
    :func:`subnlogn.interchange.swap_bit_chunks` with the bit network ``net_bit`` and the
    ``InterchangePolicy`` ``policy`` (SPEC §3.8; Pr L1669-1692, L2084-2093).  For equal widths that call
    exchanges the VALUES of the two fields (field names stay with the physical positions).  Prop 11's F2
    gates XOR whole records, so the interchange runs on the record-ID stream list(range(V)) and the realized
    address permutation is applied to the records (DEVIATIONS D12: exact, the gates act identically on
    every payload bit and the composite map is a permutation, asserted)."""
    from ..interchange import swap_bit_chunks

    def swap(stream: list, shape: Shape, name_a, name_b, inst=None) -> tuple[list, Shape]:
        a, b = (name_a, name_b) if shape.index(name_a) < shape.index(name_b) else (name_b, name_a)
        ids, sh = swap_bit_chunks(list(range(len(stream))), shape, a, b, net_bit, policy, inst)
        if [f.name for f in sh.fields] != [f.name for f in shape.fields] or sh.lengths != shape.lengths:
            raise AssertionError("swap_bit_chunks must keep the field order and lengths")
        if sorted(ids) != list(range(len(stream))):
            raise AssertionError("Lemma 12 on record IDs must realize an address permutation")
        return [stream[i] for i in ids], shape

    return swap


def _lsd_radix_sort(bank: list, key_bits: int) -> list:
    """Stable binary radix sort of (key, payload) pairs, least significant key bit first [Pr L2133-2135]."""
    for b in range(key_bits):
        bank = [e for e in bank if not (e[0] >> b) & 1] + [e for e in bank if (e[0] >> b) & 1]
    return bank


def repair_exceptional(stream: list, shape: Shape, names: dict, K: int, f: int, rho: int,
                       bad_set: str = "eq23", inst=None) -> list:
    """The correction T0 S0^{-1} on B [Pr L2104-2143; SPEC §4.2 pseudocode].  All chunks are back in their
    original positions.  Scan with a record-rank counter (ranks exclude payload bits), decode the three
    chunk values, test membership in B on the CURRENT address (S0(B) = B), compute the destination
    q' = T0(S0^{-1}(q)) and rank(q') = rank(q) + sum_h (q'_h - q_h) stride_h, bank (rank(q'), payload),
    stably LSD-radix-sort only the bank with ceil(lg M) key bits, assert keys == holes, reinsert."""
    M = len(stream)
    cx, cy, cz = (shape.field(names[c]).length for c in "xyz")
    sx, sy, sz = (shape.stride(names[c]) for c in "xyz")
    eq23 = bad_set == "eq23"
    holes, bank, memo = [], [], {}
    for rank in range(M):
        xv, yv, zv = (rank // sx) % cx, (rank // sy) % cy, (rank // sz) % cz
        key = (xv, yv, zv)
        if key in memo:
            delta = memo[key]
        else:
            bad = is_bad(yv, zv, K, f, rho) if eq23 else not all_segments_safe(xv, yv, zv, K, f, rho)
            delta = None
            if bad:
                dx, dy, dz = T0(*S0_inverse(xv, yv, zv, K, f, rho), K, f, rho)
                delta = (dx - xv) * sx + (dy - yv) * sy + (dz - zv) * sz
            memo[key] = delta
        if delta is not None:
            bank.append((rank + delta, stream[rank]))
            holes.append(rank)
    _hit(inst, "lemma13.bad_records", len(bank))
    if 0 < len(bank) < M:                                    # B neither empty nor the whole rectangle
        _hit(inst, "lemma13.repair_partial")
    if not bank:
        return stream
    bank = _lsd_radix_sort(bank, (M - 1).bit_length())
    _hit(inst, "lemma13.sort")
    if [k for k, _ in bank] != holes:
        raise AssertionError("Lemma 13 repair: sorted destination keys != marked holes "
                             "(T0 S0^{-1} must permute B, SPEC §4.2)")
    out = list(stream)
    for h, (_, payload) in zip(holes, bank):
        out[h] = payload
    _hit(inst, "lemma13.reinsert")
    return out


def _xor_top_bit(stream: list, shape: Shape, names: dict, K: int, f: int, rho: int,
                 inst=None) -> tuple[list, Shape]:
    """Lemma 3 XOR of the omitted top selected position pos = rho + (f-1) K [Pr L2144-2148; SPEC §4.1]:
    split x and y into bits (descriptor only), digit_pair_perm (a, b) -> (a, a ^ b), re-join."""
    L = f * K
    nx, ny = _bit_names(names["x"], L), _bit_names(names["y"], L)
    sh = shape.split_digits(names["x"], nx).split_digits(names["y"], ny)
    d = L - 1 - (rho + (f - 1) * K)                          # digit index, most significant first
    stream, sh = digit_pair_perm(stream, sh, nx[d], ny[d], lambda a, b: (a, a ^ b), inst)
    sh = sh.join(nx, names["x"], radix=2).join(ny, names["y"], radix=2)
    if sh.fields != shape.fields:
        raise AssertionError("top XOR must restore the field descriptors")
    _hit(inst, "lemma13.top_xor")
    return stream, shape


def packed_selected_add(stream: list, shape: Shape, names: dict, K: int, f: int, rho: int, *,
                        bad_set: str = "eq23", swap=None, inst=None) -> tuple[list, Shape]:
    """Lemma 13 [Pr L1928-2151; SPEC §4.1-§4.2]: y_{j_i} ^= x_{j_i} (j_i = rho + i K, 0 <= i < f) on the
    rectangle ``shape`` whose chunk fields are ``names["x"]``, ``names["y"]``, ``names["z"]`` (three
    distinct unpadded binary fields of length 2^{f K}, any physical order, any spectators).  x, the other
    y bits, all of z, spectators and payloads are unchanged; the returned shape is the input shape.

    Steps exactly as the SPEC §4.1 pseudocode: if f > 1, for each of the eight ROTATIONS bring the
    target chunk to the physically rightmost of the three positions with ``swap`` (value exchange of two
    equal-width fields; default :func:`bitwise_swap`, Dev-6), apply the Lemma 4 cyclic shift (22) with
    the controls = the fields now holding x and the line's other chunk (both precede the target), undo
    the swap (<= 16 swaps, 8 rotations); then :func:`repair_exceptional` with ``bad_set`` ("eq23" or the
    test-only "safe_segments", Dev-5); finally the Lemma 3 XOR at j_{f-1}."""
    if not (isinstance(K, int) and isinstance(f, int) and isinstance(rho, int)) or K < 1 or f < 1 \
            or not 0 <= rho < K:
        raise ValueError(f"Lemma 13 needs ints K >= 1, f >= 1, 0 <= rho < K (K={K}, f={f}, rho={rho})")
    if bad_set not in BAD_SETS:
        raise ValueError(f"bad_set must be one of {BAD_SETS}, got {bad_set!r}")
    if set(names) != {"x", "y", "z"} or len({names[c] for c in "xyz"}) != 3:
        raise ValueError("names must map x, y, z to three distinct field names")
    L = f * K
    for c in "xyz":
        _check_chunk(shape, names[c], L)
    if len(stream) != shape.volume:
        raise ValueError(f"stream has {len(stream)} records, shape volume is {shape.volume}")
    swap = bitwise_swap if swap is None else swap
    _hit(inst, "lemma13.call")
    stream = list(stream)
    if f > 1:                                                # rotations, swaps and repair only run for f >= 2
        _hit(inst, "lemma13.call_f2plus")
        _hit(inst, "lemma13.records_f2plus", len(stream))
        holder = {c: names[c] for c in "xyz"}               # logical chunk -> physical field (local state)
        rightmost = max(holder.values(), key=shape.index)
        mod = 1 << L
        for tgt, oth, sgn, par in ROTATIONS:
            exchanged = None
            if holder[tgt] != rightmost:                    # bring the target after both controls
                a = holder[tgt]
                occupant = next(c for c in "xyz" if holder[c] == rightmost)
                stream, sh = swap(stream, shape, a, rightmost, inst)
                if sh.fields != shape.fields:
                    raise AssertionError("swap must keep the field order and descriptors")
                _hit(inst, "lemma13.swap")
                holder[tgt], holder[occupant] = rightmost, a
                exchanged = (a, tgt, occupant)
            stream, _ = controlled_shift(
                stream, shape, holder[tgt], [holder["x"], holder[oth]],
                lambda xv, ov, s=sgn, p=par: (s * rotation_offset(xv, ov, p, f, K, rho)) % mod, inst)
            _hit(inst, "lemma13.rotation")
            if exchanged is not None:                       # undo the swap
                a, tgt_name, occupant = exchanged
                stream, sh = swap(stream, shape, a, rightmost, inst)
                if sh.fields != shape.fields:
                    raise AssertionError("swap must keep the field order and descriptors")
                _hit(inst, "lemma13.swap")
                holder[tgt_name], holder[occupant] = a, rightmost
        if holder != {c: names[c] for c in "xyz"}:
            raise AssertionError("all chunks must be back in their original positions before the repair")
        stream = repair_exceptional(stream, shape, names, K, f, rho, bad_set, inst)
    return _xor_top_bit(stream, shape, names, K, f, rho, inst)


# -- adapter for the complex-network basis changes (SPEC §4.3) ----------------------------------------


def _slot(bits, rho: int, K: int, nb: int) -> tuple[int, list]:
    """(field base, offsets) of a slot given by its selected address bits: base = min(bits) - rho, the
    offsets bits - base must be exactly {rho + i K : i < f} and the field must lie inside [0, nb)."""
    f = len(bits)
    base = min(bits) - rho
    offs = [b - base for b in bits]
    if base < 0 or sorted(offs) != [rho + i * K for i in range(f)] or base + f * K > nb:
        raise ValueError(f"slot bits {bits} are not the selected bits rho + iK of an L-bit field in [0, {nb})")
    return base, offs


def row_add_lemma13(arr: list, rows: int, nb: int, dst_bits, src_bits, z_bits, K: int, rho: int, *,
                    bad_set: str = "eq23", swap=None, inst=None) -> list:
    """One row addition dst <- dst xor src of a binary basis change = ONE Lemma 13 call with x = slot src,
    y = slot dst, z = a third slot [Pr L2152-2165; SPEC §4.3].  ``arr`` is a flat list, index
    row * 2^nb + addr; each slot is the list of its f selected address bits (from the LSB, any order,
    dst_bits[j] paired with src_bits[j] as in :func:`subnlogn.m6.cnet._row_add_direct`); its field is the
    L = f K contiguous bits starting at min(bits) - rho.  Builds the 7-field rectangle
    [N0] x [2^L] x [N1] x [2^L] x [N2] x [2^L] x [N3] (collapsed spectators, length 1 allowed) and calls
    :func:`packed_selected_add`; equals ``cnet._row_add_direct(arr, dst_bits, src_bits)``."""
    f = len(dst_bits)
    if not (f == len(src_bits) == len(z_bits) and f >= 1):
        raise ValueError("dst, src and z slots must have the same number f >= 1 of selected bits")
    if len(arr) != rows << nb:
        raise ValueError(f"arr has {len(arr)} records, expected rows * 2^nb = {rows << nb}")
    L = f * K
    slots = {"y": _slot(dst_bits, rho, K, nb), "x": _slot(src_bits, rho, K, nb), "z": _slot(z_bits, rho, K, nb)}
    if slots["y"][1] != slots["x"][1]:
        raise ValueError("dst_bits[j] and src_bits[j] must sit at the same offset of their fields")
    order = sorted("xyz", key=lambda c: -slots[c][0])       # most significant field first
    bases = [slots[c][0] for c in order]
    if any(bases[i] < bases[i + 1] + L for i in range(2)):
        raise ValueError("the three slot fields overlap")
    spect = [rows << (nb - bases[0] - L), 1 << (bases[0] - bases[1] - L), 1 << (bases[1] - bases[2] - L),
             1 << bases[2]]
    fields = []
    for i, c in enumerate(order):
        fields += [Field(("_l13spect", i), spect[i]), Field(("_l13slot", c), 1 << L, 2)]
    fields.append(Field(("_l13spect", 3), spect[3]))
    shape = Shape(tuple(fields), 1)
    require(prod(shape.lengths) == len(arr), "Lemma 13 slot shape must cover the whole array (SPEC §4.3)")
    out, _ = packed_selected_add(arr, shape, {c: ("_l13slot", c) for c in "xyz"}, K, f, rho,
                                 bad_set=bad_set, swap=swap, inst=inst)
    return out
