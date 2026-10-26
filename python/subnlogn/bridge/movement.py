"""Address movements of the bridge by Lemma 12 (SPEC §7.2; SPEC_WALSH §6.3; Lemma D).

The bridge storage layout is the stream of R = t_1 ... t_d records with fields [axis d] ... [axis 1], first field
most significant (index sum_i c_i A_i, c_1 least significant); every field is binary of width lg t_i, and the widths
differ by at most one bit (t_i in {r/2, r}, balanced_factors).  SPEC §7.2 prescribes
* "Reverse the input axes with O(d) nonadjacent exchanges (Lemma D, via §3.8 in M7)": the storage order
  (j_d, ..., j_1) <-> the tensor order (j_1, ..., j_d) by floor(d/2) exchanges of the fields at positions k and
  d + 1 - k (the same permutation is the storage -> natural frequency order k = Phi(u) of bridge_dft step 4);
* "expose axis h by one nonadjacent swap with the innermost axis and back" (spreading S_h; the axis DFTs of the
  direct middle): after the exchange the lines along axis h are CONTIGUOUS blocks of t_h records.
Every exchange is Lemma 12 for binary chunks, :func:`subnlogn.interchange.swap_bit_chunks`, through the schedule's
bit network with its Lemma 12 cutoffs (``schedule.net_bit``, ``lemma12_min_e``, ``lemma12_min_u``; Dev-6).
Prop 11's F2 gates XOR whole records, so the interchange runs on the record-ID stream list(range(R)) and the realized
address permutation is applied to the (re, im) arrays by one gather -- the approach of
:func:`subnlogn.m6.lemma13.swap_via_lemma12` (DEVIATIONS D12; exact: the gates act identically on every payload bit
and the composite map is asserted to be a permutation).  swap_bit_chunks keeps field names with the physical
positions (lengths move with the values), so each exchange renames the two fields: names always label the axis
whose digit a field holds, and the logical address (axis -> digit) of every record is preserved.

``Schedule.bridge_movement``: "index" (M2/M3 reference: RAM index maps, DEVIATIONS D2/D9/D13) or "lemma12" (this
module).  Instrument counters: "bridge.axis_swap" (one per Lemma 12 exchange), "bridge.axis_expose",
"bridge.axis_reverse", plus the interchange counters of the exchanges themselves.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..stream import Field, Shape

__all__ = ["axis", "storage_shape", "tensor_shape", "Mover", "mover_from_schedule", "swap_axes", "expose_axis",
           "restore_axis", "reverse_axes", "map_axis_blocks", "storage_to_tensor", "tensor_to_storage",
           "axis_lines", "MOVEMENTS"]

MOVEMENTS = ("index", "lemma12")


def axis(i: int) -> tuple:
    """Field name of axis i (1..d) of the bridge layout."""
    return ("axis", i)


def storage_shape(geom) -> Shape:
    """[axis d] ... [axis 1] (first most significant): the bridge storage layout, index sum_i c_i A_i (SPEC §7.2)."""
    return Shape(tuple(Field(axis(i), geom.tt(i), 2) for i in range(geom.d, 0, -1)))


def tensor_shape(geom) -> Shape:
    """[axis 1] ... [axis d]: the tensor order (j_1, ..., j_d) of the middle transforms (index sum_i c_i Q_i)."""
    return Shape(tuple(Field(axis(i), geom.tt(i), 2) for i in range(1, geom.d + 1)))


@dataclass(frozen=True)
class Mover:
    """The bit network (a compiled F2 ``Network``), the Lemma 12 cutoffs (``InterchangePolicy``) and an optional
    Instrument used by every exchange."""

    net: object
    policy: object
    inst: object = None


def mover_from_schedule(ctx) -> Mover:
    """The schedule's bit test network (``net_bit``, compiled and cached in ``ctx.tables``) and Lemma 12 cutoffs
    (``lemma12_min_e``, ``lemma12_min_u``), with ``ctx.inst`` (SPEC §6.3 TestPolicy; m6.engine)."""
    from ..interchange import InterchangePolicy
    from ..m6.engine import compiled_fixture
    sch = ctx.schedule
    return Mover(net=compiled_fixture(sch.net_bit, ctx.tables),
                 policy=InterchangePolicy(lemma12_min_e=sch.lemma12_min_e, lemma12_min_u=sch.lemma12_min_u),
                 inst=ctx.inst)


def _hit(inst, name: str, n: int = 1) -> None:
    if inst is not None:
        inst.hit(name, n)


def swap_axes(arrays, shape: Shape, a, b, mover: Mover):
    """Exchange the digits of the binary fields named ``a`` and ``b`` (any positions, widths differing by at most
    one bit) by ONE Lemma 12 interchange, :func:`swap_bit_chunks`, on record IDs, then gather every array of
    ``arrays`` with the realized permutation.  The two fields are renamed so that names follow the digits.
    Returns (new arrays, new shape) [Pr L1561-1580, L1669-1692; SPEC §3.8]."""
    from ..interchange import swap_bit_chunks
    V = shape.volume
    if any(len(arr) != V for arr in arrays):
        raise ValueError("array length differs from the shape volume")
    first, second = (a, b) if shape.index(a) < shape.index(b) else (b, a)
    ids, sh = swap_bit_chunks(list(range(V)), shape, first, second, mover.net, mover.policy, mover.inst)
    if sh.names != shape.names:
        raise AssertionError("swap_bit_chunks must keep the field order")
    if (sh.length(first), sh.length(second)) != (shape.length(second), shape.length(first)):
        raise AssertionError("swap_bit_chunks must move the field lengths with the digits")
    if len(ids) != V or sorted(ids) != list(range(V)):
        raise AssertionError("Lemma 12 on record IDs must realize an address permutation")
    tmp = ("swap-tmp", first)
    sh = sh.rename(first, tmp).rename(second, first).rename(tmp, second)
    sh = Shape(tuple(Field(f.name, f.length, 2) for f in sh.fields), shape.payload_bits)
    _hit(mover.inst, "bridge.axis_swap")
    return [[arr[i] for i in ids] for arr in arrays], sh


def expose_axis(arrays, shape: Shape, h: int, mover: Mover):
    """Expose axis h: one nonadjacent Lemma 12 exchange with the innermost field (SPEC §7.2), so that the lines along
    axis h become contiguous blocks of t_h records.  Returns (arrays, shape, partner) where ``partner`` is the axis
    name that was innermost (None if axis h already was: no exchange)."""
    inner = shape.names[-1]
    if inner == axis(h):
        return arrays, shape, None
    arrays, shape = swap_axes(arrays, shape, axis(h), inner, mover)
    _hit(mover.inst, "bridge.axis_expose")
    return arrays, shape, inner


def restore_axis(arrays, shape: Shape, h: int, partner, mover: Mover):
    """Undo :func:`expose_axis`: the same exchange again ("and back", SPEC §7.2)."""
    if partner is None:
        return arrays, shape
    return swap_axes(arrays, shape, axis(h), partner, mover)


def reverse_axes(arrays, shape: Shape, mover: Mover):
    """Reverse the field order with floor(d/2) nonadjacent Lemma 12 exchanges of the fields at positions k and
    d + 1 - k (SPEC §7.2 "O(d) nonadjacent exchanges"; SPEC_WALSH §6.3): storage <-> tensor order."""
    names = shape.names
    n = len(names)
    for k in range(n // 2):
        arrays, shape = swap_axes(arrays, shape, names[k], names[n - 1 - k], mover)
    if shape.names != tuple(reversed(names)):
        raise AssertionError("reverse_axes did not reverse the axis order")
    _hit(mover.inst, "bridge.axis_reverse")
    return arrays, shape


def map_axis_blocks(arrays, shape: Shape, h: int, mover: Mover, fn):
    """Expose axis h, apply ``fn(digits, *block)`` to every CONTIGUOUS block of t_h records (one line along axis h,
    in increasing j_h; ``digits`` = {axis index: digit} of the other axes, decoded from the block index of the
    exposed layout), write the returned block back, and restore the layout.  Returns the new arrays."""
    arrays, sh, partner = expose_axis(arrays, shape, h, mover)
    others = [(f.name[1], f.length) for f in sh.fields[:-1]]
    t = sh.fields[-1].length
    out = [list(arr) for arr in arrays]
    for blk in range(sh.volume // t):
        digits, rem = {}, blk
        for i, L in reversed(others):
            rem, digits[i] = divmod(rem, L)
        lo = blk * t
        res = fn(digits, *[arr[lo:lo + t] for arr in out])
        for arr, new in zip(out, res):
            arr[lo:lo + t] = new
    out, sh = restore_axis(out, sh, h, partner, mover)
    if sh.names != shape.names or sh.lengths != shape.lengths:
        raise AssertionError("map_axis_blocks must restore the layout")
    return out


# ----------------------------------------------------------------------------------------------- schedule dispatch
def _mode(ctx) -> str:
    mode = getattr(ctx.schedule, "bridge_movement", "index")
    if mode not in MOVEMENTS:
        raise ValueError(f"bridge_movement must be one of {MOVEMENTS}, not {mode!r}")
    return mode


def _tensor_index_map(geom) -> list[int]:
    """The reference index map storage position sum_i c_i A_i -> tensor position sum_i c_i Q_i (= Phi)."""
    return geom.storage_to_freq()


def storage_to_tensor(ctx, re, im, geom):
    """Storage order -> tensor order (j_1 most significant).  "index": the RAM index map (M2/M3 reference);
    "lemma12": :func:`reverse_axes` (floor(d/2) Lemma 12 exchanges).  The same permutation is bridge_dft's
    storage -> natural frequency order k = Phi(u)."""
    if _mode(ctx) == "lemma12":
        (re, im), _ = reverse_axes([re, im], storage_shape(geom), mover_from_schedule(ctx))
        return re, im
    perm = _tensor_index_map(geom)
    out_re, out_im = [0] * geom.R, [0] * geom.R
    for s, k in enumerate(perm):
        out_re[k], out_im[k] = re[s], im[s]
    return out_re, out_im


def tensor_to_storage(ctx, re, im, geom):
    """Tensor order -> storage order (the inverse reversal; same exchanges in the "lemma12" mode)."""
    if _mode(ctx) == "lemma12":
        (re, im), _ = reverse_axes([re, im], tensor_shape(geom), mover_from_schedule(ctx))
        return re, im
    perm = _tensor_index_map(geom)
    return [re[k] for k in perm], [im[k] for k in perm]


def axis_lines(ctx, re, im, geom, h: int, fn):
    """Apply ``fn(digits, vr, vi) -> (ur, ui)`` to every line along axis h (lines in increasing j_h; ``digits`` =
    {i: c_i} of the other axes).  "index": the lines are gathered by ``geom.line_indices(h)`` (RAM index maps);
    "lemma12": :func:`map_axis_blocks` (expose axis h by one Lemma 12 exchange, contiguous blocks, exchange back).
    Returns (re, im) in storage order."""
    if _mode(ctx) == "lemma12":
        return tuple(map_axis_blocks([re, im], storage_shape(geom), h, mover_from_schedule(ctx), fn))
    out_re, out_im = list(re), list(im)
    for line in geom.line_indices(h):
        c = geom.digits(line[0])
        digits = {i + 1: ci for i, ci in enumerate(c) if i + 1 != h}
        ur, ui = fn(digits, [re[i] for i in line], [im[i] for i in line])
        for k, i in enumerate(line):
            out_re[i], out_im[i] = ur[k], ui[k]
    return out_re, out_im
