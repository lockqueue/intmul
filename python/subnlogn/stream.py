"""Streams of records in lexicographic address order and the elementary scans of the preprint's
Lemma 3 and Lemma 4, in the RAM backend (SPEC §1.7, §1.9, §3.3; DEVIATIONS D2 / Dev-7).

Sources: Pr = the plain-text rendering of [OAI26] (line numbers), SPEC = the internal implementation specification.

Data model (Pr §2.1, L454-475; SPEC §1.7)
-----------------------------------------
A *stream* is a Python list of records stored in the lexicographic order of a :class:`Shape`: a tuple
of address :class:`Field` s, first field most significant, plus the payload width (a trailing record
of ``payload_bits`` bits is one list element; ``payload_bits = 1`` gives one-bit payloads).
Addresses are implicit (the position in the list).  A field may be a group of radix-q digits
(``radix = q``, ``length = q**k``), a binary group (``radix = 2``) or an opaque collapsed spectator
(``radix = None``).  Splitting a field into consecutive subfields, joining adjacent fields and
renaming are descriptor-only operations (lexicographic order is unchanged, Pr L461-464).

An address permutation f moves the entry at x to f(x): (f A)(f(x)) = A(x) (Pr L461-462).

Primitive set (the interchange recursion uses only these; SPEC §3.3)
-------------------------------------------------------------------
* Lemma 3 (Pr L490-512): :func:`digit_pair_perm` (any fixed permutation of the values of two
  single-digit fields, adjacent or not), :func:`digit_move` (move one single-digit field, keeping the
  order of the others), :func:`split_map_merge` (split on one digit, pointwise map, merge) and its
  aligned-stream form :func:`pointwise_map`, :func:`row_split` / :func:`row_merge` (whole rows,
  r = W g + w, merge in any fixed order of the row classes).
* Lemma 4 (Pr L533-575): :func:`controlled_shift` y <- y + a(controls) mod Q with every control
  field physically BEFORE the target (asserted), :func:`controlled_add`, :func:`unit_scale`
  y <- c y mod Q for a unit c (inverse: ``unit_scale`` by c^-1), :func:`negate_field`.
* Padding (Pr L1627-1632, L1669-1677; SPEC §1.7): :func:`pad_rows` / :func:`unpad_rows` (zero rows
  appended within every prefix) and :func:`pad_ranges` / :func:`unpad_ranges` (numeric ranges of
  fields padded, e.g. [2^u] -> [q^e], zero records where ANY padded coordinate is invalid; the
  validity limit is kept in the descriptor; unpadding asserts the removed records are zero).

RAM backend: every primitive is one explicit index map (gathered with C-level iteration), D2.  The
spec's runtime assertions (single digits, controls before target, bijective digit maps, row
divisibility, zero padding at completed boundaries) are always checked.  An optional
:class:`subnlogn.instrument.Instrument` counts calls ("stream.<primitive>").
"""

from __future__ import annotations

import operator
from dataclasses import dataclass, replace
from fractions import Fraction
from functools import reduce
from itertools import chain
from math import gcd, prod
from typing import Callable, Hashable, Sequence

from .checks import RuntimeCheckError

__all__ = [
    "Field", "Shape", "address_of", "index_of", "specialize",
    "digit_pair_perm", "digit_swap", "digit_move", "split_map_merge", "pointwise_map",
    "row_split", "row_merge", "controlled_shift", "controlled_add", "unit_scale", "negate_field",
    "pad_rows", "unpad_rows", "pad_ranges", "unpad_ranges", "xor_reduce",
]


@dataclass(frozen=True)
class Field:
    """One address field [length] (Pr L454-457).  ``radix``: digit radix if the field is a group of
    digits (length = radix**k), else None.  ``valid``: for a padded field (SPEC §1.7) the coordinates
    >= valid are padding."""

    name: Hashable
    length: int
    radix: int | None = None
    valid: int | None = None

    def __post_init__(self):
        if not isinstance(self.length, int) or self.length < 1:
            raise ValueError(f"field {self.name!r}: length must be a positive int")
        if self.radix is not None:
            n = self.length
            while n % self.radix == 0:
                n //= self.radix
            if self.radix < 2 or n != 1:
                raise ValueError(f"field {self.name!r}: length {self.length} is not a power of {self.radix}")
        if self.valid is not None and not 1 <= self.valid <= self.length:
            raise ValueError(f"field {self.name!r}: bad validity limit {self.valid}")

    @property
    def digits(self) -> int | None:
        """Number of radix digits (None for an opaque field)."""
        if self.radix is None:
            return None
        k, n = 0, self.length
        while n > 1:
            n //= self.radix
            k += 1
        return k


@dataclass(frozen=True)
class Shape:
    """Complete Cartesian address set: ``fields`` (first most significant) and the record width."""

    fields: tuple[Field, ...]
    payload_bits: int = 1

    def __post_init__(self):
        names = [f.name for f in self.fields]
        if len(set(names)) != len(names):
            raise ValueError(f"duplicate field names in {names}")

    @property
    def names(self) -> tuple:
        return tuple(f.name for f in self.fields)

    @property
    def lengths(self) -> tuple[int, ...]:
        return tuple(f.length for f in self.fields)

    @property
    def volume(self) -> int:
        """Number of records (the logical volume is volume * payload_bits bits)."""
        return prod(self.lengths)

    def index(self, name) -> int:
        for i, f in enumerate(self.fields):
            if f.name == name:
                return i
        raise KeyError(f"no field {name!r} in {self.names}")

    def field(self, name) -> Field:
        return self.fields[self.index(name)]

    def length(self, name) -> int:
        return self.field(name).length

    def stride(self, name) -> int:
        """Number of records per unit of this field (product of the later lengths)."""
        return prod(self.lengths[self.index(name) + 1:])

    def with_fields(self, fields) -> "Shape":
        return replace(self, fields=tuple(fields))

    def replace_field(self, field_name, **changes) -> "Shape":
        i = self.index(field_name)
        fs = list(self.fields)
        fs[i] = replace(fs[i], **changes)
        return self.with_fields(fs)

    def split(self, name, parts: Sequence[Field]) -> "Shape":
        """Descriptor-only: replace field ``name`` by consecutive fields whose lengths multiply to its
        length (most significant first); lexicographic order is unchanged."""
        i = self.index(name)
        if prod(p.length for p in parts) != self.fields[i].length:
            raise ValueError("split parts must multiply to the field length")
        return self.with_fields(self.fields[:i] + tuple(parts) + self.fields[i + 1:])

    def split_digits(self, name, names: Sequence | None = None) -> "Shape":
        """Descriptor-only: a radix field of k digits -> k single-digit fields (default names
        (name, 0), ..., (name, k-1), most significant first)."""
        f = self.field(name)
        if f.radix is None:
            raise ValueError(f"field {name!r} is not a digit group")
        k = f.digits
        names = list(names) if names is not None else [(name, j) for j in range(k)]
        return self.split(name, [Field(n, f.radix, f.radix) for n in names])

    def join(self, names: Sequence, new_name, radix: int | None = None) -> "Shape":
        """Descriptor-only: merge the adjacent fields ``names`` (in physical order) into one field."""
        idx = [self.index(n) for n in names]
        if idx != list(range(idx[0], idx[0] + len(idx))):
            raise ValueError(f"fields {names} are not adjacent in physical order")
        f = Field(new_name, prod(self.fields[i].length for i in idx), radix)
        return self.with_fields(self.fields[:idx[0]] + (f,) + self.fields[idx[-1] + 1:])

    def rename(self, old, new) -> "Shape":
        return self.replace_field(old, name=new)


def address_of(shape: Shape, i: int) -> dict:
    """The address (field name -> coordinate) of position i (tests and oracles only)."""
    out = {}
    for f in reversed(shape.fields):
        i, out[f.name] = divmod(i, f.length)
    return out


def index_of(shape: Shape, addr: dict) -> int:
    """Position of an address (tests and oracles only)."""
    i = 0
    for f in shape.fields:
        v = addr[f.name]
        if not 0 <= v < f.length:
            raise RuntimeCheckError(f"index_of: coordinate {v} of field {f.name!r} out of range")
        i = i * f.length + v
    return i


def specialize(c, Q: int) -> int:
    """A rational a/b with gcd(b, Q) = 1 specialized modulo Q: a b^-1 mod Q (SPEC §3.2; Pr L548-549,
    L573-575)."""
    c = Fraction(c)
    return c.numerator * pow(c.denominator, -1, Q) % Q


# -- the index-map engine (RAM backend) ------------------------------------------------------------


def _check(stream, shape: Shape) -> None:
    if len(stream) != shape.volume:
        raise ValueError(f"stream has {len(stream)} records, shape volume is {shape.volume}")


def _hit(inst, name: str) -> None:
    if inst is not None:
        inst.hit("stream." + name)


def _gather(stream: list, pre: int, seg_old: int, idx_seg: list) -> list:
    """Concatenate, over p < pre, the records stream[p * seg_old + k] for k in idx_seg."""
    get = stream.__getitem__
    if pre == 1:
        return list(map(get, idx_seg))
    return list(map(get, chain.from_iterable(map((p * seg_old).__add__, idx_seg) for p in range(pre))))


def _blocks(order: Sequence[int], S: int) -> list:
    """Source positions of the blocks numbered ``order``, each S records long."""
    if S == 1:
        return list(order)
    return list(chain.from_iterable(range(b * S, b * S + S) for b in order))


def _region_permute(stream, shape: Shape, new_shape: Shape, lo: int, hi: int) -> list:
    """Records moved by a reordering of the fields lo..hi (digits keep their values)."""
    lens = shape.lengths
    pre, S = prod(lens[:lo]), prod(lens[hi + 1:])
    old_stride, s = {}, 1
    for f in reversed(shape.fields[lo:hi + 1]):
        old_stride[f.name] = s
        s *= f.length
    order = [0]
    for f in new_shape.fields[lo:hi + 1]:
        st = old_stride[f.name]
        order = [o + d * st for o in order for d in range(f.length)]
    return _gather(stream, pre, s * S, _blocks(order, S))


def _single_digit(f: Field) -> None:
    if f.radix is None or f.length != f.radix:
        raise ValueError(f"Lemma 3 acts on single radix digits; field {f.name!r} has length {f.length}"
                         f" and radix {f.radix}")


# -- Lemma 3 ----------------------------------------------------------------------------------------


def digit_pair_perm(stream: list, shape: Shape, f1, f2, perm: Callable[[int, int], tuple[int, int]],
                    inst=None) -> tuple[list, Shape]:
    """Lemma 3(1) (Pr L491-492): apply the fixed permutation ``perm`` of the pair of digit values
    (v1, v2) -> (w1, w2) at the single-digit fields f1, f2 (adjacent or not), every other coordinate
    unchanged.  ``perm`` is checked to be a bijection of [L1] x [L2]."""
    _check(stream, shape)
    i1, i2 = shape.index(f1), shape.index(f2)
    if i1 == i2:
        raise ValueError("digit_pair_perm needs two distinct fields")
    if i1 > i2:
        return digit_pair_perm(stream, shape, f2, f1, lambda a, b: perm(b, a)[::-1], inst)
    F1, F2 = shape.fields[i1], shape.fields[i2]
    _single_digit(F1)
    _single_digit(F2)
    _hit(inst, "digit_pair_perm")
    L1, L2, lens = F1.length, F2.length, shape.lengths
    pre, mid, S = prod(lens[:i1]), prod(lens[i1 + 1:i2]), prod(lens[i2 + 1:])
    inv = {}
    for v1 in range(L1):
        for v2 in range(L2):
            w1, w2 = perm(v1, v2)
            if not (0 <= w1 < L1 and 0 <= w2 < L2) or (w1, w2) in inv:
                raise ValueError("digit_pair_perm: perm is not a bijection of the digit pairs")
            inv[(w1, w2)] = (v1, v2)
    order = []
    for w1 in range(L1):
        for b in range(mid):
            for w2 in range(L2):
                v1, v2 = inv[(w1, w2)]
                order.append((v1 * mid + b) * L2 + v2)
    return _gather(stream, pre, L1 * mid * L2 * S, _blocks(order, S)), shape


def digit_swap(stream: list, shape: Shape, f1, f2, inst=None) -> tuple[list, Shape]:
    """Lemma 3(1) with the transposition (v1, v2) -> (v2, v1): interchange two single digits."""
    return digit_pair_perm(stream, shape, f1, f2, lambda a, b: (b, a), inst)


def digit_move(stream: list, shape: Shape, name, new_index: int, inst=None) -> tuple[list, Shape]:
    """Lemma 3(2) (Pr L493-494): move the single-digit field ``name`` so that it becomes field number
    ``new_index`` of the new shape, preserving the order of all other fields."""
    _check(stream, shape)
    i = shape.index(name)
    f = shape.fields[i]
    _single_digit(f)
    if not 0 <= new_index < len(shape.fields):
        raise ValueError("digit_move: bad target position")
    _hit(inst, "digit_move")
    fs = list(shape.fields)
    fs.pop(i)
    fs.insert(new_index, f)
    new_shape = shape.with_fields(fs)
    if new_index == i:
        return list(stream), new_shape
    lo, hi = min(i, new_index), max(i, new_index)
    return _region_permute(stream, shape, new_shape, lo, hi), new_shape


def split_map_merge(stream: list, shape: Shape, digit, fn: Callable[[list], list],
                    inst=None) -> tuple[list, Shape]:
    """Lemma 3(3) (Pr L495-496): split on the single-digit field ``digit``, apply the fixed pointwise
    map ``fn`` (list of L aligned records -> list of L records) and merge back."""
    _check(stream, shape)
    i = shape.index(digit)
    _single_digit(shape.fields[i])
    _hit(inst, "split_map_merge")
    lens = shape.lengths
    L, pre, S = lens[i], prod(lens[:i]), prod(lens[i + 1:])
    out = list(stream)
    seg = L * S
    for p in range(pre):
        base = p * seg
        for c in range(S):
            new = list(fn(stream[base + c:base + seg:S]))
            if len(new) != L:
                raise ValueError("split_map_merge: the map must return one record per digit value")
            out[base + c:base + seg:S] = new
    return out, shape


def pointwise_map(streams: Sequence[list], fn: Callable, inst=None) -> list[list]:
    """The aligned-stream step of Lemma 3(3) (Pr L495-496, L510-516): streams with identical shapes are
    read in parallel and ``fn`` maps the tuple of aligned records to a tuple of new records.  Used for
    the pointwise gates of Prop 11 (Pr L1484)."""
    n = len(streams[0])
    if any(len(s) != n for s in streams):
        raise ValueError("pointwise_map: streams are not aligned")
    _hit(inst, "pointwise_map")
    res = list(map(fn, *streams))
    return [list(col) for col in zip(*res)] if res else [[] for _ in streams]


def row_split(stream: list, shape: Shape, row_field, W: int, inst=None) -> tuple[list[list], Shape]:
    """Lemma 3(4) (Pr L497-499, L510-513; SPEC §1.7): within every prefix, row r = W g + w goes to
    stream w with local row g.  Requires W | R (all role streams then have identical shape)."""
    _check(stream, shape)
    i = shape.index(row_field)
    lens = shape.lengths
    R = lens[i]
    if W < 1 or R % W:
        raise ValueError(f"row_split: W = {W} must divide the row count {R}")
    _hit(inst, "row_split")
    pre, S, Rw = prod(lens[:i]), prod(lens[i + 1:]), R // W
    role_shape = shape.replace_field(row_field, length=Rw, radix=None, valid=None)
    outs = [_gather(stream, pre, R * S, _blocks([W * g + w for g in range(Rw)], S)) for w in range(W)]
    return outs, role_shape


def row_merge(streams: Sequence[list], role_shape: Shape, row_field, source_of_class: Sequence[int],
              inst=None) -> tuple[list, Shape]:
    """Inverse of :func:`row_split` with a fixed order of the row classes (Pr L497-499, L1495-1496):
    output row W g + w (within every prefix) is row g of stream ``source_of_class[w]``."""
    W = len(streams)
    if sorted(source_of_class) != list(range(W)):
        raise ValueError("row_merge: source_of_class must be a permutation of the streams")
    for s in streams:
        _check(s, role_shape)
    _hit(inst, "row_merge")
    i = role_shape.index(row_field)
    lens = role_shape.lengths
    Rw, pre, S = lens[i], prod(lens[:i]), prod(lens[i + 1:])
    Vw = len(streams[0])
    concat = list(chain.from_iterable(streams[source_of_class[w]] for w in range(W)))
    idx = list(chain.from_iterable(range(w * Vw + g * S, w * Vw + g * S + S)
                                   for g in range(Rw) for w in range(W)))
    shape = role_shape.replace_field(row_field, length=W * Rw, radix=None, valid=None)
    return _gather(concat, pre, Rw * S, idx), shape


# -- Lemma 4 ----------------------------------------------------------------------------------------


def controlled_shift(stream: list, shape: Shape, target, controls: Sequence, offset_fn: Callable[..., int],
                     inst=None) -> tuple[list, Shape]:
    """Lemma 4 (Pr L533-547, L550-553): y <- y + a(controls) mod Q on the target field y in [Q], where
    the offset a = ``offset_fn(*control values)`` is computed per fiber.  Every control field must lie
    physically BEFORE the target (asserted, Pr L530-531); spectator fields anywhere are allowed.  Each
    fiber of Q blocks is split at Q - a and its two pieces are written in swapped order."""
    _check(stream, shape)
    it = shape.index(target)
    ics = [shape.index(c) for c in controls]
    if any(ic >= it for ic in ics):
        raise AssertionError(f"Lemma 4: controls {list(controls)} must precede the target {target!r}")
    _hit(inst, "controlled_shift")
    lens = shape.lengths
    Q, pre, S = lens[it], prod(lens[:it]), prod(lens[it + 1:])
    seg = Q * S
    dec = [(prod(lens[ic + 1:it]), lens[ic]) for ic in ics]
    out: list = []
    cache: dict = {}
    for p in range(pre):
        key = tuple((p // st) % L for st, L in dec)
        a = cache.get(key)
        if a is None:
            a = cache[key] = offset_fn(*key) % Q
        base = p * seg
        k = base + ((Q - a) % Q) * S
        out.extend(stream[k:base + seg])
        out.extend(stream[base:k])
    return out, shape


def controlled_add(stream: list, shape: Shape, target, source, sign: int = 1,
                   inst=None) -> tuple[list, Shape]:
    """Lemma 4 special case: y <- y + sign * x mod Q, with the control field x before the target y."""
    return controlled_shift(stream, shape, target, [source], lambda x: sign * x, inst)


def _unit_permute(stream, shape: Shape, target, c: int, Q: int) -> list:
    it = shape.index(target)
    lens = shape.lengths
    pre, S = prod(lens[:it]), prod(lens[it + 1:])
    cinv = pow(c, -1, Q)
    return _gather(stream, pre, Q * S, _blocks([(cinv * y) % Q for y in range(Q)], S))


def unit_scale(stream: list, shape: Shape, target, c, modulus: int | None = None,
               inst=None) -> tuple[list, Shape]:
    """Lemma 4 (Pr L554-566): y <- c y mod Q for a rational unit c (numerator and denominator prime to
    q, specialized modulo Q = the target length).  The inverse is ``unit_scale`` by 1/c."""
    _check(stream, shape)
    Q = shape.length(target)
    if modulus is not None and modulus != Q:
        raise ValueError(f"unit_scale: modulus {modulus} != target length {Q}")
    c = specialize(c, Q)
    if gcd(c, Q) != 1:
        raise ValueError(f"unit_scale: {c} is not a unit modulo {Q}")
    _hit(inst, "unit_scale")
    if c == 1 % Q:
        return list(stream), shape
    return _unit_permute(stream, shape, target, c, Q), shape


def negate_field(stream: list, shape: Shape, target, modulus: int | None = None,
                 inst=None) -> tuple[list, Shape]:
    """Lemma 4 (Pr L567-571): y <- -y mod Q (block 0 fixed, the other Q - 1 blocks reversed)."""
    _check(stream, shape)
    Q = shape.length(target)
    if modulus is not None and modulus != Q:
        raise ValueError(f"negate_field: modulus {modulus} != target length {Q}")
    _hit(inst, "negate_field")
    if Q == 1:
        return list(stream), shape
    return _unit_permute(stream, shape, target, Q - 1, Q), shape


# -- padding ----------------------------------------------------------------------------------------


def pad_rows(stream: list, shape: Shape, row_field, new_length: int, zero=0,
             inst=None) -> tuple[list, Shape]:
    """Append zero rows within every prefix until the row field has ``new_length`` rows (Lemma 12,
    Pr L1627-1632: R' = W^k ceil(R / W^k))."""
    _check(stream, shape)
    i = shape.index(row_field)
    lens = shape.lengths
    R, pre, S = lens[i], prod(lens[:i]), prod(lens[i + 1:])
    if new_length < R:
        raise ValueError("pad_rows: cannot shrink")
    _hit(inst, "pad_rows")
    seg, extra = R * S, [zero] * ((new_length - R) * S)
    out: list = []
    for p in range(pre):
        out.extend(stream[p * seg:(p + 1) * seg])
        out.extend(extra)
    return out, shape.replace_field(row_field, length=new_length, radix=None, valid=R)


def unpad_rows(stream: list, shape: Shape, row_field, length: int | None = None, zero=0,
               inst=None) -> tuple[list, Shape]:
    """Remove the rows >= ``length`` (default: the field's validity limit) within every prefix,
    asserting that they are zero (Pr L1641-1644: padded rows stay zero at completed boundaries)."""
    _check(stream, shape)
    f = shape.field(row_field)
    length = f.valid if length is None else length
    i = shape.index(row_field)
    lens = shape.lengths
    R, pre, S = lens[i], prod(lens[:i]), prod(lens[i + 1:])
    if length is None or not 1 <= length <= R:
        raise ValueError("unpad_rows: bad length")
    _hit(inst, "unpad_rows")
    seg, keep = R * S, length * S
    out: list = []
    for p in range(pre):
        base = p * seg
        out.extend(stream[base:base + keep])
        if any(x != zero for x in stream[base + keep:base + seg]):
            raise AssertionError("unpad_rows: a padded row is not zero at a completed boundary")
    return out, shape.replace_field(row_field, length=length, valid=None)


def _range_index(new_shape: Shape, old_shape: Shape, limits: dict, sentinel: int) -> list:
    """Source positions (or ``sentinel``) of every record of ``new_shape`` read from ``old_shape``;
    coordinates of field n at or above limits[n] are invalid."""
    old_stride, s = {}, 1
    for f in reversed(old_shape.fields):
        old_stride[f.name] = s
        s *= f.length
    idx = [0]
    for f in new_shape.fields:
        st, lim = old_stride[f.name], limits.get(f.name, f.length)
        idx = [o + d * st if (o >= 0 and d < lim) else -1 for o in idx for d in range(f.length)]
    return [sentinel if o < 0 else o for o in idx]


def pad_ranges(stream: list, shape: Shape, new_fields: Sequence[Field], zero=0,
               inst=None) -> tuple[list, Shape]:
    """Pad the numeric ranges of some fields (e.g. [2^u] -> [q^e], Pr L1669-1677; SPEC §1.7): each
    ``Field`` in ``new_fields`` replaces the field of the same name and must be at least as long; the
    old length becomes its validity limit; records where ANY padded coordinate is invalid are zero.
    Lexicographic order of the existing records is preserved (numeric order of both ranges)."""
    _check(stream, shape)
    fs = list(shape.fields)
    limits = {}
    for nf in new_fields:
        i = shape.index(nf.name)
        old = fs[i]
        if nf.length < old.length:
            raise ValueError("pad_ranges: cannot shrink a field")
        fs[i] = replace(nf, valid=old.length)
        limits[nf.name] = old.length
    _hit(inst, "pad_ranges")
    new_shape = shape.with_fields(fs)
    ext = list(stream) + [zero]
    return list(map(ext.__getitem__, _range_index(new_shape, shape, limits, len(stream)))), new_shape


def unpad_ranges(stream: list, shape: Shape, names: Sequence, zero=0, restore: Sequence[Field] = (),
                 inst=None) -> tuple[list, Shape]:
    """Inverse of :func:`pad_ranges`: delete every record with some named coordinate at or above its
    validity limit, asserting that they are zero (the genuine set is preserved by completed
    interchanges, Pr L1674-1677).  ``restore`` optionally gives the restored field descriptors."""
    _check(stream, shape)
    fs, rest = list(shape.fields), {f.name: f for f in restore}
    for n in names:
        i = shape.index(n)
        f = fs[i]
        if f.valid is None:
            raise ValueError(f"unpad_ranges: field {n!r} is not padded")
        fs[i] = rest.get(n, Field(n, f.valid))
        if fs[i].length != f.valid:
            raise ValueError(f"unpad_ranges: restored field {n!r} must have length {f.valid}")
    _hit(inst, "unpad_ranges")
    new_shape = shape.with_fields(fs)
    idx = _range_index(new_shape, shape, {}, -1)  # positions of the genuine records
    mask = bytearray(len(stream))
    for j in idx:
        mask[j] = 1
    if any(x != zero for x, k in zip(stream, mask) if not k):
        raise AssertionError("unpad_ranges: a padding record is not zero at a completed boundary")
    return list(map(stream.__getitem__, idx)), new_shape


def xor_reduce(streams: Sequence[list]) -> list:
    """Pointwise XOR of aligned streams of int records (helper for F2 gates, Lemma 3(3))."""
    return reduce(lambda a, b: list(map(operator.xor, a, b)), streams)
