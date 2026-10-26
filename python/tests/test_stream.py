"""Tests for subnlogn.stream: the Lemma 3 / Lemma 4 primitives and padding (SPEC §1.7, §3.3, §3.11;
Pr L454-575, L1627-1677), each checked against an explicit address oracle
new_stream[f(addr)] = old_stream[addr] with unique record ids."""

import random
from fractions import Fraction

import pytest
from hypothesis import given, settings, strategies as st

from subnlogn.stream import (
    Field, Shape, address_of, controlled_add, controlled_shift, digit_move, digit_pair_perm, digit_swap,
    index_of, negate_field, pad_ranges, pad_rows, pointwise_map, row_merge, row_split, split_map_merge,
    unit_scale, unpad_ranges, unpad_rows, xor_reduce,
)


def ids(shape):
    return list(range(shape.volume))


def check_perm(old_shape, new_shape, out, f):
    """out[index(new_shape, f(addr))] == index(old_shape, addr) for every old address."""
    assert len(out) == new_shape.volume == old_shape.volume
    for i in range(old_shape.volume):
        a = address_of(old_shape, i)
        assert out[index_of(new_shape, f(dict(a)))] == i


@st.composite
def shapes(draw, n_digits=2, radixes=(2, 3, 5)):
    """A shape with ``n_digits`` single-digit fields d0, d1, ... at random places among spectators."""
    radix = draw(st.sampled_from(radixes))
    n_spec = draw(st.integers(0, 3))
    kinds = ["d"] * n_digits + ["s"] * n_spec
    order = draw(st.permutations(kinds))
    fields, di, si = [], 0, 0
    for k in order:
        if k == "d":
            fields.append(Field(f"d{di}", radix, radix))
            di += 1
        else:
            fields.append(Field(f"s{si}", draw(st.integers(1, 4))))
            si += 1
    return Shape(tuple(fields), payload_bits=draw(st.integers(1, 8)))


@settings(max_examples=80)
@given(shapes(), st.data())
def test_digit_pair_perm(shape, data):
    L = shape.length("d0")
    pairs = [(a, b) for a in range(L) for b in range(L)]
    img = data.draw(st.permutations(pairs))
    table = dict(zip(pairs, img))
    out, sh = digit_pair_perm(ids(shape), shape, "d0", "d1", lambda a, b: table[(a, b)])
    assert sh == shape

    def f(a):
        a["d0"], a["d1"] = table[(a["d0"], a["d1"])]
        return a
    check_perm(shape, sh, out, f)
    out2, _ = digit_swap(ids(shape), shape, "d1", "d0")
    check_perm(shape, shape, out2, lambda a: {**a, "d0": a["d1"], "d1": a["d0"]})


def test_digit_pair_perm_rejects_non_bijection_and_multidigit():
    sh = Shape((Field("a", 3, 3), Field("b", 3, 3)))
    with pytest.raises(ValueError):
        digit_pair_perm(ids(sh), sh, "a", "b", lambda x, y: (0, 0))
    sh2 = Shape((Field("a", 9, 3), Field("b", 3, 3)))
    with pytest.raises(ValueError):
        digit_swap(ids(sh2), sh2, "a", "b")


@settings(max_examples=80)
@given(shapes(n_digits=1), st.data())
def test_digit_move(shape, data):
    j = data.draw(st.integers(0, len(shape.fields) - 1))
    out, sh = digit_move(ids(shape), shape, "d0", j)
    assert sh.names[j] == "d0" and [n for n in sh.names if n != "d0"] == [n for n in shape.names if n != "d0"]
    check_perm(shape, sh, out, lambda a: a)  # addresses keep their values; only the field order moves


@settings(max_examples=40)
@given(shapes(n_digits=1))
def test_split_map_merge(shape):
    out, sh = split_map_merge(ids(shape), shape, "d0", lambda vals: list(reversed(vals)))
    L = shape.length("d0")
    check_perm(shape, sh, out, lambda a: {**a, "d0": L - 1 - a["d0"]})


def test_pointwise_map_and_xor():
    a, b = [1, 2, 3, 4], [8, 8, 0, 1]
    assert pointwise_map([a, b], lambda x, y: (x ^ y, y)) == [[9, 10, 3, 5], b]
    assert xor_reduce([a, b, [1, 1, 1, 1]]) == [8, 11, 2, 4]


@settings(max_examples=60)
@given(st.integers(1, 3), st.integers(1, 4), st.integers(1, 3), st.integers(1, 3), st.data())
def test_row_split_merge(W, k, P, B, data):
    R = W * k
    shape = Shape((Field("p", P), Field("r", R), Field("b", B)))
    roles, rsh = row_split(ids(shape), shape, "r", W)
    assert rsh.length("r") == k and all(len(x) == P * k * B for x in roles)
    for w in range(W):
        for i, rec in enumerate(roles[w]):
            a = address_of(rsh, i)
            assert rec == index_of(shape, {"p": a["p"], "r": W * a["r"] + w, "b": a["b"]})
    order = data.draw(st.permutations(range(W)))
    out, sh = row_merge(roles, rsh, "r", order)
    assert sh == shape
    for i, rec in enumerate(out):
        a = address_of(shape, i)
        g, w = divmod(a["r"], W)
        assert rec == index_of(shape, {"p": a["p"], "r": W * g + order[w], "b": a["b"]})
    with pytest.raises(ValueError):
        row_split(ids(shape), shape, "r", W + 1) if R % (W + 1) else row_split([], shape, "r", W)


@settings(max_examples=80)
@given(st.sampled_from([(3, 1), (3, 2), (2, 3), (5, 1), (9, 1)]), st.integers(0, 2), st.data())
def test_controlled_shift_and_add(QB, n_ctrl, data):
    q, b = QB
    Q = q ** b
    fields = [Field(f"c{i}", data.draw(st.integers(1, 4))) for i in range(n_ctrl)]
    fields.insert(data.draw(st.integers(0, len(fields))), Field("sp", data.draw(st.integers(1, 3))))
    fields += [Field("y", Q, q), Field("z", data.draw(st.integers(1, 3)))]
    shape = Shape(tuple(fields))
    ctrls = [f"c{i}" for i in range(n_ctrl)]
    table = {}

    def off(*vals):
        if vals not in table:
            table[vals] = random.Random(hash(vals)).randrange(-50, 50)
        return table[vals]
    out, sh = controlled_shift(ids(shape), shape, "y", ctrls, off)
    check_perm(shape, sh, out, lambda a: {**a, "y": (a["y"] + off(*[a[c] for c in ctrls])) % Q})
    with pytest.raises(AssertionError):
        controlled_shift(ids(shape), shape, "c0" if n_ctrl else "sp", ["y"], off)
    if n_ctrl:
        sh2 = shape.replace_field("c0", length=Q)
        out2, _ = controlled_add(ids(sh2), sh2, "y", "c0", sign=-1)
        check_perm(sh2, sh2, out2, lambda a: {**a, "y": (a["y"] - a["c0"]) % Q})


@pytest.mark.parametrize("Q,c", [(27, 2), (27, Fraction(2, 5)), (9, -1), (32, 3), (32, Fraction(-1, 7)), (5, 4)])
def test_unit_scale_negate(Q, c):
    shape = Shape((Field("p", 2), Field("y", Q), Field("z", 3)))
    out, _ = unit_scale(ids(shape), shape, "y", c, Q)
    cq = Fraction(c).numerator * pow(Fraction(c).denominator, -1, Q) % Q
    check_perm(shape, shape, out, lambda a: {**a, "y": cq * a["y"] % Q})
    back, _ = unit_scale(out, shape, "y", 1 / Fraction(c))
    assert back == ids(shape)
    neg, _ = negate_field(ids(shape), shape, "y", Q)
    check_perm(shape, shape, neg, lambda a: {**a, "y": -a["y"] % Q})
    with pytest.raises(ValueError):
        unit_scale(ids(shape), shape, "y", Q // 3 * 3 if Q % 3 == 0 else 2 if Q % 2 == 0 else 5)


def test_pad_unpad_rows():
    shape = Shape((Field("p", 2), Field("r", 5), Field("b", 3)))
    out, sh = pad_rows(ids(shape), shape, "r", 9, zero=-1)
    assert sh.length("r") == 9 and sh.field("r").valid == 5
    for i, rec in enumerate(out):
        a = address_of(sh, i)
        assert rec == (-1 if a["r"] >= 5 else index_of(shape, a))
    back, sh2 = unpad_rows(out, sh, "r", zero=-1)
    assert back == ids(shape) and sh2 == shape
    out[-1] = 7
    with pytest.raises(AssertionError):
        unpad_rows(out, sh, "r", zero=-1)


@pytest.mark.parametrize("u,q,e", [(1, 3, 1), (2, 3, 2), (3, 3, 2), (4, 3, 3), (3, 5, 2)])
def test_pad_unpad_ranges(u, q, e):
    shape = Shape((Field("p", 2), Field("H", 2 ** u, 2), Field("g", 3), Field("D", 2 ** u, 2), Field("z", 2)))
    out, sh = pad_ranges(ids(shape), shape, [Field("H", q ** e, q), Field("D", q ** e, q)], zero=-1)
    assert sh.field("H").valid == 2 ** u and sh.field("D").length == q ** e
    for i, rec in enumerate(out):
        a = address_of(sh, i)
        if a["H"] >= 2 ** u or a["D"] >= 2 ** u:
            assert rec == -1
        else:
            assert rec == index_of(shape, a)
    back, sh2 = unpad_ranges(out, sh, ["H", "D"], zero=-1, restore=[Field("H", 2 ** u, 2), Field("D", 2 ** u, 2)])
    assert back == ids(shape) and sh2 == shape
    if q ** e > 2 ** u:
        out[index_of(sh, {"p": 0, "H": q ** e - 1, "g": 0, "D": 0, "z": 0})] = 5
        with pytest.raises(AssertionError):
            unpad_ranges(out, sh, ["H", "D"], zero=-1)


def test_shape_descriptor_ops():
    sh = Shape((Field("a", 27, 3), Field("b", 4)))
    s2 = sh.split_digits("a")
    assert s2.names == (("a", 0), ("a", 1), ("a", 2), "b") and s2.volume == sh.volume
    s3 = s2.join([("a", 1), ("a", 2)], "lo", radix=3)
    assert s3.field("lo").length == 9 and s3.field("lo").digits == 2
    assert s3.rename("b", "c").names[-1] == "c"
    with pytest.raises(ValueError):
        s2.join([("a", 0), ("a", 2)], "x")
    with pytest.raises(ValueError):
        Field("x", 6, 3)
