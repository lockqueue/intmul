"""subnlogn.bits: the linear digit split / join and the carry propagation (MS Thm 7.1 part 1; the Kronecker and
Lemma 17 packings use the same conversions).  Round trips on random and boundary inputs, the final-carry tail of
carry_propagate (never reached from multiply, whose coefficient list has a zero tail), and the input checks."""

import pytest
from hypothesis import given, strategies as st

from subnlogn.bits import carry_propagate, digits_to_int, int_to_digits


@given(st.integers(1, 64), st.integers(0, 40), st.data())
def test_digits_round_trip(b, N, data):
    A = data.draw(st.integers(0, (1 << (b * N)) - 1)) if N else 0
    ds = int_to_digits(A, b, N)
    assert len(ds) == N and all(0 <= d < 1 << b for d in ds)
    assert sum(d << (j * b) for j, d in enumerate(ds)) == A
    assert digits_to_int(ds, b) == A


@given(st.integers(1, 40), st.lists(st.integers(0, 1 << 80), max_size=30))
def test_carry_propagate_value_and_digits(b, coeffs):
    out = carry_propagate(coeffs, b)
    assert all(0 <= d < 1 << b for d in out)
    assert digits_to_int(out, b) == sum(c << (j * b) for j, c in enumerate(coeffs))


def test_edge_cases_and_checks():
    assert int_to_digits(0, 5, 0) == [] and digits_to_int([], 5) == 0
    assert carry_propagate([1 << 20], 4) == [0, 0, 0, 0, 0, 1]          # the final-carry tail
    assert int_to_digits((1 << 12) - 1, 4, 3) == [15, 15, 15]
    for bad in (lambda: int_to_digits(-1, 4, 2), lambda: int_to_digits(1, 4, 0),
                lambda: int_to_digits(1 << 8, 4, 2), lambda: digits_to_int([16], 4),
                lambda: carry_propagate([-1], 4)):
        with pytest.raises(ValueError):
            bad()
