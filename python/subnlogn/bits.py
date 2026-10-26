"""Linear-time conversions between Python integers and fixed-width digit (bit-field) sequences.

These implement the concatenation and splitting of bit strings that the tape algorithm performs by
a linear scan (input digits of the multiplier, Kronecker / Lemma 17 packing, carry propagation of
the recovered product).  They use only power-of-two-base string conversions of Python integers
(``format(x, "b")`` and ``int(s, 2)``, both linear in CPython) plus per-digit word operations; no
big-integer multiplication, division or repeated shifting of a long integer (which would cost
O(n * #digits)).  See the big-integer site table in tests/test_bigint_sites.py.
"""

from __future__ import annotations

__all__ = ["int_to_digits", "digits_to_int", "carry_propagate"]


def int_to_digits(A: int, b: int, N: int) -> list[int]:
    """The N base-2^b digits (least significant first) of 0 <= A < 2^(bN): one binary string
    conversion and N slices."""
    if A < 0:
        raise ValueError("int_to_digits needs A >= 0")
    if N == 0:
        if A:
            raise ValueError("A does not fit in 0 digits")
        return []
    s = format(A, "b")
    if len(s) > b * N:
        raise ValueError("A does not fit in N digits of b bits")
    s = s.zfill(b * N)
    L = len(s)
    return [int(s[L - (j + 1) * b:L - j * b], 2) for j in range(N)]


def digits_to_int(digits: list[int], b: int) -> int:
    """sum_j digits[j] 2^(jb) for digits 0 <= d_j < 2^b (least significant first): one binary
    string join and one conversion."""
    if not digits:
        return 0
    top = 1 << b
    for d in digits:
        if not 0 <= d < top:
            raise ValueError("digit out of range [0, 2^b)")
    return int("".join(format(d, f"0{b}b") for d in reversed(digits)), 2)


def carry_propagate(coeffs: list[int], b: int) -> list[int]:
    """Carry propagation in radix 2^b (MS Thm 7.1 part 1): nonnegative coefficients c_j become the
    base-2^b digits of sum_j c_j 2^(jb), by one left-to-right scan with a word-size carry."""
    mask = (1 << b) - 1
    out, carry = [], 0
    for c in coeffs:
        if c < 0:
            raise ValueError("carry propagation expects nonnegative coefficients")
        v = c + carry
        out.append(v & mask)
        carry = v >> b
    while carry:
        out.append(carry & mask)
        carry >>= b
    return out
