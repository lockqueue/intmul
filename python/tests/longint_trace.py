"""Dynamic long-integer trace (test helper, not a test module).

``LongIntTrace`` runs a computation under ``sys.settrace`` with call/return events only (line events
are switched off per frame) and records, per subnlogn function ("path:function", path relative to the
package), the largest bit length of an int held in the frame's locals at return or returned (ints
directly, or inside a list/tuple of at most 64 items, one level deep).  Long operands therefore show
up in the function that creates or receives them.  ``ALLOWED_LONG`` is the allow-list: every function
permitted to hold integers beyond word scale -- routed products (A), linear scans of long operands (C),
table precomputation (D).
"""

from __future__ import annotations

import os
import sys
from collections import defaultdict

import subnlogn

PKG = os.path.dirname(os.path.abspath(subnlogn.__file__))

#: Allow-list: functions permitted to hold integers beyond word scale (classes A, C, D of the big-integer
#: site table in test_bigint_sites.py).
ALLOWED_LONG = frozenset({
    # A: the operands of routed products and the hierarchy that multiplies them
    "multiply.py:multiply", "multiply.py:_multiply", "context.py:python_mul",
    "hierarchy.py:_run", "hierarchy.py:basic_mul", "hierarchy.py:multiply1", "hierarchy.py:multiply2",
    "ring.py:signed_product", "middle3/prop18.py:_pymul",
    # C: linear scans and linear operations on long operands
    "bits.py:int_to_digits", "bits.py:digits_to_int",
    "bits.py:<genexpr>",            # digits_to_int's per-digit format: bridge slots of 4P + 16 bits
    "kronecker.py:pack", "kronecker.py:unpack", "kronecker.py:spread_row",
    "bridge/spread.py:spread_axis", "bridge/spread.py:line",      # the packed bridge filters
    "ring.py:_blocks_to_int", "ring.py:_int_to_blocks", "ring.py:pack_to_int", "ring.py:centered_extract",
    "ring.py:normalized_ring_product",
    "safety.py:check_product",                                # O(n) residues of the operands and product
    "ring.py:pack_blocks", "ring.py:_complement_increment",     # the modulus B0 = 2^(4p) has 4p + 1 bits
    # D: per-level table precomputation (the packed filters of a 2D level; certified tables below)
    "tables.py:level_tables_2d",
})
#: Whole modules of table precomputation (class D): every function may hold long integers.
ALLOWED_LONG_MODULES = ("certified.py", "certcore.py", "rigorous.py")


def _bits(v, depth: int = 0) -> int:
    if isinstance(v, bool):
        return 0
    if isinstance(v, int):
        return v.bit_length()
    if depth == 0 and isinstance(v, (list, tuple)) and len(v) <= 64:
        return max((_bits(x, 1) for x in v), default=0)
    return 0


class LongIntTrace:
    """Context manager recording max int bit lengths per subnlogn function (see module doc)."""

    def __init__(self):
        self.max_bits: dict[str, int] = defaultdict(int)

    def __enter__(self) -> "LongIntTrace":
        self._prev = sys.gettrace()
        sys.settrace(self._call)
        return self

    def __exit__(self, *exc) -> None:
        sys.settrace(self._prev)

    def _call(self, frame, event, arg):
        if event != "call" or not frame.f_code.co_filename.startswith(PKG):
            return None
        frame.f_trace_lines = False
        return self._local

    def _local(self, frame, event, arg):
        if event == "return":
            key = os.path.relpath(frame.f_code.co_filename, PKG) + ":" + frame.f_code.co_name
            m = max([_bits(v) for v in frame.f_locals.values()] + [_bits(arg)])
            if m > self.max_bits[key]:
                self.max_bits[key] = m
        return self._local

    def above(self, threshold: int) -> dict[str, int]:
        """Functions that held an int of more than ``threshold`` bits, with the max bit length."""
        return {k: v for k, v in self.max_bits.items() if v > threshold}

    def unlisted(self, threshold: int) -> dict[str, int]:
        """Functions above ``threshold`` that the allow-list does not permit to hold long integers."""
        return {k: v for k, v in self.above(threshold).items()
                if k not in ALLOWED_LONG and k.split(":")[0] not in ALLOWED_LONG_MODULES}
