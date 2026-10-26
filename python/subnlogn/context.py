"""The explicit computation context: schedule + instrumentation + table cache.  Every algorithm
entry point takes a ``Ctx``; nothing is stored in module-level state."""

from __future__ import annotations

from dataclasses import dataclass, field

from .instrument import Instrument
from .schedule import Schedule, faithful_schedule

__all__ = ["Ctx", "WORD_BITS"]

#: Operands of at most this many bits are word-scale for the big-product counter (a product with
#: a word-scale factor is a linear-time scalar multiplication, not a packed product).
WORD_BITS = 64


@dataclass
class Ctx:
    schedule: Schedule = field(default_factory=faithful_schedule)
    inst: Instrument = field(default_factory=Instrument)
    #: Shared per-level tables (manuscript §2.2), keyed by the parameters that determine them.
    tables: dict = field(default_factory=dict)
    #: Optional capture of intermediate arrays for tests (component -> value); None disables.
    capture: dict | None = None
    #: Integer multiplier used for the large packed (Kronecker) products.  None = Python's exact
    #: built-in product (DEVIATIONS D1); a callback can plug in the MS Thm 7.1 bootstrap hierarchy
    #: or an independent O(N log N) multiplier (implementer spec r1 §8.5).
    imul: object | None = None
    #: Stage of the independent multiplier hierarchy running in this context (SPEC §6.5:
    #: "basic", "multiply1", "multiply2"), or None for the improved multiplier / plain runs.  The
    #: bridge path asserts it is None (recursion guard, :mod:`subnlogn.hierarchy`).
    hierarchy_level: str | None = None
    #: Packed-product mode: "python" = Python's exact ``*`` for the
    #: packed products (DEVIATIONS D1; every such product is counted as "python.big_product") or
    #: "hierarchy" = the independent multiplier hierarchy (SPEC §6.5; the faithful algorithm: packed
    #: products by Multiply1, whole-call fallback = Multiply2), in which the counter must stay 0.
    products: str = "python"
    #: Runtime safety net (NOT part of the algorithm): ``multiply`` checks every returned
    #: product against the operands modulo fixed word-size moduli (:mod:`subnlogn.safety`, O(n) per
    #: modulus, counted as "safety.residue_check").  On by default.
    safety_net: bool = True
    _wmul: object = field(default=None, init=False, repr=False, compare=False)

    def __post_init__(self):
        if self.products not in ("python", "hierarchy"):
            raise ValueError(f"products must be 'python' or 'hierarchy', got {self.products!r}")
        if self.products == "hierarchy" and self.imul is None:
            from .hierarchy import Hierarchy
            self.imul = Hierarchy(self.inst, self.tables).multiply1

    def word_mul(self):
        """The multiplier for the WORD-SCALE products of the data path: the 2D twists,
        drop-in solver products and leaf butterflies (MS Thm 7.1 part 3, tex L811-823: "invoking
        Multiply_1 for all inner integer products", (a) pre/post-twists and solver products, (b) leaf
        butterfly products), the bridge's scalar solver products and separable chirp/twist/phase products
        (br_r2 §6.3 and (6.5): "with the independent O(N lg N) multiplier"), and the root's pointwise
        squares.  products="hierarchy": operands of at most 64 bits are multiplied by Python's ``*`` (the
        MS base case, listing l.706: ``if n <= 64: return A*B``), larger ones by the next stage ``imul``
        (Multiply1 from the improved multiplier and from Multiply2; BasicMul from Multiply1), counted as
        "hierarchy.word_product".  Inside BasicMul (hierarchy_level "basic") every product is schoolbook by
        specification (MS Stage 0: "all butterfly twiddle products ... performed by schoolbook").
        products="python": Python's ``*``, counted as "python.word_product_over_64" whenever an operand
        exceeds 64 bits (DEVIATIONS D1; the counter stays 0 in hierarchy mode)."""
        if self._wmul is None:
            inst = self.inst
            if self.products == "hierarchy" and self.imul is not None:
                imul = self.imul

                def wmul(a: int, b: int) -> int:
                    if a.bit_length() > WORD_BITS or b.bit_length() > WORD_BITS:
                        inst.hit("hierarchy.word_product")
                        return imul(a, b)
                    return a * b
            elif self.hierarchy_level == "basic":
                def wmul(a: int, b: int) -> int:     # MS Stage 0: schoolbook by specification
                    return a * b
            else:
                def wmul(a: int, b: int) -> int:
                    if a.bit_length() > WORD_BITS or b.bit_length() > WORD_BITS:
                        inst.hit("python.word_product_over_64")
                    return a * b
            # Every call is counted as "word.call": the tests compare it with an independent
            # structural model of the word products per route (tests/path_model.py), so a product that bypasses
            # this multiplier (e.g. by an attribute call) changes the count.
            counts = inst.counts

            def counted(a: int, b: int, wmul=wmul) -> int:
                counts["word.call"] += 1
                return wmul(a, b)
            self._wmul = counted
        return self._wmul

    def product_mul(self, p_level: int):
        """The multiplier for the packed products of a level with working precision ``p_level``
        (Kronecker spreads, the bridge's overlap-add, Lemma 17's ring products): ``imul`` if set
        (hierarchy), else Python's ``*`` counted as "python.big_product" whenever the product is
        beyond word scale: min(operand bits) > 64 and max(operand bits) > 4 p_level (leaf p-bit
        fixed-point products are word operations)."""
        if self.imul is not None:
            return self.imul
        inst, T = self.inst, 4 * p_level

        def python_mul(a: int, b: int) -> int:
            la, lb = a.bit_length(), b.bit_length()
            if min(la, lb) > WORD_BITS and max(la, lb) > T:
                inst.hit("python.big_product")
            return a * b
        return python_mul

    @property
    def shr(self):
        """The rounding right-shift selected by the schedule (explicit rounding mode)."""
        return self.schedule.rounding.shr

    @property
    def div(self):
        return self.schedule.rounding.div
