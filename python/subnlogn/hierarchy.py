"""The independent multiplier hierarchy (SPEC §6.5; MS ``thm:main``; S1 §8.5 = S2 §8.5).

    BasicMul   = two-call root + one base radix-2 FFT (every FastDFT node a leaf; no packed products)
    Multiply1  = the 2D negative-carrier multiplier (M1, faithful schedule), packed products by BasicMul
    Multiply2  = the same, packed products by Multiply1

The improved multiplier (bridge + Bluestein/Walsh middle) uses Multiply1 for Lemma 17's packed
products and the bridge's packed overlap-add, and Multiply2 for whole-call fallback.  Both are
obtained from :func:`hierarchy_ctx`: a context whose ``imul`` is Multiply1 -- the faithful
dispatcher's 2D fallback with that context IS Multiply2, and the bridge path sends its packed
products to Multiply1.  No call from BasicMul/Multiply1/Multiply2 may reach the improved multiplier:
their contexts carry ``hierarchy_level`` and the bridge entry asserts it is unset (recursion guard).

DEVIATIONS D1 permits Python ``int.__mul__`` for inner products; the backend is always an explicit
parameter of the context (``Ctx.imul``), never global state.  Every product is exact either way.
"""

from __future__ import annotations

from dataclasses import replace

from .context import Ctx
from .instrument import Instrument
from .schedule import Schedule, faithful_schedule

__all__ = ["basic_schedule", "Hierarchy", "hierarchy_ctx", "assert_improved_allowed"]


def basic_schedule() -> Schedule:
    """BasicMul's schedule: the faithful precisions with every FastDFT node a leaf (one base
    radix-2 FFT per transform; MS §2.2 (d), Lemma 6.5 part 2)."""
    return replace(faithful_schedule(), name="basic", max_depth=0)


class Hierarchy:
    """BasicMul -> Multiply1 -> Multiply2 as callables (a, b) -> a*b with their own explicit
    contexts; ``inst`` counts the calls per stage ("hierarchy.<stage>").  ``stage_schedule`` is the
    2D schedule of Multiply1/Multiply2 (default: the faithful one; tests pass a forced-recursion
    test schedule so that small products already reach the lower stages -- stopping rules only)."""

    def __init__(self, inst: Instrument | None = None, tables: dict | None = None,
                 stage_schedule: Schedule | None = None, multiply1_schedule: Schedule | None = None):
        self.inst = inst if inst is not None else Instrument()
        self.tables = tables if tables is not None else {}
        self.stage_schedule = stage_schedule if stage_schedule is not None else faithful_schedule()
        self.multiply1_schedule = multiply1_schedule if multiply1_schedule is not None else \
            self.stage_schedule
        for sch in (self.stage_schedule, self.multiply1_schedule):
            if sch.bridge_d is not None:
                raise ValueError("Multiply1/Multiply2 are 2D multipliers (no bridge; SPEC §6.5)")

    def _run(self, stage: str, schedule: Schedule, imul, a: int, b: int) -> int:
        from .multiply import multiply
        self.inst.hit("hierarchy." + stage)
        ctx = Ctx(schedule=schedule, inst=self.inst, tables=self.tables, imul=imul,
                  hierarchy_level=stage, products="hierarchy" if imul is not None else "python")
        return multiply(a, b, ctx)

    def basic_mul(self, a: int, b: int) -> int:
        return self._run("basic", basic_schedule(), None, a, b)

    def multiply1(self, a: int, b: int) -> int:
        return self._run("multiply1", self.multiply1_schedule, self.basic_mul, a, b)

    def multiply2(self, a: int, b: int) -> int:
        return self._run("multiply2", self.stage_schedule, self.multiply1, a, b)


def hierarchy_ctx(schedule: Schedule | None = None, inst: Instrument | None = None,
                  tables: dict | None = None, stage_schedule: Schedule | None = None) -> Ctx:
    """A context for the improved multiplier with the independent hierarchy: packed products by
    Multiply1 (whose packed products use BasicMul).  Its 2D fallback is Multiply2 (SPEC §6.5)."""
    inst = inst if inst is not None else Instrument()
    tables = tables if tables is not None else {}
    h = Hierarchy(inst, tables, stage_schedule)
    return Ctx(schedule=schedule if schedule is not None else faithful_schedule(), inst=inst,
               tables=tables, imul=h.multiply1, products="hierarchy")


def assert_improved_allowed(ctx: Ctx) -> None:
    """Recursion guard (SPEC §6.5): the improved multiplier must not be reached from inside the
    independent hierarchy."""
    if ctx.hierarchy_level is not None:
        raise AssertionError(f"recursion guard: the improved multiplier was reached from the "
                             f"independent hierarchy stage {ctx.hierarchy_level!r} (SPEC §6.5)")
