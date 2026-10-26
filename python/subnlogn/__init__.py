"""subnlogn: exact-arithmetic reference implementation of the sub-n log n integer multiplication algorithm of
"A simpler algorithm for integer multiplication below n log n, with a machine-checked proof" (see README.md).

Entry point: ``from subnlogn.multiply import multiply``; ``multiply(a, b, schedule=..., products=...)``.
Modules:

* :mod:`subnlogn.fixedpoint`  -- exact dyadic fixed-point reals/complex numbers (manuscript Def. 2.1).
* :mod:`subnlogn.schedule`    -- explicit ``Schedule`` objects (faithful, test, ``test_policy``).
* :mod:`subnlogn.theorem`     -- theorem shape and cutoff; the faithful dispatcher's decision (M7).
* :mod:`subnlogn.instrument`  -- per-component call counters and record-height monitors.
* :mod:`subnlogn.rigorous`, :mod:`subnlogn.certified` -- exact-integer interval arithmetic and
  correctly rounded table entries.
* :mod:`subnlogn.tables`      -- per-level shared tables (manuscript §2.2 (a)-(d)).
* :mod:`subnlogn.fastdft2d`   -- the 2D FastDFT with the negative half-bin carrier drop-in (M1).
* :mod:`subnlogn.multiply`    -- two-call root packing, dispatch and exact recovery (Thm 7.1).
* :mod:`subnlogn.hierarchy`   -- the independent multiplier hierarchy BasicMul/Multiply1/Multiply2.
* :mod:`subnlogn.bits`        -- linear bit-string conversions (digits, carries, packing).
* :mod:`subnlogn.bridge`      -- the d-dimensional CRT-free bridge (M2).
* :mod:`subnlogn.ring`, :mod:`subnlogn.middle3` -- R_r records, Lemma 17, Lemma 16, Prop 18,
  twist and the Bluestein middle (M3).
* :mod:`subnlogn.net`         -- finite networks as data, validation, certificates (M4).
* :mod:`subnlogn.stream`, :mod:`subnlogn.interchange` -- Lemma 3/4 stream primitives and the
  interchange recursion Lemma 10 / Prop 11 / Lemma 12 (M5).
* :mod:`subnlogn.m6`          -- LayerPolicy, Lemma 13, the Prop 14 network engine (M6).
* :mod:`subnlogn.walsh`       -- the Walsh-route middle transform (M9).
* :mod:`subnlogn.checks`      -- ``require`` / ``RuntimeCheckError``: the always-on runtime checks
  of SPEC §6.8 (no ``assert`` statements in the package).
"""

if not __debug__:  # python -O / PYTHONOPTIMIZE would strip assert statements (SPEC §6.8)
    raise RuntimeError("subnlogn refuses to run under python -O: its runtime checks must stay on")
