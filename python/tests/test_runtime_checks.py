"""SPEC §6.8 / §5.10 runtime checks are always on (the runtime-assertion table;
the surviving mutants A27-A30).

1. ``subnlogn/`` contains no ``assert`` statement (``python -O`` strips them) and uses ``__debug__`` only in
   the import guard: every check is an explicit raise (:mod:`subnlogn.checks`).
2. ``import subnlogn`` fails under ``python -O`` and under ``PYTHONOPTIMIZE``.
3. Negative tests, one or more per runtime check:
   each deliberately violates the check (crafted input, monkeypatched upstream value or perturbed table)
   and expects the documented exception -- ``RuntimeCheckError`` for the former bare asserts,
   ``AssertionError`` (its base class) for checks that already were explicit ``raise AssertionError``,
   ``ValueError`` for argument checks of the stream primitives, ``ArithmeticError`` /
   ``CertifiedFallbackWarning`` for the certified tables.  Messages are matched, so each test pins the
   check it targets.

Rows that cannot be violated without rewriting internals (documented, not tested here):
- "headers parse and match the stream": the RAM backend has no tape headers (DEVIATIONS D2).
- "no numeric decoding inside a bit-network interchange": structural -- interchange gates XOR int records
  and Lemma 13's chunk exchanges run Lemma 12 on record IDs (D12); there is no decoding step to perturb.
  tests/test_lemma13.py::test_swap_via_lemma12_network_path moves payloads ("rec", i) that no arithmetic
  accepts.
- "Prop 18 width w + lg M": the factor M is a left shift by lg M (exact by construction), not a check; the
  narrowing that follows is guarded by the disk test (tested below).
"""

import ast
import functools
import os
import pathlib
import subprocess
import sys
import warnings
from fractions import Fraction
from types import SimpleNamespace

import pytest

from conftest import make_ctx
from subnlogn.checks import RuntimeCheckError, require

ROOT = pathlib.Path(__file__).resolve().parent.parent
PKG = ROOT / "subnlogn"

# ------------------------------------------------------------------------------------------- 1. no asserts


def test_require_semantics():
    require(True, "never formatted")
    require(1, lambda: 1 // 0)                      # a lazy message is not evaluated on success
    with pytest.raises(RuntimeCheckError, match="lazy 7"):
        require(0, lambda: f"lazy {7}")
    assert issubclass(RuntimeCheckError, AssertionError)


@functools.lru_cache(maxsize=1)
def _package_nodes() -> tuple:
    """(relative path, list of AST nodes) for every module of the package."""
    return tuple((path.relative_to(PKG), list(ast.walk(ast.parse(path.read_text(), filename=str(path)))))
                 for path in sorted(PKG.rglob("*.py")))


def test_package_has_no_assert_statements():
    """Every runtime check must survive ``python -O``, so the package has no ``assert`` statement."""
    offenders = [f"subnlogn/{rel}:{n.lineno}" for rel, nodes in _package_nodes() for n in nodes
                 if isinstance(n, ast.Assert)]
    assert len(_package_nodes()) > 50 and not offenders, f"assert statements (stripped by python -O): {offenders}"


def test_debug_flag_is_used_only_by_the_import_guard():
    users = [str(rel) for rel, nodes in _package_nodes()
             if any(isinstance(n, ast.Name) and n.id == "__debug__" for n in nodes)]
    assert users == ["__init__.py"]


# ------------------------------------------------------------------------------------------- 2. -O guard


@pytest.mark.parametrize("how", ["-O", "PYTHONOPTIMIZE"])
def test_import_refused_under_optimize(how):
    env = dict(os.environ, PYTHONPATH=str(ROOT))
    env.pop("PYTHONOPTIMIZE", None)
    cmd = [sys.executable, "-c", "import subnlogn"]
    if how == "-O":
        cmd.insert(1, "-O")
    else:
        env["PYTHONOPTIMIZE"] = "1"
    res = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, timeout=120)
    assert res.returncode != 0
    assert "subnlogn refuses to run under python -O" in res.stderr
    ok = subprocess.run([sys.executable, "-c", "import subnlogn"], cwd=ROOT, env=dict(env, PYTHONOPTIMIZE=""),
                        capture_output=True, text=True, timeout=120)
    assert ok.returncode == 0, ok.stderr


# ----------------------------------------------- 3. negative tests: recovered coefficients (multiply)


def _multiply_with_edited_z(monkeypatch, edit, n=200):
    """multiply two n-bit operands (test schedule) with Im z of the SECOND transform edited by ``edit(im, N,
    maxc)``.  The edits move chosen c_j = round(-Im z_j / 2^9) by exact integers (multiples of 2^9), so the
    measured recovery error is unchanged and only the targeted check can fire."""
    import random

    import subnlogn.multiply as mm
    from subnlogn.context import Ctx
    from subnlogn.schedule import test_schedule
    rng = random.Random(n)
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n) | 1
    bb, N = mm.root_parameters(n)[:2]
    maxc = N * ((1 << bb) - 1) ** 2
    real, calls = mm._transform, []

    def perturbed(ctx, x, R, p):
        y = real(ctx, x, R, p)
        calls.append(1)
        if len(calls) == 2:
            im = list(y.im)
            edit(im, N, maxc)
            y = type(y)(list(y.re), im, y.q)
        return y

    monkeypatch.setattr(mm, "_transform", perturbed)
    return mm.multiply(a, b, Ctx(schedule=test_schedule(base_threshold=2)))


def test_multiply_coefficient_range(monkeypatch):
    """SPEC §6.8: 0 <= c_j <= N (2^b - 1)^2 (c_0 pushed to maxc + 1)."""
    def edit(im, N, maxc):
        im[0] -= (maxc + 1) << 9
    with pytest.raises(RuntimeCheckError, match="recovered coefficient out of range"):
        _multiply_with_edited_z(monkeypatch, edit)


def test_multiply_zero_tail(monkeypatch):
    """SPEC §6.8 zero tail: c_j = 0 beyond degree 2N - 2 (mutant A27 deleted this check)."""
    def edit(im, N, maxc):
        im[2 * N - 1] -= 1 << 9                                  # c_{2N-1} = 1, still in range
    with pytest.raises(RuntimeCheckError, match="coefficient beyond degree 2N-2"):
        _multiply_with_edited_z(monkeypatch, edit)


def test_multiply_product_width(monkeypatch):
    """SPEC §6.8: product < 2^{2n} (c_{2N-2} = maxc: in range, inside the degree bound, too wide)."""
    def edit(im, N, maxc):
        im[2 * N - 2] = -(maxc << 9)
    with pytest.raises(RuntimeCheckError, match="product bit above 2n - 1"):
        _multiply_with_edited_z(monkeypatch, edit)


def test_multiply_recovery_bound(monkeypatch):
    """MS Thm 7.1 certified recovery error <= 3.19/128: reuses the regression test, whose transform
    error rounds correctly but exceeds the contract."""
    from test_regression_sweeps import test_recovery_check_is_not_tautological as recovery_check
    recovery_check(monkeypatch)


def test_multiply_hierarchy_mode_forbids_python_products(monkeypatch):
    """C3 / SPEC §6.5: in hierarchy mode a Python big product on the data path is a runtime error."""
    import subnlogn.multiply as mm

    def leaky(a, b, ctx):
        ctx.inst.hit("python.big_product")
        return a * b
    monkeypatch.setattr(mm, "_multiply", leaky)
    with pytest.raises(RuntimeCheckError, match="hierarchy mode used Python"):
        mm.multiply(3, 5, products="hierarchy")


# ------------------------------------------------------ FastDFT precondition, 1/8 disk, Prop 18 disk


def test_fastdft_precondition():
    """MS Thm 6.3: ||x||_inf <= 2^p (complex modulus) at every FastDFT node.  2^p + 2^-(p+2) must fail
    (mutant A29 allowed up to 2^{p+4}); so must Re = Im = 2^p, which a componentwise test would accept
    .  |x_j| = 2^p and a complex entry just inside the circle pass."""
    from math import isqrt

    from subnlogn.fastdft2d import fast_dft
    from subnlogn.fixedpoint import FxVec
    from subnlogn.schedule import test_schedule
    sched = test_schedule(base_threshold=2)
    R, p = 64, 20
    assert not sched.level(R, p).leaf
    top = 1 << (2 * p + 2)                                       # the value 2^p on C~_{p+2}
    inside = isqrt(top * top // 2)                               # 2 inside^2 <= top^2
    for a, b, ok in ((top, 0, True), (inside, inside, True), (top + 1, 0, False), (top, top, False)):
        re, im = [0] * R, [0] * R
        re[5], im[5] = a, b
        if ok:
            fast_dft(make_ctx(sched), FxVec(re, im, p + 2), R, p)
            continue
        with pytest.raises(RuntimeCheckError, match="FastDFT precondition"):
            fast_dft(make_ctx(sched), FxVec(re, im, p + 2), R, p)


class _Reached(Exception):
    pass


def test_bridge_spread_one_eighth_disk(monkeypatch):
    """r2 §5.2 / SPEC v1.2 §5.10: completed spread arrays lie in the disk of radius 1/8 (exact test).
    A spread of norm 1/4 (inside the unit disk: mutant A28's weakened test) must fail; norm exactly 1/8
    reaches the middle transform."""
    import subnlogn.bridge.bridge_dft as B
    from subnlogn.fixedpoint import FxVec
    from subnlogn.schedule import test_schedule
    R, p, d = 16, 20, 2
    sched = test_schedule(bridge_d=d)
    assert sched.bridge_constants == "r2"
    x = FxVec([1 << p] * R, [0] * R, p + 2)

    def middle(ctx, U, geom, P):
        raise _Reached
    monkeypatch.setattr(B, "middle_dft", middle)
    for shift, expect in ((3, _Reached), (2, RuntimeCheckError)):
        def spread(ctx, U, geom, h, m, w, shift=shift):
            return FxVec([1 << (U.q - shift)] * len(U.re), [0] * len(U.re), U.q)
        monkeypatch.setattr(B, "spread_axis", spread)
        with pytest.raises(expect):
            B.bridge_dft(make_ctx(sched), x, R, p, d)


def test_prop18_disk_test_before_narrowing():
    """SPEC §5.10: the Prop 18 output must lie in its disk (default radius 0.701) before it is narrowed.
    Constant operands c give M_C = c^2: c = 0.85 (0.7225) must fail -- mutant A30's radius 4 let it through
    -- and c = 0.83 (0.6889) passes.  The r2 caller radius 1/8 + C18 2^-q is covered by
    tests/test_regression_mutants.py::test_prop18_disk_test_uses_the_squared_radius."""
    from subnlogn.middle3.bluestein import complex_convolution
    from subnlogn.middle3.synth import Synth
    t, p, R = (4, 4), 24, 16
    sy = Synth((4,), 2, 1)

    def const(c):
        return [(int(c * (1 << p)), 0)] * R
    complex_convolution(const(Fraction(83, 100)), const(Fraction(83, 100)), t, p, sy)
    with pytest.raises(RuntimeCheckError, match="before narrowing"):
        complex_convolution(const(Fraction(85, 100)), const(Fraction(85, 100)), t, p, sy)


def test_bluestein_input_norm():
    """SPEC §5.9: the chirp identity needs ||x|| <= 0.6."""
    from subnlogn.middle3.bluestein import tensor_positive_dft
    p = 24
    x = [(0, 0)] * 16
    x[3] = (int(Fraction(61, 100) * (1 << p)), 0)
    with pytest.raises(RuntimeCheckError, match=r"\|\|x\|\| <= 0.6"):
        tensor_positive_dft(x, (4, 4), p)


# ------------------------------------------------- complete shapes, divisibility, bijective permutations


def _shape(*fields):
    from subnlogn.stream import Field, Shape
    return Shape(tuple(Field(*f) for f in fields), 1)


def test_complete_cartesian_shapes():
    """SPEC §6.8 complete Cartesian shapes: stream._check (len == volume), cnet.batched_c_layer (2^n)."""
    from subnlogn.m6.cnet import CCtx, batched_c_layer
    from subnlogn.stream import digit_swap
    with pytest.raises(ValueError, match="shape volume is 4"):
        digit_swap([0, 1, 2], _shape(("a", 2, 2), ("b", 2, 2)), "a", "b")
    with pytest.raises(ValueError, match="complete array of 2"):
        batched_c_layer([([0], [0])] * 3, [0], CCtx(net=None, d=2))


def test_divisibility_and_equal_role_volumes(monkeypatch):
    """SPEC §6.8 power-of-two / divisibility: stream.row_split (W | R), cnet.c_power_exact (rows % W == 0),
    interchange.power_swap (W^k | rows)."""
    import subnlogn.m6.cnet as C
    from subnlogn.interchange import power_swap
    from subnlogn.stream import row_split
    with pytest.raises(ValueError, match="must divide the row count 6"):
        row_split(list(range(12)), _shape(("r", 6), ("a", 2, 2)), "r", 4)
    monkeypatch.setattr(C, "is_leaf", lambda e, d, pol: False)          # reach the network branch
    with pytest.raises(AssertionError, match="row count must be divisible by W"):
        C.c_power_exact([], 3, [0], C.CCtx(net=SimpleNamespace(m=1, W=2), d=2))
    with pytest.raises(ValueError, match="not divisible by W"):
        power_swap(list(range(12)), _shape(("row", 3), ("H", 2, 2), ("D", 2, 2)), "H", "D",
                   SimpleNamespace(q=2, m=1, W=2), "row", 1)


def test_digit_pair_perm_must_be_bijective():
    from subnlogn.stream import digit_pair_perm
    with pytest.raises(ValueError, match="not a bijection"):
        digit_pair_perm(list(range(4)), _shape(("a", 2, 2), ("b", 2, 2)), "a", "b", lambda u, v: (0, v))


def _l13_shape(L):
    return _shape(("N0", 1), ("x", 1 << L, 2), ("N1", 1), ("y", 1 << L, 2), ("N2", 1), ("z", 1 << L, 2), ("N3", 1))


def test_lemma13_keys_equal_holes(monkeypatch):
    """SPEC §4.2 / C10: Lemma 13's repair asserts sorted destination keys == marked holes.  A perturbed T0
    (constant, so T0 S0^{-1} no longer permutes B) must fail."""
    import subnlogn.m6.lemma13 as L13
    f, K, rho = 3, 1, 0                                                 # 512 records, B moved
    sh, names = _l13_shape(f * K), {c: c for c in "xyz"}
    stream = list(range(sh.volume))
    out = L13.repair_exceptional(stream, sh, names, K, f, rho)
    assert sorted(out) == stream and out != stream                      # B is nonempty and moved
    monkeypatch.setattr(L13, "T0", lambda x, y, z, K, f, rho: (0, 0, 0))
    with pytest.raises(AssertionError, match="keys != marked holes"):
        L13.repair_exceptional(stream, sh, names, K, f, rho)


def test_lemma12_record_ids_form_a_permutation(monkeypatch):
    """SPEC §3.8 / D12: Lemma 12 runs on record IDs; the realized map must be an address permutation with
    the field order and lengths kept (lemma13.swap_via_lemma12)."""
    import subnlogn.interchange as IC
    import subnlogn.m6.lemma13 as L13
    sh = _shape(("a", 4, 2), ("b", 4, 2))
    stream = [("rec", i) for i in range(16)]

    def duplicate(ids, shape, a, b, net, policy, inst=None):
        ids = list(ids)
        ids[1] = ids[0]
        return ids, shape

    def reshaped(ids, shape, a, b, net, policy, inst=None):
        return list(ids), _shape(("b", 4, 2), ("a", 4, 2))
    monkeypatch.setattr(IC, "swap_bit_chunks", duplicate)
    swap = L13.swap_via_lemma12(None, None)                            # imports swap_bit_chunks here
    with pytest.raises(AssertionError, match="must realize an address permutation"):
        swap(stream, sh, "a", "b")
    monkeypatch.setattr(IC, "swap_bit_chunks", reshaped)
    with pytest.raises(AssertionError, match="keep the field order and lengths"):
        L13.swap_via_lemma12(None, None)(stream, sh, "a", "b")


# ---------------------------------------------------------- padded rows zero at completed boundaries


def test_unpad_rows_and_ranges_need_zero_padding():
    """Pr L1641-1644, L1674-1677: padding is asserted zero before it is removed (stream.unpad_rows,
    stream.unpad_ranges)."""
    from subnlogn.stream import Field, pad_ranges, pad_rows, unpad_ranges, unpad_rows
    st, sh = pad_rows(list(range(1, 7)), _shape(("r", 3), ("a", 2)), "r", 4)
    assert unpad_rows(st, sh, "r")[0] == list(range(1, 7))
    st[7] = 1
    with pytest.raises(AssertionError, match="padded row is not zero"):
        unpad_rows(st, sh, "r")
    st, sh = pad_ranges(list(range(1, 7)), _shape(("a", 3), ("b", 2)), [Field("a", 4)])
    assert unpad_ranges(st, sh, ["a"])[0] == list(range(1, 7))
    st[st.index(0)] = 5                                                 # the zeros are exactly the padding
    with pytest.raises(AssertionError, match="padding record is not zero"):
        unpad_ranges(st, sh, ["a"])


def test_batched_layer_padded_rows_stay_zero(monkeypatch):
    """SPEC §4.6 / C10: batched_c_layer asserts the padded rows zero before deleting them.  Forced plan with
    one padded row per prefix; a perturbed C^{tensor e} writes into the padding."""
    import subnlogn.m6.cnet as C
    plan = SimpleNamespace(individual=False, q0=0, row_len=1, row_pad=2, pieces=[2])
    monkeypatch.setattr(C, "batch_plan", lambda *a: plan)

    def leaky(arr, rows, sel, ctx):
        arr[4] = ([1], [0])                                             # first record of the padded row
    monkeypatch.setattr(C, "c_power_exact", leaky)
    arr = [([i], [0]) for i in range(8)]
    with pytest.raises(AssertionError, match="padded rows must stay zero"):
        C.batched_c_layer(arr, [1, 0], C.CCtx(net=None, d=2))
    monkeypatch.setattr(C, "c_power_exact", lambda arr, rows, sel, ctx: None)
    assert C.batched_c_layer(list(arr), [1, 0], C.CCtx(net=None, d=2)) == arr


# ------------------------------------------- fixed-width arithmetic, halvings drop only zeros (SPEC §4.8)


def test_guarded_format_gate_overflow():
    """cnet._apply_gate: every gate output fits the allocated guarded format |v| < bound."""
    from subnlogn.m6.cnet import _apply_gate
    from subnlogn.net.zi2 import ZI2
    gate = SimpleNamespace(roles=(0, 1), matrix=[[ZI2(1), ZI2(1)], [ZI2(1), ZI2(-1)]])
    roles = [[([1], [0])], [([1], [0])]]
    _apply_gate(roles, gate, bound=3)
    assert roles == [[([2], [0])], [([0], [0])]]
    with pytest.raises(AssertionError, match="guarded format exceeded by a gate output"):
        _apply_gate([[([1], [0])], [([1], [0])]], gate, bound=2)


def test_halvings_drop_only_zeros():
    """SPEC §4.8 / C10: _half, _halvek, the Z[i, 1/2] gate product and Prop 14's exact boundary refuse to
    discard a 1 bit."""
    from subnlogn.m6.cnet import _half, _halvek, _mul_zi2
    from subnlogn.m6.prop14 import finish_layer
    from subnlogn.net.zi2 import ZI2
    assert _half(6) == 3 and _halvek(12, 2) == 3 and _mul_zi2([2], [0], ZI2(1, 0, 1)) == ([1], [0])
    with pytest.raises(AssertionError, match="halving would discard a 1 bit"):
        _half(3)
    with pytest.raises(AssertionError, match=r"\(-i/2\)\^t"):
        _halvek(6, 2)
    with pytest.raises(AssertionError, match="gate product"):
        _mul_zi2([1], [0], ZI2(1, 0, 1))
    assert finish_layer([([4], [0])], 5, 3, exact_boundary=True) == ([([1], [0])], 3)
    with pytest.raises(AssertionError, match="exact_boundary"):
        finish_layer([([5], [0])], 5, 3, exact_boundary=True)


def test_layer_output_disk_and_width():
    """SPEC §4.7: finish_layer(check_disk) asserts |numerator| <= 2^p and |z| <= 1 on the output."""
    from subnlogn.m6.prop14 import finish_layer
    p = 3
    assert finish_layer([([8], [0])], p, p, check_disk=True)[1] == p
    with pytest.raises(AssertionError, match="left the unit disk"):
        finish_layer([([9], [0])], p, p, check_disk=True)               # |numerator| > 2^p
    with pytest.raises(AssertionError, match="left the unit disk"):
        finish_layer([([6], [6])], p, p, check_disk=True)               # components fit, |z| > 1


# --------------------------------------- disk on ring inputs, centered extraction bounds and final carry


def _ring_args(p=8, r=4):
    f = [((1 << p) // 2, 0)] * r
    g = [(0, (1 << p) // 3)] * r
    return f, g, p, r


def test_ring_inputs_on_the_disk():
    """Lemma 17 hypotheses (SPEC §6.8 disk on ring inputs): every input coefficient on the disk grid."""
    from subnlogn.ring import normalized_ring_product
    f, g, p, r = _ring_args()
    normalized_ring_product(f, g, p, r)
    f[1] = ((1 << p) - 1, (1 << p) // 4)                               # |z| > 1
    with pytest.raises(RuntimeCheckError, match="disk-grid polynomials"):
        normalized_ring_product(f, g, p, r)
    with pytest.raises(RuntimeCheckError, match=r"\|u_j\| <= 2\^p violated"):
        from subnlogn.ring import pack_blocks
        pack_blocks([1, (1 << p) + 1], p)


def test_ring_extraction_bound_31():
    """Pr L3125-3180 bound (31): a wrong product from the independent multiplier (one extra B0^{2r-1})
    shows up as a nonzero padded top coefficient and must fail."""
    from subnlogn.ring import normalized_ring_product
    f, g, p, r = _ring_args()
    with pytest.raises(RuntimeCheckError, match=r"bound \(31\) violated"):
        normalized_ring_product(f, g, p, r, mul=lambda x, y: x * y + (1 << (4 * p * (2 * r - 1))))


def test_ring_extraction_fit_and_final_carry(monkeypatch):
    """centered_extract: |Z| < B0^J / 2, and the final carry cancels the sign extension (a skipped
    complement-and-increment of a negative Z must fail)."""
    import subnlogn.ring as RG
    p, J = 4, 2
    assert RG.centered_extract(-5, J, p) == [-5, 0]
    with pytest.raises(RuntimeCheckError, match="does not fit in J signed blocks"):
        RG.centered_extract(1 << (4 * p * J - 1), J, p)
    monkeypatch.setattr(RG, "_complement_increment", lambda blocks, p: blocks)
    with pytest.raises(RuntimeCheckError, match="final carry does not cancel"):
        RG.centered_extract(-5, J, p)


def test_ring_output_disk(monkeypatch):
    """Lemma 17 output: trunc0(H_j / 2^{p+l}) on the disk grid (a perturbed narrowing that skips the shift
    must fail)."""
    import subnlogn.ring as RG
    f, g, p, r = _ring_args()
    monkeypatch.setattr(RG, "shr_trunc", lambda v, s: v)
    with pytest.raises(RuntimeCheckError, match="output left the disk"):
        RG.normalized_ring_product(f, g, p, r)


def test_kronecker_unpack_carries(monkeypatch):
    """MS Lemma 6.2 (ii) (the 2D fallback's extraction): the final carry cancels the sign extension."""
    import subnlogn.kronecker as KR
    assert KR.unpack(-5, 2, 8) == [-5, 0]
    monkeypatch.setattr(KR, "int_to_digits", lambda T, B, m: [0] * m)  # a corrupted block split
    with pytest.raises(RuntimeCheckError, match="final carry does not cancel"):
        KR.unpack(-5, 2, 8)


# --------------------------------------------------------- solver denominators, |rho-bar| < 1, widths


def test_closure_gamma_rho_bar_and_denominator():
    """r2 (4.16)-(4.17): the stored rho-hat = -a_hat 2^-q has |rho-hat| < 1, and the closure's denominator
    1 - a^L needs a_hat <= 1 - 1/(2t)."""
    from subnlogn.tables import closure_gamma
    q, L, t = 16, 4, 4
    closure_gamma(1 << (q - 1), L, q, t)
    with pytest.raises(ValueError, match="0 <= a-hat < 1"):
        closure_gamma(1 << q, L, q, t)
    with pytest.raises(AssertionError, match=r"a-hat <= 1 - 1/\(2t\)"):
        closure_gamma((1 << q) - 1, L, q, t)


def test_solver_tuple_checks(monkeypatch):
    """tables.solver_tuple (r2 §8): the dominance u < t/2 and rho-hat in (-1, 0], with a perturbed
    coefficient table."""
    from dataclasses import replace

    import subnlogn.certified as CF
    from subnlogn.tables import solver_tuple
    u, t, L, w, q = 1, 8, 8, 30, 24
    good = CF.solver_coeffs(u, t, w, q)
    solver_tuple(u, t, L, w, q)
    monkeypatch.setattr(CF, "solver_coeffs", lambda *a, **k: replace(good, forward=not good.forward))
    with pytest.raises(AssertionError, match="dominance must be u < t/2"):
        solver_tuple(u, t, L, w, q)
    monkeypatch.setattr(CF, "solver_coeffs", lambda *a, **k: replace(good, a=1 << q))
    with pytest.raises(AssertionError, match=r"rho-hat must lie in \(-1, 0\]"):
        solver_tuple(u, t, L, w, q)


def test_solver_state_width():
    """C10: the bridge's deconvolution states stay within the declared width
    q + K + 6 (cyclic_solve(max_bits)); reuses the mutation-sensitivity test (in-contract input passes,
    2^(q+K+8) fails)."""
    from test_regression_mutants import test_deconv_declared_width_is_enforced as width_check
    width_check()


# ------------------------------------------------------------------- table intervals meet their specs


def test_certified_tables_are_loud():
    """C9 / SPEC §6.8 tables: an enclosure that never decides the rounding is a recorded fallback with a
    CertifiedFallbackWarning (an error under the test suite's filter, and conftest fails on any recorded
    fallback); an enclosure wider than 2^-(q+4) at the cap raises ArithmeticError."""
    import subnlogn.certified as CF
    q = 8

    def tie(prec):                                   # straddles the rounding boundary 2^-(q+1) forever
        c = 1 << (prec - q - 1)
        return (c - 1, c + 1, prec)
    before = len(CF.FALLBACK_EVENTS)
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("error", CF.CertifiedFallbackWarning)
            with pytest.raises(CF.CertifiedFallbackWarning, match="faithful rounding used"):
                CF.correctly_rounded(tie, q)
        assert len(CF.FALLBACK_EVENTS) == before + 1
    finally:
        del CF.FALLBACK_EVENTS[before:]
    with pytest.raises(ArithmeticError, match="enclosure wider than"):
        CF.correctly_rounded(lambda prec: (-(1 << prec), 1 << prec, prec), q)


def test_phase_table_entries_on_the_disk(monkeypatch):
    """SPEC §5.9 phase_table: every entry satisfies re^2 + im^2 <= 2^{2p} (a perturbed octant value off the
    disk must fail)."""
    import subnlogn.certified as CF
    CF._phase_table_cached.cache_clear()
    monkeypatch.setattr(CF, "_disk_octant", lambda hn, hd, p, backend="exact": (1 << p, 1 << p))
    try:
        with pytest.raises(RuntimeCheckError, match="phase left the disk"):
            CF.phase_table(8, 13)
    finally:
        CF._phase_table_cached.cache_clear()


# ------------------------------------------------------------------ hypotheses of converted asserts


@pytest.mark.parametrize("call,match", [
    (lambda: __import__("subnlogn.bridge.precision", fromlist=["x"]).certify_bridge_precision(4, (4, 4)),
     r"p >= max\(8, K\)"),
    (lambda: __import__("subnlogn.net.primes", fromlist=["x"]).certify_prime_alphabet(9), "h >= 7, h != 9"),
    (lambda: __import__("subnlogn.ring", fromlist=["x"]).normalized_ring_product([(0, 0)] * 4, [(0, 0)] * 4, 2, 4),
     "Lemma 17 needs r = 2"),
])
def test_converted_hypothesis_checks(call, match):
    """Former bare asserts on the hypotheses of the bridge precision certificate, the prime-alphabet
    certificate and Lemma 17 now raise RuntimeCheckError."""
    with pytest.raises(RuntimeCheckError, match=match):
        call()
