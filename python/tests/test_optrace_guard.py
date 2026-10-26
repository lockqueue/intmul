"""Operator-level guard (complements the call/return trace of test_bigint_sites, which
cannot see inline operators).  Small shapes of every route run under the AST-rewriting tracer
(tests/optrace.py) in products="hierarchy", one hierarchy stage at a time (the next stage is an exact
untraced stub, so each stage is checked in isolation: the improved multiplier / Multiply2 / Multiply1 /
BasicMul).  Asserted:

(b) every superlinear inline operation -- ``* // % ** divmod pow`` with BOTH int operands above 64 bits
    -- outside BasicMul is a runtime check (class E) or a per-level table precomputation (class D) listed
    in ALLOW_SUPERLINEAR; every other long product went through the hierarchy (MS Thm 7.1 pt 3; br_r2
    (6.5); ``Ctx.word_mul``/``Ctx.product_mul``), and the counters python.word_product_over_64 and
    python.big_product stay 0;
(a) every inline operation on an int above the route's word scale T = 4 max(level precision) happens in a
    function the allow-list permits to hold long integers (tests/longint_trace.py ALLOWED_LONG, classes A/C/D/E).

Two canaries (an inline packed product in kronecker.spread_row; a hidden T*T//T in
kronecker.unpack) are injected into the traced copy only and must be caught."""

import json
import os
import subprocess
import sys

import pytest

import hierarchy_exact as HE
from longint_trace import ALLOWED_LONG, ALLOWED_LONG_MODULES
from optrace_routes import ROUTES as ROUTE_TABLE, STAGES as STAGE_TABLE

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

#: superlinear inline operations allowed outside BasicMul: (module, function) -> class and reason
ALLOW_SUPERLINEAR = {
    # PER SITE (module, function, expression text), not per function: a product written
    # inline elsewhere in an allow-listed function is NOT allowed (canary N3 below).
    ("subnlogn.bridge.bridge_dft", "bridge_dft", "a * a"): "E: r2 §5.2 input disk assertion a² + b² ≤ lim",
    ("subnlogn.bridge.bridge_dft", "bridge_dft", "b * b"): "E: r2 §5.2 input disk assertion a² + b² ≤ lim",
    ("subnlogn.bridge.spread", "spread_axis.line", "amax * hsum"): "E: slot-fit assertion (amax·Σ|taps|)",
    ("subnlogn.middle3.bluestein", "complex_convolution", "a * a"): "E: Prop 18 disk test before narrowing",
    ("subnlogn.middle3.bluestein", "complex_convolution", "b * b"): "E: Prop 18 disk test before narrowing",
    ("subnlogn.middle3.bluestein", "tensor_positive_dft", "a * a"): "E: input disk assertion ‖x‖ ≤ 0.6",
    ("subnlogn.middle3.bluestein", "tensor_positive_dft", "b * b"): "E: input disk assertion ‖x‖ ≤ 0.6",
    ("subnlogn.ring", "in_disk", "re * re"): "E: Lemma 17 ring input/output disk assertions",
    ("subnlogn.ring", "in_disk", "im * im"): "E: Lemma 17 ring input/output disk assertions",
    ("subnlogn.ring", "normalized_ring_product", "Hre * Hre"): "E: |H|² ≤ bound² check of the ring product",
    ("subnlogn.ring", "normalized_ring_product", "Him * Him"): "E: |H|² ≤ bound² check of the ring product",
    ("subnlogn.ring", "normalized_ring_product", "bound * bound"): "E: |H|² ≤ bound² check of the ring product",
    ("subnlogn.m6.prop14", "finish_layer", "a * a"): "E: disk assertion at Prop 14 layer outputs",
    ("subnlogn.m6.prop14", "finish_layer", "b * b"): "E: disk assertion at Prop 14 layer outputs",
    ("subnlogn.walsh.gadget", "assert_disk", "a * a"): "E: SPEC_WALSH §2.6 disk assertion",
    ("subnlogn.walsh.gadget", "assert_disk", "b * b"): "E: SPEC_WALSH §2.6 disk assertion",
    ("subnlogn.fastdft2d", "_input_precondition", "a * a"): "E: MS input precondition |x_j|^2 <= 2^(2p) ("
                                                           "only when the prefilter fails)",
    ("subnlogn.fastdft2d", "_input_precondition", "b * b"): "E: MS input precondition",
    ("subnlogn.tables", "closure_gamma", "acc * base"): "D: br_r2 (4.21) truncated powering, once per solver tuple",
    ("subnlogn.tables", "closure_gamma", "base * base"): "D: br_r2 (4.21) truncated powering, once per solver tuple",
    ("subnlogn.tables", "closure_gamma", "(one << Q) // den"): "D: br_r2 (4.21) guarded division, once per tuple",
}


ROUTES = ["faithful2d", "faithful2d_big", "deep2d", "bluestein", "walsh", "direct", "network",
          "walsh_network", "multiply2", "multiply1", "basic"]


def _allowed(site: dict) -> bool:
    path = site["module"].removeprefix("subnlogn.").replace(".", "/") + ".py"
    if os.path.basename(path) in ALLOWED_LONG_MODULES:
        return True
    fn = site["function"].split(".")[-1]
    return f"{path}:{fn}" in ALLOWED_LONG or (site["module"], site["function"], site["expr"]) in ALLOW_SUPERLINEAR


def run_route(route: str, tmp_path, patches: dict | None = None) -> dict:
    out = tmp_path / "trace.json"
    cmd = [sys.executable, os.path.join(ROOT, "tests", "optrace_run.py"), route, str(out)]
    if patches:
        pf = tmp_path / "patches.json"
        pf.write_text(json.dumps(patches))
        cmd.append(str(pf))
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=600)
    assert p.returncode == 0, p.stderr[-3000:]
    return json.loads(out.read_text())


def violations(res: dict) -> list[str]:
    bad = []
    c = res["counts"]
    for k in ("python.word_product_over_64", "python.big_product"):
        if c.get(k, 0):
            bad.append(f"counter {k} = {c[k]}")
    for s in res["sites"]:
        where = f"{s['module']}:{s['function']}:{s['line']} {s['op']}"
        if s["superlinear"] and (s["module"], s["function"], s["expr"]) not in ALLOW_SUPERLINEAR:
            bad.append(f"(b) {where}: {s['superlinear']} inline ops with both operands > 64 bits "
                       f"(max min-bits {s['max_min_bits']})")
        if s["max_bits"] > res["word_scale"] and not _allowed(s):
            bad.append(f"(a) {where}: {s['max_bits']}-bit operand above word scale {res['word_scale']} "
                       "outside the allow-listed functions")
    return bad


def expected_stub_calls(route: str, a: int, b: int) -> dict:
    """The exact calls of the stubbed next stage (exact counts; tests/hierarchy_exact.py): every packed product
    of the traced stage (closed form) and every word product with an operand above 64 bits (the same product,
    untraced, in products="python": counter python.word_product_over_64).  BasicMul calls nothing (schoolbook by
    specification, MS Stage 0)."""
    from subnlogn.hierarchy import Hierarchy
    if route in STAGE_TABLE:
        stage, _, kw = STAGE_TABLE[route]
        if stage == "basic_mul":
            return {"multiply1": 0, "basic": 0}
        h = Hierarchy(**kw())
        sched = h.multiply1_schedule if stage == "multiply1" else h.stage_schedule
        nxt = HE.stage_expected(sched, [(a, b)])["next"]
        return {"multiply1": 0, "basic": nxt} if stage == "multiply1" else {"multiply1": nxt, "basic": 0}
    return {"multiply1": HE.stage_expected(ROUTE_TABLE[route][0](), [(a, b)])["next"], "basic": 0}


@pytest.mark.parametrize("route", ROUTES)
def test_every_long_product_goes_through_the_hierarchy(route, tmp_path):
    res = run_route(route + ":hierarchy:stub", tmp_path)
    assert violations(res) == []
    want = expected_stub_calls(route, res["a"], res["b"])
    assert res["stub_calls"] == want, f"exact stub calls (the next hierarchy stage): {res['stub_calls']} != {want}"
    assert route == "basic" or sum(want.values()) > 0      # every other route hands long products to a stage


CANARIES = {
    # canary 1: a quarter of the packed products of a Step 1 block bypass the hierarchy
    "spread_row_inline_product": {"subnlogn.kronecker": [
        ("pii = unpack(mul(Xi, F_im), nout, B)", "pii = unpack(Xi * F_im, nout, B)")]},
    # canary 2: a hidden quadratic operation inside an allow-listed linear function
    "unpack_hidden_square": {"subnlogn.kronecker": [
        ("    eps = -1 if T < 0 else 0\n", "    T = T * T // T if T else T\n    eps = -1 if T < 0 else 0\n")]},
    # canary N3: chirp products written inline inside the allow-listed tensor_positive_dft (the per-site
    # allowlist must catch it; a per-function allowlist did not)
    "N3_inline_chirp_in_allowlisted_function": {"subnlogn.middle3.bluestein": [
        ("x0 = [trunc_cmul(xr, xi, ar, ai, p, wmul) for (xr, xi), (ar, ai) in zip(x, a)]",
         "x0 = [(shr_trunc(xr * ar - xi * ai, p), shr_trunc(xr * ai + xi * ar, p)) for (xr, xi), (ar, ai) "
         "in zip(x, a)]")]},
    # an inline word-scale product (a twist bypassing Ctx.word_mul)
    "twist_inline_product": {"subnlogn.synthetic": [
        ("nr.append(shr(mul(a, wr) - mul(b, wi), q))", "nr.append(shr(a * wr - mul(b, wi), q))")]},
}


@pytest.mark.parametrize("canary", sorted(CANARIES))
def test_canaries_are_caught(canary, tmp_path):
    route = "bluestein:hierarchy:stub" if canary.startswith("N3") else "deep2d:hierarchy:stub"
    res = run_route(route, tmp_path, CANARIES[canary])
    assert any(v.startswith("(b)") for v in violations(res)), "canary not caught"
