"""The p_fft = P + 2 precision refinement -- exact schedule certificate,
agreement with the code's bridge parameters, and the run-time width assertions."""

import random

import pytest

from conftest import make_ctx
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.bridge.geometry import balanced_factors
from subnlogn.bridge.precision import certify_bridge_precision
from subnlogn.fixedpoint import FxVec
from subnlogn.instrument import Instrument
from subnlogn.schedule import test_policy


def test_spec_appendix_a_example():
    """p = 28, t = (2,2,2,4): P = 564, p_fft = 566, w = 568, w_M = 571."""
    c = certify_bridge_precision(28, (2, 2, 2, 4))
    assert (c["P"], c["fractional_bits"], c["component_bits"], c["prop18_component_bits"],
            c["solver_component_bits"]) == (564, 566, 568, 571, 577)


@pytest.mark.parametrize("d,K", [(2, 6), (3, 6), (4, 5), (4, 8), (5, 10), (10, 11), (4, 12), (3, 9)])
def test_certificate_holds_and_matches_bridge_params(d, K):
    p = max(8, K) + 2
    t = balanced_factors(K, d)
    if t[-1] < 4:
        pytest.skip("the precision checker needs ell >= 2")
    c = certify_bridge_precision(p, t)
    sched = test_policy(d)
    P, w, m = sched.bridge_params(p, K, d)
    assert c["P"] == P and c["fractional_bits"] == P + 2      # q = p_fft = P + 2 in the code


@pytest.mark.parametrize("d,K,middle", [(2, 6, "bluestein"), (4, 8, "bluestein"), (4, 8, "walsh"),
                                        (3, 9, "direct")])
def test_measured_widths_inside_o58(d, K, middle):
    """Measured record heights (spread arrays, solver states) are inside the corrected widths
    f + 2 and f + K + 6; the solver asserts its declared width on every run."""
    R = 1 << K
    p = max(8, K) + 2
    q = p + 2
    rng = random.Random(d * 31 + K)
    big = (1 << (q + p)) * 7 // 10
    inst = Instrument(monitor_heights=True)
    ctx = make_ctx(test_policy(d, middle=middle))
    ctx.inst = inst
    bridge_dft(ctx, FxVec([rng.randint(-big, big) for _ in range(R)],
                          [rng.randint(-big, big) for _ in range(R)], q), R, p, d)
    P, _, _ = ctx.schedule.bridge_params(p, K, d)
    f = P + 2
    assert inst.heights["bridge.spread"] <= f + 1                       # width f + 2 incl. sign
    assert max(v for k, v in inst.heights.items() if "solver" in k) <= f + K + 5
