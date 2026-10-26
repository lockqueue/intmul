"""SPEC §2.1 "a gate computes every output from saved inputs" [Pr L620-623, L766-769].  Every
gate of the supplied networks (fixtures B1/B2/C1/C2, triple V/G/R/J) is one-directional, so saved-input and
in-place semantics coincide on all of them and an in-place mutant survives every network-level test.  These
unit tests use gates for which the two semantics differ -- a swap and a full 2 x 2 matrix -- and check both
gate executors (complex: m6.cnet._apply_gate; bit: interchange._apply_gate_f2) against the saved-input
definition out = matrix @ saved_in."""

import random

from subnlogn.interchange import _apply_gate_f2
from subnlogn.m6.cnet import _apply_gate
from subnlogn.net.model import Gate
from subnlogn.net.zi2 import ZI2


def _records(rng, n, width=3, bits=20):
    return [([rng.randint(-(1 << bits), 1 << bits) for _ in range(width)],
             [rng.randint(-(1 << bits), 1 << bits) for _ in range(width)]) for _ in range(n)]


def test_complex_gate_uses_saved_inputs():
    rng = random.Random(1)
    one, zero, m1 = ZI2(1), ZI2(0), ZI2(-1)
    for matrix in (((zero, one), (one, zero)),            # swap: in place would duplicate role 1
                   ((one, one), (one, m1))):              # H-like: both outputs need both inputs
        roles = [_records(rng, 4), _records(rng, 4)]
        saved = [list(r) for r in roles]
        _apply_gate(roles, Gate(roles=(0, 1), matrix=matrix, frame=None))
        for x in range(4):
            for k in range(2):
                exp_re = [0] * 3
                exp_im = [0] * 3
                for l in range(2):
                    z = matrix[k][l]
                    re, im = saved[l][x]
                    # (a + i b)(re + i im) with z = a + i b (k = 0 here)
                    exp_re = [e + z.re * u - z.im * v for e, u, v in zip(exp_re, re, im)]
                    exp_im = [e + z.re * v + z.im * u for e, u, v in zip(exp_im, re, im)]
                assert roles[k][x] == (exp_re, exp_im)


def test_bit_gate_uses_saved_inputs():
    rng = random.Random(2)
    for matrix in (((0, 1), (1, 0)), ((1, 1), (1, 0))):    # swap; (a, b) -> (a ^ b, a)
        roles = [[rng.getrandbits(16) for _ in range(5)], [rng.getrandbits(16) for _ in range(5)]]
        saved = [list(r) for r in roles]
        _apply_gate_f2(roles, Gate(roles=(0, 1), matrix=matrix, frame=None))
        for k in range(2):
            exp = [0] * 5
            for l in range(2):
                if matrix[k][l]:
                    exp = [e ^ s for e, s in zip(exp, saved[l])]
            assert roles[k] == exp
