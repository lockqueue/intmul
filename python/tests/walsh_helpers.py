"""Shared helpers for the Walsh-route tests (SPEC_WALSH §8): exact Gaussian-rational matrices, random disk
arrays, exact dense butterflies, engines."""

import random
from fractions import Fraction

from subnlogn.instrument import Instrument
from subnlogn.m6.cnet import CCtx
from subnlogn.m6.policy import LAYER_TEST
from subnlogn.net import compile_network
from subnlogn.net.fixtures import fixture_C1

NET_C1 = compile_network(fixture_C1())


def engine(kind, d, policy=LAYER_TEST, inst=None):
    return None if kind == "base" else CCtx(net=NET_C1, d=d, policy=policy, inst=inst)


def rand_disk(m0, r, p, rng, frac=2):
    """2^m0 records of r coefficients on the 2^-p grid with |component| <= 2^p/frac (disk if frac >= 2)."""
    lim = (1 << p) // frac
    return [([rng.randint(-lim, lim) for _ in range(r)], [rng.randint(-lim, lim) for _ in range(r)])
            for _ in range(1 << m0)]


def to_frac(recs, scale):
    return [[(Fraction(a, 1 << scale), Fraction(b, 1 << scale)) for a, b in zip(re, im)] for re, im in recs]


def exact_H(vals, ebits):
    """Exact normalized H0 = (1/2)[[1,1],[1,-1]] on each engine bit (values: list of lists of Fraction pairs)."""
    out = [list(v) for v in vals]
    for b in ebits:
        m = 1 << b
        for x in range(len(out)):
            if not x & m:
                u, v = out[x], out[x | m]
                out[x] = [((a[0] + c[0]) / 2, (a[1] + c[1]) / 2) for a, c in zip(u, v)]
                out[x | m] = [((a[0] - c[0]) / 2, (a[1] - c[1]) / 2) for a, c in zip(u, v)]
    return out


def address_permute(recs, f):
    """out[f(x)] = recs[x]."""
    out = [None] * len(recs)
    for x, rec in enumerate(recs):
        out[f(x)] = rec
    return out


# --- tiny exact Gaussian-rational matrices (W-T1) ---------------------------------------------------
def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def mat_mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    Z = (Fraction(0), Fraction(0))
    out = []
    for i in range(n):
        row = []
        for j in range(m):
            acc = Z
            for t in range(k):
                if A[i][t] != Z and B[t][j] != Z:
                    pr = gmul(A[i][t], B[t][j])
                    acc = (acc[0] + pr[0], acc[1] + pr[1])
            row.append(acc)
        out.append(row)
    return out


def kron_bits(factors):
    """Operator on vectors indexed by x in {0,1}^D, factor j acting on bit j of x (bit 0 = LSB)."""
    D = len(factors)
    n = 1 << D
    Z = (Fraction(0), Fraction(0))
    out = [[Z] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            acc = (Fraction(1), Fraction(0))
            for j, F in enumerate(factors):
                acc = gmul(acc, F[(x >> j) & 1][(y >> j) & 1])
                if acc == Z:
                    break
            out[x][y] = acc
    return out


def diag(entries):
    Z = (Fraction(0), Fraction(0))
    return [[entries[i] if i == j else Z for j in range(len(entries))] for i in range(len(entries))]


def scal(c, A):
    return [[gmul(c, a) for a in row] for row in A]


H0 = [[(Fraction(1, 2), Fraction(0)), (Fraction(1, 2), Fraction(0))],
      [(Fraction(1, 2), Fraction(0)), (Fraction(-1, 2), Fraction(0))]]
I2 = [[(Fraction(1), Fraction(0)), (Fraction(0), Fraction(0))], [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0))]]
S = [[(Fraction(1), Fraction(0)), (Fraction(0), Fraction(0))], [(Fraction(0), Fraction(0)), (Fraction(0), Fraction(1))]]


def fresh_inst():
    return Instrument()


RNG = random.Random
