"""The uniform cyclic column solver of the negative half-bin drop-in (r2 §8, §4.6;
MS §5.2 procedure ``CyclicSolve``).  There is NO Nyquist identity and NO Nyquist solver.

Solves (B Z)_i = c0 Z_i + c1 Z_{i-1 mod L} = Y_i on a cycle of even length L, given the stored
table scalars mu = Q(1/M), rho = -Q(min/max), gamma = Q(1/(1 - rho^L)) (all on R~_q, gamma from
the stored rho as in r2 (4.17)).  Every product is one RM_q (error <= sqrt(2)/2 2^-q).

Case 1, c0 > c1 (forward; u < t/2):
    B_i = RM(mu, Y_i);  P_0 = B_0,  P_i = B_i + RM(rho, P_{i-1})            (prefix sweep)
    Z_{L-1} = RM(gamma, P_{L-1});  Z_0 = B_0 + RM(rho, Z_{L-1});
    Z_i = B_i + RM(rho, Z_{i-1}),  i = 1..L-2                                  (second pass)
Case 2, c1 > c0 (backward; u >= t/2), with the essential +1 right-hand-side shift:
    B_i = RM(mu, Y_{i+1 mod L});  P_{L-1} = B_{L-1},  P_i = B_i + RM(rho, P_{i+1})
    Z_0 = RM(gamma, P_0);  Z_{L-1} = B_{L-1} + RM(rho, Z_0);
    Z_i = B_i + RM(rho, Z_{i+1}),  i = L-2..1
Error (r2 (4.20); r3 (4.21)): ||Z - B^{-1} Y||_inf <= 32 t^2 2^-q' max(1, ||Y||_inf) where
2^-q' is the table/product unit (here q' = q - 2 with q = q_child = P + 2, so 2^-q' = 2^-P),
independent of L.
"""

from __future__ import annotations

from typing import Callable

__all__ = ["cyclic_solve"]


def _pymul(a: int, b: int) -> int:
    return a * b


def cyclic_solve(y_re: list[int], y_im: list[int], mu: int, rho: int, gamma: int,
                 forward: bool, q: int, shr: Callable[[int, int], int],
                 inst=None, hkey: str = "solver.prefix",
                 max_bits: int | None = None, mul=None) -> tuple[list[int], list[int]]:
    """Solve one cycle (see module docstring).  Inputs/outputs are numerators at scale q.
    With a height-monitoring ``inst``, the max bit length of all prefix states is recorded under
    ``hkey`` (record width with the drop-in's +4 headroom bits, r2 §8).  ``max_bits`` asserts that
    every state, prefix and output numerator has at most that many magnitude bits (the declared
    component width minus the sign bit; e.g. the bridge's f + K + 6, the p_fft = P + 2 refinement).  ``mul`` is
    the word-scale multiplier for the scalar solver products (``Ctx.word_mul``; MS Thm 7.1 pt 3 (a),
    br_r2 (6.5)); None = Python's ``*`` (unit tests)."""
    if mul is None:
        mul = _pymul
    L = len(y_re)
    mon = inst is not None and (inst.monitor_heights or max_bits is not None)
    hmax = 0
    if forward:
        b_re = [shr(mul(mu, v), q) for v in y_re]
        b_im = [shr(mul(mu, v), q) for v in y_im]
        pr, pi = b_re[0], b_im[0]
        for i in range(1, L):
            pr = b_re[i] + shr(mul(rho, pr), q)
            pi = b_im[i] + shr(mul(rho, pi), q)
            if mon:
                hmax = max(hmax, abs(pr).bit_length(), abs(pi).bit_length())
        z_re = [0] * L
        z_im = [0] * L
        zr = shr(mul(gamma, pr), q)
        zi = shr(mul(gamma, pi), q)
        z_re[L - 1], z_im[L - 1] = zr, zi
        for i in range(0, L - 1):
            zr = b_re[i] + shr(mul(rho, zr), q)
            zi = b_im[i] + shr(mul(rho, zi), q)
            z_re[i], z_im[i] = zr, zi
        if inst is not None:
            inst.hit("solver.forward")
    else:
        b_re = [shr(mul(mu, y_re[(i + 1) % L]), q) for i in range(L)]
        b_im = [shr(mul(mu, y_im[(i + 1) % L]), q) for i in range(L)]
        pr, pi = b_re[L - 1], b_im[L - 1]
        for i in range(L - 2, -1, -1):
            pr = b_re[i] + shr(mul(rho, pr), q)
            pi = b_im[i] + shr(mul(rho, pi), q)
            if mon:
                hmax = max(hmax, abs(pr).bit_length(), abs(pi).bit_length())
        z_re = [0] * L
        z_im = [0] * L
        zr = shr(mul(gamma, pr), q)
        zi = shr(mul(gamma, pi), q)
        z_re[0], z_im[0] = zr, zi
        for i in range(L - 1, 0, -1):
            zr = b_re[i] + shr(mul(rho, zr), q)
            zi = b_im[i] + shr(mul(rho, zi), q)
            z_re[i], z_im[i] = zr, zi
        if inst is not None:
            inst.hit("solver.backward")
    if mon and inst.monitor_heights:
        inst.height(hkey, [(1 << hmax) - 1], z_re, z_im, b_re, b_im)   # (1<<h)-1 has h bits
    if max_bits is not None:
        top = max([hmax] + [abs(v).bit_length() for v in z_re + z_im + b_re + b_im])
        if top > max_bits:
            raise AssertionError(f"solver state needs {top} magnitude bits > declared {max_bits}")
    return z_re, z_im
