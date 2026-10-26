"""subnlogn.bridge: the d-dimensional CRT-free fractional-shift bridge (milestone M2).

The bridge replaces the 1D DFT F_R (R = 2^K) by a d-dimensional tensor DFT over the axes
t_1 x ... x t_d (R = prod t_i), via the triangular d-dimensional Poisson identity (bridge Lemma A,
bridge derivation r2 Theorem 1 and §3, r3 §3) and the ordered two-term deconvolution
with the negative half-bin sinc-Gaussian kernel (bridge Lemma B, r2 §4, r3 §4):

    F_t S_2 S_3 ... S_d x  =  A_2 A_3 ... A_d F_R x                      (r2 (2.2), r3 (3.7)),

spreading axes in chronological order d, d-1, ..., 2 and deconvolving with B_2^{-1}, ..., B_d^{-1}
in chronological order 2, 3, ..., d (r2 (3.9)).

Modules
-------
* :mod:`subnlogn.bridge.geometry` -- the exact (pure int / Fraction) index geometry: mixed-radix
  digits, the fractional shifts delta_h, the frequency bijection Phi, alias cycles, storage lines,
  and the balanced factorization t_i in {r/2, r}.
* :mod:`subnlogn.bridge.movement` -- the address movements of SPEC §7.2 (axis exposures, storage <-> tensor
  reversal) by O(d) Lemma 12 exchanges (``Schedule.bridge_movement="lemma12"``) or reference index maps.

Storage convention for every d-dimensional array (spatial, spread, tensor frequency): a flat list
indexed by sum_i c_i A_i with c_1 least significant.  The tensor DFT output stored at position
sum_i u_i A_i is the 1D frequency Phi(u) = sum_i u_i Q_i (u_1 MOST significant); see
:meth:`subnlogn.bridge.geometry.BridgeGeometry.storage_to_freq`.
"""
