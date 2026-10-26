/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleAddrCost

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrCostBound.lean`): the routine's cost is quartic

**Scope (honest summary).** Pure arithmetic about the cost expression `TwAddr.costTW`
(`TwiddleAddrCost.lean`); no machine program here. Proved, no `sorry`:
* `costTW_eq`: the closed form `costTW C KM Q D v = 68U + 32 + D·(76U + 31) + D·v·(42U + 10)`,
  `U = TwAddr.U C KM Q = C·(KM+2)·(Q+2)²`;
* `costTW_le`: with `Q = 6(m + w + 1)`, `D ≤ Q`, `v ≤ Q` and `C ≥ 1`,
  `costTW C KM Q D v ≤ 10⁶·(C·(KM+2))·(w + m + 1)⁴`.
Proof: with `N = w + m + 1 ≥ 1`, `U ≥ 128` absorbs the additive constants, so
`costTW ≤ 69U + 462·N·U + 1548·N²·U ≤ 2079·N²·U`, and `U ≤ 64·C·(KM+2)·N²` since
`Q + 2 ≤ 8N`; `2079·64 = 133056 ≤ 10⁶`.
-/

namespace SubNLogN.Machine.FFT.TwAddrCost

open SubNLogN.Machine.FFT.TwAddr

/-- Closed form of the routine's cost expression. -/
theorem costTW_eq (C KM Q D v : ℕ) :
    TwAddr.costTW C KM Q D v = 68 * TwAddr.U C KM Q + 32 + D * (76 * TwAddr.U C KM Q + 31) +
      D * (v * (42 * TwAddr.U C KM Q + 10)) := by
  unfold TwAddr.costTW TwAddr.cAx TwAddr.cTerm TwAddr.cHorner
  ring

/-- **The cost of the twiddle-address routine is quartic** in `w + m + 1`, for the bit-length bound
`Q = 6(m + w + 1)` and `D, v ≤ Q`. -/
theorem costTW_le (C KM m w D v : ℕ) (hC : 1 ≤ C) (hD : D ≤ 6 * (m + w + 1))
    (hv : v ≤ 6 * (m + w + 1)) :
    TwAddr.costTW C KM (6 * (m + w + 1)) D v ≤ 1000000 * (C * (KM + 2)) * (w + m + 1) ^ 4 := by
  rw [costTW_eq]
  set N := w + m + 1 with hN
  have hQ : 6 * (m + w + 1) = 6 * N := by omega
  rw [hQ] at hD hv ⊢
  set A := C * (KM + 2) with hA
  have hU : TwAddr.U C KM (6 * N) = A * (6 * N + 2) ^ 2 := rfl
  set u := TwAddr.U C KM (6 * N) with hu
  have hN1 : 1 ≤ N := by omega
  have hA2 : 2 ≤ A := by
    have h := Nat.mul_le_mul hC (show 2 ≤ KM + 2 by omega)
    omega
  have hX : 64 ≤ (6 * N + 2) ^ 2 := by
    have h8 : 8 ≤ 6 * N + 2 := by omega
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ (6 * N + 2) ^ 2 := Nat.pow_le_pow_left h8 2
  have hu128 : 128 ≤ u := by
    rw [hU]
    calc 128 = 2 * 64 := by norm_num
      _ ≤ A * (6 * N + 2) ^ 2 := Nat.mul_le_mul hA2 hX
  have hX' : (6 * N + 2) ^ 2 ≤ 64 * (N * N) := by
    have h8 : 6 * N + 2 ≤ 8 * N := by omega
    calc (6 * N + 2) ^ 2 ≤ (8 * N) ^ 2 := Nat.pow_le_pow_left h8 2
      _ = 64 * (N * N) := by ring
  have huA : u ≤ 64 * A * (N * N) := by
    rw [hU]
    calc A * (6 * N + 2) ^ 2 ≤ A * (64 * (N * N)) := Nat.mul_le_mul_left A hX'
      _ = 64 * A * (N * N) := by ring
  have h1 : D * (76 * u + 31) ≤ 6 * N * (77 * u) := Nat.mul_le_mul hD (by omega)
  have h2 : D * (v * (42 * u + 10)) ≤ 6 * N * (6 * N * (43 * u)) :=
    Nat.mul_le_mul hD (Nat.mul_le_mul hv (by omega))
  have hNN : 1 ≤ N * N := by
    have h := Nat.mul_le_mul hN1 hN1
    omega
  have h3 : u ≤ N * N * u := by
    calc u = 1 * u := (Nat.one_mul u).symm
      _ ≤ N * N * u := Nat.mul_le_mul_right u hNN
  have h4 : N * u ≤ N * N * u := by
    calc N * u = N * 1 * u := by rw [Nat.mul_one]
      _ ≤ N * N * u := Nat.mul_le_mul_right u (Nat.mul_le_mul_left N hN1)
  have e1 : 6 * N * (77 * u) = 462 * (N * u) := by ring
  have e2 : 6 * N * (6 * N * (43 * u)) = 1548 * (N * N * u) := by ring
  have hmain : 68 * u + 32 + D * (76 * u + 31) + D * (v * (42 * u + 10)) ≤
      2079 * (N * N * u) := by
    omega
  have hfin : 2079 * (N * N * u) ≤ 1000000 * A * N ^ 4 := by
    calc 2079 * (N * N * u) ≤ 2079 * (N * N * (64 * A * (N * N))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ huA)
      _ = 133056 * A * N ^ 4 := by ring
      _ ≤ 1000000 * A * N ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
  exact le_trans hmain hfin

end SubNLogN.Machine.FFT.TwAddrCost
