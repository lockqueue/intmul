/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchCost
import SubNLogN.Machine.Pipe.ReadParamsCost
import SubNLogN.Machine.FFT.MidData

/-!
# K7 (`Machine/Pipe/BranchCostW8.lean`): the Walsh cost clause at the concrete kernels (Sections 7.3–7.5 (`sec:main-tables`–`sec:main-rows`), Table 5 (`tab:cost-walsh`))

Main result: `walshCostClause_walshMidData`. For every `p : LayerParams` with
`p.lam' = Row46.lam'` (e.g. `row46Layer`, by `rfl`) and all `P₀ P₁ J`,
`WalshCostClause (branchCost readParamsCost (bridgeX τ) fnewSched (walshMidData fnewSched p P₀ P₁ J))`
with `τ = Row46.tau`; at `p = row46Layer` this is the `cost` field of `Assembly.KernelCut P₀ P₁ J`.

It instantiates `walshCostClause_branchCost_of` (`BranchCost.lean`):
* `hRP`: `readParamsCost b K0 p_in = (b + K0 + p_in + 16)^6 ≤ 64 P^6`;
* `hX`: `bridgeX τ ℓ = ⌈ℓ^τ⌉₊ ≤ 1 + ⌈ℓ^τ⌉₊`;
* `hMid`: `Tmid = midCost λ' J D ℓ K w m₀` with `m₀ = addrBits a`, `m₀ + ℓ = k`
  (`addrBits_fnewA`, so `2^{m₀}·2^ℓ = 2^k`): the cube volume is `≤ 7V`, the twiddle term
  `ℓ·2^k·mulW(2w+1) ≤ ℓ·2^k·mulW((c+1)P)`, and the setup terms
  `2^{m₀}(w+m₀+1)^J ≤ 3^J·(2^k/r)·P^J`, `2^ℓ(w+1)^J ≤ 3^J·r·P^J` (`midCost_le`, `c = 3^J + 7`);
* `hMH`: the middle header `[q, D, ℓ, K, w] ++ a` has `|hdrSyms| ≤ 4P²` (`mhdrLen_le`).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN SubNLogN.S5 Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM
  IntMulTM.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge
  SubNLogN.Math.Cost SubNLogN.Math.Walsh
open Filter

namespace BranchCostW8Aux

open BranchCostAux

theorem mulW_mono {a b : ℕ} (h : a ≤ b) : mulW a ≤ mulW b := by
  have h1 := mLog_mono h
  unfold mLog at h1
  unfold mulW
  exact Nat.add_le_add_right (Nat.mul_le_mul h h1) 1

/-- `addrBits (fnewA row46 k) + ℓ = k`: the record-axis bits plus the last axis give `k`. -/
theorem addrBits_fnewA {k : ℕ} (hd : 1 ≤ dK row46 k) (hl : 1 ≤ lK row46 k) :
    addrBits (fnewA row46 k) + lK row46 k = k := by
  have hK : k ≤ dK row46 k * lK row46 k := WalshOKProof.le_dK_mul_lK row46 k hd
  have h1 : dK row46 k * lK row46 k ≤ k + dK row46 k - 1 := by
    have := Nat.div_mul_le_self (k + dK row46 k - 1) (dK row46 k)
    unfold lK
    rw [Nat.mul_comm]
    exact this
  have hs : dK row46 k * lK row46 k - k < dK row46 k := by omega
  have e : addrBits (fnewA row46 k) = ∑ i ∈ Finset.range (fnewD row46 k),
      (if i < dK row46 k * lK row46 k - k then lK row46 k - 1 else lK row46 k) := by
    unfold addrBits
    rw [List.sum_ofFn, ← Fin.sum_univ_eq_sum_range]
    rfl
  rw [e, WalshOKProof.sum_range_ite_exp _ _ _ (by unfold fnewD; omega)]
  have := WalshOKProof.exp_sum_arith (dK row46 k) (lK row46 k) k hd hl hK hs
  unfold fnewD
  exact this

theorem pinP_of_branchPin {n pin : ℕ} (hpin : BranchPin n pin) (hb2 : w8B n ≤ 2 * w8K n)
    (hP16 : 16 * w8K n ≤ PBK (w8B n) (w8K n)) (hpP : pBK (w8B n) (w8K n) ≤ PBK (w8B n) (w8K n)) :
    pin ≤ PBK (w8B n) (w8K n) := by
  rcases hpin with e | e
  · rw [e]
    show w8B n ≤ PBK (w8B n) (w8K n)
    omega
  · rw [e]
    exact hpP

/-- **The middle's cost at a pipe call**, in the shape of the hypothesis `hMid` of
`walshCostClause_branchCost_of` (`c = 3^J + 7`, `j = J`). -/
theorem midCost_le {b k pin J : ℕ} (lam' : ℝ) (h : Facts b k pin) :
    midCost lam' J (fnewD row46 k) (fnewL row46 k) (KK row46 k) (PBK b k + 2 * k + 16)
        (addrBits (fnewA row46 k)) ≤
      (3 ^ J + 7) * VBK b k * (dK row46 k * KK row46 k +
          lK row46 k * ⌈(dK row46 k : ℝ) ^ lam'⌉₊ + lK row46 k + 1) +
        (3 ^ J + 7) * (lK row46 k * (2 ^ k * mulW ((3 ^ J + 7 + 1) * PBK b k))) +
        (3 ^ J + 7) * (2 ^ k / rK row46 k * PBK b k ^ J + rK row46 k * PBK b k ^ J +
          PBK b k ^ J) := by
  obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, hpin⟩ := h
  have hd1 : 1 ≤ dK row46 k := by omega
  have hl1 : 1 ≤ lK row46 k := by omega
  have hm := addrBits_fnewA hd1 hl1
  have hfD : fnewD row46 k + 1 = dK row46 k := by unfold fnewD; omega
  have hfL : fnewL row46 k = lK row46 k := rfl
  have h2m : 2 ^ addrBits (fnewA row46 k) * 2 ^ lK row46 k = 2 ^ k := by rw [← pow_add, hm]
  have hmk : addrBits (fnewA row46 k) ≤ k := by omega
  have h2mk : 2 ^ addrBits (fnewA row46 k) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hmk
  have hRr : 2 ^ addrBits (fnewA row46 k) = 2 ^ k / rK row46 k := by
    unfold rK
    rw [← h2m, Nat.mul_div_cancel _ (by positivity)]
  unfold midCost cvolCube
  rw [hfD, hfL]
  have hT1 : 2 ^ addrBits (fnewA row46 k) *
      (2 * 2 ^ lK row46 k * (PBK b k + 2 * k + 16 + 8 * dK row46 k) + 1) ≤
      (3 ^ J + 7) * VBK b k := by
    have e1 : 2 ^ addrBits (fnewA row46 k) *
        (2 * 2 ^ lK row46 k * (PBK b k + 2 * k + 16 + 8 * dK row46 k) + 1) =
        2 * (2 ^ addrBits (fnewA row46 k) * 2 ^ lK row46 k) *
          (PBK b k + 2 * k + 16 + 8 * dK row46 k) + 2 ^ addrBits (fnewA row46 k) := by ring
    rw [e1, h2m]
    have e2 : 2 * 2 ^ k * (PBK b k + 2 * k + 16 + 8 * dK row46 k) ≤ 2 * 2 ^ k * (3 * PBK b k) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : 2 ^ addrBits (fnewA row46 k) ≤ 2 ^ k * PBK b k :=
      le_trans h2mk (Nat.le_mul_of_pos_right _ (by omega))
    have e4 : VBK b k = 2 ^ k * PBK b k := rfl
    have e5 : 7 * VBK b k ≤ (3 ^ J + 7) * VBK b k :=
      Nat.mul_le_mul_right _ (Nat.le_add_left 7 (3 ^ J))
    have e6 : 2 * 2 ^ k * (3 * PBK b k) = 6 * (2 ^ k * PBK b k) := by ring
    omega
  have hT1' := Nat.mul_le_mul_right (dK row46 k * KK row46 k +
    lK row46 k * ⌈(dK row46 k : ℝ) ^ lam'⌉₊ + lK row46 k + 1) hT1
  have hT2 : lK row46 k * 2 ^ addrBits (fnewA row46 k) * 2 ^ lK row46 k *
      mulW (2 * (PBK b k + 2 * k + 16) + 1) ≤
      (3 ^ J + 7) * (lK row46 k * (2 ^ k * mulW ((3 ^ J + 7 + 1) * PBK b k))) := by
    have e1 : lK row46 k * 2 ^ addrBits (fnewA row46 k) * 2 ^ lK row46 k *
        mulW (2 * (PBK b k + 2 * k + 16) + 1) =
        lK row46 k * ((2 ^ addrBits (fnewA row46 k) * 2 ^ lK row46 k) *
          mulW (2 * (PBK b k + 2 * k + 16) + 1)) := by ring
    rw [e1, h2m]
    have e2 : mulW (2 * (PBK b k + 2 * k + 16) + 1) ≤ mulW ((3 ^ J + 7 + 1) * PBK b k) := by
      apply mulW_mono
      have : 3 * PBK b k ≤ (3 ^ J + 7 + 1) * PBK b k :=
        Nat.mul_le_mul_right _ (by have := Nat.zero_le (3 ^ J); omega)
      omega
    calc lK row46 k * (2 ^ k * mulW (2 * (PBK b k + 2 * k + 16) + 1))
        ≤ lK row46 k * (2 ^ k * mulW ((3 ^ J + 7 + 1) * PBK b k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ ≤ (3 ^ J + 7) * (lK row46 k * (2 ^ k * mulW ((3 ^ J + 7 + 1) * PBK b k))) :=
          Nat.le_mul_of_pos_left _ (by positivity)
  have hT3 : 2 ^ addrBits (fnewA row46 k) *
      (PBK b k + 2 * k + 16 + addrBits (fnewA row46 k) + 1) ^ J ≤
      (3 ^ J + 7) * (2 ^ k / rK row46 k * PBK b k ^ J) := by
    rw [hRr]
    calc 2 ^ k / rK row46 k * (PBK b k + 2 * k + 16 + addrBits (fnewA row46 k) + 1) ^ J
        ≤ 2 ^ k / rK row46 k * (3 * PBK b k) ^ J :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) J)
      _ = 3 ^ J * (2 ^ k / rK row46 k * PBK b k ^ J) := by rw [mul_pow]; ring
      _ ≤ (3 ^ J + 7) * (2 ^ k / rK row46 k * PBK b k ^ J) := Nat.mul_le_mul_right _ (by omega)
  have hT4 : 2 ^ lK row46 k * (PBK b k + 2 * k + 16 + 1) ^ J ≤
      (3 ^ J + 7) * (rK row46 k * PBK b k ^ J) := by
    calc 2 ^ lK row46 k * (PBK b k + 2 * k + 16 + 1) ^ J
        ≤ rK row46 k * (3 * PBK b k) ^ J :=
          Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left (by omega) J)
      _ = 3 ^ J * (rK row46 k * PBK b k ^ J) := by rw [mul_pow]; ring
      _ ≤ (3 ^ J + 7) * (rK row46 k * PBK b k ^ J) := Nat.mul_le_mul_right _ (by omega)
  have e : (3 ^ J + 7) * (2 ^ k / rK row46 k * PBK b k ^ J + rK row46 k * PBK b k ^ J +
      PBK b k ^ J) = (3 ^ J + 7) * (2 ^ k / rK row46 k * PBK b k ^ J) +
      (3 ^ J + 7) * (rK row46 k * PBK b k ^ J) + (3 ^ J + 7) * PBK b k ^ J := by ring
  omega

/-- The middle header `[q, D, ℓ, K, w] ++ a` of a pipe call has `|hdrSyms| ≤ 4P²`. -/
theorem mhdrLen_le {b k pin : ℕ} (p : LayerParams) (P₀ P₁ J : ℕ) (h : Facts b k pin)
    (hKd : KK row46 k ≤ dK row46 k) :
    (hdrSyms ((walshMidData fnewSched p P₀ P₁ J).mhdr (IntMul.rootPrecision b k) k pin)).length ≤
      4 * PBK b k ^ 2 := by
  obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, hpin⟩ := h
  have hPd : PBK b k = 2 * pBK b k + 12 * k + 32 * Nat.clog 2 (pBK b k + k + 2) + 256 := rfl
  have hpd : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hM : ∀ x ∈ (walshMidData fnewSched p P₀ P₁ J).mhdr (IntMul.rootPrecision b k) k pin,
      Nat.size x ≤ 3 * PBK b k := by
    intro x hx
    change x ∈ [schedP (IntMul.rootPrecision b k) k + 2, fnewD row46 k, fnewL row46 k,
      KK row46 k, fnewSched.wI (IntMul.rootPrecision b k) k pin] ++ List.ofFn (fnewA row46 k)
      at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact le_trans (size_le_self _) (by show PBK b k + 2 ≤ 3 * PBK b k; omega)
      · exact le_trans (size_le_self _) (by unfold fnewD; omega)
      · exact le_trans (size_le_self _) (by show lK row46 k ≤ 3 * PBK b k; omega)
      · exact le_trans (size_le_self _) (by omega)
      · exact le_trans (size_le_self _) (by show PBK b k + 2 * k + 16 ≤ 3 * PBK b k; omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      refine le_trans (size_le_self _) ?_
      have : fnewA row46 k i ≤ lK row46 k := by unfold fnewA; split_ifs <;> omega
      omega
  have h1 := length_hdrSyms_le _ _ hM
  have h2 : ((walshMidData fnewSched p P₀ P₁ J).mhdr (IntMul.rootPrecision b k) k pin).length =
      5 + fnewD row46 k := by
    change ([schedP (IntMul.rootPrecision b k) k + 2, fnewD row46 k, fnewL row46 k, KK row46 k,
      fnewSched.wI (IntMul.rootPrecision b k) k pin] ++ List.ofFn (fnewA row46 k)).length = _
    rw [List.length_append, List.length_ofFn]
    rfl
  rw [h2] at h1
  have h3 : 5 + fnewD row46 k ≤ PBK b k := by unfold fnewD; omega
  have h4 : PBK b k * 1 ≤ PBK b k * PBK b k := Nat.mul_le_mul_left _ (by omega)
  have h5 : PBK b k * (3 * PBK b k + 1) = 3 * (PBK b k * PBK b k) + PBK b k * 1 := by ring
  have h6 : PBK b k ^ 2 = PBK b k * PBK b k := by ring
  have h7 := Nat.mul_le_mul_right (3 * PBK b k + 1) h3
  omega

end BranchCostW8Aux

open BranchCostW8Aux BranchCostAux in
/-- **The Walsh cost clause at the concrete kernels** (at `p = row46Layer` this is the `cost`
field of `Assembly.KernelCut P₀ P₁ J`: `walshCostClause_walshMidData row46Layer rfl P₀ P₁ J`): for
every `p : LayerParams` with `p.lam' = Row46.lam'` and all `P₀ P₁ J`, the Walsh-branch step bound
with `rpCost = readParamsCost`, `X = bridgeX τ` (`τ = Row46.tau`) and the middle data
`walshMidData fnewSched p P₀ P₁ J` satisfies `WalshCostClause`. -/
theorem walshCostClause_walshMidData (p : LayerParams)
    (hp : p.lam' = ((Math.Cost.Row46.lam' : ℚ) : ℝ)) (P₀ P₁ J : ℕ) :
    WalshCostClause (branchCost readParamsCost (bridgeX ((Math.Cost.Row46.tau : ℚ) : ℝ)) fnewSched
      (walshMidData fnewSched p P₀ P₁ J)) := by
  apply walshCostClause_branchCost_of
  · refine ⟨64, 6, ?_⟩
    filter_upwards [eventually_w8_facts] with n hf
    intro pin hpin
    obtain ⟨hk, hP16, hP32, hkb, hb2, -, -, -, -, -, hpP, -⟩ := hf
    have hpinP := pinP_of_branchPin hpin hb2 hP16 hpP
    show (w8B n + w8K n + pin + 16) ^ 6 ≤ 64 * PBK (w8B n) (w8K n) ^ 6
    calc (w8B n + w8K n + pin + 16) ^ 6 ≤ (2 * PBK (w8B n) (w8K n)) ^ 6 :=
          Nat.pow_le_pow_left (by omega) 6
      _ = 64 * PBK (w8B n) (w8K n) ^ 6 := by ring
  · refine ⟨1, Filter.Eventually.of_forall fun l => ?_⟩
    show ⌈(l : ℝ) ^ ((Math.Cost.Row46.tau : ℚ) : ℝ)⌉₊ ≤
      1 * (1 + ⌈(l : ℝ) ^ ((Math.Cost.Row46.tau : ℚ) : ℝ)⌉₊)
    omega
  · refine ⟨3 ^ J + 7, J, ?_⟩
    filter_upwards [eventually_w8_facts] with n hf
    intro pin hpin
    obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, -, -, hpP, -⟩ := hf
    have hF : Facts (w8B n) (w8K n) pin :=
      ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, pinP_of_branchPin hpin hb2 hP16 hpP⟩
    have h1 := midCost_le (J := J) ((Math.Cost.Row46.lam' : ℚ) : ℝ) hF
    rw [walshMidData_Tmid, hp]
    exact h1
  · refine ⟨4, 2, ?_⟩
    filter_upwards [eventually_w8_facts] with n hf
    intro pin hpin
    obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, -, hKd, hpP, -⟩ := hf
    have hF : Facts (w8B n) (w8K n) pin :=
      ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, pinP_of_branchPin hpin hb2 hP16 hpP⟩
    exact mhdrLen_le p P₀ P₁ J hF hKd

end SubNLogN.Machine.Pipe
