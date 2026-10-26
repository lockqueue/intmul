import WP.W9c.RowA1

/-!
# WP.W9c.RowA2 — phase A of the row driver: markers, header, `k`, `(zl, zr)`
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Initial left cells: `0` if `low = 0`, else `r - low`. -/
def zlOf (r low : ℕ) : ℕ := if low = 0 then 0 else r - low
/-- Initial right cells: `r` if `low = 0`, else `low`. -/
def zrOf (r low : ℕ) : ℕ := if low = 0 then r else low

/-- Stacks after phase A. -/
def stA (σ0 : RL → List Sym) (pSub m1 r p_in : ℕ) : RL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update σ0
    rXR (Sym.mark :: σ0 rXR))
    rXI (Sym.mark :: σ0 rXI))
    rPG (Sym.mark :: σ0 rPG))
    rK (natSyms (strideOf pSub - 1 + 1) ++ Sym.mark :: σ0 rK))
    rPIN (natSyms p_in ++ Sym.mark :: σ0 rPIN))
    rQ (natSyms pSub ++ Sym.mark :: σ0 rQ))
    rWW (natSyms (effectiveFilterWidth m1 r) ++ Sym.mark :: σ0 rWW))
    rZL (natSyms (zlOf r (m1 % 2 ^ natLog2Fuel r r)) ++ Sym.mark :: σ0 rZL))
    rZR (natSyms (zrOf r (m1 % 2 ^ natLog2Fuel r r)) ++ Sym.mark :: σ0 rZR))
    rOL (Sym.mark :: σ0 rOL))
    rM1 (natSyms m1 ++ Sym.mark :: σ0 rM1))
    rRR (natSyms r ++ Sym.mark :: σ0 rRR))
    rMR (natSyms (natLog2Fuel r r) ++ Sym.mark :: σ0 rMR))
    rTP (Sym.mark :: σ0 rTP))
    rTC (Sym.mark :: σ0 rTC))
    rP0 (Sym.mark :: σ0 rP0))
    rP2 (Sym.mark :: σ0 rP2))
    rT1 (Sym.mark :: σ0 rT1)

variable {σ : Type} (K : RKit σ) {Mul : ℕ → ℕ} {C : ℕ} {ρ : List (HP 12 40 σ)}

theorem natSyms_zero'' : natSyms 0 = [] := natSyms_zero'

theorem ht_rowA (hK : RKitOK Mul K C) (σ0 : RL → List Sym) (pSub m1 t1 r p_in : ℕ)
    (r0 r1 : List Sym) (hC0 : σ0 rC0 = hdrSyms (preTapeFields pSub m1 t1 r) ++ r0)
    (hC1 : σ0 rC1 = hdrSyms [p_in] ++ r1) (hr : r = 2 ^ natLog2Fuel r r) :
    ∃ T, HT ρ σ0 (rowA K) (stA σ0 pSub m1 r p_in) T ∧
      T ≤ 19 + C * ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 1) +
        (C + (max (C * (ones (Computability.encodeNat (strideOf pSub)) + 1)) 1 + 1)) +
        C * (bitLen m1 + 1) +
        C * (min (natLog2Fuel r r) (bitLen m1) + bitLen (natLog2Fuel r r) + 1) +
        C * (bitLen (m1 / 2 ^ natLog2Fuel r r) + 1) +
        (C + (max (C * (bitLen r + 1)) (C * (bitLen r + bitLen (m1 % 2 ^ natLog2Fuel r r) + 1))
          + 1)) := by
  set M0 := marksOn σ0 rMarked with hM0
  have hm : ∀ j ∈ rMarked, M0 j = Sym.mark :: σ0 j := fun j hj => marksOn_mem _ _ _ (by decide) hj
  have hnm : ∀ j ∉ rMarked, M0 j = σ0 j := fun j hj => marksOn_not_mem _ _ _ hj
  have tm : ∀ j ∈ rMarked, TermOK (M0 j) := fun j hj => by rw [hm j hj]; exact termOK_mark _
  have s1 : HT ρ σ0 (pushMarks rMarked) M0 (rMarked.length + 1) := ht_pushMarks rMarked σ0
  -- header
  set M1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update M0
      rQ (natSyms pSub ++ M0 rQ))
      rM1 (natSyms m1 ++ M0 rM1))
      rRR (natSyms r ++ M0 rRR))
      rMR (natSyms (natLog2Fuel r r) ++ M0 rMR))
      rWW (natSyms (effectiveFilterWidth m1 r) ++ M0 rWW))
      rK (natSyms (strideOf pSub) ++ M0 rK))
      rPIN (natSyms p_in ++ M0 rPIN) with hM1
  have e0 : M0 rC0 = hdrSyms (preTapeFields pSub m1 t1 r) ++ r0 := by
    rw [hnm _ (by simp [rMarked])]; exact hC0
  have e1 : M0 rC1 = hdrSyms [p_in] ++ r1 := by rw [hnm _ (by simp [rMarked])]; exact hC1
  have s2 : HT ρ M0 (callI K.hd [rC0, rC1, rQ, rM1, rRR, rMR, rWW, rK, rPIN] rS K.lhd) M1
      (C * ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 1)) :=
    HT.callI_gen K.hd [rC0, rC1, rQ, rM1, rRR, rMR, rWW, rK, rPIN] rS (by decide) rfl
      (by norm_num) K.lhd M0 M1 (hK.hd pSub m1 t1 r p_in r0 r1 _ e0 e1)
      (fun i => by fin_cases i <;> rfl)
      (fun j => by simp)
      (fun g hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
        obtain ⟨-, -, h2, h3, h4, h5, h6, h7, h8⟩ := hg
        simp [hM1, Function.update_of_ne, h2, h3, h4, h5, h6, h7, h8]) ρ
  -- k := s - 1 + 1
  set M2 := Function.update M1 rK (natSyms (strideOf pSub - 1 + 1) ++ M0 rK) with hM2
  have eK : M1 rK = natSyms (strideOf pSub) ++ M0 rK := by simp [hM1]
  have s3 : HT ρ M1 (ifZero K rK (callI K.ic [rK] rS K.lic) TMFw.Lib.skip) M2
      (C + (max (C * (ones (Computability.encodeNat (strideOf pSub)) + 1)) 1 + 1)) := by
    refine ht_ifZero K hK.iz rK M1 M2 _ _ (strideOf pSub) (M0 rK) (tm _ (by simp [rMarked])) eK
      ?_ ?_
    · intro h0
      have h : HT ρ M1 (callI K.ic [rK] rS K.lic)
          (Function.update M1 rK (natSyms (strideOf pSub + 1) ++ M0 rK))
          (C * (ones (Computability.encodeNat (strideOf pSub)) + 1)) :=
        HT.callI_upd K.ic [rK] rS (List.nodup_singleton _) rfl (by norm_num) K.lic M1 (.inl 0) _
          (hK.ic (strideOf pSub) (M0 rK) _ (tm _ (by simp [rMarked])) eK) ρ
      rw [show strideOf pSub + 1 = strideOf pSub - 1 + 1 by omega] at h
      exact h
    · intro h0
      refine (ht_skip M1).of_eq ?_ le_rfl
      rw [hM2, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0), ← eK, Function.update_eq_self]
  -- T1 := m1
  set M3 := Function.update M2 rT1 (natSyms m1 ++ M0 rT1) with hM3
  have s4 : HT ρ M2 (callI K.cp [rM1, rT1] rS K.lcp) M3 (C * (bitLen m1 + 1)) := by
    have h := HT.copyNat hK.cp rS K.lcp rM1 rT1 (by decide) (by norm_num) M2 m1 (M0 rM1)
      (tm _ (by simp [rMarked])) (by simp [hM2, hM1]) ρ
    rwa [show M2 rT1 = M0 rT1 by simp [hM2, hM1]] at h
  -- split m1 at mr
  set M4 := Function.update (Function.update M3 rT1 (natSyms (m1 / 2 ^ natLog2Fuel r r) ++ M0 rT1))
    rZR (natSyms (m1 % 2 ^ natLog2Fuel r r) ++ M3 rZR) with hM4
  have e5a : M3 rT1 = natSyms m1 ++ M0 rT1 := by simp [hM3]
  have e5b : M3 rMR = natSyms (natLog2Fuel r r) ++ M0 rMR := by simp [hM3, hM2, hM1]
  have s5 : HT ρ M3 (callI K.sa [rT1, rMR, rZR] rS K.lsa) M4
      (C * (min (natLog2Fuel r r) (bitLen m1) + bitLen (natLog2Fuel r r) + 1)) :=
    HT.callI_upd2 K.sa [rT1, rMR, rZR] rS (by decide) rfl (by norm_num) K.lsa M3 (.inl 0) (.inl 2)
      _ _ (hK.sa m1 (natLog2Fuel r r) (M0 rT1) (M0 rMR) _ (tm _ (by simp [rMarked]))
        (tm _ (by simp [rMarked])) e5a e5b) ρ
  -- drop m1 / 2^mr
  set M5 := Function.update M4 rT1 (M0 rT1) with hM5
  have s6 : HT ρ M4 (callI K.dr [rT1] rS K.ldr) M5
      (C * (bitLen (m1 / 2 ^ natLog2Fuel r r) + 1)) :=
    HT.dropNat hK.dr rS K.ldr rT1 (by norm_num) M4 (m1 / 2 ^ natLog2Fuel r r) (M0 rT1)
      (tm _ (by simp [rMarked])) (by simp [hM4]) ρ
  -- (zl, zr)
  have eZR : M5 rZR = natSyms (m1 % 2 ^ natLog2Fuel r r) ++ M0 rZR := by
    simp [hM5, hM4, hM3, hM2, hM1]
  have eRR : M5 rRR = natSyms r ++ M0 rRR := by simp [hM5, hM4, hM3, hM2, hM1]
  have hlow : m1 % 2 ^ natLog2Fuel r r ≤ r := by
    have := Nat.mod_lt m1 (show 0 < 2 ^ natLog2Fuel r r by positivity)
    omega
  set M6 := Function.update (Function.update M5 rZR
    (natSyms (zrOf r (m1 % 2 ^ natLog2Fuel r r)) ++ M0 rZR)) rZL
    (natSyms (zlOf r (m1 % 2 ^ natLog2Fuel r r)) ++ M0 rZL) with hM6
  have s7 : HT ρ M5 (ifZero K rZR (callI K.cp [rRR, rZR] rS K.lcp)
      (callI K.sb [rRR, rZR, rZL] rS K.lsb)) M6
      (C + (max (C * (bitLen r + 1)) (C * (bitLen r + bitLen (m1 % 2 ^ natLog2Fuel r r) + 1))
        + 1)) := by
    refine ht_ifZero K hK.iz rZR M5 M6 _ _ (m1 % 2 ^ natLog2Fuel r r) (M0 rZR)
      (tm _ (by simp [rMarked])) eZR ?_ ?_
    · intro h0
      have h := HT.copyNat hK.cp rS K.lcp rRR rZR (by decide) (by norm_num) M5 r (M0 rRR)
        (tm _ (by simp [rMarked])) eRR ρ
      refine h.of_eq ?_ le_rfl
      have eZL : M5 rZL = M0 rZL := by simp [hM5, hM4, hM3, hM2, hM1]
      have h0' : m1 % 2 ^ r.log2 = 0 := by rwa [natLog2Fuel_self] at h0
      funext j
      by_cases h1 : j = rZL
      · subst h1; simp [hM6, zlOf, h0', natSyms_zero'', eZL]
      · by_cases h2 : j = rZR
        · subst h2; simp [hM6, zrOf, h0', eZR, natSyms_zero'']
        · simp [hM6, Function.update_of_ne h1, Function.update_of_ne h2]
    · intro h0
      have h : HT ρ M5 (callI K.sb [rRR, rZR, rZL] rS K.lsb)
          (Function.update M5 rZL (natSyms (r - m1 % 2 ^ natLog2Fuel r r) ++ M5 rZL))
          (C * (bitLen r + bitLen (m1 % 2 ^ natLog2Fuel r r) + 1)) :=
        HT.callI_upd K.sb [rRR, rZR, rZL] rS (by decide) rfl (by norm_num) K.lsb M5
          (.inl 2) _ (hK.sb r (m1 % 2 ^ natLog2Fuel r r) (M0 rRR) (M0 rZR) _
            (tm _ (by simp [rMarked])) (tm _ (by simp [rMarked])) hlow eRR eZR) ρ
      refine h.of_eq ?_ le_rfl
      have eZL : M5 rZL = M0 rZL := by simp [hM5, hM4, hM3, hM2, hM1]
      have h0' : ¬ m1 % 2 ^ r.log2 = 0 := by rwa [natLog2Fuel_self] at h0
      funext j
      by_cases h1 : j = rZL
      · subst h1; simp [hM6, zlOf, h0', eZL]
      · by_cases h2 : j = rZR
        · subst h2; simp [hM6, zrOf, h0', eZR]
        · simp [hM6, Function.update_of_ne h1, Function.update_of_ne h2]
  refine ⟨_, (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 s7)))))).of_eq ?_
    le_rfl, by simp only [rMarked, List.length_cons, List.length_nil]; omega⟩
  funext j
  by_cases hj : j ∈ rMarked
  · simp only [rMarked, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rXR ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rXI ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rPG ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rK ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rPIN ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rQ ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rWW ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rZL ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rZR ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rOL ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rM1 ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rRR ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rMR ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rTP ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rTC ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rP0 ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rP2 ∈ rMarked)]
    · simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hm _ (by simp [rMarked] : rT1 ∈ rMarked)]
  · have hj' := hj
    simp only [rMarked, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hj'
    simp [hM6, hM5, hM4, hM3, hM2, hM1, stA, hnm j hj, Function.update_of_ne, h1, h2, h3, h4, h5,
      h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]

#assert_std_axioms ht_rowA

end WP.W9c
