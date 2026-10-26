import WP.W9c.RowA2

/-!
# WP.W9c.RowB — phase B of the row driver: filter row, `ol`, the constant 2, `Pg`, split
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

theorem natSyms_two : natSyms 2 = [Sym.bit false, Sym.bit true] := by
  have h1 : Computability.encodeNat 1 = [true] := by
    have h := encodeNat_add_add_one 0
    simpa [encodeNat_zero] using h
  have h2 : Computability.encodeNat 2 = [false, true] := by
    have h := encodeNat_add 1
    simp only [show (1 : ℕ) + 1 = 2 from rfl, if_neg one_ne_zero, h1] at h
    exact h
  simp [natSyms, h2]

theorem quant02 (v : ℤ) : gQuantizeCoordToScale 0 2 v = v := by
  rw [IntMulTM.Contracts.W8_gQuantizeCoordToScale_shift_holds]
  simp

/-- Stacks after phase B. -/
def stB (σ0 : RL → List Sym) (pSub m1 r p_in : ℕ) (taps : List ℤ) (restT : List Sym)
    (row : List (ℤ × ℤ)) : RL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update
  (stA σ0 pSub m1 r p_in)
    rTR restT)
    rTL ((filterRowSyms taps).reverse ++ σ0 rTL))
    rTC (natSyms taps.length ++ Sym.mark :: σ0 rTC))
    rOL (natSyms (outLenOf (effectiveFilterWidth m1 r) taps) ++ Sym.mark :: σ0 rOL))
    rP2 (natSyms 2 ++ Sym.mark :: σ0 rP2))
    rPG (intSyms (packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ) taps) ++
      Sym.mark :: σ0 rPG))
    rW0 [])
    rXR (listSyms (row.map Prod.fst) ++ Sym.mark :: σ0 rXR))
    rXI (listSyms (row.map Prod.snd) ++ Sym.mark :: σ0 rXI)

variable {σ : Type} (K : RKit σ) {Mul : ℕ → ℕ} {C : ℕ} {ρ : List (HP 12 40 σ)}

theorem ht_rowB (hK : RKitOK Mul K C) (σ0 : RL → List Sym) (pSub m1 r p_in w : ℕ)
    (taps : List ℤ) (restT : List Sym) (row : List (ℤ × ℤ))
    (hTR : σ0 rTR = filterRowSyms taps ++ restT) (hW0 : σ0 rW0 = blkE row)
    (htW : taps.length ≤ effectiveFilterWidth m1 r) (htB : ∀ t ∈ taps, bitLen t.natAbs ≤ w) :
    ∃ T, HT ρ (stA σ0 pSub m1 r p_in) (rowB K) (stB σ0 pSub m1 r p_in taps restT row) T ∧
      T ≤ C * ((filterRowSyms taps).length + 1) +
        C * (bitLen (effectiveFilterWidth m1 r) + bitLen taps.length + 1) +
        (C + (max 1 (C * (zerosLead (Computability.encodeNat
          (effectiveFilterWidth m1 r + taps.length)) + 1)) + 1)) + 2 +
        C * (taps.length * (w + (strideOf pSub - 1 + 1) + 0 + 2 + 1) +
          bitLen (effectiveFilterWidth m1 r) + 1) +
        C * ((blkE row).length + 1) := by
  set L0 := stA σ0 pSub m1 r p_in with hL0
  have v0TR : L0 rTR = filterRowSyms taps ++ restT := by simp [hL0, stA, hTR]
  -- 1: filter row
  set L1 := Function.update (Function.update (Function.update (Function.update L0
    rTR restT) rTL ((filterRowSyms taps).reverse ++ L0 rTL)) rTP (listSyms taps ++ L0 rTP))
    rTC (natSyms taps.length ++ L0 rTC) with hL1
  have s1 : HT ρ L0 (callI K.tp [rTR, rTL, rTP, rTC] rS K.ltp) L1
      (C * ((filterRowSyms taps).length + 1)) :=
    HT.callI_gen K.tp [rTR, rTL, rTP, rTC] rS (by decide) rfl (by norm_num) K.ltp L0 L1
      (hK.tp taps restT _ v0TR) (fun i => by fin_cases i <;> rfl) (fun j => by simp)
      (fun g hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
        obtain ⟨h1, h2, h3, h4⟩ := hg
        simp [hL1, Function.update_of_ne, h1, h2, h3, h4]) ρ
  -- 2: W + T
  have v1WW : L1 rWW = natSyms (effectiveFilterWidth m1 r) ++ Sym.mark :: σ0 rWW := by
    simp [hL1, hL0, stA]
  have v1TC : L1 rTC = natSyms taps.length ++ Sym.mark :: σ0 rTC := by simp [hL1, hL0, stA]
  have v1OL : L1 rOL = Sym.mark :: σ0 rOL := by simp [hL1, hL0, stA]
  set L2 := Function.update L1 rOL (natSyms (effectiveFilterWidth m1 r + taps.length) ++ L1 rOL)
    with hL2
  have s2 : HT ρ L1 (callI K.ad [rWW, rTC, rOL] rS K.lad) L2
      (C * (bitLen (effectiveFilterWidth m1 r) + bitLen taps.length + 1)) :=
    HT.callI_upd K.ad [rWW, rTC, rOL] rS (by decide) rfl (by norm_num) K.lad L1 (.inl 2) _
      (hK.ad _ _ _ _ _ (termOK_mark _) (termOK_mark _) v1WW v1TC) ρ
  -- 3: ol
  set L3 := Function.update L1 rOL
    (natSyms (outLenOf (effectiveFilterWidth m1 r) taps) ++ Sym.mark :: σ0 rOL) with hL3
  have v2TC : L2 rTC = natSyms taps.length ++ Sym.mark :: σ0 rTC := by simp [hL2, v1TC]
  have s3 : HT ρ L2 (ifZero K rTC TMFw.Lib.skip (callI K.dc [rOL] rS K.ldc)) L3
      (C + (max 1 (C * (zerosLead (Computability.encodeNat
        (effectiveFilterWidth m1 r + taps.length)) + 1)) + 1)) := by
    refine ht_ifZero K hK.iz rTC L2 L3 _ _ taps.length _ (termOK_mark _) v2TC ?_ ?_
    · intro h0
      refine (ht_skip L2).of_eq ?_ le_rfl
      have ht : taps = [] := List.eq_nil_of_length_eq_zero h0
      rw [hL2, hL3, v1OL, h0]
      simp [outLenOf, ht]
    · intro h0
      have eOL : L2 rOL = natSyms (effectiveFilterWidth m1 r + taps.length - 1 + 1) ++ L1 rOL := by
        rw [hL2, Function.update_self, show effectiveFilterWidth m1 r + taps.length - 1 + 1 =
          effectiveFilterWidth m1 r + taps.length by omega]
      have h : HT ρ L2 (callI K.dc [rOL] rS K.ldc)
          (Function.update L2 rOL (natSyms (effectiveFilterWidth m1 r + taps.length - 1) ++ L1 rOL))
          (C * (zerosLead (Computability.encodeNat
            (effectiveFilterWidth m1 r + taps.length - 1 + 1)) + 1)) :=
        HT.callI_upd K.dc [rOL] rS (List.nodup_singleton _) rfl (by norm_num) K.ldc L2 (.inl 0) _
          (hK.dc (effectiveFilterWidth m1 r + taps.length - 1) (L1 rOL) _
            (by rw [v1OL]; exact termOK_mark _) eOL) ρ
      rw [show effectiveFilterWidth m1 r + taps.length - 1 + 1 =
        effectiveFilterWidth m1 r + taps.length by omega] at h
      refine h.of_eq ?_ le_rfl
      have ht : taps ≠ [] := fun e => h0 (by rw [e]; rfl)
      rw [hL2, hL3, v1OL, Function.update_idem]
      simp [outLenOf, ht]
  -- 4: the constant 2
  set L4 := Function.update L3 rP2 (Sym.bit true :: L3 rP2) with hL4
  set L5 := Function.update L4 rP2 (Sym.bit false :: L4 rP2) with hL5
  have s4 : HT ρ L3 (pushS rP2 (.bit true)) L4 1 := HT.pushS rP2 _ L3 ρ
  have s5 : HT ρ L4 (pushS rP2 (.bit false)) L5 1 := HT.pushS rP2 _ L4 ρ
  -- 5: Pg
  have v5TP : L5 rTP = listSyms taps ++ Sym.mark :: σ0 rTP := by
    simp [hL5, hL4, hL3, hL2, hL1, hL0, stA]
  have v5K : L5 rK = natSyms (strideOf pSub - 1 + 1) ++ Sym.mark :: σ0 rK := by
    simp [hL5, hL4, hL3, hL2, hL1, hL0, stA]
  have v5P0 : L5 rP0 = natSyms 0 ++ Sym.mark :: σ0 rP0 := by
    simp [hL5, hL4, hL3, hL2, hL1, hL0, stA, natSyms_zero'']
  have v5P2 : L5 rP2 = natSyms 2 ++ Sym.mark :: σ0 rP2 := by
    simp [hL5, hL4, hL3, hL2, hL1, hL0, stA, natSyms_two]
  have v5WW : L5 rWW = natSyms (effectiveFilterWidth m1 r) ++ Sym.mark :: σ0 rWW := by
    simp [hL5, hL4, hL3, hL2, hL1, hL0, stA]
  set L6 := Function.update (Function.update L5 rTP
    (listSyms (taps.drop (effectiveFilterWidth m1 r)) ++ Sym.mark :: σ0 rTP)) rPG
    (intSyms (packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ)
      ((taps.take (effectiveFilterWidth m1 r)).map (gQuantizeCoordToScale 0 2))) ++ L5 rPG)
    with hL6
  have s6 : HT ρ L5 (callI K.pk [rTP, rK, rP0, rP2, rWW, rPG] rS K.lpk) L6
      (C * ((taps.take (effectiveFilterWidth m1 r)).length *
        (w + (strideOf pSub - 1 + 1) + 0 + 2 + 1) + bitLen (effectiveFilterWidth m1 r) + 1)) :=
    HT.callI_upd2 K.pk [rTP, rK, rP0, rP2, rWW, rPG] rS (by decide) rfl (by norm_num) K.lpk L5
      (.inl 0) (.inl 5) _ _
      (hK.pk (strideOf pSub - 1 + 1) 0 2 (effectiveFilterWidth m1 r) w taps (Sym.mark :: σ0 rTP)
        (Sym.mark :: σ0 rK) (Sym.mark :: σ0 rP0) (Sym.mark :: σ0 rP2) (Sym.mark :: σ0 rWW) _
        (by omega) htB (endOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
        (termOK_mark _) v5TP v5K v5P0 v5P2 v5WW) ρ
  -- 6: split
  have v6W0 : L6 rW0 = blkE row ++ [] := by
    simp [hL6, hL5, hL4, hL3, hL2, hL1, hL0, stA, hW0]
  set L7 := Function.update (Function.update (Function.update L6 rW0 []) rXR
    (listSyms (row.map Prod.fst) ++ L6 rXR)) rXI (listSyms (row.map Prod.snd) ++ L6 rXI) with hL7
  have s7 : HT ρ L6 (callI K.sp [rW0, rXR, rXI] rS K.lsp) L7 (C * ((blkE row).length + 1)) :=
    HT.callI_upd3 K.sp [rW0, rXR, rXI] rS (by decide) rfl (by norm_num) K.lsp L6 (.inl 0)
      (.inl 1) (.inl 2) _ _ _ (hK.sp row [] _ (fun x hx => by simp at hx) v6W0) ρ
  have htake : taps.take (effectiveFilterWidth m1 r) = taps := List.take_of_length_le htW
  have hdrop : taps.drop (effectiveFilterWidth m1 r) = [] := List.drop_eq_nil_of_le htW
  have hmap : taps.map (gQuantizeCoordToScale 0 2) = taps := by
    conv_rhs => rw [← List.map_id taps]
    exact List.map_congr_left (fun v _ => quant02 v)
  refine ⟨_, (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 s7)))))).of_eq ?_
    le_rfl, ?_⟩
  · funext j
    by_cases h1 : j = rTR
    · subst h1; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h2 : j = rTL
    · subst h2; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h3 : j = rTP
    · subst h3; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h4 : j = rTC
    · subst h4; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h5 : j = rOL
    · subst h5; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h6 : j = rP2
    · subst h6; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h7 : j = rPG
    · subst h7; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h8 : j = rW0
    · subst h8; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h9 : j = rXR
    · subst h9; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    by_cases h10 : j = rXI
    · subst h10; simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, stA, htake, hdrop, hmap, listSyms_nil, natSyms_two]
    simp [hL7, hL6, hL5, hL4, hL3, hL2, hL1, hL0, stB, Function.update_of_ne, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · rw [htake]
    omega

#assert_std_axioms natSyms_two quant02 ht_rowB

end WP.W9c
