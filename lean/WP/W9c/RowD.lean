import WP.W9c.RowCSpec

/-!
# WP.W9c.RowD — phase D of the row driver: drop the counters, pop the markers

From `stC` (after the two passes and the zip) to the final row state
`σF = σ0 [W0 := blkE (zip cRe cIm), TR := restT, TL := (filter row).reverse ++ TL]`:
three marker/sign pops, thirteen counter drops (`dropPop`), five marker pops.

The intermediate states are `rst B σ0 ks`: `B` with the stacks `ks` reset to `σ0`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- `B` with the stacks in `ks` reset to their `σ0` content. -/
def rst (B σ0 : RL → List Sym) : List RL → RL → List Sym
  | [] => B
  | k :: ks => Function.update (rst B σ0 ks) k (σ0 k)

/-- The final state of a row. -/
def stF (σ0 : RL → List Sym) (pSub m1 r p_in : ℕ) (taps : List ℤ) (restT : List Sym)
    (row : List (ℤ × ℤ)) : RL → List Sym :=
  Function.update (Function.update (Function.update σ0
    rW0 (blkE (List.zip (rowCells pSub m1 r p_in taps (row.map Prod.fst))
      (rowCells pSub m1 r p_in taps (row.map Prod.snd)))))
    rTR restT)
    rTL ((filterRowSyms taps).reverse ++ σ0 rTL)

/-- Cost of phase D. -/
def costD (C pSub m1 r p_in : ℕ) (taps : List ℤ) : ℕ :=
  21 + C * (bitLen (packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ) taps).natAbs + 1) +
    C * (bitLen (strideOf pSub - 1 + 1) + 1) + C * (bitLen p_in + 1) + C * (bitLen pSub + 1) +
    C * (bitLen (effectiveFilterWidth m1 r) + 1) + C * (bitLen (zlOf r (lowOf m1 r)) + 1) +
    C * (bitLen (zrOf r (lowOf m1 r)) + 1) +
    C * (bitLen (outLenOf (effectiveFilterWidth m1 r) taps) + 1) + C * (bitLen m1 + 1) +
    C * (bitLen r + 1) + C * (bitLen (natLog2Fuel r r) + 1) + C * (bitLen taps.length + 1) +
    C * (bitLen 2 + 1)

variable {σ : Type} (K : RKit σ) {Mul : ℕ → ℕ} {C : ℕ} {ρ : List (HP 12 40 σ)}

theorem rst_cons (B σ0 : RL → List Sym) (ks : List RL) (k : RL) :
    Function.update (rst B σ0 ks) k (σ0 k) = rst B σ0 (k :: ks) := rfl

theorem rst_not_mem (B σ0 : RL → List Sym) : ∀ (ks : List RL) (j : RL), j ∉ ks →
    rst B σ0 ks j = B j
  | [], _, _ => rfl
  | k :: ks, j, hj => by
    simp only [List.mem_cons, not_or] at hj
    simp only [rst]
    rw [Function.update_of_ne hj.1, rst_not_mem B σ0 ks j hj.2]

theorem rst_mem (B σ0 : RL → List Sym) : ∀ (ks : List RL) (j : RL), j ∈ ks →
    rst B σ0 ks j = σ0 j
  | [], _, h => absurd h List.not_mem_nil
  | k :: ks, j, hj => by
    simp only [rst]
    by_cases h : j = k
    · subst h
      rw [Function.update_self]
    · rw [Function.update_of_ne h]
      exact rst_mem B σ0 ks j (by simpa [h] using hj)

theorem ht_popRst (B σ0 : RL → List Sym) (ks : List RL) (k : RL) (hk : k ∉ ks)
    (hB : B k = Sym.mark :: σ0 k) :
    HT ρ (rst B σ0 ks) (popS k) (rst B σ0 (k :: ks)) 1 := by
  refine (HT.popS k _ Sym.mark (σ0 k) ?_ ρ).of_eq (rst_cons B σ0 ks k) le_rfl
  rw [rst_not_mem B σ0 ks k hk, hB]

theorem ht_dropPopGen (hK : RKitOK Mul K C) (B : RL → List Sym) (k : RL) (x : ℕ)
    (rest : List Sym) (hB : B k = natSyms x ++ Sym.mark :: rest) :
    HT ρ B (dropPop K k) (Function.update B k rest) (C * (bitLen x + 1) + 1) := by
  have h1 := HT.dropNat hK.dr rS K.ldr k (by norm_num) B x (Sym.mark :: rest) (termOK_mark _) hB ρ
  have h2 := HT.popS k (Function.update B k (Sym.mark :: rest)) Sym.mark rest
    (Function.update_self _ _ _) ρ
  exact (HT.seq h1 h2).of_eq (Function.update_idem _ _ _) le_rfl

theorem ht_dropRst (hK : RKitOK Mul K C) (B σ0 : RL → List Sym) (ks : List RL) (k : RL)
    (hk : k ∉ ks) (x : ℕ) (hB : B k = natSyms x ++ Sym.mark :: σ0 k) :
    HT ρ (rst B σ0 ks) (dropPop K k) (rst B σ0 (k :: ks)) (C * (bitLen x + 1) + 1) :=
  (ht_dropPopGen K hK (rst B σ0 ks) k x (σ0 k) (by rw [rst_not_mem B σ0 ks k hk, hB])).of_eq
    (rst_cons B σ0 ks k) le_rfl

/-- **Phase D.** -/
theorem ht_rowD (hK : RKitOK Mul K C) (σ0 : RL → List Sym) (pSub m1 r p_in : ℕ)
    (taps : List ℤ) (restT : List Sym) (row : List (ℤ × ℤ)) :
    HT ρ (stC σ0 pSub m1 r p_in taps restT row) (rowD K) (stF σ0 pSub m1 r p_in taps restT row)
      (costD C pSub m1 r p_in taps) := by
  set B := stC σ0 pSub m1 r p_in taps restT row with hB
  set P := packSignedKronecker ((2 ^ (strideOf pSub - 1 + 1) : ℕ) : ℤ) taps with hP
  have e0 : rst B σ0 [] = B := rfl
  have s1 := ht_popRst (ρ := ρ) B σ0 [] rOR (by simp) (by simp [hB, stC])
  have s2 := ht_popRst (ρ := ρ) B σ0 [rOR] rOI (by simp) (by simp [hB, stC])
  have s3 := HT.popS (ρ := ρ) rPG (rst B σ0 [rOI, rOR]) (sgnSym P)
    (natSyms P.natAbs ++ Sym.mark :: σ0 rPG)
    (by rw [rst_not_mem B σ0 _ rPG (by simp)]; simp [hB, hP, stC, stB, intSyms])
  have s4 := (ht_dropPopGen K hK (ρ := ρ)
    (Function.update (rst B σ0 [rOI, rOR]) rPG (natSyms P.natAbs ++ Sym.mark :: σ0 rPG)) rPG
    P.natAbs (σ0 rPG) (Function.update_self _ _ _)).of_eq
    ((Function.update_idem _ _ _).trans (rst_cons B σ0 [rOI, rOR] rPG)) le_rfl
  have s5 := ht_dropRst K hK (ρ := ρ) B σ0 [rPG, rOI, rOR] rK (by simp) (strideOf pSub - 1 + 1)
    (by simp [hB, stC, stB, stA])
  have s6 := ht_dropRst K hK (ρ := ρ) B σ0 [rK, rPG, rOI, rOR] rPIN (by simp) p_in
    (by simp [hB, stC, stB, stA])
  have s7 := ht_dropRst K hK (ρ := ρ) B σ0 [rPIN, rK, rPG, rOI, rOR] rQ (by simp) pSub
    (by simp [hB, stC, stB, stA])
  have s8 := ht_dropRst K hK (ρ := ρ) B σ0 [rQ, rPIN, rK, rPG, rOI, rOR] rWW (by simp) (effectiveFilterWidth m1 r)
    (by simp [hB, stC, stB, stA])
  have s9 := ht_dropRst K hK (ρ := ρ) B σ0 [rWW, rQ, rPIN, rK, rPG, rOI, rOR] rZL (by simp) (zlOf r (lowOf m1 r))
    (by simp [hB, stC, stB, stA, lowOf])
  have s10 := ht_dropRst K hK (ρ := ρ) B σ0 [rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rZR
    (by simp) (zrOf r (lowOf m1 r)) (by simp [hB, stC, stB, stA, lowOf])
  have s11 := ht_dropRst K hK (ρ := ρ) B σ0 [rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rOL
    (by simp) (outLenOf (effectiveFilterWidth m1 r) taps) (by simp [hB, stC, stB, stA])
  have s12 := ht_dropRst K hK (ρ := ρ) B σ0 [rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR]
    rM1 (by simp) m1 (by simp [hB, stC, stB, stA])
  have s13 := ht_dropRst K hK (ρ := ρ) B σ0
    [rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rRR (by simp) r
    (by simp [hB, stC, stB, stA])
  have s14 := ht_dropRst K hK (ρ := ρ) B σ0
    [rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rMR (by simp) (natLog2Fuel r r)
    (by simp [hB, stC, stB, stA])
  have s15 := ht_dropRst K hK (ρ := ρ) B σ0
    [rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rTC (by simp) taps.length
    (by simp [hB, stC, stB, stA])
  have s16 := ht_dropRst K hK (ρ := ρ) B σ0
    [rTC, rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rP2 (by simp) 2
    (by simp [hB, stC, stB, stA])
  have s17 := ht_popRst (ρ := ρ) B σ0
    [rP2, rTC, rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rP0 (by simp)
    (by simp [hB, stC, stB, stA])
  have s18 := ht_popRst (ρ := ρ) B σ0
    [rP0, rP2, rTC, rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rTP
    (by simp) (by simp [hB, stC, stB, stA])
  have s19 := ht_popRst (ρ := ρ) B σ0
    [rTP, rP0, rP2, rTC, rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rT1
    (by simp) (by simp [hB, stC, stB, stA])
  have s20 := ht_popRst (ρ := ρ) B σ0
    [rT1, rTP, rP0, rP2, rTC, rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR] rXR
    (by simp) (by simp [hB, stC])
  have s21 := ht_popRst (ρ := ρ) B σ0
    [rXR, rT1, rTP, rP0, rP2, rTC, rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ, rPIN, rK, rPG, rOI, rOR]
    rXI (by simp) (by simp [hB, stC])
  rw [← e0]
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 (HT.seq s7 (HT.seq s8
    (HT.seq s9 (HT.seq s10 (HT.seq s11 (HT.seq s12 (HT.seq s13 (HT.seq s14 (HT.seq s15
    (HT.seq s16 (HT.seq s17 (HT.seq s18 (HT.seq s19 (HT.seq s20 s21)))))))))))))))))))).of_eq
    ?_ ?_
  · funext j
    by_cases hj : j ∈ [rXI, rXR, rT1, rTP, rP0, rP2, rTC, rMR, rRR, rM1, rOL, rZR, rZL, rWW, rQ,
      rPIN, rK, rPG, rOI, rOR]
    · rw [rst_mem B σ0 _ j hj]
      have hj' : j ≠ rW0 ∧ j ≠ rTR ∧ j ≠ rTL := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
          h <;> subst h <;> decide
      simp [stF, Function.update_of_ne hj'.1, Function.update_of_ne hj'.2.1,
        Function.update_of_ne hj'.2.2]
    · rw [rst_not_mem B σ0 _ j hj]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
        h19, h20⟩ := hj
      simp only [hB, stF, stC, stB, stA, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, if_false]
      by_cases g1 : j = rW0 <;> by_cases g2 : j = rTL <;> by_cases g3 : j = rTR <;> simp_all
  · simp only [costD]
    rw [← hP]
    omega

#assert_std_axioms rst_cons rst_not_mem rst_mem ht_popRst ht_dropPopGen ht_dropRst ht_rowD

end WP.W9c
