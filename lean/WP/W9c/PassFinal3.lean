import WP.W9c.PassFinal2

/-!
# WP.W9c.PassFinal3 — the end of a pass: last window, rewind, markers
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

variable {σ : Type} (K : PKit σ) {Mul : ℕ → ℕ} {C : ℕ}

/-- Cost of the end of a pass. -/
def finalT (C nw Bv Bc p r : ℕ) : ℕ :=
  C * (nw * (Bv + Bc + 1) + (p + nw - 1) / r * (r * (Bc + 1)) + 1) +
    (r * (8 * (Bc + 1) + 12) + 2) + 6

theorem ht_final (hK : PKitOK Mul K C) (S : PL → List Sym) (rx : List Sym) (r zl Bv Bc : ℕ)
    (hr : 0 < r) (wsF EF : List ℤ) (hp : (cyc r zl EF).2 ≤ r)
    (hV : ∀ e ∈ wsF, bitLen e.natAbs ≤ Bv)
    (hcells : ∀ j ≤ wsF.length, ∀ c ∈ (cycAdd r (cyc r zl EF).1 (cyc r zl EF).2 (wsF.take j)).1,
      bitLen c.natAbs ≤ Bc)
    (ρ : List (HP 10 24 σ)) :
    HT ρ (loopSt S rx r zl [] wsF EF) (passFinal K)
      (Function.update (Function.update S pX rx) pOUT
        (listSyms (cyc r zl (EF ++ wsF)).1.reverse ++ Sym.mark :: S pOUT))
      (finalT C wsF.length Bv Bc (cyc r zl EF).2 r) := by
  have hlen : (cyc r zl EF).1.length = r := by simp [cyc, cycAdd_length]
  have happ : cyc r zl (EF ++ wsF) = cycAdd r (cyc r zl EF).1 (cyc r zl EF).2 wsF := by
    unfold cyc; exact cycAdd_append _ _ _ _ _
  obtain ⟨c', p', hcp⟩ : ∃ c' p', cyc r zl (EF ++ wsF) = (c', p') := ⟨_, _, rfl⟩
  rw [hcp]
  rw [hcp] at happ
  set L0 := loopSt S rx r zl [] wsF EF with hL0
  set B := Function.update L0 pWIN (Sym.mark :: S pWIN) with hB
  have hcells' : ∀ j ≤ wsF.length, ∀ c ∈ (cycAdd (cyc r zl EF).1.length (cyc r zl EF).1
      (cyc r zl EF).2 (wsF.take j)).1, bitLen c.natAbs ≤ Bc := by rw [hlen]; exact hcells
  -- 1: emit the last window
  have s1 : HT ρ L0 (callI K.ce [pWIN, pOUT, pTR] pX K.lce)
      (Function.update (Function.update B pTR (listSyms (c'.drop p') ++ Sym.mark :: S pTR)) pOUT
        (listSyms (c'.take p').reverse ++ Sym.mark :: S pOUT))
      (C * (wsF.length * (Bv + Bc + 1) + ((cyc r zl EF).2 + wsF.length - 1) / r * (r * (Bc + 1)) +
        1)) := by
    have e0 : L0 pWIN = listSyms wsF ++ Sym.mark :: S pWIN := by simp [hL0]
    have e1 : L0 pOUT = tapeL (cyc r zl EF).1 (cyc r zl EF).2 ++ S pOUT := by simp [hL0]
    have e2 : L0 pTR = tapeR (cyc r zl EF).1 (cyc r zl EF).2 ++ S pTR := by simp [hL0]
    have h := HT.callI_upd3 K.ce [pWIN, pOUT, pTR] pX (by decide) rfl (by norm_num) K.lce L0
      (.inl 0) (.inl 1) (.inl 2) _ _ _
      (hK.ce Bc Bv (cyc r zl EF).2 (cyc r zl EF).1 wsF (Sym.mark :: S pWIN) (S pOUT) (S pTR) _
        (by rw [hlen]; exact hr) (by rw [hlen]; exact hp) (endOK_mark _) hV hcells'
        e0 e1 e2) ρ
    rw [hlen, ← happ] at h
    have h' : HT ρ L0 (callI K.ce [pWIN, pOUT, pTR] pX K.lce)
        (Function.update (Function.update (Function.update L0 pWIN (Sym.mark :: S pWIN)) pOUT
          (tapeL c' p' ++ S pOUT)) pTR (tapeR c' p' ++ S pTR))
        (C * (wsF.length * (Bv + Bc + 1) + ((cyc r zl EF).2 + wsF.length - 1) / r *
          (r * (Bc + 1)) + 1)) := h
    refine h'.of_eq ?_ le_rfl
    have eL : tapeL c' p' ++ S pOUT = listSyms (c'.take p').reverse ++ Sym.mark :: S pOUT := by
      simp [tapeL]
    have eR : tapeR c' p' ++ S pTR = listSyms (c'.drop p') ++ Sym.mark :: S pTR := by
      simp [tapeR]
    rw [eL, eR]
    funext j
    by_cases h1 : j = pTR
    · subst h1; simp [hB]
    by_cases h2 : j = pOUT
    · subst h2; simp [hB]
    by_cases h3 : j = pWIN
    · subst h3; simp [hB]
    simp [hB, Function.update_of_ne, h1, h2, h3]
  -- 2: rewind
  have hb : ∀ c ∈ c'.drop p', bitLen c.natAbs ≤ Bc := by
    intro c hc
    have := hcells wsF.length le_rfl c
    rw [List.take_length, ← happ] at this
    exact this (List.mem_of_mem_drop hc)
  have s2 := ht_rewind K.lS Bc B (S pTR) (Sym.mark :: S pOUT) ρ (c'.drop p') (c'.take p').reverse hb
  have hrev : (c'.drop p').reverse ++ (c'.take p').reverse = c'.reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [hrev] at s2
  -- 3: markers
  set B2 := Function.update (Function.update B pTR (Sym.mark :: S pTR)) pOUT
    (listSyms c'.reverse ++ Sym.mark :: S pOUT) with hB2
  set B3 := Function.update B2 pTR (S pTR) with hB3
  set B4 := Function.update B3 pWIN (S pWIN) with hB4
  set B5 := Function.update B4 pD (S pD) with hB5
  set B6 := Function.update B5 pE (S pE) with hB6
  set B7 := Function.update B6 pPF (S pPF) with hB7
  have s3 : HT ρ B2 (popS pTR) B3 1 := HT.popS pTR B2 Sym.mark (S pTR) (by simp [hB2]) ρ
  have s4 : HT ρ B3 (popS pWIN) B4 1 :=
    HT.popS pWIN B3 Sym.mark (S pWIN) (by simp [hB3, hB2, hB]) ρ
  have s5 : HT ρ B4 (popS pD) B5 1 :=
    HT.popS pD B4 Sym.mark (S pD) (by simp [hB4, hB3, hB2, hB, hL0]) ρ
  have s6 : HT ρ B5 (popS pE) B6 1 :=
    HT.popS pE B5 Sym.mark (S pE) (by simp [hB5, hB4, hB3, hB2, hB, hL0]) ρ
  have s7 : HT ρ B6 (popS pPF) B7 1 :=
    HT.popS pPF B6 Sym.mark (S pPF) (by simp [hB6, hB5, hB4, hB3, hB2, hB, hL0]) ρ
  have s8 : HT ρ B7 (popS pPP) (Function.update B7 pPP (S pPP)) 1 :=
    HT.popS pPP B7 Sym.mark (S pPP) (by simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]) ρ
  have hdl : (c'.drop p').length ≤ r := by
    have : c'.length = r := by
      have h := congrArg (fun x => x.1.length) hcp
      simp only [cyc, cycAdd_length, List.length_replicate] at h
      exact h.symm
    simp only [List.length_drop]; omega
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 (HT.seq s7
    s8))))))).of_eq ?_ ?_
  · funext j
    by_cases h1 : j = pX
    · subst h1; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0, listSyms_nil]
    by_cases h2 : j = pOUT
    · subst h2; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]
    by_cases h3 : j = pTR
    · subst h3; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]
    by_cases h4 : j = pWIN
    · subst h4; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]
    by_cases h5 : j = pD
    · subst h5; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]
    by_cases h6 : j = pE
    · subst h6; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]
    by_cases h7 : j = pPF
    · subst h7; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]
    by_cases h8 : j = pPP
    · subst h8; simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0]
    simp [hB7, hB6, hB5, hB4, hB3, hB2, hB, hL0, Function.update_of_ne, h1, h2, h3, h4, h5, h6, h7,
      h8, loopSt_other _ _ _ _ _ _ _ j h1 h2 h3 h4 h5 h6 h7 h8]
  · unfold finalT
    have := Nat.mul_le_mul_right (8 * (Bc + 1) + 12) hdl
    omega

#assert_std_axioms ht_final

end WP.W9c
