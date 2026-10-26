/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixParamBlk
import SubNLogN.Math.Walsh.Proofs.LayoutPerm

/-!
# K4-PREFIX: the parameter phase (`Machine/FFT/PrefixParam.lean`)

**Scope (honest summary).** Proves `prefixParam_holds : PrefixAux.PrefixParamStmt`
(`Machine/FFT/PrefixParamSpec.lean`, frozen by K4-DIF) with no hypotheses; no `sorry`.
The kernel (`prmProg`, `Machine/FFT/PrefixParamBlk.lean`; `Par = Unit`, runtime-uniform):
read `D, ℓ, K, w` from the header (fields in front parked and restored), convert `D, ℓ, K, v` to
unary, compute `ℓ - (v + 1)`, branch on whether it is zero (`v + 1 = ℓ`), compute `PrefixAux.pfY ℓ K v`
(by a cyclic counter for `(ℓ - 1) mod K`) and the counter `2^D - 1` (case `v + 1 < ℓ`), then
`2^{D·PrefixAux.pfY}` marks (repeated copying and doubling), `natSyms (w + D)` (`D` increments), and push the
four outputs. Exponent `J := 2`, constant `C := 3000`: the unary values are at most `2^{m₀}`
(`D·PrefixAux.pfY ≤ D(ℓ - 1) ≤ m₀`, `D ≤ m₀`, `addrBits_eq`), all other work is polynomial in `w + m₀`,
and reading the header costs at most `27·|midHdr|`.
-/

namespace SubNLogN.Machine.FFT

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine SubNLogN.Machine.FFT.DIF
  SubNLogN.Machine.FFT.TwiddleAux SubNLogN.Machine.FFT.PrefixParamAux SubNLogN.Math.Walsh

namespace PrefixParamAux

theorem xbl_le (x Y0 : ℕ) (hx : x ≤ Y0) : x * (6 * bitLen x + 11) ≤ 17 * (Y0 * Y0) := by
  have hb : bitLen x ≤ x := bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have h1 : x * (6 * bitLen x + 11) ≤ Y0 * (6 * Y0 + 11) := Nat.mul_le_mul hx (by omega)
  have h2 : Y0 * (6 * Y0 + 11) = 6 * (Y0 * Y0) + 11 * Y0 := by ring
  rcases Nat.eq_zero_or_pos Y0 with h0 | h0
  · subst h0; simp at hx; subst hx; simp
  · have h3 : 1 * Y0 ≤ Y0 * Y0 := Nat.mul_le_mul_right Y0 h0
    omega

/-- **Cost arithmetic of the parameter phase.** -/
theorem prmCost_le (D ℓ Kp v w m y H : ℕ) (hDm : D ≤ m) (hDy : D * y ≤ m) (hℓ : ℓ ≤ w)
    (hK : Kp ≤ w) (hv : v ≤ w) (hy : y ≤ w) :
    27 * H + ((9 * bitLen v + 4 + (D * (6 * bitLen D + 11) + 2 + (ℓ * (6 * bitLen ℓ + 11) + 2 +
      (Kp * (6 * bitLen Kp + 11) + 2 + (v * (6 * bitLen v + 11) + 2))))) +
      ((9 * ℓ + 4 + (9 * v + 4 + (1 + ((v + 1) * 4 + 2)))) +
      ((1 + (neCost ℓ Kp v D + (9 * ℓ + 4 + 1) + 1)) +
      ((9 * D + 4 + (D * (9 * y + 7) + 2 + (D * y * (13 * 2 ^ (D * y) + 12) + 2 +
        (1 + (4 * 2 ^ (D * y) + 2))))) +
      ((9 * D + 4 + (D * (6 * bitLen (w + D) + 12) + 2 + (9 * bitLen (w + D) + 4 +
        (3 * bitLen (w + D) + 2)))) +
      (3 * D + 2 + (3 * ℓ + 2 + (3 * Kp + 2 + (3 * v + 2 + (3 * y + 2)))))))))) ≤
    3000 * (2 ^ m * (w + m + 1) ^ 2 + H) := by
  -- atoms
  obtain ⟨Y0, hY0⟩ : ∃ Y0, Y0 = w + m + 1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ m := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hA]; exact Nat.one_le_two_pow
  have hY1 : 1 ≤ Y0 := by omega
  have hB : 2 ^ m * (w + m + 1) ^ 2 = A * (Y0 * Y0) := by rw [hA, hY0]; ring
  rw [hB]
  have hYY : 1 * Y0 ≤ Y0 * Y0 := Nat.mul_le_mul_right Y0 hY1
  have hYB : 1 * (Y0 * Y0) ≤ A * (Y0 * Y0) := Nat.mul_le_mul_right _ hA1
  have hAY : A * Y0 ≤ A * (Y0 * Y0) := Nat.mul_le_mul_left A (by omega)
  have hAB : A * 1 ≤ A * Y0 := Nat.mul_le_mul_left A hY1
  -- unary conversions
  have u1 := xbl_le D Y0 (by omega)
  have u2 := xbl_le ℓ Y0 (by omega)
  have u3 := xbl_le Kp Y0 (by omega)
  have u4 := xbl_le v Y0 (by omega)
  have hbv : bitLen v ≤ v := bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  -- the branch
  have n1 : ℓ * (4 * Kp + 11) ≤ Y0 * (4 * Y0 + 11) := Nat.mul_le_mul (by omega) (by omega)
  have n1' : Y0 * (4 * Y0 + 11) = 4 * (Y0 * Y0) + 11 * Y0 := by ring
  have hpD : 2 ^ D ≤ A := by rw [hA]; exact Nat.pow_le_pow_right (by norm_num) hDm
  have n2 : D * (13 * 2 ^ D + 12) ≤ Y0 * (13 * A + 12) := Nat.mul_le_mul (by omega) (by omega)
  have n2' : Y0 * (13 * A + 12) = 13 * (A * Y0) + 12 * Y0 := by ring
  have hne : neCost ℓ Kp v D ≤ ℓ * (4 * Kp + 11) + D * (13 * 2 ^ D + 12) + 4 * 2 ^ D +
      25 * ℓ + 12 * Kp + 9 * v + 9 * D + 40 := le_of_eq rfl
  -- powers
  have hpDy : 2 ^ (D * y) ≤ A := by rw [hA]; exact Nat.pow_le_pow_right (by norm_num) hDy
  have m1 : D * (9 * y + 7) ≤ Y0 * (9 * Y0 + 7) := Nat.mul_le_mul (by omega) (by omega)
  have m1' : Y0 * (9 * Y0 + 7) = 9 * (Y0 * Y0) + 7 * Y0 := by ring
  have m2 : D * y * (13 * 2 ^ (D * y) + 12) ≤ Y0 * (13 * A + 12) :=
    Nat.mul_le_mul (by omega) (by omega)
  -- the width
  have hbw : bitLen (w + D) ≤ w + D := bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have w1 : D * (6 * bitLen (w + D) + 12) ≤ Y0 * (6 * Y0 + 12) :=
    Nat.mul_le_mul (by omega) (by omega)
  have w1' : Y0 * (6 * Y0 + 12) = 6 * (Y0 * Y0) + 12 * Y0 := by ring
  have hfin : 3000 * (A * (Y0 * Y0) + H) = 3000 * (A * (Y0 * Y0)) + 3000 * H := by ring
  rw [hfin]
  omega

set_option maxHeartbeats 1000000 in
/-- The final stacks of the parameter phase. -/
theorem prm_final (S : PL → List Sym) (hClean : KClean S) (D ℓ Kp w v y n2 n3 z : ℕ) :
    let SA := Function.update (Function.update (Function.update (Function.update
      (Function.update S sBD (natSyms D)) sBL (natSyms ℓ)) sBK (natSyms Kp)) sBW (natSyms w))
      nO5 (natSyms w ++ S nO5)
    let SB := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update SA sBD []) sBL []) sBK []) sUD
      (List.replicate D .mark)) sUL (List.replicate ℓ .mark)) sUK (List.replicate Kp .mark)) sUV
      (List.replicate v .mark)
    let SC := Function.update SB sZ (List.replicate z .mark)
    let SD := Function.update (Function.update (Function.update SC sZ []) sY
      (List.replicate y .mark)) nO3 (List.replicate n3 .mark ++ SC nO3)
    let SE := Function.update SD nO2 (List.replicate n2 .mark ++ SD nO2)
    let SF := Function.update (Function.update SE sBW []) nO4 (natSyms (w + D) ++ SE nO4)
    Function.update (Function.update (Function.update (Function.update (Function.update SF
      sUD []) sUL []) sUK []) sUV []) sY [] =
    Function.update (Function.update (Function.update (Function.update S nO2
      (List.replicate n2 .mark ++ S nO2)) nO3 (List.replicate n3 .mark ++ S nO3)) nO4
      (natSyms (w + D) ++ S nO4)) nO5 (natSyms w ++ S nO5) := by
  intro SA SB SC SD SE SF
  have h' : ∀ i : Fin 23, S (.inr i) = [] := hClean
  funext x
  by_cases e1 : x = sBD
  · subst e1; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e2 : x = sBL
  · subst e2; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e3 : x = sBK
  · subst e3; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e4 : x = sBW
  · subst e4; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e5 : x = sUD
  · subst e5; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e6 : x = sUL
  · subst e6; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e7 : x = sUK
  · subst e7; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e8 : x = sUV
  · subst e8; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e9 : x = sZ
  · subst e9; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e10 : x = sY
  · subst e10; simp [SF, SE, SD, SC, SB, SA, h']
  by_cases e11 : x = nO2
  · subst e11; simp [SF, SE, SD, SC, SB, SA]
  by_cases e12 : x = nO3
  · subst e12; simp [SF, SE, SD, SC, SB, SA]
  by_cases e13 : x = nO4
  · subst e13; simp [SF, SE, SD, SC, SB, SA]
  by_cases e14 : x = nO5
  · subst e14; simp [SF, SE, SD, SC, SB, SA]
  simp [SF, SE, SD, SC, SB, SA, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]

end PrefixParamAux

open PrefixParamAux in
/-- **K4-PREFIX, the parameter phase.** `PrefixAux.PrefixParamStmt` holds, with no hypotheses
(exponent `J := 2`, constant `C := 3000`). -/
theorem prefixParam_holds : PrefixAux.PrefixParamStmt := by
  refine ⟨2, 3000, fun _ => ⟨Fin 23, inferInstance, inferInstance, PR, prmProg, inferInstance,
    ⟨(none, ())⟩, closed_prmProg, ?_⟩⟩
  intro q ℓ K w D v a hrest crest S hClean hShape hv hnc hcrest hS0 hS1
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hqw⟩ := id hShape
  have hc : ∀ i : Fin 23, S (.inr i) = [] := hClean
  have hK0 : 0 < K := by omega
  have hy : PrefixAux.pfY ℓ K v ≤ ℓ - 1 := by
    unfold PrefixAux.pfY
    split_ifs with h
    · exact le_rfl
    · have hb : v < layoutB0 ℓ K := by
        by_contra hb
        exact hnc ⟨hK0, by omega, by omega⟩
      omega
  have hm := LayoutPermAux.addrBits_eq ℓ a (by omega) ha
  have hDy : D * PrefixAux.pfY ℓ K v ≤ addrBits a := by
    have : D * PrefixAux.pfY ℓ K v ≤ D * (ℓ - 1) := Nat.mul_le_mul_left D hy
    omega
  have hDm : D ≤ addrBits a := by
    have : D * 1 ≤ D * (ℓ - 1) := Nat.mul_le_mul_left D (by omega)
    omega
  refine runs_congr (runs_mono
    (runs_seq' (runs_prmHdr lP (HDR := nH) (PK := sPK) (TC := sTC) (BD := sBD) (BL := sBL)
        (BK := sBK) (BW := sBW) (O5 := nO5) (by decide) S q ℓ K w a hrest hS0 (hc 0) (hc 1)
        (hc 2) (hc 3) (hc 4) (hc 5))
    (runs_seq' (runs_uBlk _ v D ℓ K crest hcrest (by simp [hS1])
        (by simp [hc]) (by simp)
        (by simp) (by simp)
        (by simp [hc]) (by simp [hc])
        (by simp [hc]) (by simp [hc])
        (by simp [hc]))
    (runs_seq' (runs_zBlk _ v ℓ (by simp)
        (by simp) (by simp [hc])
        (by simp [hc]) (by simp [hc]))
    (runs_seq' (runs_brBlk _ v ℓ K D hK0 hv (by simp)
        (by simp) (by simp)
        (by simp) (by simp)
        (by simp [hc]) (by simp [hc])
        (by simp [hc]) (by simp [hc])
        (by simp [hc]) (by simp [hc])
        (by simp [hc]) (by simp [hc]))
    (runs_seq' (runs_mulBlk _ D (PrefixAux.pfY ℓ K v) (by simp)
        (by simp) (by simp [hc])
        (by simp [hc]) (by simp [hc])
        (by simp [hc]) (by simp [hc]))
    (runs_seq' (runs_wBlk _ D w (by simp)
        (by simp) (by simp [hc])
        (by simp [hc]) (by simp [hc]))
      (runs_clBlk _ D ℓ K v (PrefixAux.pfY ℓ K v) (by simp)
        (by simp) (by simp)
        (by simp) (by simp))))))))
    (fun _ _ => trivial) ?_) ?_
  · exact prmCost_le D ℓ K v w (addrBits a) (PrefixAux.pfY ℓ K v) _ hDm hDy (by omega) (by omega)
      (by omega) (by omega)
  · exact prm_final S hClean D ℓ K w v (PrefixAux.pfY ℓ K v) _ _ (ℓ - (v + 1))

end SubNLogN.Machine.FFT
