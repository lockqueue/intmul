import WP.W7k3c.Aff

/-!
# WP.W7k3c.He — one half-erf evaluation (CTr:4826, `halfErfC`)

With the shared values on scratch `0 … 6` (`A`, `2^Bint`, `P·2^Bint`, `2^(S+Be)`, `denZ`,
`denZ²`, `N`), `pHe i o` turns `numX` on `i` into the half-erf value on `o` (18 steps, temporaries
`12 … 14`):
`numZ = A·numX`, `a0 = ⌊numZ·2^Bint / denZ⌉`, `E = series(a0, −numZ², denZ², N)` (W7S_series),
result `⌊E·2^(S+Be) / (P·2^Bint)⌉`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- The half-erf on `numX` (in place on `i`, result on `o`). -/
def pHe (I : CI) (i o : Fin 16) : CP I :=
  (pToInt I i).seq <| (pMul I 0 i 12).seq <| (pMul I 0 i 13).seq <| (pMul I 12 13 14).seq <|
  (pNeg I 14).seq <| (pDrI I 13).seq <| (pMul I 12 1 13).seq <| (pDrI I 12).seq <|
  (pDiv I 13 4 12).seq <| (pDrI I 13).seq <| (pSer I 12 14 5 6 13).seq <| (pDrI I 12).seq <|
  (pDrI I 14).seq <| (pMul I 13 3 12).seq <| (pDrI I 13).seq <| (pDiv I 12 2 o).seq <|
  (pDrI I 12).seq (pDrI I i)

/-- The machine's numerator `a0` of the half-erf series. -/
def heA0 (A Kb : ℤ) (denZ numX : ℕ) : ℤ := IntMul.divRoundRatInt ((A * numX) * Kb) denZ

/-- The machine's series value. -/
def heE (A Kb : ℤ) (denZ denSq N numX : ℕ) : ℤ :=
  (serState (heA0 A Kb denZ numX) (-((A * numX) * (A * numX))) denSq WP.W7k3.SK.erf.f
    WP.W7k3.SK.erf.g N).2

/-- The machine's half-erf value. -/
def heV (A Kb Ksh : ℤ) (Pd denZ denSq N numX : ℕ) : ℤ :=
  IntMul.divRoundRatInt (heE A Kb denZ denSq N numX * Ksh) Pd

/-- Operand widths of one half-erf evaluation. -/
structure HeW (W : ℕ) (A Kb Ksh : ℤ) (Pd denZ denSq N numX : ℕ) : Prop where
  bA : bitLen A.natAbs ≤ W
  bX : bitLen numX ≤ W
  bZ : bitLen (A * numX).natAbs ≤ W
  bKb : bitLen Kb.natAbs ≤ W
  bZK : bitLen ((A * numX) * Kb).natAbs ≤ W
  bD : bitLen denZ ≤ W
  hD : 0 < denZ
  ba0 : bitLen (heA0 A Kb denZ numX).natAbs ≤ W
  bneg : bitLen (-((A * numX) * (A * numX))).natAbs ≤ W
  hD2 : 0 < denSq
  hN : 0 < N
  bN : N ≤ W
  ser : ∃ W', W' ≤ W ∧ IntMul.RecurrenceCallSitesWidthSound W' (heA0 A Kb denZ numX)
    (-((A * numX) * (A * numX))) denSq WP.W7k3.SK.erf.f WP.W7k3.SK.erf.g N
  bE : bitLen (heE A Kb denZ denSq N numX).natAbs ≤ W
  bKsh : bitLen Ksh.natAbs ≤ W
  bEK : bitLen (heE A Kb denZ denSq N numX * Ksh).natAbs ≤ W
  hP : 0 < Pd
  bP : bitLen Pd ≤ W

section

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem sHe {i o : Fin 16} (hi7 : 7 ≤ i.val) (hi : i.val < 12) (ho7 : 7 ≤ o.val) (ho : o.val < 12)
    (hio : i ≠ o) {A Kb Ksh : ℤ} {Pd denZ denSq N numX : ℕ}
    (v0 : V 0 = some (.int A)) (v1 : V 1 = some (.int Kb)) (v2 : V 2 = some (.nat Pd))
    (v3 : V 3 = some (.int Ksh)) (v4 : V 4 = some (.nat denZ)) (v5 : V 5 = some (.nat denSq))
    (v6 : V 6 = some (.nat N)) (vi : V i = some (.nat numX)) (vo : V o = none)
    (v12 : V 12 = none) (v13 : V 13 = none) (v14 : V 14 = none)
    (hw : HeW W A Kb Ksh Pd denZ denSq N numX) :
    HT [] (St S V dv) (pHe I i o)
      (St S (Function.update (Function.update V i none) o
        (some (.int (heV A Kb Ksh Pd denZ denSq N numX)))) dv) (18 * U C W) := by
  obtain ⟨W', hW', hser⟩ := hw.ser
  have hne : ∀ j : Fin 16, j.val < 7 → j ≠ i := fun j hj h => by rw [h] at hj; omega
  have hne' : ∀ j : Fin 16, j.val < 7 → j ≠ o := fun j hj h => by rw [h] at hj; omega
  have hne2 : ∀ j : Fin 16, 12 ≤ j.val → j ≠ i := fun j hj h => by rw [h] at hj; omega
  have hne2' : ∀ j : Fin 16, 12 ≤ j.val → j ≠ o := fun j hj h => by rw [h] at hj; omega
  have i0 := hne 0 (by decide); have i1 := hne 1 (by decide); have i2 := hne 2 (by decide)
  have i3 := hne 3 (by decide); have i4 := hne 4 (by decide); have i5 := hne 5 (by decide)
  have i6 := hne 6 (by decide)
  have i12 := hne2 12 (by decide); have i13 := hne2 13 (by decide); have i14 := hne2 14 (by decide)
  have o2 := hne' 2 (by decide)
  have o12 := hne2' 12 (by decide); have o13 := hne2' 13 (by decide); have o14 := hne2' 14 (by decide)
  have bXi : bitLen ((numX : ℤ)).natAbs ≤ W := by simpa using hw.bX
  unfold pHe
  refine (HT.seq (sToInt (W := W) hI vi) <|
    HT.seq (sMul (W := W) hI W (x := 0) (y := i) (z := 12) (a := A) (b := numX) i0
      (by decide) (Ne.symm i12) (by simp [Ne.symm i0, i0, v0]) (by simp)
      (by simp [Ne.symm i12, i12, v12]) hw.bA bXi le_rfl) <|
    HT.seq (sMul (W := W) hI W (x := 0) (y := i) (z := 13) (a := A) (b := numX) i0
      (by decide) (Ne.symm i13) (by simp [Ne.symm i0, i0, v0]) (by simp [i12, Ne.symm i12])
      (by simp [Ne.symm i13, i13, v13]) hw.bA bXi le_rfl) <|
    HT.seq (sMul (W := W) hI W (x := 12) (y := 13) (z := 14) (a := A * numX) (b := A * numX)
      (by decide) (by decide) (by decide) rfl rfl (by simp [Ne.symm i14, i14, v14])
      hw.bZ hw.bZ le_rfl) <|
    HT.seq (sNeg (W := W) hI (x := 14) (z := A * numX * (A * numX)) rfl) <|
    HT.seq (sDrI (W := W) hI (x := 13) (z := A * numX) rfl hw.bZ) <|
    HT.seq (sMul (W := W) hI W (x := 12) (y := 1) (z := 13) (a := A * numX) (b := Kb)
      (by decide) (by decide) (by decide) rfl (by simp [Ne.symm i1, i1, v1]) rfl
      hw.bZ hw.bKb le_rfl) <|
    HT.seq (sDrI (W := W) hI (x := 12) (z := A * numX) rfl hw.bZ) <|
    HT.seq (sDiv (W := W) hI (x := 13) (y := 4) (z := 12) (n := A * numX * Kb) (d := denZ)
      (by decide) (by decide) (by decide) rfl (by simp [Ne.symm i4, i4, v4]) rfl hw.hD hw.bZK
      hw.bD) <|
    HT.seq (sDrI (W := W) hI (x := 13) (z := A * numX * Kb) rfl hw.bZK) <|
    HT.seq (sSer (W := W) hI (a := 12) (b := 14) (c := 5) (d := 6) (z := 13)
      (a0 := heA0 A Kb denZ numX) (cc := -(A * numX * (A * numX))) (dd := denSq) (n := N)
      (by decide) rfl rfl (by simp [Ne.symm i5, i5, v5]) (by simp [Ne.symm i6, i6, v6]) rfl
      hw.hD2 hw.hN hser hw.bN hW') <|
    HT.seq (sDrI (W := W) hI (x := 12) (z := heA0 A Kb denZ numX) rfl hw.ba0) <|
    HT.seq (sDrI (W := W) hI (x := 14) (z := -(A * numX * (A * numX))) rfl hw.bneg) <|
    HT.seq (sMul (W := W) hI W (x := 13) (y := 3) (z := 12) (a := heE A Kb denZ denSq N numX)
      (b := Ksh) (by decide) (by decide) (by decide) rfl (by simp [Ne.symm i3, i3, v3]) rfl
      hw.bE hw.bKsh le_rfl) <|
    HT.seq (sDrI (W := W) hI (x := 13) (z := heE A Kb denZ denSq N numX) rfl hw.bE) <|
    HT.seq (sDiv (W := W) hI (x := 12) (y := 2) (z := o) (n := heE A Kb denZ denSq N numX * Ksh)
      (d := Pd) (by decide) o12 o2 rfl (by simp [Ne.symm i2, i2, v2])
      (by simp [Ne.symm o12, o12, Ne.symm o13, o13, Ne.symm o14, o14, Ne.symm hio, hio, vo])
      hw.hP hw.bEK hw.bP) <|
    HT.seq (sDrI (W := W) hI (x := 12) (z := heE A Kb denZ denSq N numX * Ksh)
      (by simp [Ne.symm o12, o12]) hw.bEK) <|
    sDrI (W := W) hI (x := i) (z := numX)
      (by simp [hio, Ne.symm hio, i12, Ne.symm i12, i13, Ne.symm i13, i14, Ne.symm i14]) bXi).of_eq
    ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases hj12 : j = 12
  · subst hj12; simp [o12, Ne.symm o12, i12, Ne.symm i12, v12]
  by_cases hj13 : j = 13
  · subst hj13; simp [o13, Ne.symm o13, i13, Ne.symm i13, v13]
  by_cases hj14 : j = 14
  · subst hj14; simp [o14, Ne.symm o14, i14, Ne.symm i14, v14]
  by_cases hjo : j = o
  · rw [hjo]; simp [hio, Ne.symm hio, o12, Ne.symm o12, o13, Ne.symm o13, o14, Ne.symm o14, heV]
  by_cases hji : j = i
  · rw [hji]; simp [hio, Ne.symm hio, i12, Ne.symm i12, i13, Ne.symm i13, i14, Ne.symm i14]
  simp [hj12, hj13, hj14, hjo, hji]

end

#assert_std_axioms sHe

end WP.W7k3c
