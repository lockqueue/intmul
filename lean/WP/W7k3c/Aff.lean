import WP.W7k3c.Steps2

/-!
# WP.W7k3c.Aff — affine constants `α·p_work + β·pSub + γ`

Every precision parameter of the c0/c1 evaluator (CTr:5054-5076) is affine in `p_work`, `pSub`
(`B = pSub+2`, `S = 16p+pSub+12`, `N = 136p+pSub+13`, `Bint = 352p+3pSub+40`, …). `pAff α β γ d`
computes one into scratch stack `d < 12` with two W5 products, using scratch `12 … 15` as
temporaries (restored to empty).
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- `d := α·p_work + β·pSub + γ` (temporaries `12 … 15`). -/
def pAff (I : CI) (α β γ : ℕ) (d : Fin 16) : CP I :=
  (pPush I 12 α).seq <| (pToInt I 12).seq <| (pCp I (.inl 0) 13).seq <| (pToInt I 13).seq <|
  (pMul I 12 13 14).seq <| (pToNat I 14).seq <| (pDrI I 12).seq <| (pDrI I 13).seq <|
  (pPush I 12 β).seq <| (pToInt I 12).seq <| (pCp I (.inl 1) 13).seq <| (pToInt I 13).seq <|
  (pMul I 12 13 15).seq <| (pToNat I 15).seq <| (pDrI I 12).seq <| (pDrI I 13).seq <|
  (pAdN I 14 15 12).seq <| (pDrN I 14).seq <| (pDrN I 15).seq <| (pPush I 13 γ).seq <|
  (pAdN I 12 13 d).seq <| (pDrN I 12).seq (pDrN I 13)

theorem lt_pow_bitLen {n W : ℕ} (h : n < 2 ^ W) : bitLen n ≤ W := bitLen_le_of_lt h

section

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem sAff {pw ps : ℕ} {r0 r1 : List Sym} (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1) (α β γ : ℕ) (d : Fin 16)
    (hd : d.val < 12) (hVd : V d = none) (h12 : V 12 = none) (h13 : V 13 = none)
    (h14 : V 14 = none) (h15 : V 15 = none)
    (hW : α * pw + β * ps + γ + α + β + pw + ps < 2 ^ W) :
    HT [] (St S V dv) (pAff I α β γ d)
      (St S (Function.update V d (some (.nat (α * pw + β * ps + γ)))) dv) (23 * U C W) := by
  have hd12 : d ≠ 12 := Fin.ne_of_val_ne (by simp; omega)
  have hd13 : d ≠ 13 := Fin.ne_of_val_ne (by simp; omega)
  have hd14 : d ≠ 14 := Fin.ne_of_val_ne (by simp; omega)
  have hd15 : d ≠ 15 := Fin.ne_of_val_ne (by simp; omega)
  have bα : bitLen α ≤ W := lt_pow_bitLen (by omega)
  have bβ : bitLen β ≤ W := lt_pow_bitLen (by omega)
  have bγ : bitLen γ ≤ W := lt_pow_bitLen (by omega)
  have bpw : bitLen pw ≤ W := lt_pow_bitLen (by omega)
  have bps : bitLen ps ≤ W := lt_pow_bitLen (by omega)
  have hαp : α * pw ≤ α * pw + β * ps + γ + α + β + pw + ps := by omega
  have hβp : β * ps ≤ α * pw + β * ps + γ + α + β + pw + ps := by omega
  have bαp : bitLen (α * pw) ≤ W := lt_pow_bitLen (by omega)
  have bβp : bitLen (β * ps) ≤ W := lt_pow_bitLen (by omega)
  have bs : bitLen (α * pw + β * ps) ≤ W := lt_pow_bitLen (by omega)
  have e1 : ((α : ℤ) * (pw : ℤ)).toNat = α * pw := toNat_natCast_mul α pw
  have e2 : ((β : ℤ) * (ps : ℤ)).toNat = β * ps := toNat_natCast_mul β ps
  have i1 : ((α : ℤ) * (pw : ℤ)).natAbs = α * pw := by rw [← Nat.cast_mul, Int.natAbs_natCast]
  have i2 : ((β : ℤ) * (ps : ℤ)).natAbs = β * ps := by rw [← Nat.cast_mul, Int.natAbs_natCast]
  unfold pAff
  refine (HT.seq (sPush (W := W) hI 12 α h12 bα) <| HT.seq (sToInt (W := W) hI rfl) <|
    HT.seq (sCp (W := W) hI (.inl 0) 13 (by simp) h0 hr0 (by simp [h13]) bpw) <|
    HT.seq (sToInt (W := W) hI rfl) <|
    HT.seq (sMul (W := W) hI W (x := 12) (y := 13) (z := 14) (by decide) (by decide) (by decide)
      rfl rfl (by simp [h14]) (by simpa using bα) (by simpa using bpw) le_rfl) <|
    HT.seq (sToNat (W := W) hI rfl (by positivity)) <|
    HT.seq (sDrI (W := W) hI (x := 12) rfl (by simpa using bα)) <|
    HT.seq (sDrI (W := W) hI (x := 13) rfl (by simpa using bpw)) <|
    HT.seq (sPush (W := W) hI 12 β rfl bβ) <| HT.seq (sToInt (W := W) hI rfl) <|
    HT.seq (sCp (W := W) hI (.inl 1) 13 (by simp) h1 hr1 rfl bps) <|
    HT.seq (sToInt (W := W) hI rfl) <|
    HT.seq (sMul (W := W) hI W (x := 12) (y := 13) (z := 15) (by decide) (by decide) (by decide)
      rfl rfl (by simp [h15]) (by simpa using bβ) (by simpa using bps) le_rfl) <|
    HT.seq (sToNat (W := W) hI rfl (by positivity)) <|
    HT.seq (sDrI (W := W) hI (x := 12) rfl (by simpa using bβ)) <|
    HT.seq (sDrI (W := W) hI (x := 13) rfl (by simpa using bps)) <|
    HT.seq (sAdN (W := W) hI (x := 14) (y := 15) (z := 12) (by decide) (by decide) (by decide) rfl rfl rfl
      (by rw [e1]; exact bαp) (by rw [e2]; exact bβp)) <|
    HT.seq (sDrN (W := W) hI (x := 14) rfl (by rw [e1]; exact bαp)) <|
    HT.seq (sDrN (W := W) hI (x := 15) rfl (by rw [e2]; exact bβp)) <|
    HT.seq (sPush (W := W) hI 13 γ rfl bγ) <|
    HT.seq (sAdN (W := W) hI (x := 12) (y := 13) (z := d) (by decide) (Ne.symm hd12) (Ne.symm hd13)
      rfl rfl (by simp [Function.update_apply, hd12, hd13, hd14, hd15, hVd])
      (by rw [e1, e2]; exact bs) bγ) <|
    HT.seq (sDrN (W := W) hI (x := 12) (a := ((α : ℤ) * (pw : ℤ)).toNat + ((β : ℤ) * (ps : ℤ)).toNat)
      (by simp [Ne.symm hd12]) (by rw [e1, e2]; exact bs)) <|
    sDrN (W := W) hI (x := 13) (a := γ) (by simp [Ne.symm hd13]) bγ).of_eq ?_
      (by by_contra hc; omega)
  congr 1
  rw [e1, e2]
  funext j
  simp only [Function.update_apply]
  by_cases hj12 : j = 12
  · subst hj12; simp [hd12, Ne.symm hd12, h12]
  by_cases hj13 : j = 13
  · subst hj13; simp [hd13, Ne.symm hd13, h13]
  by_cases hj14 : j = 14
  · subst hj14; simp [hd14, Ne.symm hd14, h14]
  by_cases hj15 : j = 15
  · subst hj15; simp [hd15, Ne.symm hd15, h15]
  simp [hj12, hj13, hj14, hj15]

end

#assert_std_axioms lt_pow_bitLen sAff

end WP.W7k3c
