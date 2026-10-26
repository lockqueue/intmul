import WP.W7k3c.Vals

/-!
# WP.W7k3c.Mac — small macros with clean result values

`pMulN` (natural product, operands kept), `pPow2` (`2^k`), `pDbl` (doubling), and `sAff'` (an
affine constant with its value given in a chosen form).
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- `z := a·b` for naturals `a`, `b` on `x`, `y` (kept). -/
def pMulN (I : CI) (x y z : Fin 16) : CP I :=
  (pToInt I x).seq <| (pToInt I y).seq <| (pMul I x y z).seq <| (pToNat I z).seq <|
  (pToNat I x).seq (pToNat I y)

/-- `j := 2^k` for `k` on `c`. -/
def pPow2 (I : CI) (j c : Fin 16) : CP I := (pPush I j 1).seq (pShl I j c)

/-- `x := 2·x` (temporary `t`). -/
def pDbl (I : CI) (x t : Fin 16) : CP I := (pPush I t 1).seq <| (pShl I x t).seq (pDrN I t)

section

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem sAff' {pw ps : ℕ} {r0 r1 : List Sym} (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1) (α β γ : ℕ) (d : Fin 16)
    (hd : d.val < 12) (hVd : V d = none) (h12 : V 12 = none) (h13 : V 13 = none)
    (h14 : V 14 = none) (h15 : V 15 = none)
    (hW : α * pw + β * ps + γ + α + β + pw + ps < 2 ^ W) (v : ℕ) (hv : α * pw + β * ps + γ = v) :
    HT [] (St S V dv) (pAff I α β γ d) (St S (Function.update V d (some (.nat v))) dv)
      (23 * U C W) := by
  subst hv
  exact sAff hI h0 hr0 h1 hr1 α β γ d hd hVd h12 h13 h14 h15 hW

theorem sMulN {x y z : Fin 16} {a b : ℕ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hx : V x = some (.nat a)) (hy : V y = some (.nat b)) (hz : V z = none)
    (ha : bitLen a ≤ W) (hb : bitLen b ≤ W) :
    HT [] (St S V dv) (pMulN I x y z) (St S (Function.update V z (some (.nat (a * b)))) dv)
      (6 * U C W) := by
  have ha' : bitLen ((a : ℤ)).natAbs ≤ W := by simpa using ha
  have hb' : bitLen ((b : ℤ)).natAbs ≤ W := by simpa using hb
  unfold pMulN
  refine (HT.seq (sToInt (W := W) hI hx) <|
    HT.seq (sToInt (W := W) hI (j := y) (a := b) (by rw [Function.update_of_ne (Ne.symm h1), hy])) <|
    HT.seq (sMul (W := W) hI W (x := x) (y := y) (z := z) (a := (a : ℤ)) (b := (b : ℤ)) h1 h2 h3
      (by rw [Function.update_of_ne h1, Function.update_self])
      (by rw [Function.update_self])
      (by rw [Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h2), hz])
      ha' hb' le_rfl) <|
    HT.seq (sToNat (W := W) hI (j := z) (z := (a : ℤ) * (b : ℤ)) (by rw [Function.update_self])
      (by positivity)) <|
    HT.seq (sToNat (W := W) hI (j := x) (z := (a : ℤ))
      (by rw [Function.update_of_ne h2, Function.update_of_ne h2, Function.update_of_ne h1,
        Function.update_self])
      (by positivity)) <|
    sToNat (W := W) hI (j := y) (z := (b : ℤ))
      (by rw [Function.update_of_ne (Ne.symm h1), Function.update_of_ne h3, Function.update_of_ne h3,
        Function.update_self])
      (by positivity)).of_eq ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases hjz : j = z
  · subst hjz
    simp [Ne.symm h2, Ne.symm h3, toNat_natCast_mul]
  by_cases hjx : j = x
  · subst hjx
    simp [h1, h2, hx]
  by_cases hjy : j = y
  · subst hjy
    simp [h3, hy]
  simp [hjz, hjx, hjy]

theorem sPow2 {j c : Fin 16} {k : ℕ} (h : j ≠ c) (hj : V j = none) (hc : V c = some (.nat k))
    (hk : k ≤ W) (hW : 1 ≤ W) :
    HT [] (St S V dv) (pPow2 I j c) (St S (Function.update V j (some (.nat (2 ^ k)))) dv)
      (2 * U C W) := by
  unfold pPow2
  refine (HT.seq (sPush (W := W) hI j 1 hj (le_trans (bitLen_le_self 1) hW)) <|
    sShl (W := W) hI (x := j) (c := c) (a := 1) (k := k) h (by rw [Function.update_self])
      (by rw [Function.update_of_ne (Ne.symm h), hc]) hk).of_eq ?_ (by omega)
  rw [Function.update_idem, one_mul]

theorem sDbl {x t : Fin 16} {a : ℕ} (h : x ≠ t) (hx : V x = some (.nat a)) (ht : V t = none)
    (hW : 1 ≤ W) :
    HT [] (St S V dv) (pDbl I x t) (St S (Function.update V x (some (.nat (2 * a)))) dv)
      (3 * U C W) := by
  have b1 : bitLen 1 ≤ W := le_trans (bitLen_le_self 1) hW
  unfold pDbl
  refine (HT.seq (sPush (W := W) hI t 1 ht b1) <|
    HT.seq (sShl (W := W) hI (x := x) (c := t) (a := a) (k := 1) h
      (by rw [Function.update_of_ne h, hx]) (by rw [Function.update_self]) hW) <|
    sDrN (W := W) hI (x := t) (a := 1)
      (by rw [Function.update_of_ne (Ne.symm h), Function.update_self]) b1).of_eq ?_ (by omega)
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases hjt : j = t
  · subst hjt
    simp [Ne.symm h, ht]
  by_cases hjx : j = x
  · subst hjx
    simp [h, mul_comm]
  simp [hjt, hjx]

end

#assert_std_axioms sAff' sMulN sPow2 sDbl

end WP.W7k3c
