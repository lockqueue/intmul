/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddCtrK
import WP.W0m.Sched

/-!
# C-core leaf 9 (Lemma A.9 row addition): the cost of the counter kernel (`CCore/LeafRowAddCtrCost.lean`)

Pure natural-number arithmetic about the explicit cost expressions `costK/F/R/Pow/N3/All/Clr` of
`CCore/LeafRowAddCtrK.lean`. Main result `costAll_le`: there is one constant `Cc` such that for
every call `t` with `1 ≤ k`, `1 ≤ K`, `j0 + e ≤ D` and distinct slots `p₁, p₂ < m`,
`costAll t p₁ p₂ + costClr (ctrVals t p₁ p₂) ≤ Cc · (ctrB t + 1)^3`, where
`ctrB t = |t.hdr| + K·D`.

Ingredients (`X = ctrB t + 1`): every header field has bit length `≤ |t.hdr| ≤ X`;
`f = m^(k-1) ≤ e ≤ D ≤ K·D`; `k < e`; the slots `lo < mid < hi` are `< m`, so the `powMulN`
exponents `K·f·(mid-lo-1)`, `K·f·(hi-mid-1)`, `K·(D - (f·(hi+1) + j0))` are `≤ K·D ≤ X`;
`bitLen m ≤ 20`. Each cost is bounded by a numeral times `X^3` (`mulCost`, `mulConstCost`,
`powCost` of `AppC/C5StreamArith.lean` are at most cubic in these sizes).
-/

namespace SubNLogN.Machine.CCore.LeafRowAddCtrCostAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.CCore.LeafRowAddAux

/-! ## Generic bounds -/

theorem bitLen_pow_le' (a : ℕ) : ∀ n, bitLen (a ^ n) ≤ n * bitLen a + 1
  | 0 => by simpa using WP.W0m.bitLen_le_self 1
  | n + 1 => by
    have ih := bitLen_pow_le' a n
    have hm := bitLen_mul_le' (a ^ n) a
    rw [pow_succ, Nat.succ_mul]
    omega

theorem bitLen_mn_le : bitLen mn ≤ 20 := bitLen_le_of_lt' (by norm_num [mn, tripleM])

theorem bitLen_lt_mn {c : ℕ} (h : c ≤ mn) : bitLen c ≤ 20 :=
  bitLen_le_of_lt' (lt_of_le_of_lt h (by norm_num [mn, tripleM]))

theorem X_le_X3 {X : ℕ} (hX : 1 ≤ X) : X ≤ X ^ 3 := by
  calc X = X ^ 1 := (pow_one X).symm
    _ ≤ X ^ 3 := Nat.pow_le_pow_right hX (by norm_num)

theorem one_le_X3 {X : ℕ} (hX : 1 ≤ X) : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX

/-- `mulCost` from linear bit-length bounds. -/
theorem mulCost_le {a b X ca cb : ℕ} (hX : 1 ≤ X) (ha : bitLen a ≤ ca * X)
    (hb : bitLen b ≤ cb * X) : mulCost a b ≤ 100 * (ca + 1) * (ca + cb + 2) * X ^ 3 := by
  unfold mulCost
  have h1 : bitLen a + 1 ≤ (ca + 1) * X := by
    have : (ca + 1) * X = ca * X + X := by ring
    omega
  have h2 : bitLen a + bitLen b + 2 ≤ (ca + cb + 2) * X := by
    have : (ca + cb + 2) * X = ca * X + cb * X + 2 * X := by ring
    omega
  have h3 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX (by norm_num)
  calc 100 * (bitLen a + 1) * (bitLen a + bitLen b + 2)
      ≤ 100 * ((ca + 1) * X) * ((ca + cb + 2) * X) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    _ = 100 * (ca + 1) * (ca + cb + 2) * X ^ 2 := by ring
    _ ≤ 100 * (ca + 1) * (ca + cb + 2) * X ^ 3 := Nat.mul_le_mul_left _ h3

/-- `mulConstCost` from linear bit-length bounds. -/
theorem mulConstCost_le {a c X ca cc : ℕ} (hX : 1 ≤ X) (ha : bitLen a ≤ ca * X)
    (hc : bitLen c ≤ cc * X) :
    mulConstCost a c ≤ (100 * (ca + 1) * (ca + cc + 2) + 14 * ca + 12 * cc + 18) * X ^ 3 := by
  unfold mulConstCost
  have h1 := mulCost_le hX ha hc
  have h2 := bitLen_mul_le' a c
  have h3 := X_le_X3 hX
  have h4 := one_le_X3 hX
  have h5 : ca * X ≤ ca * X ^ 3 := Nat.mul_le_mul_left _ h3
  have h6 : cc * X ≤ cc * X ^ 3 := Nat.mul_le_mul_left _ h3
  have e : (100 * (ca + 1) * (ca + cc + 2) + 14 * ca + 12 * cc + 18) * X ^ 3 =
      100 * (ca + 1) * (ca + cc + 2) * X ^ 3 + 14 * (ca * X ^ 3) + 12 * (cc * X ^ 3) +
        18 * X ^ 3 := by ring
  omega

/-- `powCost 2 a n` is cubic. -/
theorem powCost_two_le {a n X : ℕ} (hX : 1 ≤ X) (ha : bitLen a ≤ X) (hn : n ≤ X) :
    powCost 2 a n ≤ 14400 * X ^ 3 := by
  unfold powCost
  have h1 := bitLen_mul_two_pow_le a n
  have h2 : bitLen 2 ≤ 2 := WP.W0m.bitLen_le_self 2
  have h3 : bitLen (a * 2 ^ n) + bitLen 2 + 2 ≤ 6 * X := by omega
  have h4 : n + 1 ≤ 2 * X := by omega
  calc (n + 1) * (200 * (bitLen (a * 2 ^ n) + bitLen 2 + 2) ^ 2)
      ≤ (2 * X) * (200 * (6 * X) ^ 2) :=
        Nat.mul_le_mul h4 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 2))
    _ = 14400 * X ^ 3 := by ring

/-- `powCost m 1 (k - 1)` is cubic in `k`. -/
theorem powCost_mn_le {k X : ℕ} (hX : 1 ≤ X) (hk : k ≤ X) :
    powCost mn 1 (k - 1) ≤ 369800 * X ^ 3 := by
  unfold powCost
  have hb := bitLen_mn_le
  have h1 : bitLen (1 * mn ^ (k - 1)) ≤ (k - 1) * bitLen mn + 1 := by
    rw [Nat.one_mul]; exact bitLen_pow_le' _ _
  have h2 : (k - 1) * bitLen mn ≤ (k - 1) * 20 := Nat.mul_le_mul_left _ hb
  have h3 : bitLen (1 * mn ^ (k - 1)) + bitLen mn + 2 ≤ 43 * X := by omega
  have h4 : k - 1 + 1 ≤ X := by omega
  calc (k - 1 + 1) * (200 * (bitLen (1 * mn ^ (k - 1)) + bitLen mn + 2) ^ 2)
      ≤ X * (200 * (43 * X) ^ 2) :=
        Nat.mul_le_mul h4 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 2))
    _ = 369800 * X ^ 3 := by ring

end SubNLogN.Machine.CCore.LeafRowAddCtrCostAux

namespace SubNLogN.Machine.CCore.LeafRowAddCtrCostAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.CCore.LeafRowAddAux

/-! ## The cost of each counter program -/

theorem costK_le {t : CCoreRT} {X : ℕ} (hX : 1 ≤ X) (hH : t.hdr.length ≤ X) :
    costK t ≤ 28 * X ^ 3 := by
  unfold costK
  have := X_le_X3 hX
  have := one_le_X3 hX
  omega

theorem costF_le {t : CCoreRT} {X : ℕ} (hX : 1 ≤ X) (hH : t.hdr.length ≤ X) (hk : t.k ≤ X)
    (hbk : bitLen t.k ≤ X) : costF t ≤ 370000 * X ^ 3 := by
  unfold costF
  have h1 : bitLen 1 ≤ 1 := WP.W0m.bitLen_le_self 1
  have h2 : bitLen (t.k - 1) ≤ bitLen t.k := bitLen_mono'' (Nat.sub_le _ _)
  have h3 := powCost_mn_le hX hk
  have h4 := X_le_X3 hX
  have h5 := one_le_X3 hX
  omega

theorem costR_le {t : CCoreRT} {X : ℕ} (hX : 1 ≤ X) (hH : t.hdr.length ≤ X)
    (hP : bitLen t.P ≤ X) (hΔ : bitLen t.Δ ≤ X) (hr : bitLen t.r ≤ X) :
    costR t ≤ 5000 * X ^ 3 := by
  unfold costR
  have h3 : bitLen 3 ≤ 3 := WP.W0m.bitLen_le_self 3
  have e1 := bitLen_add_le' t.Δ t.Δ
  have e2 := bitLen_add_le' t.P (t.Δ + t.Δ)
  have e3 := bitLen_add_le' (t.P + (t.Δ + t.Δ)) 3
  have hm := mulCost_le (a := t.r) (b := t.P + (t.Δ + t.Δ) + 3) (ca := 1) (cb := 9) hX
    (by omega) (by omega)
  have h4 := X_le_X3 hX
  have h5 := one_le_X3 hX
  linarith

theorem costPow_le {cst Kv fv X : ℕ} (hX : 1 ≤ X) (hK : bitLen Kv ≤ X) (hf : bitLen fv ≤ X)
    (hc : bitLen cst ≤ 20) (hn : Kv * fv * cst ≤ X) : costPow cst Kv fv ≤ 25000 * X ^ 3 := by
  unfold costPow
  have h1 : bitLen 1 ≤ 1 := WP.W0m.bitLen_le_self 1
  have hKf := bitLen_mul_le' Kv fv
  have hm1 := mulCost_le (a := Kv) (b := fv) (ca := 1) (cb := 1) hX (by omega) (by omega)
  have hm2 := mulConstCost_le (a := Kv * fv) (c := cst) (ca := 2) (cc := 20) hX (by omega)
    (by omega)
  have hp := powCost_two_le (a := 1) (n := Kv * fv * cst) hX (by omega) hn
  have hbn : bitLen (Kv * fv * cst) ≤ X := le_trans (WP.W0m.bitLen_le_self _) hn
  have h4 := X_le_X3 hX
  have h5 := one_le_X3 hX
  omega

theorem costN3_le {t : CCoreRT} {hi1 Kv fv X : ℕ} (hX : 1 ≤ X) (hH : t.hdr.length ≤ X)
    (hf : bitLen fv ≤ X) (hhi : bitLen hi1 ≤ 20) (hK : bitLen Kv ≤ X) (hj0 : bitLen t.j0 ≤ X)
    (hD : bitLen t.D ≤ X) (hS : bitLen t.S ≤ X) (hx1 : bitLen (fv * hi1) ≤ X)
    (hx2 : bitLen (fv * hi1 + t.j0) ≤ X) (hx3 : bitLen (t.D - (fv * hi1 + t.j0)) ≤ X)
    (hn3 : Kv * (t.D - (fv * hi1 + t.j0)) ≤ X) : costN3 t hi1 Kv fv ≤ 25000 * X ^ 3 := by
  unfold costN3
  have hm1 := mulConstCost_le (a := fv) (c := hi1) (ca := 1) (cc := 20) hX (by omega) (by omega)
  have hm2 := mulCost_le (a := Kv) (b := t.D - (fv * hi1 + t.j0)) (ca := 1) (cb := 1) hX
    (by omega) (by omega)
  have hp := powCost_two_le (a := t.S) (n := Kv * (t.D - (fv * hi1 + t.j0))) hX hS hn3
  have hbn : bitLen (Kv * (t.D - (fv * hi1 + t.j0))) ≤ X :=
    le_trans (WP.W0m.bitLen_le_self _) hn3
  have h4 := X_le_X3 hX
  have h5 := one_le_X3 hX
  linarith

theorem costClr_le {vals : Fin 7 → ℕ} {X : ℕ} (hX : 1 ≤ X) (h0 : bitLen (vals 0) ≤ 12 * X)
    (h1 : bitLen (vals 1) ≤ 12 * X) (h2 : bitLen (vals 2) ≤ 12 * X)
    (h3 : bitLen (vals 3) ≤ 12 * X) (h4 : bitLen (vals 4) ≤ 12 * X)
    (h5 : bitLen (vals 5) ≤ 12 * X) (h6 : bitLen (vals 6) ≤ 12 * X) :
    costClr vals ≤ 200 * X ^ 3 := by
  unfold costClr
  have h7 := X_le_X3 hX
  omega

/-! ## Slots -/

theorem hiS_lt' {p₁ p₂ : ℕ} (h1 : p₁ < mn) (h2 : p₂ < mn) : hiS p₁ p₂ < mn := by
  have h3 := (thirdSlot_ne p₁ p₂).2.2
  have hm : 3 ≤ mn := by norm_num [mn, tripleM]
  unfold hiS
  exact max_lt (max_lt h1 h2) (by omega)

theorem bitLen_two_pow_le (n : ℕ) : bitLen (2 ^ n) ≤ n + 1 := by
  have h := bitLen_mul_two_pow_le 1 n
  have h1 : bitLen 1 ≤ 1 := WP.W0m.bitLen_le_self 1
  rw [Nat.one_mul] at h
  omega

end SubNLogN.Machine.CCore.LeafRowAddCtrCostAux

namespace SubNLogN.Machine.CCore.LeafRowAddCtrCostAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.CCore.LeafRowAddAux

/-! ## The whole counter kernel -/

/-- **Cost of the counter kernel** (set-up `ctrAll` and clean-up `ctrClr`): at most
`Cc · (ctrB t + 1)^3` with one constant `Cc` (here `500000`), for every call with `1 ≤ k`,
`1 ≤ K`, `j0 + e ≤ D` and distinct slots `p₁, p₂ < m`. -/
theorem costAll_le : ∃ Cc : ℕ, ∀ (t : CCoreRT) (p₁ p₂ : ℕ), p₁ < mn → p₂ < mn → p₁ ≠ p₂ →
    1 ≤ t.k → 1 ≤ t.K → t.j0 + t.e ≤ t.D →
    costAll t p₁ p₂ + costClr (ctrVals t p₁ p₂) ≤ Cc * (ctrB t + 1) ^ 3 := by
  refine ⟨500000, fun t p₁ p₂ h1 h2 hp hk hK hfit => ?_⟩
  unfold costAll
  have hB : ctrB t = t.hdr.length + t.K * t.D := rfl
  set X := ctrB t + 1 with hXdef
  set f := mn ^ (t.k - 1) with hfdef
  set c1 := midS p₁ p₂ - loS p₁ p₂ - 1 with hc1
  set c2 := hiS p₁ p₂ - midS p₁ p₂ - 1 with hc2
  set hi1 := hiS p₁ p₂ + 1 with hhi1
  have hX : 1 ≤ X := by omega
  have hH : t.hdr.length ≤ X := by omega
  have hKD : t.K * t.D ≤ X := by omega
  -- header fields
  have bP : bitLen t.P ≤ X := le_trans (bitLen_le_hdr (hfs t) 0 (by simp [hfs])) hH
  have br : bitLen t.r ≤ X := le_trans (bitLen_le_hdr (hfs t) 2 (by simp [hfs])) hH
  have bΔ : bitLen t.Δ ≤ X := le_trans (bitLen_le_hdr (hfs t) 3 (by simp [hfs])) hH
  have bK : bitLen t.K ≤ X := le_trans (bitLen_le_hdr (hfs t) 6 (by simp [hfs])) hH
  have bD : bitLen t.D ≤ X := le_trans (bitLen_le_hdr (hfs t) 7 (by simp [hfs])) hH
  have bS : bitLen t.S ≤ X := le_trans (bitLen_le_hdr (hfs t) 8 (by simp [hfs])) hH
  have bj0 : bitLen t.j0 ≤ X := le_trans (bitLen_le_hdr (hfs t) 9 (by simp [hfs])) hH
  have bk : bitLen t.k ≤ X := le_trans (bitLen_le_hdr (hfs t) 10 (by simp [hfs])) hH
  have bρ : bitLen t.ρ ≤ X := le_trans (bitLen_le_hdr (hfs t) 11 (by simp [hfs])) hH
  -- `f = m^(k-1)`, `e`, `D`
  have he : t.e = mn ^ t.k := rfl
  have hmf : mn * f = t.e := by rw [hfdef, he, ← pow_succ', Nat.sub_add_cancel hk]
  have hmn1 : 1 ≤ mn := by norm_num [mn, tripleM]
  have hfe : f ≤ t.e := by rw [← hmf]; exact Nat.le_mul_of_pos_left _ hmn1
  have heD : t.e ≤ t.D := by omega
  have hDKD : t.D ≤ t.K * t.D := Nat.le_mul_of_pos_left _ hK
  have hke : t.k < t.e := by rw [he]; exact Nat.lt_pow_self (by norm_num [mn, tripleM])
  have hkX : t.k ≤ X := by omega
  have hbf : bitLen f ≤ X := le_trans (bitLen_mono'' (by omega : f ≤ t.D)) bD
  -- slots
  obtain ⟨hlm, hmh, -, -⟩ := slots_sorted hp
  have hhi := hiS_lt' h1 h2
  have hc1m : c1 ≤ mn := by omega
  have hc2m : c2 ≤ mn := by omega
  have hhi1m : hi1 ≤ mn := by omega
  have hfc1 : f * c1 ≤ t.e := by
    rw [← hmf, Nat.mul_comm mn f]; exact Nat.mul_le_mul_left _ hc1m
  have hfc2 : f * c2 ≤ t.e := by
    rw [← hmf, Nat.mul_comm mn f]; exact Nat.mul_le_mul_left _ hc2m
  have hfhi : f * hi1 ≤ t.e := by
    rw [← hmf, Nat.mul_comm mn f]; exact Nat.mul_le_mul_left _ hhi1m
  have hn1 : t.K * f * c1 ≤ X := by
    rw [Nat.mul_assoc]; exact le_trans (Nat.mul_le_mul_left _ (by omega : f * c1 ≤ t.D)) hKD
  have hn2 : t.K * f * c2 ≤ X := by
    rw [Nat.mul_assoc]; exact le_trans (Nat.mul_le_mul_left _ (by omega : f * c2 ≤ t.D)) hKD
  have hx : f * hi1 + t.j0 ≤ t.D := by omega
  have hn3 : t.K * (t.D - (f * hi1 + t.j0)) ≤ X :=
    le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hKD
  have bx1 : bitLen (f * hi1) ≤ X := le_trans (bitLen_mono'' (by omega)) bD
  have bx2 : bitLen (f * hi1 + t.j0) ≤ X := le_trans (bitLen_mono'' hx) bD
  have bx3 : bitLen (t.D - (f * hi1 + t.j0)) ≤ X := le_trans (bitLen_mono'' (Nat.sub_le _ _)) bD
  -- the seven programs and the clean-up
  have cK := costK_le (t := t) hX hH
  have cF := costF_le hX hH hkX bk
  have cR := costR_le hX hH bP bΔ br
  have cP1 := costPow_le (cst := c1) (Kv := t.K) (fv := f) hX bK hbf (bitLen_lt_mn hc1m) hn1
  have cP2 := costPow_le (cst := c2) (Kv := t.K) (fv := f) hX bK hbf (bitLen_lt_mn hc2m) hn2
  have cN := costN3_le (t := t) (hi1 := hi1) (Kv := t.K) (fv := f) hX hH hbf
    (bitLen_lt_mn hhi1m) bK bj0 bD bS bx1 bx2 bx3 hn3
  have cC := costClr_le (vals := ctrVals t p₁ p₂) hX
    (by show bitLen t.K ≤ 12 * X; omega)
    (by show bitLen t.ρ ≤ 12 * X; omega)
    (by show bitLen f ≤ 12 * X; omega)
    (by show bitLen (2 ^ (t.K * f * c1)) ≤ 12 * X
        have := bitLen_two_pow_le (t.K * f * c1); omega)
    (by show bitLen (2 ^ (t.K * f * c2)) ≤ 12 * X
        have := bitLen_two_pow_le (t.K * f * c2); omega)
    (by show bitLen (t.S * 2 ^ (t.K * (t.D - (f * hi1 + t.j0)))) ≤ 12 * X
        have := bitLen_mul_two_pow_le t.S (t.K * (t.D - (f * hi1 + t.j0))); omega)
    (by show bitLen (2 * t.r * t.wg) ≤ 12 * X
        have q1 := bitLen_mul_le' (2 * t.r) t.wg
        have q2 := bitLen_mul_le' 2 t.r
        have q3 : bitLen 2 ≤ 2 := WP.W0m.bitLen_le_self 2
        have q4 : bitLen t.wg ≤ bitLen (t.P + 2 * t.Δ) + bitLen 3 + 1 :=
          bitLen_add_le' (t.P + 2 * t.Δ) 3
        have q5 := bitLen_add_le' t.P (2 * t.Δ)
        have q6 := bitLen_mul_le' 2 t.Δ
        have q7 : bitLen 3 ≤ 3 := WP.W0m.bitLen_le_self 3
        omega)
  omega

end SubNLogN.Machine.CCore.LeafRowAddCtrCostAux
