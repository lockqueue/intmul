import WP.W9s.Entry
import WP.W7k2.Arith

/-!
# WP.W9s.EntryCost — width and cost bounds for one butterfly entry

With all inputs of width `≤ w`, a butterfly entry costs at most `KB·(w + 1)`
(`bflyCostE_le`), and its output has width `≤ w + 1` (crude, enough for costs).
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Cost constant of one butterfly entry. -/
def KB (CA CS CH : ℕ) : ℕ := 4 * (CA + CS + CH) + 40

theorem natAbs_opZ_le (neg : Bool) (a b : ℤ) : (opZ neg a b).natAbs ≤ a.natAbs + b.natAbs := by
  cases neg
  · exact Int.natAbs_add_le a b
  · exact Int.natAbs_sub_le a b

theorem bitLen_opZ (neg : Bool) {a b : ℤ} {w : ℕ} (ha : bitLen a.natAbs ≤ w)
    (hb : bitLen b.natAbs ≤ w) : bitLen (opZ neg a b).natAbs ≤ w + 1 := by
  rw [bitLen_le_iff] at ha hb ⊢
  have := natAbs_opZ_le neg a b
  rw [pow_succ]
  omega

theorem natAbs_divRoundPow2_le (t : ℤ) : (divRoundPow2 t 1).natAbs ≤ t.natAbs := by
  have h : divRoundPow2 t 1 = (t + 1) / 2 := by simp [divRoundPow2]
  rw [h]
  have h1 := Int.natAbs_eq ((t + 1) / 2)
  have h2 := Int.natAbs_eq t
  omega

theorem bitLen_divRoundPow2_le (t : ℤ) : bitLen (divRoundPow2 t 1).natAbs ≤ bitLen t.natAbs :=
  bitLen_mono (natAbs_divRoundPow2_le t)

theorem entryW_bflyE (neg : Bool) {x g : ℤ × ℤ} {w : ℕ} (hx : EntryW w x) (hg : EntryW w g) :
    EntryW (w + 1) (bflyE neg x g) :=
  ⟨(bitLen_divRoundPow2_le _).trans (bitLen_opZ neg hx.1 hg.1),
    (bitLen_divRoundPow2_le _).trans (bitLen_opZ neg hx.2 hg.2)⟩

theorem length_intSyms' (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

theorem bflyCostE_le (CA CS CH : ℕ) (neg : Bool) (x g : ℤ × ℤ) (w : ℕ) (hx : EntryW w x)
    (hg : EntryW w g) : bflyCostE CA CS CH neg x g ≤ KB CA CS CH * (w + 1) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hg1, hg2⟩ := hg
  have o1 := bitLen_opZ neg hx1 hg1
  have o2 := bitLen_opZ neg hx2 hg2
  have hc : (if neg then CS else CA) ≤ CA + CS := by split <;> omega
  have l1 := length_intSyms' x.1
  have l2 := length_intSyms' g.1
  have l3 : (Sym.sep2 :: (intSyms x.1).reverse).length = bitLen x.1.natAbs + 2 := by
    simp [length_intSyms']
  have l4 : (Sym.sep2 :: (intSyms g.1).reverse).length = bitLen g.1.natAbs + 2 := by
    simp [length_intSyms']
  have p1 : (if neg then CS else CA) * (bitLen x.2.natAbs + bitLen g.2.natAbs + 1) ≤
      (CA + CS) * (2 * w + 1) := Nat.mul_le_mul hc (by omega)
  have p2 : (if neg then CS else CA) * (bitLen x.1.natAbs + bitLen g.1.natAbs + 1) ≤
      (CA + CS) * (2 * w + 1) := Nat.mul_le_mul hc (by omega)
  have p3 : CH * (bitLen (opZ neg x.2 g.2).natAbs + 1) ≤ CH * (w + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have p4 : CH * (bitLen (opZ neg x.1 g.1).natAbs + 1) ≤ CH * (w + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e1 : (CA + CS) * (2 * w + 1) ≤ 2 * ((CA + CS) * (w + 1)) := by
    calc (CA + CS) * (2 * w + 1) ≤ (CA + CS) * (2 * (w + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * ((CA + CS) * (w + 1)) := by ring
  have e2 : CH * (w + 2) ≤ 2 * (CH * (w + 1)) := by
    calc CH * (w + 2) ≤ CH * (2 * (w + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (CH * (w + 1)) := by ring
  have e3 : KB CA CS CH * (w + 1) =
      4 * ((CA + CS) * (w + 1)) + 4 * (CH * (w + 1)) + 40 * (w + 1) := by
    unfold KB
    ring
  unfold bflyCostE
  dsimp only
  by_contra hc
  omega

#assert_std_axioms natAbs_opZ_le bitLen_opZ natAbs_divRoundPow2_le bitLen_divRoundPow2_le
  entryW_bflyE length_intSyms' bflyCostE_le

end WP.W9s
