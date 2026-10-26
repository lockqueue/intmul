import WP.W9sq.Main3
import WP.W3b.AddSub
import WP.W3b.Sign

/-!
# WP.W9sq.Theorem — `W9_square` from the frozen machine contracts

* `W9_square_core`: from `W5_mulAt Mul` and the W3 contracts the kernel calls that are not proved
  instances (`dropNat`, `addNat`, `shrVar`, `shlVar`, `addInt`, `subInt`, `attachSign`); `copyNat`,
  `incNat`, `decNat` are the proved instances `w3_copyNat`, `w3_incNat`, `w3_decNat`.
* `W9_square_holds : ∀ Mul, W5_mulAt Mul → W3_all → W9_square Mul` (projection of `W3_all`) and
  the binding shape of `W9comp.W9StageThms.square` (`… → W4_all → W6a_all → …`, unused).
* `W9_square_holds_min`: only the open W3 contracts (`addInt`, `subInt`, `attachSign` from
  `WP.W3b`).

The program is `(sqProg J (initK J)).mapStk eH` over `BLoc 24`; constant `1000·(ΣC + 1)`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

theorem SqI.finite (J : SqI) : Finite J.Reg := by
  haveI := J.mul.fin; haveI := J.cp.fin; haveI := J.dr.fin; haveI := J.sb.fin
  haveI := J.ad.fin; haveI := J.an.fin; haveI := J.sr.fin; haveI := J.sl.fin
  haveI := J.inc.fin; haveI := J.dec.fin; haveI := J.atT.fin; haveI := J.atF.fin
  infer_instance

theorem SqI.nonempty (J : SqI) : Nonempty J.Reg := by
  haveI := J.mul.ne; haveI := J.cp.ne; haveI := J.dr.ne; haveI := J.sb.ne
  haveI := J.ad.ne; haveI := J.an.ne; haveI := J.sr.ne; haveI := J.sl.ne
  haveI := J.inc.ne; haveI := J.dec.ne; haveI := J.atT.ne; haveI := J.atF.ne
  infer_instance

/-- The stage bound is within the contract's `C·(2^K0·(4·Mul wR + eb wR + b + K0) + hdr + 1)`. -/
theorem sqB_le (C : ℕ) (Mul : ℕ → ℕ) (wR b K0 h : ℕ) :
    sqB C Mul wR b K0 ≤ 1000 * (C + 1) * (2 ^ K0 * (4 * Mul wR + eb wR + b + K0) + h + 1) := by
  unfold sqB entB qOf eb
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ K0 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := hN ▸ Nat.one_le_two_pow
  rw [← hN]
  obtain ⟨A, hA⟩ : ∃ A, A = N * (2 * wR + 4 + b + K0) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = N * Mul wR := ⟨_, rfl⟩
  have f1 : N * (wR + (2 * b + 2 * K0 + 8) + 1) ≤ 3 * A := by
    rw [hA]
    calc N * (wR + (2 * b + 2 * K0 + 8) + 1) ≤ N * (3 * (2 * wR + 4 + b + K0)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (N * (2 * wR + 4 + b + K0)) := by ring
  have f2 : N * (2 + 3 * (2 * wR + 4)) ≤ 4 * A := by
    rw [hA]
    calc N * (2 + 3 * (2 * wR + 4)) ≤ N * (4 * (2 * wR + 4 + b + K0)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (N * (2 * wR + 4 + b + K0)) := by ring
  have f3 : 2 * wR + 4 + b + K0 ≤ A := by
    rw [hA]
    exact Nat.le_mul_of_pos_left _ hN1
  have g1 : (C + 1) * (N * (wR + (2 * b + 2 * K0 + 8) + 1)) ≤ 3 * ((C + 1) * A) := by
    calc (C + 1) * (N * (wR + (2 * b + 2 * K0 + 8) + 1)) ≤ (C + 1) * (3 * A) :=
          Nat.mul_le_mul_left _ f1
      _ = 3 * ((C + 1) * A) := by ring
  have g2 : (C + 1) * (b + K0 + 1) ≤ (C + 1) * A + (C + 1) :=
    calc (C + 1) * (b + K0 + 1) ≤ (C + 1) * (A + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (C + 1) * A + (C + 1) := by ring
  have g3 : C * (2 * b + 2 * K0 + 8 + 1) ≤ 3 * ((C + 1) * A) :=
    calc C * (2 * b + 2 * K0 + 8 + 1) ≤ (C + 1) * (3 * A) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * ((C + 1) * A) := by ring
  have g4 : N * (2 + 3 * (2 * wR + 4)) ≤ 4 * ((C + 1) * A) :=
    calc N * (2 + 3 * (2 * wR + 4)) ≤ 4 * A := f2
      _ ≤ 4 * ((C + 1) * A) := by
          have : A ≤ (C + 1) * A := Nat.le_mul_of_pos_left _ (by omega)
          omega
  have g5 : C * P ≤ (C + 1) * P := Nat.mul_le_mul_right _ (by omega)
  have g6 : 1 ≤ C + 1 := by omega
  have g7 : (C + 1) ≤ (C + 1) * (h + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have eL : N * (4 * (C * Mul wR) + 100 * (C + 1) * (wR + (2 * b + 2 * K0 + 8) + 1) + 2 +
      3 * (2 * wR + 4)) = 4 * (C * P) + 100 * ((C + 1) * (N * (wR + (2 * b + 2 * K0 + 8) + 1))) +
        N * (2 + 3 * (2 * wR + 4)) := by rw [hP]; ring
  have eR : 1000 * (C + 1) * (N * (4 * Mul wR + (2 * wR + 4) + b + K0) + h + 1) =
      4000 * ((C + 1) * P) + 1000 * ((C + 1) * A) + 1000 * ((C + 1) * (h + 1)) := by
    rw [hP, hA]; ring
  have e3 : 100 * (C + 1) * (b + K0 + 1) = 100 * ((C + 1) * (b + K0 + 1)) := by ring
  have e4 : 3 * C * (2 * b + 2 * K0 + 8 + 1) = 3 * (C * (2 * b + 2 * K0 + 8 + 1)) := by ring
  rw [eL, eR, e3, e4]
  omega

/-- **`W9_square`** from `W5_mulAt Mul` and the W3 contracts the kernel calls. -/
theorem W9_square_core (Mul : ℕ → ℕ) (hmul : W5_mulAt Mul) (hdrop : W3_dropNat)
    (haddN : W3_addNat) (hshr : W3_shrVar) (hshl : W3_shlVar) (haddI : W3_addInt)
    (hsubI : W3_subInt) (hatt : W3_attachSign) : W9_square Mul := by
  obtain ⟨Cm, hm⟩ := exists_inst hmul
  obtain ⟨Im, hIm⟩ := hm ()
  obtain ⟨Cc, hc⟩ := exists_inst w3_copyNat
  obtain ⟨Ic, hIc⟩ := hc ()
  obtain ⟨Cd, hd⟩ := exists_inst hdrop
  obtain ⟨Id, hId⟩ := hd ()
  obtain ⟨Cs, hs⟩ := exists_inst hsubI
  obtain ⟨Is, hIs⟩ := hs ()
  obtain ⟨Ca, ha⟩ := exists_inst haddI
  obtain ⟨Ia, hIa⟩ := ha ()
  obtain ⟨Cn, hn⟩ := exists_inst haddN
  obtain ⟨In, hIn⟩ := hn ()
  obtain ⟨Cr, hr⟩ := exists_inst hshr
  obtain ⟨Ir, hIr⟩ := hr ()
  obtain ⟨Cl, hl⟩ := exists_inst hshl
  obtain ⟨Il, hIl⟩ := hl ()
  obtain ⟨Ci, hi⟩ := exists_inst w3_incNat
  obtain ⟨Ii, hIi⟩ := hi ()
  obtain ⟨Ce, he⟩ := exists_inst w3_decNat
  obtain ⟨Ie, hIe⟩ := he ()
  obtain ⟨Ct, ht⟩ := exists_inst hatt
  obtain ⟨IT, hIT⟩ := ht true
  obtain ⟨IF, hIF⟩ := ht false
  obtain ⟨C, hC⟩ : ∃ C, C = Cm + Cc + Cd + Cs + Ca + Cn + Cr + Cl + Ci + Ce + Ct := ⟨_, rfl⟩
  have hJ : SqI.Spec Mul ⟨Im, Ic, Id, Is, Ia, In, Ir, Il, Ii, Ie, IT, IF⟩ C :=
    ⟨SpecMul.mono hIm (by omega), SpecCopy.mono' hIc (by omega), SpecDrop.mono' hId (by omega),
      SpecSubInt.mono hIs (by omega), SpecAddInt.mono hIa (by omega),
      SpecAddNat.mono hIn (by omega), SpecShrVar.mono hIr (by omega),
      SpecShlVar.mono' hIl (by omega), SpecInc.mono hIi (by omega), SpecDecr.mono hIe (by omega),
      SpecAttach.mono hIT (by omega), SpecAttach.mono hIF (by omega)⟩
  refine ⟨1000 * (C + 1), fun _ => ⟨nS, SqI.Reg ⟨Im, Ic, Id, Is, Ia, In, Ir, Il, Ii, Ie, IT, IF⟩,
    (sqProg ⟨Im, Ic, Id, Is, Ia, In, Ir, Il, Ii, Ie, IT, IF⟩
      (initK ⟨Im, Ic, Id, Is, Ia, In, Ir, Il, Ii, Ie, IT, IF⟩)).mapStk eH,
    by decide, SqI.finite _, SqI.nonempty _,
    closed_mapStk_eH (sqProg_closed _ _ (initK_closed _)), ?_⟩⟩
  intro b K0 k1 k2 wR z σ restS r0 hz hzw hsw hC0 hS0
  have h := sq_spec _ hJ (toH σ) b K0 k1 k2 wR r0 z restS hz hzw hsw hC0 hS0
  rw [show (hS : HL) = .inl (finOf .S) from rfl, ← toH_update] at h
  exact Triple.cost_mono (runs_of_HT h) (sqB_le C Mul wR b K0 _)

/-- **`W9_square`** at the shared-`Mul` shape, from `W3_all`. -/
theorem W9_square_holds : ∀ Mul, W5_mulAt Mul → W3_all → W9_square Mul := by
  intro Mul hmul h3
  obtain ⟨_, hdrop, _, _, _, haddN, _, _, _, hshl, hshr, _, _, _, _, _, _, hatt, _, _, _, haddI,
    hsubI, _, _⟩ := h3
  exact W9_square_core Mul hmul hdrop haddN hshr hshl haddI hsubI hatt

/-- The binding shape of `W9comp.W9StageThms.square` (`W4_all`, `W6a_all` unused). -/
theorem W9_square_holds' : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_square Mul :=
  fun Mul hmul h3 _ _ => W9_square_holds Mul hmul h3

/-- **`W9_square`** from `W5_mulAt Mul` and only the open W3 contracts it needs. -/
theorem W9_square_holds_min (Mul : ℕ → ℕ) (hmul : W5_mulAt Mul) (hdrop : W3_dropNat)
    (haddN : W3_addNat) (hsubN : W3_subNat) (hshr : W3_shrVar) (hshl : W3_shlVar) :
    W9_square Mul :=
  W9_square_core Mul hmul hdrop haddN hshr hshl (TMFw.W3b.W3_addInt_holds haddN hsubN)
    (TMFw.W3b.W3_subInt_holds haddN hsubN) TMFw.W3b.W3_attachSign_holds

#assert_std_axioms SqI.finite SqI.nonempty sqB_le W9_square_core W9_square_holds W9_square_holds'
  W9_square_holds_min

end WP.W9sq
