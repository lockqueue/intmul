import WP.W7k3.SerEnds
import WP.W7k3.SerCall

/-!
# WP.W7k3.Ser — the series sub-kernel: whole program, instance, contract

* `serProg_spec`: setup (`serSetup_spec`), loop (`serLoop_spec`), end (`serEnd_spec`); at most
  `64·(n+1)·U` with `V = W + 1`.
* `serInst`, `serInst_spec`: the program as a contract instance; its body `SpecSer` holds with the
  constant `64·C·(K+8)` (`U = C·(K+8)·(W+2)²`).
* `W7S_series_holds`: the contract, from the W3 / W5 / W6a contracts the program calls and the
  quadratic growth of `Mul`. Bundle fields the program does not use get `dummyInst`.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

/-! ## The whole program -/

theorem serProg_spec {X : KX} {I : KI} (hX : X.OK I) (κ : SK) (hκ : κ.OK) (S : SL → List Sym)
    (W : ℕ) (hV : X.V = W + 1) (a0 c : ℤ) (d n : ℕ) (r0 r1 r2 r3 : List Sym) (hd0 : 0 < d)
    (hn : 0 < n) (hw : IntMul.RecurrenceCallSitesWidthSound W a0 c d κ.f κ.g n)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : S (.inl 0) = intSyms a0 ++ r0) (e1 : S (.inl 1) = intSyms c ++ r1)
    (e2 : S (.inl 2) = natSyms d ++ r2) (e3 : S (.inl 3) = natSyms n ++ r3) :
    HT [] S (serProg I κ)
      (Function.update S (.inl 4) (intSyms (serState a0 c d κ.f κ.g n).2 ++ S (.inl 4)))
      (64 * (n + 1) * X.U) := by
  obtain ⟨wa0, wd, wn, wf0, wg10, wg20, wan, wsn, wfn, wg1n, wg2n⟩ := serW_ends hκ hd0 hn hw
  rw [← hV] at wa0 wd wn wf0 wg10 wg20 wan wsn wfn wg1n wg2n
  have hsetup := serSetup_spec hX κ S a0 d n r0 r2 r3 h0 h2 h3 e0 e2 e3 wa0 wd wn wf0 wg10 wg20
  have eS : sSt S (natSyms n ++ .mark :: S (.inr 0)) (intSyms a0 ++ .mark :: S (.inr 1))
      (intSyms 0 ++ .mark :: S (.inr 2)) (natSyms κ.fβ ++ .mark :: S (.inr 3))
      (natSyms κ.gδ ++ .mark :: S (.inr 4)) (natSyms κ.gζ ++ .mark :: S (.inr 5))
      (intSyms d ++ .mark :: S (.inr 6)) (.mark :: S (.inr 7)) (.mark :: S (.inr 8))
      (.mark :: S (.inr 9)) (.mark :: S (.inr 10)) (.mark :: S (.inr 11)) (S (.inl 4)) =
      serLS S κ a0 c d n n := by
    unfold serLS
    rw [Nat.sub_self]
    simp only [SK.f, Nat.mul_zero, Nat.zero_add, serState_zero]
  rw [eS] at hsetup
  have hloop := serLoop_spec hX κ hκ S W hV a0 c d n hd0 hn r1 h1 e1 hw
  have eE : serLS S κ a0 c d n 0 = sSt S (natSyms 0 ++ .mark :: S (.inr 0))
      (intSyms (serState a0 c d κ.f κ.g n).1 ++ .mark :: S (.inr 1))
      (intSyms (serState a0 c d κ.f κ.g n).2 ++ .mark :: S (.inr 2))
      (natSyms (κ.f n) ++ .mark :: S (.inr 3)) (natSyms (κ.gγ * n + κ.gδ) ++ .mark :: S (.inr 4))
      (natSyms (κ.gε * n + κ.gζ) ++ .mark :: S (.inr 5)) (intSyms d ++ .mark :: S (.inr 6))
      (.mark :: S (.inr 7)) (.mark :: S (.inr 8)) (.mark :: S (.inr 9)) (.mark :: S (.inr 10))
      (.mark :: S (.inr 11)) (S (.inl 4)) := by
    unfold serLS
    rw [Nat.sub_zero]
  rw [eE] at hloop
  have hend := serEnd_spec hX S (serState a0 c d κ.f κ.g n).1 (serState a0 c d κ.f κ.g n).2 d
    (κ.f n) (κ.gγ * n + κ.gδ) (κ.gε * n + κ.gζ) wan wsn wd wfn wg1n wg2n
  have e8 := KX.eight_le hX
  have hP : n ≤ n * X.U := Nat.le_mul_of_pos_right n (by omega)
  have c1 : n * (42 * X.U + 1) = 42 * (n * X.U) + n := by ring
  have c2 : 64 * (n + 1) * X.U = 64 * (n * X.U) + 64 * X.U := by ring
  refine (hsetup.seq (hloop.seq hend)).mono ?_
  rw [c1, c2]
  omega

/-! ## The instance and the contract -/

/-- The series program as a contract instance. -/
def serInst (I : KI) (κ : SK) : Inst 5 12 Unit :=
  ⟨12, I.R, fun _ => (), serProg I κ, le_rfl, I.R_finite, I.R_nonempty, serProg_closed I κ⟩

theorem serInst_spec {Mul : ℕ → ℕ} {I : KI} {C K : ℕ} (hI : I.Spec Mul C)
    (hK : ∀ w, Mul w ≤ K * (w + 1) ^ 2) (κ : SK) :
    SpecSer κ (serInst I κ) (64 * C * (K + 8)) := by
  intro hκ W a0 c d n r0 r1 r2 r3 S hd hn hw h0 h1 h2 h3 e0 e1 e2 e3
  have h := serProg_spec (X := ⟨Mul, C, K, W + 1⟩) ⟨hI, hK⟩ κ hκ S W rfl a0 c d n r0 r1 r2 r3
    hd hn hw h0 h1 h2 h3 e0 e1 e2 e3
  refine HT.runs (h.mono (le_of_eq ?_))
  simp only [KX.U]
  ring

/-- A placeholder instance, for bundle fields the series program does not use. -/
def dummyInst (n cap : ℕ) : Inst n cap Unit :=
  ⟨0, Unit, fun _ => (), .load id, Nat.zero_le _, inferInstance, ⟨()⟩, trivial⟩

/-- **The series sub-kernel's contract**, from the contracts its program calls. -/
theorem W7S_series_holds (Mul : ℕ → ℕ) (hMul : ∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2)
    (h5 : W5_mulAt Mul) (hcopy : W3_copyNat) (hdrop : W3_dropNat) (hisz : W3_isZeroNat)
    (hdec : W3_decNat) (hinc : W3_incNat) (haddI : W3_addInt) (h6 : W6a_divRound) :
    W7S_series Mul := by
  obtain ⟨K, hK⟩ := hMul
  obtain ⟨C1, hc1⟩ := exists_inst hcopy
  obtain ⟨C2, hc2⟩ := exists_inst hdrop
  obtain ⟨C3, hc3⟩ := exists_inst hisz
  obtain ⟨C4, hc4⟩ := exists_inst hdec
  obtain ⟨C5, hc5⟩ := exists_inst hinc
  obtain ⟨C6, hc6⟩ := exists_inst haddI
  obtain ⟨C7, hc7⟩ := exists_inst h5
  obtain ⟨C8, hc8⟩ := exists_inst h6
  obtain ⟨Icp, hIcp⟩ := hc1 ()
  obtain ⟨Idr, hIdr⟩ := hc2 ()
  obtain ⟨Iiz, hIiz⟩ := hc3 ()
  obtain ⟨Idc, hIdc⟩ := hc4 ()
  obtain ⟨Iic, hIic⟩ := hc5 ()
  obtain ⟨Iai, hIai⟩ := hc6 ()
  obtain ⟨Imu, hImu⟩ := hc7 ()
  obtain ⟨Idv, hIdv⟩ := hc8 ()
  obtain ⟨C, hC⟩ : ∃ C, C = C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + 1 := ⟨_, rfl⟩
  let I : KI := ⟨Icp, Idr, Iiz, Idc, Iic, Iai, Imu, Idv, dummyInst 3 4, dummyInst 1 4,
    dummyInst 2 4, dummyInst 1 4, dummyInst 2 16, dummyInst 5 12, dummyInst 5 12⟩
  have hI : I.Spec Mul C :=
    ⟨SpecCopy.mono (I := Icp) (C := C1) hIcp (by omega),
      SpecDrop.mono (I := Idr) (C := C2) hIdr (by omega),
      SpecIsZero.mono (I := Iiz) (C := C3) hIiz (by omega),
      SpecDec.mono (I := Idc) (C := C4) hIdc (by omega),
      SpecInc.mono (I := Iic) (C := C5) hIic (by omega),
      SpecAddInt.mono (I := Iai) (C := C6) hIai (by omega),
      SpecMul.mono (I := Imu) (C := C7) hImu (by omega),
      SpecDivRound.mono (I := Idv) (C := C8) hIdv (by omega), by omega⟩
  exact ⟨64 * C * (K + 8), fun κ => ⟨12, I.R, fun _ => (), serProg I κ, le_rfl, I.R_finite,
    I.R_nonempty, serProg_closed I κ, serInst_spec hI hK κ⟩⟩

#assert_std_axioms serProg_spec serInst_spec W7S_series_holds

end WP.W7k3
