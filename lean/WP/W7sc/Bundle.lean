import WP.W7k3.SerCall

/-!
# WP.W7sc.Bundle — the instance bundle of the `stdChar` kernel

`exists_bundle`: from the contracts the kernel calls (directly, or through the series
sub-kernel `W7S_series`), one bundle `I : KI` and one constant `C ≥ 1` with all the contract
bodies the kernel's proof uses: `I.Spec Mul C`, `I.SpecX C` and `SpecSer` for the cos and sin
series instances. Each contract gives its own constant (`exists_inst`, `exists_ser`); the sum
plus one bounds them all (`Spec*.mono`).
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

theorem exists_bundle {Mul : ℕ → ℕ} (hcp : W3_copyNat) (hdr : W3_dropNat) (hiz : W3_isZeroNat)
    (hdc : W3_decNat) (hic : W3_incNat) (hai : W3_addInt) (had : W3_addNat) (hs1 : W3_shlConst)
    (hsv : W3_shlVar) (hng : W3_negInt) (h5 : W5_mulAt Mul) (h6 : W6a_divRound)
    (hpi : W7_piScaled) (hser : W7S_series Mul) :
    ∃ (C : ℕ) (I : KI), I.Spec Mul C ∧ I.SpecX C ∧ SpecSer SK.cos I.sc C ∧
      SpecSer SK.sin I.ss C := by
  obtain ⟨C1, h1⟩ := exists_inst hcp
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hdr
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst hiz
  obtain ⟨Iiz, hIiz⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst hdc
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5'⟩ := exists_inst hic
  obtain ⟨Iic, hIic⟩ := h5' ()
  obtain ⟨C6, h6'⟩ := exists_inst hai
  obtain ⟨Iai, hIai⟩ := h6' ()
  obtain ⟨C7, h7⟩ := exists_inst h5
  obtain ⟨Imu, hImu⟩ := h7 ()
  obtain ⟨C8, h8⟩ := exists_inst h6
  obtain ⟨Idv, hIdv⟩ := h8 ()
  obtain ⟨C9, h9⟩ := exists_inst had
  obtain ⟨Iad, hIad⟩ := h9 ()
  obtain ⟨C10, h10⟩ := exists_inst hs1
  obtain ⟨Is1, hIs1⟩ := h10 1
  obtain ⟨C11, h11⟩ := exists_inst hsv
  obtain ⟨Isv, hIsv⟩ := h11 ()
  obtain ⟨C12, h12⟩ := exists_inst hng
  obtain ⟨Ing, hIng⟩ := h12 ()
  obtain ⟨C13, h13⟩ := exists_inst hpi
  obtain ⟨Ipi, hIpi⟩ := h13 ()
  obtain ⟨C14, h14⟩ := exists_ser hser
  obtain ⟨Isc, hIsc⟩ := h14 SK.cos
  obtain ⟨Iss, hIss⟩ := h14 SK.sin
  obtain ⟨C, hC⟩ : ∃ C, C = C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 +
      C13 + C14 + 1 := ⟨_, rfl⟩
  refine ⟨C, ⟨Icp, Idr, Iiz, Idc, Iic, Iai, Imu, Idv, Iad, Is1, Isv, Ing, Ipi, Isc, Iss⟩,
    ⟨SpecCopy.mono (I := Icp) (C := C1) hIcp (by omega),
      SpecDrop.mono (I := Idr) (C := C2) hIdr (by omega),
      SpecIsZero.mono (I := Iiz) (C := C3) hIiz (by omega),
      SpecDec.mono (I := Idc) (C := C4) hIdc (by omega),
      SpecInc.mono (I := Iic) (C := C5) hIic (by omega),
      SpecAddInt.mono (I := Iai) (C := C6) hIai (by omega),
      SpecMul.mono (I := Imu) (C := C7) hImu (by omega),
      SpecDivRound.mono (I := Idv) (C := C8) hIdv (by omega), by omega⟩,
    ⟨SpecAddNat.mono (I := Iad) (C := C9) hIad (by omega),
      SpecShlConst.mono (I := Is1) (C := C10) hIs1 (by omega),
      SpecShlVar.mono (I := Isv) (C := C11) hIsv (by omega),
      SpecNegInt.mono (I := Ing) (C := C12) hIng (by omega),
      SpecPi.mono (I := Ipi) (C := C13) hIpi (by omega)⟩,
    SpecSer.mono hIsc (by omega), SpecSer.mono hIss (by omega)⟩

#assert_std_axioms exists_bundle

end WP.W7sc
