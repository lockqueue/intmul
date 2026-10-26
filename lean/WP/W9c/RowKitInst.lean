import WP.W9c.RowKit

/-!
# WP.W9c.RowKitInst — the row kit from contract instances, with one common constant

* `Spec*.mono`: every contract body is monotone in its constant.
* `mkRKit`: the row kit over the product of the instances' register types (`RSig`).
* `rkitOK_mono`: lift all bodies to a common constant.
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

section Mono

variable {C C' : ℕ} (hC : C ≤ C')
include hC

theorem SpecHdr.mono {I : Inst 9 24 Unit} (h : SpecHdr I C) : SpecHdr I C' :=
  fun pSub m1 t1 r p_in r0 r1 S h0 h1 =>
    Triple.cost_mono (h pSub m1 t1 r p_in r0 r1 S h0 h1) (Nat.mul_le_mul_right _ hC)

theorem SpecTaps.mono {I : Inst 4 24 Unit} (h : SpecTaps I C) : SpecTaps I C' :=
  fun taps restT S h0 => Triple.cost_mono (h taps restT S h0) (Nat.mul_le_mul_right _ hC)

theorem SpecRSplit.mono {I : Inst 3 24 Unit} (h : SpecRSplit I C) : SpecRSplit I C' :=
  fun v rw S h0 h1 => Triple.cost_mono (h v rw S h0 h1) (Nat.mul_le_mul_right _ hC)

theorem SpecRZip.mono {I : Inst 3 24 Unit} (h : SpecRZip I C) : SpecRZip I C' :=
  fun a b ra rb S h0 h1 h2 h3 h4 =>
    Triple.cost_mono (h a b ra rb S h0 h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecPack.mono {I : Inst 6 24 Unit} (h : SpecPack I C) : SpecPack I C' :=
  fun k p_in q W B v rx rk ra rb rW S h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
    Triple.cost_mono (h k p_in q W B v rx rk ra rb rW S h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
      (Nat.mul_le_mul_right _ hC)

theorem SpecUnpack.mono {I : Inst 4 24 Unit} (h : SpecUnpack I C) : SpecUnpack I C' :=
  fun k n Pz rx rk rn S h1 h2 h3 h4 h5 h6 h7 =>
    Triple.cost_mono (h k n Pz rx rk rn S h1 h2 h3 h4 h5 h6 h7) (Nat.mul_le_mul_right _ hC)

theorem SpecWindow.mono {I : Inst 4 24 Unit} (h : SpecWindow I C) : SpecWindow I C' :=
  fun W B ds ws rd rw rW S h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    Triple.cost_mono (h W B ds ws rd rw rW S h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
      (Nat.mul_le_mul_right _ hC)

theorem SpecCyc.mono {I : Inst 3 24 Unit} (h : SpecCyc I C) : SpecCyc I C' :=
  fun Bc Bv p cells vs rv rL rR S h1 h2 h3 h4 h5 h6 h7 h8 =>
    Triple.cost_mono (h Bc Bv p cells vs rv rL rR S h1 h2 h3 h4 h5 h6 h7 h8)
      (Nat.mul_le_mul_right _ hC)

theorem SpecMul.mono {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} (h : SpecMul Mul I C) : SpecMul Mul I C' :=
  fun w a b ra rb S h1 h2 h3 h4 h5 h6 =>
    Triple.cost_mono (h w a b ra rb S h1 h2 h3 h4 h5 h6)
      (Nat.add_le_add (Nat.mul_le_mul_right _ hC) hC)

theorem SpecCopy.mono {I : Inst 2 4 Unit} (h : SpecCopy I C) : SpecCopy I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecDrop.mono {I : Inst 1 4 Unit} (h : SpecDrop I C) : SpecDrop I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecIsZero.mono {I : Inst 1 4 Bool} (h : SpecIsZero I C) : SpecIsZero I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) hC

theorem SpecInc.mono {I : Inst 1 4 Unit} (h : SpecInc I C) : SpecInc I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecDec.mono {I : Inst 1 4 Unit} (h : SpecDec I C) : SpecDec I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecAddN.mono {I : Inst 3 4 Unit} (h : SpecAddN I C) : SpecAddN I C' :=
  fun a b rx ry S h1 h2 h3 h4 => Triple.cost_mono (h a b rx ry S h1 h2 h3 h4)
    (Nat.mul_le_mul_right _ hC)

theorem SpecSubN.mono {I : Inst 3 4 Unit} (h : SpecSubN I C) : SpecSubN I C' :=
  fun a b rx ry S h1 h2 h3 h4 h5 => Triple.cost_mono (h a b rx ry S h1 h2 h3 h4 h5)
    (Nat.mul_le_mul_right _ hC)

theorem SpecSplitAt.mono {I : Inst 3 4 Unit} (h : SpecSplitAt I C) : SpecSplitAt I C' :=
  fun a c rx rc S h1 h2 h3 h4 => Triple.cost_mono (h a c rx rc S h1 h2 h3 h4)
    (Nat.mul_le_mul_right _ hC)

end Mono

/-! ## The row kit -/

/-- `l` on the second component. -/
def sndL {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

/-- Register type of the row driver. -/
abbrev RSig (hd : Inst 9 24 Unit) (tp : Inst 4 24 Unit) (sp zp : Inst 3 24 Unit)
    (pk : Inst 6 24 Unit) (ps : Inst 10 24 Unit) (cp : Inst 2 4 Unit) (dr : Inst 1 4 Unit)
    (iz : Inst 1 4 Bool) (ic dc : Inst 1 4 Unit) (ad sb sa : Inst 3 4 Unit) : Type :=
  hd.R × (tp.R × (sp.R × (zp.R × (pk.R × (ps.R × (cp.R × (dr.R × (iz.R × (ic.R × (dc.R ×
    (ad.R × (sb.R × sa.R))))))))))))

section Kit

variable (hd : Inst 9 24 Unit) (tp : Inst 4 24 Unit) (sp zp : Inst 3 24 Unit)
    (pk : Inst 6 24 Unit) (ps : Inst 10 24 Unit) (cp : Inst 2 4 Unit) (dr : Inst 1 4 Unit)
    (iz : Inst 1 4 Bool) (ic dc : Inst 1 4 Unit) (ad sb sa : Inst 3 4 Unit)

/-- The row kit over `RSig`. -/
def mkRKit : RKit (RSig hd tp sp zp pk ps cp dr iz ic dc ad sb sa) where
  hd := hd
  lhd := Lens.fst _ _
  tp := tp
  ltp := sndL (Lens.fst _ _)
  sp := sp
  lsp := sndL (sndL (Lens.fst _ _))
  zp := zp
  lzp := sndL (sndL (sndL (Lens.fst _ _)))
  pk := pk
  lpk := sndL (sndL (sndL (sndL (Lens.fst _ _))))
  ps := ps
  lps := sndL (sndL (sndL (sndL (sndL (Lens.fst _ _)))))
  cp := cp
  lcp := sndL (sndL (sndL (sndL (sndL (sndL (Lens.fst _ _))))))
  dr := dr
  ldr := sndL (sndL (sndL (sndL (sndL (sndL (sndL (Lens.fst _ _)))))))
  iz := iz
  liz := sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (Lens.fst _ _))))))))
  ic := ic
  lic := sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (Lens.fst _ _)))))))))
  dc := dc
  ldc := sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (Lens.fst _ _))))))))))
  ad := ad
  lad := sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL
    (Lens.fst _ _)))))))))))
  sb := sb
  lsb := sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL
    (Lens.fst _ _))))))))))))
  sa := sa
  lsa := sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL (sndL
    (Lens.snd _ _))))))))))))

theorem rsig_finite : Finite (RSig hd tp sp zp pk ps cp dr iz ic dc ad sb sa) := by
  haveI := hd.fin; haveI := tp.fin; haveI := sp.fin; haveI := zp.fin; haveI := pk.fin
  haveI := ps.fin; haveI := cp.fin; haveI := dr.fin; haveI := iz.fin; haveI := ic.fin
  haveI := dc.fin; haveI := ad.fin; haveI := sb.fin; haveI := sa.fin
  infer_instance

theorem rsig_nonempty : Nonempty (RSig hd tp sp zp pk ps cp dr iz ic dc ad sb sa) := by
  haveI := hd.ne; haveI := tp.ne; haveI := sp.ne; haveI := zp.ne; haveI := pk.ne
  haveI := ps.ne; haveI := cp.ne; haveI := dr.ne; haveI := iz.ne; haveI := ic.ne
  haveI := dc.ne; haveI := ad.ne; haveI := sb.ne; haveI := sa.ne
  infer_instance

end Kit

#assert_std_axioms SpecHdr.mono SpecTaps.mono SpecRSplit.mono SpecRZip.mono SpecPack.mono
  SpecUnpack.mono SpecWindow.mono SpecCyc.mono SpecMul.mono SpecCopy.mono SpecDrop.mono
  SpecIsZero.mono SpecInc.mono SpecDec.mono SpecAddN.mono SpecSubN.mono SpecSplitAt.mono
  rsig_finite rsig_nonempty

end WP.W9c
