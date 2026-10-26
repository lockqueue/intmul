import WP.W9h.Raw

/-!
# WP.W9h.Inst — the W3 instances of the root kernels, with one cost constant

`Kit` bundles one extracted instance per W3 contract that the root kernels call; `Kit.Reg` is the
kernel register file (a symbol register `lS` and one component per instance, with lenses), and
`Kit.Spec K C` holds the instance specifications at the single constant `C`. `exists_kit` extracts
a kit from the `W3_all` contract bundle.
-/

namespace WP.W9h

open TMFw TMFw.Contracts WP.W7k2

/-- The W3 instances the root kernels call. -/
structure Kit where
  copy : Inst 2 4 Unit
  drop : Inst 1 4 Unit
  add : Inst 3 4 Unit
  split : Inst 3 4 Unit
  concat : Inst 3 4 Unit
  shl2 : Inst 1 4 Unit
  shlV : Inst 2 4 Unit
  isZ : Inst 1 4 Bool
  dec : Inst 1 4 Unit

/-- Lens into the tail of a register pair. -/
def sn {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

namespace Kit

variable (K : Kit)

/-- Registers: a symbol register and one component per instance. -/
abbrev Reg : Type :=
  Option Sym × K.copy.R × K.drop.R × K.add.R × K.split.R × K.concat.R × K.shl2.R × K.shlV.R ×
    K.isZ.R × K.dec.R

def lS : Lens K.Reg (Option Sym) := Lens.fst _ _
def lCopy : Lens K.Reg K.copy.R := sn (Lens.fst _ _)
def lDrop : Lens K.Reg K.drop.R := sn (sn (Lens.fst _ _))
def lAdd : Lens K.Reg K.add.R := sn (sn (sn (Lens.fst _ _)))
def lSplit : Lens K.Reg K.split.R := sn (sn (sn (sn (Lens.fst _ _))))
def lConcat : Lens K.Reg K.concat.R := sn (sn (sn (sn (sn (Lens.fst _ _)))))
def lShl2 : Lens K.Reg K.shl2.R := sn (sn (sn (sn (sn (sn (Lens.fst _ _))))))
def lShlV : Lens K.Reg K.shlV.R := sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _)))))))
def lIsZ : Lens K.Reg K.isZ.R := sn (sn (sn (sn (sn (sn (sn (sn (Lens.fst _ _))))))))
def lDec : Lens K.Reg K.dec.R := sn (sn (sn (sn (sn (sn (sn (sn (Lens.snd _ _))))))))

theorem finite_Reg : Finite K.Reg := by
  haveI := K.copy.fin; haveI := K.drop.fin; haveI := K.add.fin; haveI := K.split.fin
  haveI := K.concat.fin; haveI := K.shl2.fin; haveI := K.shlV.fin; haveI := K.isZ.fin
  haveI := K.dec.fin
  infer_instance

theorem nonempty_Reg : Nonempty K.Reg := by
  haveI := K.copy.ne; haveI := K.drop.ne; haveI := K.add.ne; haveI := K.split.ne
  haveI := K.concat.ne; haveI := K.shl2.ne; haveI := K.shlV.ne; haveI := K.isZ.ne
  haveI := K.dec.ne
  infer_instance

/-- The instance specifications at one constant `C`, and the decrement amortisation. -/
structure Spec (C : ℕ) : Prop where
  copy : SpecCopy K.copy C
  drop : SpecDrop K.drop C
  add : SpecAdd K.add C
  split : SpecSplit K.split C
  concat : SpecConcat K.concat C
  shl2 : SpecShlConst 2 K.shl2 C
  shlV : SpecShlVar K.shlV C
  isZ : SpecIsZero K.isZ C
  dec : SpecDec K.dec C
  amort : W3_dec_amortised

end Kit

/-- **A kit from the W3 contracts.** -/
theorem exists_kit (h : W3_all) : ∃ (K : Kit) (C : ℕ), K.Spec C := by
  obtain ⟨hcopy, hdrop, -, hisZ, -, hadd, -, hshlC, -, hshlV, -, hsplit, hconcat, -, hdec,
    hamort, -⟩ := h
  obtain ⟨C1, h1⟩ := exists_inst hcopy
  obtain ⟨I1, s1⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hdrop
  obtain ⟨I2, s2⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst hadd
  obtain ⟨I3, s3⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst hsplit
  obtain ⟨I4, s4⟩ := h4 ()
  obtain ⟨C5, h5⟩ := exists_inst hconcat
  obtain ⟨I5, s5⟩ := h5 ()
  obtain ⟨C6, h6⟩ := exists_inst hshlC
  obtain ⟨I6, s6⟩ := h6 2
  obtain ⟨C7, h7⟩ := exists_inst hshlV
  obtain ⟨I7, s7⟩ := h7 ()
  obtain ⟨C8, h8⟩ := exists_inst hisZ
  obtain ⟨I8, s8⟩ := h8 ()
  obtain ⟨C9, h9⟩ := exists_inst hdec
  obtain ⟨I9, s9⟩ := h9 ()
  refine ⟨⟨I1, I2, I3, I4, I5, I6, I7, I8, I9⟩, C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9,
    ⟨SpecCopy.mono s1 (by omega), SpecDrop.mono s2 (by omega), SpecAdd.mono s3 (by omega),
      SpecSplit.mono s4 (by omega), SpecConcat.mono s5 (by omega),
      SpecShlConst.mono s6 (by omega), SpecShlVar.mono s7 (by omega),
      SpecIsZero.mono s8 (by omega), SpecDec.mono s9 (by omega), hamort⟩⟩

#assert_std_axioms Kit.finite_Reg Kit.nonempty_Reg exists_kit

end WP.W9h
