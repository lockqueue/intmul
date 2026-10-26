import WP.W9sp.Loop

/-!
# WP.W9sp.Kit — the W3 instances of `W9_splitPack`, with one cost constant

`Kit` bundles one extracted instance per W3 contract that `W9_splitPack` calls (copy, drop,
splitAt, shlConst 2, shlVar, isZero, dec). `Kit.Reg` is the register file (a symbol register `lS`
and one component per instance, with lenses); `Kit.Spec K C` holds the instance specifications at
the single constant `C`, plus the decrement amortisation. `exists_kit` extracts a kit from `W3_all`
(taking the W3 contracts as explicit hypotheses, following `WP.W9h.Inst`).
-/

namespace WP.W9sp

open TMFw TMFw.Contracts WP.W7k2

/-- The W3 instances `W9_splitPack` calls. -/
structure Kit where
  copy : Inst 2 4 Unit
  drop : Inst 1 4 Unit
  split : Inst 3 4 Unit
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
  Option Sym × K.copy.R × K.drop.R × K.split.R × K.shl2.R × K.shlV.R × K.isZ.R × K.dec.R

def lS : Lens K.Reg (Option Sym) := Lens.fst _ _
def lCopy : Lens K.Reg K.copy.R := sn (Lens.fst _ _)
def lDrop : Lens K.Reg K.drop.R := sn (sn (Lens.fst _ _))
def lSplit : Lens K.Reg K.split.R := sn (sn (sn (Lens.fst _ _)))
def lShl2 : Lens K.Reg K.shl2.R := sn (sn (sn (sn (Lens.fst _ _))))
def lShlV : Lens K.Reg K.shlV.R := sn (sn (sn (sn (sn (Lens.fst _ _)))))
def lIsZ : Lens K.Reg K.isZ.R := sn (sn (sn (sn (sn (sn (Lens.fst _ _))))))
def lDec : Lens K.Reg K.dec.R := sn (sn (sn (sn (sn (sn (Lens.snd _ _))))))

theorem finite_Reg : Finite K.Reg := by
  haveI := K.copy.fin; haveI := K.drop.fin; haveI := K.split.fin; haveI := K.shl2.fin
  haveI := K.shlV.fin; haveI := K.isZ.fin; haveI := K.dec.fin
  infer_instance

theorem nonempty_Reg : Nonempty K.Reg := by
  haveI := K.copy.ne; haveI := K.drop.ne; haveI := K.split.ne; haveI := K.shl2.ne
  haveI := K.shlV.ne; haveI := K.isZ.ne; haveI := K.dec.ne
  infer_instance

/-- The instance specifications at one constant `C`, and the decrement amortisation. -/
structure Spec (C : ℕ) : Prop where
  copy : SpecCopy K.copy C
  drop : SpecDrop K.drop C
  split : SpecSplit K.split C
  shl2 : SpecShlConst 2 K.shl2 C
  shlV : SpecShlVar K.shlV C
  isZ : SpecIsZero K.isZ C
  dec : SpecDec K.dec C
  amort : W3_dec_amortised

/-! ## The calls, on host stacks (`dflt` is never used: every call names distinct stacks) -/

/-- Default host stack of the call map. -/
abbrev dflt : H := .inl 0

/-- `dst += src`. -/
def pCopy (src dst : H) : Prog H (fun _ => Sym) K.Reg := callI K.copy [src, dst] dflt K.lCopy
/-- Drop the number on top of `k`. -/
def pDrop (k : H) : Prog H (fun _ => Sym) K.Reg := callI K.drop [k] dflt K.lDrop
/-- `x ↦ x / 2^c`, `y += x % 2^c`. -/
def pSplit (x c y : H) : Prog H (fun _ => Sym) K.Reg := callI K.split [x, c, y] dflt K.lSplit
/-- `x ↦ 4x`. -/
def pShl2 (k : H) : Prog H (fun _ => Sym) K.Reg := callI K.shl2 [k] dflt K.lShl2
/-- `x ↦ x·2^c`. -/
def pShlV (s c : H) : Prog H (fun _ => Sym) K.Reg := callI K.shlV [s, c] dflt K.lShlV

theorem pCopy_closed (src dst : H) : (K.pCopy src dst).Closed := callI_closed _ _ _ _
theorem pDrop_closed (k : H) : (K.pDrop k).Closed := callI_closed _ _ _ _
theorem pSplit_closed (x c y : H) : (K.pSplit x c y).Closed := callI_closed _ _ _ _
theorem pShl2_closed (k : H) : (K.pShl2 k).Closed := callI_closed _ _ _ _
theorem pShlV_closed (s c : H) : (K.pShlV s c).Closed := callI_closed _ _ _ _

end Kit

/-- **A kit from the W3 contracts.** -/
theorem exists_kit (h : W3_all) : ∃ (K : Kit) (C : ℕ), K.Spec C := by
  obtain ⟨hcopy, hdrop, -, hisZ, -, -, -, hshlC, -, hshlV, -, hsplit, -, -, hdec, hamort, -⟩ := h
  obtain ⟨C1, h1⟩ := exists_inst hcopy
  obtain ⟨I1, s1⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hdrop
  obtain ⟨I2, s2⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst hsplit
  obtain ⟨I3, s3⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst hshlC
  obtain ⟨I4, s4⟩ := h4 2
  obtain ⟨C5, h5⟩ := exists_inst hshlV
  obtain ⟨I5, s5⟩ := h5 ()
  obtain ⟨C6, h6⟩ := exists_inst hisZ
  obtain ⟨I6, s6⟩ := h6 ()
  obtain ⟨C7, h7⟩ := exists_inst hdec
  obtain ⟨I7, s7⟩ := h7 ()
  refine ⟨⟨I1, I2, I3, I4, I5, I6, I7⟩, C1 + C2 + C3 + C4 + C5 + C6 + C7,
    ⟨SpecCopy.mono s1 (by omega), SpecDrop.mono s2 (by omega), SpecSplit.mono s3 (by omega),
      SpecShlConst.mono s4 (by omega), SpecShlVar.mono s5 (by omega),
      SpecIsZero.mono s6 (by omega), SpecDec.mono s7 (by omega), hamort⟩⟩

#assert_std_axioms Kit.finite_Reg Kit.nonempty_Reg Kit.pCopy_closed Kit.pDrop_closed
  Kit.pSplit_closed Kit.pShl2_closed Kit.pShlV_closed exists_kit

end WP.W9sp
