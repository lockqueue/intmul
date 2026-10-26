import WP.W7k2.Ops2
import WP.W7k2.Arith
import WP.W7k2.Canon.Kernels
import WP.W7k3.SeriesSpec

/-!
# WP.W7k3c.Base — the instance bundle of the `W7_c0c1` kernel

The kernel is a straight-line composition of contract calls (W7k2's call layer, `WP.W7k2.Call`).
`CI` bundles one instance per contract it calls; `CI.R` is the product of their registers.

| field | contract | field | contract |
|---|---|---|---|
| `cp`, `dr` | `W3_copyNat`, `W3_dropNat` | `mu` | `W5_mulAt Mul` |
| `ad`, `sb` | `W3_addNat`, `W3_subNat` | `dv` | `W6a_divRound` |
| `sv` | `W3_shlVar` | `pi`, `ln` | `W7_piScaled`, `W7_log2Scaled` |
| `cm`, `ci` | `W3_cmpNat`, `W3_cmpInt` | `sq` | `W7_isqrt` |
| `ai`, `si`, `ng` | `W3_addInt`, `W3_subInt`, `W3_negInt` | `se` | `W7S_series` at `SK.erf` |

`CI.Spec I Mul C` states all contract bodies with one constant `C ≥ 1`, and the growth bound
`Mul w ≤ C·(w+1)²`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-! ## Contract bodies not restated in W7k2 -/

/-- Body of `W3_subNat`. -/
def SpecSubNat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_subInt`. -/
def SpecSubInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W3_negInt`. -/
def SpecNegInt (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = intSyms z ++ rx →
    Runs I.P S (Function.update S (.inl 0) (intSyms (-z) ++ rx)) (fun _ => True) C

/-- Body of `W3_cmpInt`. -/
def SpecCmpInt (I : Inst 2 4 Ordering) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S S (fun r => I.obs r = cmpZ a b) (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W6a_divRound`. -/
def SpecDivRound (I : Inst 3 6 Unit) (C : ℕ) : Prop :=
  ∀ (num : ℤ) (den : ℕ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym), 0 < den →
    TermOK ra → TermOK rb →
    S (.inl 0) = intSyms num ++ ra → S (.inl 1) = natSyms den ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (divRoundRatInt num den) ++ S (.inl 2)))
      (fun _ => True)
      (C * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1))

/-- Body of `W7_isqrt`. -/
def SpecIsq (I : Inst 2 16 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (ra : List Sym) (S : Loc 2 I.m → List Sym), TermOK ra →
    S (.inl 0) = natSyms a ++ ra →
    Runs I.P S (Function.update S (.inl 1) (natSyms (Nat.sqrt a) ++ S (.inl 1))) (fun _ => True)
      (C * (bitLen a * bitLen a + 1))

/-- Body of `W7S_series` at the half-erf kind. -/
def SpecSer (I : Inst 5 12 Unit) (C : ℕ) : Prop :=
  ∀ (W : ℕ) (a0 c : ℤ) (d n : ℕ) (r0 r1 r2 r3 : List Sym) (S : Loc 5 I.m → List Sym),
    0 < d → 0 < n →
    IntMul.RecurrenceCallSitesWidthSound W a0 c d WP.W7k3.SK.erf.f WP.W7k3.SK.erf.g n →
    TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
    S (.inl 0) = intSyms a0 ++ r0 → S (.inl 1) = intSyms c ++ r1 →
    S (.inl 2) = natSyms d ++ r2 → S (.inl 3) = natSyms n ++ r3 →
    Runs I.P S (Function.update S (.inl 4)
        (intSyms (serState a0 c d WP.W7k3.SK.erf.f WP.W7k3.SK.erf.g n).2 ++ S (.inl 4)))
      (fun _ => True) (C * (n + 1) * (W + 2) ^ 2)

theorem SpecSubNat.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecSubNat I C) (hC : C ≤ C') :
    SpecSubNat I C' := fun a b rx ry S h1 h2 h3 h4 h5 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4 h5) (Nat.mul_le_mul_right _ hC)
theorem SpecSubInt.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecSubInt I C) (hC : C ≤ C') :
    SpecSubInt I C' := fun a b rx ry S h1 h2 h3 h4 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecNegInt.mono {I : Inst 1 4 Unit} {C C' : ℕ} (h : SpecNegInt I C) (hC : C ≤ C') :
    SpecNegInt I C' := fun z rx S h1 h2 => runs_mono (h z rx S h1 h2) hC
theorem SpecCmpInt.mono {I : Inst 2 4 Ordering} {C C' : ℕ} (h : SpecCmpInt I C) (hC : C ≤ C') :
    SpecCmpInt I C' := fun a b rx ry S h1 h2 h3 h4 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecDivRound.mono {I : Inst 3 6 Unit} {C C' : ℕ} (h : SpecDivRound I C) (hC : C ≤ C') :
    SpecDivRound I C' := fun n d ra rb S h0 h1 h2 h3 h4 =>
  runs_mono (h n d ra rb S h0 h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecIsq.mono {I : Inst 2 16 Unit} {C C' : ℕ} (h : SpecIsq I C) (hC : C ≤ C') :
    SpecIsq I C' := fun a ra S h1 h2 => runs_mono (h a ra S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecSer.mono {I : Inst 5 12 Unit} {C C' : ℕ} (h : SpecSer I C) (hC : C ≤ C') :
    SpecSer I C' := by
  intro W a0 c d n r0 r1 r2 r3 S h1 h2 h3 h4 h5 h6 h7 e0 e1 e2 e3
  exact runs_mono (h W a0 c d n r0 r1 r2 r3 S h1 h2 h3 h4 h5 h6 h7 e0 e1 e2 e3)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC))

/-! ## Lenses and the bundle -/

/-- Push a lens one product component to the right. -/
def lsc {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

/-- The contract instances of the `W7_c0c1` kernel. -/
structure CI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  sb : Inst 3 4 Unit
  sv : Inst 2 4 Unit
  cm : Inst 2 4 Ordering
  ai : Inst 3 4 Unit
  si : Inst 3 4 Unit
  ng : Inst 1 4 Unit
  ci : Inst 2 4 Ordering
  mu : Inst 3 8 Unit
  dv : Inst 3 6 Unit
  pi : Inst 2 16 Unit
  ln : Inst 2 16 Unit
  sq : Inst 2 16 Unit
  se : Inst 5 12 Unit

namespace CI

variable (I : CI)

/-- Host registers: one register file per instance. -/
abbrev R : Type :=
  I.cp.R × I.dr.R × I.ad.R × I.sb.R × I.sv.R × I.cm.R × I.ai.R × I.si.R × I.ng.R × I.ci.R ×
    I.mu.R × I.dv.R × I.pi.R × I.ln.R × I.sq.R × I.se.R

def lcp : Lens I.R I.cp.R := Lens.fst _ _
def ldr : Lens I.R I.dr.R := lsc (Lens.fst _ _)
def lad : Lens I.R I.ad.R := lsc (lsc (Lens.fst _ _))
def lsb : Lens I.R I.sb.R := lsc (lsc (lsc (Lens.fst _ _)))
def lsv : Lens I.R I.sv.R := lsc (lsc (lsc (lsc (Lens.fst _ _))))
def lcm : Lens I.R I.cm.R := lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))
def lai : Lens I.R I.ai.R := lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))
def lsi : Lens I.R I.si.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))
def lng : Lens I.R I.ng.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))))
def lci : Lens I.R I.ci.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))))
def lmu : Lens I.R I.mu.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))))))
def ldv : Lens I.R I.dv.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))))))
def lpi : Lens I.R I.pi.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))))))))
def lln : Lens I.R I.ln.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))))))))
def lsq : Lens I.R I.sq.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))))))))))
def lse : Lens I.R I.se.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.snd _ _))))))))))))))

theorem R_finite : Finite I.R := by
  haveI := I.cp.fin; haveI := I.dr.fin; haveI := I.ad.fin; haveI := I.sb.fin; haveI := I.sv.fin
  haveI := I.cm.fin; haveI := I.ai.fin; haveI := I.si.fin; haveI := I.ng.fin; haveI := I.ci.fin
  haveI := I.mu.fin; haveI := I.dv.fin; haveI := I.pi.fin; haveI := I.ln.fin; haveI := I.sq.fin
  haveI := I.se.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  haveI := I.cp.ne; haveI := I.dr.ne; haveI := I.ad.ne; haveI := I.sb.ne; haveI := I.sv.ne
  haveI := I.cm.ne; haveI := I.ai.ne; haveI := I.si.ne; haveI := I.ng.ne; haveI := I.ci.ne
  haveI := I.mu.ne; haveI := I.dv.ne; haveI := I.pi.ne; haveI := I.ln.ne; haveI := I.sq.ne
  haveI := I.se.ne
  infer_instance

/-- All contract bodies with one shared constant `C ≥ 1`, and the growth of `Mul`. -/
structure Spec (Mul : ℕ → ℕ) (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  ad : SpecAddNat I.ad C
  sb : SpecSubNat I.sb C
  sv : SpecShlVar I.sv C
  cm : SpecCmpNat I.cm C
  ai : SpecAddInt I.ai C
  si : SpecSubInt I.si C
  ng : SpecNegInt I.ng C
  ci : SpecCmpInt I.ci C
  mu : SpecMul Mul I.mu C
  dv : SpecDivRound I.dv C
  pi : SpecPi I.pi C
  ln : SpecLn2 I.ln C
  sq : SpecIsq I.sq C
  se : SpecSer I.se C
  one : 1 ≤ C
  mulB : ∀ w, Mul w ≤ C * (w + 1) ^ 2

end CI

/-- Host stacks of the kernel: `0 p_work, 1 pSub, 2 r, 3 u2, 4 dst`, sixteen scratch stacks. -/
abbrev HL : Type := Loc 5 16

/-- Programs of the kernel. -/
abbrev CP (I : CI) : Type := Prog HL (fun _ => Sym) I.R

#assert_std_axioms SpecSubNat.mono SpecSubInt.mono SpecNegInt.mono SpecCmpInt.mono
  SpecDivRound.mono SpecIsq.mono SpecSer.mono CI.R_finite CI.R_nonempty

end WP.W7k3c
