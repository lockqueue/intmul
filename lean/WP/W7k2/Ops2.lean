import WP.W7k2.Loops

/-!
# WP.W7k2.Ops2 — more host rules: W3 arithmetic, W5 multiplication, the W7 kernels, constants

`Spec*` restate the bodies of `W3_addNat`, `W3_incNat`, `W3_shrConst`, `W3_addInt`, `W5_mulAt`,
`W7_stdChar`, `W7_sincGaussianTap`, `W7_c0c1`, `W7_colRecip`, `W7_piScaled`, `W7_log2Scaled` for one
extracted instance; `HT.*` are the host rules. `Spec*.mono` raise the constant, so every instance of
a program can share one constant. `pushNat` pushes a compile-time constant.
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-! ## Specifications -/

/-- Body of `W3_addNat`. -/
def SpecAddNat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_incNat`. -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (Computability.encodeNat a) + 1))

/-- Body of `W3_shrConst` at shift `k`. -/
def SpecShrConst (k : ℕ) (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ k) ++ rx)) (fun _ => True)
      (C * (k + 1))

/-- Body of `W3_addInt`. -/
def SpecAddInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W5_mulAt Mul`. -/
def SpecMul (Mul : ℕ → ℕ) (I : Inst 3 8 Unit) (C : ℕ) : Prop :=
  ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym),
    bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
    S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
      (C * Mul w + C)

/-- Body of `W7_stdChar` at sign `neg`. -/
def SpecStdChar (neg : Bool) (I : Inst 4 16 Unit) (C : ℕ) : Prop :=
  ∀ (q num den : ℕ) (r0 r1 r2 : List Sym) (S : Loc 4 I.m → List Sym),
    0 < den → num ≤ den → TermOK r0 → TermOK r1 → TermOK r2 →
    S (.inl 0) = natSyms q ++ r0 → S (.inl 1) = natSyms num ++ r1 →
    S (.inl 2) = natSyms den ++ r2 →
    Runs I.P S (Function.update S (.inl 3)
        (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den neg).1 ++ S (.inl 3)))
      (fun _ => True) (C * (q + bitLen den + 1) ^ 4)

/-- Body of `W7_sincGaussianTap`. -/
def SpecTap (I : Inst 8 16 Unit) (C : ℕ) : Prop :=
  ∀ (p_work pSub t1 j1 s : ℕ) (πZ lnZ : ℤ) (r0 r1 r2 r3 r4 r5 r6 : List Sym)
    (S : Loc 8 I.m → List Sym),
    0 < p_work → 0 < pSub → 0 < t1 → j1 < t1 → s < 2 * pSub + 1 →
    πZ = (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1 →
    lnZ = (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1 →
    TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
    S (.inl 0) = natSyms p_work ++ r0 → S (.inl 1) = natSyms pSub ++ r1 →
    S (.inl 2) = natSyms t1 ++ r2 → S (.inl 3) = natSyms j1 ++ r3 →
    S (.inl 4) = natSyms s ++ r4 → S (.inl 5) = intSyms πZ ++ r5 →
    S (.inl 6) = intSyms lnZ ++ r6 →
    Runs I.P S (Function.update S (.inl 7)
        (intSyms (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1 ++
          S (.inl 7)))
      (fun _ => True) (C * (p_work + pSub + bitLen t1 + 1) ^ 4)

/-- Body of `W7_c0c1`. -/
def SpecC0C1 (I : Inst 5 16 Unit) (C : ℕ) : Prop :=
  ∀ (p_work pSub r u2 : ℕ) (r0 r1 r2 r3 : List Sym) (S : Loc 5 I.m → List Sym),
    0 < p_work → 0 < r → u2 < r →
    TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
    S (.inl 0) = natSyms p_work ++ r0 → S (.inl 1) = natSyms pSub ++ r1 →
    S (.inl 2) = natSyms r ++ r2 → S (.inl 3) = natSyms u2 ++ r3 →
    Runs I.P S (Function.update S (.inl 4)
        (intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.1.1 ++
          intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.2.1 ++ S (.inl 4)))
      (fun _ => True) (C * (p_work + pSub + bitLen r + 1) ^ 4)

/-- Body of `W7_colRecip`. -/
def SpecColRecip (I : Inst 6 16 Unit) (C : ℕ) : Prop :=
  ∀ (H r u2 : ℕ) (a c : ℤ) (r0 r1 r2 r3 r4 : List Sym) (S : Loc 6 I.m → List Sym),
    0 < IntMulTM.Contracts.W8.columnDivisor r u2 a c →
    TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = natSyms H ++ r0 → S (.inl 1) = natSyms r ++ r1 → S (.inl 2) = natSyms u2 ++ r2 →
    S (.inl 3) = intSyms a ++ r3 → S (.inl 4) = intSyms c ++ r4 →
    Runs I.P S (Function.update S (.inl 5) (intSyms (W7.colRecip H r u2 a c) ++ S (.inl 5)))
      (fun _ => True)
      (C * ((H + 1) * (bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 a c).natAbs + 1) +
        bitLen r + bitLen u2 + bitLen a.natAbs + bitLen c.natAbs + 1))

/-- Body of `W7_piScaled`. -/
def SpecPi (I : Inst 2 16 Unit) (C : ℕ) : Prop :=
  ∀ (B : ℕ) (rB : List Sym) (S : Loc 2 I.m → List Sym), TermOK rB →
    S (.inl 0) = natSyms B ++ rB →
    Runs I.P S (Function.update S (.inl 1)
        (intSyms (IntMul.computablePiScaledWithCost B).1 ++ S (.inl 1))) (fun _ => True)
      (C * (B + 1) ^ 4)

/-- Body of `W7_log2Scaled`. -/
def SpecLn2 (I : Inst 2 16 Unit) (C : ℕ) : Prop :=
  ∀ (B : ℕ) (rB : List Sym) (S : Loc 2 I.m → List Sym), TermOK rB →
    S (.inl 0) = natSyms B ++ rB →
    Runs I.P S (Function.update S (.inl 1)
        (intSyms (IntMul.computableLog2ScaledWithCost B).1 ++ S (.inl 1))) (fun _ => True)
      (C * (B + 1) ^ 4)

/-! ## Raising the constant -/

theorem runs_mono {K R : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) R}
    {S S' : K → List Sym} {Q : R → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hT : T ≤ T') :
    Runs P S S' Q T' := Triple.cost_mono h hT

theorem SpecCopy.mono {I : Inst 2 4 Unit} {C C' : ℕ} (h : SpecCopy I C) (hC : C ≤ C') :
    SpecCopy I C' := fun a rx S h1 h2 => runs_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecDrop.mono {I : Inst 1 4 Unit} {C C' : ℕ} (h : SpecDrop I C) (hC : C ≤ C') :
    SpecDrop I C' := fun a rx S h1 h2 => runs_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecIsZero.mono {I : Inst 1 4 Bool} {C C' : ℕ} (h : SpecIsZero I C) (hC : C ≤ C') :
    SpecIsZero I C' := fun a rx S h1 h2 => runs_mono (h a rx S h1 h2) hC
theorem SpecDec.mono {I : Inst 1 4 Unit} {C C' : ℕ} (h : SpecDec I C) (hC : C ≤ C') :
    SpecDec I C' := fun a rx S h1 h2 => runs_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecInc.mono {I : Inst 1 4 Unit} {C C' : ℕ} (h : SpecInc I C) (hC : C ≤ C') :
    SpecInc I C' := fun a rx S h1 h2 => runs_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecAddNat.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecAddNat I C) (hC : C ≤ C') :
    SpecAddNat I C' := fun a b rx ry S h1 h2 h3 h4 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecShlConst.mono {k : ℕ} {I : Inst 1 4 Unit} {C C' : ℕ} (h : SpecShlConst k I C)
    (hC : C ≤ C') : SpecShlConst k I C' := fun a rx S h1 h2 =>
  runs_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecShrConst.mono {k : ℕ} {I : Inst 1 4 Unit} {C C' : ℕ} (h : SpecShrConst k I C)
    (hC : C ≤ C') : SpecShrConst k I C' := fun a rx S h1 h2 =>
  runs_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecShlVar.mono {I : Inst 2 4 Unit} {C C' : ℕ} (h : SpecShlVar I C) (hC : C ≤ C') :
    SpecShlVar I C' := fun a c rx rc S h1 h2 h3 h4 =>
  runs_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecCmpNat.mono {I : Inst 2 4 Ordering} {C C' : ℕ} (h : SpecCmpNat I C) (hC : C ≤ C') :
    SpecCmpNat I C' := fun a b rx ry S h1 h2 h3 h4 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecAddInt.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecAddInt I C) (hC : C ≤ C') :
    SpecAddInt I C' := fun a b rx ry S h1 h2 h3 h4 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecMul.mono {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} {C C' : ℕ} (h : SpecMul Mul I C)
    (hC : C ≤ C') : SpecMul Mul I C' := fun w a b ra rb S h1 h2 h3 h4 h5 h6 =>
  runs_mono (h w a b ra rb S h1 h2 h3 h4 h5 h6) (Nat.add_le_add (Nat.mul_le_mul_right _ hC) hC)
theorem SpecDivMod.mono {I : Inst 4 6 Unit} {C C' : ℕ} (h : SpecDivMod I C) (hC : C ≤ C') :
    SpecDivMod I C' := fun a b ra rb S h0 h1 h2 h3 h4 =>
  runs_mono (h a b ra rb S h0 h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)
theorem SpecStdChar.mono {neg : Bool} {I : Inst 4 16 Unit} {C C' : ℕ} (h : SpecStdChar neg I C)
    (hC : C ≤ C') : SpecStdChar neg I C' := fun q n d r0 r1 r2 S a1 a2 a3 a4 a5 a6 a7 a8 =>
  runs_mono (h q n d r0 r1 r2 S a1 a2 a3 a4 a5 a6 a7 a8) (Nat.mul_le_mul_right _ hC)
theorem SpecTap.mono {I : Inst 8 16 Unit} {C C' : ℕ} (h : SpecTap I C) (hC : C ≤ C') :
    SpecTap I C' := by
  intro p_work pSub t1 j1 s πZ lnZ r0 r1 r2 r3 r4 r5 r6 S a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6
    e0 e1 e2 e3 e4 e5 e6
  exact runs_mono (h p_work pSub t1 j1 s πZ lnZ r0 r1 r2 r3 r4 r5 r6 S a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
    b3 b4 b5 b6 e0 e1 e2 e3 e4 e5 e6) (Nat.mul_le_mul_right _ hC)
theorem SpecC0C1.mono {I : Inst 5 16 Unit} {C C' : ℕ} (h : SpecC0C1 I C) (hC : C ≤ C') :
    SpecC0C1 I C' := by
  intro p_work pSub r u2 r0 r1 r2 r3 S a1 a2 a3 b0 b1 b2 b3 e0 e1 e2 e3
  exact runs_mono (h p_work pSub r u2 r0 r1 r2 r3 S a1 a2 a3 b0 b1 b2 b3 e0 e1 e2 e3)
    (Nat.mul_le_mul_right _ hC)
theorem SpecColRecip.mono {I : Inst 6 16 Unit} {C C' : ℕ} (h : SpecColRecip I C) (hC : C ≤ C') :
    SpecColRecip I C' := by
  intro H r u2 a c r0 r1 r2 r3 r4 S hd b0 b1 b2 b3 b4 e0 e1 e2 e3 e4
  exact runs_mono (h H r u2 a c r0 r1 r2 r3 r4 S hd b0 b1 b2 b3 b4 e0 e1 e2 e3 e4)
    (Nat.mul_le_mul_right _ hC)
theorem SpecPi.mono {I : Inst 2 16 Unit} {C C' : ℕ} (h : SpecPi I C) (hC : C ≤ C') :
    SpecPi I C' := fun B rB S h1 h2 => runs_mono (h B rB S h1 h2) (Nat.mul_le_mul_right _ hC)
theorem SpecLn2.mono {I : Inst 2 16 Unit} {C C' : ℕ} (h : SpecLn2 I C) (hC : C ≤ C') :
    SpecLn2 I C' := fun B rB S h1 h2 => runs_mono (h B rB S h1 h2) (Nat.mul_le_mul_right _ hC)

/-! ## Host rules -/

variable {a b : ℕ} {σ : Type}

theorem HT.addNat {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAddNat I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sy sz : Loc a b) (hnd : [sx, sy, sz].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B sx = natSyms x ++ rx) (hy : B sy = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sy, sz] dflt l) (Function.update B sz (natSyms (x + y) ++ B sz))
      (C * (bitLen x + bitLen y + 1)) :=
  HT.callI_upd I [sx, sy, sz] dflt hnd rfl hcap l B (.inl 2) _ (hI x y rx ry _ hrx hry hx hy) ρ

theorem HT.incNat {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B s = natSyms x ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x + 1) ++ rx))
      (C * (ones (Computability.encodeNat x) + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

theorem HT.shrConst {k : ℕ} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecShrConst k I C)
    (dflt : Loc a b) (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b)
    (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B s = natSyms x ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x / 2 ^ k) ++ rx)) (C * (k + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

theorem HT.addInt {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAddInt I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sy sz : Loc a b) (hnd : [sx, sy, sz].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℤ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B sx = intSyms x ++ rx) (hy : B sy = intSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sy, sz] dflt l) (Function.update B sz (intSyms (x + y) ++ B sz))
      (C * (bitLen x.natAbs + bitLen y.natAbs + 1)) :=
  HT.callI_upd I [sx, sy, sz] dflt hnd rfl hcap l B (.inl 2) _ (hI x y rx ry _ hrx hry hx hy) ρ

theorem HT.mul {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} {C : ℕ} (hI : SpecMul Mul I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sy sz : Loc a b) (hnd : [sx, sy, sz].Nodup) (hcap : 8 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (w : ℕ) (x y : ℤ) (rx ry : List Sym) (hwx : bitLen x.natAbs ≤ w)
    (hwy : bitLen y.natAbs ≤ w) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B sx = intSyms x ++ rx) (hy : B sy = intSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sy, sz] dflt l) (Function.update B sz (intSyms (x * y) ++ B sz))
      (C * Mul w + C) :=
  HT.callI_upd I [sx, sy, sz] dflt hnd rfl hcap l B (.inl 2) _
    (hI w x y rx ry _ hwx hwy hrx hry hx hy) ρ

theorem HT.stdChar {neg : Bool} {I : Inst 4 16 Unit} {C : ℕ} (hI : SpecStdChar neg I C)
    (dflt : Loc a b) (l : Lens σ I.R) (sq sn sd dst : Loc a b) (hnd : [sq, sn, sd, dst].Nodup)
    (hcap : 16 + 4 ≤ a + b) (B : Loc a b → List Sym) (q num den : ℕ) (r0 r1 r2 : List Sym)
    (hden : 0 < den) (hnum : num ≤ den) (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2)
    (e0 : B sq = natSyms q ++ r0) (e1 : B sn = natSyms num ++ r1) (e2 : B sd = natSyms den ++ r2)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sq, sn, sd, dst] dflt l)
      (Function.update B dst
        (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den neg).1 ++ B dst))
      (C * (q + bitLen den + 1) ^ 4) :=
  HT.callI_upd I [sq, sn, sd, dst] dflt hnd rfl hcap l B (.inl 3) _
    (hI q num den r0 r1 r2 _ hden hnum h0 h1 h2 e0 e1 e2) ρ

theorem HT.tap {I : Inst 8 16 Unit} {C : ℕ} (hI : SpecTap I C) (dflt : Loc a b) (l : Lens σ I.R)
    (s0 s1 s2 s3 s4 s5 s6 dst : Loc a b) (hnd : [s0, s1, s2, s3, s4, s5, s6, dst].Nodup)
    (hcap : 16 + 8 ≤ a + b) (B : Loc a b → List Sym) (p_work pSub t1 j1 s : ℕ)
    (r0 r1 r2 r3 r4 r5 r6 : List Sym) (a1 : 0 < p_work) (a2 : 0 < pSub) (a3 : 0 < t1)
    (a4 : j1 < t1) (a5 : s < 2 * pSub + 1)
    (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2) (b3 : TermOK r3) (b4 : TermOK r4)
    (b5 : TermOK r5) (b6 : TermOK r6)
    (e0 : B s0 = natSyms p_work ++ r0) (e1 : B s1 = natSyms pSub ++ r1)
    (e2 : B s2 = natSyms t1 ++ r2) (e3 : B s3 = natSyms j1 ++ r3) (e4 : B s4 = natSyms s ++ r4)
    (e5 : B s5 = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1 ++ r5)
    (e6 : B s6 = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1 ++ r6)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s0, s1, s2, s3, s4, s5, s6, dst] dflt l)
      (Function.update B dst
        (intSyms (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1 ++ B dst))
      (C * (p_work + pSub + bitLen t1 + 1) ^ 4) :=
  HT.callI_upd I [s0, s1, s2, s3, s4, s5, s6, dst] dflt hnd rfl hcap l B (.inl 7) _
    (hI p_work pSub t1 j1 s _ _ r0 r1 r2 r3 r4 r5 r6 _ a1 a2 a3 a4 a5 rfl rfl b0 b1 b2 b3 b4 b5 b6
      e0 e1 e2 e3 e4 e5 e6) ρ

theorem HT.c0c1 {I : Inst 5 16 Unit} {C : ℕ} (hI : SpecC0C1 I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s0 s1 s2 s3 dst : Loc a b) (hnd : [s0, s1, s2, s3, dst].Nodup)
    (hcap : 16 + 5 ≤ a + b) (B : Loc a b → List Sym) (p_work pSub r u2 : ℕ)
    (r0 r1 r2 r3 : List Sym) (a1 : 0 < p_work) (a2 : 0 < r) (a3 : u2 < r)
    (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2) (b3 : TermOK r3)
    (e0 : B s0 = natSyms p_work ++ r0) (e1 : B s1 = natSyms pSub ++ r1)
    (e2 : B s2 = natSyms r ++ r2) (e3 : B s3 = natSyms u2 ++ r3)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s0, s1, s2, s3, dst] dflt l)
      (Function.update B dst
        (intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.1.1 ++
          intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.2.1 ++ B dst))
      (C * (p_work + pSub + bitLen r + 1) ^ 4) :=
  HT.callI_upd I [s0, s1, s2, s3, dst] dflt hnd rfl hcap l B (.inl 4) _
    (hI p_work pSub r u2 r0 r1 r2 r3 _ a1 a2 a3 b0 b1 b2 b3 e0 e1 e2 e3) ρ

theorem HT.colRecip {I : Inst 6 16 Unit} {C : ℕ} (hI : SpecColRecip I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s0 s1 s2 s3 s4 dst : Loc a b) (hnd : [s0, s1, s2, s3, s4, dst].Nodup)
    (hcap : 16 + 6 ≤ a + b) (B : Loc a b → List Sym) (H r u2 : ℕ) (x z : ℤ)
    (r0 r1 r2 r3 r4 : List Sym) (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 x z)
    (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2) (b3 : TermOK r3) (b4 : TermOK r4)
    (e0 : B s0 = natSyms H ++ r0) (e1 : B s1 = natSyms r ++ r1) (e2 : B s2 = natSyms u2 ++ r2)
    (e3 : B s3 = intSyms x ++ r3) (e4 : B s4 = intSyms z ++ r4)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s0, s1, s2, s3, s4, dst] dflt l)
      (Function.update B dst (intSyms (W7.colRecip H r u2 x z) ++ B dst))
      (C * ((H + 1) * (bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 x z).natAbs + 1) +
        bitLen r + bitLen u2 + bitLen x.natAbs + bitLen z.natAbs + 1)) :=
  HT.callI_upd I [s0, s1, s2, s3, s4, dst] dflt hnd rfl hcap l B (.inl 5) _
    (hI H r u2 x z r0 r1 r2 r3 r4 _ hd b0 b1 b2 b3 b4 e0 e1 e2 e3 e4) ρ

theorem HT.piScaled {I : Inst 2 16 Unit} {C : ℕ} (hI : SpecPi I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sB dst : Loc a b) (hnd : [sB, dst].Nodup) (hcap : 16 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (Bv : ℕ) (rB : List Sym) (hrB : TermOK rB)
    (e0 : B sB = natSyms Bv ++ rB) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sB, dst] dflt l)
      (Function.update B dst (intSyms (IntMul.computablePiScaledWithCost Bv).1 ++ B dst))
      (C * (Bv + 1) ^ 4) :=
  HT.callI_upd I [sB, dst] dflt hnd rfl hcap l B (.inl 1) _ (hI Bv rB _ hrB e0) ρ

theorem HT.log2Scaled {I : Inst 2 16 Unit} {C : ℕ} (hI : SpecLn2 I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sB dst : Loc a b) (hnd : [sB, dst].Nodup) (hcap : 16 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (Bv : ℕ) (rB : List Sym) (hrB : TermOK rB)
    (e0 : B sB = natSyms Bv ++ rB) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sB, dst] dflt l)
      (Function.update B dst (intSyms (IntMul.computableLog2ScaledWithCost Bv).1 ++ B dst))
      (C * (Bv + 1) ^ 4) :=
  HT.callI_upd I [sB, dst] dflt hnd rfl hcap l B (.inl 1) _ (hI Bv rB _ hrB e0) ρ

/-! ## Constants -/

/-- Push the bit list `l` (LSB first) onto `k`: the last bit first, so `l.head` ends on top. -/
def pushBits (k : Loc a b) : List Bool → Prog (Loc a b) (fun _ => Sym) σ
  | [] => .load id
  | x :: l => (pushBits k l).seq (pushS k (Sym.bit x))

theorem pushBits_closed (k : Loc a b) : ∀ l : List Bool, (pushBits (σ := σ) k l).Closed
  | [] => trivial
  | _ :: l => ⟨pushBits_closed k l, trivial⟩

theorem HT.pushBits (k : Loc a b) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (l : List Bool) (B : Loc a b → List Sym),
      HT ρ B (WP.W7k2.pushBits k l) (Function.update B k (l.map Sym.bit ++ B k)) (l.length + 1)
  | [], B => by
    rintro ⟨v, S⟩ hS
    change S = B at hS
    subst hS
    refine ⟨⟨v, S⟩, 1, Eval.load ρ id v S, ?_, le_rfl⟩
    show S = Function.update S k ([] ++ S k)
    simp
  | x :: l, B => by
    refine (HT.seq (HT.pushBits k ρ l B) (HT.pushS k (Sym.bit x) _ ρ)).of_eq ?_ (by simp)
    simp [Function.update_idem]

/-- Push the constant `c` (as `natSyms c`). -/
def pushNat (k : Loc a b) (c : ℕ) : Prog (Loc a b) (fun _ => Sym) σ :=
  pushBits k (Computability.encodeNat c)

theorem HT.pushNat (k : Loc a b) (c : ℕ) (B : Loc a b → List Sym)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W7k2.pushNat k c) (Function.update B k (natSyms c ++ B k)) (bitLen c + 1) :=
  HT.pushBits k ρ _ B

#assert_std_axioms runs_mono SpecCopy.mono SpecDrop.mono SpecIsZero.mono SpecDec.mono SpecInc.mono
  SpecAddNat.mono SpecShlConst.mono SpecShrConst.mono SpecShlVar.mono SpecCmpNat.mono
  SpecAddInt.mono SpecMul.mono SpecDivMod.mono SpecStdChar.mono SpecTap.mono SpecC0C1.mono
  SpecColRecip.mono SpecPi.mono SpecLn2.mono HT.addNat HT.incNat HT.shrConst HT.addInt HT.mul
  HT.stdChar HT.tap HT.c0c1 HT.colRecip HT.piScaled HT.log2Scaled pushBits_closed HT.pushBits
  HT.pushNat

end WP.W7k2
