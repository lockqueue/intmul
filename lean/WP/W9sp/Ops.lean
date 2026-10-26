import WP.W9sp.Host

/-!
# WP.W9sp.Ops — instance specifications and host-level call rules

`Spec*` restates, for one extracted instance (`exists_inst`), the body of a frozen machine contract
not already restated in `WP.W7k2.Ops`/`WP.W7k2.Loops` (verbatim, so `exists_inst h` produces them by
definitional unfolding). `HT.*` is the host rule: call the instance on chosen host stacks and get the
exact host update (`HT.callI_upd`, `HT.callI_upd2`). `*.mono` raises the cost constant, so that one
constant serves every instance of a kernel.

Adapted from `WP.W9h.Ops` for `W9_splitPack`.
-/

namespace WP.W9sp

open TMFw TMFw.Contracts WP.W7k2

/-! ## Instance specifications (contract bodies) -/

/-- Body of `W3_isZeroNat`. -/
def SpecIsZero (I : Inst 1 4 Bool) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx → Runs I.P S S (fun r => I.obs r = decide (a = 0)) C

/-- Body of `W3_decNat`. -/
def SpecDec (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (zerosLead (Computability.encodeNat (a + 1)) + 1))

/-- Body of `W3_addNat`. -/
def SpecAdd (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_splitAt`. -/
def SpecSplit (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx))
        (.inl 2) (natSyms (a % 2 ^ c) ++ S (.inl 2))) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_concatAt`. -/
def SpecConcat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (hi lo c : ℕ) (rx rc ry : List Sym) (S : Loc 3 I.m → List Sym),
    TermOK rx → TermOK rc → TermOK ry → lo < 2 ^ c →
    S (.inl 0) = natSyms hi ++ rx → S (.inl 1) = natSyms c ++ rc →
    S (.inl 2) = natSyms lo ++ ry →
    Runs I.P S (Function.update (Function.update S (.inl 0) (natSyms (lo + hi * 2 ^ c) ++ rx))
        (.inl 2) ry) (fun _ => True)
      (C * (c + bitLen c + 1))

/-! ## Raising the cost constant -/

section Mono

variable {C C' : ℕ}

theorem SpecCopy.mono {I : Inst 2 4 Unit} (h : SpecCopy I C) (hC : C ≤ C') : SpecCopy I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecDrop.mono {I : Inst 1 4 Unit} (h : SpecDrop I C) (hC : C ≤ C') : SpecDrop I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecShlConst.mono {k : ℕ} {I : Inst 1 4 Unit} (h : SpecShlConst k I C) (hC : C ≤ C') :
    SpecShlConst k I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecShlVar.mono {I : Inst 2 4 Unit} (h : SpecShlVar I C) (hC : C ≤ C') : SpecShlVar I C' :=
  fun a c rx rc S h1 h2 h3 h4 => Triple.cost_mono (h a c rx rc S h1 h2 h3 h4)
    (Nat.mul_le_mul_right _ hC)

theorem SpecIsZero.mono {I : Inst 1 4 Bool} (h : SpecIsZero I C) (hC : C ≤ C') : SpecIsZero I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) hC

theorem SpecDec.mono {I : Inst 1 4 Unit} (h : SpecDec I C) (hC : C ≤ C') : SpecDec I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecAdd.mono {I : Inst 3 4 Unit} (h : SpecAdd I C) (hC : C ≤ C') : SpecAdd I C' :=
  fun a b rx ry S h1 h2 h3 h4 => Triple.cost_mono (h a b rx ry S h1 h2 h3 h4)
    (Nat.mul_le_mul_right _ hC)

theorem SpecSplit.mono {I : Inst 3 4 Unit} (h : SpecSplit I C) (hC : C ≤ C') : SpecSplit I C' :=
  fun a c rx rc S h1 h2 h3 h4 => Triple.cost_mono (h a c rx rc S h1 h2 h3 h4)
    (Nat.mul_le_mul_right _ hC)

theorem SpecConcat.mono {I : Inst 3 4 Unit} (h : SpecConcat I C) (hC : C ≤ C') :
    SpecConcat I C' :=
  fun hi lo c rx rc ry S h1 h2 h3 h4 h5 h6 h7 =>
    Triple.cost_mono (h hi lo c rx rc ry S h1 h2 h3 h4 h5 h6 h7) (Nat.mul_le_mul_right _ hC)

end Mono

/-! ## Host-level rules -/

variable {a b : ℕ} {σ : Type}

/-- `z += x + y`. -/
theorem HT.addNat {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAdd I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, y, z] dflt l) (Function.update B z (natSyms (u + v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.callI_upd I [x, y, z] dflt hnd rfl hcap l B (.inl 2) _ (hI u v ru rv _ hru hrv hx hy) ρ

/-- `x ↦ x / 2^c`, `y += x % 2^c`. -/
theorem HT.splitAt {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecSplit I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x c y : Loc a b) (hnd : [x, c, y].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u w : ℕ) (rx rc : List Sym) (hrx : TermOK rx) (hrc : TermOK rc)
    (hx : B x = natSyms u ++ rx) (hc : B c = natSyms w ++ rc)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, c, y] dflt l)
      (Function.update (Function.update B x (natSyms (u / 2 ^ w) ++ rx)) y
        (natSyms (u % 2 ^ w) ++ B y))
      (C * (min w (bitLen u) + bitLen w + 1)) :=
  HT.callI_upd2 I [x, c, y] dflt hnd rfl hcap l B (.inl 0) (.inl 2) _ _
    (hI u w rx rc _ hrx hrc hx hc) ρ

/-- `x ↦ lo + x·2^c`, `lo` consumed from `y`. -/
theorem HT.concatAt {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecConcat I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x c y : Loc a b) (hnd : [x, c, y].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (hi lo w : ℕ) (rx rc ry : List Sym) (hrx : TermOK rx)
    (hrc : TermOK rc) (hry : TermOK ry) (hlo : lo < 2 ^ w) (hx : B x = natSyms hi ++ rx)
    (hc : B c = natSyms w ++ rc) (hy : B y = natSyms lo ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, c, y] dflt l)
      (Function.update (Function.update B x (natSyms (lo + hi * 2 ^ w) ++ rx)) y ry)
      (C * (w + bitLen w + 1)) :=
  HT.callI_upd2 I [x, c, y] dflt hnd rfl hcap l B (.inl 0) (.inl 2) _ _
    (hI hi lo w rx rc ry _ hrx hrc hry hlo hx hc hy) ρ

/-- Decrement in place. -/
theorem HT.decNat {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecDec I C) (dflt : Loc a b)
    (l : Lens σ I.R) (k : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (u : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B k = natSyms (u + 1) ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [k] dflt l) (Function.update B k (natSyms u ++ rx))
      (C * (zerosLead (Computability.encodeNat (u + 1)) + 1)) :=
  HT.callI_upd I [k] dflt (List.nodup_singleton k) rfl hcap l B (.inl 0) _ (hI u rx _ hrx hB) ρ

#assert_std_axioms SpecCopy.mono SpecDrop.mono SpecShlConst.mono SpecShlVar.mono SpecIsZero.mono
  SpecDec.mono SpecAdd.mono SpecSplit.mono SpecConcat.mono HT.addNat HT.splitAt HT.concatAt
  HT.decNat

end WP.W9sp
