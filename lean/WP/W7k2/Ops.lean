import WP.W7k2.Call

/-!
# WP.W7k2.Ops — host-level rules for the W3 / W6a operations

For each frozen machine contract used by W7k2, `Spec*` restates the contract body for one extracted
instance (`exists_inst`), and `HT.*` is the host-level rule: call the instance on chosen host stacks
and get the exact host update. The rules are generic in the host `Loc a b`; the capacity premise
`cap + n ≤ a + b` leaves room for the callee's scratch stacks on free host stacks.

The `Spec*` bodies are verbatim the bodies of `W3_copyNat`, `W3_dropNat`, `W3_shlConst`,
`W3_shlVar`, `W3_cmpNat`, `W6a_divModNat` (Contracts/Machine/{W3,W6a}.lean), so
`exists_inst h` produces them by definitional unfolding.
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-! ## Instance specifications (contract bodies) -/

/-- Body of `W3_copyNat`. -/
def SpecCopy (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 1) (natSyms a ++ S (.inl 1))) (fun _ => True)
      (C * (bitLen a + 1))

/-- Body of `W3_dropNat`. -/
def SpecDrop (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) rx) (fun _ => True) (C * (bitLen a + 1))

/-- Body of `W3_shlConst` at shift `k`. -/
def SpecShlConst (k : ℕ) (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a * 2 ^ k) ++ rx)) (fun _ => True)
      (C * (k + 1))

/-- Body of `W3_shlVar`. -/
def SpecShlVar (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
      (C * (c + bitLen c + 1))

/-- Body of `W3_cmpNat`. -/
def SpecCmpNat (I : Inst 2 4 Ordering) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S S (fun r => I.obs r = Lib.ordOf a b) (C * (bitLen a + bitLen b + 1))

/-- Body of `W6a_divModNat`. -/
def SpecDivMod (I : Inst 4 6 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 I.m → List Sym), 0 < b → TermOK ra → TermOK rb →
    S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
    Runs I.P S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
        (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
      (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1))

/-! ## Host-level rules -/

variable {a b : ℕ} {σ : Type}

/-- `dst += x` (copy). -/
theorem HT.copyNat {I : Inst 2 4 Unit} {C : ℕ} (hI : SpecCopy I C) (dflt : Loc a b)
    (l : Lens σ I.R) (src dst : Loc a b) (hnd : [src, dst].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B src = natSyms x ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [src, dst] dflt l) (Function.update B dst (natSyms x ++ B dst))
      (C * (bitLen x + 1)) :=
  HT.callI_upd I [src, dst] dflt hnd rfl hcap l B (.inl 1) _ (hI x rx _ hrx hB) ρ

/-- Drop the number on top of `k`. -/
theorem HT.dropNat {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecDrop I C) (dflt : Loc a b)
    (l : Lens σ I.R) (k : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B k = natSyms x ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [k] dflt l) (Function.update B k rx) (C * (bitLen x + 1)) :=
  HT.callI_upd I [k] dflt (List.nodup_singleton k) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-- Shift left by a constant, in place. -/
theorem HT.shlConst {k : ℕ} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecShlConst k I C)
    (dflt : Loc a b) (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b)
    (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B s = natSyms x ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x * 2 ^ k) ++ rx)) (C * (k + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-- Shift left by a counter, in place. -/
theorem HT.shlVar {I : Inst 2 4 Unit} {C : ℕ} (hI : SpecShlVar I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s c : Loc a b) (hnd : [s, c].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hB : B s = natSyms x ++ rx) (hC : B c = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s, c] dflt l) (Function.update B s (natSyms (x * 2 ^ y) ++ rx))
      (C * (y + bitLen y + 1)) :=
  HT.callI_upd I [s, c] dflt hnd rfl hcap l B (.inl 0) _ (hI x y rx ry _ hrx hry hB hC) ρ

/-- Compare, then branch on the result. -/
theorem HT.cmpNat_ite {I : Inst 2 4 Ordering} {C : ℕ} (hI : SpecCmpNat I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y : Loc a b) (hnd : [x, y].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B B' : Loc a b → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (f : Ordering → Bool)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    {T₁ T₂ : ℕ} (hp : f (Lib.ordOf u v) = true → HT ρ B p B' T₁)
    (hq : f (Lib.ordOf u v) = false → HT ρ B q B' T₂) :
    HT ρ B ((callI I [x, y] dflt l).seq (.ite (fun s => f (I.obs (l.get s))) p q)) B'
      (C * (bitLen u + bitLen v + 1) + (max T₁ T₂ + 1)) :=
  HT.callI_test I [x, y] dflt hnd rfl hcap l B B' f (Lib.ordOf u v)
    (hI u v ru rv _ hru hrv hx hy) p q ρ hp hq

/-- Long division: `q += x / y`, `r += x % y`. -/
theorem HT.divModNat {I : Inst 4 6 Unit} {C : ℕ} (hI : SpecDivMod I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sy sq sr : Loc a b) (hnd : [sx, sy, sq, sr].Nodup) (hcap : 6 + 4 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hy0 : 0 < y) (hrx : TermOK rx)
    (hry : TermOK ry) (hx : B sx = natSyms x ++ rx) (hy : B sy = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sy, sq, sr] dflt l)
      (Function.update (Function.update B sq (natSyms (x / y) ++ B sq)) sr
        (natSyms (x % y) ++ B sr))
      (C * (bitLen x * bitLen y + bitLen x + bitLen y + 1)) :=
  HT.callI_upd2 I [sx, sy, sq, sr] dflt hnd rfl hcap l B (.inl 2) (.inl 3) _ _
    (hI x y rx ry _ hy0 hrx hry hx hy) ρ

#assert_std_axioms HT.copyNat HT.dropNat HT.shlConst HT.shlVar HT.cmpNat_ite HT.divModNat

end WP.W7k2
