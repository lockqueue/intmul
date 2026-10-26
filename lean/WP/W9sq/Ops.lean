import WP.W9sq.Host

/-!
# WP.W9sq.Ops — instance specifications, host call rules, and the signed-number macros

`Spec*` restates, for one extracted instance (`exists_inst`), the body of a frozen contract
(verbatim, so `exists_inst h` produces it by definitional unfolding): `W5_mulAt`, `W3_addInt`,
`W3_subInt`, `W3_addNat`, `W3_shrVar`, `W3_incNat`, `W3_decNat`, `W3_attachSign`. `SpecCopy`,
`SpecDrop`, `SpecShlVar` and their rules come from `WP.W7k2.Ops`.

Macros on signed numbers (`intSyms z ++ r`, `TermOK r`):
* `xferDup src t d1 d2`: move `z` from `src` to both `d1` and `d2` (raw moves via the temporary
  `t`, one `copyNat`); the terminator stays on `src`;
* `dropInt k`: drop `z` (pop the sign, `dropNat`);
* `emitInt src dst`: move `z` symbol by symbol onto `dst`, i.e. push `(intSyms z).reverse`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Instance specifications (contract bodies) -/

/-- Body of `W5_mulAt Mul`. -/
def SpecMul (Mul : ℕ → ℕ) (I : Inst 3 8 Unit) (C : ℕ) : Prop :=
  ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym),
    bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
    S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
      (C * Mul w + C)

/-- Body of `W3_addInt`. -/
def SpecAddInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W3_subInt`. -/
def SpecSubInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W3_addNat`. -/
def SpecAddNat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_shrVar`. -/
def SpecShrVar (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_incNat`. -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (Computability.encodeNat a) + 1))

/-- Body of `W3_decNat`. -/
def SpecDecr (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (zerosLead (Computability.encodeNat (a + 1)) + 1))

/-- Body of `W3_attachSign` at the compile-time sign `isNeg`. -/
def SpecAttach (isNeg : Bool) (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0)
        (intSyms (if isNeg then -(a : ℤ) else (a : ℤ)) ++ rx)) (fun _ => True) C

/-! ## Host-level rules -/

variable {a b : ℕ} {σ : Type}

/-- `z += x · y` (declared width `w`). -/
theorem HT.mul {Mul : ℕ → ℕ} {I : Inst 3 8 Unit} {C : ℕ} (hI : SpecMul Mul I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 8 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (w : ℕ) (u v : ℤ) (ru rv : List Sym) (hu : bitLen u.natAbs ≤ w)
    (hv : bitLen v.natAbs ≤ w) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, y, z] dflt l) (Function.update B z (intSyms (u * v) ++ B z))
      (C * Mul w + C) :=
  HT.callI_upd I [x, y, z] dflt hnd rfl hcap l B (.inl 2) _
    (hI w u v ru rv _ hu hv hru hrv hx hy) ρ

/-- `z += x + y` (signed). -/
theorem HT.addInt {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAddInt I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, y, z] dflt l) (Function.update B z (intSyms (u + v) ++ B z))
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1)) :=
  HT.callI_upd I [x, y, z] dflt hnd rfl hcap l B (.inl 2) _ (hI u v ru rv _ hru hrv hx hy) ρ

/-- `z += x − y` (signed). -/
theorem HT.subInt {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecSubInt I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, y, z] dflt l) (Function.update B z (intSyms (u - v) ++ B z))
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1)) :=
  HT.callI_upd I [x, y, z] dflt hnd rfl hcap l B (.inl 2) _ (hI u v ru rv _ hru hrv hx hy) ρ

/-- `z += x + y` (unsigned). -/
theorem HT.addNat {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAddNat I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, y, z] dflt l) (Function.update B z (natSyms (u + v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.callI_upd I [x, y, z] dflt hnd rfl hcap l B (.inl 2) _ (hI u v ru rv _ hru hrv hx hy) ρ

/-- `x := x / 2^c`, in place. -/
theorem HT.shrVar {I : Inst 2 4 Unit} {C : ℕ} (hI : SpecShrVar I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s c : Loc a b) (hnd : [s, c].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hB : B s = natSyms x ++ rx) (hC : B c = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s, c] dflt l) (Function.update B s (natSyms (x / 2 ^ y) ++ rx))
      (C * (min y (bitLen x) + bitLen y + 1)) :=
  HT.callI_upd I [s, c] dflt hnd rfl hcap l B (.inl 0) _ (hI x y rx ry _ hrx hry hB hC) ρ

/-- `x := x + 1`, in place. -/
theorem HT.inc {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B s = natSyms x ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x + 1) ++ rx))
      (C * (ones (Computability.encodeNat x) + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-- `x + 1 ↦ x`, in place. -/
theorem HT.dec {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecDecr I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B s = natSyms (x + 1) ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms x ++ rx))
      (C * (zerosLead (Computability.encodeNat (x + 1)) + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-- Attach the compile-time sign `isNeg` to the natural on `s` (zero stays `pos`). -/
theorem HT.attach {isNeg : Bool} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecAttach isNeg I C)
    (dflt : Loc a b) (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b)
    (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B s = natSyms x ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l)
      (Function.update B s (intSyms (if isNeg then -(x : ℤ) else (x : ℤ)) ++ rx)) C :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-! ## Signed-number macros -/

theorem termOK_sgn (z : ℤ) (l : List Sym) : TermOK (sgnSym z :: l) := by
  unfold sgnSym
  split_ifs <;> exact TermOK.cons rfl l

/-- Move a signed number from `src` to `d1` and `d2` (via the temporary `t`). -/
def xferDup (lS : Lens σ (Option Sym)) (I : Inst 2 4 Unit) (lc : Lens σ I.R)
    (dflt src t d1 d2 : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (moveTop lS src t).seq <| (moveBlk lS src t).seq <| (moveBlk lS t d1).seq <|
    (callI I [d1, d2] dflt lc).seq (dupTop lS t d1 d2)

theorem xferDup_closed (lS : Lens σ (Option Sym)) (I : Inst 2 4 Unit) (lc : Lens σ I.R)
    (dflt src t d1 d2 : Loc a b) : (xferDup lS I lc dflt src t d1 d2).Closed :=
  ⟨moveTop_closed _ _ _, moveBlk_closed _ _ _, moveBlk_closed _ _ _, callI_closed _ _ _ _,
    dupTop_closed _ _ _ _⟩

theorem HT.xferDup (lS : Lens σ (Option Sym)) {I : Inst 2 4 Unit} {C : ℕ} (hI : SpecCopy I C)
    (lc : Lens σ I.R) (dflt : Loc a b) {src t d1 d2 : Loc a b} (hst : src ≠ t) (hs1 : src ≠ d1)
    (hs2 : src ≠ d2) (ht1 : t ≠ d1) (ht2 : t ≠ d2) (h12 : d1 ≠ d2) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (z : ℤ) (y : Sym) (r : List Sym) (hy : y.isBit = false)
    (hB : B src = intSyms z ++ y :: r) (hd1 : TermOK (B d1)) :
    HT [] B (xferDup lS I lc dflt src t d1 d2)
      (Function.update (Function.update (Function.update B src (y :: r)) d1 (intSyms z ++ B d1))
        d2 (intSyms z ++ B d2))
      (C * (bitLen z.natAbs + 1) + 6 * bitLen z.natAbs + 13) := by
  refine (HT.seq (HT.moveTop lS hst B (sgnSym z) (natSyms z.natAbs ++ y :: r) (by rw [hB]; rfl)) <|
    HT.seq (HT.moveBlk lS hst _ (Computability.encodeNat z.natAbs) (y :: r) (TermOK.cons hy r) ?_) <|
    HT.seq (HT.moveBlk lS ht1 _ (Computability.encodeNat z.natAbs).reverse (sgnSym z :: B t)
      (termOK_sgn z _) ?_) <|
    HT.seq (HT.copyNat hI dflt lc d1 d2 (by simp [h12]) hcap _ z.natAbs (B d1) hd1 ?_ []) <|
    HT.dupTop lS ht1 ht2 h12 _ (sgnSym z) (B t) ?_).of_eq ?_ ?_
  · simp [hst, natSyms]
  · simp
  · simp [Ne.symm ht1, Ne.symm hs1, natSyms]
  · simp [Function.update_apply, ht1, ht2]
  · funext k
    simp only [Function.update_apply, intSyms, natSyms, List.reverse_reverse, List.cons_append]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, bitLen]
    omega

/-- Drop the signed number on top of `k` (its terminator stays). -/
def dropInt (I : Inst 1 4 Unit) (ld : Lens σ I.R) (dflt k : Loc a b) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  (popS k).seq (callI I [k] dflt ld)

theorem dropInt_closed (I : Inst 1 4 Unit) (ld : Lens σ I.R) (dflt k : Loc a b) :
    (dropInt I ld dflt k).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem HT.dropInt {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecDrop I C) (ld : Lens σ I.R)
    (dflt k : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (z : ℤ) (r : List Sym)
    (hr : TermOK r) (hB : B k = intSyms z ++ r) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (dropInt I ld dflt k) (Function.update B k r) (1 + C * (bitLen z.natAbs + 1)) := by
  refine (HT.seq (HT.popS k B (sgnSym z) (natSyms z.natAbs ++ r) (by rw [hB]; rfl) ρ)
    (HT.dropNat hI dflt ld k hcap _ z.natAbs r hr ?_ ρ)).of_eq ?_ le_rfl
  · simp
  · rw [Function.update_idem]

/-- Move the signed number on `src` symbol by symbol onto `dst`. -/
def emitInt (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (moveTop lS src dst).seq (moveBlk lS src dst)

theorem emitInt_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) :
    (emitInt lS src dst).Closed := ⟨moveTop_closed _ _ _, moveBlk_closed _ _ _⟩

theorem HT.emitInt (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (z : ℤ) (r : List Sym) (hr : TermOK r)
    (hB : B src = intSyms z ++ r) :
    HT [] B (emitInt lS src dst)
      (Function.update (Function.update B src r) dst ((intSyms z).reverse ++ B dst))
      (3 * bitLen z.natAbs + 6) := by
  refine (HT.seq (HT.moveTop lS hne B (sgnSym z) (natSyms z.natAbs ++ r) (by rw [hB]; rfl))
    (HT.moveBlk lS hne _ (Computability.encodeNat z.natAbs) r hr ?_)).of_eq ?_ ?_
  · simp [hne, natSyms]
  · funext k
    simp only [Function.update_apply, intSyms, natSyms, List.reverse_cons, List.map_reverse,
      List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all
  · simp only [bitLen]
    omega

#assert_std_axioms HT.mul HT.addInt HT.subInt HT.addNat HT.shrVar HT.inc HT.dec HT.attach
  termOK_sgn xferDup_closed HT.xferDup dropInt_closed HT.dropInt emitInt_closed HT.emitInt

end WP.W9sq
