import WP.W9fOps.Glue

/-!
# WP.W9fOps.Shape — the statement shape consumed by W9f, and shared helpers

`W9fBinOp f`: a closed program over `Loc 3 m` (`m ≤ 16`, finite nonempty registers) with
`x = .inl 0 ↦ a`, `y = .inl 1 ↦ b` (both restored) and `z = .inl 2 += f a b`, cost
`C·(|a| + |b| + 1)` (bit lengths of the magnitudes). `W9fShiftOp f`: the same with cost
`C·(|a| + |b| + b.natAbs + 1)` (the value `|b|` pays for a shift by `|b|` positions). Shapes and
costs matching the `WP.W9fF.Kit` / `WP.W9fN.Kit` operation interface.

Helpers: the embeddings `f02` (copy `x → z`), `f21` (number `z`, counter `y`), `f2` (in place on
`z`) of the callees' named stacks; `lensId`; `bitLen_mono`; `Int.shiftRight` on non-negative and
negative arguments.
-/

namespace WP.W9fOps

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- W9f's binary operation on signed numbers (x, y restored; z receives `f a b`), cost linear
in the bit lengths (used for `a >>> b.natAbs` and `[a ≤ b]`). -/
def W9fBinOp (f : ℤ → ℤ → ℤ) : Prop :=
  ∃ C : ℕ, ∃ (m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
    m ≤ 16 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧
    ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      TermOK ra → TermOK rb → TermOK (S (.inl 2)) →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (f a b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- As `W9fBinOp`, with the shift amount `b.natAbs` in the cost (used for `a * 2 ^ b.natAbs`). -/
def W9fShiftOp (f : ℤ → ℤ → ℤ) : Prop :=
  ∃ C : ℕ, ∃ (m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
    m ≤ 16 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧
    ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      TermOK ra → TermOK rb → TermOK (S (.inl 2)) →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (f a b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a.natAbs + bitLen b.natAbs + b.natAbs + 1))

/-- The identity lens. -/
def lensId (R : Type) : Lens R R where
  get v := v
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Callee stacks `x, y ↦ x, z` (copy `x` onto `z`). -/
def f02 (i : Fin 2) : Fin 3 := if i = 0 then 0 else 2

/-- Callee stacks `number, counter ↦ z, y`. -/
def f21 (i : Fin 2) : Fin 3 := if i = 0 then 2 else 1

/-- Callee stack `x ↦ z` (in place on `z`). -/
def f2 (_ : Fin 1) : Fin 3 := 2

/-- Callee stacks `x, y ↦ x, y` (comparator). -/
def f23 (i : Fin 2) : Fin 3 := if i = 0 then 0 else 1

@[simp] theorem emb_inl {n n' m : ℕ} (f : Fin n → Fin n') (hm : m ≤ 4) (i : Fin n) :
    emb f hm (.inl i) = .inl (f i) := rfl

@[simp] theorem f02_zero : f02 0 = 0 := rfl
@[simp] theorem f02_one : f02 1 = 2 := rfl
@[simp] theorem f21_zero : f21 0 = 2 := rfl
@[simp] theorem f21_one : f21 1 = 1 := rfl
@[simp] theorem f2_zero : f2 0 = 2 := rfl
@[simp] theorem f23_zero : f23 0 = 0 := rfl
@[simp] theorem f23_one : f23 1 = 1 := rfl

theorem f02_injective : Function.Injective f02 := by
  unfold Function.Injective
  decide

theorem f21_injective : Function.Injective f21 := by
  unfold Function.Injective
  decide

theorem f2_injective : Function.Injective f2 := by
  unfold Function.Injective
  decide

theorem f23_injective : Function.Injective f23 := by
  unfold Function.Injective
  decide

/-- Bit length is monotone. -/
theorem bitLen_mono {x y : ℕ} (h : x ≤ y) : bitLen x ≤ bitLen y := by
  by_contra hc
  have hc' : bitLen y < bitLen x := Nat.lt_of_not_le hc
  have hx : encodeNat x ≠ [] := by
    intro he
    simp [bitLen, he] at hc'
  have h1 := two_pow_le_bitsVal (encodeNat x) (normBits_encodeNat x) hx
  have h2 := bitsVal_lt_two_pow (encodeNat y)
  rw [bitsVal_encodeNat] at h1 h2
  have h3 : 2 ^ (encodeNat y).length ≤ 2 ^ ((encodeNat x).length - 1) :=
    Nat.pow_le_pow_right (by omega) (by simp only [bitLen] at hc'; omega)
  omega

theorem shiftRight_ofNat (n k : ℕ) : (n : ℤ) >>> k = ((n / 2 ^ k : ℕ) : ℤ) := by
  show Int.shiftRight (Int.ofNat n) k = _
  rw [Int.shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem shiftRight_negSucc (n k : ℕ) :
    Int.negSucc n >>> k = -(((n / 2 ^ k : ℕ) : ℤ) + 1) := by
  show Int.shiftRight (Int.negSucc n) k = _
  rw [Int.shiftRight, Nat.shiftRight_eq_div_pow, Int.negSucc_eq]

/-- `cmpZ a b ≠ gt` iff `a ≤ b`. -/
theorem cmpZ_ne_gt_iff (a b : ℤ) : cmpZ a b ≠ .gt ↔ a ≤ b := by
  unfold cmpZ
  split_ifs with h1 h2
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    omega
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    omega
  · simp only [ne_eq, not_true_eq_false, false_iff, not_le]
    omega

#assert_std_axioms f02_injective f21_injective f2_injective f23_injective bitLen_mono shiftRight_ofNat
  shiftRight_negSucc cmpZ_ne_gt_iff

/-! ## Bodies of the W3 contracts used here -/

/-- Body of `W3_copyNat` (`y += a`). -/
def CopySpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 2 m) (fun _ => Sym) R) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 2 m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs P S (Function.update S (.inl 1) (natSyms a ++ S (.inl 1))) (fun _ => True)
      (C * (bitLen a + 1))

/-- Body of `W3_decNat` (`a + 1 ↦ a` in place). -/
def DecSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 1 m) (fun _ => Sym) R) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (zerosLead (encodeNat (a + 1)) + 1))

/-- Body of `W3_incNat` (`a ↦ a + 1` in place). -/
def IncSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 1 m) (fun _ => Sym) R) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (encodeNat a) + 1))

/-- Body of `W3_shrVar` (`a ↦ a / 2^c` in place, counter restored). -/
def ShrSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 2 m) (fun _ => Sym) R) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_shlVar` (`a ↦ a·2^c` in place, counter restored). -/
def ShlSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 2 m) (fun _ => Sym) R) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs P S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
      (C * (c + bitLen c + 1))

end WP.W9fOps
