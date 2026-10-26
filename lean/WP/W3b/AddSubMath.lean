import WP.W3b.Glue

/-!
# WP.W3b.AddSub — signed add and subtract from the unsigned contracts

`addSubProg … flip` computes `z += a + b` (`flip = false`) or `z += a - b` (`flip = true`) on
stacks `x = .inl 0`, `y = .inl 1` (operands, restored), `z = .inl 2`, with 4 shared scratch stacks.
It is parametrized by the unsigned subroutine programs, used only through their contracts:
`W3_addNat` (`Pa`), `W3_subNat` (`Ps`) and `W3_cmpNat` (`Pc`, from the proved `w3_cmpNat`).

1. pop the signs `sa`, `sb`; the effective sign of the second operand is
   `effNeg flip b = xor (b < 0) flip` (for `b = 0, flip = true` this is a "negative zero", which
   the case analysis below tolerates);
2. equal signs: `z += |a| + |b|` (`Pa`), push `sa`;
3. different signs: compare `|a|, |b|` (`Pc`); if `|a| < |b|`: `z += |b| - |a|` (`Ps` with the
   operands swapped), push the effective sign of `b`; else `z += |a| - |b|`, push `sa` if
   `|a| > |b|` and `pos` if equal (zero is `[pos]`);
4. push `sb`, `sa` back.

Cost `≤ (Ca + Cs + Cc + 7)·(|a| + |b| + 1)`.
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## The unsigned specifications (bodies of the contracts) -/

/-- Body of `W3_addNat`. -/
def AddSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 3 m) (fun _ => Sym) R) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_subNat`. -/
def SubSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 3 m) (fun _ => Sym) R) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_cmpNat`. -/
def CmpSpec {m : ℕ} {R : Type} (C : ℕ) (obs : R → Ordering) (P : Prog (Loc 2 m) (fun _ => Sym) R) :
    Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S S (fun r => obs r = Lib.ordOf a b) (C * (bitLen a + bitLen b + 1))

/-! ## Sign-magnitude arithmetic -/

/-- The effective second operand: `b` (add) or `-b` (subtract). -/
def effB (flip : Bool) (b : ℤ) : ℤ := if flip then -b else b

/-- The machine's sign flag for the effective second operand. -/
def effNeg (flip : Bool) (b : ℤ) : Bool := xor (decide (b < 0)) flip

theorem effB_natAbs (flip : Bool) (b : ℤ) : (effB flip b).natAbs = b.natAbs := by
  cases flip <;> simp [effB]

theorem effNeg_spec (flip : Bool) (b : ℤ) (hb : effB flip b ≠ 0) :
    effNeg flip b = true ↔ effB flip b < 0 := by
  unfold effNeg effB at *
  by_cases h : b < 0 <;> cases flip <;> simp [h] at hb ⊢ <;> omega

theorem ordOf_eq_lt {x y : ℕ} (h : Lib.ordOf x y = .lt) : x < y := by
  unfold Lib.ordOf at h
  by_cases hxy : x < y
  · exact hxy
  · rw [if_neg hxy] at h
    by_cases hxy' : x = y
    · rw [if_pos hxy'] at h
      cases h
    · rw [if_neg hxy'] at h
      cases h

theorem ordOf_ne_lt {x y : ℕ} (h : Lib.ordOf x y ≠ .lt) : y ≤ x := by
  by_contra hc
  apply h
  unfold Lib.ordOf
  rw [if_pos (show x < y by omega)]

theorem arith_same (a c : ℤ) (nc : Bool) (hnc : c ≠ 0 → (nc = true ↔ c < 0))
    (h : decide (a < 0) = nc) :
    (a + c).natAbs = a.natAbs + c.natAbs ∧ sgnSym (a + c) = sgnSym a := by
  by_cases hc : c = 0
  · subst hc
    simp
  · have h2 := hnc hc
    cases nc
    · have ha : ¬ a < 0 := by simpa using h
      have hc' : ¬ c < 0 := by simpa using h2
      exact ⟨by omega, sgnSym_congr ⟨fun _ => by omega, fun _ => by omega⟩⟩
    · have ha : a < 0 := by simpa using h
      have hc' : c < 0 := by simpa using h2
      exact ⟨by omega, sgnSym_congr ⟨fun _ => by omega, fun _ => by omega⟩⟩

theorem arith_ge (a c : ℤ) (nc : Bool) (hnc : c ≠ 0 → (nc = true ↔ c < 0))
    (h : decide (a < 0) ≠ nc) (hle : c.natAbs ≤ a.natAbs) :
    (a + c).natAbs = a.natAbs - c.natAbs ∧
      sgnSym (a + c) = (if Lib.ordOf a.natAbs c.natAbs = .gt then sgnSym a else .pos) := by
  have hab : (a + c).natAbs = a.natAbs - c.natAbs := by
    by_cases hc : c = 0
    · subst hc
      simp
    · have h2 := hnc hc
      cases nc
      · have ha : a < 0 := by simpa using h
        have hc' : ¬ c < 0 := by simpa using h2
        omega
      · have ha : ¬ a < 0 := by simpa using h
        have hc' : c < 0 := by simpa using h2
        omega
  refine ⟨hab, ?_⟩
  by_cases hlt : c.natAbs < a.natAbs
  · have hg : Lib.ordOf a.natAbs c.natAbs = .gt := by
      unfold Lib.ordOf
      rw [if_neg (show ¬ a.natAbs < c.natAbs by omega), if_neg (show a.natAbs ≠ c.natAbs by omega)]
    rw [if_pos hg]
    apply sgnSym_congr
    by_cases hc : c = 0
    · subst hc
      simp
    · have h2 := hnc hc
      cases nc
      · have ha : a < 0 := by simpa using h
        have hc' : ¬ c < 0 := by simpa using h2
        exact ⟨fun _ => by omega, fun _ => by omega⟩
      · have ha : ¬ a < 0 := by simpa using h
        have hc' : c < 0 := by simpa using h2
        exact ⟨fun _ => by omega, fun _ => by omega⟩
  · have he : Lib.ordOf a.natAbs c.natAbs = .eq := by
      unfold Lib.ordOf
      rw [if_neg (show ¬ a.natAbs < c.natAbs by omega), if_pos (show a.natAbs = c.natAbs by omega)]
    rw [if_neg (show ¬ Lib.ordOf a.natAbs c.natAbs = .gt by rw [he]; decide)]
    apply sgnSym_of_nonneg
    omega

theorem arith_lt (a c : ℤ) (nc : Bool) (hnc : c ≠ 0 → (nc = true ↔ c < 0))
    (h : decide (a < 0) ≠ nc) (hlt : a.natAbs < c.natAbs) :
    (a + c).natAbs = c.natAbs - a.natAbs ∧ sgnSym (a + c) = (if nc then .neg else .pos) := by
  have hc : c ≠ 0 := by omega
  have h2 := hnc hc
  cases nc
  · have ha : a < 0 := by simpa using h
    have hc' : ¬ c < 0 := by simpa using h2
    exact ⟨by omega, sgnSym_of_nonneg (by omega)⟩
  · have ha : ¬ a < 0 := by simpa using h
    have hc' : c < 0 := by simpa using h2
    exact ⟨by omega, sgnSym_of_neg (by omega)⟩

theorem intSyms_eq_cons {r : ℤ} {s : Sym} {m : ℕ} (hs : sgnSym r = s) (hm : r.natAbs = m) :
    intSyms r = s :: natSyms m := by
  rw [intSyms, hs, hm]

#assert_std_axioms effB_natAbs effNeg_spec ordOf_eq_lt ordOf_ne_lt arith_same arith_ge arith_lt
  intSyms_eq_cons

end TMFw.W3b
