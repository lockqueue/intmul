import WP.W9g.Loop
import WP.W9g.Pure

/-!
# WP.W9g.EntryLoops — loops over blocks of entries (generic in the stack type)

* `notSym s`: the loop test "the top symbol is not `s`". A block of entries is followed by a
  terminator symbol `term` (`mark` on private stacks, `symD` between FFT blocks); entries start
  with a sign symbol, so the test passes on every entry and fails on the terminator.
* `moveAll src dst t term`: move every entry of the block on `src` onto `dst` (entry order reversed,
  each entry keeps its orientation). `moveAll_rs` is stated for a reversed source block
  (`blkE u.reverse`, the shape that one-entry-at-a-time pushes produce), giving `blkE u` on `dst`.
* `unshPairs w0 e o t`: the unshuffle loop: entries alternately to `e` and `o`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- Block delimiter between FFT blocks (a fresh layout tag). -/
def symD : Sym := .tag 8

/-- Loop test: the top symbol is not `s`. -/
def notSym (s : Sym) (r : Option Sym) : Bool := !decide (r = some s)

theorem notSym_entry {s : Sym} (hs : s ≠ .pos ∧ s ≠ .neg) (z : ℤ × ℤ) (r : List Sym) :
    notSym s (entrySyms z ++ r).head? = true := by
  have h : (entrySyms z ++ r).head? = some (sgnSym z.1) := rfl
  rw [h]
  unfold notSym sgnSym
  split_ifs
  · simp [hs.2.symm]
  · simp [hs.1.symm]

theorem notSym_self (s : Sym) (r : List Sym) : notSym s (s :: r).head? = false := by
  simp [notSym]

theorem mark_ok : Sym.mark ≠ .pos ∧ Sym.mark ≠ .neg := ⟨by decide, by decide⟩

theorem symD_ok : symD ≠ .pos ∧ symD ≠ .neg := ⟨by decide, by decide⟩

theorem blkE_nil : blkE [] = [] := rfl

theorem blkE_cons (z : ℤ × ℤ) (l : List (ℤ × ℤ)) : blkE (z :: l) = entrySyms z ++ blkE l := rfl

theorem blkE_append (l₁ l₂ : List (ℤ × ℤ)) : blkE (l₁ ++ l₂) = blkE l₁ ++ blkE l₂ := by
  simp [blkE, blk]

theorem length_blkE (w : ℕ) (l : List (ℤ × ℤ)) (hw : ∀ z ∈ l, EntryW w z) :
    (blkE l).length ≤ l.length * eb w := length_blkE_le w l hw

section Generic

variable {K τ : Type}

/-- Move every entry of the block on `src` (terminated by `term`) onto `dst`. -/
def moveAll (src dst t : K) (term : Sym) : MProg K τ := whileTop src (notSym term) (lm (emove src dst t))

/-- The unshuffle loop: entries alternately to `e` and `o`, until `symD`. -/
def unshPairs (w0 e o t : K) : MProg K τ :=
  whileTop w0 (notSym symD) (.seq (lm (emove w0 e t)) (lm (emove w0 o t)))

theorem moveAll_closed (src dst t : K) (term : Sym) : (moveAll src dst t term : MProg K τ).Closed :=
  whileTop_closed (lm_closed (emove_closed _ _ _))

theorem unshPairs_closed (w0 e o t : K) : (unshPairs w0 e o t : MProg K τ).Closed :=
  whileTop_closed ⟨lm_closed (emove_closed _ _ _), lm_closed (emove_closed _ _ _)⟩

variable [DecidableEq K]

theorem upd4_absorb {a b : K} (σ : K → List Sym) (A B C D : List Sym) :
    Function.update (Function.update (Function.update (Function.update σ a A) b B) a C) b D =
      Function.update (Function.update σ a C) b D := by
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem moveAll_rs' {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t) {term : Sym}
    (hterm : term ≠ .pos ∧ term ≠ .neg) (w : ℕ) :
    ∀ (v : List (ℤ × ℤ)) (M W : List Sym) (σ : K → List Sym), (∀ z ∈ v, EntryW w z) →
      σ src = blkE v ++ term :: M → σ dst = W →
      RS [] (moveAll src dst t term : MProg K τ) σ
        (Function.update (Function.update σ src (term :: M)) dst (blkE v.reverse ++ W))
        (v.length * (6 * eb w + 5) + 2)
  | [], M, W, σ, _, hs, hd => by
    refine (whileTop_done ?_).congr ?_ (by simp)
    · rw [hs]
      exact notSym_self term M
    · rw [List.reverse_nil, blkE_nil, List.nil_append, ← hd]
      rw [blkE_nil, List.nil_append] at hs
      rw [← hs, Function.update_eq_self, Function.update_eq_self]
  | z :: v, M, W, σ, hw, hs, hd => by
    have hz : (entrySyms z).length ≤ eb w := length_entrySyms_le (hw z (by simp))
    have ih := moveAll_rs' hsd hst hdt hterm w v M (entrySyms z ++ W)
      (Function.update (Function.update σ src (blkE v ++ term :: M)) dst (entrySyms z ++ σ dst))
      (fun y hy => hw y (by simp [hy])) (by rw [Function.update_of_ne hsd, Function.update_self])
      (by rw [Function.update_self, hd])
    refine whileTop_step' ?_ (emove_rs hsd hst hdt z (blkE v ++ term :: M) σ
      (by rw [hs, blkE_cons, List.append_assoc])) (ih.congr ?_ le_rfl) ?_
    · rw [hs, blkE_cons, List.append_assoc]
      exact notSym_entry hterm z _
    · rw [upd4_absorb, List.reverse_cons, blkE_append, blkE_cons, blkE_nil, List.append_nil,
        List.append_assoc]
    · simp only [List.length_cons]
      have := Nat.mul_le_mul_left 6 hz
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- **Move a reversed block back**: `src = ⟦u⟧ reversed ++ term :: M` ↦ `dst = ⟦u⟧ ++ W`. -/
theorem moveAll_rs {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t) {term : Sym}
    (hterm : term ≠ .pos ∧ term ≠ .neg) (w : ℕ) (u : List (ℤ × ℤ)) (M W : List Sym)
    (σ : K → List Sym) (hw : ∀ z ∈ u, EntryW w z) (hs : σ src = blkE u.reverse ++ term :: M)
    (hd : σ dst = W) :
    RS [] (moveAll src dst t term : MProg K τ) σ
      (Function.update (Function.update σ src (term :: M)) dst (blkE u ++ W))
      (u.length * (6 * eb w + 5) + 2) := by
  have h := moveAll_rs' (τ := τ) hsd hst hdt hterm w u.reverse M W σ
    (fun z hz => hw z (List.mem_reverse.mp hz)) hs hd
  rw [List.reverse_reverse, List.length_reverse] at h
  exact h

theorem unshPairs_rs {w0 e o t : K} (h1 : w0 ≠ e) (h2 : w0 ≠ o) (h3 : w0 ≠ t) (h4 : e ≠ o)
    (h5 : e ≠ t) (h6 : o ≠ t) (w : ℕ) :
    ∀ (n : ℕ) (l ae ao : List (ℤ × ℤ)) (rest E1 O1 : List Sym) (σ : K → List Sym),
      l.length = 2 * n → (∀ z ∈ l, EntryW w z) →
      σ w0 = blkE l ++ symD :: rest → σ e = blkE ae.reverse ++ E1 →
      σ o = blkE ao.reverse ++ O1 →
      RS [] (unshPairs w0 e o t : MProg K τ) σ
        (Function.update (Function.update (Function.update σ w0 (symD :: rest)) e
          (blkE (ae ++ evensL l).reverse ++ E1)) o (blkE (ao ++ oddsL l).reverse ++ O1))
        (n * (12 * eb w + 8) + 2)
  | 0, [], ae, ao, rest, E1, O1, σ, _, _, hw0, he, ho => by
    refine (whileTop_done ?_).congr ?_ (by simp)
    · rw [hw0]
      exact notSym_self symD rest
    · simp only [evensL, oddsL, List.append_nil]
      rw [blkE_nil, List.nil_append] at hw0
      rw [← hw0, ← he, ← ho, Function.update_eq_self, Function.update_eq_self,
        Function.update_eq_self]
  | 0, _ :: _, _, _, _, _, _, _, hl, _, _, _, _ => by simp at hl
  | n + 1, [], _, _, _, _, _, _, hl, _, _, _, _ => by simp at hl
  | n + 1, [_], _, _, _, _, _, _, hl, _, _, _, _ => by simp at hl; omega
  | n + 1, a :: b :: l, ae, ao, rest, E1, O1, σ, hl, hw, hw0, he, ho => by
    have ha : (entrySyms a).length ≤ eb w := length_entrySyms_le (hw a (by simp))
    have hb : (entrySyms b).length ≤ eb w := length_entrySyms_le (hw b (by simp))
    have hw0' : σ w0 = entrySyms a ++ (entrySyms b ++ (blkE l ++ symD :: rest)) := by
      rw [hw0, blkE_cons, blkE_cons, List.append_assoc, List.append_assoc]
    have s1 := emove_rs (τ := τ) h1 h3 h5 a _ σ hw0'
    have s2 := emove_rs (τ := τ) h2 h3 h6 b (blkE l ++ symD :: rest)
      (Function.update (Function.update σ w0 (entrySyms b ++ (blkE l ++ symD :: rest))) e
        (entrySyms a ++ σ e))
      (by rw [Function.update_of_ne h1, Function.update_self])
    have ih := unshPairs_rs h1 h2 h3 h4 h5 h6 w n l (ae ++ [a]) (ao ++ [b]) rest E1 O1
      (Function.update (Function.update (Function.update (Function.update σ w0
        (entrySyms b ++ (blkE l ++ symD :: rest))) e (entrySyms a ++ σ e)) w0
        (blkE l ++ symD :: rest)) o
        (entrySyms b ++ Function.update (Function.update σ w0
          (entrySyms b ++ (blkE l ++ symD :: rest))) e (entrySyms a ++ σ e) o))
      (by simp at hl; omega) (fun z hz => hw z (by simp [hz]))
      (by rw [Function.update_of_ne h2, Function.update_self])
      (by rw [Function.update_of_ne h4, Function.update_of_ne (Ne.symm h1), Function.update_self,
        he]; simp [List.reverse_append, blkE_cons])
      (by rw [Function.update_self, Function.update_of_ne (Ne.symm h4),
        Function.update_of_ne (Ne.symm h2), ho]; simp [List.reverse_append, blkE_cons])
    refine whileTop_step' ?_ (s1.seq s2) (ih.congr ?_ le_rfl) ?_
    · rw [hw0, blkE_cons, List.append_assoc]
      exact notSym_entry symD_ok a _
    · have he' : (ae ++ [a]) ++ evensL l = ae ++ evensL (a :: b :: l) := by
        simp [evensL]
      have ho' : (ao ++ [b]) ++ oddsL l = ao ++ oddsL (a :: b :: l) := by
        simp [oddsL]
      rw [he', ho']
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · have := Nat.mul_le_mul_left 6 ha
      have := Nat.mul_le_mul_left 6 hb
      rw [Nat.add_mul, Nat.one_mul]
      omega

end Generic

#assert_std_axioms notSym_entry notSym_self mark_ok symD_ok blkE_nil blkE_cons blkE_append
  length_blkE moveAll_closed unshPairs_closed upd4_absorb moveAll_rs' moveAll_rs unshPairs_rs

end WP.W9g
