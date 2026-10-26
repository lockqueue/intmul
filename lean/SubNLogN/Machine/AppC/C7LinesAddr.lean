/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Addr

/-!
# Lemma A.9 lines, address part (`Machine/AppC/C7LinesAddr.lean`)

Pure index arithmetic for the eight packed lines of Lemma A.9 (`lem:transfer13`,
Appendix A.4 (`sec:transfer-packed`);
eight-line packed shift program). One line with target name `tn` (`y` if `op.1`, else `z`) is realized by
* a Lemma A.8 exchange bringing the target slot `j = σ⁻¹ tn` to slot `2` (none if `j = 2`):
  `swapPull j` is `swapFieldsInv (2^L) (N1·2^L·N2) (2^L) N3` (`j = 0`) or
  `swapFieldsInv (2^L) N2 (2^L) N3` (`j = 1`);
* a controlled rotation of slot `2` with controls slots `0, 1` (`rotCtlInvAddr`), whose push offset
  is `lineOff ε par xFirst K ρ L c1 c2 = (ε · lineSum K ρ (L/K) par x o) mod 2^L` (`x, o` are the
  slot-0/slot-1 controls in the order given by `xFirst`);
* the same exchange again.

**Results (0 `sorry`).** `linePull_eq`: on the rectangle the composite pull map of one line equals
`c7Lift (f·K) N1 N2 N3 σ (packedLine (f·K) K ρ f (negOp op))`. `linesPull_eq`: running the lines
of a list `ops` in order has pull map `c7Lift σ (ops.reverse.foldl (packedLine ∘ negOp))`; for
`ops = eightOps` this is `c7LinesInv` (`linesPull_eightOps`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Networks AppC.Corr AppC.C7Aux

namespace AppC.C7LinesAux

/-! ## Five-field decoding -/

theorem mul_add_div_of_lt {a B z : ℕ} (hz : z < B) : (a * B + z) / B = a := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < B), Nat.div_eq_of_lt hz, zero_add]

theorem mul_add_mod_of_lt {a B z : ℕ} (hz : z < B) : (a * B + z) % B = z := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]

/-- Decoding `(((Y·Q + h)·G + g)·Q + d)·B + z` with `h, d < Q`, `g < G`, `z < B`. -/
theorem five_decode {Y Q G B h g d z : ℕ} (hh : h < Q) (hg : g < G) (hd : d < Q) (hz : z < B) :
    ((((Y * Q + h) * G + g) * Q + d) * B + z) % B = z ∧
      ((((Y * Q + h) * G + g) * Q + d) * B + z) / B % Q = d ∧
      ((((Y * Q + h) * G + g) * Q + d) * B + z) / (B * Q) % G = g ∧
      ((((Y * Q + h) * G + g) * Q + d) * B + z) / (B * Q * G) % Q = h ∧
      ((((Y * Q + h) * G + g) * Q + d) * B + z) / (B * Q * G * Q) = Y := by
  have e1 : ((((Y * Q + h) * G + g) * Q + d) * B + z) / B = ((Y * Q + h) * G + g) * Q + d :=
    mul_add_div_of_lt hz
  have e2 : (((Y * Q + h) * G + g) * Q + d) / Q = (Y * Q + h) * G + g := mul_add_div_of_lt hd
  have e3 : ((Y * Q + h) * G + g) / G = Y * Q + h := mul_add_div_of_lt hg
  have e4 : (Y * Q + h) / Q = Y := mul_add_div_of_lt hh
  refine ⟨mul_add_mod_of_lt hz, ?_, ?_, ?_, ?_⟩
  · rw [e1, mul_add_mod_of_lt hd]
  · rw [← Nat.div_div_eq_div_mul, e1, e2, mul_add_mod_of_lt hg]
  · rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e1, e2, e3, mul_add_mod_of_lt hh]
  · rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e1, e2, e3,
      e4]

/-- `swapFieldsInv` on a five-field index with equal chunk sizes exchanges the two chunks. -/
theorem swapFieldsInv_five {Y Q G B h g d z : ℕ} (hh : h < Q) (hg : g < G) (hd : d < Q)
    (hz : z < B) :
    swapFieldsInv Q G Q B ((((Y * Q + h) * G + g) * Q + d) * B + z) =
      (((Y * Q + d) * G + g) * Q + h) * B + z := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := five_decode (Y := Y) hh hg hd hz
  unfold swapFieldsInv
  rw [e1, e2, e3, e4, e5]

/-! ## The three index maps on ranks -/

section Ranks

variable {L N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ}

/-- Exchange of slots `1` and `2`. -/
theorem swap12_rank (hc : ∀ i, c i < 2 ^ L) (h2 : a2 < N2) (h3 : a3 < N3) :
    swapFieldsInv (2 ^ L) N2 (2 ^ L) N3 (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) =
      c7Rank L N1 N2 N3 a0 a1 a2 a3 (c ∘ Equiv.swap (1 : Fin 3) 2) := by
  unfold c7Rank
  rw [swapFieldsInv_five (hc 1) h2 (hc 2) h3]
  simp [Equiv.swap_apply_of_ne_of_ne]

/-- Exchange of slots `0` and `2`. -/
theorem swap02_rank (hc : ∀ i, c i < 2 ^ L) (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3) :
    swapFieldsInv (2 ^ L) (N1 * 2 ^ L * N2) (2 ^ L) N3 (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) =
      c7Rank L N1 N2 N3 a0 a1 a2 a3 (c ∘ Equiv.swap (0 : Fin 3) 2) := by
  have hg : (a1 * 2 ^ L + c 1) * N2 + a2 < N1 * 2 ^ L * N2 := mr_lt (mr_lt h1 (hc 1)) h2
  have e : c7Rank L N1 N2 N3 a0 a1 a2 a3 c =
      (((a0 * 2 ^ L + c 0) * (N1 * 2 ^ L * N2) + ((a1 * 2 ^ L + c 1) * N2 + a2)) * 2 ^ L + c 2) *
        N3 + a3 := by
    unfold c7Rank; ring
  rw [e, swapFieldsInv_five (hc 0) hg (hc 2) h3]
  unfold c7Rank
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  ring

/-- The controlled rotation of slot `2` with controls slots `0`, `1`. -/
theorem rot_rank (hc : ∀ i, c i < 2 ^ L) (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3)
    (off : ℕ → ℕ → ℕ) :
    rotCtlInvAddr (2 ^ L) N1 (2 ^ L) N2 (2 ^ L) N3 off (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) =
      c7Rank L N1 N2 N3 a0 a1 a2 a3
        (Function.update c 2 ((c 2 + 2 ^ L - off (c 0) (c 1) % 2 ^ L) % 2 ^ L)) := by
  have hF : c7Rank L N1 N2 N3 a0 a1 a2 a3 c / (N3 * 2 ^ L) =
      (((a0 * 2 ^ L + c 0) * N1 + a1) * 2 ^ L + c 1) * N2 + a2 := by
    unfold c7Rank
    rw [← Nat.div_div_eq_div_mul, mul_add_div_of_lt h3, mul_add_div_of_lt (hc 2)]
  have hc0 : ((((a0 * 2 ^ L + c 0) * N1 + a1) * 2 ^ L + c 1) * N2 + a2) / (N2 * 2 ^ L * N1) %
      2 ^ L = c 0 := by
    rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, mul_add_div_of_lt h2,
      mul_add_div_of_lt (hc 1), mul_add_div_of_lt h1, mul_add_mod_of_lt (hc 0)]
  have hc1 : ((((a0 * 2 ^ L + c 0) * N1 + a1) * 2 ^ L + c 1) * N2 + a2) / N2 % 2 ^ L = c 1 := by
    rw [mul_add_div_of_lt h2, mul_add_mod_of_lt (hc 1)]
  have hc2 : c7Rank L N1 N2 N3 a0 a1 a2 a3 c / N3 % 2 ^ L = c 2 := by
    unfold c7Rank
    rw [mul_add_div_of_lt h3, mul_add_mod_of_lt (hc 2)]
  have ha3 : c7Rank L N1 N2 N3 a0 a1 a2 a3 c % N3 = a3 := by
    unfold c7Rank
    rw [mul_add_mod_of_lt h3]
  unfold rotCtlInvAddr
  simp only []
  rw [hF, hc0, hc1, hc2, ha3]
  unfold c7Rank
  simp only [Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true,
    Function.update_of_ne]
  ring

end Ranks

/-! ## One line -/

/-- Target name of a line: `y` (`1`) if `op.1`, else `z` (`2`). -/
def tgtName (op : Bool × ℤ × ℕ) : Fin 3 := if op.1 then 1 else 2

/-- Tested auxiliary name of a line: `z` (`2`) if `op.1`, else `y` (`1`). -/
def othName (op : Bool × ℤ × ℕ) : Fin 3 := if op.1 then 2 else 1

/-- Exchange pull map bringing slot `j` to slot `2` (the identity for `j = 2`). -/
def swapPull (L N1 N2 N3 : ℕ) (j : Fin 3) : ℕ → ℕ :=
  if j = 0 then swapFieldsInv (2 ^ L) (N1 * 2 ^ L * N2) (2 ^ L) N3
  else if j = 1 then swapFieldsInv (2 ^ L) N2 (2 ^ L) N3 else id

theorem fin3_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  fin_cases j <;> simp

theorem swapPull_rank {L N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ} (j : Fin 3)
    (hc : ∀ i, c i < 2 ^ L) (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3) :
    swapPull L N1 N2 N3 j (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) =
      c7Rank L N1 N2 N3 a0 a1 a2 a3 (c ∘ Equiv.swap j 2) := by
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [swapPull, if_pos rfl]; exact swap02_rank hc h1 h2 h3
  · rw [swapPull, if_neg (by decide), if_pos rfl]; exact swap12_rank hc h2 h3
  · rw [swapPull, if_neg (by decide), if_neg (by decide)]
    simp [Equiv.swap_self]

/-- **Push offset of a line** on the rotation controls `c1` (slot `0`) and `c2` (slot `1`):
`(ε · lineSum k1 k2 (b / k1) par x o) mod 2^b`, with `x = c1, o = c2` if `xF`, else `x = c2,
o = c1`. With `k1 = K`, `k2 = ρ`, `b = L = f·K` this is the shift of `packedLine`. -/
def lineOff (ε : ℤ) (par : ℕ) (xF : Bool) (k1 k2 b c1 c2 : ℕ) : ℕ :=
  ((ε * lineSum k1 k2 (b / k1) par (if xF then c1 else c2) (if xF then c2 else c1)) %
    (2 : ℤ) ^ b).toNat

theorem lineOff_lt (ε : ℤ) (par : ℕ) (xF : Bool) (k1 k2 b c1 c2 : ℕ) :
    lineOff ε par xF k1 k2 b c1 c2 < 2 ^ b :=
  toNat_emod_lt _ _

/-- After exchanging slot `j` with slot `2`, does slot `0` hold `x`? -/
def xFirst (σ : Equiv.Perm (Fin 3)) (j : Fin 3) : Bool := decide (σ (Equiv.swap j 2 0) = 0)

/-- The rotation offset of line `op` under the arrangement `σ`. -/
def lineOffOp (σ : Equiv.Perm (Fin 3)) (op : Bool × ℤ × ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ :=
  lineOff op.2.1 op.2.2 (xFirst σ (σ.symm (tgtName op)))

/-- **Composite pull map of one line**: exchange, rotation, exchange. -/
def linePull (σ : Equiv.Perm (Fin 3)) (op : Bool × ℤ × ℕ) (K ρ f N1 N2 N3 : ℕ) (p : ℕ) : ℕ :=
  swapPull (f * K) N1 N2 N3 (σ.symm (tgtName op))
    (rotCtlInvAddr (2 ^ (f * K)) N1 (2 ^ (f * K)) N2 (2 ^ (f * K)) N3
      (lineOffOp σ op K ρ (f * K)) (swapPull (f * K) N1 N2 N3 (σ.symm (tgtName op)) p))

theorem fin3_rest : ∀ a b t o : Fin 3, a ≠ b → a ≠ t → b ≠ t → t ≠ o → t ≠ 0 → o ≠ 0 →
    (a = 0 → b = o) ∧ (a ≠ 0 → a = o ∧ b = 0) := by
  decide

/-- The two controls of the rotation are `x` and the tested chunk, in the order `xFirst`. -/
theorem lineOff_ctrl (σ : Equiv.Perm (Fin 3)) (b : Bool) (ε : ℤ) (par k1 k2 b' : ℕ)
    (c : Fin 3 → ℕ) :
    lineOff ε par (xFirst σ (σ.symm (if b then 1 else 2))) k1 k2 b'
        (c (Equiv.swap (σ.symm (if b then 1 else 2)) 2 0))
        (c (Equiv.swap (σ.symm (if b then 1 else 2)) 2 1)) =
      ((ε * lineSum k1 k2 (b' / k1) par (c (σ.symm 0)) (c (σ.symm (if b then 2 else 1)))) %
        (2 : ℤ) ^ b').toNat := by
  set j := σ.symm (if b then 1 else 2) with hj
  have ht : σ (Equiv.swap j 2 2) = (if b then 1 else 2) := by
    rw [Equiv.swap_apply_right, hj, Equiv.apply_symm_apply]
  have hinj : ∀ x y : Fin 3, x ≠ y → σ (Equiv.swap j 2 x) ≠ σ (Equiv.swap j 2 y) :=
    fun x y hxy h => hxy ((Equiv.swap j 2).injective (σ.injective h))
  have h02 := hinj 0 2 (by decide)
  have h12 := hinj 1 2 (by decide)
  rw [ht] at h02 h12
  have key := fin3_rest _ _ _ (if b then 2 else 1) (hinj 0 1 (by decide)) h02 h12
    (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)
  unfold lineOff xFirst
  by_cases h0 : σ (Equiv.swap j 2 0) = 0
  · have h1 := key.1 h0
    have e0 : Equiv.swap j 2 0 = σ.symm 0 := by rw [Equiv.eq_symm_apply]; exact h0
    have e1 : Equiv.swap j 2 1 = σ.symm (if b then 2 else 1) := by
      rw [Equiv.eq_symm_apply]; exact h1
    rw [e0, e1]
    simp
  · obtain ⟨h0', h1'⟩ := key.2 h0
    have e0 : Equiv.swap j 2 0 = σ.symm (if b then 2 else 1) := by
      rw [Equiv.eq_symm_apply]; exact h0'
    have e1 : Equiv.swap j 2 1 = σ.symm 0 := by rw [Equiv.eq_symm_apply]; exact h1'
    have hd : decide (σ (Equiv.swap j 2 0) = 0) = false := by simpa using h0
    rw [hd, e0, e1]
    simp

/-- Subtracting a reduced push offset is adding its negation mod `Q`. -/
theorem sub_off_eq {t Q : ℕ} (ht : t < Q) (e : ℤ) :
    (t + Q - (e % (Q : ℤ)).toNat % Q) % Q = (((t : ℤ) + -e) % (Q : ℤ)).toNat := by
  have hQ : (0 : ℤ) < Q := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le t) ht)
  have h0 : 0 ≤ e % (Q : ℤ) := Int.emod_nonneg _ hQ.ne'
  have h1 : e % (Q : ℤ) < Q := Int.emod_lt_of_pos _ hQ
  set r := (e % (Q : ℤ)).toNat with hr
  have hrz : (r : ℤ) = e % (Q : ℤ) := Int.toNat_of_nonneg h0
  have hrQ : r < Q := by
    have : (r : ℤ) < Q := hrz ▸ h1
    exact_mod_cast this
  rw [Nat.mod_eq_of_lt hrQ]
  have key : ((t + Q - r : ℕ) : ℤ) = ((t : ℤ) + -e) + (Q : ℤ) * (1 + e / (Q : ℤ)) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, hrz]
    have := Int.emod_add_ediv_mul e (Q : ℤ)
    linarith
  have h2 : (((t + Q - r) % Q : ℕ) : ℤ) = ((t : ℤ) + -e) % (Q : ℤ) := by
    rw [Int.natCast_mod, key, Int.add_mul_emod_self_left]
  have h3 : ((((t : ℤ) + -e) % (Q : ℤ)).toNat : ℤ) = ((t : ℤ) + -e) % (Q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hQ.ne')
  exact_mod_cast h2.trans h3.symm

/-- The named triple of slot values, read by name. -/
theorem nameGet_named (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → ℕ) (n : Fin 3) :
    nameGet (c (σ.symm 0), c (σ.symm 1), c (σ.symm 2)) n = c (σ.symm n) := by
  rcases fin3_cases n with rfl | rfl | rfl <;> rfl

/-- A line on a named triple of slot values, read at slot `s`. -/
theorem nameGet_packedLine (L K ρ f : ℕ) (b : Bool) (ε : ℤ) (par : ℕ) (c : Fin 3 → ℕ)
    (σ : Equiv.Perm (Fin 3)) (s : Fin 3) :
    nameGet (packedLine L K ρ f (b, ε, par) (c (σ.symm 0), c (σ.symm 1), c (σ.symm 2))) (σ s) =
      if σ s = (if b then 1 else 2) then
        (((c s : ℤ) + ε * lineSum K ρ f par (c (σ.symm 0)) (c (σ.symm (if b then 2 else 1)))) %
          (2 : ℤ) ^ L).toNat
      else c s := by
  have hcs : c s = c (σ.symm (σ s)) := by rw [Equiv.symm_apply_apply]
  rw [hcs]
  generalize σ s = n
  cases b
  · rw [packedLine_false]
    rcases fin3_cases n with rfl | rfl | rfl <;> simp [nameGet]
  · rw [packedLine_true]
    rcases fin3_cases n with rfl | rfl | rfl <;> simp [nameGet]

/-- **One line on a rank**: exchange, rotation and exchange act on the slot values as the inverse
line `packedLine (negOp op)` on the named triple. -/
theorem linePull_rank (σ : Equiv.Perm (Fin 3)) (op : Bool × ℤ × ℕ)
    {K ρ f N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ} (hK : 0 < K)
    (hc : ∀ i, c i < 2 ^ (f * K)) (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3) :
    linePull σ op K ρ f N1 N2 N3 (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3 c) =
      c7Lift (f * K) N1 N2 N3 σ (packedLine (f * K) K ρ f (negOp op))
        (c7Rank (f * K) N1 N2 N3 a0 a1 a2 a3 c) := by
  obtain ⟨b, ε, par⟩ := op
  set L := f * K with hL
  set j := σ.symm (if b then 1 else 2) with hj
  have hjt : σ.symm (tgtName (b, ε, par)) = j := rfl
  have hcτ : ∀ i, (c ∘ Equiv.swap j 2) i < 2 ^ L := fun i => hc _
  set v := ((c ∘ Equiv.swap j 2) 2 + 2 ^ L -
    lineOffOp σ (b, ε, par) K ρ L ((c ∘ Equiv.swap j 2) 0) ((c ∘ Equiv.swap j 2) 1) % 2 ^ L) %
      2 ^ L with hv
  have hvL : v < 2 ^ L := Nat.mod_lt _ (by positivity)
  have hcu : ∀ i, Function.update (c ∘ Equiv.swap j 2) 2 v i < 2 ^ L := by
    intro i
    rcases eq_or_ne i 2 with rfl | hi
    · rw [Function.update_self]; exact hvL
    · rw [Function.update_of_ne hi]; exact hcτ i
  unfold linePull
  rw [hjt, swapPull_rank j hc h1 h2 h3, rot_rank hcτ h1 h2 h3, ← hv,
    swapPull_rank j hcu h1 h2 h3, c7Lift_rank σ _ hc h1 h2 h3]
  congr 1
  funext s
  rw [negOp, nameGet_packedLine]
  simp only [Function.comp_apply]
  rw [Function.update_apply]
  have hiff : (Equiv.swap j 2 s = 2) ↔ σ s = (if b then 1 else 2) := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right, hj, Equiv.eq_symm_apply]
  by_cases hs : σ s = (if b then 1 else 2)
  · rw [if_pos (hiff.mpr hs), if_pos hs]
    have hsj : s = j := by rw [hj, Equiv.eq_symm_apply]; exact hs
    subst hsj
    rw [hv]
    simp only [Function.comp_apply, Equiv.swap_apply_right]
    have hoff : lineOffOp σ (b, ε, par) K ρ L (c (Equiv.swap j 2 0)) (c (Equiv.swap j 2 1)) =
        ((ε * lineSum K ρ f par (c (σ.symm 0)) (c (σ.symm (if b then 2 else 1)))) %
          (2 : ℤ) ^ L).toNat := by
      unfold lineOffOp
      have hfK : L / K = f := by rw [hL]; exact Nat.mul_div_cancel f hK
      have := lineOff_ctrl σ b ε par K ρ L c
      rw [hfK] at this
      exact this
    rw [hoff]
    have := sub_off_eq (hc j) (ε * lineSum K ρ f par (c (σ.symm 0)) (c (σ.symm (if b then 2 else 1))))
    push_cast at this
    rw [this, neg_mul]
  · rw [if_neg (fun h => hs (hiff.mp h)), if_neg hs]
    simp only [Function.comp_apply, Equiv.swap_apply_self]

/-- `c7Lift` of the identity is the identity on the rectangle. -/
theorem c7Lift_id {L N0 N1 N2 N3 p : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (_hp : p < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3) :
    c7Lift L N1 N2 N3 σ (fun t => t) p = p := by
  rw [c7Lift_eq hN1 hN2 hN3]
  conv_rhs => rw [← c7_decode L N1 N2 N3 p]
  congr 1
  funext j
  have := nameGet_named σ (fun i => c7Slot L N1 N2 N3 i p) (σ j)
  simp only [Equiv.symm_apply_apply] at this
  exact this

/-- **One line on the rectangle.** -/
theorem linePull_eq (σ : Equiv.Perm (Fin 3)) (op : Bool × ℤ × ℕ) {K ρ f N0 N1 N2 N3 p : ℕ}
    (hK : 0 < K) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (hp : p < N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) :
    linePull σ op K ρ f N1 N2 N3 p =
      c7Lift (f * K) N1 N2 N3 σ (packedLine (f * K) K ρ f (negOp op)) p := by
  obtain ⟨-, hc, h1, h2, h3⟩ := c7_coords hN1 hN2 hN3 hp
  rw [← c7_decode (f * K) N1 N2 N3 p]
  exact linePull_rank σ op hK hc h1 h2 h3

/-! ## A list of lines -/

/-- Pull map of the lines `ops` run in order (the first line acts first on the array, so its pull
map is applied last to an output index). -/
def linesPull (σ : Equiv.Perm (Fin 3)) (K ρ f N1 N2 N3 : ℕ) : List (Bool × ℤ × ℕ) → ℕ → ℕ
  | [] => fun p => p
  | op :: ops => fun p => linePull σ op K ρ f N1 N2 N3 (linesPull σ K ρ f N1 N2 N3 ops p)

/-- **Lines in order**: the pull map is the lift of the reversed inverse lines, and it keeps
indices in range. -/
theorem linesPull_eq (σ : Equiv.Perm (Fin 3)) {K ρ f N0 N1 N2 N3 : ℕ} (hK : 0 < K)
    (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3) :
    ∀ (ops : List (Bool × ℤ × ℕ)) (p : ℕ),
      p < N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 →
      linesPull σ K ρ f N1 N2 N3 ops p =
        c7Lift (f * K) N1 N2 N3 σ
          (fun t => ops.reverse.foldl (fun t op => packedLine (f * K) K ρ f (negOp op) t) t) p ∧
      linesPull σ K ρ f N1 N2 N3 ops p <
        N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3
  | [], p, hp => by
    refine ⟨?_, hp⟩
    simp only [linesPull, List.reverse_nil, List.foldl_nil]
    exact (c7Lift_id hN1 hN2 hN3 σ hp).symm
  | op :: ops, p, hp => by
    obtain ⟨ih, hlt⟩ := linesPull_eq σ hK hN1 hN2 hN3 ops p hp
    have hG : ∀ t, InBox (f * K) t → InBox (f * K)
        (ops.reverse.foldl (fun t op => packedLine (f * K) K ρ f (negOp op) t) t) :=
      fun t ht => foldl_lines_inBox negOp ops.reverse t ht
    have hF : ∀ t, InBox (f * K) t → InBox (f * K)
        ((op :: ops).reverse.foldl (fun t op => packedLine (f * K) K ρ f (negOp op) t) t) :=
      fun t ht => foldl_lines_inBox negOp (op :: ops).reverse t ht
    refine ⟨?_, ?_⟩
    · simp only [linesPull]
      rw [linePull_eq σ op hK hN1 hN2 hN3 hlt, ih, c7Lift_comp hN1 hN2 hN3 σ _ _ hG]
      apply c7Lift_congr
      intro t _
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    · simp only [linesPull]
      rw [linePull_eq σ op hK hN1 hN2 hN3 hlt, ih, c7Lift_comp hN1 hN2 hN3 σ _ _ hG]
      exact c7Lift_lt hN1 hN2 hN3 σ _ (fun t ht => packedLine_inBox _ (hG t ht)) hp

/-- **The eight lines**: their pull map is `c7LinesInv` on the rectangle. -/
theorem linesPull_eightOps (σ : Equiv.Perm (Fin 3)) {K ρ f N0 N1 N2 N3 p : ℕ} (hK : 0 < K)
    (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3) (hp : p < c7M K f N0 N1 N2 N3) :
    linesPull σ K ρ f N1 N2 N3 eightOps p = c7LinesInv K ρ f N1 N2 N3 σ p := by
  rw [(linesPull_eq σ hK hN1 hN2 hN3 eightOps p hp).1]
  rfl

end AppC.C7LinesAux

end SubNLogN.Machine
