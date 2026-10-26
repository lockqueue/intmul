import WP.W9fF.SL
import WP.W9fW.Basic

/-!
# WP.W9fF.Bound — bit-length abstract interpretation of straight-line code

Generic part (any ops `O`, variables `V`):
* `Oracle O`: per-op result bound `rb o b1 b2` and cost cap `U o`; `Oracle.Sound or sem κ B`:
  for operands of bit length `≤ b1, b2 ≤ B`, the result has bit length `≤ rb o b1 b2` and the
  op costs `≤ U o`.
* `sBnd or p β`: abstract evaluation of bit-length bounds; `sChk or B p β`: every operand and
  every overwritten variable is bounded by `B` along the way; `sU or B p`: the cost cap
  (`U o + 20·B + 43` per op statement).
* `sBnd_sound`: concrete widths are below the abstract ones, and `p.cost ≤ sU or B p`.

Concrete part (the column ops `Op`): `kap C Mul W` (the cost function the op implementations
satisfy) and `orc C Mul W` with `orc_sound : (orc C Mul W).Sound Op.sem (kap C Mul W) W`.
-/

namespace WP.W9fF

open TMFw TMFw.Contracts WP.W9fF.IL

/-! ## Bit-length toolkit -/

theorem bitLen_eq_size (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

theorem bitLen_le_iff {n k : ℕ} : bitLen n ≤ k ↔ n < 2 ^ k := by
  rw [bitLen_eq_size]
  exact Nat.size_le

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := bitLen_le_iff.1 le_rfl

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n := by
  rw [bitLen_eq_size, bitLen_eq_size]
  exact Nat.size_le_size h

theorem bl_add (a b : ℤ) :
    bitLen (a + b).natAbs ≤ max (bitLen a.natAbs) (bitLen b.natAbs) + 1 := by
  rw [bitLen_le_iff, pow_succ]
  have h1 := lt_two_pow_bitLen a.natAbs
  have h2 := lt_two_pow_bitLen b.natAbs
  have h3 : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  have h4 : 2 ^ bitLen a.natAbs ≤ 2 ^ max (bitLen a.natAbs) (bitLen b.natAbs) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h5 : 2 ^ bitLen b.natAbs ≤ 2 ^ max (bitLen a.natAbs) (bitLen b.natAbs) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  omega

theorem bl_sub (a b : ℤ) :
    bitLen (a - b).natAbs ≤ max (bitLen a.natAbs) (bitLen b.natAbs) + 1 := by
  have h := bl_add a (-b)
  rwa [Int.natAbs_neg, ← sub_eq_add_neg] at h

theorem bl_mul (a b : ℤ) : bitLen (a * b).natAbs ≤ bitLen a.natAbs + bitLen b.natAbs := by
  rw [bitLen_le_iff, Int.natAbs_mul, pow_add]
  exact mul_lt_mul'' (lt_two_pow_bitLen _) (lt_two_pow_bitLen _) (Nat.zero_le _) (Nat.zero_le _)

theorem bl_shl (a b : ℤ) : bitLen (a * 2 ^ b.natAbs).natAbs ≤ bitLen a.natAbs + b.natAbs := by
  rw [bitLen_le_iff, Int.natAbs_mul, Int.natAbs_pow, pow_add]
  exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen _) (by positivity)

theorem natAbs_shiftRight_le (a : ℤ) (k : ℕ) : (a >>> k).natAbs ≤ a.natAbs := by
  rcases a with n | n
  · show (Int.shiftRight (Int.ofNat n) k).natAbs ≤ (Int.ofNat n).natAbs
    rw [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self n _
  · show (Int.shiftRight (Int.negSucc n) k).natAbs ≤ (Int.negSucc n).natAbs
    rw [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.succ_le_succ (Nat.div_le_self n _)

theorem bl_sar (a : ℤ) (k : ℕ) : bitLen (a >>> k).natAbs ≤ bitLen a.natAbs :=
  bitLen_mono (natAbs_shiftRight_le a k)

theorem bl_le (a b : ℤ) : bitLen (if a ≤ b then (1 : ℤ) else 0).natAbs ≤ 1 := by
  rw [bitLen_le_iff]
  split_ifs <;> simp

theorem bl_divR (a b : ℤ) : bitLen (IntMul.divRoundRatInt a b).natAbs ≤ bitLen a.natAbs + 1 := by
  by_cases hb : 0 < b
  · have hP : (0 : ℤ) ≤ ((2 ^ bitLen a.natAbs : ℕ) : ℤ) := by positivity
    have hx : |a| < ((2 ^ bitLen a.natAbs : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast lt_two_pow_bitLen a.natAbs
    exact WP.W9fW.bitLen_natAbs_le_succ (WP.W9fW.abs_divRoundRatInt_le hb hP hx)
  · have h0 : IntMul.divRoundRatInt a b = 0 := by
      unfold IntMul.divRoundRatInt
      rw [if_neg hb]
    rw [h0]
    simp [bitLen_le_iff]

theorem two_pow_bitLen_le (n : ℕ) : n < 2 ^ bitLen n := lt_two_pow_bitLen n

#assert_std_axioms bitLen_eq_size bitLen_le_iff lt_two_pow_bitLen bitLen_mono bl_add bl_sub bl_mul
  bl_shl natAbs_shiftRight_le bl_sar bl_le bl_divR two_pow_bitLen_le

/-! ## The generic abstract interpretation -/

section Generic

variable {O V : Type} [DecidableEq V]

/-- Bit-length oracle: result bound `rb` and cost cap `U` (for operand bounds `≤` the cap). -/
structure Oracle (O : Type) where
  /-- result bit-length bound from operand bounds -/
  rb : O → ℕ → ℕ → ℕ
  /-- cost cap of one op -/
  U : O → ℕ

/-- Soundness of an oracle for semantics `sem`, op costs `κ`, width cap `B`. -/
def Oracle.Sound (or : Oracle O) (sem : O → ℤ → ℤ → ℤ) (κ : O → ℤ → ℤ → ℕ) (B : ℕ) : Prop :=
  ∀ (o : O) (a b : ℤ) (b1 b2 : ℕ), bitLen a.natAbs ≤ b1 → bitLen b.natAbs ≤ b2 → b1 ≤ B →
    b2 ≤ B → bitLen (sem o a b).natAbs ≤ or.rb o b1 b2 ∧ κ o a b ≤ or.U o

/-- Abstract value of a right-hand side. -/
def eRb (or : Oracle O) (β : V → ℕ) : Expr O V → ℕ
  | .const c => bitLen c.natAbs
  | .op o y z => or.rb o (β y) (β z)

/-- Abstract evaluation of bit-length bounds. -/
def sBnd (or : Oracle O) : Stmt O V → (V → ℕ) → V → ℕ
  | .assign x e, β => Function.update β x (eRb or β e)
  | .seq p q, β => sBnd or q (sBnd or p β)

/-- Operands bounded by `B`. -/
def eChk (B : ℕ) (β : V → ℕ) : Expr O V → Prop
  | .const _ => True
  | .op _ y z => β y ≤ B ∧ β z ≤ B

/-- Width check along the program: operands and overwritten variables bounded by `B`. -/
def sChk (or : Oracle O) (B : ℕ) : Stmt O V → (V → ℕ) → Prop
  | .assign x e, β => β x ≤ B ∧ eChk B β e
  | .seq p q, β => sChk or B p β ∧ sChk or B q (sBnd or p β)

/-- Cost cap of a right-hand side. -/
def eU (or : Oracle O) (B : ℕ) : Expr O V → ℕ
  | .const c => bitLen c.natAbs + 2
  | .op o _ _ => or.U o + 18 * B + 38

/-- Cost cap of a program. -/
def sU (or : Oracle O) (B : ℕ) : Stmt O V → ℕ
  | .assign _ e => eU or B e + 2 * B + 5
  | .seq p q => sU or B p + sU or B q

/-- **Soundness of the abstract interpretation.** -/
theorem sBnd_sound {sem : O → ℤ → ℤ → ℤ} {κ : O → ℤ → ℤ → ℕ} {or : Oracle O} {B : ℕ}
    (hs : or.Sound sem κ B) :
    ∀ (p : Stmt O V) (β : V → ℕ) (env : V → ℤ), sChk or B p β →
      (∀ v, bitLen (env v).natAbs ≤ β v) →
      (∀ v, bitLen ((p.eval sem env) v).natAbs ≤ sBnd or p β v) ∧
        p.cost sem κ env ≤ sU or B p
  | .assign x (.const c), β, env, hc, hb => by
    have hx : β x ≤ B := hc.1
    refine ⟨fun v => ?_, ?_⟩
    · by_cases hv : v = x
      · subst hv
        simp only [Stmt.eval, sBnd, eRb, Expr.eval, Function.update_self, le_refl]
      · simp only [Stmt.eval, sBnd, Function.update_of_ne hv]
        exact hb v
    · simp only [Stmt.cost, Expr.cost, sU, eU]
      have := hb x
      omega
  | .assign x (.op o y z), β, env, hc, hb => by
    have hx : β x ≤ B := hc.1
    have hy : β y ≤ B := hc.2.1
    have hz : β z ≤ B := hc.2.2
    have h := hs o (env y) (env z) (β y) (β z) (hb y) (hb z) hy hz
    refine ⟨fun v => ?_, ?_⟩
    · by_cases hv : v = x
      · subst hv
        simp only [Stmt.eval, sBnd, eRb, Expr.eval, Function.update_self]
        exact h.1
      · simp only [Stmt.eval, sBnd, Function.update_of_ne hv]
        exact hb v
    · simp only [Stmt.cost, Expr.cost, sU, eU]
      have := hb x
      have := hb y
      have := hb z
      have := h.2
      omega
  | .seq p q, β, env, hc, hb => by
    obtain ⟨h1, h2⟩ := sBnd_sound hs p β env hc.1 hb
    obtain ⟨h3, h4⟩ := sBnd_sound hs q _ _ hc.2 h1
    refine ⟨h3, ?_⟩
    simp only [Stmt.cost, sU]
    omega

end Generic

/-! ## The column ops -/

/-- Cost of the column ops: what their machine implementations satisfy (`W`: declared product
width). -/
def kap (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) : Op → ℤ → ℤ → ℕ
  | .add, a, b => C * (bitLen a.natAbs + bitLen b.natAbs + 1)
  | .sub, a, b => C * (bitLen a.natAbs + bitLen b.natAbs + 1)
  | .mul, a, b => C * Mul (max W (max (bitLen a.natAbs) (bitLen b.natAbs))) + C
  | .shl, a, b => C * (bitLen a.natAbs + bitLen b.natAbs + b.natAbs + 1)
  | .sar, a, b => C * (bitLen a.natAbs + bitLen b.natAbs + 1)
  | .le, a, b => C * (bitLen a.natAbs + bitLen b.natAbs + 1)
  | .divR, a, b =>
    C * (bitLen a.natAbs * bitLen b.natAbs + bitLen a.natAbs + bitLen b.natAbs + 1)

/-- Result bounds of the column ops. -/
def orcRb : Op → ℕ → ℕ → ℕ
  | .add, b1, b2 => max b1 b2 + 1
  | .sub, b1, b2 => max b1 b2 + 1
  | .mul, b1, b2 => b1 + b2
  | .shl, b1, b2 => b1 + 2 ^ b2
  | .sar, b1, _ => b1
  | .le, _, _ => 1
  | .divR, b1, _ => b1 + 1

/-- Cost caps of the column ops at width cap `W`. -/
def orcU (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) : Op → ℕ
  | .mul => C * Mul W + C
  | .shl => C * (2 * W + 2 ^ W + 1)
  | .divR => C * (W * W + 2 * W + 1)
  | _ => C * (2 * W + 1)

/-- The oracle of the column ops. -/
def orc (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) : Oracle Op := ⟨orcRb, orcU C Mul W⟩

@[simp] theorem orc_rb (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) : (orc C Mul W).rb = orcRb := rfl

@[simp] theorem orc_U (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) : (orc C Mul W).U = orcU C Mul W := rfl

theorem small_cost (C W x y : ℕ) (hx : x ≤ W) (hy : y ≤ W) : C * (x + y + 1) ≤ C * (2 * W + 1) :=
  Nat.mul_le_mul_left _ (by omega)

/-- **The column-op oracle is sound** at width cap `W`. -/
theorem orc_sound (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) : (orc C Mul W).Sound Op.sem (kap C Mul W) W := by
  intro o a b b1 b2 ha hb h1 h2
  cases o with
  | add =>
    refine ⟨(bl_add a b).trans (by simp only [orc_rb, orcRb]; omega), ?_⟩
    exact small_cost C W _ _ (by omega) (by omega)
  | sub =>
    refine ⟨(bl_sub a b).trans (by simp only [orc_rb, orcRb]; omega), ?_⟩
    exact small_cost C W _ _ (by omega) (by omega)
  | mul =>
    refine ⟨(bl_mul a b).trans (by simp only [orc_rb, orcRb]; omega), ?_⟩
    have e : max W (max (bitLen a.natAbs) (bitLen b.natAbs)) = W := by omega
    simp only [kap, orc_U, orcU, e, le_refl]
  | shl =>
    have hk : b.natAbs < 2 ^ b2 := lt_of_lt_of_le (lt_two_pow_bitLen _)
      (Nat.pow_le_pow_right (by norm_num) hb)
    have hk' : 2 ^ b2 ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h2
    refine ⟨(bl_shl a b).trans (by simp only [orc_rb, orcRb]; omega), ?_⟩
    simp only [kap, orc_U, orcU]
    exact Nat.mul_le_mul_left _ (by omega)
  | sar =>
    refine ⟨(bl_sar a _).trans (by simp only [orc_rb, orcRb]; omega), ?_⟩
    exact small_cost C W _ _ (by omega) (by omega)
  | le =>
    refine ⟨(bl_le a b).trans (by simp only [orc_rb, orcRb]; omega), ?_⟩
    exact small_cost C W _ _ (by omega) (by omega)
  | divR =>
    refine ⟨(bl_divR a b).trans (by simp only [orc_rb, orcRb]; omega), ?_⟩
    simp only [kap, orc_U, orcU]
    have hm : bitLen a.natAbs * bitLen b.natAbs ≤ W * W := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.mul_le_mul_left _ (by omega)

#assert_std_axioms sBnd_sound orc_rb orc_U small_cost orc_sound

end WP.W9fF
