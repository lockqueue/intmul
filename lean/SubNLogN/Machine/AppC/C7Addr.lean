/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Skel

/-!
# Lemma A.9 address identity (`Machine/AppC/C7Addr.lean`): `C7AddrStmt` (pure arithmetic)

Proves `C7AddrStmt σ` (stated in `Machine/AppC/C7Skel.lean`): on the Lemma A.9 rectangle the pull maps
of the three phases keep record indices in range, and `lines ∘ repair ∘ top = packedXorAddr`.
Ingredients: mixed-radix decoding of a record index (`c7_decode`), the rank form of `c7Lift`
(`c7Lift_rank`), composition of lifts (`c7Lift_comp`), and the chunk-triple facts
`packedS0inv ∘ packedS0 = id` and `packedT0 ∘ packedTop = ` the `f`-bit XOR. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Networks AppC.Corr

namespace AppC.C7Aux

/-! ## Mixed-radix ranks -/

theorem mr_lt {x y A B : ℕ} (hx : x < A) (hy : y < B) : x * B + y < A * B := by
  calc x * B + y < x * B + B := by omega
    _ = (x + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ hx

theorem c7Rank_lt {L N0 N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ} (h0 : a0 < N0)
    (hc : ∀ i, c i < 2 ^ L) (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3) :
    c7Rank L N1 N2 N3 a0 a1 a2 a3 c < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3 :=
  mr_lt (mr_lt (mr_lt (mr_lt (mr_lt (mr_lt h0 (hc 0)) h1) (hc 1)) h2) (hc 2)) h3

/-- **Decoding** a record index into its mixed-radix coordinates. -/
theorem c7_decode (L N1 N2 N3 p : ℕ) :
    c7Rank L N1 N2 N3 (p / (N3 * 2 ^ L * N2 * 2 ^ L * N1 * 2 ^ L))
      (p / (N3 * 2 ^ L * N2 * 2 ^ L) % N1) (p / (N3 * 2 ^ L) % N2) (p % N3)
      (fun j => c7Slot L N1 N2 N3 j p) = p := by
  have e1 := Nat.div_add_mod p N3
  have e2 := Nat.div_add_mod (p / N3) (2 ^ L)
  have e3 := Nat.div_add_mod (p / N3 / 2 ^ L) N2
  have e4 := Nat.div_add_mod (p / N3 / 2 ^ L / N2) (2 ^ L)
  have e5 := Nat.div_add_mod (p / N3 / 2 ^ L / N2 / 2 ^ L) N1
  have e6 := Nat.div_add_mod (p / N3 / 2 ^ L / N2 / 2 ^ L / N1) (2 ^ L)
  simp only [Nat.div_div_eq_div_mul] at e2 e3 e4 e5 e6
  have hs0 : c7Slot L N1 N2 N3 0 p = p / (N3 * 2 ^ L * N2 * 2 ^ L * N1) % 2 ^ L := rfl
  have hs1 : c7Slot L N1 N2 N3 1 p = p / (N3 * 2 ^ L * N2) % 2 ^ L := rfl
  have hs2 : c7Slot L N1 N2 N3 2 p = p / N3 % 2 ^ L := rfl
  simp only [c7Rank, hs0, hs1, hs2]
  generalize 2 ^ L = Q at *
  zify at e1 e2 e3 e4 e5 e6 ⊢
  linear_combination e1 + (N3 : ℤ) * e2 + (N3 : ℤ) * Q * e3 + (N3 : ℤ) * Q * N2 * e4 +
    (N3 : ℤ) * Q * N2 * Q * e5 + (N3 : ℤ) * Q * N2 * Q * N1 * e6

/-- `c7Rank` is its spectator part plus the three slot contributions. -/
theorem c7Rank_split (L N1 N2 N3 a0 a1 a2 a3 : ℕ) (c : Fin 3 → ℕ) :
    c7Rank L N1 N2 N3 a0 a1 a2 a3 c = c7Rank L N1 N2 N3 a0 a1 a2 a3 (fun _ => 0) +
      (c 0 * c7Stride L N1 N2 N3 0 + c 1 * c7Stride L N1 N2 N3 1 +
        c 2 * c7Stride L N1 N2 N3 2) := by
  simp only [c7Rank, c7Stride]
  simp
  ring

/-- The named triple of a named-component function. -/
theorem nameGet_triple (t : ℕ × ℕ × ℕ) : (nameGet t 0, nameGet t 1, nameGet t 2) = t := by
  simp [nameGet]

/-- **`c7Lift` on a rank**: the slots are replaced by the image of the named triple. -/
theorem c7Lift_rank {L N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ} (σ : Equiv.Perm (Fin 3))
    (F : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (hc : ∀ i, c i < 2 ^ L) (h1 : a1 < N1) (h2 : a2 < N2)
    (h3 : a3 < N3) :
    c7Lift L N1 N2 N3 σ F (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) =
      c7Rank L N1 N2 N3 a0 a1 a2 a3
        (fun j => nameGet (F (c (σ.symm 0), c (σ.symm 1), c (σ.symm 2))) (σ j)) := by
  unfold c7Lift
  simp only [c7Slot_rank hc h1 h2 h3]
  rw [c7Rank_split L N1 N2 N3 a0 a1 a2 a3 c, Nat.add_sub_cancel]
  conv_rhs => rw [c7Rank_split]

/-- The coordinates of a record index below `M`. -/
theorem c7_coords {L N0 N1 N2 N3 p : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (hp : p < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3) :
    p / (N3 * 2 ^ L * N2 * 2 ^ L * N1 * 2 ^ L) < N0 ∧ (∀ i, c7Slot L N1 N2 N3 i p < 2 ^ L) ∧
      p / (N3 * 2 ^ L * N2 * 2 ^ L) % N1 < N1 ∧ p / (N3 * 2 ^ L) % N2 < N2 ∧ p % N3 < N3 := by
  refine ⟨?_, fun i => Nat.mod_lt _ (by positivity), Nat.mod_lt _ hN1, Nat.mod_lt _ hN2,
    Nat.mod_lt _ hN3⟩
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  calc p < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3 := hp
    _ = N0 * (N3 * 2 ^ L * N2 * 2 ^ L * N1 * 2 ^ L) := by ring

/-! ## Chunk-triple facts -/

/-- All three chunks below `2^L`. -/
def InBox (L : ℕ) (t : ℕ × ℕ × ℕ) : Prop := t.1 < 2 ^ L ∧ t.2.1 < 2 ^ L ∧ t.2.2 < 2 ^ L

/-- A line with negated sign. -/
def negOp (op : Bool × ℤ × ℕ) : Bool × ℤ × ℕ := (op.1, -op.2.1, op.2.2)

/-- Offset sum of a line, with control chunk `x` and tested chunk `o`. -/
def lineSum (K ρ f par x o : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (f - 1),
    (2 : ℤ) ^ (ρ + i * K) * (if bitAt x (ρ + i * K) = 1 ∧ bitAt o (ρ + i * K) = par then 1 else 0)

theorem packedLine_false (L K ρ f : ℕ) (ε : ℤ) (par x y z : ℕ) :
    packedLine L K ρ f (false, ε, par) (x, y, z) =
      (x, y, (((z : ℤ) + ε * lineSum K ρ f par x y) % (2 : ℤ) ^ L).toNat) := rfl

theorem packedLine_true (L K ρ f : ℕ) (ε : ℤ) (par x y z : ℕ) :
    packedLine L K ρ f (true, ε, par) (x, y, z) =
      (x, (((y : ℤ) + ε * lineSum K ρ f par x z) % (2 : ℤ) ^ L).toNat, z) := rfl

theorem toNat_emod_lt (a : ℤ) (L : ℕ) : (a % (2 : ℤ) ^ L).toNat < 2 ^ L := by
  have hpos : (0 : ℤ) < (2 : ℤ) ^ L := by positivity
  have h0 : 0 ≤ a % (2 : ℤ) ^ L := Int.emod_nonneg _ hpos.ne'
  have h1 : a % (2 : ℤ) ^ L < (2 : ℤ) ^ L := Int.emod_lt_of_pos _ hpos
  have h2 : ((a % (2 : ℤ) ^ L).toNat : ℤ) < ((2 ^ L : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]
    push_cast
    exact h1
  exact_mod_cast h2

theorem emod_roundtrip {z L : ℕ} (hz : z < 2 ^ L) (o : ℤ) :
    ((((((z : ℤ) + o) % (2 : ℤ) ^ L).toNat : ℤ) + -o) % (2 : ℤ) ^ L).toNat = z := by
  have hpos : (0 : ℤ) < (2 : ℤ) ^ L := by positivity
  have hz' : (z : ℤ) < (2 : ℤ) ^ L := by exact_mod_cast hz
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), Int.emod_add_emod, add_neg_cancel_right,
    Int.emod_eq_of_lt (by positivity) hz', Int.toNat_natCast]

theorem packedLine_inBox {L K ρ f : ℕ} (op : Bool × ℤ × ℕ) {t : ℕ × ℕ × ℕ} (ht : InBox L t) :
    InBox L (packedLine L K ρ f op t) := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨hx, hy, hz⟩ := ht
  obtain ⟨b, ε, par⟩ := op
  cases b
  · rw [packedLine_false]; exact ⟨hx, hy, toNat_emod_lt _ _⟩
  · rw [packedLine_true]; exact ⟨hx, toNat_emod_lt _ _, hz⟩

/-- A line followed by the same line with negated sign is the identity on the box. -/
theorem packedLine_neg {L K ρ f : ℕ} (op : Bool × ℤ × ℕ) {t : ℕ × ℕ × ℕ} (ht : InBox L t) :
    packedLine L K ρ f (negOp op) (packedLine L K ρ f op t) = t := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨hx, hy, hz⟩ := ht
  obtain ⟨b, ε, par⟩ := op
  cases b
  · rw [packedLine_false, show negOp (false, ε, par) = (false, -ε, par) from rfl, packedLine_false,
      neg_mul, emod_roundtrip hz]
  · rw [packedLine_true, show negOp (true, ε, par) = (true, -ε, par) from rfl, packedLine_true,
      neg_mul, emod_roundtrip hy]

/-- Folding lines keeps the box. -/
theorem foldl_lines_inBox {L K ρ f : ℕ} (g : (Bool × ℤ × ℕ) → (Bool × ℤ × ℕ)) :
    ∀ (ops : List (Bool × ℤ × ℕ)) (t : ℕ × ℕ × ℕ), InBox L t →
      InBox L (ops.foldl (fun p op => packedLine L K ρ f (g op) p) t)
  | [], _, ht => ht
  | op :: ops, _, ht => foldl_lines_inBox g ops _ (packedLine_inBox (g op) ht)

/-- Reversed negated lines undo the lines. -/
theorem foldl_lines_inv {L K ρ f : ℕ} :
    ∀ (ops : List (Bool × ℤ × ℕ)) (t : ℕ × ℕ × ℕ), InBox L t →
      ops.reverse.foldl (fun p op => packedLine L K ρ f (negOp op) p)
        (ops.foldl (fun p op => packedLine L K ρ f op p) t) = t
  | [], _, _ => rfl
  | op :: ops, t, ht => by
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      foldl_lines_inv ops _ (packedLine_inBox op ht), packedLine_neg op ht]

theorem packedS0_inBox {L K ρ f : ℕ} {t : ℕ × ℕ × ℕ} (ht : InBox L t) :
    InBox L (packedS0 L K ρ f t) :=
  foldl_lines_inBox (L := L) (K := K) (ρ := ρ) (f := f) id eightOps t ht

theorem packedS0inv_inBox {L K ρ f : ℕ} {t : ℕ × ℕ × ℕ} (ht : InBox L t) :
    InBox L (packedS0inv L K ρ f t) :=
  foldl_lines_inBox (L := L) (K := K) (ρ := ρ) (f := f) negOp eightOps.reverse t ht

theorem packedS0inv_packedS0 {L K ρ f : ℕ} {t : ℕ × ℕ × ℕ} (ht : InBox L t) :
    packedS0inv L K ρ f (packedS0 L K ρ f t) = t :=
  foldl_lines_inv eightOps t ht

/-! ## Lifts on record indices -/

theorem nameGet_lt {L : ℕ} {t : ℕ × ℕ × ℕ} (h : InBox L t) (n : Fin 3) : nameGet t n < 2 ^ L := by
  unfold nameGet
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem c7Slot_lt (L N1 N2 N3 : ℕ) (j : Fin 3) (p : ℕ) : c7Slot L N1 N2 N3 j p < 2 ^ L :=
  Nat.mod_lt _ (by positivity)

/-- `c7Lift` of a record index, in coordinates. -/
theorem c7Lift_eq {L N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (F : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (p : ℕ) :
    c7Lift L N1 N2 N3 σ F p = c7Rank L N1 N2 N3 (p / (N3 * 2 ^ L * N2 * 2 ^ L * N1 * 2 ^ L))
      (p / (N3 * 2 ^ L * N2 * 2 ^ L) % N1) (p / (N3 * 2 ^ L) % N2) (p % N3)
      (fun j => nameGet (F (c7Slot L N1 N2 N3 (σ.symm 0) p, c7Slot L N1 N2 N3 (σ.symm 1) p,
        c7Slot L N1 N2 N3 (σ.symm 2) p)) (σ j)) := by
  conv_lhs => rw [← c7_decode L N1 N2 N3 p]
  exact c7Lift_rank σ F (fun i => c7Slot_lt L N1 N2 N3 i p) (Nat.mod_lt _ hN1) (Nat.mod_lt _ hN2)
    (Nat.mod_lt _ hN3)

theorem c7Lift_lt {L N0 N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (F : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (hF : ∀ t, InBox L t → InBox L (F t))
    {p : ℕ} (hp : p < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3) :
    c7Lift L N1 N2 N3 σ F p < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3 := by
  obtain ⟨h0, hc, h1, h2, h3⟩ := c7_coords hN1 hN2 hN3 hp
  rw [c7Lift_eq hN1 hN2 hN3]
  exact c7Rank_lt h0 (fun j => nameGet_lt (hF _ ⟨hc _, hc _, hc _⟩) (σ j)) h1 h2 h3

/-- Lifts compose (the inner map must keep the box). -/
theorem c7Lift_comp {L N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (F G : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (hG : ∀ t, InBox L t → InBox L (G t)) (p : ℕ) :
    c7Lift L N1 N2 N3 σ F (c7Lift L N1 N2 N3 σ G p) = c7Lift L N1 N2 N3 σ (fun t => F (G t)) p := by
  have hb : InBox L (G (c7Slot L N1 N2 N3 (σ.symm 0) p, c7Slot L N1 N2 N3 (σ.symm 1) p,
      c7Slot L N1 N2 N3 (σ.symm 2) p)) :=
    hG _ ⟨c7Slot_lt _ _ _ _ _ _, c7Slot_lt _ _ _ _ _ _, c7Slot_lt _ _ _ _ _ _⟩
  rw [c7Lift_eq hN1 hN2 hN3 σ G p, c7Lift_rank σ F (fun j => nameGet_lt hb (σ j))
    (Nat.mod_lt _ hN1) (Nat.mod_lt _ hN2) (Nat.mod_lt _ hN3), c7Lift_eq hN1 hN2 hN3 σ _ p]
  congr 1
  funext j
  simp only [Equiv.apply_symm_apply, nameGet_triple]

/-- Lifts only depend on the map on the box. -/
theorem c7Lift_congr {L N1 N2 N3 : ℕ} (σ : Equiv.Perm (Fin 3)) {F F' : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ}
    (h : ∀ t, InBox L t → F t = F' t) (p : ℕ) :
    c7Lift L N1 N2 N3 σ F p = c7Lift L N1 N2 N3 σ F' p := by
  unfold c7Lift
  rw [h _ ⟨c7Slot_lt _ _ _ _ _ _, c7Slot_lt _ _ _ _ _ _, c7Slot_lt _ _ _ _ _ _⟩]

/-! ## The selected-bit XOR -/

theorem add_two_pow_mul_eq_xor {A J b : ℕ} (hA : A < 2 ^ J) : A + 2 ^ J * b = A ^^^ (2 ^ J * b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, add_comm, Nat.testBit_two_pow_mul_add b hA, Nat.testBit_two_pow_mul]
  by_cases hi : i < J
  · simp [hi, Nat.not_le.mpr hi]
  · have hA' : A.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, hA', Nat.le_of_not_lt hi]

/-- `T₀` after the top bit is the XOR of all `f` selected bits (`packedT0 K ρ (f + 1)`). -/
theorem packedT0_packedTop {K ρ f : ℕ} (hf : 1 ≤ f) (hρ : ρ < K) (t : ℕ × ℕ × ℕ) :
    packedT0 K ρ f (packedTop K ρ f t) = packedT0 K ρ (f + 1) t := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp only [packedT0, packedTop, Nat.add_sub_cancel, Finset.sum_range_succ]
  have hA : selMask K ρ g x < 2 ^ (ρ + g * K) :=
    lt_of_lt_of_le (selMask_lt hρ x g) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have key := add_two_pow_mul_eq_xor (b := bitAt x (ρ + g * K)) hA
  have hsel : (∑ i ∈ Finset.range g, 2 ^ (ρ + i * K) * bitAt x (ρ + i * K)) = selMask K ρ g x := rfl
  rw [hsel]
  congr 2
  show (y ^^^ 2 ^ (ρ + g * K) * bitAt x (ρ + g * K)) ^^^ selMask K ρ g x =
    y ^^^ (selMask K ρ g x + 2 ^ (ρ + g * K) * bitAt x (ρ + g * K))
  rw [key, Nat.xor_comm (selMask K ρ g x), ← Nat.xor_assoc]

/-- The named triple after `packedT0 K ρ (f + 1)`, as a slot update. -/
theorem c7_named_update (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → ℕ) (y' : ℕ) :
    (fun j => nameGet (c (σ.symm 0), y', c (σ.symm 2)) (σ j)) = Function.update c (σ.symm 1) y' := by
  funext j
  obtain ⟨v, hv⟩ : ∃ v, σ j = v := ⟨_, rfl⟩
  have hj : j = σ.symm v := by rw [← hv, Equiv.symm_apply_apply]
  subst hj
  fin_cases v <;> simp [nameGet]

/-- `packedXorAddr` is the lift of `packedT0 K ρ (f + 1)`. -/
theorem packedXorAddr_eq_lift {K ρ f N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (σ : Equiv.Perm (Fin 3)) (p : ℕ) :
    packedXorAddr (f * K) K ρ f N1 N2 N3 σ p =
      c7Lift (f * K) N1 N2 N3 σ (packedT0 K ρ (f + 1)) p := by
  rw [c7Lift_eq hN1 hN2 hN3]
  conv_lhs => rw [← c7_decode (f * K) N1 N2 N3 p]
  rw [packedXorAddr_rank σ (fun i => c7Slot_lt _ _ _ _ i p) (Nat.mod_lt _ hN1) (Nat.mod_lt _ hN2)
    (Nat.mod_lt _ hN3)]
  congr 1
  have ht : packedT0 K ρ (f + 1) (c7Slot (f * K) N1 N2 N3 (σ.symm 0) p,
      c7Slot (f * K) N1 N2 N3 (σ.symm 1) p, c7Slot (f * K) N1 N2 N3 (σ.symm 2) p) =
      (c7Slot (f * K) N1 N2 N3 (σ.symm 0) p,
        Nat.xor (c7Slot (f * K) N1 N2 N3 (σ.symm 1) p)
          (selMask K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) p)),
        c7Slot (f * K) N1 N2 N3 (σ.symm 2) p) := by
    simp only [packedT0, Nat.add_sub_cancel]
    rfl
  rw [ht]
  exact (c7_named_update σ (fun j => c7Slot (f * K) N1 N2 N3 j p) _).symm

end AppC.C7Aux

open AppC.C7Aux

/-- **Lemma A.9 address identity** (`c7Addr_holds`, 0 `sorry`): `C7AddrStmt σ` holds for every chunk
arrangement `σ`. -/
theorem c7Addr_holds (σ : Equiv.Perm (Fin 3)) : C7AddrStmt σ := by
  intro K ρ f N0 N1 N2 N3 hK hρ hf hN0 hN1 hN2 hN3 p hp
  have hpM : p < N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := hp
  have hmask : ∀ g, g ≤ f → ∀ x, selMask K ρ g x < 2 ^ (f * K) := fun g hg x =>
    lt_of_lt_of_le (selMask_lt hρ x g)
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right K hg))
  have hTop : ∀ t, InBox (f * K) t → InBox (f * K) (packedTop K ρ f t) := by
    rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩
    refine ⟨hx, Nat.xor_lt_two_pow hy ?_, hz⟩
    have hJ : ρ + (f - 1) * K < f * K := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.succ_mul]
      omega
    have hb : bitAt x (ρ + (f - 1) * K) ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    calc 2 ^ (ρ + (f - 1) * K) * bitAt x (ρ + (f - 1) * K) ≤ 2 ^ (ρ + (f - 1) * K) * 1 :=
          Nat.mul_le_mul_left _ hb
      _ < 2 ^ (f * K) := by rw [Nat.mul_one]; exact Nat.pow_lt_pow_right (by norm_num) hJ
  have hT0 : ∀ t, InBox (f * K) t → InBox (f * K) (packedT0 K ρ f t) := by
    rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩
    exact ⟨hx, Nat.xor_lt_two_pow hy (hmask (f - 1) (by omega) x), hz⟩
  have hRep : ∀ t, InBox (f * K) t →
      InBox (f * K) (packedS0 (f * K) K ρ f (packedT0 K ρ f t)) :=
    fun t ht => packedS0_inBox (hT0 t ht)
  have hInv : ∀ t, InBox (f * K) t → InBox (f * K) (packedS0inv (f * K) K ρ f t) :=
    fun t ht => packedS0inv_inBox ht
  refine ⟨c7Lift_lt hN1 hN2 hN3 σ _ hInv hpM, c7Lift_lt hN1 hN2 hN3 σ _ hRep hpM,
    c7Lift_lt hN1 hN2 hN3 σ _ hTop hpM, ?_⟩
  unfold c7LinesInv c7RepairInv c7TopInv
  rw [c7Lift_comp hN1 hN2 hN3 σ _ _ hTop,
    c7Lift_comp hN1 hN2 hN3 σ _ _ (fun t ht => hRep _ (hTop t ht)),
    c7Lift_congr σ (F' := packedT0 K ρ (f + 1)) (fun t ht => by
      rw [packedS0inv_packedS0 (hT0 _ (hTop t ht)), packedT0_packedTop hf hρ]) p,
    packedXorAddr_eq_lift hN1 hN2 hN3 σ p]

end SubNLogN.Machine
