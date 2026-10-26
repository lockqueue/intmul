import SubNLogN.Spec

/-!
# Component S2 (`Streams.lean`): Arithmetic Divisibility & Amortization Checks

**Scope.** Proves elementary `ℕ` divisibility (`(W * g) / W = g`, `(W * g) % W = 0`) and linear-scan overhead inequalities accompanying Lemma A.5 (`lem:transfer-long-record`) and Proposition A.7 (`prop:transfer11`).
The `TM2` stream kernels (Lemmas A.4–A.5, Proposition A.7) live in `SubNLogN/Machine/{K1,AppC}/`.
-/

namespace SubNLogN.S2

open SubNLogN

/-- **Role-Split Volume Preservation (Proposition A.7 (`prop:transfer11`)):**
Splitting `W * g` rows cyclically among `W > 0` role streams assigns `g` rows to each role with
zero remainder, and every role at depth `k` retains divisibility by `W^{k-1}` when the initial
row count is `W^k * g₀`. -/
theorem role_split_volume_exact (W g : ℕ) (hW : 0 < W) :
    (W * g) / W = g ∧ (W * g) % W = 0 :=
  ⟨Nat.mul_div_right g hW, Nat.mul_mod_right W g⟩

/-- Recursive role-split divisibility across `k` levels of Proposition A.7 (`prop:transfer11`):
`(W ^ (k + 1) * g₀) / W = W ^ k * g₀`. -/
theorem role_split_pow_succ (W k g₀ : ℕ) (hW : 0 < W) :
    (W ^ (k + 1) * g₀) / W = W ^ k * g₀ := by
  have h : W ^ (k + 1) * g₀ = W * (W ^ k * g₀) := by
    rw [Nat.pow_succ', Nat.mul_assoc]
  rw [h, Nat.mul_div_right _ hW]

/-- **Long-Record Address Overhead Amortization (Lemma A.5 (`lem:transfer-long-record`)):**
If `M` records each have payload length `r * P` and per-record address preparation takes `A` steps
with `A ≤ C * r * P`, then total cost `M * (A + r * P)` is bounded by `(C + 1) * (M * r * P)`. -/
theorem long_record_scan_amortized (M r P A C : ℕ) (hA : A ≤ C * (r * P)) :
    M * (A + r * P) ≤ (C + 1) * (M * r * P) := by
  calc M * (A + r * P)
      ≤ M * (C * (r * P) + r * P) := Nat.mul_le_mul_left M (Nat.add_le_add_right hA (r * P))
    _ = (C + 1) * (M * r * P) := by ring

end SubNLogN.S2
