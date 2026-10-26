import WP.W9c.RowKit

/-!
# WP.W9c.RowA1 — row-level helpers: markers, skip, zero-test branch
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

variable {σ : Type} (K : RKit σ) {Mul : ℕ → ℕ} {C : ℕ} {ρ : List (HP 12 40 σ)}

/-- Stacks after pushing a marker on each listed stack. -/
def marksOn (B : RL → List Sym) : List RL → RL → List Sym
  | [] => B
  | k :: ks => marksOn (Function.update B k (Sym.mark :: B k)) ks

theorem ht_skip (B : RL → List Sym) : HT ρ B (TMFw.Lib.skip : HP 12 40 σ) B 1 := by
  rintro ⟨v, S⟩ hS
  exact ⟨⟨v, S⟩, 1, TMFw.Lib.skip_eval ρ ⟨v, S⟩, hS, le_rfl⟩

theorem ht_pushMarks : ∀ (ks : List RL) (B : RL → List Sym),
    HT ρ B (pushMarks ks) (marksOn B ks) (ks.length + 1)
  | [], B => ht_skip B
  | k :: ks, B => (HT.seq (HT.pushS k .mark B ρ) (ht_pushMarks ks _)).mono (by simp; omega)

theorem marksOn_not_mem : ∀ (ks : List RL) (B : RL → List Sym) (j : RL), j ∉ ks →
    marksOn B ks j = B j
  | [], B, j, _ => rfl
  | k :: ks, B, j, hj => by
    simp only [List.mem_cons, not_or] at hj
    simp only [marksOn]
    rw [marksOn_not_mem ks _ j hj.2, Function.update_of_ne hj.1]

theorem marksOn_mem : ∀ (ks : List RL) (B : RL → List Sym) (j : RL), ks.Nodup → j ∈ ks →
    marksOn B ks j = Sym.mark :: B j
  | [], B, j, _, hj => absurd hj (List.not_mem_nil)
  | k :: ks, B, j, hnd, hj => by
    rw [List.nodup_cons] at hnd
    simp only [marksOn]
    by_cases hjk : j = k
    · subst hjk
      rw [marksOn_not_mem ks _ j hnd.1, Function.update_self]
    · have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hjk
        · exact h
      rw [marksOn_mem ks _ j hnd.2 hj', Function.update_of_ne hjk]

/-- **Zero-test branch.** -/
theorem ht_ifZero (hz : SpecIsZero K.iz C) (k : RL) (B B' : RL → List Sym) (p q : HP 12 40 σ)
    (n : ℕ) (rk : List Sym) (hrk : TermOK rk) (hB : B k = natSyms n ++ rk) {T₁ T₂ : ℕ}
    (hp : n = 0 → HT ρ B p B' T₁) (hq : n ≠ 0 → HT ρ B q B' T₂) :
    HT ρ B (ifZero K k p q) B' (C + (max T₁ T₂ + 1)) := by
  have hc := callI_same' (ρ := ρ) K.iz [k] rS (List.nodup_singleton _) rfl (by norm_num) K.liz B
    (hz n rk _ hrk hB)
  refine Triple.seq hc (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hso⟩, hc⟩
    have h0 : n = 0 := by
      have : K.iz.obs (K.liz.get s.var) = true := hc
      rw [hso] at this; simpa using this
    exact (hp h0).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hso⟩, hc⟩
    have h0 : n ≠ 0 := by
      have : K.iz.obs (K.liz.get s.var) = false := by simpa using hc
      rw [hso] at this; simpa using this
    exact (hq h0).mono (le_max_right _ _) s hsB

#assert_std_axioms ht_skip ht_pushMarks marksOn_not_mem marksOn_mem ht_ifZero

end WP.W9c
