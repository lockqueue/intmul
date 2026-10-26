import WP.W4.Body
import WP.W4.Unsh
import IntMulTM.Framework.Lib.CompareEval
import Mathlib.Tactic.Ring

/-!
# WP.W4.Modes — the transpose program, parametrized by the riffle pass

`transposeProgP riffP oi oo`: compare `a` and `b` (`cmpNum`); if `a > b` run `b` unshuffle passes,
else `a` riffle passes (`riffP`). `transposeProgP_spec` proves the `W4_transpose` post-state from the
riffle pass's `PassSpec`; `w4_transpose_of_riff` packages the contract (cost constant 64).
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem body_spec (pass : SProg L44) (E : L44) (hE : E = .inl 2 ∨ E = .inl 3) (oi oo : Orient)
    (N L k c : ℕ) (f : List (List Sym) → List (List Sym))
    (hP : 0 < k → PassSpec [] pass (.inr 0) side44 N L f c ∧ ∀ l, Good N L l → Good N L (f l))
    (v : List (List Sym)) (hv : Good N L v) (rest rE : List Sym) (hrest : BlkTerm rest)
    (hrE : TermOK rE) (S : L44 → List Sym) (hS0 : S (.inl 0) = blk oi v ++ rest)
    (hSE : S E = natSyms k ++ rE) :
    RunsIn [] (body pass E oi oo) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (blk oo (f^[k] v) ++ S (.inl 1)))
      (12 * L + 7 * bitLen k + k * (c + 6 * k + 10) + 31) := by
  have hw : Good N L (f^[k] v) := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      exact hv
    · exact iterate_good (hP hpos).2 k v hv
  have r1 := prefix_spec E hE oi v hv.2.2 rest rE hrest hrE k S hS0 hSE
  set S7 := Function.update (Function.update (Function.update (Function.update
    (Function.update S (.inr 0) (v.flatten ++ Sym.mark :: S (.inr 0))) (.inr 1)
    (Sym.mark :: S (.inr 1))) (.inr 2) (Sym.mark :: S (.inr 2))) (.inr 3)
    (Sym.mark :: S (.inr 3))) (.inl 0) (natSyms k ++ Sym.mark :: rest) with hS7
  have h7s : side44 S7 :=
    ⟨⟨S (.inr 1), by simp [hS7]⟩, ⟨S (.inr 2), by simp [hS7]⟩, ⟨S (.inr 3), by simp [hS7]⟩⟩
  have r2 := passLoop_spec (Q := (.inl 0 : L44)) (T := .inl 1) (X := .inr 0) (by decide)
    (by decide) [] side44 N L c f k hP (fun S x h => side44_update h _ (Or.inl rfl) x)
    (fun S x h => side44_update h _ (Or.inr rfl) x) v S7 (S (.inr 0)) (Sym.mark :: rest) hv h7s
    (by simp [hS7]) (TermOK.cons (by rfl) _) (by simp [hS7])
  set S8 := Function.update (Function.update S7 (.inr 0)
    ((f^[k] v).flatten ++ Sym.mark :: S (.inr 0))) (.inl 0) (Sym.mark :: rest) with hS8
  have r3 := suffix_spec oo (f^[k] v) hw.2.2 rest (S (.inr 0)) (S (.inr 1)) (S (.inr 2))
    (S (.inr 3)) S8 (by simp [hS8]) (by simp [hS8]) (by simp [hS8, hS7]) (by simp [hS8, hS7])
    (by simp [hS8, hS7])
  refine RunsIn.of_eq (r1.seq (r2.seq r3)) ?_ ?_
  · apply loc44_ext <;> simp [hS8, hS7]
  · have h1 := hw.2.1
    have h2 := hv.2.1
    omega

theorem freeBelow_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), (p.liftRegs l).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .ite _ p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .loop _ p, d => freeBelow_liftRegs l p d
  | .fix b, d => freeBelow_liftRegs l b (d + 1)
  | .recur _, _ => Iff.rfl

/-- **The transpose program**, for a given riffle pass. -/
def transposeProgP (riffP : SProg L44) (oi oo : Orient) : Prog L44 (fun _ => Sym) CReg :=
  .seq (cmpNum (.inl 2) (.inl 3) (.inr 0) (.inr 1))
    (.ite (fun r => decide (r.2.2 = Ordering.gt))
      (Prog.liftRegs L1 (body (unshPass (.inr 0) (.inr 1) (.inr 2)) (.inl 3) oi oo))
      (Prog.liftRegs L1 (body riffP (.inl 2) oi oo)))

theorem transposeProgP_closed {riffP : SProg L44} (hc : riffP.Closed) (oi oo : Orient) :
    (transposeProgP riffP oi oo).Closed := by
  have hb1 := body_closed (unshPass_closed (.inr 0 : L44) (.inr 1) (.inr 2)) (.inl 3) oi oo
  have hb2 := body_closed hc (.inl 2) oi oo
  simp only [Prog.Closed] at hb1 hb2 ⊢
  simp [transposeProgP, Prog.FreeBelow, cmpNum, cmpBody, freeBelow_liftRegs, pushC, popR, pushR,
    restoreR, moveBits, moveBitsBody, skip, hb1, hb2]

theorem unsh_passSpec (N L : ℕ) (hN : N % 2 = 0) :
    PassSpec [] (unshPass (.inr 0 : L44) (.inr 1) (.inr 2)) (.inr 0) side44 N L unsh
      (24 * L + 24) := by
  intro l S X0 hl hs hX
  obtain ⟨⟨Y0, hY⟩, ⟨Z0, hZ⟩, _⟩ := hs
  exact unshPass_spec (by decide) (by decide) (by decide) [] N L l hl hN S X0 Y0 Z0 hX hY hZ

theorem even_two_pow_mul (a b : ℕ) (h : 0 < a ∨ 0 < b) : 2 ^ a * 2 ^ b % 2 = 0 := by
  rcases h with h | h
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [show 2 ^ (a' + 1) * 2 ^ b = 2 * (2 ^ a' * 2 ^ b) by rw [pow_succ]; ring]
    exact Nat.mul_mod_right 2 _
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [show 2 ^ a * 2 ^ (b' + 1) = 2 * (2 ^ a * 2 ^ b') by rw [pow_succ]; ring]
    exact Nat.mul_mod_right 2 _

/-- Cost arithmetic of the whole program. -/
theorem cost_le (a b L : ℕ) (hL : 2 ^ a * 2 ^ b ≤ L) :
    12 * (bitLen a + bitLen b) + 16 + (12 * L + 7 * bitLen (min a b) +
      min a b * (24 * L + 24 + 6 * min a b + 10) + 31) ≤
    64 * (L + 1) * (min a b + 1) + 64 * (bitLen a + bitLen b + 1) := by
  set k := min a b with hk
  have hkL : k ≤ L := by
    have h1 : k ≤ a := Nat.min_le_left a b
    have h2 : a < 2 ^ a := Nat.lt_two_pow_self
    have h3 : 2 ^ a ≤ 2 ^ a * 2 ^ b := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos b)
    omega
  have hbk : bitLen k ≤ k := bitLen_le_self k
  have h1 : k * (24 * L + 24 + 6 * k + 10) ≤ k * (34 * (L + 1)) :=
    Nat.mul_le_mul_left k (by omega)
  have h2 : k * (34 * (L + 1)) = 34 * ((L + 1) * k) := by ring
  have h3 : 64 * (L + 1) * (k + 1) = 64 * ((L + 1) * k) + 64 * (L + 1) := by ring
  rw [h3]
  omega

#assert_std_axioms body_spec freeBelow_liftRegs transposeProgP_closed unsh_passSpec
  even_two_pow_mul cost_le

end TMFw.W4
