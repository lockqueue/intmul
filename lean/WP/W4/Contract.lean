import WP.W4.Modes

/-!
# WP.W4.Contract — `W4_transpose oi oo` from any riffle pass meeting `RiffOK`

`RiffOK riffP`: `riffP` is closed and computes `riff` on `X = .inr 0` (scratch `Y Z U` marked)
within `24·|blk| + 24` steps for every even record count. `WP.W4.Riff` provides one.
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- The riffle pass obligation. -/
def RiffOK (riffP : SProg L44) : Prop :=
  riffP.Closed ∧ ∀ N L : ℕ, N % 2 = 0 → PassSpec [] riffP (.inr 0) side44 N L riff (24 * L + 24)

theorem transposeProgP_spec {riffP : SProg L44} (hR : RiffOK riffP) (oi oo : Orient) (a b : ℕ)
    (v : List (List Sym)) (rest r2 r3 : List Sym) (S : L44 → List Sym)
    (hlen : v.length = 2 ^ a * 2 ^ b) (hrec : ∀ r ∈ v, RecOK r) (hrest : BlkTerm rest)
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hS0 : S (.inl 0) = blk oi v ++ rest)
    (hS2 : S (.inl 2) = natSyms a ++ r2) (hS3 : S (.inl 3) = natSyms b ++ r3) :
    Runs (transposeProgP riffP oi oo) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (blk oo (transposeL (2 ^ a) (2 ^ b) v) ++ S (.inl 1))) (fun _ => True)
      (12 * (bitLen a + bitLen b) + 16 + (12 * v.flatten.length + 7 * bitLen (min a b) +
        min a b * (24 * v.flatten.length + 24 + 6 * min a b + 10) + 31)) := by
  have hv : Good (2 ^ a * 2 ^ b) v.flatten.length v := ⟨hlen, rfl, hrec⟩
  refine Runs.of_eval fun v0 => ?_
  have e1 := cmpNum_eval (k₁ := (.inl 2 : L44)) (k₂ := .inl 3) (t₁ := .inr 0) (t₂ := .inr 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) v0 (encodeNat a)
    (encodeNat b) r2 r3 S hr2 hr3 hS2 hS3
  have hord : cmpAll .eq (encodeNat a) (encodeNat b) = ordOf a b := by
    rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
      bitsVal_encodeNat]
  rw [hord] at e1
  have hmin : min (encodeNat a).length (encodeNat b).length ≤ bitLen a + bitLen b := by
    simp only [bitLen]
    omega
  by_cases hgt : ordOf a b = .gt
  · have hba : b < a := by
      unfold ordOf at hgt
      split_ifs at hgt with h1 h2
      omega
    have hb := body_spec (unshPass (.inr 0) (.inr 1) (.inr 2)) (.inl 3) (Or.inr rfl) oi oo
      (2 ^ a * 2 ^ b) v.flatten.length b (24 * v.flatten.length + 24) unsh
      (fun hpos => ⟨unsh_passSpec _ _ (even_two_pow_mul a b (Or.inr hpos)), fun l hl => hl.unsh⟩)
      v hv rest r3 hrest hr3 S hS0 hS3
    rw [unsh_iterate_eq_transposeL b a v hlen] at hb
    obtain ⟨v', t, e, ht⟩ := RunsIn.liftRegs L1 hb (some Sym.mark, some Sym.mark, ordOf a b)
    refine ⟨v', _, Eval.seq e1 (Eval.ite_true (by simp [hgt]) e), trivial, ?_⟩
    rw [show min a b = b by omega]
    omega
  · have hab : a ≤ b := by
      unfold ordOf at hgt
      split_ifs at hgt with h1 h2 <;> first | omega | simp at hgt
    have hb := body_spec riffP (.inl 2) (Or.inl rfl) oi oo (2 ^ a * 2 ^ b) v.flatten.length a
      (24 * v.flatten.length + 24) riff
      (fun hpos => ⟨hR.2 _ _ (even_two_pow_mul a b (Or.inl hpos)),
        fun l hl => hl.riff (even_two_pow_mul a b (Or.inl hpos))⟩)
      v hv rest r2 hrest hr2 S hS0 hS2
    rw [riff_iterate_eq_transposeL a b v hlen] at hb
    obtain ⟨v', t, e, ht⟩ := RunsIn.liftRegs L1 hb (some Sym.mark, some Sym.mark, ordOf a b)
    refine ⟨v', _, Eval.seq e1 (Eval.ite_false (by simp [hgt]) e), trivial, ?_⟩
    rw [show min a b = a by omega]
    omega

/-- **W4.transpose from a riffle pass**, all orientations, cost constant `64`. -/
theorem w4_transpose_of_riff {riffP : SProg L44} (hR : RiffOK riffP) (oi oo : Orient) :
    W4_transpose oi oo := by
  refine ⟨64, fun _ => ⟨4, CReg, fun _ => (), transposeProgP riffP oi oo, le_rfl, inferInstance,
    inferInstance, transposeProgP_closed hR.1 oi oo, ?_⟩⟩
  intro a b v rest r2 r3 S hlen hrec hrest hr2 hr3 hS0 hS2 hS3
  have hblk : (blk oi v).length = v.flatten.length := by cases oi <;> simp [blk]
  have hNL : 2 ^ a * 2 ^ b ≤ v.flatten.length := by
    rw [← hlen]
    exact length_le_length_flatten v hrec
  rw [hblk]
  exact Triple.cost_mono (transposeProgP_spec hR oi oo a b v rest r2 r3 S hlen hrec hrest hr2 hr3
    hS0 hS2 hS3) (cost_le a b _ hNL)

#assert_std_axioms transposeProgP_spec w4_transpose_of_riff

end TMFw.W4
