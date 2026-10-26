import WP.W5.KLoop

/-!
# WP.W5.School — the base case (shift-and-add), from the branch state `Ebr`

Base case `max(|a|,|b|) ≤ 9` bits: `s4 := |a|`, `s5 := |b|`, `s6 := 0`; while `s5 ≠ 0`:
if the LSB of `s5` is `1` then `s6 += s4`; `s4 := 2·s4`; `s5 := s5 / 2`. Then the sign, the output on
`Z`, and every frame cleared.

Invariant after `i` rounds (`sE`): `s4 = |a|·2^i`, `s5 = |b| / 2^i`, `s6 = |a|·(|b| mod 2^i)`.
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-- The abstract state at the branch point (after prologue, counter loop and threshold test). -/
def Ebr (a b : ℤ) (K : ℕ) : L → List Ent := fun k =>
  if k = X then [.I a] else if k = Y then [.I b] else if k = s0 then [.N K, .S]
  else if k = s3 then [.N (K / 2 / 2), .S] else [.S]

theorem allLe_Ebr (a b : ℤ) (K m : ℕ) (ha : bitLen a.natAbs ≤ m) (hb : bitLen b.natAbs ≤ m)
    (hK : bitLen K ≤ m) : AllLe (Ebr a b K) m := by
  intro k e he
  unfold Ebr at he
  split_ifs at he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; exact ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; exact hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hK
    · exact Nat.zero_le _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact le_trans (bitLen_div_le _ _) (le_trans (bitLen_div_le _ _) hK)
    · exact Nat.zero_le _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; exact Nat.zero_le _

theorem natAbs_mul_pow2 (A i : ℕ) : ((A : ℤ) * 2 ^ i).natAbs = A * 2 ^ i := by
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]; rfl

theorem natAbs_mul_cast (A n : ℕ) : ((A : ℤ) * (n : ℤ)).natAbs = A * n := by
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]

/-- School state after `i` rounds. -/
def sE (a b : ℤ) (K i : ℕ) : L → List Ent :=
  Function.update (Function.update (Function.update (Ebr a b K)
    s4 [.I ((a.natAbs : ℤ) * 2 ^ i), .S]) s5 [.N (b.natAbs / 2 ^ i), .S])
    s6 [.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ i : ℕ) : ℤ)), .S]

/-- After the conditional addition of round `i`. -/
def sM (a b : ℤ) (K i : ℕ) : L → List Ent :=
  Function.update (Function.update (Function.update (Ebr a b K)
    s4 [.I ((a.natAbs : ℤ) * 2 ^ i), .S]) s5 [.N (b.natAbs / 2 ^ i), .S])
    s6 [.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ (i + 1) : ℕ) : ℤ)), .S]

theorem allLe_school (a b : ℤ) (K i j : ℕ) (ha : bitLen a.natAbs ≤ 9) (hb : bitLen b.natAbs ≤ 9)
    (hK : K ≤ 3) (hi : i ≤ 9) :
    AllLe (Function.update (Function.update (Function.update (Ebr a b K)
      s4 [.I ((a.natAbs : ℤ) * 2 ^ i), .S]) s5 [.N (b.natAbs / 2 ^ i), .S])
      s6 [.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ j : ℕ) : ℤ)), .S]) 20 := by
  have hK' : bitLen K ≤ 20 := le_trans (bitLen_le_self K) (by omega)
  refine (((allLe_Ebr a b K 20 (by omega) (by omega) hK').update s4 _ ?_).update s5 _ ?_).update
    s6 _ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · show bitLen ((a.natAbs : ℤ) * 2 ^ i).natAbs ≤ 20
      rw [natAbs_mul_pow2]
      have := bitLen_mul_pow_le a.natAbs i
      omega
    · exact Nat.zero_le _
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact le_trans (bitLen_div_le _ _) (by omega)
    · exact Nat.zero_le _
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · show bitLen ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ j : ℕ) : ℤ)).natAbs ≤ 20
      rw [natAbs_mul_cast]
      have h1 := bitLen_mul_le a.natAbs (b.natAbs % 2 ^ j)
      have h2 := bitLen_mod_le b.natAbs (2 ^ j)
      omega
    · exact Nat.zero_le _

/-- Cost bound of the base case. -/
def schoolCost (Cu : ℕ) : ℕ := 84 * unit Cu 22 + 100

section School

variable {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) {B : L → List Sym}
  (hB : ∀ k, bokXY k = true → TermOK (B k)) (ρ : List (Prog L (fun _ => Sym) U.σ))

include hU hB in
/-- One round of the base case. -/
theorem sround (a b : ℤ) (K i : ℕ) (ha : bitLen a.natAbs ≤ 9) (hb : bitLen b.natAbs ≤ 9)
    (hK : K ≤ 3) (hi : i < bitLen b.natAbs) :
    Triple ρ (fun s => s.stk = stOf (sE a b K i) B ∧
        s.var.1 = (natSyms (b.natAbs / 2 ^ i) ++ Sym.sep :: B s5).head?)
      (sbodyP U)
      (fun s => s.stk = stOf (sE a b K (i + 1)) B ∧
        s.var.1 = (natSyms (b.natAbs / 2 ^ (i + 1)) ++ Sym.sep :: B s5).head?)
      (5 * unit Cu 22 + 7) := by
  have hq : 0 < b.natAbs / 2 ^ i := by
    have h1 : ¬ (b.natAbs < 2 ^ i) := fun h => absurd (bitLen_le_of_lt h) (by omega)
    exact Nat.div_pos (by omega) (Nat.two_pow_pos _)
  have hA0 := allLe_school a b K i i ha hb hK (by omega)
  have hAm := allLe_school a b K i (i + 1) ha hb hK (by omega)
  have hhead : (natSyms (b.natAbs / 2 ^ i) ++ Sym.sep :: B s5).head? =
      some (Sym.bit (decide (b.natAbs / 2 ^ i % 2 = 1))) := by
    rw [natSyms_pos _ hq]; rfl
  -- the conditional addition
  have TA : Triple ρ (fun s => (s.stk = stOf (sE a b K i) B ∧
        s.var.1 = (natSyms (b.natAbs / 2 ^ i) ++ Sym.sep :: B s5).head?) ∧ rOne U s.var = true)
      (seqOf U schoolAdd) (fun s => s.stk = stOf (sM a b K i) B) (4 * unit Cu 21 + 1) := by
    rintro s ⟨⟨hs, hv⟩, hc⟩
    have hbit : b.natAbs / 2 ^ i % 2 = 1 := by
      simp only [rOne, hv, hhead, decide_eq_true_eq, Option.some.injEq, Sym.bit.injEq] at hc
      simpa using hc
    have R := run_post hU hB ρ 0 (rfl : run bokXY 0 schoolAdd (sE a b K i) = some _) (by simp) hA0
      (sM a b K i) (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (by
          show [Ent.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ i : ℕ) : ℤ) + (a.natAbs : ℤ) * 2 ^ i),
            Ent.S] = [Ent.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ (i + 1) : ℕ) : ℤ)), Ent.S]
          rw [Nat.mod_pow_succ, hbit]
          congr 2
          push_cast
          ring)
        rfl) 4 0 1 0 21 rfl rfl rfl rfl rfl
    exact R.1 s hs
  have TS : Triple ρ (fun s => (s.stk = stOf (sE a b K i) B ∧
        s.var.1 = (natSyms (b.natAbs / 2 ^ i) ++ Sym.sep :: B s5).head?) ∧ rOne U s.var = false)
      (skip : Prog L (fun _ => Sym) U.σ) (fun s => s.stk = stOf (sM a b K i) B) 1 := by
    rintro s ⟨⟨hs, hv⟩, hc⟩
    have hbit : b.natAbs / 2 ^ i % 2 = 0 := by
      simp only [rOne, hv, hhead, decide_eq_false_iff_not, Option.some.injEq, Sym.bit.injEq] at hc
      simp at hc
      omega
    refine ⟨s, 1, skip_eval ρ s, ?_, le_rfl⟩
    show s.stk = _
    rw [hs]
    congr 1
    refine L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ rfl
    show [Ent.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ i : ℕ) : ℤ)), Ent.S] =
      [Ent.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ (i + 1) : ℕ) : ℤ)), Ent.S]
    rw [Nat.mod_pow_succ, hbit]
    simp
  -- the shifts
  have RS := run_post hU hB ρ 0 (rfl : run bokXY 0 schoolSh (sM a b K i) = some _)
    (by simp [SmallOp.ok]) hAm (sE a b K (i + 1))
    (L_funext rfl rfl rfl rfl rfl rfl rfl
      (by
        show [Ent.I (SmallOp.apply .mul2 ((a.natAbs : ℤ) * 2 ^ i)), Ent.S] =
          [Ent.I ((a.natAbs : ℤ) * 2 ^ (i + 1)), Ent.S]
        simp only [SmallOp.apply, pow_succ]
        congr 2
        ring)
      (by
        show [Ent.N (b.natAbs / 2 ^ i / 2), Ent.S] = [Ent.N (b.natAbs / 2 ^ (i + 1)), Ent.S]
        rw [Nat.div_div_eq_div_mul, ← pow_succ])
      rfl rfl) 1 3 2 0 22 rfl rfl rfl rfl rfl
  have TP := peekL_triple ρ (stOf (sE a b K (i + 1)) B) s5
  unfold sbodyP
  refine (Triple.seq (Triple.ite (T := 4 * unit Cu 21 + 1) TA (TS.cost_mono (by omega)))
    (Triple.seq RS.1 TP)).conseq (fun s hs => hs) (fun s hs => ⟨hs.1, ?_⟩) ?_
  · rw [hs.2]
    rw [stOf_head (sE a b K (i + 1)) B (rfl : sE a b K (i + 1) s5 = _)]
    rfl
  · have := unit_mono Cu (show 21 ≤ 22 by omega)
    omega

/-- The final school state, normalized. -/
def sF (a b : ℤ) (K : ℕ) : L → List Ent :=
  Function.update (Function.update (Function.update (Ebr a b K)
    s4 [.I ((a.natAbs : ℤ) * 2 ^ bitLen b.natAbs), .S]) s5 [.N 0, .S])
    s6 [.I ((a.natAbs : ℤ) * (b.natAbs : ℤ)), .S]

include hU hB in
/-- Initialization of the base case. -/
theorem school_init (a b : ℤ) (K : ℕ) (ha : bitLen a.natAbs ≤ 9) (hb : bitLen b.natAbs ≤ 9)
    (hK : K ≤ 3) :
    Triple ρ (fun s => s.stk = stOf (Ebr a b K) B) (seqOf U schoolInit)
      (fun s => s.stk = stOf (sE a b K 0) B) (2 * unit Cu 20 + 4 + 1) :=
  (run_post hU hB ρ 0 (rfl : run bokXY 0 schoolInit (Ebr a b K) = some _) (by simp)
    (allLe_Ebr a b K 20 (by omega) (by omega) (le_trans (bitLen_le_self K) (by omega)))
    (sE a b K 0)
    (L_funext rfl rfl rfl rfl rfl rfl rfl
      (by show [Ent.I ((a.natAbs : ℤ)), Ent.S] = [Ent.I ((a.natAbs : ℤ) * 2 ^ 0), Ent.S]; simp)
      (by show [Ent.N b.natAbs, Ent.S] = [Ent.N (b.natAbs / 2 ^ 0), Ent.S]; simp)
      (by
        show [Ent.I 0, Ent.S] = [Ent.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ 0 : ℕ) : ℤ)), Ent.S]
        simp)
      rfl) 2 4 0 0 20 rfl rfl rfl rfl rfl).1

theorem allLe_sF (a b : ℤ) (K : ℕ) (ha : bitLen a.natAbs ≤ 9) (hb : bitLen b.natAbs ≤ 9)
    (hK : K ≤ 3) : AllLe (sF a b K) 20 := by
  have h := allLe_school a b K (bitLen b.natAbs) (bitLen b.natAbs) ha hb hK hb
  unfold sF
  refine ((allLe_Ebr a b K 20 (by omega) (by omega) (le_trans (bitLen_le_self K) (by omega))).update
    s4 _ (h.all s4)).update s5 _ ?_ |>.update s6 _ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [Ent.len, bitLen_zero]
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · show bitLen ((a.natAbs : ℤ) * (b.natAbs : ℤ)).natAbs ≤ 20
      rw [natAbs_mul_cast]
      have := bitLen_mul_le a.natAbs b.natAbs
      omega
    · exact Nat.zero_le _

include hU hB in
/-- Output of the base case. -/
theorem school_fin (a b : ℤ) (K : ℕ) (ha : bitLen a.natAbs ≤ 9) (hb : bitLen b.natAbs ≤ 9)
    (hK : K ≤ 3) :
    Triple ρ (fun s => s.stk = stOf (sF a b K) B) (seqOf U (finOps s6))
      (fun s => s.stk = stOf (Function.update (E0 a b) Z [.I (a * b)]) B)
      (37 * unit Cu 20 + 19 + 1) :=
  (run_post hU hB ρ 0 (rfl : run bokXY 0 (finOps s6) (sF a b K) = some _) (by simp)
    (allLe_sF a b K ha hb hK) (Function.update (E0 a b) Z [.I (a * b)])
    (L_funext rfl rfl
      (by
        show [Ent.I (sgnFix a b ((a.natAbs : ℤ) * (b.natAbs : ℤ)))] = [Ent.I (a * b)]
        rw [sgnFix_natAbs_mul])
      rfl rfl rfl rfl rfl rfl rfl rfl) 37 19 0 0 20 rfl rfl rfl rfl rfl).1

include hU hB in
/-- **The base case**: from the branch state, `Z += a·b`, every frame cleared. -/
theorem school_spec (a b : ℤ) (K : ℕ) (ha : bitLen a.natAbs ≤ 9) (hb : bitLen b.natAbs ≤ 9)
    (hK : K ≤ 3) :
    Triple ρ (fun s => s.stk = stOf (Ebr a b K) B) (schoolP U)
      (fun s => s.stk = stOf (Function.update (E0 a b) Z [.I (a * b)]) B) (schoolCost Cu) := by
  have R0 := school_init hU hB ρ a b K ha hb hK
  have TP0 := peekL_triple ρ (stOf (sE a b K 0) B) s5
  -- the loop
  have hstep : ∀ n, Triple ρ (fun s => n + 1 ≤ bitLen b.natAbs ∧
        s.stk = stOf (sE a b K (bitLen b.natAbs - (n + 1))) B ∧
        s.var.1 = (natSyms (b.natAbs / 2 ^ (bitLen b.natAbs - (n + 1))) ++ Sym.sep :: B s5).head?)
      (sbodyP U) (fun s => n ≤ bitLen b.natAbs ∧
        s.stk = stOf (sE a b K (bitLen b.natAbs - n)) B ∧
        s.var.1 = (natSyms (b.natAbs / 2 ^ (bitLen b.natAbs - n)) ++ Sym.sep :: B s5).head?)
      (5 * unit Cu 22 + 7) := by
    intro n
    rintro s ⟨hn, hs, hv⟩
    have e : bitLen b.natAbs - (n + 1) + 1 = bitLen b.natAbs - n := by omega
    obtain ⟨s', t, ev, ⟨hs', hv'⟩, ht⟩ :=
      sround hU hB ρ a b K (bitLen b.natAbs - (n + 1)) ha hb hK (by omega) s ⟨hs, hv⟩
    rw [e] at hs' hv'
    exact ⟨s', t, ev, ⟨by omega, hs', hv'⟩, ht⟩
  have hcont : ∀ n (s : St L (fun _ => Sym) U.σ), (n + 1 ≤ bitLen b.natAbs ∧
      s.stk = stOf (sE a b K (bitLen b.natAbs - (n + 1))) B ∧
      s.var.1 = (natSyms (b.natAbs / 2 ^ (bitLen b.natAbs - (n + 1))) ++ Sym.sep :: B s5).head?) →
      rBit U s.var = true := by
    rintro n s ⟨hn, -, hv⟩
    show optIsBit s.var.1 = true
    rw [hv, optIsBit_natSyms _ _ (TermOK.cons rfl _)]
    have h1 : ¬ (b.natAbs < 2 ^ (bitLen b.natAbs - (n + 1))) := fun h =>
      absurd (bitLen_le_of_lt h) (by omega)
    have := Nat.div_pos (show 2 ^ (bitLen b.natAbs - (n + 1)) ≤ b.natAbs by omega)
      (Nat.two_pow_pos (bitLen b.natAbs - (n + 1)))
    simp only [ne_eq, decide_eq_true_eq]
    omega
  have hstop : ∀ (s : St L (fun _ => Sym) U.σ), (0 ≤ bitLen b.natAbs ∧
      s.stk = stOf (sE a b K (bitLen b.natAbs - 0)) B ∧
      s.var.1 = (natSyms (b.natAbs / 2 ^ (bitLen b.natAbs - 0)) ++ Sym.sep :: B s5).head?) →
      rBit U s.var = false := by
    rintro s ⟨-, -, hv⟩
    show optIsBit s.var.1 = false
    rw [hv, optIsBit_natSyms _ _ (TermOK.cons rfl _), Nat.sub_zero,
      Nat.div_eq_of_lt (lt_two_pow_bitLen _)]
    simp
  have LOOP := Triple.loop (I := fun n (s : St L (fun _ => Sym) U.σ) => n ≤ bitLen b.natAbs ∧
      s.stk = stOf (sE a b K (bitLen b.natAbs - n)) B ∧
      s.var.1 = (natSyms (b.natAbs / 2 ^ (bitLen b.natAbs - n)) ++ Sym.sep :: B s5).head?)
    hstep hcont hstop (bitLen b.natAbs)
  -- normalization and output
  have hfin : stOf (sE a b K (bitLen b.natAbs)) B = stOf (sF a b K) B := by
    refine L_funext rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ rfl
    · show encL [.N (b.natAbs / 2 ^ bitLen b.natAbs), .S] ++ B s5 = encL [.N 0, .S] ++ B s5
      rw [Nat.div_eq_of_lt (lt_two_pow_bitLen _)]
    · show encL [.I ((a.natAbs : ℤ) * ((b.natAbs % 2 ^ bitLen b.natAbs : ℕ) : ℤ)), .S] ++ B s6 =
        encL [.I ((a.natAbs : ℤ) * (b.natAbs : ℤ)), .S] ++ B s6
      rw [Nat.mod_eq_of_lt (lt_two_pow_bitLen _)]
  have RF := school_fin hU hB ρ a b K ha hb hK
  unfold schoolP
  refine (Triple.seq R0 (Triple.seq TP0 (Triple.seq (LOOP.pre ?_) (RF.pre ?_)))).cost_mono ?_
  · rintro s ⟨hs, hv⟩
    refine ⟨le_rfl, by rw [hs, Nat.sub_self], ?_⟩
    rw [hv, Nat.sub_self, stOf_head (sE a b K 0) B (rfl : sE a b K 0 s5 = _)]
    rfl
  · rintro s ⟨-, hs, -⟩
    rw [hs, Nat.sub_zero, hfin]
  · rw [loopCost_const]
    have hN : bitLen b.natAbs ≤ 9 := hb
    have h1 := unit_mono Cu (show 20 ≤ 22 by omega)
    have h2 := Nat.mul_le_mul_right (5 * unit Cu 22 + 7 + 1) hN
    unfold schoolCost
    omega

end School

end WP.W5
