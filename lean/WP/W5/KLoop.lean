import WP.W5.Prog

/-!
# WP.W5.KLoop — register-level helpers and the counter loop `k := ⌈max(|a|,|b|)/3⌉`

* `L_funext`: equality of functions on the 11 stacks, stack by stack.
* `run_post`: `run_sound` with a clean post-state (`c'.E = E'` proved stack by stack).
* `peekL_triple`, `zt_triple`, `skip_pres`: triples for the register-reading pieces.
* `loopCost_pot`: amortised bound for `Triple.loop` with a potential (`B n + Φ n ≤ D + Φ (n+1)`).
* `kloop_spec`: the counter loop on two unsigned copies `A` (on `s1`) and `Bn` (on `s2`):
  `s0 := kOf A Bn = ⌈max(bitLen A, bitLen Bn)/3⌉`, both copies consumed, cost `≤ 38·k + 4`
  (increments amortised with the framework identity `ones_add_popcount_incBits`).
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-- The split position: `⌈max(bitLen A, bitLen Bn) / 3⌉`. -/
def kOf (A Bn : ℕ) : ℕ := (max (bitLen A) (bitLen Bn) + 2) / 3

/-- Functions on the stacks are equal if they agree on each of the 11 stacks. -/
theorem L_funext {α : Type} {f g : L → α} (h0 : f X = g X) (h1 : f Y = g Y) (h2 : f Z = g Z)
    (h3 : f s0 = g s0) (h4 : f s1 = g s1) (h5 : f s2 = g s2) (h6 : f s3 = g s3)
    (h7 : f s4 = g s4) (h8 : f s5 = g s5) (h9 : f s6 = g s6) (h10 : f s7 = g s7) : f = g := by
  funext k
  cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

/-! ## Register-level pieces -/

section Reg

variable {U : Subs} (ρ : List (Prog L (fun _ => Sym) U.σ))

theorem skip_pres (P : St L (fun _ => Sym) U.σ → Prop) :
    Triple ρ P (skip : Prog L (fun _ => Sym) U.σ) P 1 := by
  intro s hs
  exact ⟨s, 1, skip_eval ρ s, hs, le_rfl⟩

theorem peekL_triple (S : L → List Sym) (k : L) :
    Triple ρ (fun s => s.stk = S) (peekL U k) (fun s => s.stk = S ∧ s.var.1 = (S k).head?) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  have e : Eval ρ (peekL U k) ⟨v, stk⟩ ⟨((stk k).head?, v.2), stk⟩ 1 := Eval.peek _ _ _ _ _
  exact ⟨_, 1, e, ⟨rfl, rfl⟩, le_rfl⟩

theorem optIsBit_natSyms (n : ℕ) (r : List Sym) (h : TermOK r) :
    optIsBit (natSyms n ++ r).head? = decide (n ≠ 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [natSyms_zero, List.nil_append, optIsBit_head?_of_termOK h]; simp
  · rw [natSyms_pos n hn]
    have : n ≠ 0 := by omega
    simp [optIsBit, this]

theorem zt_triple (S : L → List Sym) (n1 n2 : ℕ) (r1 r2 : List Sym)
    (h1 : S s1 = natSyms n1 ++ r1) (h2 : S s2 = natSyms n2 ++ r2) (t1 : TermOK r1)
    (t2 : TermOK r2) :
    Triple ρ (fun s => s.stk = S) (ztP U)
      (fun s => s.stk = S ∧ rBit U s.var = decide (n1 ≠ 0 ∨ n2 ≠ 0)) 3 := by
  unfold ztP
  refine Triple.seq (peekL_triple ρ S s1) (Triple.ite (T := 1) ?_ ?_)
  · rintro s ⟨⟨hs, hv⟩, hc⟩
    have hn1 : n1 ≠ 0 := by
      have : optIsBit (S s1).head? = true := by rw [← hv]; exact hc
      rw [h1, optIsBit_natSyms n1 r1 t1] at this
      simpa using this
    refine ⟨s, 1, skip_eval ρ s, ⟨hs, ?_⟩, le_rfl⟩
    rw [hc]
    simp [hn1]
  · rintro s ⟨⟨hs, hv⟩, hc⟩
    have hn1 : n1 = 0 := by
      have : optIsBit (S s1).head? = false := by rw [← hv]; exact hc
      rw [h1, optIsBit_natSyms n1 r1 t1] at this
      simpa using this
    obtain ⟨s', t, e, ⟨hs', hv'⟩, ht⟩ := peekL_triple ρ S s2 s hs
    refine ⟨s', t, e, ⟨hs', ?_⟩, ht⟩
    show optIsBit s'.var.1 = _
    rw [hv', h2, optIsBit_natSyms n2 r2 t2, hn1]
    simp

end Reg

/-! ## Runs with a clean post-state -/

section Run

variable {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) {B : L → List Sym}
  (hB : ∀ k, bokXY k = true → TermOK (B k)) (ρ : List (Prog L (fun _ => Sym) U.σ))

include hU hB in
/-- `run_sound` with the computed final entries replaced by a clean `E'`, and the (closed) cost
data given explicitly. -/
theorem run_post (kb : ℕ) {os : List Op} {E E1 : L → List Ent} {P : Prop} {m : ℕ}
    (h : run bokXY kb os E = some (E1, P)) (hP : P) (hA : AllLe E m)
    (E' : L → List Ent) (hE : E1 = E') (n0 k0 d0 j0 m0 : ℕ) (hn : unitsOf os = n0)
    (hk : constsOf os = k0) (hd : dmOf os = d0) (hj : dkOf os = j0) (hm : m + d0 + j0 * kb = m0) :
    Triple ρ (fun s => s.stk = stOf E B) (seqOf U os) (fun s => s.stk = stOf E' B)
      (n0 * unit Cu m0 + k0 + 1) ∧ AllLe E' m0 := by
  obtain ⟨T, hA'⟩ := run_sound hU hB ρ kb os E E1 P m h hP hA
  subst hE hn hk hd hj hm
  exact ⟨T, hA'⟩

end Run

/-! ## Amortised loops -/

/-- **Potential method** for `loopCost`. -/
theorem loopCost_pot (B Φ : ℕ → ℕ) (D : ℕ) (h : ∀ n, B n + Φ n ≤ D + Φ (n + 1)) :
    ∀ N, loopCost B N + Φ 0 ≤ (D + 1) * N + 1 + Φ N
  | 0 => by simp [loopCost]
  | N + 1 => by
    have ih := loopCost_pot B Φ D h N
    have hN := h N
    simp only [loopCost]
    rw [Nat.mul_succ]
    omega

/-! ## The counter loop -/

/-- The counter-loop state after `i` rounds. -/
def kE (E : L → List Ent) (A Bn i : ℕ) : L → List Ent :=
  Function.update (Function.update (Function.update E s0 [.N i, .S]) s1 [.N (A / 8 ^ i), .S])
    s2 [.N (Bn / 8 ^ i), .S]

theorem div8_succ (A i : ℕ) : A / 8 ^ i / 2 / 2 / 2 = A / 8 ^ (i + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, pow_succ]

theorem allLe_kE {E : L → List Ent} {m : ℕ} (hE : AllLe E m) (A Bn i : ℕ) (hA : bitLen A ≤ m)
    (hB : bitLen Bn ≤ m) (hi : bitLen i ≤ m) : AllLe (kE E A Bn i) m := by
  unfold kE
  refine ((hE.update s0 _ ?_).update s1 _ ?_).update s2 _ ?_
  · intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hi
    · exact Nat.zero_le _
  · intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact le_trans (bitLen_div_le _ _) hA
    · exact Nat.zero_le _
  · intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact le_trans (bitLen_div_le _ _) hB
    · exact Nat.zero_le _

section Loop

variable {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) {B : L → List Sym}
  (hB : ∀ k, bokXY k = true → TermOK (B k)) (ρ : List (Prog L (fun _ => Sym) U.σ))

/-- The stack `s0` of a counter state. -/
theorem stOf_kE_s0 (E : L → List Ent) (A Bn i : ℕ) :
    stOf (kE E A Bn i) B s0 = (encodeNat i).map Sym.bit ++ (Sym.sep :: B s0) := by
  rw [stOf_head (kE E A Bn i) B (rfl : kE E A Bn i s0 = [.N i, .S])]
  rfl

include hU hB in
/-- One round of the counter loop. -/
theorem kround (E : L → List Ent) (A Bn i m : ℕ) (hA : AllLe (kE E A Bn i) m) :
    Triple ρ (fun s => s.stk = stOf (kE E A Bn i) B)
      (.seq (.seq (seqOf U kbodyOps) ((inc s0 s7).liftRegs (lR U))) (ztP U))
      (fun s => s.stk = stOf (kE E A Bn (i + 1)) B ∧
        rBit U s.var = decide (A / 8 ^ (i + 1) ≠ 0 ∨ Bn / 8 ^ (i + 1) ≠ 0))
      (6 * ones (encodeNat i) + 31) := by
  -- the shifts
  have R := run_post hU hB ρ 0 (rfl : run bokXY 0 kbodyOps (kE E A Bn i) = some _) (by simp) hA
    (Function.update (kE E A Bn (i + 1)) s0 [.N i, .S])
    (L_funext rfl rfl rfl rfl
      (by show [Ent.N (A / 8 ^ i / 2 / 2 / 2), Ent.S] = _; rw [div8_succ]; rfl)
      (by show [Ent.N (Bn / 8 ^ i / 2 / 2 / 2), Ent.S] = _; rw [div8_succ]; rfl)
      rfl rfl rfl rfl rfl) 0 18 0 0 m rfl rfl rfl rfl (by omega)
  -- the increment
  have hS0 : stOf (Function.update (kE E A Bn (i + 1)) s0 [.N i, .S]) B s0 =
      (encodeNat i).map Sym.bit ++ (Sym.sep :: B s0) := by
    rw [stOf_head _ B (Function.update_self s0 [.N i, .S] (kE E A Bn (i + 1)))]
    rfl
  have hE2 : stOf (kE E A Bn (i + 1)) B = stOf (Function.update (Function.update
      (kE E A Bn (i + 1)) s0 [.N i, .S]) s0 [.N (i + 1), .S]) B := by
    congr 1
    rw [Function.update_idem]
    funext k
    by_cases hk : k = s0
    · subst hk; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hk]
  have T2 : Triple ρ (fun s => s.stk = stOf (Function.update (kE E A Bn (i + 1)) s0 [.N i, .S]) B)
      ((inc s0 s7).liftRegs (lR U))
      (fun s => s.stk = stOf (kE E A Bn (i + 1)) B) (6 * ones (encodeNat i) + 9) := by
    refine liftR_triple (by simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody,
      pushC, popR, restoreR, pushR, skip, moveBits, moveBitsBody]) (fun r => ?_) ρ
    obtain ⟨c, hc, e⟩ := inc_eval (k := s0) (t := s7) (by decide) [] r (encodeNat i)
      (Sym.sep :: B s0) _ (TermOK.cons rfl _) hS0
    refine ⟨_, c, hc, e.of_eq (st_eq ?_) rfl⟩
    rw [← encodeNat_succ, hE2,
      stOf_replace (Function.update (kE E A Bn (i + 1)) s0 [.N i, .S]) B s0 [.N (i + 1), .S]]
    congr 1
    simp [Ent.enc, natSyms]
  -- the zero test
  have T3 := zt_triple ρ (stOf (kE E A Bn (i + 1)) B) (A / 8 ^ (i + 1)) (Bn / 8 ^ (i + 1))
    (Sym.sep :: B s1) (Sym.sep :: B s2) (stOf_head _ B (rfl : kE E A Bn (i + 1) s1 = _))
    (stOf_head _ B (rfl : kE E A Bn (i + 1) s2 = _)) (TermOK.cons rfl _) (TermOK.cons rfl _)
  refine (Triple.seq (Triple.seq R.1 T2) T3).cost_mono ?_
  omega

include hU hB in
/-- **The counter loop.** From copies `A` (on `s1`) and `Bn` (on `s2`) and an empty counter frame
(`s0`), compute `k = kOf A Bn` on `s0` and consume both copies; cost `≤ 38·k + 4`. -/
theorem kloop_spec (E : L → List Ent) (A Bn m : ℕ) (hE0 : E s0 = [.S]) (hE1 : E s1 = [.N A, .S])
    (hE2 : E s2 = [.N Bn, .S]) (hAll : AllLe E m) (hAm : bitLen A ≤ m) (hBm : bitLen Bn ≤ m)
    (hkm : kOf A Bn ≤ m) :
    Triple ρ (fun s => s.stk = stOf E B) (kloopP U)
      (fun s => s.stk = stOf (Function.update (Function.update (Function.update E
        s0 [.N (kOf A Bn), .S]) s1 [.S]) s2 [.S]) B)
      (38 * kOf A Bn + 4) := by
  set K := kOf A Bn with hK
  -- `K` rounds are needed: the copies vanish exactly at round `K`
  have hvan : ∀ i, (A / 8 ^ i ≠ 0 ∨ Bn / 8 ^ i ≠ 0) ↔ i < K := by
    intro i
    rw [Ne, div_pow8_eq_zero_iff, Ne, div_pow8_eq_zero_iff, hK, kOf]
    constructor
    · rintro (h | h) <;> omega
    · intro h
      by_contra h'
      push_neg at h'
      omega
  -- the start state is the round-0 state, the end state the round-`K` state
  have hstart : stOf E B = stOf (kE E A Bn 0) B := by
    refine L_funext rfl rfl rfl ?_ ?_ ?_ rfl rfl rfl rfl rfl
    · show encL (E s0) ++ B s0 = encL [.N 0, .S] ++ B s0
      rw [hE0]; simp [Ent.enc, natSyms_zero]
    · show encL (E s1) ++ B s1 = encL [.N (A / 8 ^ 0), .S] ++ B s1
      rw [hE1, pow_zero, Nat.div_one]
    · show encL (E s2) ++ B s2 = encL [.N (Bn / 8 ^ 0), .S] ++ B s2
      rw [hE2, pow_zero, Nat.div_one]
  have hKz1 : A / 8 ^ K = 0 := by
    by_contra h; exact absurd ((hvan K).1 (Or.inl h)) (lt_irrefl _)
  have hKz2 : Bn / 8 ^ K = 0 := by
    by_contra h; exact absurd ((hvan K).1 (Or.inr h)) (lt_irrefl _)
  have hend : stOf (kE E A Bn K) B = stOf (Function.update (Function.update (Function.update E
      s0 [.N K, .S]) s1 [.S]) s2 [.S]) B := by
    refine L_funext rfl rfl rfl rfl ?_ ?_ rfl rfl rfl rfl rfl
    · show encL [.N (A / 8 ^ K), .S] ++ B s1 = encL [.S] ++ B s1
      rw [hKz1]; simp [Ent.enc, natSyms_zero]
    · show encL [.N (Bn / 8 ^ K), .S] ++ B s2 = encL [.S] ++ B s2
      rw [hKz2]; simp [Ent.enc, natSyms_zero]
  -- the loop
  let I : ℕ → St L (fun _ => Sym) U.σ → Prop := fun n s => n ≤ K ∧
    s.stk = stOf (kE E A Bn (K - n)) B ∧
    rBit U s.var = decide (A / 8 ^ (K - n) ≠ 0 ∨ Bn / 8 ^ (K - n) ≠ 0)
  have hstep : ∀ n, Triple ρ (I (n + 1))
      (.seq (.seq (seqOf U kbodyOps) ((inc s0 s7).liftRegs (lR U))) (ztP U)) (I n)
      (6 * ones (encodeNat (K - (n + 1))) + 31) := by
    intro n
    rintro s ⟨hn, hs, -⟩
    have e : K - (n + 1) + 1 = K - n := by omega
    obtain ⟨s', t, ev, ⟨hs', hr'⟩, ht⟩ := kround hU hB ρ E A Bn (K - (n + 1)) m
      (allLe_kE hAll A Bn _ hAm hBm (le_trans (bitLen_le_self _) (by omega))) s hs
    rw [e] at hs' hr'
    exact ⟨s', t, ev, ⟨by omega, hs', hr'⟩, ht⟩
  have hcont : ∀ n s, I (n + 1) s → rBit U s.var = true := by
    rintro n s ⟨hn, -, hr⟩
    rw [hr, decide_eq_true_eq, hvan]
    omega
  have hstop : ∀ s, I 0 s → rBit U s.var = false := by
    rintro s ⟨-, -, hr⟩
    rw [hr, decide_eq_false_iff_not, hvan]
    omega
  have LOOP := Triple.loop hstep hcont hstop K
  have ZT0 := zt_triple ρ (stOf (kE E A Bn 0) B) (A / 8 ^ 0) (Bn / 8 ^ 0)
    (Sym.sep :: B s1) (Sym.sep :: B s2) (stOf_head _ B (rfl : kE E A Bn 0 s1 = _))
    (stOf_head _ B (rfl : kE E A Bn 0 s2 = _)) (TermOK.cons rfl _) (TermOK.cons rfl _)
  have hpot := loopCost_pot (fun n => 6 * ones (encodeNat (K - (n + 1))) + 31)
    (fun n => 6 * popcount (encodeNat (K - n))) 37 (by
      intro n
      by_cases hn : n + 1 ≤ K
      · have e : K - n = (K - (n + 1)) + 1 := by omega
        rw [e, encodeNat_succ]
        have := ones_add_popcount_incBits (encodeNat (K - (n + 1)))
        omega
      · have e1 : K - (n + 1) = 0 := by omega
        have e2 : K - n = 0 := by omega
        rw [e1, e2, encodeNat_zero]
        simp [ones, popcount]) K
  have hpK : 6 * popcount (encodeNat (K - K)) = 0 := by
    rw [Nat.sub_self, encodeNat_zero]; rfl
  refine (Triple.seq (ZT0.conseq (fun s hs => by rw [hs, hstart]) (fun s hs => ?_) le_rfl)
    LOOP).conseq (fun s hs => hs) (fun s hs => ?_) ?_
  · refine ⟨le_rfl, ?_, ?_⟩
    · rw [hs.1, Nat.sub_self]
    · rw [hs.2, Nat.sub_self]
  · rw [hs.2.1, Nat.sub_zero]; exact hend
  · rw [hpK] at hpot
    omega

end Loop

end WP.W5
