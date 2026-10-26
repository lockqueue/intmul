import WP.W7k3.SerBody

/-!
# WP.W7k3.SerLoop — the series loop

* `serLS S κ a0 c d n i`: the host state with loop counter `i`, holding the series state after
  `k = n - i` steps (`a_k`, `s_k`, `f k`, the two factors of `g k`).
* `serState_succ'`: one recurrence step in the machine's form (W6a's `divRoundRatInt`, natural
  denominator `(gγ·k+gδ)·(gε·k+gζ)·d`).
* `serW_n`, `serW_ends`: from the snapshot's width predicate, `n < 2^(W-1)` and the operand sizes
  at the setup and at the end (all `≤ W + 1`).
* `serLoop_spec`: the loop runs from `serLS … n` to `serLS … 0`, at most `n·(42U + 1) + U + 1`,
  with `X.V = W + 1`.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

/-- The loop state with counter `i`: the series state after `k = n - i` steps. -/
def serLS (S : SL → List Sym) (κ : SK) (a0 c : ℤ) (d n i : ℕ) : SL → List Sym :=
  sSt S (natSyms i ++ Sym.mark :: S (.inr 0))
    (intSyms (serState a0 c d κ.f κ.g (n - i)).1 ++ Sym.mark :: S (.inr 1))
    (intSyms (serState a0 c d κ.f κ.g (n - i)).2 ++ Sym.mark :: S (.inr 2))
    (natSyms (κ.f (n - i)) ++ Sym.mark :: S (.inr 3))
    (natSyms (κ.gγ * (n - i) + κ.gδ) ++ Sym.mark :: S (.inr 4))
    (natSyms (κ.gε * (n - i) + κ.gζ) ++ Sym.mark :: S (.inr 5))
    (intSyms d ++ Sym.mark :: S (.inr 6))
    (Sym.mark :: S (.inr 7)) (Sym.mark :: S (.inr 8)) (Sym.mark :: S (.inr 9))
    (Sym.mark :: S (.inr 10)) (Sym.mark :: S (.inr 11)) (S (.inl 4))

/-- One recurrence step, in the machine's form. -/
theorem serState_succ' (a0 c : ℤ) (d : ℕ) (κ : SK) (k : ℕ) :
    serState a0 c d κ.f κ.g (k + 1) =
      (divRoundRatInt ((serState a0 c d κ.f κ.g k).1 * c * (κ.f k : ℤ))
          ((κ.gγ * k + κ.gδ) * (κ.gε * k + κ.gζ) * d : ℕ),
        (serState a0 c d κ.f κ.g k).2 + (serState a0 c d κ.f κ.g k).1) := by
  rw [serState_succ]
  simp only [serStep, dr_eq, SK.g, Nat.cast_mul]

/-- The trip count is below the word bound. -/
theorem serW_n {W : ℕ} {κ : SK} (hκ : κ.OK) {a0 c : ℤ} {d n : ℕ} (hn : 0 < n)
    (hw : IntMul.RecurrenceCallSitesWidthSound W a0 c d κ.f κ.g n) :
    1 ≤ W ∧ n < 2 ^ (W - 1) := by
  obtain ⟨-, -, wk⟩ := serW_of hw
  have h1 := (wk (n - 1) (by omega)).2.2.2.1
  have h2 := SK.g_ge κ hκ (n - 1)
  have hn' : n < 2 ^ (W - 1) := by omega
  refine ⟨?_, hn'⟩
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h
    simp at hn'
    omega
  · exact h

theorem bitLen_le_two {x : ℕ} (hx : x ≤ 3) : bitLen x ≤ 2 :=
  bitLen_le_of_lt (by norm_num; omega)

/-- The operand sizes at the setup and at the end of the loop. -/
theorem serW_ends {W : ℕ} {κ : SK} (hκ : κ.OK) {a0 c : ℤ} {d n : ℕ} (hd0 : 0 < d) (hn : 0 < n)
    (hw : IntMul.RecurrenceCallSitesWidthSound W a0 c d κ.f κ.g n) :
    bitLen a0.natAbs ≤ W + 1 ∧ bitLen d ≤ W + 1 ∧ bitLen n ≤ W + 1 ∧
    bitLen κ.fβ ≤ W + 1 ∧ bitLen κ.gδ ≤ W + 1 ∧ bitLen κ.gζ ≤ W + 1 ∧
    bitLen (serState a0 c d κ.f κ.g n).1.natAbs ≤ W + 1 ∧
    bitLen (serState a0 c d κ.f κ.g n).2.natAbs ≤ W + 1 ∧
    bitLen (κ.f n) ≤ W + 1 ∧ bitLen (κ.gγ * n + κ.gδ) ≤ W + 1 ∧
    bitLen (κ.gε * n + κ.gζ) ≤ W + 1 := by
  obtain ⟨hW, hnM⟩ := serW_n hκ hn hw
  obtain ⟨-, wd, wk⟩ := serW_of hw
  have hfac := SK.fac_le κ hκ (le_refl n)
  have hgm := SK.g_ge κ hκ
  have h5 : κ.fβ ≤ 3 := hκ.2.2.2.2.1
  have h7 : κ.gδ ≤ 3 := hκ.2.2.2.2.2.2.1
  have h9 : κ.gζ ≤ 3 := hκ.2.2.2.2.2.2.2.2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨w1, w2, -, -, -, w6, w7⟩ := wk m (by omega)
  have hden : (0 : ℤ) < ((κ.gγ * m + κ.gδ) * (κ.gε * m + κ.gζ) * d : ℕ) := by
    have : 0 < (κ.gγ * m + κ.gδ) * (κ.gε * m + κ.gζ) * d :=
      Nat.mul_pos (lt_of_lt_of_le (Nat.succ_pos m) (hgm m)) hd0
    exact_mod_cast this
  refine ⟨bl_lt (wk 0 (by omega)).1, bl_lt wd, bl_lt hnM, by have := bitLen_le_two h5; omega,
    by have := bitLen_le_two h7; omega, by have := bitLen_le_two h9; omega, ?_, ?_,
    bl_fac hW hnM hfac.1, bl_fac hW hnM hfac.2.1, bl_fac hW hnM hfac.2.2⟩
  · rw [serState_succ']
    exact le_trans (bitLen_mono (natAbs_divRound_le _ hden)) (bl_lt w6)
  · rw [serState_succ']
    exact le_trans (bitLen_mono (Int.natAbs_add_le _ _)) (bl_add w2 w1)

/-- **The series loop.** -/
theorem serLoop_spec {X : KX} {I : KI} (hX : X.OK I) (κ : SK) (hκ : κ.OK) (S : SL → List Sym)
    (W : ℕ) (hV : X.V = W + 1) (a0 c : ℤ) (d n : ℕ) (hd0 : 0 < d) (hn : 0 < n)
    (rc : List Sym) (hrc : TermOK rc) (hc1 : S (.inl 1) = intSyms c ++ rc)
    (hw : IntMul.RecurrenceCallSitesWidthSound W a0 c d κ.f κ.g n) :
    HT [] (serLS S κ a0 c d n n) (kloop I (.inr 0) (serBody I κ)) (serLS S κ a0 c d n 0)
      (n * (42 * X.U + 1) + X.U + 1) := by
  obtain ⟨hW, hnM⟩ := serW_n hκ hn hw
  obtain ⟨wc, wd, wk⟩ := serW_of hw
  have hloop := HT.uloop hX (.inr 0) (by norm_num) (Sym.mark :: S (.inr 0)) (termOK_mark _)
    (serLS S κ a0 c d n) (fun i => by simp [serLS]) (serBody I κ) n (40 * X.U)
    (by rw [hV]; exact bl_lt hnM) (fun i hi => ?_)
  · refine hloop.mono (le_of_eq ?_)
    ring
  obtain ⟨k, hk⟩ : ∃ k, k = n - (i + 1) := ⟨_, rfl⟩
  have hki : n - i = k + 1 := by omega
  have hkn : k < n := by omega
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := wk k hkn
  have hg1 := SK.g1_le κ hκ k
  have hg2 := SK.g2_le κ hκ k
  have hfac := SK.fac_le κ hκ (show k + 1 ≤ n by omega)
  have hpos : 0 < κ.gγ * k + κ.gδ ∧ 0 < κ.gε * k + κ.gζ := by
    obtain ⟨-, h2, h3, -⟩ := hκ
    constructor <;> omega
  have hden : (0 : ℤ) < ((κ.gγ * k + κ.gδ) * (κ.gε * k + κ.gζ) * d : ℕ) := by
    have := Nat.mul_pos (Nat.mul_pos hpos.1 hpos.2) hd0
    exact_mod_cast this
  have ef : κ.f (k + 1) = κ.f k + κ.fα := by unfold SK.f; ring
  have eg1 : κ.gγ * (k + 1) + κ.gδ = κ.gγ * k + κ.gδ + κ.gγ := by ring
  have eg2 : κ.gε * (k + 1) + κ.gζ = κ.gε * k + κ.gζ + κ.gε := by ring
  have hpre : Function.update (serLS S κ a0 c d n (i + 1)) (.inr 0)
      (natSyms i ++ Sym.mark :: S (.inr 0)) =
      sSt S (natSyms i ++ Sym.mark :: S (.inr 0))
        (intSyms (serState a0 c d κ.f κ.g k).1 ++ Sym.mark :: S (.inr 1))
        (intSyms (serState a0 c d κ.f κ.g k).2 ++ Sym.mark :: S (.inr 2))
        (natSyms (κ.f k) ++ Sym.mark :: S (.inr 3))
        (natSyms (κ.gγ * k + κ.gδ) ++ Sym.mark :: S (.inr 4))
        (natSyms (κ.gε * k + κ.gζ) ++ Sym.mark :: S (.inr 5))
        (intSyms d ++ Sym.mark :: S (.inr 6))
        (Sym.mark :: S (.inr 7)) (Sym.mark :: S (.inr 8)) (Sym.mark :: S (.inr 9))
        (Sym.mark :: S (.inr 10)) (Sym.mark :: S (.inr 11)) (S (.inl 4)) := by
    unfold serLS
    rw [sSt_upd0, ← hk]
  rw [hpre]
  refine (serBody_spec hX κ hκ S c rc hrc hc1 d hd0 (serState a0 c d κ.f κ.g k).1
    (serState a0 c d κ.f κ.g k).2 (κ.f k) (κ.gγ * k + κ.gδ) (κ.gε * k + κ.gζ) hpos.1 hpos.2
    (natSyms i ++ Sym.mark :: S (.inr 0)) (S (.inl 4))
    (by rw [hV]; exact bl_lt w1) (by rw [hV]; exact bl_lt wc) (by rw [hV]; exact bl_lt w5)
    (by rw [hV]; exact bl_lt w3) (by rw [hV]; exact bl_lt w6)
    (by rw [hV]; exact bl_lt (lt_of_le_of_lt hg1 w4))
    (by rw [hV]; exact bl_lt (lt_of_le_of_lt hg2 w4))
    (by rw [hV]; exact bl_lt w4) (by rw [hV]; exact bl_lt wd) (by rw [hV]; exact bl_lt w7)
    (by rw [hV]; exact bl_lt w2)
    (by rw [hV]; exact le_trans (bitLen_mono (natAbs_divRound_le _ hden)) (bl_lt w6))
    (by rw [hV]; exact le_trans (bitLen_mono (Int.natAbs_add_le _ _)) (bl_add w2 w1))
    (by rw [hV, ← ef]; exact bl_fac hW hnM hfac.1)
    (by rw [hV, ← eg1]; exact bl_fac hW hnM hfac.2.1)
    (by rw [hV, ← eg2]; exact bl_fac hW hnM hfac.2.2)).of_eq ?_ le_rfl
  unfold serLS
  rw [hki, serState_succ', ef, eg1, eg2]

#assert_std_axioms serState_succ' serW_n bitLen_le_two serW_ends serLoop_spec

end WP.W7k3
