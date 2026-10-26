import WP.W9c.PureSpec

/-!
# WP.W9c.PureGlueA — digit and emitted-bucket widths (split 4: `GlueDigits`, `GlueEmit`)

* Every digit of `blockDigits` is a balanced digit at radix `2^k`: `|d| ≤ 2^(k-1)`
  (`unpack_eq_udig`, `udig_natAbs_le`), hence `bitLen |d| ≤ k`.
* `emitAll` emits sums `w + d` of a window entry and a digit, and finally the last window; window
  entries are digits or zeros. So every emitted bucket has `|e| ≤ 2·2^(k-1) = 2^k`, i.e.
  `bitLen |e| ≤ k + 1`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts IntMul

theorem two_pow_eq_two_mul_pred (k : ℕ) (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]

/-- Balanced digits of one block. -/
theorem blockDigits_natAbs_le (k p_in q ol : ℕ) (Pg : ℤ) (blk : List ℤ) (hk : 1 ≤ k) :
    ∀ d ∈ blockDigits k p_in q ol Pg blk, d.natAbs ≤ 2 ^ (k - 1) := by
  intro d hd
  unfold blockDigits at hd
  rw [unpack_eq_udig k hk] at hd
  exact udig_natAbs_le _ k hk ol _ 0 (Nat.zero_le _) d hd

theorem passDigits_natAbs_le (k p_in q W ol : ℕ) (Pg : ℤ) (x : List ℤ) (hk : 1 ≤ k) :
    ∀ ds ∈ passDigits k p_in q W ol Pg x, ∀ d ∈ ds, d.natAbs ≤ 2 ^ (k - 1) := by
  intro ds hds d hd
  unfold passDigits at hds
  obtain ⟨blk, _, rfl⟩ := List.mem_map.mp hds
  exact blockDigits_natAbs_le k p_in q ol Pg blk hk d hd

/-- **GlueDigits.** -/
theorem glueDigits_holds : GlueDigits := by
  intro k p_in q W ol Pg x hk ds hds d hd
  have h := passDigits_natAbs_le k p_in q W ol Pg x hk ds hds d hd
  apply WP.W7k2.bitLen_le_of_lt
  have h2 := two_pow_eq_two_mul_pred k hk
  have hp := Nat.two_pow_pos (k - 1)
  omega

theorem mem_zipWith_add : ∀ (l1 l2 : List ℤ) (e : ℤ), e ∈ List.zipWith (· + ·) l1 l2 →
    ∃ a ∈ l1, ∃ b ∈ l2, e = a + b
  | [], _, e, h => by simp at h
  | _ :: _, [], e, h => by simp at h
  | a :: l1, b :: l2, e, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self .., b, List.mem_cons_self .., rfl⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := mem_zipWith_add l1 l2 e h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

/-- Every emitted bucket is a window entry, or a window entry plus a digit. -/
theorem emitAll_natAbs_le (W B : ℕ) : ∀ (ws : List ℤ) (dss : List (List ℤ)),
    (∀ w ∈ ws, w.natAbs ≤ B) → (∀ ds ∈ dss, ∀ d ∈ ds, d.natAbs ≤ B) →
      ∀ e ∈ emitAll W ws dss, e.natAbs ≤ 2 * B
  | ws, [], hws, _, e, he => by
    simp only [emitAll] at he
    have := hws e he
    omega
  | ws, ds :: dss, hws, hds, e, he => by
    simp only [emitAll, List.mem_append] at he
    rcases he with he | he
    · simp only [winStep] at he
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith_add _ _ _ he
      have h1 := hws a ha
      have h2 := hds ds (List.mem_cons_self ..) b (List.mem_of_mem_take hb)
      have h3 := Int.natAbs_add_le a b
      omega
    · refine emitAll_natAbs_le W B (winStep W ws ds).2 dss ?_
        (fun ds' h' => hds ds' (List.mem_cons_of_mem _ h')) e he
      intro w hw
      simp only [winStep, List.mem_append] at hw
      rcases hw with hw | hw
      · exact hds ds (List.mem_cons_self ..) w (List.mem_of_mem_drop hw)
      · rw [List.mem_replicate] at hw
        rw [hw.2]
        simp

/-- **GlueEmit.** -/
theorem glueEmit_holds : GlueEmit := by
  intro k p_in q W ol Pg x hk _ _ e he
  unfold passEmit at he
  have hB := emitAll_natAbs_le W (2 ^ (k - 1)) (List.replicate W 0)
    (passDigits k p_in q W ol Pg x)
    (by
      intro w hw
      rw [List.mem_replicate] at hw
      rw [hw.2]
      simp)
    (passDigits_natAbs_le k p_in q W ol Pg x hk) e he
  apply WP.W7k2.bitLen_le_of_lt
  have h2 := two_pow_eq_two_mul_pred k hk
  have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp := Nat.two_pow_pos (k - 1)
  omega

#assert_std_axioms two_pow_eq_two_mul_pred blockDigits_natAbs_le passDigits_natAbs_le
  glueDigits_holds mem_zipWith_add emitAll_natAbs_le glueEmit_holds

end WP.W9c
