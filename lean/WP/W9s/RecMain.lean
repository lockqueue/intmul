import WP.W9s.RecSpec

/-!
# WP.W9s.RecMain — `fft_spec`, the recursion theorem
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

theorem head_rowE_ne' (f : List (ℤ × ℤ)) (l : List Sym) :
    decide ((rowE f ++ l).head? = some symBlk) = false := by
  have h := head_rowE_ne f l
  unfold notS at h
  revert h
  generalize decide ((rowE f ++ l).head? = some symBlk) = b
  cases b <;> simp

/-- **The recursion theorem.** -/
theorem fft_spec {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (hS : SynFacts) (r w : ℕ)
    (ρ : List (MProg K)) : ∀ g : FG,
    Triple ρ (fun s => FPre r w g ∧ s.stk = g.B) (fft K)
      (fun s => s.stk = Function.update g.B sA (blkR (synL g.Δ g.n g.X) ++ symBlk :: g.rA))
      (costF CA CS CH w r g.n + 2) := by
  refine Triple.fix (fun g => g.n) (fun g ih => ?_)
  refine Triple.pure_pre (fun hpre => ?_)
  obtain ⟨n, X, Δ, B, rA⟩ := g
  obtain ⟨hlen, hrows, hwid, hA, ⟨rDS, hDS⟩, ⟨rUR, hUR⟩, hΔ⟩ : X.length = 2 ^ n ∧
      (∀ row ∈ X, row.length = r) ∧ (∀ row ∈ X, ∀ z ∈ row, EntryW w z) ∧
      B sA = blkR X ++ symBlk :: rA ∧ (∃ rDS, B sDS = units Δ ++ symG :: rDS) ∧
      (∃ rUR, B sUR = units r ++ symG :: rUR) ∧ Δ * 2 ^ n = 2 * r := hpre
  show HT (fftBody K :: ρ) B (fftBody K) _ _
  cases n with
  | zero =>
    have h1 : X.length = 1 := by simpa using hlen
    obtain ⟨x0, rfl⟩ := List.length_eq_one_iff.mp h1
    have hx0 := hwid x0 (List.mem_singleton_self _)
    refine HT.of_eq (
      (HT.pushS sE symG B _).seq <|
      (HT.pushS sO symG _ _).seq <|
      (HT.mvRow (lS K) (src := sA) (dst := sE) (by decide) x0 (symBlk :: rA) _
        (by simp [hA, blkR]) _).seq <|
      HT.peekIte_true (lS K) sA (fun o => decide (o = some symBlk)) _ _ _ _ _ (by simp)
        ((HT.rewind (lS K) (src := sE) (dst := sA) (by decide) symG (rowE x0).reverse (B sE) _
          (symG_not_mem_rev_rowE x0) (by simp) _).seq
          (HT.popS sO _ symG (B sO) (by simp) _))) ?_ ?_
    · funext k
      by_cases h1 : k = sA
      · subst h1
        simp [blkR, synL]
      by_cases h2 : k = sE
      · subst h2
        simp
      by_cases h3 : k = sO
      · subst h3
        simp
      simp [h1, h2, h3]
    · have e1 := length_es_le w x0 hx0
      rw [hrows x0 (List.mem_singleton_self _)] at e1
      have e2 : r * eb w ≤ r * eb (w + 1) := Nat.mul_le_mul_left _ (eb_mono_succ w)
      simp only [List.length_reverse, rowE, List.length_append, List.length_singleton]
      unfold costF MF
      simp only [Nat.zero_add, pow_zero, Nat.one_mul]
      omega
  | succ m =>
    have h2 : 2 ≤ X.length := by
      rw [hlen, pow_succ]
      have := Nat.one_le_two_pow (n := m)
      omega
    obtain ⟨x0, x1, rest, rfl⟩ : ∃ x0 x1 rest, X = x0 :: x1 :: rest := by
      match X, h2 with
      | x0 :: x1 :: rest, _ => exact ⟨x0, x1, rest, rfl⟩
    have hrl : rest.length = 2 * 2 ^ m - 2 := by
      simp only [List.length_cons] at hlen
      rw [pow_succ] at hlen
      omega
    have hrest : rest.length % 2 = 0 := by omega
    have hev : (x0 :: evensL rest).length = 2 ^ m := by
      have := length_evensL rest
      simp only [List.length_cons]
      have := Nat.one_le_two_pow (n := m)
      omega
    have hod : (x1 :: oddsL rest).length = 2 ^ m := by
      have := length_oddsL rest
      simp only [List.length_cons]
      have := Nat.one_le_two_pow (n := m)
      omega
    have mem_ev : ∀ row ∈ x0 :: evensL rest, row ∈ x0 :: x1 :: rest := fun row h =>
      mem_evensL (l := x0 :: x1 :: rest) h
    have mem_od : ∀ row ∈ x1 :: oddsL rest, row ∈ x0 :: x1 :: rest := fun row h =>
      mem_oddsL (l := x0 :: x1 :: rest) h
    have hΔ' : 2 * Δ * 2 ^ m = 2 * r := by rw [pow_succ] at hΔ; rw [← hΔ]; ring
    have hΔr : Δ * 2 ^ m = r := by
      have : 2 * (Δ * 2 ^ m) = 2 * r := by rw [← hΔ']; ring
      omega
    have hΔle : Δ ≤ r := by
      have := Nat.one_le_two_pow (n := m)
      rw [← hΔr]
      exact Nat.le_mul_of_pos_right _ this
    have hY1l := hS.length (2 * Δ) m (x1 :: oddsL rest) hod
    have hY0l := hS.length (2 * Δ) m (x0 :: evensL rest) hev
    have hY1r := hS.rows (2 * Δ) r m (x1 :: oddsL rest) hod (fun row h => hrows row (mem_od row h))
    have hY0r := hS.rows (2 * Δ) r m (x0 :: evensL rest) hev (fun row h => hrows row (mem_ev row h))
    have hY1w := hS.width w (2 * Δ) m (x1 :: oddsL rest) (fun row h => hwid row (mem_od row h))
    have hY0w := hS.width w (2 * Δ) m (x0 :: evensL rest) (fun row h => hwid row (mem_ev row h))
    refine HT.of_eq (
      (HT.pushS sE symG B _).seq <|
      (HT.pushS sO symG _ _).seq <|
      (HT.mvRow (lS K) (src := sA) (dst := sE) (by decide) x0 (blkR (x1 :: rest) ++ symBlk :: rA) _
        (by simp [hA, blkR_cons]) _).seq <|
      HT.peekIte_false (lS K) sA (fun o => decide (o = some symBlk)) _ _ _ _ _
        (by simpa [blkR_cons, List.append_assoc] using head_rowE_ne' x1 (blkR rest ++ symBlk :: rA)) <|
      (HT.mvRow (lS K) (src := sA) (dst := sO) (by decide) x1 (blkR rest ++ symBlk :: rA) _
        (by simp [blkR_cons]) _).seq <|
      (HT.dealLoop K rA rest _ hrest (by simp) _).seq <|
      (HT.rewind (lS K) (src := sE) (dst := sA) (by decide) symG (blkR (x0 :: evensL rest)).reverse
        (B sE) _ (symG_not_mem_rev_blkR _) (by simp [blkR_cons]) _).seq <|
      (HT.pushS sA symBlk _ _).seq <|
      (HT.rewind (lS K) (src := sO) (dst := sA) (by decide) symG (blkR (x1 :: oddsL rest)).reverse
        (B sO) _ (symG_not_mem_rev_blkR _) (by simp [blkR_cons]) _).seq <|
      (HT.dsDouble K _ Δ rDS (by simp [hDS]) _).seq <|
      (HT.recurCall ih m (by simp) (x1 :: oddsL rest) (2 * Δ) _
        (blkR (x0 :: evensL rest) ++ symBlk :: rA)
        ⟨hod, fun row h => hrows row (mem_od row h), fun row h => hwid row (mem_od row h),
          by simp, ⟨units Δ ++ symG :: rDS, by simp⟩, ⟨rUR, by simp [hUR]⟩, hΔ'⟩).seq <|
      (HT.pushS sT symG _ _).seq <|
      (HT.rewind (lS K) (src := sA) (dst := sT) (by decide) symBlk
        (blkR (synL (2 * Δ) m (x1 :: oddsL rest))) (blkR (x0 :: evensL rest) ++ symBlk :: rA) _
        (symBlk_not_mem_blkR _) (by simp) _).seq <|
      (HT.pushS sD symBlk _ _).seq <|
      (HT.rewind (lS K) (src := sT) (dst := sD) (by decide) symG
        (blkR (synL (2 * Δ) m (x1 :: oddsL rest))).reverse (B sT) _ (symG_not_mem_rev_blkR _)
        (by simp) _).seq <|
      (HT.recurCall ih m (by simp) (x0 :: evensL rest) (2 * Δ) _ rA
        ⟨hev, fun row h => hrows row (mem_ev row h), fun row h => hwid row (mem_ev row h),
          by simp, ⟨units Δ ++ symG :: rDS, by simp⟩, ⟨rUR, by simp [hUR]⟩, hΔ'⟩).seq <|
      (HT.dsPop K _ (2 * Δ) (units Δ ++ symG :: rDS) (by simp) _).seq <|
      HT.combine hK w r Δ _ (synL (2 * Δ) m (x0 :: evensL rest)) (synL (2 * Δ) m (x1 :: oddsL rest))
        rA (B sD) rDS rUR (by rw [hY0l, hY1l]) (by rw [hY0l]; exact hΔr) hΔle hY0r hY1r hY0w hY1w
        (by simp) (by simp) (by simp) (by simp [hUR]) _) ?_ ?_
    · funext k
      by_cases h1 : k = sA
      · subst h1
        simp
        rfl
      by_cases h2 : k = sD
      · subst h2
        simp
      by_cases h3 : k = sE
      · subst h3
        simp
      by_cases h4 : k = sO
      · subst h4
        simp
      by_cases h5 : k = sT
      · subst h5
        simp
      by_cases h6 : k = sDS
      · subst h6
        simp [hDS]
      simp [h1, h2, h3, h4, h5, h6]
    · have q0 : r * eb w ≤ r * eb (w + 1) := Nat.mul_le_mul_left _ (eb_mono_succ w)
      have c3 := length_es_le w x0 (hwid x0 (List.mem_cons_self ..))
      have c5 := length_es_le w x1 (hwid x1 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      rw [hrows x0 (List.mem_cons_self ..)] at c3
      rw [hrows x1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))] at c5
      have bR := length_blkR_le w r rest (fun row h => ⟨hrows row (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ h)), hwid row (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))⟩)
      have bE := length_blkR_le w r _ (fun row h => ⟨hrows row (mem_ev row h), hwid row (mem_ev row h)⟩)
      have bO := length_blkR_le w r _ (fun row h => ⟨hrows row (mem_od row h), hwid row (mem_od row h)⟩)
      have bY := length_blkR_le w r _ (fun row h => ⟨hY1r row h, hY1w row h⟩)
      rw [hev] at bE
      rw [hod] at bO
      rw [hY1l] at bY
      have m1 : 2 ^ m * (r * eb w + 1) ≤ 2 ^ m * (r * eb (w + 1) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have m2 : rest.length * (r * eb w + 1) ≤ 2 * (2 ^ m * (r * eb (w + 1) + 1)) := by
        calc rest.length * (r * eb w + 1) ≤ (2 * 2 ^ m) * (r * eb (w + 1) + 1) :=
              Nat.mul_le_mul (by omega) (by omega)
          _ = 2 * (2 ^ m * (r * eb (w + 1) + 1)) := by ring
      have hP : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have e1 : costF CA CS CH w r (m + 1) = 2 * costF CA CS CH w r m +
          2 * (30 * (2 ^ m * (r * eb (w + 1) + 1)) + 2 ^ m * rowCostB CA CS CH w r +
            33 * (2 ^ m * r) + 71 * 2 ^ m) := by
        unfold costF MF
        ring
      have e2 : combCostB CA CS CH w r (2 ^ m) = 2 ^ m * rowCostB CA CS CH w r + 2 * 2 ^ m +
          6 * (2 ^ m * (r * eb (w + 1) + 1)) + 9 * r + 20 := by
        unfold combCostB
        ring
      have q1 : r * eb (w + 1) + 1 ≤ 2 ^ m * (r * eb (w + 1) + 1) := Nat.le_mul_of_pos_left _ hP
      have q2 : r ≤ 2 ^ m * r := Nat.le_mul_of_pos_left _ hP
      simp only [List.length_reverse, hY0l]
      omega

#assert_std_axioms head_rowE_ne' fft_spec

end WP.W9s
