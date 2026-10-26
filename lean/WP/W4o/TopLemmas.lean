import WP.W4o.RouteRec

/-!
# WP.W4o.TopLemmas — closedness of the router, the padded offset block, cost arithmetic
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem route_closed : route.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, route, body, node, phase1, phase2, phase3, phase4, base,
    deinB, dein, deinBody, interL, interBody, moveRecD, moveRecU, moveAll, addTP, addBody, saveU,
    mvBits, dropNum, popA, peekA, peekB, pushA, pushB, pushK, dropT, skipR, clrC, setB0, loadC,
    pushS]

theorem addTP_closed (sub : Bool) {κ : Type} (X U T V : κ) : (addTP sub X U T V).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, addTP, addBody, saveU, mvBits, popA, peekA, peekB, pushA,
    pushB, pushK, dropT, skipR, clrC, setB0, loadC, pushS]

theorem dropNum_closed {κ : Type} (k : κ) : (dropNum k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dropNum, popA]

theorem bitsVal_replicate_false (k : ℕ) : bitsVal (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The offset `b < 2^k` padded to `k` bits. -/
theorem pad_spec (k b : ℕ) (hb : b < 2 ^ k) :
    (addT false (List.replicate k false) (encodeNat b) false).length = k ∧
      bitsVal (addT false (List.replicate k false) (encodeNat b) false) = b := by
  refine ⟨by rw [length_addT, List.length_replicate], ?_⟩
  rw [bitsVal_addT_add, bitsVal_replicate_false, bitsVal_encodeNat, List.length_replicate]
  simp only [Bool.toNat_false, Nat.zero_add, Nat.add_zero]
  exact Nat.mod_eq_of_lt hb

theorem bitLen_le_self (n : ℕ) : (encodeNat n).length ≤ n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [two_mul, encodeNat_add]
    split_ifs with h
    · simp
    · have hm : m ≠ 0 := fun hm => h (by rw [hm, encodeNat_zero])
      have := ih m (by omega)
      simp only [List.length_cons]
      omega
  · rw [two_mul, encodeNat_add_add_one]
    have := ih m (by omega)
    simp only [List.length_cons]
    omega

/-- Cost arithmetic of the whole kernel. -/
theorem top_cost {N k bl X tR tF : ℕ} (hN : 2 ^ k ≤ N) (hk : k < 2 ^ k) (hbl : bl ≤ N)
    (hR : tR ≤ 200 * N * (k + 1) + 2) (hF : tF ≤ 30 * (k + 1) * (k + 1))
    (hX : X ≤ 10 * bl + 17 * k + 25) :
    X + tR + tF ≤ 300 * (N + 1) * (k + 1) := by
  have hQ : (k + 1) * (k + 1) ≤ N * (k + 1) := Nat.mul_le_mul_right _ (by omega)
  have hP : N ≤ N * (k + 1) := by
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ N * (k + 1) := Nat.mul_le_mul_left N (by omega)
  have e1 : 300 * (N + 1) * (k + 1) = 300 * (N * (k + 1)) + 300 * (k + 1) := by ring
  have e2 : 200 * N * (k + 1) = 200 * (N * (k + 1)) := by ring
  have e3 : 30 * (k + 1) * (k + 1) = 30 * ((k + 1) * (k + 1)) := by ring
  rw [e1]
  rw [e2] at hR
  rw [e3] at hF
  generalize N * (k + 1) = P at *
  generalize (k + 1) * (k + 1) = Q at *
  generalize 2 ^ k = M at *
  omega

#assert_std_axioms route_closed addTP_closed dropNum_closed bitsVal_replicate_false pad_spec
  bitLen_le_self top_cost

end TMFw.W4o
