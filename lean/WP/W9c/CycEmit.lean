import WP.W9c.CycPh
import Mathlib.Tactic.Ring

/-!
# WP.W9c.CycEmit — `W9c_cycEmit` (add a value list into the cyclic 2-stack tape)

`cycProg I` (stacks `Loc 3 4`, see `CycState`; `I` an instance of the frozen `W3_addInt`) is one
loop driven by the value stack: per value `v`, if the right stack shows its `mark` the left cells
are moved back (`cWrap`, `r` entries), then the right cell `c` is popped (after `cL += c + v`) and
the sum is pushed on the left. Cost: `(Ca + 20)·(|vs|·(Bv+Bc+1) + ⌊(p+|vs|-1)/r⌋·r·(Bc+1) + 1)`,
using `nwr_le` for the number of wraps.
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

/-- **The cyclic emit program.** -/
def cycProg (I : Inst 3 4 Unit) : HP 3 4 (CR I.R) := whileTop (Lens.fst _ _) cV isSign (cB I)

theorem cycProg_closed (I : Inst 3 4 Unit) : (cycProg I).Closed :=
  whileTop_closed _ _ _ (cB_closed I)

/-- The cost arithmetic of `W9c_cycEmit`. -/
theorem cyc_cost (Ca Bc Bv r n w nw : ℕ) (hr : 0 < r) (hnw : nw ≤ w) :
    n * (Ca * (Bc + Bv + 1) + 3 * Bc + 3 * Bv + 14) + nw * (r * (8 * Bc + 12) + 2) + 1 + 1 ≤
      (Ca + 20) * (n * (Bv + Bc + 1) + w * (r * (Bc + 1)) + 1) := by
  have hA : n * (Ca * (Bc + Bv + 1) + 3 * Bc + 3 * Bv + 14) ≤
      Ca * (n * (Bv + Bc + 1)) + 14 * (n * (Bv + Bc + 1)) :=
    calc n * (Ca * (Bc + Bv + 1) + 3 * Bc + 3 * Bv + 14) ≤
          n * (Ca * (Bv + Bc + 1) + 14 * (Bv + Bc + 1)) := by
          apply Nat.mul_le_mul_left
          have : Ca * (Bc + Bv + 1) = Ca * (Bv + Bc + 1) := by ring
          omega
      _ = Ca * (n * (Bv + Bc + 1)) + 14 * (n * (Bv + Bc + 1)) := by ring
  have hK2 : r * (8 * Bc + 12) + 2 ≤ 14 * (r * (Bc + 1)) := by
    have h0 : 0 < r * (Bc + 1) := Nat.mul_pos hr (Nat.succ_pos _)
    have h1 : r * (8 * Bc + 12) ≤ r * (12 * (Bc + 1)) := Nat.mul_le_mul_left _ (by omega)
    have h2 : r * (12 * (Bc + 1)) = 12 * (r * (Bc + 1)) := by ring
    omega
  have hW : nw * (r * (8 * Bc + 12) + 2) ≤ 14 * (w * (r * (Bc + 1))) :=
    calc nw * (r * (8 * Bc + 12) + 2) ≤ w * (14 * (r * (Bc + 1))) := Nat.mul_le_mul hnw hK2
      _ = 14 * (w * (r * (Bc + 1))) := by ring
  have hexp : (Ca + 20) * (n * (Bv + Bc + 1) + w * (r * (Bc + 1)) + 1) =
      Ca * (n * (Bv + Bc + 1)) + Ca * (w * (r * (Bc + 1))) + Ca + 20 * (n * (Bv + Bc + 1)) +
        20 * (w * (r * (Bc + 1))) + 20 := by ring
  omega

#assert_std_axioms cycProg_closed cyc_cost

end WP.W9c.CK

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 WP.W9c.CK

/-- **`W9c_cycEmit` holds**, given the signed-addition contract `W3_addInt`. -/
theorem w9c_cycEmit_holds (hadd : W3_addInt) : W9c_cycEmit := by
  obtain ⟨Ca, hCa⟩ := exists_inst hadd
  refine ⟨Ca + 20, fun _ => ?_⟩
  obtain ⟨I, hI⟩ := hCa ()
  haveI := I.fin
  haveI := I.ne
  refine ⟨4, CR I.R, fun _ => (), cycProg I, by norm_num, inferInstance, inferInstance,
    cycProg_closed I, ?_⟩
  intro Bc Bv p cells vs rv rL rR S hpos hp hrv hbv hbc hS0 hS1 hS2
  have key := ck_whileTop (ρ := []) _ _ _ _ (cyc_loop hI [] Bc Bv cells.length hpos rv rL rR (S cX)
    (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) hrv vs cells p rfl hp hbv hbc)
  have hpre : CS.f ⟨listSyms vs ++ rv, tapeL cells p ++ rL, tapeR cells p ++ rR, S cX, S (.inr 1),
      S (.inr 2), S (.inr 3)⟩ = S := by
    rw [← hS0, ← hS1, ← hS2]
    exact (CS.eta S).symm
  have hpost : CS.f ⟨rv, tapeL (cycAdd cells.length cells p vs).1
      (cycAdd cells.length cells p vs).2 ++ rL, tapeR (cycAdd cells.length cells p vs).1
      (cycAdd cells.length cells p vs).2 ++ rR, S cX, S (.inr 1), S (.inr 2), S (.inr 3)⟩ =
      Function.update (Function.update (Function.update S cV rv) cL
        (tapeL (cycAdd cells.length cells p vs).1 (cycAdd cells.length cells p vs).2 ++ rL)) cR
        (tapeR (cycAdd cells.length cells p vs).1 (cycAdd cells.length cells p vs).2 ++ rR) := by
    conv_rhs => rw [CS.eta S]
    simp only [cupd_v, cupd_l, cupd_r]
  rw [hpre, hpost] at key
  exact HT.runs (key.mono (cyc_cost Ca Bc Bv cells.length vs.length _ _ hpos
    (nwr_le cells.length hpos vs p hp)))

#assert_std_axioms w9c_cycEmit_holds

end WP.W9c
