import SubNLogN.Math.Networks.Proofs.CellSoundCommon

/-!
# Cell soundness, centre-edge loss: the decreasing centre edge loses exactly `h`, for every `h`

`center_dec` (`CellSoundCommon.lean`) checks at `h = 100` (by `decide +kernel`) that the name-level
centre edge `3 → 4` of stage `j` is decreasing and loses dimension `100`. Here the same is proved for
every `h`: the cell lists `cT`, `cH` and the mentioned names `eR` of the edge do not depend on `h`
(computed per stage by `decide +kernel`); the cell dimensions are then polynomials in `h` and
`h - 1`, and the tail has exactly one extra cell, of dimension `h`.
-/

namespace SubNLogN.Math.Networks.WP6b

open Cell

/-- The decreasing centre edge `3 → 4` of every stage: head cells are tail cells, and the tail cell
sum exceeds the head cell sum by exactly `h`, for every `h`. -/
theorem center_dec_gen (j : Stage) (h : ℕ) :
    (∀ x ∈ cH (aCenter j 3, aCenter j 4), x ∈ cT (aCenter j 3, aCenter j 4)) ∧
    ((cT (aCenter j 3, aCenter j 4)).map (cellDim h (eR (aCenter j 3, aCenter j 4)))).sum =
      ((cH (aCenter j 3, aCenter j 4)).map (cellDim h (eR (aCenter j 3, aCenter j 4)))).sum + h := by
  refine ⟨(center_dec j).1, ?_⟩
  cases j with
  | one =>
    have hT : cT (aCenter .one 3, aCenter .one 4) = [(.C, .L 0, .L 0)] := by decide +kernel
    have hH : cH (aCenter .one 3, aCenter .one 4) = [] := by decide +kernel
    have h0 : (eR (aCenter .one 3, aCenter .one 4) 0).length = 0 := by decide +kernel
    rw [hT, hH]
    simp [cellDim, atomDim, h0]
  | two =>
    have hT : cT (aCenter .two 3, aCenter .two 4) = [(.L 0, .C, .L 0), (.C, .C, .L 0)] := by
      decide +kernel
    have hH : cH (aCenter .two 3, aCenter .two 4) = [(.C, .C, .L 0)] := by decide +kernel
    have h0 : (eR (aCenter .two 3, aCenter .two 4) 0).length = 1 := by decide +kernel
    have h1 : (eR (aCenter .two 3, aCenter .two 4) 1).length = 0 := by decide +kernel
    rw [hT, hH]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cellDim, atomDim, h0, h1,
      Nat.sub_zero, mul_one, one_mul, add_zero]
    ring
  | three =>
    have hT : cT (aCenter .three 3, aCenter .three 4) =
        [(.L 0, .L 0, .C), (.L 0, .C, .C), (.C, .L 0, .C), (.C, .C, .C)] := by decide +kernel
    have hH : cH (aCenter .three 3, aCenter .three 4) =
        [(.C, .L 0, .C), (.C, .C, .C), (.L 0, .C, .C)] := by decide +kernel
    have h0 : (eR (aCenter .three 3, aCenter .three 4) 0).length = 1 := by decide +kernel
    have h1 : (eR (aCenter .three 3, aCenter .three 4) 1).length = 1 := by decide +kernel
    have h2 : (eR (aCenter .three 3, aCenter .three 4) 2).length = 0 := by decide +kernel
    rw [hT, hH]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cellDim, atomDim, h0, h1,
      h2, Nat.sub_zero, mul_one, one_mul, add_zero]
    ring

end SubNLogN.Math.Networks.WP6b
