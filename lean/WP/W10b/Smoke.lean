import WP.W10b.Main

/-!
# WP.W10b.Smoke — numeric look at the slots of the headline schedule

W10b has no machine program. This evaluates `allSlots` for `n = 2^j` with the uniform width profile
W11b proposes (`4·P(n)` at every level, `4·p0` at the root) and prints
`(log₂ n, #slots, max_slot cnt·wid / n, Σ lin / (n·log₂ n))`. The per-slot `cnt·wid / n` stays
bounded and the linear work is `O(n log n)`, as `w9_bounds` proves (with a much larger constant).
-/

namespace WP.W10b.Smoke

open TMFw.Contracts IntMulTM.Contracts WP.W10b

/-- Uniform level width `4·P(n)`. -/
def wdU (n : ℕ) (_ : ℕ) : ℕ := 4 * hP n

/-- Root width `4·p0`. -/
def wRU (n : ℕ) : ℕ := 4 * W8.hP0 n

/-- `(log₂ n, #slots, max cnt·wid / n, Σ lin / (n·log₂ n))` for `n = 2^j`. -/
def row (j : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let n := 2 ^ j
  let l := allSlots wdU wdU wRU n
  (j, l.length, (l.map fun s => s.cnt * s.wid / n).foldl max 0, (l.map Slot.lin).sum / (n * j))

#eval [16, 32, 64, 128, 256, 512].map row

end WP.W10b.Smoke
