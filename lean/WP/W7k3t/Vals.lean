import WP.W7k3t.Src
import WP.W7k3t.NumT

/-!
# WP.W7k3t.Vals — the values the tap kernel computes, and its width bound

* `tapW`: the global operand-width bound of the machine: twice the snapshot's tap call-site width
  (CTr:3625, in closed form `181·pSub + 2·p_work + 2·log₂ t1 + 280`), plus 8.
* `denYV`, `denThV`: `denY`, `denTheta` (CTr:3573-3581) with `B_c = 30·pSub + 42`.
* `serV g pSub NY d`: the series of one clamp: `N = 17·pSub + 22` steps of the snapshot recurrence
  (`serState`, `f ≡ 1`) from `2^Bint`, `Bint = 43·pSub + 60`, step numerator `-NY`, base denominator `d`.
* `clampSerV`: `sincClampC` / `expClampC` (CTr:3263, 3366): the clamped rescaled series sum.
* `elseV`, `tapV`: the tap (CTr:3569-3599) in these terms.
* `SerW W g pSub NY d`: the operand widths of one clamped series.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-- The machine's global operand-width bound. -/
def tapW (p_work pSub t1 : ℕ) : ℕ := 2 * (181 * pSub + 2 * p_work + 2 * Nat.log2 t1 + 280) + 8

/-- `denY = 4·p_work·ln2·t1²·2^B_c`, `B_c = 30·pSub + 42`. -/
def denYV (p_work pSub t1 lnN : ℕ) : ℕ := 4 * p_work * lnN * (t1 * t1) * 2 ^ (30 * pSub + 42)

/-- `denTheta = t1·2^B_c`. -/
def denThV (pSub t1 : ℕ) : ℕ := t1 * 2 ^ (30 * pSub + 42)

/-- The series of one clamp (`N = 17·pSub+22` steps, `a₀ = 2^(43·pSub+60)`, numerator `-NY`). -/
def serV (g : ℕ → ℕ) (pSub NY d : ℕ) : ℤ × ℤ :=
  serState ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ)) d (fun _ => 1) g (17 * pSub + 22)

/-- One clamp: the series sum rescaled to `2^(pSub+2)` and clamped. -/
def clampSerV (g : ℕ → ℕ) (pSub NY d : ℕ) : ℤ :=
  srcV (serV g pSub NY d).2 (pSub + 2) (43 * pSub + 60)

/-- The tap's else branch: the product of the sinc and Gaussian clamps, rescaled and clamped. -/
def elseV (pSub t1 NY DY : ℕ) : ℤ :=
  srcV (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (denThV pSub t1 * denThV pSub t1) *
    clampSerV (fun k => k + 1) pSub NY DY) pSub (2 * pSub + 4)

/-- The tap, as the machine computes it (`NY = numY`, `DY = denY`). -/
def tapV (p_work pSub t1 j1 s πN lnN : ℕ) : ℤ :=
  if (pSub + 4) * denYV p_work pSub t1 lnN ≤
      πN * numTV pSub t1 j1 s * (πN * numTV pSub t1 j1 s) then 0
  else elseV pSub t1 (πN * numTV pSub t1 j1 s * (πN * numTV pSub t1 j1 s))
    (denYV p_work pSub t1 lnN)

/-- Operand widths of one clamped series. -/
structure SerW (W : ℕ) (g : ℕ → ℕ) (pSub NY d : ℕ) : Prop where
  hc : bitLen NY ≤ W
  hd : bitLen d ≤ W
  ha : ∀ k ≤ 17 * pSub + 22, bitLen (serState ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ)) d
    (fun _ => 1) g k).1.natAbs ≤ W
  hs : ∀ k ≤ 17 * pSub + 22, bitLen (serState ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ)) d
    (fun _ => 1) g k).2.natAbs ≤ W
  hac : ∀ k < 17 * pSub + 22, bitLen ((serState ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ)) d
    (fun _ => 1) g k).1 * -(NY : ℤ)).natAbs ≤ W
  hgd : ∀ k < 17 * pSub + 22, bitLen (g k * d) ≤ W
  hpos : ∀ k < 17 * pSub + 22, 0 < g k * d
  hy : bitLen ((serV g pSub NY d).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ)).natAbs ≤ W
  hr : bitLen (divRoundRatInt ((serV g pSub NY d).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ))
    ((2 ^ (43 * pSub + 60) : ℕ) : ℤ)).natAbs ≤ W

end WP.W7k3t
