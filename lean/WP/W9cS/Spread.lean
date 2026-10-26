import WP.W9cS.Rowlist
import Mathlib.Tactic.Ring

/-!
# WP.W9cS.Spread — `W9_spread` from `W9_spreadRow`

The driver runs on `BLoc (max mr 6)`: named stacks `W0 TR TL C0 C1`, private scratch `0..5`
(`IN T OUT RS Q TMP`); the row kernel (scratch `mr`) is embedded with `inl ↦ inl`,
`inr j ↦ inr j` (it restores all its scratch, so overlapping the driver's is harmless) and
registers `Option Sym × R_row`. Cost constant `C_row + 136`.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 IntMul

/-- Driver stacks in `BLoc (max mr 6)`. -/
def eB (mr : ℕ) : DS → BLoc (max mr 6)
  | .W0 => .inl .W0
  | .TR => .inl .TR
  | .TL => .inl .TL
  | .C0 => .inl .C0
  | .C1 => .inl .C1
  | .IN => .inr ⟨0, by omega⟩
  | .T => .inr ⟨1, by omega⟩
  | .OUT => .inr ⟨2, by omega⟩
  | .RS => .inr ⟨3, by omega⟩
  | .Q => .inr ⟨4, by omega⟩
  | .TMP => .inr ⟨5, by omega⟩

theorem eB_injective (mr : ℕ) : Function.Injective (eB mr) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [eB] at h)

/-- The row kernel's stacks inside the driver's. -/
def kerEmb (mr : ℕ) : BLoc mr → BLoc (max mr 6) := Sum.map id (Fin.castLE (Nat.le_max_left mr 6))

theorem kerEmb_injective (mr : ℕ) : Function.Injective (kerEmb mr) := by
  intro a b h
  cases a <;> cases b <;> simp_all [kerEmb, Fin.ext_iff]

/-- **The spread program**, for a row kernel `P`. -/
def spreadProg {mr : ℕ} {Rr : Type} (P : Prog (BLoc mr) (fun _ => Sym) Rr) :
    Prog (BLoc (max mr 6)) (fun _ => Sym) (Option Sym × Rr) :=
  driver (eB mr) (embedP (kerEmb mr) (Lens.snd (Option Sym) Rr) P)

theorem spreadProg_closed {mr : ℕ} {Rr : Type} {P : Prog (BLoc mr) (fun _ => Sym) Rr}
    (hc : P.Closed) : (spreadProg P).Closed :=
  driver_closed _ (embedP_closed _ _ hc)

/-- Cost arithmetic. -/
theorem spread_cost_le (Crow t1 SRB Neb hdr bp bm bt br r reb A B : ℕ) (ht1 : 1 ≤ t1)
    (hA : A ≤ Neb) (hB : B ≤ Neb) (h1 : reb + hdr + 1 ≤ SRB) (h2 : r ≤ reb)
    (h3 : bp + bm + bt + br ≤ hdr) :
    6 * (bp + bm + bt) + 9 * br + 6 * A + 3 * B + t1 * (Crow * SRB + 7 * br + 16 * r + 9 * reb + 17) +
      72 ≤ (Crow + 136) * (t1 * SRB + Neb + 1) := by
  have hP : SRB ≤ t1 * SRB := Nat.le_mul_of_pos_left SRB (by omega)
  have e1 : t1 * (Crow * SRB + 7 * br + 16 * r + 9 * reb + 17) =
      Crow * (t1 * SRB) + t1 * (7 * br + 16 * r + 9 * reb + 17) := by ring
  have e2 : t1 * (7 * br + 16 * r + 9 * reb + 17) ≤ t1 * (49 * SRB) :=
    Nat.mul_le_mul_left _ (by omega)
  have e3 : t1 * (49 * SRB) = 49 * (t1 * SRB) := by ring
  have e4 : (Crow + 136) * (t1 * SRB + Neb + 1) =
      Crow * (t1 * SRB) + 136 * (t1 * SRB) + (Crow + 136) * Neb + (Crow + 136) := by ring
  have e5 : 136 * Neb ≤ (Crow + 136) * Neb := Nat.mul_le_mul_right _ (by omega)
  rw [e1, e4]
  omega

#assert_std_axioms eB_injective kerEmb_injective spreadProg_closed spread_cost_le

end WP.W9c
