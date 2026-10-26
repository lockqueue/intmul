import Contracts.W9.Pre

/-!
# WP.W9s.SpecDefs — the list-level reference of the synthetic FFT (definitions only)

Shared by the machine proof (W9s owner) and the spec-math proof (`WP.W9s.SpecMath`). The
list-level definitions of `synL` and its auxiliary operations.
-/

namespace WP.W9s

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- Butterfly with rounding: `neg = true` subtracts `b` (the snapshot adds a negated entry). -/
def bfly (neg : Bool) (a b : ℤ × ℤ) : ℤ × ℤ :=
  if neg then (divRoundPow2 (a.1 - b.1) 1, divRoundPow2 (a.2 - b.2) 1)
  else (divRoundPow2 (a.1 + b.1) 1, divRoundPow2 (a.2 + b.2) 1)

/-- Rotation by `s`: the last `s` entries first (`s ≤ f.length` in all uses). -/
def rotL (s : ℕ) (f : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  f.drop (f.length - s) ++ f.take (f.length - s)

/-- Entrywise butterfly; the first `s` entries use sign `!neg`, the rest `neg`. -/
def zipB (neg : Bool) : ℕ → List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | _, [], _ => []
  | _, _ :: _, [] => []
  | 0, a :: as, g :: gs => bfly neg a g :: zipB neg 0 as gs
  | s + 1, a :: as, g :: gs => bfly (!neg) a g :: zipB neg s as gs

/-- Combine with shift step `Δ`: plus rows (`zipB false`), then minus rows (`zipB true`); row `u`
uses shift `Δ·u`. -/
def combL (Δ : ℕ) (Y0 Y1 : List (List (ℤ × ℤ))) : List (List (ℤ × ℤ)) :=
  (List.range Y0.length).map (fun u =>
      zipB false (Δ * u) (Y0.getD u []) (rotL (Δ * u) (Y1.getD u []))) ++
    (List.range Y0.length).map (fun u =>
      zipB true (Δ * u) (Y0.getD u []) (rotL (Δ * u) (Y1.getD u [])))

/-- Even-indexed elements. -/
def evensL {α : Type} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: evensL l

/-- Odd-indexed elements. -/
def oddsL {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: b :: l => b :: oddsL l

/-- List-level synthetic FFT of `2^k` rows; the top combine uses step `Δ`, deeper ones `2Δ, 4Δ, …`. -/
def synL (Δ : ℕ) : ℕ → List (List (ℤ × ℤ)) → List (List (ℤ × ℤ))
  | 0, X => X
  | k + 1, X => combL Δ (synL (2 * Δ) k (evensL X)) (synL (2 * Δ) k (oddsL X))

end WP.W9s
