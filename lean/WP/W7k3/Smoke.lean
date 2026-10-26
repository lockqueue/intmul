import WP.W7k3.SerLoop

/-!
# WP.W7k3.Smoke — evaluated checks of the series sub-kernel's reference values

The kinds' step factors are proved equal to the snapshot's lambdas (`SK.cos_g`, …) and the
recurrence step in the machine's form is proved (`serState_succ'`); these `#guard` lines evaluate
both sides at small inputs as an independent bit-exactness check.
-/

namespace WP.W7k3

open IntMul TMFw.Contracts WP.W7k2

-- The step factors of the kinds are the snapshot's lambdas.
#guard (List.range 8).map SK.cos.f == (List.range 8).map (fun _ => 1)
#guard (List.range 8).map SK.cos.g == (List.range 8).map (fun k => (2 * k + 1) * (2 * k + 2))
#guard (List.range 8).map SK.sin.g == (List.range 8).map (fun k => (2 * k + 2) * (2 * k + 3))
#guard (List.range 8).map SK.erf.f == (List.range 8).map (fun k => 2 * k + 1)
#guard (List.range 8).map SK.erf.g == (List.range 8).map (fun k => (k + 1) * (2 * k + 3))

-- The series values with the kinds equal the snapshot's costed evaluator (cos(3/4), sin(3/4),
-- a half-erf numerator), at a small precision.
#guard serState (2 ^ 30) (-9) 16 SK.cos.f SK.cos.g 12 ==
  (runRecurrenceSeriesCosted 0 (2 ^ 30) (-9) 16 (fun _ => 1)
    (fun k => (2 * k + 1) * (2 * k + 2)) 12).1
#guard serState (3 * 2 ^ 28) (-9) 16 SK.sin.f SK.sin.g 12 ==
  (runRecurrenceSeriesCosted 0 (3 * 2 ^ 28) (-9) 16 (fun _ => 1)
    (fun k => (2 * k + 2) * (2 * k + 3)) 12).1
#guard serState (5 * 2 ^ 26) (-25) 49 SK.erf.f SK.erf.g 15 ==
  (runRecurrenceSeriesCosted 0 (5 * 2 ^ 26) (-25) 49 (fun k => 2 * k + 1)
    (fun k => (k + 1) * (2 * k + 3)) 15).1

-- cos(3/4) ≈ 0.7316888689 and sin(3/4) ≈ 0.6816387600 on the 2^30 grid.
#guard let v := (serState (2 ^ 30) (-9) 16 SK.cos.f SK.cos.g 12).2
  785644900 ≤ v ∧ v ≤ 785645000
#guard let v := (serState (3 * 2 ^ 28) (-9) 16 SK.sin.f SK.sin.g 12).2
  731904000 ≤ v ∧ v ≤ 731904100

-- One step in the machine's form (W6a's rounding division, natural denominator).
#guard (List.range 6).all fun k =>
  serState (2 ^ 30) (-9) 16 SK.cos.f SK.cos.g (k + 1) ==
    (TMFw.Contracts.divRoundRatInt ((serState (2 ^ 30) (-9) 16 SK.cos.f SK.cos.g k).1 * (-9) * (SK.cos.f k : ℤ))
        ((SK.cos.gγ * k + SK.cos.gδ) * (SK.cos.gε * k + SK.cos.gζ) * 16 : ℕ),
      (serState (2 ^ 30) (-9) 16 SK.cos.f SK.cos.g k).2 +
        (serState (2 ^ 30) (-9) 16 SK.cos.f SK.cos.g k).1)

end WP.W7k3
