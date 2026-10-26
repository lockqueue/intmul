import WP.W7k3t.Rules

set_option linter.unusedSimpArgs false

/-!
# WP.W7k3t.Src — `SRC`: scale, round, clamp (`z += srcV X e f`)

`srcV X e f = max (−2^e) (min (2^e) (divRound (X·2^e) (2^f)))`: the tail of the snapshot's
`normSinc` / `exp` clamps and of the tap's final rounding.

Host `Loc 4 20`; named `0 X` (signed), `1 e`, `2 f` (naturals), all restored; `3` destination.
Scratch (each on a `mark` floor, restored): `T = 2^e`, `N = −2^e`, `Z = 0` (signed), `P = X·T`,
`D = 2^f` (natural), `R = divRound P D`. Clamp: `R > T` ⇒ `z += T + 0`; else `R < N` ⇒
`z += N + 0`; else `z += R + 0`. Proof pattern of `Mul.lean`.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-- Clamped rounded rescaling `max (-2^e) (min (2^e) (divRound (X·2^e) (2^f)))`. -/
def srcV (X : ℤ) (e f : ℕ) : ℤ :=
  max (-((2 ^ e : ℕ) : ℤ)) (min ((2 ^ e : ℕ) : ℤ)
    (divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ)))

instance srcBig : Big 4 20 := ⟨by decide⟩

section Prog

variable (I : TI)

/-- `T = 2^e`, `N = −2^e`, `Z = 0` (signed, on floors). -/
def srcConsts : HP 4 20 I :=
  (pushS (.inr 0) .mark).seq <| (tp2 I (.inl 1) (.inr 0)).seq <| (pushS (.inr 0) .pos).seq <|
  (pushS (.inr 1) .mark).seq <| (tp2 I (.inl 1) (.inr 1)).seq <| (pushS (.inr 1) .neg).seq <|
  (pushS (.inr 2) .mark).seq (pushS (.inr 2) .pos)

/-- `P = X·T`, `D = 2^f`, `R = divRound P D`. -/
def srcRound : HP 4 20 I :=
  (pushS (.inr 3) .mark).seq <| (tmu I (.inl 0) (.inr 0) (.inr 3)).seq <|
  (pushS (.inr 4) .mark).seq <| (tp2 I (.inl 2) (.inr 4)).seq <|
  (pushS (.inr 5) .mark).seq (tdv I (.inr 3) (.inr 4) (.inr 5))

/-- The clamp: push the clamped `R` on the destination. -/
def srcClamp : HP 4 20 I :=
  (tci I (.inr 5) (.inr 0)).seq (.ite (fun s => decide (I.ci.obs (I.lci.get s) = .gt))
    (tai I (.inr 0) (.inr 2) (.inl 3))
    ((tci I (.inr 5) (.inr 1)).seq (.ite (fun s => decide (I.ci.obs (I.lci.get s) = .lt))
      (tai I (.inr 1) (.inr 2) (.inl 3)) (tai I (.inr 5) (.inr 2) (.inl 3)))))

/-- Drop the scratch values and floors. -/
def srcClean : HP 4 20 I :=
  (tdrI I (.inr 5)).seq <| (popS (.inr 5)).seq <| (tdr I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (tdrI I (.inr 3)).seq <| (popS (.inr 3)).seq <| (popS (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (tdrI I (.inr 1)).seq <| (popS (.inr 1)).seq <| (tdrI I (.inr 0)).seq (popS (.inr 0))

/-- **SRC.** -/
def srcProg : Prog (Loc 4 20) (fun _ => Sym) I.R :=
  (srcConsts I).seq ((srcRound I).seq ((srcClamp I).seq (srcClean I)))

theorem srcProg_closed : (srcProg I).Closed :=
  ⟨⟨trivial, tp2_closed _ _ _, trivial, trivial, tp2_closed _ _ _, trivial, trivial, trivial⟩,
    ⟨trivial, callI_closed _ _ _ _, trivial, tp2_closed _ _ _, trivial, callI_closed _ _ _ _⟩,
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
      callI_closed _ _ _ _⟩,
    ⟨tdrI_closed _ _, trivial, callI_closed _ _ _ _, trivial, tdrI_closed _ _, trivial, trivial,
      trivial, tdrI_closed _ _, trivial, tdrI_closed _ _, trivial⟩⟩

end Prog

/-! ## Value and width lemmas -/

theorem srcV_gt {X : ℤ} {e f : ℕ}
    (h : ((2 ^ e : ℕ) : ℤ) < divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ)) :
    srcV X e f = ((2 ^ e : ℕ) : ℤ) := by
  unfold srcV
  rw [min_eq_left h.le]
  have h0 : (0 : ℤ) ≤ ((2 ^ e : ℕ) : ℤ) := by positivity
  exact max_eq_right (by omega)

theorem srcV_lt {X : ℤ} {e f : ℕ}
    (h1 : ¬ ((2 ^ e : ℕ) : ℤ) < divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ))
    (h2 : divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ) < -((2 ^ e : ℕ) : ℤ)) :
    srcV X e f = -((2 ^ e : ℕ) : ℤ) := by
  unfold srcV
  rw [min_eq_right (not_lt.mp h1)]
  exact max_eq_left h2.le

theorem srcV_mid {X : ℤ} {e f : ℕ}
    (h1 : ¬ ((2 ^ e : ℕ) : ℤ) < divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ))
    (h2 : ¬ divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ) < -((2 ^ e : ℕ) : ℤ)) :
    srcV X e f = divRoundRatInt (X * ((2 ^ e : ℕ) : ℤ)) ((2 ^ f : ℕ) : ℤ) := by
  unfold srcV
  rw [min_eq_right (not_lt.mp h1)]
  exact max_eq_right (not_lt.mp h2)

theorem cmpZ_eq_gt {x y : ℤ} : cmpZ x y = .gt ↔ y < x := by
  unfold cmpZ
  split_ifs with h1 h2 <;> simp <;> omega

theorem cmpZ_eq_lt {x y : ℤ} : cmpZ x y = .lt ↔ x < y := by
  unfold cmpZ
  split_ifs with h1 h2 <;> simp <;> omega

theorem intSyms_pow2 (k : ℕ) : intSyms ((2 ^ k : ℕ) : ℤ) = Sym.pos :: natSyms (2 ^ k) :=
  intSyms_natCast _

theorem intSyms_negPow2 (k : ℕ) : intSyms (-((2 ^ k : ℕ) : ℤ)) = Sym.neg :: natSyms (2 ^ k) := by
  have hpos : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  unfold intSyms sgnSym
  rw [if_pos (by omega), Int.natAbs_neg, Int.natAbs_natCast]

theorem intSyms_zero' : intSyms 0 = [Sym.pos] := by
  simp [intSyms, sgnSym, natSyms, encodeNat_zero]

theorem bitLen_pow2_cast (k : ℕ) : bitLen (((2 ^ k : ℕ) : ℤ)).natAbs = k + 1 := by
  rw [Int.natAbs_natCast, WP.W7k2.bitLen_two_pow]

theorem bitLen_negPow2_cast (k : ℕ) : bitLen (-((2 ^ k : ℕ) : ℤ)).natAbs = k + 1 := by
  rw [Int.natAbs_neg, bitLen_pow2_cast]

theorem bitLen_zero_cast : bitLen (0 : ℤ).natAbs = 0 := WP.W7k2.bitLen_zero

#assert_std_axioms srcProg_closed srcV_gt srcV_lt srcV_mid cmpZ_eq_gt cmpZ_eq_lt intSyms_pow2
  intSyms_negPow2 intSyms_zero' bitLen_pow2_cast bitLen_negPow2_cast bitLen_zero_cast

end WP.W7k3t
