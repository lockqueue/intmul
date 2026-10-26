import Contracts.Machine.W6a
import WP.W6a.Basic
import Mathlib.Tactic.Ring

/-!
# WP.W6a.RoundMath — `divRoundRatInt` through natural-number long division

For `den > 0`, with `n = |num|`, `q = n / den`, `r = n % den` (all natural numbers):

* `num ≥ 0`: `divRoundRatInt num den = q + [den ≤ 2r]`;
* `num < 0`: `divRoundRatInt num den = −(q + [den < 2r])`.

This is `divRound_natForm`, proved directly from the definition with `Int.ediv_emod_unique`. It is
the natural-number reading of the signed Euclidean characterization
`divRoundRatInt x d = x / d + [d ≤ 2·(x % d)]` (`IntMulTM.Contracts.W8.divRound_euclid` in
`Contracts/W6.lean`), specialized to the sign-magnitude data the machine holds. We do not import
`Contracts/W6.lean` here: it would pull the snapshot into a machine work package.

`intSyms_divRound` packages the result in the machine's output format: the magnitude is
`M = q + [roundUp]`, and the sign symbol is `neg` iff `num < 0` and `M ≠ 0`.
-/

namespace WP.W6a

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem divRound_natForm (num : ℤ) (den : ℕ) (hd : 0 < den) :
    divRoundRatInt num den =
      if num < 0 then
        -(((num.natAbs / den +
          if den < num.natAbs % den + num.natAbs % den then 1 else 0 : ℕ)) : ℤ)
      else
        ((num.natAbs / den + if den ≤ num.natAbs % den + num.natAbs % den then 1 else 0 : ℕ) :
          ℤ) := by
  have hqr := Nat.mod_add_div num.natAbs den
  have hr := Nat.mod_lt num.natAbs hd
  generalize num.natAbs / den = q at hqr ⊢
  generalize num.natAbs % den = r at hqr hr ⊢
  have hqrZ : (r : ℤ) + (den : ℤ) * (q : ℤ) = (num.natAbs : ℤ) := by exact_mod_cast hqr
  have hdZ : (0 : ℤ) < den := by exact_mod_cast hd
  have hrZ : (r : ℤ) < den := by exact_mod_cast hr
  have h2d : (0 : ℤ) < 2 * (den : ℤ) := by omega
  unfold divRoundRatInt
  rw [if_pos hdZ]
  by_cases hneg : num < 0
  · have hnum : num = -((r : ℤ) + (den : ℤ) * (q : ℤ)) := by
      rw [hqrZ, Int.ofNat_natAbs_of_nonpos hneg.le, neg_neg]
    rw [if_pos hneg, hnum]
    by_cases hup : den < r + r
    · rw [if_pos hup]
      have hup' : (den : ℤ) < r + r := by exact_mod_cast hup
      refine ((Int.ediv_emod_unique (r := 3 * (den : ℤ) - 2 * r) h2d).mpr
        ⟨?_, by omega, by omega⟩).1
      push_cast
      ring
    · rw [if_neg hup]
      have hup' : ¬ ((den : ℤ) < r + r) := by exact_mod_cast hup
      refine ((Int.ediv_emod_unique (r := (den : ℤ) - 2 * r) h2d).mpr
        ⟨?_, by omega, by omega⟩).1
      push_cast
      ring
  · have hnum : num = (r : ℤ) + (den : ℤ) * (q : ℤ) := by
      rw [hqrZ, Int.natAbs_of_nonneg (not_lt.mp hneg)]
    rw [if_neg hneg, hnum]
    by_cases hup : den ≤ r + r
    · rw [if_pos hup]
      have hup' : (den : ℤ) ≤ r + r := by exact_mod_cast hup
      refine ((Int.ediv_emod_unique (r := 2 * (r : ℤ) - den) h2d).mpr
        ⟨?_, by omega, by omega⟩).1
      push_cast
      ring
    · rw [if_neg hup]
      have hup' : ¬ ((den : ℤ) ≤ r + r) := by exact_mod_cast hup
      refine ((Int.ediv_emod_unique (r := 2 * (r : ℤ) + den) h2d).mpr
        ⟨?_, by omega, by omega⟩).1
      push_cast
      ring

/-- `true` exactly on `gt`. -/
def isGt : Ordering → Bool
  | .gt => true
  | _ => false

theorem isGt_ordOf (x y : ℕ) : isGt (ordOf x y) = decide (y < x) := by
  unfold ordOf
  by_cases h1 : x < y
  · rw [if_pos h1, decide_eq_false (by omega)]
    rfl
  · rw [if_neg h1]
    by_cases h2 : x = y
    · rw [if_pos h2, decide_eq_false (by omega)]
      rfl
    · rw [if_neg h2, decide_eq_true (by omega)]
      rfl

/-- The machine's rounding test: with sign symbol `sg` of the numerator and `o = ordOf (2r) den`,
round the magnitude up iff `den < 2r` (negative numerator) or `den ≤ 2r` (otherwise). -/
def roundUp (sg : Option Sym) (o : Ordering) : Bool :=
  if sg = some .neg then isGt o else notLt o

theorem sgnSym_eq_neg_iff (z : ℤ) : sgnSym z = .neg ↔ z < 0 := by
  unfold sgnSym
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e (by decide), fun e => absurd e h⟩

theorem intSyms_neg_natCast (M : ℕ) :
    intSyms (-(M : ℤ)) = (if M = 0 then Sym.pos else Sym.neg) :: natSyms M := by
  have h1 : (-(M : ℤ)).natAbs = M := by simp
  unfold intSyms sgnSym
  rw [h1]
  by_cases h : M = 0
  · subst h
    simp
  · rw [if_pos (by omega), if_neg h]

/-- **Output format of `divRound`.** `M` is the rounded magnitude computed by the machine. -/
theorem intSyms_divRound (num : ℤ) (den : ℕ) (hd : 0 < den) :
    intSyms (divRoundRatInt num den) =
      (if sgnSym num = .neg ∧
          num.natAbs / den + (if roundUp (some (sgnSym num))
            (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0) ≠ 0
        then Sym.neg else Sym.pos) ::
        natSyms (num.natAbs / den + (if roundUp (some (sgnSym num))
          (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0)) := by
  rw [divRound_natForm num den hd]
  by_cases hneg : num < 0
  · have hs : sgnSym num = .neg := (sgnSym_eq_neg_iff num).2 hneg
    have hup : roundUp (some (sgnSym num)) (ordOf (num.natAbs % den + num.natAbs % den) den) =
        decide (den < num.natAbs % den + num.natAbs % den) := by
      rw [roundUp, if_pos (by rw [hs]), isGt_ordOf]
    rw [if_pos hneg, intSyms_neg_natCast, hup]
    simp only [hs, true_and, decide_eq_true_eq]
    split_ifs <;> simp_all
  · have hs : sgnSym num = .pos := by unfold sgnSym; rw [if_neg hneg]
    have hup : roundUp (some (sgnSym num)) (ordOf (num.natAbs % den + num.natAbs % den) den) =
        decide (den ≤ num.natAbs % den + num.natAbs % den) := by
      rw [roundUp, if_neg (by rw [hs]; decide), notLt_ordOf]
    rw [if_neg hneg, intSyms_natCast, hup]
    simp [hs]

#assert_std_axioms divRound_natForm isGt_ordOf sgnSym_eq_neg_iff intSyms_neg_natCast
  intSyms_divRound

end WP.W6a
