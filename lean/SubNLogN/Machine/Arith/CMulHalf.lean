/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulPass

/-!
# AR, products: one output component (`Arith/CMulHalf.lean`)

**Scope (honest summary).** `halfProg sub ι` turns two products `p`, `q` (as `natSyms`, consumed)
and four sign bits (read) into the `w3`-bit field of `tdivPow (±p ∓ ±q) s'` pushed on the output
stack, through two signed-field passes, one ripple pass and the field processor
(`Arith/Field.lean`, rounding `.trunc`). `halfProg_eval` is exact. Everything is proved.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

variable {K : Type}

/-- Roles of the half-output program. -/
inductive HR
  | P | Q | Sx | Sy | Sx' | Sy' | RW | X | U | V1 | V2 | Rr | Vs | Rs | Rh | R2 | T | A | B
  deriving DecidableEq

/-- First signed-field pass: `P` with signs `Sx`, `Sy` onto `V1`. -/
def hTw1 (ι : HR → K) : TwR → K
  | .P => ι .P | .Sx => ι .Sx | .Sy => ι .Sy | .RW => ι .RW | .X => ι .X | .U => ι .U | .V => ι .V1

/-- Second signed-field pass: `Q` with signs `Sx'`, `Sy'` onto `V2`. -/
def hTw2 (ι : HR → K) : TwR → K
  | .P => ι .Q | .Sx => ι .Sx' | .Sy => ι .Sy' | .RW => ι .RW | .X => ι .X | .U => ι .U | .V => ι .V2

/-- The ripple pass: `V1 ± V2` onto `Vs`. -/
def hRp (ι : HR → K) : RpR → K
  | .V1 => ι .V1 | .V2 => ι .V2 | .RW => ι .RW | .X => ι .X | .Rr => ι .Rr | .Vs => ι .Vs

/-- The field processor: `Vs` onto `T`. -/
def hFr (ι : HR → K) : FR → K
  | .src => ι .Vs | .T => ι .T | .Rs => ι .Rs | .Rh => ι .Rh | .R2 => ι .R2 | .X => ι .X
  | .A => ι .A | .B => ι .B

/-- **One output component.** -/
def halfProg (sub : Bool) (ι : HR → K) : AProg K :=
  .seq (toTwosProg (hTw1 ι)) (.seq (toTwosProg (hTw2 ι)) (.seq (rippleProg sub (hRp ι))
    (fieldProg .trunc (hFr ι))))

theorem hTw1_inj {ι : HR → K} (hι : Function.Injective ι) : Function.Injective (hTw1 ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; simp only [hTw1] at h; exact absurd (hι h) (by decide))

theorem hTw2_inj {ι : HR → K} (hι : Function.Injective ι) : Function.Injective (hTw2 ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; simp only [hTw2] at h; exact absurd (hι h) (by decide))

theorem hRp_inj {ι : HR → K} (hι : Function.Injective ι) : Function.Injective (hRp ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; simp only [hRp] at h; exact absurd (hι h) (by decide))

theorem hFr_inj {ι : HR → K} (hι : Function.Injective ι) : Function.Injective (hFr ι) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; simp only [hFr] at h; exact absurd (hι h) (by decide))

variable [DecidableEq K]

set_option maxHeartbeats 2000000 in
/-- **One output component**, exact. -/
theorem halfProg_eval (sub : Bool) {ι : HR → K} (hι : Function.Injective ι) {W w3 s' h : ℕ}
    (hW : 1 ≤ W) (hsh : s' + h = W) {p q : ℕ} (hp : p < 2 ^ W) (hq : q < 2 ^ W)
    (sx sy sx' sy' : Bool)
    (hfit : FitsTwos W (if sub then sgnV (xor sx sy) p - sgnV (xor sx' sy') q
      else sgnV (xor sx sy) p + sgnV (xor sx' sy') q))
    (DP DQ Lx Ly Lx' Ly' DR DS DH D2 : List Sym) (v : AReg) (S : K → List Sym)
    (hDP : TermOK DP) (hDQ : TermOK DQ) (hDR : DR.head? ≠ some .mark)
    (hDS : DS.head? ≠ some .mark) (hDH : DH.head? ≠ some .mark) (hD2 : D2.head? ≠ some .mark)
    (hX : (S (ι .X)).head? ≠ some .mark) (hU : TermOK (S (ι .U))) (hRr : TermOK (S (ι .Rr)))
    (hA : TermOK (S (ι .A))) (hB : TermOK (S (ι .B)))
    (hP : S (ι .P) = natSyms p ++ DP) (hQ : S (ι .Q) = natSyms q ++ DQ)
    (hSx : S (ι .Sx) = Sym.bit sx :: Lx) (hSy : S (ι .Sy) = Sym.bit sy :: Ly)
    (hSx' : S (ι .Sx') = Sym.bit sx' :: Lx') (hSy' : S (ι .Sy') = Sym.bit sy' :: Ly')
    (hR : S (ι .RW) = List.replicate W .mark ++ DR)
    (hRs : S (ι .Rs) = List.replicate s' .mark ++ DS)
    (hRh : S (ι .Rh) = List.replicate h .mark ++ DH)
    (hR2 : S (ι .R2) = List.replicate w3 .mark ++ D2) :
    ∃ v' : AReg, Eval [] (halfProg sub ι) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (ι .P) DP) (ι .Q) DQ) (ι .T)
        ((twosBits w3 (tdivPow (if sub then sgnV (xor sx sy) p - sgnV (xor sx' sy') q
          else sgnV (xor sx sy) p + sgnV (xor sx' sy') q) s')).reverse.map Sym.bit ++ S (ι .T))⟩
      (50 * W + 25 + fieldCost s' h w3) := by
  have ne : ∀ {a b : HR}, a ≠ b → ι a ≠ ι b := fun hab e => hab (hι e)
  set u := sgnV (xor sx sy) p with hu
  set x := sgnV (xor sx' sy') q with hx
  set val := if sub then u - x else u + x with hval
  set N1 := Function.update (Function.update S (ι .P) DP) (ι .V1)
    ((twosBits W u).map Sym.bit ++ S (ι .V1)) with hN1
  set N2 := Function.update (Function.update N1 (ι .Q) DQ) (ι .V2)
    ((twosBits W x).map Sym.bit ++ N1 (ι .V2)) with hN2
  set N3 := Function.update (Function.update (Function.update S (ι .P) DP) (ι .Q) DQ) (ι .Vs)
    ((twosBits W val).map Sym.bit ++ S (ι .Vs)) with hN3
  have hP3 : Function.update (Function.update (Function.update N2 (ι .V1) (S (ι .V1))) (ι .V2)
      (S (ι .V2))) (ι .Vs) ((twosBits W val).map Sym.bit ++ N2 (ι .Vs)) = N3 := by
    funext k
    simp only [hN3, hN2, hN1, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have hP4 : Function.update (Function.update N3 (ι .Vs) (S (ι .Vs))) (ι .T)
      ((twosBits w3 (tdivPow val s')).reverse.map Sym.bit ++ N3 (ι .T)) =
      Function.update (Function.update (Function.update S (ι .P) DP) (ι .Q) DQ) (ι .T)
        ((twosBits w3 (tdivPow val s')).reverse.map Sym.bit ++ S (ι .T)) := by
    funext k
    simp only [hN3, Function.update_apply, hι.eq_iff]
    split_ifs <;> simp_all
  have g1 : ∀ r : HR, r ≠ .P → r ≠ .V1 → N1 (ι r) = S (ι r) := fun r h1 h2 => by
    rw [hN1, Function.update_of_ne (ne h2), Function.update_of_ne (ne h1)]
  have g2 : ∀ r : HR, r ≠ .P → r ≠ .V1 → r ≠ .Q → r ≠ .V2 → N2 (ι r) = S (ι r) :=
    fun r h1 h2 h3 h4 => by
      rw [hN2, Function.update_of_ne (ne h4), Function.update_of_ne (ne h3), g1 r h1 h2]
  have g3 : ∀ r : HR, r ≠ .P → r ≠ .Q → r ≠ .Vs → N3 (ι r) = S (ι r) := fun r h1 h2 h3 => by
    rw [hN3, Function.update_of_ne (ne h3), Function.update_of_ne (ne h2),
      Function.update_of_ne (ne h1)]
  obtain ⟨v1, e1⟩ := toTwosProg_eval (hTw1_inj hι) hp sx sy DP DR Lx Ly v S hDP hDR hX hU hP hSx
    hSy hR
  have e1' : Eval [] (toTwosProg (hTw1 ι)) ⟨v, S⟩ ⟨v1, N1⟩ (17 * W + 9) := e1
  obtain ⟨v2, e2⟩ := toTwosProg_eval (hTw2_inj hι) hq sx' sy' DQ DR Lx' Ly' v1 N1 hDQ hDR
    (by show (N1 (ι .X)).head? ≠ _; rw [g1 _ (by decide) (by decide)]; exact hX)
    (by show TermOK (N1 (ι .U)); rw [g1 _ (by decide) (by decide)]; exact hU)
    (by show N1 (ι .Q) = _; rw [g1 _ (by decide) (by decide)]; exact hQ)
    (by show N1 (ι .Sx') = _; rw [g1 _ (by decide) (by decide)]; exact hSx')
    (by show N1 (ι .Sy') = _; rw [g1 _ (by decide) (by decide)]; exact hSy')
    (by show N1 (ι .RW) = _; rw [g1 _ (by decide) (by decide)]; exact hR)
  have e2' : Eval [] (toTwosProg (hTw2 ι)) ⟨v1, N1⟩ ⟨v2, N2⟩ (17 * W + 9) := e2
  obtain ⟨v3, e3⟩ := rippleProg_eval sub (hRp_inj hι) W u x (S (ι .V1)) (S (ι .V2)) DR v2 N2 hDR
    (by show (N2 (ι .X)).head? ≠ _
        rw [g2 _ (by decide) (by decide) (by decide) (by decide)]; exact hX)
    (by show TermOK (N2 (ι .Rr))
        rw [g2 _ (by decide) (by decide) (by decide) (by decide)]; exact hRr)
    (by show N2 (ι .V1) = _
        rw [hN2, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
          hN1, Function.update_self])
    (by show N2 (ι .V2) = _; rw [hN2, Function.update_self, g1 _ (by decide) (by decide)])
    (by show N2 (ι .RW) = _
        rw [g2 _ (by decide) (by decide) (by decide) (by decide)]; exact hR)
  have e3' : Eval [] (rippleProg sub (hRp ι)) ⟨v2, N2⟩ ⟨v3, N3⟩ (16 * W + 7) := by
    rw [← hP3]; exact e3
  obtain ⟨v4, e4⟩ := fieldProg_eval .trunc (hFr_inj hι) hW hsh hfit (S (ι .Vs)) DS DH D2 v3 N3
    hDS hDH hD2
    (by show (N3 (ι .X)).head? ≠ _; rw [g3 _ (by decide) (by decide) (by decide)]; exact hX)
    (by show TermOK (N3 (ι .A)); rw [g3 _ (by decide) (by decide) (by decide)]; exact hA)
    (by show TermOK (N3 (ι .B)); rw [g3 _ (by decide) (by decide) (by decide)]; exact hB)
    (by show N3 (ι .Vs) = _; rw [hN3, Function.update_self])
    (by show N3 (ι .Rs) = _; rw [g3 _ (by decide) (by decide) (by decide)]; exact hRs)
    (by show N3 (ι .Rh) = _; rw [g3 _ (by decide) (by decide) (by decide)]; exact hRh)
    (by show N3 (ι .R2) = _; rw [g3 _ (by decide) (by decide) (by decide)]; exact hR2)
  have e4' : Eval [] (fieldProg .trunc (hFr ι)) ⟨v3, N3⟩
      ⟨v4, Function.update (Function.update (Function.update S (ι .P) DP) (ι .Q) DQ) (ι .T)
        ((twosBits w3 (tdivPow val s')).reverse.map Sym.bit ++ S (ι .T))⟩ (fieldCost s' h w3) := by
    rw [← hP4]; exact e4
  exact ⟨v4, (Eval.seq e1' (Eval.seq e2' (Eval.seq e3' e4'))).of_eq rfl (by ring)⟩

end SubNLogN.Machine.Arith
