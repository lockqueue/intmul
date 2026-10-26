/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.RotateLevels

/-!
# K1, K4-ctl-par (`K1/RotateParFiber.lean`): the routine with parameters, one fiber

**Scope (honest summary).** Building blocks (no `sorry`) of the parameterized controlled rotation
`K4RotateCtlParStmt` (`K1/RotateParSpec.lean`; paper: Fact 3.3(4) (`fact:oai-streams`) and
Lemma A.4 (`lem:transfer-streams`)), reusing the K4-ctl kernel unchanged.

## Design (plan)
The K4-ctl programs (`fibProg`, `lvN2` … `lvC1`, `rotProg`, files `RotateFiber/Levels/Rotate`)
are generic in the offset routine's scratch family `Eo`. The parameterized kernel instantiates
them with `Eo := Fin 2 ⊕ Eo'`: the two parameter stacks `k1, k2` live in the routine's "scratch"
slots `rP1 = .inr (.inl (.inl 0))`, `rP2 = .inr (.inl (.inl 1))`, and the routine is the
parameterized routine relabeled (`relP`, along the bijection `embP : KLoc (Fin 6) Eo' →
KLoc (Fin 4) (Fin 2 ⊕ Eo')`, `4 ↦ .inr (.inl 0)`, `5 ↦ .inr (.inl 1)`). The relabeled routine
satisfies `OffSpecQ` (its output may depend on the two parameter slots); the levels' `Runs`
rules are re-proved under `OffSpecQ` with the parameter slots carried as invariants (they are never
written). At the top (`K1/RotatePar.lean`) the kernel is relabeled to `KLoc (Fin 10) _`.

## Contents
* `lensIdR`, `embP`/`unP` (inverse bijections), `relP`, `OffSpecP` (the body of
  `K4OffsetCtlParStmt`), `OffSpecQ`, `offSpecQ_relP`;
* `runs_callOQ`: the routine call inside the kernel;
* `runs_fib_fstQ`: one fiber (as `runs_fib_fst`, offset `off p1 p2 b c1 c2`);
* `fib_cost_leP`: the routine's cost `Co·(b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1)^J`
  is absorbed with constant `fibK0 q (2·cb) J Co`, given `b1, b2, p1, p2 ≤ cb·b`.
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Relabeling the parameterized routine -/

/-- The identity register lens. -/
def lensIdR (σ : Type) : Lens σ σ where
  get := id
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

section Relabel

variable {Eo : Type}

/-- The parameterized routine's stacks as stacks of a `Fin 4` routine: named `0..3` stay, the
parameters `4, 5` become scratch slots `.inr (.inl 0)`, `.inr (.inl 1)`. -/
def embP : KLoc (Fin 6) Eo → KLoc (Fin 4) (Fin 2 ⊕ Eo)
  | .inl i => if h : i.val < 4 then .inl ⟨i.val, h⟩
      else .inr (.inl ⟨i.val - 4, by have := i.isLt; omega⟩)
  | .inr e => .inr (.inr e)

/-- Inverse of `embP`. -/
def unP : KLoc (Fin 4) (Fin 2 ⊕ Eo) → KLoc (Fin 6) Eo
  | .inl i => .inl ⟨i.val, by have := i.isLt; omega⟩
  | .inr (.inl j) => .inl ⟨4 + j.val, by have := j.isLt; omega⟩
  | .inr (.inr e) => .inr e

theorem unP_embP (x : KLoc (Fin 6) Eo) : unP (embP x) = x := by
  rcases x with i | e
  · fin_cases i <;> rfl
  · rfl

theorem embP_unP (y : KLoc (Fin 4) (Fin 2 ⊕ Eo)) : embP (unP y) = y := by
  rcases y with i | j | e
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl
  · rfl

theorem embP_injective : Function.Injective (embP : KLoc (Fin 6) Eo → KLoc (Fin 4) (Fin 2 ⊕ Eo)) :=
  Function.LeftInverse.injective unP_embP

end Relabel

/-- The body of `K4OffsetCtlParStmt off J` (`K1/RotateParSpec.lean`), for one program `P` with
constant `C`. -/
def OffSpecP (off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (J : ℕ) {E R : Type} [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R) : Prop :=
  ∀ (k1 k2 b c1 c2 : ℕ) (r0 r1 r2 r4 r5 : List Sym) (S : KLoc (Fin 6) E → List Sym),
    TermOK r0 → TermOK r1 → TermOK r2 → TermOK r4 → TermOK r5 →
    S (.inl 0) = natSyms b ++ r0 → S (.inl 1) = natSyms c1 ++ r1 →
    S (.inl 2) = natSyms c2 ++ r2 → S (.inl 4) = natSyms k1 ++ r4 →
    S (.inl 5) = natSyms k2 ++ r5 →
    Runs P S (Function.update S (.inl 3) (natSyms (off k1 k2 b c1 c2) ++ S (.inl 3)))
      (fun _ => True) (C * (b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1) ^ J)

/-- The same spec for a `Fin 4` routine reading its parameters from the scratch slots
`.inr (.inl 0)`, `.inr (.inl 1)` (which, like every stack but `3`, are restored). -/
def OffSpecQ (off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (J : ℕ) {E R : Type} [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 4) (Fin 2 ⊕ E)) (fun _ => Sym) R) : Prop :=
  ∀ (k1 k2 b c1 c2 : ℕ) (r0 r1 r2 r4 r5 : List Sym) (S : KLoc (Fin 4) (Fin 2 ⊕ E) → List Sym),
    TermOK r0 → TermOK r1 → TermOK r2 → TermOK r4 → TermOK r5 →
    S (.inl 0) = natSyms b ++ r0 → S (.inl 1) = natSyms c1 ++ r1 →
    S (.inl 2) = natSyms c2 ++ r2 → S (.inr (.inl 0)) = natSyms k1 ++ r4 →
    S (.inr (.inl 1)) = natSyms k2 ++ r5 →
    Runs P S (Function.update S (.inl 3) (natSyms (off k1 k2 b c1 c2) ++ S (.inl 3)))
      (fun _ => True) (C * (b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1) ^ J)

/-- The parameterized routine, relabeled as a `Fin 4` routine. -/
def relP {E R : Type} (P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R) :
    Prog (KLoc (Fin 4) (Fin 2 ⊕ E)) (fun _ => Sym) R :=
  callInj embP (lensIdR R) P

theorem closed_relP {E R : Type} {P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R} (h : P.Closed) :
    (relP P).Closed :=
  closed_callInj _ _ h

theorem offSpecQ_relP {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J : ℕ} {E R : Type} [DecidableEq E]
    {C : ℕ} {P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R} (h : OffSpecP off J C P) :
    OffSpecQ off J C (relP P) := by
  intro k1 k2 b c1 c2 r0 r1 r2 r4 r5 S h0 h1 h2 h4 h5 hS0 hS1 hS2 hS4 hS5
  have he : (embP (.inl 3) : KLoc (Fin 4) (Fin 2 ⊕ E)) = .inl 3 := rfl
  have hP := h k1 k2 b c1 c2 r0 r1 r2 r4 r5 (S ∘ embP) h0 h1 h2 h4 h5 hS0 hS1 hS2 hS4 hS5
  refine runs_callInj (Q := fun _ => True) embP_injective (lensIdR R) ?_ ?_
  · rw [← he, Function.update_comp_eq_of_injective S embP_injective]
    exact hP
  · intro k hk
    exact absurd (embP_unP k) (hk _)

/-! ## The parameter slots inside the kernel -/

section Slots

variable {Eo : Type}

/-- The parameter `k1` (inside the kernel's routine-scratch region). -/
abbrev rP1 : RotL (Fin 2 ⊕ Eo) := .inr (.inl (.inl 0))
/-- The parameter `k2` (inside the kernel's routine-scratch region). -/
abbrev rP2 : RotL (Fin 2 ⊕ Eo) := .inr (.inl (.inl 1))

variable [DecidableEq Eo] (B : RotL (Fin 2 ⊕ Eo) → List Sym) (src O H H2 U : List Sym)

@[simp] theorem fst_P1 : fst B src O H H2 U rP1 = B rP1 := by simp [fst]
@[simp] theorem fst_P2 : fst B src O H H2 U rP2 = B rP2 := by simp [fst]

end Slots

theorem runs_callOQ {Eo Ro : Type} [DecidableEq Eo] {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) (Fin 2 ⊕ Eo)) (fun _ => Sym) Ro} (hO : OffSpecQ off J Co Po)
    (B : RotL (Fin 2 ⊕ Eo) → List Sym) (p1 p2 b c1 c2 : ℕ) (r0 r1 r2 r8 r9 : List Sym)
    (hr0 : TermOK r0) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr8 : TermOK r8) (hr9 : TermOK r9)
    (hb : B rB = natSyms b ++ r0) (h1 : B rC1 = natSyms c1 ++ r1)
    (h2 : B rC2 = natSyms c2 ++ r2) (hp1 : B rP1 = natSyms p1 ++ r8)
    (hp2 : B rP2 = natSyms p2 ++ r9) :
    Runs (callInj embO (rlR (Ro := Ro)) Po) B
      (Function.update B rO (natSyms (off p1 p2 b c1 c2) ++ B rO)) (fun _ => True)
      (Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J) := by
  have he : (embO (.inl 3) : RotL (Fin 2 ⊕ Eo)) = rO := by simp [embO]
  have hP := hO p1 p2 b c1 c2 r0 r1 r2 r8 r9 (B ∘ embO) hr0 hr1 hr2 hr8 hr9
    (by simpa [embO] using hb) (by simpa [embO] using h1) (by simpa [embO] using h2) hp1 hp2
  refine runs_callInj (Q := fun _ => True) embO_injective rlR ?_ ?_
  · rw [← he, Function.update_comp_eq_of_injective B embO_injective]
    exact hP
  · intro k hk
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hk (.inl 3) he

/-! ## One fiber -/

section Fiber

variable {Eo Ro : Type} [DecidableEq Eo]

/-- **One fiber, in `fst` form** (as `runs_fib_fst`): the fiber `f` leaves the source and its
rotation by `off p1 p2 b c1 c2` blocks is staged, reversed, on `U`. -/
theorem runs_fib_fstQ {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) (Fin 2 ⊕ Eo)) (fun _ => Sym) Ro} (hO : OffSpecQ off J Co Po)
    (q : ℕ) (hq : 2 ≤ q) (B : RotL (Fin 2 ⊕ Eo) → List Sym) (f w : List (List Bool))
    (rest : List Sym) (b c1 c2 s p1 p2 : ℕ) (rb r1 r2 rs r8 r9 : List Sym) (hrb : TermOK rb)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hrs : TermOK rs) (hr8 : TermOK r8) (hr9 : TermOK r9)
    (hs1 : 1 ≤ s) (hf : f.length = q ^ b * s) (hoff : off p1 p2 b c1 c2 < q ^ b)
    (hbS : B rB = natSyms b ++ rb) (hC1 : B rC1 = natSyms c1 ++ r1)
    (hC2 : B rC2 = natSyms c2 ++ r2) (hsS : B rS = natSyms s ++ rs)
    (hP1 : B rP1 = natSyms p1 ++ r8) (hP2 : B rP2 = natSyms p2 ++ r9)
    (O0 H0 H20 U0 : List Sym) :
    Runs (fibProg q Po) (fst B (arrSyms (f ++ w) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms w ++ rest) O0 H0 H20
        ((arrSyms (rotB (q ^ b) s (off p1 p2 b c1 c2) f)).reverse ++ U0))
      (fun _ => True)
      (Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J + fibK q * vol f) := by
  have x1 : Runs (rwk (Ro := Ro) (pushC rO .mark))
      (fst B (arrSyms (f ++ w) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (f ++ w) ++ rest) (Sym.mark :: O0) H0 H20 U0) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_wk_pushC rlO rO Sym.mark _) (by simp)
  have x2 : Runs (callInj embO (rlR (Ro := Ro)) Po)
      (fst B (arrSyms (f ++ w) ++ rest) (Sym.mark :: O0) H0 H20 U0)
      (fst B (arrSyms (f ++ w) ++ rest) (natSyms (off p1 p2 b c1 c2) ++ Sym.mark :: O0) H0 H20
        U0)
      (fun _ => True) (Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J) :=
    WP.W9comp.runs_congr (runs_callOQ hO _ p1 p2 b c1 c2 rb r1 r2 r8 r9 hrb hr1 hr2 hr8 hr9
      (by simp [hbS]) (by simp [hC1]) (by simp [hC2]) (by simp [hP1]) (by simp [hP2])) (by simp)
  have x3 : Runs (rwk (Ro := Ro) (pushC rH .mark))
      (fst B (arrSyms (f ++ w) ++ rest) (natSyms (off p1 p2 b c1 c2) ++ Sym.mark :: O0) H0 H20
        U0)
      (fst B (arrSyms (f ++ w) ++ rest) (natSyms (off p1 p2 b c1 c2) ++ Sym.mark :: O0)
        (Sym.mark :: H0) H20 U0) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_wk_pushC rlO rH Sym.mark _) (by simp)
  have x4 := runs_fib_pow (Ro := Ro) q B f w rest b s rb rs hrb hrs hf hbS hsS
    (natSyms (off p1 p2 b c1 c2) ++ Sym.mark :: O0) H0 H20 U0
  have x5 : Runs (rwk (Ro := Ro) (pushC rH2 .mark))
      (fst B (arrSyms w ++ rest) (natSyms (off p1 p2 b c1 c2) ++ Sym.mark :: O0)
        ((arrSyms f).reverse ++ Sym.mark :: H0) H20 U0)
      (fst B (arrSyms w ++ rest) (natSyms (off p1 p2 b c1 c2) ++ Sym.mark :: O0)
        ((arrSyms f).reverse ++ Sym.mark :: H0) (Sym.mark :: H20) U0) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_wk_pushC rlO rH2 Sym.mark _) (by simp)
  have x6 := runs_fib_cnt (Ro := Ro) q B f w rest b s (off p1 p2 b c1 c2) rs hrs hf hoff hsS
    O0 H0 H20 U0
  have x7 := runs_fib_tail (Ro := Ro) B (f.take ((q ^ b - off p1 p2 b c1 c2) * s))
    (f.drop ((q ^ b - off p1 p2 b c1 c2) * s)) (arrSyms w ++ rest) O0 H0 H20 U0
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq x1 (WP.W9comp.runs_seq x2
    (WP.W9comp.runs_seq x3 (WP.W9comp.runs_seq x4 (WP.W9comp.runs_seq x5
    (WP.W9comp.runs_seq x6 x7)))))) (fun _ h => h) ?_
  exact fib_cost_arith q b s (off p1 p2 b c1 c2) _ f hq hs1 hf hoff

end Fiber

/-! ## Absorbing the parameterized routine's cost -/

theorem cb_le2 {cb b x : ℕ} (h : x ≤ cb * b) : x ≤ 2 * cb * b :=
  h.trans (Nat.mul_le_mul_right _ (by omega))

theorem one_le_bitLen_of_two {q : ℕ} (hq : 2 ≤ q) : 1 ≤ bitLen q := by
  have h := TMFw.W3s.lt_two_pow_bitLen q
  rcases Nat.eq_zero_or_pos (bitLen q) with h0 | h0
  · rw [h0] at h
    simp at h
    omega
  · exact h0

/-- **Fiber cost absorption, with parameters.** With `b1, b2, p1, p2 ≤ cb·b`, the routine's cost
and the fiber's linear cost are at most `fibK0 q (2·cb) J Co` per symbol of the fiber. -/
theorem fib_cost_leP (q cb J Co b b1 b2 c1 c2 p1 p2 s : ℕ) (hq : 2 ≤ q) (hc1 : c1 < q ^ b1)
    (hc2 : c2 < q ^ b2) (hb1 : b1 ≤ cb * b) (hb2 : b2 ≤ cb * b) (hp1 : p1 ≤ cb * b)
    (hp2 : p2 ≤ cb * b) (f : List (List Bool)) (hs1 : 1 ≤ s) (hf : f.length = q ^ b * s) :
    Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J + fibK q * vol f ≤
      fibK0 q (2 * cb) J Co * vol f := by
  have e1 : bitLen c1 ≤ cb * b * bitLen q :=
    (bitLen_lt_pow q b1 c1 hc1).trans (Nat.mul_le_mul_right _ hb1)
  have e2 : bitLen c2 ≤ cb * b * bitLen q :=
    (bitLen_lt_pow q b2 c2 hc2).trans (Nat.mul_le_mul_right _ hb2)
  have e1' : bitLen p1 ≤ cb * b := (bitLen_le_self' p1).trans hp1
  have e2' : bitLen p2 ≤ cb * b := (bitLen_le_self' p2).trans hp2
  have hw : cb * b * 1 ≤ cb * b * bitLen q :=
    Nat.mul_le_mul_left _ (one_le_bitLen_of_two hq)
  have e3 : b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1 ≤
      (1 + 2 * (2 * cb) * bitLen q) * (b + 1) := by
    nlinarith
  have e4 : (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J ≤
      (1 + 2 * (2 * cb) * bitLen q) ^ J * (J.factorial * 2 ^ J * 2 ^ b) := by
    calc (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J
        ≤ ((1 + 2 * (2 * cb) * bitLen q) * (b + 1)) ^ J := Nat.pow_le_pow_left e3 J
      _ = (1 + 2 * (2 * cb) * bitLen q) ^ J * (b + 1) ^ J := by rw [mul_pow]
      _ ≤ (1 + 2 * (2 * cb) * bitLen q) ^ J * (J.factorial * 2 ^ J * 2 ^ b) :=
          Nat.mul_le_mul_left _ (pow_le_two_pow J b)
  have e5 : 2 ^ b ≤ vol f := by
    have h1 : 2 ^ b ≤ q ^ b := Nat.pow_le_pow_left hq b
    have h2 : q ^ b ≤ q ^ b * s := Nat.le_mul_of_pos_right _ hs1
    have h3 := length_le_vol f
    omega
  have e6 : Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J ≤
      Co * ((1 + 2 * (2 * cb) * bitLen q) ^ J * (J.factorial * 2 ^ J)) * vol f := by
    calc Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J
        ≤ Co * ((1 + 2 * (2 * cb) * bitLen q) ^ J * (J.factorial * 2 ^ J * 2 ^ b)) :=
          Nat.mul_le_mul_left _ e4
      _ = Co * ((1 + 2 * (2 * cb) * bitLen q) ^ J * (J.factorial * 2 ^ J)) * 2 ^ b := by ring
      _ ≤ Co * ((1 + 2 * (2 * cb) * bitLen q) ^ J * (J.factorial * 2 ^ J)) * vol f :=
          Nat.mul_le_mul_left _ e5
  unfold fibK0
  rw [Nat.add_mul]
  omega

end SubNLogN.Machine.K1.Rot
