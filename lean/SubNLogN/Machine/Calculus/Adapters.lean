/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Frame
import Contracts.Machine.W3
import Contracts.Machine.W5
import Contracts.Machine.W6a
import SubNLogN.Machine.MulBig.Contract

/-!
# Framed procedure calculus: call-site adapters (`Calculus/Adapters.lean`)

Every existing contract family states a `Runs` fact about a **closed** program over its own local
stacks. A recursive procedure body needs instead a `RunsIn ρ` fact (any environment `ρ`) about the
component embedded into the caller's stacks (`callInj ι l P`, `callX E h l P`). This file turns
each family into such `RunsIn` facts, so kernel workers never touch `Triple`/`Eval`.

All adapters take the *obtained instance* of a contract as hypotheses: the program `P`, the
constant `C`, closedness `hcl : P.Closed`, and the contract body `hspec` for this `P` and `C`
(copied verbatim from the contract). After `obtain ⟨C, hC⟩ := h; obtain ⟨m, R, obs, P, hm, hR,
hne, hcl, hspec⟩ := hC ()` (for an `MContract`), `hspec` has exactly the stated type. Finiteness
and nonemptiness of the register type are not needed. The embedding `ι` must be injective; the
register lens `l` is arbitrary.

Contract family → adapter (`RunsIn` call-site form; the `FramedRunsIn` protected-tail form has
the same name in the namespace `FramedRunsIn`):
* any closed `P` with a `Runs` fact restricted along an injective `ι` (in particular every
  `MContract` kernel over `Loc n m` and every `KContract N` kernel over `KLoc N E`):
  `callInj_same`, `callInj_upd`, `callInj_upd2`, `callInj_upd3`, `callInj_upd4` (`0`–`4` updated
  stacks); `RunsIn.of_callInj_reg` (arbitrary final stacks, keeps the register postcondition, e.g.
  for observation kernels); the framed forms take a framed local fact with a component tail
  class `Gc` and pull it back along `ι`;
* clean scratch premises (`KClean S`, `EClean S`): `kClean_comp`, `eClean_comp`; in the framed
  form, put `tl = []` on the scratch images into the tail class;
* `BContract` W9 stages over `BLoc m` inside `XLoc m' E` (`callX`): `RunsIn.callX_of_runs`
  (arbitrary final stacks), `callX_same`, `callX_upd`, `callX_upd2`, `callX_upd3` (named `LB`
  stacks updated);
* `W3_addNat`: `w3_addNat`; `W3_subNat`: `w3_subNat`; `W5_mulAt Mul`: `w5_mulAt`;
  `W6a_divModNat`: `w6a_divModNat`; `MulBigContract` (`SpecMulBig P C`): `mulBig`. The framed
  forms start from the local content `B₀` (operand encodings without tails) with tail class
  `TermOK` below the operands (and `[]` below `mulBig`'s scratch images), arbitrary elsewhere.

The costs are exactly the contracts' costs (embedding is free).
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Contracts.W9

namespace RunsIn

/-! ## Generic: a closed component on an injective sub-layout -/

section Generic

variable {K σ L R : Type} [DecidableEq K] [DecidableEq L]

/-- **`callInj` with the register postcondition kept** (through the lens): the general form, with
arbitrary big final stacks `B'` that agree with `B` outside the image of `ι`. -/
theorem of_callInj_reg {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B B' (fun v => Q (l.get v)) T := by
  refine of_runs ?_ (closed_callInj ι l hcl) ρ
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := hP ⟨l.get v, stk ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact (h1 x).trans (congrFun hs' x)
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  refine ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, ?_⟩, ht⟩
  show Q (l.get (l.set v s'.var))
  rw [l.get_set]
  exact hq

/-- A component that restores every stack it sees. -/
theorem callInj_same {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : K → List Sym)
    (h : Runs P (B ∘ ι) (B ∘ ι) Q T) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B B (fun _ => True) T :=
  of_callInj hι l hcl h (fun _ _ => rfl) ρ

/-- **One updated stack** (`RunsIn.callInj_upd`): `P` runs from `B ∘ ι` to `B ∘ ι` with stack `x`
replaced by `v`; embedded, it runs from `B` to `B` with stack `ι x` replaced by `v`. -/
theorem callInj_upd {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : K → List Sym)
    (x : L) (v : List Sym) (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T := by
  refine of_callInj (Q := Q) hι l hcl ?_ (fun k hk => Function.update_of_ne (Ne.symm (hk x)) _ _) ρ
  rw [Function.update_comp_eq_of_injective B hι x v]
  exact h

/-- **Two updated stacks** (`RunsIn.callInj_upd2`). -/
theorem callInj_upd2 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : K → List Sym)
    (x0 x1 : L) (v0 v1 : List Sym)
    (h : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x0 v0) x1 v1) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B (Function.update (Function.update B (ι x0) v0) (ι x1) v1)
      (fun _ => True) T := by
  refine of_callInj (Q := Q) hι l hcl ?_ (fun k hk => ?_) ρ
  · rw [Function.update_comp_eq_of_injective _ hι x1 v1,
      Function.update_comp_eq_of_injective B hι x0 v0]
    exact h
  · rw [Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))]

/-- **Three updated stacks** (`RunsIn.callInj_upd3`). -/
theorem callInj_upd3 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : K → List Sym)
    (x0 x1 x2 : L) (v0 v1 v2 : List Sym)
    (h : Runs P (B ∘ ι)
      (Function.update (Function.update (Function.update (B ∘ ι) x0 v0) x1 v1) x2 v2) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B
      (Function.update (Function.update (Function.update B (ι x0) v0) (ι x1) v1) (ι x2) v2)
      (fun _ => True) T := by
  refine of_callInj (Q := Q) hι l hcl ?_ (fun k hk => ?_) ρ
  · rw [Function.update_comp_eq_of_injective _ hι x2 v2,
      Function.update_comp_eq_of_injective _ hι x1 v1,
      Function.update_comp_eq_of_injective B hι x0 v0]
    exact h
  · rw [Function.update_of_ne (Ne.symm (hk x2)), Function.update_of_ne (Ne.symm (hk x1)),
      Function.update_of_ne (Ne.symm (hk x0))]

/-- **Four updated stacks** (`RunsIn.callInj_upd4`). -/
theorem callInj_upd4 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : K → List Sym)
    (x0 x1 x2 x3 : L) (v0 v1 v2 v3 : List Sym)
    (h : Runs P (B ∘ ι) (Function.update (Function.update (Function.update
      (Function.update (B ∘ ι) x0 v0) x1 v1) x2 v2) x3 v3) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B (Function.update (Function.update (Function.update
      (Function.update B (ι x0) v0) (ι x1) v1) (ι x2) v2) (ι x3) v3) (fun _ => True) T := by
  refine of_callInj (Q := Q) hι l hcl ?_ (fun k hk => ?_) ρ
  · rw [Function.update_comp_eq_of_injective _ hι x3 v3,
      Function.update_comp_eq_of_injective _ hι x2 v2,
      Function.update_comp_eq_of_injective _ hι x1 v1,
      Function.update_comp_eq_of_injective B hι x0 v0]
    exact h
  · rw [Function.update_of_ne (Ne.symm (hk x3)), Function.update_of_ne (Ne.symm (hk x2)),
      Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))]

end Generic

/-! ## `BContract` stages (`BLoc m`) inside the extended layout `XLoc m' E` (`callX`) -/

section CallX

variable {m m' : ℕ} {E σ R : Type} [DecidableEq E]

/-- **A `BLoc m` kernel inside `XLoc m' E`, general final stacks.** The big final stacks must agree
with the initial ones on every scratch stack `.inl (.inr j)` and every extra stack `.inr e`
(restored-scratch convention of `BContract`). -/
theorem callX_of_runs (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {B B' : XLoc m' E → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ embX E h) (B' ∘ embX E h) Q T)
    (hscr : ∀ j : Fin m', B' (.inl (.inr j)) = B (.inl (.inr j)))
    (hE : ∀ e : E, B' (.inr e) = B (.inr e)) (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    RunsIn ρ (callX E h l P) B B' (fun _ => True) T :=
  of_runs (runs_callX h l hP hscr hE) (closed_callX E h l hcl) ρ

/-- A `BLoc m` kernel that restores every stack. -/
theorem callX_same (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : XLoc m' E → List Sym)
    (hP : Runs P (B ∘ embX E h) (B ∘ embX E h) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    RunsIn ρ (callX E h l P) B B (fun _ => True) T :=
  callInj_same (embX_injective E h) l hcl B hP ρ

/-- A `BLoc m` kernel updating one named stack `k : LB`. -/
theorem callX_upd (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : XLoc m' E → List Sym) (k : LB) (v : List Sym)
    (hP : Runs P (B ∘ embX E h) (Function.update (B ∘ embX E h) (.inl k) v) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    RunsIn ρ (callX E h l P) B (Function.update B (.inl (.inl k)) v) (fun _ => True) T :=
  callInj_upd (embX_injective E h) l hcl B (.inl k) v hP ρ

/-- A `BLoc m` kernel updating two named stacks. -/
theorem callX_upd2 (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : XLoc m' E → List Sym) (k0 k1 : LB)
    (v0 v1 : List Sym)
    (hP : Runs P (B ∘ embX E h)
      (Function.update (Function.update (B ∘ embX E h) (.inl k0) v0) (.inl k1) v1) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    RunsIn ρ (callX E h l P) B
      (Function.update (Function.update B (.inl (.inl k0)) v0) (.inl (.inl k1)) v1)
      (fun _ => True) T :=
  callInj_upd2 (embX_injective E h) l hcl B (.inl k0) (.inl k1) v0 v1 hP ρ

/-- A `BLoc m` kernel updating three named stacks. -/
theorem callX_upd3 (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Q : R → Prop} {T : ℕ} (B : XLoc m' E → List Sym) (k0 k1 k2 : LB)
    (v0 v1 v2 : List Sym)
    (hP : Runs P (B ∘ embX E h) (Function.update (Function.update
      (Function.update (B ∘ embX E h) (.inl k0) v0) (.inl k1) v1) (.inl k2) v2) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    RunsIn ρ (callX E h l P) B (Function.update (Function.update
      (Function.update B (.inl (.inl k0)) v0) (.inl (.inl k1)) v1) (.inl (.inl k2)) v2)
      (fun _ => True) T :=
  callInj_upd3 (embX_injective E h) l hcl B (.inl k0) (.inl k1) (.inl k2) v0 v1 v2 hP ρ

end CallX

end RunsIn

/-! ## Clean-scratch premises at a call site -/

/-- The `KClean` premise of a clean `KContract` kernel, for the restricted stacks `B ∘ ι`. -/
theorem kClean_comp {K N E : Type} {ι : KLoc N E → K} {B : K → List Sym}
    (h : ∀ e : E, B (ι (.inr e)) = []) : KClean (B ∘ ι) := h

/-- The `EClean` premise of a clean `XContract` kernel, for the restricted stacks `B ∘ ι`. -/
theorem eClean_comp {K E : Type} {m : ℕ} {ι : XLoc m E → K} {B : K → List Sym}
    (h : ∀ e : E, B (ι (.inr e)) = []) : EClean (B ∘ ι) := h

/-! ## Specific contract families -/

namespace RunsIn

section Specific

variable {K σ : Type} [DecidableEq K]

/-- **`W3_addNat` at a call site** (`z += a + b`; `Contracts/Machine/W3.lean`). `hspec` is the body
of `W3_addNat` for the instance `P`, `C`. -/
theorem w3_addNat {m : ℕ} {R : Type} {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a + bitLen b + 1)))
    {ι : Loc 3 m → K} (hι : Function.Injective ι) (l : Lens σ R)
    (a b : ℕ) (rx ry : List Sym) (B : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hX : B (ι (.inl 0)) = natSyms a ++ rx) (hY : B (ι (.inl 1)) = natSyms b ++ ry)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B
      (Function.update B (ι (.inl 2)) (natSyms (a + b) ++ B (ι (.inl 2)))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) :=
  callInj_upd hι l hcl B (.inl 2) _ (hspec a b rx ry (B ∘ ι) hrx hry hX hY) ρ

/-- **`W3_subNat` at a call site** (`z += a - b` for `b ≤ a`; `Contracts/Machine/W3.lean`). -/
theorem w3_subNat {m : ℕ} {R : Type} {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
      b ≤ a → S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a + bitLen b + 1)))
    {ι : Loc 3 m → K} (hι : Function.Injective ι) (l : Lens σ R)
    (a b : ℕ) (rx ry : List Sym) (B : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hba : b ≤ a) (hX : B (ι (.inl 0)) = natSyms a ++ rx) (hY : B (ι (.inl 1)) = natSyms b ++ ry)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B
      (Function.update B (ι (.inl 2)) (natSyms (a - b) ++ B (ι (.inl 2)))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) :=
  callInj_upd hι l hcl B (.inl 2) _ (hspec a b rx ry (B ∘ ι) hrx hry hba hX hY) ρ

/-- **`W5_mulAt Mul` at a call site** (signed `z += a·b` at declared width `w`;
`Contracts/Machine/W5.lean`). -/
theorem w5_mulAt {Mul : ℕ → ℕ} {m : ℕ} {R : Type} {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
        (C * Mul w + C))
    {ι : Loc 3 m → K} (hι : Function.Injective ι) (l : Lens σ R)
    (w : ℕ) (a b : ℤ) (ra rb : List Sym) (B : K → List Sym)
    (hwa : bitLen a.natAbs ≤ w) (hwb : bitLen b.natAbs ≤ w) (hra : TermOK ra) (hrb : TermOK rb)
    (hX : B (ι (.inl 0)) = intSyms a ++ ra) (hY : B (ι (.inl 1)) = intSyms b ++ rb)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B
      (Function.update B (ι (.inl 2)) (intSyms (a * b) ++ B (ι (.inl 2)))) (fun _ => True)
      (C * Mul w + C) :=
  callInj_upd hι l hcl B (.inl 2) _ (hspec w a b ra rb (B ∘ ι) hwa hwb hra hrb hX hY) ρ

/-- **`W6a_divModNat` at a call site** (`q += a / b`, `r += a % b` for `b > 0`;
`Contracts/Machine/W6a.lean`). -/
theorem w6a_divModNat {m : ℕ} {R : Type} {P : Prog (Loc 4 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 m → List Sym), 0 < b → TermOK ra →
      TermOK rb → S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
      Runs P S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
          (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
        (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1)))
    {ι : Loc 4 m → K} (hι : Function.Injective ι) (l : Lens σ R)
    (a b : ℕ) (ra rb : List Sym) (B : K → List Sym) (hb : 0 < b) (hra : TermOK ra)
    (hrb : TermOK rb) (hX : B (ι (.inl 0)) = natSyms a ++ ra)
    (hY : B (ι (.inl 1)) = natSyms b ++ rb) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B
      (Function.update (Function.update B (ι (.inl 2)) (natSyms (a / b) ++ B (ι (.inl 2))))
        (ι (.inl 3)) (natSyms (a % b) ++ B (ι (.inl 3)))) (fun _ => True)
      (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) :=
  callInj_upd2 hι l hcl B (.inl 2) (.inl 3) _ _ (hspec a b ra rb (B ∘ ι) hb hra hrb hX hY) ρ

/-- **`mulBig` at a call site** (`MulBigContract`, `SpecMulBig P C`;
`SubNLogN/Machine/MulBig/Contract.lean`). The caller maps the 76 scratch stacks to stacks that are
empty at the call (`hG`); they are empty again afterwards. Equivalently `SpecMulBig.call` lifted
through the lens. -/
theorem mulBig {R : Type} {P : Prog MBLoc (fun _ => Sym) R} {C : ℕ} (hcl : P.Closed)
    (hspec : SpecMulBig P C) {ι : MBLoc → K} (hι : Function.Injective ι) (l : Lens σ R)
    (x y : ℕ) (rx ry rz : List Sym) (B : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hX : B (ι (.inl 0)) = natSyms x ++ rx) (hY : B (ι (.inl 1)) = natSyms y ++ ry)
    (hZ : B (ι (.inl 2)) = rz) (hG : ∀ w, B (ι (.inr w)) = [])
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B (Function.update B (ι (.inl 2)) (natSyms (x * y) ++ rz))
      (fun _ => True) (C * mulBigBound x y) :=
  callInj_upd hι l hcl B (.inl 2) _ (hspec x y rx ry rz (B ∘ ι) hrx hry hX hY hZ hG) ρ

end Specific

end RunsIn

/-! ## Protected-tail (`FramedRunsIn`) forms

Same adapters for the protected-tail judgment of `Calculus/Frame.lean`. The generic forms pull a
component's local tail class `Gc` back along `ι` (`FramedRunsIn.of_callInj`); the specific forms
start from the **local content** `B₀` (encodings only, tails stripped) and read the tail class off
the contract's hypotheses: `TermOK` tails below the operands, `[]` below `mulBig`'s scratch, and
arbitrary tails on every other stack (the contracts quantify over their content). -/

namespace FramedRunsIn

section GenericFramed

variable {K σ L R : Type} [DecidableEq K] [DecidableEq L]

/-- A framed component that restores every stack, on an injective sub-layout. -/
theorem callInj_same {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Gc : L → List Sym → Prop} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (h : FramedRunsIn Gc [] P (B ∘ ι) (B ∘ ι) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, ι y = k → Gc y tl) ρ (callInj ι l P) B B (fun _ => True) T :=
  FramedRunsIn.of_callInj («GL» := Gc) (Q := Q) hι l hcl h (fun _ _ => rfl) ρ

/-- A framed component updating one stack, on an injective sub-layout. -/
theorem callInj_upd {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Gc : L → List Sym → Prop} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (x : L) (v : List Sym)
    (h : FramedRunsIn Gc [] P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, ι y = k → Gc y tl) ρ (callInj ι l P) B
      (Function.update B (ι x) v) (fun _ => True) T := by
  refine FramedRunsIn.of_callInj («GL» := Gc) (Q := Q) hι l hcl ?_
    (fun k hk => Function.update_of_ne (Ne.symm (hk x)) _ _) ρ
  rw [Function.update_comp_eq_of_injective B hι x v]
  exact h

/-- A framed component updating two stacks, on an injective sub-layout. -/
theorem callInj_upd2 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Gc : L → List Sym → Prop} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (x0 x1 : L) (v0 v1 : List Sym)
    (h : FramedRunsIn Gc [] P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x0 v0) x1 v1) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, ι y = k → Gc y tl) ρ (callInj ι l P) B
      (Function.update (Function.update B (ι x0) v0) (ι x1) v1) (fun _ => True) T := by
  refine FramedRunsIn.of_callInj («GL» := Gc) (Q := Q) hι l hcl ?_ (fun k hk => ?_) ρ
  · rw [Function.update_comp_eq_of_injective _ hι x1 v1,
      Function.update_comp_eq_of_injective B hι x0 v0]
    exact h
  · rw [Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))]

/-- A framed component updating three stacks, on an injective sub-layout. -/
theorem callInj_upd3 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Gc : L → List Sym → Prop} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (x0 x1 x2 : L) (v0 v1 v2 : List Sym)
    (h : FramedRunsIn Gc [] P (B ∘ ι)
      (Function.update (Function.update (Function.update (B ∘ ι) x0 v0) x1 v1) x2 v2) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, ι y = k → Gc y tl) ρ (callInj ι l P) B
      (Function.update (Function.update (Function.update B (ι x0) v0) (ι x1) v1) (ι x2) v2)
      (fun _ => True) T := by
  refine FramedRunsIn.of_callInj («GL» := Gc) (Q := Q) hι l hcl ?_ (fun k hk => ?_) ρ
  · rw [Function.update_comp_eq_of_injective _ hι x2 v2,
      Function.update_comp_eq_of_injective _ hι x1 v1,
      Function.update_comp_eq_of_injective B hι x0 v0]
    exact h
  · rw [Function.update_of_ne (Ne.symm (hk x2)), Function.update_of_ne (Ne.symm (hk x1)),
      Function.update_of_ne (Ne.symm (hk x0))]

/-- A framed component updating four stacks, on an injective sub-layout. -/
theorem callInj_upd4 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {Gc : L → List Sym → Prop} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (x0 x1 x2 x3 : L) (v0 v1 v2 v3 : List Sym)
    (h : FramedRunsIn Gc [] P (B ∘ ι) (Function.update (Function.update (Function.update
      (Function.update (B ∘ ι) x0 v0) x1 v1) x2 v2) x3 v3) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, ι y = k → Gc y tl) ρ (callInj ι l P) B
      (Function.update (Function.update (Function.update (Function.update B (ι x0) v0)
        (ι x1) v1) (ι x2) v2) (ι x3) v3) (fun _ => True) T := by
  refine FramedRunsIn.of_callInj («GL» := Gc) (Q := Q) hι l hcl ?_ (fun k hk => ?_) ρ
  · rw [Function.update_comp_eq_of_injective _ hι x3 v3,
      Function.update_comp_eq_of_injective _ hι x2 v2,
      Function.update_comp_eq_of_injective _ hι x1 v1,
      Function.update_comp_eq_of_injective B hι x0 v0]
    exact h
  · rw [Function.update_of_ne (Ne.symm (hk x3)), Function.update_of_ne (Ne.symm (hk x2)),
      Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))]

end GenericFramed

section CallXFramed

variable {m m' : ℕ} {E σ R : Type} [DecidableEq E]

/-- A framed `BLoc m` kernel (e.g. a `BContract` stage) restoring every stack, inside
`XLoc m' E`. -/
theorem callX_same (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Gc : BLoc m → List Sym → Prop} {Q : R → Prop} {T : ℕ}
    (B : XLoc m' E → List Sym) (hP : FramedRunsIn Gc [] P (B ∘ embX E h) (B ∘ embX E h) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, embX E h y = k → Gc y tl) ρ (callX E h l P) B B
      (fun _ => True) T :=
  callInj_same (embX_injective E h) l hcl B hP ρ

/-- A framed `BLoc m` kernel updating one named stack `k : LB`, inside `XLoc m' E`. -/
theorem callX_upd (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Gc : BLoc m → List Sym → Prop} {Q : R → Prop} {T : ℕ}
    (B : XLoc m' E → List Sym) (k : LB) (v : List Sym)
    (hP : FramedRunsIn Gc [] P (B ∘ embX E h) (Function.update (B ∘ embX E h) (.inl k) v) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, embX E h y = k → Gc y tl) ρ (callX E h l P) B
      (Function.update B (.inl (.inl k)) v) (fun _ => True) T :=
  callInj_upd (embX_injective E h) l hcl B (.inl k) v hP ρ

/-- A framed `BLoc m` kernel updating two named stacks, inside `XLoc m' E`. -/
theorem callX_upd2 (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Gc : BLoc m → List Sym → Prop} {Q : R → Prop} {T : ℕ}
    (B : XLoc m' E → List Sym) (k0 k1 : LB) (v0 v1 : List Sym)
    (hP : FramedRunsIn Gc [] P (B ∘ embX E h)
      (Function.update (Function.update (B ∘ embX E h) (.inl k0) v0) (.inl k1) v1) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, embX E h y = k → Gc y tl) ρ (callX E h l P) B
      (Function.update (Function.update B (.inl (.inl k0)) v0) (.inl (.inl k1)) v1)
      (fun _ => True) T :=
  callInj_upd2 (embX_injective E h) l hcl B (.inl k0) (.inl k1) v0 v1 hP ρ

/-- A framed `BLoc m` kernel updating three named stacks, inside `XLoc m' E`. -/
theorem callX_upd3 (h : m ≤ m') (l : Lens σ R) {P : Prog (BLoc m) (fun _ => Sym) R}
    (hcl : P.Closed) {Gc : BLoc m → List Sym → Prop} {Q : R → Prop} {T : ℕ}
    (B : XLoc m' E → List Sym) (k0 k1 k2 : LB) (v0 v1 v2 : List Sym)
    (hP : FramedRunsIn Gc [] P (B ∘ embX E h) (Function.update (Function.update
      (Function.update (B ∘ embX E h) (.inl k0) v0) (.inl k1) v1) (.inl k2) v2) Q T)
    (ρ : List (Prog (XLoc m' E) (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ y, embX E h y = k → Gc y tl) ρ (callX E h l P) B
      (Function.update (Function.update (Function.update B (.inl (.inl k0)) v0)
        (.inl (.inl k1)) v1) (.inl (.inl k2)) v2) (fun _ => True) T :=
  callInj_upd3 (embX_injective E h) l hcl B (.inl k0) (.inl k1) (.inl k2) v0 v1 v2 hP ρ

end CallXFramed

section SpecificFramed

variable {K σ : Type} [DecidableEq K]

/-- **`W3_addNat`, protected-tail form.** Local content: `B₀` holds `natSyms a`, `natSyms b` on
`ι X`, `ι Y` (no tails); tails: `TermOK` below `ι X`, `ι Y`, arbitrary elsewhere (the old content of
`ι Z` and of the scratch images is part of `B₀` or of the tail). -/
theorem w3_addNat {m : ℕ} {R : Type} {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a + bitLen b + 1)))
    {ι : Loc 3 m → K} (hι : Function.Injective ι) (l : Lens σ R) (a b : ℕ) (B₀ : K → List Sym)
    (hX : B₀ (ι (.inl 0)) = natSyms a) (hY : B₀ (ι (.inl 1)) = natSyms b)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => (k = ι (.inl 0) ∨ k = ι (.inl 1)) → TermOK tl) ρ (callInj ι l P) B₀
      (Function.update B₀ (ι (.inl 2)) (natSyms (a + b) ++ B₀ (ι (.inl 2)))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) := by
  refine FramedRunsIn.of_runs (closed_callInj ι l hcl) (fun τ hτ => ?_) ρ
  simp only [appendTail_update, List.append_assoc]
  exact RunsIn.w3_addNat hcl hspec hι l a b (τ (ι (.inl 0))) (τ (ι (.inl 1))) (appendTail B₀ τ)
    (hτ (ι (.inl 0)) (Or.inl rfl)) (hτ (ι (.inl 1)) (Or.inr rfl)) (by simp [hX]) (by simp [hY]) []

/-- **`W3_subNat`, protected-tail form** (`b ≤ a`); local content and tails as in `w3_addNat`. -/
theorem w3_subNat {m : ℕ} {R : Type} {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
      b ≤ a → S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a + bitLen b + 1)))
    {ι : Loc 3 m → K} (hι : Function.Injective ι) (l : Lens σ R) (a b : ℕ) (B₀ : K → List Sym)
    (hba : b ≤ a) (hX : B₀ (ι (.inl 0)) = natSyms a) (hY : B₀ (ι (.inl 1)) = natSyms b)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => (k = ι (.inl 0) ∨ k = ι (.inl 1)) → TermOK tl) ρ (callInj ι l P) B₀
      (Function.update B₀ (ι (.inl 2)) (natSyms (a - b) ++ B₀ (ι (.inl 2)))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) := by
  refine FramedRunsIn.of_runs (closed_callInj ι l hcl) (fun τ hτ => ?_) ρ
  simp only [appendTail_update, List.append_assoc]
  exact RunsIn.w3_subNat hcl hspec hι l a b (τ (ι (.inl 0))) (τ (ι (.inl 1))) (appendTail B₀ τ)
    (hτ (ι (.inl 0)) (Or.inl rfl)) (hτ (ι (.inl 1)) (Or.inr rfl)) hba (by simp [hX])
    (by simp [hY]) []

/-- **`W5_mulAt Mul`, protected-tail form**; local content `intSyms a`, `intSyms b`. -/
theorem w5_mulAt {Mul : ℕ → ℕ} {m : ℕ} {R : Type} {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
        (C * Mul w + C))
    {ι : Loc 3 m → K} (hι : Function.Injective ι) (l : Lens σ R) (w : ℕ) (a b : ℤ)
    (B₀ : K → List Sym) (hwa : bitLen a.natAbs ≤ w) (hwb : bitLen b.natAbs ≤ w)
    (hX : B₀ (ι (.inl 0)) = intSyms a) (hY : B₀ (ι (.inl 1)) = intSyms b)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => (k = ι (.inl 0) ∨ k = ι (.inl 1)) → TermOK tl) ρ (callInj ι l P) B₀
      (Function.update B₀ (ι (.inl 2)) (intSyms (a * b) ++ B₀ (ι (.inl 2)))) (fun _ => True)
      (C * Mul w + C) := by
  refine FramedRunsIn.of_runs (closed_callInj ι l hcl) (fun τ hτ => ?_) ρ
  simp only [appendTail_update, List.append_assoc]
  exact RunsIn.w5_mulAt hcl hspec hι l w a b (τ (ι (.inl 0))) (τ (ι (.inl 1))) (appendTail B₀ τ)
    hwa hwb (hτ (ι (.inl 0)) (Or.inl rfl)) (hτ (ι (.inl 1)) (Or.inr rfl)) (by simp [hX])
    (by simp [hY]) []

/-- **`W6a_divModNat`, protected-tail form** (`b > 0`); local content `natSyms a`, `natSyms b`. -/
theorem w6a_divModNat {m : ℕ} {R : Type} {P : Prog (Loc 4 m) (fun _ => Sym) R} {C : ℕ}
    (hcl : P.Closed)
    (hspec : ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 m → List Sym), 0 < b → TermOK ra →
      TermOK rb → S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
      Runs P S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
          (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
        (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1)))
    {ι : Loc 4 m → K} (hι : Function.Injective ι) (l : Lens σ R) (a b : ℕ) (B₀ : K → List Sym)
    (hb : 0 < b) (hX : B₀ (ι (.inl 0)) = natSyms a) (hY : B₀ (ι (.inl 1)) = natSyms b)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => (k = ι (.inl 0) ∨ k = ι (.inl 1)) → TermOK tl) ρ (callInj ι l P) B₀
      (Function.update (Function.update B₀ (ι (.inl 2)) (natSyms (a / b) ++ B₀ (ι (.inl 2))))
        (ι (.inl 3)) (natSyms (a % b) ++ B₀ (ι (.inl 3)))) (fun _ => True)
      (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) := by
  refine FramedRunsIn.of_runs (closed_callInj ι l hcl) (fun τ hτ => ?_) ρ
  simp only [appendTail_update, List.append_assoc]
  exact RunsIn.w6a_divModNat hcl hspec hι l a b (τ (ι (.inl 0))) (τ (ι (.inl 1)))
    (appendTail B₀ τ) hb (hτ (ι (.inl 0)) (Or.inl rfl)) (hτ (ι (.inl 1)) (Or.inr rfl))
    (by simp [hX]) (by simp [hY]) []

/-- **`mulBig`, protected-tail form.** Local content: `natSyms x`, `natSyms y` on `ι X`, `ι Y`, and
the 76 scratch images empty; tails: `TermOK` below `ι X`, `ι Y`, **none** below the scratch images,
arbitrary elsewhere (in particular below `ι Z`). -/
theorem mulBig {R : Type} {P : Prog MBLoc (fun _ => Sym) R} {C : ℕ} (hcl : P.Closed)
    (hspec : SpecMulBig P C) {ι : MBLoc → K} (hι : Function.Injective ι) (l : Lens σ R)
    (x y : ℕ) (B₀ : K → List Sym) (hX : B₀ (ι (.inl 0)) = natSyms x)
    (hY : B₀ (ι (.inl 1)) = natSyms y) (hG : ∀ w, B₀ (ι (.inr w)) = [])
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ((k = ι (.inl 0) ∨ k = ι (.inl 1)) → TermOK tl) ∧
        ∀ w, k = ι (.inr w) → tl = []) ρ (callInj ι l P) B₀
      (Function.update B₀ (ι (.inl 2)) (natSyms (x * y) ++ B₀ (ι (.inl 2)))) (fun _ => True)
      (C * mulBigBound x y) := by
  refine FramedRunsIn.of_runs (closed_callInj ι l hcl) (fun τ hτ => ?_) ρ
  simp only [appendTail_update, List.append_assoc]
  exact RunsIn.mulBig hcl hspec hι l x y (τ (ι (.inl 0))) (τ (ι (.inl 1)))
    (appendTail B₀ τ (ι (.inl 2))) (appendTail B₀ τ) ((hτ (ι (.inl 0))).1 (Or.inl rfl))
    ((hτ (ι (.inl 1))).1 (Or.inr rfl)) (by simp [hX]) (by simp [hY]) rfl
    (fun w => by simp [hG w, (hτ (ι (.inr w))).2 w rfl]) []

end SpecificFramed

end FramedRunsIn

#assert_std_axioms RunsIn.of_callInj_reg RunsIn.callInj_same RunsIn.callInj_upd
  RunsIn.callInj_upd2 RunsIn.callInj_upd3 RunsIn.callInj_upd4 RunsIn.callX_of_runs
  RunsIn.callX_same RunsIn.callX_upd RunsIn.callX_upd2 RunsIn.callX_upd3 kClean_comp eClean_comp
  RunsIn.w3_addNat RunsIn.w3_subNat RunsIn.w5_mulAt RunsIn.w6a_divModNat RunsIn.mulBig
  FramedRunsIn.callInj_same FramedRunsIn.callInj_upd FramedRunsIn.callInj_upd2
  FramedRunsIn.callInj_upd3 FramedRunsIn.callInj_upd4 FramedRunsIn.callX_same
  FramedRunsIn.callX_upd FramedRunsIn.callX_upd2 FramedRunsIn.callX_upd3 FramedRunsIn.w3_addNat
  FramedRunsIn.w3_subNat FramedRunsIn.w5_mulAt FramedRunsIn.w6a_divModNat FramedRunsIn.mulBig

end SubNLogN.Machine.Calculus
