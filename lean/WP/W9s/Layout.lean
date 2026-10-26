import WP.W9s.Moves
import WP.W9s.SpecDefs

/-!
# WP.W9s.Layout — host stacks, the kit of subroutines, registers

The machine runs on the W7k2 host `Host = Loc 2 20`:
* `sA = .inl 0`: the data (the contract's `W0`);
* `sC0 = .inl 1`: the level header (the contract's `C0`, read only);
* 20 scratch stacks (`.inr i`). Every scratch stack is used under a guard and restored.

The subroutines are explicit parameters bundled in `Kit`:
* `Ia`, `Is`: instances of `W3_addInt` and `W3_subInt`;
* `Hp k`: in-place rounding halving on host stack `k` (`HalveSpec`; `WP.W9s.Halve` provides it from
  `W3_incNat`).
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- The host. -/
abbrev Host : Type := Loc 2 20

abbrev sA : Host := .inl 0
abbrev sC0 : Host := .inl 1
abbrev sE : Host := .inr 0
abbrev sO : Host := .inr 1
abbrev sT : Host := .inr 2
abbrev sT3 : Host := .inr 3
abbrev sD : Host := .inr 4
abbrev sG : Host := .inr 5
abbrev sOP : Host := .inr 6
abbrev sOM : Host := .inr 7
abbrev sEP : Host := .inr 8
abbrev sTX : Host := .inr 10
abbrev sTY : Host := .inr 11
abbrev sV : Host := .inr 12
abbrev sV' : Host := .inr 13
abbrev sDS : Host := .inr 14
abbrev sDS' : Host := .inr 15
abbrev sUR : Host := .inr 16
abbrev sUR' : Host := .inr 17
abbrev sTC : Host := .inr 18
abbrev sT2 : Host := .inr 19

/-- Body of `W3_addInt` (`op = (· + ·)`) or `W3_subInt` (`op = (· - ·)`) for one instance. -/
def SpecOp (op : ℤ → ℤ → ℤ) (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (op a b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- The subroutines. -/
structure Kit where
  Ia : Inst 3 4 Unit
  Is : Inst 3 4 Unit
  Rh : Type
  Hp : Host → Prog Host (fun _ => Sym) Rh

/-- Specification of the halving subroutine. -/
def HalveSpec {Rh : Type} (Hp : Host → Prog Host (fun _ => Sym) Rh) (C : ℕ) : Prop :=
  (∀ k, (Hp k).Closed) ∧
    ∀ (k : Host) (B : Host → List Sym) (x : ℤ) (rest : List Sym), TermOK rest →
      B k = intSyms x ++ rest →
      HT [] B (Hp k) (Function.update B k (intSyms (divRoundPow2 x 1) ++ rest))
        (C * (bitLen x.natAbs + 1))

/-- The kit meets its specifications with constants `CA`, `CS`, `CH`. -/
structure KitOK (K : Kit) (CA CS CH : ℕ) : Prop where
  add : SpecOp (· + ·) K.Ia CA
  sub : SpecOp (· - ·) K.Is CS
  halve : HalveSpec K.Hp CH

/-- Registers: a symbol register, then the registers of the subroutines. -/
abbrev Kit.R (K : Kit) : Type := Option Sym × K.Ia.R × K.Is.R × K.Rh

def lS (K : Kit) : Lens K.R (Option Sym) := Lens.fst _ _
def la (K : Kit) : Lens K.R K.Ia.R := WP.W9comp.lsnd (Lens.fst _ _)
def ls (K : Kit) : Lens K.R K.Is.R := WP.W9comp.lsnd (WP.W9comp.lsnd (Lens.fst _ _))
def lh (K : Kit) : Lens K.R K.Rh := WP.W9comp.lsnd (WP.W9comp.lsnd (Lens.snd _ _))

/-- A program of the machine. -/
abbrev MProg (K : Kit) : Type := Prog Host (fun _ => Sym) K.R

/-! ## Calls -/

/-- `z += x ± y` on `(sA, sG, sEP)`. -/
def opC (K : Kit) : Bool → MProg K
  | false => callI K.Ia [sA, sG, sEP] sA (la K)
  | true => callI K.Is [sA, sG, sEP] sA (ls K)

/-- Halve the number on top of `sEP`. -/
def halveC (K : Kit) : MProg K := (K.Hp sEP).liftRegs (lh K)

theorem opC_closed (K : Kit) (neg : Bool) : (opC K neg).Closed := by
  cases neg
  · exact callI_closed _ _ _ _
  · exact callI_closed _ _ _ _

theorem halveC_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) : (halveC K).Closed :=
  WP.W9comp.closed_liftRegs _ (hH.1 sEP)

/-- The integer operation of a butterfly coordinate. -/
def opZ : Bool → ℤ → ℤ → ℤ
  | false => (· + ·)
  | true => (· - ·)

theorem HT.opC {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (neg : Bool)
    (B : Host → List Sym) (x y : ℤ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B sA = intSyms x ++ rx) (hy : B sG = intSyms y ++ ry) (ρ : List (MProg K)) :
    HT ρ B (opC K neg) (Function.update B sEP (intSyms (opZ neg x y) ++ B sEP))
      ((if neg then CS else CA) * (bitLen x.natAbs + bitLen y.natAbs + 1)) := by
  cases neg
  · exact HT.callI_upd K.Ia [sA, sG, sEP] sA (by decide) rfl (by decide) (la K) B (.inl 2) _
      (hK.add x y rx ry _ hrx hry hx hy) ρ
  · exact HT.callI_upd K.Is [sA, sG, sEP] sA (by decide) rfl (by decide) (ls K) B (.inl 2) _
      (hK.sub x y rx ry _ hrx hry hx hy) ρ

theorem HT.halveC {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (B : Host → List Sym) (x : ℤ)
    (rest : List Sym) (hrest : TermOK rest) (hB : B sEP = intSyms x ++ rest) (ρ : List (MProg K)) :
    HT ρ B (halveC K) (Function.update B sEP (intSyms (divRoundPow2 x 1) ++ rest))
      (CH * (bitLen x.natAbs + 1)) :=
  HT.lift (lh K) (hK.halve.1 sEP) (hK.halve.2 sEP B x rest hrest hB) ρ

#assert_std_axioms opC_closed halveC_closed HT.opC HT.halveC

end WP.W9s
