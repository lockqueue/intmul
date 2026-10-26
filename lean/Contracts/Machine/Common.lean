import IntMulTM.Framework.Layout
import IntMulTM.Framework.Bits
import IntMulTM.Framework.AxiomGuard

/-!
# Contracts.Machine.Common — shared vocabulary of the machine-WP contracts (W3, W4, W5, W6a)

## Shape of a machine contract (`MContract`)

A contract `Wk_name : Prop` asserts the existence of a **closed** program
`P : Prog (Loc n m) (fun _ => Sym) R` over **local stacks** `Loc n m = Fin n ⊕ Fin m`:
* `.inl i` (`i < n`) are the contract's *named* stacks (operands, results, parameters);
* `.inr j` (`j < m`) are private *scratch* stacks, `m ≤ maxScratch`, with **arbitrary initial
  content that must be restored**;
* `R` is a private, finite, nonempty register type (`Finite R ∧ Nonempty R`; nonemptiness rules out
  vacuous triples), arbitrary on entry; results kept in registers are exposed only through an
  explicit observation `obs : R → O`;
* `P.Closed` (no free `recur`), so `P` can be used inside any procedure (`Eval.env_irrel`);
* one cost constant `C`, chosen **before** the compile-time parameter and all data.

The specification is stated with `Runs P S S' Q T`: from **every** state whose stacks are `S`
(any register value) `P` reaches, within `T` steps, a state whose stacks are **exactly** `S'` and
whose register satisfies `Q`. Since `S'` is given as a `Function.update` of `S`, every stack the
contract does not mention, in particular every scratch stack, is unchanged.

**Frame polymorphism.** The integrator embeds `P` into the global work stacks with an injective
`ι : Loc n m → W` (`Prog.mapStk`) and into the global registers with a `Lens` (`Prog.liftRegs`);
`Runs.embed` (below) and `Triple.liftRegs` give the embedded triple, with every stack outside the
image of `ι` and every register component outside the lens unchanged.

## Numeric conventions (all machine contracts)

* **Unsigned** `n : ℕ` on a stack: `natSyms n ++ rest` with `natSyms n = (encodeNat n).map Sym.bit`
  (LSB on top, canonical: no high zeros, `0 ↦ []`) and `TermOK rest` (the stack bottom or a non-bit
  symbol follows). Size measure: `bitLen n = (encodeNat n).length` (`= Nat.size n`).
* **Signed** `z : ℤ` (sign-magnitude): `intSyms z ++ rest`, `intSyms z = sgnSym z :: natSyms |z|`,
  sign symbol **on top** (`Sym.neg` iff `z < 0`, else `Sym.pos`; zero is `[pos]`, never `[neg]`),
  then the magnitude LSB-first, then a terminator (`TermOK rest`). This matches the record format
  `sgn·bits(re)·sgn·bits(im)·⊣` of complex records and the pair-entry format of `Contracts.W9.Common`.
* **Results** are pushed on top of the destination's previous content; operands are restored
  (non-destructive) unless the contract says *in place*.
-/

namespace TMFw.Contracts

open Computability

/-! ## Encodings -/

/-- Unsigned number: canonical LSB-first bits, LSB on top. -/
def natSyms (n : ℕ) : List Sym := (encodeNat n).map Sym.bit

/-- Bit length (`= Nat.size n`); the size measure of all cost bounds. -/
def bitLen (n : ℕ) : ℕ := (encodeNat n).length

/-- Sign symbol: `neg` iff negative. -/
def sgnSym (z : ℤ) : Sym := if z < 0 then .neg else .pos

/-- Signed number, sign-magnitude, sign on top. -/
def intSyms (z : ℤ) : List Sym := sgnSym z :: natSyms z.natAbs

/-- Three-way comparison on `ℤ` (`ordOf` on `ℕ` is `Lib.ordOf`). -/
def cmpZ (a b : ℤ) : Ordering := if a < b then .lt else if a = b then .eq else .gt

theorem length_natSyms (n : ℕ) : (natSyms n).length = bitLen n := by
  simp [natSyms, bitLen]

theorem intSyms_natCast (n : ℕ) : intSyms (n : ℤ) = Sym.pos :: natSyms n := by
  simp [intSyms, sgnSym]

/-! ## Contract shape -/

/-- Local stacks of a component: `n` named stacks `.inl i`, `m` scratch stacks `.inr j`. -/
abbrev Loc (n m : ℕ) := Fin n ⊕ Fin m

/-- From every state with stacks `S` (any register), reach stacks exactly `S'` with register
property `Q`, within `T` steps. -/
def Runs {K R : Type} [DecidableEq K] (P : Prog K (fun _ => Sym) R) (S S' : K → List Sym)
    (Q : R → Prop) (T : ℕ) : Prop :=
  Triple [] (fun s => s.stk = S) P (fun s => s.stk = S' ∧ Q s.var) T

/-- **Shape of every machine contract.** One cost constant `C`; for each compile-time parameter
`p : Par`, a closed program over `n` named and `m ≤ maxScratch` scratch stacks with a finite
nonempty register type `R` and an observation `obs : R → O`, satisfying `spec p m R C obs P`. -/
def MContract (Par : Type) (n maxScratch : ℕ) (O : Type)
    (spec : Par → (m : ℕ) → (R : Type) → ℕ → (R → O) → Prog (Loc n m) (fun _ => Sym) R → Prop) :
    Prop :=
  ∃ C : ℕ, ∀ p : Par, ∃ (m : ℕ) (R : Type) (obs : R → O) (P : Prog (Loc n m) (fun _ => Sym) R),
    m ≤ maxScratch ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ spec p m R C obs P

/-! ## Using and proving contracts -/

/-- Prove `Runs` from an exact evaluation for every register value. -/
theorem Runs.of_eval {K R : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) R}
    {S S' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (h : ∀ v : R, ∃ v' t, Eval [] P ⟨v, S⟩ ⟨v', S'⟩ t ∧ Q v' ∧ t ≤ T) : Runs P S S' Q T := by
  intro s hs
  obtain ⟨v', t, e, hq, ht⟩ := h s.var
  refine ⟨⟨v', S'⟩, t, ?_, ⟨rfl, hq⟩, ht⟩
  obtain ⟨var, stk⟩ := s
  change stk = S at hs
  subst hs
  exact e

/-- **Frame polymorphism.** A local contract transports along any injective stack embedding
`ι : L → K`: the embedded program maps big stacks `B` (agreeing with `S` on the image of `ι`) to
big stacks agreeing with `S'` on the image and **unchanged outside it**. -/
theorem Runs.embed {L K R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) {P : Prog L (fun _ => Sym) R} {S S' : L → List Sym}
    {Q : R → Prop} {T : ℕ} (h : Runs P S S' Q T) (B : K → List Sym) (hB : ∀ l, B (ι l) = S l) :
    Triple [] (fun s => s.stk = B) (P.mapStk ι)
      (fun s => (∀ l, s.stk (ι l) = S' l) ∧ (∀ k, (∀ l, ι l ≠ k) → s.stk k = B k) ∧ Q s.var)
      T := by
  have h2 := Triple.mapStk hι h (fun s => ∀ k, (∀ l, ι l ≠ k) → s.stk k = B k)
    (fun s s' hs hfr k hk => (hfr k hk).trans (hs k hk))
  intro s hs
  have hpre : (fun s : St K (fun _ => Sym) R =>
      (s.comap ι).stk = S ∧ ∀ k, (∀ l, ι l ≠ k) → s.stk k = B k) s := by
    refine ⟨?_, fun k _ => by rw [hs]⟩
    funext l
    show s.stk (ι l) = S l
    rw [hs, hB]
  obtain ⟨s', t, e, ⟨⟨h1, hq⟩, hfr⟩, ht⟩ := h2 s hpre
  exact ⟨s', t, e, ⟨fun l => congrFun h1 l, hfr, hq⟩, ht⟩

/-- A contract instance can be used inside any procedure environment. -/
theorem Runs.env {K R : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) R}
    {S S' : K → List Sym} {Q : R → Prop} {T : ℕ} (h : Runs P S S' Q T) (hc : P.Closed)
    (ρ : List (Prog K (fun _ => Sym) R)) :
    Triple ρ (fun s => s.stk = S) P (fun s => s.stk = S' ∧ Q s.var) T :=
  Triple.env_irrel h hc ρ

#assert_std_axioms Runs.of_eval Runs.embed Runs.env length_natSyms intSyms_natCast

end TMFw.Contracts
