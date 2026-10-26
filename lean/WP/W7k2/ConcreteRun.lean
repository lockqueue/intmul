import WP.W7k2.ColRecip
import WP.Inst.W3
import WP.W6a.DivModProg
import WP.F9.Run

/-!
# WP.W7k2.ConcreteRun — the `W7_colRecip` kernel with concrete subroutines, run on the machine

* `crJ`: the instance bundle of `crProg` (ColRecip.lean), built from the concrete W3 instances
  (`WP.Inst.W3`: `copyNat`, `shlConst 1`, `cmpNat`, `shlVar`, `dropNat`) and W6a's long division
  `divModProg subNat.prog` (the `W6a_divModNat_holds` witness).
* `crC := crProg crJ`: the `W7_colRecip_holds` witness program over these subroutines.
* `rows`: `crC` runs under `WP.F9.runTabled` (the framework machine itself, `tabled_eq`,
  `runTabled_sound`). Each row checks every stack: the destination `5` gets
  `intSyms (W7.colRecip H r u2 a c)` on top, and every other stack, including junk on the scratch
  stacks, is restored. It also reports the step count. Both regimes of the column divisor are covered.
-/

namespace WP.W7k2.ConcreteRun

open TMFw TMFw.Contracts WP.W7k2

/-- W6a's long division over the concrete `subNat` (the `W6a_divModNat_holds` witness). -/
def divI : Inst 4 6 Unit :=
  ⟨3, WP.W6a.DReg WP.Inst.subNat.R, fun _ => (), WP.W6a.divModProg WP.Inst.subNat.prog, by decide,
    inferInstance, ⟨(none, false, (none, none, .eq), WP.Inst.subNat.r0)⟩,
    WP.W6a.divModProg_closed _ WP.Inst.subNat.closed⟩

/-- The concrete instance bundle of `crProg`. -/
def crJ : CRInst where
  copy := ⟨WP.Inst.copyNat.m, WP.Inst.copyNat.R, WP.Inst.copyNat.obs, WP.Inst.copyNat.prog,
    by decide, inferInstance, ⟨WP.Inst.copyNat.r0⟩, WP.Inst.copyNat.closed⟩
  shl1 := ⟨WP.Inst.shlConst.m, WP.Inst.shlConst.R, WP.Inst.shlConst.obs, WP.Inst.shlConst.prog 1,
    by decide, inferInstance, ⟨WP.Inst.shlConst.r0⟩, WP.Inst.shlConst.closed 1⟩
  cmp := ⟨WP.Inst.cmpNat.m, WP.Inst.cmpNat.R, WP.Inst.cmpNat.obs, WP.Inst.cmpNat.prog,
    by decide, inferInstance, ⟨WP.Inst.cmpNat.r0⟩, WP.Inst.cmpNat.closed⟩
  shlV := ⟨WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.obs, WP.Inst.shlVar.prog,
    by decide, inferInstance, ⟨WP.Inst.shlVar.r0⟩, WP.Inst.shlVar.closed⟩
  drop := ⟨WP.Inst.dropNat.m, WP.Inst.dropNat.R, WP.Inst.dropNat.obs, WP.Inst.dropNat.prog,
    by decide, inferInstance, ⟨WP.Inst.dropNat.r0⟩, WP.Inst.dropNat.closed⟩
  div := divI

/-- The `W7_colRecip_holds` witness program over `crJ`. -/
def crC : Prog CRL (fun _ => Sym) crJ.Reg := crProg crJ

theorem crC_closed : crC.Closed := crProg_closed crJ

/-- Initial registers. -/
def crR0 : crJ.Reg :=
  (WP.Inst.copyNat.r0, WP.Inst.shlConst.r0, WP.Inst.cmpNat.r0, WP.Inst.shlVar.r0,
    WP.Inst.dropNat.r0, (none, false, (none, none, .eq), WP.Inst.subNat.r0))

/-- All stacks of the kernel. -/
def keys : List CRL := (List.finRange 6).map Sum.inl ++ (List.finRange 6).map Sum.inr

theorem keys_complete : ∀ k : CRL, k ∈ keys := by
  intro k
  rcases k with i | i <;> simp [keys]

/-- Junk tails; they start with a tag, so input rests are `TermOK`. -/
def junk : List Sym := [.tag 9, .bit true]

/-- Initial stacks for `(H, r, u2, a, c)`; junk on the destination and the scratch stacks. -/
def st0 (H r u2 : ℕ) (a c : ℤ) : CRL → List Sym := fun k =>
  if k = .inl 0 then natSyms H ++ junk
  else if k = .inl 1 then natSyms r ++ junk
  else if k = .inl 2 then natSyms u2 ++ junk
  else if k = .inl 3 then intSyms a ++ junk
  else if k = .inl 4 then intSyms c ++ junk
  else junk

/-- One run: `(every stack as the contract says, steps)`. -/
def row (H r u2 : ℕ) (a c : ℤ) : Bool × ℕ :=
  let S := st0 H r u2 a c
  let E := Function.update S (.inl 5) (intSyms (W7.colRecip H r u2 a c) ++ S (.inl 5))
  match WP.F9.runTabled crC crR0 keys ⟨crR0, S⟩ 1000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- `2·u2 ≤ r` (divisor `a`) twice, `2·u2 > r` (divisor `c`) once; a negative partner entry. -/
def rows : List (Bool × ℕ) :=
  [row 10 4 1 3 5, row 7 4 3 2 6, row 5 2 0 7 (-4)]

-- `(stacks ok, steps)` for each row.
#eval rows
#guard rows.all (·.1)

#assert_std_axioms crC_closed keys_complete

end WP.W7k2.ConcreteRun
