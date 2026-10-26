/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadLayout
import SubNLogN.Machine.Calculus.Adapters

/-!
# K5 spreading: the line-step contract (`Bridge/SpreadLineStmt.lean`)

**Scope (honest summary).** Statements only (no proofs). The contract of one **line step** of the
spreading kernel (`SpreadLinesStmt`, `Contracts/Bridge.lean`), frozen for the stage loop
(`spreadLines_of`): from a line `X` (`t` one-coefficient records, first on top of `arr`) and the
packed filter parts of its tap record `F` (`W` entries; stacks `F k` hold the parts of `F.reverse`),
with the rulers of the stage and empty line scratch (`LineScratch`), the program consumes the line
from `arr` and pushes the line's outputs `lineOut q t W a₀ X F` (reversed symbol order) onto `Out`;
every other stack is unchanged.

* `lineCost s t W`: `t + W` records of `O(s)` symbols, `≤ t / W + 2` blocks of `W` slots, each
  with `O(1)` `mulBig` calls on operands of `≤ 2 (W s + 1) + 1` bits (`mulW`, as in `spreadCost`).
* `SpreadLineSpec P C`: the line-step specification of a program `P` with constant `C`.
* `SpreadLineStmt`: given the packer and slot-pass sub-contracts (`PackDataStmt`, `SlotPassStmt`,
  `SpreadIface.lean`), for every register type with lenses to the AR registers and to `mulBig`'s
  registers and every closed `mulBig` program meeting `SpecMulBig`, some closed program meets
  `SpreadLineSpec` with some constant.

All declarations live in `SubNLogN.Machine.Bridge.SpreadAux`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith SubNLogN.Machine.Calculus
  Computability

/-- Cost unit of one line step (see the module docstring). -/
def lineCost (s t W : ℕ) : ℕ :=
  (t + W) * (s + 1) + (t / W + 2) * (W * (s + 1) + mulW (2 * (W * s + 1) + 1))

/-- The scratch stacks used by one line step; they are empty before and after it. -/
def LineScratch (x : SpS) : Prop :=
  (∃ j, x = .Zr j) ∨ (∃ j, x = .Zi j) ∨ (∃ k, x = .D k) ∨ (∃ j, x = .tmp j) ∨
    (∃ g, x = .mb g) ∨ x = .Es ∨ x = .Tre ∨ x = .Tim ∨ x = .Q ∨ x = .M ∨ x = .Vre ∨ x = .Vim ∨
    x = .NTre ∨ x = .NTim ∨ x = .P1 ∨ x = .P2 ∨ x = .T2 ∨ x = .T4 ∨ x = .T5 ∨ x = .Bf ∨
    x = .FA ∨ x = .FB ∨ x = .X 1 ∨ x = .X 2 ∨ x = .X 5 ∨ x = .X 6

/-- **Line-step specification** of a program `P` with constant `C`. Data: slot width `s`, widths
`wI` (data) and `wT` (taps), precision `q`, line length `t`, window `W`, rotation `a₀`, the line
`X` and the tap record `F`. Rulers: the stage rulers `ru r` and the product rulers `pr k`
(`recw = 2 wI + 1` symbols per record). -/
def SpreadLineSpec {Esu σ : Type} [DecidableEq Esu] (P : Prog (SK Esu) (fun _ => Sym) σ)
    (C : ℕ) : Prop :=
  ∀ (s wI wT q t W a0 : ℕ) (X F : List CInt) (rarr : List Sym) (S : SK Esu → List Sym),
    X.length = t → F.length = W → 1 ≤ W → W ≤ t → a0 ≤ t → 1 ≤ wI → wI ≤ s → q ≤ s →
    (∀ x ∈ X, FitsTwos wI x.1 ∧ FitsTwos wI x.2) →
    (∀ y ∈ F, FitsTwos wT y.1 ∧ FitsTwos wT y.2) →
    (W : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) < 2 ^ (s - 1) →
    W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s →
    (∀ y ∈ lineOut q t W a0 X F, FitsTwos wI y.1 ∧ FitsTwos wI y.2) →
    S (kW .arr) = carrSyms wI (X.map fun x => [x]) ++ rarr →
    (∀ k, S (sp (.F k)) = natSyms (pack s (F.reverse.map (cpart wT k)))) →
    S (sp (.ru .s)) = List.replicate s .mark → S (sp (.ru .sq)) = List.replicate q .mark →
    S (sp (.ru .h)) = List.replicate (s - q) .mark →
    S (sp (.ru .wI)) = List.replicate wI .mark →
    S (sp (.ru .Wm1)) = List.replicate (W - 1) .mark →
    S (sp (.ru .W)) = List.replicate W .mark →
    S (sp (.ru .wI1)) = List.replicate (wI - 1) .mark →
    S (sp (.ru .sWI)) = List.replicate (s - wI) .mark →
    S (sp (.pr 0)) = List.replicate ((W - 1) * (2 * wI + 1)) .mark →
    S (sp (.pr 1)) = List.replicate (t * (2 * wI + 1)) .mark →
    S (sp (.pr 2)) = List.replicate (a0 * (2 * wI + 1)) .mark →
    S (sp (.pr 3)) = List.replicate ((t - a0) * (2 * wI + 1)) .mark →
    S (sp (.pr 4)) = List.replicate ((W - 1) * s) .mark →
    (∀ x, LineScratch x → S (sp x) = []) →
    Runs P S (Function.update (Function.update S (kW .arr) rarr) (sp .Out)
        ((carrSyms wI ((lineOut q t W a0 X F).map fun y => [y])).reverse ++ S (sp .Out)))
      (fun _ => True) (C * lineCost s t W)

/-- **[SUB-CONTRACT] The line step** of the spreading kernel. -/
def SpreadLineStmt : Prop :=
  PackDataStmt → SlotPassStmt →
  ∀ {Esu σ Rm : Type} [DecidableEq Esu] (_lA : Lens σ AReg) (_lM : Lens σ Rm)
    (Pm : Prog MBLoc (fun _ => Sym) Rm) (Cm : ℕ), Pm.Closed → SpecMulBig Pm Cm →
    ∃ P : Prog (SK Esu) (fun _ => Sym) σ, P.Closed ∧ ∃ C : ℕ, SpreadLineSpec P C

end SubNLogN.Machine.Bridge.SpreadAux
