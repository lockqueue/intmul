/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadIface
import SubNLogN.Machine.Bridge.SpreadParts
import SubNLogN.Machine.MulBig.Contract

/-!
# K5 spreading: stack layout and role maps (`Bridge/SpreadLayout.lean`)

The private scratch stacks `SpS` of the spreading kernel, the stack type
`SK Esu = KLoc BrK (SpS ⊕ Esu)` (`Esu`: the setup kernel's scratch), and the injective role maps
through which the sub-programs (`SpreadIface.lean` packers and slot pass, the field processor
`fieldProg`, `mulBig`) are embedded. Definitions and injectivity proofs only.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

/-- Private scratch stacks of the spreading kernel. -/
inductive SpS
  /-- parameter rulers (built by the setup kernel) -/
  | ru (r : RulerId)
  /-- product rulers: `(W-1)·recw`, `t·recw`, `a₀·recw`, `(t-a₀)·recw`, `(W-1)·s` -/
  | pr (k : Fin 5)
  /-- packed data parts -/
  | D (k : Fin 4)
  /-- packed filter parts -/
  | F (k : Fin 4)
  /-- the eight partial products of the real component (slot-pass sources `0-7`) -/
  | Zr (j : Fin 8)
  /-- the eight partial products of the imaginary component -/
  | Zi (j : Fin 8)
  /-- record count of a block -/
  | M
  /-- packer scratch -/
  | tmp (j : Fin 8)
  /-- `mulBig` scratch -/
  | mb (g : WP.Top.GW)
  | Es | T2 | T4 | T5 | Q | P1 | P2 | TT | TR | Out
  | Tre | Tim | NTre | NTim | Vre | Vim | Bf | FA | FB
  /-- walk temporaries -/
  | X (j : Fin 8)
  deriving DecidableEq, Fintype

/-- The stack type of the spreading kernel: interface stacks and scratch (`Esu`: the setup
kernel's private scratch). -/
abbrev SK (Esu : Type) : Type := KLoc BrK (SpS ⊕ Esu)

/-- A private scratch stack. -/
abbrev sp {Esu : Type} (x : SpS) : SK Esu := .inr (.inl x)

variable {Esu : Type}

/-- Role map of the data packer. -/
def ιPD : PackRole → SK Esu
  | .src => sp .Es
  | .out k => sp (.D k)
  | .M => sp .M
  | .RW => sp (.ru .W)
  | .Rlo => sp (.ru .wI1)
  | .Rpad => sp (.ru .sWI)
  | .tmp j => sp (.tmp j)

/-- Role map of the filter packer. -/
def ιPF : FiltRole → SK Esu
  | .src => kN .tapTab
  | .out k => sp (.F k)
  | .tr => sp .TR
  | .Rlo => sp (.ru .wT1)
  | .Rpad => sp (.ru .sWT)
  | .tmp j => sp (.tmp j)

/-- Role map of a slot pass: sources `zs 0, …, zs 7` and the tail `tl`, output `o`. -/
def ιSP (zs : Fin 8 → SpS) (tl o : SpS) : SlotRole → SK Esu
  | .src j => if h : (j : ℕ) < 8 then sp (zs ⟨j, h⟩) else sp tl
  | .out => sp o
  | .R => sp (.ru .s)
  | .X => sp (.X 5)

/-- Role map of the field processor writing to `dst`. -/
def ιFP (dst : SK Esu) : FR → SK Esu
  | .src => sp .Bf
  | .T => dst
  | .Rs => sp (.ru .sq)
  | .Rh => sp (.ru .h)
  | .R2 => sp (.ru .wI)
  | .X => sp (.X 6)
  | .A => sp .FA
  | .B => sp .FB

/-- Role map of the `mulBig` call `z := D a · F b`. -/
def ιMB (a b : Fin 4) (z : SpS) : MBLoc → SK Esu :=
  Sum.elim (fun i => sp (![SpS.D a, SpS.F b, z] i)) (fun g => sp (.mb g))

theorem sp_injective : Function.Injective (sp (Esu := Esu)) := by
  intro a b h
  simpa using h

theorem ιPD_injective : Function.Injective (ιPD (Esu := Esu)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ιPD]

theorem ιPF_injective : Function.Injective (ιPF (Esu := Esu)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ιPF]

theorem ιSP_injective {zs : Fin 8 → SpS} (hz : Function.Injective zs) {tl o : SpS}
    (htl : ∀ j, tl ≠ zs j) (ho : ∀ j, o ≠ zs j) (hto : tl ≠ o) (htR : tl ≠ .ru .s)
    (hoR : o ≠ .ru .s) (htX : tl ≠ .X 5) (hoX : o ≠ .X 5) (hzR : ∀ j, zs j ≠ .ru .s)
    (hzX : ∀ j, zs j ≠ .X 5) :
    Function.Injective (ιSP (Esu := Esu) zs tl o) := by
  intro a b h
  cases a with
  | src j =>
    cases b with
    | src j' =>
      simp only [ιSP] at h
      split_ifs at h with h1 h2 h2
      · have := hz (sp_injective h)
        simp only [Fin.mk.injEq] at this
        exact congrArg _ (Fin.ext this)
      · exact absurd (sp_injective h).symm (htl _)
      · exact absurd (sp_injective h) (htl _)
      · exact congrArg _ (Fin.ext (by omega))
    | out =>
      simp only [ιSP] at h; split_ifs at h
      · exact absurd (sp_injective h).symm (ho _)
      · exact absurd (sp_injective h) hto
    | R =>
      simp only [ιSP] at h; split_ifs at h
      · exact absurd (sp_injective h) (hzR _)
      · exact absurd (sp_injective h) htR
    | X =>
      simp only [ιSP] at h; split_ifs at h
      · exact absurd (sp_injective h) (hzX _)
      · exact absurd (sp_injective h) htX
  | out =>
    cases b with
    | src j' =>
      simp only [ιSP] at h; split_ifs at h
      · exact absurd (sp_injective h) (ho _)
      · exact absurd (sp_injective h).symm hto
    | out => rfl
    | R => exact absurd (sp_injective h) hoR
    | X => exact absurd (sp_injective h) hoX
  | R =>
    cases b with
    | src j' =>
      simp only [ιSP] at h; split_ifs at h
      · exact absurd (sp_injective h).symm (hzR _)
      · exact absurd (sp_injective h).symm htR
    | out => exact absurd (sp_injective h).symm hoR
    | R => rfl
    | X => simp [ιSP] at h
  | X =>
    cases b with
    | src j' =>
      simp only [ιSP] at h; split_ifs at h
      · exact absurd (sp_injective h).symm (hzX _)
      · exact absurd (sp_injective h).symm htX
    | out => exact absurd (sp_injective h).symm hoX
    | R => simp [ιSP] at h
    | X => rfl

theorem ιFP_injective {dst : SK Esu} (h1 : dst ≠ sp .Bf) (h2 : dst ≠ sp (.ru .sq))
    (h3 : dst ≠ sp (.ru .h)) (h4 : dst ≠ sp (.ru .wI)) (h5 : dst ≠ sp (.X 6))
    (h6 : dst ≠ sp .FA) (h7 : dst ≠ sp .FB) : Function.Injective (ιFP dst) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ιFP]

theorem ιMB_injective (a b : Fin 4) {z : SpS} (hD : ∀ k, z ≠ .D k) (hF : ∀ k, z ≠ .F k)
    (hm : ∀ g, z ≠ .mb g) : Function.Injective (ιMB (Esu := Esu) a b z) := by
  have h3 : Function.Injective (![SpS.D a, SpS.F b, z]) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h <;>
      first
        | rfl
        | exact absurd h.symm (hD _)
        | exact absurd h (hD _)
        | exact absurd h.symm (hF _)
        | exact absurd h (hF _)
  refine Function.Injective.sumElim (sp_injective.comp h3) (fun g g' h => by simpa using h) ?_
  intro i g h
  have h' := sp_injective h
  fin_cases i <;> simp at h' <;> exact hm g h'

end SubNLogN.Machine.Bridge.SpreadAux
