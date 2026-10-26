/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5XorProg

/-!
# `SubNLogN.Machine.AppC.C5Xor`: the XOR gate on two aligned role arrays (Proposition A.7 leaf L3)

Paper: Proposition A.7 (`prop:transfer11`) (the bit-network gates over
`𝔽₂`); contract `C5XorStmt` (`AppC/C5Leaves.lean`). Program design in `C5XorProg`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

**Scope.** Proved (no `sorry`): `c5Xor_holds : C5XorStmt`, in
`SubNLogN.Machine.C5`; helpers in `SubNLogN.Machine.C5.XorAux`. Of the contract's hypotheses
the proof uses all except `BlkTerm rb` (the source `b` is consumed and rebuilt from the copy
buffer, so its tail is never inspected).
-/

namespace SubNLogN.Machine.C5.XorAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1.AddSubAux

theorem xMain_eval (w : ℕ) (a b : List (List Bool)) (ra rb : List Sym) (S : XK → List Sym)
    (hlen : a.length = b.length) (ha : ∀ q ∈ a, q.length = w) (hb : ∀ q ∈ b, q.length = w)
    (hra : BlkTerm ra) (hA : S xkA = arrSyms a ++ ra) (hB : S xkB = arrSyms b ++ rb)
    (o p : Option Sym) :
    ∃ (v' : XoReg) (t : ℕ), t ≤ 10 * (vol a + vol b + 1) ∧
      Eval [] xMain ⟨(o, p), S⟩ ⟨v', Function.update S xkA (arrSyms (xorArr a b) ++ ra)⟩ t := by
  have e1 := xpc_eval xkT Sym.mark (o, p) S
  set S1 := Function.update S xkT (Sym.mark :: S xkT) with hS1
  have e2 := xpc_eval xkT2 Sym.mark (o, p) S1
  have h1T2 : S1 xkT2 = S xkT2 := by simp [hS1]
  rw [h1T2] at e2
  set S2 := Function.update S1 xkT2 (Sym.mark :: S xkT2) with hS2
  have e3 := xpkO_eval xkA (o, p) S2
  obtain ⟨v4, t4, ht4, e4⟩ := recLoopX_eval w ra rb hra a b (S2 xkA).head? p S2 hlen ha hb
    (by simp [hS2, hS1, hA]) (by simp [hS2, hS1, hB]) rfl
  have h2T : S2 xkT = Sym.mark :: S xkT := by simp [hS2, hS1]
  have h2T2 : S2 xkT2 = Sym.mark :: S xkT2 := by simp [hS2]
  rw [h2T, h2T2] at e4
  set out := arrSyms (xorArr a b) with hout
  set S4 := Function.update (Function.update (Function.update (Function.update S2 xkA ra)
    xkB rb) xkT (out.reverse ++ Sym.mark :: S xkT))
    xkT2 ((arrSyms b).reverse ++ Sym.mark :: S xkT2) with hS4
  have hmO : Sym.mark ∉ out.reverse := by
    rw [List.mem_reverse, hout]
    exact mark_not_mem_arrSyms _
  have hmB : Sym.mark ∉ (arrSyms b).reverse := by
    rw [List.mem_reverse]
    exact mark_not_mem_arrSyms _
  have e5 := Eval.liftRegs lensXo (WP.W9comp.rewindTo_eval (by decide : xkT ≠ xkA) Sym.mark
    (lensXo.get v4) out.reverse (S xkT) S4 hmO (by simp [hS4])) v4 rfl
  have h4A : S4 xkA = ra := by simp [hS4]
  rw [h4A, List.reverse_reverse] at e5
  set S5 := Function.update (Function.update S4 xkT (S xkT)) xkA (out ++ ra) with hS5
  have e6 := Eval.liftRegs lensXo (WP.W9comp.rewindTo_eval (by decide : xkT2 ≠ xkB) Sym.mark
    (lensXo.get (lensXo.set v4 (some Sym.mark))) (arrSyms b).reverse (S xkT2) S5 hmB
    (by simp [hS5, hS4])) (lensXo.set v4 (some Sym.mark)) rfl
  have h5B : S5 xkB = rb := by simp [hS5, hS4]
  rw [h5B, List.reverse_reverse] at e6
  refine ⟨_, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    e6))))).of_eq (st_eqX' rfl ?_) rfl⟩
  · have hv := vol_xorArr w a b hlen ha hb
    have hlo : out.reverse.length = vol a := by
      rw [List.length_reverse, hout, ← vol, hv]
    have hlb : (arrSyms b).reverse.length = vol b := by
      rw [List.length_reverse, ← vol]
    rw [hlo, hlb]
    omega
  · clear e1 e2 e3 e4 e5 e6
    funext k
    rcases k with k | k <;> fin_cases k <;> simp [hS5, hS4, hS2, hS1, hB]

end SubNLogN.Machine.C5.XorAux

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5.XorAux

/-- **Proposition A.7 leaf L3, XOR gate, proved** (`C5XorStmt`, `AppC/C5Leaves.lean`;
Proposition A.7 (`prop:transfer11`)). Kernel `XorAux.xMain` on `KLoc (Fin 2) (Fin 2)`, registers
`Option Sym × Option Sym`, constant `C = 10`. The hypothesis `BlkTerm rb` is not used. -/
theorem c5Xor_holds : C5XorStmt := by
  refine ⟨10, fun _ => ⟨Fin 2, inferInstance, inferInstance, XoReg, xMain, inferInstance,
    inferInstance, closed_xMain, ?_⟩⟩
  intro w a b ra rb S hlen ha hb hra _ hA hB
  apply Runs.of_eval
  rintro ⟨o, p⟩
  obtain ⟨v', t, ht, e⟩ := xMain_eval w a b ra rb S hlen ha hb hra hA hB o p
  exact ⟨v', t, e, trivial, ht⟩

end SubNLogN.Machine.C5
