import WP.W9fN.NyqComp

/-!
# WP.W9fN.Closed — the Nyquist core program is closed; its register type is finite

Closedness (no free `recur`) of every macro, of compiled straight-line code (given closed op
implementations), and of `nyqProg`. `Finite Op`.
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL WP.W7k2

section Macros

variable {K : Type}

theorem pushBits_closed (k : K) : ∀ l : List Bool, (pushBits k l).Closed
  | [] => trivial
  | _ :: l => ⟨pushBits_closed k l, trivial⟩

theorem dropInt_closed (k : K) : (dropInt k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dropInt, dropBits, popR, restoreR, pushR, skip]

theorem copyInt_closed (a b c : K) : (copyInt a b c).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyInt, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]

theorem copyBlock_closed (a b c : K) : (copyBlock a b c).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]

theorem pushInt_closed (k : K) (c : ℤ) : (pushInt k c).Closed :=
  ⟨pushBits_closed k _, trivial⟩

theorem popEntry_closed (a b c d : K) : (popEntry a b c d).Closed :=
  ⟨⟨dropInt_closed _, copyInt_closed _ _ _, dropInt_closed _, trivial⟩,
    ⟨dropInt_closed _, copyInt_closed _ _ _, dropInt_closed _, trivial⟩⟩

theorem pushEntry_closed (a b c d : K) : (pushEntry a b c d).Closed :=
  ⟨⟨trivial, copyInt_closed _ _ _⟩, ⟨trivial, copyInt_closed _ _ _⟩⟩

theorem loadNat_closed (a b c : K) : (loadNat a b c).Closed :=
  ⟨dropInt_closed _, copyBlock_closed _ _ _, trivial⟩

theorem loadInt_closed (a b c : K) : (loadInt a b c).Closed :=
  ⟨dropInt_closed _, copyInt_closed _ _ _⟩

theorem initVars_closed (L : Lay K) : ∀ vs : List V, (L.initVars vs).Closed
  | [] => trivial
  | _ :: vs => ⟨trivial, trivial, initVars_closed L vs⟩

theorem dropVars_closed (L : Lay K) : ∀ vs : List V, (L.dropVars vs).Closed
  | [] => trivial
  | _ :: vs => ⟨dropInt_closed _, trivial, dropVars_closed L vs⟩

end Macros

/-! ## Compiled code -/

section Compiled

variable {O V : Type} [DecidableEq O] [DecidableEq V] (I : O → OpImpl)

omit [DecidableEq V] in
theorem compile_closed (hI : ∀ o, (I o).P.Closed) : ∀ p : Stmt O V, (p.compile I).Closed
  | .assign _ (.const _) =>
    freeBelow_liftRegs _ _ 0 ⟨dropInt_closed _, pushInt_closed _ _⟩
  | .assign _ (.op o _ _) =>
    ⟨freeBelow_liftRegs _ _ 0
        ⟨⟨trivial, copyInt_closed _ _ _, trivial, copyInt_closed _ _ _⟩, dropInt_closed _⟩,
      freeBelow_liftRegs _ _ 0 (freeBelow_mapStk _ _ 0 (hI o)),
      freeBelow_liftRegs _ _ 0 ⟨dropInt_closed _, trivial, dropInt_closed _, trivial⟩⟩
  | .seq p q => ⟨compile_closed hI p, compile_closed hI q⟩

end Compiled

/-! ## The Nyquist core -/

instance Op.instFinite : Finite Op := by
  refine Finite.of_injective (fun o : Op => (match o with
    | .add => 0 | .sub => 1 | .mul => 2 | .shl => 3 | .sar => 4 | .le => 5 | .divR => 6 : Fin 7))
    ?_
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem nyqProg_closed (I : Op → OpImpl) (hI : ∀ o, (I o).P.Closed) (IF : Inst 4 48 Unit) :
    (nyqProg I IF).Closed := by
  have hc : ∀ p : SL, ((p.compile I).mapStk LN.emb).Closed := fun p =>
    freeBelow_mapStk _ _ 0 (compile_closed I hI p)
  have hpro : (prologue I).Closed :=
    ⟨hM_closed I _ (initVars_closed LN _), hM_closed I _ (loadNat_closed _ _ _),
      hM_closed I _ (loadNat_closed _ _ _), hM_closed I _ (loadNat_closed _ _ _),
      hM_closed I _ (loadInt_closed _ _ _), hc pSetup, hM_closed I _ (popEntry_closed _ _ _ _),
      hM_closed I _ trivial, hM_closed I _ (pushEntry_closed _ _ _ _)⟩
  have hin : (inLoop I).Closed :=
    whileEnt_closed I _ _ ⟨hM_closed I _ (popEntry_closed _ _ _ _), hc pStepP,
      hM_closed I _ (pushEntry_closed _ _ _ _)⟩
  exact ⟨freeBelow_liftRegs _ _ 0 hpro, freeBelow_liftRegs _ _ 0 hin, callI_closed _ _ _ _,
    freeBelow_liftRegs _ _ 0 (hM_closed I _ trivial),
    freeBelow_liftRegs _ _ 0 (hM_closed I _ (dropVars_closed LN _))⟩

#assert_std_axioms pushBits_closed dropInt_closed copyInt_closed copyBlock_closed pushInt_closed
  popEntry_closed pushEntry_closed loadNat_closed loadInt_closed initVars_closed dropVars_closed
  compile_closed nyqProg_closed

end WP.W9fN
