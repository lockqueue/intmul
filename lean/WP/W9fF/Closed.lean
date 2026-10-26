import WP.W9fF.IntCore
import WP.W7k2.Call

/-!
# WP.W9fF.Closed — compiled straight-line programs are closed

`noRec p` checks that `p` contains no `recur`; such programs are closed (`fb_of_noRec`). The
IntLang macros are checked by evaluation (`rfl`), `pushBits` by induction, and
`compile_closed`: if every op implementation is closed, every compiled program is closed.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts WP.W9fF.IL Computability

/-- The program contains no `recur`. -/
def noRec {K : Type} {Γ : K → Type} {σ : Type} : Prog K Γ σ → Bool
  | .push _ _ => true
  | .peek _ _ => true
  | .pop _ _ => true
  | .load _ => true
  | .seq p q => noRec p && noRec q
  | .ite _ p q => noRec p && noRec q
  | .loop _ p => noRec p
  | .fix b => noRec b
  | .recur _ => false

theorem fb_of_noRec {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ (p : Prog K Γ σ) (d : ℕ), noRec p = true → p.FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => by
    simp only [noRec, Bool.and_eq_true] at h
    exact ⟨fb_of_noRec p d h.1, fb_of_noRec q d h.2⟩
  | .ite _ p q, d, h => by
    simp only [noRec, Bool.and_eq_true] at h
    exact ⟨fb_of_noRec p d h.1, fb_of_noRec q d h.2⟩
  | .loop _ p, d, h => fb_of_noRec p d h
  | .fix b, d, h => fb_of_noRec b (d + 1) h
  | .recur _, _, h => absurd h (by simp [noRec])

section Macros

variable {K : Type}

theorem noRec_pushBits (k : K) : ∀ l : List Bool, noRec (pushBits k l) = true
  | [] => rfl
  | b :: l => by
    show (noRec (pushBits k l) && true) = true
    rw [noRec_pushBits k l]
    rfl

theorem noRec_pushInt (k : K) (c : ℤ) : noRec (pushInt k c) = true := by
  show (noRec (pushBits k (encodeNat c.natAbs)) && true) = true
  rw [noRec_pushBits]
  rfl

theorem noRec_dropInt (k : K) : noRec (dropInt k) = true := rfl

theorem noRec_copyInt (src dst tmp : K) : noRec (copyInt src dst tmp) = true := rfl

end Macros

theorem noRec_loadAB {V : Type} (y z : V) : noRec (loadAB y z) = true := rfl

theorem noRec_unloadAB {V : Type} : noRec (unloadAB (V := V)) = true := rfl

/-- **Compiled programs are closed** when the op implementations are. -/
theorem compile_closed {O V : Type} [DecidableEq O] [DecidableEq V] (I : O → OpImpl)
    (hI : ∀ o, (I o).P.Closed) : ∀ p : Stmt O V, (p.compile I).Closed
  | .assign x (.const c) => by
    show ((Prog.seq (dropInt (K := IStk V) (.inl x)) (pushInt (K := IStk V) (.inl x) c)).liftRegs
      (macroLens I)).FreeBelow 0
    refine WP.W7k2.freeBelow_liftRegs _ _ 0 (fb_of_noRec _ 0 ?_)
    show (noRec (dropInt (K := IStk V) (.inl x)) && noRec (pushInt (K := IStk V) (.inl x) c)) = true
    rw [noRec_dropInt, noRec_pushInt]
    rfl
  | .assign x (.op o y z) => by
    refine ⟨WP.W7k2.freeBelow_liftRegs _ _ 0 (fb_of_noRec _ 0 ?_),
      WP.W7k2.freeBelow_liftRegs _ _ 0 (WP.W7k2.freeBelow_mapStk _ _ 0 (hI o)),
      WP.W7k2.freeBelow_liftRegs _ _ 0 (fb_of_noRec _ 0 (noRec_unloadAB))⟩
    show (noRec (loadAB y z) && noRec (dropInt (K := IStk V) (.inl x))) = true
    rw [noRec_loadAB, noRec_dropInt]
    rfl
  | .seq p q => ⟨compile_closed I hI p, compile_closed I hI q⟩

#assert_std_axioms fb_of_noRec noRec_pushBits noRec_pushInt noRec_dropInt noRec_copyInt
  noRec_loadAB noRec_unloadAB compile_closed

end WP.W9fF
