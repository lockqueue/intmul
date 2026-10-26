import WP.W7k1.Isqrt

/-!
# WP.W7k1.IsqrtOp — the isqrt kernel as a signed binary operation (IntLang shape)

IntLang (draft, `WP.IntLang.Core`) takes its operations as programs over `Loc 3 m` computing
`z += f a b` on **signed** operands (`intSyms`), operands restored (`BinOK`). The `W7_isqrt` kernel
works on an unsigned operand. `isqOp` adapts it:

1. pop the sign of `x` into a register slot (`x` now holds `natSyms |a|`);
2. run `isqrtProg` embedded by `isqEmb` (`a ↦ x`, destination `↦ z`, scratch `↦` scratch), with its
   registers behind `Lens.snd`;
3. push `pos` onto `z` (`intSyms ⌊√|a|⌋ = pos :: natSyms ⌊√|a|⌋`);
4. push the saved sign back onto `x`.

`isqOp_runs`: `z += ⌊√|a|⌋`, every other stack unchanged, within `200·(|a|²+1) + 3` steps, from any
register value. The second operand is ignored.
-/

namespace WP.W7k1

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Embedding of the isqrt kernel's stacks into a binary operation's. -/
def isqEmb : IK → Loc 3 6
  | .inl ⟨0, _⟩ => .inl 0
  | .inl ⟨_, _⟩ => .inl 2
  | .inr j => .inr j

theorem isqEmb_injective : Function.Injective isqEmb := by
  decide

theorem isqEmb_kA : isqEmb kA = .inl 0 := rfl

theorem isqEmb_kZ : isqEmb kZ = .inl 2 := rfl

/-- Stack functions on `Loc 3 6` agree iff they agree on the nine stacks. -/
theorem loc36_ext {F G : Loc 3 6 → List Sym} (h0 : F (.inl 0) = G (.inl 0))
    (h1 : F (.inl 1) = G (.inl 1)) (h2 : F (.inl 2) = G (.inl 2))
    (s0 : F (.inr 0) = G (.inr 0)) (s1 : F (.inr 1) = G (.inr 1)) (s2 : F (.inr 2) = G (.inr 2))
    (s3 : F (.inr 3) = G (.inr 3)) (s4 : F (.inr 4) = G (.inr 4)) (s5 : F (.inr 5) = G (.inr 5)) :
    F = G := by
  funext k
  rcases k with ⟨i, hi⟩ | ⟨j, hj⟩
  · match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
  · match j, hj with
    | 0, _ => exact s0
    | 1, _ => exact s1
    | 2, _ => exact s2
    | 3, _ => exact s3
    | 4, _ => exact s4
    | 5, _ => exact s5

/-- Registers of the adapter: the saved sign, then the kernel's registers. -/
abbrev OReg := Option Sym × IReg

/-- **The isqrt kernel as a signed binary operation**: `z += ⌊√|a|⌋`. -/
def isqOp : Prog (Loc 3 6) (fun _ => Sym) OReg :=
  .seq (.pop (.inl 0) (fun v o => (o, v.2)))
    (.seq ((isqrtProg.mapStk isqEmb).liftRegs (Lens.snd _ _))
    (.seq (.push (.inl 2) (fun _ => .pos)) (.push (.inl 0) (fun v => v.1.getD .sep))))

/-- Stack renaming preserves closedness. -/
theorem freeBelow_mapStk' {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), p.FreeBelow d → (p.mapStk ι).FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => ⟨freeBelow_mapStk' ι p d h.1, freeBelow_mapStk' ι q d h.2⟩
  | .ite _ p q, d, h => ⟨freeBelow_mapStk' ι p d h.1, freeBelow_mapStk' ι q d h.2⟩
  | .loop _ p, d, h => freeBelow_mapStk' ι p d h
  | .fix b, d, h => freeBelow_mapStk' ι b (d + 1) h
  | .recur _, _, h => h

/-- Register lifting preserves closedness. -/
theorem freeBelow_liftRegs' {K σ τ : Type} {Γ : K → Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), p.FreeBelow d → (p.liftRegs l).FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => ⟨freeBelow_liftRegs' l p d h.1, freeBelow_liftRegs' l q d h.2⟩
  | .ite _ p q, d, h => ⟨freeBelow_liftRegs' l p d h.1, freeBelow_liftRegs' l q d h.2⟩
  | .loop _ p, d, h => freeBelow_liftRegs' l p d h
  | .fix b, d, h => freeBelow_liftRegs' l b (d + 1) h
  | .recur _, _, h => h

theorem isqOp_closed : isqOp.Closed := by
  have h := isqrtProg_closed
  simp only [Prog.Closed] at h ⊢
  simp only [isqOp, Prog.FreeBelow]
  exact ⟨trivial, freeBelow_liftRegs' _ _ 0 (freeBelow_mapStk' _ _ 0 h), trivial, trivial⟩

/-- Stacks after an embedded run that updates one stack: the image of that stack is updated,
everything else is unchanged. -/
theorem embed_update {L K : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) {G G' : K → List Sym} {l₀ : L} {X : List Sym}
    (h1 : ∀ l, G' (ι l) = Function.update (fun l => G (ι l)) l₀ X l)
    (h2 : ∀ k, (∀ l, ι l ≠ k) → G' k = G k) :
    G' = Function.update G (ι l₀) X := by
  funext k
  by_cases hk : ∃ l, ι l = k
  · obtain ⟨l, rfl⟩ := hk
    rw [h1]
    by_cases hl : l = l₀
    · subst hl
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hl, Function.update_of_ne (hι.ne hl)]
  · have hk' : ∀ l, ι l ≠ k := fun l e => hk ⟨l, e⟩
    rw [h2 k hk', Function.update_of_ne (fun e => hk' l₀ e.symm)]

/-- **Semantics and cost of the adapter.** -/
theorem isqOp_eval (a : ℤ) (ra : List Sym) (v : OReg) (S : Loc 3 6 → List Sym)
    (hra : TermOK ra) (hA : S (.inl 0) = intSyms a ++ ra) :
    ∃ v' t, Eval [] isqOp ⟨v, S⟩
      ⟨v', Function.update S (.inl 2) (intSyms (Nat.sqrt a.natAbs : ℤ) ++ S (.inl 2))⟩ t ∧
      t ≤ 200 * (bitLen a.natAbs * bitLen a.natAbs + 1) + 3 := by
  -- 1. pop the sign
  have e1 : Eval [] (.pop (.inl 0) (fun (v : OReg) o => (o, v.2)) : Prog (Loc 3 6) (fun _ => Sym) OReg)
      ⟨v, S⟩ ⟨(some (sgnSym a), v.2), Function.update S (.inl 0) (natSyms a.natAbs ++ ra)⟩ 1 := by
    refine (Eval.pop [] (.inl 0) _ v S).of_eq ?_ rfl
    rw [hA]
    rfl
  generalize hS1 : Function.update S (.inl 0) (natSyms a.natAbs ++ ra) = S1 at e1
  -- 2. the embedded kernel
  obtain ⟨w, t, e, ht⟩ := isqrtProg_eval a.natAbs ra v.2 (fun k => S1 (isqEmb k)) hra
    (by rw [← hS1]; show Function.update S (.inl 0) _ (isqEmb kA) = _; rw [isqEmb_kA]; simp)
  obtain ⟨T', hT1, hT2, e'⟩ := Eval.mapStk isqEmb_injective e S1 (fun _ => rfl)
  have e2 := Eval.liftRegs (Lens.snd (Option Sym) IReg) e' (some (sgnSym a), v.2) rfl
  have hT' : T' = Function.update S1 (.inl 2) (natSyms (Nat.sqrt a.natAbs) ++ S1 (.inl 2)) := by
    have h := embed_update (l₀ := kZ) isqEmb_injective hT1 hT2
    rw [isqEmb_kZ] at h
    exact h
  rw [hT'] at e2
  -- 3., 4. the sign symbols
  have e3 := Eval.push [] (.inl 2) (fun (_ : OReg) => Sym.pos)
    (some (sgnSym a), w) (Function.update S1 (.inl 2) (natSyms (Nat.sqrt a.natAbs) ++ S1 (.inl 2)))
  have e4 := Eval.push [] (.inl 0) (fun (v : OReg) => v.1.getD .sep) (some (sgnSym a), w)
    (Function.update (Function.update S1 (.inl 2) (natSyms (Nat.sqrt a.natAbs) ++ S1 (.inl 2)))
      (.inl 2) (Sym.pos :: Function.update S1 (.inl 2)
        (natSyms (Nat.sqrt a.natAbs) ++ S1 (.inl 2)) (.inl 2)))
  refine ⟨(some (sgnSym a), w), _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl,
    by omega⟩
  rw [← hS1, intSyms_natCast]
  refine congrArg₂ St.mk rfl (loc36_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
    simp +decide [hA, intSyms]

/-- **The adapter in IntLang's `BinOK` shape**: for all signed operands, `z += ⌊√|a|⌋` within
`200·(|a|²+1) + 3` steps, every other stack unchanged, from any register value. -/
theorem isqOp_runs (a b : ℤ) (ra rb : List Sym) (S : Loc 3 6 → List Sym) (hra : TermOK ra)
    (_hrb : TermOK rb) (_hz : TermOK (S (.inl 2))) (hA : S (.inl 0) = intSyms a ++ ra)
    (_hB : S (.inl 1) = intSyms b ++ rb) :
    Runs isqOp S (Function.update S (.inl 2) (intSyms (Nat.sqrt a.natAbs : ℤ) ++ S (.inl 2)))
      (fun _ => True) (200 * (bitLen a.natAbs * bitLen a.natAbs + 1) + 3) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := isqOp_eval a ra v S hra hA
  exact ⟨v', t, e, trivial, ht⟩

#assert_std_axioms freeBelow_mapStk' freeBelow_liftRegs' isqEmb_injective isqEmb_kA isqEmb_kZ
  loc36_ext isqOp_closed embed_update isqOp_eval isqOp_runs

end WP.W7k1
