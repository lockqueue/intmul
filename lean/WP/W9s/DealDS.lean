import WP.W9s.CombineHT

/-!
# WP.W9s.DealDS — dealing rows, the step stack, and the peek branch

* `dealLoop K`: deal the rows of the block on `sA` in pairs onto `sE` (even) and `sO` (odd).
* `dsDouble K`: push a doubled copy of the top step block of `sDS`; `dsPop K` removes it.
* `HT.peekIte`: peek, then branch on the peeked symbol.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

section Generic

variable {a b : ℕ} {σ : Type}

theorem HT.peekIte (lS : Lens σ (Option Sym)) (k : Loc a b) (f : Option Sym → Bool)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) (B B' : Loc a b → List Sym) {T₁ T₂ : ℕ}
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    (hp : f (B k).head? = true → HT ρ B p B' T₁) (hq : f (B k).head? = false → HT ρ B q B' T₂) :
    HT ρ B (.seq (peekL lS k) (.ite (fun v => f (lS.get v)) p q)) B' (1 + (max T₁ T₂ + 1)) := by
  have h1 : Triple ρ (fun s => s.stk = B) (peekL lS k)
      (fun s => s.stk = B ∧ lS.get s.var = (B k).head?) 1 := by
    rintro ⟨v, S⟩ hS
    change S = B at hS
    subst hS
    exact ⟨_, 1, Eval.peek ρ k (fun v o => lS.set v o) v S, ⟨rfl, lS.get_set _ _⟩, le_rfl⟩
  refine Triple.seq h1 (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hfo : f (B k).head? = true := by rw [← hsx]; exact hc
    exact (hp hfo).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hfo : f (B k).head? = false := by rw [← hsx]; exact hc
    exact (hq hfo).mono (le_max_right _ _) s hsB

/-- One unit to `dst`, two to `dst2`, per unit of `src`. -/
def uDup (lS : Lens σ (Option Sym)) (src dst dst2 : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  whileTop lS src isU (.seq (popS src) (.seq (pushS dst symU) (.seq (pushS dst2 symU)
    (pushS dst2 symU))))

theorem uDup_closed (lS : Lens σ (Option Sym)) (src dst dst2 : Loc a b) :
    (uDup lS src dst dst2).Closed :=
  whileTop_closed lS src _ ⟨trivial, trivial, trivial, trivial⟩

theorem LoopHT.uDup (lS : Lens σ (Option Sym)) {src dst dst2 : Loc a b} (h1 : src ≠ dst)
    (h2 : src ≠ dst2) (h3 : dst ≠ dst2) (rest : List Sym) (hr : rest.head? ≠ some symU)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (n : ℕ) (B : Loc a b → List Sym), B src = units n ++ rest →
      LoopHT ρ lS src isU (.seq (popS src) (.seq (pushS dst symU) (.seq (pushS dst2 symU)
          (pushS dst2 symU)))) B
        (Function.update (Function.update (Function.update B src rest) dst (units n ++ B dst))
          dst2 (units (2 * n) ++ B dst2)) (6 * n + 1)
  | 0, B, hB => by
    have hB' : B src = rest := hB
    refine Triple.post (LoopHT.stop (by simp [isU, hB', hr])) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases hx : x = src
    · subst hx
      simp [hB', h1, h2]
    by_cases hy : x = dst
    · subst hy
      simp [h3, units]
    by_cases hz : x = dst2
    · subst hz
      simp [units]
    simp [hx, hy, hz]
  | n + 1, B, hB => by
    have h := LoopHT.step (by simp [isU, hB, units_succ])
      ((HT.popS (σ := σ) src B symU (units n ++ rest) (by rw [hB]; rfl) ρ).seq
        ((HT.pushS (σ := σ) dst symU _ ρ).seq ((HT.pushS (σ := σ) dst2 symU _ ρ).seq
          (HT.pushS (σ := σ) dst2 symU _ ρ))))
      (LoopHT.uDup lS h1 h2 h3 rest hr ρ n _ (by simp [h1, h2]))
    refine Triple.post (h.mono (by omega)) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases hx : x = src
    · subst hx
      simp [h1, h2]
    by_cases hy : x = dst
    · subst hy
      simp [Ne.symm h1, h3, units_append_cons]
    by_cases hz : x = dst2
    · subst hz
      simp [Ne.symm h2, Ne.symm h3]
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, ← units_append_cons, ← units_append_cons]
    simp [Function.update_apply, hx, hy, hz]

theorem HT.uDup (lS : Lens σ (Option Sym)) {src dst dst2 : Loc a b} (h1 : src ≠ dst)
    (h2 : src ≠ dst2) (h3 : dst ≠ dst2) (n : ℕ) (rest : List Sym) (hr : rest.head? ≠ some symU)
    (B : Loc a b → List Sym) (hB : B src = units n ++ rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.uDup lS src dst dst2)
      (Function.update (Function.update (Function.update B src rest) dst (units n ++ B dst))
        dst2 (units (2 * n) ++ B dst2)) (6 * n + 2) :=
  HT.whileTop (LoopHT.uDup lS h1 h2 h3 rest hr ρ n B hB)

end Generic

#assert_std_axioms HT.peekIte uDup_closed LoopHT.uDup HT.uDup

end WP.W9s
