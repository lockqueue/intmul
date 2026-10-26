import WP.W9s.Moves

/-!
# WP.W9s.Unary — dropping, unary copies and counted moves

* `dropTo k g`: pop symbols down to and including the first `g`.
* `uCopy src dst tmp`: push a copy of the unary counter on `src` onto `dst`.
* `uSubBy src v tmp`: remove from the counter `v` as many units as the counter `src` holds.
* `cntMove v v' src dst`: move as many records from `src` to `dst` as `v` holds units; the units
  go to `v'`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

section Unary

variable {a b : ℕ} {σ : Type}

/-- Is the peeked symbol a unit? -/
def isU (o : Option Sym) : Bool := decide (o = some symU)

/-- Is the peeked symbol different from `g`? -/
def notS (g : Sym) (o : Option Sym) : Bool := !decide (o = some g)

def dropTo (lS : Lens σ (Option Sym)) (k : Loc a b) (g : Sym) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (whileTop lS k (notS g) (popS k)) (popS k)

theorem dropTo_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (g : Sym) :
    (dropTo lS k g).Closed :=
  ⟨whileTop_closed lS k _ trivial, trivial⟩

theorem LoopHT.dropTo (lS : Lens σ (Option Sym)) (k : Loc a b) (g : Sym) (rest : List Sym)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (L : List Sym) (B : Loc a b → List Sym), g ∉ L → B k = L ++ g :: rest →
      LoopHT ρ lS k (notS g) (popS k) B (Function.update B k (g :: rest)) (3 * L.length + 1)
  | [], B, _, hB => by
    have hB' : B k = g :: rest := hB
    have heq : Function.update B k (g :: rest) = B := by
      rw [← hB']
      exact Function.update_eq_self k B
    rw [heq]
    exact LoopHT.stop (by simp [notS, hB'])
  | x :: L, B, hg, hB => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hstep := LoopHT.step (by simp [notS, hB, hx])
      (HT.popS (σ := σ) k B x (L ++ g :: rest) (by rw [hB]; rfl) ρ)
      (LoopHT.dropTo lS k g rest ρ L _ (fun h => hg (List.mem_cons_of_mem _ h)) (by simp))
    rw [Function.update_idem] at hstep
    exact hstep.mono (by simp only [List.length_cons]; omega)

theorem HT.dropTo (lS : Lens σ (Option Sym)) (k : Loc a b) (g : Sym) (L rest : List Sym)
    (B : Loc a b → List Sym) (hg : g ∉ L) (hB : B k = L ++ g :: rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.dropTo lS k g) (Function.update B k rest) (3 * L.length + 3) := by
  have h1 := HT.whileTop (LoopHT.dropTo lS k g rest ρ L B hg hB)
  have h2 := HT.popS (σ := σ) k (Function.update B k (g :: rest)) g rest (by simp) ρ
  exact (h1.seq h2).of_eq (by simp) (by omega)

/-- Copy a unary counter. -/
def uCopy (lS : Lens σ (Option Sym)) (src dst tmp : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (pushS tmp symG) <|
  .seq (whileTop lS src isU (.seq (popS src) (.seq (pushS tmp symU) (pushS dst symU)))) <|
  .seq (uMove lS tmp src) (popS tmp)

theorem uCopy_closed (lS : Lens σ (Option Sym)) (src dst tmp : Loc a b) :
    (uCopy lS src dst tmp).Closed :=
  ⟨trivial, whileTop_closed lS src _ ⟨trivial, trivial, trivial⟩, uMove_closed _ _ _, trivial⟩

theorem LoopHT.uCopy (lS : Lens σ (Option Sym)) {src dst tmp : Loc a b} (h1 : src ≠ dst)
    (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (rest : List Sym) (hr : rest.head? ≠ some symU)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (n : ℕ) (B : Loc a b → List Sym), B src = units n ++ rest →
      LoopHT ρ lS src isU (.seq (popS src) (.seq (pushS tmp symU) (pushS dst symU))) B
        (Function.update (Function.update (Function.update B src rest) tmp (units n ++ B tmp))
          dst (units n ++ B dst)) (5 * n + 1)
  | 0, B, hB => by
    have hB' : B src = rest := hB
    have heq : Function.update (Function.update (Function.update B src rest) tmp
        (units 0 ++ B tmp)) dst (units 0 ++ B dst) = B := by
      funext x
      by_cases hx : x = src
      · subst hx
        simp [hB', h1, h2]
      · simp [Function.update_apply, hx, units]
        split_ifs with h h' <;> simp_all
    rw [heq]
    exact LoopHT.stop (by simp [isU, hB', hr])
  | n + 1, B, hB => by
    have h := LoopHT.step (by simp [isU, hB, units_succ])
      ((HT.popS (σ := σ) src B symU (units n ++ rest) (by rw [hB]; rfl) ρ).seq
        ((HT.pushS (σ := σ) tmp symU _ ρ).seq (HT.pushS (σ := σ) dst symU _ ρ)))
      (LoopHT.uCopy lS h1 h2 h3 rest hr ρ n _ (by simp [h1, h2]))
    refine Triple.post (h.mono (by omega)) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases hx : x = src
    · subst hx
      simp [Function.update_apply, h1, h2]
    by_cases hy : x = tmp
    · subst hy
      simp [Function.update_apply, Ne.symm h2, h3.symm, units_append_cons]
    by_cases hz : x = dst
    · subst hz
      simp [Function.update_apply, Ne.symm h1, h3, units_append_cons]
    simp [Function.update_apply, hx, hy, hz]

theorem HT.uCopy (lS : Lens σ (Option Sym)) {src dst tmp : Loc a b} (h1 : src ≠ dst)
    (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (n : ℕ) (rest : List Sym) (hr : rest.head? ≠ some symU)
    (B : Loc a b → List Sym) (hB : B src = units n ++ rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.uCopy lS src dst tmp) (Function.update B dst (units n ++ B dst))
      (9 * n + 6) := by
  have chain :=
    (HT.pushS (σ := σ) tmp symG B ρ).seq <|
    (HT.whileTop (LoopHT.uCopy lS h1 h2 h3 rest hr ρ n _ (by simp [h2, hB]))).seq <|
    (HT.uMove lS (src := tmp) (dst := src) (Ne.symm h2) n (symG :: B tmp) (by simp [symG, symU])
      _ (by simp [h3.symm]) ρ).seq <|
    HT.popS (σ := σ) tmp _ symG (B tmp) (by simp [Ne.symm h2]) ρ
  refine chain.of_eq ?_ (by omega)
  funext x
  by_cases hx : x = src
  · subst hx
    simp [Function.update_apply, h1, h2, hB]
  by_cases hy : x = tmp
  · subst hy
    simp [Function.update_apply, Ne.symm h3]
  by_cases hz : x = dst
  · subst hz
    simp [Function.update_apply, Ne.symm h1, h3]
  simp [Function.update_apply, hx, hy, hz]

end Unary

#assert_std_axioms dropTo_closed LoopHT.dropTo HT.dropTo uCopy_closed LoopHT.uCopy HT.uCopy

end WP.W9s
