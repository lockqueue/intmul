import WP.W9s.Unary

/-!
# WP.W9s.Count — counted moves and counter subtraction

* `cntMove v v' src dst`: for each unit on `v` (moved to `v'`), move one record `src → dst`.
* `uSubBy src v tmp`: remove from `v` as many units as `src` holds (`src` restored).
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

section Count

variable {a b : ℕ} {σ : Type}

def cntMove (lS : Lens σ (Option Sym)) (v v' src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  whileTop lS v isU (.seq (popS v) (.seq (pushS v' symU) (moveRecD lS src dst)))

theorem cntMove_closed (lS : Lens σ (Option Sym)) (v v' src dst : Loc a b) :
    (cntMove lS v v' src dst).Closed :=
  whileTop_closed lS v _ ⟨trivial, trivial, moveRecD_closed _ _ _⟩

theorem LoopHT.cntMove (lS : Lens σ (Option Sym)) {v v' src dst : Loc a b}
    (h1 : v ≠ v') (h2 : v ≠ src) (h3 : v ≠ dst) (h4 : v' ≠ src) (h5 : v' ≠ dst) (h6 : src ≠ dst)
    (rv rs : List Sym) (hr : rv.head? ≠ some symU) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (l : List (ℤ × ℤ)) (B : Loc a b → List Sym), B v = units l.length ++ rv →
      B src = es l ++ rs →
      LoopHT ρ lS v isU (.seq (popS v) (.seq (pushS v' symU) (moveRecD lS src dst))) B
        (Function.update (Function.update (Function.update (Function.update B v rv) v'
          (units l.length ++ B v')) src rs) dst ((es l).reverse ++ B dst))
        (3 * (es l).length + 5 * l.length + 1)
  | [], B, hv, hs => by
    have hv' : B v = rv := hv
    have hs' : B src = rs := by simpa [es] using hs
    refine Triple.post ((LoopHT.stop (by simp [isU, hv', hr])).mono (by simp [es])) (fun s hs2 => ?_)
    rw [hs2]
    funext x
    by_cases hx : x = v
    · subst hx
      simp [hv', h1, h2, h3]
    by_cases hy : x = src
    · subst hy
      simp [hs', h6]
    by_cases hz : x = v'
    · subst hz
      simp [h4, h5, units]
    by_cases hw : x = dst
    · subst hw
      simp [es]
    simp [hx, hy, hz, hw]
  | z :: l, B, hv, hs => by
    have h := LoopHT.step (by simp [isU, hv, units_succ])
      ((HT.popS (σ := σ) v B symU (units l.length ++ rv) (by rw [hv]; rfl) ρ).seq
        ((HT.pushS (σ := σ) v' symU _ ρ).seq
          (HT.moveRecD lS h6 z (es l ++ rs) _ (by simp [Ne.symm h2, Ne.symm h4, hs, es_cons]) ρ)))
      (LoopHT.cntMove lS h1 h2 h3 h4 h5 h6 rv rs hr ρ l _ (by simp [h1, h2, h3]) (by simp [h6]))
    refine Triple.post (h.mono (by simp only [es_cons, List.length_append, List.length_cons]; omega))
      (fun s hs' => ?_)
    rw [hs']
    funext x
    by_cases hx : x = v
    · subst hx
      simp [Function.update_apply, h1, h2, h3]
    by_cases hy : x = v'
    · subst hy
      simp [Function.update_apply, Ne.symm h1, h4, h5, units_append_cons]
    by_cases hz : x = src
    · subst hz
      simp [Function.update_apply, h6]
    by_cases hw : x = dst
    · subst hw
      simp [Function.update_apply, Ne.symm h3, Ne.symm h5, es_cons]
    simp [Function.update_apply, hx, hy, hz, hw]

theorem HT.cntMove (lS : Lens σ (Option Sym)) {v v' src dst : Loc a b}
    (h1 : v ≠ v') (h2 : v ≠ src) (h3 : v ≠ dst) (h4 : v' ≠ src) (h5 : v' ≠ dst) (h6 : src ≠ dst)
    (rv rs : List Sym) (hr : rv.head? ≠ some symU) (l : List (ℤ × ℤ)) (B : Loc a b → List Sym)
    (hv : B v = units l.length ++ rv) (hs : B src = es l ++ rs)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.cntMove lS v v' src dst)
      (Function.update (Function.update (Function.update (Function.update B v rv) v'
        (units l.length ++ B v')) src rs) dst ((es l).reverse ++ B dst))
      (3 * (es l).length + 5 * l.length + 2) :=
  HT.whileTop (LoopHT.cntMove lS h1 h2 h3 h4 h5 h6 rv rs hr ρ l B hv hs)

/-- Subtract the counter on `src` from the counter on `v`. -/
def uSubBy (lS : Lens σ (Option Sym)) (src v tmp : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (pushS tmp symG) <|
  .seq (whileTop lS src isU (.seq (popS src) (.seq (pushS tmp symU) (popS v)))) <|
  .seq (uMove lS tmp src) (popS tmp)

theorem uSubBy_closed (lS : Lens σ (Option Sym)) (src v tmp : Loc a b) :
    (uSubBy lS src v tmp).Closed :=
  ⟨trivial, whileTop_closed lS src _ ⟨trivial, trivial, trivial⟩, uMove_closed _ _ _, trivial⟩

theorem LoopHT.uSubBy (lS : Lens σ (Option Sym)) {src v tmp : Loc a b} (h1 : src ≠ v)
    (h2 : src ≠ tmp) (h3 : v ≠ tmp) (rs rv : List Sym) (hr : rs.head? ≠ some symU)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (n c : ℕ) (B : Loc a b → List Sym), B src = units n ++ rs → B v = units (c + n) ++ rv →
      LoopHT ρ lS src isU (.seq (popS src) (.seq (pushS tmp symU) (popS v))) B
        (Function.update (Function.update (Function.update B src rs) tmp (units n ++ B tmp))
          v (units c ++ rv)) (5 * n + 1)
  | 0, c, B, hs, hv => by
    have hs' : B src = rs := hs
    refine Triple.post (LoopHT.stop (by simp [isU, hs', hr])) (fun s hs2 => ?_)
    rw [hs2]
    funext x
    by_cases hx : x = src
    · subst hx
      simp [hs', h1, h2]
    by_cases hy : x = v
    · subst hy
      simp [hv]
    by_cases hz : x = tmp
    · subst hz
      simp [Ne.symm h3, units]
    simp [hx, hy, hz]
  | n + 1, c, B, hs, hv => by
    have h := LoopHT.step (by simp [isU, hs, units_succ])
      ((HT.popS (σ := σ) src B symU (units n ++ rs) (by rw [hs]; rfl) ρ).seq
        ((HT.pushS (σ := σ) tmp symU _ ρ).seq
          (HT.popS (σ := σ) v _ symU (units (c + n) ++ rv)
            (by simp [Ne.symm h1, h3, hv, ← Nat.add_assoc, units_succ]) ρ)))
      (LoopHT.uSubBy lS h1 h2 h3 rs rv hr ρ n c _ (by simp [h1, h2]) (by simp))
    refine Triple.post (h.mono (by omega)) (fun s hs' => ?_)
    rw [hs']
    funext x
    by_cases hx : x = src
    · subst hx
      simp [Function.update_apply, h1, h2]
    by_cases hy : x = tmp
    · subst hy
      simp [Ne.symm h2, Ne.symm h3, units_append_cons]
    by_cases hz : x = v
    · subst hz
      simp [Function.update_apply]
    simp [Function.update_apply, hx, hy, hz]

theorem HT.uSubBy (lS : Lens σ (Option Sym)) {src v tmp : Loc a b} (h1 : src ≠ v)
    (h2 : src ≠ tmp) (h3 : v ≠ tmp) (n c : ℕ) (rs rv : List Sym) (hr : rs.head? ≠ some symU)
    (B : Loc a b → List Sym) (hs : B src = units n ++ rs) (hv : B v = units (c + n) ++ rv)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.uSubBy lS src v tmp) (Function.update B v (units c ++ rv)) (9 * n + 6) := by
  have chain :=
    (HT.pushS (σ := σ) tmp symG B ρ).seq <|
    (HT.whileTop (LoopHT.uSubBy lS h1 h2 h3 rs rv hr ρ n c _ (by simp [h2, hs])
      (by simp [h3, hv]))).seq <|
    (HT.uMove lS (src := tmp) (dst := src) (Ne.symm h2) n (symG :: B tmp) (by simp [symG, symU])
      _ (by simp [Ne.symm h3]) ρ).seq <|
    HT.popS (σ := σ) tmp _ symG (B tmp) (by simp [Ne.symm h2]) ρ
  refine chain.of_eq ?_ (by omega)
  funext x
  by_cases hx : x = src
  · subst hx
    simp [h1, h2, hs]
  by_cases hy : x = tmp
  · subst hy
    simp [Function.update_apply, Ne.symm h3]
  by_cases hz : x = v
  · subst hz
    simp [Function.update_apply, Ne.symm h1, h3]
  simp [Function.update_apply, hx, hy, hz]

end Count

#assert_std_axioms cntMove_closed LoopHT.cntMove HT.cntMove uSubBy_closed LoopHT.uSubBy HT.uSubBy

end WP.W9s
