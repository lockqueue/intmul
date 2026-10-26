import WP.W9s.Basic

/-!
# WP.W9s.Moves — record, row and unary moves

* `moveRecD src dst`: move one entry record (first symbol on top) symbol by symbol; `dst` receives
  it reversed.
* `mvRow src dst`: the same for a whole row and its terminator.
* `uMove src dst`: move a unary counter.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

section Moves

variable {a b : ℕ} {σ : Type}

/-- Move one entry record. -/
def moveRecD (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq ((WP.W9comp.rewindTo src dst Sym.sep).liftRegs lS) (pushS dst Sym.sep)

/-- Move one row and its terminator. -/
def mvRow (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq ((WP.W9comp.rewindTo src dst symRow).liftRegs lS) (pushS dst symRow)

/-- Move a unary counter. -/
def uMove (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  whileTop lS src (fun o => decide (o = some symU)) (.seq (popS src) (pushS dst symU))

theorem moveRecD_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) :
    (moveRecD lS src dst).Closed :=
  ⟨WP.W9comp.closed_rewind lS src dst _, trivial⟩

theorem mvRow_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) : (mvRow lS src dst).Closed :=
  ⟨WP.W9comp.closed_rewind lS src dst _, trivial⟩

theorem uMove_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) : (uMove lS src dst).Closed :=
  whileTop_closed lS src _ ⟨trivial, trivial⟩

/-- The data part of an entry record contains no `sep`. -/
theorem entrySyms_split (z : ℤ × ℤ) :
    ∃ d, entrySyms z = d ++ [Sym.sep] ∧ Sym.sep ∉ d ∧ d.length + 1 = (entrySyms z).length := by
  obtain ⟨d, hd, hdd⟩ := entrySyms_recOK z
  refine ⟨d, hd, fun h => by have := hdd _ h; exact Bool.false_ne_true this, ?_⟩
  rw [hd, List.length_append, List.length_singleton]

theorem HT.moveRecD (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (z : ℤ × ℤ) (rest : List Sym) (B : Loc a b → List Sym) (hB : B src = entrySyms z ++ rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.moveRecD lS src dst)
      (Function.update (Function.update B src rest) dst ((entrySyms z).reverse ++ B dst))
      (3 * (entrySyms z).length + 1) := by
  obtain ⟨d, hd, hs, hl⟩ := entrySyms_split z
  have h1 := HT.rewind lS hne Sym.sep d rest B hs (by rw [hB, hd, List.append_assoc]; rfl) ρ
  have h2 := HT.pushS dst Sym.sep
    (Function.update (Function.update B src rest) dst (d.reverse ++ B dst)) ρ
  refine (h1.seq h2).of_eq ?_ (by omega)
  funext x
  by_cases hx : x = dst
  · subst hx
    simp [hd]
  · simp [Function.update_apply, hx]

theorem HT.mvRow (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (row : List (ℤ × ℤ)) (rest : List Sym) (B : Loc a b → List Sym) (hB : B src = rowE row ++ rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.mvRow lS src dst)
      (Function.update (Function.update B src rest) dst ((rowE row).reverse ++ B dst))
      (3 * (es row).length + 3) := by
  have h1 := HT.rewind lS hne symRow (es row) rest B (tag_not_mem_es rfl row)
    (by rw [hB, rowE, List.append_assoc]; rfl) ρ
  have h2 := HT.pushS dst symRow
    (Function.update (Function.update B src rest) dst ((es row).reverse ++ B dst)) ρ
  refine (h1.seq h2).of_eq ?_ (by omega)
  funext x
  by_cases hx : x = dst
  · subst hx
    simp [rowE]
  · simp [Function.update_apply, hx]

theorem units_append_cons (n : ℕ) (l : List Sym) : units n ++ symU :: l = units (n + 1) ++ l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [units_succ, List.cons_append, ih, units_succ, units_succ]
    rfl

theorem LoopHT.uMove (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (rest : List Sym) (hr : rest.head? ≠ some symU) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (n : ℕ) (B : Loc a b → List Sym), B src = units n ++ rest →
      LoopHT ρ lS src (fun o => decide (o = some symU)) (.seq (popS src) (pushS dst symU)) B
        (Function.update (Function.update B src rest) dst (units n ++ B dst)) (4 * n + 1)
  | 0, B, hB => by
    have hB' : B src = rest := hB
    have hstop : LoopHT ρ lS src (fun o => decide (o = some symU))
        (.seq (popS src) (pushS dst symU)) B B 1 :=
      LoopHT.stop (by simp [hB', hr])
    have heq : Function.update (Function.update B src rest) dst (units 0 ++ B dst) = B := by
      funext x
      by_cases hx : x = src
      · subst hx
        simp [hB', hne]
      · by_cases hx' : x = dst
        · subst hx'
          simp [units]
        · simp [hx, hx']
    rw [heq]
    exact hstop
  | n + 1, B, hB => by
    have hpop := HT.popS (σ := σ) src B symU (units n ++ rest) (by rw [hB]; rfl) ρ
    have hpush := HT.pushS (σ := σ) dst symU (Function.update B src (units n ++ rest)) ρ
    have ih := LoopHT.uMove lS hne rest hr ρ n
      (Function.update (Function.update B src (units n ++ rest)) dst
        (symU :: Function.update B src (units n ++ rest) dst))
      (by simp [Function.update_apply, hne])
    refine (LoopHT.step (by simp [hB, units_succ]) (hpop.seq hpush) ih).mono (by omega) |>
      fun h => Triple.post h (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases hx : x = dst
    · subst hx
      simp [Ne.symm hne, units_append_cons]
    · by_cases hx' : x = src
      · subst hx'
        simp [Function.update_apply, hne]
      · simp [Function.update_apply, hx, hx']

theorem HT.uMove (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst) (n : ℕ)
    (rest : List Sym) (hr : rest.head? ≠ some symU) (B : Loc a b → List Sym)
    (hB : B src = units n ++ rest) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W9s.uMove lS src dst)
      (Function.update (Function.update B src rest) dst (units n ++ B dst)) (4 * n + 2) :=
  HT.whileTop (LoopHT.uMove lS hne rest hr ρ n B hB)

end Moves

#assert_std_axioms moveRecD_closed mvRow_closed uMove_closed entrySyms_split HT.moveRecD HT.mvRow
  units_append_cons LoopHT.uMove HT.uMove

end WP.W9s
