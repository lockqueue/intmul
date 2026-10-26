import WP.W9sp.Ops

/-!
# WP.W9sp.Raw — raw symbol moves through a register lens, and header-field skipping

* `moveBlk lS src dst`: the library `moveBlock` (bits of `src` reversed onto `dst`, terminator
  kept) through a lens to a symbol register.
* `moveTop lS src dst`: pop the top symbol of `src` and push it on `dst`.
* `skipF lS src tmp` / `unskipF lS tmp src`: move one header field `natSyms v ++ [mark]` from `src`
  to `tmp` (stored as `mark :: reversed bits`) and back. Used to reach the fields of `C0`.

Adapted from `WP.W9h.Raw` for `W9_splitPack`.
-/

namespace WP.W9sp

open TMFw TMFw.Lib TMFw.Contracts WP.W7k2

variable {a b : ℕ} {σ : Type}

/-- `moveBlock` through a register lens. -/
def moveBlk (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (moveBlock src dst).liftRegs lS

/-- Pop the top symbol of `src` and push it on `dst`. -/
def moveTop (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (.pop src (fun v o => lS.set v o)) (.push dst (fun v => (lS.get v).getD .sep))

/-- Move one header field from `src` to `tmp`. -/
def skipF (lS : Lens σ (Option Sym)) (src tmp : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (moveBlk lS src tmp) (moveTop lS src tmp)

/-- Move one header field back from `tmp` to `src`. -/
def unskipF (lS : Lens σ (Option Sym)) (tmp src : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (moveTop lS tmp src) (moveBlk lS tmp src)

theorem moveBlk_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) :
    (moveBlk lS src dst).Closed :=
  freeBelow_liftRegs lS _ 0 (by
    simp [Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR,
      skip])

theorem moveTop_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) :
    (moveTop lS src dst).Closed := ⟨trivial, trivial⟩

theorem skipF_closed (lS : Lens σ (Option Sym)) (src tmp : Loc a b) :
    (skipF lS src tmp).Closed := ⟨moveBlk_closed lS src tmp, moveTop_closed lS src tmp⟩

theorem unskipF_closed (lS : Lens σ (Option Sym)) (tmp src : Loc a b) :
    (unskipF lS tmp src).Closed := ⟨moveTop_closed lS tmp src, moveBlk_closed lS tmp src⟩

theorem HT.moveBlk (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (es : List Bool) (rest : List Sym) (hrest : TermOK rest)
    (hB : B src = es.map Sym.bit ++ rest) :
    HT [] B (moveBlk lS src dst)
      (Function.update (Function.update B src rest) dst (es.reverse.map Sym.bit ++ B dst))
      (3 * es.length + 4) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨_, _, Eval.liftRegs lS (moveBlock_eval hne [] (lS.get v) es rest S hrest hB) v rfl, rfl,
    le_rfl⟩

theorem HT.moveTop (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (x : Sym) (r : List Sym) (hB : B src = x :: r) :
    HT [] B (moveTop lS src dst) (Function.update (Function.update B src r) dst (x :: B dst)) 2 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.pop ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) src (fun v o => lS.set v o) v S
  have e2 := Eval.push ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) dst
    (fun v => (lS.get v).getD .sep) (lS.set v (S src).head?)
    (Function.update S src (S src).tail)
  refine ⟨_, _, Eval.seq e1 e2, ?_, le_rfl⟩
  show Function.update (Function.update S src (S src).tail) dst
    ((lS.get (lS.set v (S src).head?)).getD .sep :: Function.update S src (S src).tail dst) = _
  rw [lS.get_set, hB, Function.update_of_ne (Ne.symm hne)]
  rfl

/-- Skip the field `v` of `src` onto `tmp`. -/
theorem HT.skipF (lS : Lens σ (Option Sym)) {src tmp : Loc a b} (hne : src ≠ tmp)
    (B : Loc a b → List Sym) (v : ℕ) (r : List Sym) (hB : B src = natSyms v ++ Sym.mark :: r) :
    HT [] B (skipF lS src tmp)
      (Function.update (Function.update B src r) tmp
        (Sym.mark :: ((Computability.encodeNat v).reverse.map Sym.bit ++ B tmp)))
      (3 * bitLen v + 6) := by
  have h1 := HT.moveBlk lS hne B (Computability.encodeNat v) (Sym.mark :: r) (TermOK.cons rfl r) hB
  refine (HT.seq h1 (HT.moveTop lS hne _ Sym.mark r
    (by rw [Function.update_of_ne hne, Function.update_self]))).of_eq ?_
    (by simp only [bitLen]; omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- Restore the field `v` from `tmp` onto `src`. -/
theorem HT.unskipF (lS : Lens σ (Option Sym)) {src tmp : Loc a b} (hne : src ≠ tmp)
    (B : Loc a b → List Sym) (v : ℕ) (rt : List Sym) (hrt : TermOK rt)
    (hB : B tmp = Sym.mark :: ((Computability.encodeNat v).reverse.map Sym.bit ++ rt)) :
    HT [] B (unskipF lS tmp src)
      (Function.update (Function.update B tmp rt) src (natSyms v ++ Sym.mark :: B src))
      (3 * bitLen v + 6) := by
  have h1 := HT.moveTop lS (Ne.symm hne) B Sym.mark _ hB
  have h2 := HT.moveBlk lS (Ne.symm hne)
    (Function.update (Function.update B tmp
      ((Computability.encodeNat v).reverse.map Sym.bit ++ rt)) src (Sym.mark :: B src))
    (Computability.encodeNat v).reverse rt hrt
    (by rw [Function.update_of_ne (Ne.symm hne), Function.update_self])
  refine (HT.seq h1 h2).of_eq ?_ (by simp only [bitLen, List.length_reverse]; omega)
  funext k
  simp only [Function.update_apply, List.reverse_reverse, natSyms]
  split_ifs <;> simp_all

#assert_std_axioms moveBlk_closed moveTop_closed skipF_closed unskipF_closed HT.moveBlk HT.moveTop
  HT.skipF HT.unskipF

end WP.W9sp
