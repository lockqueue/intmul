import Contracts.W9.Pipeline
import WP.W7k2.Ops
import WP.W7k2.Arith

/-!
# WP.W9sq.Host — host stacks of the `W9_square` kernel, transport to `BLoc`, raw moves

Host conventions follow `WP.W9h.Host`. The stage program is written over the host
`HL = Loc 12 24` with the W7k2 call layer. Named host stack `i` is the layout-B stack `lbOf i`
(0 S, 1 W0, 2 TL, 3 TR, 4 RET, 5 RQ, 6 C0, 7 C1, 8 C2, 9 C3, 10 OA, 11 OB); scratch is `.inr j`.
`eH : HL → BLoc 24` is a bijection, and `runs_of_HT` turns a host triple into the stage `Runs`.
The transport block is copied from `WP.W9h.Host` (another workspace), unchanged up to names.

Raw moves through a symbol-register lens `lS` (no contract calls, so no register is carried
across a call):
* `moveBlk` (the library `moveBlock`), `moveTop` (pop one symbol, push it elsewhere) and `dupTop`
  (pop one symbol, push it on two stacks);
* `pushMarks ks` / `popMarks ks`: one `mark` floor on every stack of `ks` (`floorSt`).
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Host and transport (as `WP.W9h.Host`) -/

/-- Scratch stacks of the kernel. -/
abbrev nS : ℕ := 24

/-- Host stacks. -/
abbrev HL : Type := Loc 12 nS

/-- Named host stack `i` as a layout-B stack. -/
def lbOf (i : Fin 12) : LB :=
  match i.val with
  | 0 => .S | 1 => .W0 | 2 => .TL | 3 => .TR | 4 => .RET | 5 => .RQ
  | 6 => .C0 | 7 => .C1 | 8 => .C2 | 9 => .C3 | 10 => .OA | _ => .OB

/-- Layout-B stack as a named host stack. -/
def finOf : LB → Fin 12
  | .S => 0 | .W0 => 1 | .TL => 2 | .TR => 3 | .RET => 4 | .RQ => 5
  | .C0 => 6 | .C1 => 7 | .C2 => 8 | .C3 => 9 | .OA => 10 | .OB => 11

theorem lbOf_finOf (k : LB) : lbOf (finOf k) = k := by
  cases k <;> rfl

theorem finOf_lbOf (i : Fin 12) : finOf (lbOf i) = i := by
  fin_cases i <;> rfl

/-- The transport bijection. -/
def eH : HL → BLoc nS
  | .inl i => .inl (lbOf i)
  | .inr j => .inr j

/-- Its inverse. -/
def eHinv : BLoc nS → HL
  | .inl k => .inl (finOf k)
  | .inr j => .inr j

theorem eH_eHinv (x : BLoc nS) : eH (eHinv x) = x := by
  rcases x with k | j
  · exact congrArg Sum.inl (lbOf_finOf k)
  · rfl

theorem eHinv_eH (x : HL) : eHinv (eH x) = x := by
  rcases x with i | j
  · exact congrArg Sum.inl (finOf_lbOf i)
  · rfl

theorem eH_injective : Function.Injective eH := fun x y h => by
  rw [← eHinv_eH x, ← eHinv_eH y, h]

/-- Host view of a layout-B state. -/
def toH (σ : BLoc nS → List Sym) : HL → List Sym := σ ∘ eH

theorem toH_update (σ : BLoc nS → List Sym) (k : LB) (v : List Sym) :
    toH (Function.update σ (.inl k) v) = Function.update (toH σ) (.inl (finOf k)) v := by
  have e : (.inl k : BLoc nS) = eH (.inl (finOf k)) := by
    show (Sum.inl k : BLoc nS) = Sum.inl (lbOf (finOf k))
    rw [lbOf_finOf]
  unfold toH
  rw [e]
  exact Function.update_comp_eq_of_injective σ eH_injective _ v

/-- **Transport**: a host triple from `toH σ` to `toH σ'` is the layout-B `Runs`. -/
theorem runs_of_HT {R : Type} {P : Prog HL (fun _ => Sym) R} {σ σ' : BLoc nS → List Sym} {T : ℕ}
    (h : HT [] (toH σ) P (toH σ') T) : Runs (P.mapStk eH) σ σ' (fun _ => True) T := by
  have h1 := Runs.embed eH_injective (HT.runs h) σ (fun _ => rfl)
  intro s hs
  obtain ⟨s', t, e, ⟨hin, -, -⟩, ht⟩ := h1 s hs
  refine ⟨s', t, e, ⟨?_, trivial⟩, ht⟩
  funext x
  rw [← eH_eHinv x]
  exact hin (eHinv x)

theorem closed_mapStk_eH {R : Type} {P : Prog HL (fun _ => Sym) R} (h : P.Closed) :
    (P.mapStk eH).Closed :=
  freeBelow_mapStk eH P 0 h

/-! ## Raw moves -/

variable {a b : ℕ} {σ : Type}

/-- `moveBlock` through a register lens. -/
def moveBlk (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (moveBlock src dst).liftRegs lS

/-- Pop the top symbol of `src` and push it on `dst`. -/
def moveTop (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (.pop src (fun v o => lS.set v o)) (.push dst (fun v => (lS.get v).getD .sep))

/-- Pop the top symbol of `src` and push it on `d1` and on `d2`. -/
def dupTop (lS : Lens σ (Option Sym)) (src d1 d2 : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (.pop src (fun v o => lS.set v o))
    (.seq (.push d1 (fun v => (lS.get v).getD .sep)) (.push d2 (fun v => (lS.get v).getD .sep)))

theorem moveBlk_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) :
    (moveBlk lS src dst).Closed :=
  freeBelow_liftRegs lS _ 0 (by
    simp [Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR,
      skip])

theorem moveTop_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) :
    (moveTop lS src dst).Closed := ⟨trivial, trivial⟩

theorem dupTop_closed (lS : Lens σ (Option Sym)) (src d1 d2 : Loc a b) :
    (dupTop lS src d1 d2).Closed := ⟨trivial, trivial, trivial⟩

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

theorem HT.dupTop (lS : Lens σ (Option Sym)) {src d1 d2 : Loc a b} (h1 : src ≠ d1)
    (h2 : src ≠ d2) (h12 : d1 ≠ d2) (B : Loc a b → List Sym) (x : Sym) (r : List Sym)
    (hB : B src = x :: r) :
    HT [] B (dupTop lS src d1 d2)
      (Function.update (Function.update (Function.update B src r) d1 (x :: B d1)) d2
        (x :: B d2)) 3 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.pop ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) src (fun v o => lS.set v o) v S
  have e2 := Eval.push ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) d1
    (fun v => (lS.get v).getD .sep) (lS.set v (S src).head?)
    (Function.update S src (S src).tail)
  have e3 := Eval.push ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) d2
    (fun v => (lS.get v).getD .sep) (lS.set v (S src).head?)
    (Function.update (Function.update S src (S src).tail) d1
      ((lS.get (lS.set v (S src).head?)).getD .sep :: Function.update S src (S src).tail d1))
  refine ⟨_, _, Eval.seq e1 (Eval.seq e2 e3), ?_, le_rfl⟩
  show Function.update (Function.update (Function.update S src (S src).tail) d1
      ((lS.get (lS.set v (S src).head?)).getD .sep :: Function.update S src (S src).tail d1)) d2
    ((lS.get (lS.set v (S src).head?)).getD .sep :: Function.update (Function.update S src
      (S src).tail) d1 ((lS.get (lS.set v (S src).head?)).getD .sep ::
        Function.update S src (S src).tail d1) d2) = _
  rw [lS.get_set, hB, Function.update_of_ne (Ne.symm h1), Function.update_of_ne (Ne.symm h12),
    Function.update_of_ne (Ne.symm h2)]
  rfl

/-! ## Floors -/

/-- Push one `mark` on every stack of the list (last listed stack first). -/
def pushMarks : List (Loc a b) → Prog (Loc a b) (fun _ => Sym) σ
  | [] => .load id
  | k :: ks => (pushMarks ks).seq (pushS k .mark)

/-- Pop one symbol from every stack of the list (first listed stack first). -/
def popMarks : List (Loc a b) → Prog (Loc a b) (fun _ => Sym) σ
  | [] => .load id
  | k :: ks => (popS k).seq (popMarks ks)

theorem pushMarks_closed : ∀ ks : List (Loc a b), (pushMarks (σ := σ) ks).Closed
  | [] => trivial
  | _ :: ks => ⟨pushMarks_closed ks, trivial⟩

theorem popMarks_closed : ∀ ks : List (Loc a b), (popMarks (σ := σ) ks).Closed
  | [] => trivial
  | _ :: ks => ⟨trivial, popMarks_closed ks⟩

/-- `B` with one `mark` on top of every stack of `ks`. -/
def floorSt (B : Loc a b → List Sym) : List (Loc a b) → Loc a b → List Sym
  | [] => B
  | k :: ks => Function.update (floorSt B ks) k (Sym.mark :: B k)

theorem floorSt_of_not_mem (B : Loc a b → List Sym) {k : Loc a b} :
    ∀ ks : List (Loc a b), k ∉ ks → floorSt B ks k = B k
  | [], _ => rfl
  | j :: ks, h => by
    have hj : k ≠ j := fun e => h (e ▸ List.mem_cons_self ..)
    have hk : k ∉ ks := fun e => h (List.mem_cons_of_mem _ e)
    rw [floorSt, Function.update_of_ne hj, floorSt_of_not_mem B ks hk]

theorem HT.load_id (B : Loc a b → List Sym) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (.load id) B 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨_, 1, Eval.load ρ id v S, rfl, le_rfl⟩

theorem HT.pushMarks (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (ks : List (Loc a b)), ks.Nodup → ∀ B : Loc a b → List Sym,
      HT ρ B (pushMarks ks) (floorSt B ks) (ks.length + 1)
  | [], _, B => HT.load_id B ρ
  | k :: ks, hnd, B => by
    have hk : k ∉ ks := (List.nodup_cons.mp hnd).1
    have ih := HT.pushMarks ρ ks (List.nodup_cons.mp hnd).2 B
    refine (HT.seq ih (HT.pushS k .mark _ ρ)).of_eq ?_ ?_
    · rw [floorSt_of_not_mem B ks hk]
      rfl
    · simp only [List.length_cons]
      omega

theorem HT.popMarks (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (ks : List (Loc a b)), ks.Nodup → ∀ B : Loc a b → List Sym,
      HT ρ (floorSt B ks) (popMarks ks) B (ks.length + 1)
  | [], _, B => HT.load_id B ρ
  | k :: ks, hnd, B => by
    have hk : k ∉ ks := (List.nodup_cons.mp hnd).1
    have ih := HT.popMarks ρ ks (List.nodup_cons.mp hnd).2 B
    have h1 : HT ρ (floorSt B (k :: ks)) (popS k) (floorSt B ks) 1 := by
      refine (HT.popS k (floorSt B (k :: ks)) Sym.mark (B k) (by simp [floorSt]) ρ).of_eq ?_ le_rfl
      rw [floorSt, Function.update_idem, ← floorSt_of_not_mem B ks hk, Function.update_eq_self]
    refine (HT.seq h1 ih).mono ?_
    simp only [List.length_cons]
    omega

#assert_std_axioms lbOf_finOf finOf_lbOf eH_eHinv eHinv_eH eH_injective toH_update runs_of_HT
  closed_mapStk_eH moveBlk_closed moveTop_closed dupTop_closed HT.moveBlk HT.moveTop HT.dupTop
  pushMarks_closed popMarks_closed floorSt_of_not_mem HT.load_id HT.pushMarks HT.popMarks

end WP.W9sq
