import WP.W9f.Spec
import WP.W7k2.Call

/-!
# WP.W9f.Host — host layout of the column-solver composition

* `HL = Loc 12 64`: the 12 layout-B stacks as `Fin 12` (declaration order of `LB`) and 64 scratch
  stacks. The composition is written over `HL` with W7k2's call layer (`callI`, `HT`); `toB` is the
  bijection onto `BLoc 64`, and `runs_of_HT` turns a host `HT` into the contracts' `Runs`.
* `F`: the host stacks the composition modifies, `F.loc` their locations. A host state is
  `henc σ0 s` (stack `f.loc` holds `s f`, every other stack holds `σ0`); `henc_update` turns a
  `Function.update` of the host stacks into an update of `s`.
* `HT.ofEval`: an exact `Eval` of a macro (`SProg`, one `Option Sym` register) lifted through a
  register lens. `HT.moveBlockF`, `HT.copyBlockF`, `HT.pushF`, `HT.popF`: the library macros in
  `henc` form.
-/

namespace WP.W9f

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Host stacks and the transport to `BLoc 64` -/

/-- Host stacks: layout-B stacks as `Fin 12`, plus 64 scratch stacks. -/
abbrev HL : Type := Loc 12 64

/-- `Fin 12 → LB` in the declaration order of `LB`. -/
def lbOf (i : Fin 12) : LB :=
  match i.val with
  | 0 => .S | 1 => .W0 | 2 => .TL | 3 => .TR | 4 => .RET | 5 => .RQ | 6 => .C0 | 7 => .C1
  | 8 => .C2 | 9 => .C3 | 10 => .OA | _ => .OB

/-- `LB → Fin 12`. -/
def lbIdx : LB → Fin 12
  | .S => 0 | .W0 => 1 | .TL => 2 | .TR => 3 | .RET => 4 | .RQ => 5 | .C0 => 6 | .C1 => 7
  | .C2 => 8 | .C3 => 9 | .OA => 10 | .OB => 11

theorem lbOf_lbIdx (k : LB) : lbOf (lbIdx k) = k := by cases k <;> rfl

theorem lbIdx_lbOf (i : Fin 12) : lbIdx (lbOf i) = i := by
  fin_cases i <;> rfl

/-- Host stacks to `BLoc 64`. -/
def toB : HL → BLoc 64
  | .inl i => .inl (lbOf i)
  | .inr j => .inr j

/-- `BLoc 64` to host stacks. -/
def ofB : BLoc 64 → HL
  | .inl k => .inl (lbIdx k)
  | .inr j => .inr j

theorem toB_ofB (k : BLoc 64) : toB (ofB k) = k := by
  rcases k with k | j
  · exact congrArg Sum.inl (lbOf_lbIdx k)
  · rfl

theorem ofB_toB (l : HL) : ofB (toB l) = l := by
  rcases l with i | j
  · exact congrArg Sum.inl (lbIdx_lbOf i)
  · rfl

theorem toB_injective : Function.Injective toB := fun x y h => by
  rw [← ofB_toB x, ← ofB_toB y, h]

/-- **Transport.** An exact-stacks host run gives the contracts' `Runs` on `BLoc 64`. -/
theorem runs_of_HT {R : Type} {P : Prog HL (fun _ => Sym) R} {σ σ' : BLoc 64 → List Sym}
    {T : ℕ} (h : HT [] (fun l => σ (toB l)) P (fun l => σ' (toB l)) T) :
    Runs (P.mapStk toB) σ σ' (fun _ => True) T := by
  have h1 := Runs.embed toB_injective (HT.runs h) σ (fun _ => rfl)
  refine Triple.post h1 (fun s hs => ⟨?_, trivial⟩)
  obtain ⟨ha, -, -⟩ := hs
  funext k
  have e := ha (ofB k)
  rwa [toB_ofB] at e

theorem toB_closed {R : Type} {P : Prog HL (fun _ => Sym) R} (h : P.Closed) :
    (P.mapStk toB).Closed :=
  freeBelow_mapStk toB P 0 h

/-! ## Modified stacks and host states -/

/-- The host stacks that the composition modifies. -/
inductive F
  | W0 | TL | TR | C0 | X | X' | TT | PQ | PH | PK | PMU | PA | PC | RH
  deriving DecidableEq

/-- Their locations: `W0, TL, TR, C0` are layout-B stacks; the others are scratch. -/
def F.loc : F → HL
  | .W0 => .inl 1 | .TL => .inl 2 | .TR => .inl 3 | .C0 => .inl 6
  | .X => .inr 0 | .X' => .inr 1 | .TT => .inr 2 | .PQ => .inr 3 | .PH => .inr 4
  | .PK => .inr 5 | .PMU => .inr 6 | .PA => .inr 7 | .PC => .inr 8 | .RH => .inr 9

/-- All fields. -/
def F.all : List F := [.W0, .TL, .TR, .C0, .X, .X', .TT, .PQ, .PH, .PK, .PMU, .PA, .PC, .RH]

theorem F.mem_all (f : F) : f ∈ F.all := by cases f <;> simp [F.all]

theorem F.loc_injective : Function.Injective F.loc := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The field stored at a host stack, if any. -/
def F.of (k : HL) : Option F := F.all.find? (fun f => decide (f.loc = k))

theorem F.of_loc (f : F) : F.of f.loc = some f := by cases f <;> decide

theorem F.loc_of_of {k : HL} {f : F} (h : F.of k = some f) : f.loc = k := by
  have := List.find?_some h
  simpa using this

theorem F.of_none {k : HL} (h : F.of k = none) (f : F) : f.loc ≠ k := by
  intro e
  subst e
  rw [F.of_loc] at h
  cases h

/-- Host stacks from the base `σ0` and the modified stacks `s`. -/
def henc (σ0 : HL → List Sym) (s : F → List Sym) (k : HL) : List Sym :=
  match F.of k with
  | some f => s f
  | none => σ0 k

@[simp] theorem henc_loc (σ0 : HL → List Sym) (s : F → List Sym) (f : F) :
    henc σ0 s f.loc = s f := by
  simp [henc, F.of_loc]

theorem henc_other (σ0 : HL → List Sym) (s : F → List Sym) {k : HL} (h : ∀ f : F, f.loc ≠ k) :
    henc σ0 s k = σ0 k := by
  unfold henc
  cases hk : F.of k with
  | none => rfl
  | some f => exact absurd (F.loc_of_of hk) (h f)

@[simp] theorem henc_update (σ0 : HL → List Sym) (s : F → List Sym) (f : F) (x : List Sym) :
    Function.update (henc σ0 s) f.loc x = henc σ0 (Function.update s f x) := by
  funext k
  by_cases hk : k = f.loc
  · subst hk
    rw [Function.update_self, henc_loc, Function.update_self]
  · rw [Function.update_of_ne hk]
    cases h : F.of k with
    | none => rw [henc_other _ _ (F.of_none h), henc_other _ _ (F.of_none h)]
    | some g =>
      have hg := F.loc_of_of h
      subst hg
      have hgf : g ≠ f := fun e => hk (e ▸ rfl)
      rw [henc_loc, henc_loc, Function.update_of_ne hgf]

/-! ## Macros in host form -/

variable {σ : Type}

/-- A macro run through a register lens: an exact `Eval` (any initial register) gives `HT`. -/
theorem HT.ofEval (lS : Lens σ (Option Sym)) {p : SProg HL} {S S' : HL → List Sym} {T : ℕ}
    (h : ∀ v, ∃ v' t, Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T) : HT [] S (p.liftRegs lS) S' T := by
  rintro ⟨w, S0⟩ hs
  change S0 = S at hs
  subst hs
  obtain ⟨v', t, e, ht⟩ := h (lS.get w)
  exact ⟨_, t, Eval.liftRegs lS e w rfl, rfl, ht⟩

/-- Push a constant symbol onto a modified stack. -/
theorem HT.pushF (σ0 : HL → List Sym) (s : F → List Sym) (f : F) (x : Sym) :
    HT (σ := σ) [] (henc σ0 s) (pushS f.loc x) (henc σ0 (Function.update s f (x :: s f))) 1 := by
  have h := HT.pushS (σ := σ) f.loc x (henc σ0 s) []
  rwa [henc_loc, henc_update] at h

/-- Pop the top symbol of a modified stack. -/
theorem HT.popF (σ0 : HL → List Sym) (s : F → List Sym) (f : F) (x : Sym) (rest : List Sym)
    (hs : s f = x :: rest) :
    HT (σ := σ) [] (henc σ0 s) (popS f.loc) (henc σ0 (Function.update s f rest)) 1 := by
  have h := HT.popS (σ := σ) f.loc (henc σ0 s) x rest (by rw [henc_loc]; exact hs) []
  rwa [henc_update] at h

/-- `moveBlock` between modified stacks: the bit block is moved reversed, the terminator stays. -/
theorem HT.moveBlockF (lS : Lens σ (Option Sym)) (σ0 : HL → List Sym) (s : F → List Sym)
    (src dst : F) (hne : src ≠ dst) (es : List Bool) (rest : List Sym) (hrest : TermOK rest)
    (hs : s src = es.map Sym.bit ++ rest) :
    HT [] (henc σ0 s) ((moveBlock src.loc dst.loc).liftRegs lS)
      (henc σ0 (Function.update (Function.update s src rest) dst
        (es.reverse.map Sym.bit ++ s dst))) (3 * es.length + 4) := by
  refine HT.ofEval lS (fun v => ⟨rest.head?, 3 * es.length + 4,
    (moveBlock_eval (F.loc_injective.ne hne) [] v es rest (henc σ0 s) hrest
      (by rw [henc_loc]; exact hs)).of_eq ?_ rfl, le_rfl⟩)
  rw [henc_loc, henc_update, henc_update]

/-- `copyBlock` from a modified stack onto another (`tmp` restored). -/
theorem HT.copyBlockF (lS : Lens σ (Option Sym)) (σ0 : HL → List Sym) (s : F → List Sym)
    (src dst tmp : F) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) (blk : List Bool)
    (rest : List Sym) (hrest : TermOK rest) (hs : s src = blk.map Sym.bit ++ rest) :
    HT [] (henc σ0 s) ((copyBlock src.loc dst.loc tmp.loc).liftRegs lS)
      (henc σ0 (Function.update s dst (blk.map Sym.bit ++ s dst))) (7 * blk.length + 7) := by
  refine HT.ofEval lS (fun v => ⟨some .mark, 7 * blk.length + 7,
    (copyBlock_eval (F.loc_injective.ne hsd) (F.loc_injective.ne hst) (F.loc_injective.ne hdt)
      [] v blk rest (henc σ0 s) hrest (by rw [henc_loc]; exact hs)).of_eq ?_ rfl, le_rfl⟩)
  rw [henc_loc, henc_update]

#assert_std_axioms lbOf_lbIdx lbIdx_lbOf toB_ofB ofB_toB toB_injective runs_of_HT toB_closed
  F.mem_all F.loc_injective F.of_loc F.loc_of_of F.of_none henc_loc henc_other henc_update
  HT.ofEval HT.pushF HT.popF HT.moveBlockF HT.copyBlockF

end WP.W9f
