import WP.W9fNF.Macros2
import WP.W9fM.Move

/-!
# WP.W9fNF.Prog — the Nyquist finish program

**Layout** `FS = Loc 4 24`.
* Named: `Z = .inl 0` (Z block; later the reversed outputs), `O = .inl 1` (OUT), `K = .inl 2` (`k`),
  `AL = .inl 3` (`alt`).
* Data scratch: `T` (moved Z block), `A1`/`A2` (accumulators, later `D1`/`D2`), `X` (temporary),
  `KI` (`k - 1`), `ONE` (`1`), all above a guard `mark`; `P`, `M` (macro scratch).
* Callee pool: `.inr 8 … .inr 23`. A callee's scratch `j` is mapped to pool stack `8 + j`.

**Subroutines** (`Kit`, parameters): W3 `subInt`, `addInt`, `negInt`, W9fOps `shrFloor`. Each runs
behind its own register lens; the macros use the first register component.

**Program** `finishProg κ = setup; pass1; diff; pass2; pass3; cleanup`:
* pass 1 (`Z → T`, last entry first): `A := z - A` per coordinate;
* diff: `D = ((alt - A) >>> (k - 1) + 1) >>> 1` per coordinate, on the stacks `A1`, `A2`;
* pass 2 (`T → Z`): push `z + D`, then `D := -D`;
* pass 3: W9fM's entry mover `Z → O`.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

/-! ## Layout -/

/-- Stacks of the finish program. -/
abbrev FS := Loc 4 24

abbrev sZ : FS := .inl 0
abbrev sO : FS := .inl 1
abbrev sK : FS := .inl 2
abbrev sAL : FS := .inl 3
abbrev sT : FS := .inr 0
abbrev sA1 : FS := .inr 1
abbrev sA2 : FS := .inr 2
abbrev sX : FS := .inr 3
abbrev sKI : FS := .inr 4
abbrev sONE : FS := .inr 5
abbrev sP : FS := .inr 6
abbrev sM : FS := .inr 7

/-- Not a callee-pool stack. -/
def NotPool (a : FS) : Prop := ∀ j : Fin 24, a = .inr j → j.val < 8

theorem notPool_inl (i : Fin 4) : NotPool (.inl i) := fun _ h => by cases h

theorem notPool_inr (j : Fin 24) (h : j.val < 8) : NotPool (.inr j) := fun j' h' => by
  cases h'
  exact h

/-- Callee stacks: named `i ↦ f i`; scratch `j ↦` pool stack `8 + j`. -/
def emb {n m : ℕ} (hm : m ≤ 16) (f : Fin n → FS) : Loc n m → FS
  | .inl i => f i
  | .inr j => .inr ⟨8 + j.val, by omega⟩

theorem emb_injective {n m : ℕ} (hm : m ≤ 16) {f : Fin n → FS} (hf : Function.Injective f)
    (hp : ∀ i, NotPool (f i)) : Function.Injective (emb hm f) := by
  intro x y h
  rcases x with i | j <;> rcases y with i' | j'
  · exact congrArg Sum.inl (hf h)
  · have := hp i _ h
    dsimp only at this
    omega
  · have := hp i' _ h.symm
    dsimp only at this
    omega
  · simp only [emb, Sum.inr.injEq, Fin.mk.injEq] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- Three named stacks. -/
def tri (a b c : FS) : Fin 3 → FS
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨_ + 2, _⟩ => c

theorem tri_injective {a b c : FS} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :
    Function.Injective (tri a b c) := by
  intro i i' h
  rcases i with ⟨_ | _ | i, hi⟩ <;> rcases i' with ⟨_ | _ | i', hi'⟩
  · rfl
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h.symm h1
  · rfl
  · exact absurd h h3
  · exact absurd h.symm h2
  · exact absurd h.symm h3
  · exact Fin.ext (show i + 2 = i' + 2 by omega)

theorem tri_notPool {a b c : FS} (ha : NotPool a) (hb : NotPool b) (hc : NotPool c) :
    ∀ i, NotPool (tri a b c i)
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb
  | ⟨_ + 2, _⟩ => hc

theorem one_injective (a : FS) : Function.Injective (fun _ : Fin 1 => a) := by
  intro i i' _
  exact Subsingleton.elim i i'

/-- Pass 3's embedding of W9fM's mover: source `Z`, destination `O`, scratch `M`. -/
def ιM : Loc 2 1 → FS
  | .inl ⟨0, _⟩ => sZ
  | .inl ⟨_ + 1, _⟩ => sO
  | .inr _ => sM

/-- A left inverse of `ιM`. -/
def ιMinv : FS → Loc 2 1
  | .inl ⟨0, _⟩ => .inl 0
  | .inl ⟨_ + 1, _⟩ => .inl 1
  | .inr _ => .inr 0

theorem ιM_injective : Function.Injective ιM := by
  refine Function.LeftInverse.injective (g := ιMinv) ?_
  intro x
  rcases x with ⟨_ | x, hx⟩ | ⟨_ | x, hx⟩
  · rfl
  · obtain rfl : x = 0 := by omega
    rfl
  · rfl
  · omega

/-! ## Subroutines and registers -/

/-- The subroutine programs (W3 `subInt`, `addInt`, `negInt`; W9fOps `shrFloor`). -/
structure Kit where
  ms : ℕ
  ma : ℕ
  mn : ℕ
  mf : ℕ
  Rs : Type
  Ra : Type
  Rn : Type
  Rf : Type
  hms : ms ≤ 16
  hma : ma ≤ 16
  hmn : mn ≤ 16
  hmf : mf ≤ 16
  Psub : Prog (Loc 3 ms) (fun _ => Sym) Rs
  Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra
  Pneg : Prog (Loc 1 mn) (fun _ => Sym) Rn
  Pshr : Prog (Loc 3 mf) (fun _ => Sym) Rf

/-- The subroutine contracts (shapes of `W3_subInt`, `W3_addInt`, `W3_negInt`, and W9fOps'
`W9fBinOp (fun a b => a >>> b.natAbs)`). -/
structure Kit.OK (κ : Kit) (Cs Ca Cn Cf : ℕ) : Prop where
  sub : ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 κ.ms → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs κ.Psub S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (Cs * (bitLen a.natAbs + bitLen b.natAbs + 1))
  add : ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 κ.ma → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs κ.Padd S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (Ca * (bitLen a.natAbs + bitLen b.natAbs + 1))
  neg : ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 κ.mn → List Sym), TermOK rx →
    S (.inl 0) = intSyms z ++ rx →
    Runs κ.Pneg S (Function.update S (.inl 0) (intSyms (-z) ++ rx)) (fun _ => True) Cn
  shr : ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 κ.mf → List Sym), TermOK ra → TermOK rb →
    TermOK (S (.inl 2)) → S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs κ.Pshr S (Function.update S (.inl 2) (intSyms (a >>> b.natAbs) ++ S (.inl 2)))
      (fun _ => True) (Cf * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Registers: the macro register, then the four subroutines' registers. -/
abbrev Kit.Reg (κ : Kit) : Type := Option Sym × (κ.Rs × (κ.Ra × (κ.Rn × κ.Rf)))

def Kit.lS (κ : Kit) : Lens κ.Reg κ.Rs := Lens.comp (Lens.snd _ _) (Lens.fst _ _)

def Kit.lA (κ : Kit) : Lens κ.Reg κ.Ra :=
  Lens.comp (Lens.snd _ _) (Lens.comp (Lens.snd _ _) (Lens.fst _ _))

def Kit.lN (κ : Kit) : Lens κ.Reg κ.Rn :=
  Lens.comp (Lens.snd _ _) (Lens.comp (Lens.snd _ _) (Lens.comp (Lens.snd _ _) (Lens.fst _ _)))

def Kit.lF (κ : Kit) : Lens κ.Reg κ.Rf :=
  Lens.comp (Lens.snd _ _) (Lens.comp (Lens.snd _ _) (Lens.comp (Lens.snd _ _) (Lens.snd _ _)))

section Program

variable (κ : Kit)

/-- A macro on the first register component. -/
def liftM (p : SProg FS) : Prog FS (fun _ => Sym) κ.Reg := p.liftRegs (Lens.fst _ _)

/-- `c += a - b`. -/
def callSub (a b c : FS) : Prog FS (fun _ => Sym) κ.Reg := call (emb κ.hms (tri a b c)) κ.lS κ.Psub

/-- `c += a + b`. -/
def callAdd (a b c : FS) : Prog FS (fun _ => Sym) κ.Reg := call (emb κ.hma (tri a b c)) κ.lA κ.Padd

/-- `a := -a`. -/
def callNeg (a : FS) : Prog FS (fun _ => Sym) κ.Reg := call (emb κ.hmn (fun _ => a)) κ.lN κ.Pneg

/-- `c += a >>> |b|`. -/
def callShr (a b c : FS) : Prog FS (fun _ => Sym) κ.Reg := call (emb κ.hmf (tri a b c)) κ.lF κ.Pshr

/-- Loop test: the macro register holds the first symbol of an entry. -/
def isSgnR (v : κ.Reg) : Bool := WP.W9fM.isSgn v.1

/-- Guards, `A := (0, 0)`, `KI := k - 1`, `ONE := 1`. -/
def setup : SProg FS :=
  .seq (pushC sT .mark) (.seq (pushC sA1 .mark) (.seq (pushC sA2 .mark) (.seq (pushC sX .mark)
  (.seq (pushC sKI .mark) (.seq (pushC sONE .mark) (.seq (pushC sA1 .pos) (.seq (pushC sA2 .pos)
  (.seq (copyBlock sK sKI sM) (.seq (dec sKI sM) (.seq (pushC sKI .pos)
  (.seq (pushC sONE (.bit true)) (pushC sONE .pos))))))))))))

/-- Pass 1, one entry: `A := z - A` per coordinate; move the entry `Z → T`. -/
def body1 : Prog FS (fun _ => Sym) κ.Reg :=
  .seq (callSub κ sZ sA1 sX) (.seq (liftM κ (replInt sX sA1 sM)) (.seq (liftM κ (peel sZ sP))
  (.seq (callSub κ sZ sA2 sX) (.seq (liftM κ (replInt sX sA2 sM)) (.seq (liftM κ (stageB sP sZ))
  (.seq (liftM κ (moveOne sZ sT sM)) (liftM κ (peekR sZ))))))))

def pass1 : Prog FS (fun _ => Sym) κ.Reg :=
  .seq (liftM κ (peekR sZ)) (.loop (isSgnR κ) (body1 κ))

/-- One coordinate of `D = ((alt - A) >>> (k - 1) + 1) >>> 1`; the result replaces `A` on `Aj`. -/
def diffCoord (Aj : FS) : Prog FS (fun _ => Sym) κ.Reg :=
  .seq (callSub κ sAL Aj sX) (.seq (liftM κ (dropInt Aj)) (.seq (callShr κ sX sKI Aj)
  (.seq (liftM κ (dropInt sX)) (.seq (callAdd κ Aj sONE sX) (.seq (liftM κ (dropInt Aj))
  (.seq (callShr κ sX sONE Aj) (liftM κ (dropInt sX))))))))

def diff : Prog FS (fun _ => Sym) κ.Reg :=
  .seq (diffCoord κ sA1) (.seq (liftM κ (peel sAL sP)) (.seq (diffCoord κ sA2)
    (liftM κ (stageB sP sAL))))

/-- Pass 2, one entry: push `z + D` onto `Z`, drop the entry from `T`, `D := -D`. -/
def body2 : Prog FS (fun _ => Sym) κ.Reg :=
  .seq (liftM κ (pushC sZ .sep)) (.seq (liftM κ (peel sT sP)) (.seq (callAdd κ sT sA2 sZ)
  (.seq (liftM κ (stageB sP sT)) (.seq (liftM κ (pushC sZ .sep2)) (.seq (callAdd κ sT sA1 sZ)
  (.seq (liftM κ (dropUntil .sep sT)) (.seq (callNeg κ sA1) (.seq (callNeg κ sA2)
    (liftM κ (peekR sT))))))))))

def pass2 : Prog FS (fun _ => Sym) κ.Reg :=
  .seq (liftM κ (peekR sT)) (.loop (isSgnR κ) (body2 κ))

/-- Pass 3: W9fM's entry mover `Z → O`. -/
def pass3 : Prog FS (fun _ => Sym) κ.Reg := call ιM (Lens.fst _ _) WP.W9fM.moveEntriesProg

/-- Drop `D1`, `D2`, `KI`, `ONE`; pop the guards. -/
def cleanup : SProg FS :=
  .seq (dropInt sA1) (.seq (dropInt sA2) (.seq (dropInt sKI) (.seq (dropInt sONE)
  (.seq (popR sT) (.seq (popR sA1) (.seq (popR sA2) (.seq (popR sX) (.seq (popR sKI)
    (popR sONE)))))))))

/-- **The Nyquist finish program.** -/
def finishProg : Prog FS (fun _ => Sym) κ.Reg :=
  .seq (liftM κ setup) (.seq (pass1 κ) (.seq (diff κ) (.seq (pass2 κ) (.seq (pass3 κ)
    (liftM κ cleanup)))))

end Program

/-! ## Closedness -/

theorem closed_liftM (κ : Kit) {p : SProg FS} (h : p.Closed) : (liftM κ p).Closed :=
  closed_liftRegs _ h

theorem finishProg_closed (κ : Kit) (hs : κ.Psub.Closed) (ha : κ.Padd.Closed)
    (hn : κ.Pneg.Closed) (hf : κ.Pshr.Closed) : (finishProg κ).Closed := by
  have cS : ∀ a b c, (callSub κ a b c).Closed := fun _ _ _ => closed_call _ _ hs
  have cA : ∀ a b c, (callAdd κ a b c).Closed := fun _ _ _ => closed_call _ _ ha
  have cN : ∀ a, (callNeg κ a).Closed := fun _ => closed_call _ _ hn
  have cF : ∀ a b c, (callShr κ a b c).Closed := fun _ _ _ => closed_call _ _ hf
  have cM : ∀ p : SProg FS, p.Closed → (liftM κ p).Closed := fun _ h => closed_liftM κ h
  have c3 : (pass3 κ).Closed := closed_call _ _ WP.W9fM.moveEntriesProg_closed
  have hsetup : setup.Closed := by
    simp [setup, Prog.Closed, Prog.FreeBelow, pushC, copyBlock, moveBlock, moveBits, moveBitsBody,
      moveBitsDup, dupBody, pushR, popR, restoreR, skip, dec, decFix, scanLoop, scanBody, peekR]
  have hcl : cleanup.Closed := by
    simp [cleanup, Prog.Closed, Prog.FreeBelow, dropInt, dropBits, dropBody, popR, peekR]
  have mR : ∀ a b c : FS, (replInt a b c).Closed := by
    intro a b c
    simp [replInt, dropInt, moveInt, Prog.Closed, Prog.FreeBelow, dropBits, dropBody, popR, peekR,
      pushC, pushR, moveBlock, moveBits, moveBitsBody, restoreR, skip, stageB, stageBLoop]
  have mP : ∀ a b : FS, (peel a b).Closed := by
    intro a b
    simp [peel, stageA, stageALoop, Prog.Closed, Prog.FreeBelow, pushC, popR, pushR]
  have mB : ∀ a b : FS, (stageB a b).Closed := by
    intro a b
    simp [stageB, stageBLoop, Prog.Closed, Prog.FreeBelow, popR, pushR, peekR]
  have mO : ∀ a b c : FS, (moveOne a b c).Closed := by
    intro a b c
    simp [moveOne, stageA, stageALoop, stageB, stageBLoop, Prog.Closed, Prog.FreeBelow, pushC,
      popR, pushR, peekR]
  have mD : ∀ a : FS, (dropInt a).Closed := by
    intro a
    simp [dropInt, dropBits, dropBody, Prog.Closed, Prog.FreeBelow, popR, peekR]
  have mU : ∀ (e : Sym) (a : FS), (dropUntil e a).Closed := by
    intro e a
    simp [dropUntil, dropUntilLoop, Prog.Closed, Prog.FreeBelow, popR, peekR]
  have mK : ∀ a : FS, (peekR a).Closed := fun _ => by simp [Prog.Closed, Prog.FreeBelow, peekR]
  have mC : ∀ (a : FS) (x : Sym), (pushC a x).Closed := fun _ _ => by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  exact ⟨cM _ hsetup, ⟨cM _ (mK _), cS _ _ _, cM _ (mR _ _ _), cM _ (mP _ _), cS _ _ _,
    cM _ (mR _ _ _), cM _ (mB _ _), cM _ (mO _ _ _), cM _ (mK _)⟩,
    ⟨⟨cS _ _ _, cM _ (mD _), cF _ _ _, cM _ (mD _), cA _ _ _, cM _ (mD _), cF _ _ _, cM _ (mD _)⟩,
      cM _ (mP _ _), ⟨cS _ _ _, cM _ (mD _), cF _ _ _, cM _ (mD _), cA _ _ _, cM _ (mD _),
        cF _ _ _, cM _ (mD _)⟩, cM _ (mB _ _)⟩,
    ⟨cM _ (mK _), cM _ (mC _ _), cM _ (mP _ _), cA _ _ _, cM _ (mB _ _), cM _ (mC _ _), cA _ _ _,
      cM _ (mU _ _), cN _, cN _, cM _ (mK _)⟩, c3, cM _ hcl⟩

#assert_std_axioms notPool_inl notPool_inr emb_injective tri_injective tri_notPool one_injective
  ιM_injective closed_liftM finishProg_closed

end WP.W9fNF
