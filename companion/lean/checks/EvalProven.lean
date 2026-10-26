import IntMul
import Lean

/-!
# Compositional Machine-Size and Step-Depth Check (`checks/EvalProven.lean`)

Standalone post-build check (`lake env lean checks/EvalProven.lean`, about 15 s after `lake build`)
that folds control-label counts (`BitMachine.numLabels`) and per-transition operation maxima
(`IntMul.stmtMaxElemOps`, `IntMul.stmtPotential`) over the `BitMachine` syntax tree of
`IntMul.bmRunRaw IntMul.bmIntMulCore` with memoization across shared submachines. By definition in
`IntMul/TMCompiler.lean`, `BitMachine.numLabels M` is `Fintype.card M.Λ`, the cardinality of the
machine's control-label type (`IntMul.tmIntMul = (bmRunRaw bmIntMulCore).toFinTM2`).

At elaboration time, `#prove_tmIntMul_stats` adds two kernel-checked theorems:
- `EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq : (bmRunRaw bmIntMulCore).numLabels = 1041232178`
- `EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq : finTM2MaxStmtElemOps tmIntMul = 16`

The `unsafe`, `implemented_by`, and `opaque` declarations in `section MetaProver` belong to meta
code only (the elaborator that constructs the proof terms); the kernel re-checks the produced
theorems independently of how the terms were constructed, `#print axioms` reports `[propext,
Classical.choice, Quot.sound]` for both, and the expected values are asserted at the end of the file.
-/

set_option backward.isDefEq.respectTransparency false

namespace EvalProven

open IntMul Turing

def bmMaxOps (M : BitMachine) : ℕ :=
  Finset.univ.sup (fun l : M.Λ => stmtMaxElemOps (M.m l))

def bmMaxPot (M : BitMachine) : ℕ :=
  Finset.univ.sup (fun l : M.Λ => stmtPotential (M.m l))

theorem finTM2MaxStmtElemOps_toFinTM2 (M : BitMachine) :
    finTM2MaxStmtElemOps M.toFinTM2 = bmMaxOps M := by
  unfold finTM2MaxStmtElemOps bmMaxOps BitMachine.toFinTM2 mkBitFinTM2; rfl

abbrev BMStats (M : BitMachine) (n o p : ℕ) : Prop :=
  M.numLabels = n ∧ bmMaxOps M = o ∧ bmMaxPot M = p

theorem BMStats.mk_eq {M : BitMachine} {n o p : ℕ}
    (hn : M.numLabels = n) (ho : bmMaxOps M = o) (hp : bmMaxPot M = p) :
    BMStats M n o p := ⟨hn, ho, hp⟩

theorem stmtMaxElemOps_remapTapesStmt (π : TapeIdx ≃ TapeIdx) {Λ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ σ,
      stmtMaxElemOps (remapTapesStmt π q) = stmtMaxElemOps q
  | .push _ _ q => congrArg (1 + ·) (stmtMaxElemOps_remapTapesStmt π q)
  | .peek _ _ q => congrArg (1 + ·) (stmtMaxElemOps_remapTapesStmt π q)
  | .pop _ _ q => congrArg (1 + ·) (stmtMaxElemOps_remapTapesStmt π q)
  | .load _ q => congrArg (1 + ·) (stmtMaxElemOps_remapTapesStmt π q)
  | .branch _ q₁ q₂ => by
    simp [remapTapesStmt, stmtMaxElemOps,
      stmtMaxElemOps_remapTapesStmt π q₁, stmtMaxElemOps_remapTapesStmt π q₂]
  | .goto _ => rfl
  | .halt => rfl

theorem stmtMaxElemOps_redirectHaltStmt {Λ₁ Λ₂ σ : Type} (entry₂ : Λ₂) (resetReg : σ) :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ,
      stmtMaxElemOps (redirectHaltStmt entry₂ resetReg q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectHaltStmt entry₂ resetReg q)
  | .peek _ _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectHaltStmt entry₂ resetReg q)
  | .pop _ _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectHaltStmt entry₂ resetReg q)
  | .load _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectHaltStmt entry₂ resetReg q)
  | .branch _ q₁ q₂ => by
    simp [redirectHaltStmt, stmtMaxElemOps, stmtPotential,
      stmtMaxElemOps_redirectHaltStmt entry₂ resetReg q₁,
      stmtMaxElemOps_redirectHaltStmt entry₂ resetReg q₂]
  | .goto _ => rfl
  | .halt => rfl

theorem stmtMaxElemOps_liftInrStmt {Λ₁ Λ₂ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ,
      stmtMaxElemOps (liftInrStmt (Λ₁ := Λ₁) q) = stmtMaxElemOps q
  | .push _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftInrStmt q)
  | .peek _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftInrStmt q)
  | .pop _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftInrStmt q)
  | .load _ q => congrArg (1 + ·) (stmtMaxElemOps_liftInrStmt q)
  | .branch _ q₁ q₂ => by
    simp [liftInrStmt, stmtMaxElemOps,
      stmtMaxElemOps_liftInrStmt q₁, stmtMaxElemOps_liftInrStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

theorem stmtMaxElemOps_redirectLoopBodyStmt {Λ σ : Type} (init : σ) :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ σ,
      stmtMaxElemOps (redirectLoopBodyStmt init q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectLoopBodyStmt init q)
  | .peek _ _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectLoopBodyStmt init q)
  | .pop _ _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectLoopBodyStmt init q)
  | .load _ q => congrArg (1 + ·) (stmtMaxElemOps_redirectLoopBodyStmt init q)
  | .branch _ q₁ q₂ => by
    simp [redirectLoopBodyStmt, stmtMaxElemOps, stmtPotential,
      stmtMaxElemOps_redirectLoopBodyStmt init q₁,
      stmtMaxElemOps_redirectLoopBodyStmt init q₂]
  | .goto _ => rfl
  | .halt => rfl

theorem stmtMaxElemOps_liftSomeInlStmt {Λ₁ Λ₂ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ,
      stmtMaxElemOps (BitMachine.liftSomeInlStmt (Λ₂ := Λ₂) q) = stmtMaxElemOps q
  | .push _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInlStmt q)
  | .peek _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInlStmt q)
  | .pop _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInlStmt q)
  | .load _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInlStmt q)
  | .branch _ q₁ q₂ => by
    simp [BitMachine.liftSomeInlStmt, stmtMaxElemOps,
      stmtMaxElemOps_liftSomeInlStmt q₁, stmtMaxElemOps_liftSomeInlStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

theorem stmtMaxElemOps_liftSomeInrStmt {Λ₁ Λ₂ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ,
      stmtMaxElemOps (BitMachine.liftSomeInrStmt (Λ₁ := Λ₁) q) = stmtMaxElemOps q
  | .push _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInrStmt q)
  | .peek _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInrStmt q)
  | .pop _ _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInrStmt q)
  | .load _ q => congrArg (1 + ·) (stmtMaxElemOps_liftSomeInrStmt q)
  | .branch _ q₁ q₂ => by
    simp [BitMachine.liftSomeInrStmt, stmtMaxElemOps,
      stmtMaxElemOps_liftSomeInrStmt q₁, stmtMaxElemOps_liftSomeInrStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

theorem sup_univ_sum {α β : Type*} [Fintype α] [Fintype β] (f : α ⊕ β → ℕ) :
    Finset.univ.sup f =
      max (Finset.univ.sup (fun a => f (Sum.inl a)))
          (Finset.univ.sup (fun b => f (Sum.inr b))) := by
  apply le_antisymm
  · refine Finset.sup_le (fun x _ => ?_)
    cases x with
    | inl a =>
      exact le_trans (Finset.le_sup (f := fun a => f (Sum.inl a)) (Finset.mem_univ a))
        (le_max_left _ _)
    | inr b =>
      exact le_trans (Finset.le_sup (f := fun b => f (Sum.inr b)) (Finset.mem_univ b))
        (le_max_right _ _)
  · exact max_le
      (Finset.sup_le (fun a _ => Finset.le_sup (f := f) (Finset.mem_univ (Sum.inl a))))
      (Finset.sup_le (fun b _ => Finset.le_sup (f := f) (Finset.mem_univ (Sum.inr b))))

theorem sup_univ_option {α : Type*} [Fintype α] (f : Option α → ℕ) :
    Finset.univ.sup f = max (f none) (Finset.univ.sup (fun a => f (some a))) := by
  apply le_antisymm
  · refine Finset.sup_le (fun x _ => ?_)
    cases x with
    | none => exact le_max_left _ _
    | some a =>
      exact le_trans (Finset.le_sup (f := fun a => f (some a)) (Finset.mem_univ a))
        (le_max_right _ _)
  · exact max_le
      (Finset.le_sup (f := f) (Finset.mem_univ none))
      (Finset.sup_le (fun a _ => Finset.le_sup (f := f) (Finset.mem_univ (some a))))

theorem BMStats.of_remap (π : TapeIdx ≃ TapeIdx) {M : BitMachine} {n o p : ℕ}
    (h : BMStats M n o p) : BMStats (M.remap π) n o p := by
  rcases h with ⟨hn, ho, hp⟩
  refine ⟨by simpa using hn, ?_, ?_⟩
  · unfold bmMaxOps BitMachine.remap at *; dsimp only
    simp only [stmtMaxElemOps_remapTapesStmt]; exact ho
  · unfold bmMaxPot BitMachine.remap at *; dsimp only
    simp only [stmtPotential_remapTapesStmt]; exact hp

theorem BMStats.of_seq {M₁ M₂ : BitMachine} {n₁ o₁ p₁ n₂ o₂ p₂ n o p : ℕ}
    (h₁ : BMStats M₁ n₁ o₁ p₁) (h₂ : BMStats M₂ n₂ o₂ p₂)
    (hn : n₁ + n₂ = n) (ho : max p₁ o₂ = o) (hp : max p₁ p₂ = p) :
    BMStats (M₁.seq M₂) n o p := by
  rcases h₁ with ⟨hn₁, _, hp₁⟩
  rcases h₂ with ⟨hn₂, ho₂, hp₂⟩
  refine ⟨by rw [BitMachine.numLabels_seq, hn₁, hn₂, hn], ?_, ?_⟩
  · unfold bmMaxOps BitMachine.seq seqBitFinTM2 mkBitFinTM2
    dsimp only; rw [sup_univ_sum]; dsimp only
    simp only [stmtMaxElemOps_redirectHaltStmt, stmtMaxElemOps_liftInrStmt]
    change max (bmMaxPot M₁) (bmMaxOps M₂) = o; rw [hp₁, ho₂, ho]
  · unfold bmMaxPot BitMachine.seq seqBitFinTM2 mkBitFinTM2
    dsimp only; rw [sup_univ_sum]; dsimp only
    simp only [stmtPotential_redirectHaltStmt, stmtPotential_liftInrStmt]
    change max (bmMaxPot M₁) (bmMaxPot M₂) = p; rw [hp₁, hp₂, hp]

theorem BMStats.of_bmSeq {M₁ M₂ : BitMachine} {n₁ o₁ p₁ n₂ o₂ p₂ n o p : ℕ}
    (h₁ : BMStats M₁ n₁ o₁ p₁) (h₂ : BMStats M₂ n₂ o₂ p₂)
    (hn : n₁ + n₂ = n) (ho : max p₁ o₂ = o) (hp : max p₁ p₂ = p) :
    BMStats (bmSeq M₁ M₂) n o p :=
  BMStats.of_seq h₁ h₂ hn ho hp

theorem BMStats.of_loopDelimWord (kCnt : TapeIdx) {body : BitMachine} {n₁ o₁ p₁ n o p : ℕ}
    (h : BMStats body n₁ o₁ p₁)
    (hn : n₁ + 1 = n) (ho : max 5 p₁ = o) (hp : max 6 p₁ = p) :
    BMStats (body.loopDelimWord kCnt) n o p := by
  rcases h with ⟨hn₁, _, hp₁⟩
  refine ⟨by rw [BitMachine.numLabels_loopDelimWord, hn₁, hn], ?_, ?_⟩
  · unfold bmMaxOps BitMachine.loopDelimWord
    dsimp only; rw [sup_univ_option]; dsimp only [stmtMaxElemOps]
    simp only [stmtMaxElemOps_redirectLoopBodyStmt]
    change max 5 (bmMaxPot body) = o; rw [hp₁, ho]
  · unfold bmMaxPot BitMachine.loopDelimWord
    dsimp only; rw [sup_univ_option]; dsimp only [stmtPotential]
    simp only [stmtPotential_redirectLoopBodyStmt]
    change max 6 (bmMaxPot body) = p; rw [hp₁, hp]

theorem BMStats.of_branchDelimBit (kCond : TapeIdx) {Mf Mt : BitMachine}
    {nf of_ pf nt ot pt n o p : ℕ}
    (hf : BMStats Mf nf of_ pf) (ht : BMStats Mt nt ot pt)
    (hn : nf + nt + 1 = n) (ho : max 7 (max of_ ot) = o) (hp : max 7 (max pf pt) = p) :
    BMStats (BitMachine.branchDelimBit kCond Mf Mt) n o p := by
  rcases hf with ⟨hnf, hof, hpf⟩
  rcases ht with ⟨hnt, hot, hpt⟩
  refine ⟨by rw [BitMachine.numLabels_branchDelimBit, hnf, hnt, hn], ?_, ?_⟩
  · unfold bmMaxOps BitMachine.branchDelimBit
    dsimp only; rw [sup_univ_option, sup_univ_sum]; dsimp only [stmtMaxElemOps]
    simp only [stmtMaxElemOps_liftSomeInlStmt, stmtMaxElemOps_liftSomeInrStmt]
    change max 7 (max (bmMaxOps Mf) (bmMaxOps Mt)) = o; rw [hof, hot, ho]
  · unfold bmMaxPot BitMachine.branchDelimBit
    dsimp only; rw [sup_univ_option, sup_univ_sum]; dsimp only [stmtPotential]
    simp only [stmtPotential_liftSomeInlStmt, stmtPotential_liftSomeInrStmt]
    change max 7 (max (bmMaxPot Mf) (bmMaxPot Mt)) = p; rw [hpf, hpt, hp]

theorem BMStats.of_loopNonEmptyWord (kList : TapeIdx) {body : BitMachine} {n₁ o₁ p₁ n o p : ℕ}
    (h : BMStats body n₁ o₁ p₁)
    (hn : n₁ + 1 = n) (ho : max 7 p₁ = o) (hp : max 7 p₁ = p) :
    BMStats (body.loopNonEmptyWord kList) n o p := by
  rcases h with ⟨hn₁, _, hp₁⟩
  refine ⟨by rw [BitMachine.numLabels_loopNonEmptyWord, hn₁, hn], ?_, ?_⟩
  · unfold bmMaxOps BitMachine.loopNonEmptyWord
    dsimp only; rw [sup_univ_option]; dsimp only [stmtMaxElemOps]
    simp only [stmtMaxElemOps_redirectLoopBodyStmt]
    change max 7 (bmMaxPot body) = o; rw [hp₁, ho]
  · unfold bmMaxPot BitMachine.loopNonEmptyWord
    dsimp only; rw [sup_univ_option]; dsimp only [stmtPotential]
    simp only [stmtPotential_redirectLoopBodyStmt]
    change max 7 (bmMaxPot body) = p; rw [hp₁, hp]

theorem BMStats_bmUnaryZero : BMStats bmUnaryZero 2 6 6 := ⟨rfl, rfl, rfl⟩
theorem BMStats_bmUnarySucc : BMStats bmUnarySucc 1 3 4 := ⟨rfl, rfl, rfl⟩

theorem BMStats.of_bmUnaryConst (c n : ℕ) (hn : c + 2 = n) :
    BMStats (bmUnaryConst c) n 6 6 := by
  subst hn
  induction c with
  | zero => exact BMStats_bmUnaryZero
  | succ c ih => exact BMStats.of_bmSeq ih BMStats_bmUnarySucc (by omega) rfl rfl

section MetaProver
open Lean Meta Elab Command

structure ProverState where
  cache : Std.HashMap Expr (Nat × Nat × Nat × Name) := {}
  nextIdx : Nat := 0

def mkNatEqRefl (k : Nat) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkNatLit k)

unsafe def evalPrimitiveStats (e : Expr) : MetaM (Nat × Nat × Nat) := do
  let nExpr ← mkAppM ``BitMachine.numLabels #[e]
  let oExpr ← mkAppM ``bmMaxOps #[e]
  let pExpr ← mkAppM ``bmMaxPot #[e]
  let n ← evalExpr Nat (mkConst ``Nat) nExpr
  let o ← evalExpr Nat (mkConst ``Nat) oExpr
  let p ← evalExpr Nat (mkConst ``Nat) pExpr
  return (n, o, p)

unsafe def saveAuxThm (e : Expr) (n o p : Nat) (proof : Expr) :
    StateRefT ProverState MetaM (Nat × Nat × Nat × Name) := do
  let st ← get
  let thmName := Name.mkSimple s!"_bmstats_aux_{st.nextIdx}"
  set { st with nextIdx := st.nextIdx + 1 }
  let thmType ← mkAppM ``BMStats #[e, mkNatLit n, mkNatLit o, mkNatLit p]
  addDecl (.thmDecl {
    name := thmName
    levelParams := []
    type := thmType
    value := proof
  })
  modify fun s => { s with cache := s.cache.insert e (n, o, p, thmName) }
  return (n, o, p, thmName)

unsafe def proveBMStatsAux (e : Expr) :
    StateRefT ProverState MetaM (Nat × Nat × Nat × Name) := do
  if let some res := (← get).cache.get? e then
    return res
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``BitMachine.remap && args.size == 2 then
    let π := args[0]!
    let M := args[1]!
    let (n, o, p, hM) ← proveBMStatsAux M
    let prf ← mkAppM ``BMStats.of_remap #[π, mkConst hM]
    saveAuxThm e n o p prf
  else if (fn.isConstOf ``BitMachine.seq || fn.isConstOf ``IntMul.bmSeq) && args.size == 2 then
    let M1 := args[0]!
    let M2 := args[1]!
    let (n1, _, p1, h1) ← proveBMStatsAux M1
    let (n2, o2, p2, h2) ← proveBMStatsAux M2
    let n := n1 + n2
    let o := Nat.max p1 o2
    let p := Nat.max p1 p2
    let lem := if fn.isConstOf ``BitMachine.seq then ``BMStats.of_seq else ``BMStats.of_bmSeq
    let prf ← mkAppM lem #[mkConst h1, mkConst h2, mkNatEqRefl n, mkNatEqRefl o, mkNatEqRefl p]
    saveAuxThm e n o p prf
  else if fn.isConstOf ``BitMachine.loopDelimWord && args.size == 2 then
    let kCnt := args[0]!
    let body := args[1]!
    let (n1, _, p1, h1) ← proveBMStatsAux body
    let n := n1 + 1
    let o := Nat.max 5 p1
    let p := Nat.max 6 p1
    let prf ← mkAppM ``BMStats.of_loopDelimWord #[kCnt, mkConst h1, mkNatEqRefl n, mkNatEqRefl o, mkNatEqRefl p]
    saveAuxThm e n o p prf
  else if fn.isConstOf ``BitMachine.branchDelimBit && args.size == 3 then
    let kCond := args[0]!
    let Mf := args[1]!
    let Mt := args[2]!
    let (nf, of_, pf, hf) ← proveBMStatsAux Mf
    let (nt, ot, pt, ht) ← proveBMStatsAux Mt
    let n := nf + nt + 1
    let o := Nat.max 7 (Nat.max of_ ot)
    let p := Nat.max 7 (Nat.max pf pt)
    let prf ← mkAppM ``BMStats.of_branchDelimBit #[kCond, mkConst hf, mkConst ht, mkNatEqRefl n, mkNatEqRefl o, mkNatEqRefl p]
    saveAuxThm e n o p prf
  else if fn.isConstOf ``BitMachine.loopNonEmptyWord && args.size == 2 then
    let kList := args[0]!
    let body := args[1]!
    let (n1, _, p1, h1) ← proveBMStatsAux body
    let n := n1 + 1
    let o := Nat.max 7 p1
    let p := Nat.max 7 p1
    let prf ← mkAppM ``BMStats.of_loopNonEmptyWord #[kList, mkConst h1, mkNatEqRefl n, mkNatEqRefl o, mkNatEqRefl p]
    saveAuxThm e n o p prf
  else if fn.isConstOf ``IntMul.bmUnaryConst && args.size == 1 then
    let cExpr := args[0]!
    let c ← evalExpr Nat (mkConst ``Nat) cExpr
    let n := c + 2
    let prf ← mkAppM ``BMStats.of_bmUnaryConst #[cExpr, mkNatLit n, mkNatEqRefl n]
    saveAuxThm e n 6 6 prf
  else if fn.isConstOf ``BitMachine.mk || fn.isConstOf ``BitMachine.ofButterflyDelim || fn.isConstOf ``BitMachine.ofUniformDelim then
    let (n, o, p) ← evalPrimitiveStats e
    let prf ← mkAppOptM ``BMStats.mk_eq #[some e, some (mkNatLit n), some (mkNatLit o), some (mkNatLit p),
      some (mkNatEqRefl n), some (mkNatEqRefl o), some (mkNatEqRefl p)]
    saveAuxThm e n o p prf
  else if let .letE _ _ val body _ := e then
    let e' := body.instantiate1 val
    let (n, o, p, h') ← proveBMStatsAux e'
    saveAuxThm e n o p (mkConst h')
  else if e.isHeadBetaTarget then
    let e' := e.headBeta
    let (n, o, p, h') ← proveBMStatsAux e'
    saveAuxThm e n o p (mkConst h')
  else if let some e' ← unfoldDefinition? e then
    let (n, o, p, h') ← proveBMStatsAux e'
    saveAuxThm e n o p (mkConst h')
  else
    let e' ← whnfCore e
    if e' != e then
      let (n, o, p, h') ← proveBMStatsAux e'
      saveAuxThm e n o p (mkConst h')
    else
      throwError "Cannot analyze BitMachine expression: {e}"

unsafe def elabProveBMStatsImpl : CommandElabM Unit := do
  liftTermElabM do
    let target ← mkAppM ``IntMul.bmRunRaw #[mkConst ``IntMul.bmIntMulCore]
    let ((n, o, p, hName), st) ← proveBMStatsAux target |>.run {}
    logInfo m!"DAG nodes proved in kernel: {st.nextIdx}"
    for nm in [``IntMul.bmMulTier0, ``IntMul.bmMulTier1, ``IntMul.bmMulTier2, ``IntMul.bmIntMulCore] do
      if let some (ni, oi, pi, _) := st.cache.get? (mkConst nm) then
        logInfo m!"{nm}: numLabels = {ni}, maxOps = {oi}, maxPot = {pi}"
    logInfo m!"(IntMul.bmRunRaw IntMul.bmIntMulCore).numLabels = {n}"
    logInfo m!"IntMul.finTM2MaxStmtElemOps IntMul.tmIntMul = {o}"
    logInfo m!"bmMaxPot (IntMul.bmRunRaw IntMul.bmIntMulCore) = {p}"
    let thm1Type ← mkEq (← mkAppM ``BitMachine.numLabels #[target]) (mkNatLit n)
    let thm1Val ← mkAppM ``And.left #[mkConst hName]
    addDecl (.thmDecl {
      name := `EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq
      levelParams := []
      type := thm1Type
      value := thm1Val
    })
    let tmExpr := mkConst ``IntMul.tmIntMul
    let lhs2 ← mkAppM ``IntMul.finTM2MaxStmtElemOps #[tmExpr]
    let thm2Type ← mkEq lhs2 (mkNatLit o)
    let hBridge ← mkAppM ``finTM2MaxStmtElemOps_toFinTM2 #[target]
    let hMid ← mkAppM ``And.left #[← mkAppM ``And.right #[mkConst hName]]
    let thm2Val ← mkEqTrans hBridge hMid
    addDecl (.thmDecl {
      name := `EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq
      levelParams := []
      type := thm2Type
      value := thm2Val
    })

@[implemented_by elabProveBMStatsImpl]
opaque elabProveBMStats : CommandElabM Unit

elab "#prove_tmIntMul_stats" : command => elabProveBMStats

end MetaProver

#prove_tmIntMul_stats
#eval IntMul.C_tm_total
#check EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq
#check EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq
#print axioms EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq
#print axioms EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq
example : (bmRunRaw bmIntMulCore).numLabels = 1041232178 := EvalProven.numLabels_bmRunRaw_bmIntMulCore_eq
example : finTM2MaxStmtElemOps tmIntMul = 16 := EvalProven.finTM2MaxStmtElemOps_tmIntMul_eq

end EvalProven
