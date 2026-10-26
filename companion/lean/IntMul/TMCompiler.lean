import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.TMPrimitives
import IntMul.TMComposition

set_option backward.isDefEq.respectTransparency false

/-!
# Delimited Word-Stack Functor & Compositional `FinTM2` Compiler Infrastructure (`IntMul.TMCompiler`)

This module builds the universal 1-step-preserving delimited word-stack functor (`liftDelimTM`) and
the bundled 8-stack binary machine combinator algebra (`BitMachine`) over the 32-state
register `DelimReg := ButterflyReg × Bool` (`|σ| = 32`, `|Γ k| = 2`, Section 8 (`sec:lean`)):

1. **Self-Delimiting Bit-Word & Word-Stack Encoding (`encodeDelimWord`, `encodeWordStack`,
   `embedDelimFrame`)**:
   - Encodes any bit-word `w : List Bool` as `encodeDelimWord w` (`[] ↦ [true, false]`,
     `b :: xs ↦ false :: b :: encodeDelimWord xs`) of length `2 * w.length + 2`.
   - Encodes a stack of bit-words `ws : List (List Bool)` on a stack as `encodeWordStack ws`, so that
     `encodeWordStack (w :: ws) = encodeDelimWord w ++ encodeWordStack ws`.

2. **Universal 1-Step-Preserving Delimited-Frame Functor (`liftDelimStmt`, `liftDelimTM`)**:
   - Lifts any 8-stack binary `FinTM2` machine over `ButterflyReg` (or `UniformReg` via
     `liftUniformRegStmt`) to operate on the top delimited word `encodeDelimWord (stk k)` of each
     of the 8 stacks while leaving arbitrary deeper stack contents `rest k` (`encodeWordStack (ws k)`)
     on all 8 stacks untouched in the **exact same step count `t`** (`stepAux_liftDelimStmt`,
     `liftDelimTM_evalsToInTime_concrete`).

3. **Bundled `BitMachine` Algebra & Word-Stack Combinators (`BitMachine`, `BitMachine.seq`,
   `BitMachine.remap`, `BitMachine.loopDelimWord`, `BitMachine.branchDelimBit`)**:
   - Provides a uniform machine bundle `BitMachine` over `DelimReg` (`|σ| = 32`) with compositional
     step-bound specification `BitMachine.ComputesInTime`.
   - Implements word-stack allocation/deallocation (`tmPushEmpty`, `tmDropWord`, `tmFramePush7`,
     `tmFramePush6`, `tmFramePop7`), word-stack transfers and duplication (`tmRevMoveWord`,
     `tmMoveWord`, `tmDupWord`), raw-to-delimited front/back-end conversions (`tmRawToDelimRev`,
     `tmDelimRevToRaw`, `tmDelimIOToRawIO`), and state-indexed loop evaluation
     (`loopFinalState`, `loopStepsAux`, `BitMachine.ComputesInTime.loopDelimWord_state`).
-/

namespace IntMul

open Turing

/-! ## 1. Self-Delimiting Word & Word-Stack Encoding (`encodeDelimWord`, `encodeWordStack`) -/

/-- Self-delimiting binary encoding of a bit-word `w : List Bool` on a binary stack (`Γ k = Bool`):
each data bit `b` is prefixed by `false` (`false :: b`), and the end-of-word marker is `[true, false]`. -/
def encodeDelimWord : List Bool → List Bool
  | [] => [true, false]
  | b :: xs => false :: b :: encodeDelimWord xs

@[simp]
theorem encodeDelimWord_nil : encodeDelimWord [] = [true, false] := rfl

@[simp]
theorem encodeDelimWord_cons (b : Bool) (xs : List Bool) :
    encodeDelimWord (b :: xs) = false :: b :: encodeDelimWord xs := rfl

@[simp]
theorem length_encodeDelimWord (xs : List Bool) :
    (encodeDelimWord xs).length = 2 * xs.length + 2 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [encodeDelimWord, List.length_cons, ih]
    ring

/-- Encode a stack of bit-words `ws : List (List Bool)` on a single binary stack by concatenating
their self-delimiting encodings from top of stack to bottom of stack. -/
def encodeWordStack : List (List Bool) → List Bool
  | [] => []
  | w :: ws => encodeDelimWord w ++ encodeWordStack ws

@[simp]
theorem encodeWordStack_nil : encodeWordStack [] = [] := rfl

@[simp]
theorem encodeWordStack_cons (w : List Bool) (ws : List (List Bool)) :
    encodeWordStack (w :: ws) = encodeDelimWord w ++ encodeWordStack ws := rfl

@[simp]
theorem encodeWordStack_append (ws₁ ws₂ : List (List Bool)) :
    encodeWordStack (ws₁ ++ ws₂) = encodeWordStack ws₁ ++ encodeWordStack ws₂ := by
  induction ws₁ with
  | nil => rfl
  | cons w ws₁ ih =>
    simp only [List.cons_append, encodeWordStack_cons, ih, List.append_assoc]

/-- Embed an 8-stack top-word assignment `stk : ∀ k : TapeIdx, List Bool` above an arbitrary 8-stack
background stack `rest : ∀ k : TapeIdx, List Bool`. -/
def embedDelimFrame (stk rest : ∀ k : TapeIdx, List (BitTapeAlphabet k)) :
    ∀ k : TapeIdx, List (BitTapeAlphabet k) :=
  fun k => encodeDelimWord (stk k) ++ rest k

@[simp]
theorem embedDelimFrame_apply (stk rest : ∀ k : TapeIdx, List (BitTapeAlphabet k)) (k : TapeIdx) :
    embedDelimFrame stk rest k = encodeDelimWord (stk k) ++ rest k := rfl

theorem update_embedDelimFrame (stk rest : ∀ k : TapeIdx, List (BitTapeAlphabet k))
    (k : TapeIdx) (w : List Bool) :
    Function.update (embedDelimFrame stk rest) k (encodeDelimWord w ++ rest k) =
      embedDelimFrame (Function.update stk k w) rest := by
  funext k'
  by_cases hk : k' = k
  · subst hk
    simp [embedDelimFrame]
  · simp [embedDelimFrame, hk]

theorem update_embedDelimFrame_cons (stk rest : ∀ k : TapeIdx, List (BitTapeAlphabet k))
    (k : TapeIdx) (b : Bool) (w : List Bool) :
    Function.update (embedDelimFrame stk rest) k (false :: b :: (encodeDelimWord w ++ rest k)) =
      embedDelimFrame (Function.update stk k (b :: w)) rest := by
  rw [← List.cons_append, ← List.cons_append, ← encodeDelimWord_cons]
  exact update_embedDelimFrame stk rest k (b :: w)

/-! ## 2. Universal 1-Step-Preserving Delimited-Frame Functor (`liftDelimStmt`, `liftDelimTM`) -/

/-- Shared 5-bit ($32$-state) internal register for delimited 8-stack binary machines (`Turing.FinTM2`):
combines `ButterflyReg` ($16$ states) with a 1-bit delimiter tag flag (`Bool`). -/
abbrev DelimReg : Type := ButterflyReg × Bool

@[simp]
theorem card_delimReg : Fintype.card DelimReg = 32 := by decide

@[simp]
theorem delimReg_default : (default : DelimReg) = (default, false) := rfl

/-- Lift any `Turing.TM2.Stmt` over `ButterflyReg` to operate on the top delimited word
`encodeDelimWord (stk k)` of each stack while leaving the deeper stack contents `rest k` untouched
in a single `stepAux` transition. -/
def liftDelimStmt {Λ : Type} :
    Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg →
      Turing.TM2.Stmt BitTapeAlphabet Λ DelimReg
  | .push k f q =>
    .push k (fun rv => f rv.1)
      (.push k (fun _ => false) (liftDelimStmt q))
  | .peek k f q =>
    .pop k (fun rv bOpt => (rv.1, bOpt.getD true))
      (.branch (fun rv => rv.2)
        (.push k (fun _ => true)
          (.load (fun rv => (f rv.1 none, false)) (liftDelimStmt q)))
        (.peek k (fun rv bOpt => (f rv.1 bOpt, false))
          (.push k (fun _ => false) (liftDelimStmt q))))
  | .pop k f q =>
    .pop k (fun rv bOpt => (rv.1, bOpt.getD true))
      (.branch (fun rv => rv.2)
        (.push k (fun _ => true)
          (.load (fun rv => (f rv.1 none, false)) (liftDelimStmt q)))
        (.pop k (fun rv bOpt => (f rv.1 bOpt, false)) (liftDelimStmt q)))
  | .load a q =>
    .load (fun rv => (a rv.1, false)) (liftDelimStmt q)
  | .branch p q₁ q₂ =>
    .branch (fun rv => p rv.1) (liftDelimStmt q₁) (liftDelimStmt q₂)
  | .goto l =>
    .goto (fun rv => l rv.1)
  | .halt => .halt

/-- Map a `ButterflyReg` configuration to a `DelimReg` configuration with background frame `rest`. -/
def mapDelimFrameCfg {Λ : Type} (rest : ∀ k : TapeIdx, List (BitTapeAlphabet k))
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ ButterflyReg) :
    Turing.TM2.Cfg BitTapeAlphabet Λ DelimReg :=
  ⟨cfg.l, (cfg.var, false), embedDelimFrame cfg.stk rest⟩

/-- **Exact 1-Step Frame-Preserving Simulation Theorem (`stepAux_liftDelimStmt`)**:
For every statement `q`, register `v : ButterflyReg`, active top-word assignment `stk`, and
background stack `rest`, `stepAux (liftDelimStmt q) (v, false) (embedDelimFrame stk rest)` equals
`mapDelimFrameCfg rest (stepAux q v stk)`. -/
theorem stepAux_liftDelimStmt {Λ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg) (v : ButterflyReg)
      (stk rest : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (liftDelimStmt q) (v, false) (embedDelimFrame stk rest) =
        mapDelimFrameCfg rest (Turing.TM2.stepAux q v stk)
  | .push k f q, v, stk, rest => by
    dsimp [liftDelimStmt, Turing.TM2.stepAux]
    rw [Function.update_idem, Function.update_self, update_embedDelimFrame_cons]
    exact stepAux_liftDelimStmt q v (Function.update stk k (f v :: stk k)) rest
  | .peek k f q, v, stk, rest => by
    dsimp [liftDelimStmt, Turing.TM2.stepAux]
    cases hstk : stk k with
    | nil =>
      have htop : embedDelimFrame stk rest k = true :: false :: rest k := by
        simp [embedDelimFrame, hstk]
      have hrestore :
          Function.update (Function.update (embedDelimFrame stk rest) k (false :: rest k)) k
            (true :: false :: rest k) = embedDelimFrame stk rest := by
        rw [Function.update_idem, ← htop, Function.update_eq_self]
      simp only [encodeDelimWord_nil, List.cons_append, List.nil_append,
        List.head?_cons, List.head?_nil, List.tail_cons, Option.getD_some, cond_true,
        Function.update_self, hrestore]
      exact stepAux_liftDelimStmt q (f v none) stk rest
    | cons b xs =>
      have htop : embedDelimFrame stk rest k = false :: b :: (encodeDelimWord xs ++ rest k) := by
        simp [embedDelimFrame, hstk]
      have hrestore :
          Function.update (Function.update (embedDelimFrame stk rest) k
            (b :: (encodeDelimWord xs ++ rest k))) k
            (false :: b :: (encodeDelimWord xs ++ rest k)) = embedDelimFrame stk rest := by
        rw [Function.update_idem, ← htop, Function.update_eq_self]
      simp only [encodeDelimWord_cons, List.cons_append,
        List.head?_cons, List.tail_cons, Option.getD_some, cond_false,
        Function.update_self, hrestore]
      exact stepAux_liftDelimStmt q (f v (some b)) stk rest
  | .pop k f q, v, stk, rest => by
    dsimp [liftDelimStmt, Turing.TM2.stepAux]
    cases hstk : stk k with
    | nil =>
      have hrestore :
          Function.update (Function.update (embedDelimFrame stk rest) k (false :: rest k)) k
            (true :: false :: rest k) =
            embedDelimFrame (Function.update stk k []) rest := by
        rw [Function.update_idem]
        exact update_embedDelimFrame stk rest k []
      simp only [encodeDelimWord_nil, List.cons_append, List.nil_append,
        List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
        Option.getD_some, cond_true, Function.update_self, hrestore]
      exact stepAux_liftDelimStmt q (f v none) (Function.update stk k []) rest
    | cons b xs =>
      have hupd :
          Function.update (Function.update (embedDelimFrame stk rest) k
            (b :: (encodeDelimWord xs ++ rest k))) k (encodeDelimWord xs ++ rest k) =
            embedDelimFrame (Function.update stk k xs) rest := by
        rw [Function.update_idem]
        exact update_embedDelimFrame stk rest k xs
      simp only [encodeDelimWord_cons, List.cons_append,
        List.head?_cons, List.tail_cons, Option.getD_some, cond_false,
        Function.update_self, hupd]
      exact stepAux_liftDelimStmt q (f v (some b)) (Function.update stk k xs) rest
  | .load a q, v, stk, rest => by
    dsimp [liftDelimStmt, Turing.TM2.stepAux]
    exact stepAux_liftDelimStmt q (a v) stk rest
  | .branch p q₁ q₂, v, stk, rest => by
    dsimp [liftDelimStmt, Turing.TM2.stepAux]
    cases p v <;> simp [stepAux_liftDelimStmt]
  | .goto l, v, stk, rest => rfl
  | .halt, v, stk, rest => rfl

/-- Lift an 8-stack binary `Turing.FinTM2` machine over `ButterflyReg` to `DelimReg` (`|σ| = 32`). -/
def liftDelimTM (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg) : Turing.FinTM2 :=
  mkBitFinTM2 Λ main DelimReg default (fun l => liftDelimStmt (m l))

theorem isUniformFinTM2_liftDelimTM {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg)
    {maxLabels : ℕ} (hΛ : Fintype.card Λ ≤ maxLabels) :
    IsUniformFinTM2 (liftDelimTM Λ main m) maxLabels 32 2 :=
  isUniformFinTM2_mkBitFinTM2 main default _ hΛ (by decide) (by decide)

theorem step_liftDelimTM {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg)
    (rest : ∀ k : TapeIdx, List (BitTapeAlphabet k))
    (x y : (mkBitFinTM2 Λ main ButterflyReg default m).Cfg)
    (h : (mkBitFinTM2 Λ main ButterflyReg default m).step x = some y) :
    (liftDelimTM Λ main m).step (mapDelimFrameCfg rest x) =
      some (mapDelimFrameCfg rest y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [liftDelimTM, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, mapDelimFrameCfg]
    exact congrArg some (stepAux_liftDelimStmt (m l) v stk rest)

/-- Constructive step-bound lifting for `liftDelimTM` preserving arbitrary background stacks `rest`
in the exact same step bound `t`. -/
def liftDelimTM_evalsToInTime_concrete {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg)
    (rest : ∀ k : TapeIdx, List (BitTapeAlphabet k))
    {cfg₁ cfg₂ : (mkBitFinTM2 Λ main ButterflyReg default m).Cfg} {t : ℕ}
    (h : Turing.EvalsToInTime (mkBitFinTM2 Λ main ButterflyReg default m).step
      cfg₁ (some cfg₂) t) :
    Turing.EvalsToInTime (liftDelimTM Λ main m).step
      (mapDelimFrameCfg rest cfg₁) (some (mapDelimFrameCfg rest cfg₂)) t :=
  EvalsToInTime.map_simulation (mapDelimFrameCfg rest) (step_liftDelimTM main m rest) h

/-! ## 3. Bundled `BitMachine` Combinator Algebra over `DelimReg` (`|σ| = 32`) -/

/-- Bundled uniform 8-stack binary machine over the fixed 32-state register `DelimReg`
(`ButterflyReg × Bool`, Section 8 (`sec:lean`)). -/
structure BitMachine where
  /-- Finite control label type. -/
  Λ : Type
  /-- Finiteness instance for control labels. -/
  [instFintypeΛ : Fintype Λ]
  /-- Entry control label. -/
  main : Λ
  /-- Transition table over `BitTapeAlphabet` (`Bool`) and `DelimReg` (`|σ| = 32`). -/
  m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ DelimReg

attribute [instance] BitMachine.instFintypeΛ

namespace BitMachine

/-- Convert a `BitMachine` to Mathlib's `Turing.FinTM2`. -/
def toFinTM2 (M : BitMachine) : Turing.FinTM2 :=
  mkBitFinTM2 M.Λ M.main DelimReg default M.m

/-- Number of control labels of `M`. -/
def numLabels (M : BitMachine) : ℕ :=
  Fintype.card M.Λ

/-- Every `BitMachine` is a uniform 8-stack binary `FinTM2` with `|Λ| ≤ maxLabels`, `|σ| ≤ 32`,
and `|Γ k| = 2` (Section 8 (`sec:lean`)). -/
theorem isUniform (M : BitMachine) {maxLabels : ℕ} (hΛ : M.numLabels ≤ maxLabels) :
    IsUniformFinTM2 M.toFinTM2 maxLabels 32 2 :=
  isUniformFinTM2_mkBitFinTM2 M.main default M.m hΛ (by decide) (by decide)

/-- Step-bounded evaluation relation for a `BitMachine` starting at `(some M.main, default, T₁)`
and halting at `(none, default, T₂)` in at most `t` steps. -/
def ComputesInTime (M : BitMachine)
    (T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)) (t : ℕ) : Prop :=
  Nonempty (Turing.EvalsToInTime M.toFinTM2.step
    ⟨some M.main, default, T₁⟩ (some ⟨none, default, T₂⟩) t)

theorem ComputesInTime.mono {M : BitMachine}
    {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {t t' : ℕ}
    (h : M.ComputesInTime T₁ T₂ t) (hle : t ≤ t') :
    M.ComputesInTime T₁ T₂ t' := by
  rcases h with ⟨heval⟩
  exact ⟨EvalsToInTime.mono heval hle⟩

theorem ComputesInTime.to_evalsToInTime_init_halt {M : BitMachine}
    {xs ys : List Bool} {t : ℕ}
    (h : M.ComputesInTime (Turing.initList M.toFinTM2 xs).stk
      (Turing.haltList M.toFinTM2 ys).stk t) :
    ∃ s ≤ t,
      Turing.EvalsToInTime M.toFinTM2.step
        (Turing.initList M.toFinTM2 xs)
        (some (Turing.haltList M.toFinTM2 ys)) s :=
  let ⟨heval⟩ := h
  ⟨t, le_rfl, ⟨heval⟩⟩

/-- Embed a `ButterflyReg` machine into `BitMachine` as a delimited-frame machine operating on the
top delimited word of each stack (`liftDelimTM`). -/
def ofButterflyDelim (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg) : BitMachine where
  Λ := Λ
  main := main
  m := fun l => liftDelimStmt (m l)

@[simp]
theorem numLabels_ofButterflyDelim (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg) :
    (ofButterflyDelim Λ main m).numLabels = Fintype.card Λ := rfl

theorem ofButterflyDelim_computesInTime {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg)
    {stk₁ stk₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)}
    (rest : ∀ k : TapeIdx, List (BitTapeAlphabet k)) {t : ℕ}
    (h : Turing.EvalsToInTime (mkBitFinTM2 Λ main ButterflyReg default m).step
      ⟨some main, default, stk₁⟩ (some ⟨none, default, stk₂⟩) t) :
    (ofButterflyDelim Λ main m).ComputesInTime
      (embedDelimFrame stk₁ rest) (embedDelimFrame stk₂ rest) t :=
  ⟨liftDelimTM_evalsToInTime_concrete main m rest h⟩

/-- Embed a `UniformReg` machine into `BitMachine` as a delimited-frame machine operating on the
top delimited word of each stack (`liftDelimStmt ∘ liftUniformRegStmt`). -/
def ofUniformDelim (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg) : BitMachine :=
  ofButterflyDelim Λ main (fun l => liftUniformRegStmt (m l))

@[simp]
theorem numLabels_ofUniformDelim (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg) :
    (ofUniformDelim Λ main m).numLabels = Fintype.card Λ := rfl

theorem ofUniformDelim_computesInTime {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg)
    {stk₁ stk₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)}
    (rest : ∀ k : TapeIdx, List (BitTapeAlphabet k)) {t : ℕ}
    (h : Turing.EvalsToInTime (mkBitFinTM2 Λ main UniformReg default m).step
      ⟨some main, default, stk₁⟩ (some ⟨none, default, stk₂⟩) t) :
    (ofUniformDelim Λ main m).ComputesInTime
      (embedDelimFrame stk₁ rest) (embedDelimFrame stk₂ rest) t :=
  ofButterflyDelim_computesInTime main (fun l => liftUniformRegStmt (m l)) rest
    (liftUniformRegTM_evalsToInTime_default_concrete main m h)

/-- Relocate a `BitMachine` across a stack-index bijection `π : TapeIdx ≃ TapeIdx` (`remapTapesTM`). -/
def remap (π : TapeIdx ≃ TapeIdx) (M : BitMachine) : BitMachine where
  Λ := M.Λ
  main := M.main
  m := fun l => remapTapesStmt π (M.m l)

@[simp]
theorem numLabels_remap (π : TapeIdx ≃ TapeIdx) (M : BitMachine) :
    (M.remap π).numLabels = M.numLabels := rfl

theorem ComputesInTime.remap (π : TapeIdx ≃ TapeIdx) {M : BitMachine}
    {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {t : ℕ}
    (h : M.ComputesInTime T₁ T₂ t) :
    (M.remap π).ComputesInTime (remapStk π T₁) (remapStk π T₂) t := by
  rcases h with ⟨heval⟩
  exact ⟨remapTapesTM_evalsToInTime_concrete π M.main default M.m heval⟩

/-- Sequential composition of two `BitMachine`s (`seqBitFinTM2`). -/
def seq (M₁ M₂ : BitMachine) : BitMachine where
  Λ := M₁.Λ ⊕ M₂.Λ
  main := Sum.inl M₁.main
  m := (seqBitFinTM2 M₁.Λ M₁.main M₂.Λ M₂.main DelimReg default default M₁.m M₂.m).m

@[simp]
theorem numLabels_seq (M₁ M₂ : BitMachine) :
    (M₁.seq M₂).numLabels = M₁.numLabels + M₂.numLabels :=
  Fintype.card_sum

theorem ComputesInTime.seq {M₁ M₂ : BitMachine}
    {T₁ T₂ T₃ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {t₁ t₂ : ℕ}
    (h₁ : M₁.ComputesInTime T₁ T₂ t₁)
    (h₂ : M₂.ComputesInTime T₂ T₃ t₂) :
    (M₁.seq M₂).ComputesInTime T₁ T₃ (t₁ + t₂) := by
  rcases h₁ with ⟨heval₁⟩
  rcases h₂ with ⟨heval₂⟩
  exact ⟨seqBitFinTM2_evalsToInTime_concrete M₁.main M₂.main default default M₁.m M₂.m
    heval₁ heval₂⟩

/-- **Delimited Counter-Word Loop Combinator (`BitMachine.loopDelimWord`)**:
Iterates `body : BitMachine` once per bit of the top delimited word `cnt : List Bool` on stack
`kCnt : TapeIdx` (`encodeDelimWord cnt ++ rest` on `kCnt`), and upon reaching the end-of-word
delimiter `[true, false]` of `cnt`, consumes `[true, false]` and halts with `rest` exposed on
`kCnt`.
- At header `none : Option body.Λ`, pops 2 bits from `kCnt`:
  - If `cnt = b :: cnt'`, the top 2 bits of `encodeDelimWord (b :: cnt') ++ rest` are `false, b`,
    leaving `encodeDelimWord cnt' ++ rest` on `kCnt` and jumping to `some body.main`.
  - If `cnt = []`, the top 2 bits of `encodeDelimWord [] ++ rest` are `true, false`, leaving `rest`
    on `kCnt` and halting. -/
def loopDelimWord (kCnt : TapeIdx) (body : BitMachine) : BitMachine where
  Λ := Option body.Λ
  main := none
  m := fun lbl =>
    match lbl with
    | none =>
      Turing.TM2.Stmt.pop kCnt
        (fun _ bOpt => (default, bOpt.getD true))
        (Turing.TM2.Stmt.pop kCnt
          (fun rv _ => rv)
          (Turing.TM2.Stmt.branch (fun rv => rv.2)
            (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
            (Turing.TM2.Stmt.load (fun _ => default)
              (Turing.TM2.Stmt.goto (fun _ => some body.main)))))
    | some l => redirectLoopBodyStmt default (body.m l)

@[simp]
theorem numLabels_loopDelimWord (kCnt : TapeIdx) (body : BitMachine) :
    (body.loopDelimWord kCnt).numLabels = body.numLabels + 1 :=
  Fintype.card_option

theorem step_loopDelimWord_body (kCnt : TapeIdx) (body : BitMachine)
    (x y : body.toFinTM2.Cfg)
    (h : body.toFinTM2.step x = some y) :
    (body.loopDelimWord kCnt).toFinTM2.step (mapLoopBodyCfg default x) =
      some (mapLoopBodyCfg default y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [loopDelimWord, toFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      mapLoopBodyCfg]
    exact congrArg some (stepAux_redirectLoopBodyStmt default (body.m l) v stk)

def loopDelimWord_body_evalsToInTime_concrete (kCnt : TapeIdx) (body : BitMachine)
    {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {B : ℕ}
    (hbody : Turing.EvalsToInTime body.toFinTM2.step
      ⟨some body.main, default, T₁⟩ (some ⟨none, default, T₂⟩) B) :
    Turing.EvalsToInTime (body.loopDelimWord kCnt).toFinTM2.step
      ⟨some (some body.main), default, T₁⟩ (some ⟨some none, default, T₂⟩) B :=
  EvalsToInTime.map_simulation (mapLoopBodyCfg default)
    (step_loopDelimWord_body kCnt body) hbody

/-- Constructive multi-pass evaluation of `BitMachine.loopDelimWord`:
Given top delimited word `cnt : List Bool` above `restCnt : List Bool` on `kCnt`, executes
`cnt.length` passes of `body` and consumes `encodeDelimWord cnt`, leaving `restCnt` on `kCnt` in
`cnt.length * (B + 1) + 1` steps. -/
def loopDelimWord_evalsToInTime_concrete (kCnt : TapeIdx) (body : BitMachine) (B : ℕ) :
    ∀ (cnt : List Bool) (restCnt : List Bool)
      (stkOf : ℕ → (∀ k : TapeIdx, List (BitTapeAlphabet k))),
      (∀ (i : ℕ) (tailCnt : List Bool),
        Turing.EvalsToInTime body.toFinTM2.step
          ⟨some body.main, default, Function.update (stkOf i) kCnt tailCnt⟩
          (some ⟨none, default, Function.update (stkOf (i + 1)) kCnt tailCnt⟩) B) →
      Turing.EvalsToInTime (body.loopDelimWord kCnt).toFinTM2.step
        ⟨some none, default,
          Function.update (stkOf 0) kCnt (encodeDelimWord cnt ++ restCnt)⟩
        (some ⟨none, default,
          Function.update (stkOf cnt.length) kCnt restCnt⟩)
        (cnt.length * (B + 1) + 1)
  | [], restCnt, stkOf, _ => by
    refine EvalsToInTime.mono (EvalsToInTime.step_one ?_) (by simp)
    simp only [loopDelimWord, toFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append, List.nil_append, List.length_nil,
      Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | b :: cnt, restCnt, stkOf, hpass => by
    have hpop : (body.loopDelimWord kCnt).toFinTM2.step
        ⟨some none, default,
          Function.update (stkOf 0) kCnt (encodeDelimWord (b :: cnt) ++ restCnt)⟩ =
        some ⟨some (some body.main), default,
          Function.update (stkOf 0) kCnt (encodeDelimWord cnt ++ restCnt)⟩ := by
      simp only [loopDelimWord, toFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux, encodeDelimWord_cons, List.cons_append,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    have hbody := hpass 0 (encodeDelimWord cnt ++ restCnt)
    have hbody_lifted := loopDelimWord_body_evalsToInTime_concrete kCnt body hbody
    have ih := loopDelimWord_evalsToInTime_concrete kCnt body B cnt restCnt
      (fun i => stkOf (i + 1)) (fun i tailCnt => hpass (i + 1) tailCnt)
    have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
    have hcomb := EvalsToInTime.trans' hstep1 ih
    simp only [List.length_cons] at hcomb ⊢
    exact EvalsToInTime.mono hcomb (by ring_nf; omega)

theorem ComputesInTime.loopDelimWord (kCnt : TapeIdx) {body : BitMachine} (B : ℕ)
    (cnt : List Bool) (restCnt : List Bool)
    (stkOf : ℕ → (∀ k : TapeIdx, List (BitTapeAlphabet k)))
    (hpass : ∀ (i : ℕ) (tailCnt : List Bool),
      body.ComputesInTime
        (Function.update (stkOf i) kCnt tailCnt)
        (Function.update (stkOf (i + 1)) kCnt tailCnt) B) :
    (body.loopDelimWord kCnt).ComputesInTime
      (Function.update (stkOf 0) kCnt (encodeDelimWord cnt ++ restCnt))
      (Function.update (stkOf cnt.length) kCnt restCnt)
      (cnt.length * (B + 1) + 1) :=
  ⟨loopDelimWord_evalsToInTime_concrete kCnt body B cnt restCnt stkOf
    (fun i tailCnt => Classical.choice (hpass i tailCnt))⟩

/-- Lift a statement over `Λ₁` into `Option (Λ₁ ⊕ Λ₂)` via `some ∘ Sum.inl`. -/
def liftSomeInlStmt {Λ₁ Λ₂ σ : Type} :
    Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ → Turing.TM2.Stmt BitTapeAlphabet (Option (Λ₁ ⊕ Λ₂)) σ
  | .push k f q => .push k f (liftSomeInlStmt q)
  | .peek k f q => .peek k f (liftSomeInlStmt q)
  | .pop k f q => .pop k f (liftSomeInlStmt q)
  | .load a q => .load a (liftSomeInlStmt q)
  | .branch p q₁ q₂ => .branch p (liftSomeInlStmt q₁) (liftSomeInlStmt q₂)
  | .goto l => .goto (fun v => some (Sum.inl (l v)))
  | .halt => .halt

/-- Lift a statement over `Λ₂` into `Option (Λ₁ ⊕ Λ₂)` via `some ∘ Sum.inr`. -/
def liftSomeInrStmt {Λ₁ Λ₂ σ : Type} :
    Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ → Turing.TM2.Stmt BitTapeAlphabet (Option (Λ₁ ⊕ Λ₂)) σ
  | .push k f q => .push k f (liftSomeInrStmt q)
  | .peek k f q => .peek k f (liftSomeInrStmt q)
  | .pop k f q => .pop k f (liftSomeInrStmt q)
  | .load a q => .load a (liftSomeInrStmt q)
  | .branch p q₁ q₂ => .branch p (liftSomeInrStmt q₁) (liftSomeInrStmt q₂)
  | .goto l => .goto (fun v => some (Sum.inr (l v)))
  | .halt => .halt

def mapSomeInlCfg {Λ₁ Λ₂ σ : Type}
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ₁ σ) :
    Turing.TM2.Cfg BitTapeAlphabet (Option (Λ₁ ⊕ Λ₂)) σ :=
  ⟨cfg.l.map (fun l => some (Sum.inl l)), cfg.var, cfg.stk⟩

def mapSomeInrCfg {Λ₁ Λ₂ σ : Type}
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ₂ σ) :
    Turing.TM2.Cfg BitTapeAlphabet (Option (Λ₁ ⊕ Λ₂)) σ :=
  ⟨cfg.l.map (fun l => some (Sum.inr l)), cfg.var, cfg.stk⟩

theorem stepAux_liftSomeInlStmt {Λ₁ Λ₂ σ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ) (v : σ)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (liftSomeInlStmt (Λ₂ := Λ₂) q) v stk =
        mapSomeInlCfg (Turing.TM2.stepAux q v stk)
  | .push _ _ q, v, _ => stepAux_liftSomeInlStmt q v _
  | .peek _ _ q, _, stk => stepAux_liftSomeInlStmt q _ stk
  | .pop _ _ q, _, _ => stepAux_liftSomeInlStmt q _ _
  | .load _ q, _, stk => stepAux_liftSomeInlStmt q _ stk
  | .branch p q₁ q₂, v, stk => by
    dsimp [liftSomeInlStmt, Turing.TM2.stepAux]
    cases p v <;> simp [stepAux_liftSomeInlStmt]
  | .goto _, _, _ => rfl
  | .halt, _, _ => rfl

theorem stepAux_liftSomeInrStmt {Λ₁ Λ₂ σ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ) (v : σ)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (liftSomeInrStmt (Λ₁ := Λ₁) q) v stk =
        mapSomeInrCfg (Turing.TM2.stepAux q v stk)
  | .push _ _ q, v, _ => stepAux_liftSomeInrStmt q v _
  | .peek _ _ q, _, stk => stepAux_liftSomeInrStmt q _ stk
  | .pop _ _ q, _, _ => stepAux_liftSomeInrStmt q _ _
  | .load _ q, _, stk => stepAux_liftSomeInrStmt q _ stk
  | .branch p q₁ q₂, v, stk => by
    dsimp [liftSomeInrStmt, Turing.TM2.stepAux]
    cases p v <;> simp [stepAux_liftSomeInrStmt]
  | .goto _, _, _ => rfl
  | .halt, _, _ => rfl

/-- **Conditional Branch Combinator (`BitMachine.branchDelimBit`)**:
Pops a 1-bit delimited condition word `encodeDelimWord [b]` (`[false, b, true, false]`) from
`kCond : TapeIdx`; if `b = true`, executes `M_true`, else executes `M_false`. -/
def branchDelimBit (kCond : TapeIdx) (M_false M_true : BitMachine) : BitMachine where
  Λ := Option (M_false.Λ ⊕ M_true.Λ)
  main := none
  m := fun lbl =>
    match lbl with
    | none =>
      Turing.TM2.Stmt.pop kCond
        (fun _ _ => default)
        (Turing.TM2.Stmt.pop kCond
          (fun _ bOpt => (default, bOpt.getD false))
          (Turing.TM2.Stmt.pop kCond
            (fun rv _ => rv)
            (Turing.TM2.Stmt.pop kCond
              (fun rv _ => rv)
              (Turing.TM2.Stmt.branch (fun rv => rv.2)
                (Turing.TM2.Stmt.load (fun _ => default)
                  (Turing.TM2.Stmt.goto (fun _ => some (Sum.inr M_true.main))))
                (Turing.TM2.Stmt.load (fun _ => default)
                  (Turing.TM2.Stmt.goto (fun _ => some (Sum.inl M_false.main))))))))
    | some (Sum.inl l₁) => liftSomeInlStmt (M_false.m l₁)
    | some (Sum.inr l₂) => liftSomeInrStmt (M_true.m l₂)

@[simp]
theorem numLabels_branchDelimBit (kCond : TapeIdx) (M_false M_true : BitMachine) :
    (branchDelimBit kCond M_false M_true).numLabels =
      M_false.numLabels + M_true.numLabels + 1 := by
  simp [numLabels, branchDelimBit]

theorem step_branchDelimBit_inl (kCond : TapeIdx) (M_false M_true : BitMachine)
    (x y : M_false.toFinTM2.Cfg)
    (h : M_false.toFinTM2.step x = some y) :
    (branchDelimBit kCond M_false M_true).toFinTM2.step (mapSomeInlCfg x) =
      some (mapSomeInlCfg y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [branchDelimBit, toFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      mapSomeInlCfg]
    exact congrArg some (stepAux_liftSomeInlStmt (M_false.m l) v stk)

theorem step_branchDelimBit_inr (kCond : TapeIdx) (M_false M_true : BitMachine)
    (x y : M_true.toFinTM2.Cfg)
    (h : M_true.toFinTM2.step x = some y) :
    (branchDelimBit kCond M_false M_true).toFinTM2.step (mapSomeInrCfg x) =
      some (mapSomeInrCfg y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [branchDelimBit, toFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      mapSomeInrCfg]
    exact congrArg some (stepAux_liftSomeInrStmt (M_true.m l) v stk)

theorem ComputesInTime.branchDelimBit (kCond : TapeIdx) {M_false M_true : BitMachine}
    (b : Bool) (restCond : List Bool)
    {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {t : ℕ}
    (h : (if b then M_true else M_false).ComputesInTime
      (Function.update T₁ kCond restCond) T₂ t) :
    (BitMachine.branchDelimBit kCond M_false M_true).ComputesInTime
      (Function.update T₁ kCond (encodeDelimWord [b] ++ restCond)) T₂ (t + 1) := by
  rcases h with ⟨heval⟩
  cases b with
  | false =>
    dsimp at heval
    have hstep0 : (BitMachine.branchDelimBit kCond M_false M_true).toFinTM2.step
        ⟨some none, default,
          Function.update T₁ kCond (encodeDelimWord [false] ++ restCond)⟩ =
        some ⟨some (some (Sum.inl M_false.main)), default,
          Function.update T₁ kCond restCond⟩ := by
      simp [BitMachine.branchDelimBit, toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have hlifted := EvalsToInTime.map_simulation (mapSomeInlCfg (Λ₂ := M_true.Λ))
      (step_branchDelimBit_inl kCond M_false M_true) heval
    exact ⟨EvalsToInTime.of_step hstep0 hlifted⟩
  | true =>
    dsimp at heval
    have hstep0 : (BitMachine.branchDelimBit kCond M_false M_true).toFinTM2.step
        ⟨some none, default,
          Function.update T₁ kCond (encodeDelimWord [true] ++ restCond)⟩ =
        some ⟨some (some (Sum.inr M_true.main)), default,
          Function.update T₁ kCond restCond⟩ := by
      simp [BitMachine.branchDelimBit, toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have hlifted := EvalsToInTime.map_simulation (mapSomeInrCfg (Λ₁ := M_false.Λ))
      (step_branchDelimBit_inr kCond M_false M_true) heval
    exact ⟨EvalsToInTime.of_step hstep0 hlifted⟩

end BitMachine

/-! ## 4. Explicit 8-Stack Configuration Algebra (`mkTapes8`) & Word-Stack Gadgets -/

/-- Explicit 8-stack configuration constructor for `TapeIdx = Fin 8`, eliminating nested
`Function.update` terms in sequential and loop compositions.
Recall `kIO = 0`, `kSched = 1`, `kWork0 = 2`, `kWork1 = 3`, `kWork2 = 4`, `kWork3 = 5`,
`kWork4 = 6`, `kWork5 = 7`. -/
def mkTapes8 (tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∀ k : TapeIdx, List (BitTapeAlphabet k)
  | ⟨0, _⟩ => tIO
  | ⟨1, _⟩ => tSch
  | ⟨2, _⟩ => tW0
  | ⟨3, _⟩ => tW1
  | ⟨4, _⟩ => tW2
  | ⟨5, _⟩ => tW3
  | ⟨6, _⟩ => tW4
  | ⟨7, _⟩ => tW5

@[simp] theorem mkTapes8_kIO (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kIO = t0 := rfl
@[simp] theorem mkTapes8_kWork0 (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kWork0 = t1 := rfl
@[simp] theorem mkTapes8_kWork1 (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kWork1 = t2 := rfl
@[simp] theorem mkTapes8_kWork2 (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kWork2 = t3 := rfl
@[simp] theorem mkTapes8_kWork3 (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kWork3 = t4 := rfl
@[simp] theorem mkTapes8_kWork4 (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kWork4 = t5 := rfl
@[simp] theorem mkTapes8_kWork5 (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kWork5 = t6 := rfl
@[simp] theorem mkTapes8_kSched (t0 t1 t2 t3 t4 t5 t6 t7 : List Bool) :
    mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7 kSched = t7 := rfl

@[simp] theorem update_mkTapes8_kIO (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kIO s =
      mkTapes8 s t1 t2 t3 t4 t5 t6 t7 := by
  funext k; fin_cases k <;> rfl

@[simp] theorem update_mkTapes8_kWork0 (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kWork0 s =
      mkTapes8 t0 s t2 t3 t4 t5 t6 t7 := by
  funext k; fin_cases k <;> rfl

@[simp] theorem update_mkTapes8_kWork1 (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kWork1 s =
      mkTapes8 t0 t1 s t3 t4 t5 t6 t7 := by
  funext k; fin_cases k <;> rfl

@[simp] theorem update_mkTapes8_kWork2 (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kWork2 s =
      mkTapes8 t0 t1 t2 s t4 t5 t6 t7 := by
  funext k; fin_cases k <;> rfl

@[simp] theorem update_mkTapes8_kWork3 (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kWork3 s =
      mkTapes8 t0 t1 t2 t3 s t5 t6 t7 := by
  funext k; fin_cases k <;> rfl

@[simp] theorem update_mkTapes8_kWork4 (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kWork4 s =
      mkTapes8 t0 t1 t2 t3 t4 s t6 t7 := by
  funext k; fin_cases k <;> rfl

@[simp] theorem update_mkTapes8_kWork5 (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kWork5 s =
      mkTapes8 t0 t1 t2 t3 t4 t5 s t7 := by
  funext k; fin_cases k <;> rfl

@[simp] theorem update_mkTapes8_kSched (t0 t1 t2 t3 t4 t5 t6 t7 s : List Bool) :
    Function.update (mkTapes8 t0 t1 t2 t3 t4 t5 t6 t7) kSched s =
      mkTapes8 t0 t1 t2 t3 t4 t5 t6 s := by
  funext k; fin_cases k <;> rfl

@[simp] theorem initList_stk_eq_mkTapes8 (M : BitMachine) (xs : List Bool) :
    (Turing.initList M.toFinTM2 xs).stk = mkTapes8 xs [] [] [] [] [] [] [] := by
  funext k; fin_cases k <;> rfl

@[simp] theorem haltList_stk_eq_mkTapes8 (M : BitMachine) (ys : List Bool) :
    (Turing.haltList M.toFinTM2 ys).stk = mkTapes8 ys [] [] [] [] [] [] [] := by
  funext k; fin_cases k <;> rfl

theorem singleTapeStk_eq_mkTapes8 (xs : List Bool) :
    singleTapeStk xs = mkTapes8 xs [] [] [] [] [] [] [] := by
  funext k; fin_cases k <;> simp [singleTapeStk, mkTapes8, kIO]

theorem twoTapeStk_eq_mkTapes8 (xs ys : List Bool) :
    twoTapeStk xs ys = mkTapes8 xs ys [] [] [] [] [] [] := by
  funext k; fin_cases k <;> simp [twoTapeStk, mkTapes8, kIO, kWork0]

theorem threeTapeWorkStk_eq_mkTapes8 (xs ys zs : List Bool) :
    threeTapeWorkStk xs ys zs = mkTapes8 xs ys zs [] [] [] [] [] := by
  funext k; fin_cases k <;> simp [threeTapeWorkStk, mkTapes8, kIO, kWork0, kWork1]

theorem BitMachine.ComputesInTime.loopDelimWord_kSched {body : BitMachine} (B : ℕ)
    (cnt : List Bool) (restSch : List Bool)
    (t0 t1 t2 t3 t4 t5 t6 : ℕ → List Bool)
    (hpass : ∀ (i : ℕ) (tailSch : List Bool),
      body.ComputesInTime
        (mkTapes8 (t0 i) (t1 i) (t2 i) (t3 i) (t4 i) (t5 i) (t6 i) tailSch)
        (mkTapes8 (t0 (i + 1)) (t1 (i + 1)) (t2 (i + 1)) (t3 (i + 1))
          (t4 (i + 1)) (t5 (i + 1)) (t6 (i + 1)) tailSch) B) :
    (body.loopDelimWord kSched).ComputesInTime
      (mkTapes8 (t0 0) (t1 0) (t2 0) (t3 0) (t4 0) (t5 0) (t6 0)
        (encodeDelimWord cnt ++ restSch))
      (mkTapes8 (t0 cnt.length) (t1 cnt.length) (t2 cnt.length) (t3 cnt.length)
        (t4 cnt.length) (t5 cnt.length) (t6 cnt.length) restSch)
      (cnt.length * (B + 1) + 1) := by
  simpa using BitMachine.ComputesInTime.loopDelimWord kSched B cnt restSch
    (fun i => mkTapes8 (t0 i) (t1 i) (t2 i) (t3 i) (t4 i) (t5 i) (t6 i) [])
    (fun i tailSch => by simpa using hpass i tailSch)

/-- **Gadget 1 (`tmPushEmpty k`)**: Pushes `encodeDelimWord []` (`[true, false]`) onto stack `k`
in 1 step (`|Λ| = 1`, `|σ| = 32`). -/
def tmPushEmpty (k : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.push k (fun _ => false)
      (Turing.TM2.Stmt.push k (fun _ => true) Turing.TM2.Stmt.halt)

@[simp] theorem numLabels_tmPushEmpty (k : TapeIdx) : (tmPushEmpty k).numLabels = 1 := rfl

theorem tmPushEmpty_computesInTime (k : TapeIdx)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmPushEmpty k).ComputesInTime T
      (Function.update T k (encodeDelimWord [] ++ T k)) 1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp [tmPushEmpty, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux]

/-- **Gadget 2 (`tmPopEmpty k`)**: Pops 2 bits (`encodeDelimWord [] = [true, false]`) from stack `k`
in 1 step (`|Λ| = 1`, `|σ| = 32`). -/
def tmPopEmpty (k : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop k (fun v _ => v)
      (Turing.TM2.Stmt.pop k (fun v _ => v) Turing.TM2.Stmt.halt)

@[simp] theorem numLabels_tmPopEmpty (k : TapeIdx) : (tmPopEmpty k).numLabels = 1 := rfl

theorem tmPopEmpty_computesInTime (k : TapeIdx)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) (rest : List Bool)
    (hk : T k = encodeDelimWord [] ++ rest) :
    (tmPopEmpty k).ComputesInTime T (Function.update T k rest) 1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp [tmPopEmpty, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, hk]

/-- **Gadget 3 (`tmConsBit b k`)**: Prepends bit `b : Bool` to the top delimited word on stack `k`
(`encodeDelimWord w ++ rest` $\mapsto$ `encodeDelimWord (b :: w) ++ rest`) in 1 step. -/
def tmConsBit (b : Bool) (k : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.push k (fun _ => b)
      (Turing.TM2.Stmt.push k (fun _ => false) Turing.TM2.Stmt.halt)

@[simp] theorem numLabels_tmConsBit (b : Bool) (k : TapeIdx) :
    (tmConsBit b k).numLabels = 1 := rfl

theorem tmConsBit_computesInTime (b : Bool) (k : TapeIdx)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) (w rest : List Bool)
    (hk : T k = encodeDelimWord w ++ rest) :
    (tmConsBit b k).ComputesInTime T
      (Function.update T k (encodeDelimWord (b :: w) ++ rest)) 1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp [tmConsBit, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, hk]

/-- **Gadget 4 (`tmTailBits k`)**: Drops the head bit of the top delimited word on stack `k`
(`encodeDelimWord w ++ rest` $\mapsto$ `encodeDelimWord w.tail ++ rest`, preserving `[]` when
`w = []`) in 1 step (`|Λ| = 1`). -/
def tmTailBits (k : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop k
      (fun _ bOpt => (default, bOpt.getD true))
      (Turing.TM2.Stmt.pop k
        (fun rv _ => rv)
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.push k (fun _ => false)
            (Turing.TM2.Stmt.push k (fun _ => true)
              (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))
          (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))

@[simp] theorem numLabels_tmTailBits (k : TapeIdx) : (tmTailBits k).numLabels = 1 := rfl

theorem tmTailBits_computesInTime (k : TapeIdx)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) (w rest : List Bool)
    (hk : T k = encodeDelimWord w ++ rest) :
    (tmTailBits k).ComputesInTime T
      (Function.update T k (encodeDelimWord w.tail ++ rest)) 1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  cases w <;> simp [tmTailBits, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, hk]

/-- **Gadget 5 (`tmDropWord kSrc`)**: Pops and discards the entire top delimited word `w` from
`kSrc` (`encodeDelimWord w ++ rest` $\mapsto$ `rest`) in `w.length + 1` steps (`|Λ| = 1`). -/
def tmDropWord (kSrc : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kSrc
      (fun _ bOpt => (default, bOpt.getD true))
      (Turing.TM2.Stmt.pop kSrc
        (fun rv _ => rv)
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
          (Turing.TM2.Stmt.load (fun _ => default)
            (Turing.TM2.Stmt.goto (fun _ => ())))))

@[simp] theorem numLabels_tmDropWord (kSrc : TapeIdx) : (tmDropWord kSrc).numLabels = 1 := rfl

def tmDropWord_evalsToInTime_concrete (kSrc : TapeIdx) :
    ∀ (w rest : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmDropWord kSrc).toFinTM2.step
        ⟨some (), default, Function.update T kSrc (encodeDelimWord w ++ rest)⟩
        (some ⟨none, default, Function.update T kSrc rest⟩)
        (w.length + 1)
  | [], rest, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmDropWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  | b :: w, rest, T => by
    have hstep : (tmDropWord kSrc).toFinTM2.step
        ⟨some (), default, Function.update T kSrc (encodeDelimWord (b :: w) ++ rest)⟩ =
        some ⟨some (), default, Function.update T kSrc (encodeDelimWord w ++ rest)⟩ := by
      simp [tmDropWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    exact EvalsToInTime.of_step hstep (tmDropWord_evalsToInTime_concrete kSrc w rest T)

theorem tmDropWord_computesInTime (kSrc : TapeIdx)
    (w rest : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmDropWord kSrc).ComputesInTime
      (Function.update T kSrc (encodeDelimWord w ++ rest))
      (Function.update T kSrc rest)
      (w.length + 1) :=
  ⟨tmDropWord_evalsToInTime_concrete kSrc w rest T⟩

/-- **Gadget 6 (`tmRevMoveWord kSrc kDst`)**: Pops `encodeDelimWord w` from `kSrc` and pushes
`encodeDelimWord w.reverse` onto `kDst` in `w.length + 2` steps (`|Λ| = 2`, touching only `kSrc`
and `kDst`). -/
def tmRevMoveWord (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Bool
  main := false
  m := fun lbl =>
    match lbl with
    | false =>
      Turing.TM2.Stmt.push kDst (fun _ => false)
        (Turing.TM2.Stmt.push kDst (fun _ => true)
          (Turing.TM2.Stmt.goto (fun _ => true)))
    | true =>
      Turing.TM2.Stmt.pop kSrc
        (fun _ bOpt => (default, bOpt.getD true))
        (Turing.TM2.Stmt.pop kSrc
          (fun rv bOpt => (⟨bOpt.getD false, false, false, false⟩, rv.2))
          (Turing.TM2.Stmt.branch (fun rv => rv.2)
            (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
            (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitA)
              (Turing.TM2.Stmt.push kDst (fun _ => false)
                (Turing.TM2.Stmt.load (fun _ => default)
                  (Turing.TM2.Stmt.goto (fun _ => true)))))))

@[simp] theorem numLabels_tmRevMoveWord (kSrc kDst : TapeIdx) :
    (tmRevMoveWord kSrc kDst).numLabels = 2 := rfl

def tmRevMoveWord_loop_evalsToInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst) :
    ∀ (w acc restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmRevMoveWord kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc))
            kDst (encodeDelimWord acc ++ restDst)⟩
        (some ⟨none, default,
          Function.update (Function.update T kSrc restSrc)
            kDst (encodeDelimWord (w.reverseAux acc) ++ restDst)⟩)
        (w.length + 1)
  | [], acc, restSrc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmRevMoveWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hne]
  | b :: w, acc, restSrc, restDst, T => by
    have hstep : (tmRevMoveWord kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord (b :: w) ++ restSrc))
            kDst (encodeDelimWord acc ++ restDst)⟩ =
        some ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc))
            kDst (encodeDelimWord (b :: acc) ++ restDst)⟩ := by
      simp [tmRevMoveWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hne.symm,
        Function.update_comm hne]
    exact EvalsToInTime.of_step hstep
      (tmRevMoveWord_loop_evalsToInTime kSrc kDst hne w (b :: acc) restSrc restDst T)

theorem tmRevMoveWord_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (w restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmRevMoveWord kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc)) kDst restDst)
      (Function.update (Function.update T kSrc restSrc)
        kDst (encodeDelimWord w.reverse ++ restDst))
      (w.length + 2) := by
  have hstep0 : (tmRevMoveWord kSrc kDst).toFinTM2.step
      ⟨some false, default,
        Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc)) kDst restDst⟩ =
      some ⟨some true, default,
        Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc))
          kDst (encodeDelimWord [] ++ restDst)⟩ := by
    simp [tmRevMoveWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  exact ⟨EvalsToInTime.of_step hstep0
    (tmRevMoveWord_loop_evalsToInTime kSrc kDst hne w [] restSrc restDst T)⟩

/-- **Gadget 7 (`tmMoveWord kSrc kTmp kDst`)**: Order-preserving move of `encodeDelimWord w` from
`kSrc` to `kDst` via `kTmp` in `2 * w.length + 4` steps (`|Λ| = 4`). -/
def tmMoveWord (kSrc kTmp kDst : TapeIdx) : BitMachine :=
  (tmRevMoveWord kSrc kTmp).seq (tmRevMoveWord kTmp kDst)

@[simp] theorem numLabels_tmMoveWord (kSrc kTmp kDst : TapeIdx) :
    (tmMoveWord kSrc kTmp kDst).numLabels = 4 := rfl

theorem tmMoveWord_computesInTime (kSrc kTmp kDst : TapeIdx)
    (hST : kSrc ≠ kTmp) (hTD : kTmp ≠ kDst) (hSD : kSrc ≠ kDst)
    (w restSrc restTmp restDst : List Bool)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmMoveWord kSrc kTmp kDst).ComputesInTime
      (Function.update (Function.update (Function.update T
        kSrc (encodeDelimWord w ++ restSrc)) kTmp restTmp) kDst restDst)
      (Function.update (Function.update (Function.update T
        kSrc restSrc) kTmp restTmp) kDst (encodeDelimWord w ++ restDst))
      (2 * w.length + 4) := by
  have hcomm : ∀ a b,
      Function.update (Function.update (Function.update T kDst restDst) kSrc a) kTmp b =
      Function.update (Function.update (Function.update T kSrc a) kTmp b) kDst restDst :=
    fun a b => by rw [Function.update_comm hSD.symm, Function.update_comm hTD.symm]
  have h1 := tmRevMoveWord_computesInTime kSrc kTmp hST w restSrc restTmp
    (Function.update T kDst restDst)
  rw [hcomm, hcomm] at h1
  have h2 := tmRevMoveWord_computesInTime kTmp kDst hTD w.reverse restTmp restDst
    (Function.update T kSrc restSrc)
  rw [List.length_reverse, List.reverse_reverse] at h2
  have h12 := h1.seq h2
  convert h12 using 1 <;> first | rfl | omega

/-- **Gadget 8 (`tmRevDupWord kSrc kDst1 kDst2`)**: Pops `encodeDelimWord u` from `kSrc` and
pushes `encodeDelimWord u.reverse` onto both `kDst1` and `kDst2` in `u.length + 2` steps (`|Λ| = 2`). -/
def tmRevDupWord (kSrc kDst1 kDst2 : TapeIdx) : BitMachine where
  Λ := Bool
  main := false
  m := fun lbl =>
    match lbl with
    | false =>
      Turing.TM2.Stmt.push kDst1 (fun _ => false)
        (Turing.TM2.Stmt.push kDst1 (fun _ => true)
          (Turing.TM2.Stmt.push kDst2 (fun _ => false)
            (Turing.TM2.Stmt.push kDst2 (fun _ => true)
              (Turing.TM2.Stmt.goto (fun _ => true)))))
    | true =>
      Turing.TM2.Stmt.pop kSrc
        (fun _ bOpt => (default, bOpt.getD true))
        (Turing.TM2.Stmt.pop kSrc
          (fun rv bOpt => (⟨bOpt.getD false, false, false, false⟩, rv.2))
          (Turing.TM2.Stmt.branch (fun rv => rv.2)
            (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
            (Turing.TM2.Stmt.push kDst1 (fun rv => rv.1.bitA)
              (Turing.TM2.Stmt.push kDst1 (fun _ => false)
                (Turing.TM2.Stmt.push kDst2 (fun rv => rv.1.bitA)
                  (Turing.TM2.Stmt.push kDst2 (fun _ => false)
                    (Turing.TM2.Stmt.load (fun _ => default)
                      (Turing.TM2.Stmt.goto (fun _ => true)))))))))

@[simp] theorem numLabels_tmRevDupWord (kSrc kDst1 kDst2 : TapeIdx) :
    (tmRevDupWord kSrc kDst1 kDst2).numLabels = 2 := rfl

def tmRevDupWord_loop_evalsToInTime (kSrc kDst1 kDst2 : TapeIdx)
    (hS1 : kSrc ≠ kDst1) (hS2 : kSrc ≠ kDst2) (h12 : kDst1 ≠ kDst2) :
    ∀ (u acc1 acc2 restSrc rest1 rest2 : List Bool)
      (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmRevDupWord kSrc kDst1 kDst2).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update (Function.update T
            kSrc (encodeDelimWord u ++ restSrc))
            kDst1 (encodeDelimWord acc1 ++ rest1))
            kDst2 (encodeDelimWord acc2 ++ rest2)⟩
        (some ⟨none, default,
          Function.update (Function.update (Function.update T
            kSrc restSrc)
            kDst1 (encodeDelimWord (u.reverseAux acc1) ++ rest1))
            kDst2 (encodeDelimWord (u.reverseAux acc2) ++ rest2)⟩)
        (u.length + 1)
  | [], acc1, acc2, restSrc, rest1, rest2, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmRevDupWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hS1, Function.update_comm hS2]
  | b :: u, acc1, acc2, restSrc, rest1, rest2, T => by
    have hstep : (tmRevDupWord kSrc kDst1 kDst2).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update (Function.update T
            kSrc (encodeDelimWord (b :: u) ++ restSrc))
            kDst1 (encodeDelimWord acc1 ++ rest1))
            kDst2 (encodeDelimWord acc2 ++ rest2)⟩ =
        some ⟨some true, default,
          Function.update (Function.update (Function.update T
            kSrc (encodeDelimWord u ++ restSrc))
            kDst1 (encodeDelimWord (b :: acc1) ++ rest1))
            kDst2 (encodeDelimWord (b :: acc2) ++ rest2)⟩ := by
      simp [tmRevDupWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hS1.symm,
        Function.update_of_ne hS2.symm,
        Function.update_of_ne h12.symm, Function.update_comm hS1,
        Function.update_comm hS2, Function.update_comm h12]
    exact EvalsToInTime.of_step hstep
      (tmRevDupWord_loop_evalsToInTime kSrc kDst1 kDst2 hS1 hS2 h12
        u (b :: acc1) (b :: acc2) restSrc rest1 rest2 T)

theorem tmRevDupWord_computesInTime (kSrc kDst1 kDst2 : TapeIdx)
    (hS1 : kSrc ≠ kDst1) (hS2 : kSrc ≠ kDst2) (h12 : kDst1 ≠ kDst2)
    (u restSrc rest1 rest2 : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmRevDupWord kSrc kDst1 kDst2).ComputesInTime
      (Function.update (Function.update (Function.update T
        kSrc (encodeDelimWord u ++ restSrc)) kDst1 rest1) kDst2 rest2)
      (Function.update (Function.update (Function.update T
        kSrc restSrc) kDst1 (encodeDelimWord u.reverse ++ rest1))
        kDst2 (encodeDelimWord u.reverse ++ rest2))
      (u.length + 2) := by
  have hstep0 : (tmRevDupWord kSrc kDst1 kDst2).toFinTM2.step
      ⟨some false, default,
        Function.update (Function.update (Function.update T
          kSrc (encodeDelimWord u ++ restSrc)) kDst1 rest1) kDst2 rest2⟩ =
      some ⟨some true, default,
        Function.update (Function.update (Function.update T
          kSrc (encodeDelimWord u ++ restSrc))
          kDst1 (encodeDelimWord [] ++ rest1))
          kDst2 (encodeDelimWord [] ++ rest2)⟩ := by
    simp [tmRevDupWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux,
      Function.update_of_ne h12.symm, Function.update_comm h12]
  exact ⟨EvalsToInTime.of_step hstep0
    (tmRevDupWord_loop_evalsToInTime kSrc kDst1 kDst2 hS1 hS2 h12 u [] [] restSrc rest1 rest2 T)⟩

/-- **Gadget 9 (`tmDupWord kSrc kTmp kDst`)**: Non-destructively copies `encodeDelimWord w` from
`kSrc` onto `kDst` (using `kTmp` as scratch and restoring both `kSrc` and `kTmp`) in
`2 * w.length + 4` steps (`|Λ| = 4`). -/
def tmDupWord (kSrc kTmp kDst : TapeIdx) : BitMachine :=
  (tmRevMoveWord kSrc kTmp).seq (tmRevDupWord kTmp kSrc kDst)

@[simp] theorem numLabels_tmDupWord (kSrc kTmp kDst : TapeIdx) :
    (tmDupWord kSrc kTmp kDst).numLabels = 4 := rfl

theorem tmDupWord_computesInTime (kSrc kTmp kDst : TapeIdx)
    (hST : kSrc ≠ kTmp) (hTD : kTmp ≠ kDst) (hSD : kSrc ≠ kDst)
    (w restSrc restTmp restDst : List Bool)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmDupWord kSrc kTmp kDst).ComputesInTime
      (Function.update (Function.update (Function.update T
        kSrc (encodeDelimWord w ++ restSrc)) kTmp restTmp) kDst restDst)
      (Function.update (Function.update (Function.update T
        kSrc (encodeDelimWord w ++ restSrc)) kTmp restTmp)
        kDst (encodeDelimWord w ++ restDst))
      (2 * w.length + 4) := by
  have hcomm1 : ∀ a b,
      Function.update (Function.update (Function.update T kDst restDst) kSrc a) kTmp b =
      Function.update (Function.update (Function.update T kSrc a) kTmp b) kDst restDst :=
    fun a b => by rw [Function.update_comm hSD.symm, Function.update_comm hTD.symm]
  have h1 := tmRevMoveWord_computesInTime kSrc kTmp hST w restSrc restTmp
    (Function.update T kDst restDst)
  rw [hcomm1, hcomm1] at h1
  have hcomm2 : ∀ a b c,
      Function.update (Function.update (Function.update T kTmp a) kSrc b) kDst c =
      Function.update (Function.update (Function.update T kSrc b) kTmp a) kDst c :=
    fun a b c => by rw [Function.update_comm hST.symm]
  have h2 := tmRevDupWord_computesInTime kTmp kSrc kDst hST.symm hTD hSD
    w.reverse restTmp restSrc restDst T
  rw [List.length_reverse, List.reverse_reverse, hcomm2, hcomm2] at h2
  have h12 := h1.seq h2
  convert h12 using 1 <;> first | rfl | omega

/-- **Gadget 10 (`tmPushRevWord kSrc kDst`)**: Pops `encodeDelimWord v` from `kSrc` and prepends
`(encodeDelimWord v).reverse` onto the top delimited word `acc` of `kDst`
(`encodeDelimWord acc ++ restDst` $\mapsto$ `encodeDelimWord ((encodeDelimWord v).reverse ++ acc) ++ restDst`)
in `v.length + 1` steps (`|Λ| = 1`, zero scratch stacks). -/
def tmPushRevWord (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kSrc
      (fun _ bOpt => (default, bOpt.getD true))
      (Turing.TM2.Stmt.pop kSrc
        (fun rv bOpt => (⟨bOpt.getD false, false, false, false⟩, rv.2))
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.push kDst (fun _ => true)
            (Turing.TM2.Stmt.push kDst (fun _ => false)
              (Turing.TM2.Stmt.push kDst (fun _ => false)
                (Turing.TM2.Stmt.push kDst (fun _ => false)
                  (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))))
          (Turing.TM2.Stmt.push kDst (fun _ => false)
            (Turing.TM2.Stmt.push kDst (fun _ => false)
              (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitA)
                (Turing.TM2.Stmt.push kDst (fun _ => false)
                  (Turing.TM2.Stmt.load (fun _ => default)
                    (Turing.TM2.Stmt.goto (fun _ => ())))))))))

@[simp] theorem numLabels_tmPushRevWord (kSrc kDst : TapeIdx) :
    (tmPushRevWord kSrc kDst).numLabels = 1 := rfl

def tmPushRevWord_evalsToInTime_concrete (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst) :
    ∀ (v acc restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmPushRevWord kSrc kDst).toFinTM2.step
        ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord v ++ restSrc))
            kDst (encodeDelimWord acc ++ restDst)⟩
        (some ⟨none, default,
          Function.update (Function.update T kSrc restSrc)
            kDst (encodeDelimWord ((encodeDelimWord v).reverseAux acc) ++ restDst)⟩)
        (v.length + 1)
  | [], acc, restSrc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmPushRevWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hne.symm,
      Function.update_comm hne]
  | b :: v, acc, restSrc, restDst, T => by
    have hstep : (tmPushRevWord kSrc kDst).toFinTM2.step
        ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord (b :: v) ++ restSrc))
            kDst (encodeDelimWord acc ++ restDst)⟩ =
        some ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord v ++ restSrc))
            kDst (encodeDelimWord (b :: false :: acc) ++ restDst)⟩ := by
      simp [tmPushRevWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hne.symm,
        Function.update_comm hne]
    exact EvalsToInTime.of_step hstep
      (tmPushRevWord_evalsToInTime_concrete kSrc kDst hne v (b :: false :: acc) restSrc restDst T)

theorem tmPushRevWord_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (v acc restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmPushRevWord kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc (encodeDelimWord v ++ restSrc))
        kDst (encodeDelimWord acc ++ restDst))
      (Function.update (Function.update T kSrc restSrc)
        kDst (encodeDelimWord ((encodeDelimWord v).reverse ++ acc) ++ restDst))
      (v.length + 1) := by
  rw [← List.reverseAux_eq]
  exact ⟨tmPushRevWord_evalsToInTime_concrete kSrc kDst hne v acc restSrc restDst T⟩

/-- **Gadget 11 (`tmPrependRevWord kSrc kDst`)**: Pops `encodeDelimWord u` from `kSrc` (where
`u = v.reverse`) and prepends `encodeDelimWord v` (`encodeDelimWord u.reverse`) onto the top
delimited word `s` of `kDst` (`encodeDelimWord s ++ restDst` $\mapsto$
`encodeDelimWord (encodeDelimWord u.reverse ++ s) ++ restDst`) in `u.length + 2` steps (`|Λ| = 2`). -/
def tmPrependRevWord (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Bool
  main := false
  m := fun lbl =>
    match lbl with
    | false =>
      Turing.TM2.Stmt.push kDst (fun _ => false)
        (Turing.TM2.Stmt.push kDst (fun _ => false)
          (Turing.TM2.Stmt.push kDst (fun _ => true)
            (Turing.TM2.Stmt.push kDst (fun _ => false)
              (Turing.TM2.Stmt.goto (fun _ => true)))))
    | true =>
      Turing.TM2.Stmt.pop kSrc
        (fun _ bOpt => (default, bOpt.getD true))
        (Turing.TM2.Stmt.pop kSrc
          (fun rv bOpt => (⟨bOpt.getD false, false, false, false⟩, rv.2))
          (Turing.TM2.Stmt.branch (fun rv => rv.2)
            (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
            (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitA)
              (Turing.TM2.Stmt.push kDst (fun _ => false)
                (Turing.TM2.Stmt.push kDst (fun _ => false)
                  (Turing.TM2.Stmt.push kDst (fun _ => false)
                    (Turing.TM2.Stmt.load (fun _ => default)
                      (Turing.TM2.Stmt.goto (fun _ => true)))))))))

@[simp] theorem numLabels_tmPrependRevWord (kSrc kDst : TapeIdx) :
    (tmPrependRevWord kSrc kDst).numLabels = 2 := rfl

def tmPrependRevWord_loop_evalsToInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst) :
    ∀ (u acc s restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmPrependRevWord kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
            kDst (encodeDelimWord (encodeDelimWord acc ++ s) ++ restDst)⟩
        (some ⟨none, default,
          Function.update (Function.update T kSrc restSrc)
            kDst (encodeDelimWord (encodeDelimWord (u.reverseAux acc) ++ s) ++ restDst)⟩)
        (u.length + 1)
  | [], acc, s, restSrc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmPrependRevWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hne]
  | b :: u, acc, s, restSrc, restDst, T => by
    have hstep : (tmPrependRevWord kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord (b :: u) ++ restSrc))
            kDst (encodeDelimWord (encodeDelimWord acc ++ s) ++ restDst)⟩ =
        some ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
            kDst (encodeDelimWord (encodeDelimWord (b :: acc) ++ s) ++ restDst)⟩ := by
      simp [tmPrependRevWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hne.symm,
        Function.update_comm hne]
    exact EvalsToInTime.of_step hstep
      (tmPrependRevWord_loop_evalsToInTime kSrc kDst hne u (b :: acc) s restSrc restDst T)

theorem tmPrependRevWord_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (u s restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmPrependRevWord kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
        kDst (encodeDelimWord s ++ restDst))
      (Function.update (Function.update T kSrc restSrc)
        kDst (encodeDelimWord (encodeDelimWord u.reverse ++ s) ++ restDst))
      (u.length + 2) := by
  have hstep0 : (tmPrependRevWord kSrc kDst).toFinTM2.step
      ⟨some false, default,
        Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
          kDst (encodeDelimWord s ++ restDst)⟩ =
      some ⟨some true, default,
        Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
          kDst (encodeDelimWord (encodeDelimWord [] ++ s) ++ restDst)⟩ := by
    simp [tmPrependRevWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  exact ⟨EvalsToInTime.of_step hstep0
    (tmPrependRevWord_loop_evalsToInTime kSrc kDst hne u [] s restSrc restDst T)⟩

/-- **Gadget 12 (`tmConsWord kSrc kTmp kDst`)**: Pops `encodeDelimWord v` from `kSrc` and prepends
`encodeDelimWord v` onto the top delimited word `s` of `kDst`
(`encodeDelimWord s ++ restDst` $\mapsto$ `encodeDelimWord (encodeDelimWord v ++ s) ++ restDst`)
in `2 * v.length + 4` steps (`|Λ| = 4`, independent of `s.length`). -/
def tmConsWord (kSrc kTmp kDst : TapeIdx) : BitMachine :=
  (tmRevMoveWord kSrc kTmp).seq (tmPrependRevWord kTmp kDst)

@[simp] theorem numLabels_tmConsWord (kSrc kTmp kDst : TapeIdx) :
    (tmConsWord kSrc kTmp kDst).numLabels = 4 := rfl

theorem tmConsWord_computesInTime (kSrc kTmp kDst : TapeIdx)
    (hST : kSrc ≠ kTmp) (hTD : kTmp ≠ kDst) (hSD : kSrc ≠ kDst)
    (v s restSrc restTmp restDst : List Bool)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmConsWord kSrc kTmp kDst).ComputesInTime
      (Function.update (Function.update (Function.update T
        kSrc (encodeDelimWord v ++ restSrc)) kTmp restTmp)
        kDst (encodeDelimWord s ++ restDst))
      (Function.update (Function.update (Function.update T
        kSrc restSrc) kTmp restTmp)
        kDst (encodeDelimWord (encodeDelimWord v ++ s) ++ restDst))
      (2 * v.length + 4) := by
  have hcomm : ∀ a b,
      Function.update (Function.update (Function.update T kDst (encodeDelimWord s ++ restDst)) kSrc a) kTmp b =
      Function.update (Function.update (Function.update T kSrc a) kTmp b) kDst (encodeDelimWord s ++ restDst) :=
    fun a b => by rw [Function.update_comm hSD.symm, Function.update_comm hTD.symm]
  have h1 := tmRevMoveWord_computesInTime kSrc kTmp hST v restSrc restTmp
    (Function.update T kDst (encodeDelimWord s ++ restDst))
  rw [hcomm, hcomm] at h1
  have h2 := tmPrependRevWord_computesInTime kTmp kDst hTD v.reverse s restTmp restDst
    (Function.update T kSrc restSrc)
  rw [List.length_reverse, List.reverse_reverse] at h2
  have h12 := h1.seq h2
  convert h12 using 1 <;> first | rfl | omega

/-- Total pure parser splitting a packed word-stack `w : List Bool` into its first subword
`(unconsDelimWord w).1` and remaining packed word-stack `(unconsDelimWord w).2`. -/
def unconsDelimWord : List Bool → List Bool × List Bool
  | [] => ([], [])
  | [_] => ([], [])
  | true :: _ :: s => ([], s)
  | false :: b :: rest =>
    let p := unconsDelimWord rest
    (b :: p.1, p.2)

@[simp] theorem unconsDelimWord_nil : unconsDelimWord [] = ([], []) := rfl
@[simp] theorem unconsDelimWord_singleton (b : Bool) : unconsDelimWord [b] = ([], []) := rfl
@[simp] theorem unconsDelimWord_true_cons (b : Bool) (s : List Bool) :
    unconsDelimWord (true :: b :: s) = ([], s) := rfl
@[simp] theorem unconsDelimWord_false_cons (b : Bool) (rest : List Bool) :
    unconsDelimWord (false :: b :: rest) =
      (b :: (unconsDelimWord rest).1, (unconsDelimWord rest).2) := rfl

@[simp] theorem unconsDelimWord_encodeDelimWord_append :
    ∀ (u s : List Bool), unconsDelimWord (encodeDelimWord u ++ s) = (u, s)
  | [], s => rfl
  | b :: u, s => by
    simp [encodeDelimWord_cons, unconsDelimWord_encodeDelimWord_append u s]

/-- **Gadget 13 (`tmTailWords kSrc`)**: Drops the first subword `(unconsDelimWord w).1` from the
top delimited word `w` on `kSrc` (`encodeDelimWord w ++ restSrc` $\mapsto$
`encodeDelimWord (unconsDelimWord w).2 ++ restSrc`) in `(unconsDelimWord w).1.length + 1` steps
(`|Λ| = 1`, zero scratch stacks). -/
def tmTailWords (kSrc : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kSrc
      (fun _ bOpt => (default, bOpt.getD true))
      (Turing.TM2.Stmt.pop kSrc
        (fun rv bOpt => (⟨bOpt.getD false, false, false, false⟩, rv.2))
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.push kSrc (fun _ => false)
            (Turing.TM2.Stmt.push kSrc (fun _ => true)
              (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))
          (Turing.TM2.Stmt.pop kSrc
            (fun rv bOpt => (rv.1, bOpt.getD true))
            (Turing.TM2.Stmt.pop kSrc
              (fun rv bOpt => (⟨rv.1.bitA, bOpt.getD false, false, false⟩, rv.2))
              (Turing.TM2.Stmt.branch (fun rv => rv.2)
                (Turing.TM2.Stmt.push kSrc (fun _ => false)
                  (Turing.TM2.Stmt.push kSrc (fun _ => true)
                    (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))
                (Turing.TM2.Stmt.branch (fun rv => rv.1.bitA)
                  (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
                  (Turing.TM2.Stmt.load (fun _ => default)
                    (Turing.TM2.Stmt.goto (fun _ => ())))))))))

@[simp] theorem numLabels_tmTailWords (kSrc : TapeIdx) :
    (tmTailWords kSrc).numLabels = 1 := rfl

def tmTailWords_evalsToInTime_concrete (kSrc : TapeIdx) :
    ∀ (w restSrc : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmTailWords kSrc).toFinTM2.step
        ⟨some (), default, Function.update T kSrc (encodeDelimWord w ++ restSrc)⟩
        (some ⟨none, default,
          Function.update T kSrc (encodeDelimWord (unconsDelimWord w).2 ++ restSrc)⟩)
        ((unconsDelimWord w).1.length + 1)
  | [], restSrc, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmTailWords, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  | [b], restSrc, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmTailWords, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  | true :: b :: s, restSrc, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmTailWords, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  | false :: b :: rest, restSrc, T => by
    have hstep : (tmTailWords kSrc).toFinTM2.step
        ⟨some (), default,
          Function.update T kSrc (encodeDelimWord (false :: b :: rest) ++ restSrc)⟩ =
        some ⟨some (), default,
          Function.update T kSrc (encodeDelimWord rest ++ restSrc)⟩ := by
      simp [tmTailWords, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    exact EvalsToInTime.of_step hstep
      (tmTailWords_evalsToInTime_concrete kSrc rest restSrc T)

theorem tmTailWords_computesInTime (kSrc : TapeIdx)
    (w restSrc : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmTailWords kSrc).ComputesInTime
      (Function.update T kSrc (encodeDelimWord w ++ restSrc))
      (Function.update T kSrc (encodeDelimWord (unconsDelimWord w).2 ++ restSrc))
      ((unconsDelimWord w).1.length + 1) :=
  ⟨tmTailWords_evalsToInTime_concrete kSrc w restSrc T⟩

/-- **Gadget 14 (`tmPopFirstSubwordRev kSrc kDst`)**: Pops the first subword `(unconsDelimWord w).1`
from the top delimited word `w` on `kSrc` (leaving `encodeDelimWord (unconsDelimWord w).2 ++ restSrc`
on `kSrc`) and pushes `encodeDelimWord (unconsDelimWord w).1.reverse` onto `kDst` in
`(unconsDelimWord w).1.length + 2` steps (`|Λ| = 2`). -/
def tmPopFirstSubwordRev (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Bool
  main := false
  m := fun lbl =>
    match lbl with
    | false =>
      Turing.TM2.Stmt.push kDst (fun _ => false)
        (Turing.TM2.Stmt.push kDst (fun _ => true)
          (Turing.TM2.Stmt.goto (fun _ => true)))
    | true =>
      Turing.TM2.Stmt.pop kSrc
        (fun _ bOpt => (default, bOpt.getD true))
        (Turing.TM2.Stmt.pop kSrc
          (fun rv bOpt => (⟨bOpt.getD false, false, false, false⟩, rv.2))
          (Turing.TM2.Stmt.branch (fun rv => rv.2)
            (Turing.TM2.Stmt.push kSrc (fun _ => false)
              (Turing.TM2.Stmt.push kSrc (fun _ => true)
                (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))
            (Turing.TM2.Stmt.pop kSrc
              (fun rv bOpt => (rv.1, bOpt.getD true))
              (Turing.TM2.Stmt.pop kSrc
                (fun rv bOpt => (⟨rv.1.bitA, bOpt.getD false, false, false⟩, rv.2))
                (Turing.TM2.Stmt.branch (fun rv => rv.2)
                  (Turing.TM2.Stmt.push kSrc (fun _ => false)
                    (Turing.TM2.Stmt.push kSrc (fun _ => true)
                      (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))
                  (Turing.TM2.Stmt.branch (fun rv => rv.1.bitA)
                    (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
                    (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitB)
                      (Turing.TM2.Stmt.push kDst (fun _ => false)
                        (Turing.TM2.Stmt.load (fun _ => default)
                          (Turing.TM2.Stmt.goto (fun _ => true)))))))))))

@[simp] theorem numLabels_tmPopFirstSubwordRev (kSrc kDst : TapeIdx) :
    (tmPopFirstSubwordRev kSrc kDst).numLabels = 2 := rfl

def tmPopFirstSubwordRev_loop_evalsToInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst) :
    ∀ (w acc restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmPopFirstSubwordRev kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc))
            kDst (encodeDelimWord acc ++ restDst)⟩
        (some ⟨none, default,
          Function.update (Function.update T
            kSrc (encodeDelimWord (unconsDelimWord w).2 ++ restSrc))
            kDst (encodeDelimWord ((unconsDelimWord w).1.reverseAux acc) ++ restDst)⟩)
        ((unconsDelimWord w).1.length + 1)
  | [], acc, restSrc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmPopFirstSubwordRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hne]
  | [b], acc, restSrc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmPopFirstSubwordRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hne]
  | true :: b :: s, acc, restSrc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmPopFirstSubwordRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hne]
  | false :: b :: rest, acc, restSrc, restDst, T => by
    have hstep : (tmPopFirstSubwordRev kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T
            kSrc (encodeDelimWord (false :: b :: rest) ++ restSrc))
            kDst (encodeDelimWord acc ++ restDst)⟩ =
        some ⟨some true, default,
          Function.update (Function.update T kSrc (encodeDelimWord rest ++ restSrc))
            kDst (encodeDelimWord (b :: acc) ++ restDst)⟩ := by
      simp [tmPopFirstSubwordRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hne.symm,
        Function.update_comm hne]
    exact EvalsToInTime.of_step hstep
      (tmPopFirstSubwordRev_loop_evalsToInTime kSrc kDst hne rest (b :: acc) restSrc restDst T)

theorem tmPopFirstSubwordRev_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (w restSrc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmPopFirstSubwordRev kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc)) kDst restDst)
      (Function.update (Function.update T
        kSrc (encodeDelimWord (unconsDelimWord w).2 ++ restSrc))
        kDst (encodeDelimWord (unconsDelimWord w).1.reverse ++ restDst))
      ((unconsDelimWord w).1.length + 2) := by
  have hstep0 : (tmPopFirstSubwordRev kSrc kDst).toFinTM2.step
      ⟨some false, default,
        Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc)) kDst restDst⟩ =
      some ⟨some true, default,
        Function.update (Function.update T kSrc (encodeDelimWord w ++ restSrc))
          kDst (encodeDelimWord [] ++ restDst)⟩ := by
    simp [tmPopFirstSubwordRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  exact ⟨EvalsToInTime.of_step hstep0
    (tmPopFirstSubwordRev_loop_evalsToInTime kSrc kDst hne w [] restSrc restDst T)⟩

/-- **Gadget 15 (`tmPopStreamWord kSrc kTmp kDst`)**: Pops the first subword `(unconsDelimWord w).1`
from the top delimited word `w` on `kSrc` (updating `kSrc` in place to
`encodeDelimWord (unconsDelimWord w).2 ++ restSrc`) and pushes `encodeDelimWord (unconsDelimWord w).1`
onto `kDst` (via `kTmp`) in `2 * (unconsDelimWord w).1.length + 4` steps (`|Λ| = 4`). -/
def tmPopStreamWord (kSrc kTmp kDst : TapeIdx) : BitMachine :=
  (tmPopFirstSubwordRev kSrc kTmp).seq (tmRevMoveWord kTmp kDst)

@[simp] theorem numLabels_tmPopStreamWord (kSrc kTmp kDst : TapeIdx) :
    (tmPopStreamWord kSrc kTmp kDst).numLabels = 4 := rfl

theorem tmPopStreamWord_computesInTime (kSrc kTmp kDst : TapeIdx)
    (hST : kSrc ≠ kTmp) (hTD : kTmp ≠ kDst) (hSD : kSrc ≠ kDst)
    (w restSrc restTmp restDst : List Bool)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmPopStreamWord kSrc kTmp kDst).ComputesInTime
      (Function.update (Function.update (Function.update T
        kSrc (encodeDelimWord w ++ restSrc)) kTmp restTmp) kDst restDst)
      (Function.update (Function.update (Function.update T
        kSrc (encodeDelimWord (unconsDelimWord w).2 ++ restSrc)) kTmp restTmp)
        kDst (encodeDelimWord (unconsDelimWord w).1 ++ restDst))
      (2 * (unconsDelimWord w).1.length + 4) := by
  have hcomm : ∀ a b,
      Function.update (Function.update (Function.update T kDst restDst) kSrc a) kTmp b =
      Function.update (Function.update (Function.update T kSrc a) kTmp b) kDst restDst :=
    fun a b => by rw [Function.update_comm hSD.symm, Function.update_comm hTD.symm]
  have h1 := tmPopFirstSubwordRev_computesInTime kSrc kTmp hST w restSrc restTmp
    (Function.update T kDst restDst)
  rw [hcomm, hcomm] at h1
  have h2 := tmRevMoveWord_computesInTime kTmp kDst hTD (unconsDelimWord w).1.reverse restTmp restDst
    (Function.update T kSrc (encodeDelimWord (unconsDelimWord w).2 ++ restSrc))
  rw [List.length_reverse, List.reverse_reverse] at h2
  have h12 := h1.seq h2
  convert h12 using 1 <;> first | rfl | omega

/-- **Gadget 16 (`tmRawToDelimRev kSrc kDst`)**: Pops a raw undelimited bit-list `xs` from `kSrc`
(until `kSrc` is empty) and pushes `encodeDelimWord xs.reverse` onto `kDst` in `xs.length + 2`
steps (`|Λ| = 2`). -/
def tmRawToDelimRev (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Bool
  main := false
  m := fun lbl =>
    match lbl with
    | false =>
      Turing.TM2.Stmt.push kDst (fun _ => false)
        (Turing.TM2.Stmt.push kDst (fun _ => true)
          (Turing.TM2.Stmt.goto (fun _ => true)))
    | true =>
      Turing.TM2.Stmt.pop kSrc
        (fun _ bOpt =>
          match bOpt with
          | none => (default, true)
          | some b => (⟨b, false, false, false⟩, false))
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
          (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitA)
            (Turing.TM2.Stmt.push kDst (fun _ => false)
              (Turing.TM2.Stmt.load (fun _ => default)
                (Turing.TM2.Stmt.goto (fun _ => true))))))

@[simp] theorem numLabels_tmRawToDelimRev (kSrc kDst : TapeIdx) :
    (tmRawToDelimRev kSrc kDst).numLabels = 2 := rfl

def tmRawToDelimRev_loop_evalsToInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst) :
    ∀ (xs acc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmRawToDelimRev kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T kSrc xs)
            kDst (encodeDelimWord acc ++ restDst)⟩
        (some ⟨none, default,
          Function.update (Function.update T kSrc [])
            kDst (encodeDelimWord (xs.reverseAux acc) ++ restDst)⟩)
        (xs.length + 1)
  | [], acc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmRawToDelimRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hne]
  | b :: xs, acc, restDst, T => by
    have hstep : (tmRawToDelimRev kSrc kDst).toFinTM2.step
        ⟨some true, default,
          Function.update (Function.update T kSrc (b :: xs))
            kDst (encodeDelimWord acc ++ restDst)⟩ =
        some ⟨some true, default,
          Function.update (Function.update T kSrc xs)
            kDst (encodeDelimWord (b :: acc) ++ restDst)⟩ := by
      simp [tmRawToDelimRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hne.symm,
        Function.update_comm hne]
    exact EvalsToInTime.of_step hstep
      (tmRawToDelimRev_loop_evalsToInTime kSrc kDst hne xs (b :: acc) restDst T)

theorem tmRawToDelimRev_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (xs restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmRawToDelimRev kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc xs) kDst restDst)
      (Function.update (Function.update T kSrc []) kDst (encodeDelimWord xs.reverse ++ restDst))
      (xs.length + 2) := by
  have hstep0 : (tmRawToDelimRev kSrc kDst).toFinTM2.step
      ⟨some false, default,
        Function.update (Function.update T kSrc xs) kDst restDst⟩ =
      some ⟨some true, default,
        Function.update (Function.update T kSrc xs)
          kDst (encodeDelimWord [] ++ restDst)⟩ := by
    simp [tmRawToDelimRev, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  exact ⟨EvalsToInTime.of_step hstep0
    (tmRawToDelimRev_loop_evalsToInTime kSrc kDst hne xs [] restDst T)⟩

/-- **Gadget 18 (`tmDelimRevToRaw kSrc kDst`)**: Pops `encodeDelimWord u` from `kSrc` and pushes
raw undelimited `u.reverse` onto `kDst` in `u.length + 1` steps (`|Λ| = 1`). -/
def tmDelimRevToRaw (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kSrc
      (fun _ bOpt => (default, bOpt.getD true))
      (Turing.TM2.Stmt.pop kSrc
        (fun rv bOpt => (⟨bOpt.getD false, false, false, false⟩, rv.2))
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
          (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitA)
            (Turing.TM2.Stmt.load (fun _ => default)
              (Turing.TM2.Stmt.goto (fun _ => ()))))))

@[simp] theorem numLabels_tmDelimRevToRaw (kSrc kDst : TapeIdx) :
    (tmDelimRevToRaw kSrc kDst).numLabels = 1 := rfl

def tmDelimRevToRaw_evalsToInTime_concrete (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst) :
    ∀ (u restSrc accDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)),
      Turing.EvalsToInTime (tmDelimRevToRaw kSrc kDst).toFinTM2.step
        ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc)) kDst accDst⟩
        (some ⟨none, default,
          Function.update (Function.update T kSrc restSrc) kDst (u.reverseAux accDst)⟩)
        (u.length + 1)
  | [], restSrc, accDst, T => by
    refine EvalsToInTime.step_one ?_
    simp [tmDelimRevToRaw, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update_comm hne]
  | b :: u, restSrc, accDst, T => by
    have hstep : (tmDelimRevToRaw kSrc kDst).toFinTM2.step
        ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord (b :: u) ++ restSrc))
            kDst accDst⟩ =
        some ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
            kDst (b :: accDst)⟩ := by
      simp [tmDelimRevToRaw, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update_of_ne hne.symm,
        Function.update_comm hne]
    exact EvalsToInTime.of_step hstep
      (tmDelimRevToRaw_evalsToInTime_concrete kSrc kDst hne u restSrc (b :: accDst) T)

theorem tmDelimRevToRaw_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (u restSrc accDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmDelimRevToRaw kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc)) kDst accDst)
      (Function.update (Function.update T kSrc restSrc) kDst (u.reverse ++ accDst))
      (u.length + 1) := by
  rw [← List.reverseAux_eq]
  exact ⟨tmDelimRevToRaw_evalsToInTime_concrete kSrc kDst hne u restSrc accDst T⟩

/-- **Gadget 19 (`tmDelimIOToRawIO`)**: Unwraps `encodeDelimWord out` on `kIO` into raw undelimited
`out` on `kIO` (`mkTapes8 (encodeDelimWord out) [] [] [] [] [] [] []` $\mapsto$
`mkTapes8 out [] [] [] [] [] [] []`) in `2 * out.length + 3` steps (`|Λ| = 3`). -/
def tmDelimIOToRawIO : BitMachine :=
  (tmRevMoveWord kIO kWork0).seq (tmDelimRevToRaw kWork0 kIO)

@[simp] theorem numLabels_tmDelimIOToRawIO : tmDelimIOToRawIO.numLabels = 3 := rfl

theorem tmDelimIOToRawIO_computesInTime (out : List Bool) :
    tmDelimIOToRawIO.ComputesInTime
      (mkTapes8 (encodeDelimWord out) [] [] [] [] [] [] [])
      (mkTapes8 out [] [] [] [] [] [] [])
      (2 * out.length + 3) := by
  have h1 := tmRevMoveWord_computesInTime kIO kWork0 (by decide) out [] []
    (mkTapes8 [] [] [] [] [] [] [] [])
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at h1
  have h2 := tmDelimRevToRaw_computesInTime kWork0 kIO (by decide) out.reverse [] []
    (mkTapes8 [] [] [] [] [] [] [] [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.append_nil,
    List.length_reverse, List.reverse_reverse] at h2
  have h12 := h1.seq h2
  convert h12 using 1 <;> first | rfl | omega

/-! ## 6. 1-Step Frame Push/Pop Gadgets (`tmFramePush7`, `tmFramePush6`, `tmFramePop7`) -/

/-- **Gadget 22 (`tmFramePush7`)**: Pushes `encodeDelimWord []` (`[true, false]`) onto the 7 stacks
`kWork0..kWork5` and `kSched` in `1` step (`|Λ| = 1`). -/
def tmFramePush7 : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.push kWork0 (fun _ => false)
      (Turing.TM2.Stmt.push kWork0 (fun _ => true)
        (Turing.TM2.Stmt.push kWork1 (fun _ => false)
          (Turing.TM2.Stmt.push kWork1 (fun _ => true)
            (Turing.TM2.Stmt.push kWork2 (fun _ => false)
              (Turing.TM2.Stmt.push kWork2 (fun _ => true)
                (Turing.TM2.Stmt.push kWork3 (fun _ => false)
                  (Turing.TM2.Stmt.push kWork3 (fun _ => true)
                    (Turing.TM2.Stmt.push kWork4 (fun _ => false)
                      (Turing.TM2.Stmt.push kWork4 (fun _ => true)
                        (Turing.TM2.Stmt.push kWork5 (fun _ => false)
                          (Turing.TM2.Stmt.push kWork5 (fun _ => true)
                            (Turing.TM2.Stmt.push kSched (fun _ => false)
                              (Turing.TM2.Stmt.push kSched (fun _ => true)
                                Turing.TM2.Stmt.halt)))))))))))))

@[simp] theorem numLabels_tmFramePush7 : tmFramePush7.numLabels = 1 := rfl

theorem tmFramePush7_computesInTime (xs tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmFramePush7.ComputesInTime
      (mkTapes8 (encodeDelimWord xs ++ tIO) tW0 tW1 tW2 tW3 tW4 tW5 tSch)
      (embedDelimFrame (singleTapeStk xs) (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch))
      1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp only [tmFramePush7, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, Option.some.injEq, Turing.TM2.Cfg.mk.injEq,
    true_and]
  funext k; fin_cases k <;> rfl

/-- **Gadget 23 (`tmFramePush6`)**: Pushes `encodeDelimWord []` (`[true, false]`) onto the 6 stacks
`kWork1..kWork5` and `kSched` in `1` step (`|Λ| = 1`). -/
def tmFramePush6 : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.push kWork1 (fun _ => false)
      (Turing.TM2.Stmt.push kWork1 (fun _ => true)
        (Turing.TM2.Stmt.push kWork2 (fun _ => false)
          (Turing.TM2.Stmt.push kWork2 (fun _ => true)
            (Turing.TM2.Stmt.push kWork3 (fun _ => false)
              (Turing.TM2.Stmt.push kWork3 (fun _ => true)
                (Turing.TM2.Stmt.push kWork4 (fun _ => false)
                  (Turing.TM2.Stmt.push kWork4 (fun _ => true)
                    (Turing.TM2.Stmt.push kWork5 (fun _ => false)
                      (Turing.TM2.Stmt.push kWork5 (fun _ => true)
                        (Turing.TM2.Stmt.push kSched (fun _ => false)
                          (Turing.TM2.Stmt.push kSched (fun _ => true)
                            Turing.TM2.Stmt.halt)))))))))))

@[simp] theorem numLabels_tmFramePush6 : tmFramePush6.numLabels = 1 := rfl

theorem tmFramePush6_computesInTime (xs ys tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmFramePush6.ComputesInTime
      (mkTapes8 (encodeDelimWord xs ++ tIO) (encodeDelimWord ys ++ tW0) tW1 tW2 tW3 tW4 tW5 tSch)
      (embedDelimFrame (twoTapeStk xs ys) (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch))
      1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp only [tmFramePush6, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, Option.some.injEq, Turing.TM2.Cfg.mk.injEq,
    true_and]
  funext k; fin_cases k <;> rfl

/-- **Gadget 24 (`tmFramePop7`)**: Pops `encodeDelimWord []` (`[true, false]`) from the 7 stacks
`kWork0..kWork5` and `kSched` in `1` step (`|Λ| = 1`). -/
def tmFramePop7 : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kWork0 (fun _ _ => default)
      (Turing.TM2.Stmt.pop kWork0 (fun _ _ => default)
        (Turing.TM2.Stmt.pop kWork1 (fun _ _ => default)
          (Turing.TM2.Stmt.pop kWork1 (fun _ _ => default)
            (Turing.TM2.Stmt.pop kWork2 (fun _ _ => default)
              (Turing.TM2.Stmt.pop kWork2 (fun _ _ => default)
                (Turing.TM2.Stmt.pop kWork3 (fun _ _ => default)
                  (Turing.TM2.Stmt.pop kWork3 (fun _ _ => default)
                    (Turing.TM2.Stmt.pop kWork4 (fun _ _ => default)
                      (Turing.TM2.Stmt.pop kWork4 (fun _ _ => default)
                        (Turing.TM2.Stmt.pop kWork5 (fun _ _ => default)
                          (Turing.TM2.Stmt.pop kWork5 (fun _ _ => default)
                            (Turing.TM2.Stmt.pop kSched (fun _ _ => default)
                              (Turing.TM2.Stmt.pop kSched (fun _ _ => default)
                                Turing.TM2.Stmt.halt)))))))))))))

@[simp] theorem numLabels_tmFramePop7 : tmFramePop7.numLabels = 1 := rfl

theorem tmFramePop7_computesInTime (ys tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmFramePop7.ComputesInTime
      (embedDelimFrame (singleTapeStk ys) (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch))
      (mkTapes8 (encodeDelimWord ys ++ tIO) tW0 tW1 tW2 tW3 tW4 tW5 tSch)
      1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp only [tmFramePop7, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, Option.some.injEq, Turing.TM2.Cfg.mk.injEq,
    true_and]
  funext k; fin_cases k <;> rfl

/-! ## 7. State-Indexed Loop Theorem (`loopFinalState`, `loopStepsAux`, `loopDelimWord_state`) -/

/-- Final state reached by iterating `nextSt : α → α` once per bit of `cnt : List Bool`. -/
def loopFinalState {α : Type} (nextSt : α → α) : List Bool → α → α
  | [], st => st
  | _ :: cnt, st => loopFinalState nextSt cnt (nextSt st)

@[simp] theorem loopFinalState_nil {α : Type} (nextSt : α → α) (st : α) :
    loopFinalState nextSt [] st = st := rfl

@[simp] theorem loopFinalState_cons {α : Type} (nextSt : α → α) (b : Bool)
    (cnt : List Bool) (st : α) :
    loopFinalState nextSt (b :: cnt) st = loopFinalState nextSt cnt (nextSt st) := rfl

/-- Total step count of `body.loopDelimWord kCnt` with state-dependent iteration cost `stepCost st`. -/
def loopStepsAux {α : Type} (nextSt : α → α) (stepCost : α → ℕ) :
    List Bool → α → ℕ
  | [], _ => 1
  | _ :: cnt, st => 1 + stepCost st + loopStepsAux nextSt stepCost cnt (nextSt st)

@[simp] theorem loopStepsAux_nil {α : Type} (nextSt : α → α) (stepCost : α → ℕ) (st : α) :
    loopStepsAux nextSt stepCost [] st = 1 := rfl

@[simp] theorem loopStepsAux_cons {α : Type} (nextSt : α → α) (stepCost : α → ℕ)
    (b : Bool) (cnt : List Bool) (st : α) :
    loopStepsAux nextSt stepCost (b :: cnt) st =
      1 + stepCost st + loopStepsAux nextSt stepCost cnt (nextSt st) := rfl

def loopDelimWord_state_evalsToInTime_concrete {α : Type} (kCnt : TapeIdx) (body : BitMachine)
    (nextSt : α → α) (stepCost : α → ℕ)
    (stkOf : α → (∀ k : TapeIdx, List (BitTapeAlphabet k)))
    (hpass : ∀ (st : α) (tailCnt : List Bool),
      Turing.EvalsToInTime body.toFinTM2.step
        ⟨some body.main, default, Function.update (stkOf st) kCnt tailCnt⟩
        (some ⟨none, default, Function.update (stkOf (nextSt st)) kCnt tailCnt⟩)
        (stepCost st)) :
    ∀ (cnt : List Bool) (restCnt : List Bool) (st : α),
      Turing.EvalsToInTime (body.loopDelimWord kCnt).toFinTM2.step
        ⟨some none, default,
          Function.update (stkOf st) kCnt (encodeDelimWord cnt ++ restCnt)⟩
        (some ⟨none, default,
          Function.update (stkOf (loopFinalState nextSt cnt st)) kCnt restCnt⟩)
        (loopStepsAux nextSt stepCost cnt st)
  | [], restCnt, st => by
    refine EvalsToInTime.step_one ?_
    simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, Function.update_self, Function.update_idem, List.head?_cons,
      List.tail_cons, Option.getD_some, cond_true, loopFinalState_nil]
  | b :: cnt, restCnt, st => by
    have hpop : (body.loopDelimWord kCnt).toFinTM2.step
        ⟨some none, default,
          Function.update (stkOf st) kCnt (encodeDelimWord (b :: cnt) ++ restCnt)⟩ =
        some ⟨some (some body.main), default,
          Function.update (stkOf st) kCnt (encodeDelimWord cnt ++ restCnt)⟩ := by
      simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons, List.cons_append,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    have hbody := hpass st (encodeDelimWord cnt ++ restCnt)
    have hbody_lifted := BitMachine.loopDelimWord_body_evalsToInTime_concrete kCnt body hbody
    have ih := loopDelimWord_state_evalsToInTime_concrete kCnt body nextSt stepCost stkOf hpass
      cnt restCnt (nextSt st)
    have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
    have hcomb := EvalsToInTime.trans' hstep1 ih
    simp only [loopStepsAux_cons]
    exact EvalsToInTime.mono hcomb (by omega)

theorem BitMachine.ComputesInTime.loopDelimWord_state {α : Type} (kCnt : TapeIdx) {body : BitMachine}
    (nextSt : α → α) (stepCost : α → ℕ)
    (stkOf : α → (∀ k : TapeIdx, List (BitTapeAlphabet k)))
    (hpass : ∀ (st : α) (tailCnt : List Bool),
      body.ComputesInTime
        (Function.update (stkOf st) kCnt tailCnt)
        (Function.update (stkOf (nextSt st)) kCnt tailCnt)
        (stepCost st))
    (cnt : List Bool) (restCnt : List Bool) (st : α) :
    (body.loopDelimWord kCnt).ComputesInTime
      (Function.update (stkOf st) kCnt (encodeDelimWord cnt ++ restCnt))
      (Function.update (stkOf (loopFinalState nextSt cnt st)) kCnt restCnt)
      (loopStepsAux nextSt stepCost cnt st) :=
  ⟨loopDelimWord_state_evalsToInTime_concrete kCnt body nextSt stepCost stkOf
    (fun st' tailCnt => Classical.choice (hpass st' tailCnt)) cnt restCnt st⟩


end IntMul
