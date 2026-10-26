/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7LinesLine
import SubNLogN.Machine.K1.RotatePar
import WP.W3.Misc
import IntMulTM.SpecFacts

/-!
# Lemma A.9 lines (`Machine/AppC/C7LinesMain.lean`): `C7LinesStmt` from its leaves

Phase 1 of Lemma A.9 (`lem:transfer13`, Appendix A.4 (`sec:transfer-packed`),
eight-line packed shift phase): the eight packed lines `eightOps`, each a Lemma A.8 exchange, a parameterized controlled
rotation (`K1.k4RotateCtlPar_holds`) and the inverse exchange (`C7LinesLine.lean`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

**Program.** Push a `mark` on five private stacks (`T`, three copies of `L = f·K`, `G`); the counter
kernel (`C7LinesSetupStmt`) pushes `natSyms L` three times and `natSyms (N1·2^L·N2)`; then the
eight line kernels run, the array alternating between stack `0` and `T` (eight is even, so it ends
on stack `0`); finally the counters are dropped (`W3_dropNat_holds`) and the marks popped. The
`mark`s make the `TermOK`/`BlkTerm` premises hold over arbitrary initial private stacks.

**Result (0 `sorry`).** `c7Lines_of : C6InterchangeStmt τ → (∀ ε par xF, (ε = 1 ∨ ε = -1) →
par ≤ 1 → K4OffsetCtlParStmt (lineOff ε par xF) J) → C7LinesSetupStmt → C7LinesStmt τ σ` (only the
eight lines of `eightOps`, with `ε = ±1` and `par ∈ {0, 1}`, are used). The three hypotheses are
component leaves: the Lemma A.8 interchange, the Lemma A.9 offset routine (an `O(b^J)` single-pass
bit scan), and the counter kernel (products of counters).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Networks AppC.Corr AppC.C7Aux

/-- **[CONTRACT] Counters of the Lemma A.9 lines.** Named stacks (`Fin 8`): `0` `K`, `1` `f`,
`2` `N1`, `3` `N2` (restored); `natSyms (f·K)` is pushed onto stacks `4`, `5`, `6` and
`natSyms (N1·2^{f·K}·N2)` onto stack `7`. Cost `C·(f·K + |K| + |f| + |N1| + |N2| + 1)²` (`|·|` the
bit length), as for schoolbook multiplications and a shift. -/
def C7LinesSetupStmt : Prop :=
  KContract (Fin 8) Unit fun _ E _ _ _ C P =>
    ∀ (K f N1 N2 : ℕ) (r0 r1 r2 r3 : List Sym) (S : KLoc (Fin 8) E → List Sym),
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
      S (.inl 0) = natSyms K ++ r0 → S (.inl 1) = natSyms f ++ r1 →
      S (.inl 2) = natSyms N1 ++ r2 → S (.inl 3) = natSyms N2 ++ r3 →
      Runs P S
        (Function.update (Function.update (Function.update (Function.update S
          (.inl 4) (natSyms (f * K) ++ S (.inl 4))) (.inl 5) (natSyms (f * K) ++ S (.inl 5)))
          (.inl 6) (natSyms (f * K) ++ S (.inl 6)))
          (.inl 7) (natSyms (N1 * 2 ^ (f * K) * N2) ++ S (.inl 7)))
        (fun _ => True) (C * (f * K + bitLen K + bitLen f + bitLen N1 + bitLen N2 + 1) ^ 2)

namespace AppC.C7LinesAux

/-! ## Lines, flags, small programs -/

/-- The `i`-th line of the eight-operation program. -/
def opOf (i : Fin 8) : Bool × ℤ × ℕ := eightOps.getD i (true, 0, 0)

theorem map_opOf : (List.finRange 8).map opOf = eightOps := by decide

/-- Where the array is after running the lines `is` from the side `b` (`true` = stack `0`). -/
def finalFlag : Bool → List (Fin 8) → Bool
  | b, [] => b
  | b, _ :: t => finalFlag (!b) t

/-- Pop and discard (any register type). -/
def popD {K σ : Type} (k : K) : Prog K (fun _ => Sym) σ := .pop k (fun r _ => r)

theorem runs_popD {K σ : Type} [DecidableEq K] (k : K) (x : Sym) (rest : List Sym)
    (S : K → List Sym) (hS : S k = x :: rest) :
    Runs (popD (σ := σ) k) S (Function.update S k rest) (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ⟨v, 1, ?_, trivial, le_refl _⟩
  have h := Eval.pop (Γ := fun _ => Sym) [] k (fun (r : σ) (_ : Option Sym) => r) v S
  rw [hS] at h
  exact h

theorem closed_popD {K σ : Type} (k : K) : (popD (σ := σ) k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, popD]

theorem runs_loadId {K σ : Type} [DecidableEq K] (S : K → List Sym) :
    Runs (Prog.load (K := K) (Γ := fun _ => Sym) (σ := σ) id) S S (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v S, trivial, le_refl _⟩

theorem closed_loadId {K σ : Type} :
    (Prog.load (K := K) (Γ := fun _ => Sym) (σ := σ) id).Closed := by
  simp [Prog.Closed, Prog.FreeBelow]

theorem permByInv_id {α : Type} [Inhabited α] (w : List α) : permByInv (fun y => y) w = w := by
  apply List.ext_getElem
  · simp [permByInv_length]
  · intro n h1 h2
    simp [permByInv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! ## Layout -/

/-- Private scratch of the lines phase: five own stacks (`T`, three copies of `L`, `G`), and the
scratch of the Lemma A.8 kernel, of the eight rotation kernels, of the counter kernel and of the drop
kernel. -/
abbrev MainE (E₆ : Type) (Er : Fin 8 → Type) (Es : Type) (md : ℕ) : Type :=
  Fin 5 ⊕ E₆ ⊕ (Σ i, Er i) ⊕ Es ⊕ Fin md

instance instDecEqMainE {E₆ : Type} {Er : Fin 8 → Type} {Es : Type} {md : ℕ} [DecidableEq E₆]
    [∀ i, DecidableEq (Er i)] [DecidableEq Es] : DecidableEq (MainE E₆ Er Es md) :=
  inferInstanceAs (DecidableEq (Fin 5 ⊕ E₆ ⊕ (Σ i, Er i) ⊕ Es ⊕ Fin md))

instance (priority := high) instDecEqMainL {E₆ : Type} {Er : Fin 8 → Type} {Es : Type} {md : ℕ}
    [DecidableEq E₆] [∀ i, DecidableEq (Er i)] [DecidableEq Es] :
    DecidableEq (KLoc (Fin 8) (MainE E₆ Er Es md)) :=
  @instDecidableEqSum (Fin 8) (MainE E₆ Er Es md) _ instDecEqMainE

instance instFintypeMainE {E₆ : Type} {Er : Fin 8 → Type} {Es : Type} {md : ℕ} [Fintype E₆]
    [∀ i, Fintype (Er i)] [Fintype Es] : Fintype (MainE E₆ Er Es md) :=
  inferInstanceAs (Fintype (Fin 5 ⊕ E₆ ⊕ (Σ i, Er i) ⊕ Es ⊕ Fin md))

section Layout

variable {E₆ : Type} {Er : Fin 8 → Type} {Es : Type} {md : ℕ}

/-- Own private stack `k` (`0` = `T`, `1, 2, 3` = copies of `L`, `4` = `G`). -/
def own (k : Fin 5) : KLoc (Fin 8) (MainE E₆ Er Es md) := .inr (.inl k)

/-- A numeric code of a stack (`0..7` named, `8..12` own, `100` kernel scratch). -/
def code : KLoc (Fin 8) (MainE E₆ Er Es md) → ℕ
  | .inl i => i.val
  | .inr (.inl k) => 8 + k.val
  | .inr (.inr _) => 100

/-- Named-stack map of the line call: source, destination, `L, L, L, G, K, ρ, N1, N2, N3, R`. -/
def lineSlot (onA : Bool) (k : Fin 12) : KLoc (Fin 8) (MainE E₆ Er Es md) :=
  ![if onA then .inl 0 else own 0, if onA then own 0 else .inl 0, own 1, own 2, own 3, own 4,
    .inl 1, .inl 2, .inl 4, .inl 5, .inl 6, .inl 7] k

theorem code_lineSlot (onA : Bool) (k : Fin 12) :
    code (lineSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA k) =
      (![if onA then 0 else 8, if onA then 8 else 0, 9, 10, 11, 12, 1, 2, 4, 5, 6, 7] k : ℕ) := by
  fin_cases k <;> cases onA <;> rfl

theorem lineSlot_injective (onA : Bool) :
    Function.Injective (lineSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA) := by
  have hv : Function.Injective
      (fun k : Fin 12 => (![if onA then 0 else 8, if onA then 8 else 0, 9, 10, 11, 12, 1, 2, 4, 5,
        6, 7] k : ℕ)) := by
    cases onA <;> decide
  intro a b h
  have := congrArg code h
  rw [code_lineSlot, code_lineSlot] at this
  exact hv this

theorem code_lineSlot_lt (onA : Bool) (k : Fin 12) :
    code (lineSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA k) < 13 := by
  rw [code_lineSlot]
  fin_cases k <;> cases onA <;> decide

/-- Stack map of line `i` (array from `onA ? 0 : T` to the other one). -/
def ιL (onA : Bool) (i : Fin 8) : KLoc (Fin 12) (E₆ ⊕ Er i) → KLoc (Fin 8) (MainE E₆ Er Es md)
  | .inl k => lineSlot onA k
  | .inr (.inl e) => .inr (.inr (.inl e))
  | .inr (.inr e) => .inr (.inr (.inr (.inl ⟨i, e⟩)))

theorem ιL_injective (onA : Bool) (i : Fin 8) :
    Function.Injective (ιL (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA i) := by
  rintro (a | a | a) (b | b | b) h
  · exact congrArg Sum.inl (lineSlot_injective onA h)
  · have h1 : code (lineSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA a) = 100 :=
      congrArg code h
    have h2 := code_lineSlot_lt (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA a
    omega
  · have h1 : code (lineSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA a) = 100 :=
      congrArg code h
    have h2 := code_lineSlot_lt (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA a
    omega
  · have h1 : 100 = code (lineSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA b) :=
      congrArg code h
    have h2 := code_lineSlot_lt (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA b
    omega
  · simp only [ιL, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]
  · simp [ιL] at h
  · have h1 : 100 = code (lineSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA b) :=
      congrArg code h
    have h2 := code_lineSlot_lt (E₆ := E₆) (Er := Er) (Es := Es) (md := md) onA b
    omega
  · simp [ιL] at h
  · simp only [ιL, Sum.inr.injEq, Sum.inl.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    rw [h]

/-- Named-stack map of the counter kernel: `K, f, N1, N2`, then the four counter stacks. -/
def setSlot (k : Fin 8) : KLoc (Fin 8) (MainE E₆ Er Es md) :=
  ![.inl 1, .inl 3, .inl 4, .inl 5, own 1, own 2, own 3, own 4] k

theorem code_setSlot (k : Fin 8) :
    code (setSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) k) =
      (![1, 3, 4, 5, 9, 10, 11, 12] k : ℕ) := by
  fin_cases k <;> rfl

theorem code_setSlot_lt (k : Fin 8) :
    code (setSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) k) < 13 := by
  rw [code_setSlot]
  fin_cases k <;> decide

/-- Stack map of the counter kernel. -/
def ιS : KLoc (Fin 8) Es → KLoc (Fin 8) (MainE E₆ Er Es md)
  | .inl k => setSlot k
  | .inr e => .inr (.inr (.inr (.inr (.inl e))))

theorem ιS_injective : Function.Injective (ιS (E₆ := E₆) (Er := Er) (Es := Es) (md := md)) := by
  have hv : Function.Injective (fun k : Fin 8 => (![1, 3, 4, 5, 9, 10, 11, 12] k : ℕ)) := by
    decide
  rintro (a | a) (b | b) h
  · have := congrArg code h
    simp only [ιS] at this
    rw [code_setSlot, code_setSlot] at this
    exact congrArg Sum.inl (hv this)
  · have h1 : code (setSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) a) = 100 :=
      congrArg code h
    have h2 := code_setSlot_lt (E₆ := E₆) (Er := Er) (Es := Es) (md := md) a
    omega
  · have h1 : 100 = code (setSlot (E₆ := E₆) (Er := Er) (Es := Es) (md := md) b) :=
      congrArg code h
    have h2 := code_setSlot_lt (E₆ := E₆) (Er := Er) (Es := Es) (md := md) b
    omega
  · simp only [ιS, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

/-- Stack map of the drop kernel on stack `k` (an own stack). -/
def ιD (k : Fin 5) : Loc 1 md → KLoc (Fin 8) (MainE E₆ Er Es md)
  | .inl _ => own k
  | .inr j => .inr (.inr (.inr (.inr (.inr j))))

theorem ιD_injective (k : Fin 5) :
    Function.Injective (ιD (E₆ := E₆) (Er := Er) (Es := Es) (md := md) k) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Subsingleton.elim a b)
  · simp [ιD, own] at h
  · simp [ιD, own] at h
  · simp only [ιD, Sum.inr.injEq] at h
    rw [h]

end Layout

/-! ## Register lenses -/

section Lenses

variable {R₆ Rs Rd : Type} {Rr : Fin 8 → Type}

/-- Registers of line `i`: the Lemma A.8 registers and those of rotation `i`. -/
def lensL (i : Fin 8) : Lens (R₆ × (∀ j, Rr j) × Rs × Rd) (R₆ × Rr i) where
  get r := (r.1, r.2.1 i)
  set r x := (x.1, Function.update r.2.1 i x.2, r.2.2)
  get_set r x := by simp
  set_get r := by simp
  set_set r x y := by simp

/-- Registers of the counter kernel. -/
def lensS : Lens (R₆ × (∀ j, Rr j) × Rs × Rd) Rs :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))

/-- Registers of the drop kernel. -/
def lensD : Lens (R₆ × (∀ j, Rr j) × Rs × Rd) Rd :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))

end Lenses

/-! ## The eight lines -/

section Lines

variable {E₆ : Type} {Er : Fin 8 → Type} {Es : Type} {md : ℕ}
  {R₆ Rs Rd : Type} {Rr : Fin 8 → Type}

/-- The lines `is`, the first one moving the array away from the side `onA`. -/
def linesP (σ : Equiv.Perm (Fin 3)) (P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆)
    (Pr : ∀ i, Prog (KLoc (Fin 10) (Er i)) (fun _ => Sym) (Rr i)) :
    Bool → List (Fin 8) →
      Prog (KLoc (Fin 8) (MainE E₆ Er Es md)) (fun _ => Sym) (R₆ × (∀ j, Rr j) × Rs × Rd)
  | _, [] => .load id
  | onA, i :: is => .seq (callInj (ιL onA i) (lensL i) (lineProg (σ.symm (tgtName (opOf i))) P₆ (Pr i)))
      (linesP σ P₆ Pr (!onA) is)

theorem closed_linesP (σ : Equiv.Perm (Fin 3)) {P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆}
    {Pr : ∀ i, Prog (KLoc (Fin 10) (Er i)) (fun _ => Sym) (Rr i)} (h6 : P₆.Closed)
    (hr : ∀ i, (Pr i).Closed) :
    ∀ (onA : Bool) (is : List (Fin 8)),
      (linesP (Es := Es) (md := md) (Rs := Rs) (Rd := Rd) σ P₆ Pr onA is).Closed
  | _, [] => closed_loadId
  | onA, i :: is => ⟨closed_callInj _ _ (closed_lineProg _ h6 (hr i)), closed_linesP σ h6 hr (!onA) is⟩

theorem own_ne_inl (k : Fin 5) (i : Fin 8) :
    (own k : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ .inl i := by simp [own]

theorem own_ne_own {k k' : Fin 5} (h : k ≠ k') :
    (own k : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own k' := by simp [own, h]

variable [DecidableEq E₆] [∀ i, DecidableEq (Er i)] [DecidableEq Es]

/-- Stacks during the lines: the base stacks `B` (whose stack `0` holds `rest`) with the array `w`
on stack `0` (`onA`) or on top of `T`. -/
def lineSt (B : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym) (rest : List Sym) (onA : Bool)
    (w : List (List Bool)) : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym :=
  if onA then Function.update B (.inl 0) (arrSyms w ++ rest)
  else Function.update B (own 0) (arrSyms w ++ B (own 0))

/-- The base-stack hypotheses of the lines phase. -/
structure LinesBase (B : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym) (rest : List Sym)
    (K ρ f N1 N2 N3 R : ℕ) : Prop where
  hA : B (.inl 0) = rest
  hrest : BlkTerm rest
  hT : BlkTerm (B (own 0))
  hL1 : ∃ t, B (own 1) = natSyms (f * K) ++ t ∧ TermOK t
  hL2 : ∃ t, B (own 2) = natSyms (f * K) ++ t ∧ TermOK t
  hL3 : ∃ t, B (own 3) = natSyms (f * K) ++ t ∧ TermOK t
  hG : ∃ t, B (own 4) = natSyms (N1 * 2 ^ (f * K) * N2) ++ t ∧ TermOK t
  hK : ∃ t, B (.inl 1) = natSyms K ++ t ∧ TermOK t
  hρ : ∃ t, B (.inl 2) = natSyms ρ ++ t ∧ TermOK t
  hN1 : ∃ t, B (.inl 4) = natSyms N1 ++ t ∧ TermOK t
  hN2 : ∃ t, B (.inl 5) = natSyms N2 ++ t ∧ TermOK t
  hN3 : ∃ t, B (.inl 6) = natSyms N3 ++ t ∧ TermOK t
  hR : ∃ t, B (.inl 7) = natSyms R ++ t ∧ TermOK t

/-- **One line call** in the lines layout. -/
theorem lineStep (τ : ℝ) (σ : Equiv.Perm (Fin 3)) {C₆ : ℕ} {Cr : Fin 8 → ℕ}
    {P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆}
    {Pr : ∀ i, Prog (KLoc (Fin 10) (Er i)) (fun _ => Sym) (Rr i)}
    (h6 : C6Body τ C₆ P₆) (hr : ∀ i, RotBody (lineOffOp σ (opOf i)) (Cr i) (Pr i))
    {K ρ f N0 N1 N2 N3 R : ℕ} {rest : List Sym} {B : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym}
    (hK : 6 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) (hB : LinesBase B rest K ρ f N1 N2 N3 R) (onA : Bool) (i : Fin 8)
    (w : List (List Bool))
    (hlen : w.length = N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3)
    (hrec : ∀ p ∈ w, p.length = R) :
    Runs (callInj (ιL onA i) (lensL (Rs := Rs) (Rd := Rd) i)
        (lineProg (σ.symm (tgtName (opOf i))) P₆ (Pr i)))
      (lineSt B rest onA w)
      (lineSt B rest (!onA) (permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w)) (fun _ => True)
      ((2 * C₆ + Cr i) * (⌈(vol w : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ + 1)) := by
  obtain ⟨t1, h1, ht1⟩ := hB.hL1
  obtain ⟨t2, h2, ht2⟩ := hB.hL2
  obtain ⟨t3, h3, ht3⟩ := hB.hL3
  obtain ⟨t4, h4, ht4⟩ := hB.hG
  obtain ⟨t6, h6', ht6⟩ := hB.hK
  obtain ⟨t7, h7, ht7⟩ := hB.hρ
  obtain ⟨t8, h8, ht8⟩ := hB.hN1
  obtain ⟨t9, h9, ht9⟩ := hB.hN2
  obtain ⟨t10, h10, ht10⟩ := hB.hN3
  obtain ⟨t11, h11, ht11⟩ := hB.hR
  cases onA
  · -- array on `T`, moving to stack `0`
    set Bw := lineSt B rest false w with hBw
    have hBw' : Bw = Function.update B (own 0) (arrSyms w ++ B (own 0)) := rfl
    have hx : ∀ x, x ≠ own 0 → Bw x = B x := fun x hx => by
      rw [hBw']; exact Function.update_of_ne hx _ _
    have e := line_runs τ σ (opOf i) h6 (hr i) (S := Bw ∘ ιL false i) (rest := B (own 0))
      hK hρ hf hN0 hN1 hN2 hN3 hlen hrec hB.hT
      (by show BlkTerm (Bw (.inl 0)); rw [hx _ (own_ne_inl 0 0).symm, hB.hA]; exact hB.hrest)
      ht1 ht2 ht3 ht4 ht6 ht7 ht8 ht9 ht10 ht11
      (by show Bw (own 0) = _; rw [hBw']; exact Function.update_self _ _ _)
      (by show Bw (own 1) = _; rw [hx _ (own_ne_own (by decide))]; exact h1)
      (by show Bw (own 2) = _; rw [hx _ (own_ne_own (by decide))]; exact h2)
      (by show Bw (own 3) = _; rw [hx _ (own_ne_own (by decide))]; exact h3)
      (by show Bw (own 4) = _; rw [hx _ (own_ne_own (by decide))]; exact h4)
      (by show Bw (.inl 1) = _; rw [hx _ (own_ne_inl 0 1).symm]; exact h6')
      (by show Bw (.inl 2) = _; rw [hx _ (own_ne_inl 0 2).symm]; exact h7)
      (by show Bw (.inl 4) = _; rw [hx _ (own_ne_inl 0 4).symm]; exact h8)
      (by show Bw (.inl 5) = _; rw [hx _ (own_ne_inl 0 5).symm]; exact h9)
      (by show Bw (.inl 6) = _; rw [hx _ (own_ne_inl 0 6).symm]; exact h10)
      (by show Bw (.inl 7) = _; rw [hx _ (own_ne_inl 0 7).symm]; exact h11)
    have X := runs_call_upd2 (ιL_injective false i) (lensL (Rs := Rs) (Rd := Rd) i)
      (.inl 0) (.inl 1) _ _ e
    refine WP.W9comp.runs_congr X ?_
    show Function.update (Function.update Bw (own 0) (B (own 0))) (.inl 0)
        (arrSyms (permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w) ++ Bw (.inl 0)) =
      Function.update B (.inl 0) (arrSyms (permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w) ++ rest)
    rw [hx _ (own_ne_inl 0 0).symm, hB.hA, hBw', Function.update_idem, Function.update_eq_self]
  · -- array on stack `0`, moving to `T`
    set Bw := lineSt B rest true w with hBw
    have hBw' : Bw = Function.update B (.inl 0) (arrSyms w ++ rest) := rfl
    have hx : ∀ x, x ≠ .inl 0 → Bw x = B x := fun x hx => by
      rw [hBw']; exact Function.update_of_ne hx _ _
    have e := line_runs τ σ (opOf i) h6 (hr i) (S := Bw ∘ ιL true i) (rest := rest)
      hK hρ hf hN0 hN1 hN2 hN3 hlen hrec hB.hrest
      (by show BlkTerm (Bw (own 0)); rw [hx _ (own_ne_inl 0 0)]; exact hB.hT)
      ht1 ht2 ht3 ht4 ht6 ht7 ht8 ht9 ht10 ht11
      (by show Bw (.inl 0) = _; rw [hBw']; exact Function.update_self _ _ _)
      (by show Bw (own 1) = _; rw [hx _ (own_ne_inl 1 0)]; exact h1)
      (by show Bw (own 2) = _; rw [hx _ (own_ne_inl 2 0)]; exact h2)
      (by show Bw (own 3) = _; rw [hx _ (own_ne_inl 3 0)]; exact h3)
      (by show Bw (own 4) = _; rw [hx _ (own_ne_inl 4 0)]; exact h4)
      (by show Bw (.inl 1) = _; rw [hx _ (by simp)]; exact h6')
      (by show Bw (.inl 2) = _; rw [hx _ (by simp)]; exact h7)
      (by show Bw (.inl 4) = _; rw [hx _ (by simp)]; exact h8)
      (by show Bw (.inl 5) = _; rw [hx _ (by simp)]; exact h9)
      (by show Bw (.inl 6) = _; rw [hx _ (by simp)]; exact h10)
      (by show Bw (.inl 7) = _; rw [hx _ (by simp)]; exact h11)
    have X := runs_call_upd2 (ιL_injective true i) (lensL (Rs := Rs) (Rd := Rd) i)
      (.inl 0) (.inl 1) _ _ e
    refine WP.W9comp.runs_congr X ?_
    show Function.update (Function.update Bw (.inl 0) rest) (own 0)
        (arrSyms (permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w) ++ Bw (own 0)) =
      Function.update B (own 0) (arrSyms (permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w) ++ B (own 0))
    rw [hx _ (own_ne_inl 0 0), hBw', Function.update_idem, ← hB.hA, Function.update_eq_self]

/-- **The lines `is`** from the side `onA`. -/
theorem lines_runs (τ : ℝ) (σ : Equiv.Perm (Fin 3)) {C₆ : ℕ} {Cr : Fin 8 → ℕ}
    {P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆}
    {Pr : ∀ i, Prog (KLoc (Fin 10) (Er i)) (fun _ => Sym) (Rr i)}
    (h6 : C6Body τ C₆ P₆) (hr : ∀ i, RotBody (lineOffOp σ (opOf i)) (Cr i) (Pr i))
    {K ρ f N0 N1 N2 N3 R : ℕ} {rest : List Sym} {B : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym}
    (hK : 6 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) (hB : LinesBase B rest K ρ f N1 N2 N3 R) :
    ∀ (is : List (Fin 8)) (onA : Bool) (w : List (List Bool)),
      w.length = N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 →
      (∀ p ∈ w, p.length = R) →
      Runs (linesP (Rs := Rs) (Rd := Rd) σ P₆ Pr onA is) (lineSt B rest onA w)
        (lineSt B rest (finalFlag onA is)
          (permByInv (linesPull σ K ρ f N1 N2 N3 (is.map opOf)) w)) (fun _ => True)
        ((is.map fun i => 2 * C₆ + Cr i).sum *
          (⌈(((N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) * (R + 1) : ℕ) : ℝ) *
            (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ + 1) + 1)
  | [], onA, w, _, _ => by
    simp only [linesP, finalFlag, List.map_nil, linesPull, List.sum_nil, zero_mul, zero_add]
    rw [permByInv_id]
    exact runs_loadId _
  | i :: is, onA, w, hlen, hrec => by
    have hK0 : 0 < K := by omega
    have X1 := lineStep (Rs := Rs) (Rd := Rd) τ σ h6 hr hK hρ hf hN0 hN1 hN2 hN3 hB onA i w hlen hrec
    have hpl : ∀ y < w.length, linePull σ (opOf i) K ρ f N1 N2 N3 y < w.length := fun y hy => by
      rw [hlen] at hy ⊢
      rw [linePull_eq σ (opOf i) hK0 hN1 hN2 hN3 hy]
      exact c7Lift_lt hN1 hN2 hN3 σ _ (fun t ht => packedLine_inBox _ ht) hy
    have hlen' : (permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w).length =
        N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 :=
      (permByInv_length _ _).trans hlen
    have hrec' : ∀ p ∈ permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w, p.length = R :=
      fun p hp => hrec p (permByInv_mem hpl hp)
    have X2 := lines_runs τ σ h6 hr hK hρ hf hN0 hN1 hN2 hN3 hB is (!onA) _ hlen' hrec'
    have X := WP.W9comp.runs_seq X1 X2
    have hvol : vol w = (N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) * (R + 1) := by
      rw [vol_of_len hrec, hlen]
    have hcomp : permByInv (linesPull σ K ρ f N1 N2 N3 (is.map opOf))
        (permByInv (linePull σ (opOf i) K ρ f N1 N2 N3) w) =
        permByInv (linesPull σ K ρ f N1 N2 N3 ((i :: is).map opOf)) w := by
      rw [permByInv_permByInv]
      · rfl
      · intro y hy
        rw [hlen] at hy ⊢
        exact (linesPull_eq σ hK0 hN1 hN2 hN3 (is.map opOf) y hy).2
    rw [hcomp, hvol] at X
    refine WP.W9comp.runs_mono X (fun _ _ => trivial) (le_of_eq ?_)
    simp only [List.map_cons, List.sum_cons]
    ring

end Lines

/-! ## Arithmetic for the cost -/

theorem sq_le_two_mul_two_pow : ∀ x : ℕ, x ^ 2 ≤ 2 * 2 ^ x
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | n + 4 => by
    have ih := sq_le_two_mul_two_pow (n + 3)
    have h1 : (n + 4) ^ 2 ≤ 2 * (n + 3) ^ 2 :=
      Nat.le.intro (by ring : (n + 4) ^ 2 + (n ^ 2 + 4 * n + 2) = 2 * (n + 3) ^ 2)
    calc (n + 4) ^ 2 ≤ 2 * (n + 3) ^ 2 := h1
      _ ≤ 2 * (2 * 2 ^ (n + 3)) := Nat.mul_le_mul_left _ ih
      _ = 2 * 2 ^ (n + 4) := by ring

theorem two_pow_bitLen_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ bitLen n ≤ 2 * n := by
  have hb : bitLen n = Nat.size n := IntMulTM.length_encodeNat n
  have hs : 0 < Nat.size n := Nat.size_pos.mpr hn
  have h1 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  rw [hb]
  calc 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * n := by omega

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := by
  have hb : bitLen n = Nat.size n := IntMulTM.length_encodeNat n
  rw [hb]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- The counter kernel's cost is at most `64·M`. -/
theorem setup_cost_le {K f N0 N1 N2 N3 : ℕ} (hK : 1 ≤ K) (hf : 1 ≤ f) (hN0 : 1 ≤ N0)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) :
    (f * K + bitLen K + bitLen f + bitLen N1 + bitLen N2 + 1) ^ 2 ≤
      64 * (N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) := by
  have h1 := sq_le_two_mul_two_pow (f * K + bitLen K + bitLen f + bitLen N1 + bitLen N2 + 1)
  have hK2 := two_pow_bitLen_le hK
  have hf2 := two_pow_bitLen_le hf
  have hN12 := two_pow_bitLen_le hN1
  have hN22 := two_pow_bitLen_le hN2
  have hL : f * K < 2 ^ (f * K) := Nat.lt_two_pow_self
  have hP : 2 ^ (f * K + bitLen K + bitLen f + bitLen N1 + bitLen N2 + 1) =
      2 ^ (f * K) * 2 ^ bitLen K * 2 ^ bitLen f * 2 ^ bitLen N1 * 2 ^ bitLen N2 * 2 := by
    simp only [pow_add, pow_one]
  have hQ : 2 ^ (f * K) * 2 ^ bitLen K * 2 ^ bitLen f * 2 ^ bitLen N1 * 2 ^ bitLen N2 * 2 ≤
      2 ^ (f * K) * (2 * K) * (2 * f) * (2 * N1) * (2 * N2) * 2 := by
    gcongr
  have hR : 2 ^ (f * K) * (2 * K) * (2 * f) * (2 * N1) * (2 * N2) * 2 ≤
      32 * (N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) := by
    have hKf : K * f ≤ 2 ^ (f * K) := by rw [mul_comm]; exact hL.le
    have h2 : 1 ≤ 2 ^ (f * K) := Nat.one_le_two_pow
    calc 2 ^ (f * K) * (2 * K) * (2 * f) * (2 * N1) * (2 * N2) * 2
        = 32 * (2 ^ (f * K) * (K * f) * N1 * N2) := by ring
      _ ≤ 32 * (2 ^ (f * K) * 2 ^ (f * K) * N1 * N2) := by gcongr
      _ = 32 * (1 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 1 * 1) := by ring
      _ ≤ 32 * (N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) := by gcongr
  rw [hP] at h1
  omega

/-- The register file of the lines phase. -/
abbrev MainR (R₆ : Type) (Rr : Fin 8 → Type) (Rs Rd : Type) : Type := R₆ × (∀ j, Rr j) × Rs × Rd

/-! ## The main program -/

section MainProg

variable {E₆ : Type} {Er : Fin 8 → Type} {Es : Type} {md : ℕ}
  {R₆ Rs Rd : Type} {Rr : Fin 8 → Type}

/-- Push a `mark` on the five own stacks. -/
def pushMarks : Prog (KLoc (Fin 8) (MainE E₆ Er Es md)) (fun _ => Sym) (MainR R₆ Rr Rs Rd) :=
  .seq (WP.W9comp.pushConst (own 0) .mark) (.seq (WP.W9comp.pushConst (own 1) .mark)
    (.seq (WP.W9comp.pushConst (own 2) .mark) (.seq (WP.W9comp.pushConst (own 3) .mark)
      (WP.W9comp.pushConst (own 4) .mark))))

/-- Pop the five `mark`s. -/
def popMarks : Prog (KLoc (Fin 8) (MainE E₆ Er Es md)) (fun _ => Sym) (MainR R₆ Rr Rs Rd) :=
  .seq (popD (own 0)) (.seq (popD (own 1)) (.seq (popD (own 2)) (.seq (popD (own 3))
    (popD (own 4)))))

/-- Drop the four counters. -/
def dropsP (Pd : Prog (Loc 1 md) (fun _ => Sym) Rd) :
    Prog (KLoc (Fin 8) (MainE E₆ Er Es md)) (fun _ => Sym) (MainR R₆ Rr Rs Rd) :=
  .seq (callInj (ιD 1) lensD Pd) (.seq (callInj (ιD 2) lensD Pd)
    (.seq (callInj (ιD 3) lensD Pd) (callInj (ιD 4) lensD Pd)))

/-- **The lines phase.** -/
def mainProg (σ : Equiv.Perm (Fin 3)) (P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆)
    (Pr : ∀ i, Prog (KLoc (Fin 10) (Er i)) (fun _ => Sym) (Rr i))
    (Ps : Prog (KLoc (Fin 8) Es) (fun _ => Sym) Rs) (Pd : Prog (Loc 1 md) (fun _ => Sym) Rd) :
    Prog (KLoc (Fin 8) (MainE E₆ Er Es md)) (fun _ => Sym) (MainR R₆ Rr Rs Rd) :=
  .seq pushMarks (.seq (callInj ιS lensS Ps) (.seq (linesP σ P₆ Pr true (List.finRange 8))
    (.seq (dropsP Pd) popMarks)))

theorem closed_mainProg (σ : Equiv.Perm (Fin 3)) {P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆}
    {Pr : ∀ i, Prog (KLoc (Fin 10) (Er i)) (fun _ => Sym) (Rr i)}
    {Ps : Prog (KLoc (Fin 8) Es) (fun _ => Sym) Rs} {Pd : Prog (Loc 1 md) (fun _ => Sym) Rd}
    (h6 : P₆.Closed) (hr : ∀ i, (Pr i).Closed) (hs : Ps.Closed) (hd : Pd.Closed) :
    (mainProg σ P₆ Pr Ps Pd).Closed :=
  ⟨⟨WP.W9comp.closed_pushConst _ _, WP.W9comp.closed_pushConst _ _, WP.W9comp.closed_pushConst _ _,
      WP.W9comp.closed_pushConst _ _, WP.W9comp.closed_pushConst _ _⟩,
    closed_callInj _ _ hs, closed_linesP σ h6 hr true _,
    ⟨closed_callInj _ _ hd, closed_callInj _ _ hd, closed_callInj _ _ hd, closed_callInj _ _ hd⟩,
    closed_popD _, closed_popD _, closed_popD _, closed_popD _, closed_popD _⟩

variable [DecidableEq E₆] [∀ i, DecidableEq (Er i)] [DecidableEq Es]

/-- The `mark`ed stacks. -/
def markUp (S : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym) :
    KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    (own 0) (.mark :: S (own 0))) (own 1) (.mark :: S (own 1))) (own 2) (.mark :: S (own 2)))
    (own 3) (.mark :: S (own 3))) (own 4) (.mark :: S (own 4))

theorem runs_pushMarks (S : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym) :
    Runs (pushMarks (R₆ := R₆) (Rr := Rr) (Rs := Rs) (Rd := Rd)) S (markUp S) (fun _ => True) 5 := by
  have e1 := WP.W9comp.runs_pushConst (σ := MainR R₆ Rr Rs Rd) (own 0) Sym.mark S
  have e2 := WP.W9comp.runs_pushConst (σ := MainR R₆ Rr Rs Rd) (own 1) Sym.mark
    (Function.update S (own 0) (.mark :: S (own 0)))
  rw [Function.update_of_ne (own_ne_own (by decide))] at e2
  have e3 := WP.W9comp.runs_pushConst (σ := MainR R₆ Rr Rs Rd) (own 2) Sym.mark
    (Function.update (Function.update S (own 0) (.mark :: S (own 0))) (own 1) (.mark :: S (own 1)))
  rw [Function.update_of_ne (own_ne_own (by decide)), Function.update_of_ne (own_ne_own (by decide))]
    at e3
  have e4 := WP.W9comp.runs_pushConst (σ := MainR R₆ Rr Rs Rd) (own 3) Sym.mark
    (Function.update (Function.update (Function.update S (own 0) (.mark :: S (own 0))) (own 1)
      (.mark :: S (own 1))) (own 2) (.mark :: S (own 2)))
  rw [Function.update_of_ne (own_ne_own (by decide)), Function.update_of_ne (own_ne_own (by decide)),
    Function.update_of_ne (own_ne_own (by decide))] at e4
  have e5 := WP.W9comp.runs_pushConst (σ := MainR R₆ Rr Rs Rd) (own 4) Sym.mark
    (Function.update (Function.update (Function.update (Function.update S (own 0)
      (.mark :: S (own 0))) (own 1) (.mark :: S (own 1))) (own 2) (.mark :: S (own 2))) (own 3)
      (.mark :: S (own 3)))
  rw [Function.update_of_ne (own_ne_own (by decide)), Function.update_of_ne (own_ne_own (by decide)),
    Function.update_of_ne (own_ne_own (by decide)), Function.update_of_ne (own_ne_own (by decide))]
    at e5
  exact WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 (WP.W9comp.runs_seq e3
    (WP.W9comp.runs_seq e4 e5)))

/-- Popping the five `mark`s restores the own stacks. -/
theorem runs_popMarks (S X : KLoc (Fin 8) (MainE E₆ Er Es md) → List Sym)
    (hX : ∀ k : Fin 5, X (own k) = .mark :: S (own k)) :
    Runs (popMarks (R₆ := R₆) (Rr := Rr) (Rs := Rs) (Rd := Rd)) X
      (Function.update (Function.update (Function.update (Function.update (Function.update X
        (own 0) (S (own 0))) (own 1) (S (own 1))) (own 2) (S (own 2))) (own 3) (S (own 3)))
        (own 4) (S (own 4))) (fun _ => True) 5 := by
  have n10 : (own 1 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 0 := own_ne_own (by decide)
  have n20 : (own 2 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 0 := own_ne_own (by decide)
  have n21 : (own 2 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 1 := own_ne_own (by decide)
  have n30 : (own 3 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 0 := own_ne_own (by decide)
  have n31 : (own 3 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 1 := own_ne_own (by decide)
  have n32 : (own 3 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 2 := own_ne_own (by decide)
  have n40 : (own 4 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 0 := own_ne_own (by decide)
  have n41 : (own 4 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 1 := own_ne_own (by decide)
  have n42 : (own 4 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 2 := own_ne_own (by decide)
  have n43 : (own 4 : KLoc (Fin 8) (MainE E₆ Er Es md)) ≠ own 3 := own_ne_own (by decide)
  have e1 := runs_popD (σ := MainR R₆ Rr Rs Rd) (own 0) _ _ X (hX 0)
  have e2 := runs_popD (σ := MainR R₆ Rr Rs Rd) (own 1) _ _
    (Function.update X (own 0) (S (own 0)))
    (by rw [Function.update_of_ne n10]; exact hX 1)
  have e3 := runs_popD (σ := MainR R₆ Rr Rs Rd) (own 2) _ _
    (Function.update (Function.update X (own 0) (S (own 0))) (own 1) (S (own 1)))
    (by rw [Function.update_of_ne n21, Function.update_of_ne n20]; exact hX 2)
  have e4 := runs_popD (σ := MainR R₆ Rr Rs Rd) (own 3) _ _
    (Function.update (Function.update (Function.update X (own 0) (S (own 0))) (own 1) (S (own 1)))
      (own 2) (S (own 2)))
    (by rw [Function.update_of_ne n32, Function.update_of_ne n31, Function.update_of_ne n30]
        exact hX 3)
  have e5 := runs_popD (σ := MainR R₆ Rr Rs Rd) (own 4) _ _
    (Function.update (Function.update (Function.update (Function.update X (own 0) (S (own 0)))
      (own 1) (S (own 1))) (own 2) (S (own 2))) (own 3) (S (own 3)))
    (by rw [Function.update_of_ne n43, Function.update_of_ne n42, Function.update_of_ne n41,
          Function.update_of_ne n40]
        exact hX 4)
  exact WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 (WP.W9comp.runs_seq e3
    (WP.W9comp.runs_seq e4 e5)))

end MainProg

/-- Four updates through an injective embedding. -/
theorem runs_call_upd4 {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {B : K → List Sym}
    (x0 x1 x2 x3 : L) (w0 w1 w2 w3 : List Sym) {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (Function.update (Function.update (Function.update (Function.update
      (B ∘ ι) x0 w0) x1 w1) x2 w2) x3 w3) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update (Function.update (Function.update
      B (ι x0) w0) (ι x1) w1) (ι x2) w2) (ι x3) w3) (fun _ => True) T := by
  refine runs_callInj hι l (Q := Q) ?_ (fun k hk => ?_)
  · rw [Function.update_comp_eq_of_injective _ hι x3 w3,
      Function.update_comp_eq_of_injective _ hι x2 w2,
      Function.update_comp_eq_of_injective _ hι x1 w1,
      Function.update_comp_eq_of_injective B hι x0 w0]
    exact h
  · rw [Function.update_of_ne (fun h => hk x3 h.symm), Function.update_of_ne (fun h => hk x2 h.symm),
      Function.update_of_ne (fun h => hk x1 h.symm), Function.update_of_ne (fun h => hk x0 h.symm)]

/-- The total cost bound of the lines phase. -/
theorem total_cost_le {Y V M Cs Cd Sg X a g : ℕ} (hY1 : 1 ≤ Y) (hVY : V ≤ Y) (hMV : M ≤ V)
    (hX : X ^ 2 ≤ 64 * M) (ha : bitLen a ≤ M) (hg : bitLen g ≤ M) :
    5 + (Cs * X ^ 2 + ((Sg * (Y + 1) + 1) + (Cd * (bitLen a + 1) + (Cd * (bitLen a + 1) +
      (Cd * (bitLen a + 1) + Cd * (bitLen g + 1))) + 5))) ≤
      (11 + 64 * Cs + 8 * Cd + 2 * Sg) * Y := by
  have h1 : Cs * X ^ 2 ≤ 64 * Cs * Y := by
    calc Cs * X ^ 2 ≤ Cs * (64 * M) := Nat.mul_le_mul_left _ hX
      _ ≤ Cs * (64 * Y) := Nat.mul_le_mul_left _ (by omega)
      _ = 64 * Cs * Y := by ring
  have h2 : Cd * (bitLen a + 1) ≤ 2 * Cd * Y := by
    calc Cd * (bitLen a + 1) ≤ Cd * (2 * Y) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Cd * Y := by ring
  have h3 : Cd * (bitLen g + 1) ≤ 2 * Cd * Y := by
    calc Cd * (bitLen g + 1) ≤ Cd * (2 * Y) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Cd * Y := by ring
  have h4 : Sg * (Y + 1) ≤ 2 * Sg * Y := by
    calc Sg * (Y + 1) ≤ Sg * (2 * Y) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Sg * Y := by ring
  nlinarith

end AppC.C7LinesAux

open AppC.C7LinesAux

/-- **Lemma A.9 phase 1, the eight packed lines** (`c7Lines_of`, 0 `sorry`): from the leaf hypotheses
`C6InterchangeStmt τ` (Lemma A.8), the Lemma A.9 offset routines `K4OffsetCtlParStmt (lineOff ε par xF) J` and
the counter kernel `C7LinesSetupStmt`, `C7LinesStmt τ σ` holds. The rotations are the proved
`K1.k4RotateCtlPar_holds`, the counter drops `WP.W3.W3_dropNat_holds`. -/
theorem c7Lines_of (τ : ℝ) (σ : Equiv.Perm (Fin 3)) (J : ℕ) (hC6 : C6InterchangeStmt τ)
    (hOff : ∀ (ε : ℤ) (par : ℕ) (xF : Bool), (ε = 1 ∨ ε = -1) → par ≤ 1 →
      K4OffsetCtlParStmt (lineOff ε par xF) J)
    (hSetup : C7LinesSetupStmt) : C7LinesStmt τ σ := by
  intro hprem
  obtain ⟨C₆, hC₆⟩ := hC6 hprem
  obtain ⟨E₆, iE6f, iE6d, R₆, P₆, hR6f, hR6n, hcl6, hs6⟩ := hC₆ ()
  have hRot : ∀ i : Fin 8, ∃ (C : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
      (P : Prog (KLoc (Fin 10) E) (fun _ => Sym) R), Finite R ∧ Nonempty R ∧ P.Closed ∧
        RotBody (lineOffOp σ (opOf i)) C P := by
    intro i
    obtain ⟨C, hC⟩ := K1.k4RotateCtlPar_holds 2 1 J (lineOffOp σ (opOf i)) (le_refl 2)
      (hOff (opOf i).2.1 (opOf i).2.2 (xFirst σ (σ.symm (tgtName (opOf i))))
        (by fin_cases i <;> decide) (by fin_cases i <;> decide))
      (fun k1 k2 b c1 c2 => lineOff_lt _ _ _ k1 k2 b c1 c2)
    obtain ⟨E, i1, i2, R, P, h1, h2, h3, h4⟩ := hC ()
    exact ⟨C, E, i1, i2, R, P, h1, h2, h3, h4⟩
  choose Cr Er iErf iErd Rr Pr hRrf hRrn hclr hsr using hRot
  obtain ⟨Cs, hCs⟩ := hSetup
  obtain ⟨Es, iEsf, iEsd, Rs, Ps, hRsf, hRsn, hcls, hss⟩ := hCs ()
  obtain ⟨Cd, hCd⟩ := WP.W3.W3_dropNat_holds
  obtain ⟨md, Rd, obsd, Pd, hmd, hRdf, hRdn, hcld, hsd⟩ := hCd ()
  refine ⟨11 + 64 * Cs + 8 * Cd + 2 * ((List.finRange 8).map fun i => 2 * C₆ + Cr i).sum,
    fun _ => ⟨MainE E₆ Er Es md, instFintypeMainE, instDecEqMainE, MainR R₆ Rr Rs Rd,
      mainProg σ P₆ Pr Ps Pd, inferInstance, inferInstance,
      closed_mainProg σ hcl6 hclr hcls hcld, ?_⟩⟩
  intro K ρ f N0 N1 N2 N3 R v rest r1 r2 r3 r4 r5 r6 r7 S hK hρ hf hN0 hN1 hN2 hN3 hR hlen hrec
    hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  have hK1 : 1 ≤ K := by omega
  have hmk : ∀ x, TermOK (Sym.mark :: x) := fun x d hd => by
    simp only [List.head?_cons, Option.some.injEq] at hd; subst hd; rfl
  have hmkB : ∀ x, BlkTerm (Sym.mark :: x) := fun x d hd => by
    simp only [List.head?_cons, Option.some.injEq] at hd; subst hd; exact ⟨rfl, by decide⟩
  -- 1. marks
  have XP := runs_pushMarks (R₆ := R₆) (Rr := Rr) (Rs := Rs) (Rd := Rd) S
  set S1 := markUp S with hS1def
  have hS1own : ∀ k : Fin 5, S1 (own k) = .mark :: S (own k) := by
    intro k; fin_cases k <;> simp [hS1def, markUp, own]
  have hS1inl : ∀ i : Fin 8, S1 (.inl i) = S (.inl i) := by
    intro i; simp [hS1def, markUp, own]
  have hS1own' : ∀ k : Fin 5, S1 (.inr (.inl k)) = .mark :: S (.inr (.inl k)) := hS1own
  -- 2. counters
  have e_s := hss K f N1 N2 r1 r3 r4 r5 (S1 ∘ ιS) hr1 hr3 hr4 hr5
    (by show S1 (.inl 1) = _; rw [hS1inl]; exact hS1)
    (by show S1 (.inl 3) = _; rw [hS1inl]; exact hS3)
    (by show S1 (.inl 4) = _; rw [hS1inl]; exact hS4)
    (by show S1 (.inl 5) = _; rw [hS1inl]; exact hS5)
  set S2 := Function.update (Function.update (Function.update (Function.update S1
    (own 1) (natSyms (f * K) ++ S1 (own 1))) (own 2) (natSyms (f * K) ++ S1 (own 2)))
    (own 3) (natSyms (f * K) ++ S1 (own 3))) (own 4) (natSyms (N1 * 2 ^ (f * K) * N2) ++ S1 (own 4))
    with hS2def
  have XS : Runs (callInj ιS (lensS (R₆ := R₆) (Rr := Rr) (Rd := Rd)) Ps) S1 S2 (fun _ => True)
      (Cs * (f * K + bitLen K + bitLen f + bitLen N1 + bitLen N2 + 1) ^ 2) :=
    runs_call_upd4 ιS_injective lensS (.inl 4) (.inl 5) (.inl 6) (.inl 7) _ _ _ _ e_s
  have hS2own : ∀ k : Fin 5, k ≠ 0 → ∃ t, S2 (own k) = t ++ .mark :: S (own k) := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · exact ⟨natSyms (f * K), by simp [hS2def, own, hS1own']⟩
    · exact ⟨natSyms (f * K), by simp [hS2def, own, hS1own']⟩
    · exact ⟨natSyms (f * K), by simp [hS2def, own, hS1own']⟩
    · exact ⟨natSyms (N1 * 2 ^ (f * K) * N2), by simp [hS2def, own, hS1own']⟩
  have hS2L : ∀ k : Fin 5, k = 1 ∨ k = 2 ∨ k = 3 → S2 (own k) = natSyms (f * K) ++ .mark :: S (own k) := by
    intro k hk
    rcases hk with rfl | rfl | rfl <;> simp [hS2def, own, hS1own']
  have hS2G : S2 (own 4) = natSyms (N1 * 2 ^ (f * K) * N2) ++ .mark :: S (own 4) := by
    simp [hS2def, own, hS1own']
  have hS2T : S2 (own 0) = .mark :: S (own 0) := by
    simp [hS2def, own, hS1own']
  have hS2inl : ∀ i : Fin 8, S2 (.inl i) = S (.inl i) := by
    intro i; simp [hS2def, own, hS1inl]
  -- 3. the eight lines
  set B := Function.update S2 (.inl 0) rest with hBdef
  have hBown : ∀ k : Fin 5, B (own k) = S2 (own k) := fun k =>
    Function.update_of_ne (own_ne_inl k 0) _ _
  have hBinl : ∀ i : Fin 8, i ≠ 0 → B (.inl i) = S (.inl i) := fun i hi =>
    (Function.update_of_ne (by simpa using hi) _ _).trans (hS2inl i)
  have hB : LinesBase B rest K ρ f N1 N2 N3 R :=
    { hA := Function.update_self _ _ _
      hrest := hrest
      hT := by rw [hBown, hS2T]; exact hmkB _
      hL1 := ⟨_, by rw [hBown, hS2L 1 (by decide)], hmk _⟩
      hL2 := ⟨_, by rw [hBown, hS2L 2 (by decide)], hmk _⟩
      hL3 := ⟨_, by rw [hBown, hS2L 3 (by decide)], hmk _⟩
      hG := ⟨_, by rw [hBown, hS2G], hmk _⟩
      hK := ⟨r1, by rw [hBinl 1 (by decide)]; exact hS1, hr1⟩
      hρ := ⟨r2, by rw [hBinl 2 (by decide)]; exact hS2, hr2⟩
      hN1 := ⟨r4, by rw [hBinl 4 (by decide)]; exact hS4, hr4⟩
      hN2 := ⟨r5, by rw [hBinl 5 (by decide)]; exact hS5, hr5⟩
      hN3 := ⟨r6, by rw [hBinl 6 (by decide)]; exact hS6, hr6⟩
      hR := ⟨r7, by rw [hBinl 7 (by decide)]; exact hS7, hr7⟩ }
  have XL := lines_runs (Rs := Rs) (Rd := Rd) τ σ hs6 hsr hK hρ hf hN0 hN1 hN2 hN3 hB
    (List.finRange 8) true v hlen hrec
  have hfin : finalFlag true (List.finRange 8) = true := by decide
  rw [map_opOf, hfin] at XL
  have hK0 : 0 < K := by omega
  have hw8 : permByInv (linesPull σ K ρ f N1 N2 N3 eightOps) v =
      permByInv (c7LinesInv K ρ f N1 N2 N3 σ) v := by
    apply permByInv_congr
    intro y hy
    rw [hlen] at hy
    exact linesPull_eightOps σ hK0 hN1 hN2 hN3 hy
  rw [hw8] at XL
  have hSt0 : lineSt B rest true v = S2 := by
    show Function.update B (.inl 0) (arrSyms v ++ rest) = S2
    rw [hBdef, Function.update_idem, ← hS0, ← hS2inl 0, Function.update_eq_self]
  rw [hSt0] at XL
  set w8 := permByInv (c7LinesInv K ρ f N1 N2 N3 σ) v with hw8def
  set S3 := Function.update B (.inl 0) (arrSyms w8 ++ rest) with hS3def
  have XL' : Runs (linesP (Rs := Rs) (Rd := Rd) σ P₆ Pr true (List.finRange 8)) S2 S3
      (fun _ => True) _ := XL
  -- 4. drops
  have hS3own : ∀ k : Fin 5, S3 (own k) = S2 (own k) := fun k =>
    (Function.update_of_ne (own_ne_inl k 0) _ _).trans (hBown k)
  have d1 := hsd (f * K) (.mark :: S (own 1)) (S3 ∘ ιD 1) (hmk _)
    (by show S3 (own 1) = _; rw [hS3own, hS2L 1 (by decide)])
  have D1 := runs_call_upd1 (ιD_injective (E₆ := E₆) (Er := Er) (Es := Es) (md := md) 1)
    (lensD (R₆ := R₆) (Rr := Rr) (Rs := Rs)) (.inl 0) _ d1
  set S31 := Function.update S3 (own 1) (.mark :: S (own 1)) with hS31
  have d2 := hsd (f * K) (.mark :: S (own 2)) (S31 ∘ ιD 2) (hmk _)
    (by show S31 (own 2) = _; rw [hS31, Function.update_of_ne (own_ne_own (by decide)), hS3own,
      hS2L 2 (by decide)])
  have D2 := runs_call_upd1 (ιD_injective (E₆ := E₆) (Er := Er) (Es := Es) (md := md) 2)
    (lensD (R₆ := R₆) (Rr := Rr) (Rs := Rs)) (.inl 0) _ d2
  set S32 := Function.update S31 (own 2) (.mark :: S (own 2)) with hS32
  have d3 := hsd (f * K) (.mark :: S (own 3)) (S32 ∘ ιD 3) (hmk _)
    (by show S32 (own 3) = _; rw [hS32, Function.update_of_ne (own_ne_own (by decide)), hS31,
      Function.update_of_ne (own_ne_own (by decide)), hS3own, hS2L 3 (by decide)])
  have D3 := runs_call_upd1 (ιD_injective (E₆ := E₆) (Er := Er) (Es := Es) (md := md) 3)
    (lensD (R₆ := R₆) (Rr := Rr) (Rs := Rs)) (.inl 0) _ d3
  set S33 := Function.update S32 (own 3) (.mark :: S (own 3)) with hS33
  have d4 := hsd (N1 * 2 ^ (f * K) * N2) (.mark :: S (own 4)) (S33 ∘ ιD 4) (hmk _)
    (by show S33 (own 4) = _; rw [hS33, Function.update_of_ne (own_ne_own (by decide)), hS32,
      Function.update_of_ne (own_ne_own (by decide)), hS31,
      Function.update_of_ne (own_ne_own (by decide)), hS3own, hS2G])
  have D4 := runs_call_upd1 (ιD_injective (E₆ := E₆) (Er := Er) (Es := Es) (md := md) 4)
    (lensD (R₆ := R₆) (Rr := Rr) (Rs := Rs)) (.inl 0) _ d4
  set S4 := Function.update S33 (own 4) (.mark :: S (own 4)) with hS4
  -- 5. pops
  have hS4own : ∀ k : Fin 5, S4 (own k) = .mark :: S (own k) := by
    intro k
    fin_cases k
    · simp [hS4, hS33, hS32, hS31, own]
      exact (hS3own 0).trans hS2T
    all_goals simp [hS4, hS33, hS32, hS31, own]
  have XO := runs_popMarks (R₆ := R₆) (Rr := Rr) (Rs := Rs) (Rd := Rd) S S4 hS4own
  -- 6. assemble
  have X := WP.W9comp.runs_seq XP (WP.W9comp.runs_seq XS (WP.W9comp.runs_seq XL'
    (WP.W9comp.runs_seq (WP.W9comp.runs_seq D1 (WP.W9comp.runs_seq D2 (WP.W9comp.runs_seq D3 D4)))
      XO)))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext x
    rcases x with i | k | e
    · by_cases hi : i = 0
      · subst hi
        simp [hS4, hS33, hS32, hS31, hS3def, own]
      · simp [hS4, hS33, hS32, hS31, hS3def, hBdef, own, hi, hS2inl]
    · fin_cases k <;> simp [own]
    · simp [hS4, hS33, hS32, hS31, hS3def, hBdef, hS2def, hS1def, markUp,
        own]
  · -- cost
    have hM : 1 ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
      have : 0 < N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by positivity
      omega
    have hvol : vol v = (N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) * (R + 1) := by
      rw [vol_of_len hrec, hlen]
    have hMV : N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 ≤ vol v := by
      rw [hvol]; nlinarith
    have hVY : vol v ≤ ⌈(vol v : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ := by
      have hpow : (0 : ℝ) ≤ ((f * K : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h3 : (vol v : ℝ) ≤ (vol v : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1) := by
        have : (0 : ℝ) ≤ vol v := Nat.cast_nonneg _
        nlinarith
      exact_mod_cast h3.trans (Nat.le_ceil _)
    have hYc : ⌈(vol v : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ ≤ c7Cost τ K f v.length (vol v) R := by
      unfold c7Cost
      omega
    have hLM : bitLen (f * K) ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
      have h1 := bitLen_le_self' (f * K)
      have h2 : f * K < 2 ^ (f * K) := Nat.lt_two_pow_self
      have h3 : 2 ^ (f * K) ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
        have : 1 ≤ 2 ^ (f * K) := Nat.one_le_two_pow
        calc 2 ^ (f * K) = 1 * 1 * 1 * 1 * 1 * 2 ^ (f * K) * 1 := by ring
          _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by gcongr
      omega
    have hGM : bitLen (N1 * 2 ^ (f * K) * N2) ≤
        N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
      have h1 := bitLen_le_self' (N1 * 2 ^ (f * K) * N2)
      have : 1 ≤ 2 ^ (f * K) := Nat.one_le_two_pow
      have h3 : N1 * 2 ^ (f * K) * N2 ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
        calc N1 * 2 ^ (f * K) * N2 = 1 * 1 * N1 * 2 ^ (f * K) * N2 * 1 * 1 := by ring
          _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by gcongr
      omega
    have hset := setup_cost_le hK1 hf hN0 hN1 hN2 hN3
    have hY1 : 1 ≤ ⌈(vol v : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ := le_trans (le_trans hM hMV) hVY
    rw [← hvol]
    calc _ ≤ (11 + 64 * Cs + 8 * Cd + 2 * ((List.finRange 8).map fun i => 2 * C₆ + Cr i).sum) *
          ⌈(vol v : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ :=
        total_cost_le hY1 hVY hMV hset hLM hGM
      _ ≤ _ := Nat.mul_le_mul_left _ hYc

end SubNLogN.Machine
