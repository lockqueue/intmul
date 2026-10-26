import WP.W0m.WorkMain
import IntMulTM.Framework.IO
import IntMulTM.Framework.Accept

/-!
# WP.W0m.Stage — the input stage over the production layout

`inputStage ι Pw` is copy-in from the `PairSym` input stack onto work stack `ι inp`, followed by
the work program `Pw`. `Pw` runs on the local stacks `Stk`; they are renamed along an injective
`ι : Stk → W` into the machine's work stacks and lifted into `StackId W` with `Prog.liftWork`.

`inputStage_triple` starts from the initial machine state, where the input stack holds
`encNatPair.encode (a, b)` and every other stack is empty. It reaches a state with:
* input and output stacks empty;
* `work (ι x) = outW a b x` for every local stack `x`;
* every work stack outside the image of `ι` empty.

Cost: `3·L + 2` for the copy-in plus the work program's cost.

Closedness is preserved by `liftRegs`, `mapStk` and `liftWork` (`freeBelow_*`), and copy-in is
closed. So the stage is closed whenever `Pw` is.
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts IntMulTM

/-- Input alphabet into the work alphabet. -/
def trIn : PairSym → Sym
  | .bit b => .bit b
  | .sep => .sep

theorem map_trIn_bit (l : List Bool) : (l.map PairSym.bit).map trIn = l.map Sym.bit := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [trIn, ih]

theorem copyIn_image (a b : ℕ) :
    ((encNatPair.encode (a, b)).map trIn).reverse = inputSyms a b := by
  rw [encNatPair_encode_eq]
  simp only [encodeNatPair, List.map_append, List.map_cons, map_trIn_bit, List.reverse_append,
    List.reverse_cons, inputSyms, trIn, List.map_reverse, List.append_assoc, List.singleton_append]

/-! ## Closedness is preserved by the embeddings -/

section Closed

variable {K K' : Type} {Γ : K → Type} {σ τ : Type}

theorem freeBelow_liftRegs (l : Lens σ τ) (p : Prog K Γ τ) :
    ∀ d, (p.liftRegs l).FreeBelow d ↔ p.FreeBelow d := by
  induction p with
  | push => intro d; exact Iff.rfl
  | peek => intro d; exact Iff.rfl
  | pop => intro d; exact Iff.rfl
  | load => intro d; exact Iff.rfl
  | seq p q ihp ihq => intro d; simp only [Prog.liftRegs, Prog.FreeBelow, ihp, ihq]
  | ite c p q ihp ihq => intro d; simp only [Prog.liftRegs, Prog.FreeBelow, ihp, ihq]
  | loop c p ih => intro d; simp only [Prog.liftRegs, Prog.FreeBelow, ih]
  | fix b ih => intro d; simp only [Prog.liftRegs, Prog.FreeBelow, ih]
  | recur n => intro d; exact Iff.rfl

theorem freeBelow_mapStk {A : Type} (ι : K → K') (p : Prog K (fun _ => A) σ) :
    ∀ d, (p.mapStk ι).FreeBelow d ↔ p.FreeBelow d := by
  induction p with
  | push => intro d; exact Iff.rfl
  | peek => intro d; exact Iff.rfl
  | pop => intro d; exact Iff.rfl
  | load => intro d; exact Iff.rfl
  | seq p q ihp ihq => intro d; simp only [Prog.mapStk, Prog.FreeBelow, ihp, ihq]
  | ite c p q ihp ihq => intro d; simp only [Prog.mapStk, Prog.FreeBelow, ihp, ihq]
  | loop c p ih => intro d; simp only [Prog.mapStk, Prog.FreeBelow, ih]
  | fix b ih => intro d; simp only [Prog.mapStk, Prog.FreeBelow, ih]
  | recur n => intro d; exact Iff.rfl

theorem freeBelow_liftWork {W A : Type} (p : Prog W (fun _ => Sym) σ) :
    ∀ d, (p.liftWork A).FreeBelow d ↔ p.FreeBelow d := by
  induction p with
  | push => intro d; exact Iff.rfl
  | peek => intro d; exact Iff.rfl
  | pop => intro d; exact Iff.rfl
  | load => intro d; exact Iff.rfl
  | seq p q ihp ihq => intro d; simp only [Prog.liftWork, Prog.FreeBelow, ihp, ihq]
  | ite c p q ihp ihq => intro d; simp only [Prog.liftWork, Prog.FreeBelow, ihp, ihq]
  | loop c p ih => intro d; simp only [Prog.liftWork, Prog.FreeBelow, ih]
  | fix b ih => intro d; simp only [Prog.liftWork, Prog.FreeBelow, ih]
  | recur n => intro d; exact Iff.rfl

end Closed

/-- **The input stage** over the production layout. -/
def inputStage {W : Type} (ι : Stk → W) {σ : Type} (Pw : Prog Stk (fun _ => Sym) σ) :
    Prog (StackId W) (StackId.Γ encNatPair.Γ) (Option Sym × σ) :=
  .seq ((copyIn trIn (ι .inp)).liftRegs (Lens.fst _ _))
    (((Pw.mapStk ι).liftWork encNatPair.Γ).liftRegs (Lens.snd _ _))

theorem inputStage_closed {W : Type} (ι : Stk → W) {σ : Type} {Pw : Prog Stk (fun _ => Sym) σ}
    (h : Pw.Closed) : (inputStage ι Pw).Closed := by
  unfold Prog.Closed inputStage
  simp only [Prog.FreeBelow, freeBelow_liftRegs, freeBelow_liftWork, freeBelow_mapStk]
  refine ⟨?_, h⟩
  simp [copyIn, popIn, copyInBody, Prog.FreeBelow]

theorem inputStk_input {W : Type} [DecidableEq W] (l : List encNatPair.Γ) :
    (inputStk (W := W) l) .input = l := by
  simp [inputStk, stkOnly]

theorem inputStk_output {W : Type} [DecidableEq W] (l : List encNatPair.Γ) :
    (inputStk (W := W) l) .output = [] := by
  simp [inputStk, stkOnly]

theorem inputStk_work {W : Type} [DecidableEq W] (l : List encNatPair.Γ) (w : W) :
    (inputStk (W := W) l) (.work w) = [] := by
  simp [inputStk, stkOnly]

/-- **Input stage, correctness and cost**, from any work program with the `Runs` spec of
`workProg`. -/
theorem inputStage_triple {W : Type} [DecidableEq W] {ι : Stk → W} (hι : Function.Injective ι)
    {σ : Type} {Pw : Prog Stk (fun _ => Sym) σ} {T : ℕ → ℕ → ℕ}
    (hw : ∀ a b, Runs Pw (S0 a b) (outW a b) (fun _ => True) (T a b)) (a b : ℕ) :
    Triple [] (fun s => s.stk = inputStk (encNatPair.encode (a, b))) (inputStage ι Pw)
      (fun s => s.stk .input = [] ∧ s.stk .output = [] ∧
        (∀ x, s.stk (.work (ι x)) = outW a b x) ∧ ∀ w, (∀ x, ι x ≠ w) → s.stk (.work w) = [])
      (3 * (encNatPair.encode (a, b)).length + 2 + T a b) := by
  set I := inputStk (W := W) (encNatPair.encode (a, b)) with hI
  set I1 : ∀ k : StackId W, List (StackId.Γ encNatPair.Γ k) :=
    Function.update (Function.update I .input []) (.work (ι .inp))
      (((I .input).map trIn).reverse ++ I (.work (ι .inp))) with hI1
  -- the work part of the state after copy-in
  set B : W → List Sym := fun w => I1 (.work w) with hB
  have hBw : ∀ w, B w = if w = ι .inp then inputSyms a b else [] := by
    intro w
    simp only [hB, hI1, upd_work_eq, upd_input_work, hI, inputStk_input, inputStk_work,
      copyIn_image, List.append_nil]
  have hBι : ∀ x, B (ι x) = S0 a b x := by
    intro x
    rw [hBw]
    by_cases hx : x = .inp
    · subst hx
      simp [S0]
    · rw [if_neg (hι.ne hx)]
      simp [S0, hx]
  -- work program: renamed, lifted to the production layout, registers lifted
  have hW := Runs.embed hι (hw a b) B hBι
  have hL := Triple.liftWork (A := encNatPair.Γ) hW
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun s s' hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  have hR := Triple.liftRegs (Lens.snd (Option Sym) σ) hL (fun _ => True) (fun _ _ _ => trivial)
  -- copy-in, as a triple
  have hC : Triple [] (fun s : St (StackId W) (StackId.Γ encNatPair.Γ) (Option Sym × σ) =>
      s.stk = I) ((copyIn trIn (ι .inp)).liftRegs (Lens.fst _ _))
      (fun s => ((⟨(Lens.snd (Option Sym) σ).get s.var, s.stk⟩ :
        St (StackId W) (StackId.Γ encNatPair.Γ) σ).work.stk = B ∧
        s.stk .input = [] ∧ s.stk .output = []) ∧ True)
      (3 * (encNatPair.encode (a, b)).length + 2) := by
    intro s hs
    obtain ⟨v, stk⟩ := s
    change stk = I at hs
    subst hs
    have e := copyIn_eval trIn (ι .inp) [] v.1 I
    refine ⟨⟨(none, v.2), I1⟩, _, Eval.liftRegs (Lens.fst _ _) e v rfl, ⟨⟨rfl, ?_, ?_⟩, trivial⟩, ?_⟩
    · show I1 .input = []
      rw [hI1, upd_work_input, Function.update_self]
    · show I1 .output = []
      rw [hI1, upd_work_output, upd_input_output, hI, inputStk_output]
    · rw [hI, inputStk_input]
  refine Triple.conseq (Triple.seq hC hR) (fun s hs => hs) ?_ le_rfl
  rintro ⟨v, stk⟩ ⟨⟨⟨hin, hout, -⟩, hio⟩, -⟩
  refine ⟨hio.1, hio.2, hin, fun w hw' => ?_⟩
  change stk (.work w) = []
  have := hout w hw'
  change stk (.work w) = B w at this
  rw [this, hBw, if_neg (fun h => hw' .inp h.symm)]

#assert_std_axioms map_trIn_bit copyIn_image freeBelow_liftRegs freeBelow_mapStk freeBelow_liftWork
  inputStage_closed inputStk_input inputStk_output inputStk_work inputStage_triple

end WP.W0m
