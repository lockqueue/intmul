/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadLineStmt
import SubNLogN.Machine.Bridge.SpreadPrim2

/-!
# K5 spreading, stage loop: base (`Bridge/SpreadStageBase.lean`)

Generic tools for the stage loop of `SpreadLinesStmt` (`spreadLines_of`, `Bridge/SpreadStageMain`):

* `dropAll A`: pop every symbol of `A` (`dropAll_eval`, cost `3n + 2`);
* `walkL lA R X body`: a ruler walk whose body runs in an arbitrary register type `σ` (the AR
  steps through the lens `lA`); `runs_walkL` from a family of stack states with `Runs` bodies;
* `runs_ar`: an AR `Runs` fact transported along `lA`;
* `ιSU`: the embedding of the setup kernel's stacks (`SpreadSetupStmt`) into `SK Es`, and
  `runs_setupCall`: the embedded setup installs the rulers on `sp (.ru r)`.

**Scope (honest summary).** Everything here is proved (no `sorry`). Helpers live in
`SubNLogN.Machine.Bridge.SpreadAux.Stage`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux.Stage

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## Pop everything -/

section DropAll

variable {K : Type} [DecidableEq K]

/-- Pop every symbol of `A`: loop. -/
def dropLoop (A : K) : AProg K := .loop (fun v => v.o.isSome) (.seq (drop1 A) (peekO A))

/-- Pop every symbol of `A`. -/
def dropAll (A : K) : AProg K := .seq (peekO A) (dropLoop A)

theorem closed_dropAll (A : K) : (dropAll A).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dropAll, dropLoop, drop1, peekO]

theorem dropLoop_eval (A : K) : ∀ (L : List Sym) (v : AReg) (S : K → List Sym), S A = L →
    v.o = L.head? →
    ∃ v', Eval [] (dropLoop A) ⟨v, S⟩ ⟨v', Function.update S A []⟩ (3 * L.length + 1)
  | [], v, S, hS, hv => by
    refine ⟨v, (Eval.loop_false (by simp [hv])).of_eq ?_ rfl⟩
    congr 1
    rw [← hS, Function.update_eq_self]
  | y :: L, v, S, hS, hv => by
    have e1 := eval_drop1 A v S y L hS
    have hs1 : Function.update S A L A = L := Function.update_self ..
    have e2 : Eval [] (peekO A) ⟨v, Function.update S A L⟩
        ⟨{ v with o := L.head? }, Function.update S A L⟩ 1 :=
      (eval_peekO A v _).of_eq (by rw [hs1]) rfl
    obtain ⟨v', e3⟩ := dropLoop_eval A L { v with o := L.head? } _ hs1 rfl
    refine ⟨v', (Eval.loop_true (by simp [hv]) (Eval.seq e1 e2) e3).of_eq ?_
      (by simp only [List.length_cons]; ring)⟩
    rw [Function.update_idem]

/-- **dropAll**, exact: `A` ends empty. Cost `3n + 2`. -/
theorem dropAll_eval (A : K) (v : AReg) (S : K → List Sym) :
    ∃ v', Eval [] (dropAll A) ⟨v, S⟩ ⟨v', Function.update S A []⟩ (3 * (S A).length + 2) := by
  obtain ⟨v', e⟩ := dropLoop_eval A (S A) { v with o := (S A).head? } S rfl rfl
  exact ⟨v', (Eval.seq (eval_peekO A v S) e).of_eq rfl (by ring)⟩

theorem runs_dropAll (A : K) (S : K → List Sym) :
    Runs (dropAll A) S (Function.update S A []) (fun _ => True) (3 * (S A).length + 2) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := dropAll_eval A v S
    exact ⟨v', _, e, trivial, le_rfl⟩

end DropAll

/-! ## AR programs inside a larger register type -/

section Lift

variable {K σ : Type} [DecidableEq K] (lA : Lens σ AReg)

/-- An AR program run inside the registers `σ` (through `lA`). -/
abbrev ar (p : AProg K) : Prog K (fun _ => Sym) σ := Prog.liftRegs lA p

theorem closed_ar {p : AProg K} (hp : p.Closed) : (ar lA p).Closed :=
  WP.W9comp.closed_liftRegs lA hp

/-- An AR `Runs` fact, transported along `lA`. -/
theorem runs_ar {p : AProg K} {S S' : K → List Sym} {Q : AReg → Prop} {T : ℕ}
    (h : Runs p S S' Q T) : Runs (ar lA p) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨⟨w, stk'⟩, t, e, ⟨hs', -⟩, ht⟩ := h ⟨lA.get v, stk⟩ rfl
  exact ⟨⟨lA.set v w, stk'⟩, t, Eval.liftRegs lA e v rfl, ⟨hs', trivial⟩, ht⟩

end Lift

/-! ## Closedness helpers -/

theorem closed_seq' {K σ : Type} {p q : Prog K (fun _ => Sym) σ} (hp : p.Closed)
    (hq : q.Closed) : (Prog.seq p q).Closed := by
  simp only [Prog.Closed] at hp hq ⊢
  exact ⟨hp, hq⟩

theorem closed_loop' {K σ : Type} {c : σ → Bool} {p : Prog K (fun _ => Sym) σ}
    (hp : p.Closed) : (Prog.loop c p).Closed := by
  simp only [Prog.Closed] at hp ⊢
  exact hp

/-! ## Walks with a `σ`-body -/

section WalkL

variable {K σ : Type} [DecidableEq K] (lA : Lens σ AReg)

/-- One mark from `R` to `X`. -/
def wStep (R X : K) : AProg K := .seq (drop1 R) (pushS X .mark)

/-- The loop of a `σ`-walk. -/
def walkLoopL (R X : K) (body : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .loop (fun v => isMarkO (lA.get v).r) (.seq (ar lA (wStep R X)) (.seq body (ar lA (peekR R))))

/-- Walk the ruler `R` (its marks move to `X`) with a `σ`-body: one run of the body per mark. -/
def walkL (R X : K) (body : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq (ar lA (peekR R)) (walkLoopL lA R X body)

theorem closed_walkL (R X : K) {body : Prog K (fun _ => Sym) σ} (hb : body.Closed) :
    (walkL lA R X body).Closed := by
  have h1 : (ar lA (peekR R)).Closed :=
    closed_ar lA (by simp [Prog.Closed, Prog.FreeBelow, peekR])
  have h2 : (ar lA (wStep R X)).Closed :=
    closed_ar lA (by simp [Prog.Closed, Prog.FreeBelow, wStep, drop1, pushS])
  unfold walkL walkLoopL
  exact closed_seq' h1 (closed_loop' (closed_seq' h2 (closed_seq' hb h1)))

theorem walkLoopL_eval {R X : K} (hRX : R ≠ X) (body : Prog K (fun _ => Sym) σ) (n : ℕ)
    (D X0 : List Sym) (hD : D.head? ≠ some .mark) (S : ℕ → K → List Sym)
    (hSR : ∀ j ≤ n, S j R = List.replicate (n - j) .mark ++ D)
    (hSX : ∀ j ≤ n, S j X = List.replicate j .mark ++ X0) (Tb : ℕ)
    (hb : ∀ j < n, Runs body (Function.update (Function.update (S j) R
      (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: S j X)) (S (j + 1)) (fun _ => True)
      Tb) :
    ∀ k j, j + k = n → ∀ v : σ, (lA.get v).r = (S j R).head? →
      ∃ v' t, Eval [] (walkLoopL lA R X body) ⟨v, S j⟩ ⟨v', S n⟩ t ∧ t ≤ k * (Tb + 4) + 1
  | 0, j, hj, v, hv => by
    have hjn : j = n := by omega
    rw [hjn] at hv ⊢
    refine ⟨v, 1, Eval.loop_false ?_, by omega⟩
    show isMarkO (lA.get v).r = false
    rw [hv, hSR n le_rfl, Nat.sub_self, List.replicate_zero, List.nil_append]
    exact isMarkO_false_of_ne hD
  | k + 1, j, hj, v, hv => by
    have hjn : j < n := by omega
    have hR : S j R = .mark :: (List.replicate (n - j - 1) .mark ++ D) := by
      rw [hSR j hjn.le]
      obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, List.replicate_succ, List.cons_append]
    have hc : isMarkO (lA.get v).r = true := by rw [hv, hR]; rfl
    have e1 : Eval [] (wStep R X) ⟨lA.get v, S j⟩ ⟨lA.get v, Function.update (Function.update
        (S j) R (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: S j X)⟩ 2 := by
      have ea := eval_drop1 R (lA.get v) (S j) .mark _ hR
      have eb := eval_pushS X .mark (lA.get v)
        (Function.update (S j) R (List.replicate (n - j - 1) .mark ++ D))
      refine (Eval.seq ea eb).of_eq ?_ rfl
      rw [Function.update_of_ne hRX.symm]
    have e1' := Eval.liftRegs lA e1 v rfl
    rw [lA.set_get] at e1'
    obtain ⟨⟨v1, s1⟩, t1, e2, ⟨hs1, -⟩, ht1⟩ := hb j hjn ⟨v, _⟩ rfl
    change s1 = S (j + 1) at hs1
    subst hs1
    have e3 := Eval.liftRegs lA (eval_peekR R (lA.get v1) (S (j + 1))) v1 rfl
    obtain ⟨v', t', e4, ht'⟩ := walkLoopL_eval hRX body n D X0 hD S hSR hSX Tb hb k (j + 1)
      (by omega) (lA.set v1 { lA.get v1 with r := (S (j + 1) R).head? }) (by rw [lA.get_set])
    refine ⟨v', (2 + (t1 + 1)) + t' + 1, Eval.loop_true hc (Eval.seq e1' (Eval.seq e2 e3)) e4, ?_⟩
    rw [Nat.succ_mul]
    omega

/-- **A `σ`-walk from a family of stack states**: `S j` holds `n - j` marks of `R` above `D`
and `j` marks of `X` above `X0`; the body takes `S j` with one more mark moved to `S (j+1)`. -/
theorem runs_walkL {R X : K} (hRX : R ≠ X) (body : Prog K (fun _ => Sym) σ) (n : ℕ)
    (D X0 : List Sym) (hD : D.head? ≠ some .mark) (S : ℕ → K → List Sym)
    (hSR : ∀ j ≤ n, S j R = List.replicate (n - j) .mark ++ D)
    (hSX : ∀ j ≤ n, S j X = List.replicate j .mark ++ X0) (Tb : ℕ)
    (hb : ∀ j < n, Runs body (Function.update (Function.update (S j) R
      (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: S j X)) (S (j + 1)) (fun _ => True)
      Tb) :
    Runs (walkL lA R X body) (S 0) (S n) (fun _ => True) (n * (Tb + 4) + 2) :=
  Runs.of_eval fun v => by
    have e0 := Eval.liftRegs lA (eval_peekR R (lA.get v) (S 0)) v rfl
    obtain ⟨v', t', e, ht⟩ := walkLoopL_eval lA hRX body n D X0 hD S hSR hSX Tb hb n 0
      (by omega) (lA.set v { lA.get v with r := (S 0 R).head? }) (by rw [lA.get_set])
    exact ⟨v', 1 + t', Eval.seq e0 e, trivial, by omega⟩

end WalkL

/-! ## The embedded setup kernel -/

section Setup

variable {Es : Type} [DecidableEq Es]

/-- Embedding of the setup kernel's stacks into `SK Es`: header, axis, the rulers on
`sp (.ru r)`, the setup's private scratch on `Es`. -/
def ιSU : KLoc SetupN Es → SK Es
  | .inl .par => kN .par
  | .inl .ax => kW .ax
  | .inl (.ru r) => sp (.ru r)
  | .inr e => .inr (.inr e)

theorem ιSU_injective : Function.Injective (ιSU (Es := Es)) := by
  intro a b h
  rcases a with (_ | _ | r) | e <;> rcases b with (_ | _ | r') | e' <;> simp_all [ιSU, sp]

/-- The state `B` with the rulers of the stage installed on `sp (.ru r)`. -/
def setRu (b : BrPar) (i : Fin b.d) (B : SK Es → List Sym) : SK Es → List Sym
  | .inr (.inl (.ru r)) => List.replicate (spreadRulers b i r) .mark
  | k => B k

/-- **The embedded setup kernel** (from the specification of `SpreadSetupStmt`): it installs the
rulers on `sp (.ru r)` and leaves every other stack unchanged. -/
theorem runs_setupCall {Rs σ : Type} (lS : Lens σ Rs)
    {Ps : Prog (KLoc SetupN Es) (fun _ => Sym) Rs} {Cs : ℕ}
    (hspec : ∀ (b : BrPar) (i : Fin b.d) (rax rpar : List Sym) (S : KLoc SetupN Es → List Sym),
      KClean S → ShapeOK b.t → (i : ℕ) ≠ 0 → 1 ≤ b.wI → 1 ≤ b.wT →
      b.P + 2 ≤ b.wI → Nat.log2 (totalLen b.t) ≤ b.wI → TermOK rax →
      S (.inl .par) = hdrSyms b.hdr ++ rpar → S (.inl .ax) = natSyms i ++ rax →
      (∀ r, S (.inl (.ru r)) = []) →
      Runs Ps S (withRulers b i S) (fun _ => True) (Cs * (b.setup + b.R + spreadSlot b i)))
    (b : BrPar) (i : Fin b.d) (rax rpar : List Sym) (B : SK Es → List Sym)
    (hclean : ∀ e : Es, B (.inr (.inr e)) = []) (hru : ∀ r, B (sp (.ru r)) = [])
    (ht : ShapeOK b.t) (hi0 : (i : ℕ) ≠ 0) (hwI : 1 ≤ b.wI) (hwT : 1 ≤ b.wT)
    (hPw : b.P + 2 ≤ b.wI) (hlog : Nat.log2 (totalLen b.t) ≤ b.wI) (hrax : TermOK rax)
    (hpar : B (kN .par) = hdrSyms b.hdr ++ rpar) (hax : B (kW .ax) = natSyms i ++ rax) :
    Runs (callInj ιSU lS Ps) B (setRu b i B) (fun _ => True)
      (Cs * (b.setup + b.R + spreadSlot b i)) := by
  refine runs_callInj (Q := fun _ => True) ιSU_injective lS ?_ ?_
  · have h := hspec b i rax rpar (B ∘ ιSU) (fun e => hclean e) ht hi0 hwI hwT hPw hlog hrax hpar
      hax (fun r => hru r)
    have he : withRulers b i (B ∘ ιSU) = setRu b i B ∘ ιSU := by
      funext k
      rcases k with (_ | _ | r) | e <;> rfl
    rw [he] at h
    exact h
  · intro k hk
    unfold setRu
    split
    · next r => exact absurd rfl (hk (.inl (.ru r)))
    · rfl

end Setup

/-! ## The lines of one group (frozen interface of the inner loop) -/

/-- The lines of one group: one line step per mark of `ru rep` (walk temporary `X 4`), then the
ruler is restored. -/
def lineWalk {Es σ : Type} [DecidableEq Es] (lA : Lens σ AReg)
    (PL : Prog (SK Es) (fun _ => Sym) σ) : Prog (SK Es) (fun _ => Sym) σ :=
  .seq (walkL lA (sp (.ru .rep)) (sp (.X 4)) PL) (ar lA (moveMarks (sp (.X 4)) (sp (.ru .rep))))

/-- The outputs of the lines `l0, …, l0 + n - 1` of `xs` (`t` entries each) with the tap record
`F`. -/
def grpOuts (q t W a0 : ℕ) (xs F : List CInt) (l0 n : ℕ) : List CInt :=
  (List.range n).flatMap fun j => lineOut q t W a0 ((xs.drop ((l0 + j) * t)).take t) F

/-- **[INTERFACE] The lines of one group.** From a state with the packed parts of the tap record
`F` on `F k` (exactly), the lines `l0, l0 + 1, …` of `xs` on `arr`, `X 4` empty, `rep` marks on
`ru rep`, the line rulers and empty line scratch, `lineWalk` consumes `rep` lines from `arr` and
pushes their outputs (reversed symbol order, `SpreadLineSpec`) onto `Out`; every other stack is
unchanged. -/
def LineWalkStmt : Prop :=
  ∀ {Es σ : Type} [DecidableEq Es] (lA : Lens σ AReg) (PL : Prog (SK Es) (fun _ => Sym) σ)
    (CL : ℕ), SpreadLineSpec PL CL →
  ∀ (s wI wT q t W a0 rep l0 : ℕ) (xs F : List CInt) (rarr : List Sym) (S : SK Es → List Sym),
    (l0 + rep) * t ≤ xs.length → F.length = W → 1 ≤ W → W ≤ t → a0 ≤ t → 1 ≤ wI → wI ≤ s →
    q ≤ s →
    (∀ x ∈ xs, FitsTwos wI x.1 ∧ FitsTwos wI x.2) →
    (∀ y ∈ F, FitsTwos wT y.1 ∧ FitsTwos wT y.2) →
    (W : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) < 2 ^ (s - 1) →
    W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s →
    (∀ y ∈ grpOuts q t W a0 xs F l0 rep, FitsTwos wI y.1 ∧ FitsTwos wI y.2) →
    S (kW .arr) = carrSyms wI ((xs.drop (l0 * t)).map fun x => [x]) ++ rarr →
    (∀ k, S (sp (.F k)) = natSyms (pack s (F.reverse.map (cpart wT k)))) →
    S (sp (.X 4)) = [] → S (sp (.ru .rep)) = List.replicate rep .mark →
    S (sp (.ru .s)) = List.replicate s .mark → S (sp (.ru .sq)) = List.replicate q .mark →
    S (sp (.ru .h)) = List.replicate (s - q) .mark →
    S (sp (.ru .wI)) = List.replicate wI .mark →
    S (sp (.ru .Wm1)) = List.replicate (W - 1) .mark →
    S (sp (.ru .W)) = List.replicate W .mark →
    S (sp (.ru .wI1)) = List.replicate (wI - 1) .mark →
    S (sp (.ru .sWI)) = List.replicate (s - wI) .mark →
    S (sp (.pr 0)) = List.replicate ((W - 1) * (2 * wI + 1)) .mark →
    S (sp (.pr 1)) = List.replicate (t * (2 * wI + 1)) .mark →
    S (sp (.pr 2)) = List.replicate (a0 * (2 * wI + 1)) .mark →
    S (sp (.pr 3)) = List.replicate ((t - a0) * (2 * wI + 1)) .mark →
    S (sp (.pr 4)) = List.replicate ((W - 1) * s) .mark →
    (∀ x, LineScratch x → S (sp x) = []) →
    Runs (lineWalk lA PL) S
      (Function.update (Function.update S (kW .arr)
          (carrSyms wI ((xs.drop ((l0 + rep) * t)).map fun x => [x]) ++ rarr))
        (sp .Out) ((carrSyms wI ((grpOuts q t W a0 xs F l0 rep).map fun y => [y])).reverse ++
          S (sp .Out)))
      (fun _ => True) (rep * (CL * lineCost s t W + 4) + 4 * rep + 4)

end SubNLogN.Machine.Bridge.SpreadAux.Stage
