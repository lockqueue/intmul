import WP.W9fF.IntMacros

/-!
# WP.W9fF.IntCore — the integer straight-line language, its compiler, and the main theorem

Copy of `WP.IntLang.Core` (IntLang), placed in namespace `WP.W9fF.IL` with
four elaboration fixes (explicit `K := IStk V`, explicit register witness).

**Language** (`Stmt O V`): a finite type `V` of integer variables and a type `O` of binary
operation symbols.
* `assign x (.const c)` : `x := c`;
* `assign x (.op o y z)` : `x := sem o (env y) (env z)` (aliasing `x = y = z` allowed);
* `seq p q`;
* `ite v sel p q` : `if sel (cmpZ (env v) 0) then p else q` (sign test, `O(1)` on the machine);
* `rep n p` : run `p` exactly `(env n).toNat` times (count fixed at entry; a binary counter).

**Machine layout** (`IStk V = V ⊕ Fin 20`):
* variable `v` lives on stack `.inl v` as `intSyms (env v) ++ R v` with `TermOK (R v)`;
* scratch `.inr 0..3` = `A, B, T, CNT` (operand copies, copy temporary, loop counters),
  `.inr 4..19` = the 16-stack pool for the operations' own scratch stacks;
* scratch stacks have arbitrary content `Z j` and are restored exactly.

**Operations** are parameters: `I : O → OpImpl`, each a program in the machine
contracts' shape (`Loc 3 m`, `m ≤ 16`, private registers) satisfying `BinOK (I o) (sem o) (κ o)`:
`z += sem o a b`, operands restored, within `κ o a b` steps.

**Main theorem** (`compile_correct`): for every environment `env`, every `R` with `TermOK` and every
scratch content `Z`, the compiled program runs from `enc R Z env` to exactly `enc R Z (eval env)`
within `cost env` steps, from any register value. `compile_runs` restates it with the contracts'
`Runs`, so it embeds into any global layout with `Runs.embed`.
-/

namespace WP.W9fF.IL

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Stacks, registers, operation implementations -/

/-- Stacks of a compiled program: variables `.inl v`; scratch `.inr 0..3` = `A, B, T, CNT`;
op scratch pool `.inr 4..19`. -/
abbrev IStk (V : Type) := V ⊕ Fin 20

/-- An implementation of a binary signed operation, in the machine contracts' shape: a program
over `Loc 3 m` (`.inl 0` = `x`, `.inl 1` = `y` operands, `.inl 2` = `z` destination; `m ≤ 16`
scratch stacks) with private registers `R`. -/
structure OpImpl where
  /-- number of scratch stacks -/
  m : ℕ
  /-- at most 16 scratch stacks (the pool) -/
  hm : m ≤ 16
  /-- private registers -/
  R : Type
  /-- the program -/
  P : Prog (Loc 3 m) (fun _ => Sym) R

/-- The contract side conditions: closed program, finite nonempty registers. -/
def OpImpl.Good (I : OpImpl) : Prop := I.P.Closed ∧ Finite I.R ∧ Nonempty I.R

/-- **`I` computes `z += f a b`**: operands `x`, `y` restored, every other stack unchanged, within
`κ a b` steps, from any register value. The destination's old content must be terminated. -/
def BinOK (I : OpImpl) (f : ℤ → ℤ → ℤ) (κ : ℤ → ℤ → ℕ) : Prop :=
  ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym), TermOK ra → TermOK rb →
    TermOK (S (.inl 2)) → S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (f a b) ++ S (.inl 2))) (fun _ => True)
      (κ a b)

/-- Registers of a compiled program: the macro register, the sign-test result, and every
operation's private registers. -/
abbrev GReg {O : Type} (I : O → OpImpl) := (Option Sym × Ordering) × ((o : O) → (I o).R)

/-- Lens onto one component of a dependent function. -/
def piLens {O : Type} [DecidableEq O] (R : O → Type) (o : O) : Lens ((o : O) → R o) (R o) where
  get v := v o
  set v w := Function.update v o w
  get_set v w := Function.update_self o w v
  set_get v := Function.update_eq_self o v
  set_set v w w' := Function.update_idem w w' v

section Lenses

variable {O : Type} [DecidableEq O] (I : O → OpImpl)

/-- The macro register. -/
def macroLens : Lens (GReg I) (Option Sym) := Lens.comp (Lens.fst _ _) (Lens.fst _ _)

/-- The sign-test registers (macro register and result). -/
def testLens : Lens (GReg I) (Option Sym × Ordering) := Lens.fst _ _

/-- The registers of operation `o`. -/
def opLens (o : O) : Lens (GReg I) (I o).R := Lens.comp (Lens.snd _ _) (piLens _ o)

end Lenses

/-- Compiled programs. -/
abbrev GProg {O : Type} (I : O → OpImpl) (V : Type) := Prog (IStk V) (fun _ => Sym) (GReg I)

/-- Stack-only `Runs`: from stacks `S` (any registers) to stacks exactly `S'` within `T`. -/
def RunsS {K σ : Type} [DecidableEq K] (P : Prog K (fun _ => Sym) σ) (S S' : K → List Sym)
    (T : ℕ) : Prop :=
  Triple [] (fun s => s.stk = S) P (fun s => s.stk = S') T

section RunsS

variable {K σ : Type} [DecidableEq K]

theorem RunsS.seq {p q : Prog K (fun _ => Sym) σ} {S₁ S₂ S₃ : K → List Sym} {T₁ T₂ : ℕ}
    (h₁ : RunsS p S₁ S₂ T₁) (h₂ : RunsS q S₂ S₃ T₂) : RunsS (.seq p q) S₁ S₃ (T₁ + T₂) :=
  Triple.seq h₁ h₂

theorem RunsS.of_eq {p : Prog K (fun _ => Sym) σ} {S S₁ S₂ : K → List Sym} {T₁ T₂ : ℕ}
    (h : RunsS p S S₁ T₁) (hS : S₁ = S₂) (hT : T₁ ≤ T₂) : RunsS p S S₂ T₂ := by
  subst hS
  exact Triple.cost_mono h hT

theorem RunsS.toRuns {p : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {T : ℕ}
    (h : RunsS p S S' T) : Runs p S S' (fun _ => True) T :=
  Triple.post h (fun _ hs => ⟨hs, trivial⟩)

end RunsS

/-! ## Lifting macros and embedding operations -/

section Embed

variable {O V : Type} [DecidableEq O] [DecidableEq V] (I : O → OpImpl)

/-- Run a macro (`Option Sym` register) inside a compiled program. -/
def liftM (p : SProg (IStk V)) : GProg I V := p.liftRegs (macroLens I)

/-- Embedding of an operation's local stacks: `x ↦ A`, `y ↦ B`, `z ↦` variable `d`,
scratch `j ↦ .inr (j + 4)`. -/
def opEmb (d : V) {m : ℕ} (hm : m ≤ 16) : Loc 3 m → IStk V
  | .inl i => if i.1 = 0 then .inr 0 else if i.1 = 1 then .inr 1 else .inl d
  | .inr j => .inr ⟨j.1 + 4, by omega⟩

omit [DecidableEq V] in
theorem opEmb_injective (d : V) {m : ℕ} (hm : m ≤ 16) : Function.Injective (opEmb d hm) := by
  rintro (⟨i, hi⟩ | ⟨j, hj⟩) (⟨i', hi'⟩ | ⟨j', hj'⟩) h <;> simp only [opEmb] at h
  · have : i = i' := by
      split_ifs at h <;> first | omega | (simp at h)
    subst this
    rfl
  · split_ifs at h <;> simp [Fin.ext_iff] at h
  · split_ifs at h <;> simp [Fin.ext_iff] at h
  · simp only [Sum.inr.injEq, Fin.mk.injEq, Nat.add_right_cancel_iff] at h
    subst h
    rfl

/-- Call operation `o` with operands on `A`, `B` and destination variable `d`. -/
def callOp (o : O) (d : V) : GProg I V :=
  ((I o).P.mapStk (opEmb d (I o).hm)).liftRegs (opLens I o)

omit [DecidableEq O] in
theorem liftM_runs {p : SProg (IStk V)} {S S' : IStk V → List Sym} {t : ℕ}
    (h : ∀ v, ∃ v', Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t) : RunsS (liftM I p) S S' t := by
  rintro ⟨w, S0⟩ hs
  change S0 = S at hs
  subst hs
  obtain ⟨v', e⟩ := h ((macroLens I).get w)
  exact ⟨_, t, Eval.liftRegs (macroLens I) e w rfl, rfl, le_rfl⟩

omit [DecidableEq O] [DecidableEq V] in
/-- Stacks after an embedded run: the image is updated, the rest unchanged. -/
theorem stk_eq_update_of_embed {L K : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) {G G' : K → List Sym} {l₀ : L} {X : List Sym}
    (h1 : ∀ l, G' (ι l) = Function.update (fun l => G (ι l)) l₀ X l)
    (h2 : ∀ k, (∀ l, ι l ≠ k) → G' k = G k) :
    G' = Function.update G (ι l₀) X := by
  funext k
  by_cases hk : ∃ l, ι l = k
  · obtain ⟨l, rfl⟩ := hk
    rw [h1]
    by_cases hl : l = l₀
    · subst hl
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hl, Function.update_of_ne (hι.ne hl)]
  · simp only [not_exists] at hk
    rw [h2 k hk, Function.update_of_ne (fun e => hk l₀ e.symm)]

/-- **Calling an operation**: `d += f a b` for operands on `A`, `B`. -/
theorem callOp_runs (o : O) (d : V) {f : ℤ → ℤ → ℤ} {κ : ℤ → ℤ → ℕ} (hok : BinOK (I o) f κ)
    (a b : ℤ) (ra rb : List Sym) (G : IStk V → List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hA : G (.inr 0) = intSyms a ++ ra) (hB : G (.inr 1) = intSyms b ++ rb)
    (hD : TermOK (G (.inl d))) :
    RunsS (callOp I o d) G (Function.update G (.inl d) (intSyms (f a b) ++ G (.inl d)))
      (κ a b) := by
  have hι : Function.Injective (opEmb d (I o).hm) := opEmb_injective d (I o).hm
  have h2 : opEmb d (I o).hm (.inl 2) = .inl d := rfl
  have hrun := hok a b ra rb (fun l => G (opEmb d (I o).hm l)) hra hrb hD hA hB
  have hemb := Runs.embed hι hrun G (fun _ => rfl)
  have hlift := Triple.liftRegs (opLens I o) hemb (fun _ => True) (fun _ _ _ => trivial)
  intro s hs
  obtain ⟨s', t, e, ⟨⟨hA', hB', -⟩, -⟩, ht⟩ := hlift s ⟨hs, trivial⟩
  refine ⟨s', t, e, ?_, ht⟩
  have := stk_eq_update_of_embed hι hA' hB'
  rw [h2] at this
  exact this

end Embed

/-! ## Operand loading and unloading -/

section Load

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
theorem inr_ne {i j : Fin 20} (h : i ≠ j) : (Sum.inr i : IStk V) ≠ Sum.inr j :=
  fun e => h (Sum.inr.inj e)

/-- Load `y` onto `A` and `z` onto `B`, each above a `mark`. -/
def loadAB (y z : V) : SProg (IStk V) :=
  .seq (pushC (.inr 0) .mark) (.seq (copyInt (.inl y) (.inr 0) (.inr 2))
    (.seq (pushC (.inr 1) .mark) (copyInt (.inl z) (.inr 1) (.inr 2))))

theorem loadAB_eval (y z : V) (a b : ℤ) (ry rz : List Sym) (G : IStk V → List Sym)
    (hry : TermOK ry) (hrz : TermOK rz) (hy : G (.inl y) = intSyms a ++ ry)
    (hz : G (.inl z) = intSyms b ++ rz) (v : Option Sym) :
    ∃ v', Eval [] (loadAB y z) ⟨v, G⟩
      ⟨v', Function.update (Function.update G (.inr 0) (intSyms a ++ .mark :: G (.inr 0)))
        (.inr 1) (intSyms b ++ .mark :: G (.inr 1))⟩
      (7 * bitLen a.natAbs + 7 * bitLen b.natAbs + 26) := by
  have hAB : (Sum.inr 0 : IStk V) ≠ Sum.inr 1 := inr_ne (by decide)
  have hAT : (Sum.inr 0 : IStk V) ≠ Sum.inr 2 := inr_ne (by decide)
  have hBT : (Sum.inr 1 : IStk V) ≠ Sum.inr 2 := inr_ne (by decide)
  have e1 : Eval [] (pushC (.inr 0) .mark) ⟨v, G⟩
      ⟨v, Function.update G (.inr 0) (.mark :: G (.inr 0))⟩ 1 :=
    (Eval.push ([] : List (SProg (IStk V))) (Sum.inr 0) (fun _ => Sym.mark) v G).of_eq rfl rfl
  set G1 := Function.update G (.inr 0) (.mark :: G (.inr 0)) with hG1
  have e2 := copyInt_eval (K := IStk V) (src := .inl y) (dst := .inr 0) (tmp := .inr 2) Sum.inl_ne_inr
    Sum.inl_ne_inr hAT [] v a ry G1 hry (by rw [hG1, Function.update_of_ne Sum.inl_ne_inr, hy])
  set G2 := Function.update G1 (.inr 0) (intSyms a ++ G1 (.inr 0)) with hG2
  have e3 : Eval [] (pushC (.inr 1) .mark) ⟨some (sgnSym a), G2⟩
      ⟨some (sgnSym a), Function.update G2 (.inr 1) (.mark :: G2 (.inr 1))⟩ 1 :=
    (Eval.push ([] : List (SProg (IStk V))) (Sum.inr 1) (fun _ => Sym.mark) (some (sgnSym a)) G2).of_eq
      rfl rfl
  set G3 := Function.update G2 (.inr 1) (.mark :: G2 (.inr 1)) with hG3
  have e4 := copyInt_eval (K := IStk V) (src := .inl z) (dst := .inr 1) (tmp := .inr 2) Sum.inl_ne_inr
    Sum.inl_ne_inr hBT [] (some (sgnSym a)) b rz G3 hrz
    (by rw [hG3, Function.update_of_ne Sum.inl_ne_inr, hG2, Function.update_of_ne Sum.inl_ne_inr,
      hG1, Function.update_of_ne Sum.inl_ne_inr, hz])
  refine ⟨some (sgnSym b), (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ (by omega)⟩
  congr 1
  funext k
  simp only [hG3, hG2, hG1, Function.update_apply]
  split_ifs <;> simp_all

/-- Drop the operand copies on `A` and `B` and their marks. -/
def unloadAB : SProg (IStk V) :=
  .seq (dropInt (.inr 0)) (.seq (popR (.inr 0)) (.seq (dropInt (.inr 1)) (popR (.inr 1))))

theorem unloadAB_eval (a b : ℤ) (ZA ZB : List Sym) (G : IStk V → List Sym)
    (hA : G (.inr 0) = intSyms a ++ .mark :: ZA) (hB : G (.inr 1) = intSyms b ++ .mark :: ZB)
    (v : Option Sym) :
    ∃ v', Eval [] unloadAB ⟨v, G⟩
      ⟨v', Function.update (Function.update G (.inr 0) ZA) (.inr 1) ZB⟩
      (2 * bitLen a.natAbs + 2 * bitLen b.natAbs + 12) := by
  have hAB : (Sum.inr 0 : IStk V) ≠ Sum.inr 1 := inr_ne (by decide)
  have e1 := dropInt_eval [] (.inr 0) v a (.mark :: ZA) G (TermOK.cons rfl _) hA
  set G1 := Function.update G (.inr 0) (.mark :: ZA) with hG1
  have e2 : Eval [] (popR (.inr 0)) ⟨some .mark, G1⟩
      ⟨some .mark, Function.update G1 (.inr 0) ZA⟩ 1 := by
    have h := Eval.pop [] (.inr 0) (fun _ o => o) (some .mark) G1
    rw [hG1, Function.update_self] at h
    rw [hG1]
    exact h
  set G2 := Function.update G1 (.inr 0) ZA with hG2
  have e3 := dropInt_eval [] (.inr 1) (some .mark) b (.mark :: ZB) G2 (TermOK.cons rfl _)
    (by rw [hG2, Function.update_of_ne (Ne.symm hAB), hG1, Function.update_of_ne (Ne.symm hAB),
      hB])
  set G3 := Function.update G2 (.inr 1) (.mark :: ZB) with hG3
  have e4 : Eval [] (popR (.inr 1)) ⟨some .mark, G3⟩
      ⟨some .mark, Function.update G3 (.inr 1) ZB⟩ 1 := by
    have h := Eval.pop [] (.inr 1) (fun _ o => o) (some .mark) G3
    rw [hG3, Function.update_self] at h
    rw [hG3]
    exact h
  refine ⟨some Sym.mark, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ (by omega)⟩
  congr 1
  funext k
  simp only [hG3, hG2, hG1, Function.update_apply]
  split_ifs <;> simp_all

end Load

/-! ## The language -/

/-- Right-hand sides. -/
inductive Expr (O V : Type) where
  /-- a compile-time constant -/
  | const (c : ℤ)
  /-- a binary operation on two variables -/
  | op (o : O) (y z : V)

/-- Statements. -/
inductive Stmt (O V : Type) where
  /-- `x := e` -/
  | assign (x : V) (e : Expr O V)
  /-- `p; q` -/
  | seq (p q : Stmt O V)

section Semantics

variable {O V : Type}

/-- Value of a right-hand side. -/
def Expr.eval (sem : O → ℤ → ℤ → ℤ) (env : V → ℤ) : Expr O V → ℤ
  | .const c => c
  | .op o y z => sem o (env y) (env z)

/-- Cost of a right-hand side (machine steps, given the operations' bounds `κ`). -/
def Expr.cost (κ : O → ℤ → ℤ → ℕ) (env : V → ℤ) : Expr O V → ℕ
  | .const c => bitLen c.natAbs + 2
  | .op o y z => κ o (env y) (env z) + 9 * bitLen (env y).natAbs + 9 * bitLen (env z).natAbs + 38

variable [DecidableEq V]

/-- **Semantics**: the pure interpreter. -/
def Stmt.eval (sem : O → ℤ → ℤ → ℤ) : Stmt O V → (V → ℤ) → V → ℤ
  | .assign x e, env => Function.update env x (e.eval sem env)
  | .seq p q, env => q.eval sem (p.eval sem env)

/-- **Cost** (machine steps), given the operations' bounds `κ`. -/
def Stmt.cost (sem : O → ℤ → ℤ → ℤ) (κ : O → ℤ → ℤ → ℕ) : Stmt O V → (V → ℤ) → ℕ
  | .assign x e, env => e.cost κ env + 2 * bitLen (env x).natAbs + 5
  | .seq p q, env => p.cost sem κ env + q.cost sem κ (p.eval sem env)

end Semantics

/-! ## The compiler -/

section Compile

variable {O V : Type} [DecidableEq O] [DecidableEq V] (I : O → OpImpl)

/-- Compile `x := e`. -/
def Expr.compile (x : V) : Expr O V → GProg I V
  | .const c => liftM I (.seq (dropInt (.inl x)) (pushInt (.inl x) c))
  | .op o y z => .seq (liftM I (.seq (loadAB y z) (dropInt (.inl x))))
      (.seq (callOp I o x) (liftM I unloadAB))

/-- **The compiler.** -/
def Stmt.compile : Stmt O V → GProg I V
  | .assign x e => e.compile I x
  | .seq p q => .seq p.compile q.compile

/-- Stacks encoding an environment: variable `v` holds `intSyms (env v) ++ R v`, scratch stack
`j` holds `Z j`. -/
def enc (R : V → List Sym) (Z : Fin 20 → List Sym) (env : V → ℤ) : IStk V → List Sym
  | .inl v => intSyms (env v) ++ R v
  | .inr j => Z j

theorem enc_update (R : V → List Sym) (Z : Fin 20 → List Sym) (env : V → ℤ) (x : V) (c : ℤ) :
    enc R Z (Function.update env x c) =
      Function.update (enc R Z env) (.inl x) (intSyms c ++ R x) := by
  funext k
  rcases k with v | j
  · by_cases h : v = x
    · subst h
      simp [enc]
    · simp [enc, h]
  · simp [enc]

/-- **Main theorem (exact stacks, cost bound).** -/
theorem compile_correct (sem : O → ℤ → ℤ → ℤ) (κ : O → ℤ → ℤ → ℕ)
    (hok : ∀ o, BinOK (I o) (sem o) (κ o)) (R : V → List Sym) (hR : ∀ v, TermOK (R v)) :
    ∀ (p : Stmt O V) (Z : Fin 20 → List Sym) (env : V → ℤ),
      RunsS (p.compile I) (enc R Z env) (enc R Z (p.eval sem env)) (p.cost sem κ env)
  | .assign x (.const c), Z, env => by
    show RunsS (liftM I (.seq (dropInt (.inl x)) (pushInt (.inl x) c))) (enc R Z env)
      (enc R Z (Function.update env x c)) (bitLen c.natAbs + 2 + 2 * bitLen (env x).natAbs + 5)
    rw [enc_update]
    refine liftM_runs I (fun v => ?_)
    have e1 := dropInt_eval [] (.inl x) v (env x) (R x) (enc R Z env) (hR x) rfl
    have e2 := pushInt_eval [] (.inl x) (R x).head? c
      (Function.update (enc R Z env) (.inl x) (R x))
    refine ⟨(R x).head?, (Eval.seq e1 e2).of_eq ?_ (by omega)⟩
    rw [Function.update_idem, Function.update_self]
  | .assign x (.op o y z), Z, env => by
    show RunsS (.seq (liftM I (.seq (loadAB y z) (dropInt (.inl x))))
        (.seq (callOp I o x) (liftM I unloadAB))) (enc R Z env)
      (enc R Z (Function.update env x (sem o (env y) (env z))))
      (κ o (env y) (env z) + 9 * bitLen (env y).natAbs + 9 * bitLen (env z).natAbs + 38 +
        2 * bitLen (env x).natAbs + 5)
    have hAB : (Sum.inr 0 : IStk V) ≠ Sum.inr 1 := inr_ne (by decide)
    set G := enc R Z env with hG
    set G1 := Function.update (Function.update (Function.update G (.inr 0)
      (intSyms (env y) ++ .mark :: G (.inr 0))) (.inr 1) (intSyms (env z) ++ .mark :: G (.inr 1)))
      (.inl x) (R x) with hG1
    have r1 : RunsS (liftM I (.seq (loadAB y z) (dropInt (K := IStk V) (.inl x)))) G G1
        (7 * bitLen (env y).natAbs + 7 * bitLen (env z).natAbs + 26 +
          (2 * bitLen (env x).natAbs + 5)) := by
      refine liftM_runs I (fun v => ?_)
      obtain ⟨v1, e1⟩ := loadAB_eval y z (env y) (env z) (R y) (R z) G (hR y) (hR z) rfl rfl v
      have e2 := dropInt_eval (K := IStk V) [] (.inl x) v1 (env x) (R x)
        (Function.update (Function.update G (.inr 0) (intSyms (env y) ++ .mark :: G (.inr 0)))
          (.inr 1) (intSyms (env z) ++ .mark :: G (.inr 1))) (hR x)
        (by rw [Function.update_of_ne Sum.inl_ne_inr, Function.update_of_ne Sum.inl_ne_inr]; rfl)
      exact ⟨_, Eval.seq e1 e2⟩
    have hA1 : G1 (.inr 0) = intSyms (env y) ++ .mark :: G (.inr 0) := by
      rw [hG1, Function.update_of_ne Sum.inr_ne_inl, Function.update_of_ne hAB,
        Function.update_self]
    have hB1 : G1 (.inr 1) = intSyms (env z) ++ .mark :: G (.inr 1) := by
      rw [hG1, Function.update_of_ne Sum.inr_ne_inl, Function.update_self]
    have hX1 : G1 (.inl x) = R x := by rw [hG1, Function.update_self]
    have r2 := callOp_runs I o x (hok o) (env y) (env z) _ _ G1 (TermOK.cons rfl _)
      (TermOK.cons rfl _) hA1 hB1 (by rw [hX1]; exact hR x)
    set G2 := Function.update G1 (.inl x) (intSyms (sem o (env y) (env z)) ++ G1 (.inl x))
      with hG2
    have r3 : RunsS (liftM I unloadAB) G2
        (Function.update (Function.update G2 (.inr 0) (G (.inr 0))) (.inr 1) (G (.inr 1)))
        (2 * bitLen (env y).natAbs + 2 * bitLen (env z).natAbs + 12) :=
      liftM_runs I (fun v => unloadAB_eval (env y) (env z) _ _ G2
        (by rw [hG2, Function.update_of_ne Sum.inr_ne_inl, hA1])
        (by rw [hG2, Function.update_of_ne Sum.inr_ne_inl, hB1]) v)
    refine (RunsS.seq r1 (RunsS.seq r2 r3)).of_eq ?_ (by omega)
    rw [enc_update]
    funext k
    simp only [hG2, hG1, Function.update_apply]
    split_ifs <;> simp_all
  | .seq p q, Z, env =>
    RunsS.seq (compile_correct sem κ hok R hR p Z env)
      (compile_correct sem κ hok R hR q Z (p.eval sem env))

/-- **Main theorem, contract form** (`Runs`, so `Runs.embed` applies). -/
theorem compile_runs (sem : O → ℤ → ℤ → ℤ) (κ : O → ℤ → ℤ → ℕ)
    (hok : ∀ o, BinOK (I o) (sem o) (κ o)) (R : V → List Sym) (hR : ∀ v, TermOK (R v))
    (p : Stmt O V) (Z : Fin 20 → List Sym) (env : V → ℤ) :
    Runs (p.compile I) (enc R Z env) (enc R Z (p.eval sem env)) (fun _ => True)
      (p.cost sem κ env) :=
  (compile_correct I sem κ hok R hR p Z env).toRuns

end Compile

#assert_std_axioms RunsS.seq RunsS.of_eq RunsS.toRuns opEmb_injective liftM_runs
  stk_eq_update_of_embed callOp_runs loadAB_eval unloadAB_eval enc_update compile_correct
  compile_runs

end WP.W9fF.IL
