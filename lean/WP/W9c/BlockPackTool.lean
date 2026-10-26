import WP.W7k2.Ops

/-!
# WP.W9c.BlockPackTool — generic host rules used by `W9c_blockPack`

Exact-stack (`HT`) rules over host stacks `Loc a b` (any register type `σ`):
* symbol level: `peekR` (`tr_peekR`), `skipP`, `mvSym`, `ifTopP` (peek then branch);
* loops: `whileTopP` (count-down, peek condition) and `HT.loopFwd` (forward index, any test
  program, cost as a `List.range` sum, for amortised bodies);
* instance specifications of the W3 contracts not in `WP.W7k2.Ops` (verbatim contract bodies),
  their host rules, and monotonicity in the cost constant (to share one constant).

The symbol-level rules follow the owner's `WP.W9c.Tool` (same proofs, own names).
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

/-- Host programs. -/
abbrev BProg (a b : ℕ) (σ : Type) : Type := Prog (Loc a b) (fun _ => Sym) σ

/-- A test on an optional symbol (`none` fails). -/
def optP (c : Sym → Bool) : Option Sym → Bool
  | none => false
  | some x => c x

variable {a b : ℕ} {σ : Type}

/-- Peek `k` into the symbol register `lS`. -/
def peekR (lS : Lens σ (Option Sym)) (k : Loc a b) : BProg a b σ := .peek k (fun v o => lS.set v o)

/-- Push the symbol register (default `sep`). -/
def pushR' (lS : Lens σ (Option Sym)) (k : Loc a b) : BProg a b σ :=
  .push k (fun v => (lS.get v).getD .sep)

/-- Move one symbol from `src` to `dst`. -/
def mvSym (lS : Lens σ (Option Sym)) (src dst : Loc a b) : BProg a b σ :=
  (popR' lS src).seq (pushR' lS dst)

/-- Do nothing (one step). -/
def skipP : BProg a b σ := .load id

/-- `peek k; while c (top k) do (body; peek k)`. -/
def whileTopP (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (body : BProg a b σ) :
    BProg a b σ :=
  (peekR lS k).seq (.loop (fun v => optP c (lS.get v)) (body.seq (peekR lS k)))

/-- `peek k; if c (top k) then p else q`. -/
def ifTopP (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool) (p q : BProg a b σ) :
    BProg a b σ :=
  (peekR lS k).seq (.ite (fun v => optP c (lS.get v)) p q)

theorem mvSym_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) : (mvSym lS src dst).Closed :=
  ⟨trivial, trivial⟩

theorem whileTopP_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    {body : BProg a b σ} (h : body.Closed) : (whileTopP lS k c body).Closed :=
  ⟨trivial, h, trivial⟩

theorem ifTopP_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    {p q : BProg a b σ} (hp : p.Closed) (hq : q.Closed) : (ifTopP lS k c p q).Closed :=
  ⟨trivial, hp, hq⟩

variable {ρ : List (BProg a b σ)}

theorem tr_peekR (lS : Lens σ (Option Sym)) (k : Loc a b) (B : Loc a b → List Sym) :
    Triple ρ (fun s => s.stk = B) (peekR lS k)
      (fun s => s.stk = B ∧ lS.get s.var = (B k).head?) 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  refine ⟨_, 1, Eval.peek ρ k (fun v o => lS.set v o) v S, ⟨rfl, ?_⟩, le_rfl⟩
  show lS.get (lS.set v (S k).head?) = (S k).head?
  rw [lS.get_set]

theorem HT.skipP (B : Loc a b → List Sym) : HT ρ B skipP B 1 := by
  rintro ⟨v, S⟩ hS
  exact ⟨_, 1, Eval.load ρ id v S, hS, le_rfl⟩

theorem HT.mvSym (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (x : Sym) (rest : List Sym) (hB : B src = x :: rest) :
    HT ρ B (mvSym lS src dst) (Function.update (Function.update B src rest) dst (x :: B dst)) 2 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.pop ρ src (fun v o => lS.set v o) v S
  have e2 := Eval.push ρ dst (fun v => (lS.get v).getD .sep) (lS.set v (S src).head?)
    (Function.update S src (S src).tail)
  refine ⟨_, 2, Eval.seq e1 e2, ?_, le_rfl⟩
  show Function.update (Function.update S src (S src).tail) dst
      ((lS.get (lS.set v (S src).head?)).getD .sep ::
        Function.update S src (S src).tail dst) = _
  rw [lS.get_set, hB, Function.update_of_ne hne.symm]
  rfl

/-- **Branch on the top symbol.** -/
theorem HT.ifTopP (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    (B B' : Loc a b → List Sym) (p q : BProg a b σ) {T₁ T₂ : ℕ}
    (hp : optP c (B k).head? = true → HT ρ B p B' T₁)
    (hq : optP c (B k).head? = false → HT ρ B q B' T₂) :
    HT ρ B (ifTopP lS k c p q) B' (1 + (max T₁ T₂ + 1)) := by
  refine Triple.seq (tr_peekR lS k B) (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have h1 : optP c (B k).head? = true := by rw [← hsx]; exact hc
    exact (hp h1).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hc' : optP c (lS.get s.var) = false := by simpa using hc
    have h1 : optP c (B k).head? = false := by rw [← hsx]; exact hc'
    exact (hq h1).mono (le_max_right _ _) s hsB

/-- **Count-down peek loop.** `St n` has `n` iterations left. -/
theorem HT.whileTopP (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    (St : ℕ → Loc a b → List Sym) (body : BProg a b σ) (cb : ℕ → ℕ) (N : ℕ)
    (hc : ∀ n < N, optP c ((St (n + 1)) k).head? = true) (hc0 : optP c ((St 0) k).head? = false)
    (hbody : ∀ n < N, HT ρ (St (n + 1)) body (St n) (cb n)) :
    HT ρ (St N) (whileTopP lS k c body) (St 0) (loopCost (fun n => cb n + 1) N + 1) := by
  have hloop := Triple.loop (ρ := ρ) (c := fun v => optP c (lS.get v))
    (p := body.seq (peekR lS k))
    (I := fun n s => n ≤ N ∧ s.stk = St n ∧ lS.get s.var = (St n k).head?)
    (B := fun n => cb n + 1)
    (fun n => by
      by_cases hn : n < N
      · have h := Triple.seq (hbody n hn) (tr_peekR lS k (St n))
        exact Triple.conseq h (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) le_rfl
      · intro s hs
        exact absurd hs.1 (by omega))
    (fun n s hs => by show optP c (lS.get s.var) = true; rw [hs.2.2]; exact hc n (by omega))
    (fun s hs => by show optP c (lS.get s.var) = false; rw [hs.2.2]; exact hc0) N
  have h := Triple.seq (tr_peekR lS k (St N)) (Triple.pre hloop (fun s hs => ⟨le_rfl, hs⟩))
  exact Triple.conseq h (fun s hs => hs) (fun s hs => hs.2.1) (by omega)

/-! ## Forward counted loop with an arbitrary test program -/

theorem tr_loop_unfold {c : σ → Bool} {p : BProg a b σ}
    {P R Q : St (Loc a b) (fun _ => Sym) σ → Prop} {T₁ T₂ : ℕ}
    (hc : ∀ s, P s → c s.var = true) (h₁ : Triple ρ P p R T₁) (h₂ : Triple ρ R (.loop c p) Q T₂) :
    Triple ρ P (.loop c p) Q (T₁ + T₂ + 1) := by
  intro s hs
  obtain ⟨s₁, t₁, e₁, hr, ht₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := h₂ s₁ hr
  exact ⟨s₂, _, Eval.loop_true (hc s hs) e₁ e₂, hq, by omega⟩

theorem tr_loop_exit {c : σ → Bool} {p : BProg a b σ} {P : St (Loc a b) (fun _ => Sym) σ → Prop}
    (hc : ∀ s, P s → c s.var = false) : Triple ρ P (.loop c p) P 1 :=
  fun s hs => ⟨s, 1, Eval.loop_false (hc s hs), hs, le_rfl⟩

theorem sum_range_succ' (f : ℕ → ℕ) (j : ℕ) :
    ((List.range (j + 1)).map f).sum = f 0 + ((List.range j).map fun t => f (t + 1)).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rfl

/-- **Forward loop.** `test` sets the condition `c` to `i < N` on the state `St i`. -/
theorem HT.loopFwd (test body : BProg a b σ) (c : σ → Bool) (St : ℕ → Loc a b → List Sym)
    (N ct : ℕ) (cb : ℕ → ℕ)
    (htest : ∀ i ≤ N, Triple ρ (fun s => s.stk = St i) test
      (fun s => s.stk = St i ∧ c s.var = decide (i < N)) ct)
    (hbody : ∀ i < N, HT ρ (St i) body (St (i + 1)) (cb i)) :
    HT ρ (St 0) (test.seq (.loop c (body.seq test))) (St N)
      (ct + (((List.range N).map fun i => cb i + ct + 1).sum + 1)) := by
  have key : ∀ j i, i + j = N → Triple ρ (fun s => s.stk = St i ∧ c s.var = decide (i < N))
      (.loop c (body.seq test)) (fun s => s.stk = St N)
      (((List.range j).map fun t => cb (i + t) + ct + 1).sum + 1) := by
    intro j
    induction j with
    | zero =>
      intro i hi
      simp only [Nat.add_zero] at hi
      subst hi
      refine Triple.cost_mono (Triple.post (tr_loop_exit (fun s hs => ?_)) (fun s hs => hs.1))
        (by simp)
      rw [hs.2]
      simp
    | succ j ih =>
      intro i hi
      have hlt : i < N := by omega
      have h1 : Triple ρ (fun s => s.stk = St i ∧ c s.var = decide (i < N)) (body.seq test)
          (fun s => s.stk = St (i + 1) ∧ c s.var = decide (i + 1 < N)) (cb i + ct) :=
        Triple.seq (Triple.pre (hbody i hlt) (fun s hs => hs.1)) (htest (i + 1) (by omega))
      have h2 := ih (i + 1) (by omega)
      refine (tr_loop_unfold (fun s hs => by rw [hs.2]; exact decide_eq_true hlt) h1 h2).cost_mono ?_
      rw [sum_range_succ']
      have e : ((List.range j).map fun t => cb (i + (t + 1)) + ct + 1) =
          ((List.range j).map fun t => cb (i + 1 + t) + ct + 1) := by
        refine List.map_congr_left fun t _ => ?_
        rw [show i + (t + 1) = i + 1 + t by omega]
      rw [e]
      simp only [Nat.add_zero]
      omega
  have h0 := Triple.seq (htest 0 (Nat.zero_le _)) (key N 0 (by omega))
  simp only [Nat.zero_add] at h0
  exact h0

/-! ## Instance specifications (verbatim bodies of the W3 contracts) -/

/-- Body of `W3_incNat`. -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (encodeNat a) + 1))

/-- Body of `W3_decNat`. -/
def SpecDec (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (zerosLead (encodeNat (a + 1)) + 1))

/-- Body of `W3_addNat`. -/
def SpecAdd (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_subNat`. -/
def SpecSub (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_shrVar`. -/
def SpecShrVar (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_shrConst` at shift `k`. -/
def SpecShrConst (k : ℕ) (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ k) ++ rx)) (fun _ => True)
      (C * (k + 1))

/-- Body of `W3_splitAt`. -/
def SpecSplit (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx))
        (.inl 2) (natSyms (a % 2 ^ c) ++ S (.inl 2))) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_concatAt`. -/
def SpecCat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (hi lo c : ℕ) (rx rc ry : List Sym) (S : Loc 3 I.m → List Sym),
    TermOK rx → TermOK rc → TermOK ry → lo < 2 ^ c →
    S (.inl 0) = natSyms hi ++ rx → S (.inl 1) = natSyms c ++ rc →
    S (.inl 2) = natSyms lo ++ ry →
    Runs I.P S (Function.update (Function.update S (.inl 0) (natSyms (lo + hi * 2 ^ c) ++ rx))
        (.inl 2) ry) (fun _ => True)
      (C * (c + bitLen c + 1))

/-- Body of `W3_subInt`. -/
def SpecSubInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-! ## Monotonicity in the cost constant -/

section Mono

variable {C C' : ℕ} (hC : C ≤ C')
include hC

theorem SpecCopy.mono {I : Inst 2 4 Unit} (h : SpecCopy I C) : SpecCopy I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecDrop.mono {I : Inst 1 4 Unit} (h : SpecDrop I C) : SpecDrop I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecShlVar.mono {I : Inst 2 4 Unit} (h : SpecShlVar I C) : SpecShlVar I C' :=
  fun a c rx rc S h1 h2 h3 h4 =>
    Triple.cost_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecCmpNat.mono {I : Inst 2 4 Ordering} (h : SpecCmpNat I C) : SpecCmpNat I C' :=
  fun a b' rx ry S h1 h2 h3 h4 =>
    Triple.cost_mono (h a b' rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecInc.mono {I : Inst 1 4 Unit} (h : SpecInc I C) : SpecInc I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecDec.mono {I : Inst 1 4 Unit} (h : SpecDec I C) : SpecDec I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecAdd.mono {I : Inst 3 4 Unit} (h : SpecAdd I C) : SpecAdd I C' :=
  fun a b' rx ry S h1 h2 h3 h4 =>
    Triple.cost_mono (h a b' rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecSub.mono {I : Inst 3 4 Unit} (h : SpecSub I C) : SpecSub I C' :=
  fun a b' rx ry S h1 h2 h0 h3 h4 =>
    Triple.cost_mono (h a b' rx ry S h1 h2 h0 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecShrVar.mono {I : Inst 2 4 Unit} (h : SpecShrVar I C) : SpecShrVar I C' :=
  fun a c rx rc S h1 h2 h3 h4 =>
    Triple.cost_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecShrConst.mono {k : ℕ} {I : Inst 1 4 Unit} (h : SpecShrConst k I C) :
    SpecShrConst k I C' :=
  fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem SpecSplit.mono {I : Inst 3 4 Unit} (h : SpecSplit I C) : SpecSplit I C' :=
  fun a c rx rc S h1 h2 h3 h4 =>
    Triple.cost_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecCat.mono {I : Inst 3 4 Unit} (h : SpecCat I C) : SpecCat I C' :=
  fun hi lo c rx rc ry S h1 h2 h3 h0 h4 h5 h6 =>
    Triple.cost_mono (h hi lo c rx rc ry S h1 h2 h3 h0 h4 h5 h6) (Nat.mul_le_mul_right _ hC)

theorem SpecSubInt.mono {I : Inst 3 4 Unit} (h : SpecSubInt I C) : SpecSubInt I C' :=
  fun a b' rx ry S h1 h2 h3 h4 =>
    Triple.cost_mono (h a b' rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

end Mono

#assert_std_axioms mvSym_closed whileTopP_closed ifTopP_closed tr_peekR HT.skipP HT.mvSym
  HT.ifTopP HT.whileTopP tr_loop_unfold tr_loop_exit sum_range_succ' HT.loopFwd SpecCopy.mono
  SpecDrop.mono SpecShlVar.mono SpecCmpNat.mono SpecInc.mono SpecDec.mono SpecAdd.mono
  SpecSub.mono SpecShrVar.mono SpecShrConst.mono SpecSplit.mono SpecCat.mono SpecSubInt.mono

end WP.W9c.BlockPack
