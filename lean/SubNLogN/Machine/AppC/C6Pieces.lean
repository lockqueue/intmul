/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6PiecesMath
import SubNLogN.Machine.K1.LongRecordBase
import SubNLogN.Machine.K1.RotateBase
import SubNLogN.Machine.Calculus.Loops

/-!
# Lemma A.8 level E (`Machine/AppC/C6Pieces.lean`): the base-`m` pieces by Proposition A.7

**Theorem** (`c6Pieces_of_parts`): for `q ≥ 2`, `C5InterchangeStmt q τ` and the three counter
leaves `C6PcTestStmt q`, `C6PcArgsStmt q`, `C6PcAdvStmt q` give `C6PiecesStmt q τ`
(Lemma A.8 (`lem:transfer12`), base-`m` piece loop). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Program** (`progE`) on `KLoc (Fin 5) (Et ⊕ Ea ⊕ E5 ⊕ Ev ⊕ Fin 6)`: put a `mark` floor on the six
counter stacks (`o`, then the Proposition A.7 counters `j, R', N1, G', B'`); test `o < ℓ`; while it holds:
push the Proposition A.7 counters of the piece at offset `o`, run Proposition A.7, advance `o` by the piece length and pop
the counters, test again; finally drop `o = ℓ` with its floor and pop the five floors.

**Correctness**: the array after the pieces up to offset `o` is
`permByInv (c6SP q ℓ G B o) v` (`c6SP_step`, `c6SP_zero`, `c6SP_full`).

**Cost**: with the digit potential `Φ = c6Phi e (m^τ) (ℓ - o)`, each iteration costs at most
`D·(m^τ)^j` and lowers `Φ` by exactly `(m^τ)^j` (`c6Phi_step`), so the loop costs at most
`⌈D·Φ(ℓ)⌉₊ + 1 ≤ ⌈2(m-1)·D·e^τ⌉₊ + 1` (`c6Phi_le`, `m^τ ≥ 2`), and `D = O(V)` (`cube_le`,
`len_ge`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.Calculus

namespace AppC.C6Aux

/-! ## The composite layout of level E -/

/-- Scratch of level E: test, args, Proposition A.7, advance, and the six counter stacks. -/
abbrev EE (Et Ea E5 Ev : Type) : Type := Et ⊕ (Ea ⊕ (E5 ⊕ (Ev ⊕ Fin 6)))

/-- Registers of level E; the last component is the work register of `dropBits`. -/
abbrev RE (Rt Ra R5 Rv : Type) : Type := Rt × (Ra × (R5 × (Rv × Option Sym)))

section Layout

variable (Et Ea E5 Ev : Type)

/-- The six counter stacks: `0` the offset `o`, `1`-`5` the Proposition A.7 counters `j, R', N1, G', B'`. -/
def scE (i : Fin 6) : KLoc (Fin 5) (EE Et Ea E5 Ev) := .inr (.inr (.inr (.inr (.inr i))))

def ιET : KLoc (Fin 2) Et → KLoc (Fin 5) (EE Et Ea E5 Ev) :=
  Sum.elim ![.inl 1, scE Et Ea E5 Ev 0] fun x => .inr (.inl x)

def ιEA : KLoc (Fin 9) Ea → KLoc (Fin 5) (EE Et Ea E5 Ev) :=
  Sum.elim ![.inl 1, .inl 2, .inl 3, scE Et Ea E5 Ev 0, scE Et Ea E5 Ev 1, scE Et Ea E5 Ev 2,
    scE Et Ea E5 Ev 3, scE Et Ea E5 Ev 4, scE Et Ea E5 Ev 5] fun x => .inr (.inr (.inl x))

def ιE5 : KLoc (Fin 6) E5 → KLoc (Fin 5) (EE Et Ea E5 Ev) :=
  Sum.elim ![.inl 0, scE Et Ea E5 Ev 1, scE Et Ea E5 Ev 2, scE Et Ea E5 Ev 3, scE Et Ea E5 Ev 4,
    scE Et Ea E5 Ev 5] fun x => .inr (.inr (.inr (.inl x)))

def ιEV : KLoc (Fin 6) Ev → KLoc (Fin 5) (EE Et Ea E5 Ev) :=
  Sum.elim ![scE Et Ea E5 Ev 0, scE Et Ea E5 Ev 1, scE Et Ea E5 Ev 2, scE Et Ea E5 Ev 3,
    scE Et Ea E5 Ev 4, scE Et Ea E5 Ev 5] fun x => .inr (.inr (.inr (.inr (.inl x))))

theorem ιET_inj : Function.Injective (ιET Et Ea E5 Ev) := by
  refine Function.Injective.sumElim ?_ (fun a b h => by simpa using h) ?_
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [scE]
  · intro a b h
    fin_cases a <;> simp_all [scE]

theorem ιEA_inj : Function.Injective (ιEA Et Ea E5 Ev) := by
  refine Function.Injective.sumElim ?_ (fun a b h => by simpa using h) ?_
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [scE]
  · intro a b h
    fin_cases a <;> simp_all [scE]

theorem ιE5_inj : Function.Injective (ιE5 Et Ea E5 Ev) := by
  refine Function.Injective.sumElim ?_ (fun a b h => by simpa using h) ?_
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [scE]
  · intro a b h
    fin_cases a <;> simp_all [scE]

theorem ιEV_inj : Function.Injective (ιEV Et Ea E5 Ev) := by
  refine Function.Injective.sumElim ?_ (fun a b h => by simpa using h) ?_
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [scE]
  · intro a b h
    fin_cases a <;> simp_all [scE]

theorem scE_inj : Function.Injective (scE Et Ea E5 Ev) := fun a b h => by simpa [scE] using h

end Layout

section SimpLemmas

variable {Et Ea E5 Ev : Type}

@[simp] theorem scE_ne_inl (i : Fin 6) (j : Fin 5) :
    scE Et Ea E5 Ev i ≠ (Sum.inl j : KLoc (Fin 5) (EE Et Ea E5 Ev)) := by
  simp [scE]

@[simp] theorem inl_ne_scE (i : Fin 6) (j : Fin 5) :
    (Sum.inl j : KLoc (Fin 5) (EE Et Ea E5 Ev)) ≠ scE Et Ea E5 Ev i := by
  simp [scE]

@[simp] theorem scE_eq_iff (i j : Fin 6) : scE Et Ea E5 Ev i = scE Et Ea E5 Ev j ↔ i = j :=
  (scE_inj Et Ea E5 Ev).eq_iff

end SimpLemmas

section Lenses

variable (Rt Ra R5 Rv : Type)

def lET : Lens (RE Rt Ra R5 Rv) Rt := Lens.fst _ _

def lEA : Lens (RE Rt Ra R5 Rv) Ra := (Lens.snd _ _).comp (Lens.fst _ _)

def lE5 : Lens (RE Rt Ra R5 Rv) R5 := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))

def lEV : Lens (RE Rt Ra R5 Rv) Rv :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))

def lEW : Lens (RE Rt Ra R5 Rv) (Option Sym) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))

end Lenses

/-! ## The level-E program -/

/-- Push a `mark` floor. -/
def pushMk {K σ : Type} (k : K) : Prog K (fun _ => Sym) σ := .push k fun _ => Sym.mark

/-- Pop the top symbol. -/
def popMk {K σ : Type} (k : K) : Prog K (fun _ => Sym) σ := .pop k fun v _ => v

/-- Floors on the six counter stacks, then the first test. -/
def initE {K σ : Type} (sc : Fin 6 → K) (test : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq (pushMk (sc 0)) (.seq (pushMk (sc 1)) (.seq (pushMk (sc 2)) (.seq (pushMk (sc 3))
    (.seq (pushMk (sc 4)) (.seq (pushMk (sc 5)) test)))))

/-- Drop `o` with its floor, pop the five other floors. -/
def finE {K σ : Type} (sc : Fin 6 → K) (dropO : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq dropO (.seq (popMk (sc 1)) (.seq (popMk (sc 2)) (.seq (popMk (sc 3))
    (.seq (popMk (sc 4)) (popMk (sc 5))))))

/-- **The level-E program**: `initE`; `while cont: args; Proposition A.7; advance; test`; `finE`. -/
def progE {K σ : Type} (sc : Fin 6 → K) (test args c5 adv dropO : Prog K (fun _ => Sym) σ)
    (cont : σ → Bool) : Prog K (fun _ => Sym) σ :=
  .seq (.seq (initE sc test) (.loop cont (.seq args (.seq c5 (.seq adv test))))) (finE sc dropO)

theorem closed_progE {K σ : Type} {sc : Fin 6 → K} {test args c5 adv dropO : Prog K (fun _ => Sym) σ}
    {cont : σ → Bool} (ht : test.Closed) (ha : args.Closed) (h5 : c5.Closed) (hv : adv.Closed)
    (hd : dropO.Closed) : (progE sc test args c5 adv dropO cont).Closed :=
  ⟨⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, ht⟩, ha, h5, hv, ht⟩,
    ⟨hd, trivial, trivial, trivial, trivial, trivial⟩⟩

/-! ## `Runs` helpers -/

section RunsHelpers

variable {K σ : Type} [DecidableEq K]

/-- A `mark` push onto a stack whose content is `S k`. -/
theorem runs_pushMk_upd (k : K) (S T : K → List Sym) (h : T k = S k) :
    Runs (pushMk (σ := σ) k) T (Function.update T k (Sym.mark :: S k)) (fun _ => True) 1 :=
  runs_congr (runs_pushMark k T) (by rw [h]) le_rfl

/-- A pop of a `mark` floor above `S k`. -/
theorem runs_popMk_upd (k : K) (S T : K → List Sym) (h : T k = Sym.mark :: S k) :
    Runs (popMk (σ := σ) k) T (Function.update T k (S k)) (fun _ => True) 1 :=
  runs_congr (runs_popDrop k T) (by rw [h]; rfl) le_rfl

/-- The state with `mark` floors on the six counter stacks. -/
def mk6 (sc : Fin 6 → K) (S : K → List Sym) : K → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S (sc 0) (Sym.mark :: S (sc 0))) (sc 1) (Sym.mark :: S (sc 1)))
    (sc 2) (Sym.mark :: S (sc 2))) (sc 3) (Sym.mark :: S (sc 3))) (sc 4) (Sym.mark :: S (sc 4)))
    (sc 5) (Sym.mark :: S (sc 5))

theorem runs_initE {sc : Fin 6 → K} (hsc : Function.Injective sc) {test : Prog K (fun _ => Sym) σ}
    {S : K → List Sym} {Q : σ → Prop} {Tt : ℕ} (ht : Runs test (mk6 sc S) (mk6 sc S) Q Tt) :
    Runs (initE sc test) S (mk6 sc S) Q (1 + (1 + (1 + (1 + (1 + (1 + Tt)))))) := by
  unfold initE
  refine runs_seq (runs_pushMk_upd (sc 0) S S rfl) (runs_seq (runs_pushMk_upd (sc 1) S _ ?_)
    (runs_seq (runs_pushMk_upd (sc 2) S _ ?_) (runs_seq (runs_pushMk_upd (sc 3) S _ ?_)
    (runs_seq (runs_pushMk_upd (sc 4) S _ ?_) (runs_seq (runs_pushMk_upd (sc 5) S _ ?_) ht)))))
  all_goals simp [hsc.eq_iff]

/-- `callInj` of a kernel that updates five stacks. -/
theorem runs_callInj_upd5 {L R : Type} [DecidableEq L] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (x0 x1 x2 x3 x4 : L) (v0 v1 v2 v3 v4 : List Sym)
    (h : Runs P (B ∘ ι) (Function.update (Function.update (Function.update (Function.update
      (Function.update (B ∘ ι) x0 v0) x1 v1) x2 v2) x3 v3) x4 v4) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update (Function.update (Function.update
      (Function.update B (ι x0) v0) (ι x1) v1) (ι x2) v2) (ι x3) v3) (ι x4) v4)
      (fun _ => True) T :=
  runs_callInj hι l (by
      rw [Function.update_comp_eq_of_injective _ hι x4 v4,
        Function.update_comp_eq_of_injective _ hι x3 v3,
        Function.update_comp_eq_of_injective _ hι x2 v2,
        Function.update_comp_eq_of_injective _ hι x1 v1,
        Function.update_comp_eq_of_injective B hι x0 v0]
      exact h)
    (fun k hk => by
      rw [Function.update_of_ne (Ne.symm (hk x4)), Function.update_of_ne (Ne.symm (hk x3)),
        Function.update_of_ne (Ne.symm (hk x2)), Function.update_of_ne (Ne.symm (hk x1)),
        Function.update_of_ne (Ne.symm (hk x0))])

/-- `callInj` of a kernel that updates six stacks. -/
theorem runs_callInj_upd6 {L R : Type} [DecidableEq L] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {Q : R → Prop}
    {T : ℕ} (B : K → List Sym) (x0 x1 x2 x3 x4 x5 : L) (v0 v1 v2 v3 v4 v5 : List Sym)
    (h : Runs P (B ∘ ι) (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (B ∘ ι) x0 v0) x1 v1) x2 v2) x3 v3) x4 v4) x5 v5) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update B (ι x0) v0) (ι x1) v1) (ι x2) v2) (ι x3) v3) (ι x4) v4)
      (ι x5) v5) (fun _ => True) T :=
  runs_callInj hι l (by
      rw [Function.update_comp_eq_of_injective _ hι x5 v5,
        Function.update_comp_eq_of_injective _ hι x4 v4,
        Function.update_comp_eq_of_injective _ hι x3 v3,
        Function.update_comp_eq_of_injective _ hι x2 v2,
        Function.update_comp_eq_of_injective _ hι x1 v1,
        Function.update_comp_eq_of_injective B hι x0 v0]
      exact h)
    (fun k hk => by
      rw [Function.update_of_ne (Ne.symm (hk x5)), Function.update_of_ne (Ne.symm (hk x4)),
        Function.update_of_ne (Ne.symm (hk x3)), Function.update_of_ne (Ne.symm (hk x2)),
        Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))])

end RunsHelpers

/-! ## The loop states -/

section States

variable {Et Ea E5 Ev : Type} [DecidableEq Et] [DecidableEq Ea] [DecidableEq E5] [DecidableEq Ev]

/-- The loop state: array `arr`, offset stack `oS`, five floored Proposition A.7 counter stacks. -/
def stE (S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym) (arr oS : List Sym) :
    KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym :=
  Function.update (Function.update (mk6 (scE Et Ea E5 Ev) S) (.inl 0) arr) (scE Et Ea E5 Ev 0) oS

theorem stE_inl {S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym} {arr oS : List Sym} {i : Fin 5}
    (hi : i ≠ 0) : stE S arr oS (.inl i) = S (.inl i) := by
  simp [stE, mk6, scE, hi]

theorem stE_arr {S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym} {arr oS : List Sym} :
    stE S arr oS (.inl 0) = arr := by
  simp [stE, scE]

theorem stE_o {S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym} {arr oS : List Sym} :
    stE S arr oS (scE Et Ea E5 Ev 0) = oS :=
  Function.update_self _ _ _

theorem stE_sc {S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym} {arr oS : List Sym} {i : Fin 6}
    (hi : i ≠ 0) : stE S arr oS (scE Et Ea E5 Ev i) = Sym.mark :: S (scE Et Ea E5 Ev i) := by
  fin_cases i <;> simp_all [stE, mk6, scE]

/-- The floored initial state is the loop state at offset `0`. -/
theorem stE_init (S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym) :
    stE S (S (.inl 0)) (Sym.mark :: S (scE Et Ea E5 Ev 0)) = mk6 (scE Et Ea E5 Ev) S := by
  funext k
  rcases k with i | x | x | x | x | i
  · fin_cases i <;> simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · fin_cases i <;> simp [stE, mk6, scE]

/-- One loop iteration (args pushed, array replaced, offset advanced, args popped) gives the next
loop state. -/
theorem stE_body (S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym)
    (arr arr' oS oS' a1 a2 a3 a4 a5 : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (stE S arr oS)
      (scE Et Ea E5 Ev 1) a1) (scE Et Ea E5 Ev 2) a2) (scE Et Ea E5 Ev 3) a3)
      (scE Et Ea E5 Ev 4) a4) (scE Et Ea E5 Ev 5) a5) (.inl 0) arr')
      (scE Et Ea E5 Ev 0) oS') (scE Et Ea E5 Ev 1) (Sym.mark :: S (scE Et Ea E5 Ev 1)))
      (scE Et Ea E5 Ev 2) (Sym.mark :: S (scE Et Ea E5 Ev 2)))
      (scE Et Ea E5 Ev 3) (Sym.mark :: S (scE Et Ea E5 Ev 3)))
      (scE Et Ea E5 Ev 4) (Sym.mark :: S (scE Et Ea E5 Ev 4)))
      (scE Et Ea E5 Ev 5) (Sym.mark :: S (scE Et Ea E5 Ev 5)) = stE S arr' oS' := by
  funext k
  rcases k with i | x | x | x | x | i
  · fin_cases i <;> simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · fin_cases i <;> simp [stE, mk6, scE]

/-- The cleanup (drop `o` and its floor, pop five floors) leaves only the new array. -/
theorem stE_fin (S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym) (arr oS : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (stE S arr oS) (scE Et Ea E5 Ev 0) (S (scE Et Ea E5 Ev 0)))
      (scE Et Ea E5 Ev 1) (S (scE Et Ea E5 Ev 1))) (scE Et Ea E5 Ev 2) (S (scE Et Ea E5 Ev 2)))
      (scE Et Ea E5 Ev 3) (S (scE Et Ea E5 Ev 3))) (scE Et Ea E5 Ev 4) (S (scE Et Ea E5 Ev 4)))
      (scE Et Ea E5 Ev 5) (S (scE Et Ea E5 Ev 5)) = Function.update S (.inl 0) arr := by
  funext k
  rcases k with i | x | x | x | x | i
  · fin_cases i <;> simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · simp [stE, mk6, scE]
  · fin_cases i <;> simp [stE, mk6, scE]

end States

/-! ## Cost bounds -/

/-- One loop iteration costs at most `D·x` (`x = (m^τ)^j ≥ 1`). -/
theorem body_cost_le {Ca Cv Ct C5 P e V Ta Tv Tt : ℕ} {x : ℝ} (hx : 1 ≤ x) (hTa : Ta ≤ Ca * P)
    (hTv : Tv ≤ Cv * P) (hTt : Tt ≤ Ct * (e + 1) ^ 3) (hP : (e + 1) ^ 3 ≤ P) :
    ((Ta + (C5 * (⌈(V : ℝ) * x⌉₊ + 1) + (Tv + Tt)) + 1 : ℕ) : ℝ) ≤
      ((((Ca + Cv + Ct) * P + 2 * C5 + 1 : ℕ) : ℝ) + (C5 : ℝ) * V) * x := by
  have hc : (⌈(V : ℝ) * x⌉₊ : ℝ) ≤ V * x + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) (by linarith))).le
  have hTt' : Tt ≤ Ct * P := le_trans hTt (Nat.mul_le_mul_left _ hP)
  have h1 : (Ta : ℝ) ≤ Ca * P := by exact_mod_cast hTa
  have h2 : (Tv : ℝ) ≤ Cv * P := by exact_mod_cast hTv
  have h3 : (Tt : ℝ) ≤ Ct * P := by exact_mod_cast hTt'
  have hK : (0 : ℝ) ≤ ((Ca + Cv + Ct) * P + 2 * C5 + 1 : ℕ) := Nat.cast_nonneg _
  have hC5 : (0 : ℝ) ≤ C5 := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left hc hC5
  have h5 := mul_le_mul_of_nonneg_left hx hK
  push_cast at hK h5 ⊢
  nlinarith

/-- The potential bookkeeping of one iteration. -/
theorem W_step {D Φ' x : ℝ} {Tb : ℕ} (hD : 0 ≤ D) (hΦ' : 0 ≤ Φ')
    (hb : ((Tb + 1 : ℕ) : ℝ) ≤ D * x) :
    Tb + 1 + (⌈D * Φ'⌉₊ + 1) ≤ ⌈D * (x + Φ')⌉₊ + 1 := by
  have h2 : ⌈D * Φ' + ((Tb + 1 : ℕ) : ℝ)⌉₊ = ⌈D * Φ'⌉₊ + (Tb + 1) :=
    Nat.ceil_add_natCast (mul_nonneg hD hΦ') _
  have h3 : ⌈D * Φ' + ((Tb + 1 : ℕ) : ℝ)⌉₊ ≤ ⌈D * (x + Φ')⌉₊ :=
    Nat.ceil_mono (by nlinarith)
  omega

/-- The total cost of level E fits `C·(⌈V·E⌉₊ + 1)` (`E = e^τ ≥ 1`). -/
theorem total_le {Ct C5 Ca Cv P V e lb Tt M : ℕ} {E D Φ : ℝ} (hM : 1 ≤ M) (hV1 : 1 ≤ V)
    (hP : P ≤ 48 * V) (heV : e ≤ V) (hlb : lb ≤ e) (hE1 : 1 ≤ E)
    (hD : D = (((Ca + Cv + Ct) * P + 2 * C5 + 1 : ℕ) : ℝ) + (C5 : ℝ) * V)
    (hΦ0 : 0 ≤ Φ) (hΦ : Φ ≤ 2 * ((M : ℝ) - 1) * E)
    (hTt : Tt ≤ Ct * (e + 1) ^ 3) (heP : (e + 1) ^ 3 ≤ P) :
    1 + (1 + (1 + (1 + (1 + (1 + Tt))))) + (⌈D * Φ⌉₊ + 1) +
        (2 * lb + 2 + (1 + (1 + (1 + (1 + 1))))) ≤
      (2 * (M - 1) * (48 * (Ca + Cv + Ct) + 3 * C5 + 1) + 48 * Ct + 16) *
        (⌈(V : ℝ) * E⌉₊ + 1) := by
  have hVX : V ≤ ⌈(V : ℝ) * E⌉₊ := by
    have h : (V : ℝ) ≤ (V : ℝ) * E := le_mul_of_one_le_right (Nat.cast_nonneg _) hE1
    exact_mod_cast h.trans (Nat.le_ceil _)
  have hV1' : (1 : ℝ) ≤ V := by exact_mod_cast hV1
  have hP' : (P : ℝ) ≤ 48 * V := by exact_mod_cast hP
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hDle : D ≤ ((48 * (Ca + Cv + Ct) + 3 * C5 + 1 : ℕ) : ℝ) * V := by
    rw [hD]
    push_cast
    have hCa : (0 : ℝ) ≤ Ca := Nat.cast_nonneg _
    have hCv : (0 : ℝ) ≤ Cv := Nat.cast_nonneg _
    have hCt : (0 : ℝ) ≤ Ct := Nat.cast_nonneg _
    have hC5 : (0 : ℝ) ≤ C5 := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hP' (add_nonneg (add_nonneg hCa hCv) hCt)]
  have hE0 : (0 : ℝ) ≤ E := by linarith
  have hceil : ⌈D * Φ⌉₊ ≤ 2 * (M - 1) * (48 * (Ca + Cv + Ct) + 3 * C5 + 1) *
      ⌈(V : ℝ) * E⌉₊ := by
    apply Nat.ceil_le.2
    push_cast [Nat.cast_sub hM]
    have hK0 : (0 : ℝ) ≤ 2 * ((M : ℝ) - 1) * (48 * ((Ca : ℝ) + Cv + Ct) + 3 * C5 + 1) := by
      have : (0 : ℝ) ≤ (M : ℝ) - 1 := by linarith
      positivity
    have hDle' : D ≤ (48 * ((Ca : ℝ) + Cv + Ct) + 3 * C5 + 1) * V := by
      have := hDle; push_cast at this; exact this
    calc D * Φ ≤ ((48 * ((Ca : ℝ) + Cv + Ct) + 3 * C5 + 1) * V) * (2 * ((M : ℝ) - 1) * E) :=
          mul_le_mul hDle' hΦ hΦ0 (by positivity)
      _ = 2 * ((M : ℝ) - 1) * (48 * ((Ca : ℝ) + Cv + Ct) + 3 * C5 + 1) * ((V : ℝ) * E) := by
          ring
      _ ≤ 2 * ((M : ℝ) - 1) * (48 * ((Ca : ℝ) + Cv + Ct) + 3 * C5 + 1) * ⌈(V : ℝ) * E⌉₊ :=
          mul_le_mul_of_nonneg_left (Nat.le_ceil _) hK0
  have hTt' : Tt ≤ 48 * Ct * ⌈(V : ℝ) * E⌉₊ := by
    have h1 : Tt ≤ Ct * P := le_trans hTt (Nat.mul_le_mul_left _ heP)
    have h2 : Ct * P ≤ Ct * (48 * V) := Nat.mul_le_mul_left _ hP
    have h3 : Ct * (48 * V) ≤ Ct * (48 * ⌈(V : ℝ) * E⌉₊) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hVX)
    calc Tt ≤ Ct * (48 * ⌈(V : ℝ) * E⌉₊) := h1.trans (h2.trans h3)
      _ = 48 * Ct * ⌈(V : ℝ) * E⌉₊ := by ring
  have e1 : (2 * (M - 1) * (48 * (Ca + Cv + Ct) + 3 * C5 + 1) + 48 * Ct + 16) *
      (⌈(V : ℝ) * E⌉₊ + 1) = 2 * (M - 1) * (48 * (Ca + Cv + Ct) + 3 * C5 + 1) *
      ⌈(V : ℝ) * E⌉₊ + 48 * Ct * ⌈(V : ℝ) * E⌉₊ + 16 * ⌈(V : ℝ) * E⌉₊ +
      (2 * (M - 1) * (48 * (Ca + Cv + Ct) + 3 * C5 + 1) + 48 * Ct + 16) := by ring
  rw [e1]
  omega

/-- The cleanup `finE` from a loop state with offset `n`. -/
theorem runs_finE_stE {Et Ea E5 Ev σ : Type} [DecidableEq Et] [DecidableEq Ea] [DecidableEq E5]
    [DecidableEq Ev] (l : Lens σ (Option Sym)) (S : KLoc (Fin 5) (EE Et Ea E5 Ev) → List Sym)
    (arr : List Sym) (n : ℕ) :
    Runs (finE (scE Et Ea E5 Ev) ((SubNLogN.Machine.K1.dropBits (scE Et Ea E5 Ev 0)).liftRegs l))
      (stE S arr (natSyms n ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
      (Function.update S (.inl 0) arr) (fun _ => True)
      (2 * bitLen n + 2 + (1 + (1 + (1 + (1 + 1))))) := by
  unfold finE
  refine runs_congr (runs_seq (SubNLogN.Machine.K1.runs_wk_dropBits l (scE Et Ea E5 Ev 0)
      (Computability.encodeNat n) Sym.mark (S (scE Et Ea E5 Ev 0)) _ rfl stE_o)
    (runs_seq (runs_popMk_upd (scE Et Ea E5 Ev 1) S _ ?_)
    (runs_seq (runs_popMk_upd (scE Et Ea E5 Ev 2) S _ ?_)
    (runs_seq (runs_popMk_upd (scE Et Ea E5 Ev 3) S _ ?_)
    (runs_seq (runs_popMk_upd (scE Et Ea E5 Ev 4) S _ ?_)
      (runs_popMk_upd (scE Et Ea E5 Ev 5) S _ ?_)))))) (stE_fin S arr _) le_rfl
  all_goals simp [stE_sc]

end AppC.C6Aux

open AppC.C6Aux in
/-- **Lemma A.8 level E** (Lemma A.8 (`lem:transfer12`), base-`m` piece loop): for
`q ≥ 2`, Proposition A.7 (`C5InterchangeStmt q τ`) and the three counter leaves of the greedy piece loop
(`C6PcTestStmt q`, `C6PcArgsStmt q`, `C6PcAdvStmt q`) give `C6PiecesStmt q τ`. -/
theorem c6Pieces_of_parts {q : ℕ} {τ : ℝ} (hq : 2 ≤ q) (h5 : C5InterchangeStmt q τ)
    (hT : C6PcTestStmt q) (hA : C6PcArgsStmt q) (hV : C6PcAdvStmt q) : C6PiecesStmt q τ := by
  intro hτ
  have hτ0 : 0 < τ := tau_pos hτ
  have hrr2 : (2 : ℝ) ≤ (tripleM 100 : ℝ) ^ τ := two_le_mrpow hτ
  have hr0 : (0 : ℝ) ≤ (tripleM 100 : ℝ) ^ τ := by linarith
  obtain ⟨C5, h5⟩ := h5 hτ
  obtain ⟨Ct, hT⟩ := hT
  obtain ⟨Ca, hA⟩ := hA
  obtain ⟨Cv, hV⟩ := hV
  obtain ⟨Et, _, _, Rt, Pt, hRt1, hRt2, hPt, obs, hsT⟩ := hT ()
  obtain ⟨Ea, _, _, Ra, Pa, hRa1, hRa2, hPa, hsA⟩ := hA ()
  obtain ⟨E5, _, _, R5, P5, hR51, hR52, hP5, hs5⟩ := h5 ()
  obtain ⟨Ev, _, _, Rv, Pv, hRv1, hRv2, hPv, hsV⟩ := hV ()
  have := hRt1; have := hRt2; have := hRa1; have := hRa2; have := hR51; have := hR52
  have := hRv1; have := hRv2
  refine ⟨2 * (tripleM 100 - 1) * (48 * (Ca + Cv + Ct) + 3 * C5 + 1) + 48 * Ct + 16,
    fun _ => ⟨EE Et Ea E5 Ev, inferInstance, inferInstance, RE Rt Ra R5 Rv,
    progE (scE Et Ea E5 Ev) (callInj (ιET Et Ea E5 Ev) (lET Rt Ra R5 Rv) Pt)
      (callInj (ιEA Et Ea E5 Ev) (lEA Rt Ra R5 Rv) Pa)
      (callInj (ιE5 Et Ea E5 Ev) (lE5 Rt Ra R5 Rv) P5)
      (callInj (ιEV Et Ea E5 Ev) (lEV Rt Ra R5 Rv) Pv)
      ((SubNLogN.Machine.K1.dropBits (scE Et Ea E5 Ev 0)).liftRegs (lEW Rt Ra R5 Rv))
      (fun x => obs x.1),
    inferInstance, inferInstance,
    closed_progE (closed_callInj _ _ hPt) (closed_callInj _ _ hPa) (closed_callInj _ _ hP5)
      (closed_callInj _ _ hPv) (SubNLogN.Machine.K1.Rot.closed_dropBits_lift _ _), ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he hA1 hG hB hlen hw hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2
    hS3 hS4
  -- basic facts
  have ht := c6T_lt hq he
  have hq0 : 0 < q := by omega
  have hVol : vol v = v.length * (w + 1) := vol_eq_of_width hw
  have hlenV : v.length ≤ vol v := by
    rw [hVol]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos w)
  have hlen2 : 2 ^ e * G * B ≤ v.length := by rw [hlen]; exact len_ge hq he hA1
  have hGB : 2 ^ e ≤ 2 ^ e * G * B := by
    calc 2 ^ e = 2 ^ e * 1 * 1 := by ring
      _ ≤ 2 ^ e * G * B := by gcongr
  have heV : e ≤ vol v := by
    have h1 : e < 2 ^ e := Nat.lt_two_pow_self
    omega
  have hV1 : 1 ≤ vol v := by omega
  have hPV : (e + bitLen G + bitLen B + 1) ^ 3 ≤ 48 * vol v :=
    (cube_le hG hB).trans (by omega)
  have heP : (e + 1) ^ 3 ≤ (e + bitLen G + bitLen B + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (((Ca + Cv + Ct) * (e + bitLen G + bitLen B + 1) ^ 3 + 2 * C5 + 1 :
      ℕ) : ℝ) + (C5 : ℝ) * (vol v : ℝ) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  -- the arrays after the pieces up to offset `o`
  have hrange : ∀ o, o ≤ e - c6T q e → ∀ y < v.length,
      c6SP q (e - c6T q e) G B o y < v.length := by
    intro o ho y hy
    rw [hlen] at hy ⊢
    exact c6SP_lt ho hy
  have hwo : ∀ o, o ≤ e - c6T q e →
      ∀ p ∈ permByInv (c6SP q (e - c6T q e) G B o) v, p.length = w :=
    fun o ho p hp => hw p (mem_permByInv (hrange o ho) hp)
  have hvolo : ∀ o, o ≤ e - c6T q e →
      vol (permByInv (c6SP q (e - c6T q e) G B o) v) = vol v := by
    intro o ho
    rw [vol_eq_of_width (hwo o ho), vol_eq_of_width hw, length_permByInv]
  -- the loop test
  have htest : ∀ (o : ℕ) (arr : List Sym), o ≤ e →
      Runs (callInj (ιET Et Ea E5 Ev) (lET Rt Ra R5 Rv) Pt)
        (stE S arr (natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
        (stE S arr (natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
        (fun x => obs x.1 = decide (o < e - c6T q e)) (Ct * (e + 1) ^ 3) := by
    intro o arr ho
    exact runs_callInj_reg (ιET_inj Et Ea E5 Ev) (lET Rt Ra R5 Rv)
      (hsT e o r1 (Sym.mark :: S (scE Et Ea E5 Ev 0)) _ he ho hr1 (termOK_mark _)
        (by show stE _ _ _ (.inl 1) = _; rw [stE_inl (by decide)]; exact hS1)
        (by show stE _ _ _ (scE Et Ea E5 Ev 0) = _; exact stE_o))
      (fun _ _ => rfl)
  -- one loop iteration
  have hbody : ∀ o, o < e - c6T q e →
      Runs (.seq (callInj (ιEA Et Ea E5 Ev) (lEA Rt Ra R5 Rv) Pa)
        (.seq (callInj (ιE5 Et Ea E5 Ev) (lE5 Rt Ra R5 Rv) P5)
          (.seq (callInj (ιEV Et Ea E5 Ev) (lEV Rt Ra R5 Rv) Pv)
            (callInj (ιET Et Ea E5 Ev) (lET Rt Ra R5 Rv) Pt))))
        (stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B o) v) ++ rest)
          (natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
        (stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B (o + c6PL q e o)) v) ++ rest)
          (natSyms (o + c6PL q e o) ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
        (fun x => obs x.1 = decide (o + c6PL q e o < e - c6T q e))
        (Ca * (e + bitLen G + bitLen B + 1) ^ 3 +
          (C5 * (⌈(vol v : ℝ) * ((tripleM 100 ^ c6PJ q e o : ℕ) : ℝ) ^ τ⌉₊ + 1) +
            (Cv * (e + bitLen G + bitLen B + 1) ^ 3 + Ct * (e + 1) ^ 3))) := by
    intro o ho
    have hL := c6PL_le ho
    have hL' : tripleM 100 ^ c6PJ q e o ≤ e - c6T q e - o := hL
    have hoℓ : o ≤ e - c6T q e := ho.le
    -- (1) push the Proposition A.7 counters
    have hAk := hsA e G B o r1 r2 r3 (Sym.mark :: S (scE Et Ea E5 Ev 0))
      (Sym.mark :: S (scE Et Ea E5 Ev 1)) (Sym.mark :: S (scE Et Ea E5 Ev 2))
      (Sym.mark :: S (scE Et Ea E5 Ev 3)) (Sym.mark :: S (scE Et Ea E5 Ev 4))
      (Sym.mark :: S (scE Et Ea E5 Ev 5))
      (stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B o) v) ++ rest)
        (natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0)) ∘ ιEA Et Ea E5 Ev)
      he hG hB ho hr1 hr2 hr3 (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (termOK_mark _) (termOK_mark _)
      (by show stE _ _ _ (.inl 1) = _; rw [stE_inl (by decide)]; exact hS1)
      (by show stE _ _ _ (.inl 2) = _; rw [stE_inl (by decide)]; exact hS2)
      (by show stE _ _ _ (.inl 3) = _; rw [stE_inl (by decide)]; exact hS3)
      (by show stE _ _ _ (scE Et Ea E5 Ev 0) = _; exact stE_o)
      (by show stE _ _ _ (scE Et Ea E5 Ev 1) = _; exact stE_sc (by decide))
      (by show stE _ _ _ (scE Et Ea E5 Ev 2) = _; exact stE_sc (by decide))
      (by show stE _ _ _ (scE Et Ea E5 Ev 3) = _; exact stE_sc (by decide))
      (by show stE _ _ _ (scE Et Ea E5 Ev 4) = _; exact stE_sc (by decide))
      (by show stE _ _ _ (scE Et Ea E5 Ev 5) = _; exact stE_sc (by decide))
    obtain ⟨SA, hSA, hAr⟩ : ∃ SA, SA = Function.update (Function.update (Function.update
        (Function.update (Function.update
        (stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B o) v) ++ rest)
          (natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
        (scE Et Ea E5 Ev 1) (natSyms (c6PJ q e o) ++ Sym.mark :: S (scE Et Ea E5 Ev 1)))
        (scE Et Ea E5 Ev 2) (natSyms (c6Rp q e) ++ Sym.mark :: S (scE Et Ea E5 Ev 2)))
        (scE Et Ea E5 Ev 3) (natSyms (q ^ o) ++ Sym.mark :: S (scE Et Ea E5 Ev 3)))
        (scE Et Ea E5 Ev 4) (natSyms (c6PG q e G o) ++ Sym.mark :: S (scE Et Ea E5 Ev 4)))
        (scE Et Ea E5 Ev 5) (natSyms (c6PB q e B o) ++ Sym.mark :: S (scE Et Ea E5 Ev 5)) ∧
        Runs (callInj (ιEA Et Ea E5 Ev) (lEA Rt Ra R5 Rv) Pa)
          (stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B o) v) ++ rest)
            (natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0))) SA (fun _ => True)
          (Ca * (e + bitLen G + bitLen B + 1) ^ 3) :=
      ⟨_, rfl, runs_callInj_upd5 (ιEA_inj Et Ea E5 Ev) (lEA Rt Ra R5 Rv) _ (.inl 4) (.inl 5)
        (.inl 6) (.inl 7) (.inl 8) _ _ _ _ _ hAk⟩
    have hSA0 : SA (.inl 0) = arrSyms (permByInv (c6SP q (e - c6T q e) G B o) v) ++ rest := by
      rw [hSA]; simp [stE_arr]
    have hSAo : SA (scE Et Ea E5 Ev 0) = natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0) := by
      rw [hSA]; simp [stE_o]
    have hSA1 : SA (scE Et Ea E5 Ev 1) =
        natSyms (c6PJ q e o) ++ Sym.mark :: S (scE Et Ea E5 Ev 1) := by rw [hSA]; simp
    have hSA2 : SA (scE Et Ea E5 Ev 2) =
        natSyms (c6Rp q e) ++ Sym.mark :: S (scE Et Ea E5 Ev 2) := by rw [hSA]; simp
    have hSA3 : SA (scE Et Ea E5 Ev 3) =
        natSyms (q ^ o) ++ Sym.mark :: S (scE Et Ea E5 Ev 3) := by rw [hSA]; simp
    have hSA4 : SA (scE Et Ea E5 Ev 4) =
        natSyms (c6PG q e G o) ++ Sym.mark :: S (scE Et Ea E5 Ev 4) := by rw [hSA]; simp
    have hSA5 : SA (scE Et Ea E5 Ev 5) =
        natSyms (c6PB q e B o) ++ Sym.mark :: S (scE Et Ea E5 Ev 5) := by rw [hSA]; simp
    -- (2) the Proposition A.7 piece
    have hsplit : q ^ (e - c6T q e) = q ^ o * q ^ (tripleM 100 ^ c6PJ q e o) *
        q ^ (e - c6T q e - o - tripleM 100 ^ c6PJ q e o) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have hlen5 : (permByInv (c6SP q (e - c6T q e) G B o) v).length = A * c6Rp q e * q ^ o *
        q ^ (tripleM 100 ^ c6PJ q e o) * c6PG q e G o * q ^ (tripleM 100 ^ c6PJ q e o) *
        c6PB q e B o := by
      rw [length_permByInv, hlen]; unfold c6PG c6PB c6PL; rw [hsplit]; ring
    have hRp1 : 1 ≤ c6Rp q e := (c6R_pos hq).trans_le (c6R_le_c6Rp q e)
    have hG' : 1 ≤ c6PG q e G o := Nat.mul_pos (Nat.mul_pos (pow_pos hq0 _) hG) (pow_pos hq0 _)
    have hB' : 1 ≤ c6PB q e B o := Nat.mul_pos (pow_pos hq0 _) hB
    have h5k := hs5 (c6PJ q e o) A (c6Rp q e) (q ^ o) (c6PG q e G o) (c6PB q e B o) w
      (permByInv (c6SP q (e - c6T q e) G B o) v) rest
      (Sym.mark :: S (scE Et Ea E5 Ev 1)) (Sym.mark :: S (scE Et Ea E5 Ev 2))
      (Sym.mark :: S (scE Et Ea E5 Ev 3)) (Sym.mark :: S (scE Et Ea E5 Ev 4))
      (Sym.mark :: S (scE Et Ea E5 Ev 5)) (SA ∘ ιE5 Et Ea E5 Ev)
      hA1 hRp1 (Nat.one_le_pow _ _ hq0) hG' hB' (c6Wj_dvd ho) hlen5 (hwo o hoℓ) hrest
      (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (by show SA (.inl 0) = _; exact hSA0)
      (by show SA (scE Et Ea E5 Ev 1) = _; exact hSA1)
      (by show SA (scE Et Ea E5 Ev 2) = _; exact hSA2)
      (by show SA (scE Et Ea E5 Ev 3) = _; exact hSA3)
      (by show SA (scE Et Ea E5 Ev 4) = _; exact hSA4)
      (by show SA (scE Et Ea E5 Ev 5) = _; exact hSA5)
    rw [hvolo o hoℓ] at h5k
    obtain ⟨S5, hS5, h5r⟩ : ∃ S5, S5 = Function.update SA (.inl 0)
        (arrSyms (permByInv (swapFieldsInv (q ^ (tripleM 100 ^ c6PJ q e o)) (c6PG q e G o)
          (q ^ (tripleM 100 ^ c6PJ q e o)) (c6PB q e B o))
          (permByInv (c6SP q (e - c6T q e) G B o) v)) ++ rest) ∧
        Runs (callInj (ιE5 Et Ea E5 Ev) (lE5 Rt Ra R5 Rv) P5) SA S5 (fun _ => True)
          (C5 * (⌈(vol v : ℝ) * ((tripleM 100 ^ c6PJ q e o : ℕ) : ℝ) ^ τ⌉₊ + 1)) :=
      ⟨_, rfl, runs_callInj_upd1 (ιE5_inj Et Ea E5 Ev) (lE5 Rt Ra R5 Rv) SA (.inl 0) _ h5k⟩
    -- (3) advance the offset, pop the Proposition A.7 counters
    have hS5o : S5 (scE Et Ea E5 Ev 0) = natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0) := by
      rw [hS5, Function.update_of_ne (scE_ne_inl _ _), hSAo]
    have hS5i : ∀ i : Fin 6, S5 (scE Et Ea E5 Ev i) = SA (scE Et Ea E5 Ev i) := by
      intro i; rw [hS5, Function.update_of_ne (scE_ne_inl _ _)]
    have hVk := hsV e G B o (Sym.mark :: S (scE Et Ea E5 Ev 0))
      (Sym.mark :: S (scE Et Ea E5 Ev 1)) (Sym.mark :: S (scE Et Ea E5 Ev 2))
      (Sym.mark :: S (scE Et Ea E5 Ev 3)) (Sym.mark :: S (scE Et Ea E5 Ev 4))
      (Sym.mark :: S (scE Et Ea E5 Ev 5)) (S5 ∘ ιEV Et Ea E5 Ev)
      he hG hB ho (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (termOK_mark _) (termOK_mark _)
      (by show S5 (scE Et Ea E5 Ev 0) = _; exact hS5o)
      (by show S5 (scE Et Ea E5 Ev 1) = _; rw [hS5i]; exact hSA1)
      (by show S5 (scE Et Ea E5 Ev 2) = _; rw [hS5i]; exact hSA2)
      (by show S5 (scE Et Ea E5 Ev 3) = _; rw [hS5i]; exact hSA3)
      (by show S5 (scE Et Ea E5 Ev 4) = _; rw [hS5i]; exact hSA4)
      (by show S5 (scE Et Ea E5 Ev 5) = _; rw [hS5i]; exact hSA5)
    have hVr := runs_callInj_upd6 (ιEV_inj Et Ea E5 Ev) (lEV Rt Ra R5 Rv) S5 (.inl 0) (.inl 1)
      (.inl 2) (.inl 3) (.inl 4) (.inl 5) _ _ _ _ _ _ hVk
    -- (4) the next loop state
    have hrangeF : ∀ y < v.length, swapFieldsInv (q ^ (tripleM 100 ^ c6PJ q e o)) (c6PG q e G o)
        (q ^ (tripleM 100 ^ c6PJ q e o)) (c6PB q e B o) y < v.length := by
      intro y hy
      have e5 := hlen5
      rw [length_permByInv] at e5
      rw [e5] at hy ⊢
      exact swapFieldsInv_lt hy
    have harr : permByInv (swapFieldsInv (q ^ (tripleM 100 ^ c6PJ q e o)) (c6PG q e G o)
        (q ^ (tripleM 100 ^ c6PJ q e o)) (c6PB q e B o))
        (permByInv (c6SP q (e - c6T q e) G B o) v) =
        permByInv (c6SP q (e - c6T q e) G B (o + c6PL q e o)) v := by
      rw [permByInv_comp _ _ _ hrangeF]
      apply permByInv_congr
      intro y _
      exact c6SP_step hq0 hG hB (by omega) y
    have hpost : Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S5 (scE Et Ea E5 Ev 0)
          (natSyms (o + c6PL q e o) ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
        (scE Et Ea E5 Ev 1) (Sym.mark :: S (scE Et Ea E5 Ev 1)))
        (scE Et Ea E5 Ev 2) (Sym.mark :: S (scE Et Ea E5 Ev 2)))
        (scE Et Ea E5 Ev 3) (Sym.mark :: S (scE Et Ea E5 Ev 3)))
        (scE Et Ea E5 Ev 4) (Sym.mark :: S (scE Et Ea E5 Ev 4)))
        (scE Et Ea E5 Ev 5) (Sym.mark :: S (scE Et Ea E5 Ev 5)) =
        stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B (o + c6PL q e o)) v) ++ rest)
          (natSyms (o + c6PL q e o) ++ Sym.mark :: S (scE Et Ea E5 Ev 0)) := by
      rw [hS5, hSA, stE_body, harr]
    have htest' := htest (o + c6PL q e o)
      (arrSyms (permByInv (c6SP q (e - c6T q e) G B (o + c6PL q e o)) v) ++ rest) (by omega)
    exact runs_seq hAr (runs_seq h5r (runs_seq (runs_congr hVr hpost le_rfl) htest'))
  -- the initial state
  have hperm0 : permByInv (c6SP q (e - c6T q e) G B 0) v = v :=
    permByInv_of_id v fun y _ => c6SP_zero hq0 hG hB y
  have hnat0 : natSyms 0 = [] := by simp [natSyms, TMFw.encodeNat_zero]
  have hst0 : stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B 0) v) ++ rest)
      (natSyms 0 ++ Sym.mark :: S (scE Et Ea E5 Ev 0)) = mk6 (scE Et Ea E5 Ev) S := by
    rw [hperm0, ← hS0, hnat0, List.nil_append, stE_init]
  have h0 : Runs (initE (scE Et Ea E5 Ev) (callInj (ιET Et Ea E5 Ev) (lET Rt Ra R5 Rv) Pt)) S
      (stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B 0) v) ++ rest)
        (natSyms 0 ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
      (fun x => obs x.1 = decide (0 < e - c6T q e))
      (1 + (1 + (1 + (1 + (1 + (1 + Ct * (e + 1) ^ 3)))))) := by
    have ht0 := htest 0 (arrSyms (permByInv (c6SP q (e - c6T q e) G B 0) v) ++ rest)
      (Nat.zero_le e)
    rw [hst0] at ht0 ⊢
    exact runs_initE (scE_inj Et Ea E5 Ev) ht0
  -- the loop
  have hloop := RunsIn.seq_while_det (ρ := [])
    (st := fun o => stE S (arrSyms (permByInv (c6SP q (e - c6T q e) G B o) v) ++ rest)
      (natSyms o ++ Sym.mark :: S (scE Et Ea E5 Ev 0)))
    (cont := fun o => decide (o < e - c6T q e))
    (fun o => o + c6PL q e o) (fun o => if o < e - c6T q e then e - c6T q e else o)
    (fun o => e - c6T q e - o)
    (fun o => ⌈D * c6Phi e ((tripleM 100 : ℝ) ^ τ) (e - c6T q e - o)⌉₊ + 1)
    (x₀ := 0) (RunsIn.iff_runs.2 h0)
    (fun o ho => by
      simp only [decide_eq_false_iff_not] at ho
      simp [ho])
    (fun o ho => by
      simp only [decide_eq_true_eq] at ho
      have := c6PL_le ho
      simp only [ho, if_true]
      split_ifs <;> omega)
    (fun o _ => Nat.le_add_left 1 _)
    (fun o ho => by
      simp only [decide_eq_true_eq] at ho
      refine ⟨_, ?_, ?_, RunsIn.iff_runs.2 (hbody o ho)⟩
      · have := c6PL_le ho
        have := c6PL_pos q e o
        omega
      · have hL' : tripleM 100 ^ c6PJ q e o ≤ e - c6T q e - o := c6PL_le ho
        have hj : c6PJ q e o < e := by
          have h1 : c6PJ q e o < 2 ^ c6PJ q e o := Nat.lt_two_pow_self
          have h2 : 2 ^ c6PJ q e o ≤ tripleM 100 ^ c6PJ q e o :=
            Nat.pow_le_pow_left tripleM_two_le _
          omega
        have hsub : e - c6T q e - (o + c6PL q e o) =
            e - c6T q e - o - tripleM 100 ^ c6PJ q e o := by
          show e - c6T q e - (o + tripleM 100 ^ c6PJ q e o) = _
          omega
        show _ + 1 + (⌈D * c6Phi e ((tripleM 100 : ℝ) ^ τ) (e - c6T q e - (o + c6PL q e o))⌉₊ +
          1) ≤ ⌈D * c6Phi e ((tripleM 100 : ℝ) ^ τ) (e - c6T q e - o)⌉₊ + 1
        rw [hsub, c6Phi_step (J := c6PJ q e o) (n := e - c6T q e - o) _ hL' (c6PL_lt q e o) hj]
        apply W_step hD0 (c6Phi_nonneg _ hr0 _)
        have hx : (1 : ℝ) ≤ ((tripleM 100 ^ c6PJ q e o : ℕ) : ℝ) ^ τ :=
          Real.one_le_rpow (by exact_mod_cast Nat.one_le_pow _ _ (by decide)) hτ0.le
        have hb := body_cost_le (Ca := Ca) (Cv := Cv) (Ct := Ct) (C5 := C5)
          (P := (e + bitLen G + bitLen B + 1) ^ 3) (e := e) (V := vol v)
          (Ta := Ca * (e + bitLen G + bitLen B + 1) ^ 3)
          (Tv := Cv * (e + bitLen G + bitLen B + 1) ^ 3) (Tt := Ct * (e + 1) ^ 3) hx le_rfl
          le_rfl le_rfl heP
        rw [← hD] at hb
        exact hb.trans_eq (by rw [natpow_rpow]))
  have hfin0 : (if 0 < e - c6T q e then e - c6T q e else 0) = e - c6T q e := if_pos (by omega)
  have hloop2 := RunsIn.iff_runs.1 hloop
  simp only [hfin0, Nat.sub_zero] at hloop2
  -- the cleanup
  have hfinal := runs_finE_stE (lEW Rt Ra R5 Rv) S
    (arrSyms (permByInv (c6SP q (e - c6T q e) G B (e - c6T q e)) v) ++ rest) (e - c6T q e)
  refine runs_congr (runs_seq hloop2 hfinal) (by rw [c6SP_full]) ?_
  -- the cost
  have hJ := Nat.lt_pow_succ_log_self (by decide : 1 < tripleM 100) (e - c6T q e)
  have hΦ1 := c6Phi_le (e := e) hrr2 hJ
  have hpowJ : tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e) ≤ e :=
    (Nat.pow_log_le_self _ (by omega)).trans (by omega)
  have hrJ : ((tripleM 100 : ℝ) ^ τ) ^ Nat.log (tripleM 100) (e - c6T q e) ≤ (e : ℝ) ^ τ := by
    rw [← natpow_rpow]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hpowJ) hτ0.le
  have hm1 : (0 : ℝ) ≤ 2 * ((tripleM 100 : ℝ) - 1) := by
    have : (2 : ℝ) ≤ tripleM 100 := by exact_mod_cast tripleM_two_le
    linarith
  have hΦ : c6Phi e ((tripleM 100 : ℝ) ^ τ) (e - c6T q e) ≤
      2 * ((tripleM 100 : ℝ) - 1) * (e : ℝ) ^ τ :=
    hΦ1.trans (mul_le_mul_of_nonneg_left hrJ hm1)
  have hE1 : (1 : ℝ) ≤ (e : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ e)) hτ0.le
  have hlb : bitLen (e - c6T q e) ≤ e :=
    (TMFw.W3s.bitLen_le_of_lt Nat.lt_two_pow_self).trans (by omega)
  exact total_le (M := tripleM 100) (by decide) hV1 hPV heV hlb hE1 hD (c6Phi_nonneg _ hr0 _) hΦ
    le_rfl heP

end SubNLogN.Machine
