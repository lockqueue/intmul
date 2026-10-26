/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Leaves
import SubNLogN.Machine.K1.DigitMoveDigitMix
import SubNLogN.Machine.K1.LongRecordBase
import SubNLogN.Machine.Calculus.Basic
import WP.Inst.W3Ok

/-!
# Lemma A.8 (`Machine/AppC/C6BitMove.lean`): the single-bit move, in place

**Theorem** (`c6BitMove_holds`, no hypotheses): `C6BitMoveStmt toRight` for both directions
(`Machine/AppC/C6Leaves.lean`; Lemma A.8 (`lem:transfer12`)). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Program** on `KLoc (Fin 4) (E1 ⊕ Fin 4 ⊕ Fin mc ⊕ Fin ms ⊕ Fin md)`: peek the array stack;
if it is empty (`isRecTop` false, by `BlkTerm rest`) do nothing. Otherwise:
1. on the private counter stacks `N1`, `N2` (a `mark` pushed first, so the rest is `TermOK`) build
   `natSyms (2^u·G)` and `natSyms (2^u·B)` by the proved W3 kernels `copyNat` and `shlVar`;
2. call the proved K1 kernel `k1MoveDigitMix_holds 2 toRight` (source: the array stack,
   destination: a private stack `D` with a `mark` pushed first, counters `N1`, `N2`);
3. move the result back in the original orientation: `rewindTo D T mark`, then `rewindTo T 0 mark`
   (`T` private, `mark` pushed first; each rewind reverses and drops its mark);
4. drop the two counters (`dropNat`) and their marks.
Every private stack ends with its initial content.

**Cost** `C·(vol v + 1)`, `C = C1 + 2·Cc + 2·Cs + 2·Cd + 20`. For a nonempty array
`v.length = N0·2·2^u·G·2^u·B` with `N0, G, B ≥ 1`, so every counter cost (`bitLen G`, `u + bitLen u`,
`bitLen (2^u·G)`, …) is at most `v.length ≤ vol v`; the empty array costs `3`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

namespace AppC.C6BitMoveAux

/-! ## Layout, embeddings and register lenses -/

/-- Private scratch: the K1 kernel's scratch `E1`, the four stacks `D, T, N1, N2`, and the scratch
of the W3 kernels `copyNat`, `shlVar`, `dropNat`. -/
abbrev EB (E1 : Type) (mc ms md : ℕ) : Type := E1 ⊕ (Fin 4 ⊕ (Fin mc ⊕ (Fin ms ⊕ Fin md)))

/-- The composite layout. -/
abbrev KB (E1 : Type) (mc ms md : ℕ) : Type := KLoc (Fin 4) (EB E1 mc ms md)

/-- Registers: the four kernels' registers and one work register. -/
abbrev RB (R1 Rc Rs Rd : Type) : Type := R1 × (Rc × (Rs × (Rd × Option Sym)))

section Layout

variable (E1 : Type) (mc ms md : ℕ)

def locD : KB E1 mc ms md := .inr (.inr (.inl 0))
def locT : KB E1 mc ms md := .inr (.inr (.inl 1))
def locN1 : KB E1 mc ms md := .inr (.inr (.inl 2))
def locN2 : KB E1 mc ms md := .inr (.inr (.inl 3))

/-- The K1 kernel: source `0 ↦ 0`, destination `1 ↦ D`, counters `2 ↦ N1`, `3 ↦ N2`. -/
def ιK : KLoc (Fin 4) E1 → KB E1 mc ms md :=
  Sum.elim ![.inl 0, locD E1 mc ms md, locN1 E1 mc ms md, locN2 E1 mc ms md]
    fun e => .inr (.inl e)

/-- `copyNat`: number `src`, destination `dst`. -/
def ιC (src dst : KB E1 mc ms md) : Loc 2 mc → KB E1 mc ms md :=
  Sum.elim ![src, dst] fun j => .inr (.inr (.inr (.inl j)))

/-- `shlVar`: number `num` (in place), counter `u` (stack `1`). -/
def ιS (num : KB E1 mc ms md) : Loc 2 ms → KB E1 mc ms md :=
  Sum.elim ![num, .inl 1] fun j => .inr (.inr (.inr (.inr (.inl j))))

/-- `dropNat`: number `num`. -/
def ιD (num : KB E1 mc ms md) : Loc 1 md → KB E1 mc ms md :=
  Sum.elim ![num] fun j => .inr (.inr (.inr (.inr (.inr j))))

theorem ιK_inj : Function.Injective (ιK E1 mc ms md) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [locD, locN1, locN2]
  · intro a b h
    simpa using h
  · intro i e
    fin_cases i <;> simp [locD, locN1, locN2]

theorem ιC_inj {src dst : KB E1 mc ms md} (hsd : src ≠ dst)
    (hs : ∀ j, src ≠ .inr (.inr (.inr (.inl j)))) (hd : ∀ j, dst ≠ .inr (.inr (.inr (.inl j)))) :
    Function.Injective (ιC E1 mc ms md src dst) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro a b h
    simpa using h
  · intro i j
    fin_cases i
    · exact hs j
    · exact hd j

theorem ιS_inj {num : KB E1 mc ms md} (hn : num ≠ .inl 1)
    (hs : ∀ j, num ≠ .inr (.inr (.inr (.inr (.inl j))))) :
    Function.Injective (ιS E1 mc ms md num) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro a b h
    simpa using h
  · intro i j
    fin_cases i
    · exact hs j
    · simp

theorem ιD_inj {num : KB E1 mc ms md} (hs : ∀ j, num ≠ .inr (.inr (.inr (.inr (.inr j))))) :
    Function.Injective (ιD E1 mc ms md num) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j _
    exact Subsingleton.elim i j
  · intro a b h
    simpa using h
  · intro i j
    fin_cases i
    exact hs j

end Layout

section Lenses

variable (R1 Rc Rs Rd : Type)

def lK : Lens (RB R1 Rc Rs Rd) R1 := Lens.fst _ _
def lC : Lens (RB R1 Rc Rs Rd) Rc := (Lens.snd _ _).comp (Lens.fst _ _)
def lS : Lens (RB R1 Rc Rs Rd) Rs := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lD : Lens (RB R1 Rc Rs Rd) Rd :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lW : Lens (RB R1 Rc Rs Rd) (Option Sym) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))

end Lenses

/-! ## Generic `Runs` plumbing -/

section Plumbing

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

/-- `callInj` of a kernel that updates one stack. -/
theorem runs_inj_upd1 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x : L)
    (v : List Sym) (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T :=
  runs_callInj hι l (by rw [Function.update_comp_eq_of_injective B hι x v]; exact h)
    (fun k hk => Function.update_of_ne (Ne.symm (hk x)) _ _)

/-- `callInj` of a kernel that updates two stacks. -/
theorem runs_inj_upd2 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x y : L)
    (vx vy : List Sym)
    (h : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x vx) y vy) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update B (ι x) vx) (ι y) vy)
      (fun _ => True) T :=
  runs_callInj hι l
    (by rw [Function.update_comp_eq_of_injective _ hι y vy,
          Function.update_comp_eq_of_injective B hι x vx]; exact h)
    (fun k hk => by rw [Function.update_of_ne (Ne.symm (hk y)), Function.update_of_ne (Ne.symm (hk x))])

omit [DecidableEq L] in
theorem runs_skip (S : K → List Sym) :
    Runs (TMFw.Lib.skip : Prog K (fun _ => Sym) σ) S S (fun _ => True) 1 :=
  (Triple.load (ρ := []) id (fun s => s.stk = S ∧ True)).pre (fun _ hs => ⟨hs, trivial⟩)

omit [DecidableEq L] in
/-- Peek at stack `k` and record whether its top starts a record. -/
theorem runs_peek_test (l : Lens σ (Option Sym)) (k : K) (S : K → List Sym) (b : Bool)
    (hb : K1.isRecTop (S k).head? = b) :
    Runs ((peekR k).liftRegs l) S S (fun r => K1.isRecTop (l.get r) = b) 1 :=
  Triple.post (K1.triple_peek_lens l k S) (fun s hs => ⟨hs.1, by
    show K1.isRecTop (l.get s.var) = b
    rw [hs.2]
    exact hb⟩)

end Plumbing

/-! ## Pure facts -/

theorem termOK_mark (l : List Sym) : TermOK (Sym.mark :: l) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

theorem mark_not_mem_arrSyms (v : List (List Bool)) : Sym.mark ∉ arrSyms v := by
  intro h
  rcases K1.mem_arrSyms h with h | ⟨b, h⟩ <;> cases h

theorem len_le_of_mem_permByInv {v : List (List Bool)} {w : ℕ} (hw : ∀ p ∈ v, p.length = w)
    {f : ℕ → ℕ} {p : List Bool} (hp : p ∈ permByInv f v) : p.length ≤ w := by
  unfold permByInv at hp
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
  by_cases hy : f y < v.length
  · rw [List.getD_eq_getElem _ _ hy]
    exact (hw _ (List.getElem_mem _)).le
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem vol_permByInv_le {v : List (List Bool)} {w : ℕ} (hw : ∀ p ∈ v, p.length = w)
    (f : ℕ → ℕ) : vol (permByInv f v) ≤ vol v := by
  rw [K1.vol_eq_sum, AppC.C6Aux.vol_eq_of_width hw]
  calc ((permByInv f v).map fun p => p.length + 1).sum
      ≤ ((permByInv f v).map fun _ => w + 1).sum :=
        List.sum_le_sum fun p hp => by have := len_le_of_mem_permByInv hw hp; omega
    _ = v.length * (w + 1) := by
        rw [List.map_const', List.sum_replicate, AppC.C6Aux.length_permByInv, smul_eq_mul]

theorem permByInv_nil_bm (f : ℕ → ℕ) : permByInv f ([] : List (List Bool)) = [] := rfl

/-! ## The move-back pattern on generic keys -/

section Generic

variable {K σ : Type} [DecidableEq K]

/-- Push a `mark` on `D`; run `Pk` (meant to leave its result `A` on `D`, above the `mark`); push a
`mark` on `T`; then move `A` back onto `Z` in its original orientation: `rewindTo D T mark`, then
`rewindTo T Z mark` (each rewind reverses and drops its `mark`). -/
def movePG (l : Lens σ (Option Sym)) (Pk : Prog K (fun _ => Sym) σ) (Z D T : K) :
    Prog K (fun _ => Sym) σ :=
  .seq (WP.W9comp.pushConst D .mark)
    (.seq Pk (.seq (WP.W9comp.pushConst T .mark)
      (.seq ((WP.W9comp.rewindTo D T .mark).liftRegs l)
        ((WP.W9comp.rewindTo T Z .mark).liftRegs l))))

omit [DecidableEq K] in
theorem closed_movePG (l : Lens σ (Option Sym)) {Pk : Prog K (fun _ => Sym) σ} (hPk : Pk.Closed)
    (Z D T : K) : (movePG l Pk Z D T).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_pushConst _ _)
    (WP.W9comp.closed_seq hPk (WP.W9comp.closed_seq (WP.W9comp.closed_pushConst _ _)
      (WP.W9comp.closed_seq (WP.W9comp.closed_rewind _ _ _ _) (WP.W9comp.closed_rewind _ _ _ _))))

/-- **The move-back pattern.** Suppose `Pk`, started right after the `mark` push on `D`, replaces
stack `Z` by `rest` and pushes a mark-free block `A` on `D`. Then `movePG` puts `A` on top of `rest`
on `Z` and leaves every other stack (including `D` and `T`) unchanged. -/
theorem runs_movePG (l : Lens σ (Option Sym)) {Pk : Prog K (fun _ => Sym) σ} {Tk : ℕ} {Z D T : K}
    (hZD : Z ≠ D) (hZT : Z ≠ T) (hDT : D ≠ T) (S : K → List Sym) (A rest : List Sym)
    (hA : Sym.mark ∉ A)
    (hK : Runs Pk (Function.update S D (Sym.mark :: S D))
      (Function.update (Function.update (Function.update S D (Sym.mark :: S D)) Z rest) D
        (A ++ Function.update S D (Sym.mark :: S D) D)) (fun _ => True) Tk) :
    Runs (movePG l Pk Z D T) S (Function.update S Z (A ++ rest)) (fun _ => True)
      (1 + (Tk + (1 + ((3 * A.length + 2) + (3 * A.reverse.length + 2))))) := by
  have hA' : Sym.mark ∉ A.reverse := fun h => hA (List.mem_reverse.1 h)
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (WP.W9comp.runs_pushConst D Sym.mark S)
    (WP.W9comp.runs_seq hK (WP.W9comp.runs_seq (WP.W9comp.runs_pushConst T Sym.mark _)
      (WP.W9comp.runs_seq (WP.W9comp.runs_rewind l hDT Sym.mark A (S D) _ hA ?_)
        (WP.W9comp.runs_rewind l hZT.symm Sym.mark A.reverse (S T) _ hA' ?_))))) ?_
  · simp only [Function.update_of_ne hDT, Function.update_self]
  · simp only [Function.update_self, Function.update_of_ne hDT.symm, Function.update_of_ne hZT.symm]
  · funext k
    by_cases hkZ : k = Z
    · rw [hkZ]
      simp only [Function.update_self, Function.update_of_ne hZT, Function.update_of_ne hZD,
        List.reverse_reverse]
    · by_cases hkT : k = T
      · rw [hkT]
        simp only [Function.update_self, Function.update_of_ne hZT.symm]
      · by_cases hkD : k = D
        · rw [hkD]
          simp only [Function.update_self, Function.update_of_ne hZD.symm,
            Function.update_of_ne hDT]
        · simp only [Function.update_of_ne hkZ, Function.update_of_ne hkT,
            Function.update_of_ne hkD]

end Generic

/-! ## The program -/

section Prog

variable {E1 : Type} [DecidableEq E1] {mc ms md : ℕ} {R1 Rc Rs Rd : Type}

/-- Build `natSyms (2^u·X)` on the private stack `N`, above a fresh `mark`: copy the counter `X`
from stack `src` (`copyNat`), then shift it left by the counter `u` on stack `1` (`shlVar`). -/
def buildP (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) (Ps : Prog (Loc 2 ms) (fun _ => Sym) Rs)
    (src N : KB E1 mc ms md) : Prog (KB E1 mc ms md) (fun _ => Sym) (RB R1 Rc Rs Rd) :=
  .seq (WP.W9comp.pushConst N .mark)
    (.seq (callInj (ιC E1 mc ms md src N) (lC R1 Rc Rs Rd) Pc)
      (callInj (ιS E1 mc ms md N) (lS R1 Rc Rs Rd) Ps))

/-- The K1 kernel into the private stack `D`, then the move back onto stack `0` through `T`. -/
def moveP (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (KB E1 mc ms md) (fun _ => Sym) (RB R1 Rc Rs Rd) :=
  movePG (lW R1 Rc Rs Rd) (callInj (ιK E1 mc ms md) (lK R1 Rc Rs Rd) P1) (.inl 0)
    (locD E1 mc ms md) (locT E1 mc ms md)

/-- Drop the number on the private stack `N` (`dropNat`), then the `mark` below it. -/
def cleanP (Pd : Prog (Loc 1 md) (fun _ => Sym) Rd) (N : KB E1 mc ms md) :
    Prog (KB E1 mc ms md) (fun _ => Sym) (RB R1 Rc Rs Rd) :=
  .seq (callInj (ιD E1 mc ms md N) (lD R1 Rc Rs Rd) Pd) ((popR N).liftRegs (lW R1 Rc Rs Rd))

/-- The nonempty case: build both counters, move, drop both counters. -/
def mainP (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc)
    (Ps : Prog (Loc 2 ms) (fun _ => Sym) Rs) (Pd : Prog (Loc 1 md) (fun _ => Sym) Rd) :
    Prog (KB E1 mc ms md) (fun _ => Sym) (RB R1 Rc Rs Rd) :=
  .seq (buildP Pc Ps (.inl 2) (locN1 E1 mc ms md))
    (.seq (buildP Pc Ps (.inl 3) (locN2 E1 mc ms md))
      (.seq (moveP P1) (.seq (cleanP Pd (locN1 E1 mc ms md)) (cleanP Pd (locN2 E1 mc ms md)))))

/-- **The single-bit move.** Peek the array stack; run `mainP` iff its top starts a record. -/
def bitMoveP (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1)
    (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) (Ps : Prog (Loc 2 ms) (fun _ => Sym) Rs)
    (Pd : Prog (Loc 1 md) (fun _ => Sym) Rd) :
    Prog (KB E1 mc ms md) (fun _ => Sym) (RB R1 Rc Rs Rd) :=
  .seq ((peekR (Sum.inl 0 : KB E1 mc ms md)).liftRegs (lW R1 Rc Rs Rd))
    (.ite (fun r => K1.isRecTop ((lW R1 Rc Rs Rd).get r)) (mainP P1 Pc Ps Pd) TMFw.Lib.skip)

omit [DecidableEq E1] in
theorem closed_buildP {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc}
    {Ps : Prog (Loc 2 ms) (fun _ => Sym) Rs} (hPc : Pc.Closed) (hPs : Ps.Closed)
    (src N : KB E1 mc ms md) : (buildP (R1 := R1) (Rd := Rd) Pc Ps src N).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_pushConst _ _)
    (WP.W9comp.closed_seq (closed_callInj _ _ hPc) (closed_callInj _ _ hPs))

omit [DecidableEq E1] in
theorem closed_cleanP {Pd : Prog (Loc 1 md) (fun _ => Sym) Rd} (hPd : Pd.Closed)
    (N : KB E1 mc ms md) : (cleanP (R1 := R1) (Rc := Rc) (Rs := Rs) Pd N).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ hPd)
    (WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, popR]))

omit [DecidableEq E1] in
theorem closed_bitMoveP {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc} {Ps : Prog (Loc 2 ms) (fun _ => Sym) Rs}
    {Pd : Prog (Loc 1 md) (fun _ => Sym) Rd} (hP1 : P1.Closed) (hPc : Pc.Closed)
    (hPs : Ps.Closed) (hPd : Pd.Closed) : (bitMoveP P1 Pc Ps Pd).Closed := by
  have hmain : (mainP P1 Pc Ps Pd).Closed :=
    WP.W9comp.closed_seq (closed_buildP hPc hPs _ _)
      (WP.W9comp.closed_seq (closed_buildP hPc hPs _ _)
        (WP.W9comp.closed_seq (closed_movePG _ (closed_callInj _ _ hP1) _ _ _)
          (WP.W9comp.closed_seq (closed_cleanP hPd _) (closed_cleanP hPd _))))
  exact WP.W9comp.closed_seq
    (WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, peekR])) ⟨hmain, trivial⟩

/-- `buildP`: from `S` (counter `X` on `src`, `u` on stack `1`) to `natSyms (2^u·X)` above a `mark`
on `N`. -/
theorem runs_buildP {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc}
    {Ps : Prog (Loc 2 ms) (fun _ => Sym) Rs} {Cc Cs : ℕ}
    (hc : ∀ (a : ℕ) (rx : List Sym) (S : Loc 2 mc → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs Pc S (Function.update S (.inl 1) (natSyms a ++ S (.inl 1))) (fun _ => True)
        (Cc * (bitLen a + 1)))
    (hs : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 ms → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs Ps S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
        (Cs * (c + bitLen c + 1)))
    {src N : KB E1 mc ms md} (hιC : Function.Injective (ιC E1 mc ms md src N))
    (hιS : Function.Injective (ιS E1 mc ms md N)) (hsN : src ≠ N)
    (h1N : (Sum.inl 1 : KB E1 mc ms md) ≠ N)
    (S : KB E1 mc ms md → List Sym) (X u : ℕ) (rX ru : List Sym) (hrX : TermOK rX)
    (hru : TermOK ru) (hsrc : S src = natSyms X ++ rX) (h1 : S (.inl 1) = natSyms u ++ ru) :
    Runs (buildP (R1 := R1) (Rd := Rd) Pc Ps src N) S
      (Function.update S N (natSyms (2 ^ u * X) ++ Sym.mark :: S N)) (fun _ => True)
      (1 + (Cc * (bitLen X + 1) + Cs * (u + bitLen u + 1))) := by
  have hb := runs_inj_upd1 hιC (lC R1 Rc Rs Rd) (Function.update S N (Sym.mark :: S N)) (.inl 1) _
    (hc X rX _ hrX (by
      change Function.update S N _ src = _
      rw [Function.update_of_ne hsN]
      exact hsrc))
  have hb' : Runs (callInj (ιC E1 mc ms md src N) (lC R1 Rc Rs Rd) Pc)
      (Function.update S N (Sym.mark :: S N))
      (Function.update S N (natSyms X ++ Sym.mark :: S N)) (fun _ => True)
      (Cc * (bitLen X + 1)) := by
    refine WP.W9comp.runs_congr hb ?_
    change Function.update (Function.update S N (Sym.mark :: S N)) N
      (natSyms X ++ Function.update S N (Sym.mark :: S N) N) = _
    rw [Function.update_self, Function.update_idem]
  have hc' := runs_inj_upd1 hιS (lS R1 Rc Rs Rd)
    (Function.update S N (natSyms X ++ Sym.mark :: S N)) (.inl 0) _
    (hs X u (Sym.mark :: S N) ru _ (termOK_mark _) hru
      (by change Function.update S N _ N = _; rw [Function.update_self])
      (by change Function.update S N _ (.inl 1) = _; rw [Function.update_of_ne h1N]; exact h1))
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (WP.W9comp.runs_pushConst N Sym.mark S)
    (WP.W9comp.runs_seq hb' hc')) ?_
  change Function.update (Function.update S N (natSyms X ++ Sym.mark :: S N)) N
    (natSyms (X * 2 ^ u) ++ Sym.mark :: S N) = _
  rw [Function.update_idem, Nat.mul_comm X]

/-- `cleanP`: drop `natSyms X` and the `mark` below it from `N`. -/
theorem runs_cleanP {Pd : Prog (Loc 1 md) (fun _ => Sym) Rd} {Cd : ℕ}
    (hd : ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 md → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs Pd S (Function.update S (.inl 0) rx) (fun _ => True) (Cd * (bitLen a + 1)))
    {N : KB E1 mc ms md} (hι : Function.Injective (ιD E1 mc ms md N))
    (S : KB E1 mc ms md → List Sym) (X : ℕ) (r : List Sym)
    (hS : S N = natSyms X ++ Sym.mark :: r) :
    Runs (cleanP (R1 := R1) (Rc := Rc) (Rs := Rs) Pd N) S (Function.update S N r)
      (fun _ => True) (Cd * (bitLen X + 1) + 1) := by
  have h1 : Runs (callInj (ιD E1 mc ms md N) (lD R1 Rc Rs Rd) Pd) S
      (Function.update S N (Sym.mark :: r)) (fun _ => True) (Cd * (bitLen X + 1)) :=
    runs_inj_upd1 hι (lD R1 Rc Rs Rd) S (.inl 0) (Sym.mark :: r)
      (hd X (Sym.mark :: r) _ (termOK_mark r) hS)
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq h1
    (K1.runs_wk_popR (lW R1 Rc Rs Rd) N (Function.update S N (Sym.mark :: r)))) ?_
  rw [Function.update_self, List.tail_cons, Function.update_idem]

/-- `moveP`: the K1 kernel (consuming `arrSyms v` from stack `0`, pushing `arrSyms w` on `D`), then
the move back: stack `0` ends with `arrSyms w ++ rest`; every other stack is unchanged. -/
theorem runs_moveP {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1} {T1 : ℕ}
    (S : KB E1 mc ms md → List Sym) (v w : List (List Bool)) (rest r2 r3 : List Sym) (N1 N2 : ℕ)
    (hK : ∀ S' : KLoc (Fin 4) E1 → List Sym, S' (.inl 0) = arrSyms v ++ rest →
      S' (.inl 2) = natSyms N1 ++ r2 → S' (.inl 3) = natSyms N2 ++ r3 →
      Runs P1 S' (Function.update (Function.update S' (.inl 0) rest) (.inl 1)
        (arrSyms w ++ S' (.inl 1))) (fun _ => True) T1)
    (hS0 : S (.inl 0) = arrSyms v ++ rest) (hN1 : S (locN1 E1 mc ms md) = natSyms N1 ++ r2)
    (hN2 : S (locN2 E1 mc ms md) = natSyms N2 ++ r3) :
    Runs (moveP (Rc := Rc) (Rs := Rs) (Rd := Rd) P1) S
      (Function.update S (.inl 0) (arrSyms w ++ rest)) (fun _ => True)
      (1 + (T1 + (1 + ((3 * (arrSyms w).length + 2) + (3 * (arrSyms w).reverse.length + 2))))) := by
  have h0D : (Sum.inl 0 : KB E1 mc ms md) ≠ locD E1 mc ms md := by simp [locD]
  have h0T : (Sum.inl 0 : KB E1 mc ms md) ≠ locT E1 mc ms md := by simp [locT]
  have hDT : locD E1 mc ms md ≠ locT E1 mc ms md := by simp [locD, locT]
  have h1D : locN1 E1 mc ms md ≠ locD E1 mc ms md := by simp [locN1, locD]
  have h2D : locN2 E1 mc ms md ≠ locD E1 mc ms md := by simp [locN2, locD]
  refine runs_movePG (lW R1 Rc Rs Rd) h0D h0T hDT S (arrSyms w) rest (mark_not_mem_arrSyms w) ?_
  exact runs_inj_upd2 (ιK_inj E1 mc ms md) (lK R1 Rc Rs Rd) _ (.inl 0) (.inl 1) rest _
    (hK _ (by change Function.update S (locD E1 mc ms md) _ (.inl 0) = _
              rw [Function.update_of_ne h0D]; exact hS0)
      (by change Function.update S (locD E1 mc ms md) _ (locN1 E1 mc ms md) = _
          rw [Function.update_of_ne h1D]; exact hN1)
      (by change Function.update S (locD E1 mc ms md) _ (locN2 E1 mc ms md) = _
          rw [Function.update_of_ne h2D]; exact hN2))

end Prog

end AppC.C6BitMoveAux

open AppC.C6BitMoveAux in
/-- **Lemma A.8, the single-bit move** (Lemma A.8 (`lem:transfer12`)):
`C6BitMoveStmt toRight` holds for both directions, with no hypotheses. The program `bitMoveP` uses
only proved kernels: `K1Digit.k1MoveDigitMix_holds 2 toRight` (with `N1 = 2^u·G`, `N2 = 2^u·B`) and
the W3 kernels `copyNat`, `shlVar`, `dropNat`. -/
theorem c6BitMove_holds (toRight : Bool) : C6BitMoveStmt toRight := by
  obtain ⟨C1, hK⟩ := K1Digit.k1MoveDigitMix_holds 2 toRight
  obtain ⟨Cc, hC⟩ := WP.Inst.copyNat.ok
  obtain ⟨Cs, hS⟩ := WP.Inst.shlVar.ok
  obtain ⟨Cd, hD⟩ := WP.Inst.dropNat.ok
  obtain ⟨E1, _, _, R1, P1, hR1a, hR1b, hP1, hs1⟩ := hK ()
  obtain ⟨mc, Rc, -, Pc, -, hRca, hRcb, hPc, hsc⟩ := hC ()
  obtain ⟨ms, Rs, -, Ps, -, hRsa, hRsb, hPs, hss⟩ := hS ()
  obtain ⟨md, Rd, -, Pd, -, hRda, hRdb, hPd, hsd⟩ := hD ()
  have := hR1a; have := hR1b; have := hRca; have := hRcb
  have := hRsa; have := hRsb; have := hRda; have := hRdb
  refine ⟨C1 + 2 * Cc + 2 * Cs + 2 * Cd + 20, fun _ => ⟨EB E1 mc ms md, inferInstance,
    inferInstance, RB R1 Rc Rs Rd, bitMoveP P1 Pc Ps Pd, inferInstance, inferInstance,
    closed_bitMoveP hP1 hPc hPs hPd, ?_⟩⟩
  intro N0 u G B w v rest r1 r2 r3 S hlen hw hrest hr1 hr2 hr3 hS0 hS1 hS2 hS3
  by_cases hv : v = []
  · -- empty array: the peek sees no record, nothing to do
    subst hv
    have hS0' : S (.inl 0) = rest := by rw [hS0, K1.arrSyms_nil, List.nil_append]
    have h := RunsIn.ite_false (ρ := []) (Pt := mainP P1 Pc Ps Pd)
      (RunsIn.iff_runs.2 (runs_peek_test (lW R1 Rc Rs Rd) (Sum.inl 0) S false
        (by rw [hS0]; exact K1.isRecTop_nil hrest)))
      (RunsIn.iff_runs.2 (runs_skip S))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (RunsIn.iff_runs.1 h) ?_)
      (fun _ _ => trivial) ?_
    · rw [permByInv_nil_bm, K1.arrSyms_nil, List.nil_append, ← hS0', Function.update_eq_self]
    · simp only [K1.vol_nil, zero_add, mul_one]
      omega
  -- nonempty array
  have hrec : K1.isRecTop (S (.inl 0)).head? = true := by
    obtain ⟨p, v', rfl⟩ := List.exists_cons_of_ne_nil hv
    rw [hS0]
    exact K1.isRecTop_cons p v' rest
  have hlen0 : 0 < v.length := Nat.pos_of_ne_zero fun h => hv (List.eq_nil_of_length_eq_zero h)
  have hprod : 0 < N0 * 2 * 2 ^ u * G * 2 ^ u * B := by rw [← hlen]; exact hlen0
  have hN0 : 0 < N0 := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hG : 0 < G := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hB : 0 < B := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have h2u : 0 < 2 ^ u := pow_pos (by norm_num) u
  have hLV : v.length ≤ vol v := K1.length_le_vol v
  have hGl : 2 ^ u * G ≤ v.length := by
    rw [hlen, show N0 * 2 * 2 ^ u * G * 2 ^ u * B = 2 ^ u * G * (N0 * 2 * 2 ^ u * B) by ring]
    exact Nat.le_mul_of_pos_right _
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN0 (by norm_num)) h2u) hB)
  have hBl : 2 ^ u * B ≤ v.length := by
    rw [hlen, show N0 * 2 * 2 ^ u * G * 2 ^ u * B = 2 ^ u * B * (N0 * 2 * 2 ^ u * G) by ring]
    exact Nat.le_mul_of_pos_right _
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN0 (by norm_num)) h2u) hG)
  have h2l : 2 * 2 ^ u ≤ v.length := by
    rw [hlen, show N0 * 2 * 2 ^ u * G * 2 ^ u * B = 2 * 2 ^ u * (N0 * G * 2 ^ u * B) by ring]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN0 hG) h2u) hB)
  have hGG : G ≤ 2 ^ u * G := Nat.le_mul_of_pos_left G h2u
  have hBB : B ≤ 2 ^ u * B := Nat.le_mul_of_pos_left B h2u
  have hu : u < 2 ^ u := Nat.lt_two_pow_self
  have hbG : bitLen G ≤ G := WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hbB : bitLen B ≤ B := WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hbu : bitLen u ≤ u := WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hbGu : bitLen (2 ^ u * G) ≤ 2 ^ u * G :=
    WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hbBu : bitLen (2 ^ u * B) ≤ 2 ^ u * B :=
    WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hlen' : v.length = N0 * 2 * (2 ^ u * G) * (2 ^ u * B) := by rw [hlen]; ring
  have h0N1 : (Sum.inl 0 : KB E1 mc ms md) ≠ locN1 E1 mc ms md := by simp [locN1]
  have h0N2 : (Sum.inl 0 : KB E1 mc ms md) ≠ locN2 E1 mc ms md := by simp [locN2]
  have h1N1 : (Sum.inl 1 : KB E1 mc ms md) ≠ locN1 E1 mc ms md := by simp [locN1]
  have h1N2 : (Sum.inl 1 : KB E1 mc ms md) ≠ locN2 E1 mc ms md := by simp [locN2]
  have h2N1 : (Sum.inl 2 : KB E1 mc ms md) ≠ locN1 E1 mc ms md := by simp [locN1]
  have h3N1 : (Sum.inl 3 : KB E1 mc ms md) ≠ locN1 E1 mc ms md := by simp [locN1]
  have h3N2 : (Sum.inl 3 : KB E1 mc ms md) ≠ locN2 E1 mc ms md := by simp [locN2]
  have hN12 : locN1 E1 mc ms md ≠ locN2 E1 mc ms md := by simp [locN1, locN2]
  have hιC1 : Function.Injective (ιC E1 mc ms md (.inl 2) (locN1 E1 mc ms md)) :=
    ιC_inj E1 mc ms md h2N1 (fun j => by simp) (fun j => by simp [locN1])
  have hιC2 : Function.Injective (ιC E1 mc ms md (.inl 3) (locN2 E1 mc ms md)) :=
    ιC_inj E1 mc ms md h3N2 (fun j => by simp) (fun j => by simp [locN2])
  have hιS1 : Function.Injective (ιS E1 mc ms md (locN1 E1 mc ms md)) :=
    ιS_inj E1 mc ms md h1N1.symm (fun j => by simp [locN1])
  have hιS2 : Function.Injective (ιS E1 mc ms md (locN2 E1 mc ms md)) :=
    ιS_inj E1 mc ms md h1N2.symm (fun j => by simp [locN2])
  have hιD1 : Function.Injective (ιD E1 mc ms md (locN1 E1 mc ms md)) :=
    ιD_inj E1 mc ms md (fun j => by simp [locN1])
  have hιD2 : Function.Injective (ιD E1 mc ms md (locN2 E1 mc ms md)) :=
    ιD_inj E1 mc ms md (fun j => by simp [locN2])
  have hmain := WP.W9comp.runs_seq
    (runs_buildP (R1 := R1) (Rd := Rd) hsc hss hιC1 hιS1 h2N1 h1N1 S G u r2 r1 hr2 hr1 hS2 hS1)
    (WP.W9comp.runs_seq
      (runs_buildP (R1 := R1) (Rd := Rd) hsc hss hιC2 hιS2 h3N2 h1N2 _ B u r3 r1 hr3 hr1
        (by simp only [Function.update_of_ne h3N1, hS3])
        (by simp only [Function.update_of_ne h1N1, hS1]))
      (WP.W9comp.runs_seq
        (runs_moveP (Rc := Rc) (Rs := Rs) (Rd := Rd) _ v _ rest
          (Sym.mark :: S (locN1 E1 mc ms md)) (Sym.mark :: S (locN2 E1 mc ms md))
          (2 ^ u * G) (2 ^ u * B)
          (fun S' h0 h2 h3 => hs1 N0 (2 ^ u * G) (2 ^ u * B) v rest _ _ S' hlen' hrest
            (termOK_mark _) (termOK_mark _) h0 h2 h3)
          (by simp only [Function.update_of_ne h0N2, Function.update_of_ne h0N1, hS0])
          (by simp only [Function.update_of_ne hN12, Function.update_self])
          (by simp only [Function.update_self, Function.update_of_ne hN12.symm]))
        (WP.W9comp.runs_seq
          (runs_cleanP (R1 := R1) (Rc := Rc) (Rs := Rs) hsd hιD1 _ (2 ^ u * G)
            (S (locN1 E1 mc ms md))
            (by simp only [Function.update_of_ne h0N1.symm, Function.update_of_ne hN12,
              Function.update_self]))
          (runs_cleanP (R1 := R1) (Rc := Rc) (Rs := Rs) hsd hιD2 _ (2 ^ u * B)
            (S (locN2 E1 mc ms md))
            (by simp only [Function.update_of_ne hN12.symm, Function.update_of_ne h0N2.symm,
              Function.update_self])))))
  refine WP.W9comp.runs_mono (RunsIn.iff_runs.1 (RunsIn.ite_true (ρ := []) (Pf := TMFw.Lib.skip)
    (RunsIn.iff_runs.2 (runs_peek_test (lW R1 Rc Rs Rd) (Sum.inl 0) S true hrec))
    (RunsIn.iff_runs.2 (WP.W9comp.runs_congr hmain ?_)))) (fun _ _ => trivial) ?_
  · funext k
    by_cases hk0 : k = Sum.inl 0
    · rw [hk0]
      simp only [Function.update_self, Function.update_of_ne h0N1, Function.update_of_ne h0N2]
    · by_cases hk1 : k = locN1 E1 mc ms md
      · rw [hk1]
        simp only [Function.update_self, Function.update_of_ne hN12,
          Function.update_of_ne h0N1.symm]
      · by_cases hk2 : k = locN2 E1 mc ms md
        · rw [hk2]
          simp only [Function.update_self, Function.update_of_ne h0N2.symm]
        · simp only [Function.update_of_ne hk0, Function.update_of_ne hk1,
            Function.update_of_ne hk2]
  · have hW : (arrSyms (permByInv (if toRight then moveRightMixInv 2 (2 ^ u * G) (2 ^ u * B)
        else moveLeftMixInv 2 (2 ^ u * G) (2 ^ u * B)) v)).length ≤ vol v :=
      vol_permByInv_le hw _
    have hcG : Cc * (bitLen G + 1) ≤ Cc * (vol v + 1) := Nat.mul_le_mul_left _ (by omega)
    have hcB : Cc * (bitLen B + 1) ≤ Cc * (vol v + 1) := Nat.mul_le_mul_left _ (by omega)
    have hsu : Cs * (u + bitLen u + 1) ≤ Cs * (vol v + 1) := Nat.mul_le_mul_left _ (by omega)
    have hdG : Cd * (bitLen (2 ^ u * G) + 1) ≤ Cd * (vol v + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hdB : Cd * (bitLen (2 ^ u * B) + 1) ≤ Cd * (vol v + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : (C1 + 2 * Cc + 2 * Cs + 2 * Cd + 20) * (vol v + 1) = C1 * (vol v + 1) +
        2 * (Cc * (vol v + 1)) + 2 * (Cs * (vol v + 1)) + 2 * (Cd * (vol v + 1)) +
        20 * (vol v + 1) := by ring
    simp only [List.length_reverse]
    omega

end SubNLogN.Machine
