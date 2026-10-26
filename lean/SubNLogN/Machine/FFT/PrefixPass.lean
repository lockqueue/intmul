/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixPassSpec
import SubNLogN.Machine.FFT.PrefixPassMath
import SubNLogN.Machine.FFT.PrefixKit
import SubNLogN.Machine.Arith.CAdd
import IntMulTM.SpecFacts

/-!
# K4-PREFIX, one exact butterfly pass on the machine (`Machine/FFT/PrefixPass.lean`)

Proof of the sub-contract `PrefixPassStmt` (`Machine/FFT/PrefixPassSpec.lean` in
`Machine/FFT/`): `prefixPass_holds`, from the proved exact array sum/difference kernels
`Arith.cAdd_holds` / `Arith.cSub_holds` (`Machine/Arith/CAdd.lean`).

**Program** (`passProg`), on the named stacks `0` (array), `1` (`mark^h`), `2` (`natSyms W`), the
kernel stacks `PS` and the scratch of the two arithmetic kernels:
1. two copies of `natSyms W` onto `W1`, `W2` (`copyBits`);
2. the array, reversed, onto `T` (`movePrefix … isRecO`);
3. split loop on `T` (while a reversed record is on top): `h` records onto `L1`, `L2`, then `h`
   records onto `U1`, `U2` (`bdupRev`, counter = stack `1`). From the reversed array the last block
   pair comes first, so `L1 = L2 = bod h M B` and `U1 = U2 = bev h M B` (normal orientation);
4. `CAdd(U1, L1) → X` and `CSub(U2, L2) → Y` (`callInj`, widths `W, W, W` from stack `2`, `W1`,
   `W2`);
5. merge loop on `X`: `h` records from `X`, then `h` records from `Y`, onto `T2` (`bmov`), which
   receives the reversed interleave `bint h M X Y = bpass h M B`;
6. `T2` back onto stack `0` (normal orientation), then `W1`, `W2` emptied (`drain`).

All kernel stacks are empty again at the end. The cost is linear in `cvol W B + W`.
-/

namespace SubNLogN.Machine.FFT.PrefixPassAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine SubNLogN.Machine.FFT.DIF
  SubNLogN.Machine.FFT.PrefixAux

/-- The kernel's own private stacks. -/
inductive PS
  | T | L1 | L2 | U1 | U2 | X | Y | T2 | HA | W1 | W2
  deriving DecidableEq

instance : Fintype PS :=
  Fintype.ofList [.T, .L1, .L2, .U1, .U2, .X, .Y, .T2, .HA, .W1, .W2] (by intro x; cases x <;> simp)

/-- The full layout: named stacks `0`, `1`, `2`; the kernel stacks; the scratch of `CAdd`; the
scratch of `CSub`. -/
abbrev KP (Ea Es : Type) : Type := KLoc (Fin 3) (PS ⊕ (Ea ⊕ Es))

section Layout

variable {Ea Es : Type}

/-- A kernel stack. -/
def ps (d : PS) : KP Ea Es := .inr (.inl d)

/-- The named stacks. -/
def n0 : KP Ea Es := .inl 0
def n1 : KP Ea Es := .inl 1
def n2 : KP Ea Es := .inl 2

/-- Stacks of `CAdd`: `0 ↦ U1`, `1 ↦ L1`, `2 ↦ X`, `3 ↦ n2`, `4 ↦ W1`, `5 ↦ W2`. -/
def ιa : KLoc (Fin 6) Ea → KP Ea Es
  | .inl i => ![ps .U1, ps .L1, ps .X, n2, ps .W1, ps .W2] i
  | .inr e => .inr (.inr (.inl e))

/-- Stacks of `CSub`: `0 ↦ U2`, `1 ↦ L2`, `2 ↦ Y`, `3 ↦ n2`, `4 ↦ W1`, `5 ↦ W2`. -/
def ιs : KLoc (Fin 6) Es → KP Ea Es
  | .inl i => ![ps .U2, ps .L2, ps .Y, n2, ps .W1, ps .W2] i
  | .inr e => .inr (.inr (.inr e))

theorem ιa_injective : Function.Injective (ιa : KLoc (Fin 6) Ea → KP Ea Es) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιa, ps, n2]
  · fin_cases i <;> simp [ιa, ps, n2] at h
  · fin_cases j <;> simp [ιa, ps, n2] at h
  · simp only [ιa, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem ιs_injective : Function.Injective (ιs : KLoc (Fin 6) Es → KP Ea Es) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιs, ps, n2]
  · fin_cases i <;> simp [ιs, ps, n2] at h
  · fin_cases j <;> simp [ιs, ps, n2] at h
  · simp only [ιs, Sum.inr.injEq] at h
    rw [h]

theorem ps_ne_ps {d d' : PS} (h : d ≠ d') : (ps d : KP Ea Es) ≠ ps d' := by
  simpa [ps] using h

theorem ps_ne_n0 (d : PS) : (ps d : KP Ea Es) ≠ n0 := by simp [ps, n0]
theorem ps_ne_n1 (d : PS) : (ps d : KP Ea Es) ≠ n1 := by simp [ps, n1]
theorem ps_ne_n2 (d : PS) : (ps d : KP Ea Es) ≠ n2 := by simp [ps, n2]
theorem n0_ne_n2 : (n0 : KP Ea Es) ≠ n2 := by simp [n0, n2]

/-! ## States -/

/-- The kernel stacks, with `HA` empty. -/
def fs (t l1 l2 u1 u2 x y t2 w1 w2 : List Sym) : PS → List Sym
  | .T => t | .L1 => l1 | .L2 => l2 | .U1 => u1 | .U2 => u2 | .X => x | .Y => y | .T2 => t2
  | .HA => [] | .W1 => w1 | .W2 => w2

/-- A state of the pass: stack `0` holds `a0`, the kernel stacks hold `f`, the other stacks are
those of `S`. -/
def st (S : KP Ea Es → List Sym) (a0 : List Sym) (f : PS → List Sym) : KP Ea Es → List Sym :=
  fun x => match x with
  | .inl i => if i = 0 then a0 else S (.inl i)
  | .inr (.inl d) => f d
  | .inr (.inr e) => S (.inr (.inr e))

variable (S : KP Ea Es → List Sym) (a0 : List Sym) (f : PS → List Sym)

@[simp] theorem st_ps (d : PS) : st S a0 f (ps d) = f d := rfl
@[simp] theorem st_n0 : st S a0 f n0 = a0 := rfl
@[simp] theorem st_n1 : st S a0 f n1 = S n1 := rfl
@[simp] theorem st_n2 : st S a0 f n2 = S n2 := rfl

theorem st_upd_ps [DecidableEq Ea] [DecidableEq Es] (d : PS) (v : List Sym) :
    Function.update (st S a0 f) (ps d) v = st S a0 (Function.update f d v) := by
  funext x
  rcases x with i | d' | e
  · simp [st, ps]
  · by_cases hd : d' = d
    · subst hd; simp [st, ps]
    · simp [st, ps, hd]
  · simp [st, ps]

theorem st_upd_n0 [DecidableEq Ea] [DecidableEq Es] (v : List Sym) : Function.update (st S a0 f) n0 v = st S v f := by
  funext x
  rcases x with i | d' | e
  · fin_cases i <;> simp [st, n0]
  · simp [st, n0]
  · simp [st, n0]

end Layout

section FS

variable (t l1 l2 u1 u2 x y t2 w1 w2 v : List Sym)

@[simp] theorem fs_upd_T : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .T v =
    fs v l1 l2 u1 u2 x y t2 w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_L1 : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .L1 v =
    fs t v l2 u1 u2 x y t2 w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_L2 : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .L2 v =
    fs t l1 v u1 u2 x y t2 w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_U1 : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .U1 v =
    fs t l1 l2 v u2 x y t2 w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_U2 : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .U2 v =
    fs t l1 l2 u1 v x y t2 w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_X : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .X v =
    fs t l1 l2 u1 u2 v y t2 w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_Y : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .Y v =
    fs t l1 l2 u1 u2 x v t2 w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_T2 : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .T2 v =
    fs t l1 l2 u1 u2 x y v w1 w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_W1 : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .W1 v =
    fs t l1 l2 u1 u2 x y t2 v w2 := by
  funext d; cases d <;> rfl
@[simp] theorem fs_upd_W2 : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .W2 v =
    fs t l1 l2 u1 u2 x y t2 w1 v := by
  funext d; cases d <;> rfl

@[simp] theorem fs_upd_HA_nil : Function.update (fs t l1 l2 u1 u2 x y t2 w1 w2) .HA [] =
    fs t l1 l2 u1 u2 x y t2 w1 w2 := by
  funext d; cases d <;> rfl

end FS

/-- The clean initial state. -/
theorem st_init {Ea Es : Type} (S : KP Ea Es → List Sym) (hcl : KClean S) :
    S = st S (S n0) (fs [] [] [] [] [] [] [] [] [] []) := by
  funext x
  rcases x with i | d | e
  · fin_cases i <;> rfl
  · rw [hcl (.inl d)]
    cases d <;> rfl
  · rfl

/-- The clean final state. -/
theorem st_final {Ea Es : Type} [DecidableEq Ea] [DecidableEq Es] (S : KP Ea Es → List Sym) (hcl : KClean S) (v : List Sym) :
    st S v (fs [] [] [] [] [] [] [] [] [] []) = Function.update S n0 v := by
  conv_rhs => rw [st_init S hcl, st_upd_n0]

/-! ## Record lengths and volumes -/

theorem length_twosBits' (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem length_crecBits' (W : ℕ) : ∀ (cs : List CInt), (crecBits W cs).length = 2 * W * cs.length
  | [] => by simp [crecBits]
  | c :: cs => by
    have ih := length_crecBits' W cs
    simp only [crecBits, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [coefBits, length_twosBits']
    ring

theorem length_arrSyms_unif (v : List (List Bool)) (n : ℕ) (h : ∀ p ∈ v, p.length = n) :
    (arrSyms v).length = v.length * (n + 1) := length_arrSyms_uniform v n h

theorem cvol_unif {W r : ℕ} {v : List (List CInt)} (hr : ∀ row ∈ v, row.length = r) :
    cvol W v = v.length * (2 * W * r + 1) := by
  unfold cvol carrSyms
  rw [length_arrSyms_unif _ (2 * W * r), List.length_map]
  intro p hp
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hp
  rw [length_crecBits', hr row hrow]

theorem length_natSyms_le' (n : ℕ) : (natSyms n).length ≤ n := by
  simp only [natSyms, List.length_map]
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.2 Nat.lt_two_pow_self

/-! ## The arithmetic sub-kernels as hypotheses on given programs -/

/-- The `spec` body of `CAddStmt` (`Contracts/Arith.lean`), for a given program. -/
def CAddSpec (Ea : Type) [DecidableEq Ea] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 w3 : ℕ) (u v : List (List CInt)) (ru rv r3 r4 r5 : List Sym)
    (S : KLoc (Fin 6) Ea → List Sym),
    1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 u → CArrFits w2 v → CAligned u v →
    CArrFits w3 (zipC caddC u v) →
    BlkTerm ru → BlkTerm rv → TermOK r3 → TermOK r4 → TermOK r5 →
    S (.inl 0) = carrSyms w1 u ++ ru → S (.inl 1) = carrSyms w2 v ++ rv →
    S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
    S (.inl 5) = natSyms w3 ++ r5 →
    Runs P S
      (Function.update (Function.update (Function.update S (.inl 0) ru) (.inl 1) rv) (.inl 2)
        (carrSyms w3 (zipC caddC u v) ++ S (.inl 2)))
      (fun _ => True) (C * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1))

/-- The `spec` body of `CSubStmt` (`Contracts/Arith.lean`), for a given program. -/
def CSubSpec (Es : Type) [DecidableEq Es] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 6) Es) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 w3 : ℕ) (u v : List (List CInt)) (ru rv r3 r4 r5 : List Sym)
    (S : KLoc (Fin 6) Es → List Sym),
    1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 u → CArrFits w2 v → CAligned u v →
    CArrFits w3 (zipC csubC u v) →
    BlkTerm ru → BlkTerm rv → TermOK r3 → TermOK r4 → TermOK r5 →
    S (.inl 0) = carrSyms w1 u ++ ru → S (.inl 1) = carrSyms w2 v ++ rv →
    S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
    S (.inl 5) = natSyms w3 ++ r5 →
    Runs P S
      (Function.update (Function.update (Function.update S (.inl 0) ru) (.inl 1) rv) (.inl 2)
        (carrSyms w3 (zipC csubC u v) ++ S (.inl 2)))
      (fun _ => True) (C * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1))

section Calls

variable {Ea Es σ Ra Rs : Type} [DecidableEq Ea] [DecidableEq Es]

theorem runs_addCall (la : Lens σ Ra) {Ca : ℕ} {Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra}
    (hP : CAddSpec Ea Ra Ca Pa) (S : KP Ea Es → List Sym) (a0 : List Sym)
    (t l2 u2 y t2 : List Sym) (W : ℕ) (u v : List (List CInt)) (r2 : List Sym)
    (hr2 : TermOK r2) (hS2 : S n2 = natSyms W ++ r2) (hw : 1 ≤ W) (hu : CArrFits W u)
    (hv : CArrFits W v) (huv : CAligned u v) (hout : CArrFits W (zipC caddC u v)) :
    Runs (callInj ιa la Pa)
      (st S a0 (fs t (carrSyms W v) l2 (carrSyms W u) u2 [] y t2 (natSyms W) (natSyms W)))
      (st S a0 (fs t [] l2 [] u2 (carrSyms W (zipC caddC u v)) y t2 (natSyms W) (natSyms W)))
      (fun _ => True) (Ca * (cvol W u + cvol W v + cvol W u + W + W + W + 1)) := by
  have h := hP W W W u v [] [] r2 [] []
    (st S a0 (fs t (carrSyms W v) l2 (carrSyms W u) u2 [] y t2 (natSyms W) (natSyms W)) ∘ ιa)
    hw hw hw hu hv huv hout (fun _ h => by simp at h) (fun _ h => by simp at h) hr2 TermOK.nil
    TermOK.nil (by simp [ιa, fs]) (by simp [ιa, fs]) (by simp [ιa, hS2]) (by simp [ιa, fs])
    (by simp [ιa, fs])
  refine runs_callInj ιa_injective la (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with i | e
    · fin_cases i <;> simp [ιa, fs, st, ps, n2]
    · simp [ιa, st]
  · intro k hk
    rcases k with i | d | e
    · rfl
    · cases d
      all_goals first
        | rfl
        | exact absurd (by simp [ιa, ps] : ιa (.inl 0) = (ps .U1 : KP Ea Es)) (hk (.inl 0))
        | exact absurd (by simp [ιa, ps] : ιa (.inl 1) = (ps .L1 : KP Ea Es)) (hk (.inl 1))
        | exact absurd (by simp [ιa, ps] : ιa (.inl 2) = (ps .X : KP Ea Es)) (hk (.inl 2))
    · rfl

theorem runs_subCall (ls : Lens σ Rs) {Cs : ℕ} {Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs}
    (hP : CSubSpec Es Rs Cs Ps) (S : KP Ea Es → List Sym) (a0 : List Sym)
    (t l1 u1 x t2 : List Sym) (W : ℕ) (u v : List (List CInt)) (r2 : List Sym)
    (hr2 : TermOK r2) (hS2 : S n2 = natSyms W ++ r2) (hw : 1 ≤ W) (hu : CArrFits W u)
    (hv : CArrFits W v) (huv : CAligned u v) (hout : CArrFits W (zipC csubC u v)) :
    Runs (callInj ιs ls Ps)
      (st S a0 (fs t l1 (carrSyms W v) u1 (carrSyms W u) x [] t2 (natSyms W) (natSyms W)))
      (st S a0 (fs t l1 [] u1 [] x (carrSyms W (zipC csubC u v)) t2 (natSyms W) (natSyms W)))
      (fun _ => True) (Cs * (cvol W u + cvol W v + cvol W u + W + W + W + 1)) := by
  have h := hP W W W u v [] [] r2 [] []
    (st S a0 (fs t l1 (carrSyms W v) u1 (carrSyms W u) x [] t2 (natSyms W) (natSyms W)) ∘ ιs)
    hw hw hw hu hv huv hout (fun _ h => by simp at h) (fun _ h => by simp at h) hr2 TermOK.nil
    TermOK.nil (by simp [ιs, fs]) (by simp [ιs, fs]) (by simp [ιs, hS2]) (by simp [ιs, fs])
    (by simp [ιs, fs])
  refine runs_callInj ιs_injective ls (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with i | e
    · fin_cases i <;> simp [ιs, fs, st, ps, n2]
    · simp [ιs, st]
  · intro k hk
    rcases k with i | d | e
    · rfl
    · cases d
      all_goals first
        | rfl
        | exact absurd (by simp [ιs, ps] : ιs (.inl 0) = (ps .U2 : KP Ea Es)) (hk (.inl 0))
        | exact absurd (by simp [ιs, ps] : ιs (.inl 1) = (ps .L2 : KP Ea Es)) (hk (.inl 1))
        | exact absurd (by simp [ιs, ps] : ιs (.inl 2) = (ps .Y : KP Ea Es)) (hk (.inl 2))
    · rfl

end Calls

section FSeval

variable (t l1 l2 u1 u2 x y t2 w1 w2 : List Sym)

@[simp] theorem fs_T : fs t l1 l2 u1 u2 x y t2 w1 w2 .T = t := rfl
@[simp] theorem fs_L1 : fs t l1 l2 u1 u2 x y t2 w1 w2 .L1 = l1 := rfl
@[simp] theorem fs_L2 : fs t l1 l2 u1 u2 x y t2 w1 w2 .L2 = l2 := rfl
@[simp] theorem fs_U1 : fs t l1 l2 u1 u2 x y t2 w1 w2 .U1 = u1 := rfl
@[simp] theorem fs_U2 : fs t l1 l2 u1 u2 x y t2 w1 w2 .U2 = u2 := rfl
@[simp] theorem fs_X : fs t l1 l2 u1 u2 x y t2 w1 w2 .X = x := rfl
@[simp] theorem fs_Y : fs t l1 l2 u1 u2 x y t2 w1 w2 .Y = y := rfl
@[simp] theorem fs_T2 : fs t l1 l2 u1 u2 x y t2 w1 w2 .T2 = t2 := rfl
@[simp] theorem fs_HA : fs t l1 l2 u1 u2 x y t2 w1 w2 .HA = [] := rfl
@[simp] theorem fs_W1 : fs t l1 l2 u1 u2 x y t2 w1 w2 .W1 = w1 := rfl
@[simp] theorem fs_W2 : fs t l1 l2 u1 u2 x y t2 w1 w2 .W2 = w2 := rfl

end FSeval

/-! ## Straight-line phases -/

section Phases

variable {Ea Es σ : Type} [DecidableEq Ea] [DecidableEq Es] (lO : Lens σ (Option Sym))

theorem runs_copyW (S : KP Ea Es → List Sym) (a0 l1 l2 u1 u2 x y t2 : List Sym) (W : ℕ)
    (r2 : List Sym) (hr2 : TermOK r2) (hS2 : S n2 = natSyms W ++ r2) :
    Runs (.seq (copyBits lO n2 (ps .W1) (ps .T)) (copyBits lO n2 (ps .W2) (ps .T)))
      (st S a0 (fs [] l1 l2 u1 u2 x y t2 [] []))
      (st S a0 (fs [] l1 l2 u1 u2 x y t2 (natSyms W) (natSyms W)))
      (fun _ => True) (2 * (9 * (natSyms W).length + 4)) := by
  have hS2' : ∀ F : PS → List Sym,
      st S a0 F n2 = (Computability.encodeNat W).map Sym.bit ++ r2 := fun F => by
    rw [st_n2, hS2]; rfl
  have e1 := runs_copyBits lO (ps_ne_n2 .W1).symm (ps_ne_n2 .T).symm (ps_ne_ps (by decide))
    (st S a0 (fs [] l1 l2 u1 u2 x y t2 [] [])) (Computability.encodeNat W) r2 (hS2' _) hr2
    (by simp only [st_ps, fs_T]; exact TermOK.nil)
  rw [st_upd_ps, st_ps, fs_W1, List.append_nil, fs_upd_W1] at e1
  have e2 := runs_copyBits lO (ps_ne_n2 .W2).symm (ps_ne_n2 .T).symm (ps_ne_ps (by decide))
    (st S a0 (fs [] l1 l2 u1 u2 x y t2 ((Computability.encodeNat W).map Sym.bit) []))
    (Computability.encodeNat W) r2 (hS2' _) hr2
    (by simp only [st_ps, fs_T]; exact TermOK.nil)
  rw [st_upd_ps, st_ps, fs_W2, List.append_nil, fs_upd_W2] at e2
  exact runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
    (by simp only [natSyms, List.length_map]; omega)

theorem runs_toT (S : KP Ea Es → List Sym) (l1 l2 u1 u2 x y t2 w1 w2 : List Sym)
    (P : List (List Bool)) (rest : List Sym) (hrest : BlkTerm rest) :
    Runs (movePrefix lO n0 (ps .T) isRecO)
      (st S (arrSyms P ++ rest) (fs [] l1 l2 u1 u2 x y t2 w1 w2))
      (st S rest (fs (arrSyms P).reverse l1 l2 u1 u2 x y t2 w1 w2))
      (fun _ => True) (4 * (arrSyms P).length + 2) := by
  have e := runs_revArr_out lO (ps_ne_n0 .T).symm
    (st S (arrSyms P ++ rest) (fs [] l1 l2 u1 u2 x y t2 w1 w2)) P rest (st_n0 _ _ _) hrest
  refine runs_congr e ?_
  rw [st_upd_n0, st_upd_ps, st_ps, fs_T, List.append_nil, fs_upd_T]

theorem runs_fromT2 (S : KP Ea Es → List Sym) (rest t l1 l2 u1 u2 x y w1 w2 : List Sym)
    (v : List (List Bool)) :
    Runs (movePrefix lO (ps .T2) n0 isRecO)
      (st S rest (fs t l1 l2 u1 u2 x y (arrSyms v).reverse w1 w2))
      (st S (arrSyms v ++ rest) (fs t l1 l2 u1 u2 x y [] w1 w2))
      (fun _ => True) (4 * (arrSyms v).length + 2) := by
  have e := runs_revArr_in lO (ps_ne_n0 .T2)
    (st S rest (fs t l1 l2 u1 u2 x y (arrSyms v).reverse w1 w2)) v rfl
  refine runs_congr e ?_
  rw [st_upd_ps, st_upd_n0, st_n0, fs_upd_T2]

theorem runs_drains (S : KP Ea Es → List Sym) (a0 : List Sym) (W : ℕ) :
    Runs (.seq (drain lO (ps .W1)) (drain lO (ps .W2)))
      (st S a0 (fs [] [] [] [] [] [] [] [] (natSyms W) (natSyms W)))
      (st S a0 (fs [] [] [] [] [] [] [] [] [] []))
      (fun _ => True) (2 * (3 * (natSyms W).length + 2)) := by
  have e1 := runs_drain lO (ps .W1) (st S a0 (fs [] [] [] [] [] [] [] [] (natSyms W) (natSyms W)))
  rw [st_upd_ps, fs_upd_W1, st_ps, fs_W1] at e1
  have e2 := runs_drain lO (ps .W2) (st S a0 (fs [] [] [] [] [] [] [] [] [] (natSyms W)))
  rw [st_upd_ps, fs_upd_W2, st_ps, fs_W2] at e2
  exact runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) (by omega)

end Phases

/-! ## The split loop -/

section Split

variable {Ea Es σ : Type} [DecidableEq Ea] [DecidableEq Es] (lO : Lens σ (Option Sym))

/-- Split-loop body: `h` reversed records onto `L1, L2`, then `h` onto `U1, U2`. -/
def splitBody : Prog (KP Ea Es) (fun _ => Sym) σ :=
  .seq (bdupRev lO (ps .T) (ps .L1) (ps .L2) n1 (ps .HA))
    (bdupRev lO (ps .T) (ps .U1) (ps .U2) n1 (ps .HA))

/-- State of the split loop after `i` block pairs (the last `i` pairs of `P` are split off). -/
def splitSt (S : KP Ea Es → List Sym) (a1 : List Sym) (P : List (List Bool)) (h M : ℕ)
    (x y t2 w1 w2 : List Sym) (i : ℕ) : KP Ea Es → List Sym :=
  st S a1 (fs (arrSyms (P.take (2 * h * (M - i)))).reverse
    (arrSyms (bod h i (P.drop (2 * h * (M - i))))) (arrSyms (bod h i (P.drop (2 * h * (M - i)))))
    (arrSyms (bev h i (P.drop (2 * h * (M - i))))) (arrSyms (bev h i (P.drop (2 * h * (M - i)))))
    x y t2 w1 w2)

omit [DecidableEq Ea] [DecidableEq Es] in
theorem nodup_TL : ([ps .T, ps .L1, ps .L2, n1, ps .HA] : List (KP Ea Es)).Nodup := by
  simp [ps, n1]

omit [DecidableEq Ea] [DecidableEq Es] in
theorem nodup_TU : ([ps .T, ps .U1, ps .U2, n1, ps .HA] : List (KP Ea Es)).Nodup := by
  simp [ps, n1]

theorem runs_splitBody (S : KP Ea Es → List Sym) (a1 x y t2 w1 w2 : List Sym)
    (P : List (List Bool)) (h M n : ℕ) (hS1 : S n1 = List.replicate h .mark)
    (hP : P.length = 2 * h * M) (hn : ∀ p ∈ P, p.length = n) (i : ℕ) (hi : i < M) :
    Runs (splitBody lO) (splitSt S a1 P h M x y t2 w1 w2 i)
      (splitSt S a1 P h M x y t2 w1 w2 (i + 1))
      (fun _ => True) (2 * (h * (5 * n + 9) + 4 * h + 4)) := by
  obtain ⟨k, hk⟩ : ∃ k, M - i = k + 1 := ⟨M - i - 1, by omega⟩
  have hk' : M - (i + 1) = k := by omega
  have hkM : 2 * h * k + h + h ≤ P.length := by
    rw [hP]
    have : k + 1 ≤ M := by omega
    nlinarith
  have hElen : ((P.drop (2 * h * k)).take h).length = h := by
    rw [List.length_take, List.length_drop]; omega
  have hOlen : ((P.drop (2 * h * k + h)).take h).length = h := by
    rw [List.length_take, List.length_drop]; omega
  have hEn : ∀ p ∈ (P.drop (2 * h * k)).take h, p.length = n := fun p hp =>
    hn p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
  have hOn : ∀ p ∈ (P.drop (2 * h * k + h)).take h, p.length = n := fun p hp =>
    hn p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
  have htake : P.take (2 * h * (k + 1)) =
      P.take (2 * h * k) ++ (P.drop (2 * h * k)).take h ++ (P.drop (2 * h * k + h)).take h := by
    rw [show 2 * h * (k + 1) = 2 * h * k + h + h by ring, List.take_add, List.take_add]
  have hdrop : (P.drop (2 * h * k)).drop (2 * h) = P.drop (2 * h * (k + 1)) := by
    rw [List.drop_drop, show 2 * h * k + 2 * h = 2 * h * (k + 1) by ring]
  have hbod : bod h (i + 1) (P.drop (2 * h * k)) =
      (P.drop (2 * h * k + h)).take h ++ bod h i (P.drop (2 * h * (k + 1))) := by
    rw [bod_succ, hdrop, List.drop_drop]
  have hbev : bev h (i + 1) (P.drop (2 * h * k)) =
      (P.drop (2 * h * k)).take h ++ bev h i (P.drop (2 * h * (k + 1))) := by
    rw [bev_succ, hdrop]
  have hT0 : (arrSyms (P.take (2 * h * (M - i)))).reverse =
      (arrSyms ((P.drop (2 * h * k + h)).take h)).reverse ++
        ((arrSyms ((P.drop (2 * h * k)).take h)).reverse ++
          (arrSyms (P.take (2 * h * k))).reverse) := by
    rw [hk, htake, arrSyms_append', arrSyms_append', List.reverse_append, List.reverse_append]
  have hL1 : arrSyms (bod h (i + 1) (P.drop (2 * h * (M - (i + 1))))) =
      arrSyms ((P.drop (2 * h * k + h)).take h) ++ arrSyms (bod h i (P.drop (2 * h * (M - i)))) := by
    rw [hk', hbod, arrSyms_append', hk]
  have hU1 : arrSyms (bev h (i + 1) (P.drop (2 * h * (M - (i + 1))))) =
      arrSyms ((P.drop (2 * h * k)).take h) ++ arrSyms (bev h i (P.drop (2 * h * (M - i)))) := by
    rw [hk', hbev, arrSyms_append', hk]
  have hT1 : (arrSyms (P.take (2 * h * (M - (i + 1))))).reverse =
      (arrSyms (P.take (2 * h * k))).reverse := by rw [hk']
  have hRT : TermOK (arrSyms (P.take (2 * h * k))).reverse := by
    simpa using termOK_rev_arrSyms (P.take (2 * h * k)) [] TermOK.nil
  unfold splitSt
  rw [hT0, hL1, hU1, hT1]
  have e1 := runs_bdupRev lO nodup_TL
    (st S a1 (fs ((arrSyms ((P.drop (2 * h * k + h)).take h)).reverse ++
        ((arrSyms ((P.drop (2 * h * k)).take h)).reverse ++ (arrSyms (P.take (2 * h * k))).reverse))
      (arrSyms (bod h i (P.drop (2 * h * (M - i))))) (arrSyms (bod h i (P.drop (2 * h * (M - i)))))
      (arrSyms (bev h i (P.drop (2 * h * (M - i))))) (arrSyms (bev h i (P.drop (2 * h * (M - i)))))
      x y t2 w1 w2))
    _ n hOn _ (termOK_rev_arrSyms _ _ hRT) (by rw [st_ps, fs_T]) (by rw [st_n1, hS1, hOlen])
    (by rw [st_ps, fs_HA])
  simp only [st_upd_ps, st_ps, fs_L1, fs_L2, fs_upd_T, fs_upd_L1, fs_upd_L2, hOlen] at e1
  have e2 := runs_bdupRev lO nodup_TU
    (st S a1 (fs ((arrSyms ((P.drop (2 * h * k)).take h)).reverse ++
        (arrSyms (P.take (2 * h * k))).reverse)
      (arrSyms ((P.drop (2 * h * k + h)).take h) ++ arrSyms (bod h i (P.drop (2 * h * (M - i)))))
      (arrSyms ((P.drop (2 * h * k + h)).take h) ++ arrSyms (bod h i (P.drop (2 * h * (M - i)))))
      (arrSyms (bev h i (P.drop (2 * h * (M - i))))) (arrSyms (bev h i (P.drop (2 * h * (M - i)))))
      x y t2 w1 w2))
    _ n hEn _ hRT (by rw [st_ps, fs_T]) (by rw [st_n1, hS1, hElen]) (by rw [st_ps, fs_HA])
  simp only [st_upd_ps, st_ps, fs_U1, fs_U2, fs_upd_T, fs_upd_U1, fs_upd_U2, hElen] at e2
  exact runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) (le_of_eq (by ring))

theorem runs_splitLoop (S : KP Ea Es → List Sym) (a1 x y t2 w1 w2 : List Sym)
    (P : List (List Bool)) (h M n : ℕ) (hh : 1 ≤ h) (hS1 : S n1 = List.replicate h .mark)
    (hP : P.length = 2 * h * M) (hn : ∀ p ∈ P, p.length = n) :
    Runs (ploop lO (ps .T) isSepO (splitBody lO))
      (st S a1 (fs (arrSyms P).reverse [] [] [] [] x y t2 w1 w2))
      (st S a1 (fs [] (arrSyms (bod h M P)) (arrSyms (bod h M P)) (arrSyms (bev h M P))
        (arrSyms (bev h M P)) x y t2 w1 w2))
      (fun _ => True) (M * (2 * (h * (5 * n + 9) + 4 * h + 4) + 2) + 2) := by
  have h0 : splitSt S a1 P h M x y t2 w1 w2 0 =
      st S a1 (fs (arrSyms P).reverse [] [] [] [] x y t2 w1 w2) := by
    simp only [splitSt, Nat.sub_zero, bod_zero, bev_zero, arrSyms_nil',
      List.take_of_length_le (le_of_eq hP)]
  have hM : splitSt S a1 P h M x y t2 w1 w2 M =
      st S a1 (fs [] (arrSyms (bod h M P)) (arrSyms (bod h M P)) (arrSyms (bev h M P))
        (arrSyms (bev h M P)) x y t2 w1 w2) := by
    simp only [splitSt, Nat.sub_self, Nat.mul_zero, List.take_zero, List.drop_zero, arrSyms_nil',
      List.reverse_nil]
  rw [← h0, ← hM]
  refine runs_ploop_const lO (ps .T) isSepO (splitBody lO) M (splitSt S a1 P h M x y t2 w1 w2) _
    ?_ (fun i hi => runs_splitBody lO S a1 x y t2 w1 w2 P h M n hS1 hP hn i hi)
  intro i hi
  simp only [splitSt, st_ps, fs_T]
  rcases Nat.lt_or_ge i M with hlt | hge
  · have hpos : 0 < (P.take (2 * h * (M - i))).length := by
      rw [List.length_take, hP]
      have h1 : 0 < 2 * h * (M - i) := Nat.mul_pos (Nat.mul_pos (by norm_num) hh) (by omega)
      have h2 : 0 < 2 * h * M := Nat.mul_pos (Nat.mul_pos (by norm_num) hh) (by omega)
      exact Nat.lt_min.2 ⟨h1, h2⟩
    rcases List.eq_nil_or_concat (P.take (2 * h * (M - i))) with h0 | ⟨u, p, hup⟩
    · rw [h0] at hpos; simp at hpos
    · rw [hup, List.concat_eq_append]
      have hs := head?_rev_arrSyms_cons u p []
      rw [List.append_nil] at hs
      rw [hs]
      simp [isSepO, hlt]
  · have hiM : i = M := le_antisymm hi hge
    subst hiM
    simp [isSepO, arrSyms_nil']

end Split

/-! ## The merge loop -/

section Merge

variable {Ea Es σ : Type} [DecidableEq Ea] [DecidableEq Es] (lO : Lens σ (Option Sym))

/-- Merge-loop body: `h` records from `X`, then `h` records from `Y`, onto `T2` (reversed). -/
def mergeBody : Prog (KP Ea Es) (fun _ => Sym) σ :=
  .seq (bmov lO (ps .X) (ps .T2) n1 (ps .HA)) (bmov lO (ps .Y) (ps .T2) n1 (ps .HA))

/-- State of the merge loop after `i` block pairs. -/
def mergeSt (S : KP Ea Es → List Sym) (a2 : List Sym) (SP DP : List (List Bool)) (h : ℕ)
    (w1 w2 : List Sym) (i : ℕ) : KP Ea Es → List Sym :=
  st S a2 (fs [] [] [] [] [] (arrSyms (SP.drop (i * h))) (arrSyms (DP.drop (i * h)))
    (arrSyms (bint h i SP DP)).reverse w1 w2)

omit [DecidableEq Ea] [DecidableEq Es] in
theorem nodup_XT : ([ps .X, ps .T2, n1, ps .HA] : List (KP Ea Es)).Nodup := by simp [ps, n1]

omit [DecidableEq Ea] [DecidableEq Es] in
theorem nodup_YT : ([ps .Y, ps .T2, n1, ps .HA] : List (KP Ea Es)).Nodup := by simp [ps, n1]

theorem runs_mergeBody (S : KP Ea Es → List Sym) (a2 w1 w2 : List Sym)
    (SP DP : List (List Bool)) (h M n : ℕ) (hS1 : S n1 = List.replicate h .mark)
    (hSP : SP.length = h * M) (hDP : DP.length = h * M) (hnS : ∀ p ∈ SP, p.length = n)
    (hnD : ∀ p ∈ DP, p.length = n) (i : ℕ) (hi : i < M) :
    Runs (mergeBody lO) (mergeSt S a2 SP DP h w1 w2 i) (mergeSt S a2 SP DP h w1 w2 (i + 1))
      (fun _ => True) (2 * (h * (4 * n + 8) + 4 * h + 4)) := by
  have hih : i * h + h ≤ h * M := by
    have : i + 1 ≤ M := hi
    nlinarith
  have hPlen : ((SP.drop (i * h)).take h).length = h := by
    rw [List.length_take, List.length_drop, hSP]; omega
  have hQlen : ((DP.drop (i * h)).take h).length = h := by
    rw [List.length_take, List.length_drop, hDP]; omega
  have hnP : ∀ p ∈ (SP.drop (i * h)).take h, p.length = n := fun p hp =>
    hnS p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
  have hnQ : ∀ p ∈ (DP.drop (i * h)).take h, p.length = n := fun p hp =>
    hnD p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
  have hSs : arrSyms (SP.drop (i * h)) =
      arrSyms ((SP.drop (i * h)).take h) ++ arrSyms (SP.drop ((i + 1) * h)) := by
    rw [← arrSyms_append', Nat.succ_mul, ← List.drop_drop, List.take_append_drop]
  have hDs : arrSyms (DP.drop (i * h)) =
      arrSyms ((DP.drop (i * h)).take h) ++ arrSyms (DP.drop ((i + 1) * h)) := by
    rw [← arrSyms_append', Nat.succ_mul, ← List.drop_drop, List.take_append_drop]
  have hT2 : (arrSyms (bint h (i + 1) SP DP)).reverse =
      (arrSyms ((DP.drop (i * h)).take h)).reverse ++
        ((arrSyms ((SP.drop (i * h)).take h)).reverse ++ (arrSyms (bint h i SP DP)).reverse) := by
    rw [bint_succ, arrSyms_append', arrSyms_append', List.reverse_append, List.reverse_append,
      List.append_assoc]
  unfold mergeSt
  rw [hSs, hDs, hT2]
  have e1 := runs_bmov lO nodup_XT
    (st S a2 (fs [] [] [] [] [] (arrSyms ((SP.drop (i * h)).take h) ++ arrSyms (SP.drop ((i + 1) * h)))
      (arrSyms ((DP.drop (i * h)).take h) ++ arrSyms (DP.drop ((i + 1) * h)))
      (arrSyms (bint h i SP DP)).reverse w1 w2))
    _ n hnP _ (by rw [st_ps, fs_X]) (by rw [st_n1, hS1, hPlen]) (by rw [st_ps, fs_HA])
  simp only [st_upd_ps, st_ps, fs_T2, fs_upd_X, fs_upd_T2, hPlen] at e1
  have e2 := runs_bmov lO nodup_YT
    (st S a2 (fs [] [] [] [] [] (arrSyms (SP.drop ((i + 1) * h)))
      (arrSyms ((DP.drop (i * h)).take h) ++ arrSyms (DP.drop ((i + 1) * h)))
      ((arrSyms ((SP.drop (i * h)).take h)).reverse ++ (arrSyms (bint h i SP DP)).reverse) w1 w2))
    _ n hnQ _ (by rw [st_ps, fs_Y]) (by rw [st_n1, hS1, hQlen]) (by rw [st_ps, fs_HA])
  simp only [st_upd_ps, st_ps, fs_T2, fs_upd_Y, fs_upd_T2, hQlen] at e2
  exact runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) (le_of_eq (by ring))

theorem runs_mergeLoop (S : KP Ea Es → List Sym) (a2 w1 w2 : List Sym) (SP DP : List (List Bool))
    (h M n : ℕ) (hh : 1 ≤ h) (hS1 : S n1 = List.replicate h .mark) (hSP : SP.length = h * M)
    (hDP : DP.length = h * M) (hnS : ∀ p ∈ SP, p.length = n) (hnD : ∀ p ∈ DP, p.length = n) :
    Runs (ploop lO (ps .X) isRecO (mergeBody lO))
      (st S a2 (fs [] [] [] [] [] (arrSyms SP) (arrSyms DP) [] w1 w2))
      (st S a2 (fs [] [] [] [] [] [] [] (arrSyms (bint h M SP DP)).reverse w1 w2))
      (fun _ => True) (M * (2 * (h * (4 * n + 8) + 4 * h + 4) + 2) + 2) := by
  have h0 : mergeSt S a2 SP DP h w1 w2 0 =
      st S a2 (fs [] [] [] [] [] (arrSyms SP) (arrSyms DP) [] w1 w2) := by
    simp only [mergeSt, Nat.zero_mul, List.drop_zero, bint_zero, arrSyms_nil', List.reverse_nil]
  have hM : mergeSt S a2 SP DP h w1 w2 M =
      st S a2 (fs [] [] [] [] [] [] [] (arrSyms (bint h M SP DP)).reverse w1 w2) := by
    simp only [mergeSt, List.drop_of_length_le (le_of_eq (hSP.trans (Nat.mul_comm h M))),
      List.drop_of_length_le (le_of_eq (hDP.trans (Nat.mul_comm h M))), arrSyms_nil']
  rw [← h0, ← hM]
  refine runs_ploop_const lO (ps .X) isRecO (mergeBody lO) M (mergeSt S a2 SP DP h w1 w2) _
    ?_ (fun i hi => runs_mergeBody lO S a2 w1 w2 SP DP h M n hS1 hSP hDP hnS hnD i hi)
  intro i hi
  simp only [mergeSt, st_ps, fs_X]
  rcases Nat.lt_or_ge i M with hlt | hge
  · have hlt' : i * h < SP.length := by
      rw [hSP]
      have : i + 1 ≤ M := hlt
      nlinarith
    rw [List.drop_eq_getElem_cons hlt', arrSyms_cons', recSyms_eq]
    generalize SP[i * h] = p
    cases p <;> simp [isRecO, hlt]
  · have hiM : i = M := le_antisymm hi hge
    subst hiM
    rw [List.drop_of_length_le (le_of_eq (hSP.trans (Nat.mul_comm h i)))]
    simp [isRecO, arrSyms_nil']

end Merge

/-! ## The pass -/

section Pass

variable {Ea Es σ Ra Rs : Type} [DecidableEq Ea] [DecidableEq Es]

/-- The program of one exact butterfly pass. -/
def passProg (lO : Lens σ (Option Sym)) (la : Lens σ Ra) (ls : Lens σ Rs)
    (Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra)
    (Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs) : Prog (KP Ea Es) (fun _ => Sym) σ :=
  .seq (.seq (copyBits lO n2 (ps .W1) (ps .T)) (copyBits lO n2 (ps .W2) (ps .T)))
    (.seq (movePrefix lO n0 (ps .T) isRecO)
      (.seq (ploop lO (ps .T) isSepO (splitBody lO))
        (.seq (callInj ιa la Pa)
          (.seq (callInj ιs ls Ps)
            (.seq (ploop lO (ps .X) isRecO (mergeBody lO))
              (.seq (movePrefix lO (ps .T2) n0 isRecO)
                (.seq (drain lO (ps .W1)) (drain lO (ps .W2)))))))))

omit [DecidableEq Ea] [DecidableEq Es] in
theorem closed_passProg (lO : Lens σ (Option Sym)) (la : Lens σ Ra) (ls : Lens σ Rs)
    {Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra}
    {Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs} (hPa : Pa.Closed) (hPs : Ps.Closed) :
    (passProg lO la ls Pa Ps).Closed :=
  ⟨⟨closed_copyBits lO _ _ _, closed_copyBits lO _ _ _⟩, closed_movePrefix lO _ _ _,
    closed_ploop lO _ _ ⟨closed_bdupRev lO _ _ _ _ _, closed_bdupRev lO _ _ _ _ _⟩,
    closed_callInj _ _ hPa, closed_callInj _ _ hPs,
    closed_ploop lO _ _ ⟨closed_bmov lO _ _ _ _, closed_bmov lO _ _ _ _⟩,
    closed_movePrefix lO _ _ _, closed_drain lO _, closed_drain lO _⟩

/-- The cost arithmetic of the pass (all quantities abstract). -/
theorem pass_cost_le (Ca Cs W h M n b V Vb X : ℕ) (hh : 1 ≤ h) (hb : b ≤ W) (hV : V = 2 * X)
    (hVb : Vb = 2 * X) (hX : X = h * M * n + h * M) :
    2 * (9 * b + 4) + (4 * V + 2 + (M * (2 * (h * (5 * n + 9) + 4 * h + 4) + 2) + 2 +
      (Ca * (X + X + X + W + W + W + 1) + (Cs * (X + X + X + W + W + W + 1) +
        (M * (2 * (h * (4 * n + 8) + 4 * h + 4) + 2) + 2 + (4 * Vb + 2 +
          2 * (3 * b + 2))))))) ≤
      (50 + 3 * Ca + 3 * Cs) * (V + W + 1) := by
  subst hV hVb
  have hM : M ≤ h * M := Nat.le_mul_of_pos_left M hh
  have hA : Ca * (X + X + X + W + W + W + 1) ≤ 3 * Ca * (2 * X + W + 1) := by
    have : X + X + X + W + W + W + 1 ≤ 3 * (2 * X + W + 1) := by omega
    calc Ca * (X + X + X + W + W + W + 1) ≤ Ca * (3 * (2 * X + W + 1)) :=
          Nat.mul_le_mul_left _ this
      _ = 3 * Ca * (2 * X + W + 1) := by ring
  have hS : Cs * (X + X + X + W + W + W + 1) ≤ 3 * Cs * (2 * X + W + 1) := by
    have : X + X + X + W + W + W + 1 ≤ 3 * (2 * X + W + 1) := by omega
    calc Cs * (X + X + X + W + W + W + 1) ≤ Cs * (3 * (2 * X + W + 1)) :=
          Nat.mul_le_mul_left _ this
      _ = 3 * Cs * (2 * X + W + 1) := by ring
  have h3 : M * (2 * (h * (5 * n + 9) + 4 * h + 4) + 2) = 10 * X + 16 * (h * M) + 10 * M := by
    rw [hX]; ring
  have h6 : M * (2 * (h * (4 * n + 8) + 4 * h + 4) + 2) = 8 * X + 16 * (h * M) + 10 * M := by
    rw [hX]; ring
  have hXM : h * M ≤ X := by rw [hX]; omega
  have hsplit : (50 + 3 * Ca + 3 * Cs) * (2 * X + W + 1) =
      50 * (2 * X + W + 1) + 3 * Ca * (2 * X + W + 1) + 3 * Cs * (2 * X + W + 1) := by ring
  rw [hsplit]
  omega

theorem runs_pass (lO : Lens σ (Option Sym)) (la : Lens σ Ra) (ls : Lens σ Rs) {Ca Cs : ℕ}
    {Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra} {Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs}
    (hA : CAddSpec Ea Ra Ca Pa) (hSb : CSubSpec Es Rs Cs Ps)
    (S : KP Ea Es → List Sym) (hcl : KClean S) (W h M r : ℕ) (B : List (List CInt))
    (rest r2 : List Sym) (hW : 1 ≤ W) (hh : 1 ≤ h) (hB : B.length = 2 * h * M)
    (hr : ∀ row ∈ B, row.length = r) (hfit : CArrFits W B) (hfit' : CArrFits W (bpass h M B))
    (hrest : BlkTerm rest) (hr2 : TermOK r2) (hS0 : S n0 = carrSyms W B ++ rest)
    (hS1 : S n1 = List.replicate h .mark) (hS2 : S n2 = natSyms W ++ r2) :
    Runs (passProg lO la ls Pa Ps) S (Function.update S n0 (carrSyms W (bpass h M B) ++ rest))
      (fun _ => True) ((50 + 3 * Ca + 3 * Cs) * (cvol W B + W + 1)) := by
  -- record payloads
  have hPlen : (B.map (crecBits W)).length = 2 * h * M := by rw [List.length_map, hB]
  have hPn : ∀ p ∈ B.map (crecBits W), p.length = 2 * W * r := by
    intro p hp
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hp
    rw [length_crecBits', hr row hrow]
  have hSPlen : ((sumsOf h M B).map (crecBits W)).length = h * M := by
    rw [List.length_map, length_sumsOf hB]
  have hDPlen : ((diffsOf h M B).map (crecBits W)).length = h * M := by
    rw [List.length_map, length_diffsOf hB]
  have hnS : ∀ p ∈ (sumsOf h M B).map (crecBits W), p.length = 2 * W * r := by
    intro p hp
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hp
    rw [length_crecBits', rows_sumsOf hr row hrow]
  have hnD : ∀ p ∈ (diffsOf h M B).map (crecBits W), p.length = 2 * W * r := by
    intro p hp
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hp
    rw [length_crecBits', rows_diffsOf hr row hrow]
  have hbodP : arrSyms (bod h M (B.map (crecBits W))) = carrSyms W (bod h M B) := by
    rw [bod_map]; rfl
  have hbevP : arrSyms (bev h M (B.map (crecBits W))) = carrSyms W (bev h M B) := by
    rw [bev_map]; rfl
  have hfinal : arrSyms (bint h M ((sumsOf h M B).map (crecBits W))
      ((diffsOf h M B).map (crecBits W))) = carrSyms W (bpass h M B) := by
    rw [bint_map, bpass_eq]; rfl
  -- the phases
  have e1 := runs_copyW lO S (carrSyms W B ++ rest) [] [] [] [] [] [] [] W r2 hr2 hS2
  have e2 := runs_toT lO S [] [] [] [] [] [] [] (natSyms W) (natSyms W) (B.map (crecBits W)) rest
    hrest
  have e3 := runs_splitLoop lO S rest [] [] [] (natSyms W) (natSyms W) (B.map (crecBits W)) h M
    (2 * W * r) hh hS1 hPlen hPn
  rw [hbodP, hbevP] at e3
  have e4 := runs_addCall la hA S rest [] (carrSyms W (bod h M B)) (carrSyms W (bev h M B)) [] []
    W (bev h M B) (bod h M B) r2 hr2 hS2 hW (fits_bev hfit) (fits_bod hfit)
    (aligned_bev_bod hB hr) (fits_sumsOf hB hfit')
  have e5 := runs_subCall ls hSb S rest [] [] [] (carrSyms W (zipC caddC (bev h M B) (bod h M B)))
    [] W (bev h M B) (bod h M B) r2 hr2 hS2 hW (fits_bev hfit) (fits_bod hfit)
    (aligned_bev_bod hB hr) (fits_diffsOf hB hfit')
  have e6 := runs_mergeLoop lO S rest (natSyms W) (natSyms W) ((sumsOf h M B).map (crecBits W))
    ((diffsOf h M B).map (crecBits W)) h M (2 * W * r) hh hS1 hSPlen hDPlen hnS hnD
  have e7 := runs_fromT2 lO S rest [] [] [] [] [] [] [] (natSyms W) (natSyms W)
    (bint h M ((sumsOf h M B).map (crecBits W)) ((diffsOf h M B).map (crecBits W)))
  have e8 := runs_drains lO S
    (arrSyms (bint h M ((sumsOf h M B).map (crecBits W)) ((diffsOf h M B).map (crecBits W))) ++
      rest) W
  have e := runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4 (runs_seq' e5
    (runs_seq' e6 (runs_seq' e7 e8))))))
  have hinit : st S (carrSyms W B ++ rest) (fs [] [] [] [] [] [] [] [] [] []) = S := by
    rw [← hS0]; exact (st_init S hcl).symm
  rw [hinit, st_final S hcl, hfinal] at e
  refine runs_mono e (fun _ _ => trivial) ?_
  -- volumes
  have hV : (arrSyms (B.map (crecBits W))).length = cvol W B := rfl
  have hcv : cvol W B = 2 * (h * M * (2 * W * r) + h * M) := by
    rw [cvol_unif hr, hB]; ring
  have hcev : cvol W (bev h M B) = h * M * (2 * W * r) + h * M := by
    rw [cvol_unif (fun x hx => hr x (mem_of_mem_bev hx)), length_bev hB]; ring
  have hcod : cvol W (bod h M B) = h * M * (2 * W * r) + h * M := by
    rw [cvol_unif (fun x hx => hr x (mem_of_mem_bod hx)), length_bod hB]; ring
  have hVb : (carrSyms W (bpass h M B)).length = 2 * (h * M * (2 * W * r) + h * M) := by
    show cvol W (bpass h M B) = _
    rw [cvol_unif (rows_bpass hr), length_bpass hB]; ring
  rw [hV, hcev, hcod, hVb]
  have hc := pass_cost_le Ca Cs W h M (2 * W * r) (natSyms W).length (cvol W B)
    (2 * (h * M * (2 * W * r) + h * M)) (h * M * (2 * W * r) + h * M) hh
    (length_natSyms_le' W) hcv rfl rfl
  refine le_trans (le_of_eq ?_) hc
  ring

end Pass

/-- **`PrefixPassStmt`**: one exact butterfly pass, from the proved exact array sum and difference
kernels `Arith.cAdd_holds`, `Arith.cSub_holds`. -/
theorem prefixPass_holds : PrefixPassStmt := by
  obtain ⟨Ca, hCa⟩ := Arith.cAdd_holds
  obtain ⟨Ea, iFa, iDa, Ra, Pa, hRaf, hRan, hPac, hPa⟩ := hCa ()
  obtain ⟨Cs, hCs⟩ := Arith.cSub_holds
  obtain ⟨Es, iFs, iDs, Rs, Ps, hRsf, hRsn, hPsc, hPs⟩ := hCs ()
  have hA : CAddSpec Ea Ra Ca Pa := hPa
  have hSb : CSubSpec Es Rs Cs Ps := hPs
  refine ⟨50 + 3 * Ca + 3 * Cs, fun _ => ⟨PS ⊕ (Ea ⊕ Es), inferInstance, inferInstance,
    Option Sym × (Ra × Rs), passProg (Lens.fst _ _) ((Lens.snd _ _).comp (Lens.fst _ _))
      ((Lens.snd _ _).comp (Lens.snd _ _)) Pa Ps, ?_, ?_, closed_passProg _ _ _ hPac hPsc, ?_⟩⟩
  · have := hRaf
    have := hRsf
    infer_instance
  · have := hRan
    have := hRsn
    infer_instance
  · intro W h M r B rest r2 S hcl hW hh hB hr hfit hfit' hrest hr2 hS0 hS1 hS2
    exact runs_pass (Lens.fst _ _) ((Lens.snd _ _).comp (Lens.fst _ _))
      ((Lens.snd _ _).comp (Lens.snd _ _)) hA hSb S hcl W h M r B rest r2 hW hh hB hr hfit hfit'
      hrest hr2 hS0 hS1 hS2

end SubNLogN.Machine.FFT.PrefixPassAux
