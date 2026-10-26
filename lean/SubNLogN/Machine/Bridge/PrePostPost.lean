/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostW3
import SubNLogN.Machine.Bridge.Values
import SubNLogN.Math.Bridge.IntForms.Spread

/-!
# K5 output part (`Bridge/PrePostPost.lean`): `PostStmt`

`PostStmt` (`SubNLogN/Machine/Contracts/Bridge.lean` §7; Section 4.4 (`sec:bridge-alg`), step (5)):
consume the array `Z` (`q = P+2`-grid, width `wI`) from `arr` and `e` from `ex`, push onto `dst`
the array `crnd roundHalfUpR (p+2) (2^e Z)` at width `wOut` (exact `×2^e`, one nearest rounding
with ties toward `+∞`).

## Program (`postProg`)
If `arr` is empty (`R = 0`; then nothing may cost more than the budget `eBound + setup`), only
`e` is dropped from `ex`. Otherwise:
1. fetch `P, p, wI, wOut` from the header (`fetchField`), copy `e` from `ex`;
2. `q := P + 2`, `X := p + e + 2` (W3 add, `Lib.inc`); compare `q` with `X` (W3 cmp);
3. if `q > X`: `s := q - X` and call the half-up right shift `RoundHalfUpShiftStmt`
   (`Contracts/Arith.lean`) from `arr` to `dst`; else `s := X - q` and call the exact left shift
   `ShlStmt` (both with `w1 = wI`, `w2 = wOut`, consuming `arr`);
4. drop every number (scratch clean again) and `e` from `ex`.
By `crnd_two_pow_mul_gridValC` (`Math/Bridge/IntForms/Spread.lean`) the output numerators
are `postScaleInt q p e c`, which is the left shift or the half-up right shift (`post_encVec`).

**Scope (honest summary).** Definitions, component lemmas, the value lemma `post_encVec`, the
correctness theorem `runs_postMain`, closedness, and the reduction
`post_holds_of (hShl : ShlStmt) (hRhu : RoundHalfUpShiftStmt) : PostStmt`; no `sorry`. The
unconditional `SubNLogN.Machine.post_holds` is in `Bridge/PrePostFinal.lean`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Math.Common SubNLogN.Math.Common.GridInt SubNLogN.Math.Bridge

/-! ## Value lemmas -/

theorem gridInt_gridValC' (F : ℕ) (c : ℤ × ℤ) : gridInt F (gridValC F c) = c :=
  gridIntC_gridValC F c

theorem gridValC_gridInt' {F : ℕ} {z : ℂ} (hz : OnGrid F z) : gridValC F (gridInt F z) = z :=
  gridValC_gridIntC hz

theorem postScaleInt_of_le {q p e : ℕ} (h : q ≤ p + 2 + e) :
    IntForms.postScaleInt q p e = shlC (p + 2 + e - q) := by
  funext c
  simp only [IntForms.postScaleInt, if_pos h, smulC, shlC, mul_comm]

theorem postScaleInt_of_gt {q p e : ℕ} (h : ¬ q ≤ p + 2 + e) :
    IntForms.postScaleInt q p e = roundHalfUpShiftC (q - (p + 2 + e)) := by
  funext c
  simp only [IntForms.postScaleInt, if_neg h, rhuShiftC, rhuShift, roundHalfUpShiftC, rhuPow]

/-- **The output numerators** (from `crnd_two_pow_mul_gridValC`). -/
theorem post_encVec (P p e : ℕ) {R : ℕ} (Z : Fin R → ℂ) (hZ : ∀ f, OnGrid (P + 2) (Z f)) :
    encVec (p + 2) (fun f => crnd roundHalfUpR (p + 2) ((2 : ℂ) ^ e * Z f)) =
      mapC (IntForms.postScaleInt (P + 2) p e) (encVec (P + 2) Z) := by
  unfold encVec mapC
  rw [List.map_map]
  apply List.map_congr_left
  intro f _
  simp only [Function.comp_apply, List.map_cons, List.map_nil]
  congr 1
  have h := gridValC_gridInt' (hZ f)
  conv_lhs => rw [← h]
  rw [IntForms.crnd_two_pow_mul_gridValC, gridInt_gridValC']

theorem twosBits_len (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem length_carrSyms_map (w : ℕ) {α : Type} (g : α → CInt) :
    ∀ l : List α, (carrSyms w (l.map fun j => [g j])).length = l.length * (2 * w + 1)
  | [] => by simp [carrSyms, arrSyms, blk]
  | j :: l => by
    have ih := length_carrSyms_map w g l
    simp only [List.map_cons, carrSyms, arrSyms, blk, List.flatten_cons, List.length_append,
      List.map_map] at ih ⊢
    rw [ih]
    simp [recSyms, crecBits, coefBits, twosBits_len]
    ring

theorem length_carrSyms_encVec (w F : ℕ) {R : ℕ} (Z : Fin R → ℂ) :
    (carrSyms w (encVec F Z)).length = R * (2 * w + 1) := by
  have h := length_carrSyms_map w (fun j => gridInt F (Z j)) (List.finRange R)
  rw [List.length_finRange] at h
  exact h

theorem cvol_encVec (w F : ℕ) {R : ℕ} (Z : Fin R → ℂ) : cvol w (encVec F Z) = R * (2 * w + 1) :=
  length_carrSyms_encVec w F Z

theorem cvol_mapC_encVec (w F : ℕ) {R : ℕ} (Z : Fin R → ℂ) (f : CInt → CInt) :
    cvol w (mapC f (encVec F Z)) = R * (2 * w + 1) := by
  have h := length_carrSyms_map w (fun j => f (gridInt F (Z j))) (List.finRange R)
  rw [List.length_finRange] at h
  unfold cvol
  simpa [mapC, encVec, List.map_map, Function.comp_def] using h

theorem carrSyms_encVec_zero (w F : ℕ) (Z : Fin 0 → ℂ) : carrSyms w (encVec F Z) = [] := by
  simp [carrSyms, arrSyms, blk, encVec]

theorem optIsBit_carrSyms_encVec {w F R : ℕ} (hw : 1 ≤ w) (hR : 0 < R) (Z : Fin R → ℂ)
    (L : List Sym) : optIsBit (carrSyms w (encVec F Z) ++ L).head? = true := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  simp [carrSyms, arrSyms, blk, encVec, List.finRange_succ, recSyms, crecBits, coefBits, twosBits,
    bitsLE, List.range_succ_eq_map]

theorem optIsBit_of_blkTerm {L : List Sym} (h : BlkTerm L) : optIsBit L.head? = false := by
  rcases L with _ | ⟨y, L⟩
  · rfl
  · obtain ⟨hd, -⟩ := h y rfl
    rcases y with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [isDataSym]

/-! ## Small `Runs` wrappers -/

section Wrap

variable {K : Type} [DecidableEq K]

theorem runs_inc {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (inc k t) S (Function.update S k (natSyms (n + 1) ++ rest)) (fun _ => True)
      (6 * bitLen n + 9) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval (ρ := []) hkt v (encodeNat n) rest S hrest hS
  refine ⟨some .mark, c, ?_, trivial, ?_⟩
  · rw [natSyms, encodeNat_succ]
    exact e
  · have : ones (encodeNat n) ≤ bitLen n := by
      unfold bitLen
      clear e hc
      induction (encodeNat n) with
      | nil => simp [ones]
      | cons b l ih => cases b <;> simp [ones] <;> omega
    omega

theorem runs_dropNum {k : K} (n : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms n ++ rest) :
    Runs (WP.W3.dropNum k) S (Function.update S k rest) (fun _ => True) (2 * bitLen n + 4) :=
  Runs.of_eval fun v => ⟨_, _, WP.W3.dropNum_eval [] v (encodeNat n) rest S hrest hS, trivial,
    by unfold bitLen; omega⟩

end Wrap

/-! ## Layout, registers, state descriptions -/

/-- Private work stacks of the post part. -/
inductive QW
  | G | U | NP | Np | NI | NO | NE | NX | NS
  deriving DecidableEq

/-- Scratch of the post part: own stacks, W3 scratch, the two AR kernels' scratch. -/
abbrev QE (Es Er : Type) : Type := QW ⊕ (Fin 4 ⊕ (Es ⊕ Er))

/-- Registers of the post part. -/
abbrev QReg (Rs Rr : Type) : Type :=
  Option Sym × (Rs × (Rr × (theW3Kit.Ra × (theW3Kit.Rb × theW3Kit.Rc))))

section Layout

variable {Es Er Rs Rr : Type}

/-- An own work stack. -/
abbrev qL (x : QW) : KLoc BrK (QE Es Er) := .inr (.inl x)
/-- A W3 scratch stack. -/
abbrev w3L (j : Fin 4) : KLoc BrK (QE Es Er) := .inr (.inr (.inl j))
/-- A scratch stack of the left-shift kernel. -/
abbrev esL (e : Es) : KLoc BrK (QE Es Er) := .inr (.inr (.inr (.inl e)))
/-- A scratch stack of the half-up kernel. -/
abbrev erL (e : Er) : KLoc BrK (QE Es Er) := .inr (.inr (.inr (.inr e)))

def lq0 : Lens (QReg Rs Rr) (Option Sym) := Lens.fst _ _
def lqS : Lens (QReg Rs Rr) Rs := (Lens.snd _ _).comp (Lens.fst _ _)
def lqR : Lens (QReg Rs Rr) Rr := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lqA : Lens (QReg Rs Rr) theW3Kit.Ra :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lqB : Lens (QReg Rs Rr) theW3Kit.Rb :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lqC : Lens (QReg Rs Rr) theW3Kit.Rc :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.snd _ _))))

/-- Stack map of a W3 call with named stacks `xs`. -/
def w3Map {n m : ℕ} (hm : m ≤ 4) (xs : Fin n → QW) : Loc n m → KLoc BrK (QE Es Er) :=
  locMap (fun i => qL (xs i)) (fun j => w3L (Fin.castLE hm j))

/-- Stack map of an AR kernel call (`Fin 5`: source, destination, `w1`, `w2`, `s`). -/
def arMap {E' : Type} (scr : E' → KLoc BrK (QE Es Er)) : KLoc (Fin 5) E' → KLoc BrK (QE Es Er) :=
  Sum.elim ![kW .arr, kN .dst, qL .NI, qL .NO, qL .NS] scr

/-- State description: own work stacks `f`, `arr = A`, `ex = E`, `dst = D`, the rest from `S`. -/
def qst (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym) :
    KLoc BrK (QE Es Er) → List Sym
  | .inl (.inr .arr) => A
  | .inl (.inr .ex) => E
  | .inl (.inl .dst) => D
  | .inr (.inl x) => f x
  | k => S k

variable [DecidableEq Es] [DecidableEq Er]

theorem qst_upd_q (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (x : QW) (w : List Sym) :
    Function.update (qst S f A E D) (qL x) w = qst S (Function.update f x w) A E D := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> rfl
  · by_cases h : y = x
    · subst h; simp [qst]
    · simp [qst, h]
  · simp [qst]

theorem qst_upd_arr (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D A' : List Sym) :
    Function.update (qst S f A E D) (kW .arr) A' = qst S f A' E D := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> simp [qst]
  · simp [qst]
  · simp [qst]

theorem qst_upd_ex (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D E' : List Sym) :
    Function.update (qst S f A E D) (kW .ex) E' = qst S f A E' D := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> simp [qst]
  · simp [qst]
  · simp [qst]

theorem qst_upd_dst (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D D' : List Sym) :
    Function.update (qst S f A E D) (kN .dst) D' = qst S f A E D' := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> simp [qst]
  · cases w' <;> rfl
  · simp [qst]
  · simp [qst]

end Layout

/-! ## Component steps on state descriptions -/

section Steps

variable {Es Er Rs Rr : Type} [DecidableEq Es] [DecidableEq Er]

theorem qst_par (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym) :
    qst S f A E D (kN .par) = S (kN .par) := rfl

theorem qst_self (S : KLoc BrK (QE Es Er) → List Sym) (hS : KClean S) :
    qst S (fun _ => []) (S (kW .arr)) (S (kW .ex)) (S (kN .dst)) = S := by
  funext k
  rcases k with ((n | w') | (y | j))
  · cases n <;> rfl
  · cases w' <;> rfl
  · exact (hS (.inl y)).symm
  · rfl

theorem q_fetch (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (x : QW) (hxG : x ≠ .G) (hxU : x ≠ .U) (hfx : f x = []) (fs1 : List ℕ) (a : ℕ)
    (fs2 : List ℕ) (L : List Sym) (hpar : S (kN .par) = hdrSyms (fs1 ++ a :: fs2) ++ L) :
    Runs ((fetchField (kN .par) (qL .G) (qL .U) (qL x) fs1.length).liftRegs
        (lq0 (Rs := Rs) (Rr := Rr)))
      (qst S f A E D) (qst S (Function.update f x (natSyms a ++ [])) A E D) (fun _ => True)
      (9 * (hdrSyms (fs1 ++ a :: fs2)).length + 11) := by
  have h := runs_fetchField (src := kN .par) (G := (qL .G : KLoc BrK (QE Es Er))) (tmp := qL .U)
    (dst := qL x) (by simp) (by simp) (by simp) (by simpa using Ne.symm hxG)
    (by simpa using Ne.symm hxU) fs1 a fs2 L (qst S f A E D) hpar
  refine WP.W9comp.runs_congr (runs_liftRegs lq0 h) ?_
  have hx : qst S f A E D (qL x) = [] := hfx
  rw [hx, qst_upd_q]

theorem q_copyE (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (hfx : f .NE = []) (n : ℕ) (rex : List Sym) (hrex : TermOK rex) (hE : E = natSyms n ++ rex) :
    Runs ((copyBlock (kW .ex) (qL .NE) (qL .U)).liftRegs (lq0 (Rs := Rs) (Rr := Rr)))
      (qst S f A E D) (qst S (Function.update f .NE (natSyms n ++ [])) A E D) (fun _ => True)
      (7 * bitLen n + 7) := by
  have h := runs_copyBlock (src := kW .ex) (dst := (qL .NE : KLoc BrK (QE Es Er))) (tmp := qL .U)
    (by simp) (by simp) (by simp) (encodeNat n) rex (qst S f A E D) hrex hE
  refine WP.W9comp.runs_congr (runs_liftRegs lq0 h) ?_
  have hx : qst S f A E D (qL .NE) = [] := hfx
  rw [hx, qst_upd_q]
  rfl

theorem q_inc (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (x : QW) (hxU : x ≠ .U) (n : ℕ) (hfx : f x = natSyms n ++ []) :
    Runs ((inc (qL x) (qL .U)).liftRegs (lq0 (Rs := Rs) (Rr := Rr)))
      (qst S f A E D) (qst S (Function.update f x (natSyms (n + 1) ++ [])) A E D) (fun _ => True)
      (6 * bitLen n + 9) := by
  have h := runs_inc (k := (qL x : KLoc BrK (QE Es Er))) (t := qL .U) (by simpa using hxU) n []
    (qst S f A E D) TermOK.nil hfx
  refine WP.W9comp.runs_congr (runs_liftRegs lq0 h) ?_
  exact qst_upd_q S f A E D x _

theorem q_drop (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (x : QW) (n : ℕ) (hfx : f x = natSyms n ++ []) :
    Runs ((WP.W3.dropNum (qL x)).liftRegs (lq0 (Rs := Rs) (Rr := Rr)))
      (qst S f A E D) (qst S (Function.update f x []) A E D) (fun _ => True)
      (2 * bitLen n + 4) := by
  have h := runs_dropNum (k := (qL x : KLoc BrK (QE Es Er))) n [] (qst S f A E D) TermOK.nil hfx
  refine WP.W9comp.runs_congr (runs_liftRegs lq0 h) ?_
  exact qst_upd_q S f A E D x _

theorem q_dropEx (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (n : ℕ) (rex : List Sym) (hrex : TermOK rex) (hE : E = natSyms n ++ rex) :
    Runs ((WP.W3.dropNum (kW .ex)).liftRegs (lq0 (Rs := Rs) (Rr := Rr)))
      (qst S f A E D) (qst S f A rex D) (fun _ => True) (2 * bitLen n + 4) := by
  have h := runs_dropNum (k := (kW .ex : KLoc BrK (QE Es Er))) n rex (qst S f A E D) hrex hE
  refine WP.W9comp.runs_congr (runs_liftRegs lq0 h) ?_
  exact qst_upd_ex S f A E D rex

theorem w3Map_injective {n m : ℕ} (hm : m ≤ 4) (xs : Fin n → QW) (hxs : Function.Injective xs) :
    Function.Injective (w3Map (Es := Es) (Er := Er) hm xs) := by
  refine locMap_injective ?_ ?_ ?_
  · intro i j h
    exact hxs (by simpa using h)
  · intro i j h
    exact Fin.castLE_injective hm (by simpa using h)
  · intro i j
    simp

theorem inj3 {a b c : QW} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem inj2 {a b : QW} (hab : a ≠ b) : Function.Injective ![a, b] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem q_add (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (x y z : QW) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (a b : ℕ)
    (hx : f x = natSyms a ++ []) (hy : f y = natSyms b ++ []) (hz : f z = []) :
    Runs (callInj (w3Map theW3Kit.hma ![x, y, z]) (lqA (Rs := Rs) (Rr := Rr)) theW3Kit.Pa)
      (qst S f A E D) (qst S (Function.update f z (natSyms (a + b) ++ [])) A E D)
      (fun _ => True) (theW3Kit.Ca * (bitLen a + bitLen b + 1)) := by
  have hinj := w3Map_injective (Es := Es) (Er := Er) theW3Kit.hma _ (inj3 hxy hxz hyz)
  have hs := theW3Kit.specA a b [] [] (qst S f A E D ∘ w3Map theW3Kit.hma ![x, y, z])
    TermOK.nil TermOK.nil (by simpa [w3Map, locMap, qst] using hx)
    (by simpa [w3Map, locMap, qst] using hy)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_call1 hinj lqA hs) ?_)
    (fun _ _ => trivial) le_rfl
  have hz' : (qst S f A E D ∘ w3Map theW3Kit.hma ![x, y, z]) (.inl 2) = [] := by
    simpa [w3Map, locMap, qst] using hz
  rw [hz']
  exact qst_upd_q S f A E D z _

theorem q_sub (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (x y z : QW) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (a b : ℕ) (hba : b ≤ a)
    (hx : f x = natSyms a ++ []) (hy : f y = natSyms b ++ []) (hz : f z = []) :
    Runs (callInj (w3Map theW3Kit.hmb ![x, y, z]) (lqB (Rs := Rs) (Rr := Rr)) theW3Kit.Pb)
      (qst S f A E D) (qst S (Function.update f z (natSyms (a - b) ++ [])) A E D)
      (fun _ => True) (theW3Kit.Cb * (bitLen a + bitLen b + 1)) := by
  have hinj := w3Map_injective (Es := Es) (Er := Er) theW3Kit.hmb _ (inj3 hxy hxz hyz)
  have hs := theW3Kit.specB a b [] [] (qst S f A E D ∘ w3Map theW3Kit.hmb ![x, y, z])
    TermOK.nil TermOK.nil hba (by simpa [w3Map, locMap, qst] using hx)
    (by simpa [w3Map, locMap, qst] using hy)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_call1 hinj lqB hs) ?_)
    (fun _ _ => trivial) le_rfl
  have hz' : (qst S f A E D ∘ w3Map theW3Kit.hmb ![x, y, z]) (.inl 2) = [] := by
    simpa [w3Map, locMap, qst] using hz
  rw [hz']
  exact qst_upd_q S f A E D z _

theorem q_cmp (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (x y : QW) (hxy : x ≠ y) (a b : ℕ) (hx : f x = natSyms a ++ []) (hy : f y = natSyms b ++ []) :
    Runs (callInj (w3Map theW3Kit.hmc ![x, y]) (lqC (Rs := Rs) (Rr := Rr)) theW3Kit.Pc)
      (qst S f A E D) (qst S f A E D)
      (fun v => theW3Kit.obs ((lqC (Rs := Rs) (Rr := Rr)).get v) = Lib.ordOf a b)
      (theW3Kit.Cc * (bitLen a + bitLen b + 1)) := by
  have hinj := w3Map_injective (Es := Es) (Er := Er) theW3Kit.hmc _ (inj2 hxy)
  have hs := theW3Kit.specC a b [] [] (qst S f A E D ∘ w3Map theW3Kit.hmc ![x, y])
    TermOK.nil TermOK.nil (by simpa [w3Map, locMap, qst] using hx)
    (by simpa [w3Map, locMap, qst] using hy)
  exact runs_call0 hinj lqC hs

end Steps

/-! ## The AR shift kernels -/

/-- The specification shape of the `Fin 5` coefficientwise shift kernels of
`Contracts/Arith.lean` (`TruncShiftStmt`, `RoundHalfUpShiftStmt`, `ShlStmt`), with integer map
`g s`. -/
def ShiftSpec {E' R' : Type} [DecidableEq E'] (g : ℕ → CInt → CInt) (C : ℕ)
    (P : Prog (KLoc (Fin 5) E') (fun _ => Sym) R') : Prop :=
  ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
    (S : KLoc (Fin 5) E' → List Sym),
    1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (g s) v) →
    BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
    S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
    Runs P S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w2 (mapC (g s) v) ++ S (.inl 1)))
      (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

section Kernels

variable {Es Er Rs Rr : Type} [DecidableEq Es] [DecidableEq Er]

omit [DecidableEq Es] [DecidableEq Er] in
theorem arMap_injective {E' : Type} (scr : E' → KLoc BrK (QE Es Er))
    (hscr : Function.Injective scr) (hdisj : ∀ (i : Fin 5) (e : E'),
      (![kW .arr, kN .dst, qL .NI, qL .NO, qL .NS] : Fin 5 → KLoc BrK (QE Es Er)) i ≠ scr e) :
    Function.Injective (arMap scr) := by
  rintro (a | a) (b | b) h <;> simp only [arMap, Sum.elim_inl, Sum.elim_inr] at h
  · congr 1
    fin_cases a <;> fin_cases b <;> simp_all
  · exact absurd h (hdisj a b)
  · exact absurd h.symm (hdisj b a)
  · rw [hscr h]

theorem q_kernel {E' R' : Type} [DecidableEq E'] (scr : E' → KLoc BrK (QE Es Er))
    (hscr : Function.Injective scr) (hdisj : ∀ (i : Fin 5) (e : E'),
      (![kW .arr, kN .dst, qL .NI, qL .NO, qL .NS] : Fin 5 → KLoc BrK (QE Es Er)) i ≠ scr e)
    (l : Lens (QReg Rs Rr) R') (g : ℕ → CInt → CInt) (C : ℕ)
    (P : Prog (KLoc (Fin 5) E') (fun _ => Sym) R') (hP : ShiftSpec g C P)
    (S : KLoc BrK (QE Es Er) → List Sym) (f : QW → List Sym) (A E D : List Sym)
    (w1 w2 s : ℕ) (v : List (List CInt)) (rest : List Sym) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hv1 : CArrFits w1 v) (hv2 : CArrFits w2 (mapC (g s) v)) (hrest : BlkTerm rest)
    (hA : A = carrSyms w1 v ++ rest) (hI : f .NI = natSyms w1 ++ [])
    (hO : f .NO = natSyms w2 ++ []) (hS : f .NS = natSyms s ++ []) :
    Runs (callInj (arMap scr) l P) (qst S f A E D)
      (qst S f rest E (carrSyms w2 (mapC (g s) v) ++ D)) (fun _ => True)
      (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1)) := by
  have hinj := arMap_injective scr hscr hdisj
  have hs := hP w1 w2 s v rest [] [] [] (qst S f A E D ∘ arMap scr) hw1 hw2 hv1 hv2 hrest
    TermOK.nil TermOK.nil TermOK.nil (by simpa [arMap, qst] using hA)
    (by simpa [arMap, qst] using hI) (by simpa [arMap, qst] using hO)
    (by simpa [arMap, qst] using hS)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_call2 hinj l hs) ?_)
    (fun _ _ => trivial) le_rfl
  have e0 : arMap scr (.inl 0) = (kW .arr : KLoc BrK (QE Es Er)) := rfl
  have e1 : arMap scr (.inl 1) = (kN .dst : KLoc BrK (QE Es Er)) := rfl
  have e2 : (qst S f A E D ∘ arMap scr) (.inl 1) = D := rfl
  rw [e0, e1, e2, qst_upd_arr, qst_upd_dst]

theorem esL_disj (i : Fin 5) (e : Es) :
    (![kW .arr, kN .dst, qL .NI, qL .NO, qL .NS] : Fin 5 → KLoc BrK (QE Es Er)) i ≠ esL e := by
  fin_cases i <;> simp

theorem erL_disj (i : Fin 5) (e : Er) :
    (![kW .arr, kN .dst, qL .NI, qL .NO, qL .NS] : Fin 5 → KLoc BrK (QE Es Er)) i ≠ erL e := by
  fin_cases i <;> simp

theorem esL_injective : Function.Injective (esL (Es := Es) (Er := Er)) := by
  intro a b h; simpa using h

theorem erL_injective : Function.Injective (erL (Es := Es) (Er := Er)) := by
  intro a b h; simpa using h

end Kernels

/-! ## The program -/

section Prog

variable {Es Er Rs Rr : Type}

/-- Branch `q > X`: `s := q - X`, half-up right shift, drop `s`. -/
noncomputable def postBrGt (_Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs)
    (Pr : Prog (KLoc (Fin 5) Er) (fun _ => Sym) Rr) :
    Prog (KLoc BrK (QE Es Er)) (fun _ => Sym) (QReg Rs Rr) :=
  .seq (callInj (w3Map theW3Kit.hmb ![QW.NP, QW.NX, QW.NS]) lqB theW3Kit.Pb)
    (.seq (callInj (arMap erL) lqR Pr) ((WP.W3.dropNum (qL .NS)).liftRegs lq0))

/-- Branch `q ≤ X`: `s := X - q`, exact left shift, drop `s`. -/
noncomputable def postBrLe (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs)
    (_Pr : Prog (KLoc (Fin 5) Er) (fun _ => Sym) Rr) :
    Prog (KLoc BrK (QE Es Er)) (fun _ => Sym) (QReg Rs Rr) :=
  .seq (callInj (w3Map theW3Kit.hmb ![QW.NX, QW.NP, QW.NS]) lqB theW3Kit.Pb)
    (.seq (callInj (arMap esL) lqS Ps) ((WP.W3.dropNum (qL .NS)).liftRegs lq0))

/-- The non-empty case of the post part. -/
noncomputable def postMain (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs)
    (Pr : Prog (KLoc (Fin 5) Er) (fun _ => Sym) Rr) :
    Prog (KLoc BrK (QE Es Er)) (fun _ => Sym) (QReg Rs Rr) :=
  .seq ((fetchField (kN .par) (qL .G) (qL .U) (qL .NP) 1).liftRegs lq0)
  (.seq ((fetchField (kN .par) (qL .G) (qL .U) (qL .Np) 0).liftRegs lq0)
  (.seq ((fetchField (kN .par) (qL .G) (qL .U) (qL .NI) 3).liftRegs lq0)
  (.seq ((fetchField (kN .par) (qL .G) (qL .U) (qL .NO) 5).liftRegs lq0)
  (.seq ((copyBlock (kW .ex) (qL .NE) (qL .U)).liftRegs lq0)
  (.seq ((inc (qL .NP) (qL .U)).liftRegs lq0)
  (.seq ((inc (qL .NP) (qL .U)).liftRegs lq0)
  (.seq (callInj (w3Map theW3Kit.hma ![QW.Np, QW.NE, QW.NX]) lqA theW3Kit.Pa)
  (.seq ((inc (qL .NX) (qL .U)).liftRegs lq0)
  (.seq ((inc (qL .NX) (qL .U)).liftRegs lq0)
  (.seq (.seq (callInj (w3Map theW3Kit.hmc ![QW.NP, QW.NX]) lqC theW3Kit.Pc)
      (.ite (fun v => decide (theW3Kit.obs (lqC.get v) = .gt)) (postBrGt Ps Pr)
        (postBrLe Ps Pr)))
  (.seq ((WP.W3.dropNum (qL .NP)).liftRegs lq0)
  (.seq ((WP.W3.dropNum (qL .Np)).liftRegs lq0)
  (.seq ((WP.W3.dropNum (qL .NI)).liftRegs lq0)
  (.seq ((WP.W3.dropNum (qL .NO)).liftRegs lq0)
  (.seq ((WP.W3.dropNum (qL .NE)).liftRegs lq0)
  (.seq ((WP.W3.dropNum (qL .NX)).liftRegs lq0)
    ((WP.W3.dropNum (kW .ex)).liftRegs lq0)))))))))))))))))

/-- **The post program**: test `arr` for emptiness first. -/
noncomputable def postProg (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs)
    (Pr : Prog (KLoc (Fin 5) Er) (fun _ => Sym) Rr) :
    Prog (KLoc BrK (QE Es Er)) (fun _ => Sym) (QReg Rs Rr) :=
  .seq ((peekR (kW .arr)).liftRegs lq0)
    (.ite (fun v => optIsBit (lq0.get v)) (postMain Ps Pr) ((WP.W3.dropNum (kW .ex)).liftRegs lq0))

end Prog


/-! ## Correctness -/

/-- Values of the own work stacks. -/
def fP (vP vp vI vO vE vX vS : List Sym) : QW → List Sym
  | .G => []
  | .U => []
  | .NP => vP
  | .Np => vp
  | .NI => vI
  | .NO => vO
  | .NE => vE
  | .NX => vX
  | .NS => vS

section FP

variable (vP vp vI vO vE vX vS w : List Sym)

theorem fP_nil : (fun _ : QW => ([] : List Sym)) = fP [] [] [] [] [] [] [] := by
  funext y; cases y <;> rfl
theorem upd_fP_NP : Function.update (fP vP vp vI vO vE vX vS) .NP w = fP w vp vI vO vE vX vS := by
  funext y; cases y <;> rfl
theorem upd_fP_Np : Function.update (fP vP vp vI vO vE vX vS) .Np w = fP vP w vI vO vE vX vS := by
  funext y; cases y <;> rfl
theorem upd_fP_NI : Function.update (fP vP vp vI vO vE vX vS) .NI w = fP vP vp w vO vE vX vS := by
  funext y; cases y <;> rfl
theorem upd_fP_NO : Function.update (fP vP vp vI vO vE vX vS) .NO w = fP vP vp vI w vE vX vS := by
  funext y; cases y <;> rfl
theorem upd_fP_NE : Function.update (fP vP vp vI vO vE vX vS) .NE w = fP vP vp vI vO w vX vS := by
  funext y; cases y <;> rfl
theorem upd_fP_NX : Function.update (fP vP vp vI vO vE vX vS) .NX w = fP vP vp vI vO vE w vS := by
  funext y; cases y <;> rfl
theorem upd_fP_NS : Function.update (fP vP vp vI vO vE vX vS) .NS w = fP vP vp vI vO vE vX w := by
  funext y; cases y <;> rfl

end FP

theorem ordOf_eq_gt_iff (a b : ℕ) : Lib.ordOf a b = .gt ↔ b < a := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp_all <;> omega

theorem bitLen_field_le (fs1 : List ℕ) (a : ℕ) (fs2 : List ℕ) :
    bitLen a ≤ (hdrSyms (fs1 ++ a :: fs2)).length := by
  rw [hdrSyms_append, List.length_append, length_hdrSyms_cons]
  omega

theorem bitLen_mono2 {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  rw [bitLen_le_iff']
  exact lt_of_le_of_lt h (lt_two_pow_bitLen b)

theorem bitLen_succ_le (n : ℕ) : bitLen (n + 1) ≤ bitLen n + 1 := by
  rw [bitLen_le_iff']
  have := lt_two_pow_bitLen n
  rw [pow_succ]
  omega

/-- The arithmetic of the post part's cost bound. -/
theorem post_cost_le (Ca Cb Cc Cs Cr N wI wO e Hd bP bP1 bA bp be bpe bpe1 bX bI bO cv : ℕ)
    (hN : wI + wO + 1 ≤ N) (hbP : bP ≤ Hd) (hbP1 : bP1 ≤ bP + 1) (hbA : bA ≤ bP + 2)
    (hbp : bp ≤ Hd) (hbe : be ≤ e) (hbpe : bpe ≤ bp + be + 1) (hbpe1 : bpe1 ≤ bpe + 1)
    (hbX : bX ≤ bpe1 + 1) (hbI : bI ≤ Hd) (hbO : bO ≤ Hd) (hcv : cv ≤ 3 * N) :
    36 * Hd + 44 + (7 * be + 7) + (6 * bP + 9) + (6 * bP1 + 9) + Ca * (bp + be + 1) +
      (6 * bpe + 9) + (6 * bpe1 + 9) + Cc * (bA + bX + 1) +
      (Cb * (bA + bX + 1) + (Cs + Cr) * (cv + wI + wO + (bA + bX) + 1) + (2 * (bA + bX) + 4)) +
      1 + (2 * bA + 4) + (2 * bp + 4) + (2 * bI + 4) + (2 * bO + 4) + (2 * be + 4) +
      (2 * bX + 4) + (2 * be + 4) ≤
      400 * (Ca + Cb + Cc + Cs + Cr + 1) * (N + e + Hd + 1) := by
  have hM : bA + bX + 1 ≤ 10 * (N + e + Hd + 1) := by omega
  have hM2 : bp + be + 1 ≤ 10 * (N + e + Hd + 1) := by omega
  have hM3 : cv + wI + wO + (bA + bX) + 1 ≤ 14 * (N + e + Hd + 1) := by omega
  have h1 := Nat.mul_le_mul_left Ca hM2
  have h2 := Nat.mul_le_mul_left Cc hM
  have h3 := Nat.mul_le_mul_left Cb hM
  have h4 := Nat.mul_le_mul_left (Cs + Cr) hM3
  have hL : 36 * Hd + 44 + (7 * be + 7) + (6 * bP + 9) + (6 * bP1 + 9) + (6 * bpe + 9) +
      (6 * bpe1 + 9) + (2 * (bA + bX) + 4) + 1 + (2 * bA + 4) + (2 * bp + 4) + (2 * bI + 4) +
      (2 * bO + 4) + (2 * be + 4) + (2 * bX + 4) + (2 * be + 4) ≤ 200 * (N + e + Hd + 1) := by
    omega
  have hsum : 200 * (N + e + Hd + 1) + Ca * (10 * (N + e + Hd + 1)) +
      Cc * (10 * (N + e + Hd + 1)) + Cb * (10 * (N + e + Hd + 1)) +
      (Cs + Cr) * (14 * (N + e + Hd + 1)) =
      (200 + 10 * Ca + 10 * Cc + 10 * Cb + 14 * (Cs + Cr)) * (N + e + Hd + 1) := by ring
  have hfin : (200 + 10 * Ca + 10 * Cc + 10 * Cb + 14 * (Cs + Cr)) * (N + e + Hd + 1) ≤
      400 * (Ca + Cb + Cc + Cs + Cr + 1) * (N + e + Hd + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  linarith

/-- The cost constant of the post part. -/
noncomputable def postK (Cs Cr : ℕ) : ℕ :=
  400 * (theW3Kit.Ca + theW3Kit.Cb + theW3Kit.Cc + Cs + Cr + 1)

section Main

variable {Es Er Rs Rr : Type} [DecidableEq Es] [DecidableEq Er]

/-- **The non-empty case of the post part.** -/
theorem runs_postMain (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs)
    (Pr : Prog (KLoc (Fin 5) Er) (fun _ => Sym) Rr) (Cs Cr : ℕ)
    (hPs : ShiftSpec shlC Cs Ps) (hPr : ShiftSpec roundHalfUpShiftC Cr Pr)
    (b : BrPar) (Z : Fin (totalLen b.t) → ℂ) (e : ℕ) (rarr rex rpar : List Sym)
    (S : KLoc BrK (QE Es Er) → List Sym) (hclean : KClean S) (hwI : 1 ≤ b.wI)
    (hwO : 1 ≤ b.wOut) (hgrid : ∀ f, OnGrid (b.P + 2) (Z f))
    (hfitI : ArrFits b.wI (b.P + 2) Z)
    (hfitO : ArrFits b.wOut (b.p + 2) (fun f => crnd roundHalfUpR (b.p + 2) ((2 : ℂ) ^ e * Z f)))
    (hrarr : BlkTerm rarr) (hrex : TermOK rex) (hR : 0 < totalLen b.t)
    (harr : S (kW .arr) = carrSyms b.wI (encVec (b.P + 2) Z) ++ rarr)
    (hex : S (kW .ex) = natSyms e ++ rex) (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (postMain Ps Pr) S
      (Function.update (Function.update (Function.update S (kW .arr) rarr) (kW .ex) rex) (kN .dst)
        (carrSyms b.wOut (encVec (b.p + 2)
          (fun f => crnd roundHalfUpR (b.p + 2) ((2 : ℂ) ^ e * Z f))) ++ S (kN .dst)))
      (fun _ => True)
      (postK Cs Cr * (totalLen b.t * (b.wI + b.wOut + 1) + e + (hdrSyms b.hdr).length + 1)) := by
  set v := encVec (b.P + 2) Z with hv
  set out := encVec (b.p + 2) (fun f => crnd roundHalfUpR (b.p + 2) ((2 : ℂ) ^ e * Z f)) with hout
  set A0 := S (kW .arr) with hA0
  set E0 := S (kW .ex) with hE0
  set D0 := S (kN .dst) with hD0
  have hS0 : S = qst S (fP [] [] [] [] [] [] []) A0 E0 D0 := by
    rw [← fP_nil]; exact (qst_self S hclean).symm
  -- header
  have hs1 : [b.p] ++ b.P :: ([b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
  have hs0 : [] ++ b.p :: ([b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
  have hs3 : [b.p, b.P, b.ω] ++ b.wI :: ([b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
  have hs5 : [b.p, b.P, b.ω, b.wI, b.wT] ++ b.wOut :: ([b.pIn, b.wIn, b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
  have hp1 : S (kN .par) = hdrSyms ([b.p] ++ b.P :: ([b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++
      List.ofFn b.t)) ++ rpar := by rw [hs1]; exact hpar
  have hp0 : S (kN .par) = hdrSyms ([] ++ b.p :: ([b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++
      List.ofFn b.t)) ++ rpar := by rw [hs0]; exact hpar
  have hp3 : S (kN .par) = hdrSyms ([b.p, b.P, b.ω] ++ b.wI :: ([b.wT, b.wOut, b.pIn, b.wIn, b.d] ++
      List.ofFn b.t)) ++ rpar := by rw [hs3]; exact hpar
  have hp5 : S (kN .par) = hdrSyms ([b.p, b.P, b.ω, b.wI, b.wT] ++ b.wOut :: ([b.pIn, b.wIn, b.d] ++
      List.ofFn b.t)) ++ rpar := by rw [hs5]; exact hpar
  have r1 := q_fetch (Rs := Rs) (Rr := Rr) S (fP [] [] [] [] [] [] []) A0 E0 D0 .NP (by decide)
    (by decide) rfl [b.p] b.P _ rpar hp1
  rw [upd_fP_NP] at r1
  have r2 := q_fetch (Rs := Rs) (Rr := Rr) S (fP (natSyms b.P ++ []) [] [] [] [] [] []) A0 E0 D0
    .Np (by decide) (by decide) rfl [] b.p _ rpar hp0
  rw [upd_fP_Np] at r2
  have r3 := q_fetch (Rs := Rs) (Rr := Rr) S (fP (natSyms b.P ++ []) (natSyms b.p ++ []) [] [] []
    [] []) A0 E0 D0 .NI (by decide) (by decide) rfl [b.p, b.P, b.ω] b.wI _ rpar hp3
  rw [upd_fP_NI] at r3
  have r4 := q_fetch (Rs := Rs) (Rr := Rr) S (fP (natSyms b.P ++ []) (natSyms b.p ++ [])
    (natSyms b.wI ++ []) [] [] [] []) A0 E0 D0 .NO (by decide) (by decide) rfl
    [b.p, b.P, b.ω, b.wI, b.wT] b.wOut _ rpar hp5
  rw [upd_fP_NO] at r4
  have r5 := q_copyE (Rs := Rs) (Rr := Rr) S (fP (natSyms b.P ++ []) (natSyms b.p ++ [])
    (natSyms b.wI ++ []) (natSyms b.wOut ++ []) [] [] []) A0 E0 D0 rfl e rex hrex hex
  rw [upd_fP_NE] at r5
  have r6 := q_inc (Rs := Rs) (Rr := Rr) S (fP (natSyms b.P ++ []) (natSyms b.p ++ [])
    (natSyms b.wI ++ []) (natSyms b.wOut ++ []) (natSyms e ++ []) [] []) A0 E0 D0 .NP (by decide)
    b.P rfl
  rw [upd_fP_NP] at r6
  have r7 := q_inc (Rs := Rs) (Rr := Rr) S (fP (natSyms (b.P + 1) ++ []) (natSyms b.p ++ [])
    (natSyms b.wI ++ []) (natSyms b.wOut ++ []) (natSyms e ++ []) [] []) A0 E0 D0 .NP (by decide)
    (b.P + 1) rfl
  rw [upd_fP_NP] at r7
  have r8 := q_add (Rs := Rs) (Rr := Rr) S (fP (natSyms (b.P + 1 + 1) ++ []) (natSyms b.p ++ [])
    (natSyms b.wI ++ []) (natSyms b.wOut ++ []) (natSyms e ++ []) [] []) A0 E0 D0 .Np .NE .NX
    (by decide) (by decide) (by decide) b.p e rfl rfl rfl
  rw [upd_fP_NX] at r8
  have r9 := q_inc (Rs := Rs) (Rr := Rr) S (fP (natSyms (b.P + 1 + 1) ++ []) (natSyms b.p ++ [])
    (natSyms b.wI ++ []) (natSyms b.wOut ++ []) (natSyms e ++ []) (natSyms (b.p + e) ++ []) [])
    A0 E0 D0 .NX (by decide) (b.p + e) rfl
  rw [upd_fP_NX] at r9
  have r10 := q_inc (Rs := Rs) (Rr := Rr) S (fP (natSyms (b.P + 1 + 1) ++ []) (natSyms b.p ++ [])
    (natSyms b.wI ++ []) (natSyms b.wOut ++ []) (natSyms e ++ []) (natSyms (b.p + e + 1) ++ []) [])
    A0 E0 D0 .NX (by decide) (b.p + e + 1) rfl
  rw [upd_fP_NX] at r10
  set bA := b.P + 1 + 1 with hbA
  set bX := b.p + e + 1 + 1 with hbX
  set f10 := fP (natSyms bA ++ []) (natSyms b.p ++ []) (natSyms b.wI ++ [])
    (natSyms b.wOut ++ []) (natSyms e ++ []) (natSyms bX ++ []) [] with hf10
  have r11 := q_cmp (Rs := Rs) (Rr := Rr) S f10 A0 E0 D0 .NP .NX (by decide) bA bX rfl rfl
  set Dfin := carrSyms b.wOut out ++ D0 with hDfin
  have hcvI : cvol b.wI v = totalLen b.t * (2 * b.wI + 1) := cvol_encVec _ _ _
  have hcvO : cvol b.wOut out = totalLen b.t * (2 * b.wOut + 1) := cvol_encVec _ _ _
  have hcvV : cvol b.wOut v = totalLen b.t * (2 * b.wOut + 1) := cvol_encVec _ _ _
  set Tbr := theW3Kit.Cb * (bitLen bA + bitLen bX + 1) +
    (Cs + Cr) * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (2 * b.wOut + 1) + b.wI + b.wOut +
      (bitLen bA + bitLen bX) + 1) + (2 * (bitLen bA + bitLen bX) + 4) with hTbr
  have hbr1 : decide (Lib.ordOf bA bX = .gt) = true →
      Runs (postBrGt Ps Pr) (qst S f10 A0 E0 D0) (qst S f10 rarr E0 Dfin) (fun _ => True)
        Tbr := by
    intro hd
    have hlt : bX < bA := (ordOf_eq_gt_iff bA bX).1 (of_decide_eq_true hd)
    have rs := q_sub (Rs := Rs) (Rr := Rr) S f10 A0 E0 D0 .NP .NX .NS (by decide) (by decide)
      (by decide) bA bX hlt.le rfl rfl rfl
    rw [upd_fP_NS] at rs
    have hval : mapC (roundHalfUpShiftC (bA - bX)) v = out := by
      rw [hout, hv, post_encVec b.P b.p e Z hgrid, postScaleInt_of_gt (by omega)]
      congr 2
      omega
    have rk := q_kernel (Rs := Rs) (Rr := Rr) erL erL_injective erL_disj lqR roundHalfUpShiftC Cr Pr hPr S
      (fP (natSyms bA ++ []) (natSyms b.p ++ []) (natSyms b.wI ++ []) (natSyms b.wOut ++ [])
        (natSyms e ++ []) (natSyms bX ++ []) (natSyms (bA - bX) ++ [])) A0 E0 D0 b.wI b.wOut
      (bA - bX) v rarr hwI hwO (BridgeRed.cArrFits_encVec _ _ _ hfitI)
      (by rw [hval]; exact BridgeRed.cArrFits_encVec _ _ _ hfitO) hrarr harr rfl rfl rfl
    rw [hval] at rk
    have rd := q_drop (Rs := Rs) (Rr := Rr) S (fP (natSyms bA ++ []) (natSyms b.p ++ [])
      (natSyms b.wI ++ []) (natSyms b.wOut ++ []) (natSyms e ++ []) (natSyms bX ++ [])
      (natSyms (bA - bX) ++ [])) rarr E0 (carrSyms b.wOut out ++ D0) .NS (bA - bX) rfl
    rw [upd_fP_NS] at rd
    refine WP.W9comp.runs_mono (WP.W9comp.runs_seq rs (WP.W9comp.runs_seq rk rd))
      (fun _ _ => trivial) ?_
    have h1 : bitLen (bA - bX) ≤ bitLen bA := bitLen_mono2 (Nat.sub_le _ _)
    have h2 : Cr * (cvol b.wI v + cvol b.wOut v + b.wI + b.wOut + bitLen (bA - bX) + 1) ≤
        (Cs + Cr) * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (2 * b.wOut + 1) + b.wI +
        b.wOut + (bitLen bA + bitLen bX) + 1) :=
      Nat.mul_le_mul (by omega) (by rw [hcvI, hcvV]; linarith)
    linarith
  have hbr2 : decide (Lib.ordOf bA bX = .gt) = false →
      Runs (postBrLe Ps Pr) (qst S f10 A0 E0 D0) (qst S f10 rarr E0 Dfin) (fun _ => True)
        Tbr := by
    intro hd
    have hle : bA ≤ bX := by
      have := (ordOf_eq_gt_iff bA bX).not.1 (of_decide_eq_false hd)
      omega
    have rs := q_sub (Rs := Rs) (Rr := Rr) S f10 A0 E0 D0 .NX .NP .NS (by decide) (by decide)
      (by decide) bX bA hle rfl rfl rfl
    rw [upd_fP_NS] at rs
    have hval : mapC (shlC (bX - bA)) v = out := by
      rw [hout, hv, post_encVec b.P b.p e Z hgrid, postScaleInt_of_le (by omega)]
      congr 2
      omega
    have rk := q_kernel (Rs := Rs) (Rr := Rr) esL esL_injective esL_disj lqS shlC Cs Ps hPs S
      (fP (natSyms bA ++ []) (natSyms b.p ++ []) (natSyms b.wI ++ []) (natSyms b.wOut ++ [])
        (natSyms e ++ []) (natSyms bX ++ []) (natSyms (bX - bA) ++ [])) A0 E0 D0 b.wI b.wOut
      (bX - bA) v rarr hwI hwO (BridgeRed.cArrFits_encVec _ _ _ hfitI)
      (by rw [hval]; exact BridgeRed.cArrFits_encVec _ _ _ hfitO) hrarr harr rfl rfl rfl
    rw [hval] at rk
    have rd := q_drop (Rs := Rs) (Rr := Rr) S (fP (natSyms bA ++ []) (natSyms b.p ++ [])
      (natSyms b.wI ++ []) (natSyms b.wOut ++ []) (natSyms e ++ []) (natSyms bX ++ [])
      (natSyms (bX - bA) ++ [])) rarr E0 (carrSyms b.wOut out ++ D0) .NS (bX - bA) rfl
    rw [upd_fP_NS] at rd
    refine WP.W9comp.runs_mono (WP.W9comp.runs_seq rs (WP.W9comp.runs_seq rk rd))
      (fun _ _ => trivial) ?_
    have h1 : bitLen (bX - bA) ≤ bitLen bX := bitLen_mono2 (Nat.sub_le _ _)
    have h2 : Cs * (cvol b.wI v + cvol b.wOut v + b.wI + b.wOut + bitLen (bX - bA) + 1) ≤
        (Cs + Cr) * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (2 * b.wOut + 1) + b.wI +
        b.wOut + (bitLen bA + bitLen bX) + 1) :=
      Nat.mul_le_mul (by omega) (by rw [hcvI, hcvV]; linarith)
    linarith
  have hite := runs_seq_ite
    (c := fun v => decide (theW3Kit.obs ((lqC (Rs := Rs) (Rr := Rr)).get v) = .gt))
    (b := decide (Lib.ordOf bA bX = .gt))
    (WP.W9comp.runs_mono r11 (fun v hv => by
      show decide (theW3Kit.obs ((lqC (Rs := Rs) (Rr := Rr)).get v) = .gt) = _
      rw [hv]) le_rfl) hbr1 hbr2
  have d1 := q_drop (Rs := Rs) (Rr := Rr) S f10 rarr E0 Dfin .NP bA rfl
  rw [upd_fP_NP] at d1
  have d2 := q_drop (Rs := Rs) (Rr := Rr) S (fP [] (natSyms b.p ++ []) (natSyms b.wI ++ [])
    (natSyms b.wOut ++ []) (natSyms e ++ []) (natSyms bX ++ []) []) rarr E0 Dfin .Np b.p rfl
  rw [upd_fP_Np] at d2
  have d3 := q_drop (Rs := Rs) (Rr := Rr) S (fP [] [] (natSyms b.wI ++ [])
    (natSyms b.wOut ++ []) (natSyms e ++ []) (natSyms bX ++ []) []) rarr E0 Dfin .NI b.wI rfl
  rw [upd_fP_NI] at d3
  have d4 := q_drop (Rs := Rs) (Rr := Rr) S (fP [] [] [] (natSyms b.wOut ++ [])
    (natSyms e ++ []) (natSyms bX ++ []) []) rarr E0 Dfin .NO b.wOut rfl
  rw [upd_fP_NO] at d4
  have d5 := q_drop (Rs := Rs) (Rr := Rr) S (fP [] [] [] [] (natSyms e ++ [])
    (natSyms bX ++ []) []) rarr E0 Dfin .NE e rfl
  rw [upd_fP_NE] at d5
  have d6 := q_drop (Rs := Rs) (Rr := Rr) S (fP [] [] [] [] [] (natSyms bX ++ []) []) rarr E0 Dfin
    .NX bX rfl
  rw [upd_fP_NX] at d6
  have d7 := q_dropEx (Rs := Rs) (Rr := Rr) S (fP [] [] [] [] [] [] []) rarr E0 Dfin e rex hrex hex
  have hchain := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6 (WP.W9comp.runs_seq r7
    (WP.W9comp.runs_seq r8 (WP.W9comp.runs_seq r9 (WP.W9comp.runs_seq r10
    (WP.W9comp.runs_seq hite (WP.W9comp.runs_seq d1 (WP.W9comp.runs_seq d2
    (WP.W9comp.runs_seq d3 (WP.W9comp.runs_seq d4 (WP.W9comp.runs_seq d5
    (WP.W9comp.runs_seq d6 d7))))))))))))))))
  rw [← hS0] at hchain
  have hfin : Function.update (Function.update (Function.update S (kW .arr) rarr) (kW .ex) rex)
      (kN .dst) (carrSyms b.wOut out ++ S (kN .dst)) =
      qst S (fP [] [] [] [] [] [] []) rarr rex Dfin := by
    conv_lhs => rw [hS0]
    rw [qst_upd_arr, qst_upd_ex, qst_upd_dst]
    rfl
  rw [hfin]
  refine WP.W9comp.runs_mono hchain (fun _ _ => trivial) ?_
  -- cost
  rw [hs1, hs0, hs3, hs5, hTbr]
  have hbP : bitLen b.P ≤ (hdrSyms b.hdr).length := by
    rw [← hs1]; exact bitLen_field_le [b.p] b.P _
  have hbp : bitLen b.p ≤ (hdrSyms b.hdr).length := by
    rw [← hs0]; exact bitLen_field_le [] b.p _
  have hbI : bitLen b.wI ≤ (hdrSyms b.hdr).length := by
    rw [← hs3]; exact bitLen_field_le [b.p, b.P, b.ω] b.wI _
  have hbO : bitLen b.wOut ≤ (hdrSyms b.hdr).length := by
    rw [← hs5]; exact bitLen_field_le [b.p, b.P, b.ω, b.wI, b.wT] b.wOut _
  have hbe : bitLen e ≤ e := bitLen_le_self' e
  have hbP1 : bitLen (b.P + 1) ≤ bitLen b.P + 1 := bitLen_succ_le _
  have hbA' : bitLen bA ≤ bitLen b.P + 2 := by
    have := bitLen_succ_le (b.P + 1); rw [hbA]; omega
  have hbpe : bitLen (b.p + e) ≤ bitLen b.p + bitLen e + 1 := bitLen_add_le _ _
  have hbpe1 : bitLen (b.p + e + 1) ≤ bitLen (b.p + e) + 1 := bitLen_succ_le _
  have hbX' : bitLen bX ≤ bitLen (b.p + e + 1) + 1 := by
    have := bitLen_succ_le (b.p + e + 1); rw [hbX]; omega
  have hRw : b.wI + b.wOut + 1 ≤ totalLen b.t * (b.wI + b.wOut + 1) := Nat.le_mul_of_pos_left _ hR
  have hcv : totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (2 * b.wOut + 1) ≤
      3 * (totalLen b.t * (b.wI + b.wOut + 1)) := by
    have e1 : totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (2 * b.wOut + 1) =
        2 * (totalLen b.t * (b.wI + b.wOut + 1)) := by ring
    rw [e1]
    exact Nat.mul_le_mul_right _ (by norm_num)
  refine le_trans (le_of_eq ?_) (post_cost_le theW3Kit.Ca theW3Kit.Cb theW3Kit.Cc Cs Cr
    (totalLen b.t * (b.wI + b.wOut + 1)) b.wI b.wOut e (hdrSyms b.hdr).length (bitLen b.P)
    (bitLen (b.P + 1)) (bitLen bA) (bitLen b.p) (bitLen e) (bitLen (b.p + e)) (bitLen (b.p + e + 1))
    (bitLen bX) (bitLen b.wI) (bitLen b.wOut)
    (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (2 * b.wOut + 1)) hRw hbP hbP1 hbA' hbp hbe
    hbpe hbpe1 hbX' hbI hbO hcv)
  ring

end Main

/-! ## The contract -/

instance : Fintype QW where
  elems := {.G, .U, .NP, .Np, .NI, .NO, .NE, .NX, .NS}
  complete := by intro x; cases x <;> simp

section Final

variable {Es Er Rs Rr : Type} [DecidableEq Es] [DecidableEq Er]

theorem runs_liftRegsQ {K σ τ : Type} [DecidableEq K] (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun v => Q (l.get v)) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  obtain ⟨v', S''⟩ := s'
  change S'' = S' at hs'
  subst hs'
  refine ⟨⟨l.set v v', S''⟩, t, Eval.liftRegs l e v rfl, ⟨rfl, ?_⟩, ht⟩
  show Q (l.get (l.set v v'))
  rw [l.get_set]
  exact hq

theorem closed_postProg (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs)
    (Pr : Prog (KLoc (Fin 5) Er) (fun _ => Sym) Rr) (hPs : Ps.Closed) (hPr : Pr.Closed) :
    (postProg Ps Pr).Closed := by
  have hl : ∀ {p : SProg (KLoc BrK (QE Es Er))}, p.Closed →
      (p.liftRegs (lq0 (Rs := Rs) (Rr := Rr))).Closed := fun hp => WP.W9comp.closed_liftRegs _ hp
  have hF : ∀ (j : ℕ) (x : QW),
      ((fetchField (kN .par) (qL .G) (qL .U) (qL x) j).liftRegs (lq0 (Rs := Rs) (Rr := Rr))).Closed :=
    fun j x => hl (closed_fetchField _ _ _ _ _)
  have hC : ((copyBlock (kW .ex) (qL .NE) (qL .U)).liftRegs (lq0 (Rs := Rs) (Rr := Rr))).Closed :=
    hl (by simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
      moveBitsDup, dupBody, restoreR, popR, pushR, pushC, skip])
  have hI : ∀ x : QW, ((inc (qL x) (qL .U)).liftRegs (lq0 (Rs := Rs) (Rr := Rr))).Closed :=
    fun x => hl (by simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody, pushC,
      popR, skip, moveBits, moveBitsBody, pushR, restoreR])
  have hD : ∀ k : KLoc BrK (QE Es Er),
      ((WP.W3.dropNum k).liftRegs (lq0 (Rs := Rs) (Rr := Rr))).Closed :=
    fun k => hl (by simp [Prog.Closed, Prog.FreeBelow, WP.W3.dropNum, WP.W3.dropBits, restoreR,
      popR, pushR, skip])
  have hpk : ((peekR (kW .arr : KLoc BrK (QE Es Er))).liftRegs (lq0 (Rs := Rs) (Rr := Rr))).Closed :=
    hl (by simp [Prog.Closed, Prog.FreeBelow, peekR])
  have hgt : (postBrGt Ps Pr).Closed :=
    ⟨closed_callInj _ _ theW3Kit.clB, closed_callInj _ _ hPr, hD _⟩
  have hle : (postBrLe Ps Pr).Closed :=
    ⟨closed_callInj _ _ theW3Kit.clB, closed_callInj _ _ hPs, hD _⟩
  have hmain : (postMain Ps Pr).Closed :=
    ⟨hF 1 .NP, hF 0 .Np, hF 3 .NI, hF 5 .NO, hC, hI .NP, hI .NP, closed_callInj _ _ theW3Kit.clA,
      hI .NX, hI .NX, ⟨closed_callInj _ _ theW3Kit.clC, hgt, hle⟩, hD _, hD _, hD _, hD _, hD _,
      hD _, hD _⟩
  exact ⟨hpk, hmain, hD _⟩

end Final

/-- **[K5] `PostStmt` holds**, from the two AR shift kernels (`Contracts/Arith.lean`). -/
theorem post_holds_of (hShl : ShlStmt) (hRhu : RoundHalfUpShiftStmt) : PostStmt := by
  obtain ⟨Cs, hs⟩ := hShl
  obtain ⟨Cr, hr⟩ := hRhu
  refine ⟨postK Cs Cr + 2, fun _ => ?_⟩
  obtain ⟨Es, iEs1, iEs2, Rs, Ps, hRs1, hRs2, hPsC, hspecS⟩ := hs ()
  obtain ⟨Er, iEr1, iEr2, Rr, Pr, hRr1, hRr2, hPrC, hspecR⟩ := hr ()
  have := hRs1
  have := hRs2
  have := hRr1
  have := hRr2
  have := theW3Kit.finA
  have := theW3Kit.neA
  have := theW3Kit.finB
  have := theW3Kit.neB
  have := theW3Kit.finC
  have := theW3Kit.neC
  refine ⟨QE Es Er, inferInstance, inferInstance, QReg Rs Rr, postProg Ps Pr, inferInstance,
    inferInstance, closed_postProg Ps Pr hPsC hPrC, ?_⟩
  intro b Z e rarr rex rpar S hclean hwI hwO hgrid hfitI hfitO he hrarr hrex harr hex hpar
  have hPs : ShiftSpec shlC Cs Ps := hspecS
  have hPr : ShiftSpec roundHalfUpShiftC Cr Pr := hspecR
  have hHd : (hdrSyms b.hdr).length + 1 ≤ b.setup := by
    unfold BrPar.setup
    exact Nat.le_self_pow (by norm_num) _
  have hHd' : (hdrSyms b.hdr).length + 1 ≤ b.setup := hHd
  have hpk := runs_liftRegsQ (lq0 (Rs := Rs) (Rr := Rr)) (runs_peekR (kW .arr : KLoc BrK (QE Es Er)) S)
  rcases Nat.eq_zero_or_pos (totalLen b.t) with h0 | hpos
  · -- empty array
    have hv0 : encVec (b.P + 2) Z = [] := List.eq_nil_of_length_eq_zero (by simp [encVec, h0])
    have hw0 : encVec (b.p + 2) (fun f => crnd roundHalfUpR (b.p + 2) ((2 : ℂ) ^ e * Z f)) = [] :=
      List.eq_nil_of_length_eq_zero (by simp [encVec, h0])
    have harr0 : S (kW .arr) = rarr := by rw [harr, hv0]; rfl
    have hc : optIsBit (S (kW .arr)).head? = false := by rw [harr0]; exact optIsBit_of_blkTerm hrarr
    have hd := runs_liftRegs (lq0 (Rs := Rs) (Rr := Rr))
      (runs_dropNum (k := (kW .ex : KLoc BrK (QE Es Er))) e rex S hrex hex)
    have hall := runs_seq_ite (c := fun v => optIsBit ((lq0 (Rs := Rs) (Rr := Rr)).get v))
      (A := postMain Ps Pr) (A' := (WP.W3.dropNum (kW .ex)).liftRegs lq0) (b := false)
      (WP.W9comp.runs_mono hpk (fun v hv => by
        show optIsBit ((lq0 (Rs := Rs) (Rr := Rr)).get v) = _
        rw [hv]; exact hc) le_rfl)
      (fun h => absurd h (by decide)) (fun _ => hd)
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
    · rw [hw0]
      have hc0 : carrSyms b.wOut ([] : List (List CInt)) = [] := rfl
      rw [hc0, List.nil_append, ← harr0, Function.update_eq_self]
      funext k
      by_cases hk1 : k = kN .dst
      · subst hk1; simp
      · rw [Function.update_of_ne hk1]
    · have hbe := bitLen_le_self' e
      have hE6 : 6 ≤ eBound b := by unfold eBound; omega
      have hK : 3 ≤ postK Cs Cr + 2 := by unfold postK; omega
      have h3 : 3 * eBound b ≤
          (postK Cs Cr + 2) * (b.R * (b.wI + b.wOut + 1) + eBound b + b.setup) :=
        Nat.mul_le_mul hK (by omega)
      unfold postCost
      omega
  · -- non-empty array
    have hc : optIsBit (S (kW .arr)).head? = true := by
      rw [harr]; exact optIsBit_carrSyms_encVec hwI hpos Z rarr
    have hm := runs_postMain Ps Pr Cs Cr hPs hPr b Z e rarr rex rpar S hclean hwI hwO hgrid hfitI
      hfitO hrarr hrex hpos harr hex hpar
    have hall := runs_seq_ite (c := fun v => optIsBit ((lq0 (Rs := Rs) (Rr := Rr)).get v))
      (A := postMain Ps Pr) (A' := (WP.W3.dropNum (kW .ex)).liftRegs lq0) (b := true)
      (WP.W9comp.runs_mono hpk (fun v hv => by
        show optIsBit ((lq0 (Rs := Rs) (Rr := Rr)).get v) = _
        rw [hv]; exact hc) le_rfl)
      (fun _ => hm) (fun h => absurd h (by decide))
    refine WP.W9comp.runs_mono hall (fun _ _ => trivial) ?_
    unfold postCost
    have hM : totalLen b.t * (b.wI + b.wOut + 1) + e + (hdrSyms b.hdr).length + 1 ≤
        totalLen b.t * (b.wI + b.wOut + 1) + eBound b + b.setup := by omega
    have := Nat.mul_le_mul_left (postK Cs Cr) hM
    nlinarith

end SubNLogN.Machine.BridgePP
