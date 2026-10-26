/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanStep

/-!
# Layer driver phase scan: one coefficient (`Machine/Layer/DrvPhaseScanCoef.lean`)

**Scope (honest summary).** The program `coefProg` that transforms one coefficient
`(a, b)` (two `w1`-bit fields on the array) into `gEO e o (a, b)` at width `w2` (pushed, reversed,
on the staging stack `U`), and its exact `Runs` rule `runs_coefProg`; no `sorry`. The pieces:
`runs_rdField` (move `w1` bits to the buffer `Ab`), `runs_lockstep` (`w2` adder steps), then the
buffer moves. Every private stack used is restored.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine Computability

/-! ## Coefficient-phase states -/

/-- Stacks of the coefficient phase: the array, `Ab`, `A2`, `B2`, `I`, `I2`, `Cr`, `U` set, the rest
from `B`. -/
def cS (B : PL → List Sym) (A Ab A2 B2 I I2 Cr U : List Sym) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update B sA A) kAb Ab) kA2 A2) kB2 B2) kI I)
    kI2 I2) kCr Cr) kU U

section CS

variable (B : PL → List Sym) (A Ab A2 B2 I I2 Cr U : List Sym)

@[simp] theorem cS_A : cS B A Ab A2 B2 I I2 Cr U sA = A := by simp [cS]
@[simp] theorem cS_Ab : cS B A Ab A2 B2 I I2 Cr U kAb = Ab := by simp [cS]
@[simp] theorem cS_A2 : cS B A Ab A2 B2 I I2 Cr U kA2 = A2 := by simp [cS]
@[simp] theorem cS_B2 : cS B A Ab A2 B2 I I2 Cr U kB2 = B2 := by simp [cS]
@[simp] theorem cS_I : cS B A Ab A2 B2 I I2 Cr U kI = I := by simp [cS]
@[simp] theorem cS_I2 : cS B A Ab A2 B2 I I2 Cr U kI2 = I2 := by simp [cS]
@[simp] theorem cS_Cr : cS B A Ab A2 B2 I I2 Cr U kCr = Cr := by simp [cS]
@[simp] theorem cS_U : cS B A Ab A2 B2 I I2 Cr U kU = U := by simp [cS]

theorem cS_apply_ne (k : PL) (h1 : k ≠ sA) (h2 : k ≠ kAb) (h3 : k ≠ kA2) (h4 : k ≠ kB2)
    (h5 : k ≠ kI) (h6 : k ≠ kI2) (h7 : k ≠ kCr) (h8 : k ≠ kU) :
    cS B A Ab A2 B2 I I2 Cr U k = B k := by
  simp [cS, Function.update_of_ne, h1, h2, h3, h4, h5, h6, h7, h8]

@[simp] theorem cS_PW1 : cS B A Ab A2 B2 I I2 Cr U kPW1 = B kPW1 := by
  apply cS_apply_ne <;> simp
@[simp] theorem cS_PW2 : cS B A Ab A2 B2 I I2 Cr U kPW2 = B kPW2 := by
  apply cS_apply_ne <;> simp
@[simp] theorem cS_Est : cS B A Ab A2 B2 I I2 Cr U kEst = B kEst := by
  apply cS_apply_ne <;> simp
@[simp] theorem cS_Kc : cS B A Ab A2 B2 I I2 Cr U kKc = B kKc := by
  apply cS_apply_ne <;> simp
@[simp] theorem cS_Tm : cS B A Ab A2 B2 I I2 Cr U kTm = B kTm := by
  apply cS_apply_ne <;> simp

theorem cS_upd_comm (k : PL) (x : List Sym) (h1 : k ≠ sA) (h2 : k ≠ kAb) (h3 : k ≠ kA2)
    (h4 : k ≠ kB2) (h5 : k ≠ kI) (h6 : k ≠ kI2) (h7 : k ≠ kCr) (h8 : k ≠ kU) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) k x =
      cS (Function.update B k x) A Ab A2 B2 I I2 Cr U := by
  simp only [cS]
  rw [Function.update_comm (Ne.symm h8), Function.update_comm (Ne.symm h7),
    Function.update_comm (Ne.symm h6), Function.update_comm (Ne.symm h5),
    Function.update_comm (Ne.symm h4), Function.update_comm (Ne.symm h3),
    Function.update_comm (Ne.symm h2), Function.update_comm (Ne.symm h1)]

@[simp] theorem cS_upd_A (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) sA x = cS B x Ab A2 B2 I I2 Cr U := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem cS_upd_Ab (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kAb x = cS B A x A2 B2 I I2 Cr U := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem cS_upd_A2 (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kA2 x = cS B A Ab x B2 I I2 Cr U := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem cS_upd_B2 (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kB2 x = cS B A Ab A2 x I I2 Cr U := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem cS_upd_I (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kI x = cS B A Ab A2 B2 x I2 Cr U := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem cS_upd_I2 (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kI2 x = cS B A Ab A2 B2 I x Cr U := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem cS_upd_Cr (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kCr x = cS B A Ab A2 B2 I I2 x U := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem cS_upd_U (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kU x = cS B A Ab A2 B2 I I2 Cr x := by
  funext k'; simp only [cS, Function.update_apply]; split_ifs <;> simp_all

theorem cS_upd_Kc (x : List Sym) :
    Function.update (cS B A Ab A2 B2 I I2 Cr U) kKc x =
      cS (Function.update B kKc x) A Ab A2 B2 I I2 Cr U :=
  cS_upd_comm B A Ab A2 B2 I I2 Cr U kKc x (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp)

end CS

/-! ## Moving one symbol, reading a field -/

/-- Move one symbol from `src` to `dst`. -/
def moveOne (src dst : PL) : SProg PL := .seq (popR src) (pushR dst)

theorem closed_moveOne (src dst : PL) : (wk (moveOne src dst)).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, moveOne, popR, pushR])

theorem runs_moveOne {src dst : PL} (h : src ≠ dst) (S : PL → List Sym) (y : Sym)
    (L : List Sym) (hS : S src = y :: L) :
    Runs (wk (moveOne src dst)) S (Function.update (Function.update S src L) dst (y :: S dst))
      (fun _ => True) 2 := by
  refine K1.runs_liftRegs_of_eval pl fun v => ⟨some y, 2, ?_, le_rfl⟩
  have e1 := Eval.pop [] src (fun (_ : Option Sym) o => o) v S
  rw [hS] at e1
  have e2 := Eval.push [] dst (fun r : Option Sym => r.getD .sep) (some y)
    (Function.update S src L)
  rw [Function.update_of_ne h.symm] at e2
  exact Eval.seq e1 e2

/-- Move `w1` symbols (one field) from the array to `Ab`. -/
def rdField : Prog PL (fun _ => Sym) PReg := K1.Rot.nLoop pl kPW1 kKc kTm (wk (moveOne sA kAb))

theorem closed_rdField : rdField.Closed :=
  K1.Rot.closed_nLoop _ _ _ _ (closed_moveOne _ _)

theorem runs_rdField (B : PL → List Sym) (w1 : ℕ) (r1 : List Sym) (hr1 : TermOK r1)
    (hW : B kPW1 = natSyms w1 ++ r1) (X : List Bool) (hX : X.length = w1)
    (rest Ab A2 B2 I I2 Cr U : List Sym) :
    Runs rdField (cS B (X.map Sym.bit ++ rest) Ab A2 B2 I I2 Cr U)
      (cS B rest (X.reverse.map Sym.bit ++ Ab) A2 B2 I I2 Cr U) (fun _ => True)
      (18 * w1 + 13 * bitLen w1 + 12) := by
  set St : ℕ → PL → List Sym := fun j =>
    cS B ((X.drop j).map Sym.bit ++ rest) ((X.take j).reverse.map Sym.bit ++ Ab) A2 B2 I I2 Cr U
    with hSt
  have r := K1.Rot.runs_nLoop pl (ns := kPW1) (Kc := kKc) (t := kTm) (by simp) (by simp)
    (by simp) (wk (moveOne sA kAb)) St w1 r1 hr1 (by simp [hSt, hW]) (by simp [hSt])
    (fun _ => 2) (fun j hj => by
      have hj' : j < X.length := by omega
      have hm := runs_moveOne (src := sA) (dst := kAb) (by simp)
        (Function.update (St j) kKc (natSyms (w1 - (j + 1)) ++ Sym.mark :: St 0 kKc))
        (Sym.bit X[j]) ((X.drop (j + 1)).map Sym.bit ++ rest)
        (by simp only [hSt, cS_upd_Kc, cS_A]; rw [List.drop_eq_getElem_cons hj']; rfl)
      refine WP.W9comp.runs_congr hm ?_
      simp only [hSt, cS_upd_Kc, cS_upd_A, cS_upd_Ab, cS_Ab]
      rw [List.take_succ_eq_append_getElem hj', List.reverse_append]
      rfl)
  have h0 : St 0 = cS B (X.map Sym.bit ++ rest) Ab A2 B2 I I2 Cr U := by simp [hSt]
  have hN : St w1 = cS B rest (X.reverse.map Sym.bit ++ Ab) A2 B2 I I2 Cr U := by
    simp only [hSt, ← hX, List.drop_length, List.take_length, List.map_nil, List.nil_append]
  rw [h0, hN] at r
  refine WP.W9comp.runs_mono r (fun _ h => h) ?_
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

/-! ## The lockstep loop -/

/-- The sign guard below an operand: `neg` for a negative value, `pos` otherwise. -/
def sgOf (z : ℤ) : Sym := if z < 0 then .neg else .pos

theorem sgOf_isBit (z : ℤ) : (sgOf z).isBit = false := by
  unfold sgOf; split_ifs <;> rfl

theorem symBit_head {w : ℕ} (z : ℤ) (j : ℕ) (R : List Sym) :
    symBit (((twosBits w z).drop j).map Sym.bit ++ sgOf z :: R).head? = extBit w z j := by
  unfold extBit
  by_cases hj : j < (twosBits w z).length
  · rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem _ _ hj]
    rfl
  · rw [List.drop_eq_nil_of_le (by omega), List.getD_eq_default _ _ (by omega)]
    unfold sgOf
    split_ifs with h <;> simp [symBit, h]

theorem rdSt_drop {w : ℕ} (z : ℤ) (j : ℕ) (R : List Sym) :
    rdSt (((twosBits w z).drop j).map Sym.bit ++ sgOf z :: R) =
      ((twosBits w z).drop (j + 1)).map Sym.bit ++ sgOf z :: R := by
  unfold rdSt
  by_cases hj : j < (twosBits w z).length
  · rw [List.drop_eq_getElem_cons hj]
    rfl
  · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
    have h : optIsBit (some (sgOf z)) = false := by
      unfold sgOf; split_ifs <;> rfl
    simp [h]

theorem sadd_take_succ (k1 k2 : ℤ) (X Y : List Bool) (j : ℕ) (hX : j < X.length)
    (hY : j < Y.length) :
    sadd k1 k2 0 (X.take (j + 1)) (Y.take (j + 1)) =
      sadd k1 k2 0 (X.take j) (Y.take j) ++
        [decide (sstep k1 k2 (scarry k1 k2 0 (X.take j) (Y.take j)) X[j] Y[j] % 2 = 1)] := by
  rw [List.take_succ_eq_append_getElem hX, List.take_succ_eq_append_getElem hY,
    sadd_snoc k1 k2 0 _ _ _ _ (by simp; omega)]

theorem scarry_take_succ (k1 k2 : ℤ) (X Y : List Bool) (j : ℕ) (hX : j < X.length)
    (hY : j < Y.length) :
    scarry k1 k2 0 (X.take (j + 1)) (Y.take (j + 1)) =
      sstep k1 k2 (scarry k1 k2 0 (X.take j) (Y.take j)) X[j] Y[j] / 2 := by
  rw [List.take_succ_eq_append_getElem hX, List.take_succ_eq_append_getElem hY,
    scarry_snoc k1 k2 0 _ _ _ _ (by simp; omega)]

/-- The stacks after a step, in coefficient-phase form. -/
theorem stepSt_cS (B : PL → List Sym) (A Ab LA LB LI I2 LC LU : List Sym) :
    stepSt (cS B A Ab LA LB LI I2 LC LU) =
      cS B A Ab (rdSt LA) (rdSt LB)
        (.bit (decide (vSI (LB.head?, (B kEst).head?, LC.head?, LA.head?) % 2 = 1)) :: LI) I2
        (.tag (encC (vSR (LB.head?, (B kEst).head?, LC.head?, LA.head?) / 2)
          (vSI (LB.head?, (B kEst).head?, LC.head?, LA.head?) / 2)) :: LC.tail)
        (.bit (decide (vSR (LB.head?, (B kEst).head?, LC.head?, LA.head?) % 2 = 1)) :: LU) := by
  simp only [stepSt, stepRegs, cS_A2, cS_B2, cS_Est, cS_Cr, cS_U, cS_I, cS_upd_A2, cS_upd_B2,
    cS_upd_U, cS_upd_I, cS_upd_Cr]

/-- The lockstep loop: `w2` adder steps. -/
def lockstep : Prog PL (fun _ => Sym) PReg := K1.Rot.nLoop pl kPW2 kKc kTm stepProg

theorem closed_lockstep : lockstep.Closed := K1.Rot.closed_nLoop _ _ _ _ closed_stepProg

/-- **The lockstep loop.** From the operands `a`, `b` (`w1`-bit fields, LSB on top, above their
sign guards), `w2` steps push the real part `re' = kRe·(a, b)` on `U` and the imaginary part on
`I` (both reversed, `w2` bits); the operands keep their unread bits. -/
theorem runs_lockstep (B : PL → List Sym) (w1 w2 : ℕ) (hw1 : 1 ≤ w1) (r2 : List Sym)
    (hr2 : TermOK r2) (hW2 : B kPW2 = natSyms w2 ++ r2) (e : ℕ) (o : Bool) (E0 : List Sym)
    (hE : B kEst = .tag (eoTag e o) :: E0) (a b : ℤ) (ha : FitsTwos w1 a) (hb : FitsTwos w1 b)
    (A Ab A20 B20 I0 I2 C0 U0 : List Sym) :
    Runs lockstep
      (cS B A Ab ((twosBits w1 a).map Sym.bit ++ sgOf a :: A20)
        ((twosBits w1 b).map Sym.bit ++ sgOf b :: B20) I0 I2 (.tag (encC 0 0) :: C0) U0)
      (cS B A Ab (((twosBits w1 a).drop w2).map Sym.bit ++ sgOf a :: A20)
        (((twosBits w1 b).drop w2).map Sym.bit ++ sgOf b :: B20)
        ((twosBits w2 ((kIm e o).1 * a + (kIm e o).2 * b)).reverse.map Sym.bit ++ I0) I2
        (.tag (encC (scarry (kRe e o).1 (kRe e o).2 0 (twosBits w2 a) (twosBits w2 b))
          (scarry (kIm e o).1 (kIm e o).2 0 (twosBits w2 a) (twosBits w2 b))) :: C0)
        ((twosBits w2 ((kRe e o).1 * a + (kRe e o).2 * b)).reverse.map Sym.bit ++ U0))
      (fun _ => True) (28 * w2 + 13 * bitLen w2 + 12) := by
  set SA := twosBits w2 a with hSAd
  set SB := twosBits w2 b with hSBd
  have hlA : SA.length = w2 := K1.length_twosBits _ _
  have hlB : SB.length = w2 := K1.length_twosBits _ _
  have hSA : SA = (List.range w2).map (extBit w1 a) := (map_extBit hw1 ha w2).symm
  have hSB : SB = (List.range w2).map (extBit w1 b) := (map_extBit hw1 hb w2).symm
  set St : ℕ → PL → List Sym := fun j =>
    cS B A Ab (((twosBits w1 a).drop j).map Sym.bit ++ sgOf a :: A20)
      (((twosBits w1 b).drop j).map Sym.bit ++ sgOf b :: B20)
      ((sadd (kIm e o).1 (kIm e o).2 0 (SA.take j) (SB.take j)).reverse.map Sym.bit ++ I0) I2
      (.tag (encC (scarry (kRe e o).1 (kRe e o).2 0 (SA.take j) (SB.take j))
        (scarry (kIm e o).1 (kIm e o).2 0 (SA.take j) (SB.take j))) :: C0)
      ((sadd (kRe e o).1 (kRe e o).2 0 (SA.take j) (SB.take j)).reverse.map Sym.bit ++ U0)
    with hSt
  have r := K1.Rot.runs_nLoop pl (ns := kPW2) (Kc := kKc) (t := kTm) (by simp) (by simp)
    (by simp) stepProg St w2 r2 hr2 (by simp [hSt, hW2]) (by simp [hSt]) (fun _ => 12)
    (fun j hj => by
      have hjA : j < SA.length := by omega
      have hjB : j < SB.length := by omega
      have hA : SA[j] = extBit w1 a j := by simp [hSA]
      have hB : SB[j] = extBit w1 b j := by simp [hSB]
      have hR := scarry_range (kRe_range e o).1 (kRe_range e o).2 0 (SA.take j) (SB.take j)
        (by norm_num)
      have hI := scarry_range (kIm_range e o).1 (kIm_range e o).2 0 (SA.take j) (SB.take j)
        (by norm_num)
      refine WP.W9comp.runs_congr (runs_stepProg _) ?_
      simp only [hSt, cS_upd_Kc, stepSt_cS, Function.update_apply, if_neg (show kEst ≠ kKc by
        simp), hE, List.head?_cons, List.tail_cons, vSR_eq e o _ _ hR hI,
        vSI_eq e o _ _ hR hI, symBit_head, rdSt_drop]
      rw [sadd_take_succ _ _ SA SB j hjA hjB, sadd_take_succ _ _ SA SB j hjA hjB,
        scarry_take_succ _ _ SA SB j hjA hjB, scarry_take_succ _ _ SA SB j hjA hjB, hA, hB]
      simp)
  have h0 : St 0 = cS B A Ab ((twosBits w1 a).map Sym.bit ++ sgOf a :: A20)
      ((twosBits w1 b).map Sym.bit ++ sgOf b :: B20) I0 I2 (.tag (encC 0 0) :: C0) U0 := by
    simp [hSt, sadd, scarry]
  have hN : St w2 = cS B A Ab (((twosBits w1 a).drop w2).map Sym.bit ++ sgOf a :: A20)
      (((twosBits w1 b).drop w2).map Sym.bit ++ sgOf b :: B20)
      ((twosBits w2 ((kIm e o).1 * a + (kIm e o).2 * b)).reverse.map Sym.bit ++ I0) I2
      (.tag (encC (scarry (kRe e o).1 (kRe e o).2 0 (twosBits w2 a) (twosBits w2 b))
        (scarry (kIm e o).1 (kIm e o).2 0 (twosBits w2 a) (twosBits w2 b))) :: C0)
      ((twosBits w2 ((kRe e o).1 * a + (kRe e o).2 * b)).reverse.map Sym.bit ++ U0) := by
    have tA : (twosBits w2 a).take w2 = twosBits w2 a :=
      List.take_of_length_le (by rw [K1.length_twosBits])
    have tB : (twosBits w2 b).take w2 = twosBits w2 b :=
      List.take_of_length_le (by rw [K1.length_twosBits])
    simp only [hSt, hSAd, hSBd, tA, tB, sadd_twosBits, zero_add]
  rw [h0, hN] at r
  refine WP.W9comp.runs_mono r (fun _ h => h) ?_
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

/-! ## One coefficient -/

/-- Push the sign guard of the field on `Ab` (its top bit) onto `k`. -/
def sgPush (k : PL) : Prog PL (fun _ => Sym) PReg :=
  .seq (.peek kAb fun v o => (o, v.2)) (.push k fun v => sgSym v.1)

theorem closed_sgPush (k : PL) : (sgPush k).Closed := by
  simp [sgPush, Prog.Closed, Prog.FreeBelow]

theorem runs_sgPush (k : PL) (S : PL → List Sym) (s : Bool) (L : List Sym)
    (hS : S kAb = .bit s :: L) :
    Runs (sgPush k) S (Function.update S k ((if s then .neg else .pos) :: S k))
      (fun _ => True) 2 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  have e1 := Eval.peek [] kAb (fun (v : PReg) o => (o, v.2)) v stk
  have e2 := Eval.push [] k (fun v : PReg => sgSym v.1) ((stk kAb).head?, v.2) stk
  refine ⟨_, 2, Eval.seq e1 e2, ⟨?_, trivial⟩, le_rfl⟩
  show Function.update stk k (sgSym (stk kAb).head? :: stk k) = _
  rw [hS]
  cases s <;> simp [sgSym]

theorem runs_moveBlock {src dst : PL} (h : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : PL → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs (wk (moveBlock src dst)) S
      (Function.update (Function.update S src rest) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 4) :=
  K1.runs_liftRegs_of_eval pl fun v => ⟨_, _, moveBlock_eval h [] v es rest S hrest hS, le_rfl⟩

theorem closed_moveBlock_lift (src dst : PL) : (wk (moveBlock src dst)).Closed :=
  WP.W9comp.closed_liftRegs _ (by
    simp [Prog.Closed, Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR,
      skip])

/-- The top of a reversed field is its sign. -/
theorem rev_twosBits_cons {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (hz : FitsTwos w z) (R : List Sym) :
    ∃ L, (twosBits w z).reverse.map Sym.bit ++ R = .bit (decide (z < 0)) :: L := by
  rcases List.eq_nil_or_concat (twosBits w z) with h | ⟨L', x, hLx⟩
  · have := K1.length_twosBits w z
    rw [h] at this
    simp at this
    omega
  · rw [List.concat_eq_append] at hLx
    have hx : x = decide (z < 0) := by
      have := Arith.lastD_twosBits hz hw false
      rw [hLx, Arith.lastD_append] at this
      simpa [Arith.lastD] using this
    refine ⟨L'.reverse.map Sym.bit ++ R, ?_⟩
    rw [hLx, hx]
    simp

/-- Read the two fields of a coefficient into `A2`, `B2` (LSB on top, above their sign
guards). -/
def coefRead : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (pushC kAb .mark)) (.seq rdField (.seq (sgPush kA2)
  (.seq (wk (moveBlock kAb kA2)) (.seq rdField (.seq (sgPush kB2)
  (.seq (wk (moveBlock kAb kB2)) (wk (popR kAb))))))))

/-- The adder pass: guard on `I`, initial carry tag, `w2` steps. -/
def coefMid : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (pushC kI .mark)) (.seq (wk (pushC kCr (.tag (encC 0 0)))) lockstep)

/-- Clean up the operands and the carry, and move the imaginary part to `U`. -/
def coefFin : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (popR kCr)) (.seq (wk (K1.dropBits kA2)) (.seq (wk (K1.dropBits kB2))
  (.seq (wk (pushC kI2 .mark)) (.seq (wk (moveBlock kI kI2)) (.seq (wk (popR kI))
  (.seq (wk (moveBlock kI2 kU)) (wk (popR kI2))))))))

/-- **One coefficient.** -/
def coefProg : Prog PL (fun _ => Sym) PReg := .seq coefRead (.seq coefMid coefFin)

theorem closed_coefProg : coefProg.Closed :=
  ⟨⟨K1.Rot.closed_pushC_lift _ _ _, closed_rdField, closed_sgPush _, closed_moveBlock_lift _ _,
    closed_rdField, closed_sgPush _, closed_moveBlock_lift _ _, K1.Rot.closed_popR_lift _ _⟩,
    ⟨K1.Rot.closed_pushC_lift _ _ _, K1.Rot.closed_pushC_lift _ _ _, closed_lockstep⟩,
    ⟨K1.Rot.closed_popR_lift _ _, K1.Rot.closed_dropBits_lift _ _,
    K1.Rot.closed_dropBits_lift _ _, K1.Rot.closed_pushC_lift _ _ _, closed_moveBlock_lift _ _,
    K1.Rot.closed_popR_lift _ _, closed_moveBlock_lift _ _, K1.Rot.closed_popR_lift _ _⟩⟩

/-- Cost bound of one coefficient. -/
def coefCost (w1 w2 : ℕ) : ℕ := 80 * w1 + 50 * w2 + 80

theorem runs_coefRead (B : PL → List Sym) (w1 : ℕ) (hw1 : 1 ≤ w1) (r1 : List Sym)
    (hr1 : TermOK r1) (hW1 : B kPW1 = natSyms w1 ++ r1) (a b : ℤ) (ha : FitsTwos w1 a)
    (hb : FitsTwos w1 b) (rest Ab A2 B2 I I2 Cr U : List Sym) :
    Runs coefRead
      (cS B ((twosBits w1 a).map Sym.bit ++ ((twosBits w1 b).map Sym.bit ++ rest)) Ab A2 B2 I
        I2 Cr U)
      (cS B rest Ab ((twosBits w1 a).map Sym.bit ++ sgOf a :: A2)
        ((twosBits w1 b).map Sym.bit ++ sgOf b :: B2) I I2 Cr U) (fun _ => True)
      (42 * w1 + 26 * bitLen w1 + 38) := by
  set XA := twosBits w1 a with hXA
  set XB := twosBits w1 b with hXB
  have hlA : XA.length = w1 := K1.length_twosBits _ _
  have hlB : XB.length = w1 := K1.length_twosBits _ _
  obtain ⟨LA, hLA⟩ := rev_twosBits_cons hw1 ha (.mark :: Ab)
  obtain ⟨LB, hLB⟩ := rev_twosBits_cons hw1 hb (.mark :: Ab)
  have h1 : Runs (wk (pushC kAb .mark)) (cS B (XA.map Sym.bit ++ (XB.map Sym.bit ++ rest)) Ab A2
      B2 I I2 Cr U) (cS B (XA.map Sym.bit ++ (XB.map Sym.bit ++ rest)) (.mark :: Ab) A2 B2 I I2 Cr
      U) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_pushC pl kAb .mark _) (by simp)
  have h2 := runs_rdField B w1 r1 hr1 hW1 XA hlA (XB.map Sym.bit ++ rest) (.mark :: Ab) A2 B2 I
    I2 Cr U
  have h3 : Runs (sgPush kA2) (cS B (XB.map Sym.bit ++ rest) (XA.reverse.map Sym.bit ++
      .mark :: Ab) A2 B2 I I2 Cr U) (cS B (XB.map Sym.bit ++ rest) (XA.reverse.map Sym.bit ++
      .mark :: Ab) (sgOf a :: A2) B2 I I2 Cr U) (fun _ => True) 2 :=
    WP.W9comp.runs_congr (runs_sgPush kA2 _ (decide (a < 0)) LA (by rw [cS_Ab]; exact hLA))
      (by simp [sgOf])
  have h4 : Runs (wk (moveBlock kAb kA2)) (cS B (XB.map Sym.bit ++ rest) (XA.reverse.map Sym.bit ++
      .mark :: Ab) (sgOf a :: A2) B2 I I2 Cr U) (cS B (XB.map Sym.bit ++ rest) (.mark :: Ab)
      (XA.map Sym.bit ++ sgOf a :: A2) B2 I I2 Cr U) (fun _ => True) (3 * w1 + 4) := by
    have h := runs_moveBlock (src := kAb) (dst := kA2) (by simp) XA.reverse (.mark :: Ab)
      (cS B (XB.map Sym.bit ++ rest) (XA.reverse.map Sym.bit ++ .mark :: Ab) (sgOf a :: A2) B2 I
        I2 Cr U) (TermOK.cons rfl _) (cS_Ab _ _ _ _ _ _ _ _ _)
    rw [List.length_reverse, hlA] at h
    exact WP.W9comp.runs_congr h (by simp)
  have h5 := runs_rdField B w1 r1 hr1 hW1 XB hlB rest (.mark :: Ab) (XA.map Sym.bit ++ sgOf a :: A2)
    B2 I I2 Cr U
  have h6 : Runs (sgPush kB2) (cS B rest (XB.reverse.map Sym.bit ++ .mark :: Ab)
      (XA.map Sym.bit ++ sgOf a :: A2) B2 I I2 Cr U) (cS B rest (XB.reverse.map Sym.bit ++
      .mark :: Ab) (XA.map Sym.bit ++ sgOf a :: A2) (sgOf b :: B2) I I2 Cr U) (fun _ => True) 2 :=
    WP.W9comp.runs_congr (runs_sgPush kB2 _ (decide (b < 0)) LB (by rw [cS_Ab]; exact hLB))
      (by simp [sgOf])
  have h7 : Runs (wk (moveBlock kAb kB2)) (cS B rest (XB.reverse.map Sym.bit ++ .mark :: Ab)
      (XA.map Sym.bit ++ sgOf a :: A2) (sgOf b :: B2) I I2 Cr U) (cS B rest (.mark :: Ab)
      (XA.map Sym.bit ++ sgOf a :: A2) (XB.map Sym.bit ++ sgOf b :: B2) I I2 Cr U)
      (fun _ => True) (3 * w1 + 4) := by
    have h := runs_moveBlock (src := kAb) (dst := kB2) (by simp) XB.reverse (.mark :: Ab)
      (cS B rest (XB.reverse.map Sym.bit ++ .mark :: Ab) (XA.map Sym.bit ++ sgOf a :: A2)
        (sgOf b :: B2) I I2 Cr U) (TermOK.cons rfl _) (cS_Ab _ _ _ _ _ _ _ _ _)
    rw [List.length_reverse, hlB] at h
    exact WP.W9comp.runs_congr h (by simp)
  have h8 : Runs (wk (popR kAb)) (cS B rest (.mark :: Ab) (XA.map Sym.bit ++ sgOf a :: A2)
      (XB.map Sym.bit ++ sgOf b :: B2) I I2 Cr U) (cS B rest Ab (XA.map Sym.bit ++ sgOf a :: A2)
      (XB.map Sym.bit ++ sgOf b :: B2) I I2 Cr U) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_popR pl kAb _) (by simp)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2
    (WP.W9comp.runs_seq h3 (WP.W9comp.runs_seq h4 (WP.W9comp.runs_seq h5
    (WP.W9comp.runs_seq h6 (WP.W9comp.runs_seq h7 h8))))))) (fun _ h => h) ?_
  omega

theorem runs_coefFin (B : PL → List Sym) (dA dB IMl : List Bool) (gA gB cr : Sym)
    (hgA : gA.isBit = false) (hgB : gB.isBit = false) (rest Ab A2 B2 I I2 Cr U : List Sym) :
    Runs coefFin
      (cS B rest Ab (dA.map Sym.bit ++ gA :: A2) (dB.map Sym.bit ++ gB :: B2)
        (IMl.reverse.map Sym.bit ++ .mark :: I) I2 (cr :: Cr) U)
      (cS B rest Ab A2 B2 I I2 Cr (IMl.reverse.map Sym.bit ++ U)) (fun _ => True)
      (2 * dA.length + 2 * dB.length + 6 * IMl.length + 16) := by
  have h12 : Runs (wk (popR kCr)) (cS B rest Ab (dA.map Sym.bit ++ gA :: A2)
      (dB.map Sym.bit ++ gB :: B2) (IMl.reverse.map Sym.bit ++ .mark :: I) I2 (cr :: Cr) U)
      (cS B rest Ab (dA.map Sym.bit ++ gA :: A2) (dB.map Sym.bit ++ gB :: B2)
      (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr U) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_popR pl kCr _) (by simp)
  have h13 : Runs (wk (K1.dropBits kA2)) (cS B rest Ab (dA.map Sym.bit ++ gA :: A2)
      (dB.map Sym.bit ++ gB :: B2) (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr U)
      (cS B rest Ab A2 (dB.map Sym.bit ++ gB :: B2) (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr
      U) (fun _ => True) (2 * dA.length + 2) :=
    WP.W9comp.runs_congr (K1.runs_wk_dropBits pl kA2 dA gA A2
      (cS B rest Ab (dA.map Sym.bit ++ gA :: A2) (dB.map Sym.bit ++ gB :: B2)
        (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr U) hgA (cS_A2 _ _ _ _ _ _ _ _ _))
      (by simp)
  have h14 : Runs (wk (K1.dropBits kB2)) (cS B rest Ab A2 (dB.map Sym.bit ++ gB :: B2)
      (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr U) (cS B rest Ab A2 B2
      (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr U) (fun _ => True) (2 * dB.length + 2) :=
    WP.W9comp.runs_congr (K1.runs_wk_dropBits pl kB2 dB gB B2
      (cS B rest Ab A2 (dB.map Sym.bit ++ gB :: B2) (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr
        U) hgB (cS_B2 _ _ _ _ _ _ _ _ _)) (by simp)
  have h15 : Runs (wk (pushC kI2 .mark)) (cS B rest Ab A2 B2
      (IMl.reverse.map Sym.bit ++ .mark :: I) I2 Cr U) (cS B rest Ab A2 B2
      (IMl.reverse.map Sym.bit ++ .mark :: I) (.mark :: I2) Cr U) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_pushC pl kI2 .mark _) (by simp)
  have h16 : Runs (wk (moveBlock kI kI2)) (cS B rest Ab A2 B2
      (IMl.reverse.map Sym.bit ++ .mark :: I) (.mark :: I2) Cr U) (cS B rest Ab A2 B2 (.mark :: I)
      (IMl.map Sym.bit ++ .mark :: I2) Cr U) (fun _ => True) (3 * IMl.length + 4) := by
    have h := runs_moveBlock (src := kI) (dst := kI2) (by simp) IMl.reverse (.mark :: I)
      (cS B rest Ab A2 B2 (IMl.reverse.map Sym.bit ++ .mark :: I) (.mark :: I2) Cr U)
      (TermOK.cons rfl _) (cS_I _ _ _ _ _ _ _ _ _)
    rw [List.length_reverse] at h
    exact WP.W9comp.runs_congr h (by simp)
  have h17 : Runs (wk (popR kI)) (cS B rest Ab A2 B2 (.mark :: I) (IMl.map Sym.bit ++ .mark :: I2)
      Cr U) (cS B rest Ab A2 B2 I (IMl.map Sym.bit ++ .mark :: I2) Cr U) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_popR pl kI _) (by simp)
  have h18 : Runs (wk (moveBlock kI2 kU)) (cS B rest Ab A2 B2 I (IMl.map Sym.bit ++ .mark :: I2)
      Cr U) (cS B rest Ab A2 B2 I (.mark :: I2) Cr (IMl.reverse.map Sym.bit ++ U))
      (fun _ => True) (3 * IMl.length + 4) := by
    have h := runs_moveBlock (src := kI2) (dst := kU) (by simp) IMl (.mark :: I2)
      (cS B rest Ab A2 B2 I (IMl.map Sym.bit ++ .mark :: I2) Cr U) (TermOK.cons rfl _)
      (cS_I2 _ _ _ _ _ _ _ _ _)
    exact WP.W9comp.runs_congr h (by simp)
  have h19 : Runs (wk (popR kI2)) (cS B rest Ab A2 B2 I (.mark :: I2) Cr
      (IMl.reverse.map Sym.bit ++ U)) (cS B rest Ab A2 B2 I I2 Cr (IMl.reverse.map Sym.bit ++ U))
      (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_popR pl kI2 _) (by simp)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq h12 (WP.W9comp.runs_seq h13
    (WP.W9comp.runs_seq h14 (WP.W9comp.runs_seq h15 (WP.W9comp.runs_seq h16
    (WP.W9comp.runs_seq h17 (WP.W9comp.runs_seq h18 h19))))))) (fun _ h => h) ?_
  omega

theorem runs_coefMid (B : PL → List Sym) (w1 w2 : ℕ) (hw1 : 1 ≤ w1) (r2 : List Sym)
    (hr2 : TermOK r2) (hW2 : B kPW2 = natSyms w2 ++ r2) (e : ℕ) (o : Bool) (E0 : List Sym)
    (hE : B kEst = .tag (eoTag e o) :: E0) (a b : ℤ) (ha : FitsTwos w1 a) (hb : FitsTwos w1 b)
    (rest Ab A2 B2 I I2 Cr U : List Sym) :
    Runs coefMid
      (cS B rest Ab ((twosBits w1 a).map Sym.bit ++ sgOf a :: A2)
        ((twosBits w1 b).map Sym.bit ++ sgOf b :: B2) I I2 Cr U)
      (cS B rest Ab (((twosBits w1 a).drop w2).map Sym.bit ++ sgOf a :: A2)
        (((twosBits w1 b).drop w2).map Sym.bit ++ sgOf b :: B2)
        ((twosBits w2 ((kIm e o).1 * a + (kIm e o).2 * b)).reverse.map Sym.bit ++ .mark :: I) I2
        (.tag (encC (scarry (kRe e o).1 (kRe e o).2 0 (twosBits w2 a) (twosBits w2 b))
          (scarry (kIm e o).1 (kIm e o).2 0 (twosBits w2 a) (twosBits w2 b))) :: Cr)
        ((twosBits w2 ((kRe e o).1 * a + (kRe e o).2 * b)).reverse.map Sym.bit ++ U))
      (fun _ => True) (28 * w2 + 13 * bitLen w2 + 14) := by
  have h9 : Runs (wk (pushC kI .mark)) (cS B rest Ab ((twosBits w1 a).map Sym.bit ++ sgOf a :: A2)
      ((twosBits w1 b).map Sym.bit ++ sgOf b :: B2) I I2 Cr U) (cS B rest Ab
      ((twosBits w1 a).map Sym.bit ++ sgOf a :: A2) ((twosBits w1 b).map Sym.bit ++ sgOf b :: B2)
      (.mark :: I) I2 Cr U) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_pushC pl kI .mark _) (by simp)
  have h10 : Runs (wk (pushC kCr (.tag (encC 0 0)))) (cS B rest Ab
      ((twosBits w1 a).map Sym.bit ++ sgOf a :: A2) ((twosBits w1 b).map Sym.bit ++ sgOf b :: B2)
      (.mark :: I) I2 Cr U) (cS B rest Ab ((twosBits w1 a).map Sym.bit ++ sgOf a :: A2)
      ((twosBits w1 b).map Sym.bit ++ sgOf b :: B2) (.mark :: I) I2 (.tag (encC 0 0) :: Cr) U)
      (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_pushC pl kCr _ _) (by simp)
  have h11 := runs_lockstep B w1 w2 hw1 r2 hr2 hW2 e o E0 hE a b ha hb rest Ab A2 B2
    (.mark :: I) I2 Cr U
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq h9 (WP.W9comp.runs_seq h10 h11))
    (fun _ h => h) ?_
  omega

/-- **One coefficient, exact.** The coefficient `z` (fields of width `w1`) leaves the array and
`gEO e o z` (fields of width `w2`) is pushed, reversed, on `U`; every work stack is restored. -/
theorem runs_coefProg (B : PL → List Sym) (w1 w2 : ℕ) (hw1 : 1 ≤ w1) (r1 r2 : List Sym)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hW1 : B kPW1 = natSyms w1 ++ r1)
    (hW2 : B kPW2 = natSyms w2 ++ r2) (e : ℕ) (o : Bool) (E0 : List Sym)
    (hE : B kEst = .tag (eoTag e o) :: E0) (z : CInt) (hz1 : FitsTwos w1 z.1)
    (hz2 : FitsTwos w1 z.2) (rest Ab A2 B2 I I2 Cr U : List Sym) :
    Runs coefProg (cS B ((coefBits w1 z).map Sym.bit ++ rest) Ab A2 B2 I I2 Cr U)
      (cS B rest Ab A2 B2 I I2 Cr ((coefBits w2 (gEO e o z)).reverse.map Sym.bit ++ U))
      (fun _ => True) (coefCost w1 w2) := by
  obtain ⟨a, b⟩ := z
  simp only at hz1 hz2
  have hA0 : (coefBits w1 (a, b)).map Sym.bit ++ rest =
      (twosBits w1 a).map Sym.bit ++ ((twosBits w1 b).map Sym.bit ++ rest) := by
    simp [coefBits]
  have hU : (coefBits w2 (gEO e o (a, b))).reverse.map Sym.bit ++ U =
      (twosBits w2 ((kIm e o).1 * a + (kIm e o).2 * b)).reverse.map Sym.bit ++
        ((twosBits w2 ((kRe e o).1 * a + (kRe e o).2 * b)).reverse.map Sym.bit ++ U) := by
    simp [coefBits, gEO_eq]
  rw [hA0, hU]
  have h1 := runs_coefRead B w1 hw1 r1 hr1 hW1 a b hz1 hz2 rest Ab A2 B2 I I2 Cr U
  have h2 := runs_coefMid B w1 w2 hw1 r2 hr2 hW2 e o E0 hE a b hz1 hz2 rest Ab A2 B2 I I2 Cr U
  have h3 := runs_coefFin B ((twosBits w1 a).drop w2) ((twosBits w1 b).drop w2)
    (twosBits w2 ((kIm e o).1 * a + (kIm e o).2 * b)) (sgOf a) (sgOf b)
    (.tag (encC (scarry (kRe e o).1 (kRe e o).2 0 (twosBits w2 a) (twosBits w2 b))
      (scarry (kIm e o).1 (kIm e o).2 0 (twosBits w2 a) (twosBits w2 b))))
    (sgOf_isBit a) (sgOf_isBit b) rest Ab A2 B2 I I2 Cr
    ((twosBits w2 ((kRe e o).1 * a + (kRe e o).2 * b)).reverse.map Sym.bit ++ U)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 h3))
    (fun _ h => h) ?_
  have b1 := K1.Rot.bitLen_le_self' w1
  have b2 := K1.Rot.bitLen_le_self' w2
  have d1 : ((twosBits w1 a).drop w2).length ≤ w1 := by simp [K1.length_twosBits]
  have d2 : ((twosBits w1 b).drop w2).length ≤ w1 := by simp [K1.length_twosBits]
  have l3 := K1.length_twosBits w2 ((kIm e o).1 * a + (kIm e o).2 * b)
  unfold coefCost
  omega

end SubNLogN.Machine.Layer.DrvPhaseScanAux
