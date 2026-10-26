/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanMain

/-!
# Layer driver phase scan: the record loop and the whole run (`Machine/Layer/DrvPhaseScanLoop.lean`)

**Scope (honest summary).** The record loop (`triple_mainLoop`, by `K1.triple_loop_list` over the
records) and the exact run of the kernel `phaseProg` (`runs_phaseProg`), with the explicit cost
`phaseCost`; no `sorry`.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability

/-- The record loop. -/
def mainLoop : Prog PL (fun _ => Sym) PReg := .loop (fun v => K1.isRecTop v.1) recBody

theorem closed_mainLoop : mainLoop.Closed := closed_recBody

/-- The cost of record `x` with coefficients `a`. -/
def recCost (S K ρ D w1 w2 x : ℕ) (a : List CInt) : ℕ :=
  addrCost (bitLen (x / S)) (bitLen (ρ + K + D)) + 1 + (a.length * (coefCost w1 w2 + 2) + 1) +
    (6 * bitLen x + 13 * bitLen S + 31)

theorem foldG_phase (S K ρ D c o : ℕ) :
    ∀ (v : List (List CInt)) (x : ℕ) (acc : List (List CInt)),
      K1.foldG (fun x a acc => acc ++ [a.map (gEO (c + selCount S K ρ D x) (decide (o = 1)))])
        x v acc = acc ++ v.mapIdx (fun i a => phaseRec S K ρ D c o (x + i) a)
  | [], _, acc => by simp [K1.foldG]
  | a :: v, x, acc => by
    rw [K1.foldG, foldG_phase S K ρ D c o v (x + 1), List.mapIdx_cons,
      List.append_assoc, List.singleton_append]
    congr 2
    · rw [phaseRec_eq]
      simp [Nat.add_comm]
    · congr 1
      funext i b
      show phaseRec S K ρ D c o (x + 1 + i) b = phaseRec S K ρ D c o (x + (i + 1)) b
      rw [show x + 1 + i = x + (i + 1) by omega]

/-- **The record loop.** -/
theorem triple_mainLoop (B : PL → List Sym) (S K ρ D c o w1 w2 : ℕ) (hS1 : 1 ≤ S) (hK : 1 ≤ K)
    (ho : o ≤ 1) (hw1 : 1 ≤ w1) (hpar : ParOK B S K ρ D c o w1 w2) (v : List (List CInt))
    (hfit : ∀ a ∈ v, ∀ z ∈ a, FitsTwos w1 z.1 ∧ FitsTwos w1 z.2) (rest U0 Y0 R0 : List Sym)
    (hrest : BlkTerm rest) :
    Triple [] (fun s => s.stk = rS B (carrSyms w1 v ++ rest) (.mark :: U0)
        (natSyms (0 / S) ++ .mark :: Y0) (natSyms (S - 1 - 0 % S) ++ .mark :: R0) ∧
        s.var.1 = (carrSyms w1 v ++ rest).head?)
      mainLoop
      (fun s => s.stk = rS B (carrSyms w1 [] ++ rest)
        ((carrSyms w2 (v.mapIdx (phaseRec S K ρ D c o))).reverse ++ .mark :: U0)
        (natSyms (v.length / S) ++ .mark :: Y0) (natSyms (S - 1 - v.length % S) ++ .mark :: R0))
      (K1.loopB (recCost S K ρ D w1 w2) 0 v) := by
  have h := K1.triple_loop_list (c := fun r : PReg => K1.isRecTop r.1) (body := recBody)
    (fun x vs acc => rS B (carrSyms w1 vs ++ rest) ((carrSyms w2 acc).reverse ++ .mark :: U0)
      (natSyms (x / S) ++ .mark :: Y0) (natSyms (S - 1 - x % S) ++ .mark :: R0))
    (fun vs (r : PReg) => r.1 = (carrSyms w1 vs ++ rest).head?)
    (fun x a acc => acc ++ [a.map (gEO (c + selCount S K ρ D x) (decide (o = 1)))])
    (recCost S K ρ D w1 w2)
    (fun _ vs => ∀ a ∈ vs, ∀ z ∈ a, FitsTwos w1 z.1 ∧ FitsTwos w1 z.2)
    (fun _ a vs h a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    (fun r hr => by show K1.isRecTop r.1 = false; rw [hr]; exact K1.isRecTop_nil hrest)
    (fun a vs r hr => by
      show K1.isRecTop r.1 = true; rw [hr]; exact K1.isRecTop_cons _ _ rest)
    (fun x a vs acc hok => by
      have hr := triple_recBody B S K ρ D c o w1 w2 hS1 hK ho hw1 hpar x a vs
        (hok a List.mem_cons_self) rest ((carrSyms w2 acc).reverse ++ .mark :: U0) Y0 R0
      refine Triple.conseq hr (fun s hs => hs.1) (fun s hs => ⟨?_, hs.2⟩) le_rfl
      rw [hs.1, carrSyms_snoc, List.reverse_append, List.append_assoc])
    v 0 [] hfit
  refine Triple.conseq h (fun s hs => ⟨by rw [hs.1]; rfl, hs.2⟩) (fun s hs => ?_) le_rfl
  rw [hs, foldG_phase, List.nil_append, Nat.zero_add]
  have hm : (v.mapIdx fun i a => phaseRec S K ρ D c o (0 + i) a) =
      v.mapIdx (phaseRec S K ρ D c o) := by
    congr 1
    funext i a
    rw [Nat.zero_add]
  rw [hm]

/-! ## The kernel -/

/-- **The phase-scan kernel.** -/
def phaseProg : Prog PL (fun _ => Sym) PReg :=
  .seq setupProg (.seq (wk (peekR sA)) (.seq mainLoop finalProg))

theorem closed_phaseProg : phaseProg.Closed :=
  ⟨closed_setupProg, K1.Rot.closed_peekR_lift _ _, closed_mainLoop, closed_finalProg⟩

/-- The cost of the whole run. -/
def phaseCost (S K ρ D c o w1 w2 : ℕ) (v : List (List CInt)) : ℕ :=
  (hdrCost [S, K, ρ, D, c, o, w1, w2] + 13 * bitLen S + 20) +
    (1 + (K1.loopB (recCost S K ρ D w1 w2) 0 v +
      (3 * (carrSyms w2 (v.mapIdx (phaseRec S K ρ D c o))).length + 2 * bitLen (v.length / S) +
        2 * bitLen (S - 1 - v.length % S) + dropCost [S, K, ρ, D, c, o, w1, w2] + 6)))

/-- **The run of the kernel.** -/
theorem runs_phaseProg (St : PL → List Sym) (S K ρ D c o w1 w2 : ℕ) (hS1 : 1 ≤ S)
    (hρK : ρ < K) (ho : o ≤ 1) (hw1 : 1 ≤ w1) (v : List (List CInt)) (rest rp : List Sym)
    (hfit : CArrFits w1 v) (hrest : BlkTerm rest) (hA : St sA = carrSyms w1 v ++ rest)
    (hH : St sH = hdrSyms [S, K, ρ, D, c, o, w1, w2] ++ rp) :
    Runs phaseProg St
      (Function.update St sA (carrSyms w2 (v.mapIdx (phaseRec S K ρ D c o)) ++ rest))
      (fun _ => True) (phaseCost S K ρ D c o w1 w2 v) := by
  have hK : 1 ≤ K := by omega
  have h1 := runs_setupProg St S K ρ D c o w1 w2 hS1 rp hH
  rw [hA] at h1
  have hpk := K1.triple_peek_fst (τ := Option Sym × Option Sym × Option Sym) sA
    (rS (updF St pStacks [S, K, ρ, D, c, o, w1, w2]) (carrSyms w1 v ++ rest) (.mark :: St kU)
      (natSyms (0 / S) ++ .mark :: St kY) (natSyms (S - 1 - 0 % S) ++ .mark :: St kRr))
  have h3 := triple_mainLoop (updF St pStacks [S, K, ρ, D, c, o, w1, w2]) S K ρ D c o w1 w2 hS1
    hK ho hw1 (parOK_updF St S K ρ D c o w1 w2) v hfit rest (St kU) (St kY) (St kRr) hrest
  have h4 := runs_finalProg St [S, K, ρ, D, c, o, w1, w2] rfl w2 (v.length / S)
    (S - 1 - v.length % S) (v.mapIdx (phaseRec S K ρ D c o)) rest
  exact Triple.seq (Triple.post h1 fun _ h => h.1) (Triple.seq
    (Triple.post hpk fun s hs => ⟨hs.1, by rw [hs.2]; simp [rS]⟩)
    (Triple.seq h3 (Triple.pre h4 fun s hs => by rw [hs]; rfl)))

end SubNLogN.Machine.Layer.DrvPhaseScanAux
