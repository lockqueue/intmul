/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPreSteps

/-!
# K5 pre-scaling part: program and correctness (`Bridge/PrePostPreMain.lean`)

`PreScaleStmt` (`SubNLogN/Machine/Contracts/Bridge.lean` §7; Section 4.4 (`sec:bridge-alg`), step (1);
Theorem 4.7 (`thm:bridge-precision`)). Program `preProg Pt Ps` (`Pt`: truncating shift kernel, `Ps`: left-shift kernel):
1. header (phase A, `psHdr`): `NP = P`, `NI = wI`, `NQ = pIn`, `NW = wIn`, `NK = kD = Σ_{i≥1} lg t_i`;
2. scan (phase B, `psScan`): `src → Y → Y2` (array restored on `Y2`), `NM = M = scanMax`;
3. `NX = max pIn M` (`preMax`), `NC = max ((kD+1)/2) 1` (`c2Block`), `NA = NX + NC + 5`
   (`= pIn + e`, `e = preScaleExp t x`, `BridgePSH.preScaleExp_eq`), `NE = NA - pIn = e`, `NP = q = P+2`;
4. compare `q` with `NA`: `q < NA` → truncating right shift by `NA - q`, else left shift by `q - NA`,
   `Y2 → arr` (widths `wIn → wI`; exact by `BridgePSH.encVec_preScaled_gt/le`);
5. push `e` onto `ex`, drop every number.
Cost: each component is bounded by `u = 200·(K·preCost b)` (`K = pK Ct Cs`), 31 units in total.

**Scope (honest summary).** Programs, value glue, the cost helpers, `z_max`, `z_kphase`,
`runs_preProg`; no `sorry` in this file (the component lemmas are in `PrePostPreSteps.lean`).
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## Programs -/

section PreProg

variable {Et Es Rt Rs : Type}

/-- `NX := max (NQ, NM)`. -/
noncomputable def preMax : Prog (KLoc BrK (ZE Et Es)) (fun _ => Sym) (ZReg Rt Rs) :=
  .seq (callInj (zw3Map theW3Kit.hmc ![ZW.NM, ZW.NQ]) lzC theW3Kit.Pc)
    (.ite (fun v => decide (theW3Kit.obs (lzC.get v) = .gt))
      ((copyBlock (zL .NM) (zL .NX) (zL .U)).liftRegs lzO)
      ((copyBlock (zL .NQ) (zL .NX) (zL .U)).liftRegs lzO))

/-- Branch `q < A`: `s := A - q`, truncating right shift `Y2 → arr`, drop `s`. -/
noncomputable def preBrLt (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)
    (_Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs) :
    Prog (KLoc BrK (ZE Et Es)) (fun _ => Sym) (ZReg Rt Rs) :=
  .seq (callInj (zw3Map theW3Kit.hmb ![ZW.NA, ZW.NP, ZW.NS]) lzB theW3Kit.Pb)
    (.seq (callInj (azMap ztL) lzT Pt) ((WP.W3.dropNum (zL .NS)).liftRegs lzO))

/-- Branch `A ≤ q`: `s := q - A`, exact left shift `Y2 → arr`, drop `s`. -/
noncomputable def preBrGe (_Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)
    (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs) :
    Prog (KLoc BrK (ZE Et Es)) (fun _ => Sym) (ZReg Rt Rs) :=
  .seq (callInj (zw3Map theW3Kit.hmb ![ZW.NP, ZW.NA, ZW.NS]) lzB theW3Kit.Pb)
    (.seq (callInj (azMap zsL) lzS Ps) ((WP.W3.dropNum (zL .NS)).liftRegs lzO))

/-- The kernel phase: compare `q` (`NP`) with `A` (`NA`) and shift. -/
noncomputable def preKer (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)
    (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs) :
    Prog (KLoc BrK (ZE Et Es)) (fun _ => Sym) (ZReg Rt Rs) :=
  .seq (callInj (zw3Map theW3Kit.hmc ![ZW.NP, ZW.NA]) lzC theW3Kit.Pc)
    (.ite (fun v => decide (theW3Kit.obs (lzC.get v) = .lt)) (preBrLt Pt Ps) (preBrGe Pt Ps))

/-- Increment an own number stack. -/
def zIncP (x : ZW) : Prog (KLoc BrK (ZE Et Es)) (fun _ => Sym) (ZReg Rt Rs) :=
  (inc (zL x) (zL .U)).liftRegs lzO

/-- Drop an own number stack. -/
def zDropP (x : ZW) : Prog (KLoc BrK (ZE Et Es)) (fun _ => Sym) (ZReg Rt Rs) :=
  (WP.W3.dropNum (zL x)).liftRegs lzO

/-- **The pre-scaling program.** -/
noncomputable def preProg (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)
    (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs) :
    Prog (KLoc BrK (ZE Et Es)) (fun _ => Sym) (ZReg Rt Rs) :=
  .seq ((BridgePSA.psHdr (kN .par) (zL .G) (zL .U) (zL .NP) (zL .NI) (zL .NQ) (zL .NW) (zL .ND)
      (zL .NK)).liftRegs lzO)
  (.seq ((BridgePSA.psScan (kN .src) (zL .NW) (zL .C) (zL .U) (zL .Y) (zL .Y2) (zL .T) (zL .T2)
      (zL .NM)).liftRegs lzP)
  (.seq preMax
  (.seq ((c2Block (zL .NK) (zL .NC) (zL .U)).liftRegs lzO)
  (.seq (callInj (zw3Map theW3Kit.hma ![ZW.NX, ZW.NC, ZW.NA]) lzA theW3Kit.Pa)
  (.seq (zIncP .NA)
  (.seq (zIncP .NA)
  (.seq (zIncP .NA)
  (.seq (zIncP .NA)
  (.seq (zIncP .NA)
  (.seq (callInj (zw3Map theW3Kit.hmb ![ZW.NA, ZW.NQ, ZW.NE]) lzB theW3Kit.Pb)
  (.seq (zIncP .NP)
  (.seq (zIncP .NP)
  (.seq (preKer Pt Ps)
  (.seq ((copyBlock (zL .NE) (kW .ex) (zL .U)).liftRegs lzO)
  (.seq (zDropP .NP)
  (.seq (zDropP .NI)
  (.seq (zDropP .NQ)
  (.seq (zDropP .NW)
  (.seq (zDropP .NK)
  (.seq (zDropP .NM)
  (.seq (zDropP .NX)
  (.seq (zDropP .NC)
  (.seq (zDropP .NA)
    (zDropP .NE))))))))))))))))))))))))

end PreProg

/-! ## Value glue -/

theorem carrSyms_encVec_recC (w F : ℕ) {R : ℕ} (x : Fin R → ℂ) :
    carrSyms w (encVec F x) = ((BridgePSH.nums F x).map (recC w)).flatten := by
  simp only [carrSyms, arrSyms, blk, encVec, BridgePSH.nums, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [recSyms, crecBits, coefBits, recC]

theorem nums_fits {w F R : ℕ} {x : Fin R → ℂ} (h : ArrFits w F x) :
    ∀ c ∈ BridgePSH.nums F x, FitsTwos w c.1 ∧ FitsTwos w c.2 := by
  intro c hc
  simp only [BridgePSH.nums, List.mem_map, List.mem_finRange, true_and] at hc
  obtain ⟨j, rfl⟩ := hc
  exact h j

theorem length_nums (F : ℕ) {R : ℕ} (x : Fin R → ℂ) : (BridgePSH.nums F x).length = R := by
  simp [BridgePSH.nums]

theorem totalLen_pos' {d : ℕ} (t : Fin d → ℕ) (ht : ShapeOK t) : 0 < totalLen t :=
  Finset.prod_pos (fun i _ => by have := (ht i).1; omega)

theorem length_hdrSyms_tail_le (l : List ℕ) : (hdrSyms l.tail).length ≤ (hdrSyms l).length := by
  cases l with
  | nil => simp
  | cons a l => rw [List.tail_cons, BridgePSH.length_hdrSyms_cons_psv]; omega

theorem kD_le_hdr (b : BrPar) : BridgePSH.kD b.t ≤ (hdrSyms b.hdr).length := by
  have h1 := BridgePSH.zsum_le_hdr (List.ofFn b.t).tail
  have h2 := length_hdrSyms_tail_le (List.ofFn b.t)
  have hs : b.hdr = [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t := rfl
  have h3 : (hdrSyms (List.ofFn b.t)).length ≤ (hdrSyms b.hdr).length := by
    rw [hs, hdrSyms_append, List.length_append]
    omega
  unfold BridgePSH.kD
  omega

theorem preScaleExp_le_eBound (b : BrPar) (x : Fin (totalLen b.t) → ℂ) (ht : ShapeOK b.t)
    (hx : ∀ j, OnGrid b.pIn (x j)) (hfit : ArrFits b.wIn b.pIn x) :
    preScaleExp b.t x ≤ eBound b := by
  have h := IntForms.preScaleExp_le b.t (fun i => by have := (ht i).1; omega) b.pIn b.wIn x
    (fun j => gridInt b.pIn (x j)) (fun j => (gridValC_gridInt' (hx j)).symm)
    (fun j => ⟨BridgePSH.natAbs_le_of_fitsTwos_psv (hfit j).1,
      BridgePSH.natAbs_le_of_fitsTwos_psv (hfit j).2⟩)
  unfold eBound
  exact h

theorem ordOf_eq_lt_iff (a b : ℕ) : Lib.ordOf a b = .lt ↔ a < b := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp_all <;> omega

/-! ## Cost helpers -/

theorem pp_lin {a c n P K : ℕ} (hn : n ≤ 5 * P) (hP : 1 ≤ P) (hK : 1 ≤ K)
    (hac : 5 * a + c ≤ 200) : a * n + c ≤ 200 * (K * P) := by
  have h1 : a * n ≤ a * (5 * P) := Nat.mul_le_mul_left a hn
  have h2 : c ≤ c * P := Nat.le_mul_of_pos_right c hP
  have h3 : (5 * a + c) * P ≤ 200 * P := Nat.mul_le_mul_right P hac
  have h4 : P ≤ K * P := Nat.le_mul_of_pos_left P hK
  have h5 : a * (5 * P) + c * P = (5 * a + c) * P := by ring
  have h6 : 200 * P ≤ 200 * (K * P) := Nat.mul_le_mul_left 200 h4
  omega

theorem pp_w3 {C x y P K : ℕ} (hC : C ≤ K) (hx : x ≤ 5 * P) (hy : y ≤ 5 * P) (hP : 1 ≤ P) :
    C * (x + y + 1) ≤ 200 * (K * P) := by
  have h1 : C * (x + y + 1) ≤ K * (11 * P) := Nat.mul_le_mul hC (by omega)
  have h2 : K * (11 * P) = 11 * (K * P) := by ring
  omega

theorem pp_kern {C R wa wb s P K : ℕ} (hC : C ≤ K) (hR : 1 ≤ R) (hP : R * (wa + wb + 1) ≤ P)
    (hs : s ≤ 5 * P) (hP1 : 1 ≤ P) :
    C * (R * (2 * wa + 1) + R * (2 * wb + 1) + wa + wb + s + 1) ≤ 200 * (K * P) := by
  have e1 : R * (2 * wa + 1) + R * (2 * wb + 1) = 2 * (R * (wa + wb + 1)) := by ring
  have e2 : wa + wb + 1 ≤ R * (wa + wb + 1) := Nat.le_mul_of_pos_left _ hR
  have h1 : C * (R * (2 * wa + 1) + R * (2 * wb + 1) + wa + wb + s + 1) ≤ K * (9 * P) :=
    Nat.mul_le_mul hC (by omega)
  have h2 : K * (9 * P) = 9 * (K * P) := by ring
  omega

section Seq

variable {K σ : Type} [DecidableEq K]

/-- Sequencing with a unit budget: the first component costs `≤ k·u`, the rest `n·u`. -/
theorem runs_seq_u {P Q : Prog K (fun _ => Sym) σ} {S S1 S2 : K → List Sym} {Q1 Q2 : σ → Prop}
    {T1 u : ℕ} (k n : ℕ) (h1 : Runs P S S1 Q1 T1) (hT : T1 ≤ k * u) (h2 : Runs Q S1 S2 Q2 (n * u)) :
    Runs (.seq P Q) S S2 Q2 ((n + k) * u) :=
  WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ h => h) (by rw [Nat.add_mul]; omega)

end Seq

theorem u_inc {n P K : ℕ} (hn : bitLen n ≤ 5 * P) (hP : 1 ≤ P) (hK : 1 ≤ K) :
    6 * bitLen n + 9 ≤ 1 * (200 * (K * P)) := by
  have := pp_lin (a := 6) (c := 9) hn hP hK (by norm_num); omega

theorem u_drop {n P K : ℕ} (hn : bitLen n ≤ 5 * P) (hP : 1 ≤ P) (hK : 1 ≤ K) :
    2 * bitLen n + 4 ≤ 1 * (200 * (K * P)) := by
  have := pp_lin (a := 2) (c := 4) hn hP hK (by norm_num); omega

theorem u_copy {n P K : ℕ} (hn : bitLen n ≤ 5 * P) (hP : 1 ≤ P) (hK : 1 ≤ K) :
    7 * bitLen n + 7 ≤ 1 * (200 * (K * P)) := by
  have := pp_lin (a := 7) (c := 7) hn hP hK (by norm_num); omega

theorem u_c2 {n P K : ℕ} (hn : bitLen n ≤ 5 * P) (hP : 1 ≤ P) (hK : 1 ≤ K) :
    20 * bitLen n + 40 ≤ 1 * (200 * (K * P)) := by
  have := pp_lin (a := 20) (c := 40) hn hP hK (by norm_num); omega

theorem u_w3 {C a b P K : ℕ} (hC : C ≤ K) (ha : bitLen a ≤ 5 * P) (hb : bitLen b ≤ 5 * P)
    (hP : 1 ≤ P) : C * (bitLen a + bitLen b + 1) ≤ 1 * (200 * (K * P)) := by
  have := pp_w3 hC ha hb hP; omega

/-! ## The two branching phases -/

section Phases

variable {Et Es Rt Rs : Type} [DecidableEq Et] [DecidableEq Es]

theorem z_max (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (M p : ℕ) (hM : f .NM = natSyms M) (hQ : f .NQ = natSyms p) (hX : f .NX = []) :
    Runs (preMax (Et := Et) (Es := Es) (Rt := Rt) (Rs := Rs)) (zst S f Sr Pa A E)
      (zst S (Function.update f .NX (natSyms (max p M))) Sr Pa A E) (fun _ => True)
      (theW3Kit.Cc * (bitLen M + bitLen p + 1) + (7 * (bitLen M + bitLen p) + 7 + 1)) := by
  have r1 := z_cmp (Rt := Rt) (Rs := Rs) S f Sr Pa A E .NM .NQ (by decide) M p hM hQ
  have hgt : decide (Lib.ordOf M p = .gt) = true →
      Runs ((copyBlock (zL .NM) (zL .NX) (zL .U)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
        (zst S f Sr Pa A E) (zst S (Function.update f .NX (natSyms (max p M))) Sr Pa A E)
        (fun _ => True) (7 * (bitLen M + bitLen p) + 7) := by
    intro h
    have hlt : p < M := (ordOf_eq_gt_iff M p).1 (of_decide_eq_true h)
    rw [show max p M = M by omega]
    exact WP.W9comp.runs_mono (z_copy S f Sr Pa A E .NM .NX (by decide) (by decide) (by decide)
      M hM hX) (fun _ _ => trivial) (by omega)
  have hle : decide (Lib.ordOf M p = .gt) = false →
      Runs ((copyBlock (zL .NQ) (zL .NX) (zL .U)).liftRegs (lzO (Rt := Rt) (Rs := Rs)))
        (zst S f Sr Pa A E) (zst S (Function.update f .NX (natSyms (max p M))) Sr Pa A E)
        (fun _ => True) (7 * (bitLen M + bitLen p) + 7) := by
    intro h
    have hle : M ≤ p := by
      have := (ordOf_eq_gt_iff M p).not.1 (of_decide_eq_false h)
      omega
    rw [show max p M = p by omega]
    exact WP.W9comp.runs_mono (z_copy S f Sr Pa A E .NQ .NX (by decide) (by decide) (by decide)
      p hQ hX) (fun _ _ => trivial) (by omega)
  exact runs_seq_ite
    (c := fun v => decide (theW3Kit.obs ((lzC (Rt := Rt) (Rs := Rs)).get v) = .gt))
    (b := decide (Lib.ordOf M p = .gt))
    (WP.W9comp.runs_mono r1 (fun v hv => by
      show decide (theW3Kit.obs ((lzC (Rt := Rt) (Rs := Rs)).get v) = .gt) = _
      rw [hv]) le_rfl) hgt hle

theorem z_kphase (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)
    (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs) (Ct Cs : ℕ)
    (hPt : ShiftSpec truncShiftC Ct Pt) (hPs : ShiftSpec shlC Cs Ps)
    (S : KLoc BrK (ZE Et Es) → List Sym) (f : ZW → List Sym) (Sr Pa A E : List Sym)
    (wa wb q a : ℕ) (v vout : List (List CInt)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    (hv1 : CArrFits wa v) (hvo : CArrFits wb vout)
    (hlt : q < a → mapC (truncShiftC (a - q)) v = vout)
    (hge : a ≤ q → mapC (shlC (q - a)) v = vout)
    (hNP : f .NP = natSyms q) (hNA : f .NA = natSyms a) (hNS : f .NS = [])
    (hY2 : f .Y2 = carrSyms wa v) (hNW : f .NW = natSyms wa) (hNI : f .NI = natSyms wb) :
    Runs (preKer Pt Ps) (zst S f Sr Pa A E)
      (zst S (Function.update f .Y2 []) Sr Pa (carrSyms wb vout ++ A) E) (fun _ => True)
      (theW3Kit.Cc * (bitLen q + bitLen a + 1) + (theW3Kit.Cb * (bitLen q + bitLen a + 1) +
        (Ct + Cs) * (cvol wa v + cvol wb v + wa + wb + (bitLen q + bitLen a) + 1) +
        (2 * (bitLen q + bitLen a) + 4) + 1)) := by
  have r1 := z_cmp (Rt := Rt) (Rs := Rs) S f Sr Pa A E .NP .NA (by decide) q a hNP hNA
  have hb1 : decide (Lib.ordOf q a = .lt) = true →
      Runs (preBrLt Pt Ps) (zst S f Sr Pa A E)
        (zst S (Function.update f .Y2 []) Sr Pa (carrSyms wb vout ++ A) E) (fun _ => True)
        (theW3Kit.Cb * (bitLen q + bitLen a + 1) +
          (Ct + Cs) * (cvol wa v + cvol wb v + wa + wb + (bitLen q + bitLen a) + 1) +
          (2 * (bitLen q + bitLen a) + 4)) := by
    intro h
    have hqa : q < a := (ordOf_eq_lt_iff q a).1 (of_decide_eq_true h)
    have rs := z_sub (Rt := Rt) (Rs := Rs) S f Sr Pa A E .NA .NP .NS (by decide) (by decide)
      (by decide) a q hqa.le hNA hNP hNS
    have hval := hlt hqa
    have rk := z_kernel (Rt := Rt) (Rs := Rs) ztL ztL_injective ztL_disj lzT truncShiftC Ct Pt hPt
      S (Function.update f .NS (natSyms (a - q))) Sr Pa A E wa wb (a - q) v hwa hwb hv1
      (by rw [hval]; exact hvo)
      (by rw [Function.update_of_ne (by decide)]; exact hY2)
      (by rw [Function.update_of_ne (by decide)]; exact hNW)
      (by rw [Function.update_of_ne (by decide)]; exact hNI)
      (Function.update_self _ _ _)
    rw [hval] at rk
    have rd := z_drop (Rt := Rt) (Rs := Rs) S
      (Function.update (Function.update f .NS (natSyms (a - q))) .Y2 []) Sr Pa
      (carrSyms wb vout ++ A) E .NS (a - q)
      (by rw [Function.update_of_ne (by decide), Function.update_self])
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq rs
      (WP.W9comp.runs_seq rk rd)) ?_) (fun _ _ => trivial) ?_
    · congr 1
      funext y
      cases y <;> simp [Function.update_apply, hNS]
    · have h1 : bitLen (a - q) ≤ bitLen a := bitLen_mono2 (Nat.sub_le _ _)
      have h2 : Ct * (cvol wa v + cvol wb v + wa + wb + bitLen (a - q) + 1) ≤
          (Ct + Cs) * (cvol wa v + cvol wb v + wa + wb + (bitLen q + bitLen a) + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : theW3Kit.Cb * (bitLen a + bitLen q + 1) =
          theW3Kit.Cb * (bitLen q + bitLen a + 1) := by ring
      omega
  have hb2 : decide (Lib.ordOf q a = .lt) = false →
      Runs (preBrGe Pt Ps) (zst S f Sr Pa A E)
        (zst S (Function.update f .Y2 []) Sr Pa (carrSyms wb vout ++ A) E) (fun _ => True)
        (theW3Kit.Cb * (bitLen q + bitLen a + 1) +
          (Ct + Cs) * (cvol wa v + cvol wb v + wa + wb + (bitLen q + bitLen a) + 1) +
          (2 * (bitLen q + bitLen a) + 4)) := by
    intro h
    have haq : a ≤ q := by
      have := (ordOf_eq_lt_iff q a).not.1 (of_decide_eq_false h)
      omega
    have rs := z_sub (Rt := Rt) (Rs := Rs) S f Sr Pa A E .NP .NA .NS (by decide) (by decide)
      (by decide) q a haq hNP hNA hNS
    have hval := hge haq
    have rk := z_kernel (Rt := Rt) (Rs := Rs) zsL zsL_injective zsL_disj lzS shlC Cs Ps hPs
      S (Function.update f .NS (natSyms (q - a))) Sr Pa A E wa wb (q - a) v hwa hwb hv1
      (by rw [hval]; exact hvo)
      (by rw [Function.update_of_ne (by decide)]; exact hY2)
      (by rw [Function.update_of_ne (by decide)]; exact hNW)
      (by rw [Function.update_of_ne (by decide)]; exact hNI)
      (Function.update_self _ _ _)
    rw [hval] at rk
    have rd := z_drop (Rt := Rt) (Rs := Rs) S
      (Function.update (Function.update f .NS (natSyms (q - a))) .Y2 []) Sr Pa
      (carrSyms wb vout ++ A) E .NS (q - a)
      (by rw [Function.update_of_ne (by decide), Function.update_self])
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq rs
      (WP.W9comp.runs_seq rk rd)) ?_) (fun _ _ => trivial) ?_
    · congr 1
      funext y
      cases y <;> simp [Function.update_apply, hNS]
    · have h1 : bitLen (q - a) ≤ bitLen q := bitLen_mono2 (Nat.sub_le _ _)
      have h2 : Cs * (cvol wa v + cvol wb v + wa + wb + bitLen (q - a) + 1) ≤
          (Ct + Cs) * (cvol wa v + cvol wb v + wa + wb + (bitLen q + bitLen a) + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  exact runs_seq_ite
    (c := fun v => decide (theW3Kit.obs ((lzC (Rt := Rt) (Rs := Rs)).get v) = .lt))
    (b := decide (Lib.ordOf q a = .lt))
    (WP.W9comp.runs_mono r1 (fun v hv => by
      show decide (theW3Kit.obs ((lzC (Rt := Rt) (Rs := Rs)).get v) = .lt) = _
      rw [hv]) le_rfl) hb1 hb2

end Phases

/-! ## Correctness of the pre-scaling program -/

/-- The cost constant of the pre-scale part. -/
noncomputable def pK (Ct Cs : ℕ) : ℕ := theW3Kit.Ca + theW3Kit.Cb + theW3Kit.Cc + Ct + Cs + 1

theorem c2_eq (k : ℕ) : max ((k + 1) / 2) 1 = (max k 1 + 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; rfl
  · rw [max_eq_left (by omega), max_eq_left (by omega)]

section Main

variable {Et Es Rt Rs : Type} [DecidableEq Et] [DecidableEq Es]

set_option maxHeartbeats 1600000 in
/-- **The pre-scaling program is correct** (exact final stacks, cost `31·200·(pK·preCost b)`). -/
theorem runs_preProg (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)
    (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs) (Ct Cs : ℕ)
    (hPt : ShiftSpec truncShiftC Ct Pt) (hPs : ShiftSpec shlC Cs Ps)
    (b : BrPar) (x : Fin (totalLen b.t) → ℂ) (rsrc rpar : List Sym)
    (S : KLoc BrK (ZE Et Es) → List Sym) (hclean : KClean S) (hd1 : 1 ≤ b.d) (ht : ShapeOK b.t)
    (hwIn : 1 ≤ b.wIn) (hwI : 1 ≤ b.wI) (hx : ∀ j, OnGrid b.pIn (x j))
    (hg : ∀ j, OnGrid (b.P + 2) (preScaled b.t x j)) (hfitIn : ArrFits b.wIn b.pIn x)
    (hfitI : ArrFits b.wI (b.P + 2) (preScaled b.t x)) (hrsrc : BlkTerm rsrc)
    (hsrc : S (kN .src) = carrSyms b.wIn (encVec b.pIn x) ++ rsrc)
    (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (preProg Pt Ps) S
      (Function.update (Function.update (Function.update S (kN .src) rsrc)
        (kW .arr) (carrSyms b.wI (encVec (b.P + 2) (preScaled b.t x)) ++ S (kW .arr)))
        (kW .ex) (natSyms (preScaleExp b.t x) ++ S (kW .ex)))
      (fun _ => True) (31 * (200 * (pK Ct Cs * preCost b))) := by
  -- budget
  obtain ⟨P0, hP0⟩ : ∃ P0, P0 = preCost b := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ : ∃ K0, K0 = pK Ct Cs := ⟨_, rfl⟩
  rw [← hP0, ← hK0]
  have hK1 : 1 ≤ K0 := by rw [hK0]; unfold pK; omega
  have hCa : theW3Kit.Ca ≤ K0 := by rw [hK0]; unfold pK; omega
  have hCb : theW3Kit.Cb ≤ K0 := by rw [hK0]; unfold pK; omega
  have hCc : theW3Kit.Cc ≤ K0 := by rw [hK0]; unfold pK; omega
  have hCk : Ct + Cs ≤ K0 := by rw [hK0]; unfold pK; omega
  have hsetup : b.setup = ((hdrSyms b.hdr).length + 1) ^ 3 := rfl
  have hHd1 : (hdrSyms b.hdr).length + 1 ≤ b.setup := Nat.le_self_pow (by norm_num) _
  have hPdef : P0 = totalLen b.t * (b.wIn + b.wI + 1) + (b.wIn + totalLen b.t + 6) + b.setup := by
    rw [hP0]; rfl
  have hEdef : eBound b = b.wIn + totalLen b.t + 6 := rfl
  have hRpos := totalLen_pos' b.t ht
  have hP1 : 1 ≤ P0 := by omega
  have hHdP : (hdrSyms b.hdr).length + 1 ≤ P0 := by omega
  have hPR : totalLen b.t * (b.wIn + b.wI + 1) ≤ P0 := by omega
  -- values
  obtain ⟨M, hM⟩ : ∃ M, M = BridgePSH.scanMax b.pIn x := ⟨_, rfl⟩
  obtain ⟨kD, hkD⟩ : ∃ k, k = BridgePSH.kD b.t := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = preScaleExp b.t x := ⟨_, rfl⟩
  have heq : e = 1 + (max b.pIn M - b.pIn) + (max kD 1 + 1) / 2 + 4 := by
    rw [he, hM, hkD]; exact BridgePSH.preScaleExp_eq b.t hd1 ht b.pIn x hx
  have hMw : M ≤ b.wIn - 1 := by rw [hM]; exact BridgePSH.scanMax_le _ _ x hfitIn
  have hmin : min ((BridgePSH.nums b.pIn x).reverse.foldl cmax 0) b.wIn = M := by
    rw [hM]; show min (BridgePSH.scanMax b.pIn x) b.wIn = _; rw [← hM]; omega
  have heB : e ≤ eBound b := by rw [he]; exact preScaleExp_le_eBound b x ht hx hfitIn
  have hkDH : kD ≤ (hdrSyms b.hdr).length := by rw [hkD]; exact kD_le_hdr b
  have hc2 := c2_eq kD
  have hmx1 : b.pIn ≤ max b.pIn M := le_max_left _ _
  have hmx2 : max b.pIn M ≤ b.pIn + M := max_le (by omega) (by omega)
  have hAe : max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1 = b.pIn + e := by omega
  -- bit lengths
  have hbP : bitLen b.P ≤ (hdrSyms b.hdr).length := by
    have hs : [b.p] ++ b.P :: ([b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
    rw [← hs]; exact bitLen_field_le _ _ _
  have hbI : bitLen b.wI ≤ (hdrSyms b.hdr).length := by
    have hs : [b.p, b.P, b.ω] ++ b.wI :: ([b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
    rw [← hs]; exact bitLen_field_le _ _ _
  have hbQ : bitLen b.pIn ≤ (hdrSyms b.hdr).length := by
    have hs : [b.p, b.P, b.ω, b.wI, b.wT, b.wOut] ++ b.pIn :: ([b.wIn, b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
    rw [← hs]; exact bitLen_field_le _ _ _
  have hbW : bitLen b.wIn ≤ (hdrSyms b.hdr).length := by
    have hs : [b.p, b.P, b.ω, b.wI, b.wT, b.wOut, b.pIn] ++ b.wIn :: ([b.d] ++ List.ofFn b.t) =
      b.hdr := rfl
    rw [← hs]; exact bitLen_field_le _ _ _
  have hbP1 : bitLen (b.P + 1) ≤ bitLen b.P + 1 := bitLen_succ_le _
  have hbP2 : bitLen (b.P + 1 + 1) ≤ bitLen b.P + 2 := by
    have := bitLen_succ_le (b.P + 1); omega
  have hbK : bitLen kD ≤ kD := bitLen_le_self' _
  have hbM : bitLen M ≤ M := bitLen_le_self' _
  have hbe : bitLen e ≤ e := bitLen_le_self' _
  have hbmx : bitLen (max b.pIn M) ≤ bitLen b.pIn + bitLen M + 1 :=
    le_trans (bitLen_mono2 hmx2) (bitLen_add_le _ _)
  have hbc2 : bitLen (max ((kD + 1) / 2) 1) ≤ kD + 1 :=
    le_trans (bitLen_le_self' _) (by omega)
  have hbA : ∀ n, n ≤ b.pIn + e → bitLen n ≤ 2 * P0 := by
    intro n hn
    have h1 := bitLen_mono2 hn
    have h2 := bitLen_add_le b.pIn e
    omega
  have hbA5 : ∀ n, n ≤ b.pIn + e → bitLen n ≤ 5 * P0 := fun n hn => by
    have := hbA n hn; omega
  have hbe' : bitLen (preScaleExp b.t x) ≤ e := by rw [← he]; exact hbe
  have hEA : preScaleExp b.t x =
      max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1 - b.pIn := by omega
  have hlt : b.P + 1 + 1 < max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1 →
      mapC (truncShiftC (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1 - (b.P + 1 + 1)))
        (encVec b.pIn x) = encVec (b.P + 2) (preScaled b.t x) := by
    intro h
    rw [BridgePSH.encVec_preScaled_gt b.t b.pIn (b.P + 2) x hx hg (by omega)]
    congr 2
    omega
  have hge : max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1 ≤ b.P + 1 + 1 →
      mapC (shlC (b.P + 1 + 1 - (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1)))
        (encVec b.pIn x) = encVec (b.P + 2) (preScaled b.t x) := by
    intro h
    rw [BridgePSH.encVec_preScaled_le b.t b.pIn (b.P + 2) x hx (by omega)]
    congr 2
    omega
  -- initial and final states
  have hS0 : S = zst S (fun _ => []) (S (kN .src)) (S (kN .par)) (S (kW .arr)) (S (kW .ex)) :=
    (zst_self S hclean).symm
  have hfin : Function.update (Function.update (Function.update S (kN .src) rsrc)
        (kW .arr) (carrSyms b.wI (encVec (b.P + 2) (preScaled b.t x)) ++ S (kW .arr)))
        (kW .ex) (natSyms (preScaleExp b.t x) ++ S (kW .ex)) =
      zst S (fun _ => []) rsrc (S (kN .par))
        (carrSyms b.wI (encVec (b.P + 2) (preScaled b.t x)) ++ S (kW .arr))
        (natSyms (preScaleExp b.t x) ++ S (kW .ex)) := by
    conv_lhs => rw [hS0]
    rw [zst_upd_src, zst_upd_arr, zst_upd_ex]
    rfl
  rw [hfin]
  suffices key : Runs (preProg Pt Ps)
      (zst S (fun _ => []) (S (kN .src)) (S (kN .par)) (S (kW .arr)) (S (kW .ex)))
      (zst S (fun _ => []) rsrc (S (kN .par))
        (carrSyms b.wI (encVec (b.P + 2) (preScaled b.t x)) ++ S (kW .arr))
        (natSyms (preScaleExp b.t x) ++ S (kW .ex))) (fun _ => True) (31 * (200 * (K0 * P0))) by
    rwa [← hS0] at key
  have hKP := Nat.le_mul_of_pos_left P0 hK1
  -- 1. header
  refine runs_seq_u 1 30 (z_hdr S (fun _ => []) _ _ _ _ b hd1 rpar hpar rfl rfl rfl rfl rfl rfl)
    (by rw [← hsetup]; omega) ?_
  -- 2. scan
  refine runs_seq_u 1 29 (z_scan S _ _ _ _ _ hwIn (BridgePSH.nums b.pIn x) (nums_fits hfitIn) rsrc
    hrsrc (by rw [hsrc, carrSyms_encVec_recC]) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)) (by
      rw [length_nums]
      have h1 : totalLen b.t * (34 * b.wIn + 24) ≤ 34 * (totalLen b.t * (b.wIn + b.wI + 1)) := by
        calc totalLen b.t * (34 * b.wIn + 24) ≤ totalLen b.t * (34 * (b.wIn + b.wI + 1)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 34 * (totalLen b.t * (b.wIn + b.wI + 1)) := by ring
      omega) ?_
  -- 3. NX := max pIn M
  refine runs_seq_u 3 26 (z_max S _ _ _ _ _ M b.pIn (by rw [← hmin]; try rfl) (by rfl) (by rfl))
    (by
      have h1 := u_w3 (C := theW3Kit.Cc) (a := M) (b := b.pIn) hCc (by omega) (by omega) hP1
      have h2 := pp_lin (a := 7) (c := 8) (n := bitLen M + bitLen b.pIn) (by omega) hP1 hK1
        (by norm_num)
      omega) ?_
  -- 4. NC := c2
  refine runs_seq_u 1 25 (z_c2 S _ _ _ _ _ kD (by rw [hkD]; try rfl) (by rfl))
    (u_c2 (by omega) hP1 hK1) ?_
  -- 5. NA := NX + NC, then 5 increments
  refine runs_seq_u 1 24 (z_add S _ _ _ _ _ .NX .NC .NA (by decide) (by decide) (by decide)
    (max b.pIn M) (max ((kD + 1) / 2) 1) (by rfl) (by rfl) (by rfl))
    (u_w3 hCa (by omega) (by omega) hP1) ?_
  refine runs_seq_u 1 23 (z_inc S _ _ _ _ _ .NA (by decide)
    (max b.pIn M + max ((kD + 1) / 2) 1) (by rfl)) (u_inc (hbA5 _ (by omega)) hP1 hK1) ?_
  refine runs_seq_u 1 22 (z_inc S _ _ _ _ _ .NA (by decide)
    (max b.pIn M + max ((kD + 1) / 2) 1 + 1) (by rfl)) (u_inc (hbA5 _ (by omega)) hP1 hK1) ?_
  refine runs_seq_u 1 21 (z_inc S _ _ _ _ _ .NA (by decide)
    (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1) (by rfl)) (u_inc (hbA5 _ (by omega)) hP1 hK1) ?_
  refine runs_seq_u 1 20 (z_inc S _ _ _ _ _ .NA (by decide)
    (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1) (by rfl))
    (u_inc (hbA5 _ (by omega)) hP1 hK1) ?_
  refine runs_seq_u 1 19 (z_inc S _ _ _ _ _ .NA (by decide)
    (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1) (by rfl))
    (u_inc (hbA5 _ (by omega)) hP1 hK1) ?_
  -- 6. NE := NA - pIn (= e)
  refine runs_seq_u 1 18 (z_sub S _ _ _ _ _ .NA .NQ .NE (by decide) (by decide) (by decide)
    (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1) b.pIn (by omega) (by rfl) (by rfl)
    (by rfl)) (u_w3 hCb (hbA5 _ (by omega)) (by omega) hP1) ?_
  -- 7. q := P + 2
  refine runs_seq_u 1 17 (z_inc S _ _ _ _ _ .NP (by decide) b.P (by rfl))
    (u_inc (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 16 (z_inc S _ _ _ _ _ .NP (by decide) (b.P + 1) (by rfl))
    (u_inc (by omega) hP1 hK1) ?_
  -- 8. compare q with A and shift `Y2 → arr`
  refine runs_seq_u 5 11 (z_kphase Pt Ps Ct Cs hPt hPs S _ _ _ _ _ b.wIn b.wI (b.P + 1 + 1)
    (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1) (encVec b.pIn x)
    (encVec (b.P + 2) (preScaled b.t x)) hwIn hwI (BridgeRed.cArrFits_encVec _ _ _ hfitIn)
    (BridgeRed.cArrFits_encVec _ _ _ hfitI) hlt hge (by rfl) (by rfl) (by rfl)
    (by rw [carrSyms_encVec_recC]; try rfl) (by rfl) (by rfl)) (by
      rw [cvol_encVec, cvol_encVec]
      have hbq : bitLen (b.P + 1 + 1) ≤ 5 * P0 := by omega
      have hba := hbA5 (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1) (by omega)
      have hbq2 : bitLen (b.P + 1 + 1) ≤ 2 * P0 := by omega
      have hba2 := hbA (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1) (by omega)
      have h1 := u_w3 (C := theW3Kit.Cc) hCc hbq hba hP1
      have h2 := u_w3 (C := theW3Kit.Cb) hCb hbq hba hP1
      have h3 := pp_kern (C := Ct + Cs) (K := K0) (R := totalLen b.t) (wa := b.wIn) (wb := b.wI)
        (s := bitLen (b.P + 1 + 1) +
          bitLen (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1))
        hCk hRpos hPR (by omega) hP1
      have h4 := pp_lin (a := 2) (c := 5) (K := K0) (P := P0) (n := bitLen (b.P + 1 + 1) +
          bitLen (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1)) (by omega) hP1 hK1
        (by norm_num)
      omega) ?_
  -- 9. push `e` onto `ex`
  refine runs_seq_u 1 10 (z_copyEx S _ _ _ _ _ (preScaleExp b.t x) (by rw [hEA]; try rfl))
    (u_copy (by omega) hP1 hK1) ?_
  -- 10. drop every number
  refine runs_seq_u 1 9 (z_drop S _ _ _ _ _ .NP (b.P + 1 + 1) (by rfl))
    (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 8 (z_drop S _ _ _ _ _ .NI b.wI (by rfl)) (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 7 (z_drop S _ _ _ _ _ .NQ b.pIn (by rfl)) (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 6 (z_drop S _ _ _ _ _ .NW b.wIn (by rfl)) (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 5 (z_drop S _ _ _ _ _ .NK kD (by rw [hkD]; try rfl))
    (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 4 (z_drop S _ _ _ _ _ .NM M (by rw [← hmin]; try rfl))
    (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 3 (z_drop S _ _ _ _ _ .NX (max b.pIn M) (by rfl))
    (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 2 (z_drop S _ _ _ _ _ .NC (max ((kD + 1) / 2) 1) (by rfl))
    (u_drop (by omega) hP1 hK1) ?_
  refine runs_seq_u 1 1 (z_drop S _ _ _ _ _ .NA
    (max b.pIn M + max ((kD + 1) / 2) 1 + 1 + 1 + 1 + 1 + 1) (by rfl))
    (u_drop (hbA5 _ (by omega)) hP1 hK1) ?_
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (z_drop S _ _ _ _ _ .NE (preScaleExp b.t x)
    (by rw [hEA]; try rfl)) ?_) (fun _ _ => trivial) (u_drop (by omega) hP1 hK1)
  congr 1
  funext y
  cases y <;> rfl

end Main

end SubNLogN.Machine.BridgePP
