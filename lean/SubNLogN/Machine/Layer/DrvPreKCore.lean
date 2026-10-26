/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreKLayout

/-!
# Driver pre-phase kernel: counters and the arithmetic core (`Machine/Layer/DrvPreKCore.lean`)

**Scope (honest summary).** Proved, conditional only on the sub-kernel `spec` bodies, which enter
as hypotheses on given programs (`BinSpec`, `RSpec`, `TSpec`, `Machine/Layer/DrvPreKLayout.lean`).
* `setupProg`, `runs_setup`: the six counters `w, w, w+1, w+1, w+2, 1` (`ctrPre w`) from the named
  counter `w`; `tearProg`, `runs_tear`: their removal.
* `coreProg`, `runs_core`: from the halves `u`, `v` (on `U`, `V`) to the output streams
  `zipC cgate0 u v`, `zipC cgate1 u v` (on `C0`, `C1`): two copies, `CAdd`/`CSub` to width `w + 1`,
  the rotation by `i`, two copies, `CAdd`/`CSub` to width `w + 2`, two truncating shifts by `1` to
  width `w`. Cost `(70 + 11·Ca + 11·Cs + 2·Cr + 8·Ct)·(cvol w u + w + 1)`.
-/

namespace SubNLogN.Machine.Layer.DrvPreK

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability

theorem cvol_aligned (k : ℕ) : ∀ {u v : List (List CInt)}, CAligned u v → cvol k u = cvol k v
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: u, b :: v, h => by
    obtain ⟨hab, huv⟩ := List.forall₂_cons.1 h
    rw [cvol_cons, cvol_cons, hab, cvol_aligned k huv]

theorem length_incBits_le : ∀ L : List Bool, (incBits L).length ≤ L.length + 1
  | [] => by simp [incBits]
  | true :: l => by
    simp only [incBits, List.length_cons]
    have := length_incBits_le l
    omega
  | false :: l => by simp [incBits]

theorem bitLen_le_self' : ∀ n : ℕ, bitLen n ≤ n
  | 0 => by simp [bitLen, encodeNat_zero]
  | n + 1 => by
    have ih := bitLen_le_self' n
    unfold bitLen at *
    rw [encodeNat_succ]
    have := length_incBits_le (encodeNat n)
    omega

/-- The counters after the setup: `Cw`, `Cw'` hold `w`; `Cw1`, `Cw1'` hold `w + 1`; `Cw2` holds
`w + 2`; `Cs` holds `1`; every other own stack holds nothing above its guard. -/
def ctrPre (w : ℕ) : KS → List Sym
  | .Cw => natSyms w
  | .Cw' => natSyms w
  | .Cw1 => natSyms (w + 1)
  | .Cw1' => natSyms (w + 1)
  | .Cw2 => natSyms (w + 2)
  | .Cs => natSyms 1
  | _ => []

/-! ## Counters -/

section Counters

variable {Z σ : Type} [DecidableEq Z] (lO : Lens σ (Option Sym))

/-- Build the counters from the named counter `w`. -/
def setupProg : Prog (KK Z) (fun _ => Sym) σ :=
  ((((((((copyBlock (.inl 2 : KK Z) (ds .Cw) (ds .TMP)).liftRegs lO).seq
    ((copyBlock (.inl 2 : KK Z) (ds .Cw') (ds .TMP)).liftRegs lO)).seq
    ((copyBlock (.inl 2 : KK Z) (ds .Cw1) (ds .TMP)).liftRegs lO)).seq
    ((inc (ds .Cw1 : KK Z) (ds .TMP)).liftRegs lO)).seq
    ((copyBlock (ds .Cw1 : KK Z) (ds .Cw1') (ds .TMP)).liftRegs lO)).seq
    ((copyBlock (ds .Cw1 : KK Z) (ds .Cw2) (ds .TMP)).liftRegs lO)).seq
    ((inc (ds .Cw2 : KK Z) (ds .TMP)).liftRegs lO)).seq
    ((pushC (ds .Cs : KK Z) (.bit true)).liftRegs lO)

/-- Remove the counters. -/
def tearProg : Prog (KK Z) (fun _ => Sym) σ :=
  ((((((WP.W3.dropNum (ds .Cw : KK Z)).liftRegs lO).seq
    ((WP.W3.dropNum (ds .Cw' : KK Z)).liftRegs lO)).seq
    ((WP.W3.dropNum (ds .Cw1 : KK Z)).liftRegs lO)).seq
    ((WP.W3.dropNum (ds .Cw1' : KK Z)).liftRegs lO)).seq
    ((WP.W3.dropNum (ds .Cw2 : KK Z)).liftRegs lO)).seq
    ((WP.W3.dropNum (ds .Cs : KK Z)).liftRegs lO)

theorem closed_setupProg : (setupProg (Z := Z) lO).Closed := by
  simp [setupProg, Prog.Closed, Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs, copyBlock,
    moveBitsDup, dupBody, moveBlock, moveBits, moveBitsBody, restoreR, inc, scanLoop, scanBody,
    incFix, pushC, popR, pushR, peekR, skip]

theorem closed_tearProg : (tearProg (Z := Z) lO).Closed := by
  simp [tearProg, Prog.Closed, Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs, WP.W3.dropNum,
    WP.W3.dropBits, restoreR, popR, pushR, peekR, skip]

theorem runs_setup (S : KK Z → List Sym) (a0 : List Sym) (w : ℕ) (r2 : List Sym)
    (hr2 : TermOK r2) (hS2 : S (.inl 2) = natSyms w ++ r2) :
    Runs (setupProg lO) (st S a0 (fun _ => [])) (st S a0 (ctrPre w)) (fun _ => True)
      (80 * (w + 1)) := by
  have e1 := runs_copyCtr lO S a0 (fun _ => []) (src := .inl 2) (dst := .Cw) (by simp) (by simp)
    (by decide) w r2 hr2 (by simp [hS2])
  have e2 := runsSeq e1 (runs_copyCtr lO S a0 _ (src := .inl 2) (dst := .Cw') (by simp)
    (by simp) (by decide) w r2 hr2 (by simp [hS2]))
  have e3 := runsSeq e2 (runs_copyCtr lO S a0 _ (src := .inl 2) (dst := .Cw1) (by simp)
    (by simp) (by decide) w r2 hr2 (by simp [hS2]))
  have e4 := runsSeq e3 (runs_incCtr lO S a0 _ (d := .Cw1) (by decide) w
    (by simp [Function.update_apply]))
  have e5 := runsSeq e4 (runs_copyCtr lO S a0 _ (src := ds .Cw1) (dst := .Cw1')
    (ds_ne (by decide)) (ds_ne (by decide)) (by decide) (w + 1) (.mark :: S (ds .Cw1))
    (termOK_mark _) (by simp [Function.update_apply]))
  have e6 := runsSeq e5 (runs_copyCtr lO S a0 _ (src := ds .Cw1) (dst := .Cw2)
    (ds_ne (by decide)) (ds_ne (by decide)) (by decide) (w + 1) (.mark :: S (ds .Cw1))
    (termOK_mark _) (by simp [Function.update_apply]))
  have e7 := runsSeq e6 (runs_incCtr lO S a0 _ (d := .Cw2) (by decide) (w + 1)
    (by simp [Function.update_apply]))
  have e8 := runsSeq e7 (runs_pushOne lO S a0 _ (d := .Cs) (by simp [Function.update_apply]))
  refine runsMono (runsCongr e8 (congrArg (st S a0) (funext fun d => ?_))) (fun _ _ => trivial) ?_
  · cases d <;> simp [ctrPre, Function.update_apply] <;> rfl
  · have h1 := bitLen_le_self' w
    have h2 := bitLen_le_self' (w + 1)
    omega

theorem runs_tear (S : KK Z → List Sym) (a0 : List Sym) (w : ℕ) :
    Runs (tearProg lO) (st S a0 (ctrPre w)) (st S a0 (fun _ => [])) (fun _ => True)
      (40 * (w + 1)) := by
  have e1 := runs_dropCtr lO S a0 (ctrPre w) (d := .Cw) w (by simp [ctrPre])
  have e2 := runsSeq e1 (runs_dropCtr lO S a0 _ (d := .Cw') w
    (by simp [ctrPre, Function.update_apply]))
  have e3 := runsSeq e2 (runs_dropCtr lO S a0 _ (d := .Cw1) (w + 1)
    (by simp [ctrPre, Function.update_apply]))
  have e4 := runsSeq e3 (runs_dropCtr lO S a0 _ (d := .Cw1') (w + 1)
    (by simp [ctrPre, Function.update_apply]))
  have e5 := runsSeq e4 (runs_dropCtr lO S a0 _ (d := .Cw2) (w + 2)
    (by simp [ctrPre, Function.update_apply]))
  have e6 := runsSeq e5 (runs_dropCtr lO S a0 _ (d := .Cs) 1
    (by simp [ctrPre, Function.update_apply]))
  refine runsMono (runsCongr e6 (congrArg (st S a0) (funext fun d => ?_))) (fun _ _ => trivial) ?_
  · cases d <;> simp [ctrPre, Function.update_apply]
  · have h1 := bitLen_le_self' w
    have h2 := bitLen_le_self' (w + 1)
    have h3 := bitLen_le_self' (w + 2)
    have h4 := bitLen_le_self' 1
    omega

end Counters

/-! ## The arithmetic core -/

section Core

variable {Z σ Ea Es Er Et Ra Rs Rr Rt : Type} [DecidableEq Z] [DecidableEq Ea] [DecidableEq Es]
  [DecidableEq Er] [DecidableEq Et]

/-- **The arithmetic core**: from the halves on `U`, `V` to the output streams on `C0`, `C1`. -/
def coreProg (lO : Lens σ (Option Sym))
    (ja : Ea → Z) (la : Lens σ Ra) (Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra)
    (js : Es → Z) (ls : Lens σ Rs) (Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs)
    (jr : Er → Z) (lr : Lens σ Rr) (Pr : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr)
    (jt : Et → Z) (lt : Lens σ Rt) (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt) :
    Prog (KK Z) (fun _ => Sym) σ :=
  ((((((((((copyArr lO .U .U2).seq (copyArr lO .V .V2)).seq
    (callInj (emb ![.U, .V, .SS, .Cw, .Cw', .Cw1] ja) la Pa)).seq
    (callInj (emb ![.U2, .V2, .DD, .Cw, .Cw', .Cw1] js) ls Ps)).seq
    (callInj (emb ![.DD, .RR, .Cw1] jr) lr Pr)).seq
    (copyArr lO .SS .SS2)).seq (copyArr lO .RR .RR2)).seq
    (callInj (emb ![.SS, .RR, .EE, .Cw1, .Cw1', .Cw2] ja) la Pa)).seq
    (callInj (emb ![.SS2, .RR2, .FF, .Cw1, .Cw1', .Cw2] js) ls Ps)).seq
    (callInj (emb ![.EE, .C0, .Cw2, .Cw, .Cs] jt) lt Pt)).seq
    (callInj (emb ![.FF, .C1, .Cw2, .Cw, .Cs] jt) lt Pt)

theorem closed_coreProg (lO : Lens σ (Option Sym))
    (ja : Ea → Z) (la : Lens σ Ra) {Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra}
    (js : Es → Z) (ls : Lens σ Rs) {Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs}
    (jr : Er → Z) (lr : Lens σ Rr) {Pr : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr}
    (jt : Et → Z) (lt : Lens σ Rt) {Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt}
    (hPa : Pa.Closed) (hPs : Ps.Closed) (hPr : Pr.Closed) (hPt : Pt.Closed) :
    (coreProg lO ja la Pa js ls Ps jr lr Pr jt lt Pt).Closed := by
  have hc : ∀ a b : KS, (copyArr (Z := Z) lO a b).Closed := fun a b =>
    WP.W9comp.closed_liftRegs lO (closed_passC _ _ _ _)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc _ _, hc _ _⟩, closed_callInj _ _ hPa⟩, closed_callInj _ _ hPs⟩,
    closed_callInj _ _ hPr⟩, hc _ _⟩, hc _ _⟩, closed_callInj _ _ hPa⟩, closed_callInj _ _ hPs⟩,
    closed_callInj _ _ hPt⟩, closed_callInj _ _ hPt⟩

theorem runs_core (lO : Lens σ (Option Sym))
    {ja : Ea → Z} (hja : Function.Injective ja) (la : Lens σ Ra)
    {Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra} {Ca : ℕ} (hA : BinSpec caddC Ea Ra Ca Pa)
    {js : Es → Z} (hjs : Function.Injective js) (ls : Lens σ Rs)
    {Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs} {Cs : ℕ} (hS : BinSpec csubC Es Rs Cs Ps)
    {jr : Er → Z} (hjr : Function.Injective jr) (lr : Lens σ Rr)
    {Pr : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr} {Cr : ℕ} (hR : RSpec 1 Er Rr Cr Pr)
    {jt : Et → Z} (hjt : Function.Injective jt) (lt : Lens σ Rt)
    {Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt} {Ct : ℕ} (hT : TSpec Et Rt Ct Pt)
    (S : KK Z → List Sym) (a0 : List Sym) (w : ℕ) (hw : 1 ≤ w) (u v : List (List CInt))
    (hu : CArrFits w u) (hv : CArrFits w v) (huv : CAligned u v)
    (h0 : CArrFits w (zipC cgate0 u v)) (h1 : CArrFits w (zipC cgate1 u v)) :
    Runs (coreProg lO ja la Pa js ls Ps jr lr Pr jt lt Pt)
      (st S a0 (Function.update (Function.update (ctrPre w) .U (carrSyms w u)) .V
        (carrSyms w v)))
      (st S a0 (Function.update (Function.update (ctrPre w) .C0 (carrSyms w (zipC cgate0 u v)))
        .C1 (carrSyms w (zipC cgate1 u v))))
      (fun _ => True) ((70 + 11 * Ca + 11 * Cs + 2 * Cr + 8 * Ct) * (cvol w u + w + 1)) := by
  have hvu : cvol w v = cvol w u := (cvol_aligned w huv).symm
  have hb : cvol (w + 1) u ≤ 2 * cvol w u := by have := cvol_le_mul w 1 hw u; omega
  have hc : cvol (w + 2) u ≤ 3 * cvol w u := by have := cvol_le_mul w 2 hw u; omega
  have hS1 : ∀ k, cvol k (zipC caddC u v) = cvol k u := fun k => cvol_zipC k caddC u v huv
  have hD1 : ∀ k, cvol k (zipC csubC u v) = cvol k u := fun k => cvol_zipC k csubC u v huv
  have hR1 : ∀ k, cvol k (mapC (rotIPowC 1) (zipC csubC u v)) = cvol k u := fun k => by
    rw [cvol_mapC, hD1]
  have hal := aligned_zip_map caddC csubC (rotIPowC 1) u v
  have hE1 : ∀ k, cvol k (zipC caddC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) =
      cvol k u := fun k => by rw [cvol_zipC k _ _ _ hal, hS1]
  have hF1 : ∀ k, cvol k (zipC csubC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) =
      cvol k u := fun k => by rw [cvol_zipC k _ _ _ hal, hS1]
  have hb1 : bitLen 1 = 1 := by decide
  have e1 := runsMono (runs_copyArr lO S a0 (Function.update (Function.update (ctrPre w) .U
    (carrSyms w u)) .V (carrSyms w v)) (src := .U) (dst := .U2) (by decide) (by decide)
    (by decide) w u (by simp [Function.update_apply]) (by simp [Function.update_apply, ctrPre]))
    (fun _ _ => trivial) (show 9 * cvol w u + 4 ≤ 13 * (cvol w u + w + 1) by omega)
  have e2 := runsSeq e1 (runsMono (runs_copyArr lO S a0 _ (src := .V) (dst := .V2) (by decide)
    (by decide) (by decide) w v (by simp [Function.update_apply])
    (by simp [Function.update_apply, ctrPre])) (fun _ _ => trivial)
    (show 9 * cvol w v + 4 ≤ 13 * (cvol w u + w + 1) by omega))
  have e3 := runsSeq e2 (runsMono (runs_binCall hA hja la ![.U, .V, .SS, .Cw, .Cw', .Cw1]
    (by decide) S a0 _ w w (w + 1) u v hw hw (by omega) hu hv huv (fits_S hw hu hv)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre])) (fun _ _ => trivial)
    (show Ca * (cvol w u + cvol w v + cvol (w + 1) u + w + w + (w + 1) + 1) ≤
      Ca * (4 * (cvol w u + w + 1)) from Nat.mul_le_mul_left _ (by omega)))
  have e4 := runsSeq e3 (runsMono (runs_binCall hS hjs ls ![.U2, .V2, .DD, .Cw, .Cw', .Cw1]
    (by decide) S a0 _ w w (w + 1) u v hw hw (by omega) hu hv huv (fits_D hw hu hv)
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre])) (fun _ _ => trivial)
    (show Cs * (cvol w u + cvol w v + cvol (w + 1) u + w + w + (w + 1) + 1) ≤
      Cs * (4 * (cvol w u + w + 1)) from Nat.mul_le_mul_left _ (by omega)))
  have e5 := runsSeq e4 (runsMono (runs_rCall hR hjr lr ![.DD, .RR, .Cw1] (by decide) S a0 _
    (w + 1) (zipC csubC u v) (by omega) (fits_D hw hu hv) (fits_R hw hu hv)
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre]))
    (fun _ _ => trivial)
    (show Cr * (cvol (w + 1) (zipC csubC u v) + (w + 1) + 1) ≤ Cr * (2 * (cvol w u + w + 1)) from
      Nat.mul_le_mul_left _ (by rw [hD1]; omega)))
  have e6 := runsSeq e5 (runsMono (runs_copyArr lO S a0 _ (src := .SS) (dst := .SS2) (by decide)
    (by decide) (by decide) (w + 1) (zipC caddC u v) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre])) (fun _ _ => trivial)
    (show 9 * cvol (w + 1) (zipC caddC u v) + 4 ≤ 22 * (cvol w u + w + 1) by rw [hS1]; omega))
  have e7 := runsSeq e6 (runsMono (runs_copyArr lO S a0 _ (src := .RR) (dst := .RR2) (by decide)
    (by decide) (by decide) (w + 1) (mapC (rotIPowC 1) (zipC csubC u v))
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre]))
    (fun _ _ => trivial)
    (show 9 * cvol (w + 1) (mapC (rotIPowC 1) (zipC csubC u v)) + 4 ≤ 22 * (cvol w u + w + 1) by
      rw [hR1]; omega))
  have e8 := runsSeq e7 (runsMono (runs_binCall hA hja la ![.SS, .RR, .EE, .Cw1, .Cw1', .Cw2]
    (by decide) S a0 _ (w + 1) (w + 1) (w + 2) (zipC caddC u v)
    (mapC (rotIPowC 1) (zipC csubC u v)) (by omega) (by omega) (by omega) (fits_S hw hu hv)
    (fits_R hw hu hv) hal (fits_E hw hu hv)
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre])) (fun _ _ => trivial)
    (show Ca * (cvol (w + 1) (zipC caddC u v) + cvol (w + 1) (mapC (rotIPowC 1) (zipC csubC u v)) +
      cvol (w + 2) (zipC caddC u v) + (w + 1) + (w + 1) + (w + 2) + 1) ≤
      Ca * (7 * (cvol w u + w + 1)) from Nat.mul_le_mul_left _ (by rw [hS1, hR1, hS1]; omega)))
  have e9 := runsSeq e8 (runsMono (runs_binCall hS hjs ls ![.SS2, .RR2, .FF, .Cw1, .Cw1', .Cw2]
    (by decide) S a0 _ (w + 1) (w + 1) (w + 2) (zipC caddC u v)
    (mapC (rotIPowC 1) (zipC csubC u v)) (by omega) (by omega) (by omega) (fits_S hw hu hv)
    (fits_R hw hu hv) hal (fits_F hw hu hv)
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre])) (fun _ _ => trivial)
    (show Cs * (cvol (w + 1) (zipC caddC u v) + cvol (w + 1) (mapC (rotIPowC 1) (zipC csubC u v)) +
      cvol (w + 2) (zipC caddC u v) + (w + 1) + (w + 1) + (w + 2) + 1) ≤
      Cs * (7 * (cvol w u + w + 1)) from Nat.mul_le_mul_left _ (by rw [hS1, hR1, hS1]; omega)))
  have e10 := runsSeq e9 (runsMono (runs_tCall hT hjt lt ![.EE, .C0, .Cw2, .Cw, .Cs] (by decide)
    S a0 _ (w + 2) w 1 (zipC caddC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v)))
    (by omega) hw (fits_E hw hu hv) (by rw [core0_eq]; exact h0)
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre]))
    (fun _ _ => trivial)
    (show Ct * (cvol (w + 2) (zipC caddC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) +
      cvol w (zipC caddC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) + (w + 2) + w +
      bitLen 1 + 1) ≤ Ct * (4 * (cvol w u + w + 1)) from
      Nat.mul_le_mul_left _ (by rw [hE1, hE1, hb1]; omega)))
  have e11 := runsSeq e10 (runsMono (runs_tCall hT hjt lt ![.FF, .C1, .Cw2, .Cw, .Cs] (by decide)
    S a0 _ (w + 2) w 1 (zipC csubC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v)))
    (by omega) hw (fits_F hw hu hv) (by rw [core1_eq]; exact h1)
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre])
    (by simp [Function.update_apply, ctrPre]) (by simp [Function.update_apply, ctrPre]))
    (fun _ _ => trivial)
    (show Ct * (cvol (w + 2) (zipC csubC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) +
      cvol w (zipC csubC (zipC caddC u v) (mapC (rotIPowC 1) (zipC csubC u v))) + (w + 2) + w +
      bitLen 1 + 1) ≤ Ct * (4 * (cvol w u + w + 1)) from
      Nat.mul_le_mul_left _ (by rw [hF1, hF1, hb1]; omega)))
  refine runsMono (runsCongr e11 (congrArg (st S a0) (funext fun d => ?_))) (fun _ _ => trivial)
    (le_of_eq (by ring))
  cases d <;> simp [Function.update_apply, ctrPre, core0_eq, core1_eq]

end Core

end SubNLogN.Machine.Layer.DrvPreK
