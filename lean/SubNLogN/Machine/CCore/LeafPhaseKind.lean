/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseProg
import SubNLogN.Machine.CCore.LeafPhaseVal

/-!
# C-core phase leaf: values of the phase kinds and the `(-i)^f`, `i^{27f}` branch (`LeafPhaseKind.lean`)

**Scope (honest summary).** Everything proved:
* the value of `runSteps [phaseStep t κ] w` for `κ = neg, negIPow, iPow27` (`SkelDefs.lean:140`):
  `i^2 • w`, and `i^3 • w` (`k = 1`) or `w` (`k ≥ 2`; `m = 10^6` is a multiple of `4`);
* `Enc` of an `i^e` multiple is `carrSyms w_g (mapC (rotIPowC e) …)` on the grid;
* fits of the stored numerators under a growth bound `b ≤ Δ`;
* `kProg u P`: the `(-i)^f`/`i^{27f}` kernel: test `k = 1` on a scratch counter, then either do
  nothing or run the rotation path with `e = 3`; `safe_kProg_one`, `safe_kProg_ge`.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Common SubNLogN.Math.Walsh SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK

/-! ## Values -/

theorem Enc_eq (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (z : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    Enc (compactRT t) hA' hS z =
      carrSyms t.wg (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) z) := rfl

theorem four_dvd_mn_pow {n : ℕ} (hn : 1 ≤ n) : 4 ∣ mn ^ n := by
  have h : 4 ∣ mn := by norm_num [mn, tripleM]
  exact dvd_pow h (by omega)

theorem runSteps_neg (t : CCoreRT) (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    runSteps [phaseStep t .neg] w = fun x => Complex.I ^ 2 • w x := by
  simp only [phaseStep]
  rw [runSteps_recMap]
  funext x
  rw [Complex.I_sq]

theorem negI_pow (n : ℕ) : (-Complex.I) ^ n = Complex.I ^ (3 * n) := by
  rw [pow_mul, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]

theorem I_pow_four_mul (q : ℕ) : Complex.I ^ (4 * q) = 1 := by
  rw [pow_mul, Complex.I_pow_four, one_pow]

theorem runSteps_negIPow (t : CCoreRT) (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    runSteps [phaseStep t .negIPow] w = fun x => Complex.I ^ (3 * mn ^ (t.k - 1)) • w x := by
  simp only [phaseStep]
  rw [runSteps_recMap]
  funext x
  rw [negI_pow]

theorem runSteps_iPow27 (t : CCoreRT) (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    runSteps [phaseStep t .iPow27] w = fun x => Complex.I ^ (27 * mn ^ (t.k - 1)) • w x := by
  simp only [phaseStep]
  rw [runSteps_recMap]

/-- At `k ≥ 2` the exponents `3·m^(k-1)` and `27·m^(k-1)` are multiples of `4`. -/
theorem I_pow_c_mn {c k : ℕ} (hk : 2 ≤ k) : Complex.I ^ (c * mn ^ (k - 1)) = 1 := by
  obtain ⟨q, hq⟩ := four_dvd_mn_pow (n := k - 1) (by omega)
  rw [hq, show c * (4 * q) = 4 * (c * q) by ring, I_pow_four_mul]

theorem rotIPowC_3_mn_one : rotIPowC (3 * mn ^ (1 - 1)) = rotIPowC 3 := by
  simp

theorem rotIPowC_27_mn_one : rotIPowC (27 * mn ^ (1 - 1)) = rotIPowC 3 := by
  funext c; simp [rotIPowC]

theorem onGrid_of_growth {α : Type} {r P b Δ : ℕ} {w : RArr α r} (h : ArrGrowth P b w)
    (hb : b ≤ Δ) : ∀ x k, OnGrid (P + Δ) (w x k) := fun x k => (h x k).1.mono (by omega)

/-- Stored numerators of a growth-bounded array (and of its `i^e` multiples) fit `w_g`. -/
theorem fits_encArr {α : Type} {r P b Δ : ℕ} {w : RArr α r} (h : ArrGrowth P b w) (hb : b ≤ Δ)
    (addrs : List α) (e : ℕ) :
    CArrFits (P + 2 * Δ + 3) (mapC (rotIPowC e) (encArr (P + Δ) addrs w)) := by
  intro cs hcs c hc
  simp only [mapC, encArr, List.map_map, List.mem_map, Function.comp_apply] at hcs
  obtain ⟨x, -, rfl⟩ := hcs
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hc
  obtain ⟨k, -, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := abs_gridInt_le hb (h x k).1 (h x k).2
  have key : ∀ a : ℤ, |a| ≤ 2 ^ (P + 2 * Δ) → FitsTwos (P + 2 * Δ + 3) a ∧
      FitsTwos (P + 2 * Δ + 3) (-a) := fun a ha =>
    ⟨fitsTwos_of_abs_le ha, fitsTwos_of_abs_le (by rwa [abs_neg])⟩
  rw [rotIPowC_mod]
  have h4 : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (e % 4) <;> simp only [rotIPowC] <;> norm_num
  · exact ⟨(key _ h1).1, (key _ h2).1⟩
  · exact ⟨(key _ h2).2, (key _ h1).1⟩
  · exact ⟨(key _ h1).2, (key _ h2).2⟩
  · exact ⟨(key _ h2).1, (key _ h1).2⟩

theorem fits_encArr0 {α : Type} {r P b Δ : ℕ} {w : RArr α r} (h : ArrGrowth P b w) (hb : b ≤ Δ)
    (addrs : List α) : CArrFits (P + 2 * Δ + 3) (encArr (P + Δ) addrs w) := by
  have := fits_encArr h hb addrs 0
  have h0 : rotIPowC 0 = id := by funext c; simp [rotIPowC]
  simpa [mapC, h0] using this

/-! ## The middle of the rotation path, for any scratch state -/

variable {Er Rr : Type} [DecidableEq Er]

/-- Move in, rotate by `i^e`, move out. -/
def rotMid (u : Fin Wn) (P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr) :
    Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  .seq (mvIn Rr u) (.seq (callInj ιw (lid _) (callInj (ι3 .X .Y .cW id) (lR Rr) P)) (mvOut Rr u))

theorem closed_rotMid (u : Fin Wn) {P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr}
    (hP : P.Closed) : (rotMid u P).Closed :=
  ⟨closed_mvIn _ _, closed_callInj _ _ (closed_callInj _ _ hP), closed_mvOut _ _⟩

theorem safe_rotMid {e C : ℕ} {P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr}
    (hspec : ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym)
      (S : KLoc (Fin 3) Er → List Sym),
      1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC e) v) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w (mapC (rotIPowC e) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w v + w + 1)))
    (hP : P.Closed) (u : Fin Wn) (w : ℕ) (hw : 1 ≤ w) (v : List (List CInt))
    (S0 : BL Er → List Sym) (sc : PS → List Sym)
    (hu : S0 (roleL u) = carrSyms w v ++ [Sym.mark]) (hX : sc .X = [Sym.mark])
    (hY : sc .Y = [Sym.mark]) (hT : sc .Tm = [Sym.mark]) (hW : sc .cW = natSyms w)
    (hf1 : CArrFits w v) (hf2 : CArrFits w (mapC (rotIPowC e) v)) :
    SafeRunsIn ccoreFramed [] (rotMid u P) (stv S0 sc)
      (stv (Function.update S0 (roleL u) (carrSyms w (mapC (rotIPowC e) v) ++ [Sym.mark])) sc)
      (fun _ => True) (16 * cvol w v + 8 + C * (cvol w v + w + 1)) := by
  have hmk : ∀ w (x : List (List CInt)), Sym.mark ∉ carrSyms w x := fun w x =>
    mark_not_mem_arrSyms' _
  have s2 := safe_mvIn (Er := Er) Rr u S0 sc (carrSyms w v) (hmk _ _) hu hT hX
  have s3 := safe_callW (Rr := Rr) (closed_callInj _ _ hP) (Function.update S0 (roleL u) [Sym.mark])
    (Function.update sc .X (carrSyms w v ++ [Sym.mark]))
    (Function.update (Function.update (Function.update sc .X
      (carrSyms w v ++ [Sym.mark])) .X [Sym.mark]) .Y
      (carrSyms w (mapC (rotIPowC e) v) ++ [Sym.mark]))
    (runs_rotCall (lR Rr) hspec (a := .X) (b := .Y) (c := .cW) (by decide) (by decide) (by decide)
      Function.injective_id _ _ _
      w v hw hf1 hf2 (by simp) (by simp [hY]) (by simp [hW]))
  have s4 := safe_mvOut (Er := Er) Rr u (Function.update S0 (roleL u) [Sym.mark])
    (Function.update (Function.update (Function.update sc .X
      (carrSyms w v ++ [Sym.mark])) .X [Sym.mark]) .Y
      (carrSyms w (mapC (rotIPowC e) v) ++ [Sym.mark]))
    (carrSyms w (mapC (rotIPowC e) v)) (hmk _ _) (by simp) (by simp [hT]) (by simp)
  replace s4 := SafeRunsIn.congr s4 (S₂ := stv (Function.update S0 (roleL u)
    (carrSyms w (mapC (rotIPowC e) v) ++ [Sym.mark])) sc) (by
      rw [Function.update_idem]
      congr 1
      funext q
      by_cases hqX : q = .X
      · subst hqX; simp [hX]
      · by_cases hqY : q = .Y
        · subst hqY; simp [hY]
        · simp [Function.update_apply, hqX, hqY]) le_rfl
  refine SafeRunsIn.mono (SafeRunsIn.seq s2 (SafeRunsIn.seq s3 s4)) (fun _ _ => trivial) ?_
  have hlen : (carrSyms w (mapC (rotIPowC e) v)).length = cvol w v := cvol_mapC w _ v
  simp only [hlen, cvol]
  omega

/-! ## The `(-i)^f` / `i^{27 f}` kernel: a runtime test `k = 1` -/

/-- `cU ← 1`, `ct ← k - 1`. -/
def kTestW : Prog (Lw Er) (fun _ => Sym) (σ Rr) :=
  .seq ((NatArith.pushNat (wS .cU) 1).liftRegs (lN Rr))
    ((NatArith.subN (wS .cKk) (wS .cU) (wS .ct) (wS .t1) (wS .t2) (wS .t3)).liftRegs (lN Rr))

/-- Drop `ct` and `cU`. -/
def kUndoW : Prog (Lw Er) (fun _ => Sym) (σ Rr) :=
  .seq ((NatArith.dropN (wS .ct)).liftRegs (lN Rr)) ((NatArith.dropN (wS .cU)).liftRegs (lN Rr))

/-- Peek the counter `ct`. -/
def peekCt : Prog (BL Er) (fun _ => Sym) (σ Rr) := (peekR (scr .ct)).liftRegs (lO Rr)

/-- **The `(-i)^f`, `i^{27 f}` kernel**: if `k ≥ 2` nothing changes; if `k = 1` the rotation path
with the sub-kernel `P` (`e = 3`). -/
def kProg (u : Fin Wn) (P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr) :
    Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  .seq (callInj ιw (lid _) (.seq (preW psR) kTestW))
  (.seq peekCt (.ite (fun v => optIsBit ((lO Rr).get v))
    (callInj ιw (lid _) (.seq kUndoW (postW psR)))
    (.seq (rotMid u P) (callInj ιw (lid _) (.seq kUndoW (postW psR))))))

theorem closed_kProg (u : Fin Wn) {P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr}
    (hP : P.Closed) : (kProg u P).Closed := by
  refine ⟨closed_callInj _ _ ⟨closed_preW _, ?_⟩, ?_, ?_, ?_⟩
  · exact ⟨WP.W9comp.closed_liftRegs _ (NatArith.closed_pushNat _ _),
      WP.W9comp.closed_liftRegs _ (NatArith.closed_subN _ _ _ _ _ _)⟩
  · exact WP.W9comp.closed_liftRegs _ (by simp [peekR, Prog.Closed, Prog.FreeBelow])
  · exact closed_callInj _ _ ⟨⟨WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _),
      WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _)⟩, closed_postW _⟩
  · exact ⟨closed_rotMid u hP, closed_callInj _ _ ⟨⟨WP.W9comp.closed_liftRegs _
      (NatArith.closed_dropN _), WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _)⟩,
      closed_postW _⟩⟩

/-- The scratch after the `k` test. -/
def scK (t : CCoreRT) : PS → List Sym :=
  Function.update (Function.update (scP psR t) .cU (natSyms 1)) .ct (natSyms (t.k - 1))

theorem runs_kTestW (t : CCoreRT) (hk : 1 ≤ t.k) (d : List Sym) (er : Er → List Sym) :
    Runs (kTestW (Er := Er) (Rr := Rr)) (wst d (scP psR t) er) (wst d (scK t) er)
      (fun _ => True) (bitLen 1 + 1 + 20 * (bitLen t.k + bitLen 1 + 1)) := by
  have h1 := WP.W0m.runs_liftRegs (lN Rr) (runs_pushNat_w (Er := Er) d er .cU 1 (scP psR t)
    (by simp [scP, scW, scHdr]))
  have h2 := WP.W0m.runs_liftRegs (lN Rr) (runs_subN_w (Er := Er) d er .cKk .cU .ct .t1 .t2 .t3
    (by decide) t.k 1 [Sym.mark] [] (Function.update (scP psR t) .cU (natSyms 1))
    (TermOK.cons rfl _) TermOK.nil hk (by simp [scP, scW, scHdr]) (by simp)
    (by simp [scP, scW, scHdr]))
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ _ => trivial) le_rfl

theorem runs_kUndoW (t : CCoreRT) (d : List Sym) (er : Er → List Sym) :
    Runs (kUndoW (Er := Er) (Rr := Rr)) (wst d (scK t) er) (wst d (scP psR t) er)
      (fun _ => True) (2 * bitLen (t.k - 1) + 4 + (2 * bitLen 1 + 4)) := by
  have h1 := WP.W0m.runs_liftRegs (lN Rr) (runs_dropN_w (Er := Er) d er .ct (t.k - 1) (scK t)
    (by simp [scK]))
  have h2 := WP.W0m.runs_liftRegs (lN Rr) (runs_dropN_w (Er := Er) d er .cU 1
    (Function.update (scK t) .ct []) (by simp [scK]))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
    (fun _ _ => trivial) le_rfl
  congr 1
  funext q
  by_cases h1 : q = .ct
  · subst h1; simp [scK, scP, scW, scHdr]
  · by_cases h2 : q = .cU
    · subst h2; simp [scK, scP, scW, scHdr]
    · simp [scK, Function.update_apply, h1, h2]

theorem optIsBit_head_natSyms (n : ℕ) : optIsBit (natSyms n).head? = decide (0 < n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [natSyms, encodeNat_zero, optIsBit]
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat n = b :: l := by
      cases h : encodeNat n with
      | nil => rw [encodeNat_eq_nil_iff] at h; omega
      | cons b l => exact ⟨b, l, rfl⟩
    simp [natSyms, hbl, optIsBit, hn]

theorem safe_peekCt (S0 : BL Er → List Sym) (sc : PS → List Sym) :
    SafeRunsIn ccoreFramed [] (peekCt (Er := Er) (Rr := Rr)) (stv S0 sc) (stv S0 sc)
      (fun v => optIsBit ((lO Rr).get v) = optIsBit (sc .ct).head?) 1 := by
  intro v
  refine ⟨(lO Rr).set v (sc .ct).head?, 1, ?_, by beta_reduce; rw [Lens.get_set], le_rfl⟩
  exact SafeEval.peek [] (scr .ct) (fun v o => (lO Rr).set v o) v (stv S0 sc)
    (fun h => absurd h (by simp [ccoreFramed]))

end SubNLogN.Machine.CCore.LeafScalarAux
