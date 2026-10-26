/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernelPhase

/-!
# C-core leaf kernel: the runtime loop (`CCore/LeafKernelLoop.lean`)

`runs_phaseL`: the loop of `phaseL` (`CCore/LeafKernelProg.lean`) runs `e` individual kernels on
the array, one per selected-bit field of the chunks `j0, …, j0+e−1` (named hypothesis: the driver's
kernel contract `DrvCKernelStmt`, in the form of its specification), with the record weight `W`
shifted right by `K` bits after each kernel and the counter decremented.
-/

namespace SubNLogN.Machine.CCore.LeafKernelAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Walsh SubNLogN.Math.Networks SubNLogN.Math.Networks.CCoreAux
open SubNLogN.Machine.Layer

/-! ## Loop arithmetic and values -/

section LoopMath

variable {A K D S r : ℕ}

/-- The first `i` kernels of the group (or `z` if the group does not fit). -/
noncomputable def gatesUpTo (ρ : Fin K) (j0 : ℕ) (z : RArr (LayerAddr A K D S) r) (i : ℕ) :
    RArr (LayerAddr A K D S) r :=
  if h : j0 + i ≤ D then gatesR ρ j0 i h z else z

theorem gatesUpTo_zero (ρ : Fin K) (j0 : ℕ) (z : RArr (LayerAddr A K D S) r) :
    gatesUpTo ρ j0 z 0 = z := by
  unfold gatesUpTo
  split <;> rfl

theorem gatesUpTo_eq (ρ : Fin K) (j0 i : ℕ) (h : j0 + i ≤ D) (z : RArr (LayerAddr A K D S) r) :
    gatesUpTo ρ j0 z i = gatesR ρ j0 i h z := by
  unfold gatesUpTo
  rw [dif_pos h]

theorem gatesUpTo_succ (ρ : Fin K) (j0 : ℕ) (z : RArr (LayerAddr A K D S) r) (i : ℕ)
    (h : j0 + i < D) :
    gatesUpTo ρ j0 z (i + 1) = gateR ρ ⟨j0 + i, h⟩ (topC A K D S) (gatesUpTo ρ j0 z i) := by
  rw [gatesUpTo_eq ρ j0 (i + 1) (by omega), gatesUpTo_eq ρ j0 i (by omega)]
  rfl

theorem growth_gatesUpTo (ρ : Fin K) (j0 : ℕ) {P b : ℕ} {z : RArr (LayerAddr A K D S) r}
    (hz : ArrGrowth P b z) (i : ℕ) (h : j0 + i ≤ D) :
    ArrGrowth P (b + i) (gatesUpTo ρ j0 z i) := by
  rw [gatesUpTo_eq ρ j0 i h]
  exact growth_gatesR ρ j0 i h hz

theorem wSel_div (K D S ρ j0 i : ℕ) (h : j0 + i < D) :
    wSel K D S ρ j0 / 2 ^ (K * i) = wSel K D S ρ (j0 + i) := by
  unfold wSel
  have e1 : ρ + K * (D - 1 - j0) = (ρ + K * (D - 1 - (j0 + i))) + K * i := by
    have : D - 1 - j0 = (D - 1 - (j0 + i)) + i := by omega
    rw [this, Nat.mul_add]
    ring
  rw [e1, pow_add 2 (ρ + K * (D - 1 - (j0 + i))) (K * i), ← Nat.mul_assoc,
    Nat.mul_div_cancel _ (pow_pos two_pos _)]

theorem div_two_pow_succ (a K i : ℕ) : a / 2 ^ (K * i) / 2 ^ K = a / 2 ^ (K * (i + 1)) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ]

theorem zerosLead_le_length : ∀ l : List Bool, zerosLead l ≤ l.length
  | [] => le_rfl
  | false :: l => by
    have := zerosLead_le_length l
    simp only [zerosLead, List.length_cons]
    omega
  | true :: l => by simp [zerosLead]

theorem one_le_wSel {S : ℕ} (hS : 0 < S) (K D ρ j : ℕ) : 1 ≤ wSel K D S ρ j := by
  unfold wSel
  exact Nat.mul_pos hS (pow_pos two_pos _)

theorem length_recBlocks_flatten (F : ℕ) (hA : 0 < A) (hS : 0 < S) (ρ : Fin K) (j : Fin D)
    (z : RArr (LayerAddr A K D S) r) :
    (recBlocks F hA hS ρ j z).flatten.length = (layerAddrs A K D S hA hS).length := by
  rw [recBlocks_flatten, encArr, List.length_map]

/-- `recBlocks_gate` at precision `P + Δ`, from a growth bound `b < Δ`. -/
theorem recBlocks_gate_of_growth {P Δ b : ℕ} (hbΔ : b + 1 ≤ Δ) (hA : 0 < A) (hS : 0 < S)
    (ρ : Fin K) (j : Fin D) (z : RArr (LayerAddr A K D S) r) (hz : ArrGrowth P b z) :
    (recBlocks (P + Δ) hA hS ρ j z).map (cgateBlock (wSel K D S ρ j)) =
      recBlocks (P + Δ) hA hS ρ j (gateR ρ j (topC A K D S) z) := by
  obtain ⟨G, hG⟩ : ∃ G, P + Δ = G + 1 := ⟨P + Δ - 1, by omega⟩
  rw [hG]
  exact recBlocks_gate hA hS ρ j z (fun x k => (hz x k).1.mono (by omega))

end LoopMath

/-! ## The loop -/

/-- `peek` as a `Runs` fact with its register value. -/
theorem runs_peekR' {K : Type} [DecidableEq K] (k : K) (S : K → List Sym) :
    Runs (peekR k) S S (fun r => r = (S k).head?) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.peek [] k _ v stk, ⟨rfl, rfl⟩, le_rfl⟩

/-- The array after `i` kernels. -/
noncomputable def ioFun {A K D S r : ℕ} (P Δ : ℕ) (hA : 0 < A) (hS : 0 < S) (ρ : Fin K)
    (j0 : ℕ) (z : RArr (LayerAddr A K D S) r) (tio : List Sym) (i : ℕ) : List Sym :=
  carrSyms (P + 2 * Δ + 3) (encArr (P + Δ) (layerAddrs A K D S hA hS) (gatesUpTo ρ j0 z i)) ++ tio

/-- The record weight after `i` shifts. -/
def wFun (K D S ρ j0 : ℕ) (i : ℕ) : ℕ := wSel K D S ρ j0 / 2 ^ (K * i)

/-- The per-iteration cost bound. -/
def costL (Cc C2 C3 V1 M W0 w Kv e : ℕ) : ℕ :=
  Cc * (V1 + M * (bitLen W0 + 1) + w + 1) + (C2 * (Kv + bitLen Kv + 1) + (C3 * (bitLen e + 1) + 1))

section PhaseL

variable {Ec : Type} [DecidableEq Ec] {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

/-- The loop state with `n` iterations left. -/
def stL (B3 : LI Ec m1 m2 m3 → List Sym) (ioF : ℕ → List Sym) (WF : ℕ → ℕ) (e n : ℕ) :
    LI Ec m1 m2 m3 → List Sym :=
  Function.update (Function.update (Function.update B3 ioI (ioF (e - n))) (sc iCt) (natSyms n))
    (sc iW) (natSyms (WF (e - n)))

theorem runs_peekW (k : LI Ec m1 m2 m3) (S : LI Ec m1 m2 m3 → List Sym) :
    Runs (((peekR k).liftRegs lW : PL Ec m1 m2 m3 Rc R1 R2 R3)) S S
      (fun v => lW.get v = (S k).head?) 1 :=
  runs_lift lW (runs_peekR' k S)

/-- The DrvC kernel on `io`, with `W` and `w` on their stacks. -/
theorem runs_drvP {Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc} {Cc : ℕ}
    (hDrv : ∀ (W w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
      (S : KLoc (Fin 3) Ec → List Sym),
      1 ≤ W → 1 ≤ w → (∀ blk ∈ blks, CGateBlockOK W blk) →
      CArrFits w blks.flatten → CArrFits w (blks.map (cgateBlock W)).flatten →
      BlkTerm rest → TermOK r1 → TermOK r2 →
      S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms W ++ r1 →
      S (.inl 2) = natSyms w ++ r2 →
      Runs Pc S (Function.update S (.inl 0) (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest))
        (fun _ => True) (Cc * (cvol w blks.flatten + blks.flatten.length * (bitLen W + 1) + w + 1)))
    (S : LI Ec m1 m2 m3 → List Sym) (W w : ℕ) (blks : List (List (List CInt))) (rest : List Sym)
    (hW1 : 1 ≤ W) (hw1 : 1 ≤ w) (hok : ∀ blk ∈ blks, CGateBlockOK W blk)
    (hf1 : CArrFits w blks.flatten) (hf2 : CArrFits w (blks.map (cgateBlock W)).flatten)
    (hrest : BlkTerm rest) (hio : S ioI = carrSyms w blks.flatten ++ rest)
    (hWs : S (sc iW) = natSyms W) (hws : S (sc iWg) = natSyms w) :
    Runs (callInj (ιC Ec m1 m2 m3) (lC (R1 := R1) (R2 := R2) (R3 := R3)) Pc) S
      (Function.update S ioI (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest))
      (fun _ => True) (Cc * (cvol w blks.flatten + blks.flatten.length * (bitLen W + 1) + w + 1)) :=
  runs_inj_upd1 (ιC_inj Ec m1 m2 m3) lC S (.inl 0) _
    (hDrv W w blks rest [] [] _ hW1 hw1 hok hf1 hf2 hrest TermOK.nil TermOK.nil
      (by show S ioI = _; exact hio) (by show S (sc iW) = _; rw [hWs, List.append_nil])
      (by show S (sc iWg) = _; rw [hws, List.append_nil]))

theorem decide_ne_zero_eq (n : ℕ) : decide (n ≠ 0) = decide (0 < n) :=
  decide_eq_decide.2 Nat.pos_iff_ne_zero.symm

/-- **The runtime loop**: `e` individual kernels on the array (named kernel specifications for
DrvC, `shrVar`, `decNat`). -/
theorem runs_phaseL {Pc : Prog (KLoc (Fin 3) Ec) (fun _ => Sym) Rc}
    {P2 : Prog (Loc 2 m2) (fun _ => Sym) R2} {P3 : Prog (Loc 1 m3) (fun _ => Sym) R3}
    {Cc C2 C3 : ℕ}
    (hDrv : ∀ (W w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
      (S : KLoc (Fin 3) Ec → List Sym),
      1 ≤ W → 1 ≤ w → (∀ blk ∈ blks, CGateBlockOK W blk) →
      CArrFits w blks.flatten → CArrFits w (blks.map (cgateBlock W)).flatten →
      BlkTerm rest → TermOK r1 → TermOK r2 →
      S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms W ++ r1 →
      S (.inl 2) = natSyms w ++ r2 →
      Runs Pc S (Function.update S (.inl 0) (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest))
        (fun _ => True) (Cc * (cvol w blks.flatten + blks.flatten.length * (bitLen W + 1) + w + 1)))
    (hs2 : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m2 → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P2 S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
        (C2 * (min c (bitLen a) + bitLen c + 1)))
    (hd : ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m3 → List Sym), TermOK rx →
      S (.inl 0) = natSyms (a + 1) ++ rx →
      Runs P3 S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
        (C3 * (zerosLead (encodeNat (a + 1)) + 1)))
    {A K D nS r : ℕ} (hA : 0 < A) (hS : 0 < nS) (P Δ b : ℕ) (ρ : Fin K) (j0 e : ℕ)
    (hg : j0 + e ≤ D) (z : RArr (LayerAddr A K D nS) r) (tio : List Sym) (htio : BlkTerm tio)
    (hz : ArrGrowth P b z) (hbe : b + e ≤ Δ) (V1 : ℕ)
    (hV1 : ∀ i ≤ e, cvol (P + 2 * Δ + 3)
      (encArr (P + Δ) (layerAddrs A K D nS hA hS) (gatesUpTo ρ j0 z i)) ≤ V1)
    (B3 : LI Ec m1 m2 m3 → List Sym) (hio : B3 ioI = ioFun P Δ hA hS ρ j0 z tio 0)
    (hCt : B3 (sc iCt) = natSyms e) (hW : B3 (sc iW) = natSyms (wSel K D nS ρ j0))
    (hWg : B3 (sc iWg) = natSyms (P + 2 * Δ + 3)) (hK : B3 (sc iK) = natSyms K) :
    Runs (phaseL (m1 := m1) (R1 := R1) Pc P2 P3) B3
      (stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e 0) (fun _ => True)
      (1 + loopCost (fun _ => costL Cc C2 C3 V1 (layerAddrs A K D nS hA hS).length
        (wSel K D nS ρ j0) (P + 2 * Δ + 3) K e) e) := by
  have hst_e : stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e e = B3 := by
    have hw0 : wFun K D nS ρ j0 0 = wSel K D nS ρ j0 := by simp [wFun]
    simp only [stL, Nat.sub_self]
    rw [← hio, hw0, ← hCt, ← hW, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  have h0 : Runs ((peekR (sc iCt)).liftRegs lW : PL Ec m1 m2 m3 Rc R1 R2 R3) B3
      (stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e e)
      (fun v => loopTest v = decide (0 < e)) 1 := by
    rw [hst_e]
    refine WP.W9comp.runs_mono (runs_peekW (sc iCt) B3) (fun v hv => ?_) le_rfl
    have hv' : lW.get v = (B3 (sc iCt)).head? := hv
    have h1 := NatArith.optIsBit_head_natSyms e [] TermOK.nil
    rw [List.append_nil] at h1
    simp only [loopTest, hv', hCt, h1, decide_ne_zero_eq]
  have hstep : ∀ n, n < e → RunsIn [] (bodyL (m1 := m1) (R1 := R1) Pc P2 P3)
      (stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e (n + 1))
      (stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e n)
      (fun v => loopTest v = decide (0 < n))
      (costL Cc C2 C3 V1 (layerAddrs A K D nS hA hS).length (wSel K D nS ρ j0) (P + 2 * Δ + 3)
        K e) := by
    intro n hn
    obtain ⟨i, hi⟩ : ∃ i, e - (n + 1) = i := ⟨_, rfl⟩
    have hni : e - n = i + 1 := by omega
    have hji : j0 + i < D := by omega
    have hgr : ArrGrowth P (b + i) (gatesUpTo ρ j0 z i) := growth_gatesUpTo ρ j0 hz i (by omega)
    have hbi : b + i + 1 ≤ Δ := by omega
    have hflat := recBlocks_flatten (P + Δ) hA hS ρ ⟨j0 + i, hji⟩ (gatesUpTo ρ j0 z i)
    have hgate := recBlocks_gate_of_growth hbi hA hS ρ ⟨j0 + i, hji⟩ (gatesUpTo ρ j0 z i) hgr
    have hflat' := recBlocks_flatten (P + Δ) hA hS ρ ⟨j0 + i, hji⟩
      (gateR ρ ⟨j0 + i, hji⟩ (topC A K D nS) (gatesUpTo ρ j0 z i))
    have hsucc := gatesUpTo_succ ρ j0 z i hji
    have hWi : wSel K D nS ρ j0 / 2 ^ (K * i) = wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D) :=
      wSel_div K D nS ρ j0 i hji
    have st_io : stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e (n + 1) ioI =
        carrSyms (P + 2 * Δ + 3) (recBlocks (P + Δ) hA hS ρ (⟨j0 + i, hji⟩ : Fin D)
          (gatesUpTo ρ j0 z i)).flatten ++ tio := by
      simp only [stL]
      rw [hi, hflat]
      simp [ioFun]
    have st_W : stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e (n + 1) (sc iW) =
        natSyms (wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D)) := by
      simp only [stL]
      rw [hi, ← hWi]
      simp [wFun]
    have st_Wg : stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e (n + 1) (sc iWg) =
        natSyms (P + 2 * Δ + 3) := by
      simp [stL, hWg]
    have st_K : stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e (n + 1) (sc iK) =
        natSyms K := by
      simp [stL, hK]
    have st_Ct : stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e (n + 1) (sc iCt) =
        natSyms (n + 1) := by
      simp [stL]
    have v_io : carrSyms (P + 2 * Δ + 3) ((recBlocks (P + Δ) hA hS ρ (⟨j0 + i, hji⟩ : Fin D)
        (gatesUpTo ρ j0 z i)).map (cgateBlock (wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D)))).flatten ++
        tio = ioFun P Δ hA hS ρ j0 z tio (e - n) := by
      rw [hgate, hflat', ioFun, hni, hsucc]
    have v_W : wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D) / 2 ^ K = wFun K D nS ρ j0 (e - n) := by
      rw [wFun, hni, ← div_two_pow_succ, hWi]
    refine RunsIn.iff_runs.2 (WP.W9comp.runs_mono (WP.W9comp.runs_congr
      (WP.W9comp.runs_seq
        (runs_drvP (R1 := R1) (R2 := R2) (R3 := R3) hDrv _ (wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D))
          (P + 2 * Δ + 3) (recBlocks (P + Δ) hA hS ρ (⟨j0 + i, hji⟩ : Fin D) (gatesUpTo ρ j0 z i)) tio
          (one_le_wSel hS _ _ _ _) (by omega) (recBlocks_ok _ hA hS _ _ _)
          (by rw [hflat]; exact encArr_fits (by omega) hA hS _ hgr)
          (by rw [hgate, hflat']; exact encArr_fits (by omega) hA hS _ (growth_gateR ρ _ hgr))
          htio st_io st_W st_Wg)
      (WP.W9comp.runs_seq (runs_shrP (Rc := Rc) (R1 := R1) (R3 := R3) hs2 _
          (wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D)) K (by simp [st_W]) (by simp [st_K]))
      (WP.W9comp.runs_seq (runs_decP (Rc := Rc) (R1 := R1) (R2 := R2) hd iCt _ n
          (by simp [st_Ct]))
        (runs_peekW (sc iCt) _)))) ?_) ?_ ?_)
    · rw [v_io, v_W, List.append_nil, List.append_nil]
      funext x
      rcases x with i' | i' | e'
      · fin_cases i' <;> simp [stL, hni]
      · fin_cases i' <;> simp +decide [stL, hni, Function.update_apply]
      · simp [stL]
    · intro v hv
      have hv' : lW.get v = (natSyms n ++ []).head? := by
        have h := hv
        simp only [Function.update_self] at h
        exact h
      have h1 := NatArith.optIsBit_head_natSyms n [] TermOK.nil
      simp only [loopTest, hv', h1, decide_ne_zero_eq]
    · unfold costL
      have c1 : cvol (P + 2 * Δ + 3) (recBlocks (P + Δ) hA hS ρ (⟨j0 + i, hji⟩ : Fin D)
          (gatesUpTo ρ j0 z i)).flatten ≤ V1 := by
        rw [hflat]
        exact hV1 i (by omega)
      have c2 := length_recBlocks_flatten (P + Δ) hA hS ρ ⟨j0 + i, hji⟩ (gatesUpTo ρ j0 z i)
      have c3 : bitLen (wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D)) ≤ bitLen (wSel K D nS ρ j0) :=
        NatArith.bitLen_mono'' (by rw [← hWi]; exact Nat.div_le_self _ _)
      have c4 : min K (bitLen (wSel K D nS ρ (⟨j0 + i, hji⟩ : Fin D))) ≤ K := min_le_left _ _
      have c5 : zerosLead (encodeNat (n + 1)) ≤ bitLen e :=
        (zerosLead_le_length _).trans (NatArith.bitLen_mono'' (by omega))
      rw [c2]
      gcongr
  have hL := RunsIn.seq_loop (ρ := [])
    (P₀ := ((peekR (sc iCt)).liftRegs lW : PL Ec m1 m2 m3 Rc R1 R2 R3))
    (p := bodyL (m1 := m1) (R1 := R1) Pc P2 P3) (c := loopTest)
    (st := stL B3 (ioFun P Δ hA hS ρ j0 z tio) (wFun K D nS ρ j0) e)
    (B := fun _ => costL Cc C2 C3 V1 (layerAddrs A K D nS hA hS).length (wSel K D nS ρ j0)
      (P + 2 * Δ + 3) K e) (N := e) (T₀ := 1) (S := B3) (RunsIn.iff_runs.2 h0) hstep
  exact WP.W9comp.runs_mono (RunsIn.iff_runs.1 hL) (fun _ _ => trivial) le_rfl

end PhaseL

end SubNLogN.Machine.CCore.LeafKernelAux
