import WP.W9f.Main

/-!
# WP.W9f.Final — `W9_columnSolve` from the sub-kernels

`W9_columnSolve_of_cores`: `W9f_fwdCore Mul → W9f_nyqCore Mul → W9f_moveEntries →
W9_columnSolve Mul`, with program `(colProg K).mapStk toB` (64 scratch stacks) and constant
`kreg K + 6·C_cmp + 300`.
-/

namespace WP.W9f

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

variable {Mul : ℕ → ℕ} (K : Kit Mul)

theorem colCost_le (h : PostHdr) (u2 : ℕ) (a c : ℤ) (μ : ℕ) (hu2 : u2 < h.r)
    (ha : bitLen a.natAbs ≤ h.H) (hc : bitLen c.natAbs ≤ h.H) (hμ : bitLen μ ≤ h.H + 1) :
    colCost K h u2 a c μ ≤ (kreg K + 6 * K.CC + 300) * columnBound Mul h := by
  have hcb := cbase_le Mul h
  have hmv := mvCost_postFields h
  have hhl := hdrLen_eq h
  have hu := WP.W7k2.bitLen_mono (show u2 ≤ h.r by omega)
  have hr2 := WP.W7k2.bitLen_mono (Nat.div_le_self h.r 2)
  have hCB1 : h.hdrLen ≤ columnBound Mul h := by unfold columnBound; omega
  have hCB2 : (h.H + 1) ^ 2 ≤ columnBound Mul h := by unfold columnBound; omega
  have hHsq : h.H + 1 ≤ (h.H + 1) ^ 2 := by nlinarith
  unfold hbits at hhl
  have e1 : K.CC * (bitLen u2 + bitLen (h.r / 2) + 1) ≤ K.CC * (3 * columnBound Mul h) :=
    Nat.mul_le_mul_left _ (by omega)
  have e2 : kreg K * cbase Mul h.t1 h.H h.mt1 ≤ kreg K * columnBound Mul h :=
    Nat.mul_le_mul_left _ hcb
  unfold colCost
  nlinarith [e1, e2]

theorem henc_base (σ0 : HL → List Sym) : henc σ0 (fun f => σ0 f.loc) = σ0 := by
  funext k
  unfold henc
  cases h : F.of k with
  | none => rfl
  | some f => exact congrArg σ0 (F.loc_of_of h)

theorem update_comp_toB (f : BLoc 64 → List Sym) (a : HL) (v : List Sym) :
    (fun l => Function.update f (toB a) v (toB l)) = Function.update (fun l => f (toB l)) a v :=
  Function.update_comp_eq_of_injective f toB_injective a v

theorem colProg_closed : (colProg K).Closed := by
  have hmb : ∀ a b : HL, ((moveBlock a b).liftRegs (lS K)).Closed := fun a b =>
    freeBelow_liftRegs _ _ 0 (by
      simp [Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, popR,
        pushR, skip])
  have hcb : ∀ a b c : HL, ((copyBlock a b c).liftRegs (lS K)).Closed := fun a b c =>
    freeBelow_liftRegs _ _ 0 (by
      simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
        moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip])
  have hdb : ∀ a : HL, ((dropBits a).liftRegs (lS K)).Closed := fun a =>
    freeBelow_liftRegs _ _ 0 (by simp [Prog.FreeBelow, dropBits, popR, restoreR,
      pushR, skip])
  have hmr : ∀ a b : HL, ((moveRec a b).liftRegs (lS K)).Closed := fun a b =>
    freeBelow_liftRegs _ _ 0 (by simp [Prog.FreeBelow, moveRec, moveRecBody,
      Lib.pushR, Lib.popR])
  have huw : ∀ a b : HL, ((unwind a b).liftRegs (lS K)).Closed := fun a b =>
    freeBelow_liftRegs _ _ 0 (by simp [Prog.FreeBelow, unwind, unwindBody, popR,
      pushR])
  have hpa : ∀ gs, (pushAll K gs).Closed := by
    intro gs
    induction gs with
    | nil => trivial
    | cons f gs ih => exact ⟨trivial, ih⟩
  have hmv : ∀ k, (mvSeq (lS K) k).Closed := by
    intro k
    induction k with
    | zero => trivial
    | succ k ih => exact ⟨⟨hmb _ _, trivial, trivial⟩, ih⟩
  have hbk : ∀ k, (bkSeq (lS K) k).Closed := by
    intro k
    induction k with
    | zero => trivial
    | succ k ih => exact ⟨⟨trivial, trivial, hmb _ _⟩, ih⟩
  have hcf : ∀ k dst, (copyField (lS K) k dst).Closed := fun k _ => ⟨hmv k, hcb _ _ _, hbk k⟩
  have hhdr : (hdrPhase K).Closed := ⟨hcf _ _, hcf _ _, trivial, hcf _ _, hcf _ _⟩
  have hsf : ∀ dst sg, (sfBody (lS K) dst sg).Closed := fun _ _ =>
    ⟨hcb _ _ _, trivial, trivial, hmb _ _, trivial, trivial⟩
  have hss : ∀ dst, (sfStep (lS K) dst).Closed := fun _ => ⟨trivial, hsf _ _, hsf _ _⟩
  have hmu : (muStep (lS K)).Closed := ⟨hcb _ _ _, hmb _ _, trivial, trivial⟩
  have hrec : (recPass (lS K)).Closed := ⟨hss _, hss _, hmu⟩
  have hfwd : (fwdProg K).Closed := ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  have hnyq : (nyqProg K).Closed := ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  have hrot : (rotProg K).Closed := ⟨hmr _ _, callI_closed _ _ _ _, huw _ _⟩
  have hbwd : (bwdProg K).Closed := ⟨hrot, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  have hdisp : (dispatch K).Closed :=
    ⟨callI_closed _ _ _ _, hfwd, callI_closed _ _ _ _, hnyq, hbwd⟩
  have hdnm : ∀ f, (dnm K f).Closed := fun _ => ⟨hdb _, trivial⟩
  have hdim : ∀ f, (dim K f).Closed := fun _ => ⟨trivial, hdnm _⟩
  have hcl : (cleanup K).Closed :=
    ⟨hdnm _, hdnm _, hdnm _, hdnm _, hdnm _, hdim _, hdim _, trivial, trivial, trivial⟩
  exact ⟨hpa _, hhdr, hrec, hdisp, hcl⟩

/-- **`W9_columnSolve` from the sub-kernels** (forward core, Nyquist core, entry mover). -/
theorem W9_columnSolve_of_cores (Mul : ℕ → ℕ) (hF : W9f_fwdCore Mul) (hN : W9f_nyqCore Mul)
    (hM : W9f_moveEntries) : W9_columnSolve Mul := by
  obtain ⟨K⟩ := exists_kit Mul hF hN hM
  refine ⟨kreg K + 6 * K.CC + 300, fun _ => ⟨64, KReg K, (colProg K).mapStk toB, le_rfl,
    kreg_finite K, kreg_nonempty K, toB_closed (colProg_closed K), ?_⟩⟩
  intro h u2 c0 c1 alt Y σ restT rq r3 hd hctx hu2 hY hok hO hC3 hr3 hW0 hTR hRQ
  obtain ⟨r0, hr0⟩ := hctx
  apply runs_of_HT
  have hm := HT.colProg K (fun l => σ (toB l)) h u2 c0 c1 alt Y r0 restT rq r3 hd hY hok hO hr3
    hC3 hRQ hr0 hW0 hTR
  rw [henc_base] at hm
  have hpos := hok.2.2.2.1
  refine hm.of_eq ?_ (colCost_le K h u2 _ _ _ hu2 hok.2.2.2.2.2.2.2.2.2.1
    hok.2.2.2.2.2.2.2.2.2.2 (bitLen_postMu _ _ _ _ _ hpos))
  rw [← henc_update, ← henc_update, ← henc_update, henc_base]
  rw [show (Sum.inl LB.TL : BLoc 64) = toB F.TL.loc from rfl,
    show (Sum.inl LB.TR : BLoc 64) = toB F.TR.loc from rfl,
    show (Sum.inl LB.W0 : BLoc 64) = toB F.W0.loc from rfl, update_comp_toB, update_comp_toB,
    update_comp_toB]

#assert_std_axioms colCost_le henc_base update_comp_toB colProg_closed W9_columnSolve_of_cores

end WP.W9f
