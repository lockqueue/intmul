/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanSetup

/-!
# Layer driver phase scan: the whole kernel (`Machine/Layer/DrvPhaseScanMain.lean`)

**Scope (honest summary).** The kernel `phaseProg` (set-up, record loop, clean-up) and its exact
run `runs_phaseProg` with an explicit cost; no `sorry`. The contract itself is proved in
`Machine/Layer/DrvPhaseScan.lean`.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability

/-- The parameter stacks, in header order `[S, K, ρ, D, c, o, w1, w2]`. -/
def pStacks : List PL := [kPS, kPK, kPR, kPD, kPC, kPO, kPW1, kPW2]

theorem pStacks_nodup : pStacks.Nodup := by simp [pStacks]

theorem pStacks_ok : ∀ p ∈ pStacks, p ≠ sH ∧ p ≠ kHs ∧ p ≠ kTm := by simp [pStacks]

theorem not_mem_pStacks {k : PL} (h1 : k ≠ kPS) (h2 : k ≠ kPK) (h3 : k ≠ kPR) (h4 : k ≠ kPD)
    (h5 : k ≠ kPC) (h6 : k ≠ kPO) (h7 : k ≠ kPW1) (h8 : k ≠ kPW2) : k ∉ pStacks := by
  simp [pStacks, h1, h2, h3, h4, h5, h6, h7, h8]

theorem kHs_nm : kHs ∉ pStacks := not_mem_pStacks (by simp) (by simp) (by simp) (by simp)
  (by simp) (by simp) (by simp) (by simp)
theorem kY_nm : kY ∉ pStacks := not_mem_pStacks (by simp) (by simp) (by simp) (by simp)
  (by simp) (by simp) (by simp) (by simp)
theorem kRr_nm : kRr ∉ pStacks := not_mem_pStacks (by simp) (by simp) (by simp) (by simp)
  (by simp) (by simp) (by simp) (by simp)
theorem kU_nm : kU ∉ pStacks := not_mem_pStacks (by simp) (by simp) (by simp) (by simp)
  (by simp) (by simp) (by simp) (by simp)
theorem sA_nm : sA ∉ pStacks := not_mem_pStacks (by simp) (by simp) (by simp) (by simp)
  (by simp) (by simp) (by simp) (by simp)

/-! ## Set-up -/

/-- Set-up: copy the header to the parameter counters, `y := 0`, `r := S - 1`, guard on `U`. -/
def setupProg : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (pushC kHs .mark)) (.seq (hdrCopy pStacks) (.seq (wk (popR kHs))
  (.seq (wk (pushC kY .mark)) (.seq (wk (pushC kRr .mark)) (.seq (wk (copyBlock kPS kRr kTm))
  (.seq (wk (dec kRr kTm)) (wk (pushC kU .mark))))))))

theorem closed_setupProg : setupProg.Closed :=
  ⟨K1.Rot.closed_pushC_lift _ _ _, closed_hdrCopy _, K1.Rot.closed_popR_lift _ _,
    K1.Rot.closed_pushC_lift _ _ _, K1.Rot.closed_pushC_lift _ _ _,
    K1.Rot.closed_copyBlock_lift _ _ _ _, K1.Rot.closed_dec_lift _ _ _,
    K1.Rot.closed_pushC_lift _ _ _⟩

theorem parOK_updF (St : PL → List Sym) (S K ρ D c o w1 w2 : ℕ) :
    ParOK (updF St pStacks [S, K, ρ, D, c, o, w1, w2]) S K ρ D c o w1 w2 :=
  ⟨⟨St kPS, by simp [updF, pStacks]⟩, ⟨St kPK, by simp [updF, pStacks]⟩,
    ⟨St kPR, by simp [updF, pStacks]⟩, ⟨St kPD, by simp [updF, pStacks]⟩,
    ⟨St kPC, by simp [updF, pStacks]⟩, ⟨St kPO, by simp [updF, pStacks]⟩,
    ⟨St kPW1, by simp [updF, pStacks]⟩, ⟨St kPW2, by simp [updF, pStacks]⟩⟩

theorem runs_setupProg (St : PL → List Sym) (S K ρ D c o w1 w2 : ℕ) (hS1 : 1 ≤ S)
    (rp : List Sym) (hH : St sH = hdrSyms [S, K, ρ, D, c, o, w1, w2] ++ rp) :
    Runs setupProg St (rS (updF St pStacks [S, K, ρ, D, c, o, w1, w2]) (St sA) (.mark :: St kU)
        (natSyms (0 / S) ++ .mark :: St kY) (natSyms (S - 1 - 0 % S) ++ .mark :: St kRr))
      (fun _ => True) (hdrCost [S, K, ρ, D, c, o, w1, w2] + 13 * bitLen S + 20) := by
  set fs := [S, K, ρ, D, c, o, w1, w2] with hfs
  have hHs : kHs ∉ pStacks := kHs_nm
  have s1 := K1.runs_wk_pushC pl kHs .mark St
  have s2 := runs_hdrCopy pStacks fs (Function.update St kHs (.mark :: St kHs)) rp rfl pStacks_ok
    (by simp [hH]) (by simp only [Function.update_self]; exact termOK_mark _)
  rw [updF_upd_comm _ _ _ _ _ hHs] at s2
  have s3 := K1.runs_wk_popR pl kHs
    (Function.update (updF St pStacks fs) kHs (.mark :: St kHs))
  rw [Function.update_self, Function.update_idem, List.tail_cons,
    show St kHs = updF St pStacks fs kHs from (updF_apply_not_mem _ _ _ _ hHs).symm,
    Function.update_eq_self] at s3
  set B0 := updF St pStacks fs with hB0
  have hY : B0 kY = St kY := updF_apply_not_mem _ _ _ _ kY_nm
  have hR : B0 kRr = St kRr := updF_apply_not_mem _ _ _ _ kRr_nm
  have hU : B0 kU = St kU := updF_apply_not_mem _ _ _ _ kU_nm
  have hA : B0 sA = St sA := updF_apply_not_mem _ _ _ _ sA_nm
  have hPS : B0 kPS = natSyms S ++ .mark :: St kPS := by simp [hB0, hfs, updF, pStacks]
  have s4 := K1.runs_wk_pushC pl kY .mark B0
  have s5 := K1.runs_wk_pushC pl kRr .mark (Function.update B0 kY (.mark :: B0 kY))
  have s6 := runs_copyBlock (src := kPS) (dst := kRr) (t := kTm) (by simp) (by simp) (by simp)
    (encodeNat S) (.mark :: St kPS) (Function.update (Function.update B0 kY (.mark :: B0 kY)) kRr
      (.mark :: Function.update B0 kY (.mark :: B0 kY) kRr)) (termOK_mark _)
    (by simp [hPS, natSyms])
  have s7 := runs_decN (k := kRr) (t := kTm) (by simp) S S hS1 le_rfl (.mark :: St kRr)
    (Function.update (Function.update (Function.update B0 kY (.mark :: B0 kY)) kRr
      (.mark :: Function.update B0 kY (.mark :: B0 kY) kRr)) kRr ((encodeNat S).map Sym.bit ++
      Function.update (Function.update B0 kY (.mark :: B0 kY)) kRr
        (.mark :: Function.update B0 kY (.mark :: B0 kY) kRr) kRr)) (termOK_mark _)
    (by simp [hR, natSyms])
  have s8 := K1.runs_wk_pushC pl kU .mark (Function.update (Function.update (Function.update
    (Function.update B0 kY (.mark :: B0 kY)) kRr (.mark :: Function.update B0 kY
      (.mark :: B0 kY) kRr)) kRr ((encodeNat S).map Sym.bit ++ Function.update (Function.update B0 kY
        (.mark :: B0 kY)) kRr (.mark :: Function.update B0 kY (.mark :: B0 kY) kRr) kRr)) kRr
    (natSyms (S - 1) ++ .mark :: St kRr))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq s1
    (WP.W9comp.runs_seq s2 (WP.W9comp.runs_seq s3 (WP.W9comp.runs_seq s4
    (WP.W9comp.runs_seq s5 (WP.W9comp.runs_seq s6 (WP.W9comp.runs_seq s7 s8))))))) ?_)
    (fun _ h => h) ?_
  · funext k
    by_cases h1 : k = sA
    · subst h1; simp [rS, hA]
    · by_cases h2 : k = kU
      · subst h2; simp [rS, hU]
      · by_cases h3 : k = kY
        · subst h3; simp [rS, hY, natSyms, encodeNat_zero]
        · by_cases h4 : k = kRr
          · subst h4; simp [rS]
          · simp [rS, Function.update_apply, h1, h2, h3, h4]
  · have : (encodeNat S).length = bitLen S := rfl
    omega

/-! ## Clean-up -/

/-- Clean-up: the outputs from `U` back onto the array; drop the counters. -/
def finalProg : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (WP.W9comp.rewindTo kU sA .mark)) (.seq (wk (K1.dropBits kY))
    (.seq (wk (K1.dropBits kRr)) (dropAll pStacks)))

theorem closed_finalProg : finalProg.Closed :=
  ⟨WP.W9comp.closed_rewind _ _ _ _, K1.Rot.closed_dropBits_lift _ _,
    K1.Rot.closed_dropBits_lift _ _, closed_dropAll _⟩

theorem mark_not_mem_carrSyms (w : ℕ) (v : List (List CInt)) :
    Sym.mark ∉ (carrSyms w v).reverse := by
  rw [List.mem_reverse]
  intro h
  rcases K1.mem_arrSyms h with h | ⟨b, h⟩ <;> cases h

theorem runs_finalProg (St : PL → List Sym) (fs : List ℕ) (hfs : fs.length = 8)
    (w2 n m : ℕ) (out : List (List CInt)) (rest : List Sym) :
    Runs finalProg (rS (updF St pStacks fs) rest ((carrSyms w2 out).reverse ++ .mark :: St kU)
        (natSyms n ++ .mark :: St kY) (natSyms m ++ .mark :: St kRr))
      (Function.update St sA (carrSyms w2 out ++ rest)) (fun _ => True)
      (3 * (carrSyms w2 out).length + 2 * bitLen n + 2 * bitLen m + dropCost fs + 6) := by
  set B0 := updF St pStacks fs with hB0
  have f1 := WP.W9comp.runs_rewind pl (src := kU) (dst := sA) (by simp) Sym.mark
    (carrSyms w2 out).reverse (St kU) (rS B0 rest ((carrSyms w2 out).reverse ++ .mark :: St kU)
      (natSyms n ++ .mark :: St kY) (natSyms m ++ .mark :: St kRr))
    (mark_not_mem_carrSyms w2 out) (by simp [rS])
  have f2 := K1.runs_wk_dropBits pl kY (encodeNat n) .mark (St kY)
    (Function.update (Function.update (rS B0 rest ((carrSyms w2 out).reverse ++ .mark :: St kU)
      (natSyms n ++ .mark :: St kY) (natSyms m ++ .mark :: St kRr)) kU (St kU)) sA
      ((carrSyms w2 out).reverse.reverse ++ rS B0 rest ((carrSyms w2 out).reverse ++
        .mark :: St kU) (natSyms n ++ .mark :: St kY) (natSyms m ++ .mark :: St kRr) sA)) rfl
    (by simp [rS, natSyms])
  have f3 := K1.runs_wk_dropBits pl kRr (encodeNat m) .mark (St kRr)
    (Function.update (Function.update (Function.update (rS B0 rest ((carrSyms w2 out).reverse ++
      .mark :: St kU) (natSyms n ++ .mark :: St kY) (natSyms m ++ .mark :: St kRr)) kU (St kU)) sA
      ((carrSyms w2 out).reverse.reverse ++ rS B0 rest ((carrSyms w2 out).reverse ++
        .mark :: St kU) (natSyms n ++ .mark :: St kY) (natSyms m ++ .mark :: St kRr) sA)) kY
      (St kY)) rfl (by simp [rS, natSyms])
  have f4 := runs_dropAll pStacks fs (Function.update St sA (carrSyms w2 out ++ rest))
    (by rw [hfs]; rfl) pStacks_nodup
  have hst : Function.update (Function.update (Function.update (Function.update
      (rS B0 rest ((carrSyms w2 out).reverse ++ .mark :: St kU) (natSyms n ++ .mark :: St kY)
        (natSyms m ++ .mark :: St kRr)) kU (St kU)) sA
      ((carrSyms w2 out).reverse.reverse ++ rS B0 rest ((carrSyms w2 out).reverse ++
        .mark :: St kU) (natSyms n ++ .mark :: St kY) (natSyms m ++ .mark :: St kRr) sA)) kY
      (St kY)) kRr (St kRr) = updF (Function.update St sA (carrSyms w2 out ++ rest)) pStacks fs := by
    have hB0U : B0 kU = St kU := updF_apply_not_mem _ _ _ _ kU_nm
    have hB0Y : B0 kY = St kY := updF_apply_not_mem _ _ _ _ kY_nm
    have hB0R : B0 kRr = St kRr := updF_apply_not_mem _ _ _ _ kRr_nm
    rw [updF_upd_comm _ _ _ _ _ sA_nm, ← hB0]
    funext k
    by_cases h1 : k = sA
    · subst h1; simp [rS]
    · by_cases h2 : k = kU
      · subst h2; simp [rS, hB0U]
      · by_cases h3 : k = kY
        · subst h3; simp [rS, hB0Y]
        · by_cases h4 : k = kRr
          · subst h4; simp [rS, hB0R]
          · simp [rS, Function.update_apply, h1, h2, h3, h4]
  rw [hst] at f3
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq f1 (WP.W9comp.runs_seq f2
    (WP.W9comp.runs_seq f3 f4))) (fun _ h => h) ?_
  simp only [List.length_reverse]
  have e1 : (encodeNat n).length = bitLen n := rfl
  have e2 : (encodeNat m).length = bitLen m := rfl
  omega

end SubNLogN.Machine.Layer.DrvPhaseScanAux
