/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixMain
import SubNLogN.Machine.FFT.PrefixFacts
import SubNLogN.Machine.FFT.PrefixCost

/-!
# K4-PREFIX, the run of the driver (`Machine/FFT/PrefixRun.lean`)

`runs_main`: given the three sub-kernels as definitional copies of their contracts (`ParamSpec`,
`PassSpec`, `TrSpec`), the driver `mainProg` turns the data stack
`carrSyms w (encCube q z) ++ rest` into `carrSyms w out ++ rest`, where
`out = Q₀(Q₁ⁿ(bflyIter … (encCube q z)))` is the machine value. Every other stack ends as it began.
The value facts enter as hypotheses: the fit of the passes (M3) and `out` with its fit. The
packaging (`Machine/FFT/Prefix.lean`) supplies them from `PrefixMath.lean`. The cost is the
explicit `prefCost`.

Proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF SubNLogN.Math.Walsh
  SubNLogN.Math.Common

/-- The kernel stacks `H`, `G`, `E1`, `NP`, `WB1`, `WB2`, `WS`, `ONE`; all others are empty. -/
def kst (h g e1 np wb wb2 ws one : List Sym) : PS → List Sym
  | .H => h
  | .G => g
  | .E1 => e1
  | .NP => np
  | .WB1 => wb
  | .WB2 => wb2
  | .WS => ws
  | .ONE => one
  | _ => []

theorem kst_nil : kst [] [] [] [] [] [] [] [] = fun _ => [] := by
  funext d; cases d <;> rfl

theorem natSyms_one : natSyms 1 = [Sym.bit true] := rfl

theorem length_natSyms' (x : ℕ) : (natSyms x).length = bitLen x := by
  simp [natSyms, bitLen]

theorem two_pow_split (m L j : ℕ) (h : L + j + 1 ≤ m) :
    2 ^ m = 2 * 2 ^ (L + j) * 2 ^ (m - L - j - 1) := by
  rw [mul_comm 2, mul_assoc, ← pow_succ', ← pow_add]
  congr 1
  omega

section Run

variable {Er Ep Et σ Rr Rp Rt : Type} [DecidableEq Er] [DecidableEq Ep] [DecidableEq Et]
  (lO : Lens σ (Option Sym)) (lr : Lens σ Rr) (lp : Lens σ Rp) (lt : Lens σ Rt)

set_option maxHeartbeats 8000000 in
/-- **The run of the driver.** -/
theorem runs_main {Cr J Cp Ct : ℕ} {Pr : Prog (KLoc (Fin 6) Er) (fun _ => Sym) Rr}
    {Pp : Prog (KLoc (Fin 3) Ep) (fun _ => Sym) Rp} {Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt}
    (hR : ParamSpec Er Rr Cr J Pr) (hP : PassSpec Ep Rp Cp Pp) (hTr : TrSpec Et Rt Ct Pt)
    (S : KP Er Ep Et → List Sym) (hclean : ∀ e, S (.inr e) = [])
    (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
    (rest hrest crest : List Sym) (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ)
    (hnc : ¬ IsChunkRound ℓ K v) (hz : ArrOnDiskGrid q z) (hrestB : BlkTerm rest)
    (hcrest : TermOK crest) (hD : S nD = carrSyms w (encCube q z) ++ rest)
    (hH : S nH = midHdr q ℓ K w a ++ hrest) (hV : S nV = natSyms v ++ crest)
    (hfitP : ∀ j, j ≤ pfN ℓ K a v →
      CArrFits (w + D) (bflyIter (addrBits a) (D * pfY ℓ K v) j (encCube q z)))
    (out : List (List CInt))
    (hval : mapC (truncShiftC 0) ((mapC (truncShiftC 1))^[pfN ℓ K a v]
      (bflyIter (addrBits a) (D * pfY ℓ K v) (pfN ℓ K a v) (encCube q z))) = out)
    (hout : CArrFits w out) :
    Runs (mainProg lO lr lp lt Pr Pp Pt) S (Function.update S nD (carrSyms w out ++ rest))
      (fun _ => True)
      (prefCost Cr Cp Ct J w D (addrBits a) ℓ (pfN ℓ K a v) (D * pfY ℓ K v)
        (midHdr q ℓ K w a).length) := by
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hqw⟩ := id hshape
  have hw1 : 1 ≤ w := by omega
  have hW1 : 1 ≤ w + D := by omega
  have hb := pf_bound q ℓ K w v a hshape hv hnc
  have hnD := pfN_le ℓ K a v
  have hcases := prefix_cases ℓ K v hK1 hv hnc
  have hA_bits : v + 1 = ℓ → D * pfY ℓ K v + pfN ℓ K a v = addrBits a :=
    caseA_bits q ℓ K w v a hshape hv hnc
  have hB_n : v + 1 ≠ ℓ → pfN ℓ K a v = D := fun h => by simp [pfN, h]
  generalize hn : pfN ℓ K a v = n at hb hnD hfitP hval hA_bits hB_n ⊢
  generalize hL : D * pfY ℓ K v = L at hb hfitP hval hA_bits ⊢
  have hLn : L + n ≤ addrBits a := by omega
  have cl : ∀ d : PS, S (ps d) = [] := fun d => hclean (.inl d)
  obtain ⟨hB0l, hB0r⟩ := shape_encCube q ℓ z
  have hshj : ∀ j, j ≤ n → (bflyIter (addrBits a) L j (encCube q z)).length = 2 ^ addrBits a ∧
      ∀ row ∈ bflyIter (addrBits a) L j (encCube q z), row.length = 2 ^ ℓ :=
    fun j hj => shape_bflyIter (addrBits a) L (2 ^ ℓ) _ hB0l hB0r j (by omega)
  have hcv : ∀ (W : ℕ) (X : List (List CInt)), X.length = 2 ^ addrBits a →
      (∀ row ∈ X, row.length = 2 ^ ℓ) → cvol W X = vW W (addrBits a) ℓ := by
    intro W X h1 h2
    rw [cvol_shape W X _ _ h1 h2, vW]
  have hCsh := shape_iter_trunc (bflyIter (addrBits a) L n (encCube q z)) _ _ (hshj n le_rfl).1
    (hshj n le_rfl).2
  have hCfit := fits_iter_trunc (hfitP n le_rfl)
  have hcvl : ∀ (W : ℕ) (X : List (List CInt)), X.length = 2 ^ addrBits a →
      (∀ row ∈ X, row.length = 2 ^ ℓ) →
      (arrSyms (X.map (crecBits W))).length = vW W (addrBits a) ℓ := fun W X h1 h2 =>
    hcv W X h1 h2
  -- 1. the parameter phase
  have e1 := runs_paramCall (Ep := Ep) (Et := Et) lr hR (st S (kst [] [] [] [] [] [] [] []))
    (fun e => hclean (.inr (.inl e))) q ℓ K w D v a hrest crest hshape hv hnc hcrest
    (by rw [st_nH]; exact hH) (by rw [st_nV]; exact hV)
  rw [hL] at e1
  have e1' : Runs (callInj ιr lr Pr) (st S (kst [] [] [] [] [] [] [] []))
      (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) [] (natSyms w) []))
      (fun _ => True) (Cr * (2 ^ addrBits a * (w + addrBits a + 1) ^ J +
        (midHdr q ℓ K w a).length)) := by
    refine runs_congr e1 ?_
    simp only [st_upd_ps, st_ps]
    congr 1
    funext d; cases d <;> simp [kst, Function.update_apply]
  -- 2. `ONE`
  have e2 := runs_pushK (σ := σ) (ps .ONE : KP Er Ep Et) (.bit true)
    (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) [] (natSyms w) []))
  have e2' : Runs (pushK (σ := σ) (ps .ONE : KP Er Ep Et) (.bit true))
      (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) [] (natSyms w) []))
      (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) [] (natSyms w) [Sym.bit true])) (fun _ => True) 1 := by
    refine runs_congr e2 ?_
    simp only [st_upd_ps, st_ps]
    congr 1
    funext d; cases d <;> simp [kst, Function.update_apply]
  -- 3. `WB2`
  have e3 := runs_copyBits lO (src := (ps .WB1 : KP Er Ep Et)) (dst := ps .WB2) (tmp := ps .TMP)
    (by simp) (by simp) (by simp)
    (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) [] (natSyms w) [Sym.bit true]))
    (Computability.encodeNat (w + D)) [] (by simp [kst, natSyms]) TermOK.nil
    (by simp only [st_ps, kst]; exact TermOK.nil)
  have e3' : Runs (copyBits lO (ps .WB1 : KP Er Ep Et) (ps .WB2) (ps .TMP))
      (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) [] (natSyms w) [Sym.bit true]))
      (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (fun _ => True) (9 * bitLen (w + D) + 4) := by
    refine runs_congr e3 ?_
    simp only [st_upd_ps, st_ps]
    congr 1
    funext d; cases d <;> simp [kst, Function.update_apply, natSyms]
  -- 4. widening
  have e4 := runs_trW (Er := Er) (Ep := Ep) lt hTr
    (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
    w (w + D) (encCube q z) rest hw1 hW1 (fits_encCube hqw hz)
    (by rw [mapC_truncShift_zero]; exact fits_encCube (by omega) hz) hrestB
    (by rw [st_nD]; exact hD) (by simp [kst]) (by simp [kst]) (by simp [kst])
  rw [mapC_truncShift_zero] at e4
  have e4' : Runs (callInj ιtW lt Pt)
      (st S (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark) [] []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark)
        (carrSyms (w + D) (encCube q z)) []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (fun _ => True) (Ct * (vW w (addrBits a) ℓ + vW (w + D) (addrBits a) ℓ + w + (w + D) +
        bitLen 0 + 1)) := by
    rw [← hcv w _ hB0l hB0r, ← hcv (w + D) _ hB0l hB0r]
    refine runs_congr e4 ?_
    rw [st_upd_nD, st_upd_ps]
    congr 1
    funext d; cases d <;> simp [kst, Function.update_apply]
  have hwb : (natSyms (w + D)).length = bitLen (w + D) := length_natSyms' _
  -- 5. the pass counter (case `v = ℓ - 1`: count the blocks)
  have e5 : Runs (.seq (peekO lO (ps .G : KP Er Ep Et))
        (.ite (fun v => (lO.get v).isSome) skipP (countA lO)))
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark)
        (carrSyms (w + D) (encCube q z)) []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ L) .mark)
        (List.replicate (2 ^ n - 1) .mark)
        (carrSyms (w + D) (encCube q z)) []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (fun _ => True) (1 + (cntCost (w + D) (addrBits a) ℓ n L + 1)) := by
    rcases hcases with hA | ⟨hB, -⟩
    · rw [if_pos hA]
      have hLn' : L + n = addrBits a := hA_bits hA
      have hpk := runs_peekO lO (ps .G : KP Er Ep Et) (st (Function.update S nD rest)
        (kst (List.replicate (2 ^ L) .mark) (List.replicate 0 .mark)
        (carrSyms (w + D) (encCube q z)) []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      refine runs_seq_ite_f hpk (fun v hv => by simp [hv, kst]) ?_
      have hBbP : ∀ p ∈ (encCube q z).map (crecBits (w + D)),
          p.length = 2 * (w + D) * 2 ^ ℓ := by
        intro p hp
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hp
        rw [crecBits_length, hB0r row hrow]
      have hBbl : ((encCube q z).map (crecBits (w + D))).length = 2 ^ L * 2 ^ n := by
        rw [List.length_map, hB0l, ← hLn', pow_add]
      have ea := runs_countBlk lO (E := (ps .E1 : KP Er Ep Et)) (T := ps .T) (G := ps .G)
        (H := ps .H) (HA := ps .HA) (by simp [List.nodup_cons])
        (st (Function.update S nD rest) (kst (List.replicate (2 ^ L) .mark)
          (List.replicate 0 .mark) (carrSyms (w + D) (encCube q z)) []
          (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
        ((encCube q z).map (crecBits (w + D))) (2 * (w + D) * 2 ^ ℓ) (2 ^ L) (2 ^ n)
        Nat.one_le_two_pow hBbP hBbl (by simp [kst, carrSyms]) (by simp [kst]) (by simp [kst])
      have eb := runs_revArr_in lO (src := (ps .T : KP Er Ep Et)) (dst := ps .E1) (by simp)
        (st (Function.update S nD rest) (Function.update (kst (List.replicate (2 ^ L) .mark)
          (List.replicate (2 ^ n) .mark) [] []
          (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]) PS.T
          (arrSyms ((encCube q z).map (crecBits (w + D)))).reverse))
        ((encCube q z).map (crecBits (w + D))) (by simp [kst])
      have ec := runs_popO lO (ps .G : KP Er Ep Et) (st (Function.update S nD rest)
        (kst (List.replicate (2 ^ L) .mark) (List.replicate (2 ^ n) .mark)
          (carrSyms (w + D) (encCube q z)) []
          (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      refine runs_congr (runs_mono (runs_seq' (runs_congr ea ?_) (runs_seq' (runs_congr eb ?_)
        ec)) (fun _ _ => trivial) ?_) ?_
      · rw [st_upd_ps, st_upd_ps, st_upd_ps]
        congr 1
        funext d; cases d <;> simp [kst, Function.update_apply]
      · rw [st_upd_ps, st_upd_ps]
        congr 1
        funext d; cases d <;> simp [kst, Function.update_apply, carrSyms]
      · rw [hcvl (w + D) _ hB0l hB0r]
        simp only [cntCost]
        omega
      · rw [st_upd_ps]
        congr 1
        funext d; cases d <;> simp [kst, Function.update_apply, List.tail_replicate]
    · have hn' : n = D := hB_n hB
      rw [if_neg hB, show 2 ^ D - 1 = 2 ^ n - 1 by rw [hn']]
      have hpk := runs_peekO lO (ps .G : KP Er Ep Et) (st (Function.update S nD rest)
        (kst (List.replicate (2 ^ L) .mark) (List.replicate (2 ^ n - 1) .mark)
        (carrSyms (w + D) (encCube q z)) []
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      have hpos : 0 < 2 ^ n - 1 := cnt_pos n (by omega)
      refine runs_mono (runs_seq_ite_t hpk (fun v hv => ?_) (runs_skipP _)) (fun _ _ => trivial) ?_
      · show (lO.get v).isSome = true
        rw [hv, st_ps]
        simp only [kst]
        rw [isSome_head?_replicate]
        exact decide_eq_true hpos
      · have h1 : 0 < cntCost (w + D) (addrBits a) ℓ n L := by unfold cntCost; positivity
        omega
  -- 6. the pass loop
  have e6 := runs_ploop_const lO (ps .G : KP Er Ep Et) Option.isSome (passBody lO lp Pp) n
    (fun j => st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + j)) .mark)
      (List.replicate (2 ^ (n - j) - 1) .mark)
      (carrSyms (w + D) (bflyIter (addrBits a) L j (encCube q z))) (List.replicate j .mark)
      (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
    (passB Cp (w + D) (addrBits a) ℓ n) ?_ ?_
  rotate_left
  · intro j hj
    simp only [st_ps, kst, isSome_head?_replicate]
    apply decide_eq_decide.mpr
    constructor
    · intro h
      by_contra hc
      have h0 : n - j = 0 := by omega
      rw [h0] at h
      simp at h
    · intro h
      have : 2 ≤ 2 ^ (n - j) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - j) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · intro j hj
    have hx : (2 ^ (n - j) - 1) / 2 = 2 ^ (n - (j + 1)) - 1 := by
      rw [show n - j = (n - (j + 1)) + 1 by omega]; exact two_pow_sub_one_div_two _
    have hpw : 2 ^ (L + (j + 1)) = 2 * 2 ^ (L + j) := by
      rw [← Nat.add_assoc, pow_succ]; ring
    obtain ⟨hlj, hrj⟩ := hshj j (by omega)
    have hnj : 2 ^ (n - j) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hLj : 2 ^ (L + j) ≤ 2 ^ addrBits a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hx2 : 2 ^ (n - (j + 1)) - 1 ≤ 2 ^ n := by
      have : 2 ^ (n - (j + 1)) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact le_trans (Nat.sub_le _ _) this
    have ea := runs_halveTo lO (src := (ps .G : KP Er Ep Et)) (dst := ps .GA) (by simp)
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + j)) .mark)
        (List.replicate (2 ^ (n - j) - 1) .mark)
        (carrSyms (w + D) (bflyIter (addrBits a) L j (encCube q z))) (List.replicate j .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (2 ^ (n - j) - 1) (by simp [kst])
    have eb := runs_movePrefix lO (src := (ps .GA : KP Er Ep Et)) (dst := ps .G) (by simp)
      Option.isSome
      (st (Function.update S nD rest) (Function.update (kst (List.replicate (2 ^ (L + j)) .mark)
        [] (carrSyms (w + D) (bflyIter (addrBits a) L j (encCube q z))) (List.replicate j .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]) PS.GA
        (List.replicate (2 ^ (n - (j + 1)) - 1) .mark)))
      (List.replicate (2 ^ (n - (j + 1)) - 1) .mark) [] (by simp) (by simp) rfl
    have ec := runs_pushK (σ := σ) (ps .NP : KP Er Ep Et) .mark
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + j)) .mark)
        (List.replicate (2 ^ (n - (j + 1)) - 1) .mark)
        (carrSyms (w + D) (bflyIter (addrBits a) L j (encCube q z))) (List.replicate j .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
    have ed := runs_passCall (Er := Er) (Et := Et) lp hP
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + j)) .mark)
        (List.replicate (2 ^ (n - (j + 1)) - 1) .mark)
        (carrSyms (w + D) (bflyIter (addrBits a) L j (encCube q z)))
        (List.replicate (j + 1) .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (fun e => by simp [hclean, nD]) (w + D) (2 ^ (L + j)) (2 ^ (addrBits a - L - j - 1)) (2 ^ ℓ)
      (bflyIter (addrBits a) L j (encCube q z)) hW1 Nat.one_le_two_pow
      (by rw [hlj]; exact two_pow_split _ _ _ (by omega)) hrj (hfitP j (by omega))
      (hfitP (j + 1) hj) (by simp [kst]) (by simp [kst]) (by simp [kst])
    have ee := runs_dbl1 lO (src := (ps .H : KP Er Ep Et)) (aux := ps .AUX) (by simp)
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + j)) .mark)
        (List.replicate (2 ^ (n - (j + 1)) - 1) .mark)
        (carrSyms (w + D) (bflyIter (addrBits a) L (j + 1) (encCube q z)))
        (List.replicate (j + 1) .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (2 ^ (L + j)) (by simp [kst]) (by simp [kst])
    have ef := runs_popO lO (ps .H : KP Er Ep Et)
      (st (Function.update S nD rest) (kst (List.replicate (2 * 2 ^ (L + j) + 1) .mark)
        (List.replicate (2 ^ (n - (j + 1)) - 1) .mark)
        (carrSyms (w + D) (bflyIter (addrBits a) L (j + 1) (encCube q z)))
        (List.replicate (j + 1) .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
    refine runs_congr (runs_mono (runs_seq' (runs_congr ea ?_) (runs_seq' (runs_congr eb ?_)
      (runs_seq' (runs_congr ec ?_) (runs_seq' (runs_congr ed ?_) (runs_seq' (runs_congr ee ?_)
      ef))))) (fun _ _ => trivial) ?_) ?_
    · rw [st_upd_ps, st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply, hx]
    · rw [st_upd_ps, st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply]
    · rw [st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply, List.replicate_succ]
    · rw [st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply, bflyIter]
    · rw [st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply]
    · rw [hcv (w + D) _ hlj hrj]
      simp only [passB, List.length_replicate]
      omega
    · rw [st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply, List.tail_replicate, hpw]
  -- 7. the truncation loop
  have e7 := runs_ploop_const lO (ps .NP : KP Er Ep Et) Option.isSome (truncBody lO lt Pt) n
    (fun i => st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + n)) .mark) []
      (carrSyms (w + D) ((mapC (truncShiftC 1))^[i] (bflyIter (addrBits a) L n (encCube q z))))
      (List.replicate (n - i) .mark)
      (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
    (truncB Ct (w + D) (addrBits a) ℓ) ?_ ?_
  rotate_left
  · intro i hi
    simp only [st_ps, kst, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro i hi
    obtain ⟨hli, hri⟩ := hCsh i
    obtain ⟨hli', hri'⟩ := shape_mapC (truncShiftC 1) _ _ _ hli hri
    have ea := runs_popO lO (ps .NP : KP Er Ep Et)
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + n)) .mark) []
        (carrSyms (w + D) ((mapC (truncShiftC 1))^[i] (bflyIter (addrBits a) L n (encCube q z))))
        (List.replicate (n - i) .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
    have eb := runs_tr1 (Er := Er) (Ep := Ep) lt hTr
      (st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + n)) .mark) []
        (carrSyms (w + D) ((mapC (truncShiftC 1))^[i] (bflyIter (addrBits a) L n (encCube q z))))
        (List.replicate (n - (i + 1)) .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
      (w + D) _ hW1 (hCfit i) (fits_mapC_trunc (hCfit i) 1) (by simp [kst]) (by simp [kst])
      (by simp [kst]) (by simp [kst, natSyms_one])
    have ec := runs_revArr_out lO (src := (ps .E2 : KP Er Ep Et)) (dst := ps .E3) (by simp)
      (st (Function.update S nD rest) (Function.update (kst (List.replicate (2 ^ (L + n)) .mark)
        [] [] (List.replicate (n - (i + 1)) .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]) PS.E2
        (carrSyms (w + D) (mapC (truncShiftC 1)
          ((mapC (truncShiftC 1))^[i] (bflyIter (addrBits a) L n (encCube q z)))))))
      ((mapC (truncShiftC 1) ((mapC (truncShiftC 1))^[i]
        (bflyIter (addrBits a) L n (encCube q z)))).map (crecBits (w + D))) []
      (by simp [kst, carrSyms]) blkTerm_nil
    have ed := runs_revArr_in lO (src := (ps .E3 : KP Er Ep Et)) (dst := ps .E1) (by simp)
      (st (Function.update S nD rest) (Function.update (kst (List.replicate (2 ^ (L + n)) .mark)
        [] [] (List.replicate (n - (i + 1)) .mark)
        (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]) PS.E3
        (arrSyms ((mapC (truncShiftC 1) ((mapC (truncShiftC 1))^[i]
          (bflyIter (addrBits a) L n (encCube q z)))).map (crecBits (w + D)))).reverse))
      ((mapC (truncShiftC 1) ((mapC (truncShiftC 1))^[i]
        (bflyIter (addrBits a) L n (encCube q z)))).map (crecBits (w + D)))
      (by simp [kst])
    refine runs_congr (runs_mono (runs_seq' (runs_congr ea ?_) (runs_seq' (runs_congr eb ?_)
      (runs_seq' (runs_congr ec ?_) ed))) (fun _ _ => trivial) ?_) ?_
    · rw [st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply, List.tail_replicate, Nat.sub_sub]
    · rw [st_upd_ps, st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply]
    · rw [st_upd_ps, st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply]
    · rw [hcvl (w + D) _ hli' hri', hcv (w + D) _ hli hri]
      simp only [truncB]
      omega
    · rw [st_upd_ps, st_upd_ps]
      congr 1
      funext d; cases d <;> simp [kst, Function.update_apply, carrSyms,
        Function.iterate_succ_apply']
  -- 8. narrowing
  obtain ⟨hln, hrn⟩ := hCsh n
  have e8 := runs_trF (Er := Er) (Ep := Ep) lt hTr
    (st (Function.update S nD rest) (kst (List.replicate (2 ^ (L + n)) .mark) []
      (carrSyms (w + D) ((mapC (truncShiftC 1))^[n] (bflyIter (addrBits a) L n (encCube q z))))
      (List.replicate (n - n) .mark)
      (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
    (w + D) w _ hW1 hw1 (hCfit n) (by rw [hval]; exact hout) (by simp [kst]) (by simp [kst])
    (by simp [kst]) (by simp [kst])
  rw [hval, hcv (w + D) _ hln hrn, hcv w _ hln hrn] at e8
  -- 9. emptying the kernel stacks
  have d1 := runs_drain lO (ps .H : KP Er Ep Et)
    (st (Function.update S nD (carrSyms w out ++ rest)) (kst (List.replicate (2 ^ (L + n)) .mark)
      [] [] [] (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
  have d2 := runs_drain lO (ps .WB1 : KP Er Ep Et)
    (st (Function.update S nD (carrSyms w out ++ rest)) (kst [] [] [] []
      (natSyms (w + D)) (natSyms (w + D)) (natSyms w) [Sym.bit true]))
  have d3 := runs_drain lO (ps .WB2 : KP Er Ep Et)
    (st (Function.update S nD (carrSyms w out ++ rest)) (kst [] [] [] []
      [] (natSyms (w + D)) (natSyms w) [Sym.bit true]))
  have d4 := runs_drain lO (ps .WS : KP Er Ep Et)
    (st (Function.update S nD (carrSyms w out ++ rest)) (kst [] [] [] []
      [] [] (natSyms w) [Sym.bit true]))
  have d5 := runs_drain lO (ps .ONE : KP Er Ep Et)
    (st (Function.update S nD (carrSyms w out ++ rest)) (kst [] [] [] [] [] [] [] [Sym.bit true]))
  -- the whole run
  have hall := runs_seq' e1' (runs_seq' e2' (runs_seq' e3' (runs_seq' e4' (runs_seq' e5
    (runs_seq' (runs_congr e6 ?_) (runs_seq' (runs_congr e7 ?_) (runs_seq' (runs_congr e8 ?_)
    (runs_seq' (runs_congr d1 ?_) (runs_seq' (runs_congr d2 ?_) (runs_seq' (runs_congr d3 ?_)
    (runs_seq' (runs_congr d4 ?_) d5)))))))))))
  rotate_left
  · simp only [Nat.sub_self, pow_zero, List.replicate_zero, Function.iterate_zero, id_eq,
      Nat.sub_zero]
  · rfl
  · rw [st_upd_ps, st_upd_nD]
    congr 1
    · rw [st_nD]; simp
    · funext d; cases d <;> simp [kst, Function.update_apply, Nat.sub_self]
  · rw [st_upd_ps]; congr 1; funext d; cases d <;> simp [kst, Function.update_apply]
  · rw [st_upd_ps]; congr 1; funext d; cases d <;> simp [kst, Function.update_apply]
  · rw [st_upd_ps]; congr 1; funext d; cases d <;> simp [kst, Function.update_apply]
  · rw [st_upd_ps]; congr 1; funext d; cases d <;> simp [kst, Function.update_apply]
  rw [kst_nil, st_of_clean S cl] at hall
  refine runs_congr (runs_mono hall (fun _ _ => trivial) ?_) ?_
  · simp only [prefCost, st_ps, kst, List.length_replicate, hwb, length_natSyms',
      List.length_cons, List.length_nil]
    omega
  · rw [st_upd_ps]
    have hk : Function.update (kst [] [] [] [] [] [] [] [Sym.bit true]) PS.ONE [] =
        fun _ => [] := by funext d; cases d <;> rfl
    rw [hk, st_of_clean]
    intro d
    simp [nD, ps, hclean]

end Run

end SubNLogN.Machine.FFT.PrefixAux
