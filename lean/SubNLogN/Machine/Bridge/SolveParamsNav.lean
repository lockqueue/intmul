/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsEmit
import SubNLogN.Machine.Bridge.PrePostLoop

/-!
# SOL-PARAM-ROWS (7): table navigation, the half skip, restore, clearing

Programs over the layout `SK`:
* `navLoop`: skip the first `N` blocks of the table (`N` on the counter `kCD`). Each block's
  records (reversed) and its `mark` go onto `kZB` (`runs_navLoop`).
* `restLoop`: the inverse; it moves the blocks back from `kZB` (`runs_restLoop`).
* `skipLoop`: move `H` records from the table onto `kZR` (`runs_skipLoop`).
* `halfLoop`: `h ∈ {0, 1}` rounds of `skipLoop`, with `h` copied from `sHalf` (`runs_halfLoop`).
* `clearBits k`: pop the bits on top of `k` (`runs_clearBits`).

All lemmas give exact final stacks and explicit costs. All proved; helpers in
`SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

theorem runs_L_moveSym {src dst : SK} (hne : src ≠ dst) (x : Sym) (L' : List Sym)
    (S : SK → List Sym) (hS : S src = x :: L') :
    Runs (L (BridgePP.moveSym src dst)) S
      (Function.update (Function.update S src L') dst (x :: S dst)) (fun _ => True) 2 :=
  BridgePP.runs_liftRegs _ (BridgePP.runs_moveSym hne x L' S hS)

theorem termOK_mark_cons (L' : List Sym) : TermOK (Sym.mark :: L') := by
  intro d hd
  simp at hd
  subst hd
  rfl

theorem bitLen_le_one {h : ℕ} (hh : h ≤ 1) : bitLen h ≤ 1 := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.mpr (by rw [pow_one]; omega)

/-! ## Blocks -/

/-- One table block: its records, then a `mark`. -/
def blkSyms (rs : List (List Bool)) : List Sym := SolveAux.recsOf rs ++ [Sym.mark]

/-- The skipped blocks as stored on `kZB`, last skipped on top: per block a `mark` above its
records in reverse order. -/
def zbSyms (l : List (List (List Bool))) : List Sym :=
  (l.reverse.map fun rs => Sym.mark :: SolveAux.recsOf rs.reverse).flatten

/-- The table symbols of a list of blocks. -/
def tabSyms (bl : List (List (List Bool))) : List Sym := (bl.map blkSyms).flatten

theorem tabSyms_cons (rs : List (List Bool)) (bl : List (List (List Bool))) :
    tabSyms (rs :: bl) = SolveAux.recsOf rs ++ Sym.mark :: tabSyms bl := by
  simp [tabSyms, blkSyms]

theorem zbSyms_snoc (l : List (List (List Bool))) (rs : List (List Bool)) :
    zbSyms (l ++ [rs]) = Sym.mark :: (SolveAux.recsOf rs.reverse ++ zbSyms l) := by
  simp [zbSyms]

theorem termOK_zbSyms (l : List (List (List Bool))) : TermOK (zbSyms l) := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', rs, rfl⟩
  · exact termOK_nil
  · rw [List.concat_eq_append, zbSyms_snoc]
    exact termOK_mark_cons _

/-- Cost of one navigation or restore step over a block `rs`, counter value `n + 1`. -/
def navStepCost (rs : List (List Bool)) (n : ℕ) : ℕ :=
  SolveAux.drainCost rs + 3 + (6 * zerosLead (encodeNat (n + 1)) + 8)

/-! ## Navigation -/

/-- One navigation step: the next block's records (reversed) and its `mark` go onto `kZB`. -/
def navCore : BProg SK :=
  .seq (L (SolveAux.drainRecs sTab kZB kTP)) (.seq (L (BridgePP.moveSym sTab kZB))
    (L (dec kCD kTQ)))

/-- Navigation: skip `N` blocks (`N` on the counter `kCD`). -/
def navLoop : BProg SK :=
  .seq (BridgeRed.peekTop kCD) (.loop BridgeRed.topIsBit (.seq navCore (BridgeRed.peekTop kCD)))

theorem runs_navLoop (bl : List (List (List Bool))) (hbl : ∀ rs ∈ bl, ∀ bs ∈ rs, bs ≠ [])
    (rest : List Sym) (N : ℕ) (hN : N ≤ bl.length) (S : SK → List Sym)
    (hTab : S sTab = tabSyms bl ++ rest) (hZB : S kZB = []) (hTP : S kTP = [])
    (hCD : S kCD = natSyms N) :
    Runs navLoop S
      (Function.update (Function.update (Function.update S
        sTab (tabSyms (bl.drop N) ++ rest)) kZB (zbSyms (bl.take N))) kCD [])
      (fun _ => True)
      (1 + loopCost (fun n => navStepCost (bl.getD (N - (n + 1)) []) n + 1) N) := by
  let B : ℕ → SK → List Sym := fun n =>
    Function.update (Function.update (Function.update S
      sTab (tabSyms (bl.drop (N - n)) ++ rest)) kZB (zbSyms (bl.take (N - n))))
      kCD (natSyms n)
  have hk : ∀ n, n ≤ N → B n kCD = natSyms n := by
    intro n _
    simp [B]
  have hstep : ∀ n, n + 1 ≤ N → Runs navCore (B (n + 1)) (B n) (fun _ => True)
      (navStepCost (bl.getD (N - (n + 1)) []) n) := by
    intro n hn
    have hjl : N - (n + 1) < bl.length := by omega
    have hjn : N - n = N - (n + 1) + 1 := by omega
    obtain ⟨rs, hrs⟩ : ∃ rs, rs = bl[N - (n + 1)] := ⟨_, rfl⟩
    have hg : bl.getD (N - (n + 1)) [] = rs := by rw [hrs]; simp [hjl]
    have hd : bl.drop (N - (n + 1)) = rs :: bl.drop (N - n) := by
      rw [hrs, hjn]; exact List.drop_eq_getElem_cons hjl
    have ht : bl.take (N - n) = bl.take (N - (n + 1)) ++ [rs] := by
      rw [hrs, hjn]; exact List.take_succ_eq_append_getElem hjl
    have hne : ∀ bs ∈ rs, bs ≠ [] := hbl _ (by rw [hrs]; exact List.getElem_mem hjl)
    refine runs_mono (runs_congr (runs_seq
      (runs_L (K := SK) fun v => ⟨_, SolveAux.drainRecs_eval (A := sTab) (B := kZB) (tmp := kTP)
        (by decide) (by decide) (by decide) v rs (Sym.mark :: (tabSyms (bl.drop (N - n)) ++ rest))
        (B (n + 1)) hne (by simp [B, hd, tabSyms_cons]) (termOK_mark_cons _)
        (by simpa [B, hTP] using termOK_nil)⟩)
      (runs_seq (runs_L_moveSym (src := sTab) (dst := kZB) (by decide) Sym.mark
          (tabSyms (bl.drop (N - n)) ++ rest) _ (by simp [Function.update_apply]))
        (runs_L (K := SK) fun v => ⟨_, dec_eval (k := kCD) (t := kTQ) (by decide) [] v n [] _
          termOK_nil (by simp [B, Function.update_apply, natSyms_eq_map])⟩))) ?_)
      (fun _ _ => trivial) (by rw [hg]; simp only [navStepCost]; omega)
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B]
    by_cases k2 : k = kZB
    · subst k2; simp [B, ht, zbSyms_snoc]
    by_cases k3 : k = kCD
    · subst k3; simp [B, natSyms_eq_map]
    simp [B, Function.update_apply, k1, k2, k3]
  have hL := BridgeRed.runs_counted_loop kCD navCore B N
    (fun n => navStepCost (bl.getD (N - (n + 1)) []) n) hk hstep
  have hBN : B N = S := by
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B, hTab]
    by_cases k2 : k = kZB
    · subst k2; simp [B, hZB, zbSyms]
    by_cases k3 : k = kCD
    · subst k3; simp [B, hCD]
    simp [B, Function.update_apply, k1, k2, k3]
  have hB0 : B 0 = Function.update (Function.update (Function.update S
      sTab (tabSyms (bl.drop N) ++ rest)) kZB (zbSyms (bl.take N))) kCD [] := by
    simp [B, natSyms_eq_map, encodeNat_zero]
  rw [hBN, hB0] at hL
  exact hL

/-! ## Restore -/

/-- One restore step: a block's `mark` and records (order restored) go back onto `sTab`. -/
def restCore : BProg SK :=
  .seq (L (BridgePP.moveSym kZB sTab)) (.seq (L (SolveAux.drainRecs kZB sTab kTP))
    (L (dec kCD kTQ)))

/-- Restore the `N` skipped blocks (`N` on the counter `kCD`). -/
def restLoop : BProg SK :=
  .seq (BridgeRed.peekTop kCD) (.loop BridgeRed.topIsBit (.seq restCore (BridgeRed.peekTop kCD)))

theorem runs_restLoop (bl : List (List (List Bool))) (hbl : ∀ rs ∈ bl, ∀ bs ∈ rs, bs ≠ [])
    (rest : List Sym) (N : ℕ) (hN : N ≤ bl.length) (S : SK → List Sym)
    (hTab : S sTab = tabSyms (bl.drop N) ++ rest) (hZB : S kZB = zbSyms (bl.take N))
    (hTP : S kTP = []) (hCD : S kCD = natSyms N) :
    Runs restLoop S
      (Function.update (Function.update (Function.update S
        sTab (tabSyms bl ++ rest)) kZB []) kCD [])
      (fun _ => True) (1 + loopCost (fun n => navStepCost (bl.getD n []).reverse n + 1) N) := by
  let B : ℕ → SK → List Sym := fun n =>
    Function.update (Function.update (Function.update S
      sTab (tabSyms (bl.drop n) ++ rest)) kZB (zbSyms (bl.take n))) kCD (natSyms n)
  have hk : ∀ n, n ≤ N → B n kCD = natSyms n := by
    intro n _
    simp [B]
  have hstep : ∀ n, n + 1 ≤ N → Runs restCore (B (n + 1)) (B n) (fun _ => True)
      (navStepCost (bl.getD n []).reverse n) := by
    intro n hn
    have hjl : n < bl.length := by omega
    obtain ⟨rs, hrs⟩ : ∃ rs, rs = bl[n] := ⟨_, rfl⟩
    have hg : bl.getD n [] = rs := by rw [hrs]; simp [hjl]
    have hd : bl.drop n = rs :: bl.drop (n + 1) := by
      rw [hrs]; exact List.drop_eq_getElem_cons hjl
    have ht : bl.take (n + 1) = bl.take n ++ [rs] := by
      rw [hrs]; exact List.take_succ_eq_append_getElem hjl
    have hne : ∀ bs ∈ rs.reverse, bs ≠ [] := fun bs hbs =>
      hbl _ (by rw [hrs]; exact List.getElem_mem hjl) bs (List.mem_reverse.mp hbs)
    refine runs_mono (runs_congr (runs_seq
      (runs_L_moveSym (src := kZB) (dst := sTab) (by decide) Sym.mark
        (SolveAux.recsOf rs.reverse ++ zbSyms (bl.take n)) (B (n + 1))
        (by simp [B, ht, zbSyms_snoc]))
      (runs_seq (runs_L (K := SK) fun v => ⟨_, SolveAux.drainRecs_eval (A := kZB) (B := sTab)
          (tmp := kTP) (by decide) (by decide) (by decide) v rs.reverse
          (zbSyms (bl.take n)) _ hne (by simp [Function.update_apply]) (termOK_zbSyms _)
          (by simpa [B, Function.update_apply, hTP] using termOK_nil)⟩)
        (runs_L (K := SK) fun v => ⟨_, dec_eval (k := kCD) (t := kTQ) (by decide) [] v n [] _
          termOK_nil (by simp [B, Function.update_apply, natSyms_eq_map])⟩))) ?_)
      (fun _ _ => trivial) (by rw [hg]; simp only [navStepCost]; omega)
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B, hd, tabSyms_cons]
    by_cases k2 : k = kZB
    · subst k2; simp [B]
    by_cases k3 : k = kCD
    · subst k3; simp [B, natSyms_eq_map]
    simp [B, Function.update_apply, k1, k2, k3]
  have hL := BridgeRed.runs_counted_loop kCD restCore B N
    (fun n => navStepCost (bl.getD n []).reverse n) hk hstep
  have hBN : B N = S := by
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B, hTab]
    by_cases k2 : k = kZB
    · subst k2; simp [B, hZB]
    by_cases k3 : k = kCD
    · subst k3; simp [B, hCD]
    simp [B, Function.update_apply, k1, k2, k3]
  have hB0 : B 0 = Function.update (Function.update (Function.update S
      sTab (tabSyms bl ++ rest)) kZB []) kCD [] := by
    simp [B, natSyms_eq_map, encodeNat_zero, zbSyms]
  rw [hBN, hB0] at hL
  exact hL

/-! ## Skipping records -/

/-- One skip step: move one record from the table onto `kZR`. -/
def skipCore : BProg SK := .seq (L (SolveAux.moveRec sTab kZR kTP)) (L (dec kCD kTQ))

/-- Skip `H` records (`H` on the counter `kCD`). -/
def skipLoop : BProg SK :=
  .seq (BridgeRed.peekTop kCD) (.loop BridgeRed.topIsBit (.seq skipCore (BridgeRed.peekTop kCD)))

theorem runs_skipLoop (rl : List (List Bool)) (ℓ : ℕ) (hℓ : ∀ bs ∈ rl, bs.length = ℓ)
    (tail : List Sym) (H : ℕ) (hH : H ≤ rl.length) (S : SK → List Sym)
    (hTab : S sTab = SolveAux.recsOf rl ++ tail) (hZR : S kZR = []) (hTP : S kTP = [])
    (hCD : S kCD = natSyms H) :
    Runs skipLoop S
      (Function.update (Function.update (Function.update S
        sTab (SolveAux.recsOf (rl.drop H) ++ tail)) kZR (SolveAux.recsOf (rl.take H).reverse))
        kCD [])
      (fun _ => True) (H * (6 * ℓ + 6 * bitLen H + 20) + 2) := by
  let B : ℕ → SK → List Sym := fun n =>
    Function.update (Function.update (Function.update S
      sTab (SolveAux.recsOf (rl.drop (H - n)) ++ tail))
      kZR (SolveAux.recsOf (rl.take (H - n)).reverse)) kCD (natSyms n)
  let T : ℕ → ℕ := fun n => (6 * ℓ + 10) + (6 * zerosLead (encodeNat (n + 1)) + 8)
  have hk : ∀ n, n ≤ H → B n kCD = natSyms n := by
    intro n _
    simp [B]
  have hstep : ∀ n, n + 1 ≤ H → Runs skipCore (B (n + 1)) (B n) (fun _ => True) (T n) := by
    intro n hn
    have hjl : H - (n + 1) < rl.length := by omega
    have hjn : H - n = H - (n + 1) + 1 := by omega
    obtain ⟨rs, hrs⟩ : ∃ rs, rs = rl[H - (n + 1)] := ⟨_, rfl⟩
    have hd : rl.drop (H - (n + 1)) = rs :: rl.drop (H - n) := by
      rw [hrs, hjn]; exact List.drop_eq_getElem_cons hjl
    have ht : (rl.take (H - n)).reverse = rs :: (rl.take (H - (n + 1))).reverse := by
      rw [hrs, hjn, List.take_succ_eq_append_getElem hjl]
      simp
    have hlen : rs.length = ℓ := by rw [hrs]; exact hℓ _ (List.getElem_mem hjl)
    refine runs_mono (runs_congr (runs_seq
      (runs_L (K := SK) fun v => ⟨_, SolveAux.moveRec_eval (src := sTab) (dst := kZR) (tmp := kTP)
        (by decide) (by decide) (by decide) v rs (SolveAux.recsOf (rl.drop (H - n)) ++ tail)
        (B (n + 1)) (by simp [B, hd]) (by simpa [B, hTP] using termOK_nil)⟩)
      (runs_L (K := SK) fun v => ⟨_, dec_eval (k := kCD) (t := kTQ) (by decide) [] v n [] _
        termOK_nil (by simp [B, Function.update_apply, natSyms_eq_map])⟩)) ?_)
      (fun _ _ => trivial) (by simp only [T, hlen]; omega)
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B]
    by_cases k2 : k = kZR
    · subst k2; simp [B, ht]
    by_cases k3 : k = kCD
    · subst k3; simp [B, natSyms_eq_map]
    simp [B, Function.update_apply, k1, k2, k3]
  have hL := BridgeRed.runs_counted_loop kCD skipCore B H T hk hstep
  have hBH : B H = S := by
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B, hTab]
    by_cases k2 : k = kZR
    · subst k2; simp [B, hZR]
    by_cases k3 : k = kCD
    · subst k3; simp [B, hCD]
    simp [B, Function.update_apply, k1, k2, k3]
  have hB0 : B 0 = Function.update (Function.update (Function.update S
      sTab (SolveAux.recsOf (rl.drop H) ++ tail)) kZR (SolveAux.recsOf (rl.take H).reverse))
      kCD [] := by
    simp [B, natSyms_eq_map, encodeNat_zero]
  rw [hBH, hB0] at hL
  refine runs_mono hL (fun _ _ => trivial) ?_
  have hT : ∀ n, n < H → T n + 1 ≤ 6 * ℓ + 6 * bitLen H + 19 := by
    intro n hn
    have hz : zerosLead (encodeNat (n + 1)) ≤ bitLen H :=
      le_trans (zerosLead_le_length _) (bitLen_mono'' (by omega))
    simp only [T]
    omega
  have hc := loopCost_le_mul' (fun n => T n + 1) _ H hT
  nlinarith

/-! ## The half skip -/

/-- One half-skip round: skip `H` records (`H` copied from `kCT`), then decrement `kCY`. -/
def halfCore : BProg SK := .seq (L (copyBlock kCT kCD kTP)) (.seq skipLoop (L (dec kCY kTQ)))

/-- The half skip: `h ∈ {0, 1}` rounds, `h` copied from `sHalf` to `kCY`. -/
def halfLoop : BProg SK :=
  .seq (L (copyBlock sHalf kCY kTP))
    (.seq (BridgeRed.peekTop kCY) (.loop BridgeRed.topIsBit (.seq halfCore (BridgeRed.peekTop kCY))))

theorem runs_halfLoop (rl : List (List Bool)) (ℓ : ℕ) (hℓ : ∀ bs ∈ rl, bs.length = ℓ)
    (tail : List Sym) (H h : ℕ) (hh : h ≤ 1) (hH : H ≤ rl.length) (rh : List Sym)
    (hrh : TermOK rh) (S : SK → List Sym)
    (hTab : S sTab = SolveAux.recsOf rl ++ tail) (hZR : S kZR = []) (hTP : S kTP = [])
    (hCD : S kCD = []) (hCY : S kCY = []) (hCT : S kCT = natSyms H)
    (hHalf : S sHalf = natSyms h ++ rh) :
    Runs halfLoop S
      (Function.update (Function.update S sTab (SolveAux.recsOf (rl.drop (h * H)) ++ tail))
        kZR (SolveAux.recsOf (rl.take (h * H)).reverse))
      (fun _ => True) (H * (6 * ℓ + 6 * bitLen H + 20) + 7 * bitLen H + 50) := by
  let B : ℕ → SK → List Sym := fun n =>
    Function.update (Function.update (Function.update S
      sTab (SolveAux.recsOf (rl.drop ((h - n) * H)) ++ tail))
      kZR (SolveAux.recsOf (rl.take ((h - n) * H)).reverse)) kCY (natSyms n)
  let T : ℕ → ℕ := fun n => (7 * bitLen H + 7) + ((H * (6 * ℓ + 6 * bitLen H + 20) + 2) +
    (6 * zerosLead (encodeNat (n + 1)) + 8))
  have hk : ∀ n, n ≤ h → B n kCY = natSyms n := by
    intro n _
    simp [B]
  have hstep : ∀ n, n + 1 ≤ h → Runs halfCore (B (n + 1)) (B n) (fun _ => True) (T n) := by
    intro n hn
    have e1 : (h - (n + 1)) * H = 0 := by
      rw [show h - (n + 1) = 0 by omega, Nat.zero_mul]
    have e2 : (h - n) * H = H := by
      rw [show h - n = 1 by omega, Nat.one_mul]
    refine runs_mono (runs_congr (runs_seq
      (runs_L_copyBlock (src := kCT) (dst := kCD) (tmp := kTP) (by decide) (by decide) (by decide)
        (encodeNat H) [] (B (n + 1)) termOK_nil (by simp [B, hCT, natSyms_eq_map]))
      (runs_seq (runs_skipLoop rl ℓ hℓ tail H hH _ (by simp [Function.update_apply, B, e1, hTab])
          (by simp [Function.update_apply, B, e1]) (by simp [Function.update_apply, B, hTP])
          (by simp [Function.update_apply, B, hCD, natSyms_eq_map]))
        (runs_L (K := SK) fun v => ⟨_, dec_eval (k := kCY) (t := kTQ) (by decide) [] v n [] _
          termOK_nil (by simp [B, Function.update_apply, natSyms_eq_map])⟩))) ?_)
      (fun _ _ => trivial) (by simp only [T, bitLen]; omega)
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B, e2]
    by_cases k2 : k = kZR
    · subst k2; simp [B, e2]
    by_cases k3 : k = kCD
    · subst k3; simp [B, hCD]
    by_cases k4 : k = kCY
    · subst k4; simp [B, natSyms_eq_map]
    simp [B, Function.update_apply, k1, k2, k3, k4]
  have hL := BridgeRed.runs_counted_loop kCY halfCore B h T hk hstep
  have hBh : B h = Function.update S kCY ((encodeNat h).map Sym.bit ++ S kCY) := by
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B, hTab]
    by_cases k2 : k = kZR
    · subst k2; simp [B, hZR]
    by_cases k4 : k = kCY
    · subst k4; simp [B, hCY, natSyms_eq_map]
    simp [B, Function.update_apply, k1, k2, k4]
  have hB0 : B 0 = Function.update (Function.update S
      sTab (SolveAux.recsOf (rl.drop (h * H)) ++ tail))
      kZR (SolveAux.recsOf (rl.take (h * H)).reverse) := by
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B]
    by_cases k2 : k = kZR
    · subst k2; simp [B]
    by_cases k4 : k = kCY
    · subst k4; simp [B, hCY, natSyms_eq_map, encodeNat_zero]
    simp [B, Function.update_apply, k1, k2, k4]
  rw [hBh, hB0] at hL
  refine runs_mono (runs_seq
    (runs_L_copyBlock (src := sHalf) (dst := kCY) (tmp := kTP) (by decide) (by decide)
      (by decide) (encodeNat h) rh S hrh (by rw [hHalf, natSyms_eq_map])) hL)
    (fun _ _ => trivial) ?_
  have hl0 : ∀ B : ℕ → ℕ, loopCost B 0 = 1 := fun _ => rfl
  have hl1 : ∀ B : ℕ → ℕ, loopCost B 1 = B 0 + 1 + 1 := fun _ => rfl
  have hb1 : (encodeNat 1).length ≤ 1 := bitLen_le_one (le_refl 1)
  have hz1 : zerosLead (encodeNat 1) ≤ 1 := le_trans (zerosLead_le_length _) hb1
  have hz1' : zerosLead (encodeNat (0 + 1)) ≤ 1 := hz1
  rcases (show h = 0 ∨ h = 1 by omega) with rfl | rfl
  · rw [hl0]; simp only [encodeNat_zero, List.length_nil]; omega
  · rw [hl1]; simp only [T]; omega

/-! ## Clearing bits -/

/-- Pop the bits on top of `k`. -/
def clearBits (k : SK) : BProg SK := .seq (peekB k) (.loop isBitB (.seq (popB k) (peekB k)))

theorem clearLoop_eval (k : SK) :
    ∀ (bs : List Bool) (D : List Sym) (v : BReg) (S : SK → List Sym), TermOK D →
      S k = bs.map Sym.bit ++ D → v.1 = (bs.map Sym.bit ++ D).head? →
      Eval [] (.loop isBitB (.seq (popB k) (peekB k))) ⟨v, S⟩
        ⟨(D.head?, v.2), Function.update S k D⟩ (3 * bs.length + 1)
  | [], D, v, S, hD, hS, hv => by
    simp only [List.map_nil, List.nil_append] at hS hv ⊢
    have hc : isBitB v = false := by
      show isBitB (v.1, v.2) = false
      rw [hv]
      exact isBitB_head?_of_termOK hD v.2
    refine (Eval.loop_false hc).of_eq ?_ rfl
    rw [← hv, ← hS, Function.update_eq_self]
  | b :: bs, D, v, S, hD, hS, hv => by
    have hS' : S k = Sym.bit b :: (bs.map Sym.bit ++ D) := by rw [hS]; rfl
    have e1 : Eval [] (popB k) ⟨v, S⟩
        ⟨(some (Sym.bit b), v.2), Function.update S k (bs.map Sym.bit ++ D)⟩ 1 := by
      have := Eval.pop [] k (fun (v : BReg) o => (o, v.2)) v S
      rw [hS'] at this
      exact this
    have e2 : Eval [] (peekB k)
        ⟨(some (Sym.bit b), v.2), Function.update S k (bs.map Sym.bit ++ D)⟩
        ⟨((bs.map Sym.bit ++ D).head?, v.2), Function.update S k (bs.map Sym.bit ++ D)⟩ 1 := by
      have := Eval.peek [] k (fun (v : BReg) o => (o, v.2)) (some (Sym.bit b), v.2)
        (Function.update S k (bs.map Sym.bit ++ D))
      rw [Function.update_self] at this
      exact this
    have ih := clearLoop_eval k bs D ((bs.map Sym.bit ++ D).head?, v.2)
      (Function.update S k (bs.map Sym.bit ++ D)) hD (Function.update_self _ _ _) rfl
    have hc : isBitB v = true := by
      show isBitB (v.1, v.2) = true
      rw [hv]
      rfl
    refine (Eval.loop_true hc (Eval.seq e1 e2) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    rw [Function.update_idem]

theorem runs_clearBits (k : SK) (bs : List Bool) (D : List Sym) (hD : TermOK D)
    (S : SK → List Sym) (hS : S k = bs.map Sym.bit ++ D) :
    Runs (clearBits k) S (Function.update S k D) (fun _ => True) (3 * bs.length + 2) :=
  Runs.of_eval fun v => by
    have e1 : Eval [] (peekB k) ⟨v, S⟩ ⟨((bs.map Sym.bit ++ D).head?, v.2), S⟩ 1 := by
      have := Eval.peek [] k (fun (v : BReg) o => (o, v.2)) v S
      rw [hS] at this
      exact this
    exact ⟨_, _, Eval.seq e1 (clearLoop_eval k bs D _ S hD hS rfl), trivial, by omega⟩

end SubNLogN.Machine.Bridge.SolveParamsAux
