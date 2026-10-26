/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.RoundsRuns

/-!
# K4 rounds driver, loop and whole program (`Machine/FFT/RoundsLoop.lean`)

**Scope (honest summary).** Exact `Runs` facts (no `sorry`) for the loop body, the loop (by
`RunsIn.seq_while_det` over the counter `n = ℓ-1, …, 0`) and the whole driver `mainProg`, from the
part contracts and the arithmetic kernels' specs taken as hypotheses.
-/

namespace SubNLogN.Machine.FFT.RoundsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
  SubNLogN.Machine.FFTKit SubNLogN.Math.Walsh SubNLogN.Math.Common WP.W9comp

/-! ## Specifications of the arithmetic kernels -/

/-- `W3_decNat` body. -/
def DecSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 1 m) (fun _ => Sym) R) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (TMFw.zerosLead (Computability.encodeNat (a + 1)) + 1))

/-- `W3_cmpNat` body. -/
def CmpSpec {m : ℕ} {R : Type} (C : ℕ) (obs : R → Ordering) (P : Prog (Loc 2 m) (fun _ => Sym) R) :
    Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S S (fun r => obs r = Lib.ordOf a b) (C * (bitLen a + bitLen b + 1))

/-! ## Costs -/

/-- Cost bound of one prefix part call. -/
def kPc (CP JP D ℓ w m H : ℕ) : ℕ :=
  CP * ((D + 1) * cvolCube m (2 ^ ℓ) (w + D) + 2 ^ m * (w + m + 1) ^ JP + H)

/-- Cost bound of one chunk part call. -/
noncomputable def kCc (CC JC : ℕ) (lam' : ℝ) (D ℓ w m H : ℕ) : ℕ :=
  CC * (lcU lam' D ℓ w m + (w + m + 1) ^ JC + H)

/-- Cost bound of one twiddle part call. -/
def kTc (CT JT ℓ w m H : ℕ) : ℕ :=
  CT * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + cvolCube m (2 ^ ℓ) w + 2 ^ m * (w + m + 1) ^ JT + H)

/-- Cost of one loop iteration processing round `n`. -/
def bodyCost (Cdec Ccmp b₀ n KP KC KT : ℕ) : ℕ :=
  Cdec * (TMFw.zerosLead (Computability.encodeNat (n + 1)) + 1) + Ccmp * (bitLen n + bitLen b₀ + 1) +
    ((if b₀ ≤ n then KC else KP) + 1) + (KT + 1)

/-- The loop potential: `n` iterations remaining, `b₀` the first chunk slot. -/
def loopW (Bb KP KC KT b₀ n : ℕ) : ℕ := n * (Bb + KC + KT + 3) + min n b₀ * KP + 1

/-! ## The loop body -/

section Body

variable {EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type} [Fintype EP] [DecidableEq EP]
  [Fintype EC] [DecidableEq EC] [Fintype ET] [DecidableEq ET]

theorem chunkTest_of_le {obs : Rcmp → Ordering} {s : RR Rcp Rdec Rcmp Rdm RP RC RT} {n b : ℕ}
    (hs : obs (lcmp.get s) = Lib.ordOf n b) (h : b ≤ n) : chunkTest obs s = true := by
  simp only [chunkTest, hs, Lib.ordOf]
  rw [if_neg (by omega)]
  split_ifs <;> rfl

theorem chunkTest_of_lt {obs : Rcmp → Ordering} {s : RR Rcp Rdec Rcmp Rdm RP RC RT} {n b : ℕ}
    (hs : obs (lcmp.get s) = Lib.ordOf n b) (h : n < b) : chunkTest obs s = false := by
  simp only [chunkTest, hs, Lib.ordOf]
  rw [if_pos h]
  rfl

theorem runs_body {mdec mcmp Cdec Ccmp JP CP JC CC JT CT : ℕ} {Band : LayerRT → Prop} {lam' : ℝ}
    (hmdec : mdec ≤ 6) (hmcmp : mcmp ≤ 6) {Pdec : Prog (Loc 1 mdec) (fun _ => Sym) Rdec}
    {Pcmp : Prog (Loc 2 mcmp) (fun _ => Sym) Rcmp} {obsCmp : Rcmp → Ordering}
    {PP : Prog (KLoc (Fin 4) EP) (fun _ => Sym) RP} {PC : Prog (KLoc (Fin 4) EC) (fun _ => Sym) RC}
    {PT : Prog (KLoc (Fin 4) ET) (fun _ => Sym) RT}
    (hsDec : DecSpec Cdec Pdec) (hclCmp : Pcmp.Closed) (hsCmp : CmpSpec Ccmp obsCmp Pcmp)
    (hsP : PrefixSpec JP CP PP) (hsC : ChunkSpec Band lam' JC CC PC) (hsT : TwSpec JT CT PT)
    {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀)
    {q ℓ K w D : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ} {rest hrest trest : List Sym}
    (hshape : MidShapeOK q ℓ K w a) (hband : ChunkCallsBand Band q ℓ K w a) (htab : TabOK q ℓ θt)
    (hrestT : BlkTerm rest) (h1 : S₀ (.inl 1) = midHdr q ℓ K w a ++ hrest)
    (h2 : S₀ (.inl 2) = tabSyms w q ℓ θt ++ trest)
    (n : ℕ) (hn : n + 2 ≤ ℓ) {y : RArr (Cube (addrBits a)) (2 ^ ℓ)} (hy : ArrOnDiskGrid q y) :
    Runs (bodyProg (Rcp := Rcp) (Rdm := Rdm) hmdec hmcmp Pdec Pcmp obsCmp PP PC PT)
      (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms (n + 1)) (natSyms ((ℓ - 1) % K)))
      (st S₀ (carrSyms w (encCube q (truncArr q (diagArr (twPhase ℓ K a θt n)
        (truncArr q (hT (roundSet ℓ K a n) y))))) ++ rest) (natSyms n) (natSyms ((ℓ - 1) % K)))
      (fun s => loopTest s = decide (n ≠ 0))
      (bodyCost Cdec Ccmp ((ℓ - 1) % K) n (kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kTc CT JT ℓ w (addrBits a) (midHdr q ℓ K w a).length)) := by
  have hK1 : 1 ≤ K := hshape.2.2.2.2.1
  have hℓ2 : 2 ≤ ℓ := hshape.2.2.1
  have hKℓ : K ≤ ℓ - 1 := hshape.2.2.2.2.2.1
  have ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ := hshape.2.2.2.2.2.2.1
  -- 1. decrement
  have rd := runs_decK (Rcp := Rcp) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)
    hmdec hsDec (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms (n + 1))
      (natSyms ((ℓ - 1) % K))) n [] TermOK.nil (by simp)
  rw [List.append_nil, update_st_own0] at rd
  -- 2. compare with `b₀`
  have rc := runs_cmpK (Rcp := Rcp) (Rdec := Rdec) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)
    hmcmp hclCmp hsCmp (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms n)
      (natSyms ((ℓ - 1) % K))) n ((ℓ - 1) % K) [] [] TermOK.nil TermOK.nil (by simp) (by simp)
  have r12 := runs_seq rd rc
  have hy1 := truncArr_hT_diskGrid (roundSet ℓ K a n) hy
  -- 3. the chunk or prefix part
  have r3 : Runs (.seq (.seq (decK (Rcp := Rcp) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
        (RT := RT) (EP := EP) (EC := EC) (ET := ET) hmdec Pdec)
        (cmpK (Rcp := Rcp) (Rdec := Rdec) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT) hmcmp Pcmp))
      (.ite (chunkTest obsCmp) (chunkK PC) (prefixK PP)))
      (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms (n + 1)) (natSyms ((ℓ - 1) % K)))
      (st S₀ (carrSyms w (encCube q (truncArr q (hT (roundSet ℓ K a n) y))) ++ rest) (natSyms n)
        (natSyms ((ℓ - 1) % K)))
      (fun _ => True)
      (Cdec * (TMFw.zerosLead (Computability.encodeNat (n + 1)) + 1) +
        Ccmp * (bitLen n + bitLen ((ℓ - 1) % K) + 1) +
        ((if (ℓ - 1) % K ≤ n then kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length
          else kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length) + 1)) := by
    by_cases hb : (ℓ - 1) % K ≤ n
    · rw [if_pos hb]
      have hch : IsChunkRound ℓ K n := (isChunkRound_iff hK1 hn).2 hb
      obtain ⟨hfit, -⟩ := roundSet_chunk hℓ2 hK1 hKℓ ha hch
      have rC := runs_chunkK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP)
        (RT := RT) (EP := EP) (ET := ET) hsC hcl (natSyms ((ℓ - 1) % K)) hshape hband hch hy
        hrestT h1
      rw [layerCost_layerRT (q := q) (j₀ := roundJ0 ℓ K a n)
        (nS := addrBits a - roundJ0 ℓ K a n - D * K) (ρ := roundRho ℓ K n) (m := addrBits a)
        (by omega)] at rC
      exact runs_seq_ite_t' r12 (fun s hs => chunkTest_of_le hs hb) rC
    · rw [if_neg hb]
      have hnc : ¬ IsChunkRound ℓ K n := fun h => hb ((isChunkRound_iff hK1 hn).1 h)
      have rP := runs_prefixK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RC := RC)
        (RT := RT) (EC := EC) (ET := ET) (v := n) hsP hcl (natSyms ((ℓ - 1) % K)) hshape (by omega)
        hnc hy
        hrestT h1
      exact runs_seq_ite_f' r12 (fun s hs => chunkTest_of_lt hs (by omega)) rP
  -- 4. the twiddle part, 5. peek
  have rt := runs_twK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP)
    (RC := RC) (EP := EP) (EC := EC) (v := n) hsT hcl (natSyms ((ℓ - 1) % K)) hshape (by omega) htab hy1
    hrestT h1 h2
  have rp := runs_peekV (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP)
    (RC := RC) (RT := RT) (st S₀ (carrSyms w (encCube q (truncArr q (diagArr (twPhase ℓ K a θt n)
      (truncArr q (hT (roundSet ℓ K a n) y))))) ++ rest) (natSyms n) (natSyms ((ℓ - 1) % K)))
  refine runs_mono (runs_seq r3 (runs_seq rt rp)) (fun s hs => ?_) le_rfl
  rw [st_own0] at hs
  simp only [loopTest, hs, isSome_head?_natSyms]

end Body

/-! ## The loop -/

theorem bodyCost_le {Cdec Ccmp ℓ K n KP KC KT : ℕ} (hK : 1 ≤ K) (hKℓ : K ≤ ℓ) (hn : n + 1 ≤ ℓ) :
    bodyCost Cdec Ccmp ((ℓ - 1) % K) n KP KC KT ≤
      Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1) + ((if (ℓ - 1) % K ≤ n then KC else KP) + 1) +
        (KT + 1) := by
  unfold bodyCost
  have h1 : TMFw.zerosLead (Computability.encodeNat (n + 1)) ≤ ℓ := by
    have h0 := TMFw.zerosLead_le_length (Computability.encodeNat (n + 1))
    have h2 : (Computability.encodeNat (n + 1)).length ≤ n + 1 := by
      rw [IntMulTM.length_encodeNat]; exact Nat.size_le.2 Nat.lt_two_pow_self
    omega
  have h3 : bitLen n ≤ ℓ := (bitLen_le_self n).trans (by omega)
  have h4 : bitLen ((ℓ - 1) % K) ≤ ℓ :=
    (bitLen_le_self _).trans ((Nat.mod_lt _ (by omega)).le.trans hKℓ)
  have e1 : Cdec * (TMFw.zerosLead (Computability.encodeNat (n + 1)) + 1) ≤ Cdec * (ℓ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e2 : Ccmp * (bitLen n + bitLen ((ℓ - 1) % K) + 1) ≤ Ccmp * (2 * ℓ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem loopW_step {Bb KP KC KT b₀ n T : ℕ}
    (hT : T ≤ Bb + ((if b₀ ≤ n then KC else KP) + 1) + (KT + 1)) :
    T + 1 + loopW Bb KP KC KT b₀ n ≤ loopW Bb KP KC KT b₀ (n + 1) := by
  unfold loopW
  have e : (n + 1) * (Bb + KC + KT + 3) = n * (Bb + KC + KT + 3) + (Bb + KC + KT + 3) := by ring
  by_cases hb : b₀ ≤ n
  · rw [if_pos hb] at hT
    rw [Nat.min_eq_right hb, Nat.min_eq_right (by omega : b₀ ≤ n + 1), e]
    omega
  · rw [if_neg hb] at hT
    rw [Nat.min_eq_left (by omega : n ≤ b₀), Nat.min_eq_left (by omega : n + 1 ≤ b₀), e]
    have e2 : (n + 1) * KP = n * KP + KP := by ring
    rw [e2]
    omega

section Loop

variable {EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type} [Fintype EP] [DecidableEq EP]
  [Fintype EC] [DecidableEq EC] [Fintype ET] [DecidableEq ET]

theorem runs_loop {mdec mcmp Cdec Ccmp JP CP JC CC JT CT : ℕ} {Band : LayerRT → Prop} {lam' : ℝ}
    (hmdec : mdec ≤ 6) (hmcmp : mcmp ≤ 6) {Pdec : Prog (Loc 1 mdec) (fun _ => Sym) Rdec}
    {Pcmp : Prog (Loc 2 mcmp) (fun _ => Sym) Rcmp} {obsCmp : Rcmp → Ordering}
    {PP : Prog (KLoc (Fin 4) EP) (fun _ => Sym) RP} {PC : Prog (KLoc (Fin 4) EC) (fun _ => Sym) RC}
    {PT : Prog (KLoc (Fin 4) ET) (fun _ => Sym) RT}
    (hsDec : DecSpec Cdec Pdec) (hclCmp : Pcmp.Closed) (hsCmp : CmpSpec Ccmp obsCmp Pcmp)
    (hsP : PrefixSpec JP CP PP) (hsC : ChunkSpec Band lam' JC CC PC) (hsT : TwSpec JT CT PT)
    {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀)
    {q ℓ K w D : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ} {z : RArr (Cube (addrBits a)) (2 ^ ℓ)}
    {rest hrest trest : List Sym}
    (hshape : MidShapeOK q ℓ K w a) (hband : ChunkCallsBand Band q ℓ K w a) (htab : TabOK q ℓ θt)
    (hz : ArrOnDiskGrid q z) (hrestT : BlkTerm rest) (h1 : S₀ (.inl 1) = midHdr q ℓ K w a ++ hrest)
    (h2 : S₀ (.inl 2) = tabSyms w q ℓ θt ++ trest) :
    Runs (.seq (peekV (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
        (RT := RT) (EP := EP) (EC := EC) (ET := ET))
        (.loop loopTest (bodyProg (Rcp := Rcp) (Rdm := Rdm) hmdec hmcmp Pdec Pcmp obsCmp PP PC PT)))
      (st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - (ℓ - 1)))) ++ rest) (natSyms (ℓ - 1))
        (natSyms ((ℓ - 1) % K)))
      (st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - 0))) ++ rest) (natSyms 0)
        (natSyms ((ℓ - 1) % K)))
      (fun _ => True)
      (1 + loopW (Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1))
        (kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kTc CT JT ℓ w (addrBits a) (midHdr q ℓ K w a).length) ((ℓ - 1) % K) (ℓ - 1)) := by
  have hℓ2 : 2 ≤ ℓ := hshape.2.2.1
  have hK1 : 1 ≤ K := hshape.2.2.2.2.1
  have hKℓ : K ≤ ℓ - 1 := hshape.2.2.2.2.2.1
  have ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ := hshape.2.2.2.2.2.2.1
  have hℓ0 : 0 < ℓ := by omega
  have key := RunsIn.seq_while_det (ρ := [])
    (P₀ := peekV (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
        (RT := RT) (EP := EP) (EC := EC) (ET := ET))
    (p := bodyProg (Rcp := Rcp) (Rdm := Rdm) hmdec hmcmp Pdec Pcmp obsCmp PP PC PT) (c := loopTest)
    (st := fun x : Fin ℓ => st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - x.val))) ++ rest)
      (natSyms x.val) (natSyms ((ℓ - 1) % K)))
    (S := st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - (ℓ - 1)))) ++ rest)
      (natSyms (ℓ - 1)) (natSyms ((ℓ - 1) % K)))
    (cont := fun x => decide (x.val ≠ 0))
    (fun x => ⟨x.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩) (fun _ => ⟨0, hℓ0⟩)
    (fun x => x.val)
    (fun x => loopW (Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1))
      (kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
      (kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
      (kTc CT JT ℓ w (addrBits a) (midHdr q ℓ K w a).length) ((ℓ - 1) % K) x.val)
    (x₀ := ⟨ℓ - 1, by omega⟩) (T₀ := 1)
    (RunsIn.iff_runs.mpr (runs_mono (runs_peekV _) (fun s hs => by
      simp only [loopTest, hs, st_own0, isSome_head?_natSyms]) le_rfl))
    (fun x hx => by
      simp only [decide_eq_false_iff_not, not_not] at hx
      exact Fin.ext (by simp [hx])) (fun _ _ => rfl)
    (fun x _ => by unfold loopW; omega)
    (fun x hx => by
      have hx0 : x.val ≠ 0 := by simpa using hx
      obtain ⟨n, hn⟩ : ∃ n, x.val = n + 1 := ⟨x.val - 1, by omega⟩
      have hxl := x.isLt
      have hnl : n + 2 ≤ ℓ := by omega
      have hyd := arrK_diskGrid (D := D) (K := K) htab hz (ℓ - (n + 1))
      have hb := runs_body (Rcp := Rcp) (Rdm := Rdm) hmdec hmcmp hsDec hclCmp hsCmp hsP hsC hsT
        hcl hshape hband htab hrestT h1 h2 n hnl hyd
      have harr : truncArr q (diagArr (twPhase ℓ K a θt n) (truncArr q (hT (roundSet ℓ K a n)
          (arrK q D ℓ K a θt z (ℓ - (n + 1)))))) = arrK q D ℓ K a θt z (ℓ - n) := by
        rw [← roundRun_eq hℓ2 hK1 hKℓ ha n _ hyd, show ℓ - n = ℓ - (n + 1) + 1 by omega,
          arrK_succ _ _ _ _ _ _ _ (by omega : ℓ - (n + 1) < ℓ),
          show ℓ - 1 - (ℓ - (n + 1)) = n by omega]
      rw [harr] at hb
      have hcost := loopW_step (Bb := Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1))
        (KP := kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (KC := kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (KT := kTc CT JT ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (bodyCost_le (Cdec := Cdec) (Ccmp := Ccmp) hK1 (by omega) (by omega : n + 1 ≤ ℓ))
      refine ⟨bodyCost Cdec Ccmp ((ℓ - 1) % K) n
        (kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kTc CT JT ℓ w (addrBits a) (midHdr q ℓ K w a).length), ?_, ?_, ?_⟩
      · show x.val - 1 < x.val
        omega
      · show _ + 1 + loopW _ _ _ _ _ (x.val - 1) ≤ loopW _ _ _ _ _ x.val
        rw [hn, Nat.add_sub_cancel]
        exact hcost
      · show RunsIn [] _
          (st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - x.val))) ++ rest) (natSyms x.val)
            (natSyms ((ℓ - 1) % K)))
          (st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - (x.val - 1)))) ++ rest)
            (natSyms (x.val - 1)) (natSyms ((ℓ - 1) % K)))
          (fun v => loopTest v = decide (x.val - 1 ≠ 0)) _
        rw [hn, Nat.add_sub_cancel]
        exact RunsIn.iff_runs.mpr hb)
  exact runs_mono (RunsIn.iff_runs.mp key) (fun _ _ => trivial) le_rfl

end Loop

/-! ## The whole driver -/

/-- `W3_copyNat` body. -/
def CpSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 2 m) (fun _ => Sym) R) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 2 m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs P S (Function.update S (.inl 1) (natSyms a ++ S (.inl 1))) (fun _ => True)
      (C * (bitLen a + 1))

/-- `W6a_divModNat` body. -/
def DmSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 4 m) (fun _ => Sym) R) : Prop :=
  ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 m → List Sym), 0 < b → TermOK ra →
    TermOK rb → S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
    Runs P S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
        (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
      (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1))

/-- Total cost of the driver. -/
def mainCost (Ccp Cdec Ccmp Cdm q D ℓ K KP KC KT : ℕ) : ℕ :=
  setupCost Ccp Cdec Cdm q D ℓ K + ((KP + KT) +
    ((1 + loopW (Cdec * (ℓ + 1) + Ccmp * (2 * ℓ + 1)) KP KC KT ((ℓ - 1) % K) (ℓ - 1)) +
      (2 * bitLen ((ℓ - 1) % K) + 3)))

section Main

variable {EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type} [Fintype EP] [DecidableEq EP]
  [Fintype EC] [DecidableEq EC] [Fintype ET] [DecidableEq ET]

theorem runs_main {mcp mdec mcmp mdm Ccp Cdec Ccmp Cdm JP CP JC CC JT CT : ℕ}
    {Band : LayerRT → Prop} {lam' : ℝ} (hmcp : mcp ≤ 6) (hmdec : mdec ≤ 6) (hmcmp : mcmp ≤ 6)
    (hmdm : mdm ≤ 6) {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp}
    {Pdec : Prog (Loc 1 mdec) (fun _ => Sym) Rdec} {Pcmp : Prog (Loc 2 mcmp) (fun _ => Sym) Rcmp}
    {Pdm : Prog (Loc 4 mdm) (fun _ => Sym) Rdm} {obsCmp : Rcmp → Ordering}
    {PP : Prog (KLoc (Fin 4) EP) (fun _ => Sym) RP} {PC : Prog (KLoc (Fin 4) EC) (fun _ => Sym) RC}
    {PT : Prog (KLoc (Fin 4) ET) (fun _ => Sym) RT}
    (hsCp : CpSpec Ccp Pcp) (hsDec : DecSpec Cdec Pdec) (hclCmp : Pcmp.Closed)
    (hsCmp : CmpSpec Ccmp obsCmp Pcmp) (hclDm : Pdm.Closed) (hsDm : DmSpec Cdm Pdm)
    (hsP : PrefixSpec JP CP PP) (hsC : ChunkSpec Band lam' JC CC PC) (hsT : TwSpec JT CT PT)
    {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀)
    {q ℓ K w D : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ} {z : RArr (Cube (addrBits a)) (2 ^ ℓ)}
    {rest hrest trest : List Sym}
    (hshape : MidShapeOK q ℓ K w a) (hband : ChunkCallsBand Band q ℓ K w a) (htab : TabOK q ℓ θt)
    (hz : ArrOnDiskGrid q z) (hrestT : BlkTerm rest)
    (h0 : S₀ (.inl 0) = carrSyms w (encCube q z) ++ rest)
    (h1 : S₀ (.inl 1) = midHdr q ℓ K w a ++ hrest) (h2 : S₀ (.inl 2) = tabSyms w q ℓ θt ++ trest) :
    Runs (mainProg hmcp hmdec hmcmp hmdm Pcp Pdec Pcmp Pdm obsCmp PP PC PT) S₀
      (Function.update S₀ (.inl 0)
        (carrSyms w (encCube q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θt) z)) ++ rest))
      (fun _ => True)
      (mainCost Ccp Cdec Ccmp Cdm q D ℓ K
        (kPc CP JP D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kCc CC JC lam' D ℓ w (addrBits a) (midHdr q ℓ K w a).length)
        (kTc CT JT ℓ w (addrBits a) (midHdr q ℓ K w a).length)) := by
  have hℓ2 : 2 ≤ ℓ := hshape.2.2.1
  have hK1 : 1 ≤ K := hshape.2.2.2.2.1
  have hKℓ : K ≤ ℓ - 1 := hshape.2.2.2.2.2.1
  have ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ := hshape.2.2.2.2.2.2.1
  -- setup
  have rs := runs_setup (Rcmp := Rcmp) (RP := RP) (RC := RC) (RT := RT) (EP := EP) (EC := EC)
    (ET := ET) hmcp hmdec hmdm hsCp hsDec hclDm hsDm hcl hshape h1
  rw [h0] at rs
  -- the top round `v = ℓ - 1` (a prefix round)
  have htop : ¬ IsChunkRound ℓ K (ℓ - 1) := fun h => by have := h.2.2; omega
  have rP := runs_prefixK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RC := RC)
    (RT := RT) (EC := EC) (ET := ET) (v := ℓ - 1) hsP hcl (natSyms ((ℓ - 1) % K)) hshape
    (by omega) htop hz hrestT h1
  have hz1 := truncArr_hT_diskGrid (roundSet ℓ K a (ℓ - 1)) hz
  have rT := runs_twK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP)
    (RC := RC) (EP := EP) (EC := EC) (v := ℓ - 1) hsT hcl (natSyms ((ℓ - 1) % K)) hshape
    (by omega) htab hz1 hrestT h1 h2
  have harr1 : truncArr q (diagArr (twPhase ℓ K a θt (ℓ - 1))
      (truncArr q (hT (roundSet ℓ K a (ℓ - 1)) z))) = arrK q D ℓ K a θt z (ℓ - (ℓ - 1)) := by
    rw [show ℓ - (ℓ - 1) = 0 + 1 by omega, arrK_succ _ _ _ _ _ _ _ (by omega : 0 < ℓ), arrK_zero,
      Nat.sub_zero, roundRun_eq hℓ2 hK1 hKℓ ha (ℓ - 1) z hz]
  rw [harr1] at rT
  -- the loop
  have rL := runs_loop (Rcp := Rcp) (Rdm := Rdm) hmdec hmcmp hsDec hclCmp hsCmp hsP hsC hsT hcl
    hshape hband htab hz hrestT h1 h2
  -- drain `b₀`
  have rD := runs_drainK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP)
    (RC := RC) (RT := RT) 1 (st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - 0))) ++ rest)
      (natSyms 0) (natSyms ((ℓ - 1) % K)))
  rw [st_own1, update_st_own1, length_natSyms] at rD
  have hfin : st S₀ (carrSyms w (encCube q (arrK q D ℓ K a θt z (ℓ - 0))) ++ rest) (natSyms 0) [] =
      Function.update S₀ (.inl 0)
        (carrSyms w (encCube q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θt) z)) ++ rest) := by
    rw [Nat.sub_zero, arrK_ell, natSyms_zero, st, sx_final hcl]
  rw [hfin] at rD
  exact runs_seq rs (runs_seq (runs_seq rP rT) (runs_seq rL rD))

end Main

end SubNLogN.Machine.FFT.RoundsAux
