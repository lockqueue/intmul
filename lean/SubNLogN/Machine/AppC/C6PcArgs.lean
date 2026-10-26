/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6PcTest

/-!
# Lemma A.8 piece arguments (`Machine/AppC/C6PcArgs.lean`): `C6PcArgsStmt`

**Program** (`argsProg q`; named stacks `Fin 9`: `0`-`3` the counters `e, G, B, o`, `4`-`8` the
outputs; scratch `PE`; registers `NatArith.Reg`): `t = c6T q e` (`tProg`), `d = e - t - o`
(`subN`), `j = clog m (d+1) - 1 = log m d` (`satLoop`/`clogStep`, `dec`), `L = m^j`, `a = d - L`,
`q^o`, `G' = G·q^a·q^o`, `B' = B·q^a` (`powMulN`), `R' = W·⌈R/W⌉` with `W = W_b^k`, `R = (q²)^t`
(`clog` loop for `k`, `powMulN`, and a saturated loop of `q²` steps adding `W`); the five results are
copied to the outputs and every scratch number is dropped with its floor. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved (no `sorry`).** `c6PcArgs_holds (q) (hq : 2 ≤ q) : C6PcArgsStmt q`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts Computability

namespace AppC.C6PcAux

open NatArith

/-! ## Arithmetic -/

theorem clog_succ_eq {b d : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d) :
    Nat.clog b (d + 1) = Nat.log b d + 1 := by
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by omega) d)
  · rw [Nat.add_one_le_iff, Nat.lt_clog_iff_pow_lt (by omega)]
    exact Nat.lt_succ_of_le (Nat.pow_log_le_self b (by omega))

theorem ceil_lt_iff {W R : ℕ} (hW : 0 < W) (i : ℕ) : W * i < R ↔ i < (R + W - 1) / W := by
  have h := Nat.le_div_iff_mul_le (x := i + 1) (y := R + W - 1) hW
  have e : (i + 1) * W = W * i + W := by ring
  rw [e] at h
  constructor
  · intro hlt
    exact Nat.lt_of_succ_le (h.2 (by omega))
  · intro hlt
    have := h.1 (Nat.succ_le_of_lt hlt)
    omega

theorem ceil_le_sq {q e : ℕ} (hq : 2 ≤ q) (he : 35 ≤ e) :
    (c6R q e + c6Wk e - 1) / c6Wk e ≤ q ^ 2 := by
  have ht : 1 ≤ Nat.clog (q ^ 2) (c6Wk e) := (C6Aux.c6T_lt hq he).1
  have hW := C6Aux.c6Wk_pos e
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have h1 : (q ^ 2) ^ (Nat.clog (q ^ 2) (c6Wk e) - 1) < c6Wk e := (clog_lt_iff hq2).2 (by omega)
  have e1 : q ^ (2 * c6T q e) = q ^ 2 * (q ^ 2) ^ (Nat.clog (q ^ 2) (c6Wk e) - 1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    show 2 * Nat.clog (q ^ 2) (c6Wk e) = 2 + 2 * (Nat.clog (q ^ 2) (c6Wk e) - 1)
    omega
  have h2 : c6R q e < q ^ 2 * c6Wk e := by
    unfold c6R
    rw [e1]
    have hq0 : 0 < q ^ 2 := by positivity
    nlinarith
  have h3 : c6R q e + c6Wk e - 1 < (q ^ 2 + 1) * c6Wk e := by
    rw [add_mul, one_mul]
    omega
  exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hW).2 h3)

theorem c6Rp_eq (q e : ℕ) :
    c6Rp q e = c6Wk e * ((c6R q e + c6Wk e - 1) / c6Wk e) := rfl

section Generic

variable {K : Type} [DecidableEq K]

/-! ## In-place addition and the ceiling loop -/

/-- `P ← P + W` in place (`Y` a floored temporary, `t1 t2 t3` the `addN` temporaries, `T` the copy
temporary). -/
def addInPlace (P W Y t1 t2 t3 T : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark Y) (.seq (addN P W Y t1 t2 t3) (.seq (dropN P) (.seq (copyN Y P T) (dropF Y))))

theorem closed_addInPlace (P W Y t1 t2 t3 T : K) : (addInPlace P W Y t1 t2 t3 T).Closed :=
  ⟨closed_pushMark _, closed_addN _ _ _ _ _ _, closed_dropN _, closed_copyN _ _ _, closed_dropF _⟩

theorem runs_addInPlace {P W Y t1 t2 t3 T : K} (h : [P, W, Y, t1, t2, t3].Nodup) (hYT : Y ≠ T)
    (hPT : P ≠ T) (p w : ℕ) (rP rW : List Sym) (S : K → List Sym) (hrP : TermOK rP)
    (hrW : TermOK rW) (hP : S P = natSyms p ++ rP) (hW : S W = natSyms w ++ rW) :
    Runs (addInPlace P W Y t1 t2 t3 T) S (Function.update S P (natSyms (p + w) ++ rP))
      (fun _ => True) (1 + (20 * (bitLen p + bitLen w + 1) + ((2 * bitLen p + 4) +
        ((7 * bitLen (p + w) + 7) + (2 * bitLen (p + w) + 2))))) := by
  have hPY : P ≠ Y := fun e => by simp [e] at h
  have hWY : W ≠ Y := fun e => by simp [e] at h
  have e1 := runs_pushMark Y S
  have e2 := runs_addN h p w rP rW (Function.update S Y (Sym.mark :: S Y)) hrP hrW
    (by rw [Function.update_of_ne hPY]; exact hP) (by rw [Function.update_of_ne hWY]; exact hW)
  rw [Function.update_self, Function.update_idem] at e2
  have e3 := runs_dropN P p rP (Function.update S Y (natSyms (p + w) ++ Sym.mark :: S Y)) hrP
    (by rw [Function.update_of_ne hPY]; exact hP)
  have e4 := runs_copyN (src := Y) (dst := P) (tmp := T) hPY.symm hYT hPT (p + w)
    (Sym.mark :: S Y)
    (Function.update (Function.update S Y (natSyms (p + w) ++ Sym.mark :: S Y)) P rP)
    (termOK_mark _) (by rw [Function.update_of_ne hPY.symm, Function.update_self])
  rw [Function.update_self, Function.update_idem] at e4
  have e5 := runs_dropF Y (p + w) Sym.mark (S Y)
    (Function.update (Function.update S Y (natSyms (p + w) ++ Sym.mark :: S Y)) P
      (natSyms (p + w) ++ rP)) rfl (by rw [Function.update_of_ne hPY.symm, Function.update_self])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2
    (WP.W9comp.runs_seq e3 (WP.W9comp.runs_seq e4 e5)))) ?_
  rw [Function.update_comm hPY, Function.update_idem, Function.update_eq_self]

/-- Cost parameter of the ceiling loop. -/
def ceilM (W R : ℕ) : ℕ := 100 * (bitLen R + bitLen W + 2)

/-- The state of the ceiling loop after `i` steps. -/
def ceilSt (S : K → List Sym) (P : K) (W : ℕ) (rP : List Sym) (i : ℕ) : K → List Sym :=
  Function.update S P (natSyms (W * i) ++ rP)

theorem runs_ceilLoop {ns Kc t P x t1 t2 Ws Y a1 a2 a3 T : K}
    (hcmp : [P, x, t1, t2].Nodup) (hadd : [P, Ws, Y, a1, a2, a3].Nodup) (hYT : Y ≠ T)
    (hPT : P ≠ T) (hPK : P ≠ Kc) (hxK : x ≠ Kc) (hWK : Ws ≠ Kc) (hnK : ns ≠ Kc) (hnt : ns ≠ t)
    (hKt : Kc ≠ t) (W R n : ℕ) (hW : 0 < W) (hJn : (R + W - 1) / W ≤ n)
    (rP rx rW rn : List Sym) (S : K → List Sym) (hrP : TermOK rP) (hrx : TermOK rx)
    (hrW : TermOK rW) (hrn : TermOK rn) (hP : S P = natSyms 0 ++ rP)
    (hx : S x = natSyms R ++ rx) (hWs : S Ws = natSyms W ++ rW) (hns : S ns = natSyms n ++ rn) :
    Runs (satLoop ns Kc t P x t1 t2 (addInPlace P Ws Y a1 a2 a3 T)) S
      (ceilSt S P W rP ((R + W - 1) / W)) (fun _ => True)
      (n * (13 * ceilM W R + 17) + 16 * n + 13 * bitLen n + 12) := by
  have hPx : P ≠ x := fun e => by simp [e] at hcmp
  have hPW : P ≠ Ws := fun e => by simp [e] at hadd
  have hS0 : ceilSt S P W rP 0 = S := by
    rw [ceilSt, Nat.mul_zero, ← hP, Function.update_eq_self]
  have hJ : ∀ i, i ≤ (R + W - 1) / W → W * i ≤ R + W - 1 := by
    intro i hi
    have := (Nat.le_div_iff_mul_le hW).1 hi
    calc W * i = i * W := Nat.mul_comm _ _
      _ ≤ R + W - 1 := this
  have hbl : ∀ i, i ≤ (R + W - 1) / W → bitLen (W * i) ≤ bitLen R + bitLen W + 1 := by
    intro i hi
    have h1 := NatArith.bitLen_mono'' ((hJ i hi).trans (Nat.sub_le (R + W) 1))
    have h2 := NatArith.bitLen_add_le' R W
    omega
  have r := runs_satLoop hcmp hPK hxK hnK hnt hKt (addInPlace P Ws Y a1 a2 a3 T) (fun i => W * i)
    R ((R + W - 1) / W) n (ceil_lt_iff hW) hJn (ceilSt S P W rP) rP rx rn hrP hrx hrn
    (fun i _ => by simp [ceilSt])
    (fun i _ => by simp [ceilSt, Function.update_of_ne hPx.symm, hx])
    (by rw [hS0]; exact hns)
    (by simp [ceilSt, Function.update_of_ne hPK.symm])
    (ceilM W R)
    (fun i hi => (hbl i hi).trans (by unfold ceilM; omega))
    (fun i => 1 + (20 * (bitLen (W * i) + bitLen W + 1) + ((2 * bitLen (W * i) + 4) +
        ((7 * bitLen (W * i + W) + 7) + (2 * bitLen (W * i + W) + 2)))))
    (fun i hi => by
      have h1 := hbl i hi.le
      have h2 : bitLen (W * i + W) ≤ bitLen R + bitLen W + 1 := by
        rw [show W * i + W = W * (i + 1) by ring]
        exact hbl (i + 1) hi
      beta_reduce
      unfold ceilM
      omega)
    (fun i hi v => by
      have e := runs_addInPlace hadd hYT hPT (W * i) W rP rW
        (Function.update (ceilSt S P W rP i) Kc v) hrP hrW
        (by rw [Function.update_of_ne hPK, ceilSt, Function.update_self])
        (by rw [Function.update_of_ne hWK, ceilSt, Function.update_of_ne hPW.symm]; exact hWs)
      refine WP.W9comp.runs_congr e ?_
      rw [ceilSt, ceilSt, show W * i + W = W * (i + 1) by ring, Function.update_comm hPK.symm,
        Function.update_idem])
  rwa [hS0] at r

end Generic

/-! ## `d = e - t - o` -/

/-- `d = (e - t) - o` on scratch `16` (above a `mark`), `t` on scratch `3`. -/
def dProg : Prog (KLoc (Fin 9) PE) (fun _ => Sym) Reg :=
  .seq (pushMark (sv 5))
  (.seq (subN (.inl 0) (sv 3) (sv 5) (sv 8) (sv 9) (sv 15))
  (.seq (pushMark (sv 16))
  (.seq (subN (sv 5) (.inl 3) (sv 16) (sv 8) (sv 9) (sv 15))
    (dropF (sv 5)))))

theorem closed_dProg : dProg.Closed :=
  ⟨closed_pushMark _, closed_subN _ _ _ _ _ _, closed_pushMark _, closed_subN _ _ _ _ _ _,
    closed_dropF _⟩

theorem dProg_runs (e t o : ℕ) (r0 rt r3 : List Sym) (S : KLoc (Fin 9) PE → List Sym)
    (hr0 : TermOK r0) (hrt : TermOK rt) (hr3 : TermOK r3) (hte : t ≤ e) (hot : o ≤ e - t)
    (hS0 : S (.inl 0) = natSyms e ++ r0) (hS3 : S (sv 3) = natSyms t ++ rt)
    (hSo : S (.inl 3) = natSyms o ++ r3) :
    Runs dProg S (Function.update S (sv 16) (natSyms (e - t - o) ++ Sym.mark :: S (sv 16)))
      (fun _ => True) (1 + (20 * (bitLen e + bitLen t + 1) + (1 + (20 * (bitLen (e - t) +
        bitLen o + 1) + (2 * bitLen (e - t) + 2))))) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have e1 := runs_pushMark (sv 5) S
  set s1 := Function.update S (sv 5) (Sym.mark :: S (sv 5)) with hs1
  have e2 := runs_subN (x := .inl 0) (y := sv 3) (z := sv 5) (t1 := sv 8) (t2 := sv 9)
    (t3 := sv 15) (by decide) e t r0 rt s1 hr0 hrt hte (by simp [hs1, sv, hS0])
    (by simp [hs1, sv, hS3])
  rw [show s1 (sv 5) = Sym.mark :: S (sv 5) by simp [hs1]] at e2
  set s2 := Function.update s1 (sv 5) (natSyms (e - t) ++ Sym.mark :: S (sv 5)) with hs2
  have e3 := runs_pushMark (sv 16) s2
  rw [show s2 (sv 16) = S (sv 16) by simp [hs2, hs1, sv]] at e3
  set s3 := Function.update s2 (sv 16) (Sym.mark :: S (sv 16)) with hs3
  have e4 := runs_subN (x := sv 5) (y := .inl 3) (z := sv 16) (t1 := sv 8) (t2 := sv 9)
    (t3 := sv 15) (by decide) (e - t) o (Sym.mark :: S (sv 5)) r3 s3 (hmk _) hr3 hot
    (by simp [hs3, hs2, sv]) (by simp [hs3, hs2, hs1, sv, hSo])
  rw [show s3 (sv 16) = Sym.mark :: S (sv 16) by simp [hs3]] at e4
  set s4 := Function.update s3 (sv 16) (natSyms (e - t - o) ++ Sym.mark :: S (sv 16)) with hs4
  have e5 := runs_dropF (sv 5) (e - t) Sym.mark (S (sv 5)) s4 rfl (by simp [hs4, hs3, hs2, sv])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2
    (WP.W9comp.runs_seq e3 (WP.W9comp.runs_seq e4 e5)))) ?_
  funext x
  rcases x with j | j <;> fin_cases j <;> simp [hs4, hs3, hs2, hs1, sv]

/-! ## Cost helpers -/

theorem powCost_le' {c a n X Y : ℕ} (hn : n + 1 ≤ X) (hb : bitLen (a * c ^ n) + bitLen c + 2 ≤ Y) :
    powCost c a n ≤ 200 * (X * Y ^ 2) := by
  unfold powCost
  calc (n + 1) * (200 * (bitLen (a * c ^ n) + bitLen c + 2) ^ 2) ≤ X * (200 * Y ^ 2) :=
        Nat.mul_le_mul hn (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2))
    _ = 200 * (X * Y ^ 2) := by ring

theorem loopCost_le {n M X Y : ℕ} (hn : n + 1 ≤ X) (hM : M ≤ 200 * Y ^ 2) (hbn : bitLen n ≤ Y)
    (hY : 1 ≤ Y) : n * (13 * M + 17) + 16 * n + 13 * bitLen n + 12 ≤ 2700 * (X * Y ^ 2) := by
  have h1 : n * (13 * M + 17) ≤ X * (2600 * Y ^ 2 + 17) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : X * (2600 * Y ^ 2 + 17) = 2600 * (X * Y ^ 2) + 17 * X := by ring
  have h3 : X ≤ X * Y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h4 : Y ≤ X * Y ^ 2 := by
    calc Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
      _ ≤ X * Y ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem log_lt_self' {b d : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d) : Nat.log b d < d + 1 := by
  have h1 : Nat.log b d < 2 ^ Nat.log b d := Nat.lt_two_pow_self
  have h2 : 2 ^ Nat.log b d ≤ b ^ Nat.log b d := Nat.pow_le_pow_left hb _
  have h3 : b ^ Nat.log b d ≤ d := Nat.pow_log_le_self b (by omega)
  omega

theorem closed_incW {K : Type} (k t : K) :
    ((inc k t).liftRegs lW : Prog K (fun _ => Sym) Reg).Closed :=
  WP.W9comp.closed_liftRegs _ (by
    simp [Prog.Closed, Prog.FreeBelow, inc, scanLoop, scanBody, incFix, pushC, pushR, popR,
      restoreR, moveBits, moveBitsBody, Lib.skip])

theorem closed_decW {K : Type} (k t : K) :
    ((dec k t).liftRegs lW : Prog K (fun _ => Sym) Reg).Closed :=
  WP.W9comp.closed_liftRegs _ (by
    simp [Prog.Closed, Prog.FreeBelow, dec, scanLoop, scanBody, decFix, pushC, pushR, popR, peekR,
      restoreR, moveBits, moveBitsBody, Lib.skip])

/-! ## `j = log m d` -/

/-- `j = log m d` on scratch `18` (above a `mark`); `d` on scratch `16`, the loop bound `e` on
stack `0`. -/
def jProg : Prog (KLoc (Fin 9) PE) (fun _ => Sym) Reg :=
  .seq (pushMark (sv 17))
  (.seq (copyN (sv 16) (sv 17) (sv 7))
  (.seq ((inc (sv 17) (sv 15)).liftRegs lW)
  (.seq (pushMark (sv 18))
  (.seq (pushNat (sv 18) 0)
  (.seq (pushMark (sv 1))
  (.seq (pushNat (sv 1) 1)
  (.seq (satLoop (.inl 0) (sv 6) (sv 7) (sv 1) (sv 17) (sv 8) (sv 9)
    (clogStep (sv 1) (sv 18) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14) (sv 7) (sv 15) (tripleM 100)))
  (.seq ((dec (sv 18) (sv 15)).liftRegs lW)
  (.seq (dropF (sv 1))
    (dropF (sv 17)))))))))))

theorem closed_jProg : jProg.Closed :=
  ⟨closed_pushMark _, closed_copyN _ _ _, closed_incW _ _, closed_pushMark _, closed_pushNat _ _,
    closed_pushMark _, closed_pushNat _ _,
    closed_satLoop _ _ _ _ _ _ _ (closed_clogStep _ _ _ _ _ _ _ _ _ _), closed_decW _ _,
    closed_dropF _, closed_dropF _⟩

/-- Cost of `jProg` (flattened). -/
def jCost (e d : ℕ) : ℕ :=
  e * (13 * clogM (tripleM 100) (d + 1) e + 17) + 13 * bitLen d + 16 * e + 13 * bitLen e +
    6 * zerosLead (encodeNat (Nat.log (tripleM 100) d + 1)) +
    2 * bitLen (tripleM 100 ^ (Nat.log (tripleM 100) d + 1)) + 2 * bitLen (d + 1) + bitLen 0 +
    bitLen 1 + 45

theorem jCost_le {e d : ℕ} (hd : 1 ≤ d) (hde : d + 1 ≤ e) :
    jCost e d ≤ 3000 * ((e + 1) * (2 * e + 22) ^ 2) := by
  have hm := two_le_tripleM
  have hb0 : bitLen 0 ≤ 1 := (bitLen_le_self'' 0).trans (by norm_num)
  have hb1 : bitLen 1 ≤ 1 := bitLen_le_self'' 1
  have hbd : bitLen d ≤ e := (bitLen_le_self'' d).trans (by omega)
  have hbd1 : bitLen (d + 1) ≤ e := (bitLen_le_self'' _).trans hde
  have hbe : bitLen e ≤ e := bitLen_le_self'' e
  have hbm := bitLen_tripleM
  have hlog := log_lt_self' hm hd
  have hz : zerosLead (encodeNat (Nat.log (tripleM 100) d + 1)) ≤ e :=
    (zerosLead_le_length _).trans ((bitLen_le_self'' _).trans (by omega))
  have hpw : bitLen (tripleM 100 ^ (Nat.log (tripleM 100) d + 1)) ≤ 20 + e := by
    have h1 : tripleM 100 ^ (Nat.log (tripleM 100) d + 1) ≤ tripleM 100 * d := by
      rw [pow_succ']
      exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))
    have h2 := NatArith.bitLen_mono'' h1
    have h3 := NatArith.bitLen_mul_le' (tripleM 100) d
    omega
  have hc : clogM (tripleM 100) (d + 1) e ≤ 200 * (2 * e + 22) ^ 2 := by
    unfold clogM
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hL : e * (13 * clogM (tripleM 100) (d + 1) e + 17) ≤
      (e + 1) * (2600 * (2 * e + 22) ^ 2 + 17) := Nat.mul_le_mul (by omega) (by omega)
  have hE : (e + 1) * (2600 * (2 * e + 22) ^ 2 + 17) =
      2600 * ((e + 1) * (2 * e + 22) ^ 2) + 17 * (e + 1) := by ring
  have hV : 484 * (e + 1) ≤ (e + 1) * (2 * e + 22) ^ 2 := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  unfold jCost
  omega

theorem jProg_runs (e d : ℕ) (r0 rd : List Sym) (S : KLoc (Fin 9) PE → List Sym)
    (hr0 : TermOK r0) (hrd : TermOK rd) (hd : 1 ≤ d) (hde : d + 1 ≤ e)
    (hS0 : S (.inl 0) = natSyms e ++ r0) (hSd : S (sv 16) = natSyms d ++ rd) :
    Runs jProg S
      (Function.update S (sv 18) (natSyms (Nat.log (tripleM 100) d) ++ Sym.mark :: S (sv 18)))
      (fun _ => True) (jCost e d) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have hm := two_le_tripleM
  have e1 := runs_pushMark (sv 17) S
  set s1 := Function.update S (sv 17) (Sym.mark :: S (sv 17)) with hs1
  have e2 := runs_copyN (src := sv 16) (dst := sv 17) (tmp := sv 7) (by decide) (by decide)
    (by decide) d rd s1 hrd (by simp [hs1, sv, hSd])
  rw [show s1 (sv 17) = Sym.mark :: S (sv 17) by simp [hs1]] at e2
  set s2 := Function.update s1 (sv 17) (natSyms d ++ Sym.mark :: S (sv 17)) with hs2
  have e3 := WP.W9b.runs_lift lW (WP.W9b.rs_inc (k := sv 17) (t := sv 15) (by decide) d
    (Sym.mark :: S (sv 17)) s2 (hmk _) (by simp [hs2]))
  set s3 := Function.update s2 (sv 17) (natSyms (d + 1) ++ Sym.mark :: S (sv 17)) with hs3
  have e4 := runs_pushMark (sv 18) s3
  rw [show s3 (sv 18) = S (sv 18) by simp [hs3, hs2, hs1, sv]] at e4
  set s4 := Function.update s3 (sv 18) (Sym.mark :: S (sv 18)) with hs4
  have e5 := runs_pushNat (sv 18) 0 s4
  rw [show s4 (sv 18) = Sym.mark :: S (sv 18) by simp [hs4]] at e5
  set s5 := Function.update s4 (sv 18) (natSyms 0 ++ Sym.mark :: S (sv 18)) with hs5
  have e6 := runs_pushMark (sv 1) s5
  rw [show s5 (sv 1) = S (sv 1) by simp [hs5, hs4, hs3, hs2, hs1, sv]] at e6
  set s6 := Function.update s5 (sv 1) (Sym.mark :: S (sv 1)) with hs6
  have e7 := runs_pushNat (sv 1) 1 s6
  rw [show s6 (sv 1) = Sym.mark :: S (sv 1) by simp [hs6]] at e7
  set s7 := Function.update s6 (sv 1) (natSyms 1 ++ Sym.mark :: S (sv 1)) with hs7
  have hcn : Nat.clog (tripleM 100) (d + 1) ≤ e := by
    rw [clog_succ_eq hm hd]
    have := log_lt_self' hm hd
    omega
  have e8 := runs_clogLoop (ns := .inl 0) (Kc := sv 6) (t := sv 7) (P := sv 1) (x := sv 17)
    (t1 := sv 8) (t2 := sv 9) (Kk := sv 18) (Q := sv 10) (Tdst := sv 11) (A := sv 12)
    (Bs := sv 13) (Acc := sv 14) (ti := sv 15) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (tripleM 100) (d + 1) e hm hcn (Sym.mark :: S (sv 1)) (Sym.mark :: S (sv 17))
    (Sym.mark :: S (sv 18)) r0 s7 (hmk _) (hmk _) (hmk _) hr0 (by simp [hs7])
    (by simp [hs7, hs6, hs5, sv]) (by simp [hs7, hs6, hs5, hs4, hs3, sv])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hS0])
  rw [clog_succ_eq hm hd] at e8
  set s8 := clogSt s7 (sv 1) (sv 18) (tripleM 100) (Sym.mark :: S (sv 1)) (Sym.mark :: S (sv 18))
    (Nat.log (tripleM 100) d + 1) with hs8
  have e9 := WP.W9b.runs_lift lW (WP.W9b.rs_dec (k := sv 18) (t := sv 15) (by decide)
    (Nat.log (tripleM 100) d) (Sym.mark :: S (sv 18)) s8 (hmk _) (by simp [hs8, clogSt, sv]))
  set s9 := Function.update s8 (sv 18) (natSyms (Nat.log (tripleM 100) d) ++ Sym.mark :: S (sv 18))
    with hs9
  have e10 := runs_dropF (sv 1) (tripleM 100 ^ (Nat.log (tripleM 100) d + 1)) Sym.mark (S (sv 1))
    s9 rfl (by simp [hs9, hs8, clogSt, sv])
  set s10 := Function.update s9 (sv 1) (S (sv 1)) with hs10
  have e11 := runs_dropF (sv 17) (d + 1) Sym.mark (S (sv 17)) s10 rfl
    (by simp [hs10, hs9, hs8, clogSt, hs7, hs6, hs5, hs4, hs3, sv])
  have X := WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 (WP.W9comp.runs_seq e3
    (WP.W9comp.runs_seq e4 (WP.W9comp.runs_seq e5 (WP.W9comp.runs_seq e6
    (WP.W9comp.runs_seq e7 (WP.W9comp.runs_seq e8 (WP.W9comp.runs_seq e9
    (WP.W9comp.runs_seq e10 e11)))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ h => h)
    (le_of_eq (by unfold jCost; ring))
  funext x
  rcases x with j | j <;> fin_cases j <;>
    simp [hs10, hs9, hs8, clogSt, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv]

/-! ## `L`, `a`, `q^o`, `G'`, `B'` -/

/-- `L = m^j` (scratch `19`), `a = d - L` (`20`), `q^o` (`0`), `G' = G·q^a·q^o` (`2`),
`B' = B·q^a` (`4`), each above a `mark`. -/
def pProg (q : ℕ) : Prog (KLoc (Fin 9) PE) (fun _ => Sym) Reg :=
  .seq (pushMark (sv 19))
  (.seq (pushNat (sv 19) 1)
  (.seq (powMulN (sv 19) (tripleM 100) (sv 18) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14))
  (.seq (pushMark (sv 20))
  (.seq (subN (sv 16) (sv 19) (sv 20) (sv 8) (sv 9) (sv 15))
  (.seq (pushMark (sv 0))
  (.seq (pushNat (sv 0) 1)
  (.seq (powMulN (sv 0) q (.inl 3) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14))
  (.seq (pushMark (sv 2))
  (.seq (copyN (.inl 1) (sv 2) (sv 7))
  (.seq (powMulN (sv 2) q (sv 20) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14))
  (.seq (powMulN (sv 2) q (.inl 3) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14))
  (.seq (pushMark (sv 4))
  (.seq (copyN (.inl 2) (sv 4) (sv 7))
    (powMulN (sv 4) q (sv 20) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14)))))))))))))))

theorem closed_pProg (q : ℕ) : (pProg q).Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_pushMark _,
    closed_subN _ _ _ _ _ _, closed_pushMark _, closed_pushNat _ _,
    closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_pushMark _, closed_copyN _ _ _,
    closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_pushMark _,
    closed_copyN _ _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _⟩

/-- `R' = c6Rp q e` on scratch `23` (above a `mark`); `e` on stack `0`, `t` on scratch `3`. -/
def rProg (q : ℕ) : Prog (KLoc (Fin 9) PE) (fun _ => Sym) Reg :=
  .seq (pushMark (sv 17))
  (.seq (pushNat (sv 17) 0)
  (.seq (pushMark (sv 1))
  (.seq (pushNat (sv 1) 1)
  (.seq (satLoop (.inl 0) (sv 6) (sv 7) (sv 1) (.inl 0) (sv 8) (sv 9)
    (clogStep (sv 1) (sv 17) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14) (sv 7) (sv 15) (tripleM 100)))
  (.seq (dropF (sv 1))
  (.seq (pushMark (sv 21))
  (.seq (pushNat (sv 21) 1)
  (.seq (powMulN (sv 21) (tripleWb 100) (sv 17) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14))
  (.seq (dropF (sv 17))
  (.seq (pushMark (sv 22))
  (.seq (pushNat (sv 22) 1)
  (.seq (powMulN (sv 22) (q ^ 2) (sv 3) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14))
  (.seq (pushMark (sv 23))
  (.seq (pushNat (sv 23) 0)
  (.seq (pushMark (sv 5))
  (.seq (pushNat (sv 5) (q ^ 2))
  (.seq (satLoop (sv 5) (sv 6) (sv 7) (sv 23) (sv 22) (sv 8) (sv 9)
    (addInPlace (sv 23) (sv 21) (sv 1) (sv 10) (sv 11) (sv 12) (sv 13)))
  (.seq (dropF (sv 5))
  (.seq (dropF (sv 22))
    (dropF (sv 21)))))))))))))))))))))

theorem closed_rProg (q : ℕ) : (rProg q).Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, closed_pushMark _, closed_pushNat _ _,
    closed_satLoop _ _ _ _ _ _ _ (closed_clogStep _ _ _ _ _ _ _ _ _ _), closed_dropF _,
    closed_pushMark _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_dropF _,
    closed_pushMark _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_pushMark _,
    closed_pushNat _ _, closed_pushMark _, closed_pushNat _ _,
    closed_satLoop _ _ _ _ _ _ _ (closed_addInPlace _ _ _ _ _ _ _), closed_dropF _, closed_dropF _,
    closed_dropF _⟩

/-- The output state of `pProg`. -/
def pOut (S : KLoc (Fin 9) PE → List Sym) (q d j o G B : ℕ) : KLoc (Fin 9) PE → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    (sv 19) (natSyms (tripleM 100 ^ j) ++ Sym.mark :: S (sv 19)))
    (sv 20) (natSyms (d - tripleM 100 ^ j) ++ Sym.mark :: S (sv 20)))
    (sv 0) (natSyms (q ^ o) ++ Sym.mark :: S (sv 0)))
    (sv 2) (natSyms (G * q ^ (d - tripleM 100 ^ j) * q ^ o) ++ Sym.mark :: S (sv 2)))
    (sv 4) (natSyms (B * q ^ (d - tripleM 100 ^ j)) ++ Sym.mark :: S (sv 4))

/-- Cost of `pProg` (flattened). -/
def pCost (q d j o G B : ℕ) : ℕ :=
  powCost (tripleM 100) 1 j + powCost q 1 o + powCost q G (d - tripleM 100 ^ j) +
    powCost q (G * q ^ (d - tripleM 100 ^ j)) o + powCost q B (d - tripleM 100 ^ j) +
    20 * (bitLen d + bitLen (tripleM 100 ^ j) + 1) + 7 * bitLen G + 7 * bitLen B +
    2 * bitLen 1 + 21

theorem pProg_runs {q : ℕ} (hq : 2 ≤ q) (d j o G B : ℕ) (rd rj r3 r1 r2 : List Sym)
    (S : KLoc (Fin 9) PE → List Sym) (hrd : TermOK rd) (hrj : TermOK rj) (hr3 : TermOK r3)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hL : tripleM 100 ^ j ≤ d)
    (hSd : S (sv 16) = natSyms d ++ rd) (hSj : S (sv 18) = natSyms j ++ rj)
    (hSo : S (.inl 3) = natSyms o ++ r3) (hSG : S (.inl 1) = natSyms G ++ r1)
    (hSB : S (.inl 2) = natSyms B ++ r2) :
    Runs (pProg q) S (pOut S q d j o G B) (fun _ => True) (pCost q d j o G B) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have hq1 : 1 ≤ q := by omega
  have p1 := runs_pushMark (sv 19) S
  set s1 := Function.update S (sv 19) (Sym.mark :: S (sv 19)) with hs1
  have p2 := runs_pushNat (sv 19) 1 s1
  rw [show s1 (sv 19) = Sym.mark :: S (sv 19) by simp [hs1]] at p2
  set s2 := Function.update s1 (sv 19) (natSyms 1 ++ Sym.mark :: S (sv 19)) with hs2
  have p3 := runs_powMulN (k := sv 19) (ns := sv 18) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by decide) (tripleM 100)
    (by norm_num [tripleM]) 1 j (Sym.mark :: S (sv 19)) rj s2 (hmk _) hrj (by simp [hs2])
    (by simp [hs2, hs1, sv, hSj])
  rw [one_mul] at p3
  set s3 := Function.update s2 (sv 19) (natSyms (tripleM 100 ^ j) ++ Sym.mark :: S (sv 19))
    with hs3
  have p4 := runs_pushMark (sv 20) s3
  rw [show s3 (sv 20) = S (sv 20) by simp [hs3, hs2, hs1, sv]] at p4
  set s4 := Function.update s3 (sv 20) (Sym.mark :: S (sv 20)) with hs4
  have p5 := runs_subN (x := sv 16) (y := sv 19) (z := sv 20) (t1 := sv 8) (t2 := sv 9)
    (t3 := sv 15) (by decide) d (tripleM 100 ^ j) rd (Sym.mark :: S (sv 19)) s4 hrd (hmk _) hL
    (by simp [hs4, hs3, hs2, hs1, sv, hSd]) (by simp [hs4, hs3, sv])
  rw [show s4 (sv 20) = Sym.mark :: S (sv 20) by simp [hs4]] at p5
  set s5 := Function.update s4 (sv 20) (natSyms (d - tripleM 100 ^ j) ++ Sym.mark :: S (sv 20))
    with hs5
  have p6 := runs_pushMark (sv 0) s5
  rw [show s5 (sv 0) = S (sv 0) by simp [hs5, hs4, hs3, hs2, hs1, sv]] at p6
  set s6 := Function.update s5 (sv 0) (Sym.mark :: S (sv 0)) with hs6
  have p7 := runs_pushNat (sv 0) 1 s6
  rw [show s6 (sv 0) = Sym.mark :: S (sv 0) by simp [hs6]] at p7
  set s7 := Function.update s6 (sv 0) (natSyms 1 ++ Sym.mark :: S (sv 0)) with hs7
  have p8 := runs_powMulN (k := sv 0) (ns := .inl 3) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by decide) q hq1 1 o
    (Sym.mark :: S (sv 0)) r3 s7 (hmk _) hr3 (by simp [hs7])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hSo])
  rw [one_mul] at p8
  set s8 := Function.update s7 (sv 0) (natSyms (q ^ o) ++ Sym.mark :: S (sv 0)) with hs8
  have p9 := runs_pushMark (sv 2) s8
  rw [show s8 (sv 2) = S (sv 2) by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv]] at p9
  set s9 := Function.update s8 (sv 2) (Sym.mark :: S (sv 2)) with hs9
  have p10 := runs_copyN (src := .inl 1) (dst := sv 2) (tmp := sv 7) (by decide) (by decide)
    (by decide) G r1 s9 hr1 (by simp [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hSG])
  rw [show s9 (sv 2) = Sym.mark :: S (sv 2) by simp [hs9]] at p10
  set s10 := Function.update s9 (sv 2) (natSyms G ++ Sym.mark :: S (sv 2)) with hs10
  have p11 := runs_powMulN (k := sv 2) (ns := sv 20) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by decide) q hq1 G
    (d - tripleM 100 ^ j) (Sym.mark :: S (sv 2)) (Sym.mark :: S (sv 20)) s10 (hmk _) (hmk _)
    (by simp [hs10]) (by simp [hs10, hs9, hs8, hs7, hs6, hs5, sv])
  set s11 := Function.update s10 (sv 2)
    (natSyms (G * q ^ (d - tripleM 100 ^ j)) ++ Sym.mark :: S (sv 2)) with hs11
  have p12 := runs_powMulN (k := sv 2) (ns := .inl 3) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by decide) q hq1
    (G * q ^ (d - tripleM 100 ^ j)) o (Sym.mark :: S (sv 2)) r3 s11 (hmk _) hr3 (by simp [hs11])
    (by simp [hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hSo])
  set s12 := Function.update s11 (sv 2)
    (natSyms (G * q ^ (d - tripleM 100 ^ j) * q ^ o) ++ Sym.mark :: S (sv 2)) with hs12
  have p13 := runs_pushMark (sv 4) s12
  rw [show s12 (sv 4) = S (sv 4) by
    simp [hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv]] at p13
  set s13 := Function.update s12 (sv 4) (Sym.mark :: S (sv 4)) with hs13
  have p14 := runs_copyN (src := .inl 2) (dst := sv 4) (tmp := sv 7) (by decide) (by decide)
    (by decide) B r2 s13 hr2
    (by simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hSB])
  rw [show s13 (sv 4) = Sym.mark :: S (sv 4) by simp [hs13]] at p14
  set s14 := Function.update s13 (sv 4) (natSyms B ++ Sym.mark :: S (sv 4)) with hs14
  have p15 := runs_powMulN (k := sv 4) (ns := sv 20) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by decide) q hq1 B
    (d - tripleM 100 ^ j) (Sym.mark :: S (sv 4)) (Sym.mark :: S (sv 20)) s14 (hmk _) (hmk _)
    (by simp [hs14]) (by simp [hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, sv])
  have X := WP.W9comp.runs_seq p1 (WP.W9comp.runs_seq p2 (WP.W9comp.runs_seq p3
    (WP.W9comp.runs_seq p4 (WP.W9comp.runs_seq p5 (WP.W9comp.runs_seq p6
    (WP.W9comp.runs_seq p7 (WP.W9comp.runs_seq p8 (WP.W9comp.runs_seq p9
    (WP.W9comp.runs_seq p10 (WP.W9comp.runs_seq p11 (WP.W9comp.runs_seq p12
    (WP.W9comp.runs_seq p13 (WP.W9comp.runs_seq p14 p15)))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ h => h)
    (le_of_eq (by unfold pCost; ring))
  funext x
  rcases x with jj | jj <;> fin_cases jj <;>
    simp [pOut, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv]

/-- Cost of `rProg` (flattened). -/
def rCost (q e : ℕ) : ℕ :=
  e * (13 * clogM (tripleM 100) e e + 17) + 16 * e + 13 * bitLen e +
    powCost (tripleWb 100) 1 (c6K e) + powCost (q ^ 2) 1 (c6T q e) +
    q ^ 2 * (13 * ceilM (c6Wk e) (c6R q e) + 17) + 16 * q ^ 2 + 16 * bitLen (q ^ 2) +
    2 * bitLen (tripleM 100 ^ c6K e) + 2 * bitLen (c6K e) + 2 * bitLen (c6R q e) +
    2 * bitLen (c6Wk e) + 2 * bitLen 0 + 3 * bitLen 1 + 46

theorem rProg_runs {q : ℕ} (hq : 2 ≤ q) (e : ℕ) (he : 35 ≤ e) (r0 rt : List Sym)
    (S : KLoc (Fin 9) PE → List Sym) (hr0 : TermOK r0) (hrt : TermOK rt)
    (hS0 : S (.inl 0) = natSyms e ++ r0) (hS3 : S (sv 3) = natSyms (c6T q e) ++ rt) :
    Runs (rProg q) S (Function.update S (sv 23) (natSyms (c6Rp q e) ++ Sym.mark :: S (sv 23)))
      (fun _ => True) (rCost q e) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have hkle := c6K_le e
  have r1 := runs_pushMark (sv 17) S
  set s1 := Function.update S (sv 17) (Sym.mark :: S (sv 17)) with hs1
  have r2 := runs_pushNat (sv 17) 0 s1
  rw [show s1 (sv 17) = Sym.mark :: S (sv 17) by simp [hs1]] at r2
  set s2 := Function.update s1 (sv 17) (natSyms 0 ++ Sym.mark :: S (sv 17)) with hs2
  have r3 := runs_pushMark (sv 1) s2
  rw [show s2 (sv 1) = S (sv 1) by simp [hs2, hs1, sv]] at r3
  set s3 := Function.update s2 (sv 1) (Sym.mark :: S (sv 1)) with hs3
  have r4 := runs_pushNat (sv 1) 1 s3
  rw [show s3 (sv 1) = Sym.mark :: S (sv 1) by simp [hs3]] at r4
  set s4 := Function.update s3 (sv 1) (natSyms 1 ++ Sym.mark :: S (sv 1)) with hs4
  have r5 := runs_clogLoop (ns := .inl 0) (Kc := sv 6) (t := sv 7) (P := sv 1) (x := .inl 0)
    (t1 := sv 8) (t2 := sv 9) (Kk := sv 17) (Q := sv 10) (Tdst := sv 11) (A := sv 12)
    (Bs := sv 13) (Acc := sv 14) (ti := sv 15) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (tripleM 100) e e two_le_tripleM hkle (Sym.mark :: S (sv 1)) r0 (Sym.mark :: S (sv 17)) r0
    s4 (hmk _) hr0 (hmk _) hr0 (by simp [hs4]) (by simp [hs4, hs3, hs2, sv])
    (by simp [hs4, hs3, hs2, hs1, sv, hS0]) (by simp [hs4, hs3, hs2, hs1, sv, hS0])
  rw [show Nat.clog (tripleM 100) e = c6K e from rfl] at r5
  set s5 := clogSt s4 (sv 1) (sv 17) (tripleM 100) (Sym.mark :: S (sv 1))
    (Sym.mark :: S (sv 17)) (c6K e) with hs5
  have r6 := runs_dropF (sv 1) (tripleM 100 ^ c6K e) Sym.mark (S (sv 1)) s5 rfl
    (by simp [hs5, clogSt, sv])
  set s6 := Function.update s5 (sv 1) (S (sv 1)) with hs6
  have r7 := runs_pushMark (sv 21) s6
  rw [show s6 (sv 21) = S (sv 21) by simp [hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv]] at r7
  set s7 := Function.update s6 (sv 21) (Sym.mark :: S (sv 21)) with hs7
  have r8 := runs_pushNat (sv 21) 1 s7
  rw [show s7 (sv 21) = Sym.mark :: S (sv 21) by simp [hs7]] at r8
  set s8 := Function.update s7 (sv 21) (natSyms 1 ++ Sym.mark :: S (sv 21)) with hs8
  have r9 := runs_powMulN (k := sv 21) (ns := sv 17) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by decide) (tripleWb 100)
    (by decide) 1 (c6K e) (Sym.mark :: S (sv 21)) (Sym.mark :: S (sv 17)) s8 (hmk _) (hmk _)
    (by simp [hs8]) (by simp [hs8, hs7, hs6, hs5, clogSt, sv])
  rw [one_mul, show tripleWb 100 ^ c6K e = c6Wk e from rfl] at r9
  set s9 := Function.update s8 (sv 21) (natSyms (c6Wk e) ++ Sym.mark :: S (sv 21)) with hs9
  have r10 := runs_dropF (sv 17) (c6K e) Sym.mark (S (sv 17)) s9 rfl
    (by simp [hs9, hs8, hs7, hs6, hs5, clogSt, sv])
  set s10 := Function.update s9 (sv 17) (S (sv 17)) with hs10
  have r11 := runs_pushMark (sv 22) s10
  rw [show s10 (sv 22) = S (sv 22) by
    simp [hs10, hs9, hs8, hs7, hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv]] at r11
  set s11 := Function.update s10 (sv 22) (Sym.mark :: S (sv 22)) with hs11
  have r12 := runs_pushNat (sv 22) 1 s11
  rw [show s11 (sv 22) = Sym.mark :: S (sv 22) by simp [hs11]] at r12
  set s12 := Function.update s11 (sv 22) (natSyms 1 ++ Sym.mark :: S (sv 22)) with hs12
  have hR : (q ^ 2) ^ c6T q e = c6R q e := by unfold c6R; rw [← pow_mul]
  have r13 := runs_powMulN (k := sv 22) (ns := sv 3) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by decide) (q ^ 2)
    (Nat.one_le_pow _ _ (by omega)) 1 (c6T q e) (Sym.mark :: S (sv 22)) rt s12 (hmk _) hrt
    (by simp [hs12])
    (by simp [hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv, hS3])
  rw [one_mul, hR] at r13
  set s13 := Function.update s12 (sv 22) (natSyms (c6R q e) ++ Sym.mark :: S (sv 22)) with hs13
  have r14 := runs_pushMark (sv 23) s13
  rw [show s13 (sv 23) = S (sv 23) by
    simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv]] at r14
  set s14 := Function.update s13 (sv 23) (Sym.mark :: S (sv 23)) with hs14
  have r15 := runs_pushNat (sv 23) 0 s14
  rw [show s14 (sv 23) = Sym.mark :: S (sv 23) by simp [hs14]] at r15
  set s15 := Function.update s14 (sv 23) (natSyms 0 ++ Sym.mark :: S (sv 23)) with hs15
  have r16 := runs_pushMark (sv 5) s15
  rw [show s15 (sv 5) = S (sv 5) by simp [hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6,
    hs5, clogSt, hs4, hs3, hs2, hs1, sv]] at r16
  set s16 := Function.update s15 (sv 5) (Sym.mark :: S (sv 5)) with hs16
  have r17 := runs_pushNat (sv 5) (q ^ 2) s16
  rw [show s16 (sv 5) = Sym.mark :: S (sv 5) by simp [hs16]] at r17
  set s17 := Function.update s16 (sv 5) (natSyms (q ^ 2) ++ Sym.mark :: S (sv 5)) with hs17
  have r18 := runs_ceilLoop (ns := sv 5) (Kc := sv 6) (t := sv 7) (P := sv 23) (x := sv 22)
    (t1 := sv 8) (t2 := sv 9) (Ws := sv 21) (Y := sv 1) (a1 := sv 10) (a2 := sv 11)
    (a3 := sv 12) (T := sv 13) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (c6Wk e) (c6R q e) (q ^ 2)
    (C6Aux.c6Wk_pos e) (ceil_le_sq hq he) (Sym.mark :: S (sv 23)) (Sym.mark :: S (sv 22))
    (Sym.mark :: S (sv 21)) (Sym.mark :: S (sv 5)) s17 (hmk _) (hmk _) (hmk _) (hmk _)
    (by simp [hs17, hs16, hs15, sv]) (by simp [hs17, hs16, hs15, hs14, hs13, sv])
    (by simp [hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, sv]) (by simp [hs17])
  set s18 := ceilSt s17 (sv 23) (c6Wk e) (Sym.mark :: S (sv 23))
    ((c6R q e + c6Wk e - 1) / c6Wk e) with hs18
  have r19 := runs_dropF (sv 5) (q ^ 2) Sym.mark (S (sv 5)) s18 rfl
    (by simp [hs18, ceilSt, hs17, sv])
  set s19 := Function.update s18 (sv 5) (S (sv 5)) with hs19
  have r20 := runs_dropF (sv 22) (c6R q e) Sym.mark (S (sv 22)) s19 rfl
    (by simp [hs19, hs18, ceilSt, hs17, hs16, hs15, hs14, hs13, sv])
  set s20 := Function.update s19 (sv 22) (S (sv 22)) with hs20
  have r21 := runs_dropF (sv 21) (c6Wk e) Sym.mark (S (sv 21)) s20 rfl
    (by simp [hs20, hs19, hs18, ceilSt, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, sv])
  have X := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6
    (WP.W9comp.runs_seq r7 (WP.W9comp.runs_seq r8 (WP.W9comp.runs_seq r9
    (WP.W9comp.runs_seq r10 (WP.W9comp.runs_seq r11 (WP.W9comp.runs_seq r12
    (WP.W9comp.runs_seq r13 (WP.W9comp.runs_seq r14 (WP.W9comp.runs_seq r15
    (WP.W9comp.runs_seq r16 (WP.W9comp.runs_seq r17 (WP.W9comp.runs_seq r18
    (WP.W9comp.runs_seq r19 (WP.W9comp.runs_seq r20 r21)))))))))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ h => h)
    (le_of_eq (by unfold rCost; ring))
  funext x
  rcases x with jj | jj <;> fin_cases jj <;>
    simp [hs20, hs19, hs18, ceilSt, c6Rp_eq, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9,
      hs8, hs7, hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv]

/-! ## The program -/

/-- Copy the five results to the outputs. -/
def outProg : Prog (KLoc (Fin 9) PE) (fun _ => Sym) Reg :=
  .seq (copyN (sv 18) (.inl 4) (sv 7))
  (.seq (copyN (sv 23) (.inl 5) (sv 7))
  (.seq (copyN (sv 0) (.inl 6) (sv 7))
  (.seq (copyN (sv 2) (.inl 7) (sv 7))
    (copyN (sv 4) (.inl 8) (sv 7)))))

/-- Drop the scratch numbers with their floors. -/
def cleanProg : Prog (KLoc (Fin 9) PE) (fun _ => Sym) Reg :=
  .seq (dropF (sv 23)) (.seq (dropF (sv 4)) (.seq (dropF (sv 2)) (.seq (dropF (sv 0))
  (.seq (dropF (sv 20)) (.seq (dropF (sv 19)) (.seq (dropF (sv 18)) (.seq (dropF (sv 16))
    (dropF (sv 3)))))))))

/-- The piece-arguments program (named stacks `Fin 9`). -/
def argsProg (q : ℕ) : Prog (KLoc (Fin 9) PE) (fun _ => Sym) Reg :=
  .seq (tProg q 0) (.seq dProg (.seq jProg (.seq (pProg q) (.seq (rProg q)
    (.seq outProg cleanProg)))))

theorem closed_argsProg (q : ℕ) : (argsProg q).Closed :=
  ⟨closed_tProg q 0, closed_dProg, closed_jProg, closed_pProg q, closed_rProg q,
    ⟨closed_copyN _ _ _, closed_copyN _ _ _, closed_copyN _ _ _, closed_copyN _ _ _,
      closed_copyN _ _ _⟩,
    ⟨closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _,
      closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _⟩⟩

/-- Cost of `dProg`. -/
def dCost (e t o : ℕ) : ℕ :=
  1 + (20 * (bitLen e + bitLen t + 1) + (1 + (20 * (bitLen (e - t) + bitLen o + 1) +
    (2 * bitLen (e - t) + 2))))

/-- The constant of `C6PcArgsStmt q`. -/
def argsC (q : ℕ) : ℕ := tC q + 40000 * (bitLen q + 1) ^ 2 * (10000 + 2000 * q ^ 2)

theorem args_cost_le {q e G B o : ℕ} (hq : 2 ≤ q) (he : 35 ≤ e) (ho : o < e - c6T q e) :
    tC q * (e + 1) ^ 3 + dCost e (c6T q e) o + jCost e (e - c6T q e - o) +
      pCost q (e - c6T q e - o) (Nat.log (tripleM 100) (e - c6T q e - o)) o G B + rCost q e +
      7 * bitLen (Nat.log (tripleM 100) (e - c6T q e - o)) + 9 * bitLen (c6Rp q e) +
      9 * bitLen (q ^ o) +
      9 * bitLen (G * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))
        * q ^ o) +
      9 * bitLen (B * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))) +
      2 * bitLen (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) +
      2 * bitLen (tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) +
      2 * bitLen (Nat.log (tripleM 100) (e - c6T q e - o)) + 2 * bitLen (e - c6T q e - o) +
      2 * bitLen (c6T q e) + 53 ≤ argsC q * (e + bitLen G + bitLen B + 1) ^ 3 := by
  have hT := C6Aux.c6T_lt hq he
  have hm := two_le_tripleM
  have hG' : G * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) *
      q ^ o = c6PG q e G o := by unfold c6PG c6PL c6PJ; ring
  have hB' : B * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) =
      c6PB q e B o := by unfold c6PB c6PL c6PJ; ring
  rw [hG', hB']
  obtain ⟨X, hX⟩ : ∃ X, X = e + bitLen G + bitLen B + 1 := ⟨_, rfl⟩
  rw [← hX]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 200 * (bitLen q + 1) * X := ⟨_, rfl⟩
  have hYX : Y = 200 * (bitLen q * X) + 200 * X := by rw [hY]; ring
  have heX : e + 1 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hqX : bitLen q ≤ bitLen q * X := Nat.le_mul_of_pos_right _ (by omega)
  have heqX : (e + 1) * bitLen q ≤ bitLen q * X := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ heX
  have hY1 : 1 ≤ Y := by omega
  have hXZ : X ≤ X * Y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hYZ : Y ≤ X * Y ^ 2 := by
    calc Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
      _ ≤ X * Y ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hd1 : 1 ≤ e - c6T q e - o := by omega
  have hde : e - c6T q e - o + 1 ≤ e := by omega
  have hLd : tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o) ≤ e - c6T q e - o :=
    Nat.pow_log_le_self _ (by omega)
  have hjL : Nat.log (tripleM 100) (e - c6T q e - o) <
      tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hm _)
  have bt : bitLen (c6T q e) ≤ e := (bitLen_le_self'' _).trans hT.2.le
  have bd : bitLen (e - c6T q e - o) ≤ e := (bitLen_le_self'' _).trans (by omega)
  have bj : bitLen (Nat.log (tripleM 100) (e - c6T q e - o)) ≤ e :=
    (bitLen_le_self'' _).trans (by omega)
  have bL : bitLen (tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) ≤ e :=
    (bitLen_le_self'' _).trans (by omega)
  have ba : bitLen (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) ≤ e :=
    (bitLen_le_self'' _).trans (by omega)
  have bqo := bitLen_qpow_le (e := e) hq (by omega : o ≤ e)
  have bRp : bitLen (c6Rp q e) ≤ 2 * ((e + 1) * bitLen q) := by
    have h := bitLen_c6Rp_le hq he
    have e1 : (2 * e + 2) * bitLen q = 2 * ((e + 1) * bitLen q) := by ring
    omega
  have bG : bitLen (c6PG q e G o) ≤ 2 * ((e + 1) * bitLen q) + bitLen G := by
    have h := bitLen_c6PG_le (G := G) hq ho
    rw [mul_assoc] at h
    exact h
  have bB := bitLen_c6PB_le (B := B) (o := o) (e := e) hq
  have hdC : dCost e (c6T q e) o ≤ 100 * X := by
    unfold dCost
    have := bitLen_le_self'' e
    have := bitLen_le_self'' o
    have : bitLen (e - c6T q e) ≤ e := (bitLen_le_self'' _).trans (by omega)
    omega
  have hj := jCost_le hd1 hde
  have hjZ : (e + 1) * (2 * e + 22) ^ 2 ≤ X * Y ^ 2 :=
    Nat.mul_le_mul heX (Nat.pow_le_pow_left (by omega) 2)
  have hp : pCost q (e - c6T q e - o) (Nat.log (tripleM 100) (e - c6T q e - o)) o G B ≤
      1100 * (X * Y ^ 2) := by
    unfold pCost
    have hAX : (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o) + 1) *
        bitLen q ≤ bitLen q * X := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have p1 : powCost (tripleM 100) 1 (Nat.log (tripleM 100) (e - c6T q e - o)) ≤
        200 * (X * Y ^ 2) := powCost_le' (by omega) (by
          rw [one_mul]; have := bitLen_tripleM; omega)
    have p2 : powCost q 1 o ≤ 200 * (X * Y ^ 2) := powCost_le' (by omega) (by
      rw [one_mul]; omega)
    have p3 : powCost q G (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))
        ≤ 200 * (X * Y ^ 2) := powCost_le' (by omega) (by
          have h1 := NatArith.bitLen_mul_le' G
            (q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)))
          have h2 := bitLen_pow_le hq
            (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))
          omega)
    have p4 : powCost q (G * q ^ (e - c6T q e - o -
        tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))) o ≤ 200 * (X * Y ^ 2) :=
      powCost_le' (by omega) (by rw [hG']; omega)
    have p5 : powCost q B (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))
        ≤ 200 * (X * Y ^ 2) := powCost_le' (by omega) (by
          have h1 := NatArith.bitLen_mul_le' B
            (q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)))
          have h2 := bitLen_pow_le hq
            (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))
          omega)
    have hb1 : bitLen 1 ≤ 1 := bitLen_le_self'' 1
    omega
  have hr : rCost q e ≤ 3500 * (X * Y ^ 2) + 1400 * (q ^ 2 * (X * Y ^ 2)) := by
    unfold rCost
    have hkle := c6K_le e
    have hbe := bitLen_le_self'' e
    have hbm := bitLen_tripleM
    have r1 := loopCost_le (n := e) (M := clogM (tripleM 100) e e) (X := X) (Y := Y) (by omega)
      (by
        unfold clogM
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)) (by omega) hY1
    have bWk : bitLen (tripleWb 100 ^ c6K e) ≤ 68 * (e + 1) := by
      have h0 := bitLen_pow_le (q := tripleWb 100) (by decide) (c6K e)
      have h1 : (c6K e + 1) * bitLen (tripleWb 100) ≤ (e + 1) * 68 :=
        Nat.mul_le_mul (by omega) bitLen_tripleWb
      omega
    have r2 : powCost (tripleWb 100) 1 (c6K e) ≤ 200 * (X * Y ^ 2) := powCost_le' (by omega) (by
      rw [one_mul]; have := bitLen_tripleWb; omega)
    have bR : bitLen (c6R q e) ≤ 2 * ((e + 1) * bitLen q) := by
      unfold c6R
      have h := bitLen_pow_le hq (2 * c6T q e)
      have h2 : (2 * c6T q e + 1) * bitLen q ≤ 2 * ((e + 1) * bitLen q) := by
        rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have hRq : (q ^ 2) ^ c6T q e = c6R q e := by unfold c6R; rw [← pow_mul]
    have bq2 : bitLen (q ^ 2) ≤ 3 * bitLen q := by
      have := bitLen_pow_le hq 2
      omega
    have r3 : powCost (q ^ 2) 1 (c6T q e) ≤ 200 * (X * Y ^ 2) := powCost_le' (by omega) (by
      rw [one_mul, hRq]; omega)
    have bW : bitLen (c6Wk e) ≤ 68 * (e + 1) := bWk
    have hcM : ceilM (c6Wk e) (c6R q e) ≤ 100 * Y := by unfold ceilM; omega
    have r4 : q ^ 2 * (13 * ceilM (c6Wk e) (c6R q e) + 17) ≤ 1300 * (q ^ 2 * Y) + 17 * q ^ 2 := by
      have h1 : q ^ 2 * (13 * ceilM (c6Wk e) (c6R q e) + 17) ≤ q ^ 2 * (1300 * Y + 17) :=
        Nat.mul_le_mul_left _ (by omega)
      have e2 : q ^ 2 * (1300 * Y + 17) = 1300 * (q ^ 2 * Y) + 17 * q ^ 2 := by ring
      omega
    have hqY : q ^ 2 * Y ≤ q ^ 2 * (X * Y ^ 2) := Nat.mul_le_mul_left _ hYZ
    have hq2 : q ^ 2 ≤ q ^ 2 * (X * Y ^ 2) := Nat.le_mul_of_pos_right _ (by positivity)
    have bmk : bitLen (tripleM 100 ^ c6K e) ≤ bitLen e + bitLen (tripleM 100) + 2 :=
      clog_pow_bitLen hm le_rfl
    have bk : bitLen (c6K e) ≤ e := (bitLen_le_self'' _).trans hkle
    have b0 : bitLen 0 ≤ 1 := (bitLen_le_self'' 0).trans (by norm_num)
    have b1 : bitLen 1 ≤ 1 := bitLen_le_self'' 1
    omega
  have hTX : tC q * (e + 1) ^ 3 ≤ tC q * X ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left heX 3)
  have hRHS : argsC q * X ^ 3 = tC q * X ^ 3 + 10000 * (X * Y ^ 2) +
      2000 * (q ^ 2 * (X * Y ^ 2)) := by
    rw [hY]; unfold argsC; ring
  rw [hRHS]
  omega

theorem args_runs {q : ℕ} (hq : 2 ≤ q) (e G B o : ℕ) (he : 35 ≤ e) (ho : o < e - c6T q e)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 : List Sym) (S : KLoc (Fin 9) PE → List Sym)
    (hr0 : TermOK r0) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (hS0 : S (.inl 0) = natSyms e ++ r0) (hS1 : S (.inl 1) = natSyms G ++ r1)
    (hS2 : S (.inl 2) = natSyms B ++ r2) (hS3 : S (.inl 3) = natSyms o ++ r3)
    (hS4 : S (.inl 4) = r4) (hS5 : S (.inl 5) = r5) (hS6 : S (.inl 6) = r6)
    (hS7 : S (.inl 7) = r7) (hS8 : S (.inl 8) = r8) :
    Runs (argsProg q) S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (.inl 4) (natSyms (c6PJ q e o) ++ r4))
        (.inl 5) (natSyms (c6Rp q e) ++ r5))
        (.inl 6) (natSyms (q ^ o) ++ r6))
        (.inl 7) (natSyms (c6PG q e G o) ++ r7))
        (.inl 8) (natSyms (c6PB q e B o) ++ r8))
      (fun _ => True) (argsC q * (e + bitLen G + bitLen B + 1) ^ 3) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have hT := C6Aux.c6T_lt hq he
  have hd1 : 1 ≤ e - c6T q e - o := by omega
  have hde : e - c6T q e - o + 1 ≤ e := by omega
  have hLd : tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o) ≤ e - c6T q e - o :=
    Nat.pow_log_le_self _ (by omega)
  have a1 := tProg_runs hq (0 : Fin 9) e he r0 hr0 S hS0
  set A1 := Function.update S (sv 3) (natSyms (c6T q e) ++ Sym.mark :: S (sv 3)) with hA1
  have a2 := dProg_runs e (c6T q e) o r0 (Sym.mark :: S (sv 3)) r3 A1 hr0 (hmk _) hr3 hT.2.le
    (by omega) (by simp [hA1, sv, hS0]) (by simp [hA1]) (by simp [hA1, sv, hS3])
  rw [show A1 (sv 16) = S (sv 16) by simp [hA1, sv]] at a2
  set A2 := Function.update A1 (sv 16) (natSyms (e - c6T q e - o) ++ Sym.mark :: S (sv 16))
    with hA2
  have a3 := jProg_runs e (e - c6T q e - o) r0 (Sym.mark :: S (sv 16)) A2 hr0 (hmk _) hd1 hde
    (by simp [hA2, hA1, sv, hS0]) (by simp [hA2])
  rw [show A2 (sv 18) = S (sv 18) by simp [hA2, hA1, sv]] at a3
  set A3 := Function.update A2 (sv 18)
    (natSyms (Nat.log (tripleM 100) (e - c6T q e - o)) ++ Sym.mark :: S (sv 18)) with hA3
  have a4 := pProg_runs hq (e - c6T q e - o) (Nat.log (tripleM 100) (e - c6T q e - o)) o G B
    (Sym.mark :: S (sv 16)) (Sym.mark :: S (sv 18)) r3 r1 r2 A3 (hmk _) (hmk _) hr3 hr1 hr2 hLd
    (by simp [hA3, hA2, sv]) (by simp [hA3]) (by simp [hA3, hA2, hA1, sv, hS3])
    (by simp [hA3, hA2, hA1, sv, hS1]) (by simp [hA3, hA2, hA1, sv, hS2])
  set A4 := pOut A3 q (e - c6T q e - o) (Nat.log (tripleM 100) (e - c6T q e - o)) o G B
    with hA4
  have a5 := rProg_runs hq e he r0 (Sym.mark :: S (sv 3)) A4 hr0 (hmk _)
    (by simp [hA4, pOut, hA3, hA2, hA1, sv, hS0]) (by simp [hA4, pOut, hA3, hA2, hA1, sv])
  rw [show A4 (sv 23) = S (sv 23) by simp [hA4, pOut, hA3, hA2, hA1, sv]] at a5
  set A5 := Function.update A4 (sv 23) (natSyms (c6Rp q e) ++ Sym.mark :: S (sv 23)) with hA5
  have o1 := runs_copyN (src := sv 18) (dst := .inl 4) (tmp := sv 7) (by decide) (by decide)
    (by decide) (Nat.log (tripleM 100) (e - c6T q e - o)) (Sym.mark :: S (sv 18)) A5 (hmk _)
    (by simp [hA5, hA4, pOut, hA3, sv])
  rw [show A5 (.inl 4) = r4 by simp [hA5, hA4, pOut, hA3, hA2, hA1, sv, hS4]] at o1
  set A6 := Function.update A5 (.inl 4) (natSyms (Nat.log (tripleM 100) (e - c6T q e - o)) ++ r4)
    with hA6
  have o2 := runs_copyN (src := sv 23) (dst := .inl 5) (tmp := sv 7) (by decide) (by decide)
    (by decide) (c6Rp q e) (Sym.mark :: S (sv 23)) A6 (hmk _) (by simp [hA6, hA5, sv])
  rw [show A6 (.inl 5) = r5 by simp [hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv, hS5]] at o2
  set A7 := Function.update A6 (.inl 5) (natSyms (c6Rp q e) ++ r5) with hA7
  have o3 := runs_copyN (src := sv 0) (dst := .inl 6) (tmp := sv 7) (by decide) (by decide)
    (by decide) (q ^ o) (Sym.mark :: S (sv 0)) A7 (hmk _)
    (by simp [hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv])
  rw [show A7 (.inl 6) = r6 by simp [hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv, hS6]] at o3
  set A8 := Function.update A7 (.inl 6) (natSyms (q ^ o) ++ r6) with hA8
  have o4 := runs_copyN (src := sv 2) (dst := .inl 7) (tmp := sv 7) (by decide) (by decide)
    (by decide) (G * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))
      * q ^ o) (Sym.mark :: S (sv 2)) A8 (hmk _)
    (by simp [hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv])
  rw [show A8 (.inl 7) = r7 by simp [hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv, hS7]] at o4
  set A9 := Function.update A8 (.inl 7) (natSyms (G * q ^ (e - c6T q e - o -
    tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) * q ^ o) ++ r7) with hA9
  have o5 := runs_copyN (src := sv 4) (dst := .inl 8) (tmp := sv 7) (by decide) (by decide)
    (by decide) (B * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)))
    (Sym.mark :: S (sv 4)) A9 (hmk _)
    (by simp [hA9, hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv])
  rw [show A9 (.inl 8) = r8 by
    simp [hA9, hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv, hS8]] at o5
  set A10 := Function.update A9 (.inl 8) (natSyms (B * q ^ (e - c6T q e - o -
    tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))) ++ r8) with hA10
  have c1 := runs_dropF (sv 23) (c6Rp q e) Sym.mark (S (sv 23)) A10 rfl
    (by simp [hA10, hA9, hA8, hA7, hA6, hA5, sv])
  set A11 := Function.update A10 (sv 23) (S (sv 23)) with hA11
  have c2 := runs_dropF (sv 4) (B * q ^ (e - c6T q e - o -
    tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o))) Sym.mark (S (sv 4)) A11 rfl
    (by simp [hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv])
  set A12 := Function.update A11 (sv 4) (S (sv 4)) with hA12
  have c3 := runs_dropF (sv 2) (G * q ^ (e - c6T q e - o -
    tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) * q ^ o) Sym.mark (S (sv 2)) A12 rfl
    (by simp [hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv])
  set A13 := Function.update A12 (sv 2) (S (sv 2)) with hA13
  have c4 := runs_dropF (sv 0) (q ^ o) Sym.mark (S (sv 0)) A13 rfl
    (by simp [hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1, sv])
  set A14 := Function.update A13 (sv 0) (S (sv 0)) with hA14
  have c5 := runs_dropF (sv 20) (e - c6T q e - o -
    tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) Sym.mark (S (sv 20)) A14 rfl
    (by simp [hA14, hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2, hA1,
      sv])
  set A15 := Function.update A14 (sv 20) (S (sv 20)) with hA15
  have c6 := runs_dropF (sv 19) (tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) Sym.mark
    (S (sv 19)) A15 rfl
    (by simp [hA15, hA14, hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, pOut, hA3, hA2,
      hA1, sv])
  set A16 := Function.update A15 (sv 19) (S (sv 19)) with hA16
  have c7 := runs_dropF (sv 18) (Nat.log (tripleM 100) (e - c6T q e - o)) Sym.mark (S (sv 18))
    A16 rfl (by simp [hA16, hA15, hA14, hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4,
      pOut, hA3, sv])
  set A17 := Function.update A16 (sv 18) (S (sv 18)) with hA17
  have c8 := runs_dropF (sv 16) (e - c6T q e - o) Sym.mark (S (sv 16)) A17 rfl
    (by simp [hA17, hA16, hA15, hA14, hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4,
      pOut, hA3, hA2, sv])
  set A18 := Function.update A17 (sv 16) (S (sv 16)) with hA18
  have c9 := runs_dropF (sv 3) (c6T q e) Sym.mark (S (sv 3)) A18 rfl
    (by simp [hA18, hA17, hA16, hA15, hA14, hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5,
      hA4, pOut, hA3, hA2, hA1, sv])
  have X := WP.W9comp.runs_seq a1 (WP.W9comp.runs_seq a2 (WP.W9comp.runs_seq a3
    (WP.W9comp.runs_seq a4 (WP.W9comp.runs_seq a5 (WP.W9comp.runs_seq
    (WP.W9comp.runs_seq o1 (WP.W9comp.runs_seq o2 (WP.W9comp.runs_seq o3
      (WP.W9comp.runs_seq o4 o5))))
    (WP.W9comp.runs_seq c1 (WP.W9comp.runs_seq c2 (WP.W9comp.runs_seq c3
    (WP.W9comp.runs_seq c4 (WP.W9comp.runs_seq c5 (WP.W9comp.runs_seq c6
    (WP.W9comp.runs_seq c7 (WP.W9comp.runs_seq c8 c9)))))))))))))
  have hG' : G * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) *
      q ^ o = c6PG q e G o := by unfold c6PG c6PL c6PJ; ring
  have hB' : B * q ^ (e - c6T q e - o - tripleM 100 ^ Nat.log (tripleM 100) (e - c6T q e - o)) =
      c6PB q e B o := by unfold c6PB c6PL c6PJ; ring
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ h => h)
    (le_trans (le_of_eq (by unfold dCost; ring)) (args_cost_le hq he ho))
  rw [← hG', ← hB']
  simp only [c6PJ]
  funext x
  rcases x with jj | jj <;> fin_cases jj <;>
    simp [hA18, hA17, hA16, hA15, hA14, hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4,
      pOut, hA3, hA2, hA1, sv, hS4, hS5, hS6, hS7, hS8]

end AppC.C6PcAux

open AppC.C6PcAux NatArith in
/-- **`C6PcArgsStmt q`, proved** (`q ≥ 2`): the program `AppC.C6PcAux.argsProg q`, scratch `PE`,
registers `NatArith.Reg`, constant `argsC q`. -/
theorem c6PcArgs_holds (q : ℕ) (hq : 2 ≤ q) : C6PcArgsStmt q := by
  refine ⟨argsC q, fun _ => ⟨PE, inferInstance, inferInstance, Reg, argsProg q, inferInstance,
    inferInstance, closed_argsProg q, ?_⟩⟩
  intro e G B o r0 r1 r2 r3 r4 r5 r6 r7 r8 S he _ _ ho hr0 hr1 hr2 hr3 _ _ _ _ _ hS0 hS1 hS2 hS3
    hS4 hS5 hS6 hS7 hS8
  exact args_runs hq e G B o he ho r0 r1 r2 r3 r4 r5 r6 r7 r8 S hr0 hr1 hr2 hr3 hS0 hS1 hS2 hS3
    hS4 hS5 hS6 hS7 hS8

end SubNLogN.Machine
