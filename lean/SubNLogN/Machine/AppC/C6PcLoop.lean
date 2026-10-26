/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6PcBase
import WP.W9b.Macros

/-!
# Lemma A.8 piece-loop kernels: comparison and saturated loops (`Machine/AppC/C6PcLoop.lean`)

Generic (any stack type `K`, registers `NatArith.Reg`) pieces of the level-E counter kernels:
* `runs_cmpN`: the compare register after `cmpN` is `ordOf a b`;
* `satLoop`: `n` saturated steps (an `nLoop`): compare `P` with the target on `x` and run `step`
  only while `P < x`; `runs_satLoop` (for a value sequence `f` with `f i < a ↔ i < J`, `J ≤ n`, the
  loop ends in the state after exactly `J` steps);
* `clogStep` (`P ← c·P`, count `+1`) and `runs_clogLoop` (the count becomes `Nat.clog c a`).

**Proved (no `sorry`).** (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts Computability

namespace AppC.C6PcAux

open NatArith

theorem ordOf_eq_lt_iff (a b : ℕ) : ordOf a b = .lt ↔ a < b := by
  unfold ordOf
  split_ifs with h1 h2 <;> simp [h1]

section Generic

variable {K : Type} [DecidableEq K]

theorem closed_cmpN' (x y t1 t2 : K) : (cmpN x y t1 t2).Closed :=
  WP.W9comp.closed_liftRegs _ (by
    simp [Prog.Closed, Prog.FreeBelow, cmpNum, cmpBody, pushC, pushR, popR, restoreR, moveBits,
      moveBitsBody, Prog.liftRegs, Lib.skip])

theorem runs_cmpN {x y t1 t2 : K} (h : [x, y, t1, t2].Nodup) (a b : ℕ) (rx ry : List Sym)
    (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S x = natSyms a ++ rx)
    (hy : S y = natSyms b ++ ry) :
    Runs (cmpN x y t1 t2) S S (fun r => r.2.2.2.2 = ordOf a b) (12 * bitLen a + 15) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨hxy, hx1, hx2⟩, ⟨hy1, hy2⟩, h12⟩ := h'
  have hord : cmpAll .eq (encodeNat a) (encodeNat b) = ordOf a b := by
    rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
      bitsVal_encodeNat]
  refine Runs.of_eval fun v => ?_
  have e := cmpNum_eval hxy hx1 hx2 hy1 hy2 h12 (NatArith.lC.get v) (encodeNat a) (encodeNat b)
    rx ry S hrx hry hx hy
  refine ⟨_, _, Eval.liftRegs NatArith.lC e v rfl, hord, ?_⟩
  simp only [bitLen]
  omega

/-- One saturated step: compare `P` with the target on `x`; run `step` iff `P < x`. -/
def satBody (P x t1 t2 : K) (step : Prog K (fun _ => Sym) Reg) : Prog K (fun _ => Sym) Reg :=
  .seq (cmpN P x t1 t2) (.ite (fun r => decide (r.2.2.2.2 = Ordering.lt)) step (.load id))

/-- The saturated loop: `n` saturated steps, `n` read from `ns`. -/
def satLoop (ns Kc t P x t1 t2 : K) (step : Prog K (fun _ => Sym) Reg) :
    Prog K (fun _ => Sym) Reg :=
  SubNLogN.Machine.K1.Rot.nLoop lW ns Kc t (satBody P x t1 t2 step)

theorem closed_satLoop (ns Kc t P x t1 t2 : K) {step : Prog K (fun _ => Sym) Reg}
    (hs : step.Closed) : (satLoop ns Kc t P x t1 t2 step).Closed :=
  SubNLogN.Machine.K1.Rot.closed_nLoop lW ns Kc t ⟨closed_cmpN' _ _ _ _, hs, trivial⟩

theorem runs_satLoop {ns Kc t P x t1 t2 : K} (hcmp : [P, x, t1, t2].Nodup) (hPK : P ≠ Kc)
    (hxK : x ≠ Kc) (hnK : ns ≠ Kc) (hnt : ns ≠ t) (hKt : Kc ≠ t)
    (step : Prog K (fun _ => Sym) Reg) (f : ℕ → ℕ) (a J n : ℕ) (hJ : ∀ i, f i < a ↔ i < J)
    (hJn : J ≤ n) (St : ℕ → K → List Sym) (rP rx rn : List Sym) (hrP : TermOK rP)
    (hrx : TermOK rx) (hrn : TermOK rn) (hP : ∀ i, i ≤ J → St i P = natSyms (f i) ++ rP)
    (hx : ∀ i, i ≤ J → St i x = natSyms a ++ rx) (hns : St 0 ns = natSyms n ++ rn)
    (hKc : St J Kc = St 0 Kc) (M : ℕ) (hM : ∀ i, i ≤ J → bitLen (f i) ≤ M)
    (Ts : ℕ → ℕ) (hTs : ∀ i, i < J → Ts i ≤ M)
    (hstep : ∀ i, i < J → ∀ v : List Sym, Runs step (Function.update (St i) Kc v)
      (Function.update (St (i + 1)) Kc v) (fun _ => True) (Ts i)) :
    Runs (satLoop ns Kc t P x t1 t2 step) (St 0) (St J) (fun _ => True)
      (n * (13 * M + 17) + 16 * n + 13 * bitLen n + 12) := by
  let Ta : ℕ → ℕ := fun j => 12 * bitLen (f (min j J)) + 15 + ((if j < J then Ts j else 1) + 1)
  have hbody : ∀ j, j < n → Runs (satBody P x t1 t2 step)
      (Function.update (St (min j J)) Kc (natSyms (n - (j + 1)) ++ Sym.mark :: St (min 0 J) Kc))
      (Function.update (St (min (j + 1) J)) Kc
        (natSyms (n - (j + 1)) ++ Sym.mark :: St (min 0 J) Kc)) (fun _ => True) (Ta j) := by
    intro j _
    show Runs _ _ _ _ (12 * bitLen (f (min j J)) + 15 + ((if j < J then Ts j else 1) + 1))
    generalize natSyms (n - (j + 1)) ++ Sym.mark :: St (min 0 J) Kc = v
    have hc := runs_cmpN hcmp (f (min j J)) a rP rx (Function.update (St (min j J)) Kc v) hrP hrx
      (by rw [Function.update_of_ne hPK]; exact hP _ (Nat.min_le_right _ _))
      (by rw [Function.update_of_ne hxK]; exact hx _ (Nat.min_le_right _ _))
    by_cases hj : j < J
    · have e1 : min j J = j := Nat.min_eq_left hj.le
      have e2 : min (j + 1) J = j + 1 := Nat.min_eq_left hj
      rw [e1] at hc
      rw [e1, e2, if_pos hj]
      exact WP.W9b.runs_ite_true (WP.W9b.runs_mono hc (fun r hr => by
        show decide (r.2.2.2.2 = Ordering.lt) = true
        rw [hr, decide_eq_true_iff, ordOf_eq_lt_iff]
        exact (hJ j).2 hj) le_rfl) (hstep j hj v)
    · have e1 : min j J = J := Nat.min_eq_right (by omega)
      have e2 : min (j + 1) J = J := Nat.min_eq_right (by omega)
      rw [e1] at hc
      rw [e1, e2, if_neg hj]
      exact WP.W9b.runs_ite_false (WP.W9b.runs_mono hc (fun r hr => by
        show decide (r.2.2.2.2 = Ordering.lt) = false
        rw [hr, decide_eq_false_iff_not, ordOf_eq_lt_iff]
        exact fun h => (lt_irrefl J) ((hJ J).1 h)) le_rfl) (NatArith.runs_loadId _)
  have hTa : ∀ j, j < n → Ta j ≤ 13 * M + 17 := by
    intro j _
    show 12 * bitLen (f (min j J)) + 15 + ((if j < J then Ts j else 1) + 1) ≤ 13 * M + 17
    have h1 := hM (min j J) (Nat.min_le_right _ _)
    split_ifs with hj
    · have := hTs j hj
      omega
    · omega
  have r := SubNLogN.Machine.K1.Rot.runs_nLoop lW hnK hnt hKt (satBody P x t1 t2 step)
    (fun j => St (min j J)) n rn hrn (by simpa using hns)
    (by simp only [Nat.min_eq_right hJn, Nat.zero_min]; exact hKc) Ta hbody
  have hsum := NatArith.sum_range_le (f := Ta) (M := 13 * M + 17) n hTa
  have r' := WP.W9comp.runs_mono r (fun _ h => h)
    (show ((List.range n).map Ta).sum + 16 * n + 13 * bitLen n + 12 ≤
      n * (13 * M + 17) + 16 * n + 13 * bitLen n + 12 by omega)
  simp only [Nat.zero_min, Nat.min_eq_right hJn] at r'
  exact r'


/-! ## The `clog` loop -/

/-- One step of the `clog` loop: `P ← c·P` (`mulConstN`), then `Kk ← Kk + 1` (`inc`). -/
def clogStep (P Kk Q Tdst A Bs Acc T ti : K) (c : ℕ) : Prog K (fun _ => Sym) Reg :=
  .seq (mulConstN P c Q Tdst A Bs Acc T) ((inc Kk ti).liftRegs lW)

theorem closed_clogStep (P Kk Q Tdst A Bs Acc T ti : K) (c : ℕ) :
    (clogStep P Kk Q Tdst A Bs Acc T ti c).Closed :=
  ⟨closed_mulConstN _ _ _ _ _ _ _ _, WP.W9comp.closed_liftRegs _ (by
    simp [Prog.Closed, Prog.FreeBelow, inc, scanLoop, scanBody, incFix, pushC,
      pushR, popR, restoreR, moveBits, moveBitsBody, Lib.skip])⟩

theorem clog_lt_iff {c a i : ℕ} (hc : 2 ≤ c) : c ^ i < a ↔ i < Nat.clog c a :=
  (Nat.lt_clog_iff_pow_lt (by omega)).symm

/-- The state of the `clog` loop after `i` steps. -/
def clogSt (S : K → List Sym) (P Kk : K) (c : ℕ) (rP rK : List Sym) (i : ℕ) : K → List Sym :=
  Function.update (Function.update S P (natSyms (c ^ i) ++ rP)) Kk (natSyms i ++ rK)

/-- Cost parameter of the `clog` loop. -/
def clogM (c a n : ℕ) : ℕ := 200 * (bitLen a + bitLen c + n + 2) ^ 2

theorem clog_pow_bitLen {c a i : ℕ} (hc : 2 ≤ c) (hi : i ≤ Nat.clog c a) :
    bitLen (c ^ i) ≤ bitLen a + bitLen c + 2 := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have := bitLen_le_self'' (c ^ 0)
    simp only [pow_zero] at this ⊢
    omega
  · have h1 : c ^ (i - 1) < a := (clog_lt_iff hc).2 (by omega)
    have h2 : c ^ i ≤ c * a := by
      calc c ^ i = c * c ^ (i - 1) := by rw [← pow_succ']; congr 1; omega
        _ ≤ c * a := Nat.mul_le_mul_left _ h1.le
    have h3 := NatArith.bitLen_mono'' h2
    have h4 := NatArith.bitLen_mul_le' c a
    omega

theorem runs_clogLoop {ns Kc t P x t1 t2 Kk Q Tdst A Bs Acc ti : K}
    (hcmp : [P, x, t1, t2].Nodup) (hmul : [P, Q, Tdst, A, Bs, Acc, t].Nodup) (hPK : P ≠ Kc)
    (hxK : x ≠ Kc) (hKkK : Kk ≠ Kc) (hKkP : Kk ≠ P) (hxKk : x ≠ Kk) (hKki : Kk ≠ ti)
    (hnK : ns ≠ Kc) (hnt : ns ≠ t) (hKt : Kc ≠ t)
    (c a n : ℕ) (hc : 2 ≤ c) (hcn : Nat.clog c a ≤ n) (rP rx rK rn : List Sym) (S : K → List Sym)
    (hrP : TermOK rP) (hrx : TermOK rx) (hrK : TermOK rK) (hrn : TermOK rn)
    (hP : S P = natSyms 1 ++ rP) (hK : S Kk = natSyms 0 ++ rK) (hx : S x = natSyms a ++ rx)
    (hns : S ns = natSyms n ++ rn) :
    Runs (satLoop ns Kc t P x t1 t2 (clogStep P Kk Q Tdst A Bs Acc t ti c)) S
      (clogSt S P Kk c rP rK (Nat.clog c a)) (fun _ => True)
      (n * (13 * clogM c a n + 17) + 16 * n + 13 * bitLen n + 12) := by
  have hPx : P ≠ x := fun h => by simp [h] at hcmp
  have hS0 : clogSt S P Kk c rP rK 0 = S := by
    rw [clogSt, pow_zero, ← hP, Function.update_eq_self, ← hK, Function.update_eq_self]
  have r := runs_satLoop hcmp hPK hxK hnK hnt hKt (clogStep P Kk Q Tdst A Bs Acc t ti c)
    (fun i => c ^ i) a (Nat.clog c a) n (fun i => clog_lt_iff hc) hcn (clogSt S P Kk c rP rK)
    rP rx rn hrP hrx hrn
    (fun i _ => by simp [clogSt, hKkP.symm])
    (fun i _ => by simp [clogSt, hxKk, hPx.symm, hx])
    (by rw [hS0]; exact hns)
    (by simp [clogSt, hPK.symm, hKkK.symm])
    (clogM c a n)
    (fun i hi => (clog_pow_bitLen hc hi).trans (by unfold clogM; nlinarith))
    (fun i => mulConstCost (c ^ i) c + (6 * bitLen i + 9))
    (fun i hi => by
      have hlt : c ^ i < a := (clog_lt_iff hc).2 hi
      have h1 := mulConstCost_le (c := c) (NatArith.bitLen_mono'' hlt.le)
      have h2 := NatArith.bitLen_mul_le' (c ^ i) c
      have h3 := NatArith.bitLen_mono'' hlt.le
      have h4 : bitLen i ≤ n := (bitLen_le_self'' i).trans (by omega)
      have h5 : (bitLen a + bitLen c + 2) ^ 2 ≤ (bitLen a + bitLen c + n + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have h6 : bitLen a + bitLen c + n + 2 ≤ (bitLen a + bitLen c + n + 2) ^ 2 :=
        Nat.le_self_pow (by norm_num) _
      unfold clogM
      omega)
    (fun i hi v => by
      have e1 := runs_mulConstN hmul c (c ^ i) rP
        (Function.update (clogSt S P Kk c rP rK i) Kc v) hrP (by simp [clogSt, hPK, hKkP.symm])
      have e2 := WP.W9b.runs_lift lW (WP.W9b.rs_inc hKki i rK
        (Function.update (Function.update (clogSt S P Kk c rP rK i) Kc v) P
          (natSyms (c ^ i * c) ++ rP)) hrK (by simp [clogSt, hKkK, hKkP]))
      refine WP.W9comp.runs_congr (WP.W9comp.runs_seq e1 e2) ?_
      funext k
      by_cases h1 : k = Kk
      · subst h1; simp [clogSt, hKkK, hKkP]
      · by_cases h2 : k = P
        · subst h2; simp [clogSt, hPK, hKkP.symm, pow_succ]
        · by_cases h3 : k = Kc
          · subst h3; simp [clogSt, hPK.symm, hKkK.symm]
          · simp [clogSt, Function.update_apply, h1, h2, h3])
  rwa [hS0] at r

/-! ## Register-preserving drops and sequencing -/

theorem dropF_eval_pres (k : K) (a : ℕ) (tt : Sym) (rest : List Sym) (S : K → List Sym)
    (ht : tt.isBit = false) (hS : S k = natSyms a ++ tt :: rest) (v : Reg) :
    Eval [] (dropF k) ⟨v, S⟩ ⟨(some tt, v.2), Function.update S k rest⟩ (2 * bitLen a + 2) :=
  Eval.liftRegs lW (SubNLogN.Machine.K1.dropBits_eval k v.1 (encodeNat a) tt rest S ht hS) v rfl

theorem runs_seq_pres {P L : Prog K (fun _ => Sym) Reg} {S1 S2 S3 : K → List Sym}
    {Q : Reg → Prop} {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q T1)
    (h2 : ∀ v : Reg, ∃ w t, Eval [] L ⟨v, S2⟩ ⟨(w, v.2), S3⟩ t ∧ t ≤ T2)
    (hQ : ∀ v w, Q v → Q (w, v.2)) : Runs (.seq P L) S1 S3 Q (T1 + T2) := by
  intro s hs
  obtain ⟨⟨var1, stk1⟩, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := h1 s hs
  change stk1 = S2 at hs1
  subst hs1
  obtain ⟨w, t, e2, ht⟩ := h2 var1
  exact ⟨⟨(w, var1.2), S3⟩, t1 + t, Eval.seq e1 e2, ⟨rfl, hQ var1 w hq1⟩, by omega⟩

end Generic

end AppC.C6PcAux

end SubNLogN.Machine
