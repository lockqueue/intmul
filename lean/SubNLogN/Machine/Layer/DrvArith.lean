/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamArith
import SubNLogN.Machine.Walsh.CubeHdrKit
import WP.Inst.W6a
import SubNLogN.Math.Networks.AppCLayerProc

/-!
# Layer driver: shared parameter arithmetic (`Machine/Layer/DrvArith.lean`)

**Scope (honest summary).** Generic machine programs (any stack type `K`, stacks given by an
injective map `st : Fin n → K`; register file `NatArith.Reg`) computing the integer parameters of
the layer procedure of Appendix A (`Math/Networks/AppCLayerProc.lean:91-100`), each with an exact `Runs`
specification (every stack other than the destination is restored; temporaries may hold arbitrary
content, a `mark` floor is put on them first and removed at the end) and an explicit cost. All
proved (no `sorry`), in the namespace `SubNLogN.Machine.Layer.DrvArith`.
* `runs_liftRegs'`: lifting a `Runs` fact through a register lens, keeping its register
  postcondition; `runs_cmpN`: the W3 comparison (`cmpNum`) as `NatArith.cmpN`, register
  postcondition `ordOf a b`.
* `runs_seq_loopN`: a counted loop (`n` iterations, uniform cost bound per iteration).
* `clogN b st`: `natSyms n` on `st 0` (restored) ↦ pushes `natSyms (Nat.clog b n)` on `st 1`
  (`1 < b` a constant; loop `p := 1; while p < n: p := p·b, k := k + 1`).
Shared with the piece-descriptor arithmetic (`DrvDescStmt`).
-/

namespace SubNLogN.Machine.Layer.DrvArith

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.NatArith

/-! ## 1. Lifting with a register postcondition; comparison -/

/-- A `Runs` fact lifted through a register lens, keeping the register postcondition. -/
theorem runs_liftRegs' {K σ τ : Type} [DecidableEq K] (l : Lens σ τ)
    {p : Prog K (fun _ => Sym) τ} {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ}
    (h : Runs p S S' Q T) : Runs (p.liftRegs l) S S' (fun r => Q (l.get r)) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨⟨v', stk'⟩, t, e, ⟨hs', hq⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  refine ⟨⟨l.set v v', stk'⟩, t, Eval.liftRegs l e v rfl, ⟨hs', ?_⟩, ht⟩
  show Q (l.get (l.set v v'))
  rw [l.get_set]
  exact hq

/-- **Comparison** (`NatArith.cmpN`, the W3 comparator `cmpNum`): both operands restored, the
compare register receives `ordOf a b`. -/
theorem runs_cmpN {K : Type} [DecidableEq K] {x y t1 t2 : K} (h : [x, y, t1, t2].Nodup)
    (a b : ℕ) (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (cmpN x y t1 t2) S S (fun r => r.2.2.2.2 = ordOf a b)
      (12 * min (bitLen a) (bitLen b) + 15) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨hxy, hx1, hx2⟩, ⟨hy1, hy2⟩, h12⟩ := h'
  have hc : Runs (cmpNum x y t1 t2) S S (fun c : CReg => c.2.2 = ordOf a b)
      (12 * min (bitLen a) (bitLen b) + 15) := by
    apply Runs.of_eval
    intro v
    refine ⟨_, _, cmpNum_eval hxy hx1 hx2 hy1 hy2 h12 v (encodeNat a) (encodeNat b) rx ry S hrx
      hry hx hy, ?_, le_rfl⟩
    show cmpAll .eq (encodeNat a) (encodeNat b) = ordOf a b
    rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
      bitsVal_encodeNat]
  exact runs_liftRegs' lC hc

/-! ## 2. Counted loops -/

theorem runs_loopN {K σ : Type} [DecidableEq K] {c : σ → Bool} {body : Prog K (fun _ => Sym) σ}
    (St : ℕ → K → List Sym) (Rg : ℕ → σ → Prop) (N B : ℕ)
    (hbody : ∀ i < N, Runs body (St i) (St (i + 1)) (Rg (i + 1)) B)
    (hcont : ∀ i < N, ∀ v, Rg i v → c v = true)
    (hstop : ∀ v, Rg N v → c v = false) :
    ∀ j i, i + j = N → ∀ v, Rg i v →
      ∃ v' t, Eval [] (.loop c body) ⟨v, St i⟩ ⟨v', St N⟩ t ∧ Rg N v' ∧ t ≤ j * (B + 1) + 1 := by
  intro j
  induction j with
  | zero =>
    intro i hi v hv
    have hiN : i = N := by omega
    subst hiN
    exact ⟨v, 1, Eval.loop_false (hstop v hv), hv, by omega⟩
  | succ j ih =>
    intro i hi v hv
    have hlt : i < N := by omega
    obtain ⟨⟨sv, sstk⟩, t, e, ⟨hs', hq⟩, ht⟩ := hbody i hlt ⟨v, St i⟩ rfl
    change sstk = St (i + 1) at hs'
    subst hs'
    obtain ⟨v'', t2, e2, hq2, ht2⟩ := ih (i + 1) (by omega) sv hq
    refine ⟨v'', t + t2 + 1, Eval.loop_true (hcont i hlt v hv) e e2, hq2, ?_⟩
    rw [Nat.succ_mul]
    omega

/-- **A counted loop after a set-up step**: `pre` reaches state `0` with register property
`Rg 0`; from state `i < N` the body reaches state `i + 1` (cost `≤ B`); the loop test is true at
`i < N` and false at `N`. -/
theorem runs_seq_loopN {K σ : Type} [DecidableEq K] {c : σ → Bool}
    {pre body : Prog K (fun _ => Sym) σ} {S0 : K → List Sym} {T0 : ℕ}
    (St : ℕ → K → List Sym) (Rg : ℕ → σ → Prop) (N B : ℕ)
    (hpre : Runs pre S0 (St 0) (Rg 0) T0)
    (hbody : ∀ i < N, Runs body (St i) (St (i + 1)) (Rg (i + 1)) B)
    (hcont : ∀ i < N, ∀ v, Rg i v → c v = true)
    (hstop : ∀ v, Rg N v → c v = false) :
    Runs (.seq pre (.loop c body)) S0 (St N) (Rg N) (T0 + (N * (B + 1) + 1)) := by
  intro s hs
  obtain ⟨⟨v0, s0⟩, t0, e0, ⟨hs0, hq0⟩, ht0⟩ := hpre s hs
  change s0 = St 0 at hs0
  subst hs0
  obtain ⟨v', t, e, hq, ht⟩ := runs_loopN St Rg N B hbody hcont hstop N 0 (by omega) v0 hq0
  exact ⟨⟨v', St N⟩, t0 + t, Eval.seq e0 e, ⟨rfl, hq⟩, by omega⟩

/-! ## 3. Ceiling logarithm `clogN` -/

/-- Loop test: the compare register says `<`. -/
def isLtR (r : Reg) : Bool := decide (r.2.2.2.2 = Ordering.lt)

section ClogProg

variable {K : Type}

/-- Loop body of `clogN`: `p := p·b`, `k := k + 1`, compare `p` with `n`. -/
def clogBody (b : ℕ) (st : Fin 12 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (mulConstN (st 2) b (st 6) (st 7) (st 8) (st 9) (st 10) (st 11))
    (.seq ((inc (st 3) (st 4)).liftRegs lW) (cmpN (st 2) (st 0) (st 4) (st 5)))

/-- Set-up of `clogN`: floors on `p` and `k`, `p := 1`, `k := 0`, compare `p` with `n`. -/
def clogPre (st : Fin 12 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark (st 2)) (.seq (pushNat (st 2) 1) (.seq (pushMark (st 3))
    (cmpN (st 2) (st 0) (st 4) (st 5))))

/-- **`clogN b st`**: `natSyms n` on `st 0` (restored) ↦ `natSyms (Nat.clog b n)` pushed on
`st 1`. Work stacks `st 2` (the power `p`), `st 3` (the count `k`); temporaries `st 4 … st 11`. -/
def clogN (b : ℕ) (st : Fin 12 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (.seq (clogPre st) (.loop isLtR (clogBody b st)))
    (.seq (copyN (st 3) (st 1) (st 4)) (.seq (dropF (st 3)) (dropF (st 2))))

theorem closed_cmpN' (x y t1 t2 : K) : (cmpN x y t1 t2).Closed := by
  unfold cmpN
  exact WP.W9comp.closed_liftRegs lC (by
    simp [Prog.Closed, Prog.FreeBelow, cmpNum, cmpBody, Prog.liftRegs, pushC, pushR, popR,
      restoreR, moveBits, moveBitsBody, skip])

theorem closed_incL (k t : K) : ((inc k t).liftRegs lW).Closed :=
  WP.W9comp.closed_liftRegs lW (by
    simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody, pushC, popR, restoreR,
      pushR, skip, moveBits, moveBitsBody])

theorem closed_clogN (b : ℕ) (st : Fin 12 → K) : (clogN b st).Closed := by
  refine WP.W9comp.closed_seq (WP.W9comp.closed_seq ?_ ?_) ?_
  · exact WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq (closed_pushNat _ _)
      (WP.W9comp.closed_seq (closed_pushMark _) (closed_cmpN' _ _ _ _)))
  · show (clogBody b st).FreeBelow 0
    exact WP.W9comp.closed_seq (closed_mulConstN _ _ _ _ _ _ _ _)
      (WP.W9comp.closed_seq (closed_incL _ _) (closed_cmpN' _ _ _ _))
  · exact WP.W9comp.closed_seq (closed_copyN _ _ _) (WP.W9comp.closed_seq (closed_dropF _)
      (closed_dropF _))

end ClogProg

/-- The cost bound of `clogN`. -/
def clogCost (b n : ℕ) : ℕ := 400 * (bitLen n + bitLen b + 2) ^ 3

/-- The loop states of `clogN`: `p = b^i` and `k = i` above their floors. -/
def clogSt {K : Type} [DecidableEq K] (S : K → List Sym) (st : Fin 12 → K) (b i : ℕ) :
    K → List Sym :=
  Function.update (Function.update S (st 2) (natSyms (b ^ i) ++ Sym.mark :: S (st 2))) (st 3)
    (natSyms i ++ Sym.mark :: S (st 3))

theorem upd2_upd2 {K : Type} [DecidableEq K] {a c : K} (_hac : a ≠ c) (S : K → List Sym)
    (x0 y0 x y : List Sym) :
    Function.update (Function.update (Function.update (Function.update S a x0) c y0) a x) c y =
      Function.update (Function.update S a x) c y := by
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

section ClogSpec

variable {K : Type} [DecidableEq K]

theorem clogSt_at0 {S : K → List Sym} {st : Fin 12 → K} (hst : Function.Injective st) (b i : ℕ) :
    clogSt S st b i (st 0) = S (st 0) := by
  rw [clogSt, Function.update_of_ne (hst.ne (by decide)), Function.update_of_ne (hst.ne (by decide))]

theorem clogSt_at2 {S : K → List Sym} {st : Fin 12 → K} (hst : Function.Injective st) (b i : ℕ) :
    clogSt S st b i (st 2) = natSyms (b ^ i) ++ Sym.mark :: S (st 2) := by
  rw [clogSt, Function.update_of_ne (hst.ne (by decide)), Function.update_self]

theorem clogSt_at3 {S : K → List Sym} (st : Fin 12 → K) (b i : ℕ) :
    clogSt S st b i (st 3) = natSyms i ++ Sym.mark :: S (st 3) := by
  rw [clogSt, Function.update_self]

/-- Bit length of the powers met by the loop: `b^i ≤ …` for `i ≤ clog b n`. -/
theorem bitLen_pow_le_of_le_clog {b n i : ℕ} (hb : 1 < b) (hi : i ≤ Nat.clog b n) :
    bitLen (b ^ i) ≤ bitLen b + bitLen n := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have h1 : bitLen 1 ≤ bitLen b := bitLen_mono'' (by omega)
    simpa using h1.trans (Nat.le_add_right _ _)
  · have hlt : b ^ (i - 1) < n := (Nat.lt_clog_iff_pow_lt hb).1 (by omega)
    have heq : b ^ i = b * b ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hle : b ^ i ≤ b * n := by
      rw [heq]
      exact Nat.mul_le_mul_left b hlt.le
    exact (bitLen_mono'' hle).trans (bitLen_mul_le' b n)

theorem clog_le_bitLen {b n : ℕ} (hb : 1 < b) : Nat.clog b n ≤ bitLen n := by
  apply Nat.clog_le_of_le_pow
  have h1 := lt_two_pow_bitLen n
  have h2 : 2 ^ bitLen n ≤ b ^ bitLen n := Nat.pow_le_pow_left (by omega) _
  omega

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n :=
  bitLen_le_of_lt' Nat.lt_two_pow_self

end ClogSpec

section ClogMain

variable {K : Type} [DecidableEq K]

/-- **`clogN`**: `natSyms n` on `st 0` (restored) ↦ `natSyms (Nat.clog b n)` pushed on `st 1`;
every other stack restored; cost `≤ clogCost b n`. -/
theorem runs_clogN {st : Fin 12 → K} (hst : Function.Injective st) {b : ℕ} (hb : 1 < b)
    (n : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hx : S (st 0) = natSyms n ++ rx) :
    Runs (clogN b st) S (Function.update S (st 1) (natSyms (Nat.clog b n) ++ S (st 1)))
      (fun _ => True) (clogCost b n) := by
  have hnd : ∀ l : List (Fin 12), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  have h12 : st 1 ≠ st 2 := hst.ne (by decide)
  have h13 : st 1 ≠ st 3 := hst.ne (by decide)
  have h14 : st 1 ≠ st 4 := hst.ne (by decide)
  have h23 : st 2 ≠ st 3 := hst.ne (by decide)
  have h34 : st 3 ≠ st 4 := hst.ne (by decide)
  set N := Nat.clog b n with hN
  set L := bitLen n + bitLen b with hL
  have hNL : N ≤ L := (clog_le_bitLen hb).trans (by omega)
  -- the set-up
  have hpre : Runs (clogPre st) S (clogSt S st b 0) (fun r => r.2.2.2.2 = ordOf (b ^ 0) n)
      (1 + ((bitLen 1 + 1) + (1 + (12 * min (bitLen 1) (bitLen n) + 15)))) := by
    have r1 := runs_pushMark (st 2) S
    have r2 := runs_pushNat (st 2) 1 (Function.update S (st 2) (Sym.mark :: S (st 2)))
    have r3 := runs_pushMark (st 3) (Function.update (Function.update S (st 2)
      (Sym.mark :: S (st 2))) (st 2) (natSyms 1 ++ Function.update S (st 2)
        (Sym.mark :: S (st 2)) (st 2)))
    have e3 : Function.update (Function.update (Function.update S (st 2) (Sym.mark :: S (st 2)))
        (st 2) (natSyms 1 ++ Function.update S (st 2) (Sym.mark :: S (st 2)) (st 2))) (st 3)
        (Sym.mark :: Function.update (Function.update S (st 2) (Sym.mark :: S (st 2))) (st 2)
          (natSyms 1 ++ Function.update S (st 2) (Sym.mark :: S (st 2)) (st 2)) (st 3)) =
        clogSt S st b 0 := by
      rw [clogSt, pow_zero, natSyms_zero, List.nil_append, Function.update_self,
        Function.update_idem, Function.update_of_ne h23.symm]
    have r4 := runs_cmpN (x := st 2) (y := st 0) (t1 := st 4) (t2 := st 5)
      (hnd [2, 0, 4, 5] (by decide)) 1 n (Sym.mark :: S (st 2)) rx (clogSt S st b 0)
      (termOK_mark _) hrx (by rw [clogSt_at2 hst, pow_zero]) (by rw [clogSt_at0 hst, hx])
    rw [pow_zero]
    exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq
      (WP.W9comp.runs_congr r3 e3) r4))
  -- one iteration
  have hbody : ∀ i < N, Runs (clogBody b st) (clogSt S st b i) (clogSt S st b (i + 1))
      (fun r => r.2.2.2.2 = ordOf (b ^ (i + 1)) n) (250 * (L + 1) ^ 2) := by
    intro i hi
    have m1 := runs_mulConstN (k := st 2) (Q := st 6) (Tdst := st 7) (A := st 8) (Bs := st 9)
      (Acc := st 10) (T := st 11) (hnd [2, 6, 7, 8, 9, 10, 11] (by decide)) b (b ^ i)
      (Sym.mark :: S (st 2)) (clogSt S st b i) (termOK_mark _) (clogSt_at2 hst b i)
    have hA1 : Function.update (clogSt S st b i) (st 2)
        (natSyms (b ^ i * b) ++ Sym.mark :: S (st 2)) (st 3) = natSyms i ++ Sym.mark :: S (st 3) := by
      rw [Function.update_of_ne h23.symm, clogSt_at3]
    have m2 := runs_liftRegs' lW (SubNLogN.Machine.WalshCubeAux.runs_inc (k := st 3) (t := st 4)
      h34 i (Sym.mark :: S (st 3)) _ (termOK_mark _) hA1)
    have e12 : Function.update (Function.update (clogSt S st b i) (st 2)
        (natSyms (b ^ i * b) ++ Sym.mark :: S (st 2))) (st 3)
        (natSyms (i + 1) ++ Sym.mark :: S (st 3)) = clogSt S st b (i + 1) := by
      rw [clogSt, clogSt, upd2_upd2 h23, ← pow_succ]
    have m3 := runs_cmpN (x := st 2) (y := st 0) (t1 := st 4) (t2 := st 5)
      (hnd [2, 0, 4, 5] (by decide)) (b ^ (i + 1)) n (Sym.mark :: S (st 2)) rx
      (clogSt S st b (i + 1)) (termOK_mark _) hrx (clogSt_at2 hst b (i + 1))
      (by rw [clogSt_at0 hst, hx])
    have hall := WP.W9comp.runs_seq m1 (WP.W9comp.runs_seq (WP.W9comp.runs_congr m2 e12) m3)
    refine WP.W9comp.runs_mono hall (fun _ h => h) ?_
    have h1 : bitLen (b ^ i) ≤ L := (bitLen_pow_le_of_le_clog hb hi.le).trans (by omega)
    have h2 : bitLen (b ^ i * b) ≤ L := by
      rw [← pow_succ]
      exact (bitLen_pow_le_of_le_clog hb hi).trans (by omega)
    have h3 : bitLen i ≤ L := (bitLen_le_self' i).trans (by omega)
    have h5 : min (bitLen (b ^ (i + 1))) (bitLen n) ≤ L := (min_le_right _ _).trans (by omega)
    have hm : (bitLen (b ^ i) + 1) * (bitLen (b ^ i) + bitLen b + 2) ≤ (L + 1) * (2 * L + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [mulConstCost, mulCost]
    nlinarith [hm, h1, h2, h3, h5]
  -- the loop test
  have hcont : ∀ i < N, ∀ v : Reg, v.2.2.2.2 = ordOf (b ^ i) n → isLtR v = true := by
    intro i hi v hv
    have hlt : b ^ i < n := (Nat.lt_clog_iff_pow_lt hb).1 hi
    simp [isLtR, hv, ordOf, hlt]
  have hstop : ∀ v : Reg, v.2.2.2.2 = ordOf (b ^ N) n → isLtR v = false := by
    intro v hv
    have hge : n ≤ b ^ N := Nat.le_pow_clog hb n
    have hnlt : ¬ b ^ N < n := by omega
    by_cases heq : b ^ N = n <;> simp [isLtR, hv, ordOf, hnlt, heq]
  have hloop := runs_seq_loopN (c := isLtR) (pre := clogPre st) (body := clogBody b st)
    (clogSt S st b) (fun i r => r.2.2.2.2 = ordOf (b ^ i) n) N (250 * (L + 1) ^ 2)
    hpre hbody hcont hstop
  -- the result, and the floors
  have hStN1 : clogSt S st b N (st 1) = S (st 1) := by
    rw [clogSt, Function.update_of_ne h13, Function.update_of_ne h12]
  have c1 := runs_copyN (src := st 3) (dst := st 1) (tmp := st 4) h13.symm h34 h14 N
    (Sym.mark :: S (st 3)) (clogSt S st b N) (termOK_mark _) (clogSt_at3 st b N)
  have c2 := runs_dropF (st 3) N Sym.mark (S (st 3)) (Function.update (clogSt S st b N) (st 1)
    (natSyms N ++ clogSt S st b N (st 1))) rfl
    (by rw [Function.update_of_ne h13.symm, clogSt_at3])
  have c3 := runs_dropF (st 2) (b ^ N) Sym.mark (S (st 2)) (Function.update (Function.update
    (clogSt S st b N) (st 1) (natSyms N ++ clogSt S st b N (st 1))) (st 3) (S (st 3))) rfl
    (by rw [Function.update_of_ne h23, Function.update_of_ne h12.symm, clogSt_at2 hst])
  have hall := WP.W9comp.runs_seq (WP.W9comp.runs_mono hloop (fun _ _ => trivial) le_rfl)
    (WP.W9comp.runs_seq c1 (WP.W9comp.runs_seq c2 c3))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · rw [hStN1]
    funext k
    simp only [clogSt, Function.update_apply]
    split_ifs <;> simp_all
  · have hb1 : bitLen 1 ≤ 1 := bitLen_le_of_lt' (by norm_num)
    have hbN : bitLen N ≤ L := (bitLen_le_self' N).trans hNL
    have hbpN : bitLen (b ^ N) ≤ L := (bitLen_pow_le_of_le_clog hb le_rfl).trans (by omega)
    have hmin : min (bitLen 1) (bitLen n) ≤ 1 := (min_le_left _ _).trans hb1
    have hNB : N * (250 * (L + 1) ^ 2 + 1) ≤ L * (250 * (L + 1) ^ 2 + 1) :=
      Nat.mul_le_mul_right _ hNL
    simp only [clogCost]
    rw [show bitLen n + bitLen b + 2 = L + 2 by omega]
    nlinarith [hNB, hb1, hbN, hbpN, hmin]

end ClogMain


/-! ## 4. Floored values and branches -/

section Floors

variable {K : Type} [DecidableEq K]

/-- The value `v` above a `mark` floor on stack `w`. -/
def fl (S : K → List Sym) (w : K) (v : ℕ) : K → List Sym :=
  Function.update S w (natSyms v ++ Sym.mark :: S w)

theorem fl_self (S : K → List Sym) (w : K) (v : ℕ) : fl S w v w = natSyms v ++ Sym.mark :: S w := by
  rw [fl, Function.update_self]

theorem fl_ne {S : K → List Sym} {w k : K} (h : k ≠ w) (v : ℕ) : fl S w v k = S k := by
  rw [fl, Function.update_of_ne h]

/-- **A floored push**: if `op` pushes `natSyms v` on `w` above the floor, then `pushMark w; op`
goes from `S` to `fl S w v`. -/
theorem runs_fl {op : Prog K (fun _ => Sym) Reg} {S : K → List Sym} {w : K} {v T : ℕ}
    (h : Runs op (Function.update S w (Sym.mark :: S w))
      (Function.update (Function.update S w (Sym.mark :: S w)) w
        (natSyms v ++ Sym.mark :: S w)) (fun _ => True) T) :
    Runs (.seq (pushMark w) op) S (fl S w v) (fun _ => True) (1 + T) := by
  have h0 := runs_pushMark w S
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq h0 h) ?_
  rw [Function.update_idem]
  rfl

/-- Removing the outermost floored value. -/
theorem runs_dropF_fl {S : K → List Sym} {w : K} {v : ℕ} :
    Runs (dropF w) (fl S w v) S (fun _ => True) (2 * bitLen v + 2) := by
  have h := runs_dropF w v Sym.mark (S w) (fl S w v) rfl (fl_self S w v)
  refine WP.W9comp.runs_congr h ?_
  rw [fl, Function.update_idem, Function.update_eq_self]

/-- A comparison followed by a branch whose test holds after the comparison. -/
theorem runs_seq_ite_true {σ : Type} {c : σ → Bool} {cmp p q : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T0 T1 : ℕ} (h0 : Runs cmp S S Q T0)
    (hc : ∀ v, Q v → c v = true) (h1 : Runs p S S' (fun _ => True) T1) :
    Runs (.seq cmp (.ite c p q)) S S' (fun _ => True) (T0 + (T1 + 1)) := by
  intro s hs
  obtain ⟨⟨v0, s0⟩, t0, e0, ⟨hs0, hq0⟩, ht0⟩ := h0 s hs
  change s0 = S at hs0
  subst hs0
  obtain ⟨⟨v1, s1⟩, t1, e1, ⟨hs1, -⟩, ht1⟩ := h1 ⟨v0, s0⟩ rfl
  exact ⟨⟨v1, s1⟩, t0 + (t1 + 1), Eval.seq e0 (Eval.ite_true (hc v0 hq0) e1), ⟨hs1, trivial⟩,
    by omega⟩

theorem runs_seq_ite_false {σ : Type} {c : σ → Bool} {cmp p q : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T0 T1 : ℕ} (h0 : Runs cmp S S Q T0)
    (hc : ∀ v, Q v → c v = false) (h1 : Runs q S S' (fun _ => True) T1) :
    Runs (.seq cmp (.ite c p q)) S S' (fun _ => True) (T0 + (T1 + 1)) := by
  intro s hs
  obtain ⟨⟨v0, s0⟩, t0, e0, ⟨hs0, hq0⟩, ht0⟩ := h0 s hs
  change s0 = S at hs0
  subst hs0
  obtain ⟨⟨v1, s1⟩, t1, e1, ⟨hs1, -⟩, ht1⟩ := h1 ⟨v0, s0⟩ rfl
  exact ⟨⟨v1, s1⟩, t0 + (t1 + 1), Eval.seq e0 (Eval.ite_false (hc v0 hq0) e1), ⟨hs1, trivial⟩,
    by omega⟩

end Floors

/-! ## 5. Moving a floored value; dropping an inner layer -/

section Xfer

variable {K : Type}

/-- Move the floored value of `src` onto `dst` (natural order), consuming the floor of `src`;
`tmp` gets a floor that is consumed as well. -/
def xferN (src dst tmp : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark tmp) (.seq ((moveBits src tmp).liftRegs lW) ((moveBits tmp dst).liftRegs lW))

theorem closed_xferN (src dst tmp : K) : (xferN src dst tmp).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
    (WP.W9comp.closed_liftRegs lW (by simp [Prog.Closed, Prog.FreeBelow, moveBits, moveBitsBody,
      pushR, popR]))
    (WP.W9comp.closed_liftRegs lW (by simp [Prog.Closed, Prog.FreeBelow, moveBits, moveBitsBody,
      pushR, popR])))

variable [DecidableEq K]

/-- **`xferN`**: `src = natSyms v ++ mark :: J` becomes `J`; `dst` receives `natSyms v`. -/
theorem runs_xferN {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (v : ℕ) (J : List Sym) (S : K → List Sym) (hS : S src = natSyms v ++ Sym.mark :: J) :
    Runs (xferN src dst tmp) S (Function.update (Function.update S src J) dst
      (natSyms v ++ S dst)) (fun _ => True) (6 * bitLen v + 5) := by
  have r0 := runs_pushMark tmp S
  have r1 := runs_liftRegs' lW (Q := fun _ => True) (Runs.of_eval fun w =>
    ⟨_, _, moveBits_eval hst [] w (encodeNat v) (Sym.mark :: J)
      (Function.update S tmp (Sym.mark :: S tmp)) (termOK_mark _)
      (by rw [Function.update_of_ne hst]; exact hS), trivial, le_rfl⟩)
  have hT : Function.update (Function.update (Function.update S tmp (Sym.mark :: S tmp)) src
      (Sym.mark :: J).tail) tmp ((encodeNat v).reverse.map Sym.bit ++
        Function.update S tmp (Sym.mark :: S tmp) tmp) tmp =
      (encodeNat v).reverse.map Sym.bit ++ (Sym.mark :: S tmp) := by
    rw [Function.update_self, Function.update_self]
  have r2 := runs_liftRegs' lW (Q := fun _ => True) (Runs.of_eval fun w =>
    ⟨_, _, moveBits_eval hdt.symm [] w (encodeNat v).reverse (Sym.mark :: S tmp) _
      (termOK_mark _) hT, trivial, le_rfl⟩)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r0
    (WP.W9comp.runs_seq r1 r2)) ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply, List.tail_cons, List.reverse_reverse]
    split_ifs <;> simp_all [natSyms]
  · simp only [List.length_reverse, bitLen]
    omega

/-- Dropping (restoring) a stack under an update at another stack. -/
theorem upd_drop_under {a b : K} (hab : a ≠ b) (S : K → List Sym) (X Y : List Sym) :
    Function.update (Function.update (Function.update S a X) b Y) a (S a) =
      Function.update S b Y := by
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Xfer

/-! ## 6. `q₀ = ⌈lg W_c⌉·⌈log_m 2d⌉` -/

section Q0

open SubNLogN.Math.Networks

variable {K : Type}

/-- The `clogN` stacks inside `q0N`. -/
def q0ClogMap : Fin 12 → Fin 16 := ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- **`q0N st`**: `natSyms d` on `st 0` (restored) ↦ pushes `natSyms (q0Of d)` on `st 1`
(`st 2`, `st 3` floored work stacks, `st 4 … st 13` temporaries). -/
noncomputable def q0N (st : Fin 16 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (.seq (pushMark (st 2)) (.seq (copyN (st 0) (st 2) (st 6)) (dblN (st 2))))
  (.seq (.seq (pushMark (st 3)) (clogN mH (st ∘ q0ClogMap)))
  (.seq (dropF (st 2))
  (.seq (mulConstN (st 3) (Nat.clog 2 Wc) (st 8) (st 9) (st 10) (st 11) (st 12) (st 13))
  (xferN (st 3) (st 1) (st 6)))))

theorem closed_q0N (st : Fin 16 → K) : (q0N st).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
    (closed_copyN _ _ _) (closed_dblN _)))
  (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_clogN _ _))
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq
    (closed_mulConstN _ _ _ _ _ _ _ _) (closed_xferN _ _ _))))

/-- The cost of `q0N`. -/
noncomputable def q0Cost (d : ℕ) : ℕ :=
  (1 + ((7 * bitLen d + 7) + 3)) + ((1 + clogCost mH (d + d)) + ((2 * bitLen (d + d) + 2) +
    (mulConstCost (Nat.clog mH (d + d)) (Nat.clog 2 Wc) +
      (6 * bitLen (Nat.clog mH (d + d) * Nat.clog 2 Wc) + 5))))

variable [DecidableEq K]

/-- **`q0N`**: pushes `natSyms (q0Of d)` on `st 1`; every other stack restored. -/
theorem runs_q0N {st : Fin 16 → K} (hst : Function.Injective st) (d : ℕ) (rx : List Sym)
    (S : K → List Sym) (hrx : TermOK rx) (hx : S (st 0) = natSyms d ++ rx) :
    Runs (q0N st) S (Function.update S (st 1) (natSyms (q0Of d) ++ S (st 1))) (fun _ => True)
      (q0Cost d) := by
  have h02 : st 0 ≠ st 2 := hst.ne (by decide)
  have h06 : st 0 ≠ st 6 := hst.ne (by decide)
  have h13 : st 1 ≠ st 3 := hst.ne (by decide)
  have h16 : st 1 ≠ st 6 := hst.ne (by decide)
  have h23 : st 2 ≠ st 3 := hst.ne (by decide)
  have h26 : st 2 ≠ st 6 := hst.ne (by decide)
  have h36 : st 3 ≠ st 6 := hst.ne (by decide)
  have hnd : ∀ l : List (Fin 16), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  -- 1. `2d` above a floor on `st 2`
  have r1 : Runs (.seq (pushMark (st 2)) (.seq (copyN (st 0) (st 2) (st 6)) (dblN (st 2)))) S
      (fl S (st 2) (d + d)) (fun _ => True) (1 + ((7 * bitLen d + 7) + 3)) := by
    apply runs_fl
    have c1 := runs_copyN h02 h06 h26 d rx (Function.update S (st 2) (Sym.mark :: S (st 2))) hrx
      (by rw [Function.update_of_ne h02]; exact hx)
    have c2 := runs_dblN (st 2) d (Sym.mark :: S (st 2))
      (Function.update (Function.update S (st 2) (Sym.mark :: S (st 2))) (st 2)
        (natSyms d ++ Function.update S (st 2) (Sym.mark :: S (st 2)) (st 2))) (termOK_mark _)
      (by rw [Function.update_self, Function.update_self])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem]
  -- 2. `clog_m (2d)` above a floor on `st 3`
  have r2 : Runs (.seq (pushMark (st 3)) (clogN mH (st ∘ q0ClogMap))) (fl S (st 2) (d + d))
      (fl (fl S (st 2) (d + d)) (st 3) (Nat.clog mH (d + d))) (fun _ => True)
      (1 + clogCost mH (d + d)) := by
    apply runs_fl
    have hinj : Function.Injective (st ∘ q0ClogMap) := hst.comp (by decide)
    have c := runs_clogN hinj (b := mH) (by norm_num) (d + d) (Sym.mark :: S (st 2))
      (Function.update (fl S (st 2) (d + d)) (st 3) (Sym.mark :: fl S (st 2) (d + d) (st 3)))
      (termOK_mark _) (by
        show Function.update (fl S (st 2) (d + d)) (st 3) _ (st 2) = _
        rw [Function.update_of_ne h23, fl_self])
    rw [show (st ∘ q0ClogMap) 1 = st 3 from rfl, Function.update_self] at c
    exact c
  -- 3. drop `2d`
  have r3 : Runs (dropF (st 2)) (fl (fl S (st 2) (d + d)) (st 3) (Nat.clog mH (d + d)))
      (fl S (st 3) (Nat.clog mH (d + d))) (fun _ => True) (2 * bitLen (d + d) + 2) := by
    have c := runs_dropF (st 2) (d + d) Sym.mark (S (st 2))
      (fl (fl S (st 2) (d + d)) (st 3) (Nat.clog mH (d + d))) rfl
      (by rw [fl_ne h23, fl_self])
    refine WP.W9comp.runs_congr c ?_
    funext k
    simp only [fl, Function.update_apply]
    split_ifs <;> simp_all
  -- 4. multiply by `⌈lg W_c⌉`
  have r4 : Runs (mulConstN (st 3) (Nat.clog 2 Wc) (st 8) (st 9) (st 10) (st 11) (st 12) (st 13))
      (fl S (st 3) (Nat.clog mH (d + d))) (fl S (st 3) (Nat.clog mH (d + d) * Nat.clog 2 Wc))
      (fun _ => True) (mulConstCost (Nat.clog mH (d + d)) (Nat.clog 2 Wc)) := by
    have c := runs_mulConstN (k := st 3) (Q := st 8) (Tdst := st 9) (A := st 10) (Bs := st 11)
      (Acc := st 12) (T := st 13) (hnd [3, 8, 9, 10, 11, 12, 13] (by decide)) (Nat.clog 2 Wc)
      (Nat.clog mH (d + d)) (Sym.mark :: S (st 3)) (fl S (st 3) (Nat.clog mH (d + d)))
      (termOK_mark _) (fl_self _ _ _)
    refine WP.W9comp.runs_congr c ?_
    rw [fl, fl, Function.update_idem]
  -- 5. move the result onto `st 1`
  have r5 := runs_xferN h13.symm h36 h16 (Nat.clog mH (d + d) * Nat.clog 2 Wc) (S (st 3))
    (fl S (st 3) (Nat.clog mH (d + d) * Nat.clog 2 Wc)) (fl_self _ _ _)
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 r5)))
  refine WP.W9comp.runs_congr hall ?_
  rw [fl_ne h13, fl, Function.update_idem, Function.update_eq_self, q0Of, two_mul, mul_comm]

end Q0


/-! ## 7. Long division and decrement -/

/-- Register file with the long-division registers. -/
abbrev Reg2 : Type := Reg × WP.W6a.DReg WP.Inst.subNat.R

/-- Lens to the library registers. -/
def lN : Lens Reg2 Reg := Lens.fst _ _

/-- Lens to the long-division registers. -/
def lD : Lens Reg2 (WP.W6a.DReg WP.Inst.subNat.R) := Lens.snd _ _

section Div

variable {K : Type}

/-- The stacks of the long division as `Fin 7`. -/
def divLoc : Loc 4 3 → Fin 7 := fun x => finSumFinEquiv x

theorem divLoc_injective : Function.Injective divLoc := fun _ _ h => finSumFinEquiv.injective h

/-- **Long division** (the proved W6a divider over the W3 subtractor): stacks `dst 0 = a`,
`dst 1 = b` (restored), `dst 2 += a / b`, `dst 3 += a % b`, scratch `dst 4 … dst 6`. -/
def divN (dst : Fin 7 → K) : Prog K (fun _ => Sym) Reg2 :=
  callInj (dst ∘ divLoc) lD WP.Inst.divModNat.prog

theorem closed_divN (dst : Fin 7 → K) : (divN dst).Closed :=
  closed_callInj _ _ WP.Inst.divModNat.closed

/-- Decrement, lifted to the library registers. -/
def decL (k t : K) : Prog K (fun _ => Sym) Reg := (dec k t).liftRegs lW

theorem closed_decL (k t : K) : (decL k t).Closed :=
  WP.W9comp.closed_liftRegs lW (by
    simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, scanBody, pushC, popR, peekR,
      pushR, skip, moveBits, moveBitsBody])

variable [DecidableEq K]

theorem runs_divN {dst : Fin 7 → K} (hd : Function.Injective dst) (a b : ℕ) (hb : 0 < b)
    (ra rb : List Sym) (S : K → List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hA : S (dst 0) = natSyms a ++ ra) (hB : S (dst 1) = natSyms b ++ rb) :
    Runs (divN dst) S (Function.update (Function.update S (dst 2) (natSyms (a / b) ++ S (dst 2)))
      (dst 3) (natSyms (a % b) ++ S (dst 3))) (fun _ => True)
      ((2 * 20 + 70) * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) := by
  have hι : Function.Injective (dst ∘ divLoc) := hd.comp divLoc_injective
  have hP := WP.W6a.divModProg_spec (by decide) WP.Inst.subNat.subSpec a b ra rb
    (S ∘ (dst ∘ divLoc)) hb hra hrb hA hB
  have k2 : dst 2 = (dst ∘ divLoc) WP.W6a.sQ := rfl
  have k3 : dst 3 = (dst ∘ divLoc) WP.W6a.sR := rfl
  refine runs_callInj (Q := fun _ => True) hι lD ?_ ?_
  · rw [k2, k3, Function.update_comp_eq_of_injective _ hι,
      Function.update_comp_eq_of_injective _ hι]
    exact hP
  · intro k hk
    rw [Function.update_of_ne (show k ≠ dst 3 from fun h => hk WP.W6a.sR h.symm),
      Function.update_of_ne (show k ≠ dst 2 from fun h => hk WP.W6a.sQ h.symm)]

theorem runs_decL {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (n + 1) ++ rest) :
    Runs (decL k t) S (Function.update S k (natSyms n ++ rest)) (fun _ => True)
      (6 * bitLen (n + 1) + 8) :=
  SubNLogN.Machine.K1.runs_liftRegs_of_eval lW fun v =>
    ⟨_, _, dec_eval hkt [] v n rest S hrest hS, by
      have := zerosLead_le_length (encodeNat (n + 1))
      simp only [bitLen]
      omega⟩

end Div

/-! ## 8. `padR d K` (and `2^{q₀K}`) -/

section PadR

open SubNLogN.Math.Networks

variable {K : Type}

/-- The `clogN` stacks for `k₀ = ⌈log_m d⌉` inside `padRN`. -/
def padK0Map : Fin 12 → Fin 32 := ![0, 4, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]

/-- The `q0N` stacks inside `padRN`. -/
def padQ0Map : Fin 16 → Fin 32 := ![0, 6, 24, 25, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 29, 30]

/-- The division stacks inside `padRN` (`num`, `M`, quotient, remainder, scratch). -/
def padDivMap : Fin 7 → Fin 32 := ![9, 5, 10, 11, 26, 27, 28]

/-- `padRN`, first part: floored `k₀`, `M = W_c^{k₀}`, `q₀`, `q₀K`, `X = 2^{q₀K}`, `X + M − 1`,
and the floors of the quotient and the remainder. -/
noncomputable def padPartA (st : Fin 32 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (.seq (pushMark (st 4)) (clogN mH (st ∘ padK0Map)))
  (.seq (.seq (pushMark (st 5)) (.seq (pushNat (st 5) 1)
      (powMulN (st 5) Wc (st 4) (st 23) (st 14) (st 17) (st 18) (st 19) (st 20) (st 21))))
  (.seq (.seq (pushMark (st 6)) (q0N (st ∘ padQ0Map)))
  (.seq (.seq (pushMark (st 7)) (mulN (st 6) (st 1) (st 7) (st 19) (st 20) (st 21) (st 22)))
  (.seq (.seq (pushMark (st 8)) (.seq (pushNat (st 8) 1)
      (powMulN (st 8) 2 (st 7) (st 23) (st 14) (st 17) (st 18) (st 19) (st 20) (st 21))))
  (.seq (.seq (pushMark (st 9)) (.seq (addN (st 8) (st 5) (st 9) (st 14) (st 15) (st 16))
      (decL (st 9) (st 14))))
  (.seq (pushMark (st 10)) (pushMark (st 11))))))))

/-- `padRN`, last part: `padR = M·⌈X/M⌉` onto `st 2`, `X` onto `st 3`, drop the work stacks. -/
def padPartB (st : Fin 32 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (mulN (st 5) (st 10) (st 2) (st 19) (st 20) (st 21) (st 22))
  (.seq (copyN (st 8) (st 3) (st 14))
  (.seq (dropF (st 11)) (.seq (dropF (st 10)) (.seq (dropF (st 9)) (.seq (dropF (st 8))
  (.seq (dropF (st 7)) (.seq (dropF (st 6)) (.seq (dropF (st 5)) (dropF (st 4))))))))))

/-- **`padRN st`**: `natSyms d` on `st 0`, `natSyms K` on `st 1` (restored) ↦ pushes
`natSyms (padR d K)` on `st 2` and `natSyms (2^{q₀K})` on `st 3`; `st 4 … st 30` work stacks and
temporaries (restored). -/
noncomputable def padRN (st : Fin 32 → K) : Prog K (fun _ => Sym) Reg2 :=
  .seq ((padPartA st).liftRegs lN) (.seq (divN (st ∘ padDivMap)) ((padPartB st).liftRegs lN))

theorem closed_padRN (st : Fin 32 → K) : (padRN st).Closed := by
  refine WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN ?_)
    (WP.W9comp.closed_seq (closed_divN _) (WP.W9comp.closed_liftRegs lN ?_))
  · exact WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_clogN _ _))
      (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
        (closed_pushNat _ _) (closed_powMulN _ _ _ _ _ _ _ _ _ _)))
      (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_q0N _))
      (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_mulN _ _ _ _ _ _ _))
      (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
        (closed_pushNat _ _) (closed_powMulN _ _ _ _ _ _ _ _ _ _)))
      (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
        (closed_addN _ _ _ _ _ _) (closed_decL _ _)))
      (WP.W9comp.closed_seq (closed_pushMark _) (closed_pushMark _)))))))
  · exact WP.W9comp.closed_seq (closed_mulN _ _ _ _ _ _ _) (WP.W9comp.closed_seq
      (closed_copyN _ _ _) (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq
      (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
      (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
      (WP.W9comp.closed_seq (closed_dropF _) (closed_dropF _)))))))))

end PadR

section PadRSpec

open SubNLogN.Math.Networks

variable {K : Type} [DecidableEq K]

/-- The cost of `padRN` (`M = W_c^{k₀}`, `X = 2^{q₀K}`, `num = X + M − 1`). -/
noncomputable def padRCost (d K : ℕ) : ℕ :=
  (1 + clogCost mH d) + (1 + ((bitLen 1 + 1) + powCost Wc 1 (Nat.clog mH d))) +
  (1 + q0Cost d) + (1 + mulCost (q0Of d) K) +
  (1 + ((bitLen 1 + 1) + powCost 2 1 (q0Of d * K))) +
  (1 + (20 * (bitLen (2 ^ (q0Of d * K)) + bitLen (Wc ^ Nat.clog mH d) + 1) +
    (6 * bitLen (2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1 + 1) + 8))) + (1 + 1) +
  (2 * 20 + 70) * (bitLen (2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1) *
    bitLen (Wc ^ Nat.clog mH d) + bitLen (2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1) +
    bitLen (Wc ^ Nat.clog mH d) + 1) +
  mulCost (Wc ^ Nat.clog mH d) ((2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1) / Wc ^ Nat.clog mH d) +
  (7 * bitLen (2 ^ (q0Of d * K)) + 7) +
  (2 * bitLen ((2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1) % Wc ^ Nat.clog mH d) + 2) +
  (2 * bitLen ((2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1) / Wc ^ Nat.clog mH d) + 2) +
  (2 * bitLen (2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1) + 2) +
  (2 * bitLen (2 ^ (q0Of d * K)) + 2) + (2 * bitLen (q0Of d * K) + 2) + (2 * bitLen (q0Of d) + 2) +
  (2 * bitLen (Wc ^ Nat.clog mH d) + 2) + (2 * bitLen (Nat.clog mH d) + 2)

theorem padR_eq (d K : ℕ) : padR d K = Wc ^ Nat.clog mH d *
    ((2 ^ (q0Of d * K) + Wc ^ Nat.clog mH d - 1) / Wc ^ Nat.clog mH d) := rfl

/-- **`padRN`**: pushes `natSyms (padR d K)` on `st 2` and `natSyms (2^{q₀K})` on `st 3`; every
other stack restored. -/
theorem runs_padRN {st : Fin 32 → K} (hst : Function.Injective st) (d Kv : ℕ)
    (rd rK : List Sym) (S : K → List Sym) (hrd : TermOK rd) (hrK : TermOK rK)
    (hd : S (st 0) = natSyms d ++ rd) (hK : S (st 1) = natSyms Kv ++ rK) :
    Runs (padRN st) S (Function.update (Function.update S (st 2) (natSyms (padR d Kv) ++ S (st 2)))
      (st 3) (natSyms (2 ^ (q0Of d * Kv)) ++ S (st 3))) (fun _ => True) (padRCost d Kv) := by
  have hnd : ∀ l : List (Fin 32), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  have hM0 : 0 < Wc ^ Nat.clog mH d := pow_pos Wc_pos _
  have hX0 : 1 ≤ 2 ^ (q0Of d * Kv) := Nat.one_le_two_pow
  -- the states of the first part
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (st 4) (Nat.clog mH d) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ T, T = fl S1 (st 5) (Wc ^ Nat.clog mH d) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ T, T = fl S2 (st 6) (q0Of d) := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ T, T = fl S3 (st 7) (q0Of d * Kv) := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ T, T = fl S4 (st 8) (2 ^ (q0Of d * Kv)) := ⟨_, rfl⟩
  obtain ⟨S6, hS6⟩ : ∃ T, T = fl S5 (st 9) (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) :=
    ⟨_, rfl⟩
  obtain ⟨S7, hS7⟩ : ∃ T, T = Function.update (Function.update S6 (st 10)
      (Sym.mark :: S (st 10))) (st 11) (Sym.mark :: S (st 11)) := ⟨_, rfl⟩
  -- step 1: `k₀`
  have r1 : Runs (.seq (pushMark (st 4)) (clogN mH (st ∘ padK0Map))) S S1 (fun _ => True)
      (1 + clogCost mH d) := by
    rw [hS1]
    apply runs_fl
    have c := runs_clogN (hst.comp (by decide : Function.Injective padK0Map)) (b := mH)
      (by norm_num) d rd (Function.update S (st 4) (Sym.mark :: S (st 4))) hrd
      (by rw [show (st ∘ padK0Map) 0 = st 0 from rfl, Function.update_of_ne (hst.ne (by decide)), hd])
    rw [show (st ∘ padK0Map) 1 = st 4 from rfl, Function.update_self] at c
    exact c
  -- step 2: `M`
  have r2 : Runs (.seq (pushMark (st 5)) (.seq (pushNat (st 5) 1)
      (powMulN (st 5) Wc (st 4) (st 23) (st 14) (st 17) (st 18) (st 19) (st 20) (st 21)))) S1 S2
      (fun _ => True) (1 + ((bitLen 1 + 1) + powCost Wc 1 (Nat.clog mH d))) := by
    rw [hS2]
    apply runs_fl
    have c1 := runs_pushNat (st 5) 1 (Function.update S1 (st 5) (Sym.mark :: S1 (st 5)))
    have c2 := runs_powMulN (k := st 5) (ns := st 4) (Kc := st 23) (t := st 14) (Q := st 17)
      (Tdst := st 18) (A := st 19) (Bs := st 20) (Acc := st 21)
      (hnd [5, 4, 23, 14, 17, 18, 19, 20, 21] (by decide)) Wc Wc_pos 1 (Nat.clog mH d)
      (Sym.mark :: S1 (st 5)) (Sym.mark :: S (st 4))
      (Function.update (Function.update S1 (st 5) (Sym.mark :: S1 (st 5))) (st 5)
        (natSyms 1 ++ Function.update S1 (st 5) (Sym.mark :: S1 (st 5)) (st 5)))
      (termOK_mark _) (termOK_mark _)
      (by rw [Function.update_self, Function.update_self])
      (by simp +decide only [hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem, one_mul]
  -- step 3: `q₀`
  have r3 : Runs (.seq (pushMark (st 6)) (q0N (st ∘ padQ0Map))) S2 S3 (fun _ => True)
      (1 + q0Cost d) := by
    rw [hS3]
    apply runs_fl
    have c := runs_q0N (hst.comp (by decide : Function.Injective padQ0Map)) d rd
      (Function.update S2 (st 6) (Sym.mark :: S2 (st 6))) hrd
      (by rw [show (st ∘ padQ0Map) 0 = st 0 from rfl]
          simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
          exact hd)
    rw [show (st ∘ padQ0Map) 1 = st 6 from rfl, Function.update_self] at c
    exact c
  -- step 4: `q₀K`
  have r4 : Runs (.seq (pushMark (st 7)) (mulN (st 6) (st 1) (st 7) (st 19) (st 20) (st 21)
      (st 22))) S3 S4 (fun _ => True) (1 + mulCost (q0Of d) Kv) := by
    rw [hS4]
    apply runs_fl
    have c := runs_mulN (x := st 6) (y := st 1) (z := st 7) (A := st 19) (Bs := st 20)
      (Acc := st 21) (T := st 22) (hnd [6, 1, 7, 19, 20, 21, 22] (by decide)) (q0Of d) Kv
      (Sym.mark :: S (st 6)) rK (Function.update S3 (st 7) (Sym.mark :: S3 (st 7)))
      (termOK_mark _) hrK
      (by simp +decide only [hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
      (by simp +decide only [hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false]; exact hK)
    rw [Function.update_self] at c
    exact c
  -- step 5: `X = 2^{q₀K}`
  have r5 : Runs (.seq (pushMark (st 8)) (.seq (pushNat (st 8) 1)
      (powMulN (st 8) 2 (st 7) (st 23) (st 14) (st 17) (st 18) (st 19) (st 20) (st 21)))) S4 S5
      (fun _ => True) (1 + ((bitLen 1 + 1) + powCost 2 1 (q0Of d * Kv))) := by
    rw [hS5]
    apply runs_fl
    have c1 := runs_pushNat (st 8) 1 (Function.update S4 (st 8) (Sym.mark :: S4 (st 8)))
    have c2 := runs_powMulN (k := st 8) (ns := st 7) (Kc := st 23) (t := st 14) (Q := st 17)
      (Tdst := st 18) (A := st 19) (Bs := st 20) (Acc := st 21)
      (hnd [8, 7, 23, 14, 17, 18, 19, 20, 21] (by decide)) 2 (by norm_num) 1 (q0Of d * Kv)
      (Sym.mark :: S4 (st 8)) (Sym.mark :: S (st 7))
      (Function.update (Function.update S4 (st 8) (Sym.mark :: S4 (st 8))) (st 8)
        (natSyms 1 ++ Function.update S4 (st 8) (Sym.mark :: S4 (st 8)) (st 8)))
      (termOK_mark _) (termOK_mark _)
      (by rw [Function.update_self, Function.update_self])
      (by simp +decide only [hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem, one_mul]
  -- step 6: `X + M − 1`
  have r6 : Runs (.seq (pushMark (st 9)) (.seq (addN (st 8) (st 5) (st 9) (st 14) (st 15) (st 16))
      (decL (st 9) (st 14)))) S5 S6 (fun _ => True)
      (1 + (20 * (bitLen (2 ^ (q0Of d * Kv)) + bitLen (Wc ^ Nat.clog mH d) + 1) +
        (6 * bitLen (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1 + 1) + 8))) := by
    rw [hS6]
    apply runs_fl
    have c1 := runs_addN (x := st 8) (y := st 5) (z := st 9) (t1 := st 14) (t2 := st 15)
      (t3 := st 16) (hnd [8, 5, 9, 14, 15, 16] (by decide)) (2 ^ (q0Of d * Kv))
      (Wc ^ Nat.clog mH d) (Sym.mark :: S (st 8)) (Sym.mark :: S (st 5))
      (Function.update S5 (st 9) (Sym.mark :: S5 (st 9))) (termOK_mark _) (termOK_mark _)
      (by simp +decide only [hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false])
      (by simp +decide only [hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false])
    have hsum : 2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d =
        2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1 + 1 := by omega
    have c2 := runs_decL (k := st 9) (t := st 14) (hst.ne (by decide))
      (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1)
      (Function.update S5 (st 9) (Sym.mark :: S5 (st 9)) (st 9))
      (Function.update (Function.update S5 (st 9) (Sym.mark :: S5 (st 9))) (st 9)
        (natSyms (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d) ++
          Function.update S5 (st 9) (Sym.mark :: S5 (st 9)) (st 9)))
      (by rw [Function.update_self]; exact termOK_mark _)
      (by rw [Function.update_self, ← hsum])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem, Function.update_self]
  -- step 7: floors of the quotient and the remainder
  have r7 : Runs (.seq (pushMark (st 10)) (pushMark (st 11))) S6 S7 (fun _ => True) (1 + 1) := by
    have c1 := runs_pushMark (st 10) S6
    have c2 := runs_pushMark (st 11) (Function.update S6 (st 10) (Sym.mark :: S6 (st 10)))
    have e10 : S6 (st 10) = S (st 10) := by
      simp +decide only [hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false]
    have e11 : Function.update S6 (st 10) (Sym.mark :: S6 (st 10)) (st 11) = S (st 11) := by
      simp +decide only [hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false]
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [hS7, e11, e10]
  have hA : Runs (padPartA st) S S7 (fun _ => True)
      ((1 + clogCost mH d) + ((1 + ((bitLen 1 + 1) + powCost Wc 1 (Nat.clog mH d))) +
      ((1 + q0Cost d) + ((1 + mulCost (q0Of d) Kv) +
      ((1 + ((bitLen 1 + 1) + powCost 2 1 (q0Of d * Kv))) +
      ((1 + (20 * (bitLen (2 ^ (q0Of d * Kv)) + bitLen (Wc ^ Nat.clog mH d) + 1) +
        (6 * bitLen (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1 + 1) + 8))) + (1 + 1))))))) :=
    WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4
      (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6 r7)))))
  -- the division
  obtain ⟨S8, hS8⟩ : ∃ T, T = Function.update (Function.update S7 (st 10)
      (natSyms ((2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) / Wc ^ Nat.clog mH d) ++
        Sym.mark :: S (st 10))) (st 11)
      (natSyms ((2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) % Wc ^ Nat.clog mH d) ++
        Sym.mark :: S (st 11)) := ⟨_, rfl⟩
  have hD : Runs (divN (st ∘ padDivMap)) S7 S8 (fun _ => True)
      ((2 * 20 + 70) * (bitLen (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) *
        bitLen (Wc ^ Nat.clog mH d) + bitLen (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) +
        bitLen (Wc ^ Nat.clog mH d) + 1)) := by
    have c := runs_divN (hst.comp (by decide : Function.Injective padDivMap))
      (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) (Wc ^ Nat.clog mH d) hM0
      (Sym.mark :: S (st 9)) (Sym.mark :: S (st 5)) S7 (termOK_mark _) (termOK_mark _)
      (by rw [show (st ∘ padDivMap) 0 = st 9 from rfl]
          simp +decide only [hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
            hst.eq_iff, if_true, if_false])
      (by rw [show (st ∘ padDivMap) 1 = st 5 from rfl]
          simp +decide only [hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
            hst.eq_iff, if_true, if_false])
    rw [show (st ∘ padDivMap) 2 = st 10 from rfl, show (st ∘ padDivMap) 3 = st 11 from rfl] at c
    have e10 : S7 (st 10) = Sym.mark :: S (st 10) := by
      rw [hS7, Function.update_of_ne (hst.ne (by decide)), Function.update_self]
    have e11 : S7 (st 11) = Sym.mark :: S (st 11) := by
      rw [hS7, Function.update_self]
    rw [e11, e10] at c
    rw [hS8]
    exact c
  -- the outputs and the cleanup
  obtain ⟨S9, hS9⟩ : ∃ T, T = Function.update S8 (st 2) (natSyms (padR d Kv) ++ S (st 2)) :=
    ⟨_, rfl⟩
  obtain ⟨S10, hS10⟩ : ∃ T, T = Function.update S9 (st 3)
      (natSyms (2 ^ (q0Of d * Kv)) ++ S (st 3)) := ⟨_, rfl⟩
  have b1 : Runs (mulN (st 5) (st 10) (st 2) (st 19) (st 20) (st 21) (st 22)) S8 S9
      (fun _ => True) (mulCost (Wc ^ Nat.clog mH d)
        ((2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) / Wc ^ Nat.clog mH d)) := by
    have c := runs_mulN (x := st 5) (y := st 10) (z := st 2) (A := st 19) (Bs := st 20)
      (Acc := st 21) (T := st 22) (hnd [5, 10, 2, 19, 20, 21, 22] (by decide))
      (Wc ^ Nat.clog mH d) ((2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) / Wc ^ Nat.clog mH d)
      (Sym.mark :: S (st 5)) (Sym.mark :: S (st 10)) S8 (termOK_mark _) (termOK_mark _)
      (by simp +decide only [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
        hst.eq_iff, if_true, if_false])
      (by simp +decide only [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
        hst.eq_iff, if_true, if_false])
    have e2 : S8 (st 2) = S (st 2) := by
      simp +decide only [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
        hst.eq_iff, if_true, if_false]
    rw [e2, ← padR_eq] at c
    rw [hS9]
    exact c
  have b2 : Runs (copyN (st 8) (st 3) (st 14)) S9 S10 (fun _ => True)
      (7 * bitLen (2 ^ (q0Of d * Kv)) + 7) := by
    have c := runs_copyN (src := st 8) (dst := st 3) (tmp := st 14) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) (2 ^ (q0Of d * Kv)) (Sym.mark :: S (st 8)) S9
      (termOK_mark _)
      (by simp +decide only [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false])
    have e3 : S9 (st 3) = S (st 3) := by
      simp +decide only [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
        hst.eq_iff, if_true, if_false]
    rw [e3] at c
    rw [hS10]
    exact c
  -- drop the work stacks
  obtain ⟨D1, hD1⟩ : ∃ T, T = Function.update S10 (st 11) (S (st 11)) := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ T, T = Function.update D1 (st 10) (S (st 10)) := ⟨_, rfl⟩
  obtain ⟨D3, hD3⟩ : ∃ T, T = Function.update D2 (st 9) (S (st 9)) := ⟨_, rfl⟩
  obtain ⟨D4, hD4⟩ : ∃ T, T = Function.update D3 (st 8) (S (st 8)) := ⟨_, rfl⟩
  obtain ⟨D5, hD5⟩ : ∃ T, T = Function.update D4 (st 7) (S (st 7)) := ⟨_, rfl⟩
  obtain ⟨D6, hD6⟩ : ∃ T, T = Function.update D5 (st 6) (S (st 6)) := ⟨_, rfl⟩
  obtain ⟨D7, hD7⟩ : ∃ T, T = Function.update D6 (st 5) (S (st 5)) := ⟨_, rfl⟩
  obtain ⟨D8, hD8⟩ : ∃ T, T = Function.update D7 (st 4) (S (st 4)) := ⟨_, rfl⟩
  have d1 := runs_dropF (st 11) ((2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) % Wc ^ Nat.clog mH d)
    Sym.mark (S (st 11)) S10 rfl (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  have d2 := runs_dropF (st 10) ((2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) / Wc ^ Nat.clog mH d)
    Sym.mark (S (st 10)) D1 rfl (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  have d3 := runs_dropF (st 9) (2 ^ (q0Of d * Kv) + Wc ^ Nat.clog mH d - 1) Sym.mark (S (st 9)) D2
    rfl (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  have d4 := runs_dropF (st 8) (2 ^ (q0Of d * Kv)) Sym.mark (S (st 8)) D3 rfl
    (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  have d5 := runs_dropF (st 7) (q0Of d * Kv) Sym.mark (S (st 7)) D4 rfl
    (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  have d6 := runs_dropF (st 6) (q0Of d) Sym.mark (S (st 6)) D5 rfl
    (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  have d7 := runs_dropF (st 5) (Wc ^ Nat.clog mH d) Sym.mark (S (st 5)) D6 rfl
    (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  have d8 := runs_dropF (st 4) (Nat.clog mH d) Sym.mark (S (st 4)) D7 rfl
    (by simp +decide only [hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false])
  rw [← hD1] at d1
  rw [← hD2] at d2
  rw [← hD3] at d3
  rw [← hD4] at d4
  rw [← hD5] at d5
  rw [← hD6] at d6
  rw [← hD7] at d7
  rw [← hD8] at d8
  have hB := WP.W9comp.runs_seq b1 (WP.W9comp.runs_seq b2 (WP.W9comp.runs_seq d1
    (WP.W9comp.runs_seq d2 (WP.W9comp.runs_seq d3 (WP.W9comp.runs_seq d4 (WP.W9comp.runs_seq d5
    (WP.W9comp.runs_seq d6 (WP.W9comp.runs_seq d7 d8))))))))
  have hall := WP.W9comp.runs_seq (runs_liftRegs' lN hA) (WP.W9comp.runs_seq hD
    (runs_liftRegs' lN hB))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases eq_or_ne k (st 2) with rfl | h2
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 3) with rfl | h3
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 4) with rfl | h4
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 5) with rfl | h5
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 6) with rfl | h6
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 7) with rfl | h7
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 8) with rfl | h8
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 9) with rfl | h9
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 10) with rfl | h10
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 11) with rfl | h11
    · simp +decide only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false]
    simp only [hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3,
      hS2, hS1, fl, Function.update_apply, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, if_false]
  · simp only [padRCost]
    omega

end PadRSpec

end SubNLogN.Machine.Layer.DrvArith
