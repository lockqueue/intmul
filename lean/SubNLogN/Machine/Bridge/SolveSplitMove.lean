/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSplitDefs
import SubNLogN.Machine.K1.DistributeCore
import SubNLogN.Machine.Calculus.API

/-!
# K5-SOLVE-b (`Bridge/SolveSplitMove.lean`): counted and exhaustive record moves

Generic sub-kernels for the half split/merge and the backward reindex (namespace
`SubNLogN.Machine.Bridge.SolveBAux`; all helpers):
* `moveM ctr src dst cnt ctmp`: move exactly `M` records from `src` onto `dst` (each pushed reversed,
  W4's `moveRec`), where `M` is `natSyms M` on `ctr` (restored); `cnt` is a work counter (empty
  before and after), `ctmp` a temporary (restored). `moveM_runs`: exact final stacks, cost
  `3·vol + M·(6·bitLen M + 10) + 7·bitLen M + 9`.
* `moveAll src dst`: move all records of `src` (down to a `BlkTerm` rest) onto `dst`.
  `moveAll_runs`: exact final stacks, cost `3·vol + 2·#records + 2`.
-/

namespace SubNLogN.Machine.Bridge.SolveBAux

open TMFw TMFw.Contracts TMFw.Lib WP.W9comp SubNLogN.Machine.K2 SubNLogN.Machine.Calculus
  Computability

variable {K : Type} [DecidableEq K]

theorem bitLen_mono' {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem decide_pos_eq (n : ℕ) : (!decide (n = 0)) = decide (0 < n) := by
  by_cases h : n = 0 <;> simp [h, Nat.pos_iff_ne_zero]

/-! ## `moveM`: move `M` records -/

/-- Loop body of `moveM`: move one record, decrement the work counter, test it. -/
def moveMBody (src dst cnt ctmp : K) : SProg K :=
  .seq (moveRec src dst) (.seq (dec cnt ctmp) (zeroTest cnt))

/-- Move `M` records from `src` onto `dst` (each pushed reversed); `M` is read from `ctr`. -/
def moveM (ctr src dst cnt ctmp : K) : SProg K :=
  .seq (.seq (copyBlock ctr cnt ctmp) (zeroTest cnt)) (.loop optIsBit (moveMBody src dst cnt ctmp))

omit [DecidableEq K] in
theorem closed_moveM (ctr src dst cnt ctmp : K) : (moveM ctr src dst cnt ctmp).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveM, moveMBody, copyBlock, moveBlock, moveBits,
    moveBitsBody, restoreR, moveBitsDup, dupBody, pushC, pushR, popR, peekR, skip, dec, scanLoop,
    scanBody, decFix, zeroTest, moveRec, moveRecBody]

section MoveM

variable {ctr src dst cnt ctmp : K}

/-- State of `moveM` with `n` moves remaining (counter `n` on `cnt`). -/
def mvState (src dst cnt : K) (S : K → List Sym) (M : ℕ) (ps qs : List (List Bool))
    (rest : List Sym) (n : ℕ) : K → List Sym :=
  Function.update (Function.update (Function.update S src (arrSyms (ps.drop (M - n) ++ qs) ++ rest))
    dst ((arrSyms (ps.take (M - n))).reverse ++ S dst)) cnt (natSyms n)

/-- One iteration of `moveM`. -/
theorem moveM_step (hsd : src ≠ dst) (hsc : src ≠ cnt) (hdc : dst ≠ cnt) (hct : cnt ≠ ctmp)
    (S : K → List Sym) (M : ℕ) (ps qs : List (List Bool)) (hps : ps.length = M)
    (rest : List Sym) (n : ℕ) (hn : n < M) :
    Runs (moveMBody src dst cnt ctmp) (mvState src dst cnt S M ps qs rest (n + 1))
      (mvState src dst cnt S M ps qs rest n) (fun v => optIsBit v = decide (0 < n))
      (3 * vol (ps.drop (M - (n + 1))) - 3 * vol (ps.drop (M - n)) + (6 * bitLen M + 9)) := by
  apply Runs.of_eval
  intro x
  have hlt : M - (n + 1) < ps.length := by omega
  have hdrop : ps.drop (M - (n + 1)) = ps[M - (n + 1)] :: ps.drop (M - n) := by
    rw [List.drop_eq_getElem_cons hlt]
    congr 2
    omega
  have htake : ps.take (M - n) = ps.take (M - (n + 1)) ++ [ps[M - (n + 1)]] := by
    rw [show M - n = M - (n + 1) + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hlt]
    rfl
  set p := ps[M - (n + 1)] with hp
  -- the source holds record `p` on top
  have hS : mvState src dst cnt S M ps qs rest (n + 1) src =
      p.map Sym.bit ++ Sym.sep :: (arrSyms (ps.drop (M - n) ++ qs) ++ rest) := by
    simp only [mvState, Function.update_of_ne hsc, Function.update_of_ne hsd,
      Function.update_self, hdrop, List.cons_append, arrSyms_cons, List.append_assoc,
      recSyms_append]
  have e1 := moveRec_eval hsd x (p.map Sym.bit) (arrSyms (ps.drop (M - n) ++ qs) ++ rest)
    (mvState src dst cnt S M ps qs rest (n + 1)) (bits_data p) hS
  set S1 := Function.update (Function.update (mvState src dst cnt S M ps qs rest (n + 1)) src
    (arrSyms (ps.drop (M - n) ++ qs) ++ rest)) dst (Sym.sep :: ((p.map Sym.bit).reverse ++
      mvState src dst cnt S M ps qs rest (n + 1) dst)) with hS1
  have hS1c : S1 cnt = (encodeNat (n + 1)).map Sym.bit ++ [] := by
    rw [hS1, Function.update_of_ne (Ne.symm hdc), Function.update_of_ne (Ne.symm hsc), mvState,
      Function.update_self, List.append_nil]
    rfl
  have e2 := dec_eval hct [] (some Sym.sep) n [] S1 TermOK.nil hS1c
  set S2 := Function.update S1 cnt ((encodeNat n).map Sym.bit ++ []) with hS2
  obtain ⟨r, hr, e3⟩ := zeroTest_eval (k := cnt) [] (some Sym.mark) n [] S2 TermOK.nil
    (by rw [hS2, Function.update_self])
  refine ⟨r, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, by rw [hr, decide_pos_eq], ?_⟩
  · -- the final state
    congr 1
    funext k
    rw [hS2, hS1]
    simp only [mvState, Function.update_apply]
    by_cases hk1 : k = cnt
    · simp [hk1, natSyms]
    · by_cases hk2 : k = dst
      · simp [hk1, hk2, hdc, htake, arrSyms_append, arrSyms_singleton, reverse_recSyms]
      · by_cases hk3 : k = src
        · simp [hk1, hk2, hk3, hsd, hsc]
        · simp [hk1, hk2, hk3]
  · -- cost
    have hz := zerosLead_le_length (encodeNat (n + 1))
    have hb : (encodeNat (n + 1)).length ≤ bitLen M := bitLen_mono' (by omega)
    have hv : vol (ps.drop (M - (n + 1))) = p.length + 1 + vol (ps.drop (M - n)) := by
      rw [hdrop, vol_cons]
    simp only [List.length_map]
    omega


theorem natSyms_zero' : natSyms 0 = [] := by
  show (encodeNat 0).map Sym.bit = []
  rw [TMFw.encodeNat_zero]
  rfl

/-- **`moveM`**: the first `M` records `ps` of `src` move onto `dst` (reversed); `cnt` ends empty,
`ctr` and `ctmp` are restored. -/
theorem moveM_runs (hsd : src ≠ dst) (hsc : src ≠ cnt) (hdc : dst ≠ cnt) (hct : cnt ≠ ctmp)
    (hrc : ctr ≠ cnt) (hrt : ctr ≠ ctmp)
    (S : K → List Sym) (M : ℕ) (rM : List Sym) (hrM : TermOK rM) (ps qs : List (List Bool))
    (hps : ps.length = M) (rest : List Sym)
    (hctr : S ctr = natSyms M ++ rM) (hcnt : S cnt = [])
    (hsrc : S src = arrSyms (ps ++ qs) ++ rest) :
    Runs (moveM ctr src dst cnt ctmp) S
      (Function.update (Function.update S src (arrSyms qs ++ rest)) dst
        ((arrSyms ps).reverse ++ S dst))
      (fun _ => True) (3 * vol ps + M * (6 * bitLen M + 10) + 7 * bitLen M + 9) := by
  have h0 : Runs (.seq (copyBlock ctr cnt ctmp) (zeroTest cnt)) S
      (mvState src dst cnt S M ps qs rest M) (fun v => optIsBit v = decide (0 < M))
      (7 * bitLen M + 8) := by
    apply Runs.of_eval
    intro x
    have e1 := copyBlock_eval hrc hrt hct [] x (encodeNat M) rM S hrM hctr
    obtain ⟨r, hr, e2⟩ := zeroTest_eval (k := cnt) [] (some Sym.mark) M []
      (Function.update S cnt ((encodeNat M).map Sym.bit ++ S cnt)) TermOK.nil
      (by rw [Function.update_self, hcnt])
    refine ⟨r, _, (Eval.seq e1 e2).of_eq ?_ rfl, by rw [hr, decide_pos_eq], ?_⟩
    · congr 1
      funext k
      simp only [mvState, Function.update_apply, Nat.sub_self, List.drop_zero, List.take_zero,
        arrSyms_nil, List.reverse_nil, List.nil_append]
      by_cases hk1 : k = cnt
      · simp [hk1, hcnt, natSyms]
      · by_cases hk2 : k = dst
        · simp [hk2, hdc]
        · by_cases hk3 : k = src
          · simp [hk3, hsrc, hsd, hsc]
          · simp [hk1, hk2, hk3]
    · show 7 * (encodeNat M).length + 7 + 1 ≤ 7 * bitLen M + 8
      rfl
  have hloop := API.seq_loop_pot (ρ := []) (p := moveMBody src dst cnt ctmp) (c := optIsBit)
    (st := mvState src dst cnt S M ps qs rest) (S := S)
    (B := fun n => 3 * vol (ps.drop (M - (n + 1))) - 3 * vol (ps.drop (M - n)) +
      (6 * bitLen M + 9))
    (Φ := fun n => 3 * vol (ps.drop (M - n))) (a := 6 * bitLen M + 9) (N := M)
    ((API.runsIn_nil_iff _ _ _ _ _).2 h0)
    (fun n hn => (API.runsIn_nil_iff _ _ _ _ _).2
      (moveM_step hsd hsc hdc hct S M ps qs hps rest n hn))
    (fun n hn => by
      have := vol_drop_anti ps (show M - (n + 1) ≤ M - n by omega)
      omega)
  have hfin : mvState src dst cnt S M ps qs rest 0 =
      Function.update (Function.update S src (arrSyms qs ++ rest)) dst
        ((arrSyms ps).reverse ++ S dst) := by
    funext k
    simp only [mvState, Function.update_apply, Nat.sub_zero,
      List.drop_eq_nil_of_le (le_of_eq hps), List.take_of_length_le (le_of_eq hps),
      List.nil_append, natSyms_zero']
    by_cases hk1 : k = cnt
    · simp [hk1, hcnt, Ne.symm hdc, Ne.symm hsc]
    · simp [hk1]
  have h := (API.runsIn_nil_iff _ _ _ _ _).1 hloop
  refine runs_mono (runs_congr h hfin) (fun _ _ => trivial) ?_
  rw [Nat.sub_self, List.drop_zero]
  have e : M * (6 * bitLen M + 9 + 1) = M * (6 * bitLen M + 10) := by ring
  omega

end MoveM

/-! ## `moveAll`: move every record -/

/-- Loop body of `moveAll`: move one record, peek the source. -/
def moveAllBody (src dst : K) : SProg K := .seq (moveRec src dst) (peekR src)

/-- Move all records of `src` (down to a `BlkTerm` rest) onto `dst`, each pushed reversed. -/
def moveAll (src dst : K) : SProg K := .seq (peekR src) (.loop isRecR (moveAllBody src dst))

omit [DecidableEq K] in
theorem closed_moveAll (src dst : K) : (moveAll src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveAll, moveAllBody, moveRec, moveRecBody, pushR, popR,
    peekR]

section MoveAll

variable {src dst : K}

/-- State of `moveAll` with `n` records remaining. -/
def maState (src dst : K) (S : K → List Sym) (qs : List (List Bool)) (rest : List Sym) (n : ℕ) :
    K → List Sym :=
  Function.update (Function.update S src (arrSyms (qs.drop (qs.length - n)) ++ rest)) dst
    ((arrSyms (qs.take (qs.length - n))).reverse ++ S dst)

theorem maState_head (hsd : src ≠ dst) (S : K → List Sym) (qs : List (List Bool))
    (rest : List Sym) (hrest : BlkTerm rest) (n : ℕ) (hn : n ≤ qs.length) :
    isRecR (maState src dst S qs rest n src).head? = decide (0 < n) := by
  simp only [maState, Function.update_of_ne hsd, Function.update_self]
  by_cases h0 : n = 0
  · subst h0
    simp only [Nat.sub_zero, List.drop_length, arrSyms_nil, List.nil_append,
      isRecR_of_blkTerm hrest, lt_irrefl, decide_false]
  · have hlt : qs.length - n < qs.length := by omega
    rw [List.drop_eq_getElem_cons hlt, isRecR_head_cons]
    exact (decide_eq_true (by omega)).symm

theorem moveAll_step (hsd : src ≠ dst) (S : K → List Sym) (qs : List (List Bool))
    (rest : List Sym) (hrest : BlkTerm rest) (n : ℕ) (hn : n < qs.length) :
    Runs (moveAllBody src dst) (maState src dst S qs rest (n + 1)) (maState src dst S qs rest n)
      (fun v => isRecR v = decide (0 < n))
      (3 * vol (qs.drop (qs.length - (n + 1))) - 3 * vol (qs.drop (qs.length - n)) + 1) := by
  apply Runs.of_eval
  intro x
  have hlt : qs.length - (n + 1) < qs.length := by omega
  have hdrop : qs.drop (qs.length - (n + 1)) = qs[qs.length - (n + 1)] :: qs.drop (qs.length - n) := by
    rw [List.drop_eq_getElem_cons hlt]
    congr 2
    omega
  have htake : qs.take (qs.length - n) =
      qs.take (qs.length - (n + 1)) ++ [qs[qs.length - (n + 1)]] := by
    rw [show qs.length - n = qs.length - (n + 1) + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hlt]
    rfl
  set p := qs[qs.length - (n + 1)] with hp
  have hS : maState src dst S qs rest (n + 1) src =
      p.map Sym.bit ++ Sym.sep :: (arrSyms (qs.drop (qs.length - n)) ++ rest) := by
    simp only [maState, Function.update_of_ne hsd, Function.update_self, hdrop, arrSyms_cons,
      List.append_assoc, recSyms_append, List.cons_append]
  have e1 := moveRec_eval hsd x (p.map Sym.bit) (arrSyms (qs.drop (qs.length - n)) ++ rest)
    (maState src dst S qs rest (n + 1)) (bits_data p) hS
  have e2 := peekR_eval src (some Sym.sep) (Function.update (Function.update
    (maState src dst S qs rest (n + 1)) src (arrSyms (qs.drop (qs.length - n)) ++ rest)) dst
      (Sym.sep :: ((p.map Sym.bit).reverse ++ maState src dst S qs rest (n + 1) dst)))
  have hfin : Function.update (Function.update (maState src dst S qs rest (n + 1)) src
      (arrSyms (qs.drop (qs.length - n)) ++ rest)) dst
      (Sym.sep :: ((p.map Sym.bit).reverse ++ maState src dst S qs rest (n + 1) dst)) =
      maState src dst S qs rest n := by
    funext k
    simp only [maState, Function.update_apply]
    by_cases hk2 : k = dst
    · simp [hk2, Ne.symm hsd, htake, arrSyms_append, arrSyms_singleton, reverse_recSyms]
    · by_cases hk3 : k = src
      · simp [hk3, hsd]
      · simp [hk2, hk3]
  refine ⟨(maState src dst S qs rest n src).head?, _, (Eval.seq e1 e2).of_eq (by rw [hfin]) rfl,
    ?_, ?_⟩
  · exact maState_head hsd S qs rest hrest n (by omega)
  · have hv : vol (qs.drop (qs.length - (n + 1))) = p.length + 1 + vol (qs.drop (qs.length - n)) := by
      rw [hdrop, vol_cons]
    simp only [List.length_map]
    omega

/-- **`moveAll`**: all records `qs` of `src` move onto `dst` (reversed); cost
`3·vol qs + 2·|qs| + 2`. -/
theorem moveAll_runs (hsd : src ≠ dst) (S : K → List Sym) (qs : List (List Bool))
    (rest : List Sym) (hrest : BlkTerm rest) (hsrc : S src = arrSyms qs ++ rest) :
    Runs (moveAll src dst) S
      (Function.update (Function.update S src rest) dst ((arrSyms qs).reverse ++ S dst))
      (fun _ => True) (3 * vol qs + 2 * qs.length + 2) := by
  have h0 : Runs (peekR src) S (maState src dst S qs rest qs.length)
      (fun v => isRecR v = decide (0 < qs.length)) 1 := by
    have hst : maState src dst S qs rest qs.length = S := by
      funext k
      simp only [maState, Nat.sub_self, List.drop_zero, List.take_zero, arrSyms_nil,
        List.reverse_nil, List.nil_append, Function.update_apply]
      by_cases hk2 : k = dst
      · simp [hk2]
      · by_cases hk3 : k = src
        · simp [hk3, hsrc, hsd]
        · simp [hk2, hk3]
    rw [hst]
    apply Runs.of_eval
    intro x
    refine ⟨_, 1, peekR_eval src x S, ?_, le_rfl⟩
    have := maState_head hsd S qs rest hrest qs.length le_rfl
    rwa [hst] at this
  have hloop := API.seq_loop_pot (ρ := []) (p := moveAllBody src dst) (c := isRecR)
    (st := maState src dst S qs rest) (S := S)
    (B := fun n => 3 * vol (qs.drop (qs.length - (n + 1))) - 3 * vol (qs.drop (qs.length - n)) + 1)
    (Φ := fun n => 3 * vol (qs.drop (qs.length - n))) (a := 1) (N := qs.length)
    ((API.runsIn_nil_iff _ _ _ _ _).2 h0)
    (fun n hn => (API.runsIn_nil_iff _ _ _ _ _).2 (moveAll_step hsd S qs rest hrest n hn))
    (fun n hn => by
      have := vol_drop_anti qs (show qs.length - (n + 1) ≤ qs.length - n by omega)
      omega)
  have hfin : maState src dst S qs rest 0 =
      Function.update (Function.update S src rest) dst ((arrSyms qs).reverse ++ S dst) := by
    simp only [maState, Nat.sub_zero, List.drop_length, List.take_length, arrSyms_nil,
      List.nil_append]
  have h := (API.runsIn_nil_iff _ _ _ _ _).1 hloop
  refine runs_mono (runs_congr h hfin) (fun _ _ => trivial) ?_
  rw [Nat.sub_self, List.drop_zero]
  omega

end MoveAll

end SubNLogN.Machine.Bridge.SolveBAux
