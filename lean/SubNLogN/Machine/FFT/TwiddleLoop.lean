/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleSel

/-!
# K4-TWIDDLE part (D): the selection loop over the records (`Machine/FFT/TwiddleLoop.lean`)

**Scope (honest summary).** Generic machine loop (any stack type `K`, registers through a lens) for
the twiddle pass `TwiddlePassStmt`: for every record `i` of the array on `A` (data-driven loop),
move the record to a side stack `T`, run an address routine `addr` (a parameter, specified by the
hypothesis `haddr`: it pushes `natSyms (J i)` on `I`), select the table entry `J i` by **one table
scan** (`selEntry`, part C) onto `PHI`, and increment the record counter `N`. Afterwards the
counter is dropped, the records are put on `Z` and the selected phase records on `PHI2`, both in
record order. Everything is proved (no `sorry`); costs are explicit.
-/

namespace SubNLogN.Machine.FFT.TwiddleAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF

theorem isRecO_head_arrSyms_cons (p : List Bool) (v : List (List Bool)) (R : List Sym) :
    isRecO (arrSyms (p :: v) ++ R).head? = true := by
  rw [arrSyms_cons', recSyms_eq]
  cases p <;> rfl

section Loop

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- One record: move it from `A` to `T`, compute its table index onto `I`, select the table entry
onto `PHI`, increment the record counter `N`. -/
def selBody (addr : Prog K (fun _ => Sym) σ) (A T N PHI TB TT TMP I I2 t : K) :
    Prog K (fun _ => Sym) σ :=
  .seq (moveRec lO A T) (.seq addr (.seq (selEntry lO TB TT TMP PHI I I2 t) (incP lO N t)))

/-- The selection loop: one iteration per record of `A`. -/
def selLoop (addr : Prog K (fun _ => Sym) σ) (A T N PHI TB TT TMP I I2 t : K) :
    Prog K (fun _ => Sym) σ :=
  ploop lO A isRecO (selBody lO addr A T N PHI TB TT TMP I I2 t)

/-- The selection phase: the loop, then drop the counter `N`, move the records from `T` to `Z` and
the selected phase records from `PHI` to `PHI2` (both end in record order). -/
def selPhase (addr : Prog K (fun _ => Sym) σ) (A T N PHI TB TT TMP I I2 t Z PHI2 : K) :
    Prog K (fun _ => Sym) σ :=
  .seq (selLoop lO addr A T N PHI TB TT TMP I I2 t) (.seq (drain lO N)
    (.seq (movePrefix lO T Z isRecO) (movePrefix lO PHI PHI2 isRecO)))

omit [DecidableEq K] in
theorem closed_selPhase {addr : Prog K (fun _ => Sym) σ} (haddr : addr.Closed)
    (A T N PHI TB TT TMP I I2 t Z PHI2 : K) :
    (selPhase lO addr A T N PHI TB TT TMP I I2 t Z PHI2).Closed :=
  ⟨closed_ploop lO A isRecO ⟨closed_moveRec lO A T, haddr,
      closed_selEntry lO TB TT TMP PHI I I2 t, closed_incP lO N t⟩,
    closed_drain lO N, closed_movePrefix lO T Z isRecO, closed_movePrefix lO PHI PHI2 isRecO⟩

/-- Loop state after `i` records. -/
def selSt (S : K → List Sym) (A T N PHI : K) (vs phs : List (List Bool)) (R : List Sym)
    (i : ℕ) : K → List Sym :=
  upd4 S A T N PHI (arrSyms (vs.drop i) ++ R) (arrSyms (vs.take i)).reverse (natSyms i)
    (arrSyms (phs.take i)).reverse

/-- State of record `i` just before its address call (the record is already on `T`). -/
def selMid (S : K → List Sym) (A T N PHI : K) (vs phs : List (List Bool)) (R : List Sym)
    (i : ℕ) : K → List Sym :=
  upd4 S A T N PHI (arrSyms (vs.drop (i + 1)) ++ R) (arrSyms (vs.take (i + 1))).reverse
    (natSyms i) (arrSyms (phs.take i)).reverse

/-- Uniform per-record cost bound of the loop. -/
def selRecCost (n1 TA tl n0 len : ℕ) : ℕ :=
  4 * n1 + 4 + TA + selCost tl n0 + (6 * bitLen len + 9)

theorem runs_selLoop {A T N PHI TB TT TMP I I2 t : K}
    (hd : [A, T, N, TB, TT, TMP, PHI, I, I2, t].Nodup)
    (addr : Prog K (fun _ => Sym) σ) (S : K → List Sym)
    (vs phs tab : List (List Bool)) (n0 n1 : ℕ) (R R' : List Sym) (J : ℕ → ℕ) (TA : ℕ)
    (hvs : ∀ p ∈ vs, p.length = n1) (htab : ∀ p ∈ tab, p.length = n0)
    (hlen : phs.length = vs.length) (hJ : ∀ i, i < vs.length → J i < tab.length)
    (hphs : ∀ i (hi : i < vs.length), phs[i]'(by omega) = tab[J i]'(hJ i hi))
    (hR : BlkTerm R)
    (hA : S A = arrSyms vs ++ R) (hT : S T = []) (hN : S N = []) (hPHI : S PHI = [])
    (hTB : S TB = arrSyms tab ++ R') (hTT : S TT = []) (hTMP : S TMP = []) (hI : S I = [])
    (hI2 : S I2 = []) (ht : S t = [])
    (haddr : ∀ i, i < vs.length → Runs addr (selMid S A T N PHI vs phs R i)
      (Function.update (selMid S A T N PHI vs phs R i) I (natSyms (J i))) (fun _ => True) TA) :
    Runs (selLoop lO addr A T N PHI TB TT TMP I I2 t) S (selSt S A T N PHI vs phs R vs.length)
      (fun _ => True) (vs.length * (selRecCost n1 TA tab.length n0 vs.length + 2) + 2) := by
  have p0 := List.pairwise_cons.1 hd
  have dAT : A ≠ T := p0.1 T (by simp)
  have dAN : A ≠ N := p0.1 N (by simp)
  have dAB : A ≠ TB := p0.1 TB (by simp)
  have dAX : A ≠ TT := p0.1 TT (by simp)
  have dAM : A ≠ TMP := p0.1 TMP (by simp)
  have dAP : A ≠ PHI := p0.1 PHI (by simp)
  have dAI : A ≠ I := p0.1 I (by simp)
  have dAJ : A ≠ I2 := p0.1 I2 (by simp)
  have dAt : A ≠ t := p0.1 t (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have dTN : T ≠ N := p1.1 N (by simp)
  have dTB : T ≠ TB := p1.1 TB (by simp)
  have dTX : T ≠ TT := p1.1 TT (by simp)
  have dTM : T ≠ TMP := p1.1 TMP (by simp)
  have dTP : T ≠ PHI := p1.1 PHI (by simp)
  have dTI : T ≠ I := p1.1 I (by simp)
  have dTJ : T ≠ I2 := p1.1 I2 (by simp)
  have dTt : T ≠ t := p1.1 t (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have dNB : N ≠ TB := p2.1 TB (by simp)
  have dNX : N ≠ TT := p2.1 TT (by simp)
  have dNM : N ≠ TMP := p2.1 TMP (by simp)
  have dNP : N ≠ PHI := p2.1 PHI (by simp)
  have dNI : N ≠ I := p2.1 I (by simp)
  have dNJ : N ≠ I2 := p2.1 I2 (by simp)
  have dNt : N ≠ t := p2.1 t (by simp)
  have hsel : [TB, TT, TMP, PHI, I, I2, t].Nodup := p2.2
  have p3 := List.pairwise_cons.1 p2.2
  have dBP : TB ≠ PHI := p3.1 PHI (by simp)
  have dBI : TB ≠ I := p3.1 I (by simp)
  have p4 := List.pairwise_cons.1 p3.2
  have dXP : TT ≠ PHI := p4.1 PHI (by simp)
  have dXI : TT ≠ I := p4.1 I (by simp)
  have p5 := List.pairwise_cons.1 p4.2
  have dMP : TMP ≠ PHI := p5.1 PHI (by simp)
  have dMI : TMP ≠ I := p5.1 I (by simp)
  have p6 := List.pairwise_cons.1 p5.2
  have dPI : PHI ≠ I := p6.1 I (by simp)
  have dPJ : PHI ≠ I2 := p6.1 I2 (by simp)
  have dPt : PHI ≠ t := p6.1 t (by simp)
  have p7 := List.pairwise_cons.1 p6.2
  have dIJ : I ≠ I2 := p7.1 I2 (by simp)
  have dIt : I ≠ t := p7.1 t (by simp)
  have hM : ∀ i x, x ≠ A → x ≠ T → x ≠ N → x ≠ PHI →
      selMid S A T N PHI vs phs R i x = S x := fun _ _ h1 h2 h3 h4 => upd4_o h1 h2 h3 h4
  have h0 : selSt S A T N PHI vs phs R 0 = S := by
    have h : selSt S A T N PHI vs phs R 0 = upd4 S A T N PHI (S A) (S T) (S N) (S PHI) := by
      rw [hA, hT, hN, hPHI]
      simp [selSt, arrSyms_nil', natSyms_zero']
    rw [h, upd4_self]
  have hloop := runs_ploop_const lO A isRecO (selBody lO addr A T N PHI TB TT TMP I I2 t)
    vs.length (selSt S A T N PHI vs phs R) (selRecCost n1 TA tab.length n0 vs.length) ?_ ?_
  · rw [h0] at hloop
    exact hloop
  · intro i hi
    have hSA : selSt S A T N PHI vs phs R i A = arrSyms (vs.drop i) ++ R := upd4_1 dAT dAN dAP
    rw [hSA]
    rcases Nat.lt_or_ge i vs.length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt, isRecO_head_arrSyms_cons]
      simp [hlt]
    · have hi' : i = vs.length := le_antisymm hi hge
      subst hi'
      rw [List.drop_of_length_le (le_refl _), arrSyms_nil', List.nil_append, isRecO_of_blkTerm hR]
      simp
  · intro i hi
    have hdrop : vs.drop i = vs[i] :: vs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have htake : vs.take (i + 1) = vs.take i ++ [vs[i]] := List.take_succ_eq_append_getElem hi
    have hip : i < phs.length := by omega
    have htakeP : phs.take (i + 1) = phs.take i ++ [phs[i]] :=
      List.take_succ_eq_append_getElem hip
    have hJi := hJ i hi
    -- 1. move record `i` to `T`
    have hSA : selSt S A T N PHI vs phs R i A =
        recSyms vs[i] ++ (arrSyms (vs.drop (i + 1)) ++ R) := by
      rw [show selSt S A T N PHI vs phs R i A = arrSyms (vs.drop i) ++ R from upd4_1 dAT dAN dAP,
        hdrop, arrSyms_cons', List.append_assoc]
    have e1 := runs_moveRec lO dAT (selSt S A T N PHI vs phs R i) vs[i] _ hSA
    have hST : selSt S A T N PHI vs phs R i T = (arrSyms (vs.take i)).reverse := upd4_2 dTN dTP
    have hmid : Function.update (Function.update (selSt S A T N PHI vs phs R i) A
        (arrSyms (vs.drop (i + 1)) ++ R)) T ((recSyms vs[i]).reverse ++
          selSt S A T N PHI vs phs R i T) = selMid S A T N PHI vs phs R i := by
      rw [hST]
      unfold selSt selMid
      rw [upd4_set1 dAT dAN dAP, upd4_set2 dTN dTP, htake, arrSyms_append', arrSyms_cons',
        arrSyms_nil', List.append_nil, List.reverse_append]
    rw [hmid] at e1
    -- 2. the address routine
    have e2 := haddr i hi
    -- 3. one table scan
    have hX2 : ∀ x, x ≠ I → Function.update (selMid S A T N PHI vs phs R i) I (natSyms (J i)) x =
        selMid S A T N PHI vs phs R i x := fun x hx => Function.update_of_ne hx _ _
    have e3 := runs_selEntry lO hsel
      (Function.update (selMid S A T N PHI vs phs R i) I (natSyms (J i))) tab n0 htab R' (J i) hJi
      (by rw [hX2 TB dBI, hM i TB dAB.symm dTB.symm dNB.symm dBP, hTB])
      (Function.update_self _ _ _)
      (by rw [hX2 TT dXI, hM i TT dAX.symm dTX.symm dNX.symm dXP, hTT]; exact termOK_nil')
      (by rw [hX2 TMP dMI, hM i TMP dAM.symm dTM.symm dNM.symm dMP, hTMP]; exact termOK_nil')
      (by rw [hX2 I2 dIJ.symm, hM i I2 dAJ.symm dTJ.symm dNJ.symm dPJ.symm, hI2])
      (by rw [hX2 t dIt.symm, hM i t dAt.symm dTt.symm dNt.symm dPt.symm, ht]; exact termOK_nil')
    have hMI0 : [] = selMid S A T N PHI vs phs R i I :=
      ((hM i I dAI.symm dTI.symm dNI.symm dPI.symm).trans hI).symm
    have hMP : selMid S A T N PHI vs phs R i PHI = (arrSyms (phs.take i)).reverse := upd4_4
    have hUI : Function.update (selMid S A T N PHI vs phs R i) I [] =
        selMid S A T N PHI vs phs R i := Function.update_eq_self_iff.2 hMI0
    have hX3 : Function.update (Function.update (Function.update (selMid S A T N PHI vs phs R i) I
        (natSyms (J i))) I []) PHI ((recSyms tab[J i]).reverse ++
          Function.update (selMid S A T N PHI vs phs R i) I (natSyms (J i)) PHI) =
        Function.update (selMid S A T N PHI vs phs R i) PHI
          (arrSyms (phs.take (i + 1))).reverse := by
      rw [Function.update_idem, Function.update_of_ne dPI, hUI, hMP,
        htakeP, hphs i hi, arrSyms_append', arrSyms_cons', arrSyms_nil', List.append_nil,
        List.reverse_append]
    -- 4. next record index
    have e4 := runs_incP lO dNt (Function.update (selMid S A T N PHI vs phs R i) PHI
        (arrSyms (phs.take (i + 1))).reverse) i [] termOK_nil'
      (by rw [Function.update_of_ne dNP, List.append_nil]; exact upd4_3 dNP)
    have hfin : Function.update (Function.update (selMid S A T N PHI vs phs R i) PHI
        (arrSyms (phs.take (i + 1))).reverse) N (natSyms (i + 1) ++ []) =
        selSt S A T N PHI vs phs R (i + 1) := by
      unfold selMid selSt
      rw [upd4_set4, upd4_set3 dNP, List.append_nil]
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' (runs_congr e3 hX3) e4)))
      (fun _ _ => trivial) ?_) hfin
    have hl : vs[i].length = n1 := hvs _ (List.getElem_mem _)
    have hsc := selCost_mono n0 hJi.le
    have hb := bitLen_le_bitLen hi.le
    simp only [selRecCost, hl]
    omega

/-- The final stacks of the selection phase. -/
theorem selPhase_final {A T N PHI Z PHI2 : K} (dAT : A ≠ T) (dAN : A ≠ N) (dAP : A ≠ PHI)
    (_dTN : T ≠ N) (_dTP : T ≠ PHI) (_dNP : N ≠ PHI) (hZ1 : Z ≠ A) (hZ2 : Z ≠ T) (hZ3 : Z ≠ N)
    (hZ4 : Z ≠ PHI) (hQ1 : PHI2 ≠ A) (hQ2 : PHI2 ≠ T) (hQ3 : PHI2 ≠ N) (hQ4 : PHI2 ≠ PHI)
    (hZQ : Z ≠ PHI2) (S : K → List Sym) (vs phs : List (List Bool)) (R : List Sym)
    (hT : S T = []) (hN : S N = []) (hPHI : S PHI = []) (hZ : S Z = []) (hPHI2 : S PHI2 = []) :
    let L1 := Function.update (selSt S A T N PHI vs phs R vs.length) N []
    let L2 := Function.update (Function.update L1 T []) Z (arrSyms vs ++ L1 Z)
    Function.update (Function.update L2 PHI []) PHI2 (arrSyms phs ++ L2 PHI2) =
      Function.update (Function.update (Function.update S A R) Z (arrSyms vs)) PHI2
        (arrSyms phs) := by
  intro L1 L2
  funext j
  simp only [L2, L1, selSt, upd4, Function.update_apply]
  split_ifs <;> simp_all [arrSyms_nil']

set_option maxHeartbeats 1000000 in
theorem runs_selPhase {A T N PHI TB TT TMP I I2 t Z PHI2 : K}
    (hd : [A, T, N, TB, TT, TMP, PHI, I, I2, t].Nodup)
    (hZ1 : Z ≠ A) (hZ2 : Z ≠ T) (hZ3 : Z ≠ N) (hZ4 : Z ≠ PHI)
    (hQ1 : PHI2 ≠ A) (hQ2 : PHI2 ≠ T) (hQ3 : PHI2 ≠ N) (hQ4 : PHI2 ≠ PHI) (hZQ : Z ≠ PHI2)
    (addr : Prog K (fun _ => Sym) σ) (S : K → List Sym)
    (vs phs tab : List (List Bool)) (n0 n1 : ℕ) (R R' : List Sym) (J : ℕ → ℕ) (TA : ℕ)
    (hvs : ∀ p ∈ vs, p.length = n1) (htab : ∀ p ∈ tab, p.length = n0)
    (hlen : phs.length = vs.length) (hJ : ∀ i, i < vs.length → J i < tab.length)
    (hphs : ∀ i (hi : i < vs.length), phs[i]'(by omega) = tab[J i]'(hJ i hi))
    (hR : BlkTerm R)
    (hA : S A = arrSyms vs ++ R) (hT : S T = []) (hN : S N = []) (hPHI : S PHI = [])
    (hTB : S TB = arrSyms tab ++ R') (hTT : S TT = []) (hTMP : S TMP = []) (hI : S I = [])
    (hI2 : S I2 = []) (ht : S t = []) (hZ : S Z = []) (hPHI2 : S PHI2 = [])
    (haddr : ∀ i, i < vs.length → Runs addr (selMid S A T N PHI vs phs R i)
      (Function.update (selMid S A T N PHI vs phs R i) I (natSyms (J i))) (fun _ => True) TA) :
    Runs (selPhase lO addr A T N PHI TB TT TMP I I2 t Z PHI2) S
      (Function.update (Function.update (Function.update S A R) Z (arrSyms vs)) PHI2
        (arrSyms phs))
      (fun _ => True)
      (vs.length * (selRecCost n1 TA tab.length n0 vs.length + 2) + 2 +
        (3 * bitLen vs.length + 2 + (4 * (arrSyms vs).length + 2 +
          (4 * (arrSyms phs).length + 2)))) := by
  have p0 := List.pairwise_cons.1 hd
  have dAT : A ≠ T := p0.1 T (by simp)
  have dAN : A ≠ N := p0.1 N (by simp)
  have dAP : A ≠ PHI := p0.1 PHI (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have dTN : T ≠ N := p1.1 N (by simp)
  have dTP : T ≠ PHI := p1.1 PHI (by simp)
  have dNP : N ≠ PHI := (List.pairwise_cons.1 p1.2).1 PHI (by simp)
  have eL := runs_selLoop lO hd addr S vs phs tab n0 n1 R R' J TA hvs htab hlen hJ hphs hR hA hT
    hN hPHI hTB hTT hTMP hI hI2 ht haddr
  have hLN : selSt S A T N PHI vs phs R vs.length N = natSyms vs.length := upd4_3 dNP
  have eD := runs_drain lO N (selSt S A T N PHI vs phs R vs.length)
  rw [hLN, length_natSyms] at eD
  have hLT : Function.update (selSt S A T N PHI vs phs R vs.length) N [] T =
      (arrSyms vs).reverse := by
    rw [Function.update_of_ne dTN]
    unfold selSt
    rw [upd4_2 dTN dTP, List.take_of_length_le (le_refl _)]
  have eT := runs_revArr_in lO hZ2.symm _ vs hLT
  have hLP : Function.update (Function.update (Function.update
      (selSt S A T N PHI vs phs R vs.length) N []) T []) Z
      (arrSyms vs ++ Function.update (selSt S A T N PHI vs phs R vs.length) N [] Z) PHI =
      (arrSyms phs).reverse := by
    rw [Function.update_of_ne hZ4.symm, Function.update_of_ne dTP.symm,
      Function.update_of_ne dNP.symm]
    unfold selSt
    rw [upd4_4, List.take_of_length_le (le_of_eq hlen)]
  have eP := runs_revArr_in lO hQ4.symm _ phs hLP
  refine runs_congr (runs_mono (runs_seq' eL (runs_seq' eD (runs_seq' eT eP)))
    (fun _ _ => trivial) (by omega)) ?_
  exact selPhase_final dAT dAN dAP dTN dTP dNP hZ1 hZ2 hZ3 hZ4 hQ1 hQ2 hQ3 hQ4 hZQ S vs phs R hT
    hN hPHI hZ hPHI2

end Loop

end SubNLogN.Machine.FFT.TwiddleAux
