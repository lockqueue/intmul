/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6JoinCost

/-!
# Lemma A.8 join/unjoin: the high join (`Machine/AppC/C6JoinHigh.lean`)

**Theorem** `c6HighJoin_holds (q) (hq : 2 ≤ q) : C6HighJoinStmt q` (`C6QLeaves.lean`).

**Program** `progHJ q P1` on `KJ E1` (`C6JoinMove.lean`); `P1` is the proved K1 kernel
`K1Digit.k1MoveDigitMix_holds q false`.
1. `setupJ q 1 PB` (`C6JoinCommon.lean`): `t := c6T q e` on `tS`, `ℓ := e - t` on `lS`,
   `N1 := G·q^e`, `PB := B·q^ℓ`, every counter above a `mark`.
2. `t` iterations (`K1.Rot.nLoop`, counter `Kc`). Iteration `j`, with `r = t - (j+1)` on `Kc`:
   `N2 := PB·q^r = q^(e-1-j)·B`; the left move `hjStep q e G B j =
   moveLeftMixInv q (q^e·G) (q^(e-1-j)·B)` (`moveJ`: the K1 kernel into `D`, then back); drop `N2`.
3. `cleanJ PB`: drop `PB, N1, lS, tS`.
After `j` iterations the array is `permByInv (hjComp q e G B j) v` (`permByInv_hjComp_succ`), and
`hjComp q e G B t` agrees with `c6HJInv (q^t) (q^ℓ) G B` on the index range (`c6HJInv_eq_hjComp`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Cost.** Every counter operation costs at most `K·Λ`, `Λ = q^(2e)·G·B ≤ |v| ≤ V` (`master_le`,
`K` depending on `q` only); each move costs `C1·(V + 1) + 6V + 6`. Total
`≤ cHJ q C1 · (V·(t + 1) + 1)` (`costHJ_le`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

namespace AppC.C6JoinAux

open NatArith

section Programs

variable {E1 : Type} {R1 : Type}

/-- One iteration of the high join: `N2 := PB·q^r` (`r` read from `Kc`), the left move, drop
`N2`. -/
def bodyHJ (q : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  .seq (mkPowJ q (jp .PB) .N2 (jp .Kc)) (.seq (moveJ P1) ((dropF (jp .N2)).liftRegs (lN R1)))

/-- **The high-join program.** -/
def progHJ (q : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  .seq (setupJ q (.inl 1) .PB)
    (.seq (K1.Rot.nLoop (lWJ R1) (jp .tS) (jp .Kc) (jp .Kt) (bodyHJ q P1)) (cleanJ .PB))

theorem closed_progHJ (q : ℕ) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    (hP1 : P1.Closed) : (progHJ q P1).Closed :=
  ⟨closed_setupJ _ _ _, K1.Rot.closed_nLoop _ _ _ _ ⟨closed_mkPowJ _ _ _ _, closed_moveJ hP1,
      WP.W9comp.closed_liftRegs _ (closed_dropF _)⟩, closed_cleanJ _⟩

end Programs

/-! ## Index identities -/

theorem hj_len {q e t j A G B : ℕ} (hj : j < t) (ht : t ≤ e) :
    A * q ^ e * G * q ^ e * B =
      A * q ^ j * q * (G * q ^ e) * (B * q ^ (e - t) * q ^ (t - (j + 1))) := by
  have h1 : q ^ j * q * (q ^ (e - t) * q ^ (t - (j + 1))) = q ^ e := by
    rw [← pow_succ, ← pow_add, ← pow_add]
    congr 1
    omega
  calc A * q ^ e * G * q ^ e * B
      = A * (q ^ j * q * (q ^ (e - t) * q ^ (t - (j + 1)))) * G * q ^ e * B := by rw [h1]
    _ = A * q ^ j * q * (G * q ^ e) * (B * q ^ (e - t) * q ^ (t - (j + 1))) := by ring

theorem hj_n2 {q e t j B : ℕ} (hj : j < t) (ht : t ≤ e) :
    B * q ^ (e - t) * q ^ (t - (j + 1)) = q ^ (e - 1 - j) * B := by
  rw [mul_assoc, ← pow_add, show e - t + (t - (j + 1)) = e - 1 - j by omega, mul_comm]

theorem permByInv_id_j {α : Type} [Inhabited α] (v : List α) : permByInv (fun y => y) v = v := by
  unfold permByInv
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getElem?_eq_getElem h2]

/-! ## One iteration and the loop -/

section Runs

variable {E1 : Type} [DecidableEq E1] {R1 : Type}

/-- **One iteration of the high join.** `N2 := b0·q^r` (`b0` on `PB`, `r` on `Kc`), the kernel
move from `arrSyms v` to `arrSyms w` (counters `n1` on `N1`, `b0·q^r` on `N2`), drop `N2`. -/
theorem runs_bodyHJ {q : ℕ} (hq : 1 ≤ q) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    {T1 : ℕ} (U : KJ E1 → List Sym) (v w : List (List Bool)) (rest : List Sym) (n1 b0 r : ℕ)
    (rP rK r2 : List Sym) (hrP : TermOK rP) (hrK : TermOK rK)
    (hK : ∀ S' : KLoc (Fin 4) E1 → List Sym, S' (.inl 0) = arrSyms v ++ rest →
      S' (.inl 2) = natSyms n1 ++ r2 →
      S' (.inl 3) = natSyms (b0 * q ^ r) ++ Sym.mark :: U (jp .N2) →
      Runs P1 S' (Function.update (Function.update S' (.inl 0) rest) (.inl 1)
        (arrSyms w ++ S' (.inl 1))) (fun _ => True) T1)
    (hU0 : U (.inl 0) = arrSyms v ++ rest) (hUP : U (jp .PB) = natSyms b0 ++ rP)
    (hUK : U (jp .Kc) = natSyms r ++ rK) (hUN1 : U (jp .N1) = natSyms n1 ++ r2) :
    Runs (bodyHJ q P1) U (Function.update U (.inl 0) (arrSyms w ++ rest)) (fun _ => True)
      (costP q b0 r + ((1 + (T1 + (1 + ((3 * (arrSyms w).length + 2) +
        (3 * (arrSyms w).reverse.length + 2))))) + (2 * bitLen (b0 * q ^ r) + 2))) := by
  have c1 := runs_mkPowJ (R1 := R1) hq (src := jp .PB) (ns := jp .Kc) (Y := .N2) (by simp)
    (by simp) (by simp) b0 r rP rK U hrP hrK hUP hUK
  set U1 : KJ E1 → List Sym :=
    Function.update U (jp .N2) (natSyms (b0 * q ^ r) ++ Sym.mark :: U (jp .N2)) with hU1
  have c2 := runs_moveJ (P1 := P1) U1 v w rest r2 (Sym.mark :: U (jp .N2)) n1 (b0 * q ^ r) hK
    (by simp [hU1, hU0]) (by simp [hU1, hUN1]) (by simp [hU1])
  have c3 := runs_lift (lN R1) (runs_dropF (jp .N2) (b0 * q ^ r) Sym.mark (U (jp .N2))
    (Function.update U1 (.inl 0) (arrSyms w ++ rest)) rfl (by simp [hU1]))
  have e3 : Function.update (Function.update U1 (.inl 0) (arrSyms w ++ rest)) (jp .N2)
      (U (jp .N2)) = Function.update U (.inl 0) (arrSyms w ++ rest) := by
    funext k
    by_cases hk : k = jp .N2
    · subst hk
      simp
    · simp [hU1, hk, Function.update_apply]
  exact WP.W9comp.runs_seq c1 (WP.W9comp.runs_seq c2 (WP.W9comp.runs_congr c3 e3))

/-- Per-iteration cost bound of the high join (`V` bounds the volume of every array). -/
def taHJ (q C1 V b0 t j : ℕ) : ℕ :=
  costP q b0 (t - (j + 1)) + ((1 + (C1 * (V + 1) + (1 + ((3 * V + 2) + (3 * V + 2))))) +
    (2 * bitLen (b0 * q ^ (t - (j + 1))) + 2))

/-- **The loop of the high join**: `t` iterations take the array from `v` to
`permByInv (hjComp q e G B t) v`. -/
theorem runs_loopHJ {q : ℕ} (hq : 2 ≤ q) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    {C1 : ℕ}
    (hs1 : ∀ (N0 N1 N2 : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
      (S : KLoc (Fin 4) E1 → List Sym), v.length = N0 * q * N1 * N2 → BlkTerm rest →
      TermOK r2 → TermOK r3 → S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms N1 ++ r2 →
      S (.inl 3) = natSyms N2 ++ r3 →
      Runs P1 S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (permByInv (moveLeftMixInv q N1 N2) v) ++ S (.inl 1))) (fun _ => True)
        (C1 * (vol v + 1)))
    (A e G B w : ℕ) (v : List (List Bool)) (rest : List Sym) (S : KJ E1 → List Sym)
    (he : c6T q e ≤ e) (hlen : v.length = A * q ^ e * G * q ^ e * B)
    (hw : ∀ p ∈ v, p.length = w) (hrest : BlkTerm rest) (hS0 : S (.inl 0) = arrSyms v ++ rest) :
    Runs (K1.Rot.nLoop (lWJ R1) (jp .tS) (jp .Kc) (jp .Kt) (bodyHJ q P1))
      (stA S (c6T q e) (e - c6T q e) (G * q ^ e) .PB (B * q ^ (e - c6T q e)))
      (Function.update (stA S (c6T q e) (e - c6T q e) (G * q ^ e) .PB (B * q ^ (e - c6T q e)))
        (.inl 0) (arrSyms (permByInv (hjComp q e G B (c6T q e)) v) ++ rest))
      (fun _ => True)
      (((List.range (c6T q e)).map (taHJ q C1 (vol v) (B * q ^ (e - c6T q e)) (c6T q e))).sum +
        16 * c6T q e + 13 * bitLen (c6T q e) + 12) := by
  have hq1 : 1 ≤ q := by omega
  set t := c6T q e with ht
  set b0 := B * q ^ (e - t) with hb0
  set SA := stA S t (e - t) (G * q ^ e) .PB b0 with hSA
  have hSA0 : SA (.inl 0) = arrSyms v ++ rest := by simp [hSA, stA, hS0]
  set St : ℕ → KJ E1 → List Sym := fun j =>
    Function.update SA (.inl 0) (arrSyms (permByInv (hjComp q e G B j) v) ++ rest) with hSt
  have hSt0 : St 0 = SA := by
    simp only [hSt]
    rw [show hjComp q e G B 0 = fun y => y from rfl, permByInv_id_j, ← hSA0,
      Function.update_eq_self]
  have hact : ∀ j, j < t → Runs (bodyHJ q P1)
      (Function.update (St j) (jp .Kc) (natSyms (t - (j + 1)) ++ Sym.mark :: St 0 (jp .Kc)))
      (Function.update (St (j + 1)) (jp .Kc)
        (natSyms (t - (j + 1)) ++ Sym.mark :: St 0 (jp .Kc)))
      (fun _ => True) (taHJ q C1 (vol v) b0 t j) := by
    intro j hj
    have hlenj : (permByInv (hjComp q e G B j) v).length =
        A * q ^ j * q * (G * q ^ e) * (b0 * q ^ (t - (j + 1))) := by
      rw [AppC.C6Aux.length_permByInv, hlen, hb0]
      exact hj_len hj he
    have hwj : permByInv (moveLeftMixInv q (G * q ^ e) (b0 * q ^ (t - (j + 1))))
        (permByInv (hjComp q e G B j) v) = permByInv (hjComp q e G B (j + 1)) v := by
      rw [permByInv_hjComp_succ (by omega) v hlen, hb0, hj_n2 hj he, mul_comm G]
      rfl
    have hbody := runs_bodyHJ (R1 := R1) hq1 (P1 := P1)
      (T1 := C1 * (vol (permByInv (hjComp q e G B j) v) + 1))
      (Function.update (St j) (jp .Kc) (natSyms (t - (j + 1)) ++ Sym.mark :: St 0 (jp .Kc)))
      (permByInv (hjComp q e G B j) v) (permByInv (hjComp q e G B (j + 1)) v) rest
      (G * q ^ e) b0 (t - (j + 1)) (Sym.mark :: S (jp .PB)) (Sym.mark :: St 0 (jp .Kc))
      (Sym.mark :: S (jp .N1)) (termOK_mark _) (termOK_mark _)
      (fun S' h0 h2 h3 => by
        have h := hs1 (A * q ^ j) (G * q ^ e) (b0 * q ^ (t - (j + 1)))
          (permByInv (hjComp q e G B j) v) rest (Sym.mark :: S (jp .N1)) _ S' hlenj hrest
          (termOK_mark _) (termOK_mark _) h0 h2 h3
        rwa [hwj] at h)
      (by simp [hSt]) (by simp [hSt, hSA, stA]) (by simp) (by simp [hSt, hSA, stA])
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hbody ?_) (fun _ _ => trivial) ?_
    · simp only [hSt]
      rw [Function.update_comm (show (jp .Kc : KJ E1) ≠ .inl 0 by simp), Function.update_idem]
    · have h1 := C6BitMoveAux.vol_permByInv_le hw (hjComp q e G B j)
      have h2 := C6BitMoveAux.vol_permByInv_le hw (hjComp q e G B (j + 1))
      have h3 : C1 * (vol (permByInv (hjComp q e G B j) v) + 1) ≤ C1 * (vol v + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (arrSyms (permByInv (hjComp q e G B (j + 1)) v)).length =
          vol (permByInv (hjComp q e G B (j + 1)) v) := rfl
      simp only [taHJ, List.length_reverse]
      omega
  have hloop := K1.Rot.runs_nLoop (lWJ R1) (ns := jp .tS) (Kc := jp .Kc) (t := jp .Kt)
    (by simp) (by simp) (by simp) (bodyHJ q P1) St t (Sym.mark :: S (jp .tS)) (termOK_mark _)
    (by simp [hSt, hSA, stA]) (by simp [hSt]) (taHJ q C1 (vol v) b0 t) hact
  rw [hSt0] at hloop
  exact hloop

/-- Cost of the high-join program. -/
def costHJ (q C1 e G B V : ℕ) : ℕ :=
  (costT q e + (costP q G e + costP q B (e - c6T q e))) +
    ((((List.range (c6T q e)).map (taHJ q C1 V (B * q ^ (e - c6T q e)) (c6T q e))).sum +
      16 * c6T q e + 13 * bitLen (c6T q e) + 12) +
      ((2 * bitLen (B * q ^ (e - c6T q e)) + 2) + ((2 * bitLen (G * q ^ e) + 2) +
        ((2 * bitLen (e - c6T q e) + 2) + (2 * bitLen (c6T q e) + 2)))))

/-- **The high-join program** takes the array from `v` to `permByInv (hjComp q e G B t) v`. -/
theorem runs_progHJ {q : ℕ} (hq : 2 ≤ q) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    {C1 : ℕ}
    (hs1 : ∀ (N0 N1 N2 : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
      (S : KLoc (Fin 4) E1 → List Sym), v.length = N0 * q * N1 * N2 → BlkTerm rest →
      TermOK r2 → TermOK r3 → S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms N1 ++ r2 →
      S (.inl 3) = natSyms N2 ++ r3 →
      Runs P1 S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (permByInv (moveLeftMixInv q N1 N2) v) ++ S (.inl 1))) (fun _ => True)
        (C1 * (vol v + 1)))
    (A e G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 : List Sym) (S : KJ E1 → List Sym)
    (he : c6T q e ≤ e) (hlen : v.length = A * q ^ e * G * q ^ e * B)
    (hw : ∀ p ∈ v, p.length = w) (hrest : BlkTerm rest) (hr1 : TermOK r1) (hr2 : TermOK r2)
    (hr3 : TermOK r3) (hS0 : S (.inl 0) = arrSyms v ++ rest)
    (hS1 : S (.inl 1) = natSyms e ++ r1) (hS2 : S (.inl 2) = natSyms G ++ r2)
    (hS3 : S (.inl 3) = natSyms B ++ r3) :
    Runs (progHJ q P1) S
      (Function.update S (.inl 0) (arrSyms (permByInv (hjComp q e G B (c6T q e)) v) ++ rest))
      (fun _ => True) (costHJ q C1 e G B (vol v)) := by
  have h1 := runs_setupHJ (R1 := R1) hq e G B r1 r2 r3 S hr1 hr2 hr3 he hS1 hS2 hS3
  have h2 := runs_loopHJ (R1 := R1) hq hs1 A e G B w v rest S he hlen hw hrest hS0
  have h3 := runs_cleanJ (R1 := R1) (Y := .PB) (by simp) (by simp) (by simp) (c6T q e)
    (e - c6T q e) (G * q ^ e) (B * q ^ (e - c6T q e)) S
    (arrSyms (permByInv (hjComp q e G B (c6T q e)) v) ++ rest)
  exact WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 h3)

end Runs

/-! ## The cost -/

/-- The constant of the high join. -/
def cHJ (q C1 : ℕ) : ℕ := 8 * tC q + 600 * K0 q + 2 * C1 + 300

theorem costHJ_le {q C1 e G B V : ℕ} (hq : 2 ≤ q) (he : 35 ≤ e) (hG : 1 ≤ G) (hB : 1 ≤ B)
    (hV : q ^ (2 * e) * G * B ≤ V) :
    costHJ q C1 e G B V ≤ cHJ q C1 * (V * (c6T q e + 1) + 1) := by
  obtain ⟨-, hte⟩ := AppC.C6Aux.c6T_lt hq he
  have ht : c6T q e ≤ e := hte.le
  have hΛ1 := budget_pos (e := e) hq hG hB
  have hV1 : 1 ≤ V := hΛ1.trans hV
  have hΛe := succ_le_budget (e := e) hq hG hB
  have pT := costT_le hq hG hB ht
  have pG : costP q G e ≤ (200 * K0 q + 15) * (q ^ (2 * e) * G * B) := by
    refine costP_le hq hG hB le_rfl ?_ ?_
    · have := G_pow_le_budget (G := G) (B := B) (n := 0) (e := e) hq hB (by omega)
      simpa using this
    · have h1 := bitLen_mul_pow_le G q e
      have h2 := mul_bitLen_le q (show e ≤ 2 * e by omega)
      omega
  have pB : costP q B (e - c6T q e) ≤ (200 * K0 q + 15) * (q ^ (2 * e) * G * B) := by
    refine costP_le hq hG hB (by omega) ?_ ?_
    · have := B_pow_le_budget (G := G) (B := B) (n := 0) (e := e) hq hG (by omega)
      simpa using this
    · have h1 := bitLen_mul_pow_le B q (e - c6T q e)
      have h2 := mul_bitLen_le q (show e - c6T q e ≤ 2 * e by omega)
      omega
  have pTa : ∀ j, j < c6T q e →
      taHJ q C1 V (B * q ^ (e - c6T q e)) (c6T q e) j ≤ (2 * C1 + 200 * K0 q + 40) * V := by
    intro j hj
    have hr : c6T q e - (j + 1) ≤ e := by omega
    have hb0 : B * q ^ (e - c6T q e) ≤ q ^ (2 * e) * G * B := B_pow_le_budget hq hG (by omega)
    have hb0r : B * q ^ (e - c6T q e) * q ^ (c6T q e - (j + 1)) ≤ q ^ (2 * e) * G * B := by
      rw [mul_assoc, ← pow_add]
      exact B_pow_le_budget hq hG (by omega)
    have hbit : bitLen (B * q ^ (e - c6T q e) * q ^ (c6T q e - (j + 1))) ≤
        2 * e * bitLen q + bitLen G + bitLen B + 2 := by
      have h1 := bitLen_mul_pow_pow_le B q (e - c6T q e) (c6T q e - (j + 1))
      have h2 := mul_bitLen_le q (show e - c6T q e + (c6T q e - (j + 1)) ≤ 2 * e by omega)
      omega
    have hcp := costP_le hq hG hB hr hb0 hbit
    have hbl := bitLen_le_self' (B * q ^ (e - c6T q e) * q ^ (c6T q e - (j + 1)))
    have hKV : K0 q * (q ^ (2 * e) * G * B) ≤ K0 q * V := Nat.mul_le_mul_left _ hV
    have hC1 : C1 ≤ C1 * V := Nat.le_mul_of_pos_right _ hV1
    unfold taHJ
    nlinarith
  have pSum := NatArith.sum_range_le (c6T q e) pTa
  have pOv := loop_overhead_le hq hG hB ht
  have pCl : (2 * bitLen (B * q ^ (e - c6T q e)) + 2) + ((2 * bitLen (G * q ^ e) + 2) +
      ((2 * bitLen (e - c6T q e) + 2) + (2 * bitLen (c6T q e) + 2))) ≤
      12 * (q ^ (2 * e) * G * B) := by
    have h1 := bitLen_le_self' (B * q ^ (e - c6T q e))
    have h2 := bitLen_le_self' (G * q ^ e)
    have h3 := bitLen_le_self' (e - c6T q e)
    have h4 := bitLen_le_self' (c6T q e)
    have h5 : B * q ^ (e - c6T q e) ≤ q ^ (2 * e) * G * B := B_pow_le_budget hq hG (by omega)
    have h6 : G * q ^ e ≤ q ^ (2 * e) * G * B := G_pow_le_budget hq hB (by omega)
    omega
  have hTV : tC q * (q ^ (2 * e) * G * B) ≤ tC q * V := Nat.mul_le_mul_left _ hV
  have hKV : K0 q * (q ^ (2 * e) * G * B) ≤ K0 q * V := Nat.mul_le_mul_left _ hV
  have hX1 : 8 * tC q + 400 * K0 q + 145 ≤ cHJ q C1 := by unfold cHJ; omega
  have hX2 : 2 * C1 + 200 * K0 q + 40 ≤ cHJ q C1 := by unfold cHJ; omega
  have step1 : costHJ q C1 e G B V ≤ (8 * tC q + 400 * K0 q + 145) * V +
      c6T q e * ((2 * C1 + 200 * K0 q + 40) * V) := by
    unfold costHJ
    generalize hΛdef : q ^ (2 * e) * G * B = Λ at pT pG pB pOv pCl hTV hKV hV
    nlinarith
  calc costHJ q C1 e G B V ≤ (8 * tC q + 400 * K0 q + 145) * V +
        c6T q e * ((2 * C1 + 200 * K0 q + 40) * V) := step1
    _ ≤ cHJ q C1 * V + c6T q e * (cHJ q C1 * V) :=
        Nat.add_le_add (Nat.mul_le_mul_right V hX1)
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right V hX2))
    _ ≤ cHJ q C1 * (V * (c6T q e + 1) + 1) := by
        have e1 : cHJ q C1 * (V * (c6T q e + 1) + 1) =
            cHJ q C1 * V + c6T q e * (cHJ q C1 * V) + cHJ q C1 := by ring
        omega

end AppC.C6JoinAux

open AppC.C6JoinAux in
/-- **Lemma A.8, the high join** (`C6HighJoinStmt`, `C6QLeaves.lean`; Lemma A.8 (`lem:transfer12`)): for
every `q ≥ 2` the leaf contract holds. The program `progHJ q P1` uses only proved kernels:
`K1Digit.k1MoveDigitMix_holds q false` (the `t` left moves), the threshold kernel `tKerP`
(`C6TArith.lean`) and the `NatArith` counter library. Cost constant `cHJ q C1`. -/
theorem c6HighJoin_holds (q : ℕ) (hq : 2 ≤ q) : C6HighJoinStmt q := by
  obtain ⟨C1, hK⟩ := K1Digit.k1MoveDigitMix_holds q false
  obtain ⟨E1, _, _, R1, P1, hR1a, hR1b, hP1, hs1⟩ := hK ()
  have := hR1a
  have := hR1b
  refine ⟨cHJ q C1, fun _ => ⟨EJ E1, inferInstance, inferInstance, RJ R1, progHJ q P1,
    inferInstance, inferInstance, closed_progHJ q hP1, ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he hA hG hB hlen hw hrest hr1 hr2 hr3 _ hS0 hS1 hS2 hS3 _
  obtain ⟨-, hte⟩ := AppC.C6Aux.c6T_lt hq he
  have h := runs_progHJ (R1 := R1) hq (C1 := C1) hs1 A e G B w v rest r1 r2 r3 S hte.le hlen hw
    hrest hr1 hr2 hr3 hS0 hS1 hS2 hS3
  have hperm : permByInv (hjComp q e G B (c6T q e)) v =
      permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v :=
    AppC.C6Aux.permByInv_congr v (fun y hy =>
      (c6HJInv_eq_hjComp (A := A) (by omega) hte.le (by rw [← hlen]; exact hy)).symm)
  rw [hperm] at h
  exact WP.W9comp.runs_mono h (fun _ _ => trivial)
    (costHJ_le hq he hG hB (budget_le_vol_hj hA hlen))

end SubNLogN.Machine
