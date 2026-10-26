/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanCoef

/-!
# Layer driver phase scan: the record exponent (`Machine/Layer/DrvPhaseScanAddr.lean`)

**Scope (honest summary).** The program `addrProg` that, from the counter `y = x / S` (on `Y`),
pushes the tag `eoTag ((c + selCount S K ρ D x) mod 4) (o = 1)` on `Est` (`runs_addrProg`; no
`sorry`). It scans the bits of `y` (moved to `Y2` and back) with the counters `T` (positions to
the next selected bit, from `ρ`, reset to `K - 1`), `Jc` (selected positions left, from `D`) and
the count `Cnt` (a tag, from `c mod 4`), i.e. it runs `selRun` (`DrvPhaseScanMath.lean`). Also
the generic pieces `runs_peek_ite` (a register test after a peek) and `runs_copyBlock`.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine Computability

/-! ## Generic pieces -/

/-- **A test on the top of a stack**: peek `k`, then branch on "the top is a bit". -/
theorem runs_peek_ite (k : PL) (P Q : Prog PL (fun _ => Sym) PReg) (S S' : PL → List Sym)
    (T : ℕ) (hP : optIsBit (S k).head? = true → Runs P S S' (fun _ => True) T)
    (hQ : optIsBit (S k).head? = false → Runs Q S S' (fun _ => True) T) :
    Runs (.seq (wk (peekR k)) (.ite (fun v => optIsBit v.1) P Q)) S S' (fun _ => True)
      (T + 2) := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  have e1 : Eval [] (wk (peekR k)) ⟨v, stk⟩ ⟨((stk k).head?, v.2), stk⟩ 1 :=
    Eval.peek [] k _ v stk
  by_cases hb : optIsBit (stk k).head? = true
  · obtain ⟨s', t, e, hs', ht⟩ := hP hb ⟨((stk k).head?, v.2), stk⟩ rfl
    exact ⟨s', 1 + (t + 1), Eval.seq e1 (Eval.ite_true hb e), hs', by omega⟩
  · have hb' : optIsBit (stk k).head? = false := by simpa using hb
    obtain ⟨s', t, e, hs', ht⟩ := hQ hb' ⟨((stk k).head?, v.2), stk⟩ rfl
    exact ⟨s', 1 + (t + 1), Eval.seq e1 (Eval.ite_false hb' e), hs', by omega⟩

theorem closed_peek_ite (k : PL) {P Q : Prog PL (fun _ => Sym) PReg} (hP : P.Closed)
    (hQ : Q.Closed) : (Prog.seq (wk (peekR k)) (.ite (fun v => optIsBit v.1) P Q)).Closed :=
  ⟨K1.Rot.closed_peekR_lift _ _, hP, hQ⟩

theorem runs_copyBlock {src dst t : PL} (h1 : src ≠ dst) (h2 : src ≠ t) (h3 : dst ≠ t)
    (blk : List Bool) (rest : List Sym) (S : PL → List Sym) (hrest : TermOK rest)
    (hS : S src = blk.map Sym.bit ++ rest) :
    Runs (wk (copyBlock src dst t)) S (Function.update S dst (blk.map Sym.bit ++ S dst))
      (fun _ => True) (7 * blk.length + 7) :=
  K1.runs_liftRegs_of_eval pl fun v =>
    ⟨_, _, copyBlock_eval h1 h2 h3 [] v blk rest S hrest hS, le_rfl⟩

/-- `natSyms` followed by a guard is a valid terminator context. -/
theorem termOK_mark (L : List Sym) : TermOK (Sym.mark :: L) := TermOK.cons rfl _

theorem head_natSyms_mark (n : ℕ) (L : List Sym) :
    optIsBit (natSyms n ++ Sym.mark :: L).head? = decide (0 < n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [natSyms, encodeNat_zero, optIsBit]
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat n = b :: l := by
      cases h : encodeNat n with
      | nil => rw [encodeNat_eq_nil_iff] at h; omega
      | cons b l => exact ⟨b, l, rfl⟩
    simp [natSyms, hbl, optIsBit, hn]

/-! ## Scan states -/

/-- Stacks of the exponent phase: `Y`, `Y2`, `T`, `Jc`, `Cnt`, `Est` set, the rest from `B`. -/
def aS (B : PL → List Sym) (Y Y2 T J C E : List Sym) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update B kY Y) kY2 Y2) kT T) kJc J) kCnt C) kEst E

section AS

variable (B : PL → List Sym) (Y Y2 T J C E : List Sym)

@[simp] theorem aS_Y : aS B Y Y2 T J C E kY = Y := by simp [aS]
@[simp] theorem aS_Y2 : aS B Y Y2 T J C E kY2 = Y2 := by simp [aS]
@[simp] theorem aS_T : aS B Y Y2 T J C E kT = T := by simp [aS]
@[simp] theorem aS_J : aS B Y Y2 T J C E kJc = J := by simp [aS]
@[simp] theorem aS_C : aS B Y Y2 T J C E kCnt = C := by simp [aS]
@[simp] theorem aS_E : aS B Y Y2 T J C E kEst = E := by simp [aS]

theorem aS_apply_ne (k : PL) (h1 : k ≠ kY) (h2 : k ≠ kY2) (h3 : k ≠ kT) (h4 : k ≠ kJc)
    (h5 : k ≠ kCnt) (h6 : k ≠ kEst) : aS B Y Y2 T J C E k = B k := by
  simp [aS, Function.update_of_ne, h1, h2, h3, h4, h5, h6]

@[simp] theorem aS_PR : aS B Y Y2 T J C E kPR = B kPR := by apply aS_apply_ne <;> simp
@[simp] theorem aS_PD : aS B Y Y2 T J C E kPD = B kPD := by apply aS_apply_ne <;> simp
@[simp] theorem aS_PK : aS B Y Y2 T J C E kPK = B kPK := by apply aS_apply_ne <;> simp
@[simp] theorem aS_PC : aS B Y Y2 T J C E kPC = B kPC := by apply aS_apply_ne <;> simp
@[simp] theorem aS_PO : aS B Y Y2 T J C E kPO = B kPO := by apply aS_apply_ne <;> simp
@[simp] theorem aS_Tm : aS B Y Y2 T J C E kTm = B kTm := by apply aS_apply_ne <;> simp

@[simp] theorem aS_upd_Y (x : List Sym) :
    Function.update (aS B Y Y2 T J C E) kY x = aS B x Y2 T J C E := by
  funext k'; simp only [aS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem aS_upd_Y2 (x : List Sym) :
    Function.update (aS B Y Y2 T J C E) kY2 x = aS B Y x T J C E := by
  funext k'; simp only [aS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem aS_upd_T (x : List Sym) :
    Function.update (aS B Y Y2 T J C E) kT x = aS B Y Y2 x J C E := by
  funext k'; simp only [aS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem aS_upd_J (x : List Sym) :
    Function.update (aS B Y Y2 T J C E) kJc x = aS B Y Y2 T x C E := by
  funext k'; simp only [aS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem aS_upd_C (x : List Sym) :
    Function.update (aS B Y Y2 T J C E) kCnt x = aS B Y Y2 T J x E := by
  funext k'; simp only [aS, Function.update_apply]; split_ifs <;> simp_all
@[simp] theorem aS_upd_E (x : List Sym) :
    Function.update (aS B Y Y2 T J C E) kEst x = aS B Y Y2 T J C x := by
  funext k'; simp only [aS, Function.update_apply]; split_ifs <;> simp_all

end AS

/-! ## The scan body -/

/-- The count tag (the count mod 4). -/
def cntTag (n : ℕ) : Fin 16 := ⟨n % 4, by omega⟩

/-- Scan state: the unread bits `bs` of `y` on `Y`, the read bits `acc` (reversed) on `Y2`, the
counters `T = st.1`, `Jc = st.2.1` and the count `st.2.2` (as a tag on `Cnt`). -/
def scS (B : PL → List Sym) (Y0 Y20 T0 J0 C0 E : List Sym) (bs acc : List Bool)
    (st : ℕ × ℕ × ℕ) : PL → List Sym :=
  aS B (bs.map Sym.bit ++ .mark :: Y0) (acc.map Sym.bit ++ .mark :: Y20)
    (natSyms st.1 ++ .mark :: T0) (natSyms st.2.1 ++ .mark :: J0) (.tag (cntTag st.2.2) :: C0) E

theorem scS_T (B : PL → List Sym) (Y0 Y20 T0 J0 C0 E : List Sym) (bs acc : List Bool)
    (st : ℕ × ℕ × ℕ) : scS B Y0 Y20 T0 J0 C0 E bs acc st kT = natSyms st.1 ++ .mark :: T0 := by
  simp [scS]

theorem scS_J (B : PL → List Sym) (Y0 Y20 T0 J0 C0 E : List Sym) (bs acc : List Bool)
    (st : ℕ × ℕ × ℕ) : scS B Y0 Y20 T0 J0 C0 E bs acc st kJc = natSyms st.2.1 ++ .mark :: J0 := by
  simp [scS]

theorem runs_skip (S : PL → List Sym) :
    Runs (skip : Prog PL (fun _ => Sym) PReg) S S (fun _ => True) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, skip_eval [] _, ⟨rfl, trivial⟩, le_rfl⟩

/-- Count the bit on top of `Y2` into the tag on `Cnt`. -/
def cntInc : Prog PL (fun _ => Sym) PReg :=
  .seq (.peek kY2 fun v o => (v.1, o, v.2.2))
  (.seq (.pop kCnt fun v o => (v.1, v.2.1, o, v.2.2.2))
    (.push kCnt fun v =>
      .tag (cntTag (if symBit v.2.1 then tagN v.2.2.1 + 1 else tagN v.2.2.1))))

theorem closed_cntInc : cntInc.Closed := by
  simp [cntInc, Prog.Closed, Prog.FreeBelow]

theorem runs_cntInc (S : PL → List Sym) (b : Bool) (L : List Sym) (n : ℕ) (C0 : List Sym)
    (hY : S kY2 = .bit b :: L) (hC : S kCnt = .tag (cntTag n) :: C0) :
    Runs cntInc S (Function.update S kCnt (.tag (cntTag (if b then n + 1 else n)) :: C0))
      (fun _ => True) 3 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  have e1 := Eval.peek [] kY2 (fun (v : PReg) o => (v.1, o, v.2.2)) v stk
  have e2 := Eval.pop [] kCnt (fun (v : PReg) o => (v.1, v.2.1, o, v.2.2.2))
    (v.1, (stk kY2).head?, v.2.2) stk
  have e3 := Eval.push [] kCnt (fun v : PReg =>
      Sym.tag (cntTag (if symBit v.2.1 then tagN v.2.2.1 + 1 else tagN v.2.2.1)))
    (v.1, (stk kY2).head?, (stk kCnt).head?, v.2.2.2) (Function.update stk kCnt (stk kCnt).tail)
  refine ⟨_, 3, Eval.seq e1 (Eval.seq e2 e3), ⟨?_, trivial⟩, le_rfl⟩
  simp only [Function.update_idem, Function.update_self]
  rw [hY, hC]
  simp only [List.head?_cons, List.tail_cons]
  congr 3
  apply Fin.ext
  cases b <;> simp [cntTag, tagN, symBit] <;> omega

/-- The branch at a selected position (`T = 0`): count the bit if `Jc > 0` (and decrement `Jc`),
then reset `T` to `K - 1`. -/
def selBranch : Prog PL (fun _ => Sym) PReg :=
  .seq (.seq (wk (peekR kJc)) (.ite (fun v => optIsBit v.1) (.seq cntInc (wk (dec kJc kTm)))
    skip)) (.seq (wk (copyBlock kPK kT kTm)) (wk (dec kT kTm)))

theorem closed_selBranch : selBranch.Closed :=
  ⟨⟨K1.Rot.closed_peekR_lift _ _, ⟨closed_cntInc, K1.Rot.closed_dec_lift _ _ _⟩,
    by simp [skip, Prog.Closed, Prog.FreeBelow]⟩,
    K1.Rot.closed_copyBlock_lift _ _ _ _, K1.Rot.closed_dec_lift _ _ _⟩

/-- One scan step. -/
def scanBody : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (moveOne kY kY2))
    (.seq (wk (peekR kT)) (.ite (fun v => optIsBit v.1) (wk (dec kT kTm)) selBranch))

theorem closed_scanBody : scanBody.Closed :=
  ⟨closed_moveOne _ _, K1.Rot.closed_peekR_lift _ _, K1.Rot.closed_dec_lift _ _ _,
    closed_selBranch⟩

theorem zerosLead_le_bitLen {n M : ℕ} (h : n ≤ M) : zerosLead (encodeNat n) ≤ bitLen M :=
  (zerosLead_le_length _).trans (TMFw.W3s.bitLen_mono h)

theorem runs_decN {k t : PL} (hkt : k ≠ t) (n M : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) (rest : List Sym)
    (S : PL → List Sym) (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (wk (dec k t)) S (Function.update S k (natSyms (n - 1) ++ rest)) (fun _ => True)
      (6 * bitLen M + 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := K1.runs_wk_dec pl hkt m rest S hrest hS
  simp only [Nat.add_sub_cancel]
  exact WP.W9comp.runs_mono h (fun _ h => h) (by have := zerosLead_le_bitLen hM; omega)

theorem runs_selBranch (B : PL → List Sym) (K : ℕ) (hK : 1 ≤ K) (rK : List Sym)
    (hrK : TermOK rK) (hPK : B kPK = natSyms K ++ rK) (Y0 Y20 T0 J0 C0 E : List Sym)
    (bs acc : List Bool) (b : Bool) (J n M : ℕ) (hJM : J ≤ M) (hKM : K ≤ M) :
    Runs selBranch (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J, n))
      (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc)
        (K - 1, J - 1, if 0 < J ∧ b = true then n + 1 else n))
      (fun _ => True) (19 * bitLen M + 28) := by
  set n' := if 0 < J ∧ b = true then n + 1 else n with hn'
  have p1 : Runs (.seq (wk (peekR kJc)) (.ite (fun v => optIsBit v.1)
      (.seq cntInc (wk (dec kJc kTm))) skip))
      (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J, n))
      (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J - 1, n'))
      (fun _ => True) (6 * bitLen M + 11 + 2) := by
    apply runs_peek_ite
    · intro hb
      have hJ : 0 < J := by rw [scS_J, head_natSyms_mark] at hb; simpa using hb
      have c1 := runs_cntInc (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J, n)) b
        (acc.map Sym.bit ++ .mark :: Y20) n C0 (by simp [scS]) (by simp [scS])
      have c2 := runs_decN (k := kJc) (t := kTm) (by simp) J M hJ hJM (.mark :: J0)
        (Function.update (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J, n)) kCnt
          (.tag (cntTag (if b then n + 1 else n)) :: C0)) (termOK_mark _) (by simp [scS])
      refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_)
        (fun _ h => h) (by omega)
      simp [scS, hn', hJ]
    · intro hb
      have hJ : J = 0 := by
        rw [scS_J, head_natSyms_mark] at hb
        have : ¬ 0 < J := by simpa using hb
        omega
      subst hJ
      exact WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_skip _) (by simp [scS, hn']))
        (fun _ h => h) (by omega)
  have p2 := runs_copyBlock (src := kPK) (dst := kT) (t := kTm) (by simp) (by simp) (by simp)
    (encodeNat K) rK (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J - 1, n')) hrK
    (by simp [scS, hPK, natSyms])
  have p3 := runs_decN (k := kT) (t := kTm) (by simp) K M hK hKM (.mark :: T0)
    (Function.update (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J - 1, n')) kT
      ((encodeNat K).map Sym.bit ++ scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (0, J - 1, n') kT))
    (termOK_mark _) (by simp [scS, natSyms, encodeNat_zero])
  have hKl : (encodeNat K).length ≤ bitLen M := TMFw.W3s.bitLen_mono hKM
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq p1
    (WP.W9comp.runs_seq p2 p3)) ?_) (fun _ h => h) (by omega)
  simp [scS]

theorem runs_scanBody (B : PL → List Sym) (K : ℕ) (hK : 1 ≤ K) (rK : List Sym)
    (hrK : TermOK rK) (hPK : B kPK = natSyms K ++ rK) (Y0 Y20 T0 J0 C0 E : List Sym)
    (bs acc : List Bool) (b : Bool) (st : ℕ × ℕ × ℕ) (M : ℕ) (hTM : st.1 ≤ M)
    (hJM : st.2.1 ≤ M) (hKM : K ≤ M) :
    Runs scanBody (scS B Y0 Y20 T0 J0 C0 E (b :: bs) acc st)
      (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (selStep K st b)) (fun _ => True)
      (19 * bitLen M + 33) := by
  obtain ⟨T, J, n⟩ := st
  simp only at hTM hJM
  have m1 : Runs (wk (moveOne kY kY2)) (scS B Y0 Y20 T0 J0 C0 E (b :: bs) acc (T, J, n))
      (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (T, J, n)) (fun _ => True) 2 :=
    WP.W9comp.runs_congr (runs_moveOne (src := kY) (dst := kY2) (by simp)
      (scS B Y0 Y20 T0 J0 C0 E (b :: bs) acc (T, J, n)) (.bit b)
      (bs.map Sym.bit ++ .mark :: Y0) (by simp [scS])) (by simp [scS])
  have m2 : Runs (.seq (wk (peekR kT)) (.ite (fun v => optIsBit v.1) (wk (dec kT kTm))
      selBranch)) (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (T, J, n))
      (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (selStep K (T, J, n) b)) (fun _ => True)
      (19 * bitLen M + 29 + 2) := by
    apply runs_peek_ite
    · intro hb
      have hT : 0 < T := by rw [scS_T, head_natSyms_mark] at hb; simpa using hb
      have h := runs_decN (k := kT) (t := kTm) (by simp) T M hT hTM (.mark :: T0)
        (scS B Y0 Y20 T0 J0 C0 E bs (b :: acc) (T, J, n)) (termOK_mark _) (by simp [scS])
      refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ h => h) (by omega)
      simp [scS, selStep, show T ≠ 0 by omega]
    · intro hb
      have hT : T = 0 := by
        rw [scS_T, head_natSyms_mark] at hb
        have : ¬ 0 < T := by simpa using hb
        omega
      subst hT
      have h := runs_selBranch B K hK rK hrK hPK Y0 Y20 T0 J0 C0 E bs acc b J n M hJM hKM
      refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ h => h) (by omega)
      simp [selStep]
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq m1 m2) (fun _ h => h) (by omega)

/-! ## The scan loop -/

theorem selRun_le (K M : ℕ) (hKM : K ≤ M) : ∀ (bs : List Bool) (st : ℕ × ℕ × ℕ),
    st.1 ≤ M → st.2.1 ≤ M → (selRun K st bs).1 ≤ M ∧ (selRun K st bs).2.1 ≤ M
  | [], st, h1, h2 => ⟨h1, h2⟩
  | b :: bs, st, h1, h2 => by
    have hs : selRun K st (b :: bs) = selRun K (selStep K st b) bs := rfl
    rw [hs]
    apply selRun_le K M hKM bs
    · unfold selStep; split_ifs <;> simp <;> omega
    · unfold selStep; split_ifs <;> simp <;> omega

theorem selRun_snoc (K : ℕ) (st : ℕ × ℕ × ℕ) (acc : List Bool) (a : Bool) :
    selRun K st (a :: acc).reverse = selStep K (selRun K st acc.reverse) a := by
  simp [selRun, List.foldl_append]

theorem foldG_cons {α : Type} : ∀ (vs : List α) (x : ℕ) (acc : List α),
    K1.foldG (fun _ a acc => a :: acc) x vs acc = vs.reverse ++ acc
  | [], _, _ => rfl
  | a :: vs, x, acc => by
    simp only [K1.foldG, foldG_cons vs (x + 1) (a :: acc), List.reverse_cons, List.append_assoc,
      List.singleton_append]

theorem loopB_const {α : Type} (c : ℕ) : ∀ (vs : List α) (x : ℕ),
    K1.loopB (fun _ _ => c) x vs = vs.length * (c + 1) + 1
  | [], _ => by simp [K1.loopB]
  | a :: vs, x => by
    simp only [K1.loopB, loopB_const c vs (x + 1), List.length_cons]
    ring

/-- The scan loop over the bits of `y`. -/
def scanLoop : Prog PL (fun _ => Sym) PReg :=
  .loop (fun v => optIsBit v.1) (.seq scanBody (wk (peekR kY)))

theorem closed_scanLoop : scanLoop.Closed := ⟨closed_scanBody, K1.Rot.closed_peekR_lift _ _⟩

theorem triple_scanLoop (B : PL → List Sym) (K : ℕ) (hK : 1 ≤ K) (rK : List Sym)
    (hrK : TermOK rK) (hPK : B kPK = natSyms K ++ rK) (Y0 Y20 T0 J0 C0 E : List Sym)
    (st0 : ℕ × ℕ × ℕ) (M : ℕ) (hTM : st0.1 ≤ M) (hJM : st0.2.1 ≤ M) (hKM : K ≤ M)
    (bs : List Bool) :
    Triple [] (fun s => s.stk = scS B Y0 Y20 T0 J0 C0 E bs [] st0 ∧
        s.var.1 = (bs.map Sym.bit ++ .mark :: Y0).head?) scanLoop
      (fun s => s.stk = scS B Y0 Y20 T0 J0 C0 E [] bs.reverse (selRun K st0 bs))
      (bs.length * (19 * bitLen M + 35) + 1) := by
  have h := K1.triple_loop_list (c := fun v : PReg => optIsBit v.1)
    (body := .seq scanBody (wk (peekR kY)))
    (fun _ vs acc => scS B Y0 Y20 T0 J0 C0 E vs acc (selRun K st0 acc.reverse))
    (fun vs (r : PReg) => r.1 = (vs.map Sym.bit ++ .mark :: Y0).head?)
    (fun _ a acc => a :: acc) (fun _ _ => 19 * bitLen M + 34) (fun _ _ => True)
    (fun _ _ _ _ => trivial)
    (fun r hr => by show optIsBit r.1 = false; rw [hr]; rfl)
    (fun a vs r hr => by show optIsBit r.1 = true; rw [hr]; rfl)
    (fun x a vs acc _ => by
      have hb := selRun_le K M hKM acc.reverse st0 hTM hJM
      have hs := runs_scanBody B K hK rK hrK hPK Y0 Y20 T0 J0 C0 E vs acc a
        (selRun K st0 acc.reverse) M hb.1 hb.2 hKM
      rw [← selRun_snoc] at hs
      have hp := K1.triple_peek_fst (τ := Option Sym × Option Sym × Option Sym) kY
        (scS B Y0 Y20 T0 J0 C0 E vs (a :: acc) (selRun K st0 (a :: acc).reverse))
      refine Triple.conseq (K1.runs_seq_triple hs hp) (fun s hs => hs.1)
        (fun s hs => ⟨hs.1, ?_⟩) le_rfl
      rw [hs.2]
      simp [scS])
    bs 0 [] trivial
  refine Triple.conseq h (fun s hs => ⟨?_, hs.2⟩) (fun s hs => ?_) ?_
  · rw [hs.1]
    simp [selRun]
  · rw [hs, foldG_cons, List.append_nil, List.reverse_reverse]
  · rw [loopB_const]

/-! ## Start and end of the exponent phase -/

/-- `c mod 4` from the two low bits of the counter `c` (on `pC`, restored) to `Cnt`. -/
def initCnt : Prog PL (fun _ => Sym) PReg :=
  .seq (.pop kPC fun v o => (v.1, o, v.2.2))
  (.seq (.peek kPC fun v o => (o, v.2))
  (.seq (.push kPC fun v => v.2.1.getD .mark)
    (.push kCnt fun v => .tag (cntTag (if optIsBit v.2.1 then
      (symBit v.2.1).toNat + 2 * (if optIsBit v.1 then (symBit v.1).toNat else 0) else 0)))))

theorem closed_initCnt : initCnt.Closed := by
  simp [initCnt, Prog.Closed, Prog.FreeBelow]

theorem mod4_bits (c : ℕ) : c % 4 = (c.testBit 0).toNat + 2 * (c.testBit 1).toNat := by
  rw [show c.testBit 1 = (c / 2).testBit 0 by rw [Nat.testBit_div_two], Nat.testBit_zero,
    Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (c / 2) with h' | h' <;> simp [h, h'] <;> omega

theorem low2_val (c : ℕ) (P0 : List Sym) :
    (if optIsBit (natSyms c ++ .mark :: P0).head? then
      (symBit (natSyms c ++ .mark :: P0).head?).toNat +
        2 * (if optIsBit (natSyms c ++ .mark :: P0).tail.head? then
          (symBit (natSyms c ++ .mark :: P0).tail.head?).toNat else 0) else 0) = c % 4 := by
  rw [mod4_bits, ← encodeNat_getD c 0, ← encodeNat_getD c 1]
  unfold natSyms
  rcases encodeNat c with _ | ⟨b0, _ | ⟨b1, L⟩⟩
  · simp [optIsBit, symBit]
  · cases b0 <;> simp [optIsBit, symBit]
  · cases b0 <;> cases b1 <;> simp [optIsBit, symBit]

theorem runs_initCnt (S : PL → List Sym) (c : ℕ) (P0 : List Sym)
    (hC : S kPC = natSyms c ++ .mark :: P0) :
    Runs initCnt S (Function.update S kCnt (.tag (cntTag c) :: S kCnt)) (fun _ => True) 4 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  have e1 := Eval.pop [] kPC (fun (v : PReg) o => (v.1, o, v.2.2)) v stk
  have e2 := Eval.peek [] kPC (fun (v : PReg) o => (o, v.2)) (v.1, (stk kPC).head?, v.2.2)
    (Function.update stk kPC (stk kPC).tail)
  have e3 := Eval.push [] kPC (fun v : PReg => v.2.1.getD .mark)
    ((Function.update stk kPC (stk kPC).tail kPC).head?, (stk kPC).head?, v.2.2)
    (Function.update stk kPC (stk kPC).tail)
  have e4 := Eval.push [] kCnt (fun v : PReg => Sym.tag (cntTag (if optIsBit v.2.1 then
      (symBit v.2.1).toNat + 2 * (if optIsBit v.1 then (symBit v.1).toNat else 0) else 0)))
    ((Function.update stk kPC (stk kPC).tail kPC).head?, (stk kPC).head?, v.2.2)
    (Function.update (Function.update stk kPC (stk kPC).tail) kPC
      ((stk kPC).head?.getD .mark :: Function.update stk kPC (stk kPC).tail kPC))
  refine ⟨_, 4, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)), ⟨?_, trivial⟩, le_rfl⟩
  have hv : (if optIsBit (stk kPC).head? then (symBit (stk kPC).head?).toNat +
      2 * (if optIsBit (stk kPC).tail.head? then (symBit (stk kPC).tail.head?).toNat else 0)
      else 0) = c % 4 := by
    rw [hC]
    exact low2_val c P0
  have hne : (stk kPC).head?.getD .mark :: (stk kPC).tail = stk kPC := by
    rw [hC]
    cases h : natSyms c ++ Sym.mark :: P0 with
    | nil => simp at h
    | cons y l => rfl
  simp only [Function.update_self, Function.update_idem, hv, hne, Function.update_eq_self,
    Function.update_of_ne (show kCnt ≠ kPC by simp)]
  congr 3
  apply Fin.ext
  simp [cntTag]

/-- Start of the exponent phase: `T := ρ`, `Jc := D` (above guards), `Cnt := c mod 4`, guard on
`Y2`. -/
def addrInit : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (pushC kT .mark)) (.seq (wk (copyBlock kPR kT kTm)) (.seq (wk (pushC kJc .mark))
  (.seq (wk (copyBlock kPD kJc kTm)) (.seq initCnt (wk (pushC kY2 .mark))))))

theorem closed_addrInit : addrInit.Closed :=
  ⟨K1.Rot.closed_pushC_lift _ _ _, K1.Rot.closed_copyBlock_lift _ _ _ _,
    K1.Rot.closed_pushC_lift _ _ _, K1.Rot.closed_copyBlock_lift _ _ _ _, closed_initCnt,
    K1.Rot.closed_pushC_lift _ _ _⟩

/-- Push the tag `e + 4·o` of the count and of the parameter `o` on `Est`. -/
def finEst : Prog PL (fun _ => Sym) PReg :=
  .seq (.peek kCnt fun v o => (v.1, o, v.2.2)) (.seq (.peek kPO fun v o => (o, v.2))
    (.push kEst fun v => .tag (eoTag (tagN v.2.1) (optIsBit v.1))))

theorem closed_finEst : finEst.Closed := by
  simp [finEst, Prog.Closed, Prog.FreeBelow]

/-- End of the exponent phase: restore `Y`, drop the counters, push the tag, drop the count. -/
def addrFin : Prog PL (fun _ => Sym) PReg :=
  .seq (wk (moveBlock kY2 kY)) (.seq (wk (popR kY2)) (.seq (wk (K1.dropBits kT))
  (.seq (wk (K1.dropBits kJc)) (.seq finEst (wk (popR kCnt))))))

theorem closed_addrFin : addrFin.Closed :=
  ⟨closed_moveBlock_lift _ _, K1.Rot.closed_popR_lift _ _, K1.Rot.closed_dropBits_lift _ _,
    K1.Rot.closed_dropBits_lift _ _, closed_finEst, K1.Rot.closed_popR_lift _ _⟩

/-- **The exponent phase.** -/
def addrProg : Prog PL (fun _ => Sym) PReg :=
  .seq addrInit (.seq (wk (peekR kY)) (.seq scanLoop addrFin))

theorem closed_addrProg : addrProg.Closed :=
  ⟨closed_addrInit, K1.Rot.closed_peekR_lift _ _, closed_scanLoop, closed_addrFin⟩

/-! ## The whole exponent phase -/

theorem runs_finEst (S : PL → List Sym) :
    Runs finEst S (Function.update S kEst
      (.tag (eoTag (tagN (S kCnt).head?) (optIsBit (S kPO).head?)) :: S kEst)) (fun _ => True) 3 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 3, Eval.seq (Eval.peek [] kCnt _ v stk) (Eval.seq (Eval.peek [] kPO _ _ stk)
    (Eval.push [] kEst _ _ stk)), ⟨rfl, trivial⟩, le_rfl⟩

theorem eoTag_mod (n : ℕ) (o : Bool) : eoTag (n % 4) o = eoTag n o := by
  apply Fin.ext
  simp [eoTag]

theorem aS_self (S : PL → List Sym) : aS S (S kY) (S kY2) (S kT) (S kJc) (S kCnt) (S kEst) = S := by
  simp [aS]

/-- Cost bound of the exponent phase. -/
def addrCost (L bM : ℕ) : ℕ := (L + 1) * (19 * bM + 40)

theorem runs_addrFin (B : PL → List Sym) (o : ℕ) (ho : o ≤ 1) (P1 : List Sym)
    (hPO : B kPO = natSyms o ++ .mark :: P1) (Y0 Y20 T0 J0 C0 E : List Sym) (bs : List Bool)
    (st : ℕ × ℕ × ℕ) :
    Runs addrFin (scS B Y0 Y20 T0 J0 C0 E [] bs.reverse st)
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 J0 C0
        (.tag (eoTag st.2.2 (decide (o = 1))) :: E)) (fun _ => True)
      (3 * bs.length + 2 * bitLen st.1 + 2 * bitLen st.2.1 + 13) := by
  have f1 : Runs (wk (moveBlock kY2 kY)) (scS B Y0 Y20 T0 J0 C0 E [] bs.reverse st)
      (aS B (bs.map Sym.bit ++ .mark :: Y0) (.mark :: Y20) (natSyms st.1 ++ .mark :: T0)
        (natSyms st.2.1 ++ .mark :: J0) (.tag (cntTag st.2.2) :: C0) E) (fun _ => True)
      (3 * bs.length + 4) := by
    have h := runs_moveBlock (src := kY2) (dst := kY) (by simp) bs.reverse (.mark :: Y20)
      (scS B Y0 Y20 T0 J0 C0 E [] bs.reverse st) (termOK_mark _) (by simp [scS])
    rw [List.length_reverse] at h
    exact WP.W9comp.runs_congr h (by simp [scS])
  have f2 : Runs (wk (popR kY2)) (aS B (bs.map Sym.bit ++ .mark :: Y0) (.mark :: Y20)
      (natSyms st.1 ++ .mark :: T0) (natSyms st.2.1 ++ .mark :: J0) (.tag (cntTag st.2.2) :: C0) E)
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 (natSyms st.1 ++ .mark :: T0)
        (natSyms st.2.1 ++ .mark :: J0) (.tag (cntTag st.2.2) :: C0) E) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_popR pl kY2 _) (by simp)
  have f3 : Runs (wk (K1.dropBits kT)) (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20
      (natSyms st.1 ++ .mark :: T0) (natSyms st.2.1 ++ .mark :: J0) (.tag (cntTag st.2.2) :: C0) E)
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 (natSyms st.2.1 ++ .mark :: J0)
        (.tag (cntTag st.2.2) :: C0) E) (fun _ => True) (2 * bitLen st.1 + 2) :=
    WP.W9comp.runs_congr (K1.runs_wk_dropBits pl kT (encodeNat st.1) .mark T0
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 (natSyms st.1 ++ .mark :: T0)
        (natSyms st.2.1 ++ .mark :: J0) (.tag (cntTag st.2.2) :: C0) E) rfl
      (by simp [natSyms])) (by simp)
  have f4 : Runs (wk (K1.dropBits kJc)) (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0
      (natSyms st.2.1 ++ .mark :: J0) (.tag (cntTag st.2.2) :: C0) E)
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 J0 (.tag (cntTag st.2.2) :: C0) E)
      (fun _ => True) (2 * bitLen st.2.1 + 2) :=
    WP.W9comp.runs_congr (K1.runs_wk_dropBits pl kJc (encodeNat st.2.1) .mark J0
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 (natSyms st.2.1 ++ .mark :: J0)
        (.tag (cntTag st.2.2) :: C0) E) rfl (by simp [natSyms])) (by simp)
  have f5 : Runs finEst (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 J0
      (.tag (cntTag st.2.2) :: C0) E)
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 J0 (.tag (cntTag st.2.2) :: C0)
        (.tag (eoTag st.2.2 (decide (o = 1))) :: E)) (fun _ => True) 3 := by
    refine WP.W9comp.runs_congr (runs_finEst _) ?_
    have hO : optIsBit (natSyms o ++ Sym.mark :: P1).head? = decide (o = 1) := by
      rw [head_natSyms_mark]
      interval_cases o <;> rfl
    simp only [aS_C, aS_PO, aS_E, hPO, hO, aS_upd_E, List.head?_cons, tagN]
    rw [show (cntTag st.2.2).val = st.2.2 % 4 from rfl, eoTag_mod]
  have f6 : Runs (wk (popR kCnt)) (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 J0
      (.tag (cntTag st.2.2) :: C0) (.tag (eoTag st.2.2 (decide (o = 1))) :: E))
      (aS B (bs.map Sym.bit ++ .mark :: Y0) Y20 T0 J0 C0
        (.tag (eoTag st.2.2 (decide (o = 1))) :: E)) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_popR pl kCnt _) (by simp)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq f1 (WP.W9comp.runs_seq f2
    (WP.W9comp.runs_seq f3 (WP.W9comp.runs_seq f4 (WP.W9comp.runs_seq f5 f6))))) (fun _ h => h) ?_
  omega

/-- **The exponent phase, exact.** From `y` on `Y` (and the parameter counters), `addrProg`
pushes the tag `eoTag n (o = 1)` on `Est`, where `n` is the count of the scan
`selRun K (ρ, D, c)` over the bits of `y`; every other stack is restored. -/
theorem runs_addrProg (B : PL → List Sym) (K ρ D c o y : ℕ) (hK : 1 ≤ K) (ho : o ≤ 1)
    (rK rR rD P0 P1 : List Sym) (hrK : TermOK rK) (hrR : TermOK rR) (hrD : TermOK rD)
    (hPK : B kPK = natSyms K ++ rK) (hPR : B kPR = natSyms ρ ++ rR)
    (hPD : B kPD = natSyms D ++ rD) (hPC : B kPC = natSyms c ++ .mark :: P0)
    (hPO : B kPO = natSyms o ++ .mark :: P1) (Y0 Y20 T0 J0 C0 E : List Sym) :
    Runs addrProg (aS B (natSyms y ++ .mark :: Y0) Y20 T0 J0 C0 E)
      (aS B (natSyms y ++ .mark :: Y0) Y20 T0 J0 C0
        (.tag (eoTag (selRun K (ρ, D, c) (encodeNat y)).2.2 (decide (o = 1))) :: E))
      (fun _ => True) (addrCost (bitLen y) (bitLen (ρ + K + D))) := by
  set M := ρ + K + D with hM
  have hb := selRun_le K M (by omega) (encodeNat y) (ρ, D, c) (by simp; omega) (by simp; omega)
  have i1 : Runs (wk (pushC kT .mark)) (aS B (natSyms y ++ .mark :: Y0) Y20 T0 J0 C0 E)
      (aS B (natSyms y ++ .mark :: Y0) Y20 (.mark :: T0) J0 C0 E) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_pushC pl kT .mark _) (by simp)
  have i2 : Runs (wk (copyBlock kPR kT kTm))
      (aS B (natSyms y ++ .mark :: Y0) Y20 (.mark :: T0) J0 C0 E)
      (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0) J0 C0 E) (fun _ => True)
      (7 * bitLen ρ + 7) :=
    WP.W9comp.runs_congr (runs_copyBlock (src := kPR) (dst := kT) (t := kTm) (by simp)
      (by simp) (by simp) (encodeNat ρ) rR
      (aS B (natSyms y ++ .mark :: Y0) Y20 (.mark :: T0) J0 C0 E) hrR
      (by simp [hPR, natSyms])) (by simp [natSyms])
  have i3 : Runs (wk (pushC kJc .mark))
      (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0) J0 C0 E)
      (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0) (.mark :: J0) C0 E)
      (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_pushC pl kJc .mark _) (by simp)
  have i4 : Runs (wk (copyBlock kPD kJc kTm))
      (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0) (.mark :: J0) C0 E)
      (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0)
        (natSyms D ++ .mark :: J0) C0 E) (fun _ => True) (7 * bitLen D + 7) :=
    WP.W9comp.runs_congr (runs_copyBlock (src := kPD) (dst := kJc) (t := kTm) (by simp)
      (by simp) (by simp) (encodeNat D) rD
      (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0) (.mark :: J0) C0 E) hrD
      (by simp [hPD, natSyms])) (by simp [natSyms])
  have i5 : Runs initCnt (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0)
      (natSyms D ++ .mark :: J0) C0 E)
      (aS B (natSyms y ++ .mark :: Y0) Y20 (natSyms ρ ++ .mark :: T0)
        (natSyms D ++ .mark :: J0) (.tag (cntTag c) :: C0) E) (fun _ => True) 4 :=
    WP.W9comp.runs_congr (runs_initCnt _ c P0 (by simp [hPC])) (by simp)
  have i6 : Runs (wk (pushC kY2 .mark)) (aS B (natSyms y ++ .mark :: Y0) Y20
      (natSyms ρ ++ .mark :: T0) (natSyms D ++ .mark :: J0) (.tag (cntTag c) :: C0) E)
      (scS B Y0 Y20 T0 J0 C0 E (encodeNat y) [] (ρ, D, c)) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (K1.runs_wk_pushC pl kY2 .mark _) (by simp [scS, natSyms])
  have hinit : Runs addrInit (aS B (natSyms y ++ .mark :: Y0) Y20 T0 J0 C0 E)
      (scS B Y0 Y20 T0 J0 C0 E (encodeNat y) [] (ρ, D, c)) (fun _ => True)
      (7 * bitLen ρ + 7 * bitLen D + 21) :=
    WP.W9comp.runs_mono (WP.W9comp.runs_seq i1 (WP.W9comp.runs_seq i2 (WP.W9comp.runs_seq i3
      (WP.W9comp.runs_seq i4 (WP.W9comp.runs_seq i5 i6))))) (fun _ h => h) (by omega)
  have hpk := K1.triple_peek_fst (τ := Option Sym × Option Sym × Option Sym) kY
    (scS B Y0 Y20 T0 J0 C0 E (encodeNat y) [] (ρ, D, c))
  have hloop := triple_scanLoop B K hK rK hrK hPK Y0 Y20 T0 J0 C0 E (ρ, D, c) M
    (by simp; omega) (by simp; omega) (by omega) (encodeNat y)
  have hfin := runs_addrFin B o ho P1 hPO Y0 Y20 T0 J0 C0 E (encodeNat y)
    (selRun K (ρ, D, c) (encodeNat y))
  have hall := Triple.seq (Triple.post hinit fun _ h => h.1)
    (Triple.seq (Triple.post hpk fun s hs => ⟨hs.1, by rw [hs.2]; simp [scS]⟩)
      (Triple.seq hloop hfin))
  refine Triple.cost_mono (Triple.post hall fun s hs => ⟨hs.1, trivial⟩) ?_
  have hρM : bitLen ρ ≤ bitLen M := TMFw.W3s.bitLen_mono (by omega)
  have hDM : bitLen D ≤ bitLen M := TMFw.W3s.bitLen_mono (by omega)
  have hTM : bitLen (selRun K (ρ, D, c) (encodeNat y)).1 ≤ bitLen M := TMFw.W3s.bitLen_mono hb.1
  have hJM : bitLen (selRun K (ρ, D, c) (encodeNat y)).2.1 ≤ bitLen M :=
    TMFw.W3s.bitLen_mono hb.2
  have hL : (encodeNat y).length = bitLen y := rfl
  rw [hL]
  unfold addrCost
  nlinarith [hρM, hDM, hTM, hJM]

end SubNLogN.Machine.Layer.DrvPhaseScanAux
