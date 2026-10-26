/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFPass
import IntMulTM.Framework.Lib.Counter
import IntMulTM.SpecFacts

/-!
# K4-TWIDDLE part (C): one table entry per record (`Machine/FFT/TwiddleSel.lean`)

**Scope (honest summary).** Generic machine routines (any stack index type `K`, any register type
`σ` with a lens `lO : Lens σ (Option Sym)`) for the twiddle pass `TwiddlePassStmt`
(`Machine/Contracts/FFT.lean`):
* `decP`, `incP`: the binary counters `TMFw.Lib.dec` / `TMFw.Lib.inc` through the lens;
* `skipB` / `unskipB`: move `m` records of a record array to a side stack and back, counting a
  binary counter `natSyms m` down to `0`;
* `moveRecDup`: move one record to two stacks;
* `selEntry`: **one sequential scan of the table per record** (Theorem 6.5, Section 6.4):
  given the table index `m` on a counter stack, push the reversed record `m` of the table onto an
  accumulator; the table is restored, the counter consumed.
Everything is proved (no `sorry`); costs are explicit.
-/

namespace SubNLogN.Machine.FFT.TwiddleAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF

/-! ## Numbers -/

theorem natSyms_zero' : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem termOK_nil' : TermOK ([] : List Sym) := fun _ h => by cases h

theorem bitLen_le_bitLen {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n := by
  simp only [bitLen, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem optIsBit_natSyms_succ (n : ℕ) (R : List Sym) :
    optIsBit (natSyms (n + 1) ++ R).head? = true := by
  have hne : Computability.encodeNat (n + 1) ≠ [] := fun h =>
    Nat.succ_ne_zero n ((encodeNat_eq_nil_iff (n + 1)).1 h)
  obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
  simp [natSyms, hb]

/-- The counter test: the top of `natSyms j ++ R` is a bit iff `0 < j`. -/
theorem optIsBit_natSyms (j : ℕ) (R : List Sym) (hR : TermOK R) :
    optIsBit (natSyms j ++ R).head? = decide (0 < j) := by
  cases j with
  | zero => simpa [natSyms_zero'] using optIsBit_head?_of_termOK hR
  | succ n => simpa using optIsBit_natSyms_succ n R

section Lift

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- A single-register program run through the lens `lO` (same stacks, same cost). -/
theorem runs_liftS {P : Prog K (fun _ => Sym) (Option Sym)} {S S' : K → List Sym}
    {Q : Option Sym → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs lO) S S' (fun _ => True) T := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  obtain ⟨⟨r', s'⟩, t, e, ⟨hs', -⟩, ht⟩ := h ⟨lO.get v, stk⟩ rfl
  change s' = S' at hs'
  subst hs'
  exact ⟨_, t, Eval.liftRegs lO e v rfl, ⟨rfl, trivial⟩, ht⟩

/-- Decrement the binary counter on `k` (temporary `t`). -/
def decP (k t : K) : Prog K (fun _ => Sym) σ := (TMFw.Lib.dec k t).liftRegs lO

/-- Increment the binary counter on `k` (temporary `t`). -/
def incP (k t : K) : Prog K (fun _ => Sym) σ := (TMFw.Lib.inc k t).liftRegs lO

omit [DecidableEq K] in
theorem closed_decP (k t : K) : (decP lO k t).Closed :=
  closed_liftRegs lO (by
    simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.dec, TMFw.Lib.decFix, TMFw.Lib.scanLoop,
      TMFw.Lib.scanBody, TMFw.Lib.peekR, TMFw.Lib.popR, TMFw.Lib.pushC, TMFw.Lib.skip,
      TMFw.Lib.moveBits, TMFw.Lib.moveBitsBody, TMFw.Lib.pushR])

omit [DecidableEq K] in
theorem closed_incP (k t : K) : (incP lO k t).Closed :=
  closed_liftRegs lO (by
    simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.inc, TMFw.Lib.incFix, TMFw.Lib.scanLoop,
      TMFw.Lib.scanBody, TMFw.Lib.popR, TMFw.Lib.pushC, TMFw.Lib.skip,
      TMFw.Lib.moveBits, TMFw.Lib.moveBitsBody, TMFw.Lib.pushR, TMFw.Lib.restoreR])

theorem runs_decP {k t : K} (hkt : k ≠ t) (S : K → List Sym) (n : ℕ) (rest : List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (n + 1) ++ rest) :
    Runs (decP lO k t) S (Function.update S k (natSyms n ++ rest)) (fun _ => True)
      (6 * bitLen (n + 1) + 8) := by
  refine runs_liftS lO (Q := fun _ => True) (Runs.of_eval fun r => ?_)
  refine ⟨some .mark, _, TMFw.Lib.dec_eval hkt [] r n rest S hrest hS, trivial, ?_⟩
  have := zerosLead_le_length (Computability.encodeNat (n + 1))
  simp only [bitLen]
  omega

theorem runs_incP {k t : K} (hkt : k ≠ t) (S : K → List Sym) (n : ℕ) (rest : List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (incP lO k t) S (Function.update S k (natSyms (n + 1) ++ rest)) (fun _ => True)
      (6 * bitLen n + 9) := by
  refine runs_liftS lO (Q := fun _ => True) (Runs.of_eval fun r => ?_)
  obtain ⟨c, hc, e⟩ := TMFw.Lib.inc_eval hkt [] r (Computability.encodeNat n) rest S hrest hS
  refine ⟨some .mark, c, ?_, trivial, ?_⟩
  · rw [natSyms, encodeNat_succ]
    exact e
  · have := ones_le_length (Computability.encodeNat n)
    simp only [bitLen]
    omega

end Lift

/-! ## Counted record moves -/

section Skip

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- While the counter `I` is nonzero: decrement it and move one record from `TB` to `TT` (it
arrives reversed). -/
def skipB (TB TT I t : K) : Prog K (fun _ => Sym) σ :=
  ploop lO I optIsBit (.seq (decP lO I t) (moveRec lO TB TT))

/-- While the counter `I` is nonzero: decrement it and move one reversed record from `TT` back to
`TB`. -/
def unskipB (TT TB I t : K) : Prog K (fun _ => Sym) σ :=
  ploop lO I optIsBit (.seq (decP lO I t) (moveRevRec lO TT TB))

omit [DecidableEq K] in
theorem closed_skipB (TB TT I t : K) : (skipB lO TB TT I t).Closed :=
  closed_ploop lO I optIsBit ⟨closed_decP lO I t, closed_moveRec lO TB TT⟩

omit [DecidableEq K] in
theorem closed_unskipB (TT TB I t : K) : (unskipB lO TT TB I t).Closed :=
  closed_ploop lO I optIsBit ⟨closed_decP lO I t, closed_moveRevRec lO TT TB⟩

theorem runs_skipB {TB TT I t : K} (h1 : TB ≠ TT) (h2 : TB ≠ I) (h3 : TT ≠ I) (h4 : I ≠ t)
    (S : K → List Sym) (tab : List (List Bool)) (n0 : ℕ) (htab : ∀ p ∈ tab, p.length = n0)
    (R Ir : List Sym) (hIr : TermOK Ir) (m : ℕ) (hm : m ≤ tab.length)
    (hTB : S TB = arrSyms tab ++ R) (hI : S I = natSyms m ++ Ir) :
    Runs (skipB lO TB TT I t) S
      (Function.update (Function.update (Function.update S TB (arrSyms (tab.drop m) ++ R)) TT
        ((arrSyms (tab.take m)).reverse ++ S TT)) I Ir)
      (fun _ => True) (m * (6 * bitLen m + 4 * n0 + 14) + 2) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S TB (arrSyms (tab.drop i) ++ R)) TT
      ((arrSyms (tab.take i)).reverse ++ S TT)) I (natSyms (m - i) ++ Ir)
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply, List.drop_zero, List.take_zero, arrSyms_nil',
      List.reverse_nil, List.nil_append, Nat.sub_zero]
    split_ifs <;> simp_all
  have hN : St m = Function.update (Function.update (Function.update S TB
      (arrSyms (tab.drop m) ++ R)) TT ((arrSyms (tab.take m)).reverse ++ S TT)) I Ir := by
    simp only [St, Nat.sub_self, natSyms_zero', List.nil_append]
  have hloop := runs_ploop_const lO I optIsBit (.seq (decP lO I t) (moveRec lO TB TT)) m St
    (6 * bitLen m + 4 * n0 + 12) ?_ ?_
  · rw [h0, hN] at hloop
    exact runs_mono hloop (fun _ _ => trivial) (le_of_eq (by ring))
  · intro i _
    simp only [St, Function.update_self]
    rw [optIsBit_natSyms _ _ hIr]
    simp
  · intro i hi
    have hi' : i < tab.length := lt_of_lt_of_le hi hm
    have hdrop : tab.drop i = tab[i] :: tab.drop (i + 1) := List.drop_eq_getElem_cons hi'
    have htake : tab.take (i + 1) = tab.take i ++ [tab[i]] :=
      List.take_succ_eq_append_getElem hi'
    have hmi : m - i = m - (i + 1) + 1 := by omega
    have hSI : St i I = natSyms (m - (i + 1) + 1) ++ Ir := by
      simp only [St, Function.update_self, hmi]
    have e1 := runs_decP lO h4 (St i) (m - (i + 1)) Ir hIr hSI
    have hSB : Function.update (St i) I (natSyms (m - (i + 1)) ++ Ir) TB =
        recSyms tab[i] ++ (arrSyms (tab.drop (i + 1)) ++ R) := by
      simp only [St, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self,
        hdrop, arrSyms_cons', List.append_assoc]
    have e2 := runs_moveRec lO h1 _ tab[i] _ hSB
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) ?_) ?_
    · have hb : bitLen (m - (i + 1) + 1) ≤ bitLen m := bitLen_le_bitLen (by omega)
      have hl : tab[i].length = n0 := htab _ (List.getElem_mem _)
      omega
    · funext j
      simp only [St, Function.update_apply, htake, arrSyms_append', arrSyms_cons', arrSyms_nil',
        List.append_nil, List.reverse_append, List.append_assoc, h3, h1.symm]
      split_ifs <;> simp_all

theorem runs_unskipB {TT TB I t : K} (h1 : TT ≠ TB) (h2 : TT ≠ I) (h3 : TB ≠ I) (h4 : I ≠ t)
    (S : K → List Sym) (u : List (List Bool)) (n0 : ℕ) (hu : ∀ p ∈ u, p.length = n0)
    (R Ir : List Sym) (hR : TermOK R) (hIr : TermOK Ir)
    (hTT : S TT = (arrSyms u).reverse ++ R) (hI : S I = natSyms u.length ++ Ir) :
    Runs (unskipB lO TT TB I t) S
      (Function.update (Function.update (Function.update S TT R) TB (arrSyms u ++ S TB)) I Ir)
      (fun _ => True) (u.length * (6 * bitLen u.length + 4 * n0 + 14) + 2) := by
  let m := u.length
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S TT
      ((arrSyms (u.take (m - i))).reverse ++ R)) TB (arrSyms (u.drop (m - i)) ++ S TB)) I
      (natSyms (m - i) ++ Ir)
  have h0 : St 0 = S := by
    funext j
    simp only [St, m, Function.update_apply, Nat.sub_zero, List.take_length, List.drop_length,
      arrSyms_nil', List.nil_append]
    split_ifs <;> simp_all
  have hN : St m = Function.update (Function.update (Function.update S TT R) TB
      (arrSyms u ++ S TB)) I Ir := by
    simp only [St, Nat.sub_self, natSyms_zero', List.nil_append, List.take_zero, List.drop_zero,
      arrSyms_nil', List.reverse_nil]
  have hloop := runs_ploop_const lO I optIsBit (.seq (decP lO I t) (moveRevRec lO TT TB)) m St
    (6 * bitLen m + 4 * n0 + 12) ?_ ?_
  · rw [h0, hN] at hloop
    exact runs_mono hloop (fun _ _ => trivial) (le_of_eq (by ring))
  · intro i _
    simp only [St, Function.update_self]
    rw [optIsBit_natSyms _ _ hIr]
    simp
  · intro i hi
    have hj : m - (i + 1) < u.length := by omega
    have hdrop : u.drop (m - (i + 1)) = u[m - (i + 1)] :: u.drop (m - (i + 1) + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : u.take (m - (i + 1) + 1) = u.take (m - (i + 1)) ++ [u[m - (i + 1)]] :=
      List.take_succ_eq_append_getElem hj
    have hmi : m - i = m - (i + 1) + 1 := by omega
    have hSI : St i I = natSyms (m - (i + 1) + 1) ++ Ir := by
      simp only [St, Function.update_self, hmi]
    have e1 := runs_decP lO h4 (St i) (m - (i + 1)) Ir hIr hSI
    have hST : Function.update (St i) I (natSyms (m - (i + 1)) ++ Ir) TT =
        (recSyms u[m - (i + 1)]).reverse ++
          ((arrSyms (u.take (m - (i + 1)))).reverse ++ R) := by
      simp only [St, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self,
        hmi, htake, arrSyms_append', arrSyms_cons', arrSyms_nil', List.append_nil,
        List.reverse_append, List.append_assoc]
    have e2 := runs_moveRevRec lO h1 _ u[m - (i + 1)] _ (termOK_rev_arrSyms _ R hR) hST
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) ?_) ?_
    · have hb : bitLen (m - (i + 1) + 1) ≤ bitLen m := bitLen_le_bitLen (by omega)
      have hl : u[m - (i + 1)].length = n0 := hu _ (List.getElem_mem _)
      omega
    · funext j
      simp only [St, Function.update_apply, hmi, hdrop, arrSyms_cons', List.append_assoc, h3,
        h1.symm]
      split_ifs <;> simp_all

end Skip

/-! ## One table scan -/

section Sel

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Move one record of `src` onto both `a` and `b` (it arrives reversed on both). -/
def moveRecDup (src a b : K) : Prog K (fun _ => Sym) σ :=
  .seq (dupPrefix lO src a b optIsBit) (dupmv lO src a b)

omit [DecidableEq K] in
theorem closed_moveRecDup (src a b : K) : (moveRecDup lO src a b).Closed :=
  ⟨closed_dupPrefix lO src a b _, closed_dupmv lO src a b⟩

theorem runs_moveRecDup {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (S : K → List Sym) (p : List Bool) (rest : List Sym) (hS : S src = recSyms p ++ rest) :
    Runs (moveRecDup lO src a b) S
      (Function.update (Function.update (Function.update S src rest) a
        ((recSyms p).reverse ++ S a)) b ((recSyms p).reverse ++ S b))
      (fun _ => True) (5 * p.length + 5) := by
  have hS' : S src = p.map Sym.bit ++ (Sym.sep :: rest) := by rw [hS]; simp [recSyms]
  have e1 := runs_dupPrefix lO hsa hsb hab optIsBit S _ _ hS' (bits_optIsBit p) rfl
  set S1 := Function.update (Function.update (Function.update S src (Sym.sep :: rest)) a
    ((p.map Sym.bit).reverse ++ S a)) b ((p.map Sym.bit).reverse ++ S b) with hS1
  have h1 : S1 src = Sym.sep :: rest := by
    rw [hS1, Function.update_of_ne hsb, Function.update_of_ne hsa, Function.update_self]
  have e2 := runs_dupmv lO hsa hsb hab S1 h1
  refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
    (by simp only [List.length_map]; omega)) ?_
  clear e1 e2
  funext j
  simp only [hS1, Function.update_apply, reverse_recSyms', hab, hsa.symm, hsb.symm, hab.symm]
  split_ifs <;> simp_all

/-- Cost of `selEntry` for table index `m` and records of `n0` bits. -/
def selCost (m n0 : ℕ) : ℕ :=
  2 * (m * (6 * bitLen m + 4 * n0 + 14)) + 9 * bitLen m + 9 * n0 + 17

theorem selCost_mono {m m' : ℕ} (n0 : ℕ) (h : m ≤ m') : selCost m n0 ≤ selCost m' n0 := by
  have hb := bitLen_le_bitLen h
  have hX : m * (6 * bitLen m + 4 * n0 + 14) ≤ m' * (6 * bitLen m' + 4 * n0 + 14) :=
    Nat.mul_le_mul h (by omega)
  unfold selCost
  omega

/-- **One table scan** (Theorem 6.5, Section 6.4): with the index `m` on `I`, push the reversed
record `m` of the table on `TB` onto `PHI`. The table and every other stack are restored and `I` is
consumed; `TT`, `TMP` are side stacks, `I2` holds a copy of the counter, `t` is a temporary. -/
def selEntry (TB TT TMP PHI I I2 t : K) : Prog K (fun _ => Sym) σ :=
  .seq (copyBits lO I I2 t) (.seq (skipB lO TB TT I t) (.seq (moveRecDup lO TB TMP PHI)
    (.seq (moveRevRec lO TMP TB) (unskipB lO TT TB I2 t))))

omit [DecidableEq K] in
theorem closed_selEntry (TB TT TMP PHI I I2 t : K) :
    (selEntry lO TB TT TMP PHI I I2 t).Closed :=
  ⟨closed_copyBits lO I I2 t, closed_skipB lO TB TT I t, closed_moveRecDup lO TB TMP PHI,
    closed_moveRevRec lO TMP TB, closed_unskipB lO TT TB I2 t⟩

theorem runs_selEntry {TB TT TMP PHI I I2 t : K} (hd : [TB, TT, TMP, PHI, I, I2, t].Nodup)
    (S : K → List Sym) (tab : List (List Bool)) (n0 : ℕ) (htab : ∀ p ∈ tab, p.length = n0)
    (R : List Sym) (m : ℕ) (hm : m < tab.length)
    (hTB : S TB = arrSyms tab ++ R) (hI : S I = natSyms m) (hTT : TermOK (S TT))
    (hTMP : TermOK (S TMP)) (hI2 : S I2 = []) (ht : TermOK (S t)) :
    Runs (selEntry lO TB TT TMP PHI I I2 t) S
      (Function.update (Function.update S I []) PHI ((recSyms tab[m]).reverse ++ S PHI))
      (fun _ => True) (selCost m n0) := by
  have p0 := List.pairwise_cons.1 hd
  have hBT : TB ≠ TT := p0.1 TT (by simp)
  have hBM : TB ≠ TMP := p0.1 TMP (by simp)
  have hBP : TB ≠ PHI := p0.1 PHI (by simp)
  have hBI : TB ≠ I := p0.1 I (by simp)
  have hBJ : TB ≠ I2 := p0.1 I2 (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have hTM : TT ≠ TMP := p1.1 TMP (by simp)
  have hTP : TT ≠ PHI := p1.1 PHI (by simp)
  have hTI : TT ≠ I := p1.1 I (by simp)
  have hTJ : TT ≠ I2 := p1.1 I2 (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have hMP : TMP ≠ PHI := p2.1 PHI (by simp)
  have hMI : TMP ≠ I := p2.1 I (by simp)
  have hMJ : TMP ≠ I2 := p2.1 I2 (by simp)
  have p3 := List.pairwise_cons.1 p2.2
  have hPI : PHI ≠ I := p3.1 I (by simp)
  have hPJ : PHI ≠ I2 := p3.1 I2 (by simp)
  have p4 := List.pairwise_cons.1 p3.2
  have hIJ : I ≠ I2 := p4.1 I2 (by simp)
  have hIt : I ≠ t := p4.1 t (by simp)
  have hJt : I2 ≠ t := (List.pairwise_cons.1 p4.2).1 t (by simp)
  have hl : tab[m].length = n0 := htab _ (List.getElem_mem _)
  have hlenT : (tab.take m).length = m := by simp only [List.length_take]; omega
  have hdrop : tab.drop m = tab[m] :: tab.drop (m + 1) := List.drop_eq_getElem_cons hm
  -- 1. copy the counter onto `I2`
  have e1 : Runs (copyBits lO I I2 t) S (Function.update S I2 (natSyms m))
      (fun _ => True) (9 * bitLen m + 4) := by
    have h := runs_copyBits lO hIJ hIt hJt S (Computability.encodeNat m) []
      (by rw [hI, List.append_nil]; rfl) termOK_nil' ht
    rw [hI2, List.append_nil] at h
    exact h
  set S1 := Function.update S I2 (natSyms m) with hS1
  -- 2. skip `m` records onto `TT`
  have e2 := runs_skipB lO hBT hBI hTI hIt S1 tab n0 htab R [] termOK_nil' m hm.le
    (by rw [hS1, Function.update_of_ne hBJ, hTB])
    (by rw [hS1, Function.update_of_ne hIJ, hI, List.append_nil])
  set S2 := Function.update (Function.update (Function.update S1 TB
    (arrSyms (tab.drop m) ++ R)) TT ((arrSyms (tab.take m)).reverse ++ S1 TT)) I [] with hS2
  -- 3. copy record `m` onto `TMP` and `PHI`
  have e3 := runs_moveRecDup lO hBM hBP hMP S2 tab[m] (arrSyms (tab.drop (m + 1)) ++ R)
    (by rw [hS2, Function.update_of_ne hBI, Function.update_of_ne hBT, Function.update_self,
      hdrop, arrSyms_cons', List.append_assoc])
  set S3 := Function.update (Function.update (Function.update S2 TB
    (arrSyms (tab.drop (m + 1)) ++ R)) TMP ((recSyms tab[m]).reverse ++ S2 TMP)) PHI
    ((recSyms tab[m]).reverse ++ S2 PHI) with hS3
  -- 4. put record `m` back on the table
  have e4 := runs_moveRevRec lO hBM.symm S3 tab[m] (S TMP) hTMP
    (by simp [hS3, hS2, hS1, Function.update_apply, hMP, hMI, hMJ, hTM.symm, hBM.symm])
  set S4 := Function.update (Function.update S3 TMP (S TMP)) TB (recSyms tab[m] ++ S3 TB)
    with hS4
  -- 5. move the `m` skipped records back
  have e5 := runs_unskipB lO hBT.symm hTJ hBJ hJt S4 (tab.take m) n0
    (fun p hp => htab p (List.mem_of_mem_take hp)) (S TT) [] hTT termOK_nil'
    (by simp [hS4, hS3, hS2, hS1, Function.update_apply, hBT.symm, hTM, hTP, hTI, hTJ])
    (by simp [hlenT, hS4, hS3, hS2, hS1, Function.update_apply, hBJ.symm, hMJ.symm, hPJ.symm,
      hIJ.symm, hTJ.symm])
  have hTBfin : arrSyms (tab.take m) ++ (recSyms tab[m] ++ (arrSyms (tab.drop (m + 1)) ++ R)) =
      S TB := by
    calc arrSyms (tab.take m) ++ (recSyms tab[m] ++ (arrSyms (tab.drop (m + 1)) ++ R))
        = arrSyms (tab.take m ++ tab.drop m) ++ R := by
          rw [hdrop, arrSyms_append', arrSyms_cons']
          simp only [List.append_assoc]
      _ = S TB := by rw [List.take_append_drop, hTB]
  refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4 e5))))
    (fun _ _ => trivial) ?_) ?_
  · simp only [selCost, hl, hlenT]
    omega
  · clear e1 e2 e3 e4 e5
    funext j
    simp only [hS4, hS3, hS2, hS1, Function.update_apply, hBT, hBM, hBP, hBI, hBJ, hTJ, hMI, hMJ,
      hPI, hPJ, hBM.symm, hBP.symm, hTM.symm, hTP.symm, if_false, if_true]
    split_ifs <;> simp_all

end Sel

end SubNLogN.Machine.FFT.TwiddleAux
