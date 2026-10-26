/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.FramePassR

/-!
# Lemma A.9 repair: one binary radix pass on stacks (`Machine/AppC/C7Radix.lean`)

The stable binary radix sort of the Lemma A.9 repair phase (Lemma A.9 (`lem:transfer13`),
deterministic repair phase). A bank of **keyed records** `kb.map bit ++ [sep2] ++ p.map bit ++ [sep]` (key bits `kb`,
least significant first, then the payload `p`) lies on stack `bank` above the terminator `tag 14`.
One pass:

1. pushes `tag 14` on the buckets `b0`, `b1`;
2. for each record: pops its first key bit `k`, moves the remaining key bits, then `k`, then `sep2`,
   the payload and `sep` onto bucket `b_k` (so the bucket holds the reversed record with its key
   rotated left by one);
3. drains `b1`, then `b0`, back onto the bank and pops both bucket terminators.

Result (`rsPass_runs`): the bank holds `rsPass recs` = the records whose first key bit is `false`,
then those whose first key bit is `true`, each group in its original order, every key rotated left
by one bit. The buckets end as they started. Cost exactly
`Σ_records (8·(|kb| + |p|) + 21) + 10` for keys of length `≥ 1`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

Programs are direct `SProg` (register `Option Sym`); the stack names are parameters.
-/

namespace SubNLogN.Machine.AppC.C7RadixAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

/-! ## Keyed records -/

/-- A keyed record: key bits, `sep2`, payload bits, `sep`. -/
def keyedSyms (r : List Bool × List Bool) : List Sym :=
  r.1.map Sym.bit ++ Sym.sep2 :: (r.2.map Sym.bit ++ [Sym.sep])

/-- A bank of keyed records (first record on top). -/
def bankSyms (recs : List (List Bool × List Bool)) : List Sym := recs.flatMap keyedSyms

/-- Rotate a key left by one bit (the first key bit goes to the end). -/
def rsRot (r : List Bool × List Bool) : List Bool × List Bool := (r.1.drop 1 ++ r.1.take 1, r.2)

/-- The first key bit of a record (`false` for an empty key). -/
def rsDigit (r : List Bool × List Bool) : Bool := r.1.headD false

/-- **One radix pass on lists**: stable partition by the first key bit (`false` first), every key
rotated left by one. -/
def rsPass (recs : List (List Bool × List Bool)) : List (List Bool × List Bool) :=
  (recs.filter (fun r => !rsDigit r)).map rsRot ++ (recs.filter rsDigit).map rsRot

/-- **`n` radix passes on lists** (`rsSort (n + 1) recs = rsPass (rsSort n recs)`). -/
def rsSort : ℕ → List (List Bool × List Bool) → List (List Bool × List Bool)
  | 0, recs => recs
  | n + 1, recs => rsPass (rsSort n recs)

/-- **Fill the holes** (`none`) of a record skeleton with the given records, in order (the
reinsertion step of Lemma A.9 (`lem:transfer13`)). -/
def fillHoles : List (Option (List Bool)) → List (List Bool) → List (List Bool)
  | [], _ => []
  | some p :: hs, ps => p :: fillHoles hs ps
  | none :: hs, q :: ps => q :: fillHoles hs ps
  | none :: hs, [] => fillHoles hs []

/-- Number of holes of a skeleton. -/
def holeCount (hs : List (Option (List Bool))) : ℕ := (hs.filter Option.isNone).length

/-- The retained stream of a skeleton: `tag 8` for a hole, `recSyms p` for a kept record. -/
def holeSyms (hs : List (Option (List Bool))) : List Sym :=
  hs.flatMap fun o => match o with
    | none => [Sym.tag 8]
    | some p => SubNLogN.Machine.recSyms p

/-- The bank terminator. -/
abbrev bankEnd : Sym := Sym.tag 14

theorem fillHoles_append : ∀ (hs hs' : List (Option (List Bool))) (ps : List (List Bool)),
    holeCount hs ≤ ps.length →
      fillHoles (hs ++ hs') ps = fillHoles hs ps ++ fillHoles hs' (ps.drop (holeCount hs))
  | [], hs', ps, _ => by simp [fillHoles, holeCount]
  | some p :: hs, hs', ps, h => by
    simp only [List.cons_append, fillHoles, List.cons_append]
    rw [fillHoles_append hs hs' ps (by simpa [holeCount] using h)]
    simp [holeCount]
  | none :: hs, hs', [], h => by simp [holeCount] at h
  | none :: hs, hs', q :: ps, h => by
    simp only [List.cons_append, fillHoles]
    rw [fillHoles_append hs hs' ps (by simp [holeCount] at h ⊢; omega)]
    simp [holeCount]

/-! ## Programs -/

section Programs

variable {K : Type}

/-- Move the rest of a record (its first key bit `dig` already popped) onto bucket `d`. -/
def rsRecTo (dig : Bool) (bank d : K) : SProg K :=
  .seq (passM .sep2 bank d) (.seq (pushC d (.bit dig)) (.seq (popR bank) (.seq (pushC d .sep2)
    (.seq (passM .sep bank d) (.seq (popR bank) (pushC d .sep))))))

/-- Process one record: pop its first key bit, branch to the bucket, look at the next record. -/
def rsRec (bank b0 b1 : K) : SProg K :=
  .seq (.seq (popR bank) (.ite (fun r => decide (r = some (Sym.bit true))) (rsRecTo true bank b1)
    (rsRecTo false bank b0))) (peekR bank)

/-- **One radix pass.** -/
def rsPassProg (bank b0 b1 : K) : SProg K :=
  .seq (pushC b0 bankEnd) (.seq (pushC b1 bankEnd)
    (.seq (.seq (peekR bank) (.loop (notG bankEnd) (rsRec bank b0 b1)))
      (.seq (passM bankEnd b1 bank) (.seq (popR b1) (.seq (passM bankEnd b0 bank) (popR b0))))))

theorem closed_rsRecTo (dig : Bool) (bank d : K) : (rsRecTo dig bank d).Closed :=
  ⟨closed_passM _ _ _, trivial,
    trivial, trivial,
    closed_passM _ _ _, trivial,
    trivial⟩

theorem closed_rsRec (bank b0 b1 : K) : (rsRec bank b0 b1).Closed :=
  ⟨⟨trivial, ⟨closed_rsRecTo _ _ _, closed_rsRecTo _ _ _⟩⟩,
    trivial⟩

theorem closed_rsPassProg (bank b0 b1 : K) : (rsPassProg bank b0 b1).Closed :=
  ⟨trivial, trivial,
    ⟨trivial, closed_rsRec _ _ _⟩, closed_passM _ _ _,
    trivial, closed_passM _ _ _,
    trivial⟩

end Programs

/-! ## Single records -/

section Runs

variable {K : Type} [DecidableEq K]

theorem runs_pushC_c (k : K) (a : Sym) (S : K → List Sym) :
    Runs (pushC k a) S (Function.update S k (a :: S k)) (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ⟨v, 1, ?_, trivial, le_rfl⟩
  exact Eval.push [] k (fun _ => a) v S

theorem runs_popR_c (k : K) (S : K → List Sym) (a : Sym) (l : List Sym) (hS : S k = a :: l) :
    Runs (popR k) S (Function.update S k l) (fun r => r = some a) 1 := by
  refine Runs.of_eval fun v => ⟨some a, 1, ?_, rfl, le_rfl⟩
  refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
  simp [hS]

theorem runs_peekR_c (k : K) (S : K → List Sym) :
    Runs (peekR k) S S (fun r => r = (S k).head?) 1 := by
  refine Runs.of_eval fun v => ⟨(S k).head?, 1, ?_, rfl, le_rfl⟩
  exact Eval.peek [] k (fun _ o => o) v S

/-- The rest of a record (first key bit `dig` popped) goes onto bucket `d`, reversed, with `dig`
after the remaining key bits. -/
theorem rsRecTo_runs {bank d : K} (hd : bank ≠ d) (dig : Bool) (kr p : List Bool) (l : List Sym)
    (S : K → List Sym)
    (hS : S bank = kr.map Sym.bit ++ Sym.sep2 :: (p.map Sym.bit ++ Sym.sep :: l)) :
    Runs (rsRecTo dig bank d) S
      (Function.update (Function.update S bank l) d ((keyedSyms (kr ++ [dig], p)).reverse ++ S d))
      (fun _ => True) (4 * kr.length + 4 * p.length + 9) := by
  have hkr : Sym.sep2 ∉ kr.map Sym.bit := by simp
  have hp : Sym.sep ∉ p.map Sym.bit := by simp
  have X := RunsIn.seq (RunsIn.iff_runs.mpr
      (runs_passM hd (kr.map Sym.bit) (p.map Sym.bit ++ Sym.sep :: l) hkr S hS))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_pushC_c d (Sym.bit dig) _))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c bank _ Sym.sep2 (p.map Sym.bit ++ Sym.sep :: l)
      (by simp [hd])))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_pushC_c d Sym.sep2 _))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_passM hd (p.map Sym.bit) l hp _
      (by simp [hd, hd.symm])))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c bank _ Sym.sep l
      (by simp [hd, hd.symm])))
      (RunsIn.iff_runs.mpr (runs_pushC_c d Sym.sep _)))))))
  refine RunsIn.iff_runs.mp (RunsIn.congr X ?_ (by simp only [List.length_map]; omega))
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all [keyedSyms]

/-- **One record** with first key bit `k`: it goes, reversed and with its key rotated, onto bucket
`b_k`; the register then holds the top of the rest of the bank. Cost `4·|kr| + 4·|p| + 12`. -/
theorem rsRec_runs {bank b0 b1 : K} (h0 : bank ≠ b0) (h1 : bank ≠ b1) (k : Bool)
    (kr p : List Bool) (l : List Sym) (S : K → List Sym) (hS : S bank = keyedSyms (k :: kr, p) ++ l) :
    Runs (rsRec bank b0 b1) S
      (Function.update (Function.update S bank l) (cond k b1 b0)
        ((keyedSyms (kr ++ [k], p)).reverse ++ S (cond k b1 b0)))
      (fun v => v = l.head?) (4 * kr.length + 4 * p.length + 12) := by
  have hS' : S bank = Sym.bit k :: (kr.map Sym.bit ++ Sym.sep2 :: (p.map Sym.bit ++ Sym.sep :: l)) := by
    rw [hS]; simp [keyedSyms]
  have hpop := runs_popR_c bank S (Sym.bit k) _ hS'
  cases k
  · have hT := rsRecTo_runs h0 false kr p l
      (Function.update S bank (kr.map Sym.bit ++ Sym.sep2 :: (p.map Sym.bit ++ Sym.sep :: l)))
      (Function.update_self _ _ _)
    have hc : RunsIn [] (popR bank) S
        (Function.update S bank (kr.map Sym.bit ++ Sym.sep2 :: (p.map Sym.bit ++ Sym.sep :: l)))
        (fun v => (fun r => decide (r = some (Sym.bit true))) v = false) 1 :=
      RunsIn.mono (RunsIn.iff_runs.mpr hpop) (fun v hv => by simp [hv]) le_rfl
    have X := RunsIn.ite_false (Pt := rsRecTo true bank b1) hc (RunsIn.iff_runs.mpr hT)
    have Y := RunsIn.seq X (RunsIn.iff_runs.mpr (runs_peekR_c bank _))
    refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.mono Y (fun v hv => hv.trans ?_) le_rfl) ?_
      (by omega))
    · simp [Function.update_apply, h0]
    · funext j
      simp only [Function.update_apply, cond_false]
      split_ifs <;> simp_all
  · have hT := rsRecTo_runs h1 true kr p l
      (Function.update S bank (kr.map Sym.bit ++ Sym.sep2 :: (p.map Sym.bit ++ Sym.sep :: l)))
      (Function.update_self _ _ _)
    have hc : RunsIn [] (popR bank) S
        (Function.update S bank (kr.map Sym.bit ++ Sym.sep2 :: (p.map Sym.bit ++ Sym.sep :: l)))
        (fun v => (fun r => decide (r = some (Sym.bit true))) v = true) 1 :=
      RunsIn.mono (RunsIn.iff_runs.mpr hpop) (fun v hv => by simp [hv]) le_rfl
    have X := RunsIn.ite_true (Pf := rsRecTo false bank b0) hc (RunsIn.iff_runs.mpr hT)
    have Y := RunsIn.seq X (RunsIn.iff_runs.mpr (runs_peekR_c bank _))
    refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.mono Y (fun v hv => hv.trans ?_) le_rfl) ?_
      (by omega))
    · simp [Function.update_apply, h1]
    · funext j
      simp only [Function.update_apply, cond_true]
      split_ifs <;> simp_all

/-! ## The distribution loop -/

theorem bankSyms_append (a b : List (List Bool × List Bool)) :
    bankSyms (a ++ b) = bankSyms a ++ bankSyms b := by
  simp [bankSyms]

theorem bankSyms_cons (r : List Bool × List Bool) (rs : List (List Bool × List Bool)) :
    bankSyms (r :: rs) = keyedSyms r ++ bankSyms rs := by
  simp [bankSyms]

/-- State of the distribution loop after the first `i` records: the rest of the bank, and the
reversed rotated records of each bucket on top of the bucket's initial content. -/
def rsLoopSt (bank b0 b1 : K) (S : K → List Sym) (recs : List (List Bool × List Bool))
    (l : List Sym) (i : ℕ) : K → List Sym :=
  Function.update (Function.update (Function.update S bank (bankSyms (recs.drop i) ++ l)) b0
      ((bankSyms (((recs.take i).filter (fun r => !rsDigit r)).map rsRot)).reverse ++ S b0)) b1
    ((bankSyms (((recs.take i).filter rsDigit).map rsRot)).reverse ++ S b1)

theorem rsLoopSt_bank {bank b0 b1 : K} (h0 : bank ≠ b0) (h1 : bank ≠ b1) (S : K → List Sym)
    (recs : List (List Bool × List Bool)) (l : List Sym) (i : ℕ) :
    rsLoopSt bank b0 b1 S recs l i bank = bankSyms (recs.drop i) ++ l := by
  simp [rsLoopSt, h0, h1]

theorem rsLoopSt_zero {bank b0 b1 : K} (S : K → List Sym) (recs : List (List Bool × List Bool))
    (l : List Sym) (hS : S bank = bankSyms recs ++ l) : rsLoopSt bank b0 b1 S recs l 0 = S := by
  funext j
  simp only [rsLoopSt, List.drop_zero, List.take_zero, List.filter_nil, List.map_nil,
    Function.update_apply]
  split_ifs <;> simp_all [bankSyms]

theorem rsLoopSt_succ {bank b0 b1 : K} (h0 : bank ≠ b0) (h1 : bank ≠ b1) (h01 : b0 ≠ b1)
    (S : K → List Sym) (recs : List (List Bool × List Bool)) (l : List Sym) (i : ℕ)
    (hi : i < recs.length) (k : Bool) (kr p : List Bool) (hr : recs[i] = (k :: kr, p)) :
    Function.update (Function.update (rsLoopSt bank b0 b1 S recs l i) bank
        (bankSyms (recs.drop (i + 1)) ++ l)) (cond k b1 b0)
      ((keyedSyms (kr ++ [k], p)).reverse ++ rsLoopSt bank b0 b1 S recs l i (cond k b1 b0)) =
      rsLoopSt bank b0 b1 S recs l (i + 1) := by
  have ht : recs.take (i + 1) = recs.take i ++ [(k :: kr, p)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, hr]
    rfl
  have hrot : rsRot (k :: kr, p) = (kr ++ [k], p) := by simp [rsRot]
  funext j
  cases k
  · simp only [rsLoopSt, ht, List.filter_append, List.map_append, bankSyms_append,
      List.reverse_append, Function.update_apply, cond_false]
    split_ifs <;> simp_all [rsDigit, bankSyms]
  · simp only [rsLoopSt, ht, List.filter_append, List.map_append, bankSyms_append,
      List.reverse_append, Function.update_apply, cond_true]
    split_ifs <;> simp_all [rsDigit, bankSyms]

/-- **The distribution loop** (records with keys of length `A ≥ 1` and payloads of length `R`):
from the bank `bankSyms recs ++ l` (`l` starting with `bankEnd`), every record goes to its bucket;
the loop ends with the register on `bankEnd`. Cost `1 + loopCost (4A + 4R + 8) |recs|`. -/
theorem rsLoop_runs {bank b0 b1 : K} (h0 : bank ≠ b0) (h1 : bank ≠ b1) (h01 : b0 ≠ b1)
    {A R : ℕ} (hA : 1 ≤ A) (recs : List (List Bool × List Bool))
    (hrec : ∀ r ∈ recs, r.1.length = A ∧ r.2.length = R) (l : List Sym)
    (hl : l.head? = some bankEnd) (S : K → List Sym) (hS : S bank = bankSyms recs ++ l) :
    Runs (.seq (peekR bank) (.loop (notG bankEnd) (rsRec bank b0 b1))) S
      (rsLoopSt bank b0 b1 S recs l recs.length) (fun v => notG bankEnd v = false)
      (1 + loopCost (fun _ => 4 * A + 4 * R + 8) recs.length) := by
  have hhead : ∀ i, i ≤ recs.length →
      notG bankEnd (bankSyms (recs.drop i) ++ l).head? = decide (i < recs.length) := by
    intro i hi
    rcases Nat.lt_or_ge i recs.length with h | h
    · rw [List.drop_eq_getElem_cons h, bankSyms_cons]
      obtain ⟨hA', -⟩ := hrec _ (List.getElem_mem h)
      obtain ⟨k, kr, hk⟩ : ∃ k kr, recs[i].1 = k :: kr := by
        cases hh : recs[i].1 with
        | nil => rw [hh] at hA'; simp at hA'; omega
        | cons k kr => exact ⟨k, kr, rfl⟩
      simp [keyedSyms, hk, h, notG]
    · have : i = recs.length := le_antisymm hi h
      subst this
      simp [bankSyms, hl, notG]
  have h₀ : RunsIn [] (peekR bank) (rsLoopSt bank b0 b1 S recs l (recs.length - recs.length))
      (rsLoopSt bank b0 b1 S recs l (recs.length - recs.length))
      (fun v => notG bankEnd v = decide (0 < recs.length)) 1 := by
    refine RunsIn.mono (RunsIn.iff_runs.mpr (runs_peekR_c bank _)) (fun v hv => ?_) le_rfl
    rw [hv, rsLoopSt_bank h0 h1, hhead _ (Nat.sub_le _ _)]
    simp
  have hstep : ∀ n, n < recs.length →
      RunsIn [] (rsRec bank b0 b1) (rsLoopSt bank b0 b1 S recs l (recs.length - (n + 1)))
        (rsLoopSt bank b0 b1 S recs l (recs.length - n))
        (fun v => notG bankEnd v = decide (0 < n)) (4 * A + 4 * R + 8) := by
    intro n hn
    have hi : recs.length - (n + 1) < recs.length := by omega
    have hsucc : recs.length - n = recs.length - (n + 1) + 1 := by omega
    obtain ⟨hA', hR'⟩ := hrec _ (List.getElem_mem hi)
    obtain ⟨k, kr, hk⟩ : ∃ k kr, (recs[recs.length - (n + 1)]).1 = k :: kr := by
      cases hh : (recs[recs.length - (n + 1)]).1 with
      | nil => rw [hh] at hA'; simp at hA'; omega
      | cons k kr => exact ⟨k, kr, rfl⟩
    have hr : recs[recs.length - (n + 1)] = (k :: kr, (recs[recs.length - (n + 1)]).2) := by
      rw [← hk]
    have hSi : rsLoopSt bank b0 b1 S recs l (recs.length - (n + 1)) bank =
        keyedSyms (k :: kr, (recs[recs.length - (n + 1)]).2) ++
          (bankSyms (recs.drop (recs.length - (n + 1) + 1)) ++ l) := by
      rw [rsLoopSt_bank h0 h1, List.drop_eq_getElem_cons hi, bankSyms_cons, hr, List.append_assoc]
    have e := rsRec_runs h0 h1 k kr _ _ _ hSi
    rw [rsLoopSt_succ h0 h1 h01 S recs l _ hi k kr _ hr] at e
    rw [hsucc]
    refine RunsIn.mono (RunsIn.iff_runs.mpr e) (fun v hv => ?_) ?_
    · rw [hv, hhead _ (by omega)]
      simp only [decide_eq_decide]
      omega
    · have hkr : kr.length = A - 1 := by rw [hk] at hA'; simp at hA'; omega
      rw [hkr, hR']
      omega
  have key := RunsIn.seq_loop (st := fun n => rsLoopSt bank b0 b1 S recs l (recs.length - n))
    h₀ hstep
  simp only [Nat.sub_self, Nat.sub_zero, rsLoopSt_zero S recs l hS] at key
  exact RunsIn.iff_runs.mp key

/-! ## One pass -/

theorem keyedSyms_length (r : List Bool × List Bool) :
    (keyedSyms r).length = r.1.length + r.2.length + 2 := by
  simp [keyedSyms]
  omega

theorem bankSyms_length {A R : ℕ} :
    ∀ (rs : List (List Bool × List Bool)), (∀ r ∈ rs, r.1.length = A ∧ r.2.length = R) →
      (bankSyms rs).length = rs.length * (A + R + 2)
  | [], _ => by simp [bankSyms]
  | r :: rs, h => by
    rw [bankSyms_cons, List.length_append, keyedSyms_length,
      bankSyms_length rs (fun q hq => h q (List.mem_cons_of_mem r hq)), (h r List.mem_cons_self).1,
      (h r List.mem_cons_self).2, List.length_cons]
    ring

theorem rsRot_length (r : List Bool × List Bool) : (rsRot r).1.length = r.1.length := by
  simp only [rsRot, List.length_append, List.length_drop, List.length_take]
  omega

theorem bankEnd_not_mem_bankSyms (rs : List (List Bool × List Bool)) : bankEnd ∉ bankSyms rs := by
  simp [bankSyms, keyedSyms]

/-- **One radix pass** (`rsPass_runs`), records with keys of length `A ≥ 1` and payloads of length
`R`: the bank `bankSyms recs ++ bankEnd :: l'` becomes `bankSyms (rsPass recs) ++ bankEnd :: l'`; all
other stacks (in particular the buckets) are restored. Cost `|recs|·(8A + 8R + 17) + 10`. -/
theorem rsPass_runs {bank b0 b1 : K} (h0 : bank ≠ b0) (h1 : bank ≠ b1) (h01 : b0 ≠ b1)
    {A R : ℕ} (hA : 1 ≤ A) (recs : List (List Bool × List Bool))
    (hrec : ∀ r ∈ recs, r.1.length = A ∧ r.2.length = R) (l' : List Sym) (S : K → List Sym)
    (hS : S bank = bankSyms recs ++ bankEnd :: l') :
    Runs (rsPassProg bank b0 b1) S
      (Function.update S bank (bankSyms (rsPass recs) ++ bankEnd :: l'))
      (fun _ => True) (recs.length * (8 * A + 8 * R + 17) + 10) := by
  have hZ : ∀ r ∈ (recs.filter (fun r => !rsDigit r)).map rsRot, r.1.length = A ∧ r.2.length = R := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hq', -⟩ := List.mem_filter.mp hq
    exact ⟨(rsRot_length q).trans (hrec q hq').1, (hrec q hq').2⟩
  have hO : ∀ r ∈ (recs.filter rsDigit).map rsRot, r.1.length = A ∧ r.2.length = R := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hq', -⟩ := List.mem_filter.mp hq
    exact ⟨(rsRot_length q).trans (hrec q hq').1, (hrec q hq').2⟩
  have hlen := List.length_eq_length_filter_add (l := recs) rsDigit
  have hS2 : Function.update (Function.update S b0 (bankEnd :: S b0)) b1
      (bankEnd :: Function.update S b0 (bankEnd :: S b0) b1) bank = bankSyms recs ++ bankEnd :: l' := by
    simp [Function.update_apply, h0, h1, hS]
  have eL := rsLoop_runs h0 h1 h01 hA recs hrec (bankEnd :: l') rfl _ hS2
  have X := RunsIn.seq (RunsIn.iff_runs.mpr (runs_pushC_c b0 bankEnd S))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_pushC_c b1 bankEnd _))
    (RunsIn.seq (RunsIn.iff_runs.mpr eL)
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_passM h1.symm
        ((bankSyms ((recs.filter rsDigit).map rsRot)).reverse) (S b1)
        (by simpa using bankEnd_not_mem_bankSyms _) _
        (by simp [rsLoopSt, h01, h01.symm])))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c b1 _ bankEnd (S b1)
        (by simp [Function.update_apply, h1.symm])))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_passM h0.symm
        ((bankSyms ((recs.filter (fun r => !rsDigit r)).map rsRot)).reverse) (S b0)
        (by simpa using bankEnd_not_mem_bankSyms _) _
        (by simp [rsLoopSt, h0, h1, h01, h01.symm, h0.symm])))
      (RunsIn.iff_runs.mpr (runs_popR_c b0 _ bankEnd (S b0)
        (by simp [Function.update_apply, h0.symm]))))))))
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.mono X (fun _ _ => trivial) le_rfl) ?_ ?_)
  · funext j
    simp only [rsLoopSt, rsPass, bankSyms_append, List.drop_length, List.take_length,
      Function.update_apply]
    split_ifs <;> simp_all [bankSyms]
  · rw [loopCost_const, List.length_reverse, List.length_reverse,
      bankSyms_length _ hZ, bankSyms_length _ hO, List.length_map, List.length_map]
    rw [hlen]
    apply le_of_eq
    ring

/-! ## The sort -/

theorem rsPass_length (recs : List (List Bool × List Bool)) :
    (rsPass recs).length = recs.length := by
  simp only [rsPass, List.length_append, List.length_map]
  have := List.length_eq_length_filter_add (l := recs) rsDigit
  omega

theorem rsPass_shape {A R : ℕ} (recs : List (List Bool × List Bool))
    (h : ∀ r ∈ recs, r.1.length = A ∧ r.2.length = R) :
    ∀ r ∈ rsPass recs, r.1.length = A ∧ r.2.length = R := by
  intro r hr
  simp only [rsPass, List.mem_append, List.mem_map, List.mem_filter] at hr
  rcases hr with ⟨q, ⟨hq, -⟩, rfl⟩ | ⟨q, ⟨hq, -⟩, rfl⟩ <;>
    exact ⟨(rsRot_length q).trans (h q hq).1, (h q hq).2⟩

theorem rsSort_length : ∀ (n : ℕ) (recs : List (List Bool × List Bool)),
    (rsSort n recs).length = recs.length
  | 0, _ => rfl
  | n + 1, recs => by rw [rsSort, rsPass_length, rsSort_length n recs]

theorem rsSort_shape {A R : ℕ} : ∀ (n : ℕ) (recs : List (List Bool × List Bool)),
    (∀ r ∈ recs, r.1.length = A ∧ r.2.length = R) →
      ∀ r ∈ rsSort n recs, r.1.length = A ∧ r.2.length = R
  | 0, _, h => h
  | n + 1, recs, h => rsPass_shape _ (rsSort_shape n recs h)

/-- The identity lens on the `Option Sym` register. -/
def idLensO : Lens (Option Sym) (Option Sym) where
  get v := v
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- **The radix sort**: the pass, run once per unit of the counter `natSyms A` on `c` (temporary
stack `t`). -/
def rsSortProg (bank b0 b1 c t : K) : SProg K := countdown idLensO c t (rsPassProg bank b0 b1)

omit [DecidableEq K] in
theorem closed_rsSortProg (bank b0 b1 c t : K) : (rsSortProg bank b0 b1 c t).Closed :=
  closed_countdown idLensO c t (closed_rsPassProg bank b0 b1)

/-- **The radix sort** (`rsSort_runs`): `A ≥ 1` passes on records with keys of length `A` and
payloads of length `R`; the bank becomes `bankSyms (rsSort A recs) ++ bankEnd :: l'`, the counter
segment on `c` is consumed (`c = ct`), every other stack is restored. Cost
`countdownCost (|recs|·(8A + 8R + 17) + 10) A ≤ A·(|recs|·(8A + 8R + 17) + 10) + 16A + 2`
(`countdownCost_le`). -/
theorem rsSort_runs {bank b0 b1 c t : K} (h0 : bank ≠ b0) (h1 : bank ≠ b1) (h01 : b0 ≠ b1)
    (hcb : c ≠ bank) (hct : c ≠ t) {A R : ℕ} (hA : 1 ≤ A) (recs : List (List Bool × List Bool))
    (hrec : ∀ r ∈ recs, r.1.length = A ∧ r.2.length = R) (l' ct : List Sym) (hctm : TermOK ct)
    (S : K → List Sym) (hS : S bank = bankSyms recs ++ bankEnd :: l')
    (hc : S c = natSyms A ++ ct) :
    Runs (rsSortProg bank b0 b1 c t) S
      (Function.update (Function.update S bank (bankSyms (rsSort A recs) ++ bankEnd :: l')) c ct)
      (fun _ => True) (countdownCost (fun _ => recs.length * (8 * A + 8 * R + 17) + 10) A) := by
  have key := runsIn_countdown (ρ := []) idLensO hct (body := rsPassProg bank b0 b1) A ct hctm
    (fun n => Function.update S bank (bankSyms (rsSort (A - n) recs) ++ bankEnd :: l'))
    (fun _ => recs.length * (8 * A + 8 * R + 17) + 10) (fun n hn => by
      have hsucc : A - n = A - (n + 1) + 1 := by omega
      have e := rsPass_runs h0 h1 h01 hA (rsSort (A - (n + 1)) recs)
        (rsSort_shape _ recs hrec) l'
        (Function.update (Function.update S bank
          (bankSyms (rsSort (A - (n + 1)) recs) ++ bankEnd :: l')) c (natSyms (n + 1) ++ ct))
        (by simp [hcb.symm])
      rw [rsSort_length] at e
      refine RunsIn.congr (RunsIn.iff_runs.mpr e) ?_ le_rfl
      rw [hsucc]
      funext j
      simp only [Function.update_apply, rsSort]
      split_ifs <;> simp_all)
  have hinit : Function.update (Function.update S bank
      (bankSyms (rsSort (A - A) recs) ++ bankEnd :: l')) c (natSyms A ++ ct) = S := by
    rw [Nat.sub_self, rsSort, ← hS, ← hc, Function.update_eq_self, Function.update_eq_self]
  rw [hinit, Nat.sub_zero] at key
  exact RunsIn.iff_runs.mp (RunsIn.mono key (fun _ _ => trivial) le_rfl)

end Runs

end SubNLogN.Machine.AppC.C7RadixAux
