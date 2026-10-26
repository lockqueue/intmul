/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Radix

/-!
# Lemma A.9 repair: reinsertion on stacks (`Machine/AppC/C7Reinsert.lean`)

The reinsertion of the Lemma A.9 repair phase (Lemma A.9 (`lem:transfer13`)). The skeleton
`holeSyms hs ++ tag 15 :: …` lies on stack `H` (`tag 8` for a hole, `recSyms p` for a kept record),
the sorted bank `bankSyms recs ++ …` on stack `Bk`. Scanning the skeleton, a kept record is moved to
the reversed output on `tmp`; a hole takes the next bank record (its key is erased). Finally the
reversed output is moved, reversed once more, onto the destination stack `D`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

Result (`rinProg_runs`): `D` receives `arrSyms (fillHoles hs (recs.map Prod.snd))`; `H` and `Bk` lose
the skeleton (with its `tag 15`) and the bank records; `tmp` is restored. Exact program, generic stack
names, register `Option Sym`.
-/

namespace SubNLogN.Machine.AppC.C7RadixAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

/-- The skeleton terminator. -/
abbrev holeEnd : Sym := Sym.tag 15

/-- The hole marker. -/
abbrev holeMark : Sym := Sym.tag 8

section Programs

variable {K : Type}

/-- A hole: drop its marker, erase the key of the next bank record, move its payload and `sep`. -/
def rinHole (H Bk tmp : K) : SProg K :=
  .seq (popR H) (.seq (passE .sep2 Bk) (.seq (popR Bk) (.seq (passM .sep Bk tmp)
    (.seq (popR Bk) (pushC tmp .sep)))))

/-- A kept record: move its payload and `sep`. -/
def rinGood (H tmp : K) : SProg K := .seq (passM .sep H tmp) (.seq (popR H) (pushC tmp .sep))

/-- One skeleton entry. -/
def rinBody (H Bk tmp : K) : SProg K :=
  .seq (.seq (peekR H) (.ite (fun r => decide (r = some holeMark)) (rinHole H Bk tmp)
    (rinGood H tmp))) (peekR H)

/-- **Reinsertion.** -/
def rinProg (H Bk tmp D : K) : SProg K :=
  .seq (pushC tmp .mark) (.seq (.seq (peekR H) (.loop (notG holeEnd) (rinBody H Bk tmp)))
    (.seq (popR H) (.seq (passM .mark tmp D) (popR tmp))))

theorem closed_rinProg (H Bk tmp D : K) : (rinProg H Bk tmp D).Closed :=
  ⟨trivial, ⟨⟨trivial, ⟨⟨trivial, ⟨⟨trivial, ⟨closed_passE _ _, trivial, closed_passM _ _ _,
    trivial, trivial⟩⟩, ⟨closed_passM _ _ _, trivial, trivial⟩⟩⟩, trivial⟩⟩, trivial,
    closed_passM _ _ _, trivial⟩⟩

end Programs

/-! ## Entries -/

section Runs

variable {K : Type} [DecidableEq K]

theorem rinHole_runs {H Bk tmp : K} (hHB : H ≠ Bk) (hHt : H ≠ tmp) (hBt : Bk ≠ tmp)
    (kb q : List Bool) (h' b' : List Sym) (S : K → List Sym)
    (hH : S H = holeMark :: h') (hB : S Bk = keyedSyms (kb, q) ++ b') :
    Runs (rinHole H Bk tmp) S
      (Function.update (Function.update (Function.update S H h') Bk b') tmp
        ((SubNLogN.Machine.recSyms q).reverse ++ S tmp))
      (fun _ => True) (3 * kb.length + 4 * q.length + 8) := by
  have hkb : Sym.sep2 ∉ kb.map Sym.bit := by simp
  have hq : Sym.sep ∉ q.map Sym.bit := by simp
  have X := RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c H S holeMark h' hH))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_passE (src := Bk) (kb.map Sym.bit)
        (q.map Sym.bit ++ Sym.sep :: b') hkb _
        (by simp [hHB.symm, hB, keyedSyms])))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c Bk _ Sym.sep2 (q.map Sym.bit ++ Sym.sep :: b')
        (by simp)))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_passM hBt (q.map Sym.bit) b' hq _ (by simp)))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c Bk _ Sym.sep b'
        (by simp [Function.update_apply, hBt])))
      (RunsIn.iff_runs.mpr (runs_pushC_c tmp Sym.sep _))))))
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.mono X (fun _ _ => trivial) le_rfl) ?_
    (by simp only [List.length_map]; omega))
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all [SubNLogN.Machine.recSyms]

theorem rinGood_runs {H tmp : K} (hHt : H ≠ tmp) (p : List Bool) (h' : List Sym)
    (S : K → List Sym) (hH : S H = SubNLogN.Machine.recSyms p ++ h') :
    Runs (rinGood H tmp) S
      (Function.update (Function.update S H h') tmp
        ((SubNLogN.Machine.recSyms p).reverse ++ S tmp))
      (fun _ => True) (4 * p.length + 4) := by
  have hp : Sym.sep ∉ p.map Sym.bit := by simp
  have hH' : S H = p.map Sym.bit ++ Sym.sep :: h' := by
    rw [hH]; simp [SubNLogN.Machine.recSyms]
  have X := RunsIn.seq (RunsIn.iff_runs.mpr (runs_passM hHt (p.map Sym.bit) h' hp S hH'))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c H _ Sym.sep h'
        (by simp [hHt])))
      (RunsIn.iff_runs.mpr (runs_pushC_c tmp Sym.sep _)))
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.mono X (fun _ _ => trivial) le_rfl) ?_
    (by simp only [List.length_map]; omega))
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all [SubNLogN.Machine.recSyms]

/-- A hole entry; the register then holds the top of the rest of the skeleton. -/
theorem rinBody_hole_runs {H Bk tmp : K} (hHB : H ≠ Bk) (hHt : H ≠ tmp) (hBt : Bk ≠ tmp)
    (kb q : List Bool) (h' b' : List Sym) (S : K → List Sym)
    (hH : S H = holeMark :: h') (hB : S Bk = keyedSyms (kb, q) ++ b') :
    Runs (rinBody H Bk tmp) S
      (Function.update (Function.update (Function.update S H h') Bk b') tmp
        ((SubNLogN.Machine.recSyms q).reverse ++ S tmp))
      (fun v => v = h'.head?) (3 * kb.length + 4 * q.length + 11) := by
  have hpk : RunsIn [] (peekR H) S S
      (fun v => (fun r => decide (r = some holeMark)) v = true) 1 :=
    RunsIn.mono (RunsIn.iff_runs.mpr (runs_peekR_c H S)) (fun v hv => by simp [hv, hH]) le_rfl
  have X := RunsIn.ite_true (Pf := rinGood H tmp) hpk
    (RunsIn.iff_runs.mpr (rinHole_runs hHB hHt hBt kb q h' b' S hH hB))
  have Y := RunsIn.seq X (RunsIn.iff_runs.mpr (runs_peekR_c H _))
  exact RunsIn.iff_runs.mp (RunsIn.mono Y
    (fun v hv => hv.trans (by simp [hHB, hHt])) (by omega))

/-- A kept-record entry. -/
theorem rinBody_good_runs {H Bk tmp : K} (hHt : H ≠ tmp)
    (p : List Bool) (h' : List Sym) (S : K → List Sym)
    (hH : S H = SubNLogN.Machine.recSyms p ++ h') :
    Runs (rinBody H Bk tmp) S
      (Function.update (Function.update S H h') tmp
        ((SubNLogN.Machine.recSyms p).reverse ++ S tmp))
      (fun v => v = h'.head?) (4 * p.length + 7) := by
  have hpk : RunsIn [] (peekR H) S S
      (fun v => (fun r => decide (r = some holeMark)) v = false) 1 := by
    refine RunsIn.mono (RunsIn.iff_runs.mpr (runs_peekR_c H S)) (fun v hv => ?_) le_rfl
    rw [hv, hH]
    cases p <;> simp [SubNLogN.Machine.recSyms]
  have X := RunsIn.ite_false (Pt := rinHole H Bk tmp) hpk
    (RunsIn.iff_runs.mpr (rinGood_runs hHt p h' S hH))
  have Y := RunsIn.seq X (RunsIn.iff_runs.mpr (runs_peekR_c H _))
  exact RunsIn.iff_runs.mp (RunsIn.mono Y
    (fun v hv => hv.trans (by simp [hHt])) (by omega))

end Runs

/-! ## Skeleton lists -/

theorem holeCount_append (a b : List (Option (List Bool))) :
    holeCount (a ++ b) = holeCount a + holeCount b := by
  simp [holeCount]

theorem holeCount_some (p : List Bool) : holeCount [some p] = 0 := by simp [holeCount]

theorem holeCount_none : holeCount [none] = 1 := by simp [holeCount]

theorem holeCount_take_le (hs : List (Option (List Bool))) (i : ℕ) :
    holeCount (hs.take i) ≤ holeCount hs := by
  conv_rhs => rw [← List.take_append_drop i hs]
  rw [holeCount_append]
  omega

theorem fillHoles_snoc_some (xs : List (Option (List Bool))) (p : List Bool) (ps : List (List Bool))
    (h : holeCount xs ≤ ps.length) : fillHoles (xs ++ [some p]) ps = fillHoles xs ps ++ [p] := by
  rw [fillHoles_append xs [some p] ps h]
  rfl

theorem fillHoles_snoc_none (xs : List (Option (List Bool))) (ps : List (List Bool))
    (h : holeCount xs < ps.length) :
    fillHoles (xs ++ [none]) ps = fillHoles xs ps ++ [ps[holeCount xs]] := by
  rw [fillHoles_append xs [none] ps h.le, List.drop_eq_getElem_cons h]
  rfl

theorem holeSyms_cons_none (os : List (Option (List Bool))) :
    holeSyms (none :: os) = Sym.tag 8 :: holeSyms os := rfl

theorem holeSyms_cons_some (p : List Bool) (os : List (Option (List Bool))) :
    holeSyms (some p :: os) = SubNLogN.Machine.recSyms p ++ holeSyms os := rfl

theorem arrSyms_snoc (a : List (List Bool)) (p : List Bool) :
    SubNLogN.Machine.arrSyms (a ++ [p]) = SubNLogN.Machine.arrSyms a ++ SubNLogN.Machine.recSyms p := by
  simp [SubNLogN.Machine.arrSyms, blk]

/-! ## The reinsertion loop -/

section Loop

variable {K : Type} [DecidableEq K]

/-- State of the reinsertion loop after the first `i` skeleton entries. -/
def rinSt (H Bk tmp : K) (S : K → List Sym) (hs : List (Option (List Bool)))
    (recs : List (List Bool × List Bool)) (h' b' T0 : List Sym) (i : ℕ) : K → List Sym :=
  Function.update (Function.update (Function.update S H (holeSyms (hs.drop i) ++ holeEnd :: h'))
      Bk (bankSyms (recs.drop (holeCount (hs.take i))) ++ b'))
    tmp ((SubNLogN.Machine.arrSyms (fillHoles (hs.take i) (recs.map Prod.snd))).reverse ++
      Sym.mark :: T0)

theorem rinSt_H {H Bk tmp : K} (hHB : H ≠ Bk) (hHt : H ≠ tmp) (S : K → List Sym)
    (hs : List (Option (List Bool))) (recs : List (List Bool × List Bool)) (h' b' T0 : List Sym)
    (i : ℕ) : rinSt H Bk tmp S hs recs h' b' T0 i H = holeSyms (hs.drop i) ++ holeEnd :: h' := by
  simp [rinSt, hHB, hHt]

theorem rinSt_Bk {H Bk tmp : K} (hBt : Bk ≠ tmp) (S : K → List Sym)
    (hs : List (Option (List Bool))) (recs : List (List Bool × List Bool)) (h' b' T0 : List Sym)
    (i : ℕ) : rinSt H Bk tmp S hs recs h' b' T0 i Bk =
      bankSyms (recs.drop (holeCount (hs.take i))) ++ b' := by
  simp [rinSt, hBt]

theorem rinSt_zero {H Bk tmp : K} (S : K → List Sym) (hs : List (Option (List Bool)))
    (recs : List (List Bool × List Bool)) (h' b' T0 : List Sym)
    (hH : S H = holeSyms hs ++ holeEnd :: h') (hB : S Bk = bankSyms recs ++ b')
    (hT : S tmp = Sym.mark :: T0) : rinSt H Bk tmp S hs recs h' b' T0 0 = S := by
  funext j
  simp only [rinSt, List.drop_zero, List.take_zero, Function.update_apply]
  split_ifs <;> simp_all [holeCount, fillHoles, SubNLogN.Machine.arrSyms, blk]

theorem holeSyms_head_ne {o : Option (List Bool)} {os : List (Option (List Bool))} {X : List Sym} :
    (holeSyms (o :: os) ++ X).head? ≠ some holeEnd := by
  rcases o with _ | p
  · simp [holeSyms]
  · cases p <;> simp [holeSyms, SubNLogN.Machine.recSyms]

/-- **The reinsertion loop** (kept records of length `R`, bank keys of length `A`, payloads of length
`R`, at most as many holes as bank records). Cost `1 + loopCost (3A + 4R + 11) |hs|`. -/
theorem rinLoop_runs {H Bk tmp : K} (hHB : H ≠ Bk) (hHt : H ≠ tmp) (hBt : Bk ≠ tmp) {A R : ℕ}
    (hs : List (Option (List Bool))) (recs : List (List Bool × List Bool))
    (hhs : ∀ p, some p ∈ hs → p.length = R)
    (hrec : ∀ r ∈ recs, r.1.length = A ∧ r.2.length = R)
    (hcount : holeCount hs ≤ recs.length) (h' b' T0 : List Sym) (S : K → List Sym)
    (hH : S H = holeSyms hs ++ holeEnd :: h') (hB : S Bk = bankSyms recs ++ b')
    (hT : S tmp = Sym.mark :: T0) :
    Runs (.seq (peekR H) (.loop (notG holeEnd) (rinBody H Bk tmp))) S
      (rinSt H Bk tmp S hs recs h' b' T0 hs.length) (fun v => notG holeEnd v = false)
      (1 + loopCost (fun _ => 3 * A + 4 * R + 11) hs.length) := by
  have hhead : ∀ i, i ≤ hs.length →
      notG holeEnd (holeSyms (hs.drop i) ++ holeEnd :: h').head? = decide (i < hs.length) := by
    intro i hi
    rcases Nat.lt_or_ge i hs.length with h | h
    · rw [List.drop_eq_getElem_cons h]
      have := holeSyms_head_ne (o := hs[i]) (os := hs.drop (i + 1)) (X := holeEnd :: h')
      simp only [notG, h, decide_true, decide_eq_true_eq]
      exact this
    · have : i = hs.length := le_antisymm hi h
      subst this
      simp [holeSyms, notG]
  have h₀ : RunsIn [] (peekR H) (rinSt H Bk tmp S hs recs h' b' T0 (hs.length - hs.length))
      (rinSt H Bk tmp S hs recs h' b' T0 (hs.length - hs.length))
      (fun v => notG holeEnd v = decide (0 < hs.length)) 1 := by
    refine RunsIn.mono (RunsIn.iff_runs.mpr (runs_peekR_c H _)) (fun v hv => ?_) le_rfl
    rw [hv, rinSt_H hHB hHt, hhead _ (Nat.sub_le _ _)]
    simp
  have hstep : ∀ n, n < hs.length →
      RunsIn [] (rinBody H Bk tmp) (rinSt H Bk tmp S hs recs h' b' T0 (hs.length - (n + 1)))
        (rinSt H Bk tmp S hs recs h' b' T0 (hs.length - n))
        (fun v => notG holeEnd v = decide (0 < n)) (3 * A + 4 * R + 11) := by
    intro n hn
    have hi : hs.length - (n + 1) < hs.length := by omega
    have hsucc : hs.length - n = hs.length - (n + 1) + 1 := by omega
    have htake : hs.take (hs.length - (n + 1) + 1) =
        hs.take (hs.length - (n + 1)) ++ [hs[hs.length - (n + 1)]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    have hreg : ∀ v, v = (holeSyms (hs.drop (hs.length - (n + 1) + 1)) ++ holeEnd :: h').head? →
        notG holeEnd v = decide (0 < n) := by
      intro v hv
      rw [hv, hhead _ (by omega)]
      simp only [decide_eq_decide]
      omega
    have hHi : rinSt H Bk tmp S hs recs h' b' T0 (hs.length - (n + 1)) H =
        holeSyms (hs.drop (hs.length - (n + 1))) ++ holeEnd :: h' := rinSt_H hHB hHt _ _ _ _ _ _ _
    rw [List.drop_eq_getElem_cons hi] at hHi
    rw [hsucc]
    cases he : hs[hs.length - (n + 1)] with
    | some p =>
      rw [he, holeSyms_cons_some, List.append_assoc] at hHi
      have hp : p.length = R := hhs p (he ▸ List.getElem_mem hi)
      have e := rinBody_good_runs (Bk := Bk) hHt p _ _ hHi
      refine RunsIn.mono (RunsIn.congr (RunsIn.iff_runs.mpr e) ?_ le_rfl) hreg (by omega)
      have hc : holeCount (hs.take (hs.length - (n + 1))) ≤ (recs.map Prod.snd).length := by
        have := holeCount_take_le hs (hs.length - (n + 1))
        simp only [List.length_map]
        omega
      funext j
      simp only [rinSt, htake, he, holeCount_append, holeCount_some, Nat.add_zero,
        fillHoles_snoc_some _ p _ hc, arrSyms_snoc, List.reverse_append, Function.update_apply]
      split_ifs <;> simp_all
    | none =>
      rw [he, holeSyms_cons_none, List.cons_append] at hHi
      have hlt : holeCount (hs.take (hs.length - (n + 1))) < recs.length := by
        have h1 := holeCount_take_le hs (hs.length - (n + 1) + 1)
        rw [htake, he, holeCount_append, holeCount_none] at h1
        omega
      have hBi : rinSt H Bk tmp S hs recs h' b' T0 (hs.length - (n + 1)) Bk =
          keyedSyms recs[holeCount (hs.take (hs.length - (n + 1)))] ++
            (bankSyms (recs.drop (holeCount (hs.take (hs.length - (n + 1))) + 1)) ++ b') := by
        rw [rinSt_Bk hBt, List.drop_eq_getElem_cons hlt, bankSyms_cons, List.append_assoc]
      obtain ⟨hk, hq⟩ := hrec _ (List.getElem_mem hlt)
      have e := rinBody_hole_runs hHB hHt hBt _ _ _ _ _ hHi hBi
      refine RunsIn.mono (RunsIn.congr (RunsIn.iff_runs.mpr e) ?_ le_rfl) hreg
        (by simp only [List.get_eq_getElem]; omega)
      have hc : holeCount (hs.take (hs.length - (n + 1))) < (recs.map Prod.snd).length := by
        simpa using hlt
      funext j
      simp only [rinSt, htake, he, holeCount_append, holeCount_none,
        fillHoles_snoc_none _ _ hc, arrSyms_snoc, List.reverse_append, List.getElem_map,
        Function.update_apply]
      split_ifs <;> simp_all
  have key := RunsIn.seq_loop (st := fun n => rinSt H Bk tmp S hs recs h' b' T0 (hs.length - n))
    h₀ hstep
  simp only [Nat.sub_self, Nat.sub_zero, rinSt_zero S hs recs h' b' T0 hH hB hT] at key
  exact RunsIn.iff_runs.mp key

end Loop

/-! ## Reinsertion -/

theorem fillHoles_length : ∀ (hs : List (Option (List Bool))) (ps : List (List Bool)),
    holeCount hs ≤ ps.length → (fillHoles hs ps).length = hs.length
  | [], _, _ => rfl
  | some p :: hs, ps, h => by
    simp only [fillHoles, List.length_cons]
    rw [fillHoles_length hs ps (by simpa [holeCount] using h)]
  | none :: hs, [], h => by simp [holeCount] at h
  | none :: hs, q :: ps, h => by
    simp only [fillHoles, List.length_cons]
    rw [fillHoles_length hs ps (by simp [holeCount] at h ⊢; omega)]

theorem fillHoles_mem_len {R : ℕ} : ∀ (hs : List (Option (List Bool))) (ps : List (List Bool)),
    (∀ p, some p ∈ hs → p.length = R) → (∀ q ∈ ps, q.length = R) →
      ∀ x ∈ fillHoles hs ps, x.length = R
  | [], _, _, _ => by simp [fillHoles]
  | some p :: hs, ps, hh, hp => by
    intro x hx
    simp only [fillHoles, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hh x (List.mem_cons_self)
    · exact fillHoles_mem_len hs ps (fun p' hp' => hh p' (List.mem_cons_of_mem _ hp')) hp x hx
  | none :: hs, [], hh, hp => by
    intro x hx
    simp only [fillHoles] at hx
    exact fillHoles_mem_len hs [] (fun p' hp' => hh p' (List.mem_cons_of_mem _ hp')) hp x hx
  | none :: hs, q :: ps, hh, hp => by
    intro x hx
    simp only [fillHoles, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hp x List.mem_cons_self
    · exact fillHoles_mem_len hs ps (fun p' hp' => hh p' (List.mem_cons_of_mem _ hp'))
        (fun q' hq' => hp q' (List.mem_cons_of_mem _ hq')) x hx

theorem arrSyms_length_of {R : ℕ} : ∀ (v : List (List Bool)), (∀ p ∈ v, p.length = R) →
    (SubNLogN.Machine.arrSyms v).length = v.length * (R + 1)
  | [], _ => by simp [SubNLogN.Machine.arrSyms, blk]
  | p :: v, h => by
    have ih := arrSyms_length_of v (fun q hq => h q (List.mem_cons_of_mem p hq))
    simp only [SubNLogN.Machine.arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      SubNLogN.Machine.recSyms, List.length_map, List.length_singleton] at ih ⊢
    rw [ih, h p List.mem_cons_self, List.length_cons]
    ring

theorem mark_not_mem_arrSyms (v : List (List Bool)) : Sym.mark ∉ SubNLogN.Machine.arrSyms v := by
  simp [SubNLogN.Machine.arrSyms, blk, SubNLogN.Machine.recSyms]

section Final

variable {K : Type} [DecidableEq K]

/-- **Reinsertion** (`rinProg_runs`): with the skeleton `holeSyms hs ++ tag 15 :: h'` on `H` and the
bank `bankSyms recs ++ b'` on `Bk` (exactly as many bank records as holes; kept records and bank
payloads of length `R`, keys of length `A`), the destination `D` receives
`arrSyms (fillHoles hs (recs.map Prod.snd))` on top of its content; `H := h'`, `Bk := b'`, `tmp`
restored. Cost `|hs|·(3A + 8R + 16) + 7`. -/
theorem rinProg_runs {H Bk tmp D : K} (hHB : H ≠ Bk) (hHt : H ≠ tmp) (hBt : Bk ≠ tmp)
    (htD : tmp ≠ D) (hHD : H ≠ D) (hBD : Bk ≠ D) {A R : ℕ}
    (hs : List (Option (List Bool))) (recs : List (List Bool × List Bool))
    (hhs : ∀ p, some p ∈ hs → p.length = R)
    (hrec : ∀ r ∈ recs, r.1.length = A ∧ r.2.length = R)
    (hcount : holeCount hs = recs.length) (h' b' : List Sym) (S : K → List Sym)
    (hH : S H = holeSyms hs ++ holeEnd :: h') (hB : S Bk = bankSyms recs ++ b') :
    Runs (rinProg H Bk tmp D) S
      (Function.update (Function.update (Function.update S H h') Bk b') D
        (SubNLogN.Machine.arrSyms (fillHoles hs (recs.map Prod.snd)) ++ S D))
      (fun _ => True) (hs.length * (3 * A + 8 * R + 16) + 7) := by
  have hps : ∀ q ∈ recs.map Prod.snd, q.length = R := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact (hrec r hr).2
  have hout := fillHoles_mem_len hs (recs.map Prod.snd) hhs hps
  have hlen := fillHoles_length hs (recs.map Prod.snd) (by simp [hcount])
  have eL := rinLoop_runs hHB hHt hBt hs recs hhs hrec hcount.le h' b' (S tmp)
    (Function.update S tmp (Sym.mark :: S tmp)) (by simp [hHt, hH]) (by simp [hBt, hB]) (by simp)
  have X := RunsIn.seq (RunsIn.iff_runs.mpr (runs_pushC_c tmp Sym.mark S))
    (RunsIn.seq (RunsIn.iff_runs.mpr eL)
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR_c H _ holeEnd h'
        (by simp [rinSt, hHB, hHt, holeSyms])))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_passM htD
        ((SubNLogN.Machine.arrSyms (fillHoles hs (recs.map Prod.snd))).reverse) (S tmp)
        (by simpa using mark_not_mem_arrSyms _) _
        (by simp [rinSt, hHt.symm])))
      (RunsIn.iff_runs.mpr (runs_popR_c tmp _ Sym.mark (S tmp) (by simp [htD]))))))
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.mono X (fun _ _ => trivial) le_rfl) ?_ ?_)
  · funext j
    simp only [rinSt, List.drop_length, List.take_length, hcount, Function.update_apply]
    split_ifs <;> simp_all [holeSyms, bankSyms]
  · rw [loopCost_const, List.length_reverse, arrSyms_length_of _ hout, hlen]
    apply le_of_eq
    ring

end Final

end SubNLogN.Machine.AppC.C7RadixAux
