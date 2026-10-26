/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadStageBase

/-!
# K5 spreading, stage loop: the lines of one group (`Bridge/SpreadStageInner.lean`)

`Stage.lineWalk_holds : Stage.LineWalkStmt` (the interface frozen in `SpreadStageBase.lean`): the
inner walk of one group runs the line step `PL` (`SpreadLineSpec`) on `rep` consecutive lines
`l0, …, l0 + rep - 1` of `xs`, then moves the marks of `X 4` back onto `ru rep`.

Proof: `runs_walkL` over the family `StageInner.st j` (the lines `l0 + j, …` on `arr`, the outputs
of the first `j` lines on `Out`, `rep - j` marks on `ru rep`, `j` marks on `X 4`); each body run is
one `SpreadLineSpec` call (`st_step` identifies its final state with `st (j + 1)`); then
`moveMarks_eval`. Cost `rep·(CL·lineCost + 4) + 2 + (4·rep + 2)`.

**Scope (honest summary).** Everything here is proved. Helpers live in
`SubNLogN.Machine.Bridge.SpreadAux.StageInner`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux.StageInner

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux SubNLogN.Machine.Bridge.SpreadAux.Stage SubNLogN.Math.Common
  SubNLogN.Math.Bridge

theorem carrSyms_append_si (w : ℕ) (u v : List (List CInt)) :
    carrSyms w (u ++ v) = carrSyms w u ++ carrSyms w v := by
  simp [carrSyms, arrSyms, blk]

theorem carrSyms_nil_si (w : ℕ) : carrSyms w [] = [] := by
  simp [carrSyms, arrSyms, blk]

theorem grpOuts_zero_si (q t W a0 : ℕ) (xs F : List CInt) (l0 : ℕ) :
    grpOuts q t W a0 xs F l0 0 = [] := by
  simp [grpOuts]

theorem grpOuts_succ_si (q t W a0 : ℕ) (xs F : List CInt) (l0 j : ℕ) :
    grpOuts q t W a0 xs F l0 (j + 1) =
      grpOuts q t W a0 xs F l0 j ++ lineOut q t W a0 ((xs.drop ((l0 + j) * t)).take t) F := by
  simp [grpOuts, List.range_succ, List.flatMap_append]

/-- The array `arr` split after one line. -/
theorem carr_drop_split (w : ℕ) (xs : List CInt) (a t : ℕ) (rarr : List Sym) :
    carrSyms w ((xs.drop a).map fun x => [x]) ++ rarr =
      carrSyms w (((xs.drop a).take t).map fun x => [x]) ++
        (carrSyms w ((xs.drop (a + t)).map fun x => [x]) ++ rarr) := by
  have h : xs.drop (a + t) = (xs.drop a).drop t := by simp [List.drop_drop]
  rw [h, ← List.append_assoc, ← carrSyms_append_si, ← List.map_append, List.take_append_drop]

section Ne

variable {Es : Type}

theorem ne_Out_X4 : (sp .Out : SK Es) ≠ sp (.X 4) := by simp
theorem ne_Out_rep : (sp .Out : SK Es) ≠ sp (.ru .rep) := by simp
theorem ne_Out_arr : (sp .Out : SK Es) ≠ kW .arr := by simp
theorem ne_arr_X4 : (kW .arr : SK Es) ≠ sp (.X 4) := by simp
theorem ne_arr_rep : (kW .arr : SK Es) ≠ sp (.ru .rep) := by simp
theorem ne_rep_X4 : (sp (.ru .rep) : SK Es) ≠ sp (.X 4) := by simp

/-- A line-scratch stack is none of `arr`, `Out`, `ru rep`, `X 4`. -/
theorem lineScratch_ne {x : SpS} (hx : LineScratch x) :
    (sp x : SK Es) ≠ kW .arr ∧ (sp x : SK Es) ≠ sp .Out ∧ (sp x : SK Es) ≠ sp (.ru .rep) ∧
      (sp x : SK Es) ≠ sp (.X 4) := by
  refine ⟨by simp, ?_, ?_, ?_⟩ <;> intro h <;> simp only [sp, Sum.inr.injEq, Sum.inl.injEq] at h <;>
    subst h <;> simp [LineScratch] at hx

end Ne

variable {Es : Type} [DecidableEq Es]

/-- The state after `j` lines of the group. -/
def st (S : SK Es → List Sym) (wI q t W a0 rep l0 : ℕ) (xs F : List CInt) (rarr : List Sym)
    (j : ℕ) : SK Es → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (kW .arr)
    (carrSyms wI ((xs.drop ((l0 + j) * t)).map fun x => [x]) ++ rarr)) (sp .Out)
    ((carrSyms wI ((grpOuts q t W a0 xs F l0 j).map fun y => [y])).reverse ++ S (sp .Out)))
    (sp (.ru .rep)) (List.replicate (rep - j) .mark)) (sp (.X 4)) (List.replicate j .mark)

theorem st_other (S : SK Es → List Sym) (wI q t W a0 rep l0 : ℕ) (xs F : List CInt)
    (rarr : List Sym) (j : ℕ) (k : SK Es) (h1 : k ≠ kW .arr) (h2 : k ≠ sp .Out)
    (h3 : k ≠ sp (.ru .rep)) (h4 : k ≠ sp (.X 4)) :
    st S wI q t W a0 rep l0 xs F rarr j k = S k := by
  rw [st, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
    Function.update_of_ne h1]

theorem stP_other (S : SK Es → List Sym) (wI q t W a0 rep l0 : ℕ) (xs F : List CInt)
    (rarr : List Sym) (j : ℕ) (v1 v2 : List Sym) (k : SK Es) (h1 : k ≠ kW .arr)
    (h2 : k ≠ sp .Out) (h3 : k ≠ sp (.ru .rep)) (h4 : k ≠ sp (.X 4)) :
    Function.update (Function.update (st S wI q t W a0 rep l0 xs F rarr j) (sp (.ru .rep)) v1)
      (sp (.X 4)) v2 k = S k := by
  rw [Function.update_of_ne h4, Function.update_of_ne h3]
  exact st_other S wI q t W a0 rep l0 xs F rarr j k h1 h2 h3 h4

theorem st_zero (S : SK Es → List Sym) (wI q t W a0 rep l0 : ℕ) (xs F : List CInt)
    (rarr : List Sym) (harr : S (kW .arr) = carrSyms wI ((xs.drop (l0 * t)).map fun x => [x]) ++ rarr)
    (hX4 : S (sp (.X 4)) = []) (hrR : S (sp (.ru .rep)) = List.replicate rep .mark) :
    st S wI q t W a0 rep l0 xs F rarr 0 = S := by
  funext k
  simp only [st, Function.update_apply, Nat.add_zero, Nat.sub_zero, grpOuts_zero_si, List.map_nil,
    carrSyms_nil_si, List.reverse_nil, List.nil_append, List.replicate_zero]
  split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp_all

/-- One line step ends in `st (j + 1)`. -/
theorem st_step (S : SK Es → List Sym) (wI q t W a0 rep l0 : ℕ) (xs F : List CInt)
    (rarr : List Sym) (j : ℕ) :
    Function.update (Function.update
      (Function.update (Function.update (st S wI q t W a0 rep l0 xs F rarr j) (sp (.ru .rep))
        (List.replicate (rep - j - 1) .mark ++ [])) (sp (.X 4))
        (.mark :: st S wI q t W a0 rep l0 xs F rarr j (sp (.X 4))))
      (kW .arr) (carrSyms wI ((xs.drop ((l0 + j) * t + t)).map fun x => [x]) ++ rarr))
      (sp .Out) ((carrSyms wI ((lineOut q t W a0 ((xs.drop ((l0 + j) * t)).take t) F).map
        fun y => [y])).reverse ++
        Function.update (Function.update (st S wI q t W a0 rep l0 xs F rarr j) (sp (.ru .rep))
          (List.replicate (rep - j - 1) .mark ++ [])) (sp (.X 4))
          (.mark :: st S wI q t W a0 rep l0 xs F rarr j (sp (.X 4))) (sp .Out)) =
    st S wI q t W a0 rep l0 xs F rarr (j + 1) := by
  have hOut : Function.update (Function.update (st S wI q t W a0 rep l0 xs F rarr j)
      (sp (.ru .rep)) (List.replicate (rep - j - 1) .mark ++ [])) (sp (.X 4))
      (.mark :: st S wI q t W a0 rep l0 xs F rarr j (sp (.X 4))) (sp .Out) =
      (carrSyms wI ((grpOuts q t W a0 xs F l0 j).map fun y => [y])).reverse ++ S (sp .Out) := by
    rw [Function.update_of_ne ne_Out_X4, Function.update_of_ne ne_Out_rep, st,
      Function.update_of_ne ne_Out_X4, Function.update_of_ne ne_Out_rep, Function.update_self]
  have hX4 : st S wI q t W a0 rep l0 xs F rarr j (sp (.X 4)) = List.replicate j .mark := by
    rw [st, Function.update_self]
  rw [hOut, hX4, show (l0 + j) * t + t = (l0 + (j + 1)) * t by ring, ← List.append_assoc,
    ← List.reverse_append, ← carrSyms_append_si, ← List.map_append, ← grpOuts_succ_si]
  funext k
  simp only [st, Function.update_apply]
  split_ifs <;> simp_all <;> rfl

/-- The final state after the walk and the ruler restoration. -/
theorem st_final (S : SK Es → List Sym) (wI q t W a0 rep l0 : ℕ) (xs F : List CInt)
    (rarr : List Sym) (hX4 : S (sp (.X 4)) = []) (hrR : S (sp (.ru .rep)) = List.replicate rep .mark) :
    Function.update (Function.update (st S wI q t W a0 rep l0 xs F rarr rep) (sp (.X 4)) [])
      (sp (.ru .rep)) (List.replicate rep .mark ++ st S wI q t W a0 rep l0 xs F rarr rep
        (sp (.ru .rep))) =
    Function.update (Function.update S (kW .arr)
        (carrSyms wI ((xs.drop ((l0 + rep) * t)).map fun x => [x]) ++ rarr))
      (sp .Out) ((carrSyms wI ((grpOuts q t W a0 xs F l0 rep).map fun y => [y])).reverse ++
        S (sp .Out)) := by
  have hR : st S wI q t W a0 rep l0 xs F rarr rep (sp (.ru .rep)) = [] := by
    rw [st, Function.update_of_ne ne_rep_X4, Function.update_self, Nat.sub_self,
      List.replicate_zero]
  rw [hR, List.append_nil]
  funext k
  simp only [st, Function.update_apply]
  split_ifs <;> simp_all

end StageInner

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux.Stage SubNLogN.Math.Common SubNLogN.Math.Bridge

open StageInner in
/-- **The lines of one group** (`LineWalkStmt`, the interface of `Bridge/SpreadStageLoop.lean`). -/
theorem Stage.lineWalk_holds : Stage.LineWalkStmt := by
  intro Es σ _ lA PL CL hPL s wI wT q t W a0 rep l0 xs F rarr S hlen hFW hW1 hWt ha0 hwI hwIs hq
    hX hF hslot1 hslot2 hY harr hFk hX4 hrR hs hsq hh hwIr hWm1 hWr hwI1 hsWI hp0 hp1 hp2 hp3 hp4
    hLS
  -- the body: one line step from `st j` (one more mark moved) to `st (j + 1)`
  have hb : ∀ j < rep, Runs PL (Function.update (Function.update
      (st S wI q t W a0 rep l0 xs F rarr j) (sp (.ru .rep)) (List.replicate (rep - j - 1) .mark ++ []))
      (sp (.X 4)) (.mark :: st S wI q t W a0 rep l0 xs F rarr j (sp (.X 4))))
      (st S wI q t W a0 rep l0 xs F rarr (j + 1)) (fun _ => True) (CL * lineCost s t W) := by
    intro j hj
    have hlt : (l0 + j) * t + t ≤ xs.length := by
      have e : (l0 + j) * t + t = (l0 + (j + 1)) * t := by ring
      have h2 : (l0 + (j + 1)) * t ≤ (l0 + rep) * t := Nat.mul_le_mul_right _ (by omega)
      omega
    have hXlen : ((xs.drop ((l0 + j) * t)).take t).length = t := by
      rw [List.length_take, List.length_drop]
      omega
    have ho := fun k h1 h2 h3 h4 => stP_other S wI q t W a0 rep l0 xs F rarr j
      (List.replicate (rep - j - 1) .mark ++ [])
      (.mark :: st S wI q t W a0 rep l0 xs F rarr j (sp (.X 4))) k h1 h2 h3 h4
    refine WP.W9comp.runs_congr (hPL s wI wT q t W a0 ((xs.drop ((l0 + j) * t)).take t) F
      (carrSyms wI ((xs.drop ((l0 + j) * t + t)).map fun x => [x]) ++ rarr) _ hXlen hFW hW1 hWt ha0
      hwI hwIs hq (fun x hx => hX x (List.mem_of_mem_drop (List.mem_of_mem_take hx))) hF hslot1
      hslot2 (fun y hy => hY y (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, hy⟩)) ?_ ?_
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hs)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hsq)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hh)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hwIr)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hWm1)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hWr)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hwI1)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hsWI)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hp0)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hp1)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hp2)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hp3)
      (by rw [ho _ (by simp) (by simp) (by simp) (by simp)]; exact hp4) ?_)
      (st_step S wI q t W a0 rep l0 xs F rarr j)
    · rw [Function.update_of_ne ne_arr_X4, Function.update_of_ne ne_arr_rep, st,
        Function.update_of_ne ne_arr_X4, Function.update_of_ne ne_arr_rep,
        Function.update_of_ne ne_Out_arr.symm, Function.update_self]
      exact carr_drop_split wI xs ((l0 + j) * t) t rarr
    · intro k
      rw [ho _ (by simp) (by simp) (by simp) (by simp)]
      exact hFk k
    · intro x hx
      obtain ⟨n1, n2, n3, n4⟩ := lineScratch_ne (Es := Es) hx
      rw [ho _ n1 n2 n3 n4]
      exact hLS x hx
  -- the walk, then the ruler restoration
  have hw := runs_walkL lA ne_rep_X4 PL rep [] [] (by simp) (st S wI q t W a0 rep l0 xs F rarr)
    (fun j _ => by rw [st, Function.update_of_ne ne_rep_X4, Function.update_self, List.append_nil])
    (fun j _ => by rw [st, Function.update_self, List.append_nil]) (CL * lineCost s t W) hb
  rw [st_zero S wI q t W a0 rep l0 xs F rarr harr hX4 hrR] at hw
  have hm : Runs (ar lA (moveMarks (sp (.X 4)) (sp (.ru .rep)))) (st S wI q t W a0 rep l0 xs F rarr rep)
      (Function.update (Function.update (st S wI q t W a0 rep l0 xs F rarr rep) (sp (.X 4)) [])
        (sp (.ru .rep)) (List.replicate rep .mark ++ st S wI q t W a0 rep l0 xs F rarr rep
          (sp (.ru .rep)))) (fun _ => True) (4 * rep + 2) :=
    runs_ar lA (Q := fun _ => True) (Runs.of_eval fun v => ⟨_, _, moveMarks_eval ne_rep_X4.symm rep [] v _ (by simp)
      (by rw [st, Function.update_self, List.append_nil]), trivial, le_rfl⟩)
  rw [st_final S wI q t W a0 rep l0 xs F rarr hX4 hrR] at hm
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq hw hm) (fun _ _ => trivial) ?_
  omega

end SubNLogN.Machine.Bridge.SpreadAux
