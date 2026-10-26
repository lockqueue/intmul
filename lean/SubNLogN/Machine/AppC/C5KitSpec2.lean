/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5KitSpec

/-!
# Proposition A.7 kit builder, part 3 (`AppC/C5KitSpec2.lean`): stream macros, gates, the base case

Exact `Runs` specs of the multi-step kit components: a stream macro (`streamP`, its elementary L2
kernels in order, the array permuted by the composed inverse map `macroMap`), a gate (`gateP`, its
elementary L3 XORs in order), and the level-`0` interchange (`baseP`: mark, `K1PairPermMix` with
`π = prodComm` into `tmp2`, transfer back, unmark). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus

theorem permByInv_id (v : List (List Bool)) : permByInv id v = v := by
  simp only [permByInv]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range, id]
  rw [List.getD_eq_getElem _ _ h2]

section Spec2

variable {q W m : ℕ} {D : NetData W m} (hL : Leaves q D) [NeZero q]

theorem ctrOK_update {S : KK hL → List Sym} {k N1 G B : ℕ} (h : CtrOK (slotK hL) S k N1 G B)
    (x : Slot W) (hx : x ≠ .ck ∧ x ≠ .cN1 ∧ x ≠ .cG ∧ x ≠ .cB) (v : List Sym) :
    CtrOK (slotK hL) (Function.update S (slotK hL x) v) k N1 G B := by
  obtain ⟨r1, r3, r4, r5, t1, t3, t4, t5, e1, e3, e4, e5⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine ⟨r1, r3, r4, r5, t1, t3, t4, t5, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (fun h => h1 (slotK_inj hL h).symm)]; exact e1
  · rw [Function.update_of_ne (fun h => h2 (slotK_inj hL h).symm)]; exact e3
  · rw [Function.update_of_ne (fun h => h3 (slotK_inj hL h).symm)]; exact e4
  · rw [Function.update_of_ne (fun h => h4 (slotK_inj hL h).symm)]; exact e5

/-- One elementary stream kernel on the array of `arrSlot a`. -/
theorem streamStep_spec (i : SIdx D) (a : Option (Fin W)) (k Rt N1 G B w : ℕ)
    (u : List (List Bool)) (rest : List Sym) (S : KK hL → List Sym) (hk : 1 ≤ k) (hRt : 1 ≤ Rt)
    (hN1 : 1 ≤ N1) (hG : 1 ≤ G) (hB : 1 ≤ B) (hu : u.length = Rt * rowSize q m k N1 G B)
    (huw : ∀ p ∈ u, p.length = w) (hrest : BlkTerm rest)
    (hS : S (slotK hL (arrSlot a)) = arrSyms u ++ rest) (hctr : CtrOK (slotK hL) S k N1 G B) :
    Runs (callInj (ιS hL i a) (lS hL i) (pkS hL i).P) S
      (Function.update S (slotK hL (arrSlot a))
        (arrSyms (permByInv (streamMap q m i.op k N1 G B) u) ++ rest))
      (fun _ => True) ((pkS hL i).C * (vol u + 1)) := by
  obtain ⟨r1, r3, r4, r5, t1, t3, t4, t5, e1, e3, e4, e5⟩ := hctr
  refine runs_callInj_le (Q := fun _ => True) (ιS_inj hL i a) _ ?_ ?_ le_rfl
  · rw [show slotK hL (arrSlot a) = ιS hL i a (.inl 0) from rfl,
      Function.update_comp_eq_of_injective S (ιS_inj hL i a) (.inl 0)]
    exact (pkS hL i).spec k Rt N1 G B w u rest r1 r3 r4 r5 (S ∘ ιS hL i a) hk hRt hN1 hG hB hu
      huw hrest t1 t3 t4 t5 hS e1 e3 e4 e5
  · intro key hk'
    exact Function.update_of_ne (fun h => hk' (.inl 0) h.symm) _ _

/-- One elementary XOR `role t ← xorArr (role t) (role s)`. -/
theorem xorStep_spec (t s : Fin W) (hts : t ≠ s) (w : ℕ) (a b : List (List Bool))
    (ra rb : List Sym) (S : KK hL → List Sym) (hab : a.length = b.length)
    (ha : ∀ p ∈ a, p.length = w) (hb : ∀ p ∈ b, p.length = w) (hra : BlkTerm ra)
    (hrb : BlkTerm rb) (hSa : S (slotK hL (.role t)) = arrSyms a ++ ra)
    (hSb : S (slotK hL (.role s)) = arrSyms b ++ rb) :
    Runs (callInj (ιX hL t s) (lX hL) (pkX hL).P) S
      (Function.update S (slotK hL (.role t)) (arrSyms (xorArr a b) ++ ra)) (fun _ => True)
      ((pkX hL).C * (vol a + vol b + 1)) := by
  refine runs_callInj_le (Q := fun _ => True) (ιX_inj hL hts) _ ?_ ?_ le_rfl
  · rw [show slotK hL (.role t) = ιX hL t s (.inl 0) from rfl,
      Function.update_comp_eq_of_injective S (ιX_inj hL hts) (.inl 0)]
    exact (pkX hL).spec w a b ra rb (S ∘ ιX hL t s) hab ha hb hra hrb hSa hSb
  · intro key hk'
    exact Function.update_of_ne (fun h => hk' (.inl 0) h.symm) _ _

/-- **A stream macro**: its elementary kernels in order; the array is permuted by `macroMap`. -/
theorem streamP_spec (o : Fin D.nOps) (a : Option (Fin W)) (k Rt N1 G B w : ℕ)
    (v : List (List Bool)) (rest : List Sym) (S : KK hL → List Sym) (hk : 1 ≤ k) (hRt : 1 ≤ Rt)
    (hN1 : 1 ≤ N1) (hG : 1 ≤ G) (hB : 1 ≤ B) (hv : v.length = Rt * rowSize q m k N1 G B)
    (hvw : ∀ p ∈ v, p.length = w) (hrest : BlkTerm rest)
    (hS : S (slotK hL (arrSlot a)) = arrSyms v ++ rest) (hctr : CtrOK (slotK hL) S k N1 G B)
    (hx : arrSlot a ≠ .ck ∧ arrSlot a ≠ .cN1 ∧ arrSlot a ≠ .cG ∧ arrSlot a ≠ .cB) :
    Runs (streamP hL o a) S
      (Function.update S (slotK hL (arrSlot a))
        (arrSyms (permByInv (macroMap q m (D.ops o) k N1 G B) v) ++ rest)) (fun _ => True)
      ((((List.finRange (D.ops o).length).map fun pos => (pkS hL ⟨o, pos⟩).C).sum + 1) *
        (vol v + 1)) := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdv : rowSize q m k N1 G B ∣ v.length := by rw [hv]; exact Dvd.intro_left _ rfl
  have hlt : ∀ l : List (StreamOp m), ∀ y < v.length, macroMap q m l k N1 G B y < v.length :=
    fun l => macroMap_lt q m l k N1 G B v.length hq hk hdv
  have hwid : ∀ l, ∀ p ∈ permByInv (macroMap q m l k N1 G B) v, p.length = w :=
    fun l => permByInv_widths _ _ _ (hlt l) hvw
  have hvol : ∀ l, vol (permByInv (macroMap q m l k N1 G B) v) = vol v := fun l => by
    rw [vol_of_widths _ w (hwid l), vol_of_widths v w hvw, permByInv_length]
  set st : ℕ → KK hL → List Sym := fun i => Function.update S (slotK hL (arrSlot a))
    (arrSyms (permByInv (macroMap q m ((D.ops o).take i) k N1 G B) v) ++ rest) with hst
  have key := RunsIn.forEachProg (ρ := [])
    (fun pos => callInj (ιS hL ⟨o, pos⟩ a) (lS hL ⟨o, pos⟩) (pkS hL ⟨o, pos⟩).P)
    (fun pos => (pkS hL ⟨o, pos⟩).C * (vol v + 1)) (List.finRange (D.ops o).length) st
    (fun i hi => by
      generalize hp : (List.finRange (D.ops o).length)[i] = pos
      have hpi : pos.val = i := by rw [← hp]; simp
      subst hpi
      have h1 := streamStep_spec hL ⟨o, pos⟩ a k Rt N1 G B w
        (permByInv (macroMap q m ((D.ops o).take pos.val) k N1 G B) v) rest (st pos.val) hk hRt
        hN1 hG hB (by rw [permByInv_length, hv]) (hwid _) hrest
        (by simp only [hst, Function.update_self]) (ctrOK_update hL hctr _ hx _)
      rw [hvol] at h1
      have e : permByInv (streamMap q m (SIdx.op (⟨o, pos⟩ : SIdx D)) k N1 G B)
          (permByInv (macroMap q m ((D.ops o).take pos.val) k N1 G B) v) =
          permByInv (macroMap q m ((D.ops o).take (pos.val + 1)) k N1 G B) v := by
        rw [permByInv_comp _ _ v (fun y hy => streamMap_lt q m _ k N1 G B _ hq hk hdv y hy),
          ← macroMap_append_one, List.take_add_one, List.getElem?_eq_getElem pos.isLt,
          Option.toList_some]
        rfl
      have hfin : Function.update (st pos.val) (slotK hL (arrSlot a))
          (arrSyms (permByInv (streamMap q m (SIdx.op (⟨o, pos⟩ : SIdx D)) k N1 G B)
            (permByInv (macroMap q m ((D.ops o).take pos.val) k N1 G B) v)) ++ rest) =
          st (pos.val + 1) := by
        simp only [hst, Function.update_idem, e]
      rw [hfin] at h1
      exact h1)
  have h0 : st 0 = S := by
    simp only [hst, List.take_zero]
    rw [show macroMap q m [] k N1 G B = id from rfl, permByInv_id, ← hS, Function.update_eq_self]
  have hn : st (List.finRange (D.ops o).length).length = Function.update S (slotK hL (arrSlot a))
      (arrSyms (permByInv (macroMap q m (D.ops o) k N1 G B) v) ++ rest) := by
    simp only [hst, List.length_finRange, List.take_length]
  rw [h0, hn] at key
  refine RunsIn.iff_runs.1 (RunsIn.mono key (fun _ _ => trivial) ?_)
  rw [List.sum_map_mul_right]
  generalize ((List.finRange (D.ops o).length).map fun pos => (pkS hL ⟨o, pos⟩).C).sum = A
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem fun_update_arr (cur : Fin W → List (List Bool)) (rests : Fin W → List Sym) (t : Fin W)
    (X : List (List Bool)) :
    (fun r => arrSyms (Function.update cur t X r) ++ rests r) =
      Function.update (fun r => arrSyms (cur r) ++ rests r) t (arrSyms X ++ rests t) := by
  funext r
  by_cases hr : r = t
  · subst hr; simp
  · simp [Function.update_of_ne hr]

theorem setRoles_update (F : KK hL → List Sym) (f : Fin W → List Sym) (t : Fin W) (x : List Sym) :
    setRoles (roleOfK hL) F (Function.update f t x) =
      Function.update (setRoles (roleOfK hL) F f) (slotK hL (.role t)) x := by
  funext key
  rcases hk : roleOfK hL key with _ | r
  · have hne : key ≠ slotK hL (.role t) := fun h => by
      rw [h, roleOfK_slot] at hk
      simp [Slot.roleIdx] at hk
    rw [setRoles_noneK hL _ _ _ hk, Function.update_of_ne hne, setRoles_noneK hL _ _ _ hk]
  · have e := roleOfK_eq_some hL key r hk
    subst e
    rw [setRoles_roleK]
    by_cases hrt : r = t
    · subst hrt
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hrt,
        Function.update_of_ne (fun h => hrt (Slot.role.inj (slotK_inj hL h))), setRoles_roleK]

theorem setRoles_self (S : KK hL → List Sym) :
    setRoles (roleOfK hL) S (fun r => S (slotK hL (.role r))) = S := by
  funext key
  rcases hk : roleOfK hL key with _ | r
  · exact setRoles_noneK hL _ _ _ hk
  · have e := roleOfK_eq_some hL key r hk
    subst e
    rfl

/-- **A gate**: its elementary XORs in order. -/
theorem gateP_spec (g : Fin D.nG) (us : Fin W → List (List Bool)) (rests : Fin W → List Sym)
    (n w : ℕ) (S : KK hL → List Sym) (hn : ∀ r, (us r).length = n)
    (hw : ∀ r, ∀ p ∈ us r, p.length = w) (hrests : ∀ r, BlkTerm (rests r))
    (hS : ∀ r, S (slotK hL (.role r)) = arrSyms (us r) ++ rests r) :
    Runs (gateP hL g) S
      (setRoles (roleOfK hL) S fun r => arrSyms (gateApply (D.gates g) us r) ++ rests r)
      (fun _ => True) ((D.gates g).length * ((pkX hL).C * (2 * (n * (w + 1)) + 1)) + 1) := by
  set st : ℕ → KK hL → List Sym := fun i => setRoles (roleOfK hL) S
    (fun r => arrSyms (gateApply ((D.gates g).take i) us r) ++ rests r) with hst
  have key := RunsIn.forEachProg (ρ := []) (fun p => callInj (ιX hL p.1 p.2) (lX hL) (pkX hL).P)
    (fun _ => (pkX hL).C * (2 * (n * (w + 1)) + 1)) (D.gates g) st (fun i hi => by
      have hts : (D.gates g)[i].1 ≠ (D.gates g)[i].2 :=
        hL.gates_ne g _ (List.getElem_mem hi)
      obtain ⟨hcl, hcw⟩ := gateApply_shape ((D.gates g).take i) n w us hn hw
      have h1 := xorStep_spec hL _ _ hts w (gateApply ((D.gates g).take i) us (D.gates g)[i].1)
        (gateApply ((D.gates g).take i) us (D.gates g)[i].2) (rests _) (rests _) (st i)
        (by rw [hcl, hcl]) (hcw _) (hcw _) (hrests _) (hrests _) (setRoles_roleK hL _ _ _)
        (setRoles_roleK hL _ _ _)
      rw [vol_of_widths _ w (hcw _), vol_of_widths _ w (hcw _), hcl, hcl] at h1
      have hnext : gateApply ((D.gates g).take (i + 1)) us =
          xorStep (gateApply ((D.gates g).take i) us) (D.gates g)[i] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, gateApply,
          List.foldl_append]
        rfl
      have hfin : Function.update (st i) (slotK hL (.role (D.gates g)[i].1))
          (arrSyms (xorArr (gateApply ((D.gates g).take i) us (D.gates g)[i].1)
            (gateApply ((D.gates g).take i) us (D.gates g)[i].2)) ++ rests (D.gates g)[i].1) =
          st (i + 1) := by
        simp only [hst]
        rw [hnext, xorStep, fun_update_arr, setRoles_update]
      rw [hfin, show n * (w + 1) + n * (w + 1) + 1 = 2 * (n * (w + 1)) + 1 by ring] at h1
      exact h1)
  have h0 : st 0 = S := by
    simp only [hst, List.take_zero]
    rw [show gateApply [] us = us from rfl]
    conv_rhs => rw [← setRoles_self hL S]
    congr 1
    funext r
    rw [hS r]
  have hn' : st (D.gates g).length =
      setRoles (roleOfK hL) S fun r => arrSyms (gateApply (D.gates g) us r) ++ rests r := by
    simp only [hst, List.take_length]
  rw [h0, hn'] at key
  refine RunsIn.iff_runs.1 (RunsIn.mono key (fun _ _ => trivial) (le_of_eq ?_))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]

end Spec2

end SubNLogN.Machine.C5
