/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostLoop
import WP.W3b.DecAmortised

/-!
# K5-PP thermometer set-up and read-out (`Bridge/PrePostTherm.lean`)

* `zbProg C U T`: from a counter `natSyms n` on `C` (consumed), push `n` bits `false` on `T`
  (the empty thermometer of pass 1/2). Amortized cost `≤ 17 n + 6·bitLen n + 2`
  (`W3_dec_amortised_holds`, `WP/W3b/DecAmortised.lean`).
* `cntProg T N U`: pop the bit block of `T` (down to the stack bottom) and count its `true`
  bits in binary on `N` (`natSyms`). Amortized cost `≤ 20·(#bits) + 2` (`Lib.incSeqCost_le`).

**Scope (honest summary).** Programs and proved `Runs` lemmas (no `sorry`).
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability

variable {K : Type}

/-- One step of the zero-bit builder: decrement `C`, push `bit false` on `T`. -/
def zbBody (C U T : K) : PProg K := .seq ((dec C U).liftRegs lensPO) (.push T fun _ => .bit false)

/-- **Zero-bit builder.** -/
def zbProg (C U T : K) : PProg K :=
  .seq (peekT C) (.loop (fun v => isBitO v.t) (.seq (zbBody C U T) (peekT C)))

/-- One step of the counter: pop a bit of `T`; if it is `true`, increment `N`. -/
def cntBody (T N U : K) : PProg K :=
  .seq (.pop T fun v o => { v with o := o })
    (.ite (fun v => bitOf v.o) ((inc N U).liftRegs lensPO) (.load id))

/-- **Counter of `true` bits.** -/
def cntProg (T N U : K) : PProg K :=
  .seq (peekT T) (.loop (fun v => isBitO v.t) (.seq (cntBody T N U) (peekT T)))

theorem closed_zbProg (C U T : K) : (zbProg C U T).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, zbProg, zbBody, peekT, dec, decFix, scanLoop, scanBody,
    pushC, popR, peekR, skip, moveBits, moveBitsBody, pushR, Prog.liftRegs]

theorem closed_cntProg (T N U : K) : (cntProg T N U).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, cntProg, cntBody, peekT, inc, incFix, scanLoop, scanBody,
    pushC, popR, skip, moveBits, moveBitsBody, pushR, restoreR, Prog.liftRegs]

theorem isBitO_natSyms (n : ℕ) {L : List Sym} (hL : TermOK L) :
    isBitO (natSyms n ++ L).head? = decide (n ≠ 0) := by
  rcases h : encodeNat n with _ | ⟨b, l⟩
  · have := (encodeNat_eq_nil_iff n).mp h
    subst this
    simp [natSyms, h, isBitO_of_termOK hL]
  · have hn : n ≠ 0 := by
      intro h0
      subst h0
      simp [encodeNat_zero] at h
    simp [natSyms, h, hn]

variable [DecidableEq K]

/-- Cost of the zero-bit builder, as a sum. -/
theorem whileCost_zb (Tb : List Unit → Unit → List Unit → ℕ)
    (hTb : ∀ d x r, Tb d x r = 6 * zerosLead (encodeNat (r.length + 1)) + 9) :
    ∀ (k : ℕ) (done : List Unit), whileCost 1 Tb done (List.replicate k ()) =
      ((List.range k).map fun i => 6 * zerosLead (encodeNat (k - i)) + 11).sum + 1
  | 0, _ => by simp [whileCost]
  | k + 1, done => by
    rw [List.replicate_succ, whileCost, whileCost_zb Tb hTb k, hTb, List.length_replicate,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Nat.sub_zero, Function.comp_def, Nat.succ_sub_succ]
    omega

/-- **Zero-bit builder**, as `Runs`. -/
theorem runs_zbProg {C U T : K} (hCU : C ≠ U) (hCT : C ≠ T) (n : ℕ)
    (RC : List Sym) (S : K → List Sym) (hRC : TermOK RC) (hC : S C = natSyms n ++ RC) :
    Runs (zbProg C U T) S
      (Function.update (Function.update S C RC) T (List.replicate n (Sym.bit false) ++ S T))
      (fun _ => True) (17 * n + 6 * bitLen n + 2) := by
  let st : List Unit → List Unit → K → List Sym := fun done rest =>
    Function.update (Function.update S C (natSyms rest.length ++ RC)) T
      (List.replicate done.length (Sym.bit false) ++ S T)
  have h0 : st [] (List.replicate n ()) = S := by
    simp only [st, List.length_replicate, List.length_nil, List.replicate_zero, List.nil_append]
    rw [← hC, Function.update_eq_self, Function.update_eq_self]
  have hw := runs_while (pk := peekT C) (body := zbBody C U T) (c := fun v => isBitO v.t) st 1
    (fun _ _ r => 6 * zerosLead (encodeNat (r.length + 1)) + 9)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT C (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne hCT, Function.update_self] at hv
      show isBitO v.t = !rest.isEmpty
      rw [hv, isBitO_natSyms _ hRC]
      cases rest <;> simp)
    (fun done x rest => by
      refine Runs.of_eval fun v => ?_
      have e1 := Eval.liftRegs lensPO
        (dec_eval (ρ := []) hCU (lensPO.get v) rest.length RC (st done (x :: rest)) hRC
          (by simp [st, Function.update_of_ne hCT, natSyms])) v rfl
      have e2 := Eval.push (Γ := fun _ => Sym) [] T (fun _ : PReg => Sym.bit false) (lensPO.set v
        (some Sym.mark)) (Function.update (st done (x :: rest)) C
          ((encodeNat rest.length).map Sym.bit ++ RC))
      refine ⟨lensPO.set v (some Sym.mark), _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, le_refl _⟩
      congr 1
      funext k
      simp only [st, Function.update_apply, List.length_append, List.length_cons]
      split_ifs <;> simp_all [natSyms, List.replicate_succ])
    (List.replicate n ()) []
  rw [h0] at hw
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st, natSyms, encodeNat_zero]
  · rw [whileCost_zb _ (fun _ _ _ => rfl) n []]
    have ha := TMFw.W3b.W3_dec_amortised_holds n n le_rfl
    have key : ∀ l : List ℕ, (l.map fun i => 6 * zerosLead (encodeNat (n - i)) + 11).sum =
        6 * (l.map fun i => zerosLead (encodeNat (n - i)) + 1).sum + 5 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
        ring
    rw [key, List.length_range]
    omega

/-- Cost of the counter, with the amortized increments. -/
theorem whileCost_cnt (B : ℕ) (Tb : List Bool → Bool → List Bool → ℕ)
    (hTb : ∀ d x r, Tb d x r ≤ (if x then 6 * ones (encodeNat (d.count true)) + 9 else 0) + B) :
    ∀ (rest done : List Bool), whileCost 1 Tb done rest + incSeqCost 6 9 (done.count true) ≤
      rest.length * (B + 2) + 1 + incSeqCost 6 9 ((done ++ rest).count true)
  | [], done => by simp [whileCost]
  | x :: rest, done => by
    have ih := whileCost_cnt B Tb hTb rest (done ++ [x])
    have h := hTb done x rest
    simp only [whileCost, List.length_cons]
    rw [List.append_assoc, List.singleton_append] at ih
    have hc : incSeqCost 6 9 ((done ++ [x]).count true) = incSeqCost 6 9 (done.count true) +
        (if x then 6 * ones (encodeNat (done.count true)) + 9 else 0) := by
      cases x
      · simp
      · simp [incSeqCost]
    rw [hc] at ih
    split_ifs at h ih hc <;> nlinarith

/-- **Counter of `true` bits**, as `Runs`: `T` (a bit block down to the stack bottom) is emptied,
`N` receives `natSyms (#true)` on top of `RN`. -/
theorem runs_cntProg {T N U : K} (hTN : T ≠ N) (hNU : N ≠ U) (bs : List Bool)
    (RN : List Sym) (S : K → List Sym) (hRN : TermOK RN) (hT : S T = bs.map Sym.bit)
    (hN : S N = RN) :
    Runs (cntProg T N U) S (Function.update (Function.update S T []) N
      (natSyms (bs.count true) ++ RN)) (fun _ => True) (20 * bs.length + 2) := by
  let st : List Bool → List Bool → K → List Sym := fun done rest =>
    Function.update (Function.update S T (rest.map Sym.bit)) N (natSyms (done.count true) ++ RN)
  have h0 : st [] bs = S := by
    simp only [st, List.count_nil, natSyms, encodeNat_zero, List.map_nil, List.nil_append]
    rw [← hT, ← hN, Function.update_eq_self, Function.update_eq_self]
  have hw := runs_while (pk := peekT T) (body := cntBody T N U) (c := fun v => isBitO v.t) st 1
    (fun d x _ => (if x then 6 * ones (encodeNat (d.count true)) + 9 else 0) + 3)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT T (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne hTN, Function.update_self] at hv
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      cases rest <;> simp [isBitO])
    (fun done x rest => by
      refine Runs.of_eval fun v => ?_
      have e1 : Eval [] (.pop T fun v o => { v with o := o } : PProg K) ⟨v, st done (x :: rest)⟩
          ⟨{ v with o := some (.bit x) }, Function.update (st done (x :: rest)) T
            (rest.map Sym.bit)⟩ 1 := by
        refine (Eval.pop [] T _ v _).of_eq ?_ rfl
        simp [st, Function.update_of_ne hTN]
      cases x
      · have e2 := Eval.ite_false (ρ := []) (c := fun v : PReg => bitOf v.o)
          (p := (inc N U).liftRegs lensPO) (q := (.load id : PProg K)) (by rfl)
          (Eval.load [] id { v with o := some (.bit false) }
            (Function.update (st done (false :: rest)) T (rest.map Sym.bit)))
        refine ⟨{ v with o := some (.bit false) }, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial,
          by simp⟩
        congr 1
        funext k
        simp only [st, Function.update_apply]
        split_ifs <;> simp_all
      · obtain ⟨c, hc, e⟩ := inc_eval (ρ := []) hNU (lensPO.get { v with o := some (.bit true) })
          (encodeNat (done.count true)) RN
          (Function.update (st done (true :: rest)) T (rest.map Sym.bit)) hRN
          (by simp [st, Function.update_of_ne hTN.symm, natSyms])
        have e2 := Eval.ite_true (ρ := []) (c := fun v : PReg => bitOf v.o)
          (p := (inc N U).liftRegs lensPO) (q := (.load id : PProg K)) (by rfl)
          (Eval.liftRegs lensPO e { v with o := some (.bit true) } rfl)
        refine ⟨lensPO.set { v with o := some (.bit true) } (some Sym.mark), _,
          (Eval.seq e1 e2).of_eq ?_ rfl, trivial, by simp; omega⟩
        congr 1
        funext k
        simp only [st, Function.update_apply, ← encodeNat_succ]
        split_ifs <;> simp_all [natSyms, List.count_append])
    bs []
  rw [h0] at hw
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have h1 := whileCost_cnt 3 (fun d x _ => (if x then 6 * ones (encodeNat (d.count true)) + 9
      else 0) + 3) (fun _ _ _ => le_rfl) bs []
    have h2 := incSeqCost_le 6 9 (([] ++ bs).count true)
    have h3 : ([] ++ bs).count true ≤ bs.length := by simpa using List.count_le_length
    simp only [List.count_nil, incSeqCost, Nat.add_zero, List.nil_append] at h1 h2 h3
    omega

end SubNLogN.Machine.BridgePP
