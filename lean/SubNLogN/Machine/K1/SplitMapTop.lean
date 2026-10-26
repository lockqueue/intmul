/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.SplitMapMain

/-!
# K1c-mix, the contract (`K1/SplitMapTop.lean`)

**Scope (honest summary).** Proves `k1SplitMapMergeMix_holds : K1SplitMapMergeMixStmt q A g`
(`SubNLogN/Machine/Contracts/Streams.lean`, §5) for every `q` (with `[NeZero q]`), `A` and `g`.
Paper: Fact 3.3(2) (`fact:oai-streams`) and Lemma A.4(3) (`lem:transfer-streams`,
`q` streams, nested merge, and amortized counters).

* Program `k1mixProg g`: one superblock (`q·N1` records) per iteration while the source shows a
  record; then the accumulator is rewound onto the destination. An empty input never reads `N1`.
* Cost: each superblock costs at most `68·q·N1·ℓ` steps, `ℓ = B·digitWidth A + 1` the record
  length in symbols, so the total is at most `C·(V + 1)` with `C` depending only on the
  compile-time `q`, `A` (through nothing else: `g` enters only the finite register function).
* The hypothesis `∀ f c, (∀ c', f c' < A) → g f c < A` of the contract is not used: the kernel
  writes the `digitWidth A` low bits of `g`, which is exactly `digitRec A` of the output.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem flatMap_congr' {α β : Type} {l : List α} {f f' : α → List β}
    (h : ∀ x ∈ l, f x = f' x) : l.flatMap f = l.flatMap f' := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem rev_arrSyms_map (f : ℕ → List Bool) :
    ∀ n : ℕ, (arrSyms ((List.range n).map f)).reverse =
      (List.range n).reverse.flatMap (fun l => (recSyms (f l)).reverse)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, arrSyms_append, List.reverse_append, rev_arrSyms_map f n,
      List.reverse_append]
    simp [arrSyms_cons]

section Super

variable {q : ℕ} [NeZero q] {A : ℕ} (g : (Fin q → ℕ) → Fin q → ℕ)

/-- Record tuple `l` of a superblock whose data starts with `w`. -/
def sbTup (N1 : ℕ) (w : List (List ℕ)) (l : ℕ) : Fin q → List ℕ := fun c => w.getD (c.val * N1 + l) []

/-- Output records of the superblock whose data starts with `w`, in address order. -/
def sbOut (B N1 : ℕ) (w : List (List ℕ)) : List (List ℕ) :=
  (List.finRange q).flatMap fun c => (List.range N1).map fun l => outRec g B (sbTup N1 w l) c

theorem length_digitRec (ds : List ℕ) : (digitRec A ds).length = ds.length * digitWidth A := by
  induction ds with
  | nil => simp [digitRec]
  | cons d ds ih =>
    simp only [digitRec, List.flatMap_cons, List.length_append, digitBits, length_bitsLE] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul]
    omega

omit [NeZero q] in
theorem sbTup_mem (N1 : ℕ) (w : List (List ℕ)) (hw : q * N1 ≤ w.length) (l : ℕ) (hl : l < N1)
    (c : Fin q) : sbTup N1 w l c ∈ w := by
  have h : c.val * N1 + l < w.length := by
    have := Nat.mul_le_mul_right N1 (Nat.succ_le_of_lt c.isLt)
    rw [Nat.succ_mul] at this
    omega
  simp only [sbTup]
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem _

omit [NeZero q] in
/-- The stream contents after the split equal the map phase's input form. -/
theorem split_streams_eq (N1 : ℕ) (w : List (List ℕ)) (hw : q * N1 ≤ w.length) (c : Fin q)
    (Z : List Sym) :
    (arrSyms (((w.map (digitRec A)).drop (c.val * N1)).take N1)).reverse ++ Z =
      ((List.range N1).reverse.map (sbTup N1 w)).flatMap
        (fun t => (recSyms (digitRec A (t c))).reverse) ++ Z := by
  have hc : c.val * N1 + N1 ≤ w.length := by
    have := Nat.mul_le_mul_right N1 (Nat.succ_le_of_lt c.isLt)
    rw [Nat.succ_mul] at this
    omega
  rw [← List.map_drop, ← List.map_take, take_drop_eq_map w (c.val * N1) N1 [] hc, List.map_map,
    rev_arrSyms_map, List.flatMap_map]
  rfl

omit [NeZero q] in
/-- The output stack contents after the map phase, as an array. -/
theorem out_eq_arrSyms (B N1 : ℕ) (w : List (List ℕ)) (c : Fin q) :
    ((List.range N1).reverse.map (sbTup N1 w)).reverse.flatMap
        (fun t => recSyms (digitRec A (outRec g B t c))) =
      arrSyms ((List.range N1).map fun l => digitRec A (outRec g B (sbTup N1 w l) c)) := by
  rw [arrSyms_eq_flatMap, ← List.map_reverse, List.reverse_reverse]
  simp [List.flatMap_map]

omit [NeZero q] in
theorem sbOut_arrSyms (B N1 : ℕ) (w : List (List ℕ)) :
    arrSyms ((sbOut g B N1 w).map (digitRec A)) =
      (List.finRange q).flatMap fun c =>
        arrSyms ((List.range N1).map fun l => digitRec A (outRec g B (sbTup N1 w l) c)) := by
  simp [sbOut, arrSyms_eq_flatMap, List.flatMap_map, List.map_flatMap, List.flatMap_assoc]

/-- Cost of one superblock (before simplification). -/
def sbCost (q N1 B w : ℕ) : ℕ :=
  2 * q + 1 + (q * (14 * N1 + 3 * (N1 * (B * w + 1)) + 2 * N1 + 7 * N1 + 12) + 1) +
    (N1 * (2 * q + 6 + B * (w * (4 * q + 4))) + 1 + 1) + (q + 1) +
    (3 * (q * (N1 * (B * w + 1))) + 2 * q + 1)

theorem sbCost_le (q N1 B w : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N1) :
    sbCost q N1 B w ≤ 68 * (q * (N1 * (B * w + 1))) := by
  have e : sbCost q N1 B w = 17 * q + 31 * (q * N1) + 10 * (q * N1 * (B * w)) + 6 * N1 +
      4 * (N1 * (B * w)) + 6 := by
    unfold sbCost
    ring
  have e2 : 68 * (q * (N1 * (B * w + 1))) = 68 * (q * N1 * (B * w)) + 68 * (q * N1) := by ring
  rw [e, e2]
  have h1 : N1 * (B * w) ≤ q * N1 * (B * w) := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ hq
  have h2 : N1 ≤ q * N1 := Nat.le_mul_of_pos_left _ hq
  have h3 : q ≤ q * N1 := Nat.le_mul_of_pos_right _ hN
  have h4 : 1 ≤ q * N1 := Nat.mul_le_mul hq hN
  omega

/-- **One superblock.** -/
theorem runs_superblock (B N1 : ℕ) (r2 : List Sym) (hr2 : TermOK r2) (w : List (List ℕ))
    (R : List Sym) (hw : q * N1 ≤ w.length) (hN : 1 ≤ N1)
    (hwd : ∀ ds ∈ w, ds.length = B ∧ ∀ d ∈ ds, d < A)
    (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (hnm0 : nm 0 = arrSyms (w.map (digitRec A)) ++ R) (hnm2 : nm 2 = natSyms N1 ++ r2) :
    Runs (superblock (A := A) g) (mk1 nm st ou ex)
      (mk1 (Function.update nm 0 (arrSyms ((w.drop (q * N1)).map (digitRec A)) ++ R)) st ou
        (Function.update ex 0 ((arrSyms ((sbOut g B N1 w).map (digitRec A))).reverse ++ ex 0)))
      (fun _ => True) (68 * (q * (N1 * (B * digitWidth A + 1)))) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlen : (w.map (digitRec A)).length = w.length := List.length_map _
  have hrec : ∀ p ∈ w.map (digitRec A), p.length = B * digitWidth A := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨ds, hds, rfl⟩ := hp
    rw [length_digitRec, (hwd ds hds).1]
  -- 1. marks
  have h1 := runs_pushMarks (A := A) nm ex st ou
  -- 2. split
  have h2 := runs_splitAll (A := A) N1 r2 hr2 (w.map (digitRec A)) R (by rw [hlen]; exact hw) nm
    (fun c => Sym.mark :: st c) (fun c => Sym.mark :: ou c) ex hnm0 hnm2
  -- 3. map phase
  set ts := (List.range N1).reverse.map (sbTup N1 w) with hts
  have hts_ok : ∀ t ∈ ts, ∀ c, (t c).length = B ∧ ∀ d ∈ t c, d < A := by
    intro t ht c
    rw [hts] at ht
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at ht
    obtain ⟨l, hl, rfl⟩ := ht
    exact hwd _ (sbTup_mem N1 w hw l hl c)
  have h3 := runs_whileTop (loopR_mapPhase (A := A) g B
    (Function.update nm 0 (arrSyms ((w.map (digitRec A)).drop (q * N1)) ++ R)) ex
    (fun c => Sym.mark :: st c) (by simp) ts
    (fun c => (arrSyms (((w.map (digitRec A)).drop (c.val * N1)).take N1)).reverse ++
      Sym.mark :: st c)
    (fun c => Sym.mark :: ou c) hts_ok (fun c => split_streams_eq N1 w hw c _))
  -- 4. stream marks
  have h4 := runs_popSeps (A := A)
    (Function.update nm 0 (arrSyms ((w.map (digitRec A)).drop (q * N1)) ++ R)) ex
    (fun c => Sym.mark :: st c)
    (fun c => ts.reverse.flatMap (fun t => recSyms (digitRec A (outRec g B t c))) ++
      Sym.mark :: ou c) st Sym.mark (fun c => rfl)
  -- 5. merge
  have h5 := runs_mergeAll (A := A)
    (Function.update nm 0 (arrSyms ((w.map (digitRec A)).drop (q * N1)) ++ R)) ex st ou
    (fun c => ts.reverse.flatMap (fun t => recSyms (digitRec A (outRec g B t c))))
    (fun c => by rw [hts, out_eq_arrSyms]; exact mark_not_mem_arrSyms _)
  refine runs_of_eq (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 (WP.W9comp.runs_seq h3
    (WP.W9comp.runs_seq h4 h5)))) rfl ?_ ?_
  · refine mk1_ext ?_ rfl rfl ?_
    · rw [List.map_drop]
    · congr 2
      rw [sbOut_arrSyms]
      congr 1
      refine flatMap_congr' fun c _ => ?_
      rw [hts, out_eq_arrSyms]
  · have hb : ∀ x ∈ (List.finRange q).map (fun c : Fin q => incSeqCost 6 8 N1 +
        3 * vol (((w.map (digitRec A)).drop (c.val * N1)).take N1) + 2 * N1 + 7 * bitLen N1 + 12),
        x ≤ 14 * N1 + 3 * (N1 * (B * digitWidth A + 1)) + 2 * N1 + 7 * N1 + 12 := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨c, -, rfl⟩ := hx
      have hc : c.val * N1 + N1 ≤ w.length := by
        have := Nat.mul_le_mul_right N1 (Nat.succ_le_of_lt c.isLt)
        rw [Nat.succ_mul] at this
        omega
      have hv : vol (((w.map (digitRec A)).drop (c.val * N1)).take N1) =
          N1 * (B * digitWidth A + 1) := by
        rw [vol_uniform (B * digitWidth A) _
          (fun p hp => hrec p (List.mem_of_mem_drop (List.mem_of_mem_take hp)))]
        simp only [List.length_take, List.length_drop, List.length_map]
        congr 1
        omega
      have hi := incSeqCost_le 6 8 N1
      have hbl : bitLen N1 ≤ N1 := TMFw.W3s.bitLen_le_of_lt (Nat.lt_two_pow_self)
      rw [hv]
      omega
    have hs2 := List.sum_le_card_nsmul _ _ hb
    simp only [List.length_map, List.length_finRange, smul_eq_mul] at hs2
    have hL : ∀ x ∈ (List.finRange q).map (fun c : Fin q =>
        (ts.reverse.flatMap (fun t => recSyms (digitRec A (outRec g B t c)))).length),
        x ≤ N1 * (B * digitWidth A + 1) := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨c, -, rfl⟩ := hx
      rw [hts, out_eq_arrSyms, ← vol, vol_uniform (B * digitWidth A)]
      · simp
      · intro p hp
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨l, -, rfl⟩ := hp
        rw [length_digitRec]
        simp [outRec]
    have hs5 := List.sum_le_card_nsmul _ _ hL
    simp only [List.length_map, List.length_finRange, smul_eq_mul] at hs5
    have htl : ts.length = N1 := by simp [hts]
    have hle := sbCost_le q N1 B (digitWidth A) hq hN
    unfold sbCost at hle
    rw [htl]
    have e1 : q * (14 * N1 + 3 * (N1 * (B * digitWidth A + 1)) + 2 * N1 + 7 * N1 + 12) =
        q * (14 * N1 + 3 * (N1 * (B * digitWidth A + 1)) + 2 * N1 + 7 * N1 + 12) := rfl
    have e2 : 3 * (q * (N1 * (B * digitWidth A + 1))) =
        3 * (q * (N1 * (B * digitWidth A + 1))) := rfl
    nlinarith

end Super

end SubNLogN.Machine.K1.SMM

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

section Loop

variable {q : ℕ} [NeZero q] {A : ℕ} (g : (Fin q → ℕ) → Fin q → ℕ)

/-- Outputs of `n` consecutive superblocks starting at `w`. -/
def outAll (B N1 : ℕ) (w : List (List ℕ)) (n : ℕ) : List (List ℕ) :=
  (List.range n).flatMap fun h => sbOut g B N1 (w.drop (h * (q * N1)))

omit [NeZero q] in
theorem outAll_succ (B N1 : ℕ) (w : List (List ℕ)) (n : ℕ) :
    outAll g B N1 w (n + 1) = sbOut g B N1 w ++ outAll g B N1 (w.drop (q * N1)) n := by
  rw [outAll, outAll, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.zero_mul, List.drop_zero]
  congr 1
  congr 1
  funext h
  rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]

/-- **All superblocks**, by induction on their number. -/
theorem loopR_main (B N1 : ℕ) (hN : 1 ≤ N1) (r2 : List Sym) (hr2 : TermOK r2) (R : List Sym)
    (hR : BlkTerm R) (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (hnm2 : nm 2 = natSyms N1 ++ r2) :
    ∀ (n : ℕ) (w : List (List ℕ)) (Y : List Sym), w.length = n * (q * N1) →
      (∀ ds ∈ w, ds.length = B ∧ ∀ d ∈ ds, d < A) →
      LoopR (M := M1 q A) SRC isRecStart (superblock (A := A) g)
        (mk1 (Function.update nm 0 (arrSyms (w.map (digitRec A)) ++ R)) st ou
          (Function.update ex 0 Y))
        (mk1 (Function.update nm 0 R) st ou
          (Function.update ex 0 ((arrSyms ((outAll g B N1 w n).map (digitRec A))).reverse ++ Y)))
        (n * (68 * (q * (N1 * (B * digitWidth A + 1))) + 2) + 1)
  | 0, w, Y, hw, _ => by
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
    subst hw0
    refine (LoopR.congr (LoopR.stop ?_) ?_).mono (Nat.le_add_left _ _)
    · rw [mk1_nm, Function.update_self, List.map_nil, arrSyms_nil, List.nil_append]
      exact testO_recStart_of_blkTerm hR
    · simp only [outAll, List.range_zero, List.flatMap_nil, List.map_nil, arrSyms_nil,
        List.reverse_nil, List.nil_append]
  | n + 1, w, Y, hw, hwd => by
    have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hlen : q * N1 ≤ w.length := by
      rw [hw, Nat.succ_mul]
      omega
    have h1 := runs_superblock (A := A) g B N1 r2 hr2 w R hlen hN hwd
      (Function.update nm 0 (arrSyms (w.map (digitRec A)) ++ R)) st ou (Function.update ex 0 Y)
      (Function.update_self _ _ _) (by rw [Function.update_of_ne (by decide)]; exact hnm2)
    have hdl : (w.drop (q * N1)).length = n * (q * N1) := by
      rw [List.length_drop, hw, Nat.succ_mul]
      omega
    have ih := loopR_main B N1 hN r2 hr2 R hR nm st ou ex hnm2 n (w.drop (q * N1))
      ((arrSyms ((sbOut g B N1 w).map (digitRec A))).reverse ++ Y) hdl
      (fun ds hds => hwd ds (List.mem_of_mem_drop hds))
    have hc : testO isRecStart ((mk1 (Function.update nm 0 (arrSyms (w.map (digitRec A)) ++ R))
        st ou (Function.update ex 0 Y)) SRC).head? = true := by
      obtain ⟨ds, w', rfl⟩ : ∃ ds w', w = ds :: w' := by
        cases w with
        | nil =>
          simp at hw
          have : 0 < (n + 1) * (q * N1) := Nat.mul_pos (Nat.succ_pos n) (Nat.mul_pos hq hN)
          omega
        | cons ds w' => exact ⟨ds, w', rfl⟩
      simp only [mk1_nm, Function.update_self, List.map_cons, arrSyms_cons, List.append_assoc]
      exact testO_recStart _ _
    refine ((LoopR.step hc (runs_of_eq h1 rfl ?_ le_rfl) ih).congr ?_).mono ?_
    · simp only [Function.update_idem, Function.update_self]
    · refine mk1_ext rfl rfl rfl ?_
      rw [outAll_succ, List.map_append, arrSyms_append, List.reverse_append, List.append_assoc]
    · have e : (n + 1) * (68 * (q * (N1 * (B * digitWidth A + 1))) + 2) =
          n * (68 * (q * (N1 * (B * digitWidth A + 1))) + 2) +
            (68 * (q * (N1 * (B * digitWidth A + 1))) + 2) := by ring
      rw [e]
      omega

end Loop

end SubNLogN.Machine.K1.SMM

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-! ## The specification in superblock form -/

theorem finRange_flatMap_eq {q : ℕ} [NeZero q] {β : Type} (f : Fin q → List β) :
    (List.finRange q).flatMap f = (List.range q).flatMap (fun c => f (modFin q c)) := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1
  funext c
  congr 1
  exact Fin.ext (by simp [modFin, Nat.mod_eq_of_lt c.isLt])

theorem getD_drop' {α : Type} (v : List α) (n i : ℕ) (d : α) :
    (v.drop n).getD i d = v.getD (n + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem idx_facts (q N1 h c l : ℕ) (hc : c < q) (hl : l < N1) :
    (h * (q * N1) + (c * N1 + l)) / (N1 * q) = h ∧ (h * (q * N1) + (c * N1 + l)) % N1 = l ∧
      (h * (q * N1) + (c * N1 + l)) / N1 % q = c := by
  have hN : 0 < N1 := by omega
  have hr : c * N1 + l < N1 * q := by
    have := Nat.mul_le_mul_right N1 (Nat.succ_le_of_lt hc)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm N1 q]
    omega
  have e1 : h * (q * N1) + (c * N1 + l) = (c * N1 + l) + h * (N1 * q) := by ring
  have e2 : h * (q * N1) + (c * N1 + l) = l + (c + h * q) * N1 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Nat.add_mul_div_right _ _ (Nat.mul_pos hN (by omega)), Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  · rw [e2, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hl, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem outAll_eq {q : ℕ} [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) (B N1 N0 : ℕ)
    (v : List (List ℕ)) (hv : v.length = N0 * q * N1) :
    outAll g B N1 v N0 = splitMapMergeMix q N1 g B v := by
  unfold splitMapMergeMix outAll
  rw [hv, show N0 * q * N1 = N0 * (q * N1) by ring, range_mul_flatMap, List.map_flatMap]
  refine flatMap_congr' fun h _ => ?_
  rw [List.map_map, range_mul_flatMap, List.map_flatMap, sbOut, finRange_flatMap_eq]
  refine flatMap_congr' fun c hc => ?_
  rw [List.map_map]
  refine List.map_congr_left fun l hl => ?_
  simp only [List.mem_range] at hc hl
  obtain ⟨f1, f2, f3⟩ := idx_facts q N1 h c l hc hl
  simp only [Function.comp, outRec, sbTup]
  rw [f1, f2]
  have hm : modFin q ((h * (q * N1) + (c * N1 + l)) / N1) = modFin q c := by
    apply Fin.ext
    simp only [modFin]
    rw [f3, Nat.mod_eq_of_lt hc]
  rw [hm]
  refine List.map_congr_left fun t _ => ?_
  congr 1
  funext c'
  rw [getD_drop', Nat.add_assoc]

end SubNLogN.Machine.K1.SMM

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem length_splitMapMergeMix {q : ℕ} [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) (N1 B : ℕ)
    (v : List (List ℕ)) : (splitMapMergeMix q N1 g B v).length = v.length := by
  simp [splitMapMergeMix]

theorem vol_map_digitRec (A B : ℕ) (u : List (List ℕ)) (hu : ∀ ds ∈ u, ds.length = B) :
    vol (u.map (digitRec A)) = u.length * (B * digitWidth A + 1) := by
  rw [vol_uniform (B * digitWidth A), List.length_map]
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨ds, hds, rfl⟩ := hp
  rw [length_digitRec, hu ds hds]

/-- **K1c-mix holds** (`K1SplitMapMergeMixStmt`, `SubNLogN/Machine/Contracts/Streams.lean` §5).
For every radix `q ≥ 1`, data alphabet `[A]` and pointwise map `g`, the program `k1mixProg g`
(stacks `Fin 3 ⊕ E1 q`, registers `Option Sym × M1 q A`) maps an array of `N0·q·N1` records of
`B` digits (`digitRec A`) to `splitMapMergeMix q N1 g B v` within `80·(V + 1)` steps. Paper:
Fact 3.3(2) (`fact:oai-streams`), Lemma A.4(3) (`lem:transfer-streams`). -/
theorem k1SplitMapMergeMix_holds (q : ℕ) [NeZero q] (A : ℕ) (g : (Fin q → ℕ) → Fin q → ℕ) :
    K1SplitMapMergeMixStmt q A g := by
  refine ⟨80, fun _ => ⟨E1 q, inferInstance, inferInstance, Option Sym × M1 q A,
    k1mixProg (A := A) g, inferInstance, ⟨(none, fun _ _ => false)⟩, closed_k1mixProg g, ?_⟩⟩
  intro N0 N1 B v rest r2 S hv hvd _ hR hr2 hS0 hS2
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rw [mk1_eta S] at hS0 hS2 ⊢
  set nm : Fin 3 → List Sym := fun i => S (.inl i) with hnm
  set st : Fin q → List Sym := fun c => S (.inr (.inl c))
  set ou : Fin q → List Sym := fun c => S (.inr (.inr (.inl c)))
  set ex : Fin 4 → List Sym := fun j => S (.inr (.inr (.inr j)))
  simp only [mk1_nm] at hS0 hS2
  -- step 1: accumulator mark
  have h1r := runs_of_runsM_all (fun m => RunsM.push (M := M1 q A) ACC Sym.mark m (mk1 nm st ou ex))
  simp only [upd_ex, mk1_ex] at h1r
  -- the output
  set out := splitMapMergeMix q N1 g B v with hout
  have hV : vol (out.map (digitRec A)) = vol (v.map (digitRec A)) := by
    rw [vol_map_digitRec A B out, vol_map_digitRec A B v (fun ds h => (hvd ds h).1),
      hout, length_splitMapMergeMix]
    intro ds hds
    rw [hout] at hds
    simp only [splitMapMergeMix, List.mem_map, List.mem_range] at hds
    obtain ⟨x, -, rfl⟩ := hds
    simp
  -- step 3: the final rewind
  have h3 := runs_of_runsM_all (fun m => runsM_rwd (M := M1 q A) (src := ACC) (dst := DST)
    (by simp) ((arrSyms (out.map (digitRec A))).reverse) (ex 0)
    (by rw [List.mem_reverse]; exact mark_not_mem_arrSyms _) m
    (mk1 (Function.update nm 0 rest) st ou (Function.update ex 0
      ((arrSyms (out.map (digitRec A))).reverse ++ Sym.mark :: ex 0)))
      (by rw [mk1_ex, Function.update_self]))
  -- step 2: the superblock loop, and assembly
  by_cases hv0 : v = []
  · subst hv0
    have hout0 : out = [] := by rw [hout]; simp [splitMapMergeMix]
    have hloop : LoopR (M := M1 q A) SRC isRecStart (superblock (A := A) g)
        (mk1 nm st ou (Function.update ex 0 (Sym.mark :: ex 0)))
        (mk1 (Function.update nm 0 rest) st ou (Function.update ex 0
          ((arrSyms (out.map (digitRec A))).reverse ++ Sym.mark :: ex 0))) 1 := by
      refine LoopR.congr (LoopR.stop ?_) ?_
      · simp only [mk1_nm, hS0, List.map_nil, arrSyms_nil, List.nil_append]
        exact testO_recStart_of_blkTerm hR
      · refine mk1_ext ?_ rfl rfl ?_
        · have h0 : nm 0 = rest := by rw [hS0]; simp
          rw [← h0, Function.update_eq_self]
        · simp [hout0]
    refine runs_of_eq (WP.W9comp.runs_seq h1r (WP.W9comp.runs_seq (runs_whileTop hloop) h3))
      rfl ?_ (by rw [hout0]; simp)
    simp only [upd_ex, upd_nm, Function.update_idem,
      List.reverse_reverse]
    refine mk1_ext ?_ rfl rfl ?_
    · simp [hout0]
    · simp
  · have hN : 1 ≤ N1 := by
      rcases Nat.eq_zero_or_pos N1 with h | h
      · exact absurd (List.eq_nil_of_length_eq_zero (by rw [hv, h, Nat.mul_zero])) hv0
      · exact h
    have hN0 : 1 ≤ N0 := by
      rcases Nat.eq_zero_or_pos N0 with h | h
      · exact absurd (List.eq_nil_of_length_eq_zero (by rw [hv, h, Nat.zero_mul, Nat.zero_mul]))
          hv0
      · exact h
    have hloop := loopR_main (A := A) g B N1 hN r2 hr2 rest hR nm st ou ex hS2 N0 v
      (Sym.mark :: ex 0) (by rw [hv, Nat.mul_assoc]) hvd
    rw [show Function.update nm 0 (arrSyms (v.map (digitRec A)) ++ rest) = nm by
      rw [← hS0, Function.update_eq_self]] at hloop
    rw [outAll_eq g B N1 N0 v hv] at hloop
    refine runs_of_eq (WP.W9comp.runs_seq h1r (WP.W9comp.runs_seq (runs_whileTop hloop) h3))
      rfl ?_ ?_
    · simp only [upd_ex, upd_nm, Function.update_idem,
        List.reverse_reverse]
      refine mk1_ext ?_ rfl rfl ?_
      · simp
      · simp
    · rw [List.length_reverse, ← vol, hV]
      have hX : vol (v.map (digitRec A)) = N0 * (q * (N1 * (B * digitWidth A + 1))) := by
        rw [vol_map_digitRec A B v (fun ds h => (hvd ds h).1), hv]
        ring
      have hX1 : 1 ≤ q * (N1 * (B * digitWidth A + 1)) :=
        Nat.mul_le_mul hq (Nat.mul_le_mul hN (Nat.le_add_left 1 _))
      have hN0V : N0 ≤ vol (v.map (digitRec A)) := by
        rw [hX]
        exact Nat.le_mul_of_pos_right _ hX1
      rw [hX] at hN0V ⊢
      nlinarith

end SubNLogN.Machine.K1.SMM

namespace SubNLogN.Machine.K1

/-- **K1c-mix holds** (deliverable; `K1SplitMapMergeMixStmt`, Contracts/Streams.lean §5). Alias of
`SubNLogN.Machine.K1.SMM.k1SplitMapMergeMix_holds`, see there. Paper:
Fact 3.3(2) (`fact:oai-streams`), Lemma A.4(3) (`lem:transfer-streams`). -/
theorem k1SplitMapMergeMix_holds (q : ℕ) [NeZero q] (A : ℕ) (g : (Fin q → ℕ) → Fin q → ℕ) :
    K1SplitMapMergeMixStmt q A g :=
  SMM.k1SplitMapMergeMix_holds q A g

end SubNLogN.Machine.K1
