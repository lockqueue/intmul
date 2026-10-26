/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Net
import SubNLogN.Math.Networks.AppCProc

/-!
# Proposition A.7 network simulation, part 3: records and gates (`AppC/C5NetSimGate.lean`)

* Records: a bit list of width `w` is the `𝔽₂`-vector `toRec w p : Fin w → ZMod 2`, and back
  (`ofRec`); record XOR (`List.zipWith Bool.xor`) is vector addition (`ofRec_add`).
* The list-level gates (`gateApply`, sequences of elementary XORs `xorStep`) act position-wise on lists
  given as maps over `List.range n` (`gateApply_range`), through the value-level XOR sequence
  `scalarGate`.
* A gate given by source lists `srcL` with no source being a target (`hfree`) is computed by the XOR
  list `xorsOf srcL` (one XOR per target and source; `scalarGate_xorsOf`), and its XORs have
  distinct ends (`xorsOf_ne`).
* The pure-network scalar rows (`rowUpd`, `Scalar.lean`) of the bit network are of this form (`rowUpd_eq`,
  `srcR_free`); hence the gate of `gateOpB j ι r` (`AppCProc.lean`) is `scalarGate (gateXors j ι r)`
  (`gate_eq`).
Helpers are in `SubNLogN.Machine.C5.NetAux`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks

/-! ## Records as `𝔽₂`-vectors -/

/-- Records of width `w` as `𝔽₂`-vectors. -/
abbrev Rec (w : ℕ) : Type := Fin w → ZMod 2

/-- A bit list as a record of width `w`. -/
def toRec (w : ℕ) (p : List Bool) : Rec w := fun i => if p.getD i.val false then 1 else 0

/-- A record as a bit list of length `w`. -/
def ofRec {w : ℕ} (x : Rec w) : List Bool := List.ofFn fun i => decide (x i = 1)

theorem ofRec_length {w : ℕ} (x : Rec w) : (ofRec x).length = w := List.length_ofFn

theorem ofRec_toRec {w : ℕ} (p : List Bool) (hp : p.length = w) : ofRec (toRec w p) = p := by
  apply List.ext_getElem
  · rw [ofRec_length, hp]
  · intro n h1 h2
    simp only [ofRec, toRec, List.getElem_ofFn, List.getD_eq_getElem _ _ h2]
    cases p[n] <;> decide

theorem zmod2_xor (a c : ZMod 2) : decide (a + c = 1) = (decide (a = 1) ^^ decide (c = 1)) := by
  revert a c
  decide

theorem ofRec_add {w : ℕ} (x y : Rec w) :
    ofRec (x + y) = List.zipWith Bool.xor (ofRec x) (ofRec y) := by
  apply List.ext_getElem
  · simp [ofRec_length]
  · intro n h1 h2
    simp only [ofRec, List.getElem_ofFn, List.getElem_zipWith, Pi.add_apply]
    exact zmod2_xor _ _

/-! ## Gates on lists and on values -/

/-- One elementary XOR on values: `v t ← v t + v s`. -/
def xorV {W : ℕ} {β : Type} [Add β] (v : Fin W → β) (p : Fin W × Fin W) : Fin W → β :=
  Function.update v p.1 (v p.1 + v p.2)

/-- A sequence of elementary XORs on values. -/
def scalarGate {W : ℕ} {β : Type} [Add β] (xs : List (Fin W × Fin W)) (v : Fin W → β) :
    Fin W → β :=
  xs.foldl xorV v

/-- The list-level gates act position-wise. -/
theorem gateApply_range {W w : ℕ} (xs : List (Fin W × Fin W)) (n : ℕ) :
    ∀ F : ℕ → Fin W → Rec w,
      gateApply xs (fun r => (List.range n).map fun y => ofRec (F y r)) =
        fun r => (List.range n).map fun y => ofRec (scalarGate xs (F y) r) := by
  induction xs with
  | nil => intro F; rfl
  | cons p xs ih =>
    intro F
    have hstep : xorStep (fun r => (List.range n).map fun y => ofRec (F y r)) p =
        fun r => (List.range n).map fun y => ofRec (xorV (F y) p r) := by
      funext r
      unfold xorStep xorV
      by_cases hr : r = p.1
      · subst hr
        simp only [Function.update_self, xorArr, List.zipWith_map, List.zipWith_self, ofRec_add]
      · simp only [Function.update_of_ne hr]
    show gateApply xs (xorStep _ p) = _
    rw [hstep, ih (fun y => xorV (F y) p)]
    rfl

/-- The XOR list of a gate given by its source lists (targets in `Fin W` order). -/
def xorsOf {W : ℕ} (srcL : Fin W → List (Fin W)) : List (Fin W × Fin W) :=
  (List.finRange W).flatMap fun t => (srcL t).map fun s => (t, s)

theorem foldl_xorV_block {W : ℕ} {β : Type} [AddCommMonoid β] (t : Fin W) :
    ∀ (l : List (Fin W)) (v : Fin W → β), t ∉ l →
      (l.map fun s => (t, s)).foldl xorV v = Function.update v t (v t + (l.map v).sum)
  | [], v, _ => by simp
  | s :: l, v, ht => by
    have htl : t ∉ l := fun h => ht (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_xorV_block t l _ htl]
    have hmap : l.map (xorV v (t, s)) = l.map v := List.map_congr_left fun x hx => by
      have hxt : x ≠ t := fun h => htl (h ▸ hx)
      simp only [xorV]
      rw [Function.update_of_ne hxt]
    rw [hmap]
    simp only [xorV, Function.update_self, Function.update_idem, List.sum_cons, add_assoc]

theorem foldl_targets {W : ℕ} {β : Type} [AddCommMonoid β] (srcL : Fin W → List (Fin W))
    (hfree : ∀ t, ∀ s ∈ srcL t, srcL s = []) :
    ∀ (ts : List (Fin W)) (v : Fin W → β), ts.Nodup →
      (ts.flatMap fun t => (srcL t).map fun s => (t, s)).foldl xorV v =
        fun r => if r ∈ ts then v r + ((srcL r).map v).sum else v r
  | [], v, _ => by funext r; simp
  | t :: ts, v, hnd => by
    rw [List.nodup_cons] at hnd
    have htt : t ∉ srcL t := fun h => by
      have h2 := hfree t t h
      rw [h2] at h
      simp at h
    rw [List.flatMap_cons, List.foldl_append, foldl_xorV_block t (srcL t) v htt,
      foldl_targets srcL hfree ts _ hnd.2]
    funext r
    have hv1 : ∀ x r', x ∈ srcL r' →
        Function.update v t (v t + ((srcL t).map v).sum) x = v x := by
      intro x r' hx
      by_cases hxt : x = t
      · subst hxt
        rw [Function.update_self, hfree r' x hx, List.map_nil, List.sum_nil, add_zero]
      · rw [Function.update_of_ne hxt]
    by_cases hrt : r = t
    · subst hrt
      rw [if_neg hnd.1, if_pos (List.mem_cons_self ..), Function.update_self]
    · by_cases hr : r ∈ ts
      · rw [if_pos hr, if_pos (List.mem_cons_of_mem _ hr), Function.update_of_ne hrt]
        congr 1
        exact congrArg List.sum (List.map_congr_left fun x hx => hv1 x r hx)
      · rw [if_neg hr, if_neg (fun h => hr ((List.mem_cons.1 h).resolve_left hrt)),
          Function.update_of_ne hrt]

/-- **Gates from source lists.** If no source is a target, the XOR list `xorsOf srcL` adds to
every target the sum of its sources. -/
theorem scalarGate_xorsOf {W : ℕ} {β : Type} [AddCommMonoid β] (srcL : Fin W → List (Fin W))
    (hfree : ∀ t, ∀ s ∈ srcL t, srcL s = []) (v : Fin W → β) (r : Fin W) :
    scalarGate (xorsOf srcL) v r = v r + ((srcL r).map v).sum := by
  unfold scalarGate xorsOf
  rw [foldl_targets srcL hfree _ v (List.nodup_finRange W)]
  exact if_pos (List.mem_finRange r)

theorem xorsOf_ne {W : ℕ} (srcL : Fin W → List (Fin W)) (hfree : ∀ t, ∀ s ∈ srcL t, srcL s = []) :
    ∀ p ∈ xorsOf srcL, p.1 ≠ p.2 := by
  intro p hp
  simp only [xorsOf, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨t, _, s, hs, rfl⟩ := hp
  intro hts
  have hts' : t = s := hts
  subst hts'
  rw [hfree t t hs] at hs
  simp at hs

/-! ## Pure-network scalar rows as source lists -/

/-- The sources of role `w` in the row `(j, ι, op)` of the bit network (empty for non-targets). -/
noncomputable def srcR (j : Stage) (ι : Fix 100) : Op → Role .bit 100 → List (Role .bit 100)
  | .V, .side j' ι' p => if j' = j ∧ ι' = ι then [srcRole j ι p.1.2] else []
  | .G, .center j' ι' (.inl i) => if j' = j ∧ ι' = ι then
      (Finset.univ.filter (fun T : Tri 100 => i ∈ T.1)).toList.map (srcRole j ι) else []
  | .G, .center j' ι' (.inr _) => if j' = j ∧ ι' = ι then
      (Finset.univ : Finset (Tri 100)).toList.map (srcRole j ι) else []
  | .J, w => match tgtTriple? j ι w with
      | some S => (Finset.univ : Finset {T : Tri 100 // Nbr .bit S T}).toList.map
          (fun T => Role.side j ι ⟨(S, T.1), T.2⟩)
      | none => []
  | .R, w => match tgtTriple? j ι w with
      | some S => S.1.toList.map (fun i => Role.center j ι (.inl i))
      | none => []
  | _, _ => []

theorem rowUpd_eq {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (j : Stage) (ι : Fix 100)
    (op : Op) (s : Role .bit 100 → M) (w : Role .bit 100) :
    rowUpd .bit (0 : ZMod 2) j ι op 1 s w = s w + ((srcR j ι op w).map s).sum := by
  cases op with
  | V =>
    rcases w with a | a | ⟨j', ι', p⟩ | ⟨j', ι', c⟩
    · simp [rowUpd, srcR]
    · simp [rowUpd, srcR]
    · simp only [rowUpd, srcR]
      split_ifs <;> simp
    · simp [rowUpd, srcR]
  | G =>
    rcases w with a | a | ⟨j', ι', p⟩ | ⟨j', ι', i | u⟩
    · simp [rowUpd, srcR]
    · simp [rowUpd, srcR]
    · simp [rowUpd, srcR]
    · simp only [rowUpd, srcR, gatherVal]
      split_ifs <;> simp [List.map_map, Function.comp_def]
    · simp only [rowUpd, srcR, gatherVal]
      split_ifs <;> simp [List.map_map, Function.comp_def]
  | J =>
    simp only [rowUpd, srcR]
    cases tgtTriple? j ι w with
    | none => simp
    | some S => simp [sideVal, coefJ, List.map_map, Function.comp_def]
  | R =>
    simp only [rowUpd, srcR]
    cases tgtTriple? j ι w with
    | none => simp
    | some S => simp [scatterVal, List.map_map, Function.comp_def]

theorem srcR_srcRole (j : Stage) (ι : Fix 100) (op : Op) (T : Tri 100)
    (hop : op = .V ∨ op = .G) : srcR j ι op (srcRole j ι T) = [] := by
  unfold srcRole
  rcases hop with rfl | rfl <;> split <;> simp [srcR]

theorem srcR_free (j : Stage) (ι : Fix 100) (op : Op) :
    ∀ w, ∀ x ∈ srcR j ι op w, srcR j ι op x = [] := by
  intro w x hx
  cases op with
  | V =>
    rcases w with a | a | ⟨j', ι', p⟩ | ⟨j', ι', c⟩
    · simp [srcR] at hx
    · simp [srcR] at hx
    · simp only [srcR] at hx
      split_ifs at hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact srcR_srcRole j ι .V _ (Or.inl rfl)
      · simp at hx
    · simp [srcR] at hx
  | G =>
    rcases w with a | a | ⟨j', ι', p⟩ | ⟨j', ι', i | u⟩
    · simp [srcR] at hx
    · simp [srcR] at hx
    · simp [srcR] at hx
    · simp only [srcR] at hx
      split_ifs at hx
      · obtain ⟨T, -, rfl⟩ := List.mem_map.1 hx
        exact srcR_srcRole j ι .G _ (Or.inr rfl)
      · simp at hx
    · simp only [srcR] at hx
      split_ifs at hx
      · obtain ⟨T, -, rfl⟩ := List.mem_map.1 hx
        exact srcR_srcRole j ι .G _ (Or.inr rfl)
      · simp at hx
  | J =>
    simp only [srcR] at hx
    split at hx
    · obtain ⟨T, -, rfl⟩ := List.mem_map.1 hx
      simp [srcR, tgtTriple?]
    · simp at hx
  | R =>
    simp only [srcR] at hx
    split at hx
    · obtain ⟨T, -, rfl⟩ := List.mem_map.1 hx
      simp [srcR, tgtTriple?]
    · simp at hx

theorem rowSign_cases (j : Stage) (r : Fin 8) : rowSign j r = 1 ∨ rowSign j r = -1 := by
  revert r
  cases j <;> decide

theorem rowSign_cast (j : Stage) (r : Fin 8) : ((rowSign j r : ℤ) : ZMod 2) = 1 := by
  rcases rowSign_cases j r with h | h <;> rw [h] <;> decide

/-- Source lists of the gate of `gateOpB j ι r`, on role indices. -/
noncomputable def gateSrc (j : Stage) (ι : Fix 100) (r : Fin 8) (t : Fin Wb) : List (Fin Wb) :=
  (srcR j ι (rowOp j r) (roleIdxB.symm t)).map roleIdxB

theorem gateSrc_free (j : Stage) (ι : Fix 100) (r : Fin 8) :
    ∀ t, ∀ s ∈ gateSrc j ι r t, gateSrc j ι r s = [] := by
  intro t s hs
  unfold gateSrc at hs ⊢
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
  rw [Equiv.symm_apply_apply, srcR_free j ι (rowOp j r) _ x hx, List.map_nil]

/-- The XOR list of the gate of `gateOpB j ι r`. -/
noncomputable def gateXors (j : Stage) (ι : Fix 100) (r : Fin 8) : List (Fin Wb × Fin Wb) :=
  xorsOf (gateSrc j ι r)

theorem gateXors_ne (j : Stage) (ι : Fix 100) (r : Fin 8) : ∀ p ∈ gateXors j ι r, p.1 ≠ p.2 :=
  xorsOf_ne _ (gateSrc_free j ι r)

/-- **The gate of `gateOpB j ι r` is the XOR list `gateXors j ι r`.** -/
theorem gate_eq {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (j : Stage) (ι : Fix 100)
    (r : Fin 8) (vals : Fin Wb → β) (idx : Fin Wb) :
    rowUpd .bit (0 : ZMod 2) j ι (rowOp j r) ((rowSign j r : ℤ) : ZMod 2)
        (fun w => vals (roleIdxB w)) (roleIdxB.symm idx) =
      scalarGate (gateXors j ι r) vals idx := by
  rw [rowSign_cast, rowUpd_eq]
  unfold gateXors
  rw [scalarGate_xorsOf _ (gateSrc_free j ι r) vals idx]
  unfold gateSrc
  simp only [Equiv.apply_symm_apply, List.map_map, Function.comp_def]

end SubNLogN.Machine.C5.NetAux
