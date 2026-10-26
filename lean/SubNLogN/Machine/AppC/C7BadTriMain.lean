/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7BadTriT0
import SubNLogN.Machine.AppC.C7ExtractInst

/-!
# Lemma A.9 extraction: the bad-record triple transform, proof (`Machine/AppC/C7BadTriMain.lean`)

Proof of `C7BadTriStmt` (`C7BadTri.lean`). Over an abstract arithmetic kit (`C7ExtractKit.lean`) on
the layout `BTLoc` of `C7BadTriLine.lean`:

* `btLine`: one packed line (`packedLine_eq`): the line sum `A = lsum … (f - 1)` on `OFF`, then the
  target becomes `(t + A) mod 2^L` or `(t + 2^L - A) mod 2^L`;
* `btLines`: the eight negated lines of `S₀⁻¹` in reverse order (`packedS0inv_eq`);
* `btT0`: `T₀` as `y + lsum … false - lsum … true` (`packedT0_eq`, `xor_mask_eq`); the two line
  sums read a copy of `y`;
* `c7BadTri_holds`: the kit `natKit` (`C7ExtractInst.lean`) and the cost bound
  `159 · opCost (L + 1) · f ≤ 165360 · (L + 1)^3`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7BadTriAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.AppC.C7ExtractAux SubNLogN.Machine.Calculus
  SubNLogN.Math.Networks

/-! ## Packed-line facts -/

theorem btLine_fst (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) (xyz : ℕ × ℕ × ℕ) :
    (packedLine L K ρ f op xyz).1 = xyz.1 := by
  obtain ⟨b, ε, par⟩ := op
  cases b <;> simp [packedLine]

/-- The new target value of a line: `(t + A) mod 2^L` (`plus`) or `(t + 2^L - A) mod 2^L`. -/
def btLval (plus : Bool) (L t A : ℕ) : ℕ :=
  (if plus then t + A else t + 2 ^ L - A) % 2 ^ L

theorem btLineNew_eq (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) (x o t : ℕ) :
    lineNew L K ρ f op x o t =
      btLval (decide (op.2.1 = 1)) L t (lsum K ρ x o (decide (op.2.2 = 1)) (f - 1)) := by
  unfold lineNew btLval
  by_cases h : op.2.1 = 1 <;> simp [h]

theorem btLine_lt (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) (hop : op.2.1 = 1 ∨ op.2.1 = -1)
    (hpar : op.2.2 ≤ 1) (hK : 1 ≤ K) (hL : ρ + (f - 1) * K ≤ L) (x y z : ℕ) (hy : y < 2 ^ L)
    (hz : z < 2 ^ L) :
    (packedLine L K ρ f op (x, y, z)).2.1 < 2 ^ L ∧
      (packedLine L K ρ f op (x, y, z)).2.2 < 2 ^ L := by
  rw [packedLine_eq L K ρ f op hop hpar hK hL x y z]
  have hlt : ∀ o t, lineNew L K ρ f op x o t < 2 ^ L := fun o t => by
    rw [btLineNew_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos L)
  obtain ⟨b, ε, par⟩ := op
  cases b
  · exact ⟨hy, hlt _ _⟩
  · exact ⟨hlt _ _, hz⟩

/-- The packed lines keep `x` and keep `y, z` below `2^L`. -/
theorem btFold (L K ρ f : ℕ) (hK : 1 ≤ K) (hL : ρ + (f - 1) * K ≤ L) (x : ℕ) :
    ∀ (ops : List (Bool × ℤ × ℕ)), (∀ op ∈ ops, (op.2.1 = 1 ∨ op.2.1 = -1) ∧ op.2.2 ≤ 1) →
    ∀ y z, y < 2 ^ L → z < 2 ^ L →
      (ops.foldl (fun p op => packedLine L K ρ f op p) (x, y, z)).1 = x ∧
      (ops.foldl (fun p op => packedLine L K ρ f op p) (x, y, z)).2.1 < 2 ^ L ∧
      (ops.foldl (fun p op => packedLine L K ρ f op p) (x, y, z)).2.2 < 2 ^ L
  | [], _, _, _, hy, hz => ⟨rfl, hy, hz⟩
  | op :: ops, hops, y, z, hy, hz => by
    obtain ⟨hop, hpar⟩ := hops op (by simp)
    obtain ⟨h2, h3⟩ := btLine_lt L K ρ f op hop hpar hK hL x y z hy hz
    have hpe : packedLine L K ρ f op (x, y, z) =
        (x, (packedLine L K ρ f op (x, y, z)).2.1, (packedLine L K ρ f op (x, y, z)).2.2) :=
      Prod.ext (btLine_fst L K ρ f op (x, y, z)) rfl
    simp only [List.foldl_cons]
    rw [hpe]
    exact btFold L K ρ f hK hL x ops (fun o h => hops o (by simp [h])) _ _ h2 h3

/-! ## Programs -/

section Progs

variable (xk : XKit BTLoc)

/-- The update of a line's target: `t + A` (`plus`) or `t + 2^L - A`. -/
def btAdd (tgt : BTLoc) (plus : Bool) : Prog BTLoc (fun _ => Sym) xk.R :=
  if plus then addTo xk tgt bOFF bT0 bT1 bT2 bT3
  else .seq (addTo xk tgt bPL bT0 bT1 bT2 bT3) (subFrom xk tgt bOFF bT0 bT1 bT2 bT3)

/-- One packed line with target `tgt` and other chunk `oth`. -/
def btLine (tgt oth : BTLoc) (plus par : Bool) : Prog BTLoc (fun _ => Sym) xk.R :=
  .seq (btLsum xk oth par)
    (.seq (btAdd xk tgt plus) (.seq (modBy xk tgt bPL bT0 bT1 bT2 bT3 bT4) (dropFW xk bOFF)))

/-- The packed line `op`. -/
def btOp (op : Bool × ℤ × ℕ) : Prog BTLoc (fun _ => Sym) xk.R :=
  if op.1 then btLine xk bY bZ (decide (op.2.1 = 1)) (decide (op.2.2 = 1))
  else btLine xk bZ bY (decide (op.2.1 = 1)) (decide (op.2.2 = 1))

/-- A list of packed lines, in order. -/
def btLines : List (Bool × ℤ × ℕ) → Prog BTLoc (fun _ => Sym) xk.R
  | [] => skipW xk
  | op :: ops => .seq (btOp xk op) (btLines ops)

/-- **The triple transform** `T₀ ∘ S₀⁻¹`. -/
def btTri : Prog BTLoc (fun _ => Sym) xk.R :=
  .seq (btLines xk (eightOps.reverse.map negL)) (btT0 xk)

theorem closed_btAdd (tgt : BTLoc) (plus : Bool) : (btAdd xk tgt plus).Closed := by
  cases plus
  · exact ⟨closed_addTo xk _ _ _ _ _ _, closed_subFrom xk _ _ _ _ _ _⟩
  · exact closed_addTo xk _ _ _ _ _ _

theorem closed_btLine (tgt oth : BTLoc) (plus par : Bool) :
    (btLine xk tgt oth plus par).Closed :=
  ⟨closed_btLsum xk _ _, closed_btAdd xk _ _, closed_modBy xk _ _ _ _ _ _ _, closed_dropFW xk _⟩

theorem closed_btOp (op : Bool × ℤ × ℕ) : (btOp xk op).Closed := by
  unfold btOp
  split
  · exact closed_btLine xk _ _ _ _
  · exact closed_btLine xk _ _ _ _

theorem closed_btLines : ∀ ops : List (Bool × ℤ × ℕ), (btLines xk ops).Closed
  | [] => closed_skipW xk
  | op :: ops => ⟨closed_btOp xk op, closed_btLines ops⟩

theorem closed_btTri : (btTri xk).Closed := ⟨closed_btLines xk _, closed_btT0 xk⟩

end Progs

/-! ## One packed line -/

theorem btAdd_runs (xk : XKit BTLoc) (tgt : BTLoc) (h1 : tgt ≠ bOFF)
    (hN1 : [tgt, bOFF, bT0, bT1, bT2, bT3].Nodup) (hN2 : [tgt, bPL, bT0, bT1, bT2, bT3].Nodup)
    (plus : Bool) (L t A : ℕ) (rt r5 lOFF : List Sym) (S : BTLoc → List Sym)
    (hrt : TermOK rt) (hr5 : TermOK r5)
    (hSt : S tgt = natSyms t ++ rt) (hOFF : S bOFF = natSyms A ++ Sym.mark :: lOFF)
    (hS5 : S bPL = natSyms (2 ^ L) ++ r5) (ht : t < 2 ^ L) (hA : A < 2 ^ L) :
    Runs (btAdd xk tgt plus) S
      (Function.update S tgt (natSyms (if plus then t + A else t + 2 ^ L - A) ++ rt))
      (fun _ => True) (2 * opCost xk (L + 1)) := by
  have hL1 : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [pow_succ]; ring
  have htB : t < 2 ^ (L + 1) := by omega
  have hAB : A < 2 ^ (L + 1) := by omega
  have hLB : 2 ^ L < 2 ^ (L + 1) := by omega
  have hsB : t + A < 2 ^ (L + 1) := by omega
  have hs2B : t + 2 ^ L < 2 ^ (L + 1) := by omega
  cases plus
  · show Runs (.seq (addTo xk tgt bPL bT0 bT1 bT2 bT3) (subFrom xk tgt bOFF bT0 bT1 bT2 bT3)) S
      (Function.update S tgt (natSyms (t + 2 ^ L - A) ++ rt)) (fun _ => True) _
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq
      (runs_addTo xk hN2 t (2 ^ L) (L + 1) rt r5 S hrt hr5 hSt hS5
        (btBitLen_le htB) (btBitLen_le hLB) (btBitLen_le hs2B))
      (runs_subFrom xk hN1 (t + 2 ^ L) A (L + 1) rt (Sym.mark :: lOFF) _ hrt (termOK_mark _)
        (by omega) (by simp) (by simp [h1.symm, hOFF])
        (btBitLen_le hs2B) (btBitLen_le hAB))) (Function.update_idem _ _ _))
      (fun _ _ => trivial) (by omega)
  · show Runs (addTo xk tgt bOFF bT0 bT1 bT2 bT3) S
      (Function.update S tgt (natSyms (t + A) ++ rt)) (fun _ => True) _
    exact WP.W9comp.runs_mono (runs_addTo xk hN1 t A (L + 1) rt (Sym.mark :: lOFF) S hrt
      (termOK_mark _) hSt hOFF (btBitLen_le htB) (btBitLen_le hAB) (btBitLen_le hsB))
      (fun _ _ => trivial) (by omega)

/-- **One packed line on the machine**: the target `tgt` becomes `btLval plus L t A` with
`A = lsum K ρ x o par N`; nothing else changes. -/
theorem btLine_runs (xk : XKit BTLoc) (tgt oth : BTLoc)
    (hto : (tgt = bY ∧ oth = bZ) ∨ (tgt = bZ ∧ oth = bY))
    (plus par : Bool) (K ρ N L x o t : ℕ) (rx ro rt r3 r4 r5 r6 : List Sym)
    (S : BTLoc → List Sym) (hrx : TermOK rx) (hro : TermOK ro) (hrt : TermOK rt)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hSx : S bX = natSyms x ++ rx) (hSo : S oth = natSyms o ++ ro)
    (hSt : S tgt = natSyms t ++ rt) (hS3 : S bPK = natSyms (2 ^ K) ++ r3)
    (hS4 : S bPr = natSyms (2 ^ ρ) ++ r4) (hS5 : S bPL = natSyms (2 ^ L) ++ r5)
    (hS6 : S bF1 = natSyms N ++ r6) (hK : 1 ≤ K) (hNL : ρ + N * K < L) (hx : x < 2 ^ L)
    (ho : o < 2 ^ L) (ht : t < 2 ^ L) :
    Runs (btLine xk tgt oth plus par) S
      (Function.update S tgt (natSyms (btLval plus L t (lsum K ρ x o par N)) ++ rt))
      (fun _ => True) (16 * opCost xk (L + 1) * (N + 1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ : tgt ≠ bOFF ∧ tgt ≠ bPL ∧ oth ≠ bXS ∧ oth ≠ bOS ∧
      oth ≠ bCT ∧ [tgt, bOFF, bT0, bT1, bT2, bT3].Nodup ∧ [tgt, bPL, bT0, bT1, bT2, bT3].Nodup ∧
      [tgt, bPL, bT0, bT1, bT2, bT3, bT4].Nodup := by
    rcases hto with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hW := btOpCost_ge xk (L + 1)
  have hNK : N ≤ N * K := Nat.le_mul_of_pos_right N hK
  have hLp : L < 2 ^ L := Nat.lt_two_pow_self
  have hL1 : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [pow_succ]; ring
  have hAL : lsum K ρ x o par N < 2 ^ L :=
    lt_of_lt_of_le (lsum_lt K ρ x o par hK N) (Nat.pow_le_pow_right (by norm_num) hNL.le)
  have hv : (if plus then t + lsum K ρ x o par N else t + 2 ^ L - lsum K ρ x o par N) <
      2 ^ (L + 1) := by
    cases plus
    · show t + 2 ^ L - lsum K ρ x o par N < 2 ^ (L + 1)
      omega
    · show t + lsum K ρ x o par N < 2 ^ (L + 1)
      omega
  have e0 := btLsum_runs xk oth h3 h4 h5 par K ρ N (L + 1) x o rx ro r3 r4 r6 S hrx hro hr3 hr4
    hr6 hSx hSo hS3 hS4 hS6 hK (by omega) (by omega) (by omega) (by omega)
  have e1 := btAdd_runs xk tgt h1 h6 h7 plus L t (lsum K ρ x o par N) rt r5 (S bOFF)
    (Function.update S bOFF (natSyms (lsum K ρ x o par N) ++ Sym.mark :: S bOFF)) hrt hr5
    (by simp [h1, hSt]) (by simp)
    (by simp +decide [hS5]) ht hAL
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq e0
    (WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq
      (runs_modBy xk h8
        (if plus then t + lsum K ρ x o par N else t + 2 ^ L - lsum K ρ x o par N) (2 ^ L)
        (L + 1) rt r5 _ hrt hr5 (Nat.two_pow_pos L) (by simp)
        (by simp +decide [h2.symm, hS5]) (btBitLen_le hv)
        (btBitLen_le (by omega)))
      (runs_dropFW xk bOFF (lsum K ρ x o par N) Sym.mark (S bOFF) _ rfl
        (by simp [h1.symm]))))) ?_) (fun _ _ => trivial) ?_
  · rw [Function.update_idem, Function.update_comm h1, Function.update_idem,
      Function.update_eq_self]
    all_goals rfl
  · have e5 : 16 * opCost xk (L + 1) * (N + 1) = 16 * (opCost xk (L + 1) * (N + 1)) := by ring
    have e6 : 12 * opCost xk (L + 1) * (N + 1) = 12 * (opCost xk (L + 1) * (N + 1)) := by ring
    have e7 : opCost xk (L + 1) ≤ opCost xk (L + 1) * (N + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have e8 := btBitLen_le hAL
    omega

/-- The packed line `op` on the chunk pair `(y, z)` (stacks `Y`, `Z`). -/
theorem btOp_runs (xk : XKit BTLoc) (op : Bool × ℤ × ℕ) (hop : op.2.1 = 1 ∨ op.2.1 = -1)
    (hpar : op.2.2 ≤ 1) (K ρ f L x y z : ℕ) (rx ry rz r3 r4 r5 r6 : List Sym)
    (S : BTLoc → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hrz : TermOK rz)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hSx : S bX = natSyms x ++ rx) (hS3 : S bPK = natSyms (2 ^ K) ++ r3)
    (hS4 : S bPr = natSyms (2 ^ ρ) ++ r4) (hS5 : S bPL = natSyms (2 ^ L) ++ r5)
    (hS6 : S bF1 = natSyms (f - 1) ++ r6) (hK : 1 ≤ K) (hNL : ρ + (f - 1) * K < L)
    (hx : x < 2 ^ L) (hy : y < 2 ^ L) (hz : z < 2 ^ L) :
    Runs (btOp xk op)
      (Function.update (Function.update S bY (natSyms y ++ ry)) bZ (natSyms z ++ rz))
      (Function.update (Function.update S bY
          (natSyms (packedLine L K ρ f op (x, y, z)).2.1 ++ ry))
        bZ (natSyms (packedLine L K ρ f op (x, y, z)).2.2 ++ rz))
      (fun _ => True) (16 * opCost xk (L + 1) * (f - 1 + 1)) := by
  rw [packedLine_eq L K ρ f op hop hpar hK hNL.le x y z, btLineNew_eq, btLineNew_eq]
  obtain ⟨b, ε, par⟩ := op
  cases b
  · have e := btLine_runs xk bZ bY (Or.inr ⟨rfl, rfl⟩) (decide (ε = 1)) (decide (par = 1)) K ρ
      (f - 1) L x y z rx ry rz r3 r4 r5 r6
      (Function.update (Function.update S bY (natSyms y ++ ry)) bZ (natSyms z ++ rz))
      hrx hry hrz hr3 hr4 hr5 hr6
      (by simp +decide [hSx]) (by simp +decide)
      (by simp) (by simp +decide [hS3])
      (by simp +decide [hS4])
      (by simp +decide [hS5])
      (by simp +decide [hS6]) hK hNL hx hy hz
    rw [Function.update_idem] at e
    exact e
  · have e := btLine_runs xk bY bZ (Or.inl ⟨rfl, rfl⟩) (decide (ε = 1)) (decide (par = 1)) K ρ
      (f - 1) L x z y rx rz ry r3 r4 r5 r6
      (Function.update (Function.update S bY (natSyms y ++ ry)) bZ (natSyms z ++ rz))
      hrx hrz hry hr3 hr4 hr5 hr6
      (by simp +decide [hSx]) (by simp)
      (by simp +decide) (by simp +decide [hS3])
      (by simp +decide [hS4])
      (by simp +decide [hS5])
      (by simp +decide [hS6]) hK hNL hx hz hy
    rw [Function.update_comm (show (bZ : BTLoc) ≠ bY by decide), Function.update_idem] at e
    exact e

/-! ## The eight lines, `T₀`, and the composite -/

/-- A list of packed lines on the chunk pair `(y, z)`. -/
theorem btLines_runs (xk : XKit BTLoc) (K ρ f L x : ℕ) (rx ry rz r3 r4 r5 r6 : List Sym)
    (S : BTLoc → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hrz : TermOK rz)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hSx : S bX = natSyms x ++ rx) (hS3 : S bPK = natSyms (2 ^ K) ++ r3)
    (hS4 : S bPr = natSyms (2 ^ ρ) ++ r4) (hS5 : S bPL = natSyms (2 ^ L) ++ r5)
    (hS6 : S bF1 = natSyms (f - 1) ++ r6) (hK : 1 ≤ K) (hNL : ρ + (f - 1) * K < L)
    (hx : x < 2 ^ L) :
    ∀ (ops : List (Bool × ℤ × ℕ)), (∀ op ∈ ops, (op.2.1 = 1 ∨ op.2.1 = -1) ∧ op.2.2 ≤ 1) →
    ∀ y z, y < 2 ^ L → z < 2 ^ L →
    Runs (btLines xk ops)
      (Function.update (Function.update S bY (natSyms y ++ ry)) bZ (natSyms z ++ rz))
      (Function.update (Function.update S bY
          (natSyms (ops.foldl (fun p op => packedLine L K ρ f op p) (x, y, z)).2.1 ++ ry))
        bZ (natSyms (ops.foldl (fun p op => packedLine L K ρ f op p) (x, y, z)).2.2 ++ rz))
      (fun _ => True) (ops.length * (16 * opCost xk (L + 1) * (f - 1 + 1)) + 1)
  | [], _, _, _, _, _ => WP.W9comp.runs_mono (runs_skipW xk _) (fun _ _ => trivial) (by simp)
  | op :: ops, hops, y, z, hy, hz => by
    obtain ⟨hop, hpar⟩ := hops op (by simp)
    obtain ⟨h2, h3⟩ := btLine_lt L K ρ f op hop hpar hK hNL.le x y z hy hz
    have hpe : packedLine L K ρ f op (x, y, z) =
        (x, (packedLine L K ρ f op (x, y, z)).2.1, (packedLine L K ρ f op (x, y, z)).2.2) :=
      Prod.ext (btLine_fst L K ρ f op (x, y, z)) rfl
    have e1 := btOp_runs xk op hop hpar K ρ f L x y z rx ry rz r3 r4 r5 r6 S hrx hry hrz hr3 hr4
      hr5 hr6 hSx hS3 hS4 hS5 hS6 hK hNL hx hy hz
    have e2 := btLines_runs xk K ρ f L x rx ry rz r3 r4 r5 r6 S hrx hry hrz hr3 hr4 hr5 hr6 hSx
      hS3 hS4 hS5 hS6 hK hNL hx ops (fun o h => hops o (by simp [h])) _ _ h2 h3
    simp only [List.foldl_cons]
    rw [hpe]
    refine WP.W9comp.runs_mono (WP.W9comp.runs_seq e1 e2) (fun _ _ => trivial) ?_
    rw [List.length_cons, add_mul, one_mul]
    omega

/-- **The triple transform on the machine**: `(x, y, z) ↦ c7BadTri K ρ f (x, y, z)` in place. -/
theorem btTri_runs (xk : XKit BTLoc) (K ρ f x y z : ℕ) (rx ry rz r3 r4 r5 r6 : List Sym)
    (S : BTLoc → List Sym) (hK : 1 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (hx : x < 2 ^ (f * K))
    (hy : y < 2 ^ (f * K)) (hz : z < 2 ^ (f * K)) (hrx : TermOK rx) (hry : TermOK ry)
    (hrz : TermOK rz) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hSx : S bX = natSyms x ++ rx) (hSy : S bY = natSyms y ++ ry) (hSz : S bZ = natSyms z ++ rz)
    (hS3 : S bPK = natSyms (2 ^ K) ++ r3) (hS4 : S bPr = natSyms (2 ^ ρ) ++ r4)
    (hS5 : S bPL = natSyms (2 ^ (f * K)) ++ r5) (hS6 : S bF1 = natSyms (f - 1) ++ r6) :
    Runs (btTri xk) S
      (Function.update (Function.update (Function.update S bX
          (natSyms (c7BadTri K ρ f (x, y, z)).1 ++ rx))
        bY (natSyms (c7BadTri K ρ f (x, y, z)).2.1 ++ ry))
        bZ (natSyms (c7BadTri K ρ f (x, y, z)).2.2 ++ rz))
      (fun _ => True) (159 * opCost xk (f * K + 1) * f) := by
  have hfK : (f - 1) * K + K = f * K := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  have hNL : ρ + (f - 1) * K < f * K := by omega
  obtain ⟨y8, z8, ht8, hy8, hz8⟩ : ∃ y8 z8, (eightOps.reverse.map negL).foldl
      (fun p op => packedLine (f * K) K ρ f op p) (x, y, z) = (x, y8, z8) ∧
      y8 < 2 ^ (f * K) ∧ z8 < 2 ^ (f * K) := by
    obtain ⟨h8x, h8y, h8z⟩ :=
      btFold (f * K) K ρ f hK hNL.le x (eightOps.reverse.map negL) negL_ok y z hy hz
    exact ⟨_, _, Prod.ext h8x rfl, h8y, h8z⟩
  have e1 := btLines_runs xk K ρ f (f * K) x rx ry rz r3 r4 r5 r6 S hrx hry hrz hr3 hr4 hr5 hr6
    hSx hS3 hS4 hS5 hS6 hK hNL hx (eightOps.reverse.map negL) negL_ok y z hy hz
  have hS0 : Function.update (Function.update S bY (natSyms y ++ ry)) bZ (natSyms z ++ rz) = S := by
    rw [← hSy, ← hSz, Function.update_eq_self, Function.update_eq_self]
  rw [hS0, ht8] at e1
  have e2 := btT0_runs xk K ρ (f - 1) (f * K) x y8 rx ry r3 r4 r6
    (Function.update (Function.update S bY (natSyms y8 ++ ry)) bZ (natSyms z8 ++ rz))
    hrx hry hr3 hr4 hr6
    (by simp +decide [hSx]) (by simp +decide)
    (by simp +decide [hS3]) (by simp +decide [hS4])
    (by simp +decide [hS6]) hK hNL hx hy8
  have hc : c7BadTri K ρ f (x, y, z) = (x, y8 + lsum K ρ x y8 false (f - 1) -
      lsum K ρ x y8 true (f - 1), z8) := by
    unfold c7BadTri
    rw [packedS0inv_eq, ht8, packedT0_eq K ρ f hK]
  rw [hc]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq e1 e2) ?_)
    (fun _ _ => trivial) ?_
  · try dsimp only
    rw [← hSx, Function.update_eq_self, Function.update_comm (show (bZ : BTLoc) ≠ bY by decide),
      Function.update_idem]
  · have hlen : (eightOps.reverse.map negL).length = 8 := rfl
    rw [hlen, Nat.sub_add_cancel hf]
    have e5 : 16 * opCost xk (f * K + 1) * f = 16 * (opCost xk (f * K + 1) * f) := by ring
    have e6 : 30 * opCost xk (f * K + 1) * f = 30 * (opCost xk (f * K + 1) * f) := by ring
    have e7 : 159 * opCost xk (f * K + 1) * f = 159 * (opCost xk (f * K + 1) * f) := by ring
    have e8 : 1 ≤ opCost xk (f * K + 1) * f :=
      Nat.mul_pos (by have := btOpCost_ge xk (f * K + 1); omega) hf
    omega

end SubNLogN.Machine.AppC.C7BadTriAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts AppC.C7BadTriAux AppC.C7ExtractAux

/-- **Lemma A.9 extraction: the bad-record triple transform** (`C7BadTriStmt`, `C7BadTri.lean`).
Witness: the program `btTri (natKit BTLoc)` on `KLoc (Fin 11) (Fin 12)` (twelve private scratch
stacks, restored), cost constant `165360`. -/
theorem c7BadTri_holds : C7BadTriStmt := by
  refine ⟨165360, fun _ => ⟨Fin 12, inferInstance, inferInstance, (natKit BTLoc).R,
    btTri (natKit BTLoc), (natKit BTLoc).finR, (natKit BTLoc).neR,
    closed_btTri (natKit BTLoc), ?_⟩⟩
  intro K ρ f x y z rx ry rz r3 r4 r5 r6 r7 r8 r9 r10 S hK hρ hf hx hy hz hrx hry hrz hr3 hr4
    hr5 hr6 hr7 hr8 hr9 hr10 hSx hSy hSz hS3 hS4 hS5 hS6 hS7 hS8 hS9 hS10
  refine WP.W9comp.runs_mono (btTri_runs (natKit BTLoc) K ρ f x y z rx ry rz r8 r9 r7 r10 S
    (by omega) hρ hf hx hy hz hrx hry hrz hr8 hr9 hr7 hr10 hSx hSy hSz hS8 hS9 hS7 hS10)
    (fun _ _ => trivial) ?_
  have hc : (natKit BTLoc).c = 110 := rfl
  have hW : opCost (natKit BTLoc) (f * K + 1) = 260 * (f * K + 1 + 1) ^ 2 := by
    simp only [opCost, hc]
  have hfL : f ≤ f * K + 1 := by
    have := Nat.le_mul_of_pos_right f (show 0 < K by omega)
    omega
  have h1 : (f * K + 1 + 1) ^ 2 ≤ 4 * (f * K + 1) ^ 2 := by
    have h2 : f * K + 1 + 1 ≤ 2 * (f * K + 1) := by omega
    calc (f * K + 1 + 1) ^ 2 ≤ (2 * (f * K + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 4 * (f * K + 1) ^ 2 := by ring
  rw [hW]
  calc 159 * (260 * (f * K + 1 + 1) ^ 2) * f
      ≤ 159 * (260 * (4 * (f * K + 1) ^ 2)) * (f * K + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)) hfL
    _ = 165360 * (f * K + 1) ^ 3 := by ring

end SubNLogN.Machine
