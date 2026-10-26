import WP.W9c.CKit

/-!
# WP.W9c.CMoves — symbol-run moves, list-entry moves and drops, the `addInt` call rule

* `ck_moveWhile` / `ck_popWhile`: move (reversed) / pop a maximal run of `c`-symbols;
* list entries `intSyms z ++ [sep]`: `ck_dropNum`, `ck_mvNum` (order preserved, through a temporary
  stack whose content is restored), `ck_mvRev` (symbol order reversed);
* `ck_addInt`: one instance of the frozen `W3_addInt` (`SpecAddInt`) called on host stacks;
* list-encoding facts (`listSyms_cons`, `listSyms_append`, lengths, peek tests).
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

variable {a b : ℕ} {σ : Type} {ρ : List (HP a b σ)}

/-! ## Update algebra -/

theorem upd2_upd2 {B : Loc a b → List Sym} {s d : Loc a b} (h : s ≠ d) (v₁ w₁ v₂ w₂ : List Sym) :
    Function.update (Function.update (Function.update (Function.update B s v₁) d w₁) s v₂) d w₂ =
      Function.update (Function.update B s v₂) d w₂ := by
  funext y
  by_cases h1 : y = d
  · subst h1
    simp only [Function.update_self]
  · by_cases h2 : y = s
    · subst h2
      simp only [Function.update_of_ne h1, Function.update_self]
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2]

/-! ## Runs of symbols -/

theorem ck_lt_moveWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) {src dst : Loc a b}
    (hne : src ≠ dst) (rest : List Sym) (hr : optT c rest.head? = false) (l : List Sym) :
    ∀ (B : Loc a b → List Sym), (∀ y ∈ l, c y = true) → B src = l ++ rest →
      LT ρ lS src c (mv1 lS src dst) B
        (Function.update (Function.update B src rest) dst (l.reverse ++ B dst))
        (4 * l.length + 1) := by
  induction l with
  | nil =>
    intro B _ hB
    have h1 : B src = rest := by simpa using hB
    have e : Function.update (Function.update B src rest) dst ([].reverse ++ B dst) = B := by
      rw [← h1]
      simp only [List.reverse_nil, List.nil_append, Function.update_eq_self]
    rw [e]
    exact ck_lt_stop lS src c _ B (by rw [h1]; exact hr)
  | cons y l ih =>
    intro B hl hB
    have hB' : B src = y :: (l ++ rest) := by simpa using hB
    have h1 := ck_mv1 (ρ := ρ) lS hne B y (l ++ rest) hB'
    have hsrc : Function.update (Function.update B src (l ++ rest)) dst (y :: B dst) src =
        l ++ rest := by
      rw [Function.update_of_ne hne, Function.update_self]
    have h2 := ih _ (fun z hz => hl z (List.mem_cons_of_mem _ hz)) hsrc
    refine LT.of_eq (ck_lt_step lS src c _ (by rw [hB']; exact hl y (by simp)) h1 h2) ?_ ?_
    · rw [Function.update_self, upd2_upd2 hne]
      simp
    · simp only [List.length_cons]
      omega

theorem ck_moveWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) {src dst : Loc a b}
    (hne : src ≠ dst) (rest : List Sym) (hr : optT c rest.head? = false) (l : List Sym)
    (B : Loc a b → List Sym) (hl : ∀ y ∈ l, c y = true) (hB : B src = l ++ rest) :
    HT ρ B (moveWhile lS c src dst)
      (Function.update (Function.update B src rest) dst (l.reverse ++ B dst)) (4 * l.length + 2) :=
  ck_whileTop lS src c _ (ck_lt_moveWhile lS c hne rest hr l B hl hB)

theorem ck_lt_popWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) (k : Loc a b)
    (rest : List Sym) (hr : optT c rest.head? = false) (l : List Sym) :
    ∀ (B : Loc a b → List Sym), (∀ y ∈ l, c y = true) → B k = l ++ rest →
      LT ρ lS k c (popS k) B (Function.update B k rest) (3 * l.length + 1) := by
  induction l with
  | nil =>
    intro B _ hB
    have h1 : B k = rest := by simpa using hB
    rw [← h1, Function.update_eq_self]
    exact ck_lt_stop lS k c _ B (by rw [h1]; exact hr)
  | cons y l ih =>
    intro B hl hB
    have hB' : B k = y :: (l ++ rest) := by simpa using hB
    have h1 := HT.popS (σ := σ) k B y (l ++ rest) hB' ρ
    have h2 := ih (Function.update B k (l ++ rest)) (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (Function.update_self _ _ _)
    refine LT.of_eq (ck_lt_step lS k c _ (by rw [hB']; exact hl y (by simp)) h1 h2)
      (Function.update_idem _ _ _) ?_
    simp only [List.length_cons]
    omega

theorem ck_popWhile (lS : Lens σ (Option Sym)) (c : Sym → Bool) (k : Loc a b) (rest : List Sym)
    (hr : optT c rest.head? = false) (l : List Sym) (B : Loc a b → List Sym)
    (hl : ∀ y ∈ l, c y = true) (hB : B k = l ++ rest) :
    HT ρ B (popWhile lS c k) (Function.update B k rest) (3 * l.length + 2) :=
  ck_whileTop lS k c _ (ck_lt_popWhile lS c k rest hr l B hl hB)

/-! ## List entries -/

theorem isBit_of_mem_natSyms (n : ℕ) : ∀ y ∈ natSyms n, y.isBit = true := by
  intro y hy
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
  rfl

theorem optT_isBit_sgn (z : ℤ) : optT Sym.isBit (some (sgnSym z)) = false := by
  unfold sgnSym
  split_ifs <;> rfl

theorem intSyms_cons_append (z : ℤ) (l : List Sym) :
    intSyms z ++ l = sgnSym z :: (natSyms z.natAbs ++ l) := rfl

theorem ck_dropNum (lS : Lens σ (Option Sym)) (k : Loc a b) (B : Loc a b → List Sym) (z : ℤ)
    (rest : List Sym) (hB : B k = intSyms z ++ Sym.sep :: rest) :
    HT ρ B (dropNum lS k) (Function.update B k rest) (3 * bitLen z.natAbs + 4) := by
  rw [intSyms_cons_append] at hB
  have h1 := HT.popS (σ := σ) k B _ _ hB ρ
  have h2 := ck_popWhile (ρ := ρ) lS Sym.isBit k (Sym.sep :: rest) rfl (natSyms z.natAbs)
    (Function.update B k (natSyms z.natAbs ++ Sym.sep :: rest)) (isBit_of_mem_natSyms _)
    (Function.update_self _ _ _)
  have h3 := HT.popS (σ := σ) k (Function.update (Function.update B k
    (natSyms z.natAbs ++ Sym.sep :: rest)) k (Sym.sep :: rest)) Sym.sep rest
    (Function.update_self _ _ _) ρ
  refine HT.of_eq (HT.seq h1 (HT.seq h2 h3)) ?_ ?_
  · simp only [Function.update_idem]
  · rw [length_natSyms]
    omega

theorem ck_mvRev (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (B : Loc a b → List Sym) (z : ℤ) (rest : List Sym) (hB : B src = intSyms z ++ Sym.sep :: rest) :
    HT ρ B (mvRev lS src dst) (Function.update (Function.update B src rest) dst
      ((intSyms z ++ [Sym.sep]).reverse ++ B dst)) (4 * bitLen z.natAbs + 6) := by
  rw [intSyms_cons_append] at hB
  have h1 := ck_mv1 (ρ := ρ) lS hne B _ _ hB
  have h2 := ck_moveWhile (ρ := ρ) lS Sym.isBit hne (Sym.sep :: rest) rfl (natSyms z.natAbs)
    (Function.update (Function.update B src (natSyms z.natAbs ++ Sym.sep :: rest)) dst
      (sgnSym z :: B dst)) (isBit_of_mem_natSyms _)
    (by rw [Function.update_of_ne hne, Function.update_self])
  refine HT.of_eq (HT.seq h1 (HT.seq h2 (ck_mv1 lS hne _ Sym.sep rest ?_))) ?_ ?_
  · rw [Function.update_of_ne hne, Function.update_self]
  · simp only [Function.update_self, upd2_upd2 hne]
    simp [intSyms]
  · rw [length_natSyms]
    omega

/-- Extensionality for two updated stacks. -/
theorem ext_upd2 {B B' : Loc a b → List Sym} {s d : Loc a b} (hsd : s ≠ d) (vs vd : List Sym)
    (hs : B' s = vs) (hd : B' d = vd) (ho : ∀ y, y ≠ s → y ≠ d → B' y = B y) :
    B' = Function.update (Function.update B s vs) d vd := by
  funext y
  by_cases h1 : y = d
  · subst h1
    rw [Function.update_self, hd]
  · rw [Function.update_of_ne h1]
    by_cases h2 : y = s
    · subst h2
      rw [Function.update_self, hs]
    · rw [Function.update_of_ne h2, ho y h2 h1]

theorem ck_mvNum (lS : Lens σ (Option Sym)) {src dst X : Loc a b} (h1 : src ≠ dst) (h2 : src ≠ X)
    (h3 : dst ≠ X) (B : Loc a b → List Sym) (z : ℤ) (rest : List Sym)
    (hB : B src = intSyms z ++ Sym.sep :: rest) :
    HT ρ B (mvNum lS src dst X)
      (Function.update (Function.update B src rest) dst (intSyms z ++ Sym.sep :: B dst))
      (8 * bitLen z.natAbs + 10) := by
  rw [intSyms_cons_append] at hB
  have e1 := ck_mv1 (ρ := ρ) lS h2 B _ _ hB
  have e2 := ck_moveWhile (ρ := ρ) lS Sym.isBit h2 (Sym.sep :: rest) rfl (natSyms z.natAbs)
    (Function.update (Function.update B src (natSyms z.natAbs ++ Sym.sep :: rest)) X
      (sgnSym z :: B X)) (isBit_of_mem_natSyms _)
    (by rw [Function.update_of_ne h2, Function.update_self])
  refine HT.of_eq (HT.seq e1 (HT.seq e2 (HT.seq (ck_mv1 lS h1 _ Sym.sep rest ?_)
    (HT.seq (ck_moveWhile lS Sym.isBit h3.symm (sgnSym z :: B X) (optT_isBit_sgn z)
      ((natSyms z.natAbs).reverse) _
      (fun y hy => isBit_of_mem_natSyms _ y (List.mem_reverse.mp hy)) ?_)
      (ck_mv1 lS h3.symm _ (sgnSym z) (B X) ?_))))) (ext_upd2 h1 _ _ ?_ ?_ ?_) ?_
  · rw [Function.update_of_ne h2, Function.update_self]
  · simp only [Function.update_self, Function.update_of_ne h3.symm, Function.update_of_ne h2.symm]
  · rw [Function.update_of_ne h3.symm, Function.update_self]
  · simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2]
  · simp only [Function.update_self, Function.update_of_ne h1.symm, Function.update_of_ne h3,
      List.reverse_reverse]
    rfl
  · intro y hys hyd
    by_cases hyx : y = X
    · subst hyx
      simp only [Function.update_self, Function.update_of_ne hyd]
    · simp only [Function.update_of_ne hys, Function.update_of_ne hyd, Function.update_of_ne hyx]
  · simp only [List.length_reverse, length_natSyms]
    omega

/-! ## The `addInt` call -/

/-- The body of `W3_addInt` for one instance. -/
def SpecAddInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (u v : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms u ++ rx → S (.inl 1) = intSyms v ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (u + v) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1))

/-- `z += u + v` (signed), operands on `x`, `y` restored. -/
theorem ck_addInt {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAddInt I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) :
    HT ρ B (callI I [x, y, z] dflt l) (Function.update B z (intSyms (u + v) ++ B z))
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1)) :=
  HT.callI_upd I [x, y, z] dflt hnd rfl hcap l B (.inl 2) _ (hI u v ru rv _ hru hrv hx hy) ρ

/-! ## The list encoding -/

theorem listSyms_nil : listSyms [] = [] := rfl

theorem listSyms_cons (v : ℤ) (vs : List ℤ) :
    listSyms (v :: vs) = intSyms v ++ Sym.sep :: listSyms vs := by
  simp [listSyms]

theorem listSyms_append (l₁ l₂ : List ℤ) : listSyms (l₁ ++ l₂) = listSyms l₁ ++ listSyms l₂ := by
  simp [listSyms]

theorem notMark_of_mem_listSyms (vs : List ℤ) : ∀ y ∈ listSyms vs, notMark y = true := by
  induction vs with
  | nil =>
    intro y hy
    simp [listSyms] at hy
  | cons v vs ih =>
    intro y hy
    rw [listSyms_cons, intSyms_cons_append] at hy
    rcases List.mem_cons.mp hy with h | h
    · subst h
      unfold sgnSym
      split_ifs <;> rfl
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h
        rfl
      · rcases List.mem_cons.mp h with h | h
        · subst h
          rfl
        · exact ih y h

theorem length_listSyms_le (vs : List ℤ) (B : ℕ) (h : ∀ v ∈ vs, bitLen v.natAbs ≤ B) :
    (listSyms vs).length ≤ vs.length * (B + 2) := by
  induction vs with
  | nil => simp [listSyms]
  | cons v vs ih =>
    have h1 := h v (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [listSyms_cons, intSyms_cons_append]
    simp only [List.length_cons, List.length_append, length_natSyms]
    rw [Nat.succ_mul]
    omega

theorem optT_isSign_cons (z : ℤ) (l : List Sym) : optT isSign (intSyms z ++ l).head? = true := by
  unfold intSyms sgnSym
  split_ifs <;> rfl

theorem optT_isSign_of_endOK {r : List Sym} (h : EndOK r) : optT isSign r.head? = false := by
  cases r with
  | nil => rfl
  | cons x r =>
    have hx := h x rfl
    cases x <;> simp_all [optT, isSign]

theorem termOK_sep (l : List Sym) : TermOK (Sym.sep :: l) := TermOK.cons rfl l

theorem intSyms_zero : intSyms 0 = [Sym.pos] := by
  simp [intSyms, sgnSym, natSyms, encodeNat_zero]

theorem cons_entry (v : ℤ) (vs : List ℤ) (r : List Sym) :
    intSyms v ++ Sym.sep :: (listSyms vs ++ r) = listSyms (v :: vs) ++ r := by
  rw [listSyms_cons]
  simp

theorem optT_isSign_listSyms_cons (v : ℤ) (vs : List ℤ) (r : List Sym) :
    optT isSign (listSyms (v :: vs) ++ r).head? = true := by
  rw [← cons_entry]
  exact optT_isSign_cons v _

theorem optT_isMark_listSyms_cons (v : ℤ) (vs : List ℤ) (r : List Sym) :
    optT isMark (listSyms (v :: vs) ++ r).head? = false := by
  rw [← cons_entry]
  unfold intSyms sgnSym
  split_ifs <;> rfl

#assert_std_axioms upd2_upd2 ck_lt_moveWhile ck_moveWhile ck_lt_popWhile ck_popWhile
  isBit_of_mem_natSyms optT_isBit_sgn intSyms_cons_append ck_dropNum ck_mvRev ext_upd2 ck_mvNum
  ck_addInt listSyms_nil listSyms_cons listSyms_append notMark_of_mem_listSyms length_listSyms_le
  optT_isSign_cons optT_isSign_of_endOK termOK_sep intSyms_zero cons_entry
  optT_isSign_listSyms_cons optT_isMark_listSyms_cons

end WP.W9c.CK
