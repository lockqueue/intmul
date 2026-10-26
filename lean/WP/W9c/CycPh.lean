import WP.W9c.CycState

/-!
# WP.W9c.CycPh — the loops of the cyclic emit kernel

Registers `CR R = Option Sym × R`. One iteration of the main loop (`cB`), for the value `v` on
top of `cV`:
* if the top of `cR` is `mark` (cursor `r`), wrap: move the `r` cells of `cL` back onto `cR`,
  entry by entry, order kept (`cWrap`, a loop driven by `cL`);
* push `sep` on `cL`, then `cL += c + v` (`c` the cell on top of `cR`), drop `c` and `v`
  (`cCommon`).
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

/-- Registers of the cyclic emit kernel: the symbol register and the adder's registers. -/
abbrev CR (R : Type) : Type := Option Sym × R

/-- The wrap: all left cells back to the right stack. -/
def cWrap (R : Type) : HP 3 4 (CR R) :=
  whileTop (Lens.fst _ _) cL isSign (mvNum (Lens.fst _ _) cL cR cX)

/-- Add the value to the right cell and push the sum on the left stack. -/
def cCommon (I : Inst 3 4 Unit) : HP 3 4 (CR I.R) :=
  (pushS cL .sep).seq ((callI I [cR, cV, cL] cV (Lens.snd _ _)).seq
    ((dropNum (Lens.fst _ _) cR).seq (dropNum (Lens.fst _ _) cV)))

/-- One iteration of the main loop. -/
def cB (I : Inst 3 4 Unit) : HP 3 4 (CR I.R) :=
  (ifTop (Lens.fst _ _) cR isMark (cWrap I.R) skipS).seq (cCommon I)

theorem cWrap_closed (R : Type) : (cWrap R).Closed :=
  whileTop_closed _ _ _ (mvNum_closed _ _ _ _)

theorem cCommon_closed (I : Inst 3 4 Unit) : (cCommon I).Closed :=
  ⟨trivial, callI_closed _ _ _ _, dropNum_closed _ _, dropNum_closed _ _⟩

theorem cB_closed (I : Inst 3 4 Unit) : (cB I).Closed :=
  ⟨ifTop_closed _ _ _ (cWrap_closed _) skipS_closed, cCommon_closed I⟩

variable {R : Type}

/-! ## The wrap loop -/

theorem cyc_wrapL (ρ : List (HP 3 4 (CR R))) (Bc : ℕ) (vv rL rR x s1 s2 s3 : List Sym)
    (ls : List ℤ) : ∀ (racc : List ℤ), (∀ c ∈ ls, bitLen c.natAbs ≤ Bc) →
      LT ρ (Lens.fst _ _) cL isSign (mvNum (Lens.fst _ _) cL cR cX)
        (CS.f ⟨vv, listSyms ls ++ Sym.mark :: rL, listSyms racc ++ rR, x, s1, s2, s3⟩)
        (CS.f ⟨vv, Sym.mark :: rL, listSyms (ls.reverse ++ racc) ++ rR, x, s1, s2, s3⟩)
        (ls.length * (8 * Bc + 12) + 1) := by
  induction ls with
  | nil =>
    intro racc _
    exact LT.of_eq (ck_lt_stop _ _ _ _ _ rfl) rfl (by simp)
  | cons c ls ih =>
    intro racc hb
    have h1 := ck_mvNum (ρ := ρ) (Lens.fst (Option Sym) R) (src := cL) (dst := cR) (X := cX)
      (by decide) (by decide) (by decide)
      (CS.f ⟨vv, listSyms (c :: ls) ++ Sym.mark :: rL, listSyms racc ++ rR, x, s1, s2, s3⟩) c
      (listSyms ls ++ Sym.mark :: rL) (cons_entry c ls _).symm
    rw [cupd_l, cf_r, cupd_r, cons_entry] at h1
    have h2 := ih (c :: racc) (fun c' hc' => hb c' (List.mem_cons_of_mem _ hc'))
    have hc := hb c (by simp)
    refine LT.of_eq (ck_lt_step _ _ _ _ (optT_isSign_listSyms_cons c ls _)
      (h1.mono (show 8 * bitLen c.natAbs + 10 ≤ 8 * Bc + 10 by omega)) h2) ?_ ?_
    · simp
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-! ## One value -/

theorem cyc_common {I : Inst 3 4 Unit} {Ca : ℕ} (hI : SpecAddInt I Ca)
    (ρ : List (HP 3 4 (CR I.R))) (Bc Bv : ℕ) (cells : List ℤ) (q : ℕ) (hq : q < cells.length)
    (v : ℤ) (vs : List ℤ) (rv rL rR x s1 s2 s3 : List Sym)
    (hc : bitLen (cells.getD q 0).natAbs ≤ Bc) (hv : bitLen v.natAbs ≤ Bv) :
    HT ρ (CS.f ⟨listSyms (v :: vs) ++ rv, listSyms (cells.take q).reverse ++ Sym.mark :: rL,
        listSyms (cells.drop q) ++ Sym.mark :: rR, x, s1, s2, s3⟩) (cCommon I)
      (CS.f ⟨listSyms vs ++ rv, tapeL (cells.set q (cells.getD q 0 + v)) (q + 1) ++ rL,
        tapeR (cells.set q (cells.getD q 0 + v)) (q + 1) ++ rR, x, s1, s2, s3⟩)
      (Ca * (Bc + Bv + 1) + 3 * Bc + 3 * Bv + 9) := by
  have hdrop : listSyms (cells.drop q) ++ Sym.mark :: rR = intSyms (cells.getD q 0) ++
      Sym.sep :: (listSyms (cells.drop (q + 1)) ++ Sym.mark :: rR) := by
    rw [drop_eq_getD_cons cells q hq, cons_entry]
  have h1 := HT.pushS (σ := CR I.R) cL Sym.sep (CS.f ⟨listSyms (v :: vs) ++ rv,
    listSyms (cells.take q).reverse ++ Sym.mark :: rL, listSyms (cells.drop q) ++ Sym.mark :: rR,
    x, s1, s2, s3⟩) ρ
  rw [cf_l, cupd_l] at h1
  have h2 := ck_addInt (ρ := ρ) hI cV (Lens.snd (Option Sym) I.R) cR cV cL (by decide)
    (by decide) (CS.f ⟨listSyms (v :: vs) ++ rv,
      Sym.sep :: (listSyms (cells.take q).reverse ++ Sym.mark :: rL),
      listSyms (cells.drop q) ++ Sym.mark :: rR, x, s1, s2, s3⟩) (cells.getD q 0) v _ _
    (termOK_sep _) (termOK_sep _) hdrop (cons_entry v vs rv).symm
  rw [cf_l, cupd_l] at h2
  have h3 := ck_dropNum (ρ := ρ) (Lens.fst (Option Sym) I.R) cR
    (CS.f ⟨listSyms (v :: vs) ++ rv, intSyms (cells.getD q 0 + v) ++ Sym.sep ::
      (listSyms (cells.take q).reverse ++ Sym.mark :: rL),
      listSyms (cells.drop q) ++ Sym.mark :: rR, x, s1, s2, s3⟩) (cells.getD q 0) _ hdrop
  rw [cupd_r] at h3
  have h4 := ck_dropNum (ρ := ρ) (Lens.fst (Option Sym) I.R) cV
    (CS.f ⟨listSyms (v :: vs) ++ rv, intSyms (cells.getD q 0 + v) ++ Sym.sep ::
      (listSyms (cells.take q).reverse ++ Sym.mark :: rL),
      listSyms (cells.drop (q + 1)) ++ Sym.mark :: rR, x, s1, s2, s3⟩) v _
    (cons_entry v vs rv).symm
  rw [cupd_v] at h4
  refine HT.of_eq (HT.seq h1 (HT.seq h2 (HT.seq h3 h4))) ?_ ?_
  · rw [cons_entry, tapeL_app, tapeR_app, take_set_succ cells q _ hq, drop_set_succ]
    simp
  · have : Ca * (bitLen (cells.getD q 0).natAbs + bitLen v.natAbs + 1) ≤ Ca * (Bc + Bv + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem cyc_step {I : Inst 3 4 Unit} {Ca : ℕ} (hI : SpecAddInt I Ca)
    (ρ : List (HP 3 4 (CR I.R))) (Bc Bv r : ℕ) (cells : List ℤ) (p : ℕ) (hlen : cells.length = r)
    (hr : 0 < r) (hp : p ≤ r) (v : ℤ) (vs : List ℤ) (rv rL rR x s1 s2 s3 : List Sym)
    (hcells : ∀ c ∈ cells, bitLen c.natAbs ≤ Bc) (hv : bitLen v.natAbs ≤ Bv) :
    HT ρ (CS.f ⟨listSyms (v :: vs) ++ rv, tapeL cells p ++ rL, tapeR cells p ++ rR, x, s1, s2, s3⟩)
      (cB I)
      (CS.f ⟨listSyms vs ++ rv,
        tapeL (cells.set (qOf r p) (cells.getD (qOf r p) 0 + v)) (qOf r p + 1) ++ rL,
        tapeR (cells.set (qOf r p) (cells.getD (qOf r p) 0 + v)) (qOf r p + 1) ++ rR,
        x, s1, s2, s3⟩)
      (Ca * (Bc + Bv + 1) + 3 * Bc + 3 * Bv + 12 +
        (if p = r then r * (8 * Bc + 12) + 2 else 0)) := by
  have hq := qOf_lt hr hp
  have hc : bitLen (cells.getD (qOf r p) 0).natAbs ≤ Bc := hcells _ (getD_mem_of_lt _ (by omega))
  have hcom := cyc_common hI ρ Bc Bv cells (qOf r p) (by omega) v vs rv rL rR x s1 s2 s3 hc hv
  by_cases hpr : p = r
  · have hq0 : qOf r p = 0 := if_pos hpr
    rw [hq0] at hcom ⊢
    rw [if_pos hpr]
    have hw := ck_whileTop (ρ := ρ) _ _ _ _ (cyc_wrapL (R := I.R) ρ Bc (listSyms (v :: vs) ++ rv)
      rL (Sym.mark :: rR) x s1 s2 s3 cells.reverse [] (fun c hc => hcells c (List.mem_reverse.mp hc)))
    have hpre : CS.f ⟨listSyms (v :: vs) ++ rv, tapeL cells p ++ rL, tapeR cells p ++ rR, x, s1,
        s2, s3⟩ = CS.f ⟨listSyms (v :: vs) ++ rv, listSyms cells.reverse ++ Sym.mark :: rL,
        listSyms [] ++ Sym.mark :: rR, x, s1, s2, s3⟩ := by
      rw [tapeL_app, tapeR_app, hpr, ← hlen, List.take_length, List.drop_length]
    have hmid : CS.f ⟨listSyms (v :: vs) ++ rv, Sym.mark :: rL,
        listSyms (cells.reverse.reverse ++ []) ++ Sym.mark :: rR, x, s1, s2, s3⟩ =
        CS.f ⟨listSyms (v :: vs) ++ rv, listSyms (cells.take 0).reverse ++ Sym.mark :: rL,
          listSyms (cells.drop 0) ++ Sym.mark :: rR, x, s1, s2, s3⟩ := by
      simp [listSyms_nil]
    rw [hpre]
    refine HT.mono (HT.seq (ck_ifTop_pos _ _ _ _ _ rfl (hw.of_eq hmid le_rfl)) hcom) ?_
    simp only [List.length_reverse, hlen]
    omega
  · have hqp : qOf r p = p := if_neg hpr
    rw [hqp] at hcom ⊢
    rw [if_neg hpr]
    have hpre : CS.f ⟨listSyms (v :: vs) ++ rv, tapeL cells p ++ rL, tapeR cells p ++ rR, x, s1,
        s2, s3⟩ = CS.f ⟨listSyms (v :: vs) ++ rv, listSyms (cells.take p).reverse ++ Sym.mark :: rL,
        listSyms (cells.drop p) ++ Sym.mark :: rR, x, s1, s2, s3⟩ := by
      rw [tapeL_app, tapeR_app]
    rw [hpre]
    have htop : optT isMark (CS.f ⟨listSyms (v :: vs) ++ rv,
        listSyms (cells.take p).reverse ++ Sym.mark :: rL,
        listSyms (cells.drop p) ++ Sym.mark :: rR, x, s1, s2, s3⟩ cR).head? = false := by
      rw [cf_r, drop_eq_getD_cons cells p (by omega)]
      exact optT_isMark_listSyms_cons _ _ _
    refine HT.mono (HT.seq (ck_ifTop_neg _ _ _ _ _ htop (ck_skip _)) hcom) ?_
    omega

/-! ## The main loop -/

theorem cyc_loop {I : Inst 3 4 Unit} {Ca : ℕ} (hI : SpecAddInt I Ca)
    (ρ : List (HP 3 4 (CR I.R))) (Bc Bv r : ℕ) (hr : 0 < r) (rv rL rR x s1 s2 s3 : List Sym)
    (hrv : EndOK rv) (vs : List ℤ) :
    ∀ (cells : List ℤ) (p : ℕ), cells.length = r → p ≤ r → (∀ v ∈ vs, bitLen v.natAbs ≤ Bv) →
      (∀ j ≤ vs.length, ∀ c ∈ (cycAdd r cells p (vs.take j)).1, bitLen c.natAbs ≤ Bc) →
      LT ρ (Lens.fst _ _) cV isSign (cB I)
        (CS.f ⟨listSyms vs ++ rv, tapeL cells p ++ rL, tapeR cells p ++ rR, x, s1, s2, s3⟩)
        (CS.f ⟨rv, tapeL (cycAdd r cells p vs).1 (cycAdd r cells p vs).2 ++ rL,
          tapeR (cycAdd r cells p vs).1 (cycAdd r cells p vs).2 ++ rR, x, s1, s2, s3⟩)
        (vs.length * (Ca * (Bc + Bv + 1) + 3 * Bc + 3 * Bv + 14) +
          nwr r p vs * (r * (8 * Bc + 12) + 2) + 1) := by
  induction vs with
  | nil =>
    intro cells p _ _ _ _
    exact LT.of_eq (ck_lt_stop _ _ _ _ _ (optT_isSign_of_endOK hrv)) rfl (by simp [nwr])
  | cons v vs ih =>
    intro cells p hlen hp hbv hbc
    have hcells : ∀ c ∈ cells, bitLen c.natAbs ≤ Bc := hbc 0 (Nat.zero_le _)
    have h1 := cyc_step hI ρ Bc Bv r cells p hlen hr hp v vs rv rL rR x s1 s2 s3 hcells
      (hbv v (by simp))
    have h2 := ih (cells.set (qOf r p) (cells.getD (qOf r p) 0 + v)) (qOf r p + 1)
      (by rw [List.length_set, hlen]) (qOf_lt hr hp) (fun u hu => hbv u (by simp [hu]))
      (fun j hj => hbc (j + 1) (by simp; omega))
    refine LT.of_eq (ck_lt_step _ _ _ _ (optT_isSign_listSyms_cons v vs rv) h1 h2) rfl ?_
    simp only [nwr, List.length_cons, Nat.add_mul, Nat.one_mul]
    split_ifs <;> omega

#assert_std_axioms cWrap_closed cCommon_closed cB_closed cyc_wrapL cyc_common cyc_step cyc_loop

end WP.W9c.CK
