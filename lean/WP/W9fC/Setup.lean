import WP.W9fC.Facts
import WP.W9fC.Steps

/-!
# WP.W9fC.Setup — phase 0 of the column driver

From any stacks `σ` whose `C0` starts with `p, pSub, t1` (each followed by `mark`): `CT := t1` above
a guard, `C3 := 0` above a mark, guards on `A` and `M`, and `W0` moved to `M2` (order restored).
`C0`, `T`, `M` end as they started.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability

variable {m : ℕ}

/-- Change the initial stacks of a `Runs` along an equality. -/
theorem runs_pre {K σ' : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) σ'}
    {S1 S2 S' : K → List Sym} {Q : σ' → Prop} {T : ℕ} (h : Runs P S2 S' Q T) (he : S1 = S2) :
    Runs P S1 S' Q T := he ▸ h

theorem guard_not_mem_hdr2 (a b : ℕ) :
    symGuard ∉ Sym.mark :: ((natSyms a).reverse ++ Sym.mark :: (natSyms b).reverse) := by
  intro h
  simp only [List.mem_cons, List.mem_append, List.mem_reverse] at h
  rcases h with h | h | h | h
  · exact absurd h (by decide)
  · exact not_mem_natSyms rfl h
  · exact absurd h (by decide)
  · exact not_mem_natSyms rfl h

/-- The stacks after phase 0. -/
def setupV (σ : BLoc m → List Sym) (hm : 7 ≤ m) (t1 : ℕ) : Vals :=
  { V0 σ hm with
    w0 := []
    c3 := Sym.mark :: σ (.inl .C3)
    sm2 := σ (.inl .W0) ++ σ (sM2 hm)
    sa := symGuard :: σ (sA hm)
    sct := natSyms t1 ++ symGuard :: σ (sCT hm) }

theorem runs_setup (hm : 7 ≤ m) (R : Type) (σ : BLoc m → List Sym) (p pSub t1 : ℕ)
    (rest3 : List Sym)
    (hC0 : σ (.inl .C0) = natSyms p ++ Sym.mark ::
      (natSyms pSub ++ Sym.mark :: (natSyms t1 ++ Sym.mark :: rest3)))
    (hgW : symGuard ∉ σ (.inl .W0)) :
    Runs (setupProg hm R) σ (cst σ (setupV σ hm t1)) (fun _ => True)
      (6 * bitLen p + 6 * bitLen pSub + 7 * bitLen t1 + 6 * (σ (.inl .W0)).length + 30) := by
  have hc0 : (Sym.mark :: ((natSyms pSub).reverse ++ Sym.mark :: (natSyms p).reverse)).reverse ++
      (natSyms t1 ++ Sym.mark :: rest3) = σ (.inl .C0) := by
    rw [hC0]
    simp
  have hsm2 : (σ (.inl .W0)).reverse.reverse ++ σ (sM2 hm) = σ (.inl .W0) ++ σ (sM2 hm) := by
    rw [List.reverse_reverse]
  refine runs_pre ?_ (cst_V0 σ hm).symm
  unfold setupProg
  exact runs_mono
    (runs_seq (runs_pushC' R (sT hm) symGuard _ _ (upd_st σ _ _ hm)) <|
     runs_seq (runs_rewind' R (ne_inl_inr _ _) Sym.mark (natSyms p)
        (natSyms pSub ++ Sym.mark :: (natSyms t1 ++ Sym.mark :: rest3)) _ _
        (not_mem_natSyms rfl) (by exact hC0) (upd2 (upd_c0 σ _ _) (upd_st σ _ _ hm))) <|
     runs_seq (runs_pushC' R (sT hm) Sym.mark _ _ (upd_st σ _ _ hm)) <|
     runs_seq (runs_rewind' R (ne_inl_inr _ _) Sym.mark (natSyms pSub)
        (natSyms t1 ++ Sym.mark :: rest3) _ _
        (not_mem_natSyms rfl) (by exact rfl) (upd2 (upd_c0 σ _ _) (upd_st σ _ _ hm))) <|
     runs_seq (runs_pushC' R (sT hm) Sym.mark _ _ (upd_st σ _ _ hm)) <|
     runs_seq (runs_pushC' R (sCT hm) symGuard _ _ (upd_sct σ _ _ hm)) <|
     runs_seq (runs_copyNat R (ne_inl_inr _ _) (ne_inl_inr _ _) (ne_scr _ _ (by decide)) t1 (Sym.mark :: rest3) _ _
        (termOK_mark _) (by exact rfl) (upd_sct σ _ _ hm)) <|
     runs_seq (runs_rewind' R (ne_inr_inl _ _) symGuard
        (Sym.mark :: ((natSyms pSub).reverse ++ Sym.mark :: (natSyms p).reverse)) (σ (sT hm)) _ _
        (guard_not_mem_hdr2 pSub p)
        (by
          show Sym.mark :: ((natSyms pSub).reverse ++ Sym.mark :: ((natSyms p).reverse ++
            symGuard :: σ (sT hm))) = _
          simp)
        (upd2 (upd_st σ _ _ hm) (upd_c0 σ _ _))) <|
     runs_seq (runs_pushC' R (.inl .C3) Sym.mark _ _ (upd_c3 σ _ _)) <|
     runs_seq (runs_pushC' R (sM hm) symGuard _ _ (upd_sm σ _ _ hm)) <|
     runs_seq (runs_pushC' R (sA hm) symGuard _ _ (upd_sa σ _ _ hm)) <|
     runs_seq (runs_xfer' R (ne_inl_inr _ _) (σ (.inl .W0)) _ _ (by exact rfl)
        (upd2 (upd_w0 σ _ _) (upd_sm σ _ _ hm))) <|
     runs_rewind' R (ne_scr _ _ (by decide)) symGuard (σ (.inl .W0)).reverse (σ (sM hm)) _ _
        (by rw [List.mem_reverse]; exact hgW) (by exact rfl)
        (upd2 (upd_sm σ _ _ hm) ((upd_sm2 σ _ _ hm).trans (by
          exact congrArg (cst σ) (Vals.ext' rfl rfl rfl rfl rfl hc0 rfl hsm2 rfl rfl rfl rfl)))))
    (fun _ _ => trivial)
    (by
      simp only [List.length_cons, List.length_append, List.length_reverse, length_natSyms]
      omega)

#assert_std_axioms runs_pre guard_not_mem_hdr2 runs_setup

end WP.W9fC
