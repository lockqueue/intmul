/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddCtrK
import SubNLogN.Machine.CCore.LeafRowAddCost
import SubNLogN.Machine.Contracts.AppC
import SubNLogN.Machine.AppC.C7Skel

/-!
# C-core leaf 9 (Lemma A.9 row addition): reduction of `RowAddStmt` to `C7PackedXorStmt` (`CCore/LeafRowAddMain.lean`)

`rowAdd_of_parts`: `RowAddStmt p` (`CCore/SkelDefs.lean`) from
* the Lemma A.9 (`lem:transfer13`) contract `C7PackedXorStmt p.τ σ` for every chunk arrangement `σ`
  (`Contracts/AppC.lean`, Section A.4);
* `p.OK` (admissible constants, `Contracts/Layer.lean`). It gives the Lemma A.9 premise `s_b/W_b < m^τ`
  and the cost absorption;
* `RowAddGlueStmt`: the machine glue (role stream → Lemma A.9 array format, counters, call, back);
* `RowAddCtrCostStmt p`: the counter set-up cost is `O(V_g)` in the bands.
Both named statements are discharged in `LeafRowAddFin.lean`. `rowAddGlue_holds` uses
`LeafRowAddGlue.lean`. `rowAddCtrCost_of` uses the counter cost bound, which comes from
`LeafRowAddCtrCost.lean`. `LeafRowAdd.lean` assembles `rowAdd_of_c7`.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Math.Common SubNLogN.Math.Networks
open SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.CCore.LeafRowAddAux

/-- **Machine glue** (named statement, discharged by `rowAddGlue_holds` in `LeafRowAddFin.lean`).
For a Lemma A.9 kernel `P7` on `KLoc (Fin 8) E7` and counter programs `Pctr`, `Pclr` on the counter layout `CS`, there is a closed
program on `CL (Fin 8 ⊕ E7 ⊕ Fin 21)`. From a clean state with role stream `u` holding
`arrSyms v ++ [mark]` and the descriptor on `desc`, it safely produces role stream
`arrSyms v' ++ [mark]` (every other stack restored), whenever the counter programs set and clear
`vals` and `P7` maps `arrSyms v ++ [mark]` to `arrSyms v' ++ [mark]` under these counters. -/
def RowAddGlueStmt : Prop :=
  ∀ (E7 : Type) [Fintype E7] [DecidableEq E7] (R7 : Type) (u : Fin Wn)
    (Pctr Pclr : Prog CS (fun _ => Sym) Reg) (P7 : Prog (KLoc (Fin 8) E7) (fun _ => Sym) R7),
    ∃ Pr : Prog (CL (Fin 8 ⊕ E7 ⊕ Fin 21)) (fun _ => Sym) (Reg × R7),
      (Pctr.Closed → Pclr.Closed → P7.Closed → Pr.Closed) ∧
      ∀ (vals : Fin 7 → ℕ) (hdr tdesc : List Sym) (v v' : List (List Bool)) (Tctr Tclr T7 : ℕ),
        (∀ Sc : CS → List Sym, Sc .desc = hdr ++ tdesc → (∀ i, Sc (.w i) = []) →
          (∀ i, Sc (.c i) = []) → Runs Pctr Sc (setC Sc vals) (fun _ => True) Tctr) →
        (∀ Sc : CS → List Sym, (∀ i, Sc (.c i) = []) →
          Runs Pclr (setC Sc vals) Sc (fun _ => True) Tclr) →
        (∀ S7 : KLoc (Fin 8) E7 → List Sym, S7 (.inl 0) = arrSyms v ++ [Sym.mark] →
          (∀ i : Fin 7, S7 (.inl i.succ) = natSyms (vals i)) →
          Runs P7 S7 (Function.update S7 (.inl 0) (arrSyms v' ++ [Sym.mark])) (fun _ => True)
            T7) →
        ∀ S : CL (Fin 8 ⊕ E7 ⊕ Fin 21) → List Sym, KClean S → S descL = hdr ++ tdesc →
          S (roleL u) = arrSyms v ++ [Sym.mark] →
          Calculus.SafeRunsIn ccoreFramed [] Pr S
            (Function.update S (roleL u) (arrSyms v' ++ [Sym.mark])) (fun _ => True)
            (8 * (arrSyms v).length + 8 * (arrSyms v').length + 12 + Tctr + T7 + Tclr)

/-- **Counter cost** (named statement, discharged by `rowAddCtrCost_of` in `LeafRowAddFin.lean`
from the bound in `LeafRowAddCtrCost.lean`): in the bands, the counter set-up and clean-up cost `O(V_g)`. -/
def RowAddCtrCostStmt (p : LayerParams) : Prop :=
  ∃ P₀ C : ℕ, ∀ (t : CCoreRT) (p₁ p₂ : ℕ), CCoreBands p P₀ t → p₁ < mn → p₂ < mn → p₁ ≠ p₂ →
    1 ≤ t.k → costAll t p₁ p₂ + costClr (ctrVals t p₁ p₂) ≤ C * t.volG

namespace LeafRowAddAux

theorem hiS_lt {p₁ p₂ : ℕ} (h1 : p₁ < mn) (h2 : p₂ < mn) : hiS p₁ p₂ < mn := by
  have h3 := (thirdSlot_ne p₁ p₂).2.2
  have : 3 ≤ mn := by norm_num [mn, tripleM]
  simp only [hiS]; omega

theorem slot_fit {t : CCoreRT} (hk : 1 ≤ t.k) (hfit : t.j0 + t.e ≤ t.D) {s : ℕ} (hs : s < mn) :
    t.j0 + s * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D := by
  have h1 : s * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ mn * mn ^ (t.k - 1) := by
    have := Nat.mul_le_mul_right (mn ^ (t.k - 1)) (Nat.succ_le_of_lt hs)
    rw [Nat.succ_mul] at this; exact this
  have h2 : mn * mn ^ (t.k - 1) = t.e := by
    rw [CCoreRT.e, ← pow_succ', Nat.sub_add_cancel hk]
  omega

theorem ctrVals_N1 (K f j0 p₁ p₂ : ℕ) (hp : p₁ ≠ p₂) :
    2 ^ (K * f * (midS p₁ p₂ - loS p₁ p₂ - 1)) = c7N1 K f j0 p₁ p₂ := by
  obtain ⟨hlm, -, -, -⟩ := slots_sorted hp
  have g := slot_gap (f := f) hlm j0
  unfold c7N1
  congr 1
  have e : j0 + midS p₁ p₂ * f - (j0 + loS p₁ p₂ * f) - f = (midS p₁ p₂ - loS p₁ p₂ - 1) * f := by
    rw [Nat.sub_mul, Nat.sub_mul, one_mul]; omega
  rw [e]; ring

theorem ctrVals_N2 (K f j0 p₁ p₂ : ℕ) (hp : p₁ ≠ p₂) :
    2 ^ (K * f * (hiS p₁ p₂ - midS p₁ p₂ - 1)) = c7N2 K f j0 p₁ p₂ := by
  obtain ⟨-, hmh, -, -⟩ := slots_sorted hp
  have g := slot_gap (f := f) hmh j0
  unfold c7N2
  congr 1
  have e : j0 + hiS p₁ p₂ * f - (j0 + midS p₁ p₂ * f) - f = (hiS p₁ p₂ - midS p₁ p₂ - 1) * f := by
    rw [Nat.sub_mul, Nat.sub_mul, one_mul]; omega
  rw [e]; ring

theorem ctrVals_N3 (K D S f j0 p₁ p₂ : ℕ) :
    S * 2 ^ (K * (D - (f * (hiS p₁ p₂ + 1) + j0))) = c7N3 K D S f j0 p₁ p₂ := by
  unfold c7N3
  congr 3
  have : f * (hiS p₁ p₂ + 1) = hiS p₁ p₂ * f + f := by ring
  omega

theorem blkTerm_mark : BlkTerm [Sym.mark] := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact ⟨rfl, by decide⟩

end LeafRowAddAux

open LeafRowAddCostAux in
/-- **`RowAddStmt` from the Lemma A.9 contract** (and the glue and counter-cost statements).
Premises: the Lemma A.9 contract `C7PackedXorStmt p.τ σ` for every chunk arrangement `σ`; admissible
constants `p.OK`; `RowAddGlueStmt`; `RowAddCtrCostStmt p`. -/
theorem rowAdd_of_parts (p : LayerParams) (hp : p.OK) (hC7 : ∀ σ, C7PackedXorStmt p.τ σ)
    (hGlue : RowAddGlueStmt) (hCC : RowAddCtrCostStmt p) : RowAddStmt p := by
  have hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ p.τ := hp.2.2.2.2.1
  have hK7 := fun σ => hC7 σ hτ
  unfold KContract at hK7
  choose C7c hK7' using hK7
  obtain ⟨P₁, C₀, hc7⟩ := c7Cost_absorb p hp
  obtain ⟨P₂, Cc, hcc⟩ := hCC
  refine ⟨max 1 (max P₁ P₂), (Finset.univ.sup C7c) * C₀ + Cc + 40, ?_⟩
  rintro ⟨u, p₁, p₂⟩
  by_cases h12 : p₁ = p₂
  · refine ⟨Empty, inferInstance, inferInstance, Unit, .load id, inferInstance, ⟨()⟩, ?_, ?_⟩
    · simp [Prog.Closed, Prog.FreeBelow]
    · intro t hA' hS w tdesc S _ _ _ hne
      exact absurd h12 hne
  · obtain ⟨E7, iF, iD, R7, P7, hfin, hne7, hcl7, hspec⟩ := hK7' (c7Sigma p₁.val p₂.val) ()
    obtain ⟨Pr, hPrc, hPr⟩ := @hGlue E7 iF iD R7 u (ctrAll p₁.val p₂.val) ctrClr P7
    refine ⟨Fin 8 ⊕ E7 ⊕ Fin 21, inferInstance, inferInstance, Reg × R7, Pr, ?_, ?_,
      hPrc (closed_ctrAll _ _) closed_ctrClr hcl7, ?_⟩
    · haveI := hfin; infer_instance
    · exact ⟨(default, hne7.some)⟩
    intro t hA' hS w tdesc S hb hk hK6 hne hclean hd hrole
    have hP1 : 1 ≤ max 1 (max P₁ P₂) := le_max_left _ _
    have hb1 : CCoreBands p P₁ t := bands_mono (le_trans (le_max_left _ _) (le_max_right _ _)) hb
    have hb2 : CCoreBands p P₂ t := bands_mono (le_trans (le_max_right _ _) (le_max_right _ _)) hb
    obtain ⟨-, -, hr1, -, -, hA1, hS1, -, -⟩ := bands_basic hp hP1 hb
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfit, hρK, -⟩ := hb
    have hp12 : p₁.val ≠ p₂.val := fun h => hne (Fin.ext h)
    have hhi := hiS_lt p₁.isLt p₂.isLt
    have hfitHi := slot_fit hk hfit hhi
    have hf1 : 1 ≤ mn ^ (t.k - 1) := Nat.one_le_pow _ _ (by norm_num [mn, tripleM])
    -- value layer
    have hvlen := recList_length t hA' hS w
    have hvw := recList_width t hA' hS w
    have hout := enc_runSteps_rowAdd t hA' hS p₁ p₂ hne hk hK6 hρK hfit w
    have hpx := packedXorAddr_rowAdd (K := t.K) (D := t.D) (S := t.S) (f := mn ^ (t.k - 1))
      (j0 := t.j0) (ρ := t.ρ) hp12 hfitHi
    rw [← hpx] at hout
    -- the image index stays in range
    have hgr : ∀ y < (recList t hA' hS w).length,
        packedXorAddr (mn ^ (t.k - 1) * t.K) t.K t.ρ (mn ^ (t.k - 1))
          (c7N1 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7N2 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂)
          (c7N3 t.K t.D t.S (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7Sigma p₁ p₂) y <
          (recList t hA' hS w).length := by
      intro y hy
      rw [hpx, hvlen]
      rw [hvlen] at hy
      exact (pxa_layer hA' hS hρK (slot_fit hk hfit p₁.isLt) (slot_fit hk hfit p₂.isLt) hy).1
    -- the Lemma A.9 call in the glue format
    have hC7' : ∀ S7 : KLoc (Fin 8) E7 → List Sym, S7 (.inl 0) = arrSyms (recList t hA' hS w) ++
        [Sym.mark] → (∀ i : Fin 7, S7 (.inl i.succ) = natSyms (ctrVals t p₁ p₂ i)) →
        Runs P7 S7 (Function.update S7 (.inl 0) (arrSyms (permByInv
          (packedXorAddr (mn ^ (t.k - 1) * t.K) t.K t.ρ (mn ^ (t.k - 1))
            (c7N1 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7N2 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂)
            (c7N3 t.K t.D t.S (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7Sigma p₁ p₂))
          (recList t hA' hS w)) ++ [Sym.mark])) (fun _ => True)
          (C7c (c7Sigma p₁ p₂) * c7Cost p.τ t.K (mn ^ (t.k - 1)) (recList t hA' hS w).length
            (vol (recList t hA' hS w)) (2 * t.r * t.wg)) := by
      intro S7 h0 hi
      have e1 : S7 (.inl 1) = natSyms t.K ++ [] := by rw [List.append_nil]; exact hi 0
      have e2 : S7 (.inl 2) = natSyms t.ρ ++ [] := by rw [List.append_nil]; exact hi 1
      have e3 : S7 (.inl 3) = natSyms (mn ^ (t.k - 1)) ++ [] := by
        rw [List.append_nil]; exact hi 2
      have e4 : S7 (.inl 4) = natSyms (c7N1 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂) ++ [] := by
        rw [List.append_nil, ← ctrVals_N1 _ _ _ _ _ hp12]; exact hi 3
      have e5 : S7 (.inl 5) = natSyms (c7N2 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂) ++ [] := by
        rw [List.append_nil, ← ctrVals_N2 _ _ _ _ _ hp12]; exact hi 4
      have e6 : S7 (.inl 6) = natSyms (c7N3 t.K t.D t.S (mn ^ (t.k - 1)) t.j0 p₁ p₂) ++ [] := by
        rw [List.append_nil, ← ctrVals_N3]; exact hi 5
      have e7 : S7 (.inl 7) = natSyms (2 * t.r * t.wg) ++ [] := by
        rw [List.append_nil]; exact hi 6
      have hwg : 3 ≤ t.wg := by simp only [CCoreRT.wg]; omega
      have hR1 : 1 ≤ 2 * t.r * t.wg := by nlinarith
      have hlen : (recList t hA' hS w).length =
          c7N0 (t.A / Wn) t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂ * 2 ^ (mn ^ (t.k - 1) * t.K) *
            c7N1 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂ * 2 ^ (mn ^ (t.k - 1) * t.K) *
            c7N2 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂ * 2 ^ (mn ^ (t.k - 1) * t.K) *
            c7N3 t.K t.D t.S (mn ^ (t.k - 1)) t.j0 p₁ p₂ := by
        rw [hvlen]; exact c7_shape hp12 hfitHi
      exact hspec t.K t.ρ (mn ^ (t.k - 1)) (c7N0 (t.A / Wn) t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂)
        (c7N1 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7N2 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂)
        (c7N3 t.K t.D t.S (mn ^ (t.k - 1)) t.j0 p₁ p₂) (2 * t.r * t.wg) (recList t hA' hS w)
        [Sym.mark] [] [] [] [] [] [] [] S7 hK6 hρK hf1
        (Nat.mul_pos hA' (Nat.two_pow_pos _)) (Nat.two_pow_pos _) (Nat.two_pow_pos _)
        (Nat.mul_pos hS (Nat.two_pow_pos _)) hR1 hlen hvw blkTerm_mark termOK_nil termOK_nil
        termOK_nil termOK_nil termOK_nil termOK_nil termOK_nil h0 e1 e2 e3 e4 e5 e6 e7
    have hle : mn ^ (t.k - 1) * (hiS p₁ p₂ + 1) + t.j0 ≤ t.D := by
      have : mn ^ (t.k - 1) * (hiS p₁ p₂ + 1) = hiS p₁ p₂ * mn ^ (t.k - 1) + mn ^ (t.k - 1) := by
        ring
      omega
    have hrole' : S (roleL u) = arrSyms (recList t hA' hS w) ++ [Sym.mark] := by
      rw [hrole, enc_eq]
    have hg := hPr (ctrVals t p₁ p₂) t.hdr tdesc (recList t hA' hS w) _ (costAll t p₁ p₂)
      (costClr (ctrVals t p₁ p₂)) _
      (fun Sc hd' hw hc => runs_ctrAll t tdesc p₁ p₂ Sc hd' hw hc hk hle)
      (fun Sc hc => runs_ctrClr' _ Sc hc) hC7' S hclean hd hrole'
    refine Calculus.SafeRunsIn.congr hg ?_ ?_
    · rw [hout]
    · -- cost
      have hwg : 3 ≤ t.wg := by simp only [CCoreRT.wg]; omega
      have hR1 : 1 ≤ 2 * t.r * t.wg := by nlinarith
      have hvol : vol (recList t hA' hS w) = (recList t hA' hS w).length * (2 * t.r * t.wg + 1) :=
        AppC.C7Aux.vol_of_len hvw
      have hvw' : ∀ q ∈ permByInv (packedXorAddr (mn ^ (t.k - 1) * t.K) t.K t.ρ (mn ^ (t.k - 1))
          (c7N1 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7N2 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂)
          (c7N3 t.K t.D t.S (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7Sigma p₁ p₂)) (recList t hA' hS w),
          q.length = 2 * t.r * t.wg :=
        fun q hq => hvw q (AppC.C7Aux.permByInv_mem hgr hq)
      have hvol' := AppC.C7Aux.vol_of_len hvw'
      rw [AppC.C7Aux.permByInv_length] at hvol'
      have hM' := M'_le_M t
      have hVG : t.volG = t.M * (2 * t.r * t.wg) := by unfold CCoreRT.volG; ring
      have hM1 : 1 ≤ t.M := by
        unfold CCoreRT.M; exact Nat.mul_pos (Nat.mul_pos hA1 hS1) (Nat.two_pow_pos _)
      have hX6 : 6 ≤ t.volG := by rw [hVG]; nlinarith
      have hA2 : vol (recList t hA' hS w) ≤ 2 * t.volG := by
        rw [hvol, hvlen, hVG]
        calc t.A / Wn * 2 ^ (t.K * t.D) * t.S * (2 * t.r * t.wg + 1)
            ≤ t.M * (2 * t.r * t.wg + 1) := Nat.mul_le_mul_right _ hM'
          _ ≤ 2 * (t.M * (2 * t.r * t.wg)) := by nlinarith
      have hA2' : vol (permByInv (packedXorAddr (mn ^ (t.k - 1) * t.K) t.K t.ρ (mn ^ (t.k - 1))
          (c7N1 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7N2 t.K (mn ^ (t.k - 1)) t.j0 p₁ p₂)
          (c7N3 t.K t.D t.S (mn ^ (t.k - 1)) t.j0 p₁ p₂) (c7Sigma p₁ p₂)) (recList t hA' hS w))
          ≤ 2 * t.volG := by rw [hvol', ← hvol]; exact hA2
      have hc7b := hc7 t hb1 hk hK6
      have hsup : C7c (c7Sigma p₁ p₂) ≤ Finset.univ.sup C7c := Finset.le_sup (Finset.mem_univ _)
      have h7 : C7c (c7Sigma p₁ p₂) * c7Cost p.τ t.K (mn ^ (t.k - 1)) (recList t hA' hS w).length
          (vol (recList t hA' hS w)) (2 * t.r * t.wg) ≤
          Finset.univ.sup C7c * (C₀ * (t.volG * (Utau p.τ (t.e * t.K) + 1))) := by
        apply Nat.mul_le_mul hsup
        rw [hvol, hvlen]
        exact hc7b
      have hccb := hcc t p₁ p₂ hb2 p₁.isLt p₂.isLt hp12 hk
      have hXU : t.volG ≤ t.volG * (Utau p.τ (t.e * t.K) + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have hfin : (Finset.univ.sup C7c * C₀ + Cc + 40) * (t.volG * (Utau p.τ (t.e * t.K) + 1)) =
          Finset.univ.sup C7c * (C₀ * (t.volG * (Utau p.τ (t.e * t.K) + 1))) +
            Cc * (t.volG * (Utau p.τ (t.e * t.K) + 1)) +
            40 * (t.volG * (Utau p.τ (t.e * t.K) + 1)) := by ring
      have hc1 := Nat.mul_le_mul_left Cc hXU
      have hc2 := Nat.mul_le_mul_left 40 hXU
      change 8 * vol (recList t hA' hS w) + 8 * vol _ + 12 + _ + _ + _ ≤ _
      rw [hfin]
      omega

end SubNLogN.Machine.CCore
