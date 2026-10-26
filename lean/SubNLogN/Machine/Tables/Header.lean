/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Host
import Contracts.W9.Common

/-!
# K6 (`Machine/Tables/Header.lean`): fetching a field of the bridge header

**Scope (honest summary).** Infrastructure only. `fetchProg I sK sT dst` copies field number `k`
(`natSyms k` on the counter stack `sK`, consumed) of a header `hdrSyms hs` on `par` onto `dst`,
restoring `par`: it moves the first `k` fields (bits and marks) onto the empty temporary `sT`,
copies the field now on top (`W3_copyNat`), and moves everything back (`HT.fetch_spec`). Cost
`(C + 3)·(|hdrSyms hs| + 2)^2`, i.e. within the setup budget `(|hdr| + 1)^3` of the bridge header
(`BrPar.setup`, `SubNLogN/Machine/Contracts/Bridge.lean:107`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Header lists -/

theorem hdrSyms_nil : hdrSyms [] = [] := rfl

theorem hdrSyms_cons (x : ℕ) (xs : List ℕ) :
    hdrSyms (x :: xs) = natSyms x ++ Sym.mark :: hdrSyms xs := by
  simp [hdrSyms]

theorem hdrSyms_append (xs ys : List ℕ) : hdrSyms (xs ++ ys) = hdrSyms xs ++ hdrSyms ys := by
  simp [hdrSyms]

theorem mark_not_mem_natSyms (x : ℕ) : Sym.mark ∉ natSyms x := by
  simp [natSyms]

theorem length_hdrSyms_cons (x : ℕ) (xs : List ℕ) :
    (hdrSyms (x :: xs)).length = bitLen x + 1 + (hdrSyms xs).length := by
  rw [hdrSyms_cons]
  simp [length_natSyms]
  omega

theorem length_hdrSyms_append (xs ys : List ℕ) :
    (hdrSyms (xs ++ ys)).length = (hdrSyms xs).length + (hdrSyms ys).length := by
  rw [hdrSyms_append, List.length_append]

theorem bitLen_le_length_hdrSyms {hs : List ℕ} {k : ℕ} (hk : k < hs.length) :
    bitLen hs[k] + 1 ≤ (hdrSyms hs).length := by
  conv_rhs => rw [← List.take_append_drop k hs, List.drop_eq_getElem_cons hk]
  rw [length_hdrSyms_append, length_hdrSyms_cons]
  omega

theorem length_le_length_hdrSyms (hs : List ℕ) : hs.length ≤ (hdrSyms hs).length := by
  induction hs with
  | nil => simp [hdrSyms_nil]
  | cons x xs ih => rw [length_hdrSyms_cons]; simp; omega

theorem length_hdrSyms_take_le (hs : List ℕ) (k : ℕ) :
    (hdrSyms (hs.take k)).length ≤ (hdrSyms hs).length := by
  conv_rhs => rw [← List.take_append_drop k hs]
  rw [length_hdrSyms_append]
  omega

/-! ## The fetch program -/

/-- Copy field `k` (counter `sK`, consumed) of the header on `par` onto `dst`, using the empty
temporary `sT`. -/
def fetchProg (I : TB) (sK sT dst : TL) : TP I :=
  (tcd I sK (moveThru I sPar sT)).seq ((tcp I sPar dst).seq (moveAll I sT sPar))

theorem fetchProg_closed (I : TB) (sK sT dst : TL) : (fetchProg I sK sT dst).Closed :=
  ⟨tcd_closed I sK _ (moveThru_closed I _ _),
    ⟨callI_closed _ _ _ _, moveAll_closed I _ _⟩⟩

/-- Cost bound of `fetchProg` in terms of the header length. -/
def fetchCost (C H : ℕ) : ℕ := (C + 3) * (H + 2) ^ 2

section Fetch

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

/-- The countdown states of `fetchProg`: `j` fields left to move. -/
def fetchSt (B : TL → List Sym) (sK sT : TL) (hs : List ℕ) (k : ℕ) (rK rpar : List Sym)
    (j : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update B sK (natSyms j ++ rK)) sPar
    (hdrSyms (hs.drop (k - j)) ++ rpar)) sT (hdrSyms (hs.take (k - j))).reverse

/-- **Fetch a header field.** -/
theorem HT.fetch_spec (hI : I.Spec Mul C) (sK sT dst : TL) (hKP : sK ≠ sPar) (hTP : sT ≠ sPar)
    (hKT : sK ≠ sT) (hdK : dst ≠ sK) (hdT : dst ≠ sT) (hdP : dst ≠ sPar)
    (B : TL → List Sym) (hs : List ℕ) (k : ℕ) (hk : k < hs.length) (rK rpar : List Sym)
    (hrK : TermOK rK) (hK : B sK = natSyms k ++ rK) (hP : B sPar = hdrSyms hs ++ rpar)
    (hT : B sT = []) (ρ : List (TP I)) :
    HT ρ B (fetchProg I sK sT dst)
      (Function.update (Function.update B sK rK) dst (natSyms hs[k] ++ B dst))
      (fetchCost C (hdrSyms hs).length) := by
  set H := (hdrSyms hs).length with hH
  have hSt : ∀ j, fetchSt B sK sT hs k rK rpar j sK = natSyms j ++ rK := fun j => by
    simp [fetchSt, Function.update_of_ne hKP, Function.update_of_ne hKT]
  -- the loop
  have hloop := HT.tcd_spec hI sK rK hrK (fetchSt B sK sT hs k rK rpar) hSt (SubNLogN.Machine.Tables.moveThru I sPar sT) k
    (fun _ => 3 * H + 3) ρ (fun i hi => by
      have hi1 : k - (i + 1) < hs.length := by omega
      have hdrop : hs.drop (k - (i + 1)) = hs[k - (i + 1)] :: hs.drop (k - i) := by
        rw [List.drop_eq_getElem_cons hi1]
        congr 2
        omega
      have htake : hs.take (k - i) = hs.take (k - (i + 1)) ++ [hs[k - (i + 1)]] := by
        rw [show k - i = k - (i + 1) + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hi1]
        rfl
      have hpre : (Function.update (fetchSt B sK sT hs k rK rpar (i + 1)) sK (natSyms i ++ rK))
          sPar = natSyms hs[k - (i + 1)] ++ Sym.mark :: (hdrSyms (hs.drop (k - i)) ++ rpar) := by
        simp [fetchSt, Function.update_of_ne hKP.symm, Function.update_of_ne hTP.symm, hdrop,
          hdrSyms_cons]
      refine (HT.moveThru_spec sPar sT hTP.symm ρ _ _ (mark_not_mem_natSyms _) _ hpre).of_eq ?_ ?_
      · funext g
        by_cases hgT : g = sT
        · rw [hgT, Function.update_self]
          simp only [fetchSt, Function.update_of_ne hKT.symm, Function.update_self]
          rw [htake, hdrSyms_append, hdrSyms_cons, hdrSyms_nil, List.reverse_append]
          simp
        · by_cases hgP : g = sPar
          · rw [hgP, Function.update_of_ne hTP.symm, Function.update_self]
            simp only [fetchSt, Function.update_of_ne hTP.symm, Function.update_self]
          · by_cases hgK : g = sK
            · rw [hgK, Function.update_of_ne hKT, Function.update_of_ne hKP, Function.update_self]
              simp only [fetchSt, Function.update_of_ne hKT, Function.update_of_ne hKP,
                Function.update_self]
            · rw [Function.update_of_ne hgT, Function.update_of_ne hgP, Function.update_of_ne hgK]
              simp only [fetchSt, Function.update_of_ne hgT, Function.update_of_ne hgP,
                Function.update_of_ne hgK]
      · have h1 := bitLen_le_length_hdrSyms hi1
        rw [length_natSyms]
        omega)
  have hSk : fetchSt B sK sT hs k rK rpar k = B := by
    simp only [fetchSt, Nat.sub_self, List.drop_zero, List.take_zero, hdrSyms_nil,
      List.reverse_nil]
    rw [← hK, ← hP, ← hT, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  rw [hSk] at hloop
  -- copy the field, then move the prefix back
  have hdrop0 : hs.drop k = hs[k] :: hs.drop (k + 1) := List.drop_eq_getElem_cons hk
  have h0P : fetchSt B sK sT hs k rK rpar 0 sPar =
      natSyms hs[k] ++ Sym.mark :: (hdrSyms (hs.drop (k + 1)) ++ rpar) := by
    simp only [fetchSt, Function.update_of_ne hTP.symm, Function.update_self, Nat.sub_zero]
    rw [hdrop0, hdrSyms_cons]
    simp only [List.append_assoc, List.cons_append]
  have hcp := HT.tcp_spec hI sPar dst (by simp [hdP.symm]) (fetchSt B sK sT hs k rK rpar 0) hs[k]
    _ (termOK_mark _) h0P ρ
  set S1 := Function.update (fetchSt B sK sT hs k rK rpar 0) dst
    (natSyms hs[k] ++ fetchSt B sK sT hs k rK rpar 0 dst) with hS1
  have h1T : S1 sT = (hdrSyms (hs.take k)).reverse := by
    simp [hS1, fetchSt, Function.update_of_ne hdT.symm]
  have hmv := HT.moveAll_spec sT sPar hTP ρ _ S1 h1T
  refine (HT.seq hloop (HT.seq hcp hmv)).of_eq ?_ ?_
  · funext g
    by_cases hgP : g = sPar
    · rw [hgP, Function.update_self, Function.update_of_ne hdP.symm,
        Function.update_of_ne hKP.symm]
      have e1 : S1 sPar = hdrSyms (hs.drop k) ++ rpar := by
        simp only [hS1, fetchSt, Function.update_of_ne hdP.symm, Function.update_of_ne hTP.symm,
          Function.update_self, Nat.sub_zero]
      rw [e1, hP, List.reverse_reverse, ← List.append_assoc, ← hdrSyms_append,
        List.take_append_drop]
    · by_cases hgT : g = sT
      · rw [hgT, Function.update_of_ne hTP, Function.update_self, Function.update_of_ne hdT.symm,
          Function.update_of_ne hKT.symm, hT]
      · by_cases hgd : g = dst
        · rw [hgd, Function.update_of_ne hdP, Function.update_of_ne hdT, Function.update_self, hS1,
            Function.update_self]
          simp only [fetchSt, Function.update_of_ne hdP, Function.update_of_ne hdT,
            Function.update_of_ne hdK]
        · by_cases hgK : g = sK
          · rw [hgK, Function.update_of_ne hKP, Function.update_of_ne hKT,
              Function.update_of_ne hdK.symm, Function.update_self, hS1,
              Function.update_of_ne hdK.symm]
            simp only [fetchSt, Function.update_of_ne hKP, Function.update_of_ne hKT,
              Function.update_self, natSyms_zero, List.nil_append]
          · rw [Function.update_of_ne hgP, Function.update_of_ne hgT, Function.update_of_ne hgd,
              Function.update_of_ne hgK, hS1, Function.update_of_ne hgd]
            simp only [fetchSt, Function.update_of_ne hgP, Function.update_of_ne hgT,
              Function.update_of_ne hgK]
  · -- cost
    have hkH : k ≤ H := le_trans hk.le (length_le_length_hdrSyms hs)
    have hlc := loopCost_le_unif (fun i => C * (bitLen (i + 1) + 1) + (3 * H + 3) + C)
      (C * (H + 1) + (3 * H + 3) + C) k (fun i hi => by
        have : bitLen (i + 1) ≤ H := le_trans (bitLen_le_self _) (by omega)
        have : C * (bitLen (i + 1) + 1) ≤ C * (H + 1) := Nat.mul_le_mul_left _ (by omega)
        show C * (bitLen (i + 1) + 1) + (3 * H + 3) + C ≤ C * (H + 1) + (3 * H + 3) + C
        omega)
    have hb := bitLen_le_length_hdrSyms hk
    have hcpc : C * (bitLen hs[k] + 1) ≤ C * H := Nat.mul_le_mul_left _ (by omega)
    have hL : ((hdrSyms (hs.take k)).reverse).length ≤ H := by
      rw [List.length_reverse]; exact length_hdrSyms_take_le hs k
    have hkm : k * (C * (H + 1) + (3 * H + 3) + C + 1) ≤ H * (C * (H + 1) + (3 * H + 3) + C + 1) :=
      Nat.mul_le_mul_right _ hkH
    unfold fetchCost
    nlinarith

end Fetch

end SubNLogN.Machine.Tables
