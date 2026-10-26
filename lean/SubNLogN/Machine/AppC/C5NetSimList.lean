/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Net
import SubNLogN.Math.Networks.LayoutEncoding2

/-!
# Proposition A.7 network simulation, part 1: list lemmas (`AppC/C5NetSimList.lean`)

Pure list facts used to simulate the pure-network Proposition A.7 node (`interchangeProc`) by the list-level machine schedule
(`NodeCorrect`, `AppC/C5Core.lean`):
* `roleBlocks_restrict`: a permutation of the records of the role-`k` rows by a row-local index map
  `f` changes only role `k`'s list, and that list by `permByInv f`;
* row-locality of the machine-level stream maps (`streamMap_rowLocal`) and of the child interchange
  (`swapFieldsInv_rowLocal`);
* `permByInv`, `roleBlocks` and `mergeBlocks` commute with `List.map` (record encodings).
Helpers are in `SubNLogN.Machine.C5.NetAux`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks.Model.LayoutEncodingAux (roleIdxMap roleIdxMap_eq')

/-- The machine-layer `roleBlocks` coincides verbatim with the pure-network definition. -/
theorem roleBlocks_eq_model {α : Type} (W w s : ℕ) (v : List α) :
    SubNLogN.Machine.roleBlocks W w s v = SubNLogN.Math.Networks.Model.roleBlocks W w s v := rfl

/-- The machine-layer `permByInv` coincides verbatim with the pure-network definition. -/
theorem permByInv_eq_model {α : Type} [Inhabited α] (g : ℕ → ℕ) (v : List α) :
    SubNLogN.Machine.permByInv g v = SubNLogN.Math.Networks.Model.permByInv g v := rfl

/-- The machine-layer `mergeBlocks` coincides verbatim with the pure-network definition. -/
theorem mergeBlocks_eq_model {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g s : ℕ)
    (us : Fin W → List α) :
    SubNLogN.Machine.mergeBlocks W ord g s us =
      SubNLogN.Math.Networks.Model.mergeBlocks W ord g s us := rfl

/-- Every list is the map of its `getD` over its index range. -/
theorem list_eq_map_range {α : Type} (v : List α) (d : α) :
    v = (List.range v.length).map fun y => v.getD y d := by
  apply List.ext_getElem
  · simp
  · intro y h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h1]

/-- `permByInv` of a list given as a map over its index range. -/
theorem permByInv_map_range {α : Type} [Inhabited α] (g : ℕ → ℕ) (F : ℕ → α) (n : ℕ)
    (hg : ∀ y < n, g y < n) :
    permByInv g ((List.range n).map F) = (List.range n).map fun y => F (g y) := by
  unfold permByInv
  rw [List.length_map, List.length_range]
  refine List.map_congr_left fun y hy => ?_
  rw [List.mem_range] at hy
  rw [List.getD_eq_getElem _ _ (by simpa using hg y hy)]
  simp

/-- **Role-local permutations.** Rows of `S` records, role of a row = row index mod `W` (`W ∣ N`
rows). Permuting the records of the role-`k` rows by a row-local index map `f` changes only role
`k`'s list, and that by `permByInv f`. -/
theorem roleBlocks_restrict {α : Type} [Inhabited α] (N S W : ℕ) (hW : 0 < W) (hWN : W ∣ N)
    (v : List α) (hv : v.length = N * S) (f : ℕ → ℕ)
    (hf : ∀ t l, l < S → f (t * S + l) = t * S + f l) (hfS : ∀ l < S, f l < S)
    (k r : ℕ) (hk : k < W) (hr : r < W) :
    roleBlocks W r S (permByInv (fun y => if y / S % W = k then f y else y) v) =
      if r = k then permByInv f (roleBlocks W r S v) else roleBlocks W r S v := by
  obtain ⟨N', rfl⟩ := hWN
  rcases Nat.eq_zero_or_pos S with hS0 | hSpos
  · subst hS0
    have hnil : v = [] := List.eq_nil_of_length_eq_zero (by rw [hv]; ring)
    subst hnil
    split_ifs <;> rfl
  have hdecomp : ∀ y, y / S * S + y % S = y := fun y => by
    rw [Nat.mul_comm]; exact Nat.div_add_mod y S
  have hfy : ∀ y, f y = y / S * S + f (y % S) := fun y => by
    conv_lhs => rw [← hdecomp y]
    exact hf (y / S) (y % S) (Nat.mod_lt _ hSpos)
  have hfrow : ∀ n, S ∣ n → ∀ y < n, f y < n := by
    intro n hn y hy
    obtain ⟨c, rfl⟩ := hn
    rw [hfy y]
    have h2 := hfS _ (Nat.mod_lt y hSpos)
    have h3 : y / S < c := by rw [Nat.div_lt_iff_lt_mul hSpos, Nat.mul_comm]; exact hy
    calc y / S * S + f (y % S) < y / S * S + S := by omega
      _ = (y / S + 1) * S := by ring
      _ ≤ c * S := Nat.mul_le_mul_right S h3
      _ = S * c := Nat.mul_comm _ _
  have hn : 1 * (W * N') * S = v.length := by rw [hv]; ring
  have hg : ∀ y < 1 * (W * N') * S, (fun y => if y / S % W = k then f y else y) y <
      1 * (W * N') * S := by
    intro y hy
    simp only
    split_ifs
    · exact hfrow _ ⟨1 * (W * N'), by ring⟩ y hy
    · exact hy
  have hv' : v = (List.range (1 * (W * N') * S)).map (fun y => v.getD y default) := by
    rw [hn]; exact list_eq_map_range v default
  have hrm := fun (F : ℕ → α) (r' : ℕ) (hr' : r' < W) =>
    SubNLogN.Math.Networks.Model.LayoutEncodingAux.roleBlocks_map_range F 1 (W * N') S W r' hW
      (Dvd.intro N' rfl) hr'
  have hN' : W * N' / W = N' := Nat.mul_div_cancel_left N' hW
  have hΦ : ∀ r' y, y < 1 * N' * S →
      roleIdxMap (W * N') S W r' y = (y / S * W + r') * S + y % S := by
    intro r' y _
    rw [Nat.mul_comm W N']
    conv_lhs => rw [← hdecomp y]
    exact roleIdxMap_eq' N' S W r' (y / S) (y % S) (Nat.mod_lt _ hSpos) hW
  have hΦrole : ∀ r' y, r' < W → y < 1 * N' * S → roleIdxMap (W * N') S W r' y / S % W = r' := by
    intro r' y hr' hy
    rw [hΦ r' y hy, Nat.add_comm, Nat.add_mul_div_right _ _ hSpos,
      Nat.div_eq_of_lt (Nat.mod_lt _ hSpos), zero_add, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hr']
  rw [hv', permByInv_map_range _ _ _ hg, roleBlocks_eq_model, hrm _ r hr, hN']
  split_ifs with hrk
  · subst hrk
    rw [roleBlocks_eq_model, hrm _ r hr, hN', permByInv_map_range]
    · refine List.map_congr_left fun y hy => ?_
      rw [List.mem_range] at hy
      have hfy' : f y < 1 * N' * S := hfrow _ ⟨1 * N', by ring⟩ y hy
      rw [if_pos (hΦrole r y hr hy), hΦ r (f y) hfy', hΦ r y hy, hfy ((y / S * W + r) * S + y % S),
        hfy y]
      have e1 : ((y / S * W + r) * S + y % S) / S = y / S * W + r := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hSpos, Nat.div_eq_of_lt (Nat.mod_lt _ hSpos),
          zero_add]
      have e2 : ((y / S * W + r) * S + y % S) % S = y % S := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.mod_lt _ hSpos)]
      have e3 : (y / S * S + f (y % S)) / S = y / S := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hSpos,
          Nat.div_eq_of_lt (hfS _ (Nat.mod_lt _ hSpos)), zero_add]
      have e4 : (y / S * S + f (y % S)) % S = f (y % S) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hfS _ (Nat.mod_lt _ hSpos))]
      rw [e1, e2, e3, e4]
    · intro y hy
      exact hfrow _ ⟨1 * N', by ring⟩ y hy
  · rw [roleBlocks_eq_model, hrm _ r hr, hN']
    refine List.map_congr_left fun y hy => ?_
    rw [List.mem_range] at hy
    rw [if_neg (by rw [hΦrole r y hr hy]; exact hrk)]

/-! ## Row-locality of the index maps -/

/-- Replacing a digit at place `P` (radix `Qd`) commutes with adding a multiple of `S`
(`P · Qd ∣ S`). -/
theorem digit_rowLocal {P Qd S : ℕ} (hdvd : P * Qd ∣ S) (t l v : ℕ) :
    (t * S + l) / P % Qd = l / P % Qd ∧
      (t * S + l) - (t * S + l) / P % Qd * P + v * P = t * S + (l - l / P % Qd * P + v * P) := by
  rcases Nat.eq_zero_or_pos P with hP | hP
  · subst hP
    simp
  obtain ⟨c, rfl⟩ := hdvd
  have e1 : (t * (P * Qd * c) + l) / P % Qd = l / P % Qd := by
    rw [show t * (P * Qd * c) + l = l + P * (Qd * (t * c)) by ring, Nat.add_mul_div_left _ _ hP,
      Nat.add_mul_mod_self_left]
  refine ⟨e1, ?_⟩
  rw [e1]
  have h1 : l / P % Qd * P ≤ l := by
    calc l / P % Qd * P ≤ l / P * P := Nat.mul_le_mul_right P (Nat.mod_le _ _)
      _ ≤ l := Nat.div_mul_le_self l P
  omega

/-- The machine-level stream maps are row-local (`S = rowSize`). -/
theorem streamMap_rowLocal (q m : ℕ) (op : StreamOp m) (k N1 G B : ℕ) (t l : ℕ) :
    streamMap q m op k N1 G B (t * rowSize q m k N1 G B + l) =
      t * rowSize q m k N1 G B + streamMap q m op k N1 G B l := by
  set Qe := q ^ m ^ k
  have hS : rowSize q m k N1 G B = N1 * Qe * G * Qe * B := rfl
  have hD : B * Qe ∣ rowSize q m k N1 G B := ⟨N1 * Qe * G, by rw [hS]; ring⟩
  have hH : B * Qe * G * Qe ∣ rowSize q m k N1 G B := ⟨N1, by rw [hS]; ring⟩
  have hDv : ∀ y, dvalOf Qe B (t * rowSize q m k N1 G B + y) = dvalOf Qe B y := fun y =>
    (digit_rowLocal hD t y 0).1
  have hHv : ∀ y, hvalOf Qe G B (t * rowSize q m k N1 G B + y) = hvalOf Qe G B y := fun y =>
    (digit_rowLocal hH t y 0).1
  have hDs : ∀ y v, setDOf Qe B (t * rowSize q m k N1 G B + y) v =
      t * rowSize q m k N1 G B + setDOf Qe B y v := fun y v => (digit_rowLocal hD t y v).2
  have hHs : ∀ y v, setHOf Qe G B (t * rowSize q m k N1 G B + y) v =
      t * rowSize q m k N1 G B + setHOf Qe G B y v := fun y v => (digit_rowLocal hH t y v).2
  have hCv : ∀ X y, chunkVal Qe G B X (t * rowSize q m k N1 G B + y) = chunkVal Qe G B X y := by
    intro X y
    cases X
    · exact hHv y
    · exact hDv y
  have hCs : ∀ X y v, setChunk Qe G B X (t * rowSize q m k N1 G B + y) v =
      t * rowSize q m k N1 G B + setChunk Qe G B X y v := by
    intro X y v
    cases X
    · exact hHs y v
    · exact hDs y v
  cases op with
  | unit X i r =>
    simp only [streamMap]
    rw [hCv, hCs]
  | lowShift X i c =>
    simp only [streamMap]
    rw [hCv, hCs]
  | hdShift i j neg =>
    simp only [streamMap]
    rw [hDv, hHv, hDs]

/-- The field interchange is row-local for rows of `S` records, `B · Hh · G · Hd ∣ S`. -/
theorem swapFieldsInv_rowLocal (Hh G Hd B S : ℕ) (hdvd : B * Hh * G * Hd ∣ S) (t l : ℕ) :
    swapFieldsInv Hh G Hd B (t * S + l) = t * S + swapFieldsInv Hh G Hd B l := by
  rcases Nat.eq_zero_or_pos (B * Hh * G * Hd) with hP | hP
  · rw [hP, zero_dvd_iff] at hdvd
    subst hdvd
    simp
  obtain ⟨c, rfl⟩ := hdvd
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · simp [h] at hP
    · exact h
  have e0 : (t * (B * Hh * G * Hd * c) + l) / (B * Hh * G * Hd) =
      t * c + l / (B * Hh * G * Hd) := by
    rw [show t * (B * Hh * G * Hd * c) + l = l + B * Hh * G * Hd * (t * c) by ring,
      Nat.add_mul_div_left _ _ hP, Nat.add_comm]
  have e1 := (digit_rowLocal (P := B) (Qd := Hh) (S := B * Hh * G * Hd * c)
    ⟨G * Hd * c, by ring⟩ t l 0).1
  have e2 := (digit_rowLocal (P := B * Hh) (Qd := G) (S := B * Hh * G * Hd * c)
    ⟨Hd * c, by ring⟩ t l 0).1
  have e3 := (digit_rowLocal (P := B * Hh * G) (Qd := Hd) (S := B * Hh * G * Hd * c)
    ⟨c, by ring⟩ t l 0).1
  have e4 : (t * (B * Hh * G * Hd * c) + l) % B = l % B := by
    rw [show t * (B * Hh * G * Hd * c) + l = l + B * (Hh * G * Hd * c * t) by ring,
      Nat.add_mul_mod_self_left]
  unfold swapFieldsInv
  rw [e0, e1, e2, e3, e4]
  ring

/-! ## Commuting with record encodings -/

theorem permByInv_map {α γ : Type} [Inhabited α] [Inhabited γ] (g : ℕ → ℕ) (h : α → γ)
    (l : List α) (hg : ∀ y < l.length, g y < l.length) :
    permByInv g (l.map h) = (permByInv g l).map h := by
  unfold permByInv
  rw [List.length_map, List.map_map]
  refine List.map_congr_left fun y hy => ?_
  rw [List.mem_range] at hy
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by simpa using hg y hy),
    List.getD_eq_getElem _ _ (hg y hy)]
  simp

theorem roleBlocks_map {α γ : Type} (W r S : ℕ) (h : α → γ) (l : List α) :
    roleBlocks W r S (l.map h) = (roleBlocks W r S l).map h := by
  unfold roleBlocks
  rw [List.length_map, List.map_filterMap]
  refine List.filterMap_congr fun x hx => ?_
  rw [List.mem_range] at hx
  split_ifs <;> simp [hx]

theorem mergeBlocks_map {α γ : Type} (W : ℕ) (ord : Fin W → Fin W) (g S : ℕ) (h : α → γ)
    (us : Fin W → List α) :
    mergeBlocks W ord g S (fun c => (us c).map h) = (mergeBlocks W ord g S us).map h := by
  unfold mergeBlocks
  simp only [List.map_flatMap, List.map_take, List.map_drop]

end SubNLogN.Machine.C5.NetAux
