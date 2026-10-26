/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Walsh
import SubNLogN.Machine.Walsh.LiftBase

/-!
# `SubNLogN.Machine.Walsh.LiftPure`: field-level facts for the lift / lower kernels (pure)

Paper: Lemma 5.3 (`lem:walsh-lift`) and
Proposition 5.5 (`prop:cnot-batch`, the exact lowering). The plan of the kernels is at the top of
`Walsh/LiftBase.lean`.

**Scope (honest summary).** Pure lemmas, all proved (no `sorry`):
* `twosBits_mul_two_pow`: `twosBits (w + δ) (a·2^δ) = replicate δ false ++ twosBits w a` (no
  hypothesis: both sides are bit patterns of residues);
* the field view of a record array (`fieldsOf`, `carrSyms_eq_fields`), of its lift
  (`carrSyms_liftC_eq`) and of the lowering (`fieldsOf_liftC_drop`);
* volumes: `cvol_eq_sum`, `cvol_mapC`, `cvol_le_cvol`.
-/

namespace SubNLogN.Machine.WalshLift

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## Lifting a two's-complement field -/

/-- **Exact lift of a field**: appending `δ` zero bits below a `w`-bit two's-complement field gives
the `(w + δ)`-bit field of `a·2^δ`. -/
theorem twosBits_mul_two_pow (w : ℕ) (a : ℤ) :
    ∀ δ : ℕ, twosBits (w + δ) (a * 2 ^ δ) = List.replicate δ false ++ twosBits w a
  | 0 => by simp
  | δ + 1 => by
    rw [← Nat.add_assoc, K1.twosBits_succ]
    have e : a * 2 ^ (δ + 1) = a * 2 ^ δ * 2 := by ring
    rw [e, Int.mul_emod_left, Int.mul_ediv_cancel _ (by norm_num), twosBits_mul_two_pow w a δ,
      List.replicate_succ, List.cons_append]
    simp

/-! ## The field view of a record array -/

/-- The two's-complement fields of a record: real then imaginary part of each coefficient. -/
def fieldsOf (w : ℕ) (cs : List CInt) : List (List Bool) :=
  cs.flatMap fun c => [twosBits w c.1, twosBits w c.2]

theorem crecBits_eq_flatten (w : ℕ) : ∀ cs : List CInt, crecBits w cs = (fieldsOf w cs).flatten
  | [] => rfl
  | c :: cs => by
    have ih := crecBits_eq_flatten w cs
    simp only [crecBits, fieldsOf, List.flatMap_cons, List.flatten_append, coefBits] at ih ⊢
    rw [ih]
    simp

theorem length_fieldsOf (w : ℕ) (cs : List CInt) : (fieldsOf w cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [fieldsOf, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    rw [ih]
    ring

theorem width_fieldsOf (w : ℕ) (cs : List CInt) : ∀ g ∈ fieldsOf w cs, g.length = w := by
  intro g hg
  simp only [fieldsOf, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hg
  obtain ⟨c, -, rfl | rfl⟩ := hg <;> exact K1.length_twosBits _ _

theorem carrSyms_eq_fields (w : ℕ) (v : List (List CInt)) :
    carrSyms w v = arrSyms ((v.map (fieldsOf w)).map List.flatten) := by
  rw [carrSyms, List.map_map]
  congr 1
  apply List.map_congr_left
  intro cs _
  exact crecBits_eq_flatten w cs

theorem fieldsOf_liftC (w δ : ℕ) (cs : List CInt) :
    fieldsOf (w + δ) (cs.map (liftC δ)) =
      (fieldsOf w cs).map fun g => List.replicate δ false ++ g := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [fieldsOf, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    simp [liftC, twosBits_mul_two_pow]

/-- The lifted array in the field view: every field gets `δ` zero bits in front (LSB side). -/
theorem carrSyms_liftC_eq (w δ : ℕ) (v : List (List CInt)) :
    carrSyms (w + δ) (mapC (liftC δ) v) =
      arrSyms ((v.map (fieldsOf w)).map fun fs =>
        (fs.map fun g => List.replicate δ false ++ g).flatten) := by
  rw [carrSyms_eq_fields, mapC, List.map_map, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro cs _
  simp only [Function.comp_apply, fieldsOf_liftC]

/-- Lowering the lifted fields gives back the fields. -/
theorem fieldsOf_liftC_drop (w δ : ℕ) (cs : List CInt) :
    (fieldsOf (w + δ) (cs.map (liftC δ))).map (List.drop δ) = fieldsOf w cs := by
  rw [fieldsOf_liftC, List.map_map]
  conv_rhs => rw [← List.map_id (fieldsOf w cs)]
  apply List.map_congr_left
  intro g _
  simp

theorem carrSyms_lower_eq (w δ : ℕ) (v : List (List CInt)) :
    carrSyms w v =
      arrSyms (((mapC (liftC δ) v).map (fieldsOf (w + δ))).map fun fs =>
        (fs.map (List.drop δ)).flatten) := by
  rw [carrSyms_eq_fields, mapC, List.map_map, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro cs _
  simp only [Function.comp_apply, fieldsOf_liftC_drop]

theorem carrSyms_liftC_fields (w δ : ℕ) (v : List (List CInt)) :
    carrSyms (w + δ) (mapC (liftC δ) v) =
      arrSyms (((mapC (liftC δ) v).map (fieldsOf (w + δ))).map List.flatten) :=
  carrSyms_eq_fields _ _

/-! ## Volumes -/

theorem length_crecBits (w : ℕ) (cs : List CInt) : (crecBits w cs).length = 2 * w * cs.length := by
  rw [crecBits_eq_flatten, List.length_flatten]
  have h : ∀ l : List (List Bool), (∀ g ∈ l, g.length = w) → (l.map List.length).sum = w * l.length
  · intro l hl
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [hl g List.mem_cons_self, ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))]
      ring
  rw [h _ (width_fieldsOf w cs), length_fieldsOf]
  ring

theorem cvol_eq_sum (w : ℕ) : ∀ v : List (List CInt),
    cvol w v = (v.map fun cs => 2 * w * cs.length + 1).sum
  | [] => rfl
  | cs :: v => by
    have ih := cvol_eq_sum w v
    simp only [cvol, carrSyms, List.map_cons, arrSyms_cons, List.length_append, recSyms,
      List.length_map, List.length_cons, List.length_nil, List.sum_cons] at ih ⊢
    rw [ih, length_crecBits]

theorem cvol_mapC (w δ : ℕ) (v : List (List CInt)) : cvol w (mapC (liftC δ) v) = cvol w v := by
  rw [cvol_eq_sum, cvol_eq_sum, mapC, List.map_map]
  congr 1
  apply List.map_congr_left
  intro cs _
  simp

theorem cvol_le_cvol (w δ : ℕ) (v : List (List CInt)) : cvol w v ≤ cvol (w + δ) v := by
  rw [cvol_eq_sum, cvol_eq_sum]
  induction v with
  | nil => simp
  | cons cs v ih =>
    simp only [List.map_cons, List.sum_cons]
    have : 2 * w * cs.length ≤ 2 * (w + δ) * cs.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end SubNLogN.Machine.WalshLift
