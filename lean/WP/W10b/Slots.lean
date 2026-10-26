import Contracts.W9.Pipeline
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W10b.Slots — W9's cost bounds as a list of cost slots

`W9_multiply`'s cost is `C·(rootBound + pipeBound F + pipeBound I + |tape| + 1)`. Every W9 bound is
affine in the multiplication cost `Mul`, so it splits into a linear part (the bound at `mul0 = 0`) plus
`count·Mul width` terms. A **slot** is one such `(lin, count, width)` triple:
* each step level gives one linear slot and three multiplication slots: PRE twists (`8·M·N` products
  at the level width), PRE spread (`2·M·t1·nb` Kronecker products of width `(W+1)(s+w)`), POST columns
  (`8·M·N` products of width `8(H+1)`);
* the leaf gives one linear slot and `K+1` slots of `4·M·2^K` products at the leaf width (one per
  butterfly stage). Splitting the leaf is what keeps `count·width ≤ A·n` per slot (W10b analysis).

`specSlots wd spec p_in ℓ M` builds the slots from the **schedule** `spec : QuantizedFastDFTSpec`, and
`pipeBound_eq_slots` proves that for any faithful table hierarchy `cSpec` the W9 bound equals the slot
cost exactly: `pipeBound Mul wd cSpec p_in ℓ M = slotsCost Mul (specSlots wd spec p_in ℓ M)`.
-/

namespace WP.W10b

open TMFw.Contracts TMFw.Contracts.W9 IntMul

/-- One cost slot: `lin` linear work plus `cnt` multiplications of declared width `wid`. -/
structure Slot where
  lin : ℕ
  cnt : ℕ
  wid : ℕ

/-- Cost of a slot at multiplication cost `Mul`. -/
def Slot.cost (Mul : ℕ → ℕ) (s : Slot) : ℕ := s.lin + s.cnt * Mul s.wid

/-- Total cost of a slot list. -/
def slotsCost (Mul : ℕ → ℕ) (l : List Slot) : ℕ := (l.map (Slot.cost Mul)).sum

/-- The zero multiplication cost: a W9 bound at `mul0` is its linear part. -/
def mul0 : ℕ → ℕ := fun _ => 0

theorem slotsCost_nil (Mul : ℕ → ℕ) : slotsCost Mul [] = 0 := rfl

theorem slotsCost_cons (Mul : ℕ → ℕ) (s : Slot) (l : List Slot) :
    slotsCost Mul (s :: l) = s.cost Mul + slotsCost Mul l := by
  simp [slotsCost]

theorem slotsCost_append (Mul : ℕ → ℕ) (l₁ l₂ : List Slot) :
    slotsCost Mul (l₁ ++ l₂) = slotsCost Mul l₁ + slotsCost Mul l₂ := by
  simp [slotsCost, List.sum_append]

theorem slotsCost_replicate (Mul : ℕ → ℕ) (k : ℕ) (s : Slot) :
    slotsCost Mul (List.replicate k s) = k * s.cost Mul := by
  induction k with
  | zero => simp [slotsCost]
  | succ k ih =>
    rw [List.replicate_succ, slotsCost_cons, ih]
    ring

/-! ## Splitting the W9 bounds into linear part and multiplications -/

theorem preNodeBound_split (Mul : ℕ → ℕ) (w : ℕ) (h : PreHdr) :
    preNodeBound Mul w h = preNodeBound mul0 w h +
      2 * h.t1 * h.nb * Mul ((h.W + 1) * (h.s + w)) + 8 * h.N * Mul w := by
  simp only [preNodeBound, spreadBound, spreadRowBound, twistBound, mul0]
  ring

theorem postNodeBound_split (Mul : ℕ → ℕ) (w : ℕ) (h : PostHdr) :
    postNodeBound Mul w h = postNodeBound mul0 w h + 8 * (h.t1 * h.r) * Mul (8 * (h.H + 1)) := by
  simp only [postNodeBound, columnBound, mul0]
  ring

theorem leafNodeBound_split (Mul : ℕ → ℕ) (w p_in p K : ℕ) :
    leafNodeBound Mul w p_in p K = leafNodeBound mul0 w p_in p K + 4 * (K + 1) * 2 ^ K * Mul w := by
  simp only [leafNodeBound, mul0]
  ring

theorem rootBound_split (Mul : ℕ → ℕ) (wR b K0 k1 k2 : ℕ) :
    rootBound Mul wR b K0 k1 k2 = rootBound mul0 wR b K0 k1 k2 + 4 * 2 ^ K0 * Mul wR := by
  simp only [rootBound, mul0]
  ring

theorem preLevelBound_split (Mul : ℕ → ℕ) (w w' : ℕ) (h : PreHdr) (M : ℕ) :
    preLevelBound Mul w w' h M = preLevelBound mul0 w w' h M +
      M * (2 * h.t1 * h.nb) * Mul ((h.W + 1) * (h.s + w)) + M * (8 * h.N) * Mul w := by
  simp only [preLevelBound]
  rw [preNodeBound_split Mul w h]
  ring

theorem postLevelBound_split (Mul : ℕ → ℕ) (w w' : ℕ) (h : PostHdr) (M : ℕ) :
    postLevelBound Mul w w' h M = postLevelBound mul0 w w' h M +
      M * (8 * (h.t1 * h.r)) * Mul (8 * (h.H + 1)) := by
  simp only [postLevelBound]
  rw [postNodeBound_split Mul w h]
  ring

theorem leafLevelBound_split (Mul : ℕ → ℕ) (w p_in p K M : ℕ) :
    leafLevelBound Mul w p_in p K M = leafLevelBound mul0 w p_in p K M +
      (K + 1) * (M * (4 * 2 ^ K) * Mul w) := by
  simp only [leafLevelBound]
  rw [leafNodeBound_split Mul w p_in p K]
  ring

/-! ## Slots of a schedule -/

/-- PRE header of the schedule step `(p, K, t1, r)` at input precision `p_in` (FTP:88:
`pSub = m1 = 2·pChild p K`). -/
def preHdrQ (p K t1 r p_in : ℕ) : PreHdr := ⟨p_in, 2 * pChild p K, 2 * pChild p K, t1, r⟩

/-- POST header of the schedule step `(p, K, t1, r)` with child precision `cp`. -/
def postHdrQ (p K t1 r cp : ℕ) : PostHdr := ⟨p, 2 * pChild p K, t1, r, cp⟩

/-- The linear slot of a step level. -/
def stepLin (wd : ℕ → ℕ) (p K t1 r cp p_in ℓ M : ℕ) : ℕ :=
  preLevelBound mul0 (wd ℓ) (wd (ℓ + 1)) (preHdrQ p K t1 r p_in) M +
    postLevelBound mul0 (wd ℓ) (wd (ℓ + 1)) (postHdrQ p K t1 r cp) M + 2

/-- The linear slot of the leaf level. -/
def leafLin (wd : ℕ → ℕ) (p K p_in ℓ M : ℕ) : ℕ := leafLevelBound mul0 (wd ℓ) p_in p K M + 1

/-- **Slots of a schedule** (the shape of `pipeBound`, read off the schedule tree). -/
def specSlots (wd : ℕ → ℕ) : QuantizedFastDFTSpec → ℕ → ℕ → ℕ → List Slot
  | .base p R, p_in, ℓ, M =>
      ⟨leafLin wd p (Nat.log2 R) p_in ℓ M, 0, 0⟩ ::
        List.replicate (Nat.log2 R + 1) ⟨0, M * (4 * 2 ^ Nat.log2 R), wd ℓ⟩
  | .step p K t1 r _ _ child, p_in, ℓ, M =>
      ⟨stepLin wd p K t1 r child.p p_in ℓ M, 0, 0⟩ ::
        ⟨0, M * (8 * (preHdrQ p K t1 r p_in).N), wd ℓ⟩ ::
        ⟨0, M * (2 * (preHdrQ p K t1 r p_in).t1 * (preHdrQ p K t1 r p_in).nb),
          ((preHdrQ p K t1 r p_in).W + 1) * ((preHdrQ p K t1 r p_in).s + wd ℓ)⟩ ::
        ⟨0, M * (8 * ((postHdrQ p K t1 r child.p).t1 * (postHdrQ p K t1 r child.p).r)),
          8 * ((postHdrQ p K t1 r child.p).H + 1)⟩ ::
        specSlots wd child (2 * pChild p K) (ℓ + 1) (M * t1)

/-- **The W9 pipeline bound is the slot cost** of the schedule, for every faithful hierarchy. -/
theorem pipeBound_eq_slots (Mul : ℕ → ℕ) (wd : ℕ → ℕ) {cSpec : ComputablePaperFastDFTSpec}
    {spec : QuantizedFastDFTSpec} (hf : TablesFaithful cSpec spec) :
    ∀ p_in ℓ M, pipeBound Mul wd cSpec p_in ℓ M = slotsCost Mul (specSlots wd spec p_in ℓ M) := by
  induction hf with
  | base p K tw _ _ _ =>
    intro p_in ℓ M
    simp only [pipeBound, specSlots, Nat.log2_two_pow, slotsCost_cons, slotsCost_replicate,
      Slot.cost, leafLin]
    rw [leafLevelBound_split Mul (wd ℓ) p_in p K M]
    ring
  | step p K t1 r _ _ _ _ _ _ _ cChild child _ _ _ _ _ hChild ih =>
    intro p_in ℓ M
    have hp : cChild.p = child.p := hChild.p_eq
    simp only [pipeBound]
    rw [preLevelBound_split, postLevelBound_split, ih, hp]
    simp only [specSlots, slotsCost_cons, Slot.cost, stepLin, preHdrQ, postHdrQ]
    ring

/-! ## Scaling by the contract constant -/

/-- `C·slotsCost Mul l` is at most the slot sum with linear parts scaled by `C` and every product
charged `C·Mul w + C` (the shape of W10's `mulCost C Mul`). -/
theorem const_mul_slotsCost_le (C : ℕ) (Mul : ℕ → ℕ) :
    ∀ l : List Slot,
      C * slotsCost Mul l ≤ (l.map fun s => C * s.lin + s.cnt * (C * Mul s.wid + C)).sum
  | [] => by simp [slotsCost]
  | s :: l => by
    have ih := const_mul_slotsCost_le C Mul l
    rw [slotsCost_cons, List.map_cons, List.sum_cons]
    have h1 : C * s.cost Mul ≤ C * s.lin + s.cnt * (C * Mul s.wid + C) := by
      unfold Slot.cost
      have e : C * (s.lin + s.cnt * Mul s.wid) = C * s.lin + s.cnt * (C * Mul s.wid) := by ring
      rw [e]
      have : s.cnt * (C * Mul s.wid) ≤ s.cnt * (C * Mul s.wid + C) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      omega
    rw [Nat.mul_add]
    omega

/-- Sums over `List.range l.length` of `getD` values are sums over the list. -/
theorem sum_range_getD {α : Type} (f : α → ℕ) (d : α) :
    ∀ l : List α, ((List.range l.length).map fun i => f (l.getD i d)).sum = (l.map f).sum
  | [] => by simp
  | x :: xs => by
    have ih := sum_range_getD f d xs
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.map_cons, List.sum_cons]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]

#assert_std_axioms slotsCost_nil slotsCost_cons slotsCost_append slotsCost_replicate
  preNodeBound_split postNodeBound_split leafNodeBound_split rootBound_split preLevelBound_split
  postLevelBound_split leafLevelBound_split pipeBound_eq_slots const_mul_slotsCost_le sum_range_getD

end WP.W10b
