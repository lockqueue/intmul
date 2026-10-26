import WP.W9s.CombLoop

/-!
# WP.W9s.Combine — one combine: `Y0` on `sA`, `Y1` on `sD` ↦ `combL Δ Y0 Y1` on `sA`

The counter `sV` starts at `r` (a copy of the unary `r` on `sUR`). The row loop leaves the plus
rows reversed on `sOP` and the minus rows reversed on `sOM`; moving `sOM` then `sOP` back onto
`sA` gives `blkR (plus ++ minus)` (`combL_eq_halfL`).
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

def combine (K : Kit) : MProg K :=
  .seq (pushS sOP symG) <| .seq (pushS sOM symG) <| .seq (pushS sV symG) <|
  .seq (uCopy (lS K) sUR sV sUR') <|
  .seq (whileTop (lS K) sD (notS symBlk) (combStep K)) <|
  .seq (popS sD) <| .seq (popS sV) <|
  .seq (rwP K sOM sA symG) (rwP K sOP sA symG)

theorem combine_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) : (combine K).Closed :=
  ⟨trivial, trivial, trivial, uCopy_closed _ _ _ _, whileTop_closed _ _ _ (combStep_closed hH),
    trivial, trivial, rwP_closed _ _ _ _, rwP_closed _ _ _ _⟩

theorem halfL_eq_range (neg : Bool) (Δ : ℕ) : ∀ (Y0 Y1 : List (List (ℤ × ℤ))) (s : ℕ),
    Y0.length = Y1.length →
    halfL neg Δ s Y0 Y1 = (List.range Y0.length).map (fun u =>
      zipB neg (s + Δ * u) (Y0.getD u []) (rotL (s + Δ * u) (Y1.getD u [])))
  | [], [], _, _ => by simp [halfL]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, f :: fs, s, h => by
    have ih := halfL_eq_range neg Δ as fs (s + Δ) (by simpa using h)
    rw [halfL, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    all_goals first
      | rfl
      | (apply List.map_congr_left
         intro u _
         simp only [Function.comp, List.getD_cons_succ]
         rw [show s + Δ * (u + 1) = s + Δ + Δ * u by ring])

theorem combL_eq_halfL (Δ : ℕ) (Y0 Y1 : List (List (ℤ × ℤ))) (h : Y0.length = Y1.length) :
    combL Δ Y0 Y1 = halfL false Δ 0 Y0 Y1 ++ halfL true Δ 0 Y0 Y1 := by
  rw [halfL_eq_range false Δ Y0 Y1 0 h, halfL_eq_range true Δ Y0 Y1 0 h]
  simp only [zero_add]
  rfl

theorem mem_blkR {X : List (List (ℤ × ℤ))} {x : Sym} (h : x ∈ blkR X) :
    isTag x = false ∨ x = symRow := by
  obtain ⟨row, -, hrow⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hrow with h1 | h1
  · exact Or.inl (notTag_es row x h1)
  · exact Or.inr (List.mem_singleton.mp h1)

theorem symG_not_mem_rev_blkR (X : List (List (ℤ × ℤ))) : symG ∉ (blkR X).reverse := by
  intro h
  rcases mem_blkR (List.mem_reverse.mp h) with h1 | h1
  · exact Bool.false_ne_true h1.symm
  · cases h1

theorem zipB_length (neg : Bool) : ∀ (s : ℕ) (as gs : List (ℤ × ℤ)), as.length = gs.length →
    (zipB neg s as gs).length = as.length
  | _, [], [], _ => by simp [zipB]
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | 0, a :: as, g :: gs, h => by simp [zipB, zipB_length neg 0 as gs (by simpa using h)]
  | s + 1, a :: as, g :: gs, h => by simp [zipB, zipB_length neg s as gs (by simpa using h)]

theorem zipB_width (neg : Bool) {w : ℕ} : ∀ (s : ℕ) (as gs : List (ℤ × ℤ)),
    (∀ z ∈ as, EntryW w z) → (∀ z ∈ gs, EntryW w z) → ∀ z ∈ zipB neg s as gs, EntryW (w + 1) z
  | _, [], _, _, _ => by simp [zipB]
  | _, _ :: _, [], _, _ => by simp [zipB]
  | 0, a :: as, g :: gs, ha, hg => by
    intro z hz
    simp only [zipB, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rw [bfly_eq_bflyE]
      exact entryW_bflyE _ (ha a (List.mem_cons_self ..)) (hg g (List.mem_cons_self ..))
    · exact zipB_width neg 0 as gs (fun z h => ha z (List.mem_cons_of_mem _ h))
        (fun z h => hg z (List.mem_cons_of_mem _ h)) z hz
  | s + 1, a :: as, g :: gs, ha, hg => by
    intro z hz
    simp only [zipB, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rw [bfly_eq_bflyE]
      exact entryW_bflyE _ (ha a (List.mem_cons_self ..)) (hg g (List.mem_cons_self ..))
    · exact zipB_width neg s as gs (fun z h => ha z (List.mem_cons_of_mem _ h))
        (fun z h => hg z (List.mem_cons_of_mem _ h)) z hz

theorem halfL_rows (neg : Bool) (Δ r w : ℕ) : ∀ (s : ℕ) (as fs : List (List (ℤ × ℤ))),
    (∀ row ∈ as, row.length = r) → (∀ row ∈ fs, row.length = r) →
    (∀ row ∈ as, ∀ z ∈ row, EntryW w z) → (∀ row ∈ fs, ∀ z ∈ row, EntryW w z) →
    ∀ row ∈ halfL neg Δ s as fs, row.length = r ∧ ∀ z ∈ row, EntryW (w + 1) z
  | _, [], _, _, _, _, _ => by simp [halfL]
  | _, _ :: _, [], _, _, _, _ => by simp [halfL]
  | s, a :: as, f :: fs, hra, hrf, hwa, hwf => by
    intro row hrow
    simp only [halfL, List.mem_cons] at hrow
    rcases hrow with rfl | hrow
    · have ha := hra a (List.mem_cons_self ..)
      have hf := hrf f (List.mem_cons_self ..)
      refine ⟨by rw [zipB_length _ _ _ _ (by rw [rotL_length, ha, hf])]; exact ha, ?_⟩
      exact zipB_width _ _ _ _ (hwa a (List.mem_cons_self ..))
        (fun z hz => hwf f (List.mem_cons_self ..) z (mem_rotL hz))
    · exact halfL_rows neg Δ r w (s + Δ) as fs (fun x h => hra x (List.mem_cons_of_mem _ h))
        (fun x h => hrf x (List.mem_cons_of_mem _ h)) (fun x h => hwa x (List.mem_cons_of_mem _ h))
        (fun x h => hwf x (List.mem_cons_of_mem _ h)) row hrow

theorem halfL_length (neg : Bool) (Δ : ℕ) : ∀ (s : ℕ) (as fs : List (List (ℤ × ℤ))),
    as.length = fs.length → (halfL neg Δ s as fs).length = as.length
  | _, [], [], _ => by simp [halfL]
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | s, a :: as, f :: fs, h => by
    simp [halfL, halfL_length neg Δ (s + Δ) as fs (by simpa using h)]

theorem length_blkR_le (w r : ℕ) : ∀ X : List (List (ℤ × ℤ)),
    (∀ row ∈ X, row.length = r ∧ ∀ z ∈ row, EntryW w z) →
    (blkR X).length ≤ X.length * (r * eb w + 1)
  | [], _ => by simp [blkR]
  | row :: X, h => by
    have h1 := h row (List.mem_cons_self ..)
    have e1 := length_es_le w row h1.2
    rw [h1.1] at e1
    have e2 := length_blkR_le w r X (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [blkR_cons, List.length_append, rowE, List.length_append, List.length_singleton,
      List.length_cons, Nat.succ_mul]
    omega

#assert_std_axioms combine_closed halfL_eq_range combL_eq_halfL mem_blkR symG_not_mem_rev_blkR
  zipB_length zipB_width halfL_rows halfL_length length_blkR_le

end WP.W9s
