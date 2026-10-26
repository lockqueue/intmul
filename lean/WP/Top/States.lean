import WP.Top.Embed
import Contracts.W9.Tables

/-!
# WP.Top.States — the global states between the later stages

| after | state | how |
|---|---|---|
| tables (W7) | `tabOut n A B cSpec` | `WP.Top.Embed.afterTab_eq` |
| tape conversion | `convOut n A B cSpec`: `tr = tapeSyms cSpec` (W9's format) | `afterConv_eq` |
| parameter glue | `w9In n A B cSpec`: `c 0 = rootHdr n = hdrSyms [hB n, hK0 n, hK n, hK n]` | `WP.Top.Glue` |
| pipeline (W9) | `w9Out n A B cSpec v`: `oa = natSyms v`, `ob = []` | `afterW9_eq` |

`w9Out_len_le` bounds every stack of the final pipeline state, hence its total size
(`totalSize_w9Out_le`). The output stage clears that content.
-/

namespace WP.Top

open Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts

/-- State after the tape conversion: W9's tape on `tr`. -/
def convOut (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : GW → List Sym :=
  Function.update (prmState n A B) .tr (tapeSyms cSpec)

/-- W9's root header `hdrSyms [b, K0, k1, k2]` at the headline parameters. -/
def rootHdr (n : ℕ) : List Sym := hdrSyms [W8.hB n, W8.hK0 n, W8.hK n, W8.hK n]

/-- State after the parameter glue: the root header on `c 0`. -/
def w9In (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : GW → List Sym :=
  Function.update (convOut n A B cSpec) (.c 0) (rootHdr n)

/-- State after W9: the product `v` on `oa`, `ob` consumed. -/
def w9Out (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (v : ℕ) : GW → List Sym :=
  Function.update (Function.update (w9In n A B cSpec) .oa (natSyms v)) .ob []

/-! ## Stage postconditions as exact states -/

/-- **The converter's embedded postcondition is `convOut`.** -/
theorem afterConv_eq {m : ℕ} (hm : m ≤ 75) (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    {T : GW → List Sym}
    (h1 : ∀ l, T (ιc hm l) =
      Function.update (fun l => tabOut n A B cSpec (ιc hm l)) (.inl 0) (tapeSyms cSpec) l)
    (h2 : ∀ k, (∀ l, ιc hm l ≠ k) → T k = tabOut n A B cSpec k) :
    T = convOut n A B cSpec := by
  funext w
  unfold convOut
  by_cases hw : w = .tr
  · subst hw
    have h := h1 (.inl 0)
    rw [Function.update_self] at h
    rw [Function.update_self]
    exact h
  · rw [Function.update_of_ne hw]
    have hpre : tabOut n A B cSpec w = prmState n A B w := by
      unfold tabOut
      rw [Function.update_of_ne hw]
    rw [← hpre]
    by_cases hr : ∃ l, ιc hm l = w
    · obtain ⟨l, rfl⟩ := hr
      have hl : l ≠ .inl 0 := by
        rintro rfl
        exact hw rfl
      rw [h1, Function.update_of_ne hl]
    · push_neg at hr
      exact h2 _ hr

/-- **W9's embedded postcondition is `w9Out`.** -/
theorem afterW9_eq {m : ℕ} (hm : m ≤ 64) (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (v : ℕ) {T : GW → List Sym}
    (h1 : ∀ l, T (ι9 hm l) =
      Function.update (Function.update (fun l => w9In n A B cSpec (ι9 hm l)) (.inl .OA)
        (natSyms v ++ [])) (.inl .OB) [] l)
    (h2 : ∀ k, (∀ l, ι9 hm l ≠ k) → T k = w9In n A B cSpec k) :
    T = w9Out n A B cSpec v := by
  funext w
  unfold w9Out
  by_cases hb : w = .ob
  · subst hb
    have h := h1 (.inl .OB)
    rw [Function.update_self] at h
    rw [Function.update_self]
    exact h
  · rw [Function.update_of_ne hb]
    by_cases ha : w = .oa
    · subst ha
      have hne : (Sum.inl LB.OA : BLoc m) ≠ Sum.inl LB.OB := by simp
      have h := h1 (.inl .OA)
      rw [Function.update_of_ne hne, Function.update_self, List.append_nil] at h
      rw [Function.update_self]
      exact h
    · rw [Function.update_of_ne ha]
      by_cases hr : ∃ l, ι9 hm l = w
      · obtain ⟨l, rfl⟩ := hr
        have hlA : l ≠ .inl .OA := by
          rintro rfl
          exact ha rfl
        have hlB : l ≠ .inl .OB := by
          rintro rfl
          exact hb rfl
        rw [h1, Function.update_of_ne hlB, Function.update_of_ne hlA]
      · push_neg at hr
        exact h2 _ hr

/-! ## Contents of the pipeline's entry state -/

theorem w9In_oa (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    w9In n A B cSpec .oa = natSyms A := by
  simp [w9In, convOut, prmState]

theorem w9In_ob (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    w9In n A B cSpec .ob = natSyms B := by
  simp [w9In, convOut, prmState]

theorem w9In_c0 (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    w9In n A B cSpec (.c 0) = rootHdr n := by
  simp [w9In]

theorem w9In_w0 (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    w9In n A B cSpec (.w 0) = [] := by
  simp [w9In, convOut, prmState]

theorem w9In_tr (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    w9In n A B cSpec .tr = tapeSyms cSpec := by
  simp [w9In, convOut]

/-! ## Size of the final pipeline state -/

theorem length_hdrSyms (fs : List ℕ) : (hdrSyms fs).length = (fs.map fun v => bitLen v + 1).sum := by
  induction fs with
  | nil => rfl
  | cons x fs ih =>
    show ((natSyms x ++ [Sym.mark]) ++ hdrSyms fs).length = ((x :: fs).map fun v => bitLen v + 1).sum
    rw [List.length_append, List.length_append, ih, length_natSyms, List.map_cons, List.sum_cons,
      List.length_singleton]

/-- A bound on every stack of the final pipeline state. -/
def w9OutBound (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (v : ℕ) : ℕ :=
  bitLen v + (tapeSyms cSpec).length + (rootHdr n).length + bitLen n + bitLen (W8.hB n) +
    bitLen (W8.hK n) + bitLen (W8.hK0 n) + bitLen (W8.hL n) + bitLen (W8.hP0 n)

theorem w9Out_len_le (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (v : ℕ) (w : GW) :
    (w9Out n A B cSpec v w).length ≤ w9OutBound n cSpec v := by
  unfold w9Out w9In convOut w9OutBound
  by_cases hb : w = .ob
  · subst hb
    simp
  · rw [Function.update_of_ne hb]
    by_cases ha : w = .oa
    · subst ha
      simp only [Function.update_self, length_natSyms]
      omega
    · rw [Function.update_of_ne ha]
      by_cases hc : w = .c 0
      · subst hc
        simp only [Function.update_self]
        omega
      · rw [Function.update_of_ne hc]
        by_cases ht : w = .tr
        · subst ht
          simp only [Function.update_self]
          omega
        · rw [Function.update_of_ne ht]
          cases w <;> simp_all [prmState, length_natSyms] <;> omega

theorem totalSize_w9Out_le (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (v : ℕ) :
    totalSize (w9Out n A B cSpec v) ≤ 76 * w9OutBound n cSpec v := by
  have h := totalSize_le_of_forall (w9Out_len_le n A B cSpec v)
  rwa [length_allGW] at h

#assert_std_axioms afterConv_eq afterW9_eq w9In_oa w9In_ob w9In_c0 w9In_w0 w9In_tr length_hdrSyms
  w9Out_len_le totalSize_w9Out_le

end WP.Top
