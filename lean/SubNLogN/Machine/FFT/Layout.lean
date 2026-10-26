/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.Kit
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Math.Walsh.Proofs.LayoutPerm
import IntMulTM.SpecFacts

/-!
# K4.3 (`Machine/FFT/Layout.lean`): the positional maps `L` and `U` of the direct FFT

**Scope (honest summary).** `layoutExec_of_posPerm` proves `LayoutExecStmt Band lam' sel`
(`Contracts/FFT.lean`, parts (ii) and (iv) of Theorem 6.5, Lemma 6.3) from two hypotheses:
* `PositionalPermMachineStmt Band lam'` (Theorem 5.8, `Contracts/Walsh.lean`; reduced by K3-PERM);
* `LayoutCompileStmt sel` (stated here): the compiler that reads the header `midHdr q ℓ K w a` and
  writes the runtime descriptors of Theorem 5.8, the header `permHdr q (D+1) (2^ℓ) w K m₀` and the
  map `permSyms (layoutMap sel ℓ K a)`, within `C·((w + m₀ + 1)^J + |midHdr|)` steps (Lemma 6.3,
  `lem:walsh-layout`: "`L` and `U` are compiled in time polynomial in `q`"). The
  runtime tables use the closed forms `layoutLList`, `layoutUList` of
  `Math/Walsh/IntForms/Address.lean` (`ofFn_layoutL`, `ofFn_layoutU`).
The value-level fact used is `walsh_layout_perm` (`L`, `B` bijective and
`U = (L ∘ B)^{-1}`, so `layoutMap sel` is a permutation). No `sorry`.

## Plan (program design, invariants, cost accounting)
* **Layout.** Named stacks `Fin 3` (`0` the cube array, in place; `1` the header `midHdr`,
  restored; `2` untouched). Private stacks `Unit ⊕ (Unit ⊕ (E_G ⊕ E_P))`: `layHdr` receives the
  descriptor header, `layMap` the map; the two blocks are the compiler's and the positional
  permutation's scratch. The compiler is embedded by `genEmb` (its stack `0` ↦ the header, `1` ↦
  `layHdr`, `2` ↦ `layMap`), the positional permutation by `ppEmb` (`0` ↦ the array, `1` ↦
  `layHdr`, `2` ↦ `layMap`), both through `callInj`; registers `Bool × (R_G × R_P)`.
* **Program.** Compile header/map descriptors, run the positional permutation, drain `layHdr`/`layMap`.
* **Invariant.** All private stacks are empty on entry (`KClean`). After the compiler, `layHdr`
  and `layMap` hold exactly the two descriptors; the positional permutation replaces the array by
  `posPermArr π z` with `π = layoutMap sel ℓ K a` as an `Equiv.Perm`; the drains empty the two
  descriptor stacks again, so the final stacks are exactly those of `LayoutExecStmt`.
* **Cost.** `|permHdr| ≤ 8(w + m₀ + 1)`, `|permSyms π| ≤ (w + m₀ + 1)^2` and
  `2^{m₀}(w + m₀ + 1)^J ≤ permCost lam' J …` give the bound with `J = J_P + J_G + 2` and
  `C = C_G + 9 C_P + 24` (`layoutCost_bound`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Machine.FFTKit

/-! ## 1. The compile leaf -/

/-- **[CONTRACT] K4.3a, compiling a positional map of the direct FFT** (Lemma 6.3, `lem:walsh-layout`:
"Both `L` and `U` are compiled in time polynomial in `q`").
* Named stacks (`Fin 3`): `0` the header `midHdr q ℓ K w a` (restored); `1` receives the header
  `permHdr q (D+1) (2^ℓ) w K m₀` of Theorem 5.8 and `2` receives the map
  `permSyms (layoutMap sel ℓ K a) = hdrSyms [π 0, …, π (m₀-1)]` (move convention), each pushed on
  the previous content of its stack.
* Hypotheses: `MidShapeOK q ℓ K w a`.
* Cost `C·((w + m₀ + 1)^J + |midHdr|)`: polynomial in the header, and every header field read is
  paid. The closed forms `layoutLList` / `layoutUList` (`Math/Walsh/IntForms/Address.lean`,
  `ofFn_layoutL`, `ofFn_layoutU`) are the intended runtime tables. -/
def LayoutCompileStmt (sel : LayoutSel) : Prop :=
  ∃ J : ℕ, KContract (Fin 3) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest phrest prest : List Sym)
      (S : KLoc (Fin 3) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest → S (.inl 1) = phrest → S (.inl 2) = prest →
      Runs Pr S
        (Function.update (Function.update S (.inl 1)
            (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) ++ phrest))
          (.inl 2) (permSyms (layoutMap sel ℓ K a) ++ prest))
        (fun _ => True) (C * ((w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

namespace FFT.LayoutAux

/-! ## 2. Value level: the selected map is a permutation -/

theorem layoutMap_bijective (sel : LayoutSel) {D : ℕ} {ℓ K : ℕ} {a : Fin D → ℕ} (hK1 : 1 ≤ K)
    (hKℓ : K ≤ ℓ - 1) (hℓ : 2 ≤ ℓ) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    Function.Bijective (layoutMap sel ℓ K a) := by
  obtain ⟨hL, -, hUL, hLU⟩ := walsh_layout_perm ℓ K a hK1 hKℓ hℓ ha
  cases sel with
  | L => exact hL
  | U =>
    exact Function.bijective_iff_has_inverse.2
      ⟨fun p => layoutL ℓ K a (bitRevB a p), hLU, hUL⟩

/-- `D ≤ m₀` (every record axis has at least one bit). -/
theorem le_addrBits {D ℓ : ℕ} {a : Fin D → ℕ} (hℓ : 2 ≤ ℓ) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    D ≤ addrBits a := by
  rw [LayoutPermAux.addrBits_eq ℓ a (by omega) ha]
  have : D ≤ D * (ℓ - 1) := Nat.le_mul_of_pos_right D (by omega)
  omega

/-! ## 3. Descriptor lengths and the cost bound -/

theorem bitLen_eq_size (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen_eq_size]
  exact Nat.size_le.2 (Nat.lt_two_pow_self)

theorem bitLen_two_pow_le (ℓ : ℕ) : bitLen (2 ^ ℓ) ≤ ℓ + 1 := by
  rw [bitLen_eq_size]
  exact Nat.size_le.2 (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self ℓ))

theorem length_hdrSyms (fs : List ℕ) : (hdrSyms fs).length = (fs.map bitLen).sum + fs.length := by
  induction fs with
  | nil => simp [hdrSyms]
  | cons f fs ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_cons, List.length_nil, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem length_permHdr_le {q ℓ K w D m : ℕ} (hq : q ≤ w) (hℓ : ℓ ≤ w) (hK : K ≤ w)
    (hD : D ≤ m) : (permHdr q (D + 1) (2 ^ ℓ) w K m).length ≤ 8 * (w + m + 1) := by
  rw [permHdr, length_hdrSyms]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  have h1 := bitLen_le_self q
  have h2 := bitLen_le_self (D + 1)
  have h3 := bitLen_two_pow_le ℓ
  have h4 := bitLen_le_self w
  have h5 := bitLen_le_self K
  have h6 := bitLen_le_self m
  omega

theorem length_permSyms_le {m : ℕ} (π : Fin m → Fin m) (w : ℕ) :
    (permSyms π).length ≤ (w + m + 1) ^ 2 := by
  rw [permSyms, length_hdrSyms, List.length_ofFn]
  have hs : ((List.ofFn fun p => (π p : ℕ)).map bitLen).sum ≤ m * m := by
    have h := List.sum_le_card_nsmul ((List.ofFn fun p => (π p : ℕ)).map bitLen) m
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hy
        exact (bitLen_le_self _).trans (π p).isLt.le)
    simpa [List.length_ofFn, smul_eq_mul] using h
  have e : (w + m + 1) ^ 2 = (w + m + 1) * (w + m + 1) := by ring
  rw [e]
  nlinarith

theorem pow_le_permCost (lam' : ℝ) (J d r w K m : ℕ) :
    (w + m + 1) ^ J ≤ permCost lam' J d r w K m := by
  unfold permCost
  have h1 : (w + m + 1) ^ J ≤ 2 ^ m * (w + m + 1) ^ J :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos m)
  have h2 : 2 ^ m * (w + m + 1) ^ J ≤
      cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) + 2 ^ m * (w + m + 1) ^ J :=
    Nat.le_add_left _ _
  have h3 := Nat.le_mul_of_pos_left
    (cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) + 2 ^ m * (w + m + 1) ^ J)
    (show 0 < m / d + K + 1 from Nat.succ_pos _)
  omega

theorem permCost_mono (lam' : ℝ) {J J' : ℕ} (h : J ≤ J') (d r w K m : ℕ) :
    permCost lam' J d r w K m ≤ permCost lam' J' d r w K m := by
  unfold permCost
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h)

/-- **The parts' costs sum to at most a constant times the layout's bound**: the compiler, the
positional permutation (with its header `Lh ≤ 8(w + m₀ + 1)`), and the two drains
(`2 Lh + 3`, `2 Lm + 3`, `Lm = |permSyms π| ≤ (w + m₀ + 1)^2`). -/
theorem layoutCost_bound (lam' : ℝ) {JP JG CP CG D ℓ K w m H Lh Lm : ℕ}
    (hLh : Lh ≤ 8 * (w + m + 1)) (hLm : Lm ≤ (w + m + 1) ^ 2) :
    CG * ((w + m + 1) ^ JG + H) +
        (CP * (permCost lam' JP (D + 1) (2 ^ ℓ) w K m + Lh) + ((2 * Lh + 3) + (2 * Lm + 3))) ≤
      (CG + 9 * CP + 24) * (permCost lam' (JP + JG + 2) (D + 1) (2 ^ ℓ) w K m + H) := by
  set X := permCost lam' (JP + JG + 2) (D + 1) (2 ^ ℓ) w K m with hX
  have hB1 : 1 ≤ w + m + 1 := by omega
  have hBX : (w + m + 1) ^ (JP + JG + 2) ≤ X := pow_le_permCost lam' _ _ _ _ _ _
  have hG : (w + m + 1) ^ JG ≤ X :=
    (Nat.pow_le_pow_right hB1 (by omega)).trans hBX
  have h2X : (w + m + 1) ^ 2 ≤ X := (Nat.pow_le_pow_right hB1 (by omega)).trans hBX
  have h1X : w + m + 1 ≤ X := by
    have : w + m + 1 ≤ (w + m + 1) ^ 2 := by nlinarith
    omega
  have hP : permCost lam' JP (D + 1) (2 ^ ℓ) w K m ≤ X := permCost_mono lam' (by omega) _ _ _ _ _
  have e1 : CG * ((w + m + 1) ^ JG + H) ≤ CG * (X + H) := Nat.mul_le_mul_left _ (by omega)
  have e2 : CP * (permCost lam' JP (D + 1) (2 ^ ℓ) w K m + Lh) ≤ CP * (9 * X) :=
    Nat.mul_le_mul_left _ (by omega)
  have e3 : (2 * Lh + 3) + (2 * Lm + 3) ≤ 24 * X := by omega
  have e4 : (CG + 9 * CP + 24) * (X + H) =
      CG * (X + H) + CP * (9 * X) + 24 * X + (9 * CP * H + 24 * H) := by ring
  omega

end FFT.LayoutAux

namespace FFT.LayoutAux

/-! ## 4. The composite program -/

section Composite

variable {EG EP RG RP : Type}

/-- Private stacks of the layout kernel: the descriptor header, the map, then the compiler's and
the positional permutation's scratch blocks. -/
abbrev LayE (EG EP : Type) : Type := Unit ⊕ (Unit ⊕ (EG ⊕ EP))

/-- The private descriptor-header stack. -/
abbrev layHdr : KLoc (Fin 3) (LayE EG EP) := .inr (.inl ())

/-- The private map stack. -/
abbrev layMap : KLoc (Fin 3) (LayE EG EP) := .inr (.inr (.inl ()))

/-- Embedding of the compiler (named stacks: header source, descriptor header, map). -/
def genEmb : KLoc (Fin 3) EG → KLoc (Fin 3) (LayE EG EP)
  | .inl i => if (i : ℕ) = 0 then .inl 1 else if (i : ℕ) = 1 then layHdr else layMap
  | .inr e => .inr (.inr (.inr (.inl e)))

/-- Embedding of the positional permutation (named stacks: array, descriptor header, map). -/
def ppEmb : KLoc (Fin 3) EP → KLoc (Fin 3) (LayE EG EP)
  | .inl i => if (i : ℕ) = 0 then .inl 0 else if (i : ℕ) = 1 then layHdr else layMap
  | .inr e => .inr (.inr (.inr (.inr e)))

@[simp] theorem genEmb_0 : (genEmb (EG := EG) (EP := EP) (.inl 0)) = .inl 1 := by simp [genEmb]
@[simp] theorem genEmb_1 : (genEmb (EG := EG) (EP := EP) (.inl 1)) = layHdr := by simp [genEmb]
@[simp] theorem genEmb_2 : (genEmb (EG := EG) (EP := EP) (.inl 2)) = layMap := by simp [genEmb]
@[simp] theorem genEmb_inr (e : EG) : (genEmb (EP := EP) (.inr e)) = .inr (.inr (.inr (.inl e))) :=
  rfl
@[simp] theorem ppEmb_0 : (ppEmb (EG := EG) (EP := EP) (.inl 0)) = .inl 0 := by simp [ppEmb]
@[simp] theorem ppEmb_1 : (ppEmb (EG := EG) (EP := EP) (.inl 1)) = layHdr := by simp [ppEmb]
@[simp] theorem ppEmb_2 : (ppEmb (EG := EG) (EP := EP) (.inl 2)) = layMap := by simp [ppEmb]
@[simp] theorem ppEmb_inr (e : EP) : (ppEmb (EG := EG) (.inr e)) = .inr (.inr (.inr (.inr e))) :=
  rfl

theorem genEmb_injective : Function.Injective (genEmb (EG := EG) (EP := EP)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [genEmb]
  · fin_cases i <;> simp [genEmb] at h
  · fin_cases i' <;> simp [genEmb] at h
  · simp only [genEmb, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem ppEmb_injective : Function.Injective (ppEmb (EG := EG) (EP := EP)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [ppEmb]
  · fin_cases i <;> simp [ppEmb] at h
  · fin_cases i' <;> simp [ppEmb] at h
  · simp only [ppEmb, Sum.inr.injEq] at h
    rw [h]

/-- Register lenses: the drain flag, the compiler, the positional permutation. -/
def lnsB : Lens (Bool × (RG × RP)) Bool := Lens.fst _ _
def lnsG : Lens (Bool × (RG × RP)) RG := (Lens.snd _ _).comp (Lens.fst _ _)
def lnsP : Lens (Bool × (RG × RP)) RP := (Lens.snd _ _).comp (Lens.snd _ _)

/-- **The layout program**: compile the descriptors; run the positional permutation; drain the
two descriptor stacks. -/
def layProg (PG : Prog (KLoc (Fin 3) EG) (fun _ => Sym) RG)
    (PP : Prog (KLoc (Fin 3) EP) (fun _ => Sym) RP) :
    Prog (KLoc (Fin 3) (LayE EG EP)) (fun _ => Sym) (Bool × (RG × RP)) :=
  .seq (callInj genEmb lnsG PG) (.seq (callInj ppEmb lnsP PP)
    (.seq (callInj id lnsB (drainProg layHdr)) (callInj id lnsB (drainProg layMap))))

theorem closed_layProg {PG : Prog (KLoc (Fin 3) EG) (fun _ => Sym) RG}
    {PP : Prog (KLoc (Fin 3) EP) (fun _ => Sym) RP} (hG : PG.Closed) (hP : PP.Closed) :
    (layProg PG PP).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ hG) (WP.W9comp.closed_seq (closed_callInj _ _ hP)
    (WP.W9comp.closed_seq (closed_callInj _ _ (closed_drainProg _))
      (closed_callInj _ _ (closed_drainProg _))))

end Composite

end FFT.LayoutAux

open FFT.LayoutAux

/-! ## 5. The reduction -/

/-- **K4.3, the positional maps `L` and `U` of the direct FFT** (stages (ii) and (iv) of
Theorem 6.5, `thm:direct-fft`; Lemma 6.3, `lem:walsh-layout`). The compiled descriptors (`LayoutCompileStmt`) drive the
positional-permutation machine (Theorem 5.8, `PositionalPermMachineStmt`); the private descriptor
stacks are emptied afterwards. The selected map `layoutMap sel ℓ K a` is a permutation by
proved `walsh_layout_perm`. -/
theorem layoutExec_of_posPerm {Band : LayerRT → Prop} {lam' : ℝ} (sel : LayoutSel)
    (hPP : PositionalPermMachineStmt Band lam') (hC : LayoutCompileStmt sel) :
    LayoutExecStmt Band lam' sel := by
  obtain ⟨JP, CP, hP⟩ := hPP
  obtain ⟨JG, CG, hG⟩ := hC
  obtain ⟨EP, iFP, iDP, RP, PP, iRP, iNP, hcP, hsP⟩ := hP ()
  obtain ⟨EG, iFG, iDG, RG, PG, iRG, iNG, hcG, hsG⟩ := hG ()
  let iFP₁ : Fintype EP := iFP
  let iDP₁ : DecidableEq EP := iDP
  let iFG₁ : Fintype EG := iFG
  let iDG₁ : DecidableEq EG := iDG
  have iRP₁ : Finite RP := iRP
  have iNP₁ : Nonempty RP := iNP
  have iRG₁ : Finite RG := iRG
  have iNG₁ : Nonempty RG := iNG
  refine ⟨JP + JG + 2, CG + 9 * CP + 24, fun _ => ?_⟩
  refine ⟨LayE EG EP, inferInstance, inferInstance, Bool × (RG × RP), layProg PG PP,
    inferInstance, inferInstance, closed_layProg hcG hcP, ?_⟩
  intro q ℓ K w D a z rest hrest S hcl hshape hband hz hrestT h0 h1
  let hinst : DecidableEq (KLoc (Fin 3) (LayE EG EP)) := inferInstance
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hshape' := hshape
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hshape'
  have hDm : D ≤ addrBits a := le_addrBits hℓ2 ha
  -- the permutation
  let π : Equiv.Perm (Fin (addrBits a)) :=
    Equiv.ofBijective _ (layoutMap_bijective sel hK1 hKℓ hℓ2 ha)
  have hπ : (π : Fin (addrBits a) → Fin (addrBits a)) = layoutMap sel ℓ K a := rfl
  -- the intermediate stacks
  obtain ⟨S1, hS1⟩ : ∃ S', S' = Function.update (Function.update S layHdr
      (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a))) layMap (permSyms (layoutMap sel ℓ K a)) :=
    ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S', S' = Function.update S1 (.inl 0)
      (carrSyms w (encCube q (posPermArr π z)) ++ rest) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S', S' = Function.update S2 layHdr [] := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ S', S' = Function.update S3 layMap [] := ⟨_, rfl⟩
  -- step 1: compile the descriptors
  have hr1 : Runs (callInj genEmb (@lnsG RG RP) PG) S S1 (fun _ => True)
      (CG * ((w + addrBits a + 1) ^ JG + (midHdr q ℓ K w a).length)) := by
    have hP1 := hsG q ℓ K w D a hrest [] [] (S ∘ genEmb) (fun e => hcl' _) hshape
      (by simpa using h1) (by simp [hcl']) (by simp [hcl'])
    refine runs_callInj genEmb_injective (@lnsG RG RP) (WP.W9comp.runs_congr hP1 ?_) ?_
    · funext k
      rcases k with i | e
      · fin_cases i <;> simp [hS1, genEmb]
      · simp [hS1]
    · intro k hk
      have h1' := hk (.inl 1)
      have h2' := hk (.inl 2)
      simp only [genEmb_1, genEmb_2] at h1' h2'
      rw [hS1, Function.update_of_ne (Ne.symm h2'), Function.update_of_ne (Ne.symm h1')]
  -- step 2: the positional permutation
  have hr2 : Runs (callInj ppEmb (@lnsP RG RP) PP) S1 S2 (fun _ => True)
      (CP * (permCost lam' JP (D + 1) (2 ^ ℓ) w K (addrBits a) +
        (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a)).length)) := by
    have hP2 := hsP q (D + 1) (2 ^ ℓ) w K (addrBits a) π z rest [] [] (S1 ∘ ppEmb)
      (fun e => by simp [hS1, hcl']) (by omega) hK1 (by omega) (by omega) (by omega) hband hz
      hrestT (by simp [hS1, h0]) (by simp [hS1]) (by simp [hS1, hπ])
    have h := runs_callInj_update ppEmb_injective (@lnsP RG RP) hP2
    rw [ppEmb_0] at h
    rw [hS2]
    exact h
  -- steps 3 and 4: empty the descriptor stacks
  have hr3 : Runs (callInj id (@lnsB RG RP) (drainProg layHdr)) S2 S3 (fun _ => True)
      (2 * (S2 layHdr).length + 3) := by
    rw [hS3]
    exact runs_callInj_update (ι := id) Function.injective_id (@lnsB RG RP)
      (runs_drainProg layHdr (S2 ∘ id))
  have hr4 : Runs (callInj id (@lnsB RG RP) (drainProg layMap)) S3 S4 (fun _ => True)
      (2 * (S3 layMap).length + 3) := by
    rw [hS4]
    exact runs_callInj_update (ι := id) Function.injective_id (@lnsB RG RP)
      (runs_drainProg layMap (S3 ∘ id))
  have hall := WP.W9comp.runs_seq hr1 (WP.W9comp.runs_seq hr2 (WP.W9comp.runs_seq hr3 hr4))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · -- the final stacks
    rw [hS4, hS3, hS2, hS1, hπ]
    funext k
    by_cases hk0 : k = .inl 0
    · subst hk0
      simp
    · by_cases hkH : k = layHdr
      · subst hkH
        simp [hcl']
      · by_cases hkM : k = layMap
        · subst hkM
          simp [hcl']
        · simp [hk0, hkH, hkM]
  · -- the cost
    have hS2H : S2 layHdr = permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) := by
      rw [hS2, hS1]; simp
    have hS3M : S3 layMap = permSyms (layoutMap sel ℓ K a) := by
      rw [hS3, hS2, hS1]; simp
    rw [hS2H, hS3M]
    exact layoutCost_bound lam'
      (length_permHdr_le (by omega) (by omega) (by omega) hDm)
      (length_permSyms_le _ w)

end SubNLogN.Machine
