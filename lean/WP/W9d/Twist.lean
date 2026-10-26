import WP.W9d.Kernel
import WP.W9d.CostPure

/-!
# WP.W9d.Twist — the generic twist contract

`twist_holds`: for any instance bundle `J` (one constant `D`), any shift setup `stp` that maps the
counter `pSub` to `sf pSub` (with `sf p ≤ 2p + 2`, cost `≤ D·(2|p| + 4)`), and any matrix value
`val` whose rows are `zipWith (twistF (sf pSub)) twRow` of the input rows, the kernel
`(kernel J stp).mapStk ιB` meets the twist contract shape of `Contracts.W9.Pre` with the constant
`17·D + 150`. `W9_preTwist` and `W9_postTwist` are the instances `val = w9P` and `val = w9QPost`.

The host `TwL` is embedded into layout B by `ιB`: named stacks `W0, TR, TL, C0`, scratch to scratch
(`m = 10 ≤ w9Scratch`).
-/

namespace WP.W9d

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## The host inside layout B -/

/-- Named host stacks in layout B. -/
def ιn (i : Fin 4) : LB :=
  match i.val with
  | 0 => .W0
  | 1 => .TR
  | 2 => .TL
  | _ => .C0

/-- The host embedding. -/
def ιB : TwL → BLoc 10 := Sum.map ιn id

theorem ιn_inj : Function.Injective ιn := by decide

theorem ιB_inj : Function.Injective ιB := by
  rintro (i | j) (i' | j') h
  · simp only [ιB, Sum.map_inl, Sum.inl.injEq] at h
    rw [ιn_inj h]
  · simp [ιB] at h
  · simp [ιB] at h
  · simp only [ιB, Sum.map_inr, Sum.inr.injEq, id] at h
    rw [h]

/-- A host triple gives the contract's `Runs` for the embedded program. -/
theorem runs_embed {R : Type} (P : Prog TwL (fun _ => Sym) R) (σ σ' : BLoc 10 → List Sym)
    (T : ℕ) (h : HT [] (σ ∘ ιB) P (σ' ∘ ιB) T) (hout : ∀ k, (∀ l, ιB l ≠ k) → σ' k = σ k) :
    Runs (P.mapStk ιB) σ σ' (fun _ => True) T := by
  have h2 := Runs.embed ιB_inj (HT.runs h) σ (fun _ => rfl)
  refine Triple.post h2 (fun s hs => ⟨?_, trivial⟩)
  obtain ⟨h1, h3, -⟩ := hs
  funext k
  by_cases hk : ∃ l, ιB l = k
  · obtain ⟨l, rfl⟩ := hk
    exact h1 l
  · push_neg at hk
    rw [h3 k hk, hout k hk]

theorem length_flatten_const {α : Type} (r : ℕ) :
    ∀ L : List (List α), (∀ l ∈ L, l.length = r) → L.flatten.length = L.length * r
  | [], _ => by simp
  | l :: L, h => by
    rw [List.flatten_cons, List.length_append, h l (List.mem_cons_self ..),
      length_flatten_const r L (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')), List.length_cons]
    ring

theorem hdrSyms_cons (n : ℕ) (L : List ℕ) : hdrSyms (n :: L) = natSyms n ++ Sym.mark :: hdrSyms L := by
  simp [hdrSyms]

theorem hdrLen_ge (h : PreHdr) : bitLen h.pSub + 3 ≤ h.hdrLen := by
  unfold PreHdr.hdrLen preTapeFields
  rw [hdrSyms_cons, List.length_append, List.length_cons, length_natSyms]
  omega

/-! ## The generic contract -/

theorem twist_holds {Mul : ℕ → ℕ} (J : TwInst) (D : ℕ) (hJ : J.Spec Mul D)
    (stp : Prog TwL (fun _ => Sym) J.Reg) (hstpC : stp.Closed) (sf Tf : ℕ → ℕ)
    (hsf : ∀ p, sf p ≤ 2 * p + 2) (hTf : ∀ p, Tf p ≤ D * (2 * bitLen p + 4))
    (hstp : ∀ (p : ℕ) (B : TwL → List Sym) (rk : List Sym), TermOK rk →
      B sK = natSyms p ++ rk → HT [] B stp (Function.update B sK (natSyms (sf p) ++ rk)) (Tf p))
    (val : ℕ → ℕ → ℕ → Array (ℤ × ℤ) → Array (Array (ℤ × ℤ)) → Array (Array (ℤ × ℤ)))
    (hval : ∀ pSub t1 r tw U, (val pSub t1 r tw U).toList.map Array.toList =
      (inRows t1 r U).map (List.zipWith (twistF (sf pSub)) (twRow r tw))) :
    BContract Unit w9Scratch fun _ m _ C P =>
      ∀ (h : PreHdr) (w : ℕ) (tw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ)))
        (σ : BLoc m → List Sym) (restT : List Sym),
        PreDims h → PreCtx h σ → U.size = h.t1 → (∀ row ∈ U.toList, row.size = h.r) →
        MatW w U → TwW w h.r tw → MatW w (val h.pSub h.t1 h.r tw U) →
        σ (.inl .W0) = matSyms U → σ (.inl .TR) = twSyms h.r tw ++ restT →
        Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
              (matSyms (val h.pSub h.t1 h.r tw U)))
            (.inl .TR) restT) (.inl .TL) ((twSyms h.r tw).reverse ++ σ (.inl .TL)))
          (fun _ => True) (C * twistBound Mul w h) := by
  refine ⟨17 * D + 150, fun _ => ⟨10, J.Reg, (kernel J stp).mapStk ιB, by decide,
    J.reg_finite, J.reg_nonempty, freeBelow_mapStk ιB _ 0 (kernel_closed J stp hstpC), ?_⟩⟩
  intro h w tw U σ restT hD hC hUs hUr hUw htw hVw hW0 hTR
  obtain ⟨ht1, hr1, -, -⟩ := hD
  obtain ⟨⟨r0, hr0⟩, -⟩ := hC
  have hrpos : 0 < h.r := by rw [hr1]; positivity
  have ht1pos : 0 < h.t1 := by rw [ht1]; positivity
  have hlt : (twRow h.r tw).length = h.r := length_twRow h.r tw
  have hlr : (inRows h.t1 h.r U).length = h.t1 := length_inRows h.t1 h.r U
  have hlen : ∀ row ∈ inRows h.t1 h.r U, row.length = (twRow h.r tw).length := fun row hrow => by
    rw [length_of_mem_inRows hrow, hlt]
  have hrow := inRows_width hUs hUr hUw
  have htw' := twRow_width htw
  have hvalr := hval h.pSub h.t1 h.r tw U
  have hout : ∀ row ∈ inRows h.t1 h.r U, ∀ z ∈ List.zipWith (twistF (sf h.pSub)) (twRow h.r tw) row,
      EntryW w z := by
    intro row hrow' z hz
    have hmem : List.zipWith (twistF (sf h.pSub)) (twRow h.r tw) row ∈
        (val h.pSub h.t1 h.r tw U).toList.map Array.toList := by
      rw [hvalr]
      exact List.mem_map_of_mem hrow'
    obtain ⟨a, ha, hae⟩ := List.mem_map.mp hmem
    exact hVw a ha z (by rw [hae]; exact hz)
  have hW0' : (σ ∘ ιB) W0 = blkE (inRows h.t1 h.r U).flatten := by
    show σ (.inl .W0) = _
    rw [hW0, matSyms_inRows _ _ U hUs hUr]
  have hTR' : (σ ∘ ιB) TR = blkE (twRow h.r tw) ++ symSub :: restT := by
    show σ (.inl .TR) = _
    rw [hTR, twSyms_eq, List.append_assoc]
    rfl
  have hC0' : (σ ∘ ιB) C0 = natSyms h.pSub ++ Sym.mark ::
      (hdrSyms [h.m1, h.t1, h.r, IntMul.natLog2Fuel h.t1 h.t1, IntMul.natLog2Fuel h.r h.r,
        IntMul.effectiveFilterWidth h.m1 h.r, IntMul.kroneckerSpreadNumBlocks h.m1 h.r,
        strideOf h.pSub] ++ r0) := by
    show σ (.inl .C0) = _
    rw [hr0]
    unfold preTapeFields
    rw [hdrSyms_cons, List.append_assoc, List.cons_append]
  have hk := kernel_spec hJ stp h.pSub (sf h.pSub) (Tf h.pSub) (hstp h.pSub) w
    (inRows h.t1 h.r U) (twRow h.r tw) (by omega) hlen hrow htw' hout (σ ∘ ιB) restT _ hW0' hTR'
    hC0'
  have hmv : matSyms (val h.pSub h.t1 h.r tw U) =
      blkE ((inRows h.t1 h.r U).map (List.zipWith (twistF (sf h.pSub)) (twRow h.r tw))).flatten := by
    unfold matSyms
    rw [List.flatMap_def, hvalr]
  refine runs_embed _ σ _ _ (hk.of_eq ?_ ?_) ?_
  · funext l
    rcases l with i | j
    · fin_cases i <;> simp [ιB, ιn, hmv, twSyms_eq]
    · simp [ιB]
  · -- cost
    have htb : (blkE (twRow h.r tw)).length ≤ h.r * (2 * w + 4) := by
      have := length_blkE_le w _ htw'
      rw [hlt] at this
      exact this
    have hob : (blkE ((inRows h.t1 h.r U).map
        (List.zipWith (twistF (sf h.pSub)) (twRow h.r tw))).flatten).length ≤
        h.t1 * h.r * (2 * w + 4) := by
      have hw : ∀ z ∈ ((inRows h.t1 h.r U).map
          (List.zipWith (twistF (sf h.pSub)) (twRow h.r tw))).flatten, EntryW w z := by
        intro z hz
        obtain ⟨row', hrow', hz'⟩ := List.mem_flatten.mp hz
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hrow'
        exact hout row hrow z hz'
      have hl := length_flatten_const h.r ((inRows h.t1 h.r U).map
        (List.zipWith (twistF (sf h.pSub)) (twRow h.r tw))) (by
          intro l hl
          obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hl
          rw [List.length_zipWith, hlt, length_of_mem_inRows hrow, Nat.min_self])
      have := length_blkE_le w _ hw
      rw [hl, List.length_map, hlr] at this
      exact this
    have hc := twist_cost_le Mul D w h.pSub (sf h.pSub) (Tf h.pSub) h.t1 h.r _ _ h.hdrLen
      (hsf _) (hTf _) ht1pos hrpos htb hob (hdrLen_ge h) (WP.W7k2.bitLen_le_self _)
    rw [hlr, hlt]
    unfold kernelCost rowCost entryCost
    unfold twistBound PreHdr.N eb
    exact hc
  · intro k hk
    have h0 : k ≠ .inl .W0 := fun e => hk W0 e.symm
    have h1 : k ≠ .inl .TR := fun e => hk TR e.symm
    have h2 : k ≠ .inl .TL := fun e => hk TL e.symm
    rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]

#assert_std_axioms ιn_inj ιB_inj runs_embed length_flatten_const hdrSyms_cons hdrLen_ge twist_holds

end WP.W9d
