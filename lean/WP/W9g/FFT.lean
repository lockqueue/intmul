import WP.W9g.FFTDefs

/-!
# WP.W9g.FFT — the recursive leaf FFT, proved with `Triple.fix`

* `fftStep_rs`: a node at stage `t + 1`, from the spec of the recursive call at stage `t` (the
  `Triple.fix` hypothesis): unshuffle, push the child stage, two calls, combine, pop.
* `fft_rs`: `fftProg X` meets `FInv → outSt` for every stage, by `Triple.fix` with measure `s`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

theorem fftStep_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w pin q K d : ℕ) (left : Bool) (tw : ℕ → ℕ → ℤ × ℤ)
    (restT L : List Sym) (htw : TwOK w K tw) (ρ : List (MProg Stk X.Reg)) (t fc : ℕ)
    (rec : ∀ (ys : List (ℤ × ℤ)) (rest' : List Sym) (σ' : Stk → List Sym),
      FInv w pin q K d left tw restT L t ys rest' σ' →
      RS ρ (.recur 0) σ' (outSt pin q tw t ys rest' σ') (fc + 2))
    (xs : List (ℤ × ℤ)) (rest : List Sym) (σ : Stk → List Sym)
    (hinv : FInv w pin q K d left tw restT L (t + 1) xs rest σ) :
    RS ρ (fftBody X) σ (outSt pin q tw (t + 1) xs rest σ)
      (2 * fc + fftO K + 2 ^ (t + 1) * fftB (cellCost CM CA CS CL CR Mul w q) w) := by
  obtain ⟨hctx, hsK, hlen, hWx, hW, ⟨cs0, hcs⟩, h0⟩ := hinv
  obtain ⟨-, -, -, -, htr, htl⟩ := id hctx
  have htK : t < K := by omega
  have hl2 : xs.length = 2 * 2 ^ t := by rw [hlen]; ring
  obtain ⟨hev, hod⟩ := length_evensL_oddsL (2 ^ t) xs hl2
  obtain ⟨hWe, hWo, -⟩ := hW
  obtain ⟨tr, htr'⟩ := leafTape_split tw t K htK
  have hYe := length_fftV pin q tw t (evensL xs)
  have hYo := length_fftV pin q tw t (oddsL xs)
  have eTR : σ .TR = (segsL t tw).flatten ++ (blkE ((List.range (2 ^ t)).map (tw t)) ++
      (blkE ((List.range (2 ^ t)).map (fun j => tw t (2 ^ t + j))) ++
        (symSub :: (tr ++ restT)))) := by
    rw [htr, htr', twSeg_split, segsL_flatten]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hww1 : ∀ z ∈ (List.range (2 ^ t)).map (tw t), EntryW w z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hz
    have hu' := List.mem_range.1 hu
    exact htw t htK u (by rw [Nat.pow_succ]; omega)
  have hww2 : ∀ z ∈ (List.range (2 ^ t)).map (fun j => tw t (2 ^ t + j)), EntryW w z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hz
    have hu' := List.mem_range.1 hu
    exact htw t htK _ (by rw [Nat.pow_succ]; omega)
  have hcells : cells (q + 2) (fftV pin q tw t (evensL xs)) (fftV pin q tw t (oddsL xs))
      ((List.range (2 ^ t)).map (tw t)) ++
      cells (q + 2) (fftV pin q tw t (evensL xs)) (fftV pin q tw t (oddsL xs))
        ((List.range (2 ^ t)).map (fun j => tw t (2 ^ t + j))) = fftV pin q tw (t + 1) xs := by
    rw [cells_range (q + 2) (2 ^ t) (tw t) _ _ hYe hYo,
      cells_range (q + 2) (2 ^ t) (fun j => tw t (2 ^ t + j)) _ _ hYe hYo]
    rfl
  have hinv1 : FInv w pin q K d left tw restT L t (evensL xs) (blkE (oddsL xs) ++ symD :: rest)
      (Function.update (Function.update σ .W0
        (blkE (evensL xs) ++ symD :: (blkE (oddsL xs) ++ symD :: rest))) .CS
        (natSyms t ++ Sym.mark :: σ .CS)) :=
    ⟨(hctx.upd (by decide) _).upd (by decide) _, by omega, hev,
      fun z hz => hWx z (mem_evensL hz), hWe, ⟨σ .CS, rfl⟩, rfl⟩
  have hinv2 : FInv w pin q K d left tw restT L t (oddsL xs) rest
      (outSt pin q tw t (evensL xs) (blkE (oddsL xs) ++ symD :: rest)
        (Function.update (Function.update σ .W0
        (blkE (evensL xs) ++ symD :: (blkE (oddsL xs) ++ symD :: rest))) .CS
        (natSyms t ++ Sym.mark :: σ .CS))) :=
    ⟨(hinv1.1.upd (by decide) _).upd (by decide) _, by omega, hod,
      fun z hz => hWx z (mem_oddsL hz), hWo, ⟨σ .CS, rfl⟩, rfl⟩
  have hD : FCtx q K d left tw restT L
      (outSt pin q tw t (oddsL xs) rest
        (outSt pin q tw t (evensL xs) (blkE (oddsL xs) ++ symD :: rest)
        (Function.update (Function.update σ .W0
        (blkE (evensL xs) ++ symD :: (blkE (oddsL xs) ++ symD :: rest))) .CS
        (natSyms t ++ Sym.mark :: σ .CS)))) :=
    (hinv2.1.upd (by decide) _).upd (by decide) _
  refine ifTop_rs' (T := 2 ^ t * (24 * eb w + 18) + 11 + (23 * bitLen (t + 1) + 27 + (fc + 2 +
      (fc + 2 + (combCost (cellCost CM CA CS CL CR Mul w q) w (2 ^ t) t (leafTape t tw).length +
      (3 * bitLen t + 3)))))) (fun _ => ?_) (fun hc => ?_)
    (step_cost_le _ w K t _ fc htK (length_leafTape w K tw htw t (Nat.le_of_lt htK)))
  · refine (((unsh_rs (τ := X.Reg) w (2 ^ t) xs rest σ hl2 hWx h0).env unshProg_closed _).seq
      (((pushCnt_rs t cs0 _ (by exact hcs)).env pushCnt_closed _).seq
      ((rec _ _ _ hinv1).seq
      ((rec _ _ _ hinv2).seq
      (((comb_rs hok w q t (fftV pin q tw t (evensL xs)) (fftV pin q tw t (oddsL xs))
        ((List.range (2 ^ t)).map (tw t)) ((List.range (2 ^ t)).map (fun j => tw t (2 ^ t + j)))
        (segsL t tw) (σ .R) (Sym.mark :: σ .CS) (symSub :: (tr ++ restT)) L _
        (by rw [hYe, hYo]) (by rw [hYe, List.length_map, List.length_range])
        (by rw [hYe, List.length_map, List.length_range]) (fftW_out hWe) (fftW_out hWo) hww1
        hww2 hD.1 (by rfl) (termOK_mark' _) (by rfl) (segsL_ok t tw) (segsL_length t tw)
        (by rw [segsL_flatten]; exact notGuard_leafTape t tw) (by exact eTR)
        (by exact htl)).env (combProg_closed X) _).seq
      ((popCnt_rs t (σ .CS) _ (by rfl)).env popCnt_closed _)))))).congr ?_ ?_
    · rw [hcells]
      unfold outSt
      funext k
      cases k <;> rfl
    · simp only [hYe, segsL_flatten, le_refl]
  · exfalso
    rw [hcs] at hc
    obtain ⟨bb, l, hbl⟩ : ∃ bb l, encodeNat (t + 1) = bb :: l := by
      cases h : encodeNat (t + 1) with
      | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
      | cons bb l => exact ⟨bb, l, rfl⟩
    simp [natSyms, hbl, optIsBit] at hc

/-- **The recursive leaf FFT.** From `FInv` at stage `s`, `fftProg` reaches `outSt` exactly. -/
theorem fft_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ} (hok : X.OK Mul CM CA CS CL CR)
    (w pin q K d : ℕ) (left : Bool) (tw : ℕ → ℕ → ℤ × ℤ) (restT L : List Sym)
    (htw : TwOK w K tw) (hld : ∀ a, rescLD left d a = rescV pin q a) (s : ℕ)
    (xs : List (ℤ × ℤ)) (rest : List Sym) (σ : Stk → List Sym)
    (hinv : FInv w pin q K d left tw restT L s xs rest σ) :
    RS [] (fftProg X) σ (outSt pin q tw s xs rest σ)
      (fftCost (fftA CL CA CR w d) (fftO K) (fftB (cellCost CM CA CS CL CR Mul w q) w) s + 2) := by
  have key := Triple.fix (ρ := []) (b := fftBody X)
    (P := fun x st => FInv w pin q K d left tw restT L x.1 x.2.1 x.2.2.1 x.2.2.2 ∧
      st.stk = x.2.2.2)
    (Q := fun x st => st.stk = outSt pin q tw x.1 x.2.1 x.2.2.1 x.2.2.2)
    (T := fun x => fftCost (fftA CL CA CR w d) (fftO K)
      (fftB (cellCost CM CA CS CL CR Mul w q) w) x.1) (fun x => x.1) ?_ (s, xs, rest, σ)
  · exact key.pre (fun st hst => ⟨hinv, hst⟩)
  rintro ⟨s, xs, rest, σ⟩ ih
  show Triple [fftBody X] (fun st => FInv w pin q K d left tw restT L s xs rest σ ∧ st.stk = σ)
    (fftBody X) (fun st => st.stk = outSt pin q tw s xs rest σ)
    (fftCost (fftA CL CA CR w d) (fftO K) (fftB (cellCost CM CA CS CL CR Mul w q) w) s)
  refine Triple.pure_pre (fun hinv => ?_)
  rcases s with _ | t
  · exact fftBase_rs hok w pin q K d left tw restT L hld _ xs rest σ hinv
  · exact fftStep_rs hok w pin q K d left tw restT L htw [fftBody X] t
      (fftCost (fftA CL CA CR w d) (fftO K) (fftB (cellCost CM CA CS CL CR Mul w q) w) t)
      (fun ys rest' σ' h => (ih (t, ys, rest', σ') (Nat.lt_succ_self t)).pre
        (fun st hst => ⟨h, hst⟩)) xs rest σ hinv

#assert_std_axioms fftStep_rs fft_rs

end WP.W9g
