/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5KitSpec

/-!
# Proposition A.7 kit builder, part 4 (`AppC/C5KitBase.lean`): the level-`0` interchange

`baseP`: push a `mark` on `tmp2`; the proved digit-pair swap `K1PairPermMix` with `π = prodComm`
(shape `[Rt·N1] × [q] × [G] × [q] × [B]`, counters `G`, `B`) moves the array from `io` onto `tmp2`;
`xfer` moves it back to `io` (stopping at the `mark`); pop the `mark`. The address map of the swap is
`swapMap q m 0 G B` (`pairPermMix_eq_swapMap`). Cost `(C₁ + 8)·(V + 1)`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus

/-- The digit-pair swap with `π = prodComm` is the level-`0` interchange. -/
theorem pairPermMix_eq_swapMap (q m : ℕ) [NeZero q] (G B : ℕ) :
    pairPermMixAddr q G B (Equiv.prodComm (Fin q) (Fin q)).symm = swapMap q m 0 G B := by
  funext x
  simp only [swapMap, pow_zero, pow_one]
  rfl

section Base

variable {q W m : ℕ} {D : NetData W m} (hL : Leaves q D) [NeZero q]

/-- **The level-`0` interchange** (`k = 0`: one digit pair). -/
theorem baseP_spec (Rt N1 G B w : ℕ) (v : List (List Bool)) (rest : List Sym)
    (S : KK hL → List Sym) (_hRt : 1 ≤ Rt) (_hN1 : 1 ≤ N1) (_hG : 1 ≤ G) (_hB : 1 ≤ B)
    (hv : v.length = Rt * rowSize q m 0 N1 G B) (hvw : ∀ p ∈ v, p.length = w)
    (hrest : BlkTerm rest) (hS : S (slotK hL .io) = arrSyms v ++ rest)
    (hctr : CtrOK (slotK hL) S 0 N1 G B) :
    Runs (baseP hL) S (Function.update S (slotK hL .io)
      (arrSyms (permByInv (swapMap q m 0 G B) v) ++ rest)) (fun _ => True)
      ((pkB q).C * (vol v + 1) + 8 * (vol v + 1)) := by
  obtain ⟨r1, r3, r4, r5, t1, t3, t4, t5, e1, e3, e4, e5⟩ := hctr
  have hne : ∀ {x y : Slot W}, x ≠ y → slotK hL x ≠ slotK hL y := fun h e => h (slotK_inj hL e)
  have h_t2_io : slotK hL .tmp2 ≠ slotK hL .io := hne (by simp)
  have h_t2_tmp : slotK hL .tmp2 ≠ slotK hL .tmp := hne (by simp)
  have h_io_tmp : slotK hL .io ≠ slotK hL .tmp := hne (by simp)
  have h_cG_t2 : slotK hL .cG ≠ slotK hL .tmp2 := hne (by simp)
  have h_cB_t2 : slotK hL .cB ≠ slotK hL .tmp2 := hne (by simp)
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdvd0 : q ^ m ^ 0 * G * q ^ m ^ 0 * B ∣ v.length := by
    rw [hv]
    exact Dvd.intro_left (Rt * N1) (by simp only [rowSize]; ring)
  have hlt : ∀ y < v.length, swapMap q m 0 G B y < v.length := fun y hy =>
    swapFieldsInv_lt _ _ _ _ _ y hdvd0 hy
  set v' := permByInv (swapMap q m 0 G B) v with hv'
  have hvw' : ∀ p ∈ v', p.length = w := permByInv_widths _ _ _ hlt hvw
  -- (1) mark `tmp2`
  set S1 := Function.update S (slotK hL .tmp2) (Sym.mark :: S (slotK hL .tmp2)) with hS1
  have h1r : Runs (pushC (slotK hL .tmp2) Sym.mark) S S1 (fun _ => True) 1 :=
    Runs.of_eval fun x => ⟨_, _, pushC_eval (slotK hL .tmp2) Sym.mark x S, trivial, le_rfl⟩
  have h1 : RunsIn [] ((pushC (slotK hL .tmp2) Sym.mark).liftRegs (lr hL)) S S1 (fun _ => True)
      1 :=
    RunsIn.mono (RunsIn.of_runs_liftRegs (lr hL) h1r
      (by simp [Prog.Closed, pushC, Prog.FreeBelow]) []) (fun _ _ => trivial) le_rfl
  -- (2) the digit-pair swap `io → tmp2`
  have hS1io : S1 (slotK hL .io) = arrSyms v ++ rest := by
    rw [hS1, Function.update_of_ne (Ne.symm h_t2_io)]; exact hS
  have hS1cG : S1 (slotK hL .cG) = natSyms G ++ r4 := by
    rw [hS1, Function.update_of_ne h_cG_t2]; exact e4
  have hS1cB : S1 (slotK hL .cB) = natSyms B ++ r5 := by
    rw [hS1, Function.update_of_ne h_cB_t2]; exact e5
  set S2 := Function.update (Function.update S1 (slotK hL .io) rest) (slotK hL .tmp2)
    (arrSyms v' ++ S1 (slotK hL .tmp2)) with hS2
  have h2 : Runs (callInj (ιB hL) (lB hL) (pkB q).P) S1 S2 (fun _ => True)
      ((pkB q).C * (vol v + 1)) := by
    refine runs_callInj_le (Q := fun _ => True) (ιB_inj hL) _ ?_ ?_ le_rfl
    · have hlen : v.length = Rt * N1 * q * G * q * B := by
        rw [hv]; simp only [rowSize, pow_zero, pow_one]; ring
      have := (pkB q).spec (Rt * N1) G B v rest r4 r5 (S1 ∘ ιB hL) hlen hrest t4 t5 hS1io hS1cG
        hS1cB
      rw [pairPermMix_eq_swapMap q m G B] at this
      rw [hS2, show slotK hL .tmp2 = ιB hL (.inl 1) from rfl,
        Function.update_comp_eq_of_injective _ (ιB_inj hL),
        show slotK hL .io = ιB hL (.inl 0) from rfl,
        Function.update_comp_eq_of_injective _ (ιB_inj hL)]
      exact this
    · intro key hk
      rw [hS2, Function.update_of_ne (a' := slotK hL .tmp2) (fun h => hk (.inl 1) h.symm),
        Function.update_of_ne (a' := slotK hL .io) (fun h => hk (.inl 0) h.symm)]
  -- (3) transfer back `tmp2 → io`
  have hS2t2 : S2 (slotK hL .tmp2) = arrSyms v' ++ (Sym.mark :: S (slotK hL .tmp2)) := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
  have hS2io : S2 (slotK hL .io) = rest := by
    rw [hS2, Function.update_of_ne (Ne.symm h_t2_io), Function.update_self]
  set S3 := Function.update (Function.update S2 (slotK hL .tmp2) (Sym.mark :: S (slotK hL .tmp2)))
    (slotK hL .io) (arrSyms v' ++ S2 (slotK hL .io)) with hS3
  have h3r : Runs (xfer (slotK hL .tmp2) (slotK hL .io) (slotK hL .tmp)) S2 S3 (fun _ => True)
      (6 * vol v' + 2 * v'.length + 5) :=
    Runs.of_eval fun x =>
      ⟨_, _, xfer_eval h_t2_io h_t2_tmp h_io_tmp x v' (Sym.mark :: S (slotK hL .tmp2)) S2 rfl
        hS2t2, trivial, le_rfl⟩
  have h3 : RunsIn [] ((xfer (slotK hL .tmp2) (slotK hL .io) (slotK hL .tmp)).liftRegs (lr hL))
      S2 S3 (fun _ => True) (6 * vol v' + 2 * v'.length + 5) :=
    RunsIn.mono (RunsIn.of_runs_liftRegs (lr hL) h3r (closed_xfer _ _ _) [])
      (fun _ _ => trivial) le_rfl
  -- (4) pop the mark
  have hS3t2 : S3 (slotK hL .tmp2) = Sym.mark :: S (slotK hL .tmp2) := by
    rw [hS3, Function.update_of_ne h_t2_io, Function.update_self]
  set S4 := Function.update S3 (slotK hL .tmp2) (S3 (slotK hL .tmp2)).tail with hS4
  have h4r : Runs (popR (slotK hL .tmp2)) S3 S4 (fun _ => True) 1 :=
    Runs.of_eval fun x => ⟨_, _, popR_eval (slotK hL .tmp2) x S3, trivial, le_rfl⟩
  have h4 : RunsIn [] ((popR (slotK hL .tmp2)).liftRegs (lr hL)) S3 S4 (fun _ => True) 1 :=
    RunsIn.mono (RunsIn.of_runs_liftRegs (lr hL) h4r
      (by simp [Prog.Closed, popR, Prog.FreeBelow]) []) (fun _ _ => trivial) le_rfl
  have hall := RunsIn.seq h1 (RunsIn.seq (RunsIn.iff_runs.2 h2) (RunsIn.seq h3 h4))
  have hfin : S4 = Function.update S (slotK hL .io) (arrSyms v' ++ rest) := by
    funext key
    by_cases k2 : key = slotK hL .tmp2
    · subst k2
      rw [hS4, Function.update_self, hS3t2, List.tail_cons, Function.update_of_ne h_t2_io]
    · rw [hS4, Function.update_of_ne k2]
      by_cases kio : key = slotK hL .io
      · subst kio
        rw [hS3, Function.update_self, hS2io, Function.update_self]
      · rw [hS3, Function.update_of_ne kio, Function.update_of_ne k2, hS2,
          Function.update_of_ne k2, Function.update_of_ne kio, hS1, Function.update_of_ne k2,
          Function.update_of_ne kio]
  rw [hfin] at hall
  refine RunsIn.iff_runs.1 (RunsIn.mono hall (fun _ _ => trivial) ?_)
  have hvol' : vol v' = vol v := by
    rw [vol_of_widths v' w hvw', vol_of_widths v w hvw, hv', permByInv_length]
  have hlen' : v'.length ≤ vol v := by
    rw [hv', permByInv_length, vol_of_widths v w hvw]
    exact Nat.le_mul_of_pos_right _ (by omega)
  rw [hvol']
  omega

end Base

end SubNLogN.Machine.C5
