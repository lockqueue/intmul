import WP.W9a.PipePost
import WP.W9a.LevelPreMain
import WP.W9a.LevelPostMain

/-!
# WP.W9a.Pipeline — `W9_levels_of_kernels` and `W9_pipeline_of_levels`

* `W9_levels_of_kernels_holds`: the three level theorems combined.
* `W9_pipeline_of_levels_holds`: the pipeline program is
  `push symGuard on TL; lvl PRE LEAF POST; rewind TL onto TR down to the guard`, where `lvl` is the
  `W9_level` driver and PRE/LEAF/POST are the level-contract programs, embedded with `embL` (scratch
  `max` of the three) and register lenses into `Rp × (Rl × Ro)`. The `W9_level` predicates are
  `PA`/`PB` (WP.W9a.PipeFrame), the steps are `pre_step`, `leaf_step`, `post_step`, and the cost
  sums by `chain_cost` and `depth_le_pipeBound`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

/-- **Assembly: level programs from the kernels.** -/
theorem W9_levels_of_kernels_holds (Mul : ℕ → ℕ) : W9_levels_of_kernels Mul :=
  fun hSw hRm hFl hPre hLeaf hPost =>
    ⟨W9_preLevelProg_holds Mul hSw hRm hPre, W9_leafLevelProg_holds Mul hSw hLeaf,
      W9_postLevelProg_holds Mul hSw hFl hPost⟩

/-- The pipeline program: guard on `TL`, the level driver, then rewind the tape onto `TR`. -/
def pipeProg {m : ℕ} {R : Type} (lv : Prog (BLoc m) (fun _ => Sym) R) :
    Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (liftQ (pushC (.inl .TL) symGuard))
    (.seq (liftK lv) (liftQ (moveUntil (.inl .TL) (.inl .TR) (isSym symGuard))))

theorem closed_pipeProg {m : ℕ} {R : Type} {lv : Prog (BLoc m) (fun _ => Sym) R}
    (h : lv.Closed) : (pipeProg lv).Closed :=
  closed_seq (closed_liftQ (closed_pushC _ _))
    (closed_seq (closed_liftK h) (closed_liftQ (closed_moveUntil _ _ _)))

/-- Cost arithmetic of the pipeline. -/
theorem pipe_cost (Cx Clv SP L SO PB T D t2 : ℕ)
    (ht2 : t2 ≤ Cx * SP + Cx * L + Cx * SO + Clv * (2 * D + 3)) (hcc : SP + L + SO ≤ PB + T)
    (hdp : 2 * D + 1 ≤ PB) :
    1 + (t2 + (3 * T + 2)) ≤ (Cx + 2 * Clv + 3) * (PB + T + 1) := by
  have f1 : Cx * SP + Cx * L + Cx * SO = Cx * (SP + L + SO) := by ring
  have f2 : Cx * (SP + L + SO) ≤ Cx * (PB + T + 1) := Nat.mul_le_mul_left _ (by omega)
  have f3 : Clv * (2 * D + 3) ≤ Clv * (2 * (PB + T + 1)) := Nat.mul_le_mul_left _ (by omega)
  have f4 : Clv * (2 * (PB + T + 1)) = 2 * (Clv * (PB + T + 1)) := by ring
  have f5 : (Cx + 2 * Clv + 3) * (PB + T + 1) =
      Cx * (PB + T + 1) + 2 * (Clv * (PB + T + 1)) + 3 * (PB + T + 1) := by ring
  omega

/-- **Assembly: the pipeline from the level driver and the level programs.** -/
theorem W9_pipeline_of_levels_holds (Mul : ℕ → ℕ) : W9_pipeline_of_levels Mul := by
  intro hLv hPre hLeaf hPost
  obtain ⟨Clv, hLv⟩ := hLv
  obtain ⟨Cp, hPre⟩ := hPre
  obtain ⟨mp, Rp, Pp, hmp, hRpF, ⟨rp0⟩, hPpC, hPp⟩ := hPre ()
  obtain ⟨Cl, hLeaf⟩ := hLeaf
  obtain ⟨ml, Rl, Pl, hml, hRlF, ⟨rl0⟩, hPlC, hPl⟩ := hLeaf ()
  obtain ⟨Co, hPost⟩ := hPost
  obtain ⟨mo, Ro, Po, hmo, hRoF, ⟨ro0⟩, hPoC, hPo⟩ := hPost ()
  have hPp' : PreLevelSpec Mul mp Rp Cp Pp := hPp
  have hPl' : LeafLevelSpec Mul ml Rl Cl Pl := hPl
  have hPo' : PostLevelSpec Mul mo Ro Co Po := hPo
  obtain ⟨mL, hmL⟩ : ∃ mL, mL = max (max mp ml) mo := ⟨_, rfl⟩
  have hmp' : mp ≤ mL := hmL ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hml' : ml ≤ mL := hmL ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hmo' : mo ≤ mL := hmL ▸ le_max_right _ _
  have hmL64 : mL ≤ w9Scratch := hmL ▸ max_le (max_le hmp hml) hmo
  obtain ⟨Q, lvl, hQF, ⟨q0⟩, hlvC, hlv⟩ := hLv mL (Rp × (Rl × Ro))
  haveI := hRpF
  haveI := hRlF
  haveI := hRoF
  haveI := hQF
  refine ⟨Cp + Cl + Co + 2 * Clv + 3, fun _ => ⟨mL, ((Rp × (Rl × Ro)) × Q) × Option Sym,
    pipeProg (lvl ((Pp.mapStk (embL hmp')).liftRegs (Lens.fst Rp (Rl × Ro)))
      ((Pl.mapStk (embL hml')).liftRegs ((Lens.snd Rp (Rl × Ro)).comp (Lens.fst Rl Ro)))
      ((Po.mapStk (embL hmo')).liftRegs ((Lens.snd Rp (Rl × Ro)).comp (Lens.snd Rl Ro)))),
    hmL64, inferInstance, ⟨(((rp0, (rl0, ro0)), q0), none)⟩,
    closed_pipeProg (hlvC _ _ _ (closed_liftRegs _ (closed_embL hmp' hPpC))
      (closed_liftRegs _ (closed_embL hml' hPlC)) (closed_liftRegs _ (closed_embL hmo' hPoC))),
    ?_⟩⟩
  intro cSpec p_in wd xs σ restS restT r1 hChain hS hW0 hTR hrestT hC1
  rintro ⟨⟨v, rq⟩, S⟩ hs
  simp only at hs
  have hs' : σ = S := hs.symm
  subst hs'
  -- (1) the guard
  have e1 : Eval [] (liftQ (R := (Rp × (Rl × Ro)) × Q) (pushC (.inl .TL) symGuard))
      ⟨(v, rq), σ⟩ ⟨(v, rq), Function.update σ (.inl .TL) (symGuard :: σ (.inl .TL))⟩ 1 :=
    liftQ_eval (Eval.push (K := BLoc mL) (Γ := fun _ => Sym) [] (.inl .TL) (fun _ => symGuard) rq σ)
      (v, rq) rfl
  -- (2) the level driver
  have hlvl := hlv ((Pp.mapStk (embL hmp')).liftRegs (Lens.fst Rp (Rl × Ro)))
    ((Pl.mapStk (embL hml')).liftRegs ((Lens.snd Rp (Rl × Ro)).comp (Lens.fst Rl Ro)))
    ((Po.mapStk (embL hmo')).liftRegs ((Lens.snd Rp (Rl × Ro)).comp (Lens.snd Rl Ro)))
    (depthOf cSpec) (PA σ cSpec p_in xs restS restT) (PB σ cSpec p_in xs restS restT)
    (fun ℓ => (Cp + Cl + Co) * preB Mul wd cSpec p_in 0 xs ℓ)
    (fun ℓ => (Cp + Cl + Co) * postB Mul wd cSpec p_in 0 xs ℓ)
    ((Cp + Cl + Co) * leafB Mul wd cSpec p_in 0 xs)
    (fun ℓ hℓ τ hA => tag_pre hℓ hA) (fun τ hA => tag_leaf hA)
    (fun ℓ hℓ τ hB => tag_post hℓ hB) (fun τ hB => tag_end hrestT hB)
    (fun ℓ hℓ τ hA => pre_step hmp' (Lens.fst Rp (Rl × Ro)) hPp' (by omega) hChain hW0 hC1 hℓ τ hA)
    (fun τ hA => leaf_step hml' ((Lens.snd Rp (Rl × Ro)).comp (Lens.fst Rl Ro)) hPl' (by omega)
      hChain hW0 hC1 τ hA)
    (fun ℓ hℓ τ hB => post_step hmo' ((Lens.snd Rp (Rl × Ro)).comp (Lens.snd Rl Ro)) hPo'
      (by omega) hChain hW0 hℓ τ hB)
    _ (pa_zero (p_in := p_in) hS hTR)
  obtain ⟨⟨v2, S2⟩, t2, e2, hB0, ht2⟩ :=
    hlvl ⟨v, Function.update σ (.inl .TL) (symGuard :: σ (.inl .TL))⟩ rfl
  obtain ⟨hTL2, hfin⟩ := pb_zero_final hTR hB0
  -- (3) the rewind
  have e3 := moveUntil_eval (src := (.inl .TL : BLoc mL)) (dst := .inl .TR) (by simp)
    (isSym symGuard) rq (tapeSyms cSpec).reverse (symGuard :: σ (.inl .TL)) S2
    (fun x hx => isSym_some_of_ne (fun e => guard_not_mem_tape cSpec
      (e ▸ List.mem_reverse.1 hx))) (isSym_some_self symGuard) hTL2
  refine ⟨_, _, Eval.seq e1 (Eval.seq (liftK_eval e2 rq) (liftQ_eval e3 (v2, rq) rfl)),
    ⟨hfin, trivial⟩, ?_⟩
  -- (4) the cost
  rw [List.length_reverse]
  rw [sumTo_mul_left, sumTo_mul_left] at ht2
  exact pipe_cost (Cp + Cl + Co) Clv _ _ _ _ _ _ t2 ht2 (chain_cost Mul wd cSpec p_in 0 xs)
    (depth_le_pipeBound Mul wd cSpec p_in 0 xs.length)

#assert_std_axioms W9_levels_of_kernels_holds pipe_cost W9_pipeline_of_levels_holds

end WP.W9a
