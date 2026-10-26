/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulB

/-!
# AR4b, the records of the broadcast product (`Arith/CMulBRec.lean`)

**Scope (honest summary).** Two evaluation lemmas for the record loop of the broadcast product
kernel `cmulBKernel` (`Arith/CMulB.lean`), consumed by `cmulTruncBcast_holds`
(`CMulTruncBcastStmt`, `Machine/Contracts/Arith.lean`; Section 6.3 (`sec:direct-fft-twiddle`): the phase of a
record "multiplies every coefficient of the record"). Everything is proved (no `sorry`); the
per-coefficient behaviour enters only through the explicit hypothesis `hcp` (the contract
`CoefSpecB` of `cpB Pm` whenever the buffer `WB` holds the record's phase).
* `recBodyB_eval`: one record `x` of `z` with its phase `t` (the single coefficient of the matching
  record of `θ`). `phaseIn` copies `t` to `WB` (`Lib.copyBlock_eval`) and drains it from `θ`
  (`drainBits_eval`); the coefficient loop (`coefLoopB_eval`) pushes the fields of
  `cmulTruncC s a t` for every coefficient `a` of `x` on `T`; `phaseOut` drains `WB` and moves the
  record ends (`recTail_eval`). Cost `≤ |x|·(cb + 1) + 30·w2 + 30` (the phase block has `2·w2` bits).
* `recLoopB_eval`: all records, down to a `BlkTerm` rest of `z`; `T` gains the reverse of
  `carrSyms w3 (cmulTruncBcast s zs θs)`; cost `≤ ncoef zs·(cb + 1) + |zs|·(30·w2 + 31) + 1`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

namespace CMulBRecAux

theorem coefBits_length' (w : ℕ) (c : CInt) : (coefBits w c).length = 2 * w := by
  simp only [coefBits, List.length_append, twosBits_length]
  omega

theorem crecBits_single (w : ℕ) (t : CInt) : crecBits w [t] = coefBits w t := by
  simp [crecBits]

theorem carrSyms_bcast_cons (w : ℕ) (t : CInt) (θs : List CInt) :
    carrSyms w (bcastArr (t :: θs)) =
      (coefBits w t).map Sym.bit ++ Sym.sep :: carrSyms w (bcastArr θs) := by
  rw [show bcastArr (t :: θs) = [t] :: bcastArr θs from rfl, carrSyms_cons', crecBits_single]

theorem cmulTruncBcast_cons (s : ℕ) (x : List CInt) (zs : List (List CInt)) (t : CInt)
    (θs : List CInt) :
    cmulTruncBcast s (x :: zs) (t :: θs) =
      (x.map fun c => cmulTruncC s c t) :: cmulTruncBcast s zs θs := rfl

end CMulBRecAux

open CMulBRecAux

/-- **One record of the broadcast product** (see the module docstring). -/
theorem recBodyB_eval {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {w1 w2 w3 s cb : ℕ}
    {S0 : CK → List Sym} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hcp : ∀ (t : CInt), FitsTwos w2 t.1 → FitsTwos w2 t.2 → ∀ S1 : CK → List Sym,
      (∀ k, k ≠ .inl 0 → k ≠ .inl 1 → k ≠ cs .T → k ≠ cs .WB → S1 k = S0 k) →
      S1 (cs .WB) = (coefBits w2 t).map Sym.bit →
      CoefSpecB (cpB Pm) w1 w3 (fun a => cmulTruncC s a t) cb S1)
    (hWB0 : S0 (cs .WB) = []) (hCT0 : S0 (cs .CT) = [])
    (x : List CInt) (t : CInt) (Lz Lθ : List Sym) (v : AReg × Rm) (S : CK → List Sym)
    (hx : ∀ a ∈ x, FitsTwos w1 a.1 ∧ FitsTwos w1 a.2) (ht : FitsTwos w2 t.1 ∧ FitsTwos w2 t.2)
    (hfr : FrameC S S0)
    (hz : S (.inl 0) = (crecBits w1 x).map Sym.bit ++ Sym.sep :: Lz)
    (hθ : S (.inl 1) = (coefBits w2 t).map Sym.bit ++ Sym.sep :: Lθ)
    (hv : v.1.o = (S (.inl 0)).head?) :
    ∃ (v' : AReg × Rm) (t' : ℕ), v'.1.o = Lz.head? ∧ Eval [] (recBodyB Pm) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (.inl 0) Lz) (.inl 1) Lθ) (cs .T)
        ((recSyms (crecBits w3 (x.map fun a => cmulTruncC s a t))).reverse ++ S (cs .T))⟩ t' ∧
      t' ≤ x.length * (cb + 1) + 30 * w2 + 30 := by
  have _hw2 := hw2
  have _hCT0 := hCT0
  have _hv := hv
  have hWB : S (cs .WB) = [] := (hfr (cs .WB) (by decide) (by decide) (by decide)).trans hWB0
  -- `phaseIn`: copy the phase to `WB`, drain it from `θ`, peek at `z`
  have e1 := Lib.copyBlock_eval (src := (.inl 1 : CK)) (dst := cs .WB) (tmp := cs .CT)
    (by decide) (by decide) (by decide) [] v.1.o (coefBits w2 t) (Sym.sep :: Lθ) S
    (TermOK.cons rfl _) hθ
  rw [hWB, List.append_nil] at e1
  have e1' := Eval.liftRegs lensO e1 v.1 rfl
  set S1 := Function.update S (cs .WB) ((coefBits w2 t).map Sym.bit) with hS1
  have e2 := drainBits_eval (B := (.inl 1 : CK)) (coefBits w2 t) (Sym.sep :: Lθ)
    (lensO.set v.1 (some .mark)) S1 (TermOK.cons rfl _)
    (by rw [hS1, Function.update_of_ne (by decide), hθ])
  set S2 := Function.update S1 (.inl 1) (Sym.sep :: Lθ) with hS2
  have ePI : Eval [] phaseIn ⟨v.1, S⟩ _ _ := Eval.seq e1' (Eval.seq e2 (eval_peekO (.inl 0) _ S2))
  obtain ⟨a1, t1, ePI', ha1, ht1⟩ : ∃ (a1 : AReg × Rm) (t1 : ℕ),
      Eval [] (phaseIn.liftRegs (Lens.fst AReg Rm)) ⟨v, S⟩ ⟨a1, S2⟩ t1 ∧
        a1.1.o = (S2 (.inl 0)).head? ∧
        t1 = 7 * (coefBits w2 t).length + 7 + (3 * (coefBits w2 t).length + 2 + 1) :=
    ⟨_, _, Eval.liftRegs (Lens.fst AReg Rm) ePI v rfl, rfl, rfl⟩
  -- the coefficient loop
  have hS2z : S2 (.inl 0) = (crecBits w1 x).map Sym.bit ++ Sym.sep :: Lz := by
    rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), hz]
  have hspec := hcp t ht.1 ht.2 S2
    (fun k h0 h1 hT hW => by
      rw [hS2, Function.update_of_ne h1, hS1, Function.update_of_ne hW]
      exact hfr k h0 h1 hT)
    (by rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_self])
  obtain ⟨v2, t2, -, e4, ht4⟩ := coefLoopB_eval hw1 hspec x (Sym.sep :: Lz) a1 S2 hx
    (fun _ _ _ => rfl) rfl hS2z ha1
  set S3 := Function.update (Function.update S2 (.inl 0) (Sym.sep :: Lz)) (cs .T)
    ((crecBits w3 (x.map fun a => cmulTruncC s a t)).reverse.map Sym.bit ++ S2 (cs .T)) with hS3
  -- `phaseOut`: drain `WB`, then the record ends
  have e5 := drainBits_eval (B := cs .WB) (coefBits w2 t) [] v2.1 S3 TermOK.nil
    (by
      rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS2,
        Function.update_of_ne (by decide), hS1, Function.update_self, List.append_nil])
  set S4 := Function.update S3 (cs .WB) [] with hS4
  have e6 := recTail_eval { v2.1 with q := ([] : List Sym).head? } S4 Lz Lθ
    (by rw [hS4, Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide),
      Function.update_self])
    (by rw [hS4, Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hS2, Function.update_self])
  have ePO : Eval [] phaseOut ⟨v2.1, S3⟩ _ _ := Eval.seq e5 e6
  have ePO' := Eval.liftRegs (Lens.fst AReg Rm) ePO v2 rfl
  refine ⟨(Lens.fst AReg Rm).set v2 { { v2.1 with q := ([] : List Sym).head? } with o := Lz.head? },
    _, rfl, (Eval.seq ePI' (Eval.seq e4 ePO')).of_eq ?_ rfl, ?_⟩
  · have hT : Sym.sep :: S4 (cs .T) =
        (recSyms (crecBits w3 (x.map fun a => cmulTruncC s a t))).reverse ++ S (cs .T) := by
      rw [hS4, Function.update_of_ne (by decide), hS3, Function.update_self, hS2,
        Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide),
        recSyms_reverse_bits, List.cons_append]
    congr 1
    show Function.update (Function.update (Function.update S4 (.inl 0) Lz) (.inl 1) Lθ) (cs .T)
      (Sym.sep :: S4 (cs .T)) = _
    rw [hT]
    clear e1 e1' e2 ePI ePI' e4 e5 e6 ePO ePO' hspec hT
    funext k
    simp only [hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> first | rfl | simp_all
  · rw [coefBits_length'] at ht1
    simp only [coefBits_length']
    omega

/-- **All records of the broadcast product** (see the module docstring). -/
theorem recLoopB_eval {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {w1 w2 w3 s cb : ℕ}
    {S0 : CK → List Sym} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hcp : ∀ (t : CInt), FitsTwos w2 t.1 → FitsTwos w2 t.2 → ∀ S1 : CK → List Sym,
      (∀ k, k ≠ .inl 0 → k ≠ .inl 1 → k ≠ cs .T → k ≠ cs .WB → S1 k = S0 k) →
      S1 (cs .WB) = (coefBits w2 t).map Sym.bit →
      CoefSpecB (cpB Pm) w1 w3 (fun a => cmulTruncC s a t) cb S1)
    (hWB0 : S0 (cs .WB) = []) (hCT0 : S0 (cs .CT) = []) :
    ∀ (zs : List (List CInt)) (θs : List CInt) (rz rθ : List Sym) (v : AReg × Rm)
      (S : CK → List Sym), zs.length = θs.length → CArrFits w1 zs → CArrFits w2 (bcastArr θs) →
      BlkTerm rz → FrameC S S0 → S (.inl 0) = carrSyms w1 zs ++ rz →
      S (.inl 1) = carrSyms w2 (bcastArr θs) ++ rθ → v.1.o = (S (.inl 0)).head? →
      ∃ (v' : AReg × Rm) (t : ℕ), Eval [] (recLoopB Pm) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (cs .T)
          ((carrSyms w3 (cmulTruncBcast s zs θs)).reverse ++ S (cs .T))⟩ t ∧
        t ≤ ncoef zs * (cb + 1) + zs.length * (30 * w2 + 31) + 1
  | [], θs, rz, rθ, v, S, hlen, _, _, hrz, _, hz, hθ, hv => by
    cases θs with
    | cons t θs' => simp at hlen
    | nil =>
      simp only [carrSyms, arrSyms, blk, bcastArr, List.map_nil, List.flatten_nil,
        List.nil_append] at hz hθ
      refine ⟨v, 1, (Eval.loop_false (c := fun v : AReg × Rm => isRecO v.1.o)
        (by show isRecO v.1.o = false; rw [hv, hz]; exact isRecO_false_of_blkTerm hrz)).of_eq ?_
        rfl, by simp [ncoef]⟩
      simp only [cmulTruncBcast, List.zipWith_nil_left, carrSyms, arrSyms, blk, List.map_nil,
        List.flatten_nil, List.reverse_nil, List.nil_append]
      rw [← hz, ← hθ, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | x :: zs, θs, rz, rθ, v, S, hlen, hz1, hθ1, hrz, hfr, hz, hθ, hv => by
    obtain ⟨t, θs', rfl⟩ : ∃ t θs', θs = t :: θs' := by
      cases θs with
      | nil => simp at hlen
      | cons t θs' => exact ⟨t, θs', rfl⟩
    have hz' : S (.inl 0) = (crecBits w1 x).map Sym.bit ++ Sym.sep :: (carrSyms w1 zs ++ rz) := by
      rw [hz, carrSyms_cons']; simp
    have hθ' : S (.inl 1) =
        (coefBits w2 t).map Sym.bit ++ Sym.sep :: (carrSyms w2 (bcastArr θs') ++ rθ) := by
      rw [hθ, carrSyms_bcast_cons]; simp
    have ht : FitsTwos w2 t.1 ∧ FitsTwos w2 t.2 := hθ1 [t] List.mem_cons_self t List.mem_cons_self
    obtain ⟨v1, t1, hv1, e1, ht1⟩ := recBodyB_eval hw1 hw2 hcp hWB0 hCT0 x t _ _ v S
      (fun a ha => hz1 x List.mem_cons_self a ha) ht hfr hz' hθ' hv
    set S1 := Function.update (Function.update (Function.update S (.inl 0) (carrSyms w1 zs ++ rz))
      (.inl 1) (carrSyms w2 (bcastArr θs') ++ rθ)) (cs .T)
      ((recSyms (crecBits w3 (x.map fun a => cmulTruncC s a t))).reverse ++ S (cs .T)) with hS1
    obtain ⟨v', t', e', ht'⟩ := recLoopB_eval hw1 hw2 hcp hWB0 hCT0 zs θs' rz rθ v1 S1
      (by simpa using hlen) (fun cs' h' => hz1 cs' (List.mem_cons_of_mem _ h'))
      (fun cs' h' => hθ1 cs' (List.mem_cons_of_mem _ h')) hrz
      (fun k h1 h2 h3 => by
        rw [hS1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
        exact hfr k h1 h2 h3)
      (by rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self])
      (by rw [hS1, Function.update_of_ne (by decide), Function.update_self])
      (by rw [hv1, hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self])
    have hc0 : isRecO v.1.o = true := by
      rw [hv, hz']
      rcases (crecBits w1 x) with _ | ⟨b, l⟩ <;> rfl
    refine ⟨v', t1 + t' + 1, (Eval.loop_true (c := fun v : AReg × Rm => isRecO v.1.o) hc0 e1
      e').of_eq ?_ rfl, ?_⟩
    · have hT : (carrSyms w3 (cmulTruncBcast s zs θs')).reverse ++ S1 (cs .T) =
          (carrSyms w3 (cmulTruncBcast s (x :: zs) (t :: θs'))).reverse ++ S (cs .T) := by
        rw [hS1, Function.update_self, cmulTruncBcast_cons, carrSyms_cons_rec, List.reverse_append,
          List.append_assoc]
      congr 1
      rw [hT]
      clear e1 e' hT
      funext k
      simp only [hS1, Function.update_apply]
      split_ifs <;> rfl
    · have hn : ncoef (x :: zs) = x.length + ncoef zs := by simp [ncoef]
      rw [hn, Nat.add_mul, List.length_cons, Nat.add_mul, Nat.one_mul]
      generalize ncoef zs * (cb + 1) = Q at ht' ⊢
      generalize x.length * (cb + 1) = P at ht1 ⊢
      generalize zs.length * (30 * w2 + 31) = R at ht' ⊢
      omega

end SubNLogN.Machine.Arith
