/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulOne

/-!
# AR, products: the two-source array driver (`Arith/CMulDrv.lean`)

**Scope (honest summary).** Loops over the coefficients of a record and over the records of two
aligned arrays (`z` on `.inl 0`, `θ` on `.inl 1`), generic in a coefficient program `cp` given by
its contract `CoefSpecC` relative to fixed stacks `S0` outside `z`, `θ` and the output stack.
* `coefLoop_eval`: all coefficients of one record; `recBodyC_eval`: one record and its `sep`s;
  `recLoopC_eval`: all records, down to a `BlkTerm` rest of `z`.
The output is accumulated on `cs .T` in push order (so reversed). Everything is proved.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

variable {Rm : Type}

/-- Coefficient loop of one record. -/
def coefLoop (cp : Prog CK (fun _ => Sym) (AReg × Rm)) : Prog CK (fun _ => Sym) (AReg × Rm) :=
  .loop (fun v => isBitO v.1.o) cp

/-- End of a record: pop both `sep`s, push `sep` on the output, peek at `z`. -/
def recTail : AProg CK :=
  .seq (drop1 (.inl 0)) (.seq (drop1 (.inl 1)) (.seq (pushS (cs .T) .sep) (peekO (.inl 0))))

/-- One record. -/
def recBodyC (cp : Prog CK (fun _ => Sym) (AReg × Rm)) : Prog CK (fun _ => Sym) (AReg × Rm) :=
  .seq (coefLoop cp) (recTail.liftRegs (Lens.fst AReg Rm))

/-- All records. -/
def recLoopC (cp : Prog CK (fun _ => Sym) (AReg × Rm)) : Prog CK (fun _ => Sym) (AReg × Rm) :=
  .loop (fun v => isRecO v.1.o) (recBodyC cp)

/-- The stacks agree with `S0` except on `z`, `θ` and the output stack. -/
def FrameC (S S0 : CK → List Sym) : Prop :=
  ∀ k, k ≠ .inl 0 → k ≠ .inl 1 → k ≠ cs .T → S k = S0 k

/-- **Coefficient-level contract** of a coefficient program, relative to `S0`. -/
def CoefSpecC (cp : Prog CK (fun _ => Sym) (AReg × Rm)) (w1 w2 w3 s cb : ℕ)
    (S0 : CK → List Sym) : Prop :=
  ∀ (a c : CInt) (Lz Lθ : List Sym) (v : AReg × Rm) (S : CK → List Sym),
    FitsTwos w1 a.1 → FitsTwos w1 a.2 → FitsTwos w2 c.1 → FitsTwos w2 c.2 → FrameC S S0 →
    S (.inl 0) = (coefBits w1 a).map Sym.bit ++ Lz →
    S (.inl 1) = (coefBits w2 c).map Sym.bit ++ Lθ →
    ∃ (v' : AReg × Rm) (t : ℕ), v'.1.o = Lz.head? ∧ Eval [] cp ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (.inl 0) Lz) (.inl 1) Lθ) (cs .T)
        ((coefBits w3 (cmulTruncC s a c)).reverse.map Sym.bit ++ S (cs .T))⟩ t ∧ t ≤ cb

theorem crecBits_cons' (w : ℕ) (a : CInt) (xs : List CInt) :
    crecBits w (a :: xs) = coefBits w a ++ crecBits w xs := by
  simp [crecBits]

theorem coefLoop_eval {cp : Prog CK (fun _ => Sym) (AReg × Rm)} {w1 w2 w3 s cb : ℕ}
    {S0 : CK → List Sym} (hw1 : 1 ≤ w1) (hspec : CoefSpecC cp w1 w2 w3 s cb S0) :
    ∀ (xs ys : List CInt) (Lz Lθ : List Sym) (v : AReg × Rm) (S : CK → List Sym),
      xs.length = ys.length →
      (∀ a ∈ xs, FitsTwos w1 a.1 ∧ FitsTwos w1 a.2) →
      (∀ c ∈ ys, FitsTwos w2 c.1 ∧ FitsTwos w2 c.2) →
      FrameC S S0 → isBitO Lz.head? = false →
      S (.inl 0) = (crecBits w1 xs).map Sym.bit ++ Lz →
      S (.inl 1) = (crecBits w2 ys).map Sym.bit ++ Lθ → v.1.o = (S (.inl 0)).head? →
      ∃ (v' : AReg × Rm) (t : ℕ), v'.1.o = Lz.head? ∧ Eval [] (coefLoop cp) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S (.inl 0) Lz) (.inl 1) Lθ) (cs .T)
          ((crecBits w3 (List.zipWith (cmulTruncC s) xs ys)).reverse.map Sym.bit ++
            S (cs .T))⟩ t ∧
        t ≤ xs.length * (cb + 1) + 1
  | [], [], Lz, Lθ, v, S, _, _, _, _, hL, hz, hθ, hv => by
    simp only [crecBits, List.flatMap_nil, List.map_nil, List.nil_append] at hz hθ
    refine ⟨v, 1, by rw [hv, hz], (Eval.loop_false (c := fun v : AReg × Rm => isBitO v.1.o)
      (by show isBitO v.1.o = false; rw [hv, hz]; exact hL)).of_eq ?_ rfl, by simp⟩
    simp only [List.zipWith_nil_left, crecBits, List.flatMap_nil, List.reverse_nil, List.map_nil,
      List.nil_append]
    rw [← hz, ← hθ, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | [], _ :: _, _, _, _, _, h, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _, _, _, _, _ => by simp at h
  | a :: xs, c :: ys, Lz, Lθ, v, S, hlen, hxs, hys, hfr, hL, hz, hθ, hv => by
    have ha := hxs a List.mem_cons_self
    have hc := hys c List.mem_cons_self
    have hz' : S (.inl 0) = (coefBits w1 a).map Sym.bit ++
        ((crecBits w1 xs).map Sym.bit ++ Lz) := by
      rw [hz, crecBits_cons', List.map_append, List.append_assoc]
    have hθ' : S (.inl 1) = (coefBits w2 c).map Sym.bit ++
        ((crecBits w2 ys).map Sym.bit ++ Lθ) := by
      rw [hθ, crecBits_cons', List.map_append, List.append_assoc]
    obtain ⟨v1, t1, hv1, e1, ht1⟩ := hspec a c _ _ v S ha.1 ha.2 hc.1 hc.2 hfr hz' hθ'
    set S1 := Function.update (Function.update (Function.update S (.inl 0)
      ((crecBits w1 xs).map Sym.bit ++ Lz)) (.inl 1) ((crecBits w2 ys).map Sym.bit ++ Lθ)) (cs .T)
      ((coefBits w3 (cmulTruncC s a c)).reverse.map Sym.bit ++ S (cs .T)) with hS1
    obtain ⟨v', t', hv', e', ht'⟩ := coefLoop_eval hw1 hspec xs ys Lz Lθ v1 S1
      (by simpa using hlen)
      (fun a' h' => hxs a' (List.mem_cons_of_mem _ h'))
      (fun c' h' => hys c' (List.mem_cons_of_mem _ h'))
      (fun k h1 h2 h3 => by
        rw [hS1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
        exact hfr k h1 h2 h3)
      hL (by simp [hS1]) (by simp [hS1]) (by rw [hv1]; simp [hS1])
    have hc0 : isBitO v.1.o = true := by
      rw [hv, hz']
      obtain ⟨k, rfl⟩ : ∃ k, w1 = k + 1 := ⟨w1 - 1, by omega⟩
      simp [coefBits, K1.twosBits_succ, isBitO]
    refine ⟨v', t1 + t' + 1, hv', (Eval.loop_true (c := fun v : AReg × Rm => isBitO v.1.o)
      hc0 e1 e').of_eq ?_ rfl, ?_⟩
    · have hT : (crecBits w3 (List.zipWith (cmulTruncC s) xs ys)).reverse.map Sym.bit ++
            S1 (cs .T) = (crecBits w3 (List.zipWith (cmulTruncC s) (a :: xs) (c :: ys))).reverse.map
            Sym.bit ++ S (cs .T) := by
        rw [hS1, Function.update_self, List.zipWith_cons_cons, crecBits_cons', List.reverse_append,
          List.map_append, List.append_assoc]
      congr 1
      rw [hT]
      funext k
      simp only [hS1, Function.update_apply]
      split_ifs <;> first | rfl | simp_all
    · simp only [List.length_cons, Nat.add_mul, one_mul]
      generalize xs.length * (cb + 1) = Q at ht' ⊢
      omega

theorem recTail_eval (v : AReg) (S : CK → List Sym) (Lz Lθ : List Sym)
    (hz : S (.inl 0) = Sym.sep :: Lz) (hθ : S (.inl 1) = Sym.sep :: Lθ) :
    Eval [] recTail ⟨v, S⟩ ⟨{ v with o := Lz.head? }, Function.update (Function.update
      (Function.update S (.inl 0) Lz) (.inl 1) Lθ) (cs .T) (Sym.sep :: S (cs .T))⟩ 4 := by
  have e1 := eval_drop1 (.inl 0) v S Sym.sep Lz hz
  have e2 := eval_drop1 (.inl 1) v (Function.update S (.inl 0) Lz) Sym.sep Lθ
    (by rw [Function.update_of_ne (by decide), hθ])
  set F2 := Function.update (Function.update S (.inl 0) Lz) (.inl 1) Lθ with hF2
  have hT : F2 (cs .T) = S (cs .T) := by simp [hF2]
  have e3 : Eval [] (pushS (cs .T) .sep) ⟨v, F2⟩
      ⟨v, Function.update F2 (cs .T) (Sym.sep :: S (cs .T))⟩ 1 := by
    have h := eval_pushS (cs .T) .sep v F2
    rwa [hT] at h
  set F3 := Function.update F2 (cs .T) (Sym.sep :: S (cs .T)) with hF3
  have h5 : F3 (.inl 0) = Lz := by simp [hF3, hF2]
  have e4 : Eval [] (peekO (.inl 0)) ⟨v, F3⟩ ⟨{ v with o := Lz.head? }, F3⟩ 1 := by
    have h := eval_peekO (.inl 0) v F3
    rwa [h5] at h
  exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))

theorem recBodyC_eval {cp : Prog CK (fun _ => Sym) (AReg × Rm)} {w1 w2 w3 s cb : ℕ}
    {S0 : CK → List Sym} (hw1 : 1 ≤ w1) (hspec : CoefSpecC cp w1 w2 w3 s cb S0)
    (xs ys : List CInt) (Lz Lθ : List Sym) (v : AReg × Rm) (S : CK → List Sym)
    (hlen : xs.length = ys.length) (hxs : ∀ a ∈ xs, FitsTwos w1 a.1 ∧ FitsTwos w1 a.2)
    (hys : ∀ c ∈ ys, FitsTwos w2 c.1 ∧ FitsTwos w2 c.2) (hfr : FrameC S S0)
    (hz : S (.inl 0) = (crecBits w1 xs).map Sym.bit ++ Sym.sep :: Lz)
    (hθ : S (.inl 1) = (crecBits w2 ys).map Sym.bit ++ Sym.sep :: Lθ)
    (hv : v.1.o = (S (.inl 0)).head?) :
    ∃ (v' : AReg × Rm) (t : ℕ), v'.1.o = Lz.head? ∧ Eval [] (recBodyC cp) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (.inl 0) Lz) (.inl 1) Lθ) (cs .T)
        ((recSyms (crecBits w3 (List.zipWith (cmulTruncC s) xs ys))).reverse ++ S (cs .T))⟩ t ∧
      t ≤ xs.length * (cb + 1) + 5 := by
  obtain ⟨v1, t1, hv1, e1, ht1⟩ := coefLoop_eval hw1 hspec xs ys (Sym.sep :: Lz) (Sym.sep :: Lθ)
    v S hlen hxs hys hfr rfl hz hθ hv
  set S1 := Function.update (Function.update (Function.update S (.inl 0) (Sym.sep :: Lz)) (.inl 1)
    (Sym.sep :: Lθ)) (cs .T) ((crecBits w3 (List.zipWith (cmulTruncC s) xs ys)).reverse.map
      Sym.bit ++ S (cs .T)) with hS1
  have e2 := recTail_eval v1.1 S1 Lz Lθ (by simp [hS1]) (by simp [hS1])
  have e2' := Eval.liftRegs (Lens.fst AReg Rm) e2 v1 rfl
  refine ⟨(Lens.fst AReg Rm).set v1 { v1.1 with o := Lz.head? }, t1 + 4, rfl,
    (Eval.seq e1 e2').of_eq ?_ rfl, by omega⟩
  have hT : Sym.sep :: S1 (cs .T) =
      (recSyms (crecBits w3 (List.zipWith (cmulTruncC s) xs ys))).reverse ++ S (cs .T) := by
    rw [hS1, Function.update_self, recSyms_reverse_bits, List.cons_append]
  congr 1
  show Function.update (Function.update (Function.update S1 (.inl 0) Lz) (.inl 1) Lθ) (cs .T)
    (Sym.sep :: S1 (cs .T)) = _
  rw [hT]
  funext k
  simp only [hS1, Function.update_apply]
  split_ifs <;> first | rfl | simp_all

theorem carrSyms_cons' (w : ℕ) (x : List CInt) (zs : List (List CInt)) :
    carrSyms w (x :: zs) = (crecBits w x).map Sym.bit ++ Sym.sep :: carrSyms w zs := by
  simp [carrSyms, arrSyms, blk, recSyms]

theorem carrSyms_cons_rec (w : ℕ) (x : List CInt) (zs : List (List CInt)) :
    carrSyms w (x :: zs) = recSyms (crecBits w x) ++ carrSyms w zs := by
  simp [carrSyms, arrSyms, blk]

theorem recLoopC_eval {cp : Prog CK (fun _ => Sym) (AReg × Rm)} {w1 w2 w3 s cb : ℕ}
    {S0 : CK → List Sym} (hw1 : 1 ≤ w1) (hspec : CoefSpecC cp w1 w2 w3 s cb S0) :
    ∀ (zs θs : List (List CInt)) (rz rθ : List Sym) (v : AReg × Rm) (S : CK → List Sym),
      CAligned zs θs → CArrFits w1 zs → CArrFits w2 θs → BlkTerm rz → FrameC S S0 →
      S (.inl 0) = carrSyms w1 zs ++ rz → S (.inl 1) = carrSyms w2 θs ++ rθ →
      v.1.o = (S (.inl 0)).head? →
      ∃ (v' : AReg × Rm) (t : ℕ), Eval [] (recLoopC cp) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (cs .T)
          ((carrSyms w3 (zipC (cmulTruncC s) zs θs)).reverse ++ S (cs .T))⟩ t ∧
        t ≤ ncoef zs * (cb + 1) + 6 * zs.length + 1
  | [], θs, rz, rθ, v, S, hal, _, _, hrz, _, hz, hθ, hv => by
    cases hal
    simp only [carrSyms, arrSyms, blk, List.map_nil, List.flatten_nil, List.nil_append] at hz hθ
    refine ⟨v, 1, (Eval.loop_false (c := fun v : AReg × Rm => isRecO v.1.o)
      (by show isRecO v.1.o = false; rw [hv, hz]; exact isRecO_false_of_blkTerm hrz)).of_eq ?_ rfl,
      by simp [ncoef]⟩
    simp only [zipC, List.zipWith_nil_left, carrSyms, arrSyms, blk, List.map_nil,
      List.flatten_nil, List.reverse_nil, List.nil_append]
    rw [← hz, ← hθ, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  | x :: zs, θs, rz, rθ, v, S, hal, hz1, hθ1, hrz, hfr, hz, hθ, hv => by
    obtain ⟨y, θs', hxy, hal', rfl⟩ : ∃ y θs', x.length = y.length ∧ CAligned zs θs' ∧
        θs = y :: θs' := by
      cases hal with
      | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
    have hz' : S (.inl 0) = (crecBits w1 x).map Sym.bit ++ Sym.sep :: (carrSyms w1 zs ++ rz) := by
      rw [hz, carrSyms_cons']; simp
    have hθ' : S (.inl 1) = (crecBits w2 y).map Sym.bit ++ Sym.sep :: (carrSyms w2 θs' ++ rθ) := by
      rw [hθ, carrSyms_cons']; simp
    obtain ⟨v1, t1, hv1, e1, ht1⟩ := recBodyC_eval hw1 hspec x y _ _ v S hxy
      (fun a ha => hz1 x List.mem_cons_self a ha) (fun c hc => hθ1 y List.mem_cons_self c hc)
      hfr hz' hθ' hv
    set S1 := Function.update (Function.update (Function.update S (.inl 0) (carrSyms w1 zs ++ rz))
      (.inl 1) (carrSyms w2 θs' ++ rθ)) (cs .T)
      ((recSyms (crecBits w3 (List.zipWith (cmulTruncC s) x y))).reverse ++ S (cs .T)) with hS1
    obtain ⟨v', t', e', ht'⟩ := recLoopC_eval hw1 hspec zs θs' rz rθ v1 S1 hal'
      (fun cs' h' => hz1 cs' (List.mem_cons_of_mem _ h'))
      (fun cs' h' => hθ1 cs' (List.mem_cons_of_mem _ h')) hrz
      (fun k h1 h2 h3 => by
        rw [hS1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
        exact hfr k h1 h2 h3)
      (by simp [hS1]) (by simp [hS1]) (by rw [hv1]; simp [hS1])
    have hc0 : isRecO v.1.o = true := by
      rw [hv, hz']
      rcases (crecBits w1 x) with _ | ⟨b, l⟩ <;> rfl
    refine ⟨v', t1 + t' + 1, (Eval.loop_true (c := fun v : AReg × Rm => isRecO v.1.o) hc0 e1
      e').of_eq ?_ rfl, ?_⟩
    · have hT : (carrSyms w3 (zipC (cmulTruncC s) zs θs')).reverse ++ S1 (cs .T) =
          (carrSyms w3 (zipC (cmulTruncC s) (x :: zs) (y :: θs'))).reverse ++ S (cs .T) := by
        rw [hS1, Function.update_self]
        simp only [zipC, List.zipWith_cons_cons, carrSyms_cons_rec, List.reverse_append,
          List.append_assoc]
      congr 1
      rw [hT]
      funext k
      simp only [hS1, Function.update_apply]
      split_ifs <;> first | rfl | simp_all
    · have hn : ncoef (x :: zs) = x.length + ncoef zs := by simp [ncoef]
      rw [hn, Nat.add_mul, List.length_cons]
      generalize ncoef zs * (cb + 1) = Q at ht' ⊢
      generalize x.length * (cb + 1) = P at ht1 ⊢
      omega

end SubNLogN.Machine.Arith
