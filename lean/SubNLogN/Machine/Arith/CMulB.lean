/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulTear

/-!
# AR4b: products with one phase per record (`Arith/CMulB.lean`)

**Scope (honest summary).** The broadcast product kernel `cmulBKernel Pm` and the theorem
`cmulTruncBcast_holds : CMulTruncBcastStmt` (`Machine/Contracts/Arith.lean`). Everything is proved
(no `sorry`); the multiplier enters only through the premise `MulBigContract`.

**Program** (Section 6.3 (`sec:direct-fft-twiddle`), Theorem 6.5 (`thm:direct-fft`): the phase multiplies every coefficient of the
record). Same setup and teardown as `cmulKernel` (`Arith/CMul.lean`). For each record: the phase
coefficient is moved from `θ` to the buffer `WB` (`phaseIn`); before each coefficient of the
record it is copied back onto `θ` (`Lib.copyBlock`) and the coefficient program `coefProg`
(`Arith/CMulOne.lean`) consumes the coefficient and the copy (`cpB`); at the record end the buffer
is drained and the record ends are moved (`phaseOut`). The copy costs `O(w2)` per coefficient,
which the cost term `(M + 1)·(w2 + bitLen s + 1)` of the statement allows.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

variable {Rm : Type}

/-- Move the record's phase from `θ` to the buffer `WB`; peek at `z`. -/
def phaseIn : AProg CK :=
  .seq ((Lib.copyBlock (.inl 1) (cs .WB) (cs .CT)).liftRegs lensO)
    (.seq (drainBits (.inl 1)) (peekO (.inl 0)))

/-- One coefficient: copy the phase back onto `θ`, then the coefficient program. -/
def cpB (Pm : Prog MBLoc (fun _ => Sym) Rm) : Prog CK (fun _ => Sym) (AReg × Rm) :=
  .seq ((((Lib.copyBlock (cs .WB) (.inl 1) (cs .CT)).liftRegs lensO)).liftRegs (Lens.fst AReg Rm))
    (coefProg Pm)

/-- End of a record: drain the buffer, then the record ends. -/
def phaseOut : AProg CK := .seq (drainBits (cs .WB)) recTail

/-- One record. -/
def recBodyB (Pm : Prog MBLoc (fun _ => Sym) Rm) : Prog CK (fun _ => Sym) (AReg × Rm) :=
  .seq (phaseIn.liftRegs (Lens.fst AReg Rm))
    (.seq (coefLoop (cpB Pm)) (phaseOut.liftRegs (Lens.fst AReg Rm)))

/-- All records. -/
def recLoopB (Pm : Prog MBLoc (fun _ => Sym) Rm) : Prog CK (fun _ => Sym) (AReg × Rm) :=
  .loop (fun v => isRecO v.1.o) (recBodyB Pm)

/-- **The broadcast product kernel.** -/
def cmulBKernel (Pm : Prog MBLoc (fun _ => Sym) Rm) : Prog CK (fun _ => Sym) (AReg × Rm) :=
  .seq (cmulSetup.liftRegs (Lens.fst AReg Rm))
  (.seq ((peekO (.inl 0)).liftRegs (Lens.fst AReg Rm))
  (.seq (recLoopB Pm) (cmulTeardown.liftRegs (Lens.fst AReg Rm))))

/-- The stacks agree with `S0` except on `z` and the output stack. -/
def FrameB (S S0 : CK → List Sym) : Prop := ∀ k, k ≠ .inl 0 → k ≠ cs .T → S k = S0 k

/-- **Coefficient-level contract** with the `θ` side untouched. -/
def CoefSpecB (cp : Prog CK (fun _ => Sym) (AReg × Rm)) (w1 w3 : ℕ) (g : CInt → CInt) (cb : ℕ)
    (S0 : CK → List Sym) : Prop :=
  ∀ (a : CInt) (Lz : List Sym) (v : AReg × Rm) (S : CK → List Sym),
    FitsTwos w1 a.1 → FitsTwos w1 a.2 → FrameB S S0 →
    S (.inl 0) = (coefBits w1 a).map Sym.bit ++ Lz →
    ∃ (v' : AReg × Rm) (t : ℕ), v'.1.o = Lz.head? ∧ Eval [] cp ⟨v, S⟩
      ⟨v', Function.update (Function.update S (.inl 0) Lz) (cs .T)
        ((coefBits w3 (g a)).reverse.map Sym.bit ++ S (cs .T))⟩ t ∧ t ≤ cb

theorem coefLoopB_eval {cp : Prog CK (fun _ => Sym) (AReg × Rm)} {w1 w3 cb : ℕ}
    {g : CInt → CInt} {S0 : CK → List Sym} (hw1 : 1 ≤ w1)
    (hspec : CoefSpecB cp w1 w3 g cb S0) :
    ∀ (xs : List CInt) (Lz : List Sym) (v : AReg × Rm) (S : CK → List Sym),
      (∀ a ∈ xs, FitsTwos w1 a.1 ∧ FitsTwos w1 a.2) → FrameB S S0 →
      isBitO Lz.head? = false → S (.inl 0) = (crecBits w1 xs).map Sym.bit ++ Lz →
      v.1.o = (S (.inl 0)).head? →
      ∃ (v' : AReg × Rm) (t : ℕ), v'.1.o = Lz.head? ∧ Eval [] (coefLoop cp) ⟨v, S⟩
        ⟨v', Function.update (Function.update S (.inl 0) Lz) (cs .T)
          ((crecBits w3 (xs.map g)).reverse.map Sym.bit ++ S (cs .T))⟩ t ∧
        t ≤ xs.length * (cb + 1) + 1
  | [], Lz, v, S, _, _, hL, hz, hv => by
    simp only [crecBits, List.flatMap_nil, List.map_nil, List.nil_append] at hz
    refine ⟨v, 1, by rw [hv, hz], (Eval.loop_false (c := fun v : AReg × Rm => isBitO v.1.o)
      (by show isBitO v.1.o = false; rw [hv, hz]; exact hL)).of_eq ?_ rfl, by simp⟩
    simp only [List.map_nil, crecBits, List.flatMap_nil, List.reverse_nil, List.nil_append]
    rw [← hz, Function.update_eq_self, Function.update_eq_self]
  | a :: xs, Lz, v, S, hxs, hfr, hL, hz, hv => by
    have ha := hxs a List.mem_cons_self
    have hz' : S (.inl 0) = (coefBits w1 a).map Sym.bit ++
        ((crecBits w1 xs).map Sym.bit ++ Lz) := by
      rw [hz, crecBits_cons', List.map_append, List.append_assoc]
    obtain ⟨v1, t1, hv1, e1, ht1⟩ := hspec a _ v S ha.1 ha.2 hfr hz'
    set S1 := Function.update (Function.update S (.inl 0) ((crecBits w1 xs).map Sym.bit ++ Lz))
      (cs .T) ((coefBits w3 (g a)).reverse.map Sym.bit ++ S (cs .T)) with hS1
    obtain ⟨v', t', hv', e', ht'⟩ := coefLoopB_eval hw1 hspec xs Lz v1 S1
      (fun a' h' => hxs a' (List.mem_cons_of_mem _ h'))
      (fun k h1 h2 => by
        rw [hS1, Function.update_of_ne h2, Function.update_of_ne h1]
        exact hfr k h1 h2)
      hL (by simp [hS1]) (by rw [hv1]; simp [hS1])
    have hc0 : isBitO v.1.o = true := by
      rw [hv, hz']
      obtain ⟨k, rfl⟩ : ∃ k, w1 = k + 1 := ⟨w1 - 1, by omega⟩
      simp [coefBits, K1.twosBits_succ, isBitO]
    refine ⟨v', t1 + t' + 1, hv', (Eval.loop_true (c := fun v : AReg × Rm => isBitO v.1.o)
      hc0 e1 e').of_eq ?_ rfl, ?_⟩
    · have hT : (crecBits w3 (xs.map g)).reverse.map Sym.bit ++ S1 (cs .T) =
          (crecBits w3 ((a :: xs).map g)).reverse.map Sym.bit ++ S (cs .T) := by
        rw [hS1, Function.update_self, List.map_cons, crecBits_cons', List.reverse_append,
          List.map_append, List.append_assoc]
      congr 1
      rw [hT]
      funext k
      simp only [hS1, Function.update_apply]
      split_ifs <;> rfl
    · simp only [List.length_cons, Nat.add_mul, one_mul]
      generalize xs.length * (cb + 1) = Q at ht' ⊢
      omega

theorem coefBits_length (w : ℕ) (c : CInt) : (coefBits w c).length = 2 * w := by
  simp [coefBits, K1.length_twosBits]; ring

set_option maxHeartbeats 4000000 in
/-- **One broadcast coefficient**: the coefficient-level contract of `cpB Pm` relative to stacks
`S1` whose buffer `WB` holds the record's phase `t`. -/
theorem cpB_spec {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ} (hPm : SpecMulBig Pm Cm)
    {w1 w2 w3 s W h : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2) (hW : W = 2 * max w1 w2 + 1)
    (hsh : min s W + h = W) (t : CInt) (ht1 : FitsTwos w2 t.1) (ht2 : FitsTwos w2 t.2)
    (S1 : CK → List Sym) (hWk : ∀ c, isWork c = true → S1 (cs c) = [])
    (hG : ∀ g, S1 (.inr (.inr g)) = [])
    (hR1 : S1 (cs .R1) = List.replicate w1 .mark) (hRt : S1 (cs .Rt) = List.replicate w2 .mark)
    (hRW : S1 (cs .RW) = List.replicate W .mark)
    (hRs : S1 (cs .Rs) = List.replicate (min s W) .mark)
    (hRh : S1 (cs .Rh) = List.replicate h .mark) (hR2 : S1 (cs .R2) = List.replicate w3 .mark)
    (hWB : S1 (cs .WB) = (coefBits w2 t).map Sym.bit) :
    CoefSpecB (cpB Pm) w1 w3 (fun a => cmulTruncC s a t)
      (14 * w2 + 7 + coefBound Cm w1 w2 w3) S1 := by
  intro a Lz v S ha1 ha2 hfr hz
  have hS : ∀ k, k ≠ .inl 0 → k ≠ cs .T → S k = S1 k := hfr
  have e1 := Lib.copyBlock_eval (src := cs .WB) (dst := (.inl 1 : CK)) (tmp := cs .CT)
    (by decide) (by decide) (by decide) [] (lensO.get v.1) (coefBits w2 t) [] S aTermOK_nil
    (by rw [hS _ (by decide) (by decide), hWB, List.append_nil])
  have e1' := Eval.liftRegs (Lens.fst AReg Rm) (Eval.liftRegs lensO e1 v.1 rfl) v rfl
  set S' := Function.update S (.inl 1) ((coefBits w2 t).map Sym.bit ++ S (.inl 1)) with hS'
  have g' : ∀ k, k ≠ .inl 0 → k ≠ .inl 1 → k ≠ cs .T → S' k = S1 k := fun k h0 h1 hT => by
    rw [hS', Function.update_of_ne h1, hS k h0 hT]
  obtain ⟨v2, t2, hv2, e2, ht2'⟩ := coefProg_eval hPm hw1 hw2 hW hsh a t ha1 ha2 ht1 ht2 Lz
    (S (.inl 1)) ((Lens.fst AReg Rm).set v (lensO.set v.1 (some .mark))) S'
    (fun c hc => by
      rw [g' _ (by simp) (by simp) (by intro e; cases e; simp [isWork] at hc), hWk c hc])
    (fun g => by rw [g' _ (by simp) (by simp) (by simp), hG])
    (by rw [g' _ (by decide) (by decide) (by decide), hR1])
    (by rw [g' _ (by decide) (by decide) (by decide), hRt])
    (by rw [g' _ (by decide) (by decide) (by decide), hRW])
    (by rw [g' _ (by decide) (by decide) (by decide), hRs])
    (by rw [g' _ (by decide) (by decide) (by decide), hRh])
    (by rw [g' _ (by decide) (by decide) (by decide), hR2])
    (by rw [hS', Function.update_of_ne (by decide)]; exact hz)
    (by rw [hS', Function.update_self])
  refine ⟨v2, _, hv2, (Eval.seq e1' e2).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    simp only [hS', Function.update_apply]
    split_ifs <;> simp_all
  · rw [coefBits_length] at *
    omega
