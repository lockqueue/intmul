import WP.W9cS.Count

/-!
# WP.W9cS.Hdr — copy the 4th field of a header stack

A header stack holds `natSyms f₀ ++ mark :: natSyms f₁ ++ mark :: …`. `getF4 C0 RS TMP Q` skips
the first three fields onto `TMP` (each as `mark :: bits.reverse`), copies the 4th field onto `RS`
(`copyBlock`, temp `Q`), and restores the skipped fields. Only `RS` changes.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.W4 Computability

variable {K : Type}

/-- Skip one header field of `src` onto `tmp` (as `mark :: bits.reverse`). -/
def skipF (src tmp : K) : SProg K := .seq (moveBlock src tmp) (.seq (popR src) (pushR tmp))

/-- Undo `skipF`. -/
def unskipF (tmp src : K) : SProg K := .seq (popR tmp) (.seq (pushR src) (moveBlock tmp src))

/-- Copy the 4th header field of `C0` onto `RS`. -/
def getF4 (C0 RS TMP Q : K) : SProg K :=
  .seq (skipF C0 TMP) (.seq (skipF C0 TMP) (.seq (skipF C0 TMP) (.seq (copyBlock C0 RS Q)
    (.seq (unskipF TMP C0) (.seq (unskipF TMP C0) (unskipF TMP C0))))))

theorem getF4_closed (C0 RS TMP Q : K) : (getF4 C0 RS TMP Q).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, getF4, skipF, unskipF, moveBlock, moveBits, moveBitsBody,
    copyBlock, moveBitsDup, dupBody, restoreR, skip, pushC, pushR, popR]

variable [DecidableEq K]

theorem skipF_spec {src tmp : K} (hst : src ≠ tmp) (ρ : List (SProg K)) (n : ℕ)
    (rest : List Sym) (S : K → List Sym) (hS : S src = natSyms n ++ Sym.mark :: rest) :
    RunsIn ρ (skipF src tmp) S
      (Function.update (Function.update S src rest) tmp
        (Sym.mark :: ((encodeNat n).reverse.map Sym.bit ++ S tmp))) (3 * bitLen n + 6) := by
  refine RunsIn.of_evLe (fun _ => some Sym.mark) fun v => ?_
  have e1 := moveBlock_eval hst ρ v (encodeNat n) (Sym.mark :: rest) S (TermOK.cons (by rfl) _) hS
  set S1 := Function.update (Function.update S src (Sym.mark :: rest)) tmp
    ((encodeNat n).reverse.map Sym.bit ++ S tmp) with hS1
  have e2 := popR_evLe ρ src (Sym.mark :: rest).head? S1
  rw [show S1 src = Sym.mark :: rest by rw [hS1, Function.update_of_ne hst, Function.update_self]]
    at e2
  set S2 := Function.update S1 src (Sym.mark :: rest).tail with hS2
  have e3 : EvLe ρ (pushR tmp) (Sym.mark :: rest).head? S2 (some Sym.mark)
      (Function.update S2 tmp (Sym.mark :: S2 tmp)) 1 :=
    ⟨1, (Eval.push ρ tmp (fun r => r.getD .sep) (some Sym.mark) S2).of_eq rfl rfl, le_rfl⟩
  refine ((EvLe.of_eval e1 le_rfl).seq (e2.seq e3)).of_eq rfl ?_ (by simp only [bitLen]; omega)
  funext k
  simp only [hS2, hS1, Function.update_apply, List.tail_cons]
  split_ifs <;> simp_all

theorem unskipF_spec {src tmp : K} (hst : src ≠ tmp) (ρ : List (SProg K)) (n : ℕ)
    (Y rest : List Sym) (S : K → List Sym) (hY : TermOK Y)
    (hT : S tmp = Sym.mark :: ((encodeNat n).reverse.map Sym.bit ++ Y)) (hS : S src = rest) :
    RunsIn ρ (unskipF tmp src) S
      (Function.update (Function.update S tmp Y) src (natSyms n ++ Sym.mark :: rest))
      (3 * bitLen n + 6) := by
  refine RunsIn.of_evLe (fun _ => Y.head?) fun v => ?_
  have e1 := popR_evLe ρ tmp v S
  rw [hT] at e1
  simp only [List.head?_cons, List.tail_cons] at e1
  set S1 := Function.update S tmp ((encodeNat n).reverse.map Sym.bit ++ Y) with hS1
  have e2 : EvLe ρ (pushR src) (some Sym.mark) S1 (some Sym.mark)
      (Function.update S1 src (Sym.mark :: S1 src)) 1 :=
    ⟨1, (Eval.push ρ src (fun r => r.getD .sep) (some Sym.mark) S1).of_eq rfl rfl, le_rfl⟩
  set S2 := Function.update S1 src (Sym.mark :: S1 src) with hS2
  have e3 := moveBlock_eval (Ne.symm hst) ρ (some Sym.mark) (encodeNat n).reverse Y S2 hY
    (by rw [hS2, Function.update_of_ne (Ne.symm hst), hS1, Function.update_self])
  refine (e1.seq (e2.seq (EvLe.of_eval e3 le_rfl))).of_eq rfl ?_
    (by simp only [bitLen, List.length_reverse]; omega)
  funext k
  simp only [hS2, hS1, Function.update_apply, List.reverse_reverse, natSyms]
  split_ifs <;> simp_all

/-- **Copy the 4th header field.** -/
theorem getF4_spec {C0 RS TMP Q : K} (h1 : C0 ≠ RS) (h2 : C0 ≠ TMP) (h3 : C0 ≠ Q) (h4 : RS ≠ TMP)
    (h5 : RS ≠ Q) (_h6 : TMP ≠ Q) (ρ : List (SProg K)) (a b c d : ℕ) (rest T0 : List Sym)
    (S : K → List Sym)
    (hC : S C0 = natSyms a ++ Sym.mark :: (natSyms b ++ Sym.mark :: (natSyms c ++ Sym.mark ::
      (natSyms d ++ Sym.mark :: rest))))
    (hT : S TMP = Sym.mark :: T0) :
    RunsIn ρ (getF4 C0 RS TMP Q) S (Function.update S RS (natSyms d ++ S RS))
      (6 * (bitLen a + bitLen b + bitLen c) + 7 * bitLen d + 43) := by
  have r1 := skipF_spec h2 ρ a _ S hC
  set S1 := Function.update (Function.update S C0 (natSyms b ++ Sym.mark :: (natSyms c ++
    Sym.mark :: (natSyms d ++ Sym.mark :: rest)))) TMP
    (Sym.mark :: ((encodeNat a).reverse.map Sym.bit ++ S TMP)) with hS1
  have r2 := skipF_spec h2 ρ b _ S1 (by rw [hS1, Function.update_of_ne h2, Function.update_self])
  set S2 := Function.update (Function.update S1 C0 (natSyms c ++ Sym.mark :: (natSyms d ++
    Sym.mark :: rest))) TMP (Sym.mark :: ((encodeNat b).reverse.map Sym.bit ++ S1 TMP)) with hS2
  have r3 := skipF_spec h2 ρ c _ S2 (by rw [hS2, Function.update_of_ne h2, Function.update_self])
  set S3 := Function.update (Function.update S2 C0 (natSyms d ++ Sym.mark :: rest)) TMP
    (Sym.mark :: ((encodeNat c).reverse.map Sym.bit ++ S2 TMP)) with hS3
  have r4 : RunsIn ρ (copyBlock C0 RS Q) S3
      (Function.update S3 RS ((encodeNat d).map Sym.bit ++ S3 RS)) (7 * bitLen d + 7) :=
    RunsIn.of_eval (f := fun _ => some Sym.mark) (fun v => copyBlock_eval h1 h3 h5 ρ v
      (encodeNat d) (Sym.mark :: rest) S3 (TermOK.cons (by rfl) _)
      (by rw [hS3, Function.update_of_ne h2, Function.update_self]; rfl)) (le_of_eq rfl)
  set S4 := Function.update S3 RS ((encodeNat d).map Sym.bit ++ S3 RS) with hS4
  have hS4T : S4 TMP = Sym.mark :: ((encodeNat c).reverse.map Sym.bit ++ S2 TMP) := by
    rw [hS4, Function.update_of_ne (Ne.symm h4), hS3, Function.update_self]
  have r5 := unskipF_spec h2 ρ c (S2 TMP) _ S4
    (by rw [hS2, Function.update_self]; exact TermOK.cons (by rfl) _) hS4T rfl
  set S5 := Function.update (Function.update S4 TMP (S2 TMP)) C0
    (natSyms c ++ Sym.mark :: S4 C0) with hS5
  have hS5T : S5 TMP = Sym.mark :: ((encodeNat b).reverse.map Sym.bit ++ S1 TMP) := by
    rw [hS5, Function.update_of_ne (Ne.symm h2), Function.update_self, hS2, Function.update_self]
  have r6 := unskipF_spec h2 ρ b (S1 TMP) _ S5
    (by rw [hS1, Function.update_self]; exact TermOK.cons (by rfl) _) hS5T rfl
  set S6 := Function.update (Function.update S5 TMP (S1 TMP)) C0
    (natSyms b ++ Sym.mark :: S5 C0) with hS6
  have hS6T : S6 TMP = Sym.mark :: ((encodeNat a).reverse.map Sym.bit ++ S TMP) := by
    rw [hS6, Function.update_of_ne (Ne.symm h2), Function.update_self, hS1, Function.update_self]
  have r7 := unskipF_spec h2 ρ a (S TMP) _ S6 (by rw [hT]; exact TermOK.cons (by rfl) _) hS6T rfl
  refine RunsIn.of_eq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))) ?_ (by omega)
  funext k
  simp only [hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, natSyms]
  split_ifs <;> simp_all [natSyms]

#assert_std_axioms getF4_closed skipF_spec unskipF_spec getF4_spec

end WP.W9c
