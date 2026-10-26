import WP.W4.IO
import WP.W4.PassLoop

/-!
# WP.W4.Body — one mode of the transpose program on the contract's stacks `Loc 4 4`

Stacks: `.inl 0` source, then pass counter `Q`; `.inl 1` destination, temp `T` of `copyBlock`/`dec`;
`.inl 2`/`.inl 3` exponents; `.inr 0..3` = `X Y Z U` (marked on entry, restored on exit).

`body pass E oi oo = prefixP E oi; passLoop pass Q T; suffixP oo` where
* `prefixP`: mark `X Y Z U`, input transfer onto `X`, mark `Q`, copy the counter from `E`;
* `suffixP`: drop `Q`'s mark, output transfer `X → dst`, drop the marks of `Z`, `U`.
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem pushC_runs {K : Type} [DecidableEq K] (k : K) (x : Sym) (S : K → List Sym) :
    RunsIn [] (pushC k x) S (Function.update S k (x :: S k)) 1 :=
  RunsIn.of_evLe (fun r => r) fun r => pushC_evLe [] k x r S

theorem popR_runs {K : Type} [DecidableEq K] (k : K) (S : K → List Sym) :
    RunsIn [] (popR k) S (Function.update S k (S k).tail) 1 :=
  RunsIn.of_evLe (fun _ => (S k).head?) fun r => popR_evLe [] k r S

/-- The contract's stacks. -/
abbrev L44 := Loc 4 4

theorem loc44_ext {S T : L44 → List Sym}
    (h0 : S (.inl 0) = T (.inl 0)) (h1 : S (.inl 1) = T (.inl 1)) (h2 : S (.inl 2) = T (.inl 2))
    (h3 : S (.inl 3) = T (.inl 3)) (h4 : S (.inr 0) = T (.inr 0)) (h5 : S (.inr 1) = T (.inr 1))
    (h6 : S (.inr 2) = T (.inr 2)) (h7 : S (.inr 3) = T (.inr 3)) : S = T := by
  funext k
  rcases k with ⟨i, hi⟩ | ⟨i, hi⟩
  · rcases i with _ | _ | _ | _ | i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · omega
  · rcases i with _ | _ | _ | _ | i
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · omega

/-- Side condition of the passes: `Y`, `Z`, `U` hold their marks. -/
def side44 (S : L44 → List Sym) : Prop :=
  (∃ Y0, S (.inr 1) = Sym.mark :: Y0) ∧ (∃ Z0, S (.inr 2) = Sym.mark :: Z0) ∧
    (∃ U0, S (.inr 3) = Sym.mark :: U0)

theorem side44_update {S : L44 → List Sym} (h : side44 S) (k : L44)
    (hk : k = .inl 0 ∨ k = .inr 0) (x : List Sym) : side44 (Function.update S k x) := by
  obtain ⟨⟨Y0, hY⟩, ⟨Z0, hZ⟩, ⟨U0, hU⟩⟩ := h
  rcases hk with rfl | rfl <;>
  exact ⟨⟨Y0, by rw [Function.update_of_ne (by decide)]; exact hY⟩,
    ⟨Z0, by rw [Function.update_of_ne (by decide)]; exact hZ⟩,
    ⟨U0, by rw [Function.update_of_ne (by decide)]; exact hU⟩⟩

theorem iterate_good {N L : ℕ} {f : List (List Sym) → List (List Sym)}
    (hf : ∀ l, Good N L l → Good N L (f l)) :
    ∀ (n : ℕ) (l : List (List Sym)), Good N L l → Good N L (f^[n] l)
  | 0, _, h => h
  | n + 1, l, h => by
    rw [Function.iterate_succ_apply]
    exact iterate_good hf n (f l) (hf l h)

/-! ## Programs -/

/-- Marks, input transfer, counter copy. -/
def prefixP (E : L44) (oi : Orient) : SProg L44 :=
  .seq (pushC (.inr 0) .mark) (.seq (pushC (.inr 1) .mark) (.seq (pushC (.inr 2) .mark)
    (.seq (pushC (.inr 3) .mark) (.seq (inputP oi (.inl 0) (.inr 0) (.inr 1))
    (.seq (pushC (.inl 0) .mark) (copyBlock E (.inl 0) (.inl 1)))))))

/-- Output transfer and cleanup. -/
def suffixP (oo : Orient) : SProg L44 :=
  .seq (popR (.inl 0)) (.seq (outputP oo (.inr 0) (.inr 1) (.inl 1))
    (.seq (popR (.inr 2)) (popR (.inr 3))))

/-- One mode: `pass` repeated `E`-many times. -/
def body (pass : SProg L44) (E : L44) (oi oo : Orient) : SProg L44 :=
  .seq (prefixP E oi) (.seq (passLoop pass (.inl 0) (.inl 1)) (suffixP oo))

theorem body_closed {pass : SProg L44} (hp : pass.Closed) (E : L44) (oi oo : Orient) :
    (body pass E oi oo).Closed := by
  have h1 := inputP_closed oi (.inl 0 : L44) (.inr 0) (.inr 1)
  have h2 := passLoop_closed hp (.inl 0 : L44) (.inl 1)
  have h3 := outputP_closed oo (.inr 0 : L44) (.inr 1) (.inl 1)
  simp only [Prog.Closed] at h1 h2 h3 ⊢
  simp [body, prefixP, suffixP, Prog.FreeBelow, pushC, popR, copyBlock, moveBlock, moveBits,
    moveBitsBody, moveBitsDup, dupBody, restoreR, skip, pushR, h1, h2, h3]

/-! ## Specifications -/

theorem prefix_spec (E : L44) (hE : E = .inl 2 ∨ E = .inl 3) (oi : Orient)
    (v : List (List Sym)) (hv : ∀ r ∈ v, RecOK r) (rest rE : List Sym) (hrest : BlkTerm rest)
    (hrE : TermOK rE) (k : ℕ) (S : L44 → List Sym) (hS0 : S (.inl 0) = blk oi v ++ rest)
    (hSE : S E = natSyms k ++ rE) :
    RunsIn [] (prefixP E oi) S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (.inr 0) (v.flatten ++ Sym.mark :: S (.inr 0))) (.inr 1) (Sym.mark :: S (.inr 1)))
        (.inr 2) (Sym.mark :: S (.inr 2))) (.inr 3) (Sym.mark :: S (.inr 3)))
        (.inl 0) (natSyms k ++ Sym.mark :: rest))
      (6 * v.flatten.length + 7 * bitLen k + 20) := by
  have hE0 : E ≠ .inl 0 := by rcases hE with rfl | rfl <;> decide
  have hE1 : E ≠ .inl 1 := by rcases hE with rfl | rfl <;> decide
  have hEX : E ≠ .inr 0 := by rcases hE with rfl | rfl <;> decide
  have hEY : E ≠ .inr 1 := by rcases hE with rfl | rfl <;> decide
  have hEZ : E ≠ .inr 2 := by rcases hE with rfl | rfl <;> decide
  have hEU : E ≠ .inr 3 := by rcases hE with rfl | rfl <;> decide
  have r1 := pushC_runs (.inr 0 : L44) Sym.mark S
  set S1 := Function.update S (.inr 0) (Sym.mark :: S (.inr 0)) with hS1
  have r2 := pushC_runs (.inr 1 : L44) Sym.mark S1
  set S2 := Function.update S1 (.inr 1) (Sym.mark :: S1 (.inr 1)) with hS2
  have r3 := pushC_runs (.inr 2 : L44) Sym.mark S2
  set S3 := Function.update S2 (.inr 2) (Sym.mark :: S2 (.inr 2)) with hS3
  have r4 := pushC_runs (.inr 3 : L44) Sym.mark S3
  set S4 := Function.update S3 (.inr 3) (Sym.mark :: S3 (.inr 3)) with hS4
  have r5 := inputP_spec oi (src := (.inl 0 : L44)) (X := .inr 0) (Y := .inr 1) (by decide)
    (by decide) (by decide) [] v hv rest hrest S4 (S (.inr 0)) (S (.inr 1))
    (by simp [hS4, hS3, hS2, hS1, hS0]) (by simp [hS4, hS3, hS2, hS1])
    (by simp [hS4, hS3, hS2, hS1])
  set S5 := Function.update (Function.update S4 (.inl 0) rest) (.inr 0)
    (v.flatten ++ Sym.mark :: S (.inr 0)) with hS5
  have r6 := pushC_runs (.inl 0 : L44) Sym.mark S5
  set S6 := Function.update S5 (.inl 0) (Sym.mark :: S5 (.inl 0)) with hS6
  have h6E : S6 E = (encodeNat k).map Sym.bit ++ rE := by
    simp only [hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, hE0, hEX, hEY, hEZ, hEU,
      if_false]
    exact hSE
  have r7 : RunsIn [] (copyBlock E (.inl 0) (.inl 1)) S6
      (Function.update S6 (.inl 0) ((encodeNat k).map Sym.bit ++ S6 (.inl 0)))
      (7 * bitLen k + 7) :=
    RunsIn.of_eval (f := fun _ => some Sym.mark)
      (fun r => copyBlock_eval hE0 hE1 (by decide) [] r (encodeNat k) rE S6 hrE h6E) (le_of_eq rfl)
  refine RunsIn.of_eq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))) ?_ (by omega)
  apply loc44_ext <;> simp [hS6, hS5, hS4, hS3, hS2, hS1, natSyms]

theorem suffix_spec (oo : Orient) (w : List (List Sym)) (hw : ∀ r ∈ w, RecOK r)
    (rest X0 Y0 Z0 U0 : List Sym) (S : L44 → List Sym) (hQ : S (.inl 0) = Sym.mark :: rest)
    (hX : S (.inr 0) = w.flatten ++ Sym.mark :: X0) (hY : S (.inr 1) = Sym.mark :: Y0)
    (hZ : S (.inr 2) = Sym.mark :: Z0) (hU : S (.inr 3) = Sym.mark :: U0) :
    RunsIn [] (suffixP oo) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S (.inl 0) rest) (.inr 0) X0) (.inr 1) Y0) (.inr 2) Z0) (.inr 3) U0)
        (.inl 1) (blk oo w ++ S (.inl 1)))
      (6 * w.flatten.length + 9) := by
  have r1 := popR_runs (.inl 0 : L44) S
  set S1 := Function.update S (.inl 0) (S (.inl 0)).tail with hS1
  have r2 := outputP_spec oo (X := (.inr 0 : L44)) (Y := .inr 1) (dst := .inl 1) (by decide)
    (by decide) (by decide) [] w hw S1 X0 Y0 (by simp [hS1, hX]) (by simp [hS1, hY])
  set S2 := Function.update (Function.update (Function.update S1 (.inr 0) X0) (.inr 1) Y0)
    (.inl 1) (blk oo w ++ S1 (.inl 1)) with hS2
  have r3 := popR_runs (.inr 2 : L44) S2
  set S3 := Function.update S2 (.inr 2) (S2 (.inr 2)).tail with hS3
  have r4 := popR_runs (.inr 3 : L44) S3
  refine RunsIn.of_eq (r1.seq (r2.seq (r3.seq r4))) ?_ (by omega)
  apply loc44_ext <;> simp [hS3, hS2, hS1, hQ, hZ, hU]

#assert_std_axioms pushC_runs popR_runs loc44_ext side44_update iterate_good body_closed
  prefix_spec suffix_spec

end TMFw.W4
