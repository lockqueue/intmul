/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulCoef

/-!
# AR, products: the output phase of one coefficient (`Arith/CMulPost.lean`)

**Scope (honest summary).** `postAll` empties the magnitude stacks, computes the two output
fields from the four products (`halfProg`, `Arith/CMulHalf.lean`), pops the sign stacks and peeks
at `z`. `postAll_eval` is exact; all work stacks are empty afterwards (`clearW`). Everything is
proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-- All work stacks emptied. -/
def clearW (S : CK → List Sym) : CK → List Sym := fun k =>
  match k with
  | .inr (.inl c) => if isWork c then [] else S k
  | _ => S k

theorem clearW_update_work (S : CK → List Sym) (c : CS) (hc : isWork c = true) (x : List Sym) :
    clearW (Function.update S (cs c) x) = clearW S := by
  funext k
  rcases k with i | d | g
  · simp [clearW]
  · by_cases h : d = c
    · subst h; simp [clearW, hc]
    · simp [clearW, Function.update_apply, h]
  · simp [clearW]

theorem clearW_update_ne (S : CK → List Sym) (k0 : CK) (hk : ∀ c, isWork c = true → k0 ≠ cs c)
    (x : List Sym) : clearW (Function.update S k0 x) = Function.update (clearW S) k0 x := by
  funext k
  rcases k with i | d | g
  · simp [clearW, Function.update_apply]
  · by_cases hd : isWork d = true
    · have hne : cs d ≠ k0 := fun e => hk d hd e.symm
      simp [clearW, Function.update_apply, hd, hne]
    · simp [clearW, Function.update_apply, hd]
  · simp [clearW, Function.update_apply]

theorem clearW_eq (S : CK → List Sym) (hW : ∀ c, isWork c = true → S (cs c) = []) :
    clearW S = S := by
  funext k
  rcases k with i | d | g
  · rfl
  · show (if isWork d = true then [] else S (cs d)) = S (cs d)
    by_cases hd : isWork d = true
    · rw [if_pos hd, hW d hd]
    · rw [if_neg hd]
  · rfl

/-- The output phase. -/
def postAll : AProg CK :=
  .seq (drainBits (cs .Ma)) (.seq (drainBits (cs .Mb)) (.seq (drainBits (cs .Mc))
  (.seq (drainBits (cs .Md))
  (.seq (halfProg true (hrι .P1 .P2 .Sa .Sc .Sb .Sd))
  (.seq (halfProg false (hrι .P3 .P4 .Sa .Sd .Sb .Sc))
  (.seq (drop1 (cs .Sa)) (.seq (drop1 (cs .Sb)) (.seq (drop1 (cs .Sc))
  (.seq (drop1 (cs .Sd)) (peekO (.inl 0)))))))))))

/-- The two output fields of one coefficient, as pushed on the output stack (so reversed): the
imaginary part on top of the real part. -/
def postOut (w3 s' ma mb mc md : ℕ) (sa sb sc sd : Bool) : List Sym :=
  (twosBits w3 (tdivPow (if false then sgnV (xor sa sd) (ma * md) - sgnV (xor sb sc) (mb * mc)
      else sgnV (xor sa sd) (ma * md) + sgnV (xor sb sc) (mb * mc)) s')).reverse.map Sym.bit ++
  (twosBits w3 (tdivPow (if true then sgnV (xor sa sc) (ma * mc) - sgnV (xor sb sd) (mb * md)
      else sgnV (xor sa sc) (ma * mc) + sgnV (xor sb sd) (mb * md)) s')).reverse.map Sym.bit

set_option maxHeartbeats 8000000 in
/-- **The output phase**, exact. -/
theorem postAll_eval {W w3 s' h : ℕ} (hW : 1 ≤ W) (hsh : s' + h = W)
    (ma mb mc md : ℕ) (sa sb sc sd : Bool)
    (hp1 : ma * mc < 2 ^ W) (hp2 : mb * md < 2 ^ W) (hp3 : ma * md < 2 ^ W)
    (hp4 : mb * mc < 2 ^ W)
    (hfit1 : FitsTwos W (if true then sgnV (xor sa sc) (ma * mc) - sgnV (xor sb sd) (mb * md)
      else sgnV (xor sa sc) (ma * mc) + sgnV (xor sb sd) (mb * md)))
    (hfit2 : FitsTwos W (if false then sgnV (xor sa sd) (ma * md) - sgnV (xor sb sc) (mb * mc)
      else sgnV (xor sa sd) (ma * md) + sgnV (xor sb sc) (mb * mc)))
    (v : AReg) (S : CK → List Sym)
    (hMa : S (cs .Ma) = natSyms ma) (hMb : S (cs .Mb) = natSyms mb)
    (hMc : S (cs .Mc) = natSyms mc) (hMd : S (cs .Md) = natSyms md)
    (hSa : S (cs .Sa) = [Sym.bit sa]) (hSb : S (cs .Sb) = [Sym.bit sb])
    (hSc : S (cs .Sc) = [Sym.bit sc]) (hSd : S (cs .Sd) = [Sym.bit sd])
    (hP1 : S (cs .P1) = natSyms (ma * mc)) (hP2 : S (cs .P2) = natSyms (mb * md))
    (hP3 : S (cs .P3) = natSyms (ma * md)) (hP4 : S (cs .P4) = natSyms (mb * mc))
    (hX : S (cs .X) = []) (hA : S (cs .A) = []) (hB : S (cs .B) = []) (hTm : S (cs .Tm) = [])
    (hU : S (cs .U) = []) (hV1 : S (cs .V1) = []) (hV2 : S (cs .V2) = [])
    (hRr : S (cs .Rr) = []) (hVs : S (cs .Vs) = [])
    (hRW : S (cs .RW) = List.replicate W .mark) (hRs : S (cs .Rs) = List.replicate s' .mark)
    (hRh : S (cs .Rh) = List.replicate h .mark) (hR2 : S (cs .R2) = List.replicate w3 .mark) :
    ∃ v' : AReg, v'.o = (S (.inl 0)).head? ∧ Eval [] postAll ⟨v, S⟩
      ⟨v', Function.update (clearW S) (cs .T) (postOut w3 s' ma mb mc md sa sb sc sd ++ S (cs .T))⟩
      (3 * (bitLen ma + bitLen mb + bitLen mc + bitLen md) +
        2 * (50 * W + 25 + fieldCost s' h w3) + 13) := by
  set D1 := Function.update S (cs .Ma) [] with hD1
  set D2 := Function.update D1 (cs .Mb) [] with hD2
  set D3 := Function.update D2 (cs .Mc) [] with hD3
  set D4 := Function.update D3 (cs .Md) [] with hD4
  obtain ⟨u1, e1⟩ : ∃ u, Eval [] (drainBits (cs .Ma)) ⟨v, S⟩ ⟨u, D1⟩ (3 * bitLen ma + 2) :=
    ⟨_, drainBits_eval (B := cs .Ma) (encodeNat ma) [] v S aTermOK_nil
      (by rw [hMa, List.append_nil]; rfl)⟩
  obtain ⟨u2, e2⟩ : ∃ u, Eval [] (drainBits (cs .Mb)) ⟨u1, D1⟩ ⟨u, D2⟩ (3 * bitLen mb + 2) :=
    ⟨_, drainBits_eval (B := cs .Mb) (encodeNat mb) [] u1 D1 aTermOK_nil
      (by simp [hD1, hMb, natSyms])⟩
  obtain ⟨u3, e3⟩ : ∃ u, Eval [] (drainBits (cs .Mc)) ⟨u2, D2⟩ ⟨u, D3⟩ (3 * bitLen mc + 2) :=
    ⟨_, drainBits_eval (B := cs .Mc) (encodeNat mc) [] u2 D2 aTermOK_nil
      (by simp [hD2, hD1, hMc, natSyms])⟩
  obtain ⟨u4, e4⟩ : ∃ u, Eval [] (drainBits (cs .Md)) ⟨u3, D3⟩ ⟨u, D4⟩ (3 * bitLen md + 2) :=
    ⟨_, drainBits_eval (B := cs .Md) (encodeNat md) [] u3 D3 aTermOK_nil
      (by simp [hD3, hD2, hD1, hMd, natSyms])⟩
  have g4 : ∀ c : CS, c ≠ .Ma → c ≠ .Mb → c ≠ .Mc → c ≠ .Md → D4 (cs c) = S (cs c) :=
    fun c h1 h2 h3 h4 => by simp [hD4, hD3, hD2, hD1, h1, h2, h3, h4]
  obtain ⟨u5, e5⟩ := halfProg_eval true hrιRe_inj hW hsh hp1 hp2 sa sc sb sd hfit1
    [] [] [] [] [] [] [] [] [] [] u4 D4 aTermOK_nil aTermOK_nil aHead_nil aHead_nil aHead_nil
    aHead_nil
    (by show (D4 (cs .X)).head? ≠ _
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hX]; exact aHead_nil)
    (by show TermOK (D4 (cs .U))
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hU]; exact aTermOK_nil)
    (by show TermOK (D4 (cs .Rr))
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hRr]; exact aTermOK_nil)
    (by show TermOK (D4 (cs .A))
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hA]; exact aTermOK_nil)
    (by show TermOK (D4 (cs .B))
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hB]; exact aTermOK_nil)
    (by show D4 (cs .P1) = _
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hP1, List.append_nil])
    (by show D4 (cs .P2) = _
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hP2, List.append_nil])
    (by show D4 (cs .Sa) = _; rw [g4 _ (by decide) (by decide) (by decide) (by decide), hSa])
    (by show D4 (cs .Sc) = _; rw [g4 _ (by decide) (by decide) (by decide) (by decide), hSc])
    (by show D4 (cs .Sb) = _; rw [g4 _ (by decide) (by decide) (by decide) (by decide), hSb])
    (by show D4 (cs .Sd) = _; rw [g4 _ (by decide) (by decide) (by decide) (by decide), hSd])
    (by show D4 (cs .RW) = _
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hRW, List.append_nil])
    (by show D4 (cs .Rs) = _
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hRs, List.append_nil])
    (by show D4 (cs .Rh) = _
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hRh, List.append_nil])
    (by show D4 (cs .R2) = _
        rw [g4 _ (by decide) (by decide) (by decide) (by decide), hR2, List.append_nil])
  set D5 := Function.update (Function.update (Function.update D4 (cs .P1) []) (cs .P2) []) (cs .T)
    ((twosBits w3 (tdivPow (if true then sgnV (xor sa sc) (ma * mc) - sgnV (xor sb sd) (mb * md)
      else sgnV (xor sa sc) (ma * mc) + sgnV (xor sb sd) (mb * md)) s')).reverse.map Sym.bit ++
      S (cs .T)) with hD5
  have h4T : D4 (cs .T) = S (cs .T) := g4 _ (by decide) (by decide) (by decide) (by decide)
  have e5' : Eval [] (halfProg true (hrι .P1 .P2 .Sa .Sc .Sb .Sd)) ⟨u4, D4⟩ ⟨u5, D5⟩
      (50 * W + 25 + fieldCost s' h w3) := by
    refine e5.of_eq ?_ rfl
    simp only [hrι, h4T] <;> rfl
  have g5 : ∀ c : CS, c ≠ .Ma → c ≠ .Mb → c ≠ .Mc → c ≠ .Md → c ≠ .P1 → c ≠ .P2 → c ≠ .T →
      D5 (cs c) = S (cs c) :=
    fun c h1 h2 h3 h4 h5 h6 h7 => by
      simp [hD5, h5, h6, h7]; exact g4 c h1 h2 h3 h4
  obtain ⟨u6, e6⟩ := halfProg_eval false hrιIm_inj hW hsh hp3 hp4 sa sd sb sc hfit2
    [] [] [] [] [] [] [] [] [] [] u5 D5 aTermOK_nil aTermOK_nil aHead_nil aHead_nil aHead_nil
    aHead_nil
    (by show (D5 (cs .X)).head? ≠ _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hX]; exact aHead_nil)
    (by show TermOK (D5 (cs .U))
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hU]; exact aTermOK_nil)
    (by show TermOK (D5 (cs .Rr))
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hRr]; exact aTermOK_nil)
    (by show TermOK (D5 (cs .A))
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hA]; exact aTermOK_nil)
    (by show TermOK (D5 (cs .B))
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hB]; exact aTermOK_nil)
    (by show D5 (cs .P3) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hP3, List.append_nil])
    (by show D5 (cs .P4) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hP4, List.append_nil])
    (by show D5 (cs .Sa) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hSa])
    (by show D5 (cs .Sd) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hSd])
    (by show D5 (cs .Sb) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hSb])
    (by show D5 (cs .Sc) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hSc])
    (by show D5 (cs .RW) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hRW, List.append_nil])
    (by show D5 (cs .Rs) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hRs, List.append_nil])
    (by show D5 (cs .Rh) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hRh, List.append_nil])
    (by show D5 (cs .R2) = _
        rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hR2, List.append_nil])
  set D6 := Function.update (Function.update (Function.update D5 (cs .P3) []) (cs .P4) []) (cs .T)
    ((twosBits w3 (tdivPow (if false then sgnV (xor sa sd) (ma * md) - sgnV (xor sb sc) (mb * mc)
      else sgnV (xor sa sd) (ma * md) + sgnV (xor sb sc) (mb * mc)) s')).reverse.map Sym.bit ++
      D5 (cs .T)) with hD6
  have e6' : Eval [] (halfProg false (hrι .P3 .P4 .Sa .Sd .Sb .Sc)) ⟨u5, D5⟩ ⟨u6, D6⟩
      (50 * W + 25 + fieldCost s' h w3) := by
    refine e6.of_eq ?_ rfl
    simp only [hrι] <;> rfl
  have g6 : ∀ c : CS, c ≠ .P3 → c ≠ .P4 → c ≠ .T → D6 (cs c) = D5 (cs c) :=
    fun c h1 h2 h3 => by simp [hD6, h1, h2, h3]
  have hS5 : ∀ c : CS, c = .Sa ∨ c = .Sb ∨ c = .Sc ∨ c = .Sd → D6 (cs c) = S (cs c) := by
    intro c hc
    rw [g6 c (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)]
    exact g5 c (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)
      (by rcases hc with h | h | h | h <;> subst h <;> decide)
  have e7 := eval_drop1 (cs .Sa) u6 D6 (Sym.bit sa) [] (by rw [hS5 _ (by simp), hSa])
  set D7 := Function.update D6 (cs .Sa) [] with hD7
  have e8 := eval_drop1 (cs .Sb) u6 D7 (Sym.bit sb) []
    (by rw [hD7, Function.update_of_ne (by decide), hS5 _ (by simp), hSb])
  set D8 := Function.update D7 (cs .Sb) [] with hD8
  have e9 := eval_drop1 (cs .Sc) u6 D8 (Sym.bit sc) []
    (by rw [hD8, Function.update_of_ne (by decide), hD7, Function.update_of_ne (by decide),
      hS5 _ (by simp), hSc])
  set D9 := Function.update D8 (cs .Sc) [] with hD9
  have e10 := eval_drop1 (cs .Sd) u6 D9 (Sym.bit sd) []
    (by rw [hD9, Function.update_of_ne (by decide), hD8, Function.update_of_ne (by decide), hD7,
      Function.update_of_ne (by decide), hS5 _ (by simp), hSd])
  set D10 := Function.update D9 (cs .Sd) [] with hD10
  have e11 := eval_peekO (.inl 0) u6 D10
  refine ⟨{ u6 with o := (D10 (.inl 0)).head? }, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
    (Eval.seq e4 (Eval.seq e5' (Eval.seq e6' (Eval.seq e7 (Eval.seq e8 (Eval.seq e9
    (Eval.seq e10 e11)))))))))).of_eq ?_ ?_⟩
  · show (D10 (.inl 0)).head? = _
    simp [hD10, hD9, hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1]
  · congr 1
    funext k
    rcases k with i | d | g
    · simp [hD10, hD9, hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, clearW]
    · cases d <;> simp [hD10, hD9, hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, clearW, isWork,
        postOut, hX, hA, hB, hTm, hU, hV1, hV2, hRr, hVs, List.append_assoc]
    · simp [hD10, hD9, hD8, hD7, hD6, hD5, hD4, hD3, hD2, hD1, clearW]
  · ring

end SubNLogN.Machine.Arith
