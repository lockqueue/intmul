/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreKDefs
import SubNLogN.Machine.Arith.Shift
import SubNLogN.Machine.Arith.CMulPure

/-!
# The rotation kernel (`Machine/Layer/DrvPreKRot.lean`)

**Scope (honest summary).** `rotIPow_holds : RotIPowStmt` (`Machine/Layer/DrvPreKDefs.lean`): every
coefficient of a record array is multiplied by `i^e`. Everything is proved. Helpers
live in `SubNLogN.Machine.Layer.DrvPreK.RotAux`.

## Program
One coefficient is one `2w`-bit field of the AR array driver (`Arith/Driver.lean`): the field
`twosBits (w + w) (packC w c)` is `coefBits w c = twosBits w re ++ twosBits w im`. The field program
`rotField` loads the real part onto `A` and the imaginary part onto `B` (ruler `Rh` of `w` marks,
both reversed); then it emits the two output components onto the output buffer `T` (ruler `R2`).
Each output component is one loaded part, moved onto `Rs` (least significant bit on top,
complemented when the component is negated) and emitted with carry `1` when negated
(`~q + 1 = -q`, `emitOut_len`, `twosBits_map_not`). The kernel `rotCore` reuses the shift kernel's
delimiters, rulers and teardown (`Arith/Shift.lean`, both rulers from the one counter `w`); it is
embedded into `KLoc (Fin 3) (SE ⊕ Fin 2)` (the shift layout's unused counters `3`, `4` go to two
untouched scratch stacks).

**Cost.** Per coefficient `O(w)`, per record `O(1)`, setup and teardown `O(w)`:
`C·(cvol w v + w + 1)`.
-/

namespace SubNLogN.Machine.Layer.DrvPreK.RotAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

/-! ## Packed coefficients -/

/-- Two `w`-bit fields packed into one `2w`-bit field. -/
def packW (w : ℕ) (a b : ℤ) : ℤ := a % 2 ^ w + 2 ^ w * b

theorem twosBits_congr {w : ℕ} {a b : ℤ} (h : a % 2 ^ w = b % 2 ^ w) :
    twosBits w a = twosBits w b := by
  unfold twosBits; rw [h]

theorem packW_emod (w : ℕ) (a b : ℤ) : packW w a b % 2 ^ w = a % 2 ^ w := by
  unfold packW
  rw [Int.add_mul_emod_self_left, Int.emod_emod]

theorem packW_ediv (w : ℕ) (a b : ℤ) : packW w a b / 2 ^ w = b := by
  have hp : (0 : ℤ) < 2 ^ w := by positivity
  unfold packW
  rw [Int.add_mul_ediv_left _ _ hp.ne',
    Int.ediv_eq_zero_of_lt (Int.emod_nonneg _ hp.ne') (Int.emod_lt_of_pos _ hp), zero_add]

theorem twosBits_packW (w : ℕ) (a b : ℤ) :
    twosBits (w + w) (packW w a b) = twosBits w a ++ twosBits w b := by
  rw [twosBits_add, twosBits_congr (packW_emod w a b), packW_ediv]

/-- The packed field of a coefficient. -/
def packC (w : ℕ) (c : CInt) : ℤ := packW w c.1 c.2

theorem crecBits_eq_packed (w : ℕ) (cs : List CInt) :
    crecBits w cs = (cs.map (packC w)).flatMap (twosBits (w + w)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, List.flatMap_cons, ← ih, packC, twosBits_packW]
    simp [crecBits, coefBits]

theorem carrSyms_eq_packed (w : ℕ) (v : List (List CInt)) :
    carrSyms w v = arrFields (w + w) (v.map (List.map (packC w))) := by
  simp only [carrSyms, arrFields, List.map_map]
  congr 2
  funext cs
  simp [crecBits_eq_packed]

theorem fits_packC {w : ℕ} (hw : 1 ≤ w) {c : CInt} (h2 : FitsTwos w c.2) :
    FitsTwos (w + w) (packC w c) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  unfold FitsTwos at *
  have e1 : k + 1 + (k + 1) - 1 = (k + 1) + k := by omega
  rw [e1, pow_add]
  simp only [Nat.add_sub_cancel] at h2
  have hp : (0 : ℤ) < 2 ^ (k + 1) := by positivity
  have hm0 := Int.emod_nonneg c.1 hp.ne'
  have hm1 := Int.emod_lt_of_pos c.1 hp
  have hk : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  obtain ⟨h21, h22⟩ := h2
  have h22' : c.2 ≤ 2 ^ k - 1 := by linarith
  have l1 : 2 ^ (k + 1) * (-(2 : ℤ) ^ k) ≤ 2 ^ (k + 1) * c.2 :=
    mul_le_mul_of_nonneg_left h21 hp.le
  have l2 : 2 ^ (k + 1) * c.2 ≤ 2 ^ (k + 1) * (2 ^ k - 1) :=
    mul_le_mul_of_nonneg_left h22' hp.le
  unfold packC packW
  constructor <;> nlinarith

/-- Negation by a flag. -/
def sgnF (n : Bool) (q : ℤ) : ℤ := if n then -q else q

theorem rot_congr (e w : ℕ) {a a' : ℤ} (b : ℤ) (h : a % 2 ^ w = a' % 2 ^ w) :
    twosBits w (rotIPowC e (a, b)).1 = twosBits w (rotIPowC e (a', b)).1 ∧
    twosBits w (rotIPowC e (a, b)).2 = twosBits w (rotIPowC e (a', b)).2 := by
  have hn : (-a) % 2 ^ w = (-a') % 2 ^ w := Int.ModEq.neg h
  unfold rotIPowC
  split_ifs <;> dsimp only <;> refine ⟨?_, ?_⟩ <;>
    first | rfl | exact twosBits_congr h | exact twosBits_congr hn

/-- The field function of the rotation: unpack, rotate, pack. -/
def rotF (e w : ℕ) (z : ℤ) : ℤ :=
  packW w (rotIPowC e (z, z / 2 ^ w)).1 (rotIPowC e (z, z / 2 ^ w)).2

theorem rotF_packC (e w : ℕ) (c : CInt) :
    twosBits (w + w) (rotF e w (packC w c)) = coefBits w (rotIPowC e c) := by
  unfold rotF
  rw [twosBits_packW, packC, packW_ediv]
  obtain ⟨r1, r2⟩ := rot_congr e w c.2 (packW_emod w c.1 c.2)
  rw [r1, r2]
  rfl

theorem out_packed (e w : ℕ) (v : List (List CInt)) :
    arrFields (w + w) ((v.map (List.map (packC w))).map (List.map (rotF e w))) =
      carrSyms w (mapC (rotIPowC e) v) := by
  simp only [arrFields, carrSyms, mapC, List.map_map]
  congr 2
  funext cs
  simp only [Function.comp, List.map_map, List.flatMap_map, crecBits]
  apply List.flatMap_congr
  intro c _
  exact rotF_packC e w c

/-- The parameters of the field program for `i^e`: the stacks holding the parts emitted first and
second, and their negation flags. -/
def rotPar (e : ℕ) : SE × SE × Bool × Bool :=
  if e % 4 = 0 then (.A, .B, false, false)
  else if e % 4 = 1 then (.B, .A, true, false)
  else if e % 4 = 2 then (.A, .B, true, true)
  else (.B, .A, false, true)

/-- Selection of a loaded part: `A` holds the real part, `B` the imaginary part. -/
def selP (P : SE) (x y : ℤ) : ℤ := if P = .A then x else y

theorem rotPar_spec (e : ℕ) (x y : ℤ) :
    rotIPowC e (x, y) = (sgnF (rotPar e).2.2.1 (selP (rotPar e).1 x y),
      sgnF (rotPar e).2.2.2 (selP (rotPar e).2.1 x y)) := by
  unfold rotIPowC rotPar
  split_ifs <;> simp [sgnF, selP]

theorem rotPar_AB (e : ℕ) : ((rotPar e).1 = .A ∧ (rotPar e).2.1 = .B) ∨
    ((rotPar e).1 = .B ∧ (rotPar e).2.1 = .A) := by
  unfold rotPar
  split_ifs <;> simp

/-! ## Programs -/

section Programs

variable {K : Type}

/-- Move the bits of `P` onto `Q` (reversed), complemented when `n`: loop. -/
def mvLoopX (n : Bool) (P Q : K) : AProg K :=
  .loop (fun v => isBitO v.q) (.seq (drop1 P) (.seq (.push Q fun v => .bit (xor (bitD v.q false) n))
    (peekQ P)))

/-- Move the bits of `P` onto `Q` (reversed), complemented when `n`. -/
def mvBitsX (n : Bool) (P Q : K) : AProg K := .seq (peekQ P) (mvLoopX n P Q)

/-- Set the carry. -/
def setC (n : Bool) : AProg K := .load fun v => { v with c := n }

end Programs

/-- Load one `w`-bit part from the source onto `P` (ruler `Rh`). -/
def loadPh (P : SK) : AProg SK :=
  .seq (walk (.inr .Rh) (.inr .X) (loadBody (.inl 0) P)) (moveMarks (.inr .X) (.inr .Rh))

/-- Emit one output component onto `T` from the part on `P`, negated when `n` (ruler `R2`). -/
def outPh (n : Bool) (P : SK) : AProg SK :=
  .seq (mvBitsX n P (.inr .Rs)) (.seq (setC n) (.seq
    (walk (.inr .R2) (.inr .X) (emitBody (.inr .Rs) (.inr .T))) (moveMarks (.inr .X) (.inr .R2))))

/-- **The field program**: real part onto `A`, imaginary part onto `B`, then the output components
from `P1` (negated when `n1`) and from `P2` (negated when `n2`). -/
def rotField (P1 P2 : SE) (n1 n2 : Bool) : AProg SK :=
  .seq (loadPh (.inr .A)) (.seq (loadPh (.inr .B)) (.seq (outPh n1 (.inr P1)) (outPh n2 (.inr P2))))

/-- The exact cost of the field program. -/
def rotCost (w : ℕ) : ℕ := 2 * (11 * w + 4) + 2 * (17 * w + 7)

/-! ## Evaluation lemmas -/

section Evals

variable {K : Type} [DecidableEq K]

theorem mvLoopX_eval (n : Bool) {P Q : K} (hPQ : P ≠ Q) :
    ∀ (L : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym), TermOK D →
      S P = L.map Sym.bit ++ D → v.q = (L.map Sym.bit ++ D).head? →
      Eval [] (mvLoopX n P Q) ⟨v, S⟩ ⟨{ v with q := D.head? }, Function.update
        (Function.update S P D) Q ((L.map (xor · n)).reverse.map Sym.bit ++ S Q)⟩
        (4 * L.length + 1)
  | [], D, v, S, hD, hP, hv => by
    simp only [List.map_nil, List.nil_append, List.reverse_nil, List.length_nil] at hP hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isBitO_false_of_termOK hD)).of_eq ?_ rfl
    rw [← hv, ← hP, Function.update_eq_self, Function.update_eq_self]
  | b :: L, D, v, S, hD, hP, hv => by
    have hP' : S P = Sym.bit b :: (L.map Sym.bit ++ D) := by rw [hP]; rfl
    set S1 := Function.update S P (L.map Sym.bit ++ D) with hS1
    set S2 := Function.update S1 Q (Sym.bit (xor b n) :: S1 Q) with hS2
    have h2P : S2 P = L.map Sym.bit ++ D := by
      rw [hS2, Function.update_of_ne hPQ, hS1, Function.update_self]
    have e1 := eval_drop1 P v S _ _ hP'
    have e2 : Eval [] (.push Q fun v : AReg => Sym.bit (xor (bitD v.q false) n)) ⟨v, S1⟩
        ⟨v, S2⟩ 1 := by
      refine (Eval.push [] Q _ v S1).of_eq ?_ rfl
      rw [hv]; rfl
    have e3 : Eval [] (peekQ P) ⟨v, S2⟩ ⟨{ v with q := (L.map Sym.bit ++ D).head? }, S2⟩ 1 := by
      refine (eval_peekQ P v S2).of_eq ?_ rfl
      rw [h2P]
    have ih := mvLoopX_eval n hPQ L D { v with q := (L.map Sym.bit ++ D).head? } S2 hD h2P rfl
    refine (Eval.loop_true (by rw [hv]; rfl) (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply, List.map_cons, List.reverse_cons, List.map_append,
      List.map_nil, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

end Evals

theorem eval_walk_peek {R : SK} (n : ℕ) (D : List Sym) (v : AReg) (S : SK → List Sym)
    (hR : S R = List.replicate n .mark ++ D) :
    Eval [] (peekR R) ⟨v, S⟩ ⟨setR v (List.replicate n Sym.mark ++ D).head?, S⟩ 1 := by
  refine (eval_peekR R v S).of_eq ?_ rfl
  rw [hR]; rfl

theorem loadPh_eval {P : SK} (h1 : P ≠ .inr .Rh) (h2 : P ≠ .inr .X) (h3 : P ≠ .inl 0)
    (w : ℕ) (q : ℤ) (L DH DX : List Sym) (v : AReg) (S : SK → List Sym)
    (hDH : DH.head? ≠ some .mark) (hDX : DX.head? ≠ some .mark)
    (hRh : S (.inr .Rh) = List.replicate w .mark ++ DH) (hX : S (.inr .X) = DX)
    (hsrc : S (.inl 0) = (twosBits w q).map Sym.bit ++ L) :
    ∃ v' : AReg, Eval [] (loadPh P) ⟨v, S⟩
      ⟨v', Function.update (Function.update S (.inl 0) L) P
        ((twosBits w q).reverse.map Sym.bit ++ S P)⟩ (11 * w + 4) := by
  have hlen : (twosBits w q).length = w := K1.length_twosBits _ _
  have hRh' : S (.inr .Rh) = List.replicate (twosBits w q).length .mark ++ DH := by rw [hlen, hRh]
  have e1 := eval_walk_peek (R := .inr .Rh) _ DH v S hRh'
  obtain ⟨v2, hv2r, -, -, -, e2⟩ := loadLoop_eval (R := (.inr .Rh : SK)) (X := .inr .X)
    (src := .inl 0) (A := P) (by decide) (by decide) (by decide) (Ne.symm h1) (Ne.symm h2)
    (Ne.symm h3) (twosBits w q) DH L (setR v (List.replicate (twosBits w q).length Sym.mark ++ DH).head?)
    S hDH hRh' hsrc rfl
  set S2 := Function.update (Function.update (Function.update (Function.update S (.inr .Rh) DH)
    (.inr .X) (List.replicate (twosBits w q).length .mark ++ S (.inr .X))) (.inl 0) L) P
    ((twosBits w q).reverse.map Sym.bit ++ S P) with hS2
  have e3 := moveMarks_eval (X := (.inr .X : SK)) (R := .inr .Rh) (by decide) w DX v2 S2 hDX
    (by rw [hS2, Function.update_of_ne (Ne.symm h2), Function.update_of_ne (by decide),
      Function.update_self, hlen, hX])
  refine ⟨{ v2 with r := DX.head? }, (Eval.seq (Eval.seq e1 e2) e3).of_eq ?_ (by rw [hlen]; ring)⟩
  congr 1
  funext k
  simp only [hS2, Function.update_apply, hlen]
  split_ifs <;> simp_all

theorem emit_sgn (n sg : Bool) (w : ℕ) (q : ℤ) :
    emitOut n sg ((twosBits w q).map (xor · n)) w = twosBits w (sgnF n q) := by
  cases n
  · have : (twosBits w q).map (xor · false) = twosBits w q := by
      conv_rhs => rw [← List.map_id (twosBits w q)]
      congr 1; funext b; simp
    rw [this, emitOut_len]; simp [sgnF]
  · have : (twosBits w q).map (xor · true) = twosBits w (-1 - q) := by
      rw [← twosBits_map_not]; congr 1; funext b; simp
    rw [this, emitOut_len]; simp only [sgnF, if_true, Bool.toNat_true, Nat.cast_one]
    congr 1; ring

theorem outPh_eval (n : Bool) {P : SK} (h1 : P ≠ .inr .Rs) (h2 : P ≠ .inr .R2)
    (h3 : P ≠ .inr .X) (h4 : P ≠ .inr .T) (w : ℕ) (q : ℤ) (DP DRs D2 DX : List Sym) (v : AReg)
    (S : SK → List Sym) (hDP : TermOK DP) (hDRs : TermOK DRs) (hD2 : D2.head? ≠ some .mark)
    (hDX : DX.head? ≠ some .mark) (hP : S P = (twosBits w q).reverse.map Sym.bit ++ DP)
    (hRs : S (.inr .Rs) = DRs) (hR2 : S (.inr .R2) = List.replicate w .mark ++ D2)
    (hX : S (.inr .X) = DX) :
    ∃ v' : AReg, Eval [] (outPh n P) ⟨v, S⟩
      ⟨v', Function.update (Function.update S P DP) (.inr .T)
        ((twosBits w (sgnF n q)).reverse.map Sym.bit ++ S (.inr .T))⟩ (17 * w + 7) := by
  have hlen : (twosBits w q).length = w := K1.length_twosBits _ _
  have e1a := eval_peekQ P v S
  rw [hP] at e1a
  have e1b := mvLoopX_eval n (P := P) (Q := (.inr .Rs : SK)) h1 (twosBits w q).reverse DP
    { v with q := ((twosBits w q).reverse.map Sym.bit ++ DP).head? } S hDP hP rfl
  set Lb := (twosBits w q).map (xor · n) with hLb
  have hLbl : Lb.length = w := by rw [hLb, List.length_map, hlen]
  set S1 := Function.update (Function.update S P DP) (.inr .Rs) (Lb.map Sym.bit ++ DRs) with hS1
  have e1b' : Eval [] (mvLoopX n P (.inr .Rs))
      ⟨{ v with q := ((twosBits w q).reverse.map Sym.bit ++ DP).head? }, S⟩
      ⟨{ { v with q := ((twosBits w q).reverse.map Sym.bit ++ DP).head? } with q := DP.head? }, S1⟩
      (4 * (twosBits w q).reverse.length + 1) := by
    refine e1b.of_eq ?_ rfl
    congr 1
    simp only [hS1, hLb, List.map_reverse, List.reverse_reverse, hRs]
  have e2 := Eval.load [] (fun v : AReg => { v with c := n }) { v with q := DP.head? } S1
  have hS1R2 : S1 (.inr .R2) = List.replicate w .mark ++ D2 := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (Ne.symm h2), hR2]
  have e3a := eval_walk_peek (R := .inr .R2) w D2 { { v with q := DP.head? } with c := n } S1 hS1R2
  obtain ⟨v4, -, -, e3b⟩ := emitLoop_eval (R := (.inr .R2 : SK)) (X := .inr .X) (B := .inr .Rs)
    (T := .inr .T) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) DRs hDRs
    w Lb D2 (setR { { v with q := DP.head? } with c := n } (List.replicate w Sym.mark ++ D2).head?)
    S1 hD2 hS1R2 (by rw [hS1, Function.update_self]) rfl
  set S3 := Function.update (Function.update (Function.update (Function.update S1 (.inr .R2) D2)
    (.inr .X) (List.replicate w .mark ++ S1 (.inr .X))) (.inr .Rs) ((Lb.drop w).map Sym.bit ++ DRs))
    (.inr .T) ((emitOut n (setR { { v with q := DP.head? } with c := n }
      (List.replicate w Sym.mark ++ D2).head?).sg Lb w).reverse.map Sym.bit ++ S1 (.inr .T))
    with hS3
  have hS3X : S3 (.inr .X) = List.replicate w .mark ++ DX := by
    rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hS1, Function.update_of_ne (by decide),
      Function.update_of_ne (Ne.symm h3), hX]
  have e4 := moveMarks_eval (X := (.inr .X : SK)) (R := .inr .R2) (by decide) w DX v4 S3 hDX hS3X
  refine ⟨{ v4 with r := DX.head? },
    (Eval.seq (Eval.seq e1a e1b') (Eval.seq e2 (Eval.seq (Eval.seq e3a e3b) e4))).of_eq ?_
    (by rw [List.length_reverse, hlen]; ring)⟩
  have hdrop : Lb.drop w = [] := List.drop_eq_nil_of_le (by rw [hLbl])
  have hem := emit_sgn n (setR { { v with q := DP.head? } with c := n }
      (List.replicate w Sym.mark ++ D2).head?).sg w q
  congr 1
  funext k
  simp only [hS3, hS1, Function.update_apply, hdrop, List.map_nil, List.nil_append, hem]
  split_ifs <;> simp_all

/-- The stacks after the delimiters and the two rulers (both from the counter `w`). -/
def ruleState (w : ℕ) (S : SK → List Sym) : SK → List Sym :=
  Function.update (Function.update (delimState S) (.inr .Rh)
    (List.replicate w .mark ++ .sep2 :: S (.inr .Rh))) (.inr .R2)
    (List.replicate w .mark ++ .sep2 :: S (.inr .R2))

theorem ruleState_eq (w : ℕ) (S : SK → List Sym) : ruleState w S = setupState w w 0 S := by
  funext k
  simp only [ruleState, setupState, delimState, Function.update_apply, Nat.zero_min,
    Nat.sub_zero, List.replicate_zero, List.nil_append]
  split_ifs <;> simp_all

/-- **The field contract of `rotField`.** -/
theorem rotField_spec (P1 P2 : SE) (hP : (P1 = .A ∧ P2 = .B) ∨ (P1 = .B ∧ P2 = .A))
    (n1 n2 : Bool) (w : ℕ) (S : SK → List Sym) :
    FieldSpec (rotField P1 P2 n1 n2) (.inl 0) (.inr .T) (w + w) (w + w)
      (fun z => packW w (sgnF n1 (selP P1 z (z / 2 ^ w))) (sgnF n2 (selP P2 z (z / 2 ^ w))))
      (rotCost w) (ruleState w S) := by
  intro z L v S' _ hS' hsrc
  have hk : ∀ k : SK, k ≠ .inl 0 → k ≠ .inr .T → S' k = ruleState w S k := hS'
  have hRh : S' (.inr .Rh) = List.replicate w .mark ++ .sep2 :: S (.inr .Rh) := by
    rw [hk _ (by decide) (by decide)]; simp [ruleState, Function.update_apply]
  have hR2 : S' (.inr .R2) = List.replicate w .mark ++ .sep2 :: S (.inr .R2) := by
    rw [hk _ (by decide) (by decide)]; simp [ruleState, Function.update_apply]
  have hX : S' (.inr .X) = .sep2 :: S (.inr .X) := by
    rw [hk _ (by decide) (by decide)]; simp [ruleState, delimState, Function.update_apply]
  have hRs : S' (.inr .Rs) = .sep2 :: S (.inr .Rs) := by
    rw [hk _ (by decide) (by decide)]; simp [ruleState, delimState, Function.update_apply]
  have hA : S' (.inr .A) = .sep2 :: S (.inr .A) := by
    rw [hk _ (by decide) (by decide)]; simp [ruleState, delimState, Function.update_apply]
  have hB : S' (.inr .B) = .sep2 :: S (.inr .B) := by
    rw [hk _ (by decide) (by decide)]; simp [ruleState, delimState, Function.update_apply]
  have hsrc' : S' (.inl 0) = (twosBits w z).map Sym.bit ++
      ((twosBits w (z / 2 ^ w)).map Sym.bit ++ L) := by
    rw [hsrc, twosBits_add, List.map_append, List.append_assoc]
  obtain ⟨v1, e1⟩ := loadPh_eval (P := .inr .A) (by decide) (by decide) (by decide) w z
    ((twosBits w (z / 2 ^ w)).map Sym.bit ++ L) (.sep2 :: S (.inr .Rh)) (.sep2 :: S (.inr .X)) v S'
    (by simp) (by simp) hRh hX hsrc'
  set S1 := Function.update (Function.update S' (.inl 0)
    ((twosBits w (z / 2 ^ w)).map Sym.bit ++ L)) (.inr .A)
    ((twosBits w z).reverse.map Sym.bit ++ S' (.inr .A)) with hS1
  obtain ⟨v2, e2⟩ := loadPh_eval (P := .inr .B) (by decide) (by decide) (by decide) w (z / 2 ^ w) L
    (.sep2 :: S (.inr .Rh)) (.sep2 :: S (.inr .X)) v1 S1 (by simp) (by simp) (by simp [hS1, Function.update_apply, hRh])
    (by simp [hS1, Function.update_apply, hX]) (by simp [hS1])
  set S2 := Function.update (Function.update S1 (.inl 0) L) (.inr .B)
    ((twosBits w (z / 2 ^ w)).reverse.map Sym.bit ++ S1 (.inr .B)) with hS2
  have hP1 : S2 (.inr P1) = (twosBits w (selP P1 z (z / 2 ^ w))).reverse.map Sym.bit ++
      .sep2 :: S (.inr P1) := by
    rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS2, hS1, Function.update_apply, selP, hA, hB]
  obtain ⟨v3, e3⟩ := outPh_eval n1 (P := .inr P1)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    w (selP P1 z (z / 2 ^ w)) (.sep2 :: S (.inr P1)) (.sep2 :: S (.inr .Rs)) (.sep2 :: S (.inr .R2))
    (.sep2 :: S (.inr .X)) v2 S2 (TermOK.cons rfl _) (TermOK.cons rfl _) (by simp)
    (by simp) hP1 (by simp [hS2, hS1, Function.update_apply, hRs])
    (by simp [hS2, hS1, Function.update_apply, hR2]) (by simp [hS2, hS1, Function.update_apply, hX])
  set S3 := Function.update (Function.update S2 (.inr P1) (.sep2 :: S (.inr P1))) (.inr .T)
    ((twosBits w (sgnF n1 (selP P1 z (z / 2 ^ w)))).reverse.map Sym.bit ++ S2 (.inr .T)) with hS3
  have hP2 : S3 (.inr P2) = (twosBits w (selP P2 z (z / 2 ^ w))).reverse.map Sym.bit ++
      .sep2 :: S (.inr P2) := by
    rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hS3, hS2, hS1, Function.update_apply, selP, hA, hB]
  obtain ⟨v4, e4⟩ := outPh_eval n2 (P := .inr P2)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    w (selP P2 z (z / 2 ^ w)) (.sep2 :: S (.inr P2)) (.sep2 :: S (.inr .Rs)) (.sep2 :: S (.inr .R2))
    (.sep2 :: S (.inr .X)) v3 S3 (TermOK.cons rfl _) (TermOK.cons rfl _) (by simp)
    (by simp) hP2
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS3, hS2, hS1, Function.update_apply, hRs])
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS3, hS2, hS1, Function.update_apply, hR2])
    (by rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hS3, hS2, hS1, Function.update_apply, hX])
  refine ⟨v4, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ (by unfold rotCost; ring)⟩
  congr 1
  funext k
  rw [twosBits_packW, List.reverse_append, List.map_append, List.append_assoc]
  rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all

/-! ## The kernel on the shift layout -/

/-- The rotation kernel on the shift kernels' layout `SK`: delimiters, the rulers `Rh = R2 = w`, the
array driver with `rotField`, teardown. -/
def rotCore (P1 P2 : SE) (n1 n2 : Bool) : AProg SK :=
  .seq shiftDelims (.seq (shiftRulers 2 2) (.seq (peekO (.inl 0))
    (.seq (recLoop (rotField P1 P2 n1 n2) (.inl 0) (.inr .T)) shiftTeardown)))

theorem rotCore_closed (P1 P2 : SE) (n1 n2 : Bool) : (rotCore P1 P2 n1 n2).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, rotCore, rotField, loadPh, outPh, mvBitsX, mvLoopX, setC,
    shiftDelims, shiftRulers, shiftTeardown, buildRuler, brLoop, brBody, double, dblLoop,
    moveMarks, mmLoop, copyRuler, subRuler, walk, walkLoop, walkStep, clearMarks, cmLoop, drop1,
    pushS, peekR, peekQ, peekO, popO, skipA, mvBits, mvLoop, recLoop, recBody, fieldLoop, discBody,
    loadBody, emitBody, carryInit, drainBits, dbLoop, Prog.liftRegs, Lib.cmpNum, Lib.cmpBody,
    Lib.pushC, Lib.popR, Lib.restoreR, Lib.moveBits, Lib.moveBitsBody, Lib.pushR, Lib.skip,
    WP.W9comp.rewindTo, WP.W9comp.rewindBody]

theorem recLoopCost_map (cf : ℕ) (g : CInt → ℤ) (v : List (List CInt)) :
    recLoopCost cf (v.map (List.map g)) = ncoef v * (cf + 2) + 5 * v.length + 1 := by
  induction v with
  | nil => simp [recLoopCost, ncoef]
  | cons cs v ih =>
    simp only [recLoopCost, ncoef, List.map_cons, List.sum_cons, List.length_cons,
      List.length_map] at ih ⊢
    have ih' := Nat.add_right_cancel ih
    rw [ih']; ring

theorem fits_packed {w : ℕ} (hw : 1 ≤ w) {v : List (List CInt)} (h : CArrFits w v) :
    ∀ zs ∈ v.map (List.map (packC w)), ∀ z ∈ zs, FitsTwos (w + w) z := by
  intro zs hzs z hz
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.1 hzs
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
  exact fits_packC hw (h cs hcs c hc).2

theorem length_flatMap_twosBits (k : ℕ) (zs : List ℤ) :
    (zs.flatMap (twosBits k)).length = k * zs.length := by
  induction zs with
  | nil => simp
  | cons z zs ih => rw [List.flatMap_cons, List.length_append, ih, K1.length_twosBits,
      List.length_cons]; ring

theorem length_arrFields (k : ℕ) (vs : List (List ℤ)) :
    (arrFields k vs).length = vs.length + k * (vs.map List.length).sum := by
  induction vs with
  | nil => simp [arrFields, arrSyms, blk]
  | cons zs vs ih =>
    rw [arrFields_cons, List.length_append, List.length_map, length_flatMap_twosBits,
      List.length_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- **The rotation kernel on the shift layout**, exact final stacks. -/
theorem rotCore_runs (P1 P2 : SE) (hP : (P1 = .A ∧ P2 = .B) ∨ (P1 = .B ∧ P2 = .A))
    (n1 n2 : Bool) (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym) (S : SK → List Sym)
    (hw : 1 ≤ w) (hfits : CArrFits w v) (hrest : BlkTerm rest) (hr2 : TermOK r2)
    (h0 : S (.inl 0) = carrSyms w v ++ rest) (h2 : S (.inl 2) = natSyms w ++ r2) :
    Runs (rotCore P1 P2 n1 n2) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrFields (w + w) ((v.map (List.map (packC w))).map (List.map
          (fun z => packW w (sgnF n1 (selP P1 z (z / 2 ^ w))) (sgnF n2 (selP P2 z (z / 2 ^ w)))))) ++
          S (.inl 1)))
      (fun _ => True) (200 * (cvol w v + w + 1)) := by
  apply Runs.of_eval
  intro v0
  have e1 := shiftDelims_eval v0 S
  obtain ⟨v2, t2, e2, ht2⟩ := shiftRulers_eval 2 2 w w r2 r2 v0 S hr2 hr2 h2 h2
  have e2' : Eval [] (shiftRulers 2 2) ⟨v0, delimState S⟩ ⟨v2, ruleState w S⟩ t2 := e2
  have hS0src : ruleState w S (.inl 0) = arrFields (w + w) (v.map (List.map (packC w))) ++ rest := by
    rw [← carrSyms_eq_packed, ← h0]
    simp [ruleState, delimState, Function.update_apply]
  have e3 := eval_peekO (.inl 0) v2 (ruleState w S)
  obtain ⟨v3, e4⟩ := recLoop_eval (src := (.inl 0 : SK)) (T := .inr .T) (by decide) (by omega)
    (rotField_spec P1 P2 hP n1 n2 w S) (v.map (List.map (packC w))) rest
    { v2 with o := (ruleState w S (.inl 0)).head? } (ruleState w S) (fits_packed hw hfits) hrest
    (fun k _ _ => rfl) hS0src rfl
  obtain ⟨v4, e5⟩ := shiftTeardown_eval w w 0 (arrFields (w + w) ((v.map (List.map (packC w))).map
    (List.map (fun z => packW w (sgnF n1 (selP P1 z (z / 2 ^ w)))
      (sgnF n2 (selP P2 z (z / 2 ^ w))))))) rest (mark_not_mem_arrFields _ _) v3 S
  rw [← ruleState_eq] at e5
  refine ⟨v4, _, Eval.seq e1 (Eval.seq e2' (Eval.seq e3 (Eval.seq e4 e5))), trivial, ?_⟩
  have hlen : (arrFields (w + w) ((v.map (List.map (packC w))).map (List.map
      (fun z => packW w (sgnF n1 (selP P1 z (z / 2 ^ w))) (sgnF n2 (selP P2 z (z / 2 ^ w))))))).length =
      v.length + (w + w) * ncoef v := by
    rw [length_arrFields]
    simp [List.map_map, Function.comp_def, ncoef]
  rw [recLoopCost_map, hlen, cvol_eq]
  have hb := bitLen_le_self' w
  have hMw : ncoef v ≤ ncoef v * w := Nat.le_mul_of_pos_right _ hw
  have hexp : ncoef v * (rotCost w + 2) = 56 * (ncoef v * w) + 24 * ncoef v := by
    unfold rotCost; ring
  have hc1 : (w + w) * ncoef v = 2 * (ncoef v * w) := by ring
  have hc2 : 2 * w * ncoef v = 2 * (ncoef v * w) := by ring
  rw [hexp, hc1, hc2]
  generalize ncoef v * w = P at *
  simp only [Nat.zero_min, Nat.sub_zero]
  omega

/-! ## The kernel on `KLoc (Fin 3)` -/

/-- Stacks of the rotation kernel: named `Fin 3`; the shift layout's scratch `SE`; two untouched
stacks receiving the shift layout's unused counters `3`, `4`. -/
abbrev RL : Type := KLoc (Fin 3) (SE ⊕ Fin 2)

/-- Embedding of the shift layout. -/
def ιW : SK → RL
  | .inl i => ![(.inl 0 : RL), .inl 1, .inl 2, .inr (.inr 0), .inr (.inr 1)] i
  | .inr e => .inr (.inl e)

theorem ιW_injective : Function.Injective ιW := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιW]
  · fin_cases i <;> simp [ιW] at h
  · fin_cases j <;> simp [ιW] at h
  · simp only [ιW, Sum.inr.injEq, Sum.inl.injEq] at h; rw [h]

/-- The identity lens. -/
def lidA : Lens AReg AReg := ⟨id, fun _ w => w, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- **The rotation kernel** for `i^e`. -/
def rotKernel (e : ℕ) : AProg RL :=
  callInj ιW lidA (rotCore (rotPar e).1 (rotPar e).2.1 (rotPar e).2.2.1 (rotPar e).2.2.2)

theorem rotKernel_closed (e : ℕ) : (rotKernel e).Closed :=
  closed_callInj _ _ (rotCore_closed _ _ _ _)

theorem rotKernel_runs (e w : ℕ) (v : List (List CInt)) (rest r2 : List Sym) (S : RL → List Sym)
    (hw : 1 ≤ w) (hfits : CArrFits w v) (hrest : BlkTerm rest) (hr2 : TermOK r2)
    (h0 : S (.inl 0) = carrSyms w v ++ rest) (h2 : S (.inl 2) = natSyms w ++ r2) :
    Runs (rotKernel e) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w (mapC (rotIPowC e) v) ++ S (.inl 1)))
      (fun _ => True) (200 * (cvol w v + w + 1)) := by
  have h := rotCore_runs (rotPar e).1 (rotPar e).2.1 (rotPar_AB e) (rotPar e).2.2.1
    (rotPar e).2.2.2 w v rest r2 (S ∘ ιW) hw hfits hrest hr2 (by simp [ιW, h0]) (by simp [ιW, h2])
  have hf : (fun z => packW w (sgnF (rotPar e).2.2.1 (selP (rotPar e).1 z (z / 2 ^ w)))
      (sgnF (rotPar e).2.2.2 (selP (rotPar e).2.1 z (z / 2 ^ w)))) = rotF e w := by
    funext z
    simp only [rotF, rotPar_spec e z (z / 2 ^ w)]
  rw [hf, out_packed] at h
  refine runs_callInj ιW_injective lidA (WP.W9comp.runs_congr h ?_) ?_
  · funext x
    rcases x with i | e'
    · fin_cases i <;> simp [ιW, Function.update_apply]
    · simp [ιW, Function.update_apply]
  · intro k hk
    exfalso
    rcases k with i | e' | j
    · fin_cases i
      · exact hk (.inl 0) rfl
      · exact hk (.inl 1) rfl
      · exact hk (.inl 2) rfl
    · exact hk (.inr e') rfl
    · fin_cases j
      · exact hk (.inl 3) rfl
      · exact hk (.inl 4) rfl

end SubNLogN.Machine.Layer.DrvPreK.RotAux

namespace SubNLogN.Machine.Layer.DrvPreK

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith RotAux

/-- **`RotIPowStmt` holds**: coefficientwise multiplication by `i^e` at one width. -/
theorem rotIPow_holds : RotIPowStmt := by
  refine ⟨200, fun e => ⟨SE ⊕ Fin 2, inferInstance, inferInstance, AReg, rotKernel e,
    inferInstance, inferInstance, rotKernel_closed e, ?_⟩⟩
  intro w v rest r2 S hw hfits _ hrest hr2 h0 h2
  exact rotKernel_runs e w v rest r2 S hw hfits hrest hr2 h0 h2

end SubNLogN.Machine.Layer.DrvPreK
