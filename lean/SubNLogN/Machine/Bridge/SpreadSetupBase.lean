/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadParts
import SubNLogN.Machine.Arith.Ruler

/-!
# K5 spreading setup, base (`Bridge/SpreadSetupBase.lean`)

Building blocks of the program of `SpreadSetupStmt` (`Bridge/SpreadParts.lean`), all on the AR
register `AReg` and over an arbitrary stack type `K`, with exact `Eval`/`Runs` lemmas:

* `mvSym A B` (move the top symbol), `skipFld`/`skipFlds` (move header fields from `A` onto `B`,
  reversed), `rewindG G A` (move them back down to a guard `sep2`);
* `dblField A B X Y`: multiply the ruler `X` by the power of two in the top field of `A`
  (one `double` per zero bit), moving the field onto `B`; `prodFields`: the same over a counted
  list of fields (amortized cost `18·(final ruler) + O(header)`);
* `cntField A B X`: one mark on `X` per bit of the top field of `A`;
* `minRulers A B TA TB W`: `W := min(a, b)` by a simultaneous walk of the rulers `A`, `B`;
* `copyR`, `subR`: copy / subtract a ruler, restoring it.

**Scope (honest summary).** Everything here is proved (no `sorry`). Helpers live in the namespace
`SubNLogN.Machine.Bridge.SpreadSetupAux`.
-/

namespace SubNLogN.Machine.Bridge.SpreadSetupAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability

/-! ## Programs -/

section Progs

variable {K : Type}

/-- Move the top symbol of `A` onto `B` (through the register `o`). -/
def mvSym (A B : K) : AProg K := .seq (popO A) (.push B fun v => v.o.getD .sep)

/-- Skip one header field: its bits, then its `mark`, move from `A` onto `B` (reversed). -/
def skipFld (A B : K) : AProg K := .seq (mvBits A B) (mvSym A B)

/-- Skip `n` header fields. -/
def skipFlds (A B : K) : ℕ → AProg K
  | 0 => skipA
  | n + 1 => .seq (skipFld A B) (skipFlds A B n)

/-- The register bit is a zero. -/
def isZeroO (o : Option Sym) : Bool := !(bitD o true)

/-- One bit of a field: move it from `A` onto `B`; on a `0` bit double the ruler `X` (via `Y`). -/
def dfBody (A B X Y : K) : AProg K :=
  .seq (popO A) (.seq (.push B fun v => v.o.getD .sep)
    (.seq (.ite (fun v => isZeroO v.o) (double X Y) skipA) (peekQ A)))

/-- The bit loop of `dblField`. -/
def dfLoop (A B X Y : K) : AProg K := .loop (fun v => isBitO v.q) (dfBody A B X Y)

/-- Multiply the ruler `X` by the power of two in the top field of `A` (one doubling per zero bit),
moving the field (bits and `mark`) onto `B`. -/
def dblField (A B X Y : K) : AProg K := .seq (peekQ A) (.seq (dfLoop A B X Y) (mvSym A B))

/-- One bit of a field: move it from `A` onto `B` and push a mark on `X`. -/
def cfBody (A B X : K) : AProg K :=
  .seq (popO A) (.seq (.push B fun v => v.o.getD .sep) (.seq (pushS X .mark) (peekQ A)))

/-- The bit loop of `cntField`. -/
def cfLoop (A B X : K) : AProg K := .loop (fun v => isBitO v.q) (cfBody A B X)

/-- Count the bits of the top field of `A` on the ruler `X`, moving the field onto `B`. -/
def cntField (A B X : K) : AProg K := .seq (peekQ A) (.seq (cfLoop A B X) (mvSym A B))

/-- For each mark of the counter `Ct` (walked via `W`, then restored): multiply `X` by the next
field of `A` (`dblField`). -/
def prodFields (Ct W A B X Y : K) : AProg K :=
  .seq (walk Ct W (dblField A B X Y)) (moveMarks W Ct)

/-- One step of the simultaneous walk: one mark from each of `A`, `B` (to `TA`, `TB`), one onto
`W`. -/
def minBody (A B TA TB W : K) : AProg K :=
  .seq (drop1 A) (.seq (pushS TA .mark) (.seq (drop1 B) (.seq (pushS TB .mark)
    (.seq (pushS W .mark) (.seq (peekR A) (peekQ B))))))

/-- The simultaneous walk loop. -/
def minLoop (A B TA TB W : K) : AProg K :=
  .loop (fun v => isMarkO v.r && isMarkO v.q) (minBody A B TA TB W)

/-- `W` receives `min(a, b)` marks; `A`, `B` lose that many (they go to `TA`, `TB`). -/
def minRulers (A B TA TB W : K) : AProg K :=
  .seq (peekR A) (.seq (peekQ B) (minLoop A B TA TB W))

/-- The register symbol is present and not the guard `sep2`. -/
def notSep2 : Option Sym → Bool
  | some .sep2 => false
  | some _ => true
  | none => false

/-- Body of the rewind loop. -/
def rwBody (G A : K) : AProg K := .seq (.push A fun v => v.o.getD .sep) (popO G)

/-- Move the symbols of `G` back onto `A` down to the guard `sep2`, which is dropped. -/
def rewindG (G A : K) : AProg K := .seq (popO G) (.loop (fun v => notSep2 v.o) (rwBody G A))

/-- Copy the ruler `R` onto `D` (via `X`), restoring `R`. -/
def copyR (R X D : K) : AProg K := .seq (copyRuler R X D) (moveMarks X R)

/-- Subtract the ruler `R` from `D` (via `X`), restoring `R`. -/
def subR (R X D : K) : AProg K := .seq (subRuler R X D) (moveMarks X R)

/-- Peek `A`; if it has no mark on top, copy the ruler `R` onto `D` (via `X`). -/
def copyIfEmpty (A R X D : K) : AProg K :=
  .seq (peekR A) (.ite (fun v => isMarkO v.r) skipA (copyR R X D))

end Progs

/-! ## Closedness -/

section Closed

variable {K : Type}

theorem closed_mvSym (A B : K) : (mvSym A B).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, mvSym, popO]

theorem closed_skipFld (A B : K) : (skipFld A B).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, skipFld, mvSym, popO, mvBits, mvLoop, peekQ, drop1]

theorem closed_skipFlds (A B : K) : ∀ n, (skipFlds A B n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, skipFlds, skipA]
  | n + 1 => by
    have h1 := closed_skipFld A B
    have h2 := closed_skipFlds A B n
    simp only [Prog.Closed] at h1 h2 ⊢
    exact ⟨h1, h2⟩

theorem closed_dblField (A B X Y : K) : (dblField A B X Y).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dblField, dfLoop, dfBody, mvSym, popO, peekQ, double,
    moveMarks, mmLoop, dblLoop, peekR, drop1, pushS, skipA]

theorem closed_cntField (A B X : K) : (cntField A B X).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, cntField, cfLoop, cfBody, mvSym, popO, peekQ, pushS]

theorem closed_prodFields (Ct W A B X Y : K) : (prodFields Ct W A B X Y).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, prodFields, walk, walkLoop, walkStep, dblField, dfLoop,
    dfBody, mvSym, popO, peekQ, double, moveMarks, mmLoop, dblLoop, peekR, drop1, pushS, skipA]

theorem closed_minRulers (A B TA TB W : K) : (minRulers A B TA TB W).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, minRulers, minLoop, minBody, peekR, peekQ, drop1, pushS]

theorem closed_rewindG (G A : K) : (rewindG G A).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, rewindG, rwBody, popO]

theorem closed_copyR (R X D : K) : (copyR R X D).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyR, copyRuler, walk, walkLoop, walkStep, moveMarks,
    mmLoop, peekR, drop1, pushS]

theorem closed_subR (R X D : K) : (subR R X D).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, subR, subRuler, walk, walkLoop, walkStep, moveMarks,
    mmLoop, peekR, drop1, pushS]

theorem closed_copyIfEmpty (A R X D : K) : (copyIfEmpty A R X D).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyIfEmpty, copyR, copyRuler, walk, walkLoop, walkStep,
    moveMarks, mmLoop, peekR, drop1, pushS, skipA]

end Closed

/-! ## Header facts -/

theorem hdrSyms_nil' : hdrSyms ([] : List ℕ) = [] := rfl

theorem hdrSyms_cons' (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append' (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

theorem length_hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    (hdrSyms (f :: fs)).length = bitLen f + 1 + (hdrSyms fs).length := by
  rw [hdrSyms_cons', List.length_append, List.length_cons, length_natSyms]
  omega

theorem termOK_mark (L : List Sym) : TermOK (Sym.mark :: L) := TermOK.cons (by rfl) L

theorem encodeNat_two_pow' : ∀ k : ℕ, encodeNat (2 ^ k) = List.replicate k false ++ [true]
  | 0 => by
    have h := encodeNat_add_add_one 0
    simpa [encodeNat_zero] using h
  | k + 1 => by
    have ih := encodeNat_two_pow' k
    have hne : encodeNat (2 ^ k) ≠ [] := by
      rw [ih]
      simp
    rw [pow_succ, Nat.mul_two, encodeNat_add, if_neg hne, ih]
    rfl

theorem bitLen_two_pow (k : ℕ) : bitLen (2 ^ k) = k + 1 := by
  simp [bitLen, encodeNat_two_pow']

/-! ## Evaluation lemmas: moves, skips, rewind, copies -/

section EvalA

variable {K : Type} [DecidableEq K]

theorem eval_mvSym {A B : K} (hAB : A ≠ B) (y : Sym) (L : List Sym) (v : AReg)
    (S : K → List Sym) (hA : S A = y :: L) :
    Eval [] (mvSym A B) ⟨v, S⟩
      ⟨{ v with o := some y }, Function.update (Function.update S A L) B (y :: S B)⟩ 2 := by
  have e1 := eval_popO A v S y L hA
  have e2 := Eval.push (Γ := fun _ => Sym) [] B (fun v : AReg => v.o.getD .sep)
    { v with o := some y } (Function.update S A L)
  refine (Eval.seq e1 e2).of_eq ?_ rfl
  rw [Function.update_of_ne hAB.symm]
  rfl

theorem eval_skipFld {A B : K} (hAB : A ≠ B) (n : ℕ) (L : List Sym) (v : AReg)
    (S : K → List Sym) (hA : S A = natSyms n ++ Sym.mark :: L) :
    ∃ v' : AReg, Eval [] (skipFld A B) ⟨v, S⟩
      ⟨v', Function.update (Function.update S A L) B ((natSyms n ++ [Sym.mark]).reverse ++ S B)⟩
        (4 * bitLen n + 4) := by
  have hA' : S A = (encodeNat n).map Sym.bit ++ Sym.mark :: L := hA
  have e1 := mvBits_eval hAB (encodeNat n) (Sym.mark :: L) v S (termOK_mark L) hA'
  set S1 := Function.update (Function.update S A (Sym.mark :: L)) B
    ((encodeNat n).reverse.map Sym.bit ++ S B) with hS1
  have h1A : S1 A = Sym.mark :: L := by
    rw [hS1, Function.update_of_ne hAB, Function.update_self]
  have e2 := eval_mvSym hAB Sym.mark L { v with q := (Sym.mark :: L).head? } S1 h1A
  refine ⟨{ { v with q := (Sym.mark :: L).head? } with o := some Sym.mark },
    (Eval.seq e1 e2).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [hS1, Function.update_apply, natSyms, List.reverse_append, List.map_reverse,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.cons_append]
    split_ifs <;> simp_all
  · simp only [bitLen] <;> omega

theorem eval_skipFlds {A B : K} (hAB : A ≠ B) :
    ∀ (fs : List ℕ) (L : List Sym) (v : AReg) (S : K → List Sym), S A = hdrSyms fs ++ L →
      ∃ v' : AReg, Eval [] (skipFlds A B fs.length) ⟨v, S⟩
        ⟨v', Function.update (Function.update S A L) B ((hdrSyms fs).reverse ++ S B)⟩
          (4 * (hdrSyms fs).length + 1)
  | [], L, v, S, hA => by
    refine ⟨v, (eval_skipA v S).of_eq ?_ rfl⟩
    rw [hdrSyms_nil', List.nil_append] at hA
    rw [hdrSyms_nil', List.reverse_nil, List.nil_append, ← hA, Function.update_eq_self,
      Function.update_eq_self]
  | f :: fs, L, v, S, hA => by
    have hA' : S A = natSyms f ++ Sym.mark :: (hdrSyms fs ++ L) := by
      rw [hA, hdrSyms_cons']
      simp
    obtain ⟨v1, e1⟩ := eval_skipFld hAB f (hdrSyms fs ++ L) v S hA'
    set S1 := Function.update (Function.update S A (hdrSyms fs ++ L)) B
      ((natSyms f ++ [Sym.mark]).reverse ++ S B) with hS1
    have h1A : S1 A = hdrSyms fs ++ L := by
      rw [hS1, Function.update_of_ne hAB, Function.update_self]
    obtain ⟨v2, e2⟩ := eval_skipFlds hAB fs L v1 S1 h1A
    refine ⟨v2, (Eval.seq e1 e2).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [hS1, Function.update_apply, hdrSyms_cons', List.reverse_append,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.cons_append]
      split_ifs <;> simp_all
    · rw [length_hdrSyms_cons]
      ring

theorem rwLoop_eval {G A : K} (hGA : G ≠ A) (G0 : List Sym) :
    ∀ (L : List Sym) (v : AReg) (S : K → List Sym), Sym.sep2 ∉ L →
      S G = (L ++ Sym.sep2 :: G0).tail → v.o = (L ++ Sym.sep2 :: G0).head? →
      ∃ v' : AReg, Eval [] (.loop (fun v : AReg => notSep2 v.o) (rwBody G A)) ⟨v, S⟩
        ⟨v', Function.update (Function.update S G G0) A (L.reverse ++ S A)⟩ (3 * L.length + 1)
  | [], v, S, _, hG, hv => by
    refine ⟨v, (Eval.loop_false (by rw [hv]; rfl)).of_eq ?_ rfl⟩
    simp only [List.nil_append, List.tail_cons] at hG
    rw [List.reverse_nil, List.nil_append, ← hG, Function.update_eq_self,
      Function.update_eq_self]
  | x :: L, v, S, hL, hG, hv => by
    have hx : x ≠ Sym.sep2 := fun h => hL (h ▸ List.mem_cons_self)
    have hL' : Sym.sep2 ∉ L := fun h => hL (List.mem_cons_of_mem x h)
    have hvo : v.o = some x := by rw [hv]; rfl
    have hc : notSep2 v.o = true := by
      rw [hvo]
      rcases x with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | exact absurd rfl hx
    have hG' : S G = L ++ Sym.sep2 :: G0 := by rw [hG]; rfl
    have e1 := Eval.push (Γ := fun _ => Sym) [] A (fun v : AReg => v.o.getD .sep) v S
    set S1 := Function.update S A ((fun v : AReg => v.o.getD .sep) v :: S A) with hS1
    have h1G : S1 G = (L ++ Sym.sep2 :: G0).head?.getD .sep :: (L ++ Sym.sep2 :: G0).tail := by
      rw [hS1, Function.update_of_ne hGA, hG']
      rcases L with _ | ⟨y, L⟩ <;> rfl
    have e2 := eval_popO G v S1 _ _ h1G
    obtain ⟨v', e3⟩ := rwLoop_eval hGA G0 L { v with o := some ((L ++ Sym.sep2 :: G0).head?.getD
      .sep) } (Function.update S1 G (L ++ Sym.sep2 :: G0).tail) hL'
      (by rw [Function.update_self]) (by rcases L with _ | ⟨y, L⟩ <;> rfl)
    refine ⟨v', (Eval.loop_true hc (Eval.seq e1 e2) e3).of_eq ?_ ?_⟩
    · congr 1
      funext k
      by_cases hkA : k = A
      · subst hkA
        simp [hS1, Function.update_apply, hGA.symm, hvo]
      · by_cases hkG : k = G
        · subst hkG
          simp [hS1, Function.update_apply, hGA, hkA]
        · simp [hS1, Function.update_apply, hkA, hkG]
    · simp only [List.length_cons]
      ring

theorem eval_rewindG {G A : K} (hGA : G ≠ A) (L G0 : List Sym) (v : AReg) (S : K → List Sym)
    (hL : Sym.sep2 ∉ L) (hG : S G = L ++ Sym.sep2 :: G0) :
    ∃ v' : AReg, Eval [] (rewindG G A) ⟨v, S⟩
      ⟨v', Function.update (Function.update S G G0) A (L.reverse ++ S A)⟩ (3 * L.length + 2) := by
  have hG' : S G = (L ++ Sym.sep2 :: G0).head?.getD .sep :: (L ++ Sym.sep2 :: G0).tail := by
    rw [hG]; rcases L with _ | ⟨y, L⟩ <;> rfl
  have e1 := eval_popO G v S _ _ hG'
  obtain ⟨v', e2⟩ := rwLoop_eval hGA G0 L
    { v with o := some ((L ++ Sym.sep2 :: G0).head?.getD .sep) }
    (Function.update S G (L ++ Sym.sep2 :: G0).tail) hL (by rw [Function.update_self])
    (by rcases L with _ | ⟨y, L⟩ <;> rfl)
  refine ⟨v', (Eval.seq e1 e2).of_eq ?_ (by ring)⟩
  congr 1
  funext k
  by_cases hkA : k = A
  · subst hkA
    simp [Function.update_apply, hGA.symm]
  · by_cases hkG : k = G
    · subst hkG
      simp [Function.update_apply, hkA]
    · simp [Function.update_apply, hkA, hkG]

theorem eval_copyR {R X D : K} (hRX : R ≠ X) (hRD : R ≠ D) (hXD : X ≠ D) (n : ℕ)
    (DR : List Sym) (v : AReg) (S : K → List Sym) (hDR : DR.head? ≠ some .mark)
    (hR : S R = List.replicate n .mark ++ DR) (hX : (S X).head? ≠ some .mark) :
    ∃ v' : AReg, Eval [] (copyR R X D) ⟨v, S⟩
      ⟨v', Function.update S D (List.replicate n .mark ++ S D)⟩ (9 * n + 4) := by
  have e1 := eval_peekR R v S
  rw [hR] at e1
  have e2 := copyLoop_eval hRX hRD hXD n DR { v with r := (List.replicate n Sym.mark ++ DR).head? }
    S hDR hR rfl
  set S2 := Function.update (Function.update (Function.update S R DR) X
    (List.replicate n .mark ++ S X)) D (List.replicate n .mark ++ S D) with hS2
  have h2X : S2 X = List.replicate n .mark ++ S X := by
    rw [hS2, Function.update_of_ne hXD, Function.update_self]
  have e3 := moveMarks_eval hRX.symm n (S X)
    { { v with r := (List.replicate n Sym.mark ++ DR).head? } with r := DR.head? } S2 hX h2X
  refine ⟨{ { { v with r := (List.replicate n Sym.mark ++ DR).head? } with r := DR.head? } with
    r := (S X).head? }, (Eval.seq (Eval.seq e1 e2) e3).of_eq ?_ (by ring)⟩
  congr 1
  funext k
  simp only [hS2, Function.update_apply]
  split_ifs <;> simp_all

theorem eval_subR {R X D : K} (hRX : R ≠ X) (hRD : R ≠ D) (hXD : X ≠ D) (n k : ℕ)
    (DR DD : List Sym) (v : AReg) (S : K → List Sym) (hDR : DR.head? ≠ some .mark)
    (hR : S R = List.replicate n .mark ++ DR) (hX : (S X).head? ≠ some .mark)
    (hD : S D = List.replicate (n + k) .mark ++ DD) :
    ∃ v' : AReg, Eval [] (subR R X D) ⟨v, S⟩
      ⟨v', Function.update S D (List.replicate k .mark ++ DD)⟩ (9 * n + 4) := by
  have e1 := eval_peekR R v S
  rw [hR] at e1
  have e2 := subLoop_eval hRX hRD hXD n k DR DD
    { v with r := (List.replicate n Sym.mark ++ DR).head? } S hDR hR hD rfl
  set S2 := Function.update (Function.update (Function.update S R DR) X
    (List.replicate n .mark ++ S X)) D (List.replicate k .mark ++ DD) with hS2
  have h2X : S2 X = List.replicate n .mark ++ S X := by
    rw [hS2, Function.update_of_ne hXD, Function.update_self]
  have e3 := moveMarks_eval hRX.symm n (S X)
    { { v with r := (List.replicate n Sym.mark ++ DR).head? } with r := DR.head? } S2 hX h2X
  refine ⟨{ { { v with r := (List.replicate n Sym.mark ++ DR).head? } with r := DR.head? } with
    r := (S X).head? }, (Eval.seq (Eval.seq e1 e2) e3).of_eq ?_ (by ring)⟩
  congr 1
  funext k
  simp only [hS2, Function.update_apply]
  split_ifs <;> simp_all

end EvalA

/-! ## Evaluation lemmas: field loops, simultaneous walk -/

section EvalB

variable {K : Type} [DecidableEq K]

theorem dfLoop_eval {A B X Y : K} (hAB : A ≠ B) (hAX : A ≠ X) (hAY : A ≠ Y) (hBX : B ≠ X)
    (hBY : B ≠ Y) (hXY : X ≠ Y) (rest DX DY : List Sym) (hDX : DX.head? ≠ some .mark)
    (hDY : DY.head? ≠ some .mark) :
    ∀ (L : List Bool) (m : ℕ) (v : AReg) (S : K → List Sym),
      S A = L.map Sym.bit ++ Sym.mark :: rest → S X = List.replicate m .mark ++ DX → S Y = DY →
      v.q = (L.map Sym.bit ++ Sym.mark :: rest).head? →
      ∃ (v' : AReg) (t : ℕ), Eval [] (dfLoop A B X Y) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S A (Sym.mark :: rest)) B
          (L.reverse.map Sym.bit ++ S B)) X
          (List.replicate (m * 2 ^ (L.count false)) .mark ++ DX)⟩ t ∧
        t + 9 * m ≤ 9 * (m * 2 ^ (L.count false)) + 10 * L.length + 1
  | [], m, v, S, hA, hX, _, hv => by
    simp only [List.map_nil, List.nil_append] at hA hv
    refine ⟨v, 1, (Eval.loop_false (by rw [hv]; rfl)).of_eq ?_ rfl,
      by simp only [List.count_nil, pow_zero, mul_one, List.length_nil, mul_zero,
        add_zero] <;> omega⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.map_nil, List.nil_append,
      List.count_nil, pow_zero, mul_one]
    split_ifs <;> simp_all
  | b :: L, m, v, S, hA, hX, hY, hv => by
    have hA' : S A = Sym.bit b :: (L.map Sym.bit ++ Sym.mark :: rest) := by rw [hA]; rfl
    have hvq : v.q = some (Sym.bit b) := by rw [hv]; rfl
    have e1 := eval_popO A v S _ _ hA'
    set S1 := Function.update S A (L.map Sym.bit ++ Sym.mark :: rest) with hS1
    have e2 : Eval [] (.push B fun v : AReg => v.o.getD .sep)
        ⟨{ v with o := some (Sym.bit b) }, S1⟩
        ⟨{ v with o := some (Sym.bit b) }, Function.update S1 B (Sym.bit b :: S1 B)⟩ 1 :=
      Eval.push [] B _ _ S1
    set S2 := Function.update S1 B (Sym.bit b :: S1 B) with hS2
    have h2X : S2 X = List.replicate m .mark ++ DX := by
      rw [hS2, Function.update_of_ne hBX.symm, hS1, Function.update_of_ne hAX.symm, hX]
    have h2Y : S2 Y = DY := by
      rw [hS2, Function.update_of_ne hBY.symm, hS1, Function.update_of_ne hAY.symm, hY]
    have h2A : S2 A = L.map Sym.bit ++ Sym.mark :: rest := by
      rw [hS2, Function.update_of_ne hAB, hS1, Function.update_self]
    -- the conditional doubling, then the peek
    obtain ⟨m', v3, t3, e3, hv3o, hv3q, hm', ht3⟩ : ∃ (m' : ℕ) (v3 : AReg) (t3 : ℕ),
        Eval [] (.ite (fun v : AReg => isZeroO v.o) (double X Y) skipA)
          ⟨{ v with o := some (Sym.bit b) }, S2⟩
          ⟨v3, Function.update S2 X (List.replicate m' .mark ++ DX)⟩ t3 ∧
        v3.o = some (Sym.bit b) ∧ v3.q = v.q ∧
        m' * 2 ^ (L.count false) = m * 2 ^ ((b :: L).count false) ∧
        t3 + 9 * m + 9 * m' ≤ 18 * m' + 5 := by
      cases b
      · refine ⟨2 * m, _, _, Eval.ite_true rfl (double_eval hXY m DX DY _ S2 hDX hDY h2X h2Y),
          rfl, rfl, ?_, by omega⟩
        simp [List.count_cons, pow_succ]
        ring
      · refine ⟨m, { v with o := some (Sym.bit true) }, _,
          (Eval.ite_false rfl (eval_skipA _ S2)).of_eq ?_ rfl, rfl, rfl, ?_, by omega⟩
        · rw [← h2X, Function.update_eq_self]
        · simp [List.count_cons]
    set S3 := Function.update S2 X (List.replicate m' .mark ++ DX) with hS3
    have h3A : S3 A = L.map Sym.bit ++ Sym.mark :: rest := by
      rw [hS3, Function.update_of_ne hAX, h2A]
    have h3Y : S3 Y = DY := by rw [hS3, Function.update_of_ne hXY.symm, h2Y]
    have e4 := eval_peekQ A v3 S3
    rw [h3A] at e4
    obtain ⟨v', t', e5, ht'⟩ := dfLoop_eval hAB hAX hAY hBX hBY hXY rest DX DY hDX hDY L m'
      { v3 with q := (L.map Sym.bit ++ Sym.mark :: rest).head? } S3 h3A
      (by rw [hS3, Function.update_self]) h3Y rfl
    have hc : isBitO v.q = true := by rw [hvq]; rfl
    refine ⟨v', _, (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) e5).of_eq ?_
      rfl, ?_⟩
    · congr 1
      funext k
      simp only [hS3, hS2, hS1, Function.update_apply, hm', List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      split_ifs <;> simp_all
    · rw [← hm']
      simp only [List.length_cons]
      nlinarith

theorem eval_dblField {A B X Y : K} (hAB : A ≠ B) (hAX : A ≠ X) (hAY : A ≠ Y) (hBX : B ≠ X)
    (hBY : B ≠ Y) (hXY : X ≠ Y) (a : ℕ) (rest DX DY : List Sym) (hDX : DX.head? ≠ some .mark)
    (hDY : DY.head? ≠ some .mark) (m : ℕ) (v : AReg) (S : K → List Sym)
    (hA : S A = natSyms (2 ^ a) ++ Sym.mark :: rest) (hX : S X = List.replicate m .mark ++ DX)
    (hY : S Y = DY) :
    ∃ (v' : AReg) (t : ℕ), Eval [] (dblField A B X Y) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S A rest) B
        ((natSyms (2 ^ a) ++ [Sym.mark]).reverse ++ S B)) X
        (List.replicate (m * 2 ^ a) .mark ++ DX)⟩ t ∧
      t + 9 * m ≤ 9 * (m * 2 ^ a) + 10 * bitLen (2 ^ a) + 4 := by
  set L := List.replicate a false ++ [true] with hL
  have hA' : S A = L.map Sym.bit ++ Sym.mark :: rest := by
    rw [hA, natSyms, encodeNat_two_pow']
  have hcount : L.count false = a := by simp [hL, List.count_replicate]
  have e1 := eval_peekQ A v S
  rw [hA'] at e1
  obtain ⟨v2, t2, e2, ht2⟩ := dfLoop_eval hAB hAX hAY hBX hBY hXY rest DX DY hDX hDY L m
    { v with q := (L.map Sym.bit ++ Sym.mark :: rest).head? } S hA' hX hY rfl
  rw [hcount] at e2 ht2
  set S2 := Function.update (Function.update (Function.update S A (Sym.mark :: rest)) B
    (L.reverse.map Sym.bit ++ S B)) X (List.replicate (m * 2 ^ a) .mark ++ DX) with hS2
  have h2A : S2 A = Sym.mark :: rest := by
    rw [hS2, Function.update_of_ne hAX, Function.update_of_ne hAB, Function.update_self]
  have e3 := eval_mvSym hAB Sym.mark rest v2 S2 h2A
  refine ⟨{ v2 with o := some Sym.mark }, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    simp only [hS2, Function.update_apply, natSyms, encodeNat_two_pow', List.reverse_append,
      List.map_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons_append, ← hL]
    split_ifs <;> simp_all
  · have hlen : L.length = a + 1 := by simp [hL]
    rw [bitLen_two_pow]
    rw [hlen] at ht2
    omega

theorem pfLoop_eval {Ct W A B X Y : K} (hCW : Ct ≠ W) (hCA : Ct ≠ A) (hCB : Ct ≠ B)
    (hCX : Ct ≠ X) (hCY : Ct ≠ Y) (hWA : W ≠ A) (hWB : W ≠ B) (hWX : W ≠ X) (hWY : W ≠ Y)
    (hAB : A ≠ B) (hAX : A ≠ X) (hAY : A ≠ Y) (hBX : B ≠ X) (hBY : B ≠ Y) (hXY : X ≠ Y)
    (DC rest DX DY : List Sym) (hDC : DC.head? ≠ some .mark) (hDX : DX.head? ≠ some .mark)
    (hDY : DY.head? ≠ some .mark) :
    ∀ (fs : List ℕ) (m : ℕ) (v : AReg) (S : K → List Sym),
      (∀ f ∈ fs, ∃ a, 1 ≤ a ∧ f = 2 ^ a) →
      S Ct = List.replicate fs.length .mark ++ DC → S A = hdrSyms fs ++ rest →
      S X = List.replicate m .mark ++ DX → S Y = DY →
      v.r = (List.replicate fs.length Sym.mark ++ DC).head? →
      ∃ (v' : AReg) (t : ℕ), Eval [] (walkLoop Ct W (dblField A B X Y)) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update
          (Function.update S Ct DC) W (List.replicate fs.length .mark ++ S W)) A rest) B
          ((hdrSyms fs).reverse ++ S B)) X (List.replicate (m * fs.prod) .mark ++ DX)⟩ t ∧
        t + 18 * m ≤ 18 * (m * fs.prod) + 10 * (hdrSyms fs).length + 1
  | [], m, v, S, _, hC, hA, hX, _, hv => by
    simp only [List.length_nil, List.replicate_zero, List.nil_append, hdrSyms_nil'] at hC hA hv
    refine ⟨v, 1, (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hDC)).of_eq ?_ rfl,
      by simp only [List.prod_nil, mul_one, hdrSyms_nil', List.length_nil, mul_zero,
        add_zero] <;> omega⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append,
      hdrSyms_nil', List.reverse_nil, List.prod_nil, mul_one]
    split_ifs <;> simp_all
  | f :: fs, m, v, S, hpow, hC, hA, hX, hY, hv => by
    obtain ⟨a, ha1, rfl⟩ := hpow f List.mem_cons_self
    have hpow' : ∀ f ∈ fs, ∃ a, 1 ≤ a ∧ f = 2 ^ a := fun f hf => hpow f (List.mem_cons_of_mem _ hf)
    have hC' : S Ct = List.replicate (fs.length + 1) .mark ++ DC := by
      rw [hC, List.length_cons]
    set S1 := Function.update (Function.update S Ct (List.replicate fs.length .mark ++ DC)) W
      (.mark :: S W) with hS1
    have h1A : S1 A = natSyms (2 ^ a) ++ Sym.mark :: (hdrSyms fs ++ rest) := by
      rw [hS1, Function.update_of_ne hWA.symm, Function.update_of_ne hCA.symm, hA, hdrSyms_cons']
      simp
    have h1X : S1 X = List.replicate m .mark ++ DX := by
      rw [hS1, Function.update_of_ne hWX.symm, Function.update_of_ne hCX.symm, hX]
    have h1Y : S1 Y = DY := by
      rw [hS1, Function.update_of_ne hWY.symm, Function.update_of_ne hCY.symm, hY]
    obtain ⟨vb, tb, eb, htb⟩ := eval_dblField hAB hAX hAY hBX hBY hXY a (hdrSyms fs ++ rest)
      DX DY hDX hDY m v S1 h1A h1X h1Y
    set S2 := Function.update (Function.update (Function.update S1 A (hdrSyms fs ++ rest)) B
      ((natSyms (2 ^ a) ++ [Sym.mark]).reverse ++ S1 B)) X
      (List.replicate (m * 2 ^ a) .mark ++ DX) with hS2
    have h2C : S2 Ct = List.replicate fs.length .mark ++ DC := by
      rw [hS2, Function.update_of_ne hCX, Function.update_of_ne hCB, Function.update_of_ne hCA,
        hS1, Function.update_of_ne hCW, Function.update_self]
    have es := walkStep_eval hCW (dblField A B X Y) fs.length DC v S hC' eb h2C
    have h2A : S2 A = hdrSyms fs ++ rest := by
      rw [hS2, Function.update_of_ne hAX, Function.update_of_ne hAB, Function.update_self]
    have h2X : S2 X = List.replicate (m * 2 ^ a) .mark ++ DX := by
      rw [hS2, Function.update_self]
    have h2Y : S2 Y = DY := by
      rw [hS2, Function.update_of_ne hXY.symm, Function.update_of_ne hBY.symm,
        Function.update_of_ne hAY.symm, h1Y]
    obtain ⟨v', t', e', ht'⟩ := pfLoop_eval hCW hCA hCB hCX hCY hWA hWB hWX hWY hAB hAX hAY hBX
      hBY hXY DC rest DX DY hDC hDX hDY fs (m * 2 ^ a)
      { vb with r := (List.replicate fs.length Sym.mark ++ DC).head? } S2 hpow' h2C h2A h2X h2Y rfl
    have hc : isMarkO v.r = true := by
      rw [hv, List.length_cons, replicate_mark_head]
      rfl
    refine ⟨v', _, (Eval.loop_true hc es e').of_eq ?_ rfl, ?_⟩
    · congr 1
      funext k
      simp only [hS2, hS1, Function.update_apply, List.length_cons, List.replicate_succ,
        List.cons_append, rep_cons, hdrSyms_cons', List.reverse_append, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.prod_cons, mul_assoc]
      split_ifs <;> simp_all [rep_cons]
    · have h2a : 2 ≤ 2 ^ a := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
      have hm2 : 2 * m ≤ m * 2 ^ a := by nlinarith
      rw [length_hdrSyms_cons, List.prod_cons]
      have hassoc : m * (2 ^ a * fs.prod) = m * 2 ^ a * fs.prod := by ring
      rw [hassoc]
      have hbl := bitLen_two_pow a
      nlinarith

theorem eval_prodFields {Ct W A B X Y : K} (hCW : Ct ≠ W) (hCA : Ct ≠ A) (hCB : Ct ≠ B)
    (hCX : Ct ≠ X) (hCY : Ct ≠ Y) (hWA : W ≠ A) (hWB : W ≠ B) (hWX : W ≠ X) (hWY : W ≠ Y)
    (hAB : A ≠ B) (hAX : A ≠ X) (hAY : A ≠ Y) (hBX : B ≠ X) (hBY : B ≠ Y) (hXY : X ≠ Y)
    (fs : List ℕ) (hpow : ∀ f ∈ fs, ∃ a, 1 ≤ a ∧ f = 2 ^ a) (m : ℕ)
    (DC rest DX DY : List Sym) (hDC : DC.head? ≠ some .mark) (hDX : DX.head? ≠ some .mark)
    (hDY : DY.head? ≠ some .mark) (v : AReg) (S : K → List Sym)
    (hC : S Ct = List.replicate fs.length .mark ++ DC) (hW : (S W).head? ≠ some .mark)
    (hA : S A = hdrSyms fs ++ rest) (hX : S X = List.replicate m .mark ++ DX) (hY : S Y = DY) :
    ∃ (v' : AReg) (t : ℕ), Eval [] (prodFields Ct W A B X Y) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S A rest) B
        ((hdrSyms fs).reverse ++ S B)) X (List.replicate (m * fs.prod) .mark ++ DX)⟩ t ∧
      t ≤ 18 * (m * fs.prod) + 10 * (hdrSyms fs).length + 4 * fs.length + 4 := by
  have e1 := eval_peekR Ct v S
  rw [hC] at e1
  obtain ⟨v2, t2, e2, ht2⟩ := pfLoop_eval hCW hCA hCB hCX hCY hWA hWB hWX hWY hAB hAX hAY hBX hBY
    hXY DC rest DX DY hDC hDX hDY fs m
    { v with r := (List.replicate fs.length Sym.mark ++ DC).head? } S hpow hC hA hX hY rfl
  set S2 := Function.update (Function.update (Function.update (Function.update
    (Function.update S Ct DC) W (List.replicate fs.length .mark ++ S W)) A rest) B
    ((hdrSyms fs).reverse ++ S B)) X (List.replicate (m * fs.prod) .mark ++ DX) with hS2
  have h2W : S2 W = List.replicate fs.length .mark ++ S W := by
    rw [hS2, Function.update_of_ne hWX, Function.update_of_ne hWB, Function.update_of_ne hWA,
      Function.update_self]
  have e3 := moveMarks_eval hCW.symm fs.length (S W) v2 S2 hW h2W
  refine ⟨{ v2 with r := (S W).head? }, _, (Eval.seq (Eval.seq e1 e2) e3).of_eq ?_ rfl,
    by omega⟩
  congr 1
  funext k
  simp only [hS2, Function.update_apply]
  split_ifs <;> simp_all

theorem cfLoop_eval {A B X : K} (hAB : A ≠ B) (hAX : A ≠ X) (hBX : B ≠ X) (rest : List Sym) :
    ∀ (L : List Bool) (v : AReg) (S : K → List Sym),
      S A = L.map Sym.bit ++ Sym.mark :: rest → v.q = (L.map Sym.bit ++ Sym.mark :: rest).head? →
      ∃ v' : AReg, Eval [] (cfLoop A B X) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S A (Sym.mark :: rest)) B
          (L.reverse.map Sym.bit ++ S B)) X (List.replicate L.length .mark ++ S X)⟩
          (5 * L.length + 1)
  | [], v, S, hA, hv => by
    simp only [List.map_nil, List.nil_append] at hA hv
    refine ⟨v, (Eval.loop_false (by rw [hv]; rfl)).of_eq ?_ rfl⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.map_nil, List.nil_append,
      List.length_nil, List.replicate_zero]
    split_ifs <;> simp_all
  | b :: L, v, S, hA, hv => by
    have hA' : S A = Sym.bit b :: (L.map Sym.bit ++ Sym.mark :: rest) := by rw [hA]; rfl
    have hvq : v.q = some (Sym.bit b) := by rw [hv]; rfl
    have e1 := eval_popO A v S _ _ hA'
    set S1 := Function.update S A (L.map Sym.bit ++ Sym.mark :: rest) with hS1
    have e2 : Eval [] (.push B fun v : AReg => v.o.getD .sep)
        ⟨{ v with o := some (Sym.bit b) }, S1⟩
        ⟨{ v with o := some (Sym.bit b) }, Function.update S1 B (Sym.bit b :: S1 B)⟩ 1 :=
      Eval.push [] B _ _ S1
    set S2 := Function.update S1 B (Sym.bit b :: S1 B) with hS2
    have e3 := eval_pushS X Sym.mark { v with o := some (Sym.bit b) } S2
    set S3 := Function.update S2 X (Sym.mark :: S2 X) with hS3
    have h3A : S3 A = L.map Sym.bit ++ Sym.mark :: rest := by
      rw [hS3, Function.update_of_ne hAX, hS2, Function.update_of_ne hAB, hS1,
        Function.update_self]
    have e4 := eval_peekQ A { v with o := some (Sym.bit b) } S3
    rw [h3A] at e4
    obtain ⟨v', e5⟩ := cfLoop_eval hAB hAX hBX rest L
      { { v with o := some (Sym.bit b) } with q := (L.map Sym.bit ++ Sym.mark :: rest).head? } S3
      h3A rfl
    have hc : isBitO v.q = true := by rw [hvq]; rfl
    refine ⟨v', (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) e5).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [hS3, hS2, hS1, Function.update_apply, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append, List.length_cons,
        List.replicate_succ, List.cons_append, rep_cons]
      split_ifs <;> simp_all [rep_cons]
    · simp only [List.length_cons]
      ring

theorem eval_cntField {A B X : K} (hAB : A ≠ B) (hAX : A ≠ X) (hBX : B ≠ X) (n : ℕ)
    (rest : List Sym) (v : AReg) (S : K → List Sym) (hA : S A = natSyms n ++ Sym.mark :: rest) :
    ∃ v' : AReg, Eval [] (cntField A B X) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S A rest) B
        ((natSyms n ++ [Sym.mark]).reverse ++ S B)) X
        (List.replicate (bitLen n) .mark ++ S X)⟩ (5 * bitLen n + 4) := by
  have hA' : S A = (encodeNat n).map Sym.bit ++ Sym.mark :: rest := hA
  have e1 := eval_peekQ A v S
  rw [hA'] at e1
  obtain ⟨v2, e2⟩ := cfLoop_eval hAB hAX hBX rest (encodeNat n)
    { v with q := ((encodeNat n).map Sym.bit ++ Sym.mark :: rest).head? } S hA' rfl
  set S2 := Function.update (Function.update (Function.update S A (Sym.mark :: rest)) B
    ((encodeNat n).reverse.map Sym.bit ++ S B)) X
    (List.replicate (encodeNat n).length .mark ++ S X) with hS2
  have h2A : S2 A = Sym.mark :: rest := by
    rw [hS2, Function.update_of_ne hAX, Function.update_of_ne hAB, Function.update_self]
  have e3 := eval_mvSym hAB Sym.mark rest v2 S2 h2A
  refine ⟨{ v2 with o := some Sym.mark }, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [hS2, Function.update_apply, natSyms, bitLen, List.reverse_append,
      List.map_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons_append]
    split_ifs <;> simp_all
  · simp only [bitLen] <;> ring

theorem minLoop_eval {A B TA TB W : K} (hAB : A ≠ B) (hATA : A ≠ TA) (hATB : A ≠ TB)
    (hAW : A ≠ W) (hBTA : B ≠ TA) (hBTB : B ≠ TB) (hBW : B ≠ W) (hTATB : TA ≠ TB)
    (hTAW : TA ≠ W) (hTBW : TB ≠ W) (DA DB : List Sym) (hDA : DA.head? ≠ some .mark)
    (hDB : DB.head? ≠ some .mark) :
    ∀ (a b : ℕ) (v : AReg) (S : K → List Sym),
      S A = List.replicate a .mark ++ DA → S B = List.replicate b .mark ++ DB →
      v.r = (List.replicate a Sym.mark ++ DA).head? →
      v.q = (List.replicate b Sym.mark ++ DB).head? →
      ∃ v' : AReg, Eval [] (minLoop A B TA TB W) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update
          (Function.update S A (List.replicate (a - min a b) .mark ++ DA)) B
          (List.replicate (b - min a b) .mark ++ DB)) TA
          (List.replicate (min a b) .mark ++ S TA)) TB
          (List.replicate (min a b) .mark ++ S TB)) W
          (List.replicate (min a b) .mark ++ S W)⟩ (8 * min a b + 1)
  | 0, b, v, S, hA, hB, hr, hq => by
    simp only [List.replicate_zero, List.nil_append] at hA hr
    refine ⟨v, (Eval.loop_false ?_).of_eq ?_ (by simp)⟩
    · rw [hr, isMarkO_false_of_ne hDA]
      rfl
    · congr 1
      rw [Nat.zero_min, Nat.zero_sub, Nat.sub_zero]
      simp only [List.replicate_zero, List.nil_append]
      rw [← hA, ← hB, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
        Function.update_eq_self, Function.update_eq_self]
  | a + 1, 0, v, S, hA, hB, hr, hq => by
    simp only [List.replicate_zero, List.nil_append] at hB hq
    refine ⟨v, (Eval.loop_false ?_).of_eq ?_ (by simp)⟩
    · rw [hq, isMarkO_false_of_ne hDB, Bool.and_false]
    · congr 1
      rw [Nat.min_zero, Nat.sub_zero, Nat.zero_sub]
      simp only [List.replicate_zero, List.nil_append]
      rw [← hA, ← hB, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
        Function.update_eq_self, Function.update_eq_self]
  | a + 1, b + 1, v, S, hA, hB, hr, hq => by
    have hA' : S A = Sym.mark :: (List.replicate a .mark ++ DA) := by
      rw [hA, List.replicate_succ, List.cons_append]
    have hB' : S B = Sym.mark :: (List.replicate b .mark ++ DB) := by
      rw [hB, List.replicate_succ, List.cons_append]
    have e1 := eval_drop1 A v S _ _ hA'
    set S1 := Function.update S A (List.replicate a .mark ++ DA) with hS1
    have e2 := eval_pushS TA Sym.mark v S1
    set S2 := Function.update S1 TA (Sym.mark :: S1 TA) with hS2
    have h2B : S2 B = Sym.mark :: (List.replicate b .mark ++ DB) := by
      rw [hS2, Function.update_of_ne hBTA, hS1, Function.update_of_ne hAB.symm, hB']
    have e3 := eval_drop1 B v S2 _ _ h2B
    set S3 := Function.update S2 B (List.replicate b .mark ++ DB) with hS3
    have e4 := eval_pushS TB Sym.mark v S3
    set S4 := Function.update S3 TB (Sym.mark :: S3 TB) with hS4
    have e5 := eval_pushS W Sym.mark v S4
    set S5 := Function.update S4 W (Sym.mark :: S4 W) with hS5
    have h5A : S5 A = List.replicate a .mark ++ DA := by
      rw [hS5, Function.update_of_ne hAW, hS4, Function.update_of_ne hATB, hS3,
        Function.update_of_ne hAB, hS2, Function.update_of_ne hATA, hS1, Function.update_self]
    have h5B : S5 B = List.replicate b .mark ++ DB := by
      rw [hS5, Function.update_of_ne hBW, hS4, Function.update_of_ne hBTB, hS3,
        Function.update_self]
    have e6 := eval_peekR A v S5
    rw [h5A] at e6
    have e7 := eval_peekQ B { v with r := (List.replicate a Sym.mark ++ DA).head? } S5
    rw [h5B] at e7
    obtain ⟨v', e8⟩ := minLoop_eval hAB hATA hATB hAW hBTA hBTB hBW hTATB hTAW hTBW DA DB hDA hDB
      a b { { v with r := (List.replicate a Sym.mark ++ DA).head? } with
        q := (List.replicate b Sym.mark ++ DB).head? } S5 h5A h5B rfl rfl
    have hc : (isMarkO v.r && isMarkO v.q) = true := by
      rw [hr, hq, replicate_mark_head, replicate_mark_head]
      rfl
    refine ⟨v', (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      (Eval.seq e5 (Eval.seq e6 e7)))))) e8).of_eq ?_ ?_⟩
    · congr 1
      have h5TA : S5 TA = Sym.mark :: S TA := by
        rw [hS5, Function.update_of_ne hTAW, hS4, Function.update_of_ne hTATB, hS3,
          Function.update_of_ne hBTA.symm, hS2, Function.update_self, hS1,
          Function.update_of_ne hATA.symm]
      have h5TB : S5 TB = Sym.mark :: S TB := by
        rw [hS5, Function.update_of_ne hTBW, hS4, Function.update_self, hS3,
          Function.update_of_ne hBTB.symm, hS2, Function.update_of_ne hTATB.symm, hS1,
          Function.update_of_ne hATB.symm]
      have h5W : S5 W = Sym.mark :: S W := by
        rw [hS5, Function.update_self, hS4, Function.update_of_ne hTBW.symm, hS3,
          Function.update_of_ne hBW.symm, hS2, Function.update_of_ne hTAW.symm, hS1,
          Function.update_of_ne hAW.symm]
      have h5o : ∀ k, k ≠ A → k ≠ B → k ≠ TA → k ≠ TB → k ≠ W → S5 k = S k := by
        intro k h1 h2 h3 h4 h5
        rw [hS5, Function.update_of_ne h5, hS4, Function.update_of_ne h4, hS3,
          Function.update_of_ne h2, hS2, Function.update_of_ne h3, hS1, Function.update_of_ne h1]
      rw [Nat.add_min_add_right, Nat.add_sub_add_right, Nat.add_sub_add_right, h5TA, h5TB, h5W]
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
      funext k
      by_cases kW : k = W
      · subst kW
        simp only [Function.update_self]
      by_cases kTB : k = TB
      · subst kTB
        simp only [Function.update_of_ne kW, Function.update_self]
      by_cases kTA : k = TA
      · subst kTA
        simp only [Function.update_of_ne kW, Function.update_of_ne kTB, Function.update_self]
      by_cases kB : k = B
      · subst kB
        simp only [Function.update_of_ne kW, Function.update_of_ne kTB, Function.update_of_ne kTA,
          Function.update_self]
      by_cases kA : k = A
      · subst kA
        simp only [Function.update_of_ne kW, Function.update_of_ne kTB, Function.update_of_ne kTA,
          Function.update_of_ne kB, Function.update_self]
      · simp only [Function.update_of_ne kW, Function.update_of_ne kTB, Function.update_of_ne kTA,
          Function.update_of_ne kB, Function.update_of_ne kA]
        exact h5o k kA kB kTA kTB kW
    · rw [Nat.add_min_add_right]
      ring

theorem eval_minRulers {A B TA TB W : K} (hAB : A ≠ B) (hATA : A ≠ TA) (hATB : A ≠ TB)
    (hAW : A ≠ W) (hBTA : B ≠ TA) (hBTB : B ≠ TB) (hBW : B ≠ W) (hTATB : TA ≠ TB)
    (hTAW : TA ≠ W) (hTBW : TB ≠ W) (a b : ℕ) (DA DB : List Sym) (hDA : DA.head? ≠ some .mark)
    (hDB : DB.head? ≠ some .mark) (v : AReg) (S : K → List Sym)
    (hA : S A = List.replicate a .mark ++ DA) (hB : S B = List.replicate b .mark ++ DB) :
    ∃ v' : AReg, Eval [] (minRulers A B TA TB W) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update (Function.update
        (Function.update S A (List.replicate (a - min a b) .mark ++ DA)) B
        (List.replicate (b - min a b) .mark ++ DB)) TA
        (List.replicate (min a b) .mark ++ S TA)) TB
        (List.replicate (min a b) .mark ++ S TB)) W
        (List.replicate (min a b) .mark ++ S W)⟩ (8 * min a b + 3) := by
  have e1 := eval_peekR A v S
  rw [hA] at e1
  have e2 := eval_peekQ B { v with r := (List.replicate a Sym.mark ++ DA).head? } S
  rw [hB] at e2
  obtain ⟨v', e3⟩ := minLoop_eval hAB hATA hATB hAW hBTA hBTB hBW hTATB hTAW hTBW DA DB hDA hDB
    a b { { v with r := (List.replicate a Sym.mark ++ DA).head? } with
      q := (List.replicate b Sym.mark ++ DB).head? } S hA hB rfl rfl
  exact ⟨v', (Eval.seq e1 (Eval.seq e2 e3)).of_eq rfl (by ring)⟩

end EvalB

/-! ## `Runs` wrappers (register-agnostic) -/

section RunsW

variable {K : Type} [DecidableEq K]

theorem runs_pushS' (k : K) (y : Sym) (S : K → List Sym) :
    Runs (pushS k y) S (Function.update S k (y :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, eval_pushS k y v S, trivial, le_rfl⟩

theorem runs_drop1' (k : K) (S : K → List Sym) (y : Sym) (L : List Sym) (h : S k = y :: L) :
    Runs (drop1 k) S (Function.update S k L) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, eval_drop1 k v S y L h, trivial, le_rfl⟩

theorem runs_skipFlds' {A B : K} (hAB : A ≠ B) (fs : List ℕ) (L : List Sym) (S : K → List Sym)
    (hA : S A = hdrSyms fs ++ L) :
    Runs (skipFlds A B fs.length) S
      (Function.update (Function.update S A L) B ((hdrSyms fs).reverse ++ S B)) (fun _ => True)
      (4 * (hdrSyms fs).length + 1) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := eval_skipFlds hAB fs L v S hA
    exact ⟨v', _, e, trivial, le_rfl⟩

theorem runs_buildRuler' {N R C Y : K} (hNR : N ≠ R) (hNC : N ≠ C) (hNY : N ≠ Y) (hRC : R ≠ C)
    (hRY : R ≠ Y) (hCY : C ≠ Y) (n : ℕ) (rN DR : List Sym) (S : K → List Sym)
    (hrN : TermOK rN) (hDR : DR.head? ≠ some .mark) (hN : S N = natSyms n ++ rN)
    (hR : S R = DR) :
    Runs (buildRuler N R C Y) S (Function.update S R (List.replicate n .mark ++ DR))
      (fun _ => True) (9 * n + 16 * bitLen n + 8) :=
  Runs.of_eval fun v => by
    obtain ⟨v', t, e, ht⟩ := buildRuler_eval hNR hNC hNY hRC hRY hCY n rN DR v S hrN hDR hN hR
    exact ⟨v', t, e, trivial, ht⟩

theorem runs_prodFields' {Ct W A B X Y : K} (hCW : Ct ≠ W) (hCA : Ct ≠ A) (hCB : Ct ≠ B)
    (hCX : Ct ≠ X) (hCY : Ct ≠ Y) (hWA : W ≠ A) (hWB : W ≠ B) (hWX : W ≠ X) (hWY : W ≠ Y)
    (hAB : A ≠ B) (hAX : A ≠ X) (hAY : A ≠ Y) (hBX : B ≠ X) (hBY : B ≠ Y) (hXY : X ≠ Y)
    (fs : List ℕ) (hpow : ∀ f ∈ fs, ∃ a, 1 ≤ a ∧ f = 2 ^ a) (m : ℕ)
    (DC rest DX DY : List Sym) (hDC : DC.head? ≠ some .mark) (hDX : DX.head? ≠ some .mark)
    (hDY : DY.head? ≠ some .mark) (S : K → List Sym)
    (hC : S Ct = List.replicate fs.length .mark ++ DC) (hW : (S W).head? ≠ some .mark)
    (hA : S A = hdrSyms fs ++ rest) (hX : S X = List.replicate m .mark ++ DX) (hY : S Y = DY) :
    Runs (prodFields Ct W A B X Y) S
      (Function.update (Function.update (Function.update S A rest) B
        ((hdrSyms fs).reverse ++ S B)) X (List.replicate (m * fs.prod) .mark ++ DX))
      (fun _ => True) (18 * (m * fs.prod) + 10 * (hdrSyms fs).length + 4 * fs.length + 4) :=
  Runs.of_eval fun v => by
    obtain ⟨v', t, e, ht⟩ := eval_prodFields hCW hCA hCB hCX hCY hWA hWB hWX hWY hAB hAX hAY hBX
      hBY hXY fs hpow m DC rest DX DY hDC hDX hDY v S hC hW hA hX hY
    exact ⟨v', t, e, trivial, ht⟩

theorem runs_cntField' {A B X : K} (hAB : A ≠ B) (hAX : A ≠ X) (hBX : B ≠ X) (n : ℕ)
    (rest : List Sym) (S : K → List Sym) (hA : S A = natSyms n ++ Sym.mark :: rest) :
    Runs (cntField A B X) S
      (Function.update (Function.update (Function.update S A rest) B
        ((natSyms n ++ [Sym.mark]).reverse ++ S B)) X
        (List.replicate (bitLen n) .mark ++ S X)) (fun _ => True) (5 * bitLen n + 4) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := eval_cntField hAB hAX hBX n rest v S hA
    exact ⟨v', _, e, trivial, le_rfl⟩

theorem runs_copyR' {R X D : K} (hRX : R ≠ X) (hRD : R ≠ D) (hXD : X ≠ D) (n : ℕ)
    (DR : List Sym) (S : K → List Sym) (hDR : DR.head? ≠ some .mark)
    (hR : S R = List.replicate n .mark ++ DR) (hX : (S X).head? ≠ some .mark) :
    Runs (copyR R X D) S (Function.update S D (List.replicate n .mark ++ S D)) (fun _ => True)
      (9 * n + 4) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := eval_copyR hRX hRD hXD n DR v S hDR hR hX
    exact ⟨v', _, e, trivial, le_rfl⟩

theorem runs_subR' {R X D : K} (hRX : R ≠ X) (hRD : R ≠ D) (hXD : X ≠ D) (n k : ℕ)
    (DR DD : List Sym) (S : K → List Sym) (hDR : DR.head? ≠ some .mark)
    (hR : S R = List.replicate n .mark ++ DR) (hX : (S X).head? ≠ some .mark)
    (hD : S D = List.replicate (n + k) .mark ++ DD) :
    Runs (subR R X D) S (Function.update S D (List.replicate k .mark ++ DD)) (fun _ => True)
      (9 * n + 4) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := eval_subR hRX hRD hXD n k DR DD v S hDR hR hX hD
    exact ⟨v', _, e, trivial, le_rfl⟩

theorem runs_minRulers' {A B TA TB W : K} (hAB : A ≠ B) (hATA : A ≠ TA) (hATB : A ≠ TB)
    (hAW : A ≠ W) (hBTA : B ≠ TA) (hBTB : B ≠ TB) (hBW : B ≠ W) (hTATB : TA ≠ TB)
    (hTAW : TA ≠ W) (hTBW : TB ≠ W) (a b : ℕ) (DA DB : List Sym) (hDA : DA.head? ≠ some .mark)
    (hDB : DB.head? ≠ some .mark) (S : K → List Sym)
    (hA : S A = List.replicate a .mark ++ DA) (hB : S B = List.replicate b .mark ++ DB) :
    Runs (minRulers A B TA TB W) S
      (Function.update (Function.update (Function.update (Function.update
        (Function.update S A (List.replicate (a - min a b) .mark ++ DA)) B
        (List.replicate (b - min a b) .mark ++ DB)) TA
        (List.replicate (min a b) .mark ++ S TA)) TB
        (List.replicate (min a b) .mark ++ S TB)) W
        (List.replicate (min a b) .mark ++ S W)) (fun _ => True) (8 * min a b + 3) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := eval_minRulers hAB hATA hATB hAW hBTA hBTB hBW hTATB hTAW hTBW a b DA DB
      hDA hDB v S hA hB
    exact ⟨v', _, e, trivial, le_rfl⟩

theorem runs_copyIfEmpty_mark {A R X D : K} (S : K → List Sym) (L : List Sym)
    (hA : S A = Sym.mark :: L) :
    Runs (copyIfEmpty A R X D) S S (fun _ => True) 3 :=
  Runs.of_eval fun v => by
    have e1 := eval_peekR A v S
    rw [hA] at e1
    exact ⟨_, _, Eval.seq e1 (Eval.ite_true rfl (eval_skipA _ S)), trivial, le_rfl⟩

theorem runs_copyIfEmpty_empty {A R X D : K} (hRX : R ≠ X) (hRD : R ≠ D) (hXD : X ≠ D) (n : ℕ)
    (DR : List Sym) (S : K → List Sym) (hDR : DR.head? ≠ some .mark)
    (hR : S R = List.replicate n .mark ++ DR) (hX : (S X).head? ≠ some .mark)
    (hA : (S A).head? ≠ some .mark) :
    Runs (copyIfEmpty A R X D) S (Function.update S D (List.replicate n .mark ++ S D))
      (fun _ => True) (9 * n + 6) :=
  Runs.of_eval fun v => by
    have e1 := eval_peekR A v S
    obtain ⟨v', e2⟩ := eval_copyR hRX hRD hXD n DR { v with r := (S A).head? } S hDR hR hX
    refine ⟨v', _, Eval.seq e1 (Eval.ite_false ?_ e2), trivial, by omega⟩
    exact isMarkO_false_of_ne hA

theorem runs_moveMarks' {X R : K} (hXR : X ≠ R) (n : ℕ) (D : List Sym) (S : K → List Sym)
    (hD : D.head? ≠ some .mark) (hX : S X = List.replicate n .mark ++ D) :
    Runs (moveMarks X R) S
      (Function.update (Function.update S X D) R (List.replicate n .mark ++ S R))
      (fun _ => True) (4 * n + 2) :=
  Runs.of_eval fun v => ⟨_, _, moveMarks_eval hXR n D v S hD hX, trivial, le_rfl⟩

theorem runs_clearMarks' {R : K} (n : ℕ) (D : List Sym) (S : K → List Sym)
    (hD : D.head? ≠ some .mark) (hR : S R = List.replicate n .mark ++ D) :
    Runs (clearMarks R) S (Function.update S R D) (fun _ => True) (3 * n + 2) :=
  Runs.of_eval fun v => ⟨_, _, clearMarks_eval n D v S hD hR, trivial, le_rfl⟩

theorem runs_rewindG' {G A : K} (hGA : G ≠ A) (L G0 : List Sym) (S : K → List Sym)
    (hL : Sym.sep2 ∉ L) (hG : S G = L ++ Sym.sep2 :: G0) :
    Runs (rewindG G A) S (Function.update (Function.update S G G0) A (L.reverse ++ S A))
      (fun _ => True) (3 * L.length + 2) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := eval_rewindG hGA L G0 v S hL hG
    exact ⟨v', _, e, trivial, le_rfl⟩

end RunsW

end SubNLogN.Machine.Bridge.SpreadSetupAux
