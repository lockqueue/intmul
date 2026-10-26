import WP.W9sq.Entry1

/-!
# WP.W9sq.Entry2 — per-entry phases 3–5 (drop, round, emit)

All states are stated relative to the entry-start state `B0`:
* after phase 3 `dropP` (`stDr`): `S = REST`, `sD = xx − yy`, `sE = xy + yx`, every other
  temporary restored;
* after phase 4 `rndP` (`stRn`): `sR = re`, `sI = im` with `re = divRoundPow2 (xx − yy) q`,
  `im = −divRoundPow2 (xy + yx) q`;
* after phase 5 `emitP`: `sO += (entrySyms (re, im)).reverse`, every temporary restored.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Host states agreeing on the stacks `ks` and with `B0` off `ks` are equal. -/
theorem st_ext (ks : List HL) {f g : HL → List Sym} (B0 : HL → List Sym)
    (hks : ∀ k ∈ ks, f k = g k) (hf : ∀ k, k ∉ ks → f k = B0 k) (hg : ∀ k, k ∉ ks → g k = B0 k) :
    f = g := by
  funext k
  by_cases hk : k ∈ ks
  · exact hks k hk
  · rw [hf k hk, hg k hk]

/-! ## Phase 3: drop -/

/-- Drop both copies of `x` and `y` and the four products. -/
def dropP (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (dropInt J.dr J.lDr dfl sX).seq <| (dropInt J.dr J.lDr dfl sX2).seq <|
  (dropInt J.dr J.lDr dfl sY).seq <| (dropInt J.dr J.lDr dfl sY2).seq <|
  (dropInt J.dr J.lDr dfl sP1).seq <| (dropInt J.dr J.lDr dfl sP2).seq <|
  (dropInt J.dr J.lDr dfl sP3).seq (dropInt J.dr J.lDr dfl sP4)

theorem dropP_closed (J : SqI) : (dropP J).Closed :=
  ⟨dropInt_closed _ _ _ _, dropInt_closed _ _ _ _, dropInt_closed _ _ _ _, dropInt_closed _ _ _ _,
    dropInt_closed _ _ _ _, dropInt_closed _ _ _ _, dropInt_closed _ _ _ _, dropInt_closed _ _ _ _⟩

/-- The state after phase 3. -/
def stDr (B0 : HL → List Sym) (REST : List Sym) (w1 w2 : ℤ) : HL → List Sym :=
  Function.update (Function.update (Function.update B0 hS REST) sD (intSyms w1 ++ B0 sD)) sE
    (intSyms w2 ++ B0 sE)

theorem drop_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (B0 : HL → List Sym)
    (x y : ℤ) (REST : List Sym) (tX : TermOK (B0 sX)) (tX2 : TermOK (B0 sX2))
    (tY : TermOK (B0 sY)) (tY2 : TermOK (B0 sY2)) (tP1 : TermOK (B0 sP1))
    (tP2 : TermOK (B0 sP2)) (tP3 : TermOK (B0 sP3)) (tP4 : TermOK (B0 sP4)) :
    HT [] (stM (stA B0 x y REST) x y) (dropP J) (stDr B0 REST (x * x - y * y) (x * y + y * x))
      (8 + 2 * (C * (bitLen x.natAbs + 1)) + 2 * (C * (bitLen y.natAbs + 1)) +
        C * (bitLen (x * x).natAbs + 1) + C * (bitLen (y * y).natAbs + 1) +
        C * (bitLen (x * y).natAbs + 1) + C * (bitLen (y * x).natAbs + 1)) := by
  refine (HT.seq (HT.dropInt hJ.dr J.lDr dfl sX (by decide) _ x (B0 sX) tX
      (by simp [stM, stA]) []) <|
    HT.seq (HT.dropInt hJ.dr J.lDr dfl sX2 (by decide) _ x (B0 sX2) tX2 (by simp [stM, stA]) []) <|
    HT.seq (HT.dropInt hJ.dr J.lDr dfl sY (by decide) _ y (B0 sY) tY (by simp [stM, stA]) []) <|
    HT.seq (HT.dropInt hJ.dr J.lDr dfl sY2 (by decide) _ y (B0 sY2) tY2 (by simp [stM, stA]) []) <|
    HT.seq (HT.dropInt hJ.dr J.lDr dfl sP1 (by decide) _ (x * x) (B0 sP1) tP1
      (by simp [stM, stA]) []) <|
    HT.seq (HT.dropInt hJ.dr J.lDr dfl sP2 (by decide) _ (y * y) (B0 sP2) tP2
      (by simp [stM, stA]) []) <|
    HT.seq (HT.dropInt hJ.dr J.lDr dfl sP3 (by decide) _ (x * y) (B0 sP3) tP3
      (by simp [stM, stA]) []) <|
    HT.dropInt hJ.dr J.lDr dfl sP4 (by decide) _ (y * x) (B0 sP4) tP4
      (by simp [stM, stA]) []).of_eq ?_ ?_
  · refine st_ext [hS, sX, sX2, sY, sY2, sP1, sP2, sP3, sP4, sD, sE] B0 ?_ ?_ ?_
    · intro k hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [stDr, stM, stA]
    · intro k hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hk
      simp [stM, stA, hk]
    · intro k hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hk
      simp [stDr, hk]
  · omega

/-! ## Phase 4: round -/

/-- Round `sD` into `sR` (real part) and `sE` into `sI` (negated imaginary part). -/
def rndP (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (roundP J.lS J.an J.lAn J.sr J.lSr J.atT J.atF J.lAtT J.lAtF J.dr J.lDr dfl sD sR sQ sH sH1).seq
    (roundP J.lS J.an J.lAn J.sr J.lSr J.atF J.atT J.lAtF J.lAtT J.dr J.lDr dfl sE sI sQ sH sH1)

theorem rndP_closed (J : SqI) : (rndP J).Closed :=
  ⟨roundP_closed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, roundP_closed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

/-- The state after phase 4. -/
def stRn (B0 : HL → List Sym) (REST : List Sym) (re im : ℤ) : HL → List Sym :=
  Function.update (Function.update (Function.update B0 hS REST) sR (intSyms re ++ B0 sR)) sI
    (intSyms im ++ B0 sI)

theorem rnd_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (B0 : HL → List Sym)
    (REST : List Sym) (w1 w2 : ℤ) (q : ℕ) (hq : 0 < q) (rQ rH rH1 : List Sym) (hrQ : TermOK rQ)
    (hrH : TermOK rH) (hrH1 : TermOK rH1) (eQ : B0 sQ = natSyms q ++ rQ)
    (eH : B0 sH = natSyms (2 ^ (q - 1)) ++ rH) (eH1 : B0 sH1 = natSyms (2 ^ (q - 1) - 1) ++ rH1)
    (tD : TermOK (B0 sD)) (tE : TermOK (B0 sE)) (tR : TermOK (B0 sR)) (tI : TermOK (B0 sI)) :
    HT [] (stDr B0 REST w1 w2) (rndP J)
      (stRn B0 REST (divRoundPow2 w1 q) (-divRoundPow2 w2 q))
      (C * (bitLen w1.natAbs + q + 1) + C * (q + bitLen q + 1) + C * (bitLen w1.natAbs + 1) + C +
        2 + (C * (bitLen w2.natAbs + q + 1) + C * (q + bitLen q + 1) +
          C * (bitLen w2.natAbs + 1) + C + 2)) := by
  have hbH : bitLen (2 ^ (q - 1)) = q := by rw [bitLen_two_pow]; omega
  refine (HT.seq (HT.roundP J.lS hJ.an hJ.sr hJ.atT hJ.atF hJ.dr J.lAn J.lSr J.lAtT J.lAtF J.lDr
      dfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ w1 (B0 sD) tD (by simp [stDr]) (by simpa [stDr] using tR) q (2 ^ (q - 1))
      rQ rH rH1 hrQ hrH hrH1 (by simp [stDr, eQ]) (by simp [stDr, eH]) (by simp [stDr, eH1]))
    (HT.roundP J.lS hJ.an hJ.sr hJ.atF hJ.atT hJ.dr J.lAn J.lSr J.lAtF J.lAtT J.lDr
      dfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ w2 (B0 sE) tE (by simp [stDr]) (by simpa [stDr] using tI) q (2 ^ (q - 1))
      rQ rH rH1 hrQ hrH hrH1 (by simp [stDr, eQ]) (by simp [stDr, eH]) (by simp [stDr, eH1]))).of_eq
    ?_ ?_
  · rw [rnd_re hq, rnd_im hq]
    funext k
    simp only [stRn, stDr, Function.update_apply]
    split_ifs <;> simp_all
  · rw [hbH]

/-! ## Phase 5: emit -/

/-- Push `(entrySyms (re, im)).reverse` on `sO`. -/
def emitP (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (emitInt J.lS sR sO).seq <| (pushS sO Sym.sep2).seq <| (emitInt J.lS sI sO).seq (pushS sO Sym.sep)

theorem emitP_closed (J : SqI) : (emitP J).Closed :=
  ⟨emitInt_closed _ _ _, trivial, emitInt_closed _ _ _, trivial⟩

theorem emit_spec (J : SqI) (B0 : HL → List Sym) (REST : List Sym) (re im : ℤ)
    (tR : TermOK (B0 sR)) (tI : TermOK (B0 sI)) :
    HT [] (stRn B0 REST re im) (emitP J)
      (Function.update (Function.update B0 hS REST) sO ((entrySyms (re, im)).reverse ++ B0 sO))
      (3 * bitLen re.natAbs + 6 + (1 + (3 * bitLen im.natAbs + 6 + 1))) := by
  refine (HT.seq (HT.emitInt J.lS (by decide) _ re (B0 sR) tR (by simp [stRn])) <|
    HT.seq (HT.pushS sO Sym.sep2 _ []) <|
    HT.seq (HT.emitInt J.lS (by decide) _ im (B0 sI) tI (by simp [stRn])) <|
    HT.pushS sO Sym.sep _ []).of_eq ?_ le_rfl
  funext k
  simp only [stRn, Function.update_apply, entrySyms, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append]
  split_ifs <;> simp_all

#assert_std_axioms st_ext dropP_closed drop_spec rndP_closed rnd_spec emitP_closed emit_spec

end WP.W9sq
