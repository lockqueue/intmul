/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreDefs
import SubNLogN.Machine.Calculus.FramePassR
import IntMulTM.SpecFacts

/-!
# Layer driver pre-phase: zero-row padding (`Machine/Layer/DrvPad.lean`)

**Scope (honest summary).** Proof of `DrvPadStmt` (`Machine/Layer/DrvPreDefs.lean`; driver pre-phase
zero-row padding, Section A.6 (`sec:transfer-layer`)): `SubNLogN.Machine.Layer.drvPad_holds`, no hypotheses. Helpers live in
`SubNLogN.Machine.Layer.DrvPadDescAux`.

**The program** `padProg` (one `Option Sym` register, private scratch `Fin 8`): floors (`mark`) on
the scratch stacks `Y, Tmp, Cnt, Pad, Cr, Cw`; then, while the next array symbol is a record symbol
(`isRecSym`), one block: copy `N0` to `Cnt` and move `N0` records to `Y` (`countdown` of
`passRBody`, each record's symbol order preserved, record order reversed on `Y`); copy `Npad` to
`Pad` and push `Npad` zero records on `Y` (`zeroRec`: `sep`, then `2rw` zero bits by nested
countdowns over copies of `r` and `w`); peek the array. Finally `passR` moves `Y` back onto the
array (re-reversing the record order) and the floors are removed. With `1 ≤ N0` every block is
nonempty, so the loop test sees exactly the blocks; `BlkTerm rest` stops it.

**Cost** (`runs_padProg`): at most `100·(V_out + (#blocks + 1)·(bitLen N0 + bitLen Npad +
bitLen r + bitLen w + 1))`: each moved record costs `≤ 24·(its symbols)`, each zero record
`≤ 76·(2rw + 1)` (it pays its own counter work because `w ≥ 1`), each block a counter overhead
`≤ 7·(bitLen N0 + bitLen Npad) + 19`, the final `passR` `8·V_out + 2`. The block sums are handled by
potentials (`sum_telescope`, `loopCost_telescope`).
-/

namespace SubNLogN.Machine.Layer.DrvPadDescAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability

/-! ## Layout and programs -/

/-- Private scratch of the padding kernel. -/
abbrev PE : Type := Fin 8

/-- Stacks of the padding kernel. -/
abbrev PK : Type := KLoc (Fin 5) PE

abbrev sA : PK := .inl 0
abbrev sN0 : PK := .inl 1
abbrev sNp : PK := .inl 2
abbrev sR : PK := .inl 3
abbrev sW : PK := .inl 4
abbrev sY : PK := .inr 0
abbrev sTmp : PK := .inr 1
abbrev sCnt : PK := .inr 2
abbrev sPad : PK := .inr 3
abbrev sT : PK := .inr 4
abbrev sCr : PK := .inr 5
abbrev sCw : PK := .inr 6
abbrev sT2 : PK := .inr 7

/-- The identity register lens. -/
def lid : Lens (Option Sym) (Option Sym) where
  get v := v
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- `2w` zero bits onto `Y` (counter `w` on `Cw`). -/
def zeroBitsW : SProg PK :=
  countdown lid sCw sT (.seq (pushC sY (.bit false)) (pushC sY (.bit false)))

/-- One zero record of `r` coefficients at width `w` onto `Y` (record end first). -/
def zeroRec : SProg PK :=
  .seq (pushC sY .sep) (.seq (copyBlock sR sCr sT2)
    (countdown lid sCr sT (.seq (copyBlock sW sCw sT2) zeroBitsW)))

/-- Continue while the next symbol of the array is a record symbol (a bit or `sep`). -/
def isRecSym : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

/-- One block: move `N0` records to `Y`, then push `Npad` zero records, then peek the array. -/
def blockBody : SProg PK :=
  .seq (copyBlock sN0 sCnt sT2) (.seq (countdown lid sCnt sT (passRBody .mark sA sTmp sY))
    (.seq (copyBlock sNp sPad sT2) (.seq (countdown lid sPad sT zeroRec) (peekR sA))))

/-- Floors (`mark`) on the private stacks with arbitrary content. -/
def floors : SProg PK :=
  .seq (pushC sY .mark) (.seq (pushC sTmp .mark) (.seq (pushC sCnt .mark)
    (.seq (pushC sPad .mark) (.seq (pushC sCr .mark) (pushC sCw .mark)))))

/-- Remove the floors. -/
def unfloors : SProg PK :=
  .seq (popR sY) (.seq (popR sTmp) (.seq (popR sCnt)
    (.seq (popR sPad) (.seq (popR sCr) (popR sCw)))))

/-- **The padding kernel.** -/
def padProg : SProg PK :=
  .seq floors (.seq (.seq (peekR sA) (.loop isRecSym blockBody))
    (.seq (passR .mark .mark sY sTmp sA) unfloors))

theorem closed_copyBlock' (a b c : PK) : (copyBlock a b c).Closed := by
  simp [copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody, restoreR, pushC, popR,
    pushR, Prog.Closed, Prog.FreeBelow, Lib.skip]

theorem closed_pushC' (k : PK) (x : Sym) : (pushC k x).Closed := by
  simp [pushC, Prog.Closed, Prog.FreeBelow]

theorem closed_popR' (k : PK) : (popR k).Closed := by
  simp [popR, Prog.Closed, Prog.FreeBelow]

theorem closed_peekR' (k : PK) : (peekR k).Closed := by
  simp [peekR, Prog.Closed, Prog.FreeBelow]

theorem closed_zeroBitsW : zeroBitsW.Closed :=
  closed_countdown lid sCw sT ⟨closed_pushC' _ _, closed_pushC' _ _⟩

theorem closed_zeroRec : zeroRec.Closed :=
  ⟨closed_pushC' _ _, closed_copyBlock' _ _ _,
    closed_countdown lid sCr sT ⟨closed_copyBlock' _ _ _, closed_zeroBitsW⟩⟩

theorem closed_blockBody : blockBody.Closed :=
  ⟨closed_copyBlock' _ _ _, closed_countdown lid sCnt sT (closed_passRBody _ _ _ _),
    closed_copyBlock' _ _ _, closed_countdown lid sPad sT closed_zeroRec, closed_peekR' _⟩

theorem closed_floors : floors.Closed :=
  ⟨closed_pushC' _ _, closed_pushC' _ _, closed_pushC' _ _, closed_pushC' _ _, closed_pushC' _ _,
    closed_pushC' _ _⟩

theorem closed_unfloors : unfloors.Closed :=
  ⟨closed_popR' _, closed_popR' _, closed_popR' _, closed_popR' _, closed_popR' _, closed_popR' _⟩

theorem closed_padProg : padProg.Closed :=
  ⟨closed_floors, ⟨closed_peekR' _, closed_blockBody⟩, closed_passR _ _ _ _ _, closed_unfloors⟩

/-! ## Elementary steps in `RunsIn` form -/

theorem runsIn_pushC (k : PK) (x : Sym) (S : PK → List Sym) (ρ : List (SProg PK)) :
    RunsIn ρ (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  RunsIn.of_runs (runs_pushC k x S) (closed_pushC' k x) ρ

theorem runsIn_popR (k : PK) (S : PK → List Sym) (d : Sym) (tl : List Sym) (hS : S k = d :: tl)
    (ρ : List (SProg PK)) :
    RunsIn ρ (popR k) S (Function.update S k tl) (fun _ => True) 1 :=
  RunsIn.of_runs (runs_popR k S d tl hS) (closed_popR' k) ρ

theorem runsIn_peekR (k : PK) (S : PK → List Sym) (ρ : List (SProg PK)) :
    RunsIn ρ (peekR k) S S (fun v => v = (S k).head?) 1 :=
  RunsIn.of_runs (FramePassRAux.runs_peekR_eq k S _ rfl) (closed_peekR' k) ρ

theorem runsIn_copyBlock {src dst tmp : PK} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (n : ℕ) (rest : List Sym) (hrest : TermOK rest) (S : PK → List Sym)
    (hS : S src = natSyms n ++ rest) (ρ : List (SProg PK)) :
    RunsIn ρ (copyBlock src dst tmp) S (Function.update S dst (natSyms n ++ S dst))
      (fun _ => True) (7 * bitLen n + 7) :=
  RunsIn.of_runs (Runs.of_eval fun v =>
    ⟨_, _, copyBlock_eval hsd hst hdt [] v (encodeNat n) rest S hrest hS, trivial, le_rfl⟩)
    (closed_copyBlock' src dst tmp) ρ

/-! ## Arithmetic and record facts -/

theorem bitLen_le' (n : ℕ) : bitLen n ≤ n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.2 Nat.lt_two_pow_self

/-- Telescoping sum of increments of a stepwise monotone potential. -/
theorem sum_telescope (Φ : ℕ → ℕ) (hΦ : ∀ j, Φ j ≤ Φ (j + 1)) (c : ℕ) :
    ∀ N, ((List.range N).map fun j => Φ (j + 1) - Φ j + c).sum = Φ N - Φ 0 + c * N
  | 0 => by simp
  | N + 1 => by
    have ih := sum_telescope Φ hΦ c N
    have hmono : ∀ n, Φ 0 ≤ Φ n := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ihn => exact le_trans ihn (hΦ n)
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have h1 := hmono N
    have h2 := hΦ N
    rw [Nat.mul_succ]
    omega

theorem length_arrSyms (ps : List (List Bool)) :
    (arrSyms ps).length = (ps.map fun p => p.length + 1).sum := by
  induction ps with
  | nil => simp [FramePassRAux.arrSyms_nil]
  | cons p ps ih =>
    rw [FramePassRAux.arrSyms_cons, List.length_append, FramePassRAux.length_recSyms, ih]
    simp

/-- The zero record payload. -/
theorem crecBits_zero (w r : ℕ) :
    crecBits w (List.replicate r ((0 : ℤ), (0 : ℤ))) = List.replicate (2 * r * w) false := by
  induction r with
  | zero => simp [crecBits]
  | succ r ih =>
    rw [List.replicate_succ, crecBits, List.flatMap_cons, ← crecBits, ih]
    have hc : coefBits w ((0 : ℤ), (0 : ℤ)) = List.replicate (2 * w) false := by
      simp [coefBits, twosBits, bitsLE, two_mul]
    rw [hc, ← List.replicate_add]
    congr 1
    ring


/-! ## The zero record -/

/-- `2w` zero bits onto `Y`; the counter `w` on `Cw` is consumed. -/
theorem runs_zeroBitsW (w : ℕ) (cwT : List Sym) (S : PK → List Sym)
    (hS : S sCw = natSyms w ++ Sym.mark :: cwT) (ρ : List (SProg PK)) :
    RunsIn ρ zeroBitsW S
      (Function.update (Function.update S sY (List.replicate (2 * w) (Sym.bit false) ++ S sY))
        sCw (Sym.mark :: cwT)) (fun _ => True) (18 * w + 2) := by
  have key := runsIn_countdown (ρ := ρ) lid (c := sCw) (t := sT) (by decide)
    (body := .seq (pushC sY (.bit false)) (pushC sY (.bit false))) w (Sym.mark :: cwT)
    (TermOK.cons rfl _)
    (fun m => Function.update S sY (List.replicate (2 * (w - m)) (Sym.bit false) ++ S sY))
    (fun _ => 2) (fun m hm => by
      refine RunsIn.congr (RunsIn.seq (runsIn_pushC sY _ _ ρ) (runsIn_pushC sY _ _ ρ)) ?_ le_rfl
      have hrep : List.replicate (2 * (w - m)) (Sym.bit false) =
          Sym.bit false :: Sym.bit false :: List.replicate (2 * (w - (m + 1))) (Sym.bit false) := by
        rw [show 2 * (w - m) = 2 * (w - (m + 1)) + 1 + 1 by omega]
        rfl
      funext k
      simp only [Function.update_apply, hrep]
      split_ifs <;> simp_all)
  have hinit : Function.update
      (Function.update S sY (List.replicate (2 * (w - w)) (Sym.bit false) ++ S sY)) sCw
      (natSyms w ++ Sym.mark :: cwT) = S := by
    funext k
    simp only [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.nil_append,
      Function.update_apply]
    split_ifs <;> simp_all
  rw [hinit] at key
  refine RunsIn.mono (RunsIn.congr key ?_ ?_) (fun _ _ => trivial) le_rfl
  · simp only [Nat.sub_zero]
  · have h := countdownCost_le (fun _ => 2) w
    simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at h
    omega

/-- **One zero record** of `r` coefficients at width `w` is pushed on `Y` (counters restored). -/
theorem runs_zeroRec (r w : ℕ) (hw : 1 ≤ w) (r3 r4 crT cwT : List Sym) (S : PK → List Sym)
    (h3 : S sR = natSyms r ++ r3) (h4 : S sW = natSyms w ++ r4) (hr3 : TermOK r3)
    (hr4 : TermOK r4) (hcr : S sCr = Sym.mark :: crT) (hcw : S sCw = Sym.mark :: cwT)
    (ρ : List (SProg PK)) :
    RunsIn ρ zeroRec S
      (Function.update S sY (recSyms (List.replicate (2 * r * w) false) ++ S sY))
      (fun _ => True) (60 * (r * w + 1) + 7 * bitLen r) := by
  have e1 := runsIn_pushC sY .sep S ρ
  set S1 := Function.update S sY (Sym.sep :: S sY) with hS1
  have e2 := runsIn_copyBlock (src := sR) (dst := sCr) (tmp := sT2) (by decide) (by decide)
    (by decide) r r3 hr3 S1 (by rw [hS1, Function.update_of_ne (by decide), h3]) ρ
  have hS1cr : S1 sCr = Sym.mark :: crT := by rw [hS1, Function.update_of_ne (by decide), hcr]
  have hS1cw : S1 sCw = Sym.mark :: cwT := by rw [hS1, Function.update_of_ne (by decide), hcw]
  have key := runsIn_countdown (ρ := ρ) lid (c := sCr) (t := sT) (by decide)
    (body := .seq (copyBlock sW sCw sT2) zeroBitsW) r (Sym.mark :: crT) (TermOK.cons rfl _)
    (fun n => Function.update S1 sY (List.replicate (2 * w * (r - n)) (Sym.bit false) ++ S1 sY))
    (fun _ => 7 * bitLen w + 7 + (18 * w + 2)) (fun n hn => by
      set X := Function.update
        (Function.update S1 sY (List.replicate (2 * w * (r - (n + 1))) (Sym.bit false) ++ S1 sY))
        sCr (natSyms (n + 1) ++ Sym.mark :: crT) with hX
      have hXw : X sW = natSyms w ++ r4 := by
        rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS1,
          Function.update_of_ne (by decide), h4]
      have hXcw : X sCw = Sym.mark :: cwT := by
        rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS1cw]
      have c1 := runsIn_copyBlock (src := sW) (dst := sCw) (tmp := sT2) (by decide) (by decide)
        (by decide) w r4 hr4 X hXw ρ
      have c2 := runs_zeroBitsW w cwT (Function.update X sCw (natSyms w ++ X sCw))
        (by rw [Function.update_self, hXcw]) ρ
      refine RunsIn.congr (RunsIn.seq c1 c2) ?_ le_rfl
      have hrep : List.replicate (2 * w * (r - n)) (Sym.bit false) =
          List.replicate (2 * w) (Sym.bit false) ++
            List.replicate (2 * w * (r - (n + 1))) (Sym.bit false) := by
        rw [← List.replicate_add]
        congr 1
        rw [show r - n = r - (n + 1) + 1 by omega]
        ring
      funext k
      by_cases k1 : k = sY
      · subst k1
        simp +decide only [hX, Function.update_apply, ↓reduceIte]
        rw [hrep, List.append_assoc]
      by_cases k2 : k = sCr
      · subst k2
        simp +decide only [hX, Function.update_apply, ↓reduceIte]
      by_cases k3 : k = sCw
      · subst k3
        simp +decide only [hX, Function.update_apply, ↓reduceIte, hS1cw]
      simp only [hX, Function.update_apply, k1, k2, k3, ↓reduceIte])
  have hinit : Function.update
      (Function.update S1 sY (List.replicate (2 * w * (r - r)) (Sym.bit false) ++ S1 sY)) sCr
      (natSyms r ++ Sym.mark :: crT) = Function.update S1 sCr (natSyms r ++ S1 sCr) := by
    funext k
    simp only [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.nil_append,
      Function.update_apply, hS1cr]
    split_ifs <;> simp_all
  rw [hinit] at key
  refine RunsIn.mono (RunsIn.congr (RunsIn.seq e1 (RunsIn.seq e2 key)) ?_ ?_)
    (fun _ _ => trivial) le_rfl
  · have hrec : recSyms (List.replicate (2 * r * w) false) ++ S sY =
        List.replicate (2 * w * r) (Sym.bit false) ++ Sym.sep :: S sY := by
      simp only [recSyms, List.map_replicate, List.append_assoc, List.singleton_append]
      congr 2
      ring
    funext k
    simp only [hS1, Nat.sub_zero, Function.update_apply, hrec]
    split_ifs <;> simp_all
  · have h := countdownCost_le (fun _ => 7 * bitLen w + 7 + (18 * w + 2)) r
    simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at h
    have hb := bitLen_le' w
    have h5 : r * (7 * bitLen w + 7 + (18 * w + 2)) ≤ r * (50 * w) - 16 * r := by
      have : 7 * bitLen w + 7 + (18 * w + 2) + 16 ≤ 50 * w := by omega
      have h6 := Nat.mul_le_mul_left r this
      rw [Nat.mul_add] at h6
      omega
    nlinarith


/-! ## Moving the records of one block -/

theorem length_le_length_arrSyms (ps : List (List Bool)) : ps.length ≤ (arrSyms ps).length := by
  rw [length_arrSyms]
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

theorem length_arrSyms_drop_mono (ps : List (List Bool)) {a b : ℕ} (h : a ≤ b) :
    (arrSyms (ps.drop b)).length ≤ (arrSyms (ps.drop a)).length := by
  have e : ps.drop a = (ps.drop a).take (b - a) ++ ps.drop b := by
    conv_lhs => rw [← List.take_append_drop (b - a) (ps.drop a)]
    rw [List.drop_drop]
    congr 2
    omega
  rw [e, FramePassRAux.arrSyms_append, List.length_append]
  omega

/-- **The records of a block** move from the array to `Y` (record order reversed on `Y`, each
record's symbol order preserved); the counter `|ps|` on `Cnt` is consumed. -/
theorem runs_moveRecs (ps : List (List Bool)) (tail ct tt : List Sym) (hct : TermOK ct)
    (S : PK → List Sym) (hA : S sA = arrSyms ps ++ tail) (hC : S sCnt = natSyms ps.length ++ ct)
    (hTmp : S sTmp = Sym.mark :: tt) (ρ : List (SProg PK)) :
    RunsIn ρ (countdown lid sCnt sT (passRBody .mark sA sTmp sY)) S
      (Function.update (Function.update (Function.update S sA tail) sY
        (arrSyms ps.reverse ++ S sY)) sCnt ct)
      (fun _ => True) (24 * (arrSyms ps).length + 2) := by
  set L := ps.length with hL
  set Φ : ℕ → ℕ := fun j => 8 * (arrSyms (ps.drop (L - j))).length with hΦ
  have key := runsIn_countdown (ρ := ρ) lid (c := sCnt) (t := sT) (by decide)
    (body := passRBody .mark sA sTmp sY) L ct hct
    (fun j => Function.update (Function.update S sA (arrSyms (ps.drop (L - j)) ++ tail)) sY
      (arrSyms (ps.take (L - j)).reverse ++ S sY))
    (fun j => Φ (j + 1) - Φ j) (fun j hj => by
      have hlt : L - (j + 1) < ps.length := by omega
      have hdrop : ps.drop (L - (j + 1)) = ps[L - (j + 1)] :: ps.drop (L - j) := by
        rw [List.drop_eq_getElem_cons hlt]
        congr 2
        omega
      have htake : ps.take (L - j) = ps.take (L - (j + 1)) ++ [ps[L - (j + 1)]] := by
        rw [show L - j = L - (j + 1) + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hlt]
        rfl
      set X := Function.update (Function.update (Function.update S sA
        (arrSyms (ps.drop (L - (j + 1))) ++ tail)) sY
        (arrSyms (ps.take (L - (j + 1))).reverse ++ S sY)) sCnt (natSyms (j + 1) ++ ct) with hX
      have hXA : X sA = recSyms ps[L - (j + 1)] ++ (arrSyms (ps.drop (L - j)) ++ tail) := by
        rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self, hdrop, FramePassRAux.arrSyms_cons, List.append_assoc]
      have hXT : X sTmp = Sym.mark :: tt := by
        rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hTmp]
      have hb := runs_passRBody (gt := Sym.mark) (src := sA) (tmp := sTmp) (dst := sY)
        (by decide) (by decide) (by decide) rfl ps[L - (j + 1)] (arrSyms (ps.drop (L - j)) ++ tail)
        tt X hXA hXT
      refine RunsIn.mono (RunsIn.congr (RunsIn.of_runs hb (closed_passRBody _ _ _ _) ρ) ?_ ?_)
        (fun _ _ => trivial) le_rfl
      · funext k
        simp only [hX, Function.update_apply, htake, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.singleton_append, FramePassRAux.arrSyms_cons,
          List.append_assoc]
        clear hb hXA hXT hX
        split_ifs <;> simp_all
      · simp only [hΦ]
        rw [hdrop, FramePassRAux.arrSyms_cons, List.length_append, FramePassRAux.length_recSyms]
        omega)
  have hinit : Function.update (Function.update (Function.update S sA
      (arrSyms (ps.drop (L - L)) ++ tail)) sY (arrSyms (ps.take (L - L)).reverse ++ S sY)) sCnt
      (natSyms L ++ ct) = S := by
    funext k
    simp only [Nat.sub_self, List.drop_zero, List.take_zero, List.reverse_nil,
      FramePassRAux.arrSyms_nil, List.nil_append, Function.update_apply]
    split_ifs <;> simp_all
  rw [hinit] at key
  refine RunsIn.mono (RunsIn.congr key ?_ ?_) (fun _ _ => trivial) le_rfl
  · simp only [Nat.sub_zero, List.drop_length, FramePassRAux.arrSyms_nil, List.nil_append,
      List.take_length, hL]
  · have h := countdownCost_le (fun j => Φ (j + 1) - Φ j) L
    have hsum := sum_telescope Φ (fun j => by
      simp only [hΦ]
      have := length_arrSyms_drop_mono ps (show L - (j + 1) ≤ L - j by omega)
      omega) 0 L
    simp only [Nat.add_zero, Nat.zero_mul] at hsum
    have hsum' : ((List.range L).map fun j => Φ (j + 1) - Φ j).sum = Φ L - Φ 0 := by
      rw [← hsum]
    have hΦL : Φ L = 8 * (arrSyms ps).length := by simp [hΦ]
    have hΦ0 : Φ 0 = 0 := by simp [hΦ, hL, FramePassRAux.arrSyms_nil]
    have hlen := length_le_length_arrSyms ps
    rw [hsum', hΦL, hΦ0] at h
    omega


/-! ## Zero records of one block -/

/-- The zero record payload of `r` coefficients at width `w`. -/
abbrev zrec (r w : ℕ) : List Bool := List.replicate (2 * r * w) false

/-- **`Npad` zero records** are pushed on `Y`; the counter `Npad` on `Pad` is consumed. -/
theorem runs_pads (r w Npad : ℕ) (hw : 1 ≤ w) (r3 r4 crT cwT ct : List Sym) (hct : TermOK ct)
    (S : PK → List Sym) (h3 : S sR = natSyms r ++ r3) (h4 : S sW = natSyms w ++ r4)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (hcr : S sCr = Sym.mark :: crT)
    (hcw : S sCw = Sym.mark :: cwT) (hP : S sPad = natSyms Npad ++ ct) (ρ : List (SProg PK)) :
    RunsIn ρ (countdown lid sPad sT zeroRec) S
      (Function.update (Function.update S sY
        (arrSyms (List.replicate Npad (zrec r w)) ++ S sY)) sPad ct)
      (fun _ => True) (Npad * (60 * (r * w + 1) + 7 * bitLen r + 16) + 2) := by
  have key := runsIn_countdown (ρ := ρ) lid (c := sPad) (t := sT) (by decide) (body := zeroRec)
    Npad ct hct
    (fun m => Function.update S sY (arrSyms (List.replicate (Npad - m) (zrec r w)) ++ S sY))
    (fun _ => 60 * (r * w + 1) + 7 * bitLen r) (fun m hm => by
      set X := Function.update (Function.update S sY
        (arrSyms (List.replicate (Npad - (m + 1)) (zrec r w)) ++ S sY)) sPad
        (natSyms (m + 1) ++ ct) with hX
      have hz := runs_zeroRec r w hw r3 r4 crT cwT X
        (by rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h3])
        (by rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h4])
        hr3 hr4
        (by rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hcr])
        (by rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hcw]) ρ
      refine RunsIn.congr hz ?_ le_rfl
      have hrep : arrSyms (List.replicate (Npad - m) (zrec r w)) =
          recSyms (zrec r w) ++ arrSyms (List.replicate (Npad - (m + 1)) (zrec r w)) := by
        rw [show Npad - m = Npad - (m + 1) + 1 by omega, List.replicate_succ,
          FramePassRAux.arrSyms_cons]
      funext k
      simp only [hX, Function.update_apply, hrep, List.append_assoc]
      clear hz hX
      split_ifs <;> simp_all)
  have hinit : Function.update (Function.update S sY
      (arrSyms (List.replicate (Npad - Npad) (zrec r w)) ++ S sY)) sPad (natSyms Npad ++ ct) = S := by
    funext k
    simp only [Nat.sub_self, List.replicate_zero, FramePassRAux.arrSyms_nil, List.nil_append,
      Function.update_apply]
    split_ifs <;> simp_all
  rw [hinit] at key
  refine RunsIn.mono (RunsIn.congr key ?_ ?_) (fun _ _ => trivial) le_rfl
  · simp only [Nat.sub_zero]
  · have h := countdownCost_le (fun _ => 60 * (r * w + 1) + 7 * bitLen r) Npad
    simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at h
    have e : Npad * (60 * (r * w + 1) + 7 * bitLen r + 16) =
        Npad * (60 * (r * w + 1) + 7 * bitLen r) + 16 * Npad := by ring
    omega

/-! ## One block -/

/-- **One block**: its `N0` records move to `Y`, then `Npad` zero records are pushed on `Y`;
counters restored, register = next symbol of the array. -/
theorem runs_blockBody (N0 Npad r w : ℕ) (hw : 1 ≤ w) (ps : List (List Bool))
    (hps : ps.length = N0) (later r1 r2 r3 r4 tt crT cwT cntT padT : List Sym)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (S : PK → List Sym) (hA : S sA = arrSyms ps ++ later)
    (h1 : S sN0 = natSyms N0 ++ r1) (h2 : S sNp = natSyms Npad ++ r2)
    (h3 : S sR = natSyms r ++ r3) (h4 : S sW = natSyms w ++ r4)
    (hTmp : S sTmp = Sym.mark :: tt) (hcr : S sCr = Sym.mark :: crT)
    (hcw : S sCw = Sym.mark :: cwT) (hcnt : S sCnt = Sym.mark :: cntT)
    (hpad : S sPad = Sym.mark :: padT) (ρ : List (SProg PK)) :
    RunsIn ρ blockBody S
      (Function.update (Function.update S sA later) sY
        (arrSyms (List.replicate Npad (zrec r w) ++ ps.reverse) ++ S sY))
      (fun v => v = later.head?)
      (7 * bitLen N0 + 7 + (24 * (arrSyms ps).length + 2) + (7 * bitLen Npad + 7 +
        ((Npad * (60 * (r * w + 1) + 7 * bitLen r + 16) + 2) + 1))) := by
  have c1 := runsIn_copyBlock (src := sN0) (dst := sCnt) (tmp := sT2) (by decide) (by decide)
    (by decide) N0 r1 hr1 S h1 ρ
  have c2 := runs_moveRecs ps later (Sym.mark :: cntT) tt (TermOK.cons rfl _)
    (Function.update S sCnt (natSyms N0 ++ S sCnt))
    (by rw [Function.update_of_ne (by decide), hA]) (by rw [Function.update_self, hcnt, hps])
    (by rw [Function.update_of_ne (by decide), hTmp]) ρ
  set S2 := Function.update (Function.update (Function.update
    (Function.update S sCnt (natSyms N0 ++ S sCnt)) sA later) sY
    (arrSyms ps.reverse ++ Function.update S sCnt (natSyms N0 ++ S sCnt) sY)) sCnt
    (Sym.mark :: cntT) with hS2
  have c3 := runsIn_copyBlock (src := sNp) (dst := sPad) (tmp := sT2) (by decide) (by decide)
    (by decide) Npad r2 hr2 S2 (by
      rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), h2]) ρ
  have hS2pad : S2 sPad = Sym.mark :: padT := by
    rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), hpad]
  have c4 := runs_pads r w Npad hw r3 r4 crT cwT (Sym.mark :: padT) (TermOK.cons rfl _)
    (Function.update S2 sPad (natSyms Npad ++ S2 sPad))
    (by rw [Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h3])
    (by rw [Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h4])
    hr3 hr4
    (by rw [Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hcr])
    (by rw [Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hcw])
    (by rw [Function.update_self, hS2pad]) ρ
  have c5 := runsIn_peekR sA (Function.update (Function.update
    (Function.update S2 sPad (natSyms Npad ++ S2 sPad)) sY
    (arrSyms (List.replicate Npad (zrec r w)) ++
      Function.update S2 sPad (natSyms Npad ++ S2 sPad) sY)) sPad (Sym.mark :: padT)) ρ
  have hfinA : (Function.update (Function.update (Function.update S2 sPad
      (natSyms Npad ++ S2 sPad)) sY (arrSyms (List.replicate Npad (zrec r w)) ++
        Function.update S2 sPad (natSyms Npad ++ S2 sPad) sY)) sPad (Sym.mark :: padT)) sA =
      later := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  refine RunsIn.mono (RunsIn.congr (RunsIn.seq c1 (RunsIn.seq c2 (RunsIn.seq c3
    (RunsIn.seq c4 c5)))) ?_ (by omega)) ?_ le_rfl
  · funext k
    by_cases k1 : k = sA
    · subst k1
      simp +decide only [hS2, Function.update_apply, ↓reduceIte]
    by_cases k2 : k = sY
    · subst k2
      simp +decide only [hS2, Function.update_apply, ↓reduceIte]
      rw [FramePassRAux.arrSyms_append, List.append_assoc]
    by_cases k3 : k = sCnt
    · subst k3
      simp +decide only [hS2, Function.update_apply, ↓reduceIte, hcnt]
    by_cases k4 : k = sPad
    · subst k4
      simp +decide only [hS2, Function.update_apply, ↓reduceIte, hpad]
    simp only [hS2, Function.update_apply, k1, k2, k3, k4, ↓reduceIte]
  · intro v hv
    rw [hv, hfinA]


/-! ## The block loop -/

/-- Output records of the padded blocks. -/
def outRecs (Npad r w : ℕ) (bs : List (List (List CInt))) : List (List Bool) :=
  ((bs.map (padBlock Npad r)).flatten).map (crecBits w)

theorem outRecs_append_single (Npad r w : ℕ) (bs : List (List (List CInt)))
    (b : List (List CInt)) :
    outRecs Npad r w (bs ++ [b]) =
      outRecs Npad r w bs ++ (b.map (crecBits w) ++ List.replicate Npad (zrec r w)) := by
  simp [outRecs, padBlock, crecBits_zero]

theorem outRecs_cons (Npad r w : ℕ) (b : List (List CInt)) (bs : List (List (List CInt))) :
    outRecs Npad r w (b :: bs) =
      (b.map (crecBits w) ++ List.replicate Npad (zrec r w)) ++ outRecs Npad r w bs := by
  simp [outRecs, padBlock, crecBits_zero]

theorem carrSyms_nil (w : ℕ) : carrSyms w [] = [] := by
  simp [carrSyms, FramePassRAux.arrSyms_nil]

theorem carrSyms_append (w : ℕ) (u v : List (List CInt)) :
    carrSyms w (u ++ v) = carrSyms w u ++ carrSyms w v := by
  simp [carrSyms, FramePassRAux.arrSyms_append]

/-- The loop test after a block: more blocks remain iff the next symbol is a record symbol. -/
theorem isRecSym_head (N0 w : ℕ) (hN0 : 1 ≤ N0) (bs : List (List (List CInt)))
    (hbs : ∀ b ∈ bs, b.length = N0) (rest : List Sym) (hrest : BlkTerm rest) :
    isRecSym (carrSyms w bs.flatten ++ rest).head? = decide (0 < bs.length) := by
  cases bs with
  | nil =>
    simp only [List.flatten_nil, carrSyms_nil, List.nil_append, List.length_nil, lt_irrefl,
      decide_false]
    cases h : rest.head? with
    | none => rfl
    | some d =>
      obtain ⟨hd1, hd2⟩ := hrest d h
      cases d <;> simp_all [isRecSym, isDataSym]
  | cons b bs =>
    have hb := hbs b List.mem_cons_self
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, b = c :: cs := by
      cases b with
      | nil => simp at hb; omega
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hcar : carrSyms w ((c :: cs) :: bs).flatten =
        recSyms (crecBits w c) ++ carrSyms w (cs ++ bs.flatten) := by
      simp [carrSyms, FramePassRAux.arrSyms_cons]
    rw [hcar, List.append_assoc]
    simp only [List.length_cons, Nat.zero_lt_succ, decide_true]
    cases crecBits w c with
    | nil => simp [recSyms, isRecSym]
    | cons x xs => simp [recSyms, isRecSym]

/-- The state of the block loop with `n` blocks left. -/
def loopSt (Npad r w : ℕ) (blks : List (List (List CInt))) (rest : List Sym)
    (S0 : PK → List Sym) (n : ℕ) : PK → List Sym :=
  Function.update (Function.update S0 sA
    (carrSyms w (blks.drop (blks.length - n)).flatten ++ rest)) sY
    (arrSyms (outRecs Npad r w (blks.take (blks.length - n))).reverse ++ S0 sY)

/-- The potential of the block loop: `76·` the output volume of the blocks left. -/
def loopPot (Npad r w : ℕ) (blks : List (List (List CInt))) (n : ℕ) : ℕ :=
  76 * (arrSyms (outRecs Npad r w (blks.drop (blks.length - n)))).length

theorem outRecs_append (Npad r w : ℕ) (u v : List (List (List CInt))) :
    outRecs Npad r w (u ++ v) = outRecs Npad r w u ++ outRecs Npad r w v := by
  simp [outRecs]

theorem loopPot_step (Npad r w : ℕ) (blks : List (List (List CInt))) (n : ℕ) :
    loopPot Npad r w blks n ≤ loopPot Npad r w blks (n + 1) := by
  unfold loopPot
  have e : blks.drop (blks.length - (n + 1)) =
      (blks.drop (blks.length - (n + 1))).take (blks.length - n - (blks.length - (n + 1))) ++
        blks.drop (blks.length - n) := by
    conv_lhs => rw [← List.take_append_drop (blks.length - n - (blks.length - (n + 1)))
      (blks.drop (blks.length - (n + 1)))]
    rw [List.drop_drop]
    congr 2
    omega
  rw [e, outRecs_append, FramePassRAux.arrSyms_append, List.length_append]
  omega

theorem loopCost_telescope (Φ : ℕ → ℕ) (hΦ : ∀ j, Φ j ≤ Φ (j + 1)) (c : ℕ) :
    ∀ N, loopCost (fun j => Φ (j + 1) - Φ j + c) N = Φ N - Φ 0 + (c + 1) * N + 1
  | 0 => by simp [loopCost]
  | N + 1 => by
    have ih := loopCost_telescope Φ hΦ c N
    have hmono : ∀ n, Φ 0 ≤ Φ n := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ihn => exact le_trans ihn (hΦ n)
    rw [loopCost, ih]
    have h1 := hmono N
    have h2 := hΦ N
    rw [Nat.mul_succ]
    omega


/-- **One iteration of the block loop** (`n + 1 → n` blocks left). -/
theorem runs_loopBody (N0 Npad r w : ℕ) (hN0 : 1 ≤ N0) (hw : 1 ≤ w)
    (blks : List (List (List CInt))) (hblk : ∀ b ∈ blks, b.length = N0) (rest : List Sym)
    (hrest : BlkTerm rest) (r1 r2 r3 r4 : List Sym) (hr1 : TermOK r1) (hr2 : TermOK r2)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (S0 : PK → List Sym)
    (h1 : S0 sN0 = natSyms N0 ++ r1) (h2 : S0 sNp = natSyms Npad ++ r2)
    (h3 : S0 sR = natSyms r ++ r3) (h4 : S0 sW = natSyms w ++ r4)
    (tt crT cwT cntT padT : List Sym) (hTmp : S0 sTmp = Sym.mark :: tt)
    (hcr : S0 sCr = Sym.mark :: crT) (hcw : S0 sCw = Sym.mark :: cwT)
    (hcnt : S0 sCnt = Sym.mark :: cntT) (hpad : S0 sPad = Sym.mark :: padT)
    (ρ : List (SProg PK)) (n : ℕ) (hn : n < blks.length) :
    RunsIn ρ blockBody (loopSt Npad r w blks rest S0 (n + 1)) (loopSt Npad r w blks rest S0 n)
      (fun v => isRecSym v = decide (0 < n))
      (loopPot Npad r w blks (n + 1) - loopPot Npad r w blks n +
        (7 * bitLen N0 + 7 * bitLen Npad + 19)) := by
  have hlt : blks.length - (n + 1) < blks.length := by omega
  have hdrop : blks.drop (blks.length - (n + 1)) =
      blks[blks.length - (n + 1)] :: blks.drop (blks.length - n) := by
    rw [List.drop_eq_getElem_cons hlt]
    congr 2
    omega
  have htake : blks.take (blks.length - n) =
      blks.take (blks.length - (n + 1)) ++ [blks[blks.length - (n + 1)]] := by
    rw [show blks.length - n = blks.length - (n + 1) + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hlt]
    rfl
  have hblen : (blks[blks.length - (n + 1)]).length = N0 := hblk _ (List.getElem_mem hlt)
  set b := blks[blks.length - (n + 1)] with hb
  set later := carrSyms w (blks.drop (blks.length - n)).flatten ++ rest with hlater
  have hloop : ∀ k : PK, k ≠ sA → k ≠ sY → loopSt Npad r w blks rest S0 (n + 1) k = S0 k := by
    intro k k1 k2
    simp only [loopSt, Function.update_apply, k1, k2, ↓reduceIte]
  have hStA : loopSt Npad r w blks rest S0 (n + 1) sA = arrSyms (b.map (crecBits w)) ++ later := by
    simp +decide only [loopSt, Function.update_apply, ↓reduceIte]
    rw [hdrop, List.flatten_cons, carrSyms_append, List.append_assoc]
    rfl
  have key := runs_blockBody N0 Npad r w hw (b.map (crecBits w)) (by rw [List.length_map, hblen])
    later r1 r2 r3 r4 tt crT cwT cntT padT hr1 hr2 hr3 hr4 (loopSt Npad r w blks rest S0 (n + 1))
    hStA (by rw [hloop _ (by decide) (by decide), h1]) (by rw [hloop _ (by decide) (by decide), h2])
    (by rw [hloop _ (by decide) (by decide), h3]) (by rw [hloop _ (by decide) (by decide), h4])
    (by rw [hloop _ (by decide) (by decide), hTmp]) (by rw [hloop _ (by decide) (by decide), hcr])
    (by rw [hloop _ (by decide) (by decide), hcw]) (by rw [hloop _ (by decide) (by decide), hcnt])
    (by rw [hloop _ (by decide) (by decide), hpad]) ρ
  have hY : arrSyms (List.replicate Npad (zrec r w) ++ (b.map (crecBits w)).reverse) ++
      loopSt Npad r w blks rest S0 (n + 1) sY =
      arrSyms (outRecs Npad r w (blks.take (blks.length - n))).reverse ++ S0 sY := by
    simp +decide only [loopSt, Function.update_apply, ↓reduceIte]
    rw [htake, outRecs_append_single]
    simp only [List.reverse_append, List.reverse_replicate, FramePassRAux.arrSyms_append,
      List.append_assoc]
  refine RunsIn.mono (RunsIn.congr key ?_ ?_) ?_ le_rfl
  · funext k
    by_cases k1 : k = sA
    · subst k1
      simp +decide only [loopSt, Function.update_apply, ↓reduceIte]
      exact hlater
    by_cases k2 : k = sY
    · subst k2
      rw [Function.update_self, hY]
      simp +decide only [loopSt, Function.update_apply, ↓reduceIte]
    rw [Function.update_of_ne k2, Function.update_of_ne k1, hloop k k1 k2]
    simp only [loopSt, Function.update_apply, k1, k2, ↓reduceIte]
  · -- cost
    have hΨ : loopPot Npad r w blks (n + 1) = loopPot Npad r w blks n +
        76 * ((arrSyms (b.map (crecBits w))).length + Npad * (2 * r * w + 1)) := by
      simp only [loopPot]
      rw [show blks.length - (n + 1) = blks.length - (n + 1) from rfl, hdrop, outRecs_cons,
        FramePassRAux.arrSyms_append, FramePassRAux.arrSyms_append, List.length_append,
        List.length_append]
      have hz : (arrSyms (List.replicate Npad (zrec r w))).length = Npad * (2 * r * w + 1) := by
        rw [length_arrSyms]
        simp [List.map_replicate, List.sum_replicate]
      rw [hz]
      ring
    have hbr : bitLen r ≤ r * w := le_trans (bitLen_le' r) (Nat.le_mul_of_pos_right r hw)
    have hm := Nat.mul_le_mul_left Npad hbr
    rw [hΨ, Nat.add_sub_cancel_left]
    nlinarith
  · intro v hv
    rw [hv, hlater, isRecSym_head N0 w hN0 _ (fun b' hb' => hblk b' (List.mem_of_mem_drop hb'))
      rest hrest, List.length_drop]
    congr 1
    apply propext
    omega

/-- The state after the floors. -/
def floorSt (S : PK → List Sym) : PK → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S sY (Sym.mark :: S sY)) sTmp (Sym.mark :: S sTmp)) sCnt
    (Sym.mark :: S sCnt)) sPad (Sym.mark :: S sPad)) sCr (Sym.mark :: S sCr)) sCw
    (Sym.mark :: S sCw)

theorem floorSt_named (S : PK → List Sym) (i : Fin 5) : floorSt S (.inl i) = S (.inl i) := by
  simp [floorSt]

theorem runs_floors (S : PK → List Sym) (ρ : List (SProg PK)) :
    RunsIn ρ floors S (floorSt S) (fun _ => True) 6 := by
  refine RunsIn.congr (RunsIn.seq (runsIn_pushC sY _ _ ρ) (RunsIn.seq (runsIn_pushC sTmp _ _ ρ)
    (RunsIn.seq (runsIn_pushC sCnt _ _ ρ) (RunsIn.seq (runsIn_pushC sPad _ _ ρ)
    (RunsIn.seq (runsIn_pushC sCr _ _ ρ) (runsIn_pushC sCw _ _ ρ)))))) ?_ le_rfl
  funext k
  simp only [floorSt, Function.update_apply]
  split_ifs <;> simp_all

/-- **The padding kernel**, exact stacks and cost. -/
theorem runs_padProg (N0 Npad r w : ℕ) (hN0 : 1 ≤ N0) (hw : 1 ≤ w)
    (blks : List (List (List CInt))) (hblk : ∀ b ∈ blks, b.length = N0)
    (rest r1 r2 r3 r4 : List Sym) (hrest : BlkTerm rest)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (S : PK → List Sym)
    (hS0 : S sA = carrSyms w blks.flatten ++ rest) (hS1 : S sN0 = natSyms N0 ++ r1)
    (hS2 : S sNp = natSyms Npad ++ r2) (hS3 : S sR = natSyms r ++ r3)
    (hS4 : S sW = natSyms w ++ r4) :
    Runs padProg S (Function.update S sA (carrSyms w (blks.map (padBlock Npad r)).flatten ++ rest))
      (fun _ => True)
      (100 * (cvol w (blks.map (padBlock Npad r)).flatten +
        (blks.length + 1) * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1))) := by
  set S0 := floorSt S with hS0def
  have f1 := runs_floors S []
  have hS0n : ∀ i : Fin 5, S0 (.inl i) = S (.inl i) := floorSt_named S
  have hS0Y : S0 sY = Sym.mark :: S sY := by simp +decide [hS0def, floorSt]
  have hS0Tmp : S0 sTmp = Sym.mark :: S sTmp := by
    simp +decide [hS0def, floorSt]
  have hS0Cnt : S0 sCnt = Sym.mark :: S sCnt := by
    simp +decide [hS0def, floorSt]
  have hS0Pad : S0 sPad = Sym.mark :: S sPad := by
    simp +decide [hS0def, floorSt]
  have hS0Cr : S0 sCr = Sym.mark :: S sCr := by
    simp +decide [hS0def, floorSt]
  have hS0Cw : S0 sCw = Sym.mark :: S sCw := by
    simp +decide [hS0def, floorSt]
  have hstep := fun n (hn : n < blks.length) => runs_loopBody N0 Npad r w hN0 hw blks hblk rest
    hrest r1 r2 r3 r4 hr1 hr2 hr3 hr4 S0 (by rw [hS0n]; exact hS1) (by rw [hS0n]; exact hS2)
    (by rw [hS0n]; exact hS3) (by rw [hS0n]; exact hS4) (S sTmp) (S sCr) (S sCw) (S sCnt) (S sPad)
    hS0Tmp hS0Cr hS0Cw hS0Cnt hS0Pad [] n hn
  have hst0 : loopSt Npad r w blks rest S0 blks.length = S0 := by
    funext k
    simp only [loopSt, Nat.sub_self, List.drop_zero, List.take_zero, outRecs, List.map_nil,
      List.flatten_nil, List.reverse_nil, FramePassRAux.arrSyms_nil, List.nil_append,
      Function.update_apply]
    split_ifs with h1 h2
    · subst h1
      rfl
    · subst h2
      show carrSyms w blks.flatten ++ rest = S0 (.inl 0)
      rw [hS0n]
      exact hS0.symm
    · rfl
  have h0 : RunsIn [] (peekR sA) S0 (loopSt Npad r w blks rest S0 blks.length)
      (fun v => isRecSym v = decide (0 < blks.length)) 1 := by
    rw [hst0]
    refine RunsIn.mono (runsIn_peekR sA S0 []) (fun v hv => ?_) le_rfl
    rw [hv, hS0n, hS0]
    exact isRecSym_head N0 w hN0 blks hblk rest hrest
  have hloop := RunsIn.seq_loop h0 hstep
  -- the state after the loop
  set V := (arrSyms (outRecs Npad r w blks)).length with hV
  have hL0A : loopSt Npad r w blks rest S0 0 sA = rest := by
    simp +decide [loopSt, carrSyms_nil]
  have hL0Y : loopSt Npad r w blks rest S0 0 sY =
      arrSyms (outRecs Npad r w blks).reverse ++ Sym.mark :: S sY := by
    simp +decide [loopSt, hS0Y]
  have hL0Tmp : loopSt Npad r w blks rest S0 0 sTmp = Sym.mark :: S sTmp := by
    simp +decide [loopSt, hS0Tmp]
  have hpR := RunsIn.of_runs (runs_passR (g := Sym.mark) (gt := Sym.mark) (src := sY) (tmp := sTmp)
    (dst := sA) (by decide) (by decide) (by decide) rfl (by decide) rfl
    (outRecs Npad r w blks).reverse (S sY) (S sTmp) (loopSt Npad r w blks rest S0 0) hL0Y hL0Tmp)
    (closed_passR _ _ _ _ _) []
  set S5 := Function.update (Function.update (loopSt Npad r w blks rest S0 0) sY
    (Sym.mark :: S sY)) sA (arrSyms (outRecs Npad r w blks).reverse.reverse ++
      loopSt Npad r w blks rest S0 0 sA) with hS5
  have hS5v : ∀ k : PK, k ≠ sA → k ≠ sY → S5 k = S0 k := by
    intro k k1 k2
    simp only [hS5, loopSt, Function.update_apply, k1, k2, ↓reduceIte]
  have u1 := runsIn_popR sY S5 Sym.mark (S sY) (by simp +decide [hS5]) []
  have u2 := runsIn_popR sTmp (Function.update S5 sY (S sY)) Sym.mark (S sTmp)
    (by rw [Function.update_of_ne (by decide), hS5v _ (by decide) (by decide), hS0Tmp]) []
  have u3 := runsIn_popR sCnt (Function.update (Function.update S5 sY (S sY)) sTmp (S sTmp))
    Sym.mark (S sCnt) (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hS5v _ (by decide) (by decide), hS0Cnt]) []
  have u4 := runsIn_popR sPad (Function.update (Function.update (Function.update S5 sY (S sY))
    sTmp (S sTmp)) sCnt (S sCnt)) Sym.mark (S sPad) (by
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hS5v _ (by decide) (by decide), hS0Pad]) []
  have u5 := runsIn_popR sCr (Function.update (Function.update (Function.update
    (Function.update S5 sY (S sY)) sTmp (S sTmp)) sCnt (S sCnt)) sPad (S sPad)) Sym.mark (S sCr) (by
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hS5v _ (by decide) (by decide), hS0Cr]) []
  have u6 := runsIn_popR sCw (Function.update (Function.update (Function.update (Function.update
    (Function.update S5 sY (S sY)) sTmp (S sTmp)) sCnt (S sCnt)) sPad (S sPad)) sCr (S sCr))
    Sym.mark (S sCw) (by
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hS5v _ (by decide) (by decide), hS0Cw]) []
  have hall := RunsIn.seq f1 (RunsIn.seq hloop (RunsIn.seq hpR
    (RunsIn.seq u1 (RunsIn.seq u2 (RunsIn.seq u3 (RunsIn.seq u4 (RunsIn.seq u5 u6)))))))
  refine RunsIn.iff_runs.mp (RunsIn.mono (RunsIn.congr hall ?_ ?_) (fun _ _ => trivial) le_rfl)
  · funext k
    by_cases k1 : k = sA
    · subst k1
      simp +decide only [Function.update_apply, ↓reduceIte, hS5, List.reverse_reverse, hL0A]
      rfl
    by_cases k2 : k = sY
    · subst k2
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k3 : k = sTmp
    · subst k3
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k4 : k = sCnt
    · subst k4
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k5 : k = sPad
    · subst k5
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k6 : k = sCr
    · subst k6
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k7 : k = sCw
    · subst k7
      simp +decide only [Function.update_apply, ↓reduceIte]
    simp only [Function.update_apply, k1, k2, k3, k4, k5, k6, k7, ↓reduceIte]
    rw [hS5v k k1 k2, hS0def]
    simp only [floorSt, Function.update_apply, k2, k3, k4, k5, k6, k7, ↓reduceIte]
  · have hlc := loopCost_telescope (loopPot Npad r w blks) (loopPot_step Npad r w blks)
      (7 * bitLen N0 + 7 * bitLen Npad + 19) blks.length
    have hP0 : loopPot Npad r w blks 0 = 0 := by
      simp [loopPot, outRecs, FramePassRAux.arrSyms_nil]
    have hPB : loopPot Npad r w blks blks.length = 76 * V := by
      simp [loopPot, hV]
    have hrev : (arrSyms (outRecs Npad r w blks).reverse).length = V := by
      rw [hV, length_arrSyms, length_arrSyms, List.map_reverse, List.sum_reverse]
    have hcv : cvol w (blks.map (padBlock Npad r)).flatten = V := rfl
    rw [hcv, hrev]
    rw [hlc, hP0, hPB]
    have hXY : (7 * bitLen N0 + 7 * bitLen Npad + 19 + 1) * blks.length ≤
        20 * ((blks.length + 1) * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1)) := by
      calc (7 * bitLen N0 + 7 * bitLen Npad + 19 + 1) * blks.length
          ≤ (20 * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1)) * (blks.length + 1) :=
            Nat.mul_le_mul (by omega) (Nat.le_succ _)
        _ = 20 * ((blks.length + 1) * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1)) := by
            ring
    have hY1 : 1 ≤ (blks.length + 1) * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    generalize (7 * bitLen N0 + 7 * bitLen Npad + 19 + 1) * blks.length = X at hXY ⊢
    generalize (blks.length + 1) * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1) = Y
      at hXY hY1 ⊢
    omega

end SubNLogN.Machine.Layer.DrvPadDescAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts SubNLogN.Machine DrvPadDescAux

/-- **Zero-row padding kernel** (`DrvPadStmt`, Section A.6 (`sec:transfer-layer`)): proved. -/
theorem drvPad_holds : DrvPadStmt := by
  refine ⟨100, fun _ => ⟨PE, inferInstance, inferInstance, Option Sym, padProg, inferInstance,
    ⟨none⟩, closed_padProg, ?_⟩⟩
  intro N0 Npad r w blks rest r1 r2 r3 r4 S hN0 hw hblk hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3 hS4
  exact runs_padProg N0 Npad r w hN0 hw blks hblk rest r1 r2 r3 r4 hrest hr1 hr2 hr3 hr4 S hS0 hS1
    hS2 hS3 hS4

end SubNLogN.Machine.Layer
