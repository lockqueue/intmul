/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadIface

/-!
# K5 spreading: the slot pass (`Bridge/SpreadSlot.lean`)

**Scope (honest summary).** Proves the sub-contract `SpreadAux.SlotPassStmt`
(`Bridge/SpreadIface.lean`): the bit-serial lockstep adder of one output slot, as an AR program
(`Arith/Base.lean`) uniform in the stack type. Everything is proved.

## Design
* **Program** (`slProg`): set the accumulator to `0`; walk the ruler `R` (marks go to `X`), and
  in each step read the head of each of the nine streams (pop it and add `±bit` if it is a bit;
  an exhausted stream or a non-bit head reads as `0` and is not popped), push the parity of the
  accumulator onto `out` and halve the accumulator (floor); finally move the marks back from `X`
  to `R`. Exact cost `47 s + 5`.
* **Accumulator.** The five flags `c, st, hf, sg, x` of `AReg` hold a residue mod `32`
  (`slAcc`, `slSetAcc`), so additions are exact. Parity and halving use the signed representative
  in `[-16, 16)` (`slSRep`). It is exact because the carry stays in `[-4, 5]` and the head sum is
  in `[-4, 5]` (five positive and four negative streams), so the accumulator stays in `[-8, 10]`.
* **Proof.** The walk with a register invariant (`slWalk_eval_inv`, from `walk_eval_family`), the
  nine reads by list induction (`slEval_readAll`), the `serialRun` snoc identity
  (`slSerialRun_snoc`), and an explicit family of stacks per walk step (`slStT`).

Helpers live in `SubNLogN.Machine.Bridge.SpreadSlotAux`; the public theorem is
`SpreadAux.slotPass_holds`.
-/

namespace SubNLogN.Machine.Bridge.SpreadSlotAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith SubNLogN.Machine.Bridge.SpreadAux

/-! ## The accumulator: five register flags holding a residue mod `32` -/

/-- A flag as `0` or `1`. -/
def slFlag (b : Bool) : ℕ := if b then 1 else 0

/-- The accumulator residue held by the flags `c, st, hf, sg, x`. -/
def slAcc (v : AReg) : ZMod 32 :=
  ((slFlag v.c + 2 * slFlag v.st + 4 * slFlag v.hf + 8 * slFlag v.sg + 16 * slFlag v.x : ℕ) :
    ZMod 32)

/-- Store a residue in the flags `c, st, hf, sg, x`. -/
def slSetAcc (z : ZMod 32) (v : AReg) : AReg :=
  { v with
    c := decide (z.val % 2 = 1)
    st := decide (z.val / 2 % 2 = 1)
    hf := decide (z.val / 4 % 2 = 1)
    sg := decide (z.val / 8 % 2 = 1)
    x := decide (z.val / 16 % 2 = 1) }

theorem slAcc_setAcc (z : ZMod 32) (v : AReg) : slAcc (slSetAcc z v) = z := by
  have hz : z.val < 32 := ZMod.val_lt z
  have key : slFlag (decide (z.val % 2 = 1)) + 2 * slFlag (decide (z.val / 2 % 2 = 1)) +
      4 * slFlag (decide (z.val / 4 % 2 = 1)) + 8 * slFlag (decide (z.val / 8 % 2 = 1)) +
      16 * slFlag (decide (z.val / 16 % 2 = 1)) = z.val := by
    simp only [slFlag, decide_eq_true_eq]
    split_ifs <;> omega
  calc slAcc (slSetAcc z v) = ((z.val : ℕ) : ZMod 32) := by rw [← key]; rfl
    _ = z := ZMod.natCast_zmod_val z

theorem slAcc_o (v : AReg) (o : Option Sym) : slAcc { v with o := o } = slAcc v := rfl

theorem slAcc_setR (v : AReg) (o : Option Sym) : slAcc (setR v o) = slAcc v := rfl

/-- The signed representative in `[-16, 16)` of a residue mod `32`. -/
def slSRep (z : ZMod 32) : ℤ := if z.val < 16 then (z.val : ℤ) else (z.val : ℤ) - 32

theorem slSRep_intCast (a : ℤ) (h1 : -16 ≤ a) (h2 : a < 16) : slSRep (a : ZMod 32) = a := by
  have hv := ZMod.val_intCast (n := 32) a
  push_cast at hv
  unfold slSRep
  split_ifs with h <;> omega

/-! ## The lockstep adder, step by step -/

/-- One step of the adder state `(carry, streams)`. -/
def slStep (x : ℤ × List (Bool × List Bool)) : ℤ × List (Bool × List Bool) :=
  ((x.1 + headSum x.2) / 2, tails x.2)

/-- The output bit of the adder in state `x`. -/
def slBit (x : ℤ × List (Bool × List Bool)) : Bool := decide ((x.1 + headSum x.2) % 2 = 1)

/-- `serialRun` grows at the end: step `t` appends the bit of the state after `t` steps. -/
theorem slSerialRun_snoc : ∀ (t : ℕ) (c : ℤ) (srcs : List (Bool × List Bool)),
    serialRun (t + 1) c srcs = serialRun t c srcs ++ [slBit (slStep^[t] (c, srcs))]
  | 0, c, srcs => rfl
  | t + 1, c, srcs => by
    have ih := slSerialRun_snoc t ((c + headSum srcs) / 2) (tails srcs)
    have e1 : serialRun (t + 1 + 1) c srcs = decide ((c + headSum srcs) % 2 = 1) ::
        serialRun (t + 1) ((c + headSum srcs) / 2) (tails srcs) := rfl
    have e2 : serialRun (t + 1) c srcs = decide ((c + headSum srcs) % 2 = 1) ::
        serialRun t ((c + headSum srcs) / 2) (tails srcs) := rfl
    rw [e1, e2, ih, Function.iterate_succ_apply]
    rfl

theorem slTails_slotSrcs (L : Fin 9 → List Bool) :
    tails (slotSrcs L) = slotSrcs fun j => (L j).tail := by
  simp [tails, slotSrcs, List.map_map, Function.comp_def]

theorem slStep_iter (L : Fin 9 → List Bool) : ∀ t : ℕ,
    (slStep^[t] (0, slotSrcs L)).2 = slotSrcs fun j => (L j).drop t
  | 0 => by simp
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    show tails (slStep^[t] (0, slotSrcs L)).2 = _
    rw [slStep_iter L t, slTails_slotSrcs]
    simp only [List.tail_drop]

/-- The carry before step `t` of the slot adder. -/
def slCarry (L : Fin 9 → List Bool) (t : ℕ) : ℤ := (slStep^[t] (0, slotSrcs L)).1

/-- The signed head sum at step `t` of the slot adder. -/
def slHeadAt (L : Fin 9 → List Bool) (t : ℕ) : ℤ := headSum (slotSrcs fun j => (L j).drop t)

theorem slCarry_succ (L : Fin 9 → List Bool) (t : ℕ) :
    slCarry L (t + 1) = (slCarry L t + slHeadAt L t) / 2 := by
  unfold slCarry slHeadAt
  rw [Function.iterate_succ_apply', ← slStep_iter L t]
  rfl

theorem slBit_slot (L : Fin 9 → List Bool) (t : ℕ) :
    slBit (slStep^[t] (0, slotSrcs L)) = decide ((slCarry L t + slHeadAt L t) % 2 = 1) := by
  unfold slBit slCarry slHeadAt
  rw [slStep_iter]

/-! ## Range of the head sum and of the carry -/

theorem slHeadSum_le (srcs : List (Bool × List Bool)) :
    headSum srcs ≤ (srcs.map fun p => if p.1 then (1 : ℤ) else 0).sum := by
  induction srcs with
  | nil => simp [headSum]
  | cons p srcs ih =>
    have hp : sgnBit p.1 (p.2.headD false) ≤ if p.1 then 1 else 0 := by
      unfold sgnBit; split_ifs <;> norm_num
    simp only [headSum, List.map_cons, List.sum_cons] at ih ⊢
    linarith

theorem slHeadSum_ge (srcs : List (Bool × List Bool)) :
    -(srcs.map fun p => if p.1 then (0 : ℤ) else 1).sum ≤ headSum srcs := by
  induction srcs with
  | nil => simp [headSum]
  | cons p srcs ih =>
    have hp : -(if p.1 then (0 : ℤ) else 1) ≤ sgnBit p.1 (p.2.headD false) := by
      unfold sgnBit; split_ifs <;> norm_num
    simp only [headSum, List.map_cons, List.sum_cons] at ih ⊢
    linarith

theorem slPos_count0 : ((List.finRange 9).map fun j => if slotSign j then (1 : ℤ) else 0).sum = 5 := by
  decide

theorem slNeg_count0 : ((List.finRange 9).map fun j => if slotSign j then (0 : ℤ) else 1).sum = 4 := by
  decide

theorem slPos_count (L : Fin 9 → List Bool) :
    ((slotSrcs L).map fun p => if p.1 then (1 : ℤ) else 0).sum = 5 := by
  simp only [slotSrcs, List.map_map, Function.comp_def]
  exact slPos_count0

theorem slNeg_count (L : Fin 9 → List Bool) :
    ((slotSrcs L).map fun p => if p.1 then (0 : ℤ) else 1).sum = 4 := by
  simp only [slotSrcs, List.map_map, Function.comp_def]
  exact slNeg_count0

/-- Five positive and four negative streams: the head sum is in `[-4, 5]`. -/
theorem slHeadSum_slot (L : Fin 9 → List Bool) :
    -4 ≤ headSum (slotSrcs L) ∧ headSum (slotSrcs L) ≤ 5 := by
  have h1 := slHeadSum_le (slotSrcs L)
  have h2 := slHeadSum_ge (slotSrcs L)
  rw [slPos_count] at h1
  rw [slNeg_count] at h2
  constructor <;> linarith

/-- The carry of the slot adder stays in `[-4, 5]`. -/
theorem slCarry_bounds (L : Fin 9 → List Bool) : ∀ t, -4 ≤ slCarry L t ∧ slCarry L t ≤ 5
  | 0 => by simp [slCarry]
  | t + 1 => by
    rw [slCarry_succ]
    have ih := slCarry_bounds L t
    have hb := slHeadSum_slot fun j => (L j).drop t
    unfold slHeadAt
    omega

/-! ## Streams -/

/-- The head bit of a stack (`false` for an empty stack or a non-bit head). -/
def slHeadBit (l : List Sym) : Bool := bitD l.head? false

/-- Pop the head of a stack if it is a bit. -/
def slPopBit (l : List Sym) : List Sym := if isBitO l.head? then l.tail else l

/-- Pop up to `t` leading bits. -/
def slPopBits (t : ℕ) (l : List Sym) : List Sym := slPopBit^[t] l

theorem slPopBit_bit (b : Bool) (l : List Sym) : slPopBit (.bit b :: l) = l := by
  simp [slPopBit]

theorem slPopBit_of_not (l : List Sym) (h : isBitO l.head? = false) : slPopBit l = l := by
  simp [slPopBit, h]

theorem slHeadBit_of_not (l : List Sym) (h : isBitO l.head? = false) : slHeadBit l = false := by
  rcases l with _ | ⟨y, l⟩
  · rfl
  · rcases y with b | _ | _ | _ | _ | _ | _ <;> simp_all [slHeadBit, isBitO, bitD]

theorem slPopBits_eq (rest : List Sym) (hr : TermOK rest) : ∀ (t : ℕ) (l : List Bool),
    slPopBits t (l.map Sym.bit ++ rest) = (l.drop t).map Sym.bit ++ rest
  | 0, l => rfl
  | t + 1, l => by
    show slPopBit^[t] (slPopBit (l.map Sym.bit ++ rest)) = _
    cases l with
    | nil =>
      rw [List.map_nil, List.nil_append, slPopBit_of_not rest (isBitO_false_of_termOK hr)]
      simpa [slPopBits] using slPopBits_eq rest hr t []
    | cons b l =>
      rw [List.map_cons, List.cons_append, slPopBit_bit]
      exact slPopBits_eq rest hr t l

theorem slPopBits_succ (t : ℕ) (l : List Sym) : slPopBits (t + 1) l = slPopBit (slPopBits t l) :=
  Function.iterate_succ_apply' _ _ _

theorem slHeadBit_stream (l : List Bool) (rest : List Sym) (hr : TermOK rest) :
    slHeadBit (l.map Sym.bit ++ rest) = l.headD false := by
  cases l with
  | nil => simpa [slHeadBit] using bitD_of_termOK hr false
  | cons b l => simp [slHeadBit]

/-! ## Programs -/

variable {K : Type}

/-- `acc += ±bit` (sign `σ`) for the bit read into `o`. -/
def slAddOp (σ : Bool) (v : AReg) : AReg :=
  slSetAcc (slAcc v + ((sgnBit σ (bitD v.o false) : ℤ) : ZMod 32)) v

/-- Read the head of stream `k` (sign `σ`): if it is a bit, pop it and add `±bit`; otherwise
do nothing. 4 steps either way. -/
def slReadAdd (σ : Bool) (k : K) : AProg K :=
  .seq (peekO k) (.ite (fun v => isBitO v.o) (.seq (drop1 k) (.load (slAddOp σ)))
    (.seq skipA skipA))

/-- Read the heads of a list of signed streams. -/
def slReadAll : List (Bool × K) → AProg K
  | [] => skipA
  | p :: ps => .seq (slReadAdd p.1 p.2) (slReadAll ps)

/-- The output bit: the parity of the accumulator. -/
def slParBit (v : AReg) : Sym := .bit (decide (slSRep (slAcc v) % 2 = 1))

/-- Halve the accumulator (floor). -/
def slHalfOp (v : AReg) : AReg := slSetAcc ((slSRep (slAcc v) / 2 : ℤ) : ZMod 32) v

/-- The signed source streams of the slot pass. -/
def slSrcPairs (ι : SlotRole → K) : List (Bool × K) :=
  (List.finRange 9).map fun j => (slotSign j, ι (.src j))

/-- One adder step: read the nine heads, push the output bit, halve the accumulator. -/
def slBody (ι : SlotRole → K) : AProg K :=
  .seq (slReadAll (slSrcPairs ι)) (.seq (.push (ι .out) slParBit) (.load slHalfOp))

/-- **The slot pass.** -/
def slProg (ι : SlotRole → K) : AProg K :=
  .seq (.load (slSetAcc 0)) (.seq (walk (ι .R) (ι .X) (slBody ι)) (moveMarks (ι .X) (ι .R)))

theorem slClosed_readAll : ∀ ps : List (Bool × K), (slReadAll ps).FreeBelow 0
  | [] => by simp [slReadAll, skipA, Prog.FreeBelow]
  | p :: ps => by
    simp only [slReadAll, Prog.FreeBelow]
    exact ⟨by simp [slReadAdd, peekO, drop1, skipA, Prog.FreeBelow], slClosed_readAll ps⟩

theorem slClosed_prog (ι : SlotRole → K) : (slProg ι).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, slProg, slBody, walk, walkLoop, walkStep, moveMarks, mmLoop,
    peekR, drop1, pushS, slClosed_readAll]

/-! ## Evaluation: one read, all reads, the walk -/

section Eval

variable [DecidableEq K]

theorem slEval_readAdd_bit (σ b : Bool) (k : K) (u : AReg) (Sx : K → List Sym) (l : List Sym)
    (hk : Sx k = .bit b :: l) :
    Eval [] (slReadAdd σ k) ⟨u, Sx⟩
      ⟨slAddOp σ { u with o := some (.bit b) }, Function.update Sx k l⟩ 4 := by
  have e1 : Eval [] (peekO k) ⟨u, Sx⟩ ⟨{ u with o := some (.bit b) }, Sx⟩ 1 := by
    have e := eval_peekO k u Sx
    rw [hk] at e
    exact e
  have e2 := eval_drop1 k { u with o := some (.bit b) } Sx _ _ hk
  have e3 := Eval.load [] (slAddOp σ) { u with o := some (.bit b) } (Function.update Sx k l)
  exact (Eval.seq e1 (Eval.ite_true (c := fun v : AReg => isBitO v.o) (q := .seq skipA skipA)
    rfl (Eval.seq e2 e3))).of_eq rfl rfl

theorem slEval_readAdd_not (σ : Bool) (k : K) (u : AReg) (Sx : K → List Sym)
    (hk : isBitO (Sx k).head? = false) :
    Eval [] (slReadAdd σ k) ⟨u, Sx⟩ ⟨{ u with o := (Sx k).head? }, Sx⟩ 4 := by
  have e1 := eval_peekO k u Sx
  have e2 := Eval.seq (eval_skipA { u with o := (Sx k).head? } Sx)
    (eval_skipA { u with o := (Sx k).head? } Sx)
  exact (Eval.seq e1 (Eval.ite_false (c := fun v : AReg => isBitO v.o)
    (p := .seq (drop1 k) (.load (slAddOp σ))) hk e2)).of_eq rfl rfl

/-- **One read**: the head bit (if any) is popped and added with its sign. -/
theorem slEval_readAdd (σ : Bool) (k : K) (u : AReg) (Sx : K → List Sym) :
    ∃ u', slAcc u' = slAcc u + ((sgnBit σ (slHeadBit (Sx k)) : ℤ) : ZMod 32) ∧
      Eval [] (slReadAdd σ k) ⟨u, Sx⟩ ⟨u', Function.update Sx k (slPopBit (Sx k))⟩ 4 := by
  by_cases hb : ∃ b l, Sx k = .bit b :: l
  · obtain ⟨b, l, hk⟩ := hb
    refine ⟨slAddOp σ { u with o := some (.bit b) }, ?_, ?_⟩
    · rw [slAddOp, slAcc_setAcc, hk]
      rfl
    · rw [hk, slPopBit_bit]
      exact slEval_readAdd_bit σ b k u Sx l hk
  · have hk : isBitO (Sx k).head? = false := by
      rcases h : Sx k with _ | ⟨y, l⟩
      · rfl
      · rcases y with b | _ | _ | _ | _ | _ | _
        · exact absurd ⟨b, l, h⟩ hb
        all_goals rfl
    refine ⟨{ u with o := (Sx k).head? }, ?_, ?_⟩
    · rw [slHeadBit_of_not _ hk, slAcc_o]
      simp [sgnBit]
    · rw [slPopBit_of_not _ hk, Function.update_eq_self]
      exact slEval_readAdd_not σ k u Sx hk

/-- The stacks after the reads: every listed stack has its head bit popped. -/
def slPopSrcs (ks : List K) (Sx : K → List Sym) : K → List Sym :=
  fun k => if k ∈ ks then slPopBit (Sx k) else Sx k

/-- The signed head sum of the listed streams. -/
def slSumHeads (Sx : K → List Sym) (ps : List (Bool × K)) : ℤ :=
  (ps.map fun p => sgnBit p.1 (slHeadBit (Sx p.2))).sum

/-- **All reads** (distinct streams): every head bit is popped, the signed head sum is added. -/
theorem slEval_readAll : ∀ (ps : List (Bool × K)), (ps.map Prod.snd).Nodup →
    ∀ (u : AReg) (Sx : K → List Sym),
    ∃ u', slAcc u' = slAcc u + ((slSumHeads Sx ps : ℤ) : ZMod 32) ∧
      Eval [] (slReadAll ps) ⟨u, Sx⟩ ⟨u', slPopSrcs (ps.map Prod.snd) Sx⟩ (4 * ps.length + 1)
  | [], _, u, Sx => ⟨u, by simp [slSumHeads], (eval_skipA u Sx).of_eq rfl (by simp)⟩
  | p :: ps, hnd, u, Sx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨u1, hu1, e1⟩ := slEval_readAdd p.1 p.2 u Sx
    obtain ⟨u2, hu2, e2⟩ := slEval_readAll ps hnd.2 u1
      (Function.update Sx p.2 (slPopBit (Sx p.2)))
    have hsum : slSumHeads (Function.update Sx p.2 (slPopBit (Sx p.2))) ps =
        slSumHeads Sx ps := by
      unfold slSumHeads
      congr 1
      refine List.map_congr_left fun q hq => ?_
      have hne : q.2 ≠ p.2 := fun h => hnd.1 (h ▸ List.mem_map_of_mem (f := Prod.snd) hq)
      rw [Function.update_of_ne hne]
    refine ⟨u2, ?_, (Eval.seq e1 e2).of_eq ?_ ?_⟩
    · rw [hu2, hu1, hsum]
      simp only [slSumHeads, List.map_cons, List.sum_cons]
      push_cast
      ring
    · congr 1
      funext k
      by_cases hk : k = p.2
      · subst hk
        have h1 : p.2 ∈ (p :: ps).map Prod.snd := by simp
        simp only [slPopSrcs, if_neg hnd.1, if_pos h1, Function.update_self]
      · have h1 : (k ∈ (p :: ps).map Prod.snd) ↔ k ∈ ps.map Prod.snd := by
          simp only [List.map_cons, List.mem_cons, hk, false_or]
        simp only [slPopSrcs, Function.update_of_ne hk, h1]
    · simp only [List.length_cons]
      ring

/-- **A ruler walk with a register invariant** `P` (insensitive to the ruler register). -/
theorem slWalk_eval_inv {R X : K} (hRX : R ≠ X) (body : AProg K) (n : ℕ)
    (D X0 : List Sym) (hD : D.head? ≠ some .mark)
    (S : ℕ → K → List Sym) (hSR : ∀ j ≤ n, S j R = List.replicate (n - j) .mark ++ D)
    (hSX : ∀ j ≤ n, S j X = List.replicate j .mark ++ X0) (t : ℕ → ℕ)
    (P : ℕ → AReg → Prop) (hP : ∀ j u o, P j u → P j (setR u o))
    (hb : ∀ j < n, ∀ u : AReg, P j u → ∃ w : AReg, P (j + 1) w ∧
      Eval [] body ⟨u, Function.update (Function.update (S j) R
        (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: S j X)⟩ ⟨w, S (j + 1)⟩ (t j))
    (v0 : AReg) (h0 : P 0 v0) :
    ∃ v', P n v' ∧ Eval [] (walk R X body) ⟨v0, S 0⟩ ⟨v', S n⟩
      ((Finset.range n).sum (fun j => t j + 4) + 2) := by
  classical
  let step : ℕ → AReg → AReg := fun j u =>
    if h : j < n ∧ P j u then Classical.choose (hb j h.1 u h.2) else u
  let u : ℕ → AReg := fun j => Nat.rec (motive := fun _ => AReg) (setR v0 (S 0 R).head?)
    (fun j uj => setR (step j uj) (S (j + 1) R).head?) j
  have hPu : ∀ j, j ≤ n → P j (u j) := by
    intro j
    induction j with
    | zero => intro _; exact hP 0 v0 _ h0
    | succ j ih =>
      intro hj
      have hj' : j < n := by omega
      have hPj := ih (by omega)
      show P (j + 1) (setR (step j (u j)) (S (j + 1) R).head?)
      apply hP
      simp only [step, dif_pos (And.intro hj' hPj)]
      exact (Classical.choose_spec (hb j hj' (u j) hPj)).1
  refine ⟨u n, hPu n le_rfl, walk_eval_family hRX body n D X0 hD S hSR hSX u
    (fun j => step j (u j)) t (fun j _ => ?_) (fun j _ => rfl) (fun j hj => ?_) v0 rfl⟩
  · cases j <;> rfl
  · have hPj := hPu j hj.le
    show Eval [] body _ ⟨step j (u j), S (j + 1)⟩ (t j)
    simp only [step, dif_pos (And.intro hj hPj)]
    exact (Classical.choose_spec (hb j hj (u j) hPj)).2

end Eval

/-! ## The stacks of the walk -/

section Stacks

/-- The source stacks. -/
def slSrcList (ι : SlotRole → K) : List K := (List.finRange 9).map fun j => ι (.src j)

theorem slSrcPairs_snd (ι : SlotRole → K) : (slSrcPairs ι).map Prod.snd = slSrcList ι := by
  simp [slSrcPairs, slSrcList, List.map_map, Function.comp_def]

theorem slNot_mem_srcList {ι : SlotRole → K} (hinj : Function.Injective ι) (r : SlotRole)
    (hr : ∀ j, r ≠ .src j) : ι r ∉ slSrcList ι := by
  simp only [slSrcList, List.mem_map, List.mem_finRange, true_and, not_exists]
  intro j h
  exact hr j (hinj h).symm

variable [DecidableEq K]

/-- The stacks before step `t` of the walk. -/
def slStT (ι : SlotRole → K) (s : ℕ) (D : List Sym) (S : K → List Sym)
    (L : Fin 9 → List Bool) (t : ℕ) : K → List Sym := fun k =>
  if k = ι .R then List.replicate (s - t) .mark ++ D
  else if k = ι .X then List.replicate t .mark ++ S (ι .X)
  else if k = ι .out then (serialRun t 0 (slotSrcs L)).reverse.map Sym.bit ++ S (ι .out)
  else if k ∈ slSrcList ι then slPopBits t (S k)
  else S k

variable {ι : SlotRole → K} {s : ℕ} {D : List Sym} {S : K → List Sym} {L : Fin 9 → List Bool}

theorem slStT_R (t : ℕ) : slStT ι s D S L t (ι .R) = List.replicate (s - t) .mark ++ D := by
  simp [slStT]

theorem slStT_X (hinj : Function.Injective ι) (t : ℕ) :
    slStT ι s D S L t (ι .X) = List.replicate t .mark ++ S (ι .X) := by
  simp [slStT, hinj.eq_iff]

theorem slStT_out (hinj : Function.Injective ι) (t : ℕ) :
    slStT ι s D S L t (ι .out) =
      (serialRun t 0 (slotSrcs L)).reverse.map Sym.bit ++ S (ι .out) := by
  simp [slStT, hinj.eq_iff]

theorem slStT_src (hinj : Function.Injective ι) (t : ℕ) (j : Fin 9) :
    slStT ι s D S L t (ι (.src j)) = slPopBits t (S (ι (.src j))) := by
  simp [slStT, slSrcList, hinj.eq_iff]

theorem slStT_other (t : ℕ) (k : K) (h1 : k ≠ ι .R) (h2 : k ≠ ι .X) (h3 : k ≠ ι .out)
    (h4 : ∀ j, k ≠ ι (.src j)) : slStT ι s D S L t k = S k := by
  have hm : k ∉ slSrcList ι := by
    simp only [slSrcList, List.mem_map, List.mem_finRange, true_and, not_exists]
    exact fun j hj => h4 j hj.symm
  simp [slStT, h1, h2, h3, hm]

/-- **One step of the walk**: from the stacks of step `t` (one more mark moved from `R` to `X`)
and the carry `slCarry L t`, the body reaches the stacks of step `t + 1` and the next carry. -/
theorem slBody_step (hinj : Function.Injective ι) (rest : Fin 9 → List Sym)
    (hrest : ∀ j, TermOK (rest j)) (hsrc : ∀ j, S (ι (.src j)) = (L j).map Sym.bit ++ rest j)
    (t : ℕ) (u : AReg) (hu : slAcc u = ((slCarry L t : ℤ) : ZMod 32)) :
    ∃ w, slAcc w = ((slCarry L (t + 1) : ℤ) : ZMod 32) ∧
      Eval [] (slBody ι) ⟨u, Function.update (Function.update (slStT ι s D S L t) (ι .R)
        (List.replicate (s - t - 1) .mark ++ D)) (ι .X) (.mark :: slStT ι s D S L t (ι .X))⟩
        ⟨w, slStT ι s D S L (t + 1)⟩ 39 := by
  have hRX : ι .R ≠ ι .X := hinj.ne (by simp)
  have hoR : ι .out ≠ ι .R := hinj.ne (by simp)
  have hoX : ι .out ≠ ι .X := hinj.ne (by simp)
  have hsR : ∀ j, ι (.src j) ≠ ι .R := fun j => hinj.ne (by simp)
  have hsX : ∀ j, ι (.src j) ≠ ι .X := fun j => hinj.ne (by simp)
  set B0 := Function.update (Function.update (slStT ι s D S L t) (ι .R)
    (List.replicate (s - t - 1) .mark ++ D)) (ι .X) (.mark :: slStT ι s D S L t (ι .X)) with hB0
  have hnd : ((slSrcPairs ι).map Prod.snd).Nodup := by
    rw [slSrcPairs_snd]
    exact List.Nodup.map (fun a b h => by simpa using hinj h) (List.nodup_finRange 9)
  obtain ⟨u1, hu1, e1⟩ := slEval_readAll (slSrcPairs ι) hnd u B0
  have hB0src : ∀ j, B0 (ι (.src j)) = ((L j).drop t).map Sym.bit ++ rest j := by
    intro j
    rw [hB0, Function.update_of_ne (hsX j), Function.update_of_ne (hsR j), slStT_src hinj,
      hsrc j, slPopBits_eq _ (hrest j)]
  have hsumEq : slSumHeads B0 (slSrcPairs ι) = slHeadAt L t := by
    simp only [slSumHeads, slHeadAt, headSum, slSrcPairs, slotSrcs, List.map_map,
      Function.comp_def]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [hB0src j, slHeadBit_stream _ _ (hrest j)]
  have hrange : -16 ≤ slCarry L t + slHeadAt L t ∧ slCarry L t + slHeadAt L t < 16 := by
    have h1 := slCarry_bounds L t
    have h2 := slHeadSum_slot fun j => (L j).drop t
    unfold slHeadAt
    omega
  have hacc1 : slAcc u1 = ((slCarry L t + slHeadAt L t : ℤ) : ZMod 32) := by
    rw [hu1, hu, hsumEq]
    push_cast
    ring
  have hsr : slSRep (slAcc u1) = slCarry L t + slHeadAt L t := by
    rw [hacc1]
    exact slSRep_intCast _ hrange.1 hrange.2
  set B1 := slPopSrcs ((slSrcPairs ι).map Prod.snd) B0 with hB1
  have hB1n : ∀ k, k ∉ slSrcList ι → B1 k = B0 k := by
    intro k hk
    rw [hB1, slSrcPairs_snd]
    simp only [slPopSrcs, if_neg hk]
  have hB1m : ∀ k, k ∈ slSrcList ι → B1 k = slPopBit (B0 k) := by
    intro k hk
    rw [hB1, slSrcPairs_snd]
    simp only [slPopSrcs, if_pos hk]
  have e2 := Eval.push [] (ι .out) slParBit u1 B1
  have e3 := Eval.load [] slHalfOp u1 (Function.update B1 (ι .out) (slParBit u1 :: B1 (ι .out)))
  refine ⟨slHalfOp u1, ?_, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ ?_⟩
  · rw [slHalfOp, slAcc_setAcc, hsr, slCarry_succ]
  · congr 1
    funext k
    by_cases hko : k = ι .out
    · subst hko
      rw [Function.update_self, hB1n _ (slNot_mem_srcList hinj .out (fun j => by simp)), hB0,
        Function.update_of_ne hoX, Function.update_of_ne hoR, slStT_out hinj t,
        slStT_out hinj (t + 1), slSerialRun_snoc, slBit_slot, slParBit, hsr]
      simp
    · rw [Function.update_of_ne hko]
      by_cases hkX : k = ι .X
      · subst hkX
        rw [hB1n _ (slNot_mem_srcList hinj .X (fun j => by simp)), hB0, Function.update_self,
          slStT_X hinj t, slStT_X hinj (t + 1), List.replicate_succ, List.cons_append]
      · by_cases hkR : k = ι .R
        · subst hkR
          rw [hB1n _ (slNot_mem_srcList hinj .R (fun j => by simp)), hB0,
            Function.update_of_ne hRX, Function.update_self, slStT_R (t + 1), Nat.sub_sub]
        · by_cases hks : k ∈ slSrcList ι
          · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hks
            rw [hB1m _ hks, hB0src j, slStT_src hinj, slPopBits_succ, hsrc j,
              slPopBits_eq _ (hrest j)]
          · have h4 : ∀ j, k ≠ ι (.src j) := fun j h =>
              hks (h ▸ List.mem_map_of_mem (f := fun j => ι (.src j)) (List.mem_finRange j))
            rw [hB1n _ hks, hB0, Function.update_of_ne hkX, Function.update_of_ne hkR,
              slStT_other t k hkR hkX hko h4, slStT_other (t + 1) k hkR hkX hko h4]
  · simp [slSrcPairs]

end Stacks

end SubNLogN.Machine.Bridge.SpreadSlotAux

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
open SubNLogN.Machine.Bridge.SpreadSlotAux

/-- **The slot pass holds** (`SlotPassStmt`), by `slProg` (exact cost `47 s + 5`, so `C = 50`). -/
theorem slotPass_holds : SlotPassStmt := by
  refine ⟨fun K _ ι => slProg ι, 50, fun K _ ι => slClosed_prog ι, ?_⟩
  intro K _ ι hinj s L rest D S v hrest hD hX hR hsrc
  have hRX : ι .R ≠ ι .X := hinj.ne (by simp)
  have hXR : ι .X ≠ ι .R := hinj.ne (by simp)
  have hoR : ι .out ≠ ι .R := hinj.ne (by simp)
  have hoX : ι .out ≠ ι .X := hinj.ne (by simp)
  have hsR : ∀ j, ι (.src j) ≠ ι .R := fun j => hinj.ne (by simp)
  have hsX : ∀ j, ι (.src j) ≠ ι .X := fun j => hinj.ne (by simp)
  obtain ⟨v2, -, e2⟩ := slWalk_eval_inv hRX (slBody ι) s D (S (ι .X)) hD (slStT ι s D S L)
    (fun j _ => slStT_R j) (fun j _ => slStT_X hinj j) (fun _ => 39)
    (fun t u => slAcc u = ((slCarry L t : ℤ) : ZMod 32))
    (fun j u o h => (slAcc_setR u o).trans h)
    (fun t _ u hu => slBody_step hinj rest hrest hsrc t u hu)
    (slSetAcc 0 v) (by
      show slAcc (slSetAcc 0 v) = ((slCarry L 0 : ℤ) : ZMod 32)
      rw [slAcc_setAcc]
      simp [slCarry])
  have hT0 : slStT ι s D S L 0 = S := by
    funext k
    unfold slStT
    split_ifs with h1 h2 h3 h4
    · rw [h1, hR, Nat.sub_zero]
    · rw [h2]; simp
    · rw [h3]; simp [serialRun]
    · rfl
    · rfl
  rw [hT0] at e2
  have e1 := Eval.load [] (slSetAcc 0) v S
  have e3 := moveMarks_eval hXR s (S (ι .X)) v2 (slStT ι s D S L s) hX (slStT_X hinj s)
  refine ⟨_, _, _, Eval.seq e1 (Eval.seq e2 e3), ?_, ?_, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  · intro j
    rw [Function.update_of_ne (hsR j), Function.update_of_ne (hsX j), slStT_src hinj,
      hsrc j, slPopBits_eq _ (hrest j)]
  · rw [Function.update_of_ne hoR, Function.update_of_ne hoX, slStT_out hinj]
  · intro k hk1 hk2
    by_cases hkR : k = ι .R
    · subst hkR
      rw [Function.update_self, slStT_R, Nat.sub_self, List.replicate_zero, List.nil_append, hR]
    · by_cases hkX : k = ι .X
      · subst hkX
        rw [Function.update_of_ne hXR, Function.update_self]
      · rw [Function.update_of_ne hkR, Function.update_of_ne hkX,
          slStT_other s k hkR hkX hk2 hk1]

end SubNLogN.Machine.Bridge.SpreadAux
