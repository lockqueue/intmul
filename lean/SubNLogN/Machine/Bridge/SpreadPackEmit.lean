/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadPackMath
import SubNLogN.Machine.Bridge.SpreadPrim2

/-!
# K5 spreading, Kronecker packing: the trimmed emitter (`Bridge/SpreadPackEmit.lean`)

**Scope (honest summary).** Programs and proved exact evaluation lemmas (no contract here):
* `tpush F out bit`: trimmed push of one bit onto the output `out`, with the flag stack `F`
  (`[]` before the first `1`, `[mark]` after); cost exactly `5` (`eval_tpush`, `eval_tpushT`).
  The bit is read from the register `o` or is the constant `0`, and the flag is peeked inside the
  program, so the stack effect does not depend on the starting register.
* `emitField e`: one `w`-bit field, most significant bit on top of the buffer `A`, is emitted into
  the part pair `p`/`m` (`re⁺`/`re⁻` or `im⁺`/`im⁻`): `s - w` zeros to both (ruler `Rpad`), the
  sign (`0` to `p`, sign to `m`), the `w - 1` low bits (ruler `Rlo`; bit to `p`, `0` to `m`).
  Rulers and walk temporaries are restored (`emitField_eval`).
-/

namespace SubNLogN.Machine.Bridge.SpreadPackAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SpreadAux Computability

/-- Flag stack content: `[mark]` once a `1` was emitted. -/
def flagStk (b : Bool) : List Sym := if b then [Sym.mark] else []

/-- Output content: the trimmed bits `P` (most significant first) above `D`. -/
def tst (P : List Bool) (D : List Sym) : List Sym := (trimPush false P []).map Sym.bit ++ D

theorem isMarkO_flagStk (g : Bool) : isMarkO (flagStk g).head? = g := by cases g <;> rfl

theorem tst_snoc (P : List Bool) (b : Bool) (D : List Sym) :
    tst (P ++ [b]) D = if P.any id || b then Sym.bit b :: tst P D else tst P D := by
  unfold tst
  rw [trimPush_append, Bool.false_or, trimPush_single]
  split_ifs <;> simp

theorem any_snoc (P : List Bool) (b : Bool) : (P ++ [b]).any id = (P.any id || b) := by simp

section Kit

variable {K : Type}

/-- Trimmed push of `bit v` onto `out` with flag stack `F` (cost `5`). -/
def tpush (F out : K) (bit : AReg → Bool) : AProg K :=
  .seq (peekQ F) (.ite (fun v => isMarkO v.q || bit v)
    (.seq (.push out fun v => Sym.bit (bit v)) (.ite (fun v => isMarkO v.q) skipA (pushS F .mark)))
    (.seq skipA (.seq skipA skipA)))

variable [DecidableEq K]

theorem eval_tpush {F out : K} (hFo : F ≠ out) (bit : AReg → Bool) (g b : Bool) (v : AReg)
    (S : K → List Sym) (hF : S F = flagStk g) (hbit : bit { v with q := (S F).head? } = b) :
    Eval [] (tpush F out bit) ⟨v, S⟩
      ⟨{ v with q := (S F).head? }, Function.update (Function.update S out
        (if g || b then Sym.bit b :: S out else S out)) F (flagStk (g || b))⟩ 5 := by
  set v1 : AReg := { v with q := (S F).head? } with hv1
  have e1 : Eval [] (peekQ F) ⟨v, S⟩ ⟨v1, S⟩ 1 := eval_peekQ F v S
  have hq : isMarkO v1.q = g := by
    rw [hv1]
    show isMarkO (S F).head? = g
    rw [hF, isMarkO_flagStk]
  have epush : Eval [] (.push out fun v : AReg => Sym.bit (bit v)) ⟨v1, S⟩
      ⟨v1, Function.update S out (Sym.bit b :: S out)⟩ 1 :=
    (Eval.push [] out _ v1 S).of_eq (by rw [← hbit]) rfl
  have hFo' : (Function.update S out (Sym.bit b :: S out)) F = S F :=
    Function.update_of_ne hFo _ _
  cases g <;> cases b
  · refine (Eval.seq e1 (Eval.ite_false ?_ (Eval.seq (eval_skipA v1 S)
      (Eval.seq (eval_skipA v1 S) (eval_skipA v1 S))))).of_eq ?_ rfl
    · show (isMarkO v1.q || bit v1) = false
      rw [hq, hbit]
      rfl
    · congr 1
      funext k
      simp only [Function.update_apply]
      split_ifs with h1 h2 <;> simp_all [flagStk]
  · refine (Eval.seq e1 (Eval.ite_true ?_ (Eval.seq epush (Eval.ite_false ?_
      (eval_pushS F .mark v1 _))))).of_eq ?_ rfl
    · show (isMarkO v1.q || bit v1) = true
      rw [hq, hbit]
      rfl
    · exact hq
    · congr 1
      rw [hFo', hF]
      rfl
  · refine (Eval.seq e1 (Eval.ite_true ?_ (Eval.seq epush (Eval.ite_true ?_
      (eval_skipA v1 _))))).of_eq ?_ rfl
    · show (isMarkO v1.q || bit v1) = true
      rw [hq]
      rfl
    · exact hq
    · congr 1
      simp only [Bool.true_or, if_true]
      rw [← hF, ← hFo', Function.update_eq_self]
  · refine (Eval.seq e1 (Eval.ite_true ?_ (Eval.seq epush (Eval.ite_true ?_
      (eval_skipA v1 _))))).of_eq ?_ rfl
    · show (isMarkO v1.q || bit v1) = true
      rw [hq]
      rfl
    · exact hq
    · congr 1
      simp only [Bool.true_or, if_true]
      rw [← hF, ← hFo', Function.update_eq_self]

/-- `tpush` on a trimmed output: the emitted prefix grows by `b`. -/
theorem eval_tpushT {F out : K} (hFo : F ≠ out) (bit : AReg → Bool) (b : Bool) (P : List Bool)
    (D : List Sym) (v : AReg) (S : K → List Sym) (hF : S F = flagStk (P.any id))
    (hO : S out = tst P D) (hbit : bit { v with q := (S F).head? } = b) :
    Eval [] (tpush F out bit) ⟨v, S⟩
      ⟨{ v with q := (S F).head? }, Function.update (Function.update S out (tst (P ++ [b]) D)) F
        (flagStk ((P ++ [b]).any id))⟩ 5 := by
  refine (eval_tpush hFo bit (P.any id) b v S hF hbit).of_eq ?_ rfl
  rw [tst_snoc, any_snoc, ← hO]

/-- Rewrite the final stacks (and cost) of an evaluation, keeping its final register. -/
theorem eval_of_stk {p : AProg K} {s : ASt K} {v' : AReg} {S1 S2 : K → List Sym} {t1 t2 : ℕ}
    (h : Eval [] p s ⟨v', S1⟩ t1) (hS : S1 = S2) (ht : t1 = t2) : Eval [] p s ⟨v', S2⟩ t2 := by
  subst hS; subst ht; exact h

end Kit

/-- Stack roles of the field emitter: buffer, rulers `w - 1` / `s - w` with walk temporaries,
flag stacks and outputs of the part pair. -/
inductive EF
  | A | Rlo | X2 | Rpad | X3 | Fp | Fm | Op | Om
  deriving DecidableEq

section Emit

variable {K : Type}

/-- Zero step: `0` to both parts. -/
def zBody (e : EF → K) : AProg K :=
  .seq (tpush (e .Fp) (e .Op) fun _ => false) (tpush (e .Fm) (e .Om) fun _ => false)

/-- Low-bit step: pop a bit of `A`; it goes to `p`, `0` to `m`. -/
def lBody (e : EF → K) : AProg K :=
  .seq (popO (e .A)) (.seq (tpush (e .Fp) (e .Op) fun v => bitD v.o false)
    (tpush (e .Fm) (e .Om) fun _ => false))

/-- `s - w` zero steps (ruler `Rpad`, restored). -/
def emitZ (e : EF → K) : AProg K :=
  .seq (walk (e .Rpad) (e .X3) (zBody e)) (moveMarks (e .X3) (e .Rpad))

/-- Sign step: pop the sign of `A`; `0` to `p`, the sign to `m`. -/
def emitS (e : EF → K) : AProg K :=
  .seq (popO (e .A)) (.seq (tpush (e .Fp) (e .Op) fun _ => false)
    (tpush (e .Fm) (e .Om) fun v => bitD v.o false))

/-- `w - 1` low-bit steps (ruler `Rlo`, restored). -/
def emitL (e : EF → K) : AProg K :=
  .seq (walk (e .Rlo) (e .X2) (lBody e)) (moveMarks (e .X2) (e .Rlo))

/-- **The field emitter.** -/
def emitField (e : EF → K) : AProg K := .seq (emitZ e) (.seq (emitS e) (emitL e))

variable [DecidableEq K]

/-- Outputs and flags of the part pair set to the emitted prefixes `Pp`, `Pm`. -/
def setPM (e : EF → K) (S : K → List Sym) (Pp Pm : List Bool) (Dp Dm : List Sym) :
    K → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (e .Op) (tst Pp Dp))
    (e .Om) (tst Pm Dm)) (e .Fp) (flagStk (Pp.any id))) (e .Fm) (flagStk (Pm.any id))

theorem ext_e {e : EF → K} {f g : K → List Sym}
    (h1 : ∀ k, (∀ x, k ≠ e x) → f k = g k) (h2 : ∀ x, f (e x) = g (e x)) : f = g := by
  funext k
  by_cases hk : ∃ x, k = e x
  · obtain ⟨x, rfl⟩ := hk
    exact h2 x
  · exact h1 k (fun x hx => hk ⟨x, hx⟩)

theorem emitZ_eval (e : EF → K) (he : Function.Injective e) (n : ℕ) (Dpad : List Sym)
    (hD : Dpad.head? ≠ some .mark) (Pp Pm : List Bool) (Dp Dm : List Sym) (S : K → List Sym)
    (hX : (S (e .X3)).head? ≠ some .mark) (hR : S (e .Rpad) = List.replicate n .mark ++ Dpad)
    (v : AReg) :
    ∃ v', Eval [] (emitZ e) ⟨v, setPM e S Pp Pm Dp Dm⟩
      ⟨v', setPM e S (Pp ++ List.replicate n false) (Pm ++ List.replicate n false) Dp Dm⟩
      (18 * n + 4) := by
  let Sf : ℕ → K → List Sym := fun j => Function.update (Function.update
    (setPM e S (Pp ++ List.replicate j false) (Pm ++ List.replicate j false) Dp Dm)
    (e .Rpad) (List.replicate (n - j) .mark ++ Dpad)) (e .X3) (List.replicate j .mark ++ S (e .X3))
  have hRX : e .Rpad ≠ e .X3 := he.ne (by decide)
  have hSR : ∀ j ≤ n, Sf j (e .Rpad) = List.replicate (n - j) .mark ++ Dpad := by
    intro j _
    simp only [Sf, Function.update_of_ne hRX, Function.update_self]
  have hSX : ∀ j ≤ n, Sf j (e .X3) = List.replicate j .mark ++ S (e .X3) := by
    intro j _
    simp only [Sf, Function.update_self]
  have h0 : Sf 0 = setPM e S Pp Pm Dp Dm := by
    refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
    · simp [Sf, setPM, Function.update_apply, hk]
    · cases x <;> simp [Sf, setPM, Function.update_apply, he.eq_iff, hR]
  have hstep : ∀ j < n, ∀ u, ∃ w, Eval [] (zBody e) ⟨u, Function.update (Function.update (Sf j)
      (e .Rpad) (List.replicate (n - j - 1) .mark ++ Dpad)) (e .X3) (.mark :: Sf j (e .X3))⟩
      ⟨w, Sf (j + 1)⟩ 10 := by
    intro j hj u
    set T := Function.update (Function.update (Sf j) (e .Rpad)
      (List.replicate (n - j - 1) .mark ++ Dpad)) (e .X3) (.mark :: Sf j (e .X3)) with hT
    have hTFp : T (e .Fp) = flagStk ((Pp ++ List.replicate j false).any id) := by
      simp [hT, Sf, setPM, Function.update_apply, he.eq_iff]
    have hTOp : T (e .Op) = tst (Pp ++ List.replicate j false) Dp := by
      simp [hT, Sf, setPM, Function.update_apply, he.eq_iff]
    have ev1 := eval_tpushT (he.ne (by decide)) (fun _ => false) false
      (Pp ++ List.replicate j false) Dp u T hTFp hTOp rfl
    refine ⟨_, eval_of_stk (Eval.seq ev1 (eval_tpushT (he.ne (by decide)) (fun _ => false) false
      (Pm ++ List.replicate j false) Dm _ _ ?_ ?_ rfl)) ?_ rfl⟩
    · simp [hT, Sf, setPM, Function.update_apply, he.eq_iff]
    · simp [hT, Sf, setPM, Function.update_apply, he.eq_iff]
    · have hx3 : Sym.mark :: (List.replicate j Sym.mark ++ S (e .X3)) =
          List.replicate (j + 1) Sym.mark ++ S (e .X3) := by simp [List.replicate_succ]
      have hn1 : n - j - 1 = n - (j + 1) := by omega
      refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
      · simp [hT, Sf, setPM, Function.update_apply, hk]
      · cases x <;> simp [hT, Sf, setPM, Function.update_apply, he.eq_iff, hx3, hn1,
          List.replicate_succ']
  obtain ⟨v1, e1⟩ := walk_eval_family' hRX (zBody e) n Dpad (S (e .X3)) hD Sf hSR hSX
    (fun _ => 10) hstep v
  rw [h0] at e1
  have e2 := moveMarks_eval (he.ne (by decide) : e .X3 ≠ e .Rpad) n (S (e .X3)) v1 (Sf n) hX
    (hSX n le_rfl)
  have hfin : Function.update (Function.update (Sf n) (e .X3) (S (e .X3))) (e .Rpad)
      (List.replicate n .mark ++ Sf n (e .Rpad)) =
      setPM e S (Pp ++ List.replicate n false) (Pm ++ List.replicate n false) Dp Dm := by
    refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
    · simp [Sf, setPM, Function.update_apply, hk]
    · cases x <;> simp [Sf, setPM, Function.update_apply, he.eq_iff, hR]
  refine ⟨_, eval_of_stk (Eval.seq e1 e2) hfin ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

theorem emitS_eval (e : EF → K) (he : Function.Injective e) (sgn : Bool) (RA : List Sym)
    (Pp Pm : List Bool) (Dp Dm : List Sym) (S : K → List Sym)
    (hA : S (e .A) = Sym.bit sgn :: RA) (v : AReg) :
    ∃ v', Eval [] (emitS e) ⟨v, setPM e S Pp Pm Dp Dm⟩
      ⟨v', setPM e (Function.update S (e .A) RA) (Pp ++ [false]) (Pm ++ [sgn]) Dp Dm⟩ 11 := by
  have hA' : setPM e S Pp Pm Dp Dm (e .A) = Sym.bit sgn :: RA := by
    simp [setPM, he.eq_iff, hA]
  have e1 := eval_popO (e .A) v (setPM e S Pp Pm Dp Dm) _ _ hA'
  set T := Function.update (setPM e S Pp Pm Dp Dm) (e .A) RA with hT
  have hTFp : T (e .Fp) = flagStk (Pp.any id) := by simp [hT, setPM, he.eq_iff]
  have hTOp : T (e .Op) = tst Pp Dp := by simp [hT, setPM, he.eq_iff]
  have ev1 := eval_tpushT (he.ne (by decide)) (fun _ => false) false Pp Dp
    { v with o := some (Sym.bit sgn) } T hTFp hTOp rfl
  set T1 := Function.update (Function.update T (e .Op) (tst (Pp ++ [false]) Dp)) (e .Fp)
    (flagStk ((Pp ++ [false]).any id)) with hT1
  have hT1Fm : T1 (e .Fm) = flagStk (Pm.any id) := by simp [hT1, hT, setPM, he.eq_iff]
  have hT1Om : T1 (e .Om) = tst Pm Dm := by simp [hT1, hT, setPM, he.eq_iff]
  refine ⟨_, eval_of_stk (Eval.seq e1 (Eval.seq ev1 (eval_tpushT (he.ne (by decide))
    (fun v => bitD v.o false) sgn Pm Dm _ T1 hT1Fm hT1Om rfl))) ?_ rfl⟩
  refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
  · simp [hT1, hT, setPM, Function.update_apply, hk]
  · cases x <;> simp [hT1, hT, setPM, Function.update_apply, he.eq_iff]

theorem emitL_eval (e : EF → K) (he : Function.Injective e) (lows : List Bool)
    (RA Dlo : List Sym) (hD : Dlo.head? ≠ some .mark) (Pp Pm : List Bool) (Dp Dm : List Sym)
    (S : K → List Sym) (hX : (S (e .X2)).head? ≠ some .mark)
    (hR : S (e .Rlo) = List.replicate lows.length .mark ++ Dlo)
    (hA : S (e .A) = lows.reverse.map Sym.bit ++ RA) (v : AReg) :
    ∃ v', Eval [] (emitL e) ⟨v, setPM e S Pp Pm Dp Dm⟩
      ⟨v', setPM e (Function.update S (e .A) RA) (Pp ++ lows.reverse)
        (Pm ++ List.replicate lows.length false) Dp Dm⟩ (19 * lows.length + 4) := by
  set n := lows.length with hn
  set L := lows.reverse with hL
  have hLn : L.length = n := by rw [hL, List.length_reverse]
  let Sf : ℕ → K → List Sym := fun j => Function.update (Function.update
    (setPM e (Function.update S (e .A) ((L.drop j).map Sym.bit ++ RA)) (Pp ++ L.take j)
      (Pm ++ List.replicate j false) Dp Dm)
    (e .Rlo) (List.replicate (n - j) .mark ++ Dlo)) (e .X2) (List.replicate j .mark ++ S (e .X2))
  have hRX : e .Rlo ≠ e .X2 := he.ne (by decide)
  have hSR : ∀ j ≤ n, Sf j (e .Rlo) = List.replicate (n - j) .mark ++ Dlo := by
    intro j _
    simp only [Sf, Function.update_of_ne hRX, Function.update_self]
  have hSX : ∀ j ≤ n, Sf j (e .X2) = List.replicate j .mark ++ S (e .X2) := by
    intro j _
    simp only [Sf, Function.update_self]
  have h0 : Sf 0 = setPM e S Pp Pm Dp Dm := by
    refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
    · simp [Sf, setPM, Function.update_apply, hk]
    · cases x <;> simp [Sf, setPM, Function.update_apply, he.eq_iff, hR, hA, hL]
  obtain ⟨v1, e1⟩ := walk_eval_family' hRX (lBody e) n Dlo (S (e .X2)) hD Sf hSR hSX
    (fun _ => 11) (fun j hj u => by
      have hj' : j < L.length := by omega
      set T := Function.update (Function.update (Sf j) (e .Rlo)
        (List.replicate (n - j - 1) .mark ++ Dlo)) (e .X2) (.mark :: Sf j (e .X2)) with hT
      have hTA : T (e .A) = Sym.bit L[j] :: ((L.drop (j + 1)).map Sym.bit ++ RA) := by
        simp [hT, Sf, setPM, he.eq_iff]
        rw [List.drop_eq_getElem_cons (by simpa using hj'), List.getElem_map, List.cons_append]
      have e0 := eval_popO (e .A) u T _ _ hTA
      set T0 := Function.update T (e .A) ((L.drop (j + 1)).map Sym.bit ++ RA) with hT0
      have hFp : T0 (e .Fp) = flagStk ((Pp ++ L.take j).any id) := by
        simp [hT0, hT, Sf, setPM, he.eq_iff]
      have hOp : T0 (e .Op) = tst (Pp ++ L.take j) Dp := by
        simp [hT0, hT, Sf, setPM, he.eq_iff]
      have ev1 := eval_tpushT (he.ne (by decide)) (fun v => bitD v.o false) L[j] (Pp ++ L.take j)
        Dp { u with o := some (Sym.bit L[j]) } T0 hFp hOp rfl
      set T1 := Function.update (Function.update T0 (e .Op) (tst (Pp ++ L.take j ++ [L[j]]) Dp))
        (e .Fp) (flagStk ((Pp ++ L.take j ++ [L[j]]).any id)) with hT1
      have hFm : T1 (e .Fm) = flagStk ((Pm ++ List.replicate j false).any id) := by
        simp [hT1, hT0, hT, Sf, setPM, he.eq_iff]
      have hOm : T1 (e .Om) = tst (Pm ++ List.replicate j false) Dm := by
        simp [hT1, hT0, hT, Sf, setPM, he.eq_iff]
      refine ⟨_, eval_of_stk (Eval.seq e0 (Eval.seq ev1 (eval_tpushT (he.ne (by decide))
        (fun _ => false) false (Pm ++ List.replicate j false) Dm _ T1 hFm hOm rfl))) ?_ rfl⟩
      have ht : Pp ++ L.take j ++ [L[j]] = Pp ++ L.take (j + 1) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
          List.append_assoc]
      have hr : Pm ++ List.replicate j false ++ [false] = Pm ++ List.replicate (j + 1) false := by
        rw [List.replicate_succ', List.append_assoc]
      have hx2 : Sym.mark :: (List.replicate j Sym.mark ++ S (e .X2)) =
          List.replicate (j + 1) Sym.mark ++ S (e .X2) := by simp [List.replicate_succ]
      have hn1 : n - j - 1 = n - (j + 1) := by omega
      simp only [hT1, hT0, hT, ht, hr]
      refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
      · simp [Sf, setPM, Function.update_apply, hk]
      · cases x <;> simp [Sf, setPM, Function.update_apply, he.eq_iff, hx2, hn1]) v
  rw [h0] at e1
  have e2 := moveMarks_eval (he.ne (by decide) : e .X2 ≠ e .Rlo) n (S (e .X2)) v1 (Sf n) hX
    (hSX n le_rfl)
  have hdrop : L.drop n = [] := List.drop_of_length_le (le_of_eq hLn)
  have htake : L.take n = L := List.take_of_length_le (le_of_eq hLn)
  refine ⟨_, eval_of_stk (Eval.seq e1 e2) ?_ ?_⟩
  · refine ext_e (e := e) (fun k hk => ?_) (fun x => ?_)
    · simp [Sf, setPM, Function.update_apply, hk]
    · cases x <;> simp [Sf, setPM, Function.update_apply, he.eq_iff, hR, hdrop, htake, hLn]
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

/-- **The field emitter**, exact: from the field `sgn :: lows.reverse` (most significant bit on
top of `A`), part `p` receives `slotP s w lows` and part `m` receives `slotM s w sgn` (trimmed). -/
theorem emitField_eval (e : EF → K) (he : Function.Injective e) {w s : ℕ} (hw : 1 ≤ w)
    (hws : w ≤ s) (lows : List Bool) (hl : lows.length = w - 1) (sgn : Bool)
    (RA Dlo Dpad : List Sym) (hDlo : Dlo.head? ≠ some .mark) (hDpad : Dpad.head? ≠ some .mark)
    (Pp Pm : List Bool) (Dp Dm : List Sym) (S : K → List Sym)
    (hX2 : (S (e .X2)).head? ≠ some .mark) (hX3 : (S (e .X3)).head? ≠ some .mark)
    (hlo : S (e .Rlo) = List.replicate (w - 1) .mark ++ Dlo)
    (hpad : S (e .Rpad) = List.replicate (s - w) .mark ++ Dpad)
    (hA : S (e .A) = (sgn :: lows.reverse).map Sym.bit ++ RA) (v : AReg) :
    ∃ v', Eval [] (emitField e) ⟨v, setPM e S Pp Pm Dp Dm⟩
      ⟨v', setPM e (Function.update S (e .A) RA) (Pp ++ slotP s w lows) (Pm ++ slotM s w sgn)
        Dp Dm⟩ (18 * (s - w) + 19 * (w - 1) + 19) := by
  obtain ⟨v1, e1⟩ := emitZ_eval e he (s - w) Dpad hDpad Pp Pm Dp Dm S hX3 hpad v
  obtain ⟨v2, e2⟩ := emitS_eval e he sgn (lows.reverse.map Sym.bit ++ RA)
    (Pp ++ List.replicate (s - w) false) (Pm ++ List.replicate (s - w) false) Dp Dm S
    (by rw [hA]; rfl) v1
  obtain ⟨v3, e3⟩ := emitL_eval e he lows RA Dlo hDlo (Pp ++ List.replicate (s - w) false ++ [false])
    (Pm ++ List.replicate (s - w) false ++ [sgn]) Dp Dm
    (Function.update S (e .A) (lows.reverse.map Sym.bit ++ RA))
    (by rw [Function.update_of_ne (he.ne (by decide))]; exact hX2)
    (by rw [Function.update_of_ne (he.ne (by decide)), hlo, hl]) (Function.update_self _ _ _) v2
  have hP : Pp ++ List.replicate (s - w) false ++ [false] ++ lows.reverse = Pp ++ slotP s w lows := by
    simp [slotP]
  have hM : Pm ++ List.replicate (s - w) false ++ [sgn] ++ List.replicate lows.length false =
      Pm ++ slotM s w sgn := by
    simp [slotM, hl]
  refine ⟨v3, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ ?_⟩
  · rw [Function.update_idem, hP, hM]
  · rw [hl]
    omega

end Emit

end SubNLogN.Machine.Bridge.SpreadPackAux
