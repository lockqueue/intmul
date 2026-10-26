/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedDefs
import SubNLogN.Machine.Walsh.PosPermSchedIO
import SubNLogN.Machine.Walsh.PosPermSchedCost
import SubNLogN.Machine.Walsh.PosPermSchedIOStk
import SubNLogN.Machine.Walsh.PosPermSchedCycAll

/-!
# Schedule compiler, assembly (`Machine/Walsh/PosPermSchedMain.lean`): `posPermSched_of_parts`

**Main result.** `SubNLogN.Machine.posPermSched_of_parts`: the runtime schedule compiler contract
`PosPermSchedStmt` (`PosPermLeaf.lean`; Theorem 5.8, `thm:positional-perm`)
from the phase contracts of the compiler on `Stk = KLoc (Fin 3) (RawN ⊕ RegN)`
(`PosPermSchedState.lean`), taken as explicit hypotheses:
* `DecHdrStmt` (header decode, `PosPermSchedIOStk.lean`; proved, `decHdr_holds`):
  registers `d, K, m := una d, una K, una m` from `permHdr P d r w K m` on stack `0` (restored);
* `DecPiStmt` (map decode, `PosPermSchedIOStk.lean`; proved, `decPi_holds`):
  `PT := utab (finVals π) ++ PT` from `permSyms π` on stack `1` (restored);
* `CycPhaseStmt` (cycle phase, `PosPermSchedDefs.lean`; proved, `cycPhase_holds`,
  `PosPermSchedCycAll.lean`): `I0T, I1T := utab (finVals (invol0 π)), utab (finVals (invol1 π))`;
* `StageProgStmt` (stage emission, `PosPermSchedState.lean`): one stage of `stageCmds`, pushed
  reversed onto `ACC`.

With the three proved phases plugged in, `posPermSched_of_emit : StageProgStmt → PosPermSchedStmt`
(the only remaining hypothesis is the stage emitter).

**Program** (`schedProg`): `decHdr ; decPi ; cyc ; stage(I0T,A) ; stage(I0T,B) ; stage(I0T,A) ;
stage(I1T,A) ; stage(I1T,B) ; stage(I1T,A) ; moveAll ACC → stack 2 ; clear PT, I0T, I1T, m, d, K`.

**Invariant.** After the cycle phase the state is `S₃ = S` updated at `d, K, m, PT, I0T, I1T`
(everything else, in particular stacks `0, 1, 2` and all other scratch, as in `S`); stage `j`
changes only `ACC`, which holds the reverse of the schedule text emitted so far
(`schedSyms_append_reverse`), so after six stages `ACC = (schedSyms (posPermSched m d K π)).reverse`
(`posPermSched = involCmds (invol0 π) ++ involCmds (invol1 π)`, `involCmds = A ++ B ++ A`). The
final move reverses it onto stack `2`; the clean-up empties the six scratch stacks, so the final
state is `S` with stack `2` replaced (`KClean S`).

**Cost.** `Tdec + Tpi + Tcyc + 6·Temit + (4|ACC| + 2) + Σ (3|·| + 2)`, each polynomial in
`m + d + K + 1 ≤ 3 (w + m + 1)` plus the header and map lengths.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Main

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO

/-! ## Clearing a stack -/

section Generic

variable {K : Type} [DecidableEq K]

/-- `clearU k` (pop until empty) clears any stack, not only unary registers. -/
theorem runs_clearAll (k : K) (S : K → List Sym) :
    Runs (clearU k) S (Function.update S k []) (fun _ => True) ((S k).length * 3 + 2) := by
  have h := runs_whileNE (k := k) (p := popR k)
    (fun i => Function.update S k ((S k).drop i)) 1 (S k).length
    (fun i hi => by
      simp only [Function.update_self]
      intro h0
      rw [List.drop_eq_nil_iff] at h0
      omega)
    (by simp)
    (fun i hi => by
      have hp := runs_popR k (Function.update S k ((S k).drop i))
      simp only [Function.update_self, Function.update_idem, List.tail_drop] at hp
      exact runs_true hp)
  simp only [List.drop_zero, List.drop_length, Function.update_eq_self] at h
  exact h

end Generic

/-! ## The program -/

/-- The six emission stages: `I0T` with stages A, B, A, then `I1T` with stages A, B, A. -/
def emitAll (sg : RawN → Bool → SProg Stk) : SProg Stk :=
  .seq (sg .I0T true) (.seq (sg .I0T false) (.seq (sg .I0T true)
    (.seq (sg .I1T true) (.seq (sg .I1T false) (sg .I1T true)))))

/-- Clean-up: empty the tables and the three header registers. -/
def cleanProg : SProg Stk :=
  .seq (clearU (rs .PT)) (.seq (clearU (rs .I0T)) (.seq (clearU (rs .I1T))
    (.seq (clearU (rg .m)) (.seq (clearU (rg .d)) (clearU (rg .K))))))

/-- Decoding and the cycle phase. -/
def frontProg (dh dp cy : SProg Stk) : SProg Stk := .seq dh (.seq dp cy)

/-- The final move of the accumulator onto stack `2`, then the clean-up. -/
def finishProg : SProg Stk := .seq (moveAll (rs .ACC) (.inl 2)) cleanProg

/-- **The schedule compiler.** -/
def schedProg (dh dp cy : SProg Stk) (sg : RawN → Bool → SProg Stk) : SProg Stk :=
  .seq (frontProg dh dp cy) (.seq (emitAll sg) finishProg)

theorem closed_clearU {K : Type} (k : K) : (clearU k).Closed := by
  simp [clearU, whileNE, whileTop, popR, peekR, Prog.Closed, Prog.FreeBelow]

theorem closed_cleanProg : cleanProg.Closed :=
  ⟨closed_clearU _, closed_clearU _, closed_clearU _, closed_clearU _, closed_clearU _,
    closed_clearU _⟩

theorem closed_emitAll {sg : RawN → Bool → SProg Stk} (h : ∀ IT stA, (sg IT stA).Closed) :
    (emitAll sg).Closed :=
  ⟨h _ _, h _ _, h _ _, h _ _, h _ _, h _ _⟩

theorem closed_schedProg {dh dp cy : SProg Stk} {sg : RawN → Bool → SProg Stk} (hh : dh.Closed)
    (hp : dp.Closed) (hc : cy.Closed) (hs : ∀ IT stA, (sg IT stA).Closed) :
    (schedProg dh dp cy sg).Closed :=
  ⟨⟨hh, hp, hc⟩, closed_emitAll hs, closed_moveAll _ _, closed_cleanProg⟩

/-! ## Clean scratch -/

theorem scrClean_of_kClean {S : Stk → List Sym} (hS : KClean S) (keep : List RegN) :
    ScrClean S keep :=
  ⟨fun q _ => hS (.inr q), hS (.inl .U), hS (.inl .BT), hS (.inl .B1), hS (.inl .B2),
    hS (.inl .B3), hS (.inl .B4)⟩

theorem scrClean_updRaw {S : Stk → List Sym} {keep : List RegN} (h : ScrClean S keep) (w : RawN)
    (hw : w = .PT ∨ w = .I0T ∨ w = .I1T ∨ w = .ACC) (v : List Sym) :
    ScrClean (Function.update S (rs w) v) keep := by
  obtain ⟨hr, hU, hBT, hB1, hB2, hB3, hB4⟩ := h
  refine ⟨fun q hq => by rw [Function.update_of_ne (by simp)]; exact hr q hq, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    rw [Function.update_of_ne (by rcases hw with rfl | rfl | rfl | rfl <;> decide)] <;> assumption

theorem scrClean_updReg {S : Stk → List Sym} {keep : List RegN} (h : ScrClean S keep) (q : RegN)
    (hq : q ∈ keep) (v : List Sym) : ScrClean (Function.update S (rg q) v) keep := by
  obtain ⟨hr, hU, hBT, hB1, hB2, hB3, hB4⟩ := h
  refine ⟨fun q' hq' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hne : q' ≠ q := fun he => hq' (he ▸ hq)
    rw [Function.update_of_ne (by simpa using hne)]
    exact hr q' hq'
  all_goals rw [Function.update_of_ne (by simp)]; assumption

/-! ## The state after the cycle phase -/

/-- The state after decoding and the cycle phase: `S` with `d, K, m, PT, I0T, I1T` set. -/
def st3 (S : Stk → List Sym) (m d K : ℕ) (π : Fin m → Fin m) : Stk → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S (rg .d) (una d)) (rg .K) (una K)) (rg .m) (una m)) (rs .PT)
    (utab (finVals π))) (rs .I0T) (utab (finVals (invol0 π)))) (rs .I1T)
    (utab (finVals (invol1 π)))

section St3

variable (S : Stk → List Sym) (m d K : ℕ) (π : Fin m → Fin m)

theorem st3_I0T : st3 S m d K π (rs .I0T) = utab (finVals (invol0 π)) := by
  simp [st3]

theorem st3_I1T : st3 S m d K π (rs .I1T) = utab (finVals (invol1 π)) := by
  simp [st3]

theorem st3_PT : st3 S m d K π (rs .PT) = utab (finVals π) := by
  simp [st3]

theorem st3_m : st3 S m d K π (rg .m) = una m := by simp [st3]

theorem st3_d : st3 S m d K π (rg .d) = una d := by simp [st3]

theorem st3_K : st3 S m d K π (rg .K) = una K := by simp [st3]

theorem st3_rg (q : RegN) (h1 : q ≠ .m) (h2 : q ≠ .d) (h3 : q ≠ .K) :
    st3 S m d K π (rg q) = S (rg q) := by
  simp [st3, h1, h2, h3]

theorem st3_rs (w : RawN) (h1 : w ≠ .PT) (h2 : w ≠ .I0T) (h3 : w ≠ .I1T) :
    st3 S m d K π (rs w) = S (rs w) := by
  simp [st3, h1, h2, h3]

theorem st3_inl (i : Fin 3) : st3 S m d K π (.inl i) = S (.inl i) := by
  simp [st3]

end St3

/-! ## Decoding and the cycle phase -/

/-- **Front phases** (`decHdr ; decPi ; cyc`): from a clean state with the header on stack `0`
and the map on stack `1`, reach `st3`. -/
theorem runs_front {dh dp cy : SProg Stk} {Ch kh Cp kp Cc kc : ℕ}
    (sH : ∀ (Ph d r w K m : ℕ) (hrest : List Sym) (S : Stk → List Sym), KClean S →
      S (.inl 0) = permHdr Ph d r w K m ++ hrest →
      Runs dh S
        (Function.update (Function.update (Function.update S (rg .d) (una d)) (rg .K) (una K))
          (rg .m) (una m))
        (fun _ => True) (Ch * ((m + d + K + 1) ^ kh + (permHdr Ph d r w K m).length)))
    (sP : ∀ (m : ℕ) (π : Fin m → Fin m) (prest : List Sym) (S : Stk → List Sym),
      S (.inl 1) = permSyms π ++ prest → S (rg .m) = una m → ScrClean S [.m, .d, .K] →
      Runs dp S (Function.update S (rs .PT) (utab (finVals π) ++ S (rs .PT)))
        (fun _ => True) (Cp * ((m + 1) ^ kp + (permSyms π).length)))
    (sC : ∀ (m : ℕ) (π : Fin m → Fin m) (S : Stk → List Sym),
      S (rs .PT) = utab (finVals π) → S (rg .m) = una m → S (rs .I0T) = [] →
      S (rs .I1T) = [] → ScrClean S [.m, .d, .K] →
      Runs cy S
        (Function.update (Function.update S (rs .I0T) (utab (finVals (invol0 π)))) (rs .I1T)
          (utab (finVals (invol1 π))))
        (fun _ => True) (Cc * (m + 1) ^ kc))
    (Ph d r w K m : ℕ) (π : Fin m → Fin m) (hrest prest : List Sym) (S : Stk → List Sym)
    (hS : KClean S) (h0 : S (.inl 0) = permHdr Ph d r w K m ++ hrest)
    (h1 : S (.inl 1) = permSyms π ++ prest) :
    Runs (frontProg dh dp cy) S (st3 S m d K π) (fun _ => True)
      (Ch * ((m + d + K + 1) ^ kh + (permHdr Ph d r w K m).length) +
        (Cp * ((m + 1) ^ kp + (permSyms π).length) + Cc * (m + 1) ^ kc)) := by
  have r1 := sH Ph d r w K m hrest S hS h0
  have hc1 : ScrClean (Function.update (Function.update (Function.update S (rg .d) (una d))
      (rg .K) (una K)) (rg .m) (una m)) [.m, .d, .K] :=
    scrClean_updReg (scrClean_updReg (scrClean_updReg (scrClean_of_kClean hS _) .d (by simp) _)
      .K (by simp) _) .m (by simp) _
  have r2 := sP m π prest _ (by simp [h1]) (by simp) hc1
  have hPT : Function.update (Function.update (Function.update S (rg .d) (una d)) (rg .K)
      (una K)) (rg .m) (una m) (rs .PT) = [] := by
    simp [hS (.inl .PT)]
  rw [hPT, List.append_nil] at r2
  have hc2 := scrClean_updRaw hc1 .PT (Or.inl rfl) (utab (finVals π))
  have r3 := sC m π _ (by simp) (by simp)
    (by simp [hS (.inl .I0T)])
    (by simp [hS (.inl .I1T)]) hc2
  exact runs_seq' r1 (runs_seq' r2 r3 le_rfl) le_rfl

/-! ## The six emission stages -/

/-- The unpacked `StageEmitSpec` hypothesis. -/
def StageHyp (sg : RawN → Bool → SProg Stk) (Ce ke : ℕ) : Prop :=
  ∀ (IT : RawN) (_ : IT = .I0T ∨ IT = .I1T) (stA : Bool) (m d K : ℕ)
    (I : Fin m → Fin m) (S : Stk → List Sym) (A : List Sym), 1 ≤ d → 1 ≤ K →
    S (rs IT) = utab (finVals I) → S (rg .m) = una m → S (rg .d) = una d → S (rg .K) = una K →
    S (rs .ACC) = A → (∀ q, q ≠ .m → q ≠ .d → q ≠ .K → S (rg q) = []) →
    S (rs .BT) = [] → S (rs .U) = [] → S (rs .B1) = [] → S (rs .B2) = [] →
    S (rs .B3) = [] → S (rs .B4) = [] →
    Runs (sg IT stA) S
      (Function.update S (rs .ACC)
        ((schedSyms (stageCmds m d K (if stA then stageA I else stageB I))).reverse ++ A))
      (fun _ => True) (Ce * (m + d + K + 1) ^ ke)

/-- One emission stage from `st3` with accumulator `A`. -/
theorem runs_stage1 {sg : RawN → Bool → SProg Stk} {Ce ke : ℕ} (sE : StageHyp sg Ce ke)
    {m d K : ℕ} (π : Fin m → Fin m) (S : Stk → List Sym) (hS : KClean S) (hd : 1 ≤ d)
    (hK : 1 ≤ K) (IT : RawN) (hIT : IT = .I0T ∨ IT = .I1T) (stA : Bool) (I : Fin m → Fin m)
    (hI : st3 S m d K π (rs IT) = utab (finVals I)) (A : List Sym) :
    Runs (sg IT stA) (Function.update (st3 S m d K π) (rs .ACC) A)
      (Function.update (st3 S m d K π) (rs .ACC)
        ((schedSyms (stageCmds m d K (if stA then stageA I else stageB I))).reverse ++ A))
      (fun _ => True) (Ce * (m + d + K + 1) ^ ke) := by
  have hne : (rs IT : Stk) ≠ rs .ACC := by rcases hIT with rfl | rfl <;> decide
  have h := sE IT hIT stA m d K I (Function.update (st3 S m d K π) (rs .ACC) A) A hd hK
    (by rw [Function.update_of_ne hne]; exact hI)
    (by rw [Function.update_of_ne (by decide), st3_m])
    (by rw [Function.update_of_ne (by decide), st3_d])
    (by rw [Function.update_of_ne (by decide), st3_K])
    (Function.update_self _ _ _)
    (fun q h1 h2 h3 => by
      rw [Function.update_of_ne (by simp), st3_rg S m d K π q h1 h2 h3]
      exact hS (.inr q))
    (by rw [Function.update_of_ne (by decide), st3_rs S m d K π _ (by decide) (by decide)
      (by decide)]; exact hS (.inl _))
    (by rw [Function.update_of_ne (by decide), st3_rs S m d K π _ (by decide) (by decide)
      (by decide)]; exact hS (.inl _))
    (by rw [Function.update_of_ne (by decide), st3_rs S m d K π _ (by decide) (by decide)
      (by decide)]; exact hS (.inl _))
    (by rw [Function.update_of_ne (by decide), st3_rs S m d K π _ (by decide) (by decide)
      (by decide)]; exact hS (.inl _))
    (by rw [Function.update_of_ne (by decide), st3_rs S m d K π _ (by decide) (by decide)
      (by decide)]; exact hS (.inl _))
    (by rw [Function.update_of_ne (by decide), st3_rs S m d K π _ (by decide) (by decide)
      (by decide)]; exact hS (.inl _))
  rwa [Function.update_idem] at h

/-- The accumulator after the six stages is the reversed schedule text. -/
theorem acc_six {m : ℕ} (d K : ℕ) (π : Fin m → Fin m) :
    (schedSyms (stageCmds m d K (if true then stageA (invol1 π) else stageB (invol1 π)))).reverse ++
      ((schedSyms (stageCmds m d K (if false then stageA (invol1 π) else stageB (invol1 π)))).reverse ++
      ((schedSyms (stageCmds m d K (if true then stageA (invol1 π) else stageB (invol1 π)))).reverse ++
      ((schedSyms (stageCmds m d K (if true then stageA (invol0 π) else stageB (invol0 π)))).reverse ++
      ((schedSyms (stageCmds m d K (if false then stageA (invol0 π) else stageB (invol0 π)))).reverse ++
      ((schedSyms (stageCmds m d K (if true then stageA (invol0 π) else stageB (invol0 π)))).reverse ++
        []))))) = (schedSyms (posPermSched m d K π)).reverse := by
  simp [posPermSched, involCmds, schedSyms_append, List.reverse_append, List.append_assoc]

/-- **The six emission stages**: from `st3` (empty accumulator) to `st3` with the reversed
schedule text on `ACC`. -/
theorem runs_emitAll {sg : RawN → Bool → SProg Stk} {Ce ke : ℕ} (sE : StageHyp sg Ce ke)
    {m d K : ℕ} (π : Fin m → Fin m) (S : Stk → List Sym) (hS : KClean S) (hd : 1 ≤ d)
    (hK : 1 ≤ K) :
    Runs (emitAll sg) (st3 S m d K π)
      (Function.update (st3 S m d K π) (rs .ACC) (schedSyms (posPermSched m d K π)).reverse)
      (fun _ => True) (6 * (Ce * (m + d + K + 1) ^ ke)) := by
  have e0 : Function.update (st3 S m d K π) (rs .ACC) [] = st3 S m d K π := by
    rw [Function.update_eq_self_iff, st3_rs S m d K π _ (by decide) (by decide) (by decide)]
    exact (hS (.inl _)).symm
  have r1 := runs_stage1 sE π S hS hd hK .I0T (Or.inl rfl) true (invol0 π) (st3_I0T S m d K π) []
  rw [e0] at r1
  refine runs_weak (runs_seq' r1 (runs_seq'
    (runs_stage1 sE π S hS hd hK .I0T (Or.inl rfl) false (invol0 π) (st3_I0T S m d K π) _)
    (runs_seq' (runs_stage1 sE π S hS hd hK .I0T (Or.inl rfl) true (invol0 π)
      (st3_I0T S m d K π) _)
    (runs_seq' (runs_stage1 sE π S hS hd hK .I1T (Or.inr rfl) true (invol1 π)
      (st3_I1T S m d K π) _)
    (runs_seq' (runs_stage1 sE π S hS hd hK .I1T (Or.inr rfl) false (invol1 π)
      (st3_I1T S m d K π) _)
      (runs_stage1 sE π S hS hd hK .I1T (Or.inr rfl) true (invol1 π) (st3_I1T S m d K π) _)
      le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) ?_ (by omega)
  rw [acc_six]

/-! ## The final move and the clean-up -/

/-- `clearU k` on a stack with known content `v`. -/
theorem runs_clearAll' {K : Type} [DecidableEq K] (k : K) (S : K → List Sym) {v : List Sym}
    (hv : S k = v) :
    Runs (clearU k) S (Function.update S k []) (fun _ => True) (v.length * 3 + 2) := by
  have h := runs_clearAll k S
  rwa [hv] at h

/-- The state after the clean-up is `S` with stack `2` replaced. -/
theorem final_eq (S : Stk → List Sym) (hS : KClean S) {m : ℕ} (d K : ℕ) (π : Fin m → Fin m)
    (X Y : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (st3 S m d K π)
        (rs .ACC) Y) (rs .ACC) []) (.inl 2) X) (rs .PT) []) (rs .I0T) []) (rs .I1T) [])
      (rg .m) []) (rg .d) []) (rg .K) [] = Function.update S (.inl 2) X := by
  have hR : ∀ w, S (rs w) = [] := fun w => hS (.inl w)
  have hG : ∀ q, S (rg q) = [] := fun q => hS (.inr q)
  funext k
  simp only [st3, Function.update_apply]
  split_ifs <;> (try subst_vars) <;> simp_all

/-- **Final move and clean-up**: `ACC` (the reversed schedule text) is moved onto stack `2`, then
`PT, I0T, I1T, m, d, K` are emptied. -/
theorem runs_finish {m : ℕ} (d K : ℕ) (π : Fin m → Fin m) (S : Stk → List Sym) (hS : KClean S) :
    Runs finishProg
      (Function.update (st3 S m d K π) (rs .ACC) (schedSyms (posPermSched m d K π)).reverse)
      (Function.update S (.inl 2) (schedSyms (posPermSched m d K π) ++ S (.inl 2)))
      (fun _ => True)
      ((schedSyms (posPermSched m d K π)).length * 4 + 2 +
        ((utab (finVals π)).length * 3 + 2 + ((utab (finVals (invol0 π))).length * 3 + 2 +
          ((utab (finVals (invol1 π))).length * 3 + 2 + (m * 3 + 2 + (d * 3 + 2 +
            (K * 3 + 2))))))) := by
  have r0 := runs_moveAll (src := (rs .ACC : Stk)) (dst := .inl 2) (by decide)
    (Function.update (st3 S m d K π) (rs .ACC) (schedSyms (posPermSched m d K π)).reverse)
  have hA : Function.update (st3 S m d K π) (rs .ACC) (schedSyms (posPermSched m d K π)).reverse
      (rs .ACC) = (schedSyms (posPermSched m d K π)).reverse := Function.update_self _ _ _
  have h2 : Function.update (st3 S m d K π) (rs .ACC) (schedSyms (posPermSched m d K π)).reverse
      (.inl 2) = S (.inl 2) := by
    rw [Function.update_of_ne (by decide), st3_inl]
  rw [hA, h2, List.reverse_reverse, List.length_reverse] at r0
  set F1 := Function.update (Function.update (Function.update (st3 S m d K π) (rs .ACC)
    (schedSyms (posPermSched m d K π)).reverse) (rs .ACC) []) (.inl 2)
    (schedSyms (posPermSched m d K π) ++ S (.inl 2)) with hF1
  have c1 := runs_clearAll' (rs .PT) F1 (v := utab (finVals π))
    (by simp [hF1, st3])
  have c2 := runs_clearAll' (rs .I0T) (Function.update F1 (rs .PT) [])
    (v := utab (finVals (invol0 π))) (by simp [hF1, st3])
  have c3 := runs_clearAll' (rs .I1T) (Function.update (Function.update F1 (rs .PT) [])
    (rs .I0T) []) (v := utab (finVals (invol1 π))) (by simp [hF1, st3])
  have c4 := runs_clearAll' (rg .m) (Function.update (Function.update (Function.update F1
    (rs .PT) []) (rs .I0T) []) (rs .I1T) []) (v := una m)
    (by simp [hF1, st3])
  have c5 := runs_clearAll' (rg .d) (Function.update (Function.update (Function.update
    (Function.update F1 (rs .PT) []) (rs .I0T) []) (rs .I1T) []) (rg .m) []) (v := una d)
    (by simp [hF1, st3])
  have c6 := runs_clearAll' (rg .K) (Function.update (Function.update (Function.update
    (Function.update (Function.update F1 (rs .PT) []) (rs .I0T) []) (rs .I1T) []) (rg .m) [])
    (rg .d) []) (v := una K) (by simp [hF1, st3])
  rw [length_una] at c4 c5 c6
  exact runs_weak (runs_seq' r0 (runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4
    (runs_seq' c5 c6 le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
    (final_eq S hS d K π _ _) le_rfl

end SubNLogN.Machine.Walsh.PosPermSchedAux.Main

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux SubNLogN.Machine.Walsh.PosPermSchedAux.Main
  SubNLogN.Machine.Walsh.PosPermSchedAux.Cost

/-- **The runtime schedule compiler from its phases (`posPermSched_of_parts`, 0 `sorry`).**
`PosPermSchedStmt` (Theorem 5.8's schedule, `thm:positional-perm`; `PosPermLeaf.lean`) holds, given the four
phase contracts on the compiler's stacks `Stk`: the header decode `DecHdrStmt` and the map decode
`DecPiStmt`, the cycle phase `CycPhaseStmt`, and the stage emitter
`StageProgStmt`. Program `schedProg`; the cost exponent and constant are `bandJ`,
`bandC` of the phases' exponents and constants (`PosPermSchedCost.lean`). -/
theorem posPermSched_of_parts (hH : DecHdrStmt) (hP : DecPiStmt) (hC : CycPhaseStmt)
    (hE : StageProgStmt) : PosPermSchedStmt := by
  obtain ⟨dh, hdh, Ch, kh, sH⟩ := hH
  obtain ⟨dp, hdp, Cp, kp, sP⟩ := hP
  obtain ⟨cy, hcy, Cc, kc, sC⟩ := hC
  obtain ⟨sg, hsg, Ce, ke, sE⟩ := hE
  refine ⟨bandJ kh kp kc ke, bandC Ch kh Cp Cc Ce ke 12, fun _ => ⟨Scr, inferInstance,
    inferInstance, Option Sym, schedProg dh dp cy sg, inferInstance, ⟨none⟩,
    closed_schedProg hdh hdp hcy hsg, ?_⟩⟩
  intro P d r w K m π hrest prest S hS hd hK hdw hKw h0 h1
  have rf := runs_front sH sP sC P d r w K m (⇑π) hrest prest S hS h0 h1
  have re := runs_emitAll sE (⇑π) S hS hd hK
  have rn := runs_finish d K (⇑π) S hS
  refine runs_weak (runs_seq' rf (runs_seq' re rn le_rfl) le_rfl) rfl ?_
  have hb := sched_cost_le (P := P) (r := r) π hd hK hdw hKw (Ch := Ch) (kh := kh) (Cp := Cp)
    (kp := kp) (Cc := Cc) (kc := kc) (Ce := Ce) (ke := ke) (Ccl := 12) le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
  exact le_trans (by omega) hb

/-- **The schedule compiler from the cycle phase and the stage emitter
(`posPermSched_of_cyc_emit`, 0 `sorry`)**: `posPermSched_of_parts` with the proved decoders
`decHdr_holds`, `decPi_holds` (`PosPermSchedIOStk.lean`). Remaining hypotheses:
`CycPhaseStmt` and `StageProgStmt`. -/
theorem posPermSched_of_cyc_emit (hC : CycPhaseStmt) (hE : StageProgStmt) : PosPermSchedStmt :=
  posPermSched_of_parts decHdr_holds decPi_holds hC hE

/-- **The schedule compiler from the stage emitter (`posPermSched_of_emit`, 0 `sorry`)**:
`posPermSched_of_cyc_emit` with the proved cycle phase `cycPhase_holds`
(`PosPermSchedCycAll.lean`). The only remaining hypothesis is `StageProgStmt`. -/
theorem posPermSched_of_emit (hE : StageProgStmt) : PosPermSchedStmt :=
  posPermSched_of_cyc_emit cycPhase_holds hE

end SubNLogN.Machine
