/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermMath
import SubNLogN.Machine.Walsh.PosPermGlue
import SubNLogN.Machine.Walsh.CnotBatch

/-!
# K3-PERM: positional-permutation machine (Theorem 5.8, `thm:positional-perm`), from its parts

**Scope (honest summary).** A sequencing reduction, fully proved: `positionalPermMachine_of`
proves `PositionalPermMachineStmt Band lam'` (`Contracts/Walsh.lean`) from the slice-batched
controlled flips (`CnotBatchMachineStmt Band lam'`), the single controlled flip
(`Cnot1MachineStmt`) and the runtime schedule compiler (`PosPermSchedStmt`). The composite is ONE
fixed program `ppProg` (`Par := Unit`): it compiles the schedule onto a private stack and then
interprets it in a `Prog.loop` (Theorem 5.8 (`thm:positional-perm`): a uniform descriptor interpreter,
not a program built from `π`). Constants: `J = J_B + J_1 + J_S + 2`, `C = ppConst C_S C_B C_1`.

**Leaf contracts** (explicit hypotheses, not proved here):
* `PosPermSchedStmt` (`Machine/Walsh/PosPermLeaf.lean`), K3.5a, the schedule compiler: on
  `(permHdr, permSyms π, sch)` it pushes `schedSyms (posPermSched m d K π)` (the exact command list;
  `sched_erase` in `PosPermMath.lean` shows its erasure is the algebraic `posPermProg`), restoring the
  inputs, at cost `C·((w+m+1)^J + |permHdr| + |permSyms π|)`.
* `CnotBatchMachineStmt`, `Cnot1MachineStmt` (`Contracts/Walsh.lean`); see `PosPermFull.lean` for
  the corollaries with the proved parts plugged in.

## The interpreter
Private stacks `sch` (the schedule), `h` (a slice header), `p` (a pair list), `t` (copy buffer).
`main = sched; peek sch; while (top of sch is a tag) body`, where `body` pops the tag and either
* (batch, `tag 0`) moves `hdrSyms [j₀, D, nS, ρ]` to `h`, copies the six fields of `permHdr` on top
  of it (so `h = sliceHdr P d r w K m j₀ D nS ρ`), moves the pairs to `p`, calls
  `CnotBatchMachineStmt` on (array, `h`, `p`), drains `h` and `p`; or
* (single flip, `tag 1`) moves the pair to `p`, calls `Cnot1MachineStmt` on (array, `permHdr`, `p`),
  drains `p`;
and then peeks the next tag. Values: `foldl_sched` (the algebraic `positional_perm`); cost: at most
`6(N_slice + K)` commands, each `O(V_* d^{λ'} + 2^m (w+m+1)^J + |permHdr|)`.
-/

namespace SubNLogN.Machine.PosPermRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Math.Common
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Layout -/

section Layout

variable {X : Type}

/-- The composite's stacks: named array / header / map, then `sch, h, p, t`, then the parts. -/
abbrev PPLoc (X : Type) : Type := KLoc (Fin 3) (Fin 4 ⊕ X)

/-- The schedule stack. -/
abbrev kSch : PPLoc X := .inr (.inl 0)
/-- The slice-header stack. -/
abbrev kH : PPLoc X := .inr (.inl 1)
/-- The pair-list stack. -/
abbrev kP : PPLoc X := .inr (.inl 2)
/-- The copy buffer. -/
abbrev kT : PPLoc X := .inr (.inl 3)

/-- Composite state: the initial stacks `S` with the array, `sch`, `h`, `p` replaced. -/
def pst [DecidableEq X] (S : PPLoc X → List Sym) (a sc h p : List Sym) : PPLoc X → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (.inl 0) a) kSch sc) kH h)
    kP p

/-- Embedding of a part (named stacks placed by `f`, private scratch by `j`). -/
def pemb {N Y : Type} (f : N → PPLoc X) (j : Y → X) : KLoc N Y → PPLoc X
  | .inl i => f i
  | .inr e => .inr (.inr (j e))

theorem pemb_injective {N Y : Type} {f : N → PPLoc X} {j : Y → X} (hf : Function.Injective f)
    (hj : Function.Injective j) (hfj : ∀ i x, f i ≠ .inr (.inr x)) :
    Function.Injective (pemb f j) := by
  rintro (i | e) (i' | e') h
  · exact congrArg Sum.inl (hf h)
  · exact absurd h (hfj i (j e'))
  · exact absurd h.symm (hfj i' (j e))
  · simp only [pemb, Sum.inr.injEq] at h
    rw [hj h]

@[simp] theorem pemb_inl {N Y : Type} (f : N → PPLoc X) (j : Y → X) (i : N) :
    pemb f j (.inl i) = f i := rfl

variable [DecidableEq X] (S : PPLoc X → List Sym) (a sc h p : List Sym)

@[simp] theorem pst_arr : pst S a sc h p (.inl 0) = a := by simp [pst]
@[simp] theorem pst_hdr : pst S a sc h p (.inl 1) = S (.inl 1) := by simp [pst]
@[simp] theorem pst_map : pst S a sc h p (.inl 2) = S (.inl 2) := by simp [pst]
@[simp] theorem pst_sch : pst S a sc h p kSch = sc := by simp [pst]
@[simp] theorem pst_h : pst S a sc h p kH = h := by simp [pst]
@[simp] theorem pst_p : pst S a sc h p kP = p := by simp [pst]
@[simp] theorem pst_t : pst S a sc h p kT = S kT := by simp [pst]
@[simp] theorem pst_inr (x : X) : pst S a sc h p (.inr (.inr x)) = S (.inr (.inr x)) := by
  simp [pst]

theorem pst_upd_arr (a' : List Sym) :
    Function.update (pst S a sc h p) (.inl 0) a' = pst S a' sc h p := by
  funext k; simp only [pst, Function.update_apply]; split_ifs <;> simp_all

theorem pst_upd_sch (sc' : List Sym) :
    Function.update (pst S a sc h p) kSch sc' = pst S a sc' h p := by
  funext k; simp only [pst, Function.update_apply]; split_ifs <;> simp_all

theorem pst_upd_h (h' : List Sym) :
    Function.update (pst S a sc h p) kH h' = pst S a sc h' p := by
  funext k; simp only [pst, Function.update_apply]; split_ifs <;> simp_all

theorem pst_upd_p (p' : List Sym) :
    Function.update (pst S a sc h p) kP p' = pst S a sc h p' := by
  funext k; simp only [pst, Function.update_apply]; split_ifs <;> simp_all

theorem pst_init (h1 : S kSch = []) (h2 : S kH = []) (h3 : S kP = []) :
    pst S (S (.inl 0)) [] [] [] = S := by
  funext k; simp only [pst, Function.update_apply]; split_ifs <;> simp_all

theorem pst_final (h1 : S kSch = []) (h2 : S kH = []) (h3 : S kP = []) :
    pst S a [] [] [] = Function.update S (.inl 0) a := by
  funext k; simp only [pst, Function.update_apply]; split_ifs <;> simp_all

theorem kclean_pemb (hS : KClean S) {N Y : Type} (f : N → PPLoc X) (j : Y → X) :
    KClean (pst S a sc h p ∘ pemb f j) := fun e => by
  simp only [Function.comp_apply, pemb, pst_inr]
  exact hS (.inr (j e))

end Layout

/-! ## Calls along an embedding, keeping the part's register property -/

theorem runs_callInjQ {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (callInj ι l P) B B' (fun v => Q (l.get v)) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := hP ⟨l.get v, stk ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact (h1 x).trans (congrFun hs' x)
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  refine ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, ?_⟩, ht⟩
  show Q (l.get (l.set v s'.var))
  rw [l.get_set]
  exact hq

/-- A glue program on the composite's own stacks, its register property kept. -/
theorem runs_glue {K σ : Type} [DecidableEq K] (l : Lens σ (Option Sym)) {P : SProg K}
    {B B' : K → List Sym} {Q : Option Sym → Prop} {T : ℕ} (hP : Runs P B B' Q T) :
    Runs (callInj id l P) B B' (fun v => Q (l.get v)) T :=
  runs_callInjQ Function.injective_id l hP (fun k hk => absurd rfl (hk k))

/-! ## Glue steps on the composite -/

section GlueSteps

variable {X : Type} [DecidableEq X] (S : PPLoc X → List Sym)

theorem hdrSyms_append' (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

theorem sep2_not_mem_hdrSyms (fs : List ℕ) : Sym.sep2 ∉ hdrSyms fs := by
  simp [hdrSyms, natSyms]

theorem sep2_not_mem_rev_hdrSyms (fs : List ℕ) : Sym.sep2 ∉ (hdrSyms fs).reverse := by
  rw [List.mem_reverse]; exact sep2_not_mem_hdrSyms fs

/-- Pop the tag of the next command. -/
theorem runs_popTag (a h p : List Sym) (tg : Sym) (rest : List Sym) :
    Runs (popR (kSch : PPLoc X)) (pst S a (tg :: rest) h p) (pst S a rest h p)
      (fun r => r = some tg) 1 := by
  apply Runs.of_eval
  intro v
  refine ⟨some tg, 1, (Eval.pop (Γ := fun _ => Sym) [] kSch (fun _ o => o) v _).of_eq ?_ rfl, rfl,
    le_rfl⟩
  simp only [pst_sch, List.head?_cons, List.tail_cons, pst_upd_sch]

/-- Peek the schedule. -/
theorem runs_peekSch (B : PPLoc X → List Sym) :
    Runs (peekR (kSch : PPLoc X)) B B (fun r => r = (B kSch).head?) 1 := by
  apply Runs.of_eval
  intro v
  exact ⟨_, 1, Eval.peek (Γ := fun _ => Sym) [] kSch (fun _ o => o) v B, rfl, le_rfl⟩

/-- Move a block of the schedule to `h`. -/
theorem runs_moveH (a h p blk rest : List Sym) (hb : Sym.sep2 ∉ blk) :
    Runs (moveUntil .sep2 (kSch : PPLoc X) kH) (pst S a (blk ++ .sep2 :: rest) h p)
      (pst S a rest (blk.reverse ++ h) p) (fun r => r = some .sep2) (3 * blk.length + 2) := by
  apply Runs.of_eval
  intro v
  refine ⟨some .sep2, _, (moveUntil_eval (by simp) .sep2 [] v blk rest _ hb (by simp)).of_eq ?_
    rfl, rfl, le_rfl⟩
  rw [pst_upd_sch, pst_h, pst_upd_h]

/-- Move a block of the schedule to `p`. -/
theorem runs_moveP (a h p blk rest : List Sym) (hb : Sym.sep2 ∉ blk) :
    Runs (moveUntil .sep2 (kSch : PPLoc X) kP) (pst S a (blk ++ .sep2 :: rest) h p)
      (pst S a rest h (blk.reverse ++ p)) (fun r => r = some .sep2) (3 * blk.length + 2) := by
  apply Runs.of_eval
  intro v
  refine ⟨some .sep2, _, (moveUntil_eval (by simp) .sep2 [] v blk rest _ hb (by simp)).of_eq ?_
    rfl, rfl, le_rfl⟩
  rw [pst_upd_sch, pst_p, pst_upd_p]

/-- Copy the six fields of `permHdr` (stack `1`) on top of `h`. -/
theorem runs_copyHdr (a sc h p : List Sym) (fs : List ℕ) (hfs : fs.length = 6) (rest : List Sym)
    (h1 : S (.inl 1) = hdrSyms fs ++ rest) (hT : S kT = []) :
    Runs (copyHdr 6 (.inl 1 : PPLoc X) kH kT) (pst S a sc h p) (pst S a sc (hdrSyms fs ++ h) p)
      (fun _ => True) (fieldsCost fs + (4 * (hdrSyms fs).length + 2)) := by
  apply Runs.of_eval
  intro v
  obtain ⟨v', e⟩ := copyHdr_eval (K := PPLoc X) (src := .inl 1) (dst := kH) (tmp := kT)
    (by simp) (by simp) (by simp) [] v fs rest (pst S a sc h p) (by simp [h1]) (by simp [hT])
  rw [hfs] at e
  exact ⟨v', _, e.of_eq (by rw [pst_h, pst_upd_h]) rfl, trivial, le_rfl⟩

end GlueSteps

/-- A drain step on any stack. -/
theorem runs_drainK {K σ : Type} [DecidableEq K] (l : Lens σ Bool) (k : K) (B : K → List Sym) :
    Runs (callInj id l (CnotBatchRed.drainProg k)) B (Function.update B k []) (fun _ => True)
      (2 * (B k).length + 3) :=
  CnotBatchRed.runs_callInj_update Function.injective_id l
    (by simpa using CnotBatchRed.runs_drainProg k B)

/-! ## The parts' specifications (bodies of the contracts) -/

section Specs

/-- Body of `PosPermSchedStmt`. -/
def SchedSpec (J : ℕ) (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (P d r w K m : ℕ) (π : Equiv.Perm (Fin m)) (hrest prest : List Sym)
      (S : KLoc (Fin 3) E → List Sym),
      KClean S → 1 ≤ d → 1 ≤ K → d ≤ w + m → K ≤ w + m →
      S (.inl 0) = permHdr P d r w K m ++ hrest →
      S (.inl 1) = permSyms π ++ prest →
      Runs Pr S (Function.update S (.inl 2) (schedSyms (posPermSched m d K π) ++ S (.inl 2)))
        (fun _ => True)
        (C * ((w + m + 1) ^ J + (permHdr P d r w K m).length + (permSyms π).length))

/-- Body of `CnotBatchMachineStmt`. -/
def BatchSpec (Band : LayerRT → Prop) (lam' : ℝ) (J : ℕ) (E : Type) [DecidableEq E] (R : Type)
    (C : ℕ) (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m)) (z : RArr (Cube m) r)
      (rest hrest prest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → j₀ + D * K + nS = m → 1 ≤ D → D ≤ d → ρ < K → P + 2 ≤ w → d ≤ w + m →
      K ≤ w + m → CnotPairsValid pairs → targets pairs ⊆ slicePos m K j₀ D ρ →
      Band (sliceRT P d r w K j₀ D nS ρ) → ArrOnDiskGrid P z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube P z) ++ rest →
      S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      S (.inl 2) = pairsSyms pairs ++ prest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms w (encCube P (cnotArr pairs z)) ++ rest))
        (fun _ => True)
        (C * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + cvolCube m r (w + 8 * d) +
          2 ^ m * (w + m + 1) ^ J + (sliceHdr P d r w K m j₀ D nS ρ).length))

/-- Body of `Cnot1MachineStmt`. -/
def OneSpec (J : ℕ) (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (P d r w K m : ℕ) (c t : Fin m) (z : RArr (Cube m) r) (rest hrest prest : List Sym)
      (S : KLoc (Fin 3) E → List Sym),
      KClean S → c ≠ t → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube P z) ++ rest →
      S (.inl 1) = permHdr P d r w K m ++ hrest →
      S (.inl 2) = pairsSyms [(c, t)] ++ prest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms w (encCube P (cnotArr [(c, t)] z)) ++ rest))
        (fun _ => True) (C * (cvolCube m r w + (w + m + 1) ^ J + (permHdr P d r w K m).length))

end Specs

/-! ## Placements and the three part calls -/

section Calls

variable {X : Type}

/-- The schedule compiler: header (stack `1`), map (stack `2`), output `sch`. -/
def fSc : Fin 3 → PPLoc X := ![.inl 1, .inl 2, kSch]
/-- A batch: array, `h`, `p`. -/
def fBa : Fin 3 → PPLoc X := ![.inl 0, kH, kP]
/-- A single flip: array, header (stack `1`), `p`. -/
def fOn : Fin 3 → PPLoc X := ![.inl 0, .inl 1, kP]

theorem fSc_inj : Function.Injective (fSc (X := X)) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fSc]
theorem fBa_inj : Function.Injective (fBa (X := X)) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fBa]
theorem fOn_inj : Function.Injective (fOn (X := X)) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fOn]
theorem fSc_ne (i : Fin 3) (x : X) : fSc i ≠ .inr (.inr x) := by fin_cases i <;> simp [fSc]
theorem fBa_ne (i : Fin 3) (x : X) : fBa i ≠ .inr (.inr x) := by fin_cases i <;> simp [fBa]
theorem fOn_ne (i : Fin 3) (x : X) : fOn i ≠ .inr (.inr x) := by fin_cases i <;> simp [fOn]

@[simp] theorem fSc_0 : fSc (X := X) 0 = .inl 1 := rfl
@[simp] theorem fSc_1 : fSc (X := X) 1 = .inl 2 := rfl
@[simp] theorem fSc_2 : fSc (X := X) 2 = kSch := rfl
@[simp] theorem fBa_0 : fBa (X := X) 0 = .inl 0 := rfl
@[simp] theorem fBa_1 : fBa (X := X) 1 = kH := rfl
@[simp] theorem fBa_2 : fBa (X := X) 2 = kP := rfl
@[simp] theorem fOn_0 : fOn (X := X) 0 = .inl 0 := rfl
@[simp] theorem fOn_1 : fOn (X := X) 1 = .inl 1 := rfl
@[simp] theorem fOn_2 : fOn (X := X) 2 = kP := rfl

variable [DecidableEq X] {S : PPLoc X → List Sym}

/-- The schedule compiler call: `sch` receives the encoded schedule. -/
theorem runs_schedCall {ES RS σ : Type} [DecidableEq ES] {J C : ℕ}
    {PS : Prog (KLoc (Fin 3) ES) (fun _ => Sym) RS} (hspec : SchedSpec J ES RS C PS)
    {jS : ES → X} (hj : Function.Injective jS) (l : Lens σ RS) (hS : KClean S)
    {P d r w K m : ℕ} {π : Equiv.Perm (Fin m)} {hrest prest : List Sym}
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hdw : d ≤ w + m) (hKw : K ≤ w + m)
    (h1 : S (.inl 1) = permHdr P d r w K m ++ hrest) (h2 : S (.inl 2) = permSyms π ++ prest)
    (a : List Sym) :
    Runs (callInj (pemb fSc jS) l PS) (pst S a [] [] [])
      (pst S a (schedSyms (posPermSched m d K π)) [] []) (fun _ => True)
      (C * ((w + m + 1) ^ J + (permHdr P d r w K m).length + (permSyms π).length)) := by
  have h := CnotBatchRed.runs_callInj_update (B := pst S a [] [] [])
    (pemb_injective fSc_inj hj fSc_ne) l
    (hspec P d r w K m π hrest prest _ (kclean_pemb S a [] [] [] hS fSc jS) hd hK hdw hKw
      (by simp [h1]) (by simp [h2]))
  rw [show pemb fSc jS (.inl 2) = kSch from rfl] at h
  simpa [pst_upd_sch] using h

/-- A batch call on `(array, h, p)`. -/
theorem runs_batchCall {EB RB σ : Type} [DecidableEq EB] {Band : LayerRT → Prop} {lam' : ℝ}
    {J C : ℕ} {PB : Prog (KLoc (Fin 3) EB) (fun _ => Sym) RB}
    (hspec : BatchSpec Band lam' J EB RB C PB) {jB : EB → X} (hj : Function.Injective jB)
    (l : Lens σ RB) (hS : KClean S) {P d r w K m j₀ D nS ρ : ℕ} {ps : List (Fin m × Fin m)}
    {z : RArr (Cube m) r} {rest : List Sym}
    (hm : j₀ + D * K + nS = m) (hD1 : 1 ≤ D) (hDd : D ≤ d) (hρ : ρ < K) (hw : P + 2 ≤ w)
    (hdw : d ≤ w + m) (hKw : K ≤ w + m) (hv : CnotPairsValid ps)
    (htgt : targets ps ⊆ slicePos m K j₀ D ρ) (hband : Band (sliceRT P d r w K j₀ D nS ρ))
    (hz : ArrOnDiskGrid P z) (hbt : BlkTerm rest) (sc : List Sym) :
    Runs (callInj (pemb fBa jB) l PB)
      (pst S (carrSyms w (encCube P z) ++ rest) sc (sliceHdr P d r w K m j₀ D nS ρ) (pairsSyms ps))
      (pst S (carrSyms w (encCube P (cnotArr ps z)) ++ rest) sc (sliceHdr P d r w K m j₀ D nS ρ)
        (pairsSyms ps))
      (fun _ => True)
      (C * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + cvolCube m r (w + 8 * d) +
          2 ^ m * (w + m + 1) ^ J + (sliceHdr P d r w K m j₀ D nS ρ).length)) := by
  have h := CnotBatchRed.runs_callInj_update
    (B := pst S (carrSyms w (encCube P z) ++ rest) sc (sliceHdr P d r w K m j₀ D nS ρ)
      (pairsSyms ps)) (pemb_injective fBa_inj hj fBa_ne) l
    (hspec P d r w K m j₀ D nS ρ ps z rest [] [] _ (kclean_pemb S _ _ _ _ hS fBa jB) hm hD1 hDd
      hρ hw hdw hKw hv htgt hband hz hbt (by simp) (by simp) (by simp))
  rwa [show pemb fBa jB (.inl 0) = .inl 0 from rfl, pst_upd_arr] at h

/-- A single-flip call on `(array, permHdr, p)`. -/
theorem runs_oneCall {E1 R1 σ : Type} [DecidableEq E1] {J C : ℕ}
    {P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1} (hspec : OneSpec J E1 R1 C P1)
    {j1 : E1 → X} (hj : Function.Injective j1) (l : Lens σ R1) (hS : KClean S)
    {P d r w K m : ℕ} {c t : Fin m} {z : RArr (Cube m) r} {rest hrest : List Sym}
    (hct : c ≠ t) (hbt : BlkTerm rest) (h1 : S (.inl 1) = permHdr P d r w K m ++ hrest)
    (sc h : List Sym) :
    Runs (callInj (pemb fOn j1) l P1)
      (pst S (carrSyms w (encCube P z) ++ rest) sc h (pairsSyms [(c, t)]))
      (pst S (carrSyms w (encCube P (cnotArr [(c, t)] z)) ++ rest) sc h (pairsSyms [(c, t)]))
      (fun _ => True) (C * (cvolCube m r w + (w + m + 1) ^ J + (permHdr P d r w K m).length)) := by
  have h' := CnotBatchRed.runs_callInj_update
    (B := pst S (carrSyms w (encCube P z) ++ rest) sc h (pairsSyms [(c, t)]))
    (pemb_injective fOn_inj hj fOn_ne) l
    (hspec P d r w K m c t z rest hrest [] _ (kclean_pemb S _ _ _ _ hS fOn j1) hct hbt (by simp)
      (by simp [h1]) (by simp))
  rwa [show pemb fOn j1 (.inl 0) = .inl 0 from rfl, pst_upd_arr] at h'

end Calls
/-! ## Branching and looping -/

/-- An `ite` whose test is known to be true. -/
theorem triple_ite_true {K σ : Type} [DecidableEq K] {c : σ → Bool}
    {p q : Prog K (fun _ => Sym) σ} {B B' : K → List Sym} {R : σ → Prop} {T : ℕ}
    (hR : ∀ v, R v → c v = true) (hp : Runs p B B' (fun _ => True) T) :
    Triple [] (fun s => s.stk = B ∧ R s.var) (.ite c p q) (fun s => s.stk = B' ∧ True) (T + 1) :=
  Triple.ite (Triple.pre hp (fun s hs => hs.1.1))
    (Triple.pre Triple.false_pre (fun s hs => absurd (hR _ hs.1.2) (by rw [hs.2]; simp)))

/-- An `ite` whose test is known to be false. -/
theorem triple_ite_false {K σ : Type} [DecidableEq K] {c : σ → Bool}
    {p q : Prog K (fun _ => Sym) σ} {B B' : K → List Sym} {R : σ → Prop} {T : ℕ}
    (hR : ∀ v, R v → c v = false) (hq : Runs q B B' (fun _ => True) T) :
    Triple [] (fun s => s.stk = B ∧ R s.var) (.ite c p q) (fun s => s.stk = B' ∧ True) (T + 1) :=
  Triple.ite (Triple.pre Triple.false_pre (fun s hs => absurd (hR _ hs.1.2) (by rw [hs.2]; simp)))
    (Triple.pre hq (fun s hs => hs.1.1))

/-- **A loop over a list of commands** (invariant indexed by the remaining commands and a value). -/
theorem triple_loop_list {K σ α β : Type} [DecidableEq K] (c : σ → Bool)
    (body : Prog K (fun _ => Sym) σ) (I : β → List α → St K (fun _ => Sym) σ → Prop)
    (eff : α → β → β) (G : β → Prop) (OK : α → Prop) (T : α → ℕ)
    (hG : ∀ a b, OK a → G b → G (eff a b))
    (hstep : ∀ a l b, OK a → G b → Triple [] (I b (a :: l)) body (I (eff a b) l) (T a))
    (hcont : ∀ a l b s, I b (a :: l) s → c s.var = true)
    (hstop : ∀ b s, I b [] s → c s.var = false) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, OK a) → G b →
      Triple [] (I b l) (.loop c body) (I (l.foldl (fun b a => eff a b) b) [])
        ((l.map T).sum + l.length + 1)
  | [], b, _, _ => fun s hs => ⟨s, 1, Eval.loop_false (hstop b s hs), hs, le_rfl⟩
  | a :: l, b, hl, hb => by
    intro s hs
    obtain ⟨s₁, t₁, e₁, h₁, ht₁⟩ := hstep a l b (hl a List.mem_cons_self) hb s hs
    obtain ⟨s₂, t₂, e₂, h₂, ht₂⟩ := triple_loop_list c body I eff G OK T hG hstep hcont hstop l
      (eff a b) (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha'))
      (hG a b (hl a List.mem_cons_self) hb) s₁ h₁
    refine ⟨s₂, t₁ + t₂ + 1, Eval.loop_true (hcont a l b s hs) e₁ e₂, h₂, ?_⟩
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-! ## The interpreter program -/

/-- The parts' private block. -/
abbrev PPX (ES EB E1 : Type) : Type := ES ⊕ (EB ⊕ E1)

/-- Registers: the parts', then the glue register and the drain flag. -/
abbrev PPR (RS RB R1 : Type) : Type := (RS × (RB × R1)) × (Option Sym × Bool)

/-- The composite's stacks. -/
abbrev PLoc (ES EB E1 : Type) : Type := PPLoc (PPX ES EB E1)

section Prog

variable {ES EB E1 RS RB R1 : Type}

def jS : ES → PPX ES EB E1 := Sum.inl
def jB : EB → PPX ES EB E1 := fun e => .inr (.inl e)
def j1 : E1 → PPX ES EB E1 := fun e => .inr (.inr e)

def lS : Lens (PPR RS RB R1) RS := (Lens.fst _ _).comp (Lens.fst _ _)
def lB : Lens (PPR RS RB R1) RB := (Lens.fst _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def l1 : Lens (PPR RS RB R1) R1 := (Lens.fst _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))
def lO : Lens (PPR RS RB R1) (Option Sym) := (Lens.snd _ _).comp (Lens.fst _ _)
def lD : Lens (PPR RS RB R1) Bool := (Lens.snd _ _).comp (Lens.snd _ _)

/-- A tag on top. -/
def isTagO : Option Sym → Bool
  | some (.tag _) => true
  | _ => false

/-- The loop test: the glue register holds a tag. -/
def isTagR (v : PPR RS RB R1) : Bool := isTagO (lO.get v)

/-- The dispatch test: the tag is `tag 0` (a batch). -/
def isTag0 (v : PPR RS RB R1) : Bool := decide (lO.get v = some (.tag 0))

variable (PS : Prog (KLoc (Fin 3) ES) (fun _ => Sym) RS)
  (PB : Prog (KLoc (Fin 3) EB) (fun _ => Sym) RB) (P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1)

/-- A glue program on the composite's own stacks. -/
def gl (P : SProg (PLoc ES EB E1)) : Prog (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1) :=
  callInj id lO P

/-- The batch branch. -/
def batchBr : Prog (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1) :=
  .seq (gl (moveUntil .sep2 kSch kH)) (.seq (gl (copyHdr 6 (.inl 1) kH kT))
  (.seq (gl (moveUntil .sep2 kSch kP)) (.seq (callInj (pemb fBa jB) lB PB)
  (.seq (callInj id lD (CnotBatchRed.drainProg kH)) (callInj id lD (CnotBatchRed.drainProg kP))))))

/-- The single-flip branch. -/
def oneBr : Prog (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1) :=
  .seq (gl (moveUntil .sep2 kSch kP))
    (.seq (callInj (pemb fOn j1) l1 P1) (callInj id lD (CnotBatchRed.drainProg kP)))

/-- The loop body: pop the tag, dispatch, peek the next tag. -/
def body : Prog (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1) :=
  .seq (gl (popR kSch)) (.seq (.ite isTag0 (batchBr PB) (oneBr P1)) (gl (peekR kSch)))

/-- **The composite**: compile the schedule, then interpret it. -/
def ppProg : Prog (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1) :=
  .seq (callInj (pemb fSc jS) lS PS) (.seq (gl (peekR kSch)) (.loop isTagR (body PB P1)))

theorem closed_fieldMoves {K : Type} (src tmp : K) :
    ∀ n, (fieldMoves src tmp n).Closed
  | 0 => by simp [fieldMoves, skip, Prog.Closed, Prog.FreeBelow]
  | n + 1 => ⟨by simp [fieldMove, moveBits, moveBitsBody, popR, pushR, Prog.FreeBelow],
      closed_fieldMoves src tmp n⟩

theorem closed_ppProg (hS : PS.Closed) (hB : PB.Closed) (h1 : P1.Closed) :
    (ppProg PS PB P1).Closed := by
  have hmv : ∀ (a b : PLoc ES EB E1), (moveUntil .sep2 a b).Closed := fun a b => by
    simp [moveUntil, moveBitsBody, popR, pushR, Prog.Closed, Prog.FreeBelow]
  have hcp : (copyHdr 6 (.inl 1 : PLoc ES EB E1) kH kT).Closed :=
    ⟨closed_fieldMoves _ _ 6, by simp [dupAll, dupBody2, popR, pushR, Prog.FreeBelow]⟩
  have hpop : (popR (kSch : PLoc ES EB E1)).Closed := by
    simp [popR, Prog.Closed, Prog.FreeBelow]
  have hpeek : (peekR (kSch : PLoc ES EB E1)).Closed := by
    simp [peekR, Prog.Closed, Prog.FreeBelow]
  have hgl : ∀ P : SProg (PLoc ES EB E1), P.Closed →
      (gl (RS := RS) (RB := RB) (R1 := R1) P).Closed := fun P hP => closed_callInj _ _ hP
  refine ⟨closed_callInj _ _ hS, hgl _ hpeek, hgl _ hpop,
    ⟨⟨hgl _ (hmv _ _), hgl _ hcp, hgl _ (hmv _ _), closed_callInj _ _ hB,
      closed_callInj _ _ (CnotBatchRed.closed_drainProg _),
      closed_callInj _ _ (CnotBatchRed.closed_drainProg _)⟩,
     ⟨hgl _ (hmv _ _), closed_callInj _ _ h1, closed_callInj _ _ (CnotBatchRed.closed_drainProg _)⟩⟩,
    hgl _ hpeek⟩

end Prog

/-! ## One command of the interpreter -/

/-- Cost of one iteration (pop, dispatch, branch, peek) for a command. -/
noncomputable def cmdCost (lam' : ℝ) (JB CB J1 C1 P d r w K m : ℕ) : PosCmd m K → ℕ
  | .batch j₀ D nS ρ ps =>
      1 + (((3 * (hdrSyms [j₀, D, nS, (ρ : ℕ)]).reverse.length + 2) +
        ((fieldsCost [P, d, r, w, K, m] + (4 * (hdrSyms [P, d, r, w, K, m]).length + 2)) +
        ((3 * (pairsSyms ps).reverse.length + 2) +
        (CB * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + cvolCube m r (w + 8 * d) +
            2 ^ m * (w + m + 1) ^ JB + (sliceHdr P d r w K m j₀ D nS ρ).length) +
        ((2 * (sliceHdr P d r w K m j₀ D nS ρ).length + 3) + (2 * (pairsSyms ps).length + 3)))))) +
        1 + 1)
  | .one c t =>
      1 + (((3 * (pairsSyms [(c, t)]).reverse.length + 2) +
        (C1 * (cvolCube m r w + (w + m + 1) ^ J1 + (permHdr P d r w K m).length) +
        (2 * (pairsSyms [(c, t)]).length + 3))) + 1 + 1)

section Body

variable {ES EB E1 RS RB R1 : Type} [DecidableEq ES] [DecidableEq EB] [DecidableEq E1]
  [iX : DecidableEq (PPX ES EB E1)]

omit [DecidableEq ES] [DecidableEq E1] in
/-- **A batch command**: the body performs `CNOT` of its pairs. -/
theorem runs_body_batch {Band : LayerRT → Prop} {lam' : ℝ} {JB CB J1 C1 : ℕ}
    {PB : Prog (KLoc (Fin 3) EB) (fun _ => Sym) RB} (P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1)
    (hB : BatchSpec Band lam' JB EB RB CB PB) {S : PLoc ES EB E1 → List Sym} (hS : KClean S)
    {P d r w K m : ℕ} {hrest : List Sym} (h1 : S (.inl 1) = permHdr P d r w K m ++ hrest)
    (hw : P + 2 ≤ w) (hdw : d ≤ w + m) (hKw : K ≤ w + m)
    (hband : SliceCallsBand Band P d r w K m) {j₀ D nS : ℕ} {ρ : Fin K}
    {ps : List (Fin m × Fin m)} (hok : CmdOK m d K (.batch j₀ D nS ρ ps)) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid P z) {rest : List Sym} (hbt : BlkTerm rest) (sc : List Sym) :
    Runs (body (RS := RS) PB P1)
      (pst S (carrSyms w (encCube P z) ++ rest) (cmdSyms (PosCmd.batch j₀ D nS ρ ps) ++ sc) [] [])
      (pst S (carrSyms w (encCube P (cnotArr ps z)) ++ rest) sc [] [])
      (fun v => lO.get v = sc.head?)
      (cmdCost lam' JB CB J1 C1 P d r w K m (.batch j₀ D nS ρ ps)) := by
  obtain ⟨hm, hD1, hDd, hv, htgt⟩ := hok
  have hT : S kT = [] := hS (.inl 3)
  have hjB : Function.Injective (jB : EB → PPX ES EB E1) := fun _ _ h => by simpa [jB] using h
  have e0 : cmdSyms (PosCmd.batch j₀ D nS ρ ps) ++ sc = Sym.tag 0 ::
      ((hdrSyms [j₀, D, nS, (ρ : ℕ)]).reverse ++
        Sym.sep2 :: ((pairsSyms ps).reverse ++ Sym.sep2 :: sc)) := by
    simp [cmdSyms]
  rw [e0]
  have t1 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_popTag S (carrSyms w (encCube P z) ++ rest) [] [] (Sym.tag 0)
      ((hdrSyms [j₀, D, nS, (ρ : ℕ)]).reverse ++
        Sym.sep2 :: ((pairsSyms ps).reverse ++ Sym.sep2 :: sc)))
  have m1 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_moveH S (carrSyms w (encCube P z) ++ rest) [] [] (hdrSyms [j₀, D, nS, (ρ : ℕ)]).reverse
      ((pairsSyms ps).reverse ++ Sym.sep2 :: sc) (sep2_not_mem_rev_hdrSyms _))
  rw [List.reverse_reverse, List.append_nil] at m1
  have c2 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_copyHdr S (carrSyms w (encCube P z) ++ rest) ((pairsSyms ps).reverse ++ Sym.sep2 :: sc)
      (hdrSyms [j₀, D, nS, (ρ : ℕ)]) [] [P, d, r, w, K, m] rfl hrest h1 hT)
  have hsl : hdrSyms [P, d, r, w, K, m] ++ hdrSyms [j₀, D, nS, (ρ : ℕ)] =
      sliceHdr P d r w K m j₀ D nS ρ := by
    rw [← hdrSyms_append']; rfl
  rw [hsl] at c2
  have m3 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_moveP S (carrSyms w (encCube P z) ++ rest) (sliceHdr P d r w K m j₀ D nS ρ) []
      (pairsSyms ps).reverse sc (by rw [List.mem_reverse]; exact sep2_not_mem_hdrSyms _))
  rw [List.reverse_reverse, List.append_nil] at m3
  have c4 := runs_batchCall hB hjB (lB : Lens (PPR RS RB R1) RB) hS hm hD1 hDd ρ.isLt hw hdw hKw
    hv htgt (hband j₀ D nS ρ hm hD1 hDd ρ.isLt) hz hbt sc
  have d5 := runs_drainK (lD : Lens (PPR RS RB R1) Bool) kH
    (pst S (carrSyms w (encCube P (cnotArr ps z)) ++ rest) sc (sliceHdr P d r w K m j₀ D nS ρ)
      (pairsSyms ps))
  rw [pst_upd_h, pst_h] at d5
  have d6 := runs_drainK (lD : Lens (PPR RS RB R1) Bool) kP
    (pst S (carrSyms w (encCube P (cnotArr ps z)) ++ rest) sc [] (pairsSyms ps))
  rw [pst_upd_p, pst_p] at d6
  have tb := runs_seq m1 (runs_seq c2 (runs_seq m3 (runs_seq c4 (runs_seq d5 d6))))
  have tite := triple_ite_true (q := oneBr P1) (c := isTag0)
    (R := fun v => (lO : Lens (PPR RS RB R1) (Option Sym)).get v = some (Sym.tag 0))
    (fun v hv => by simp [isTag0, hv]) tb
  have t3 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_peekSch (pst S (carrSyms w (encCube P (cnotArr ps z)) ++ rest) sc [] []))
  simp only [pst_sch] at t3
  have hall := Triple.seq t1 (Triple.seq tite (Triple.pre t3 (fun s hs => hs.1)))
  exact Triple.cost_mono hall (le_of_eq (by simp only [cmdCost]))

omit [DecidableEq ES] [DecidableEq EB] in
/-- **A single-flip command**: the body performs `CNOT` of its pair. -/
theorem runs_body_one {J1 C1 JB CB : ℕ} {lam' : ℝ}
    (PB : Prog (KLoc (Fin 3) EB) (fun _ => Sym) RB) {P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1}
    (h1s : OneSpec J1 E1 R1 C1 P1) {S : PLoc ES EB E1 → List Sym} (hS : KClean S)
    {P d r w K m : ℕ} {hrest : List Sym} (h1 : S (.inl 1) = permHdr P d r w K m ++ hrest)
    {c t : Fin m} (hok : CmdOK m d K (PosCmd.one (K := K) c t)) {z : RArr (Cube m) r}
    {rest : List Sym} (hbt : BlkTerm rest) (sc : List Sym) :
    Runs (body (RS := RS) PB P1)
      (pst S (carrSyms w (encCube P z) ++ rest) (cmdSyms (PosCmd.one (K := K) c t) ++ sc) [] [])
      (pst S (carrSyms w (encCube P (cnotArr [(c, t)] z)) ++ rest) sc [] [])
      (fun v => lO.get v = sc.head?)
      (cmdCost lam' JB CB J1 C1 P d r w K m (PosCmd.one c t)) := by
  have hct : c ≠ t := hok
  have hj1 : Function.Injective (j1 : E1 → PPX ES EB E1) := fun _ _ h => by simpa [j1] using h
  have e0 : cmdSyms (PosCmd.one (K := K) c t) ++ sc = Sym.tag 1 ::
      ((pairsSyms [(c, t)]).reverse ++ Sym.sep2 :: sc) := by
    simp [cmdSyms]
  rw [e0]
  have t1 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_popTag S (carrSyms w (encCube P z) ++ rest) [] [] (Sym.tag 1)
      ((pairsSyms [(c, t)]).reverse ++ Sym.sep2 :: sc))
  have m1 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_moveP S (carrSyms w (encCube P z) ++ rest) [] [] (pairsSyms [(c, t)]).reverse sc
      (by rw [List.mem_reverse]; exact sep2_not_mem_hdrSyms _))
  rw [List.reverse_reverse, List.append_nil] at m1
  have c2 := runs_oneCall h1s hj1 (l1 : Lens (PPR RS RB R1) R1) hS (z := z) hct hbt h1 sc []
  have d3 := runs_drainK (lD : Lens (PPR RS RB R1) Bool) kP
    (pst S (carrSyms w (encCube P (cnotArr [(c, t)] z)) ++ rest) sc [] (pairsSyms [(c, t)]))
  rw [pst_upd_p, pst_p] at d3
  have tb := runs_seq m1 (runs_seq c2 d3)
  have tite := triple_ite_false (p := batchBr PB) (c := isTag0)
    (R := fun v => (lO : Lens (PPR RS RB R1) (Option Sym)).get v = some (Sym.tag 1))
    (fun v hv => by simp [isTag0, hv]) tb
  have t3 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_peekSch (pst S (carrSyms w (encCube P (cnotArr [(c, t)] z)) ++ rest) sc [] []))
  simp only [pst_sch] at t3
  have hall := Triple.seq t1 (Triple.seq tite (Triple.pre t3 (fun s hs => hs.1)))
  exact Triple.cost_mono hall (le_of_eq (by simp only [cmdCost]))

end Body

/-! ## The cost bound -/

section Cost

/-- The bracket of `permCost`: `V_*·(⌈d^{λ'}⌉₊ + 1) + 2^m·(w + m + 1)^J`. -/
noncomputable def ppQ (lam' : ℝ) (J d r w m : ℕ) : ℕ :=
  cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) + 2 ^ m * (w + m + 1) ^ J

theorem pow_le_ppQ {lam' : ℝ} {J d r w m k : ℕ} (hk : k ≤ J) :
    2 ^ m * (w + m + 1) ^ k ≤ ppQ lam' J d r w m := by
  unfold ppQ
  exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk)) (Nat.le_add_left _ _)

theorem pow_le_ppQ' {lam' : ℝ} {J d r w m k : ℕ} (hk : k ≤ J) :
    (w + m + 1) ^ k ≤ ppQ lam' J d r w m :=
  le_trans (Nat.le_mul_of_pos_left _ (by positivity)) (pow_le_ppQ hk)

theorem vol_le_ppQ {lam' : ℝ} {J d r w m : ℕ} :
    cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) ≤ ppQ lam' J d r w m := by
  unfold ppQ
  exact Nat.le_add_right _ _

theorem cvol_le_ppQ {lam' : ℝ} {J d r w m : ℕ} :
    cvolCube m r (w + 8 * d) ≤ ppQ lam' J d r w m := by
  have h1 : cvolCube m r (w + 8 * d) ≤ cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  exact le_trans h1 vol_le_ppQ

theorem one_le_ppQ {lam' : ℝ} {J d r w m : ℕ} : 1 ≤ ppQ lam' J d r w m := by
  have h := pow_le_ppQ' (lam' := lam') (J := J) (d := d) (r := r) (w := w) (m := m) (Nat.zero_le J)
  simpa using h

theorem r_le_cvol {m r w d : ℕ} (hd : 1 ≤ d) : r ≤ cvolCube m r (w + 8 * d) := by
  unfold cvolCube
  have h0 : r ≤ r * (w + 8 * d) := Nat.le_mul_of_pos_right r (by omega)
  have h1 : r ≤ 2 * r * (w + 8 * d) + 1 := by
    have e : 2 * r * (w + 8 * d) = 2 * (r * (w + 8 * d)) := by ring
    omega
  exact le_trans h1 (Nat.le_mul_of_pos_left _ (by positivity))

/-- `|permHdr| ≤ r + 6(w + m + 1)` (each field's binary length is at most the field). -/
theorem permHdr_le {P d r w K m : ℕ} (hw : P + 2 ≤ w) (hdw : d ≤ w + m) (hKw : K ≤ w + m) :
    (hdrSyms [P, d, r, w, K, m]).length ≤ r + 6 * (w + m + 1) := by
  have h1 := CnotBatchRed.bitLen_le_self' P
  have h2 := CnotBatchRed.bitLen_le_self' d
  have h3 := CnotBatchRed.bitLen_le_self' r
  have h4 := CnotBatchRed.bitLen_le_self' w
  have h5 := CnotBatchRed.bitLen_le_self' K
  have h6 := CnotBatchRed.bitLen_le_self' m
  simp only [CnotBatchRed.length_hdrSyms', List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

theorem permHdr_le_ppQ {lam' : ℝ} {J P d r w K m : ℕ} (hJ : 1 ≤ J) (hd : 1 ≤ d)
    (hw : P + 2 ≤ w) (hdw : d ≤ w + m) (hKw : K ≤ w + m) :
    (hdrSyms [P, d, r, w, K, m]).length ≤ 7 * ppQ lam' J d r w m := by
  have h1 := permHdr_le (r := r) hw hdw hKw
  have h2 := r_le_cvol (m := m) (r := r) (w := w) hd
  have h3 : cvolCube m r (w + 8 * d) ≤ ppQ lam' J d r w m := cvol_le_ppQ
  have h4 : (w + m + 1) ^ 1 ≤ ppQ lam' J d r w m := pow_le_ppQ' hJ
  rw [pow_one] at h4
  omega

/-- The slice-shape header block is short: `|hdrSyms [j₀, D, nS, ρ]| ≤ 4(w + m + 1)`. -/
theorem hdr4_le {w m K j₀ D nS ρ : ℕ} (hm : j₀ + D * K + nS = m) (hK : 1 ≤ K) (hρ : ρ < K)
    (hKw : K ≤ w + m) : (hdrSyms [j₀, D, nS, ρ]).length ≤ 4 * (w + m + 1) := by
  have hDK : D ≤ D * K := Nat.le_mul_of_pos_right D (by omega)
  have h1 := CnotBatchRed.bitLen_le_self' j₀
  have h2 := CnotBatchRed.bitLen_le_self' D
  have h3 := CnotBatchRed.bitLen_le_self' nS
  have h4 := CnotBatchRed.bitLen_le_self' ρ
  simp only [CnotBatchRed.length_hdrSyms', List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

theorem fieldsCost_le (fs : List ℕ) : fieldsCost fs ≤ 3 * (hdrSyms fs).length + 1 := by
  rw [fieldsCost, CnotBatchRed.length_hdrSyms']
  have h : ∀ l : List ℕ, (l.map fun f => 3 * bitLen f + 3).sum =
      3 * (l.map fun n => bitLen n + 1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [h]

/-- A slice layer call costs at most `V_*·(⌈d^{λ'}⌉₊ + 1) + 1` (its record count is `2^m`). -/
theorem layerCost_slice_le {lam' : ℝ} {P d r w K m j₀ D nS ρ : ℕ} (hm : j₀ + D * K + nS = m) :
    layerCost lam' (sliceRT P d r w K j₀ D nS ρ) ≤
      cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) + 1 := by
  have hM : (sliceRT P d r w K j₀ D nS ρ).M = 2 ^ m := by
    simp only [sliceRT, layerRT, LayerRT.M]
    rw [← pow_add, ← pow_add, ← hm]
    congr 1
    ring
  have hvol : (sliceRT P d r w K j₀ D nS ρ).vol ≤ cvolCube m r (w + 8 * d) := by
    unfold LayerRT.vol
    rw [hM]
    simp only [sliceRT, layerRT, cvolCube]
    calc 2 * 2 ^ m * r * (w + 8 * d) = 2 ^ m * (2 * r * (w + 8 * d)) := by ring
      _ ≤ 2 ^ m * (2 * r * (w + 8 * d) + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  unfold layerCost
  have hd' : (sliceRT P d r w K j₀ D nS ρ).d = d := rfl
  rw [hd']
  have h := Nat.mul_le_mul_right ⌈(d : ℝ) ^ lam'⌉₊ hvol
  calc _ ≤ cvolCube m r (w + 8 * d) * ⌈(d : ℝ) ^ lam'⌉₊ + cvolCube m r (w + 8 * d) + 1 := by
        omega
    _ = _ := by ring

theorem sum_map_le_len {α : Type} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [Nat.succ_mul]
    omega

/-- **One iteration's cost** is at most `(130 + 16 C_B + 16 C_1)·Q` (`Q` the bracket of
`permCost`), for both command kinds. -/
theorem cmdCost_le {lam' : ℝ} {JB CB J1 C1 J P d r w K m : ℕ} (hJB : JB ≤ J) (hJ1 : J1 ≤ J)
    (hJ2 : 2 ≤ J) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : P + 2 ≤ w) (hdw : d ≤ w + m)
    (hKw : K ≤ w + m) (c : PosCmd m K) (hc : CmdOK m d K c) :
    cmdCost lam' JB CB J1 C1 P d r w K m c ≤ (130 + 16 * CB + 16 * C1) * ppQ lam' J d r w m := by
  obtain ⟨Q, hQ⟩ : ∃ x, x = ppQ lam' J d r w m := ⟨_, rfl⟩
  rw [← hQ]
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_ppQ
  have hV : cvolCube m r (w + 8 * d) ≤ Q := by rw [hQ]; exact cvol_le_ppQ
  have hVL : cvolCube m r (w + 8 * d) * (⌈(d : ℝ) ^ lam'⌉₊ + 1) ≤ Q := by
    rw [hQ]; exact vol_le_ppQ
  have hlin : w + m + 1 ≤ Q := by
    have h := pow_le_ppQ' (lam' := lam') (J := J) (d := d) (r := r) (w := w) (m := m)
      (show 1 ≤ J by omega)
    rw [pow_one] at h
    rw [hQ]; exact h
  have hsq : (m + 1) ^ 2 ≤ Q := by
    rw [hQ]
    exact le_trans (Nat.pow_le_pow_left (by omega) 2) (pow_le_ppQ' hJ2)
  have hH : (hdrSyms [P, d, r, w, K, m]).length ≤ 7 * Q := by
    rw [hQ]; exact permHdr_le_ppQ (by omega) hd hw hdw hKw
  have hH' : (permHdr P d r w K m).length ≤ 7 * Q := hH
  cases c with
  | batch j₀ D nS ρ ps =>
    obtain ⟨hm, hD1, hDd, hv, -⟩ := hc
    have h4 := hdr4_le hm hK ρ.isLt hKw
    have hps := CnotBatchRed.length_pairsSyms_le hv
    have hLC := layerCost_slice_le (lam' := lam') (P := P) (d := d) (r := r) (w := w)
      (ρ := (ρ : ℕ)) hm
    have hJBQ : 2 ^ m * (w + m + 1) ^ JB ≤ Q := by rw [hQ]; exact pow_le_ppQ hJB
    have hfc := fieldsCost_le [P, d, r, w, K, m]
    have hsl : (sliceHdr P d r w K m j₀ D nS ρ).length =
        (hdrSyms [P, d, r, w, K, m]).length + (hdrSyms [j₀, D, nS, (ρ : ℕ)]).length := by
      rw [← List.length_append, ← hdrSyms_append']; rfl
    have hCB : CB * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + cvolCube m r (w + 8 * d) +
        2 ^ m * (w + m + 1) ^ JB + (sliceHdr P d r w K m j₀ D nS ρ).length) ≤ CB * (15 * Q) :=
      Nat.mul_le_mul_left _ (by omega)
    have hX : CB * (15 * Q) = 15 * (CB * Q) := by ring
    simp only [cmdCost, List.length_reverse]
    calc _ ≤ 130 * Q + 16 * (CB * Q) + 16 * (C1 * Q) := by omega
      _ = (130 + 16 * CB + 16 * C1) * Q := by ring
  | one c t =>
    have hct : c ≠ t := hc
    have hv1 : CnotPairsValid [(c, t)] := by simp [CnotPairsValid, hct]
    have hps := CnotBatchRed.length_pairsSyms_le hv1
    have hcw : cvolCube m r w ≤ cvolCube m r (w + 8 * d) := by
      unfold cvolCube
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1)
    have hJ1Q : (w + m + 1) ^ J1 ≤ Q := by rw [hQ]; exact pow_le_ppQ' hJ1
    have hC1 : C1 * (cvolCube m r w + (w + m + 1) ^ J1 + (permHdr P d r w K m).length) ≤
        C1 * (9 * Q) := Nat.mul_le_mul_left _ (by omega)
    have hX : C1 * (9 * Q) = 9 * (C1 * Q) := by ring
    simp only [cmdCost, List.length_reverse]
    calc _ ≤ 130 * Q + 16 * (CB * Q) + 16 * (C1 * Q) := by omega
      _ = (130 + 16 * CB + 16 * C1) * Q := by ring

/-- The composite's constant (fixed before the data): `9·C_S` for the schedule compiler,
`12·(131 + 16·C_B + 16·C_1)` for the interpreter loop, `14` for the glue. -/
def ppConst (CS CB C1 : ℕ) : ℕ := 9 * CS + 12 * (131 + 16 * CB + 16 * C1) + 14

/-- **The parts' costs fit `C·(permCost + |permHdr|)`** with `J = J_B + J_1 + J_S + 2`: at most
`6(N_slice + K) ≤ 12(m/d + K + 1)` commands (`length_sched_le`, `nSlice_le_nat`), each within
`O(Q)` (`cmdCost_le`), plus the compiler's `C_S((w+m+1)^{J_S} + |permHdr| + |permSyms π|)`. -/
theorem ppCost_le {lam' : ℝ} {JS CS JB CB J1 C1 P d r w K m : ℕ} (π : Equiv.Perm (Fin m))
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : P + 2 ≤ w) (hdw : d ≤ w + m) (hKw : K ≤ w + m) :
    CS * ((w + m + 1) ^ JS + (permHdr P d r w K m).length + (permSyms π).length) +
        (1 + (((posPermSched m d K π).map (cmdCost lam' JB CB J1 C1 P d r w K m)).sum +
          (posPermSched m d K π).length + 1)) ≤
      ppConst CS CB C1 *
        (permCost lam' (JB + J1 + JS + 2) d r w K m + (permHdr P d r w K m).length) := by
  obtain ⟨J, hJ⟩ : ∃ x, x = JB + J1 + JS + 2 := ⟨_, rfl⟩
  rw [← hJ]
  obtain ⟨Q, hQ⟩ : ∃ x, x = ppQ lam' J d r w m := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ x, x = m / d := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ x, x = q + K + 1 := ⟨_, rfl⟩
  have hpc : permCost lam' J d r w K m = N * Q := by rw [hN, hq, hQ]; rfl
  rw [hpc]
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_ppQ
  have hJS : (w + m + 1) ^ JS ≤ Q := by rw [hQ]; exact pow_le_ppQ' (by omega)
  have hsq : (w + m + 1) ^ 2 ≤ Q := by rw [hQ]; exact pow_le_ppQ' (by omega)
  have hH : (permHdr P d r w K m).length ≤ 7 * Q := by
    rw [hQ]; exact permHdr_le_ppQ (by omega) hd hw hdw hKw
  have hpS : (permSyms π).length ≤ Q := by
    have h1 : (permSyms π).length ≤ m * (m + 1) := by
      have h := CnotBatchRed.length_hdrSyms_le (List.ofFn fun p : Fin m => ((π p : Fin m) : ℕ)) m
        (by
          intro x hx
          rw [List.mem_ofFn] at hx
          obtain ⟨p, rfl⟩ := hx
          exact (π p).isLt.le)
      rw [List.length_ofFn] at h
      exact h
    have h2 : m * (m + 1) ≤ (w + m + 1) ^ 2 := by
      calc m * (m + 1) ≤ (w + m + 1) * (w + m + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (w + m + 1) ^ 2 := (sq _).symm
    omega
  have hc : ∀ c ∈ posPermSched m d K π,
      cmdCost lam' JB CB J1 C1 P d r w K m c ≤ (130 + 16 * CB + 16 * C1) * Q := by
    intro c hc
    rw [hQ]
    exact cmdCost_le (by omega) (by omega) (by omega) hd hK hw hdw hKw c (sched_ok hd π c hc)
  have hsum := sum_map_le_len (posPermSched m d K π) (cmdCost lam' JB CB J1 C1 P d r w K m)
    ((130 + 16 * CB + 16 * C1) * Q) hc
  have hlen : (posPermSched m d K π).length ≤ 12 * N := by
    have h1 := length_sched_le (m := m) (d := d) hK π
    have h2 := nSlice_le_nat m K d hd
    rw [← hq] at h2
    omega
  have hNQ : Q ≤ N * Q := Nat.le_mul_of_pos_left Q (by omega)
  have hN1 : N ≤ N * Q := Nat.le_mul_of_pos_right N (by omega)
  have e1 : CS * ((w + m + 1) ^ JS + (permHdr P d r w K m).length + (permSyms π).length) ≤
      CS * (9 * (N * Q)) := Nat.mul_le_mul_left _ (by omega)
  have e2 : (posPermSched m d K π).length * ((130 + 16 * CB + 16 * C1) * Q) ≤
      12 * N * ((130 + 16 * CB + 16 * C1) * Q) := Nat.mul_le_mul_right _ hlen
  have e3 : 12 * N * ((130 + 16 * CB + 16 * C1) * Q) =
      12 * (130 * (N * Q) + 16 * (CB * (N * Q)) + 16 * (C1 * (N * Q))) := by ring
  have e4 : CS * (9 * (N * Q)) = 9 * (CS * (N * Q)) := by ring
  have e5 : ppConst CS CB C1 * (N * Q + (permHdr P d r w K m).length) =
      9 * (CS * (N * Q)) + 12 * (130 * (N * Q) + 16 * (CB * (N * Q)) + 16 * (C1 * (N * Q))) +
        26 * (N * Q) + ppConst CS CB C1 * (permHdr P d r w K m).length := by
    unfold ppConst; ring
  omega

end Cost

/-! ## The interpreter loop and the composite -/

section Loop

variable {ES EB E1 RS RB R1 : Type} [DecidableEq ES] [DecidableEq EB] [DecidableEq E1]
  [iX : DecidableEq (PPX ES EB E1)]

/-- The loop invariant at array value `b` with the commands `l` still to run: the array stack holds
`b`, `sch` holds `schedSyms l`, `h` and `p` are empty, and the glue register holds the top of
`sch`. -/
def LInv (S : PLoc ES EB E1 → List Sym) (P w : ℕ) (rest : List Sym) {m K r : ℕ}
    (b : RArr (Cube m) r) (l : List (PosCmd m K))
    (s : St (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1)) : Prop :=
  s.stk = pst S (carrSyms w (encCube P b) ++ rest) (schedSyms l) [] [] ∧
    (lO : Lens (PPR RS RB R1) (Option Sym)).get s.var = (schedSyms l).head?

omit [DecidableEq ES] in
/-- **One iteration**: the body runs the head command (`cmdEff`) and exposes the next one. -/
theorem loop_step {Band : LayerRT → Prop} {lam' : ℝ} {JB CB J1 C1 : ℕ}
    {PB : Prog (KLoc (Fin 3) EB) (fun _ => Sym) RB} {P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1}
    (hB : BatchSpec Band lam' JB EB RB CB PB) (h1s : OneSpec J1 E1 R1 C1 P1)
    {S : PLoc ES EB E1 → List Sym} (hS : KClean S) {P d r w K m : ℕ} {hrest : List Sym}
    (h1 : S (.inl 1) = permHdr P d r w K m ++ hrest) (hw : P + 2 ≤ w) (hdw : d ≤ w + m)
    (hKw : K ≤ w + m) (hband : SliceCallsBand Band P d r w K m) {rest : List Sym}
    (hbt : BlkTerm rest) (a : PosCmd m K) (l : List (PosCmd m K)) (z : RArr (Cube m) r)
    (hok : CmdOK m d K a) (hz : ArrOnDiskGrid P z) :
    Triple [] (LInv (RS := RS) (RB := RB) (R1 := R1) S P w rest z (a :: l)) (body PB P1)
      (LInv S P w rest (cmdEff a z) l) (cmdCost lam' JB CB J1 C1 P d r w K m a) := by
  have e : schedSyms (a :: l) = cmdSyms a ++ schedSyms l := by
    simp only [schedSyms, List.flatMap_cons]
  cases a with
  | batch j₀ D nS ρ ps =>
    have h := runs_body_batch (RS := RS) (J1 := J1) (C1 := C1) P1 hB hS h1 hw hdw hKw hband hok
      hz hbt (schedSyms l)
    refine Triple.conseq h (fun s hs => ?_) (fun s hs => hs) le_rfl
    obtain ⟨h', -⟩ := hs
    rw [e] at h'
    exact h'
  | one c t =>
    have h := runs_body_one (RS := RS) (JB := JB) (CB := CB) (lam' := lam') (z := z) PB h1s hS h1
      hok hbt (schedSyms l)
    refine Triple.conseq h (fun s hs => ?_) (fun s hs => hs) le_rfl
    obtain ⟨h', -⟩ := hs
    rw [e] at h'
    exact h'

/-- **The interpreter loop** runs the whole schedule: the array goes from `z` to `posPermArr π z`
(`foldl_sched`, matching `positional_perm` in `Math/Walsh/PositionalPerm.lean`). -/
theorem runs_loop {Band : LayerRT → Prop} {lam' : ℝ} {JB CB J1 C1 : ℕ}
    {PB : Prog (KLoc (Fin 3) EB) (fun _ => Sym) RB} {P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1}
    (hB : BatchSpec Band lam' JB EB RB CB PB) (h1s : OneSpec J1 E1 R1 C1 P1)
    {S : PLoc ES EB E1 → List Sym} (hS : KClean S) {P d r w K m : ℕ} {hrest : List Sym}
    (h1 : S (.inl 1) = permHdr P d r w K m ++ hrest) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : P + 2 ≤ w)
    (hdw : d ≤ w + m) (hKw : K ≤ w + m) (hband : SliceCallsBand Band P d r w K m)
    {rest : List Sym} (hbt : BlkTerm rest) (π : Equiv.Perm (Fin m)) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid P z) :
    Triple [] (LInv (RS := RS) (RB := RB) (R1 := R1) S P w rest z (posPermSched m d K π))
      (.loop isTagR (body PB P1)) (LInv S P w rest (posPermArr π z) ([] : List (PosCmd m K)))
      (((posPermSched m d K π).map (cmdCost lam' JB CB J1 C1 P d r w K m)).sum +
        (posPermSched m d K π).length + 1) := by
  have hcont : ∀ (a : PosCmd m K) (l : List (PosCmd m K)) (b : RArr (Cube m) r)
      (s : St (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1)),
      LInv S P w rest b (a :: l) s → isTagR s.var = true := by
    intro a l b s hs
    show isTagO (lO.get s.var) = true
    rw [hs.2]
    cases a <;> simp [schedSyms, cmdSyms, isTagO]
  have hstop : ∀ (b : RArr (Cube m) r) (s : St (PLoc ES EB E1) (fun _ => Sym) (PPR RS RB R1)),
      LInv S P w rest b ([] : List (PosCmd m K)) s → isTagR s.var = false := by
    intro b s hs
    show isTagO (lO.get s.var) = false
    rw [hs.2]
    rfl
  have h := triple_loop_list isTagR (body PB P1) (LInv S P w rest) cmdEff (ArrOnDiskGrid P)
    (CmdOK m d K) (cmdCost lam' JB CB J1 C1 P d r w K m)
    (fun a b _ hb => cmdEff_diskGrid a hb)
    (fun a l b hok hb => loop_step hB h1s hS h1 hw hdw hKw hband hbt a l b hok hb)
    hcont hstop (posPermSched m d K π) z (sched_ok hd π) hz
  rwa [foldl_sched P d K hd hK π z hz] at h

/-- **The composite runs**: exact value `posPermArr π z`, every other named stack restored, all
private stacks cleaned; the cost is the sum of the parts' costs. -/
theorem ppProg_runs {Band : LayerRT → Prop} {lam' : ℝ} {JS CS JB CB J1 C1 : ℕ}
    {PS : Prog (KLoc (Fin 3) ES) (fun _ => Sym) RS}
    {PB : Prog (KLoc (Fin 3) EB) (fun _ => Sym) RB} {P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1}
    (hSc : SchedSpec JS ES RS CS PS) (hB : BatchSpec Band lam' JB EB RB CB PB)
    (h1s : OneSpec J1 E1 R1 C1 P1)
    {P d r w K m : ℕ} {π : Equiv.Perm (Fin m)} {z : RArr (Cube m) r} {rest hrest prest : List Sym}
    {S : PLoc ES EB E1 → List Sym} (hS : KClean S) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : P + 2 ≤ w)
    (hdw : d ≤ w + m) (hKw : K ≤ w + m) (hband : SliceCallsBand Band P d r w K m)
    (hz : ArrOnDiskGrid P z) (hbt : BlkTerm rest)
    (hs0 : S (.inl 0) = carrSyms w (encCube P z) ++ rest)
    (hs1 : S (.inl 1) = permHdr P d r w K m ++ hrest) (hs2 : S (.inl 2) = permSyms π ++ prest) :
    Runs (ppProg PS PB P1) S
      (Function.update S (.inl 0) (carrSyms w (encCube P (posPermArr π z)) ++ rest))
      (fun _ => True)
      (CS * ((w + m + 1) ^ JS + (permHdr P d r w K m).length + (permSyms π).length) +
        (1 + (((posPermSched m d K π).map (cmdCost lam' JB CB J1 C1 P d r w K m)).sum +
          (posPermSched m d K π).length + 1))) := by
  have hSch : S kSch = [] := hS (.inl 0)
  have hH : S kH = [] := hS (.inl 1)
  have hP : S kP = [] := hS (.inl 2)
  have hjS : Function.Injective (jS : ES → PPX ES EB E1) := fun _ _ h => by simpa [jS] using h
  have t1 := runs_schedCall hSc hjS (lS : Lens (PPR RS RB R1) RS) hS hd hK hdw hKw hs1 hs2
    (carrSyms w (encCube P z) ++ rest)
  have t2 := runs_glue (lO : Lens (PPR RS RB R1) (Option Sym))
    (runs_peekSch (pst S (carrSyms w (encCube P z) ++ rest) (schedSyms (posPermSched m d K π))
      [] []))
  simp only [pst_sch] at t2
  have t3 := runs_loop (RS := RS) hB h1s hS hs1 hd hK hw hdw hKw hband hbt π hz
  have hall := Triple.seq t1 (Triple.seq (Triple.pre t2 (fun s hs => hs.1)) t3)
  refine Triple.conseq hall (fun s (hs : s.stk = S) => ?_) (fun s hs => ⟨?_, trivial⟩) le_rfl
  · show s.stk = pst S (carrSyms w (encCube P z) ++ rest) [] [] []
    rw [hs, ← hs0, pst_init S hSch hH hP]
  · obtain ⟨h', -⟩ := hs
    rw [show schedSyms ([] : List (PosCmd m K)) = [] from rfl, pst_final S _ hSch hH hP] at h'
    exact h'

end Loop

end SubNLogN.Machine.PosPermRed

namespace SubNLogN.Machine

open PosPermRed in
/-- **Theorem 5.8 on the machine, from its parts** (`thm:positional-perm`): the
slice-batched controlled flips (`CnotBatchMachineStmt`), the single controlled flip
(`Cnot1MachineStmt`) and the runtime schedule compiler (`PosPermSchedStmt`) give
`PositionalPermMachineStmt`. One fixed program `ppProg` (`Par := Unit`): compile the schedule, then
interpret it in a `Prog.loop`. Value: `foldl_sched` (`positional_perm` via
`sched_erase`); cost: `ppCost_le` with `J = J_B + J_1 + J_S + 2` and `C = ppConst C_S C_B C_1`. -/
theorem positionalPermMachine_of {Band : LayerRT → Prop} {lam' : ℝ}
    (hB : CnotBatchMachineStmt Band lam') (h1 : Cnot1MachineStmt) (hC : PosPermSchedStmt) :
    PositionalPermMachineStmt Band lam' := by
  obtain ⟨JB, CB, hB⟩ := hB
  obtain ⟨EB, iBf, iBd, RB, PB, fRB, nRB, cPB, sPB⟩ := hB ()
  obtain ⟨J1, C1, h1⟩ := h1
  obtain ⟨E1, i1f, i1d, R1, P1, fR1, nR1, cP1, sP1⟩ := h1 ()
  obtain ⟨JS, CS, hC⟩ := hC
  obtain ⟨ES, iSf, iSd, RS, PS, fRS, nRS, cPS, sPS⟩ := hC ()
  have sB : BatchSpec Band lam' JB EB RB CB PB := sPB
  have s1 : OneSpec J1 E1 R1 C1 P1 := sP1
  have sS : SchedSpec JS ES RS CS PS := sPS
  let iDX : DecidableEq (PPX ES EB E1) :=
    CnotBatchRed.decEqSum iSd (CnotBatchRed.decEqSum iBd i1d)
  let iFX : Fintype (PPX ES EB E1) :=
    CnotBatchRed.fintypeSum iSf (CnotBatchRed.fintypeSum iBf i1f)
  refine ⟨JB + J1 + JS + 2, ppConst CS CB C1, fun _ =>
    ⟨Fin 4 ⊕ PPX ES EB E1, CnotBatchRed.fintypeSum inferInstance iFX,
      CnotBatchRed.decEqSum inferInstance iDX, PPR RS RB R1, ppProg PS PB P1, inferInstance,
      inferInstance, closed_ppProg PS PB P1 cPS cPB cP1, ?_⟩⟩
  intro P d r w K m π z rest hrest prest S hS hd hK hw hdw hKw hband hz hbt hs0 hs1 hs2
  exact WP.W9comp.runs_mono (ppProg_runs (iX := iDX) sS sB s1 hS hd hK hw hdw hKw hband hz hbt
    hs0 hs1 hs2) (fun _ _ => trivial) (ppCost_le π hd hK hw hdw hKw)

end SubNLogN.Machine
