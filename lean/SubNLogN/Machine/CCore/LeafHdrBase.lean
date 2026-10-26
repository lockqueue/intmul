/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.Calculus.SafeFootprint
import SubNLogN.Machine.Calculus.Hdr
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# C-core header kernels: shared tools (`CCore/LeafHdrBase.lean`)

Generic tools for the header kernels `HdrTestStmt` and `PushChildHdrStmt`
(`CCore/SkelDefs.lean:181, 190`). Nothing here is specific to one kernel.

* `readsIn_of_forall`: a program on a layout whose stacks all satisfy `A` reads only `A`-stacks.
  With `runs_mapStk_post` (transport of an exact `Runs` fact, **with** its register postcondition,
  along an injective stack map) this is how the header kernels get their safety certificate: they
  are written on a sub-layout made of `desc` and private scratch stacks (all unframed in
  `ccoreFramed`), and embedded by `Prog.mapStk`.
* `extractField i d dst t tmp`: copy field `i` of the header on top of `d` onto `dst`
  (`runs_extractField`, exact, every other stack restored).
* The flag register `FReg = Bool × NatArith.Reg` (`lN`, `lS` lenses) and `RunsF`: an exact run that
  keeps the `Bool` flag component (used for the leaf test result).
* `triple_cmpF`: the comparison `NatArith.cmpN` with its result (`Lib.ordOf`) in the register.
* `mulInPlace`, `mulPow n`: `x ↦ x·y` and `x ↦ x·y^n` in place (from `NatArith.mulN`);
  `runs_mulInPlace` here, `runs_mulPow` in `CCore/LeafHdrTest.lean`.
-/

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability

section Footprint

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- If every stack satisfies `A`, every program reads only `A`-stacks. -/
theorem readsIn_of_forall {A : K → Prop} (hA : ∀ k, A k) : ∀ p : Prog K Γ σ, ReadsIn A p
  | .push _ _ => trivial
  | .peek k _ => hA k
  | .pop k _ => hA k
  | .load _ => trivial
  | .seq p q => ⟨readsIn_of_forall hA p, readsIn_of_forall hA q⟩
  | .ite _ p q => ⟨readsIn_of_forall hA p, readsIn_of_forall hA q⟩
  | .loop _ p => readsIn_of_forall hA p
  | .fix b => readsIn_of_forall hA b
  | .recur _ => trivial

end Footprint

section MapStk

variable {L K σ : Type} [DecidableEq L] [DecidableEq K]

/-- **Transport along an injective stack map, keeping the register postcondition.** -/
theorem runs_mapStk_post {ι : L → K} (hι : Function.Injective ι) {P : Prog L (fun _ => Sym) σ}
    {B B' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (P.mapStk ι) B B' Q T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := hP ⟨v, stk ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact (h1 x).trans (congrFun hs' x)
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  exact ⟨⟨s'.var, T'⟩, t, e', ⟨rfl, hq⟩, ht⟩

end MapStk

theorem closed_mapStk {L K σ : Type} (ι : L → K) {P : Prog L (fun _ => Sym) σ} (hP : P.Closed) :
    (P.mapStk ι).Closed :=
  (WP.W9comp.freeBelow_mapStk ι P 0).2 hP

section Extract

variable {K : Type}

/-- Copy field `i` of the header on top of `d` onto `dst`: park fields `0, …, i-1` on `t`, copy
the top number of `d` (temporary `tmp`), move the parked fields back. -/
def extractField (i : ℕ) (d dst t tmp : K) : SProg K :=
  .seq (forEachRange i (fun _ => moveFieldTo d t))
    (.seq (copyBlock d dst tmp) (forEachRange i (fun _ => moveFieldBack t d)))

theorem closed_extractField (i : ℕ) (d dst t tmp : K) : (extractField i d dst t tmp).Closed :=
  ⟨closed_forEachRange i _ (fun _ _ => closed_moveFieldTo d t),
    by simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
      moveBitsDup, dupBody, restoreR, popR, pushR, pushC, Lib.skip],
    closed_forEachRange i _ (fun _ _ => closed_moveFieldBack t d)⟩

variable [DecidableEq K]

/-- **`extractField`**, exact: `natSyms fs[i]` is pushed on `dst`; `d`, `t` (holding a number
terminator) and `tmp` are restored. -/
theorem runs_extractField {d dst t tmp : K} (hdd : d ≠ dst) (hdt : d ≠ t) (hdm : d ≠ tmp)
    (hst : dst ≠ t) (hsm : dst ≠ tmp) {i : ℕ} {fs : List ℕ} (hi : i < fs.length)
    (tl : List Sym) (S : K → List Sym) (hS : S d = W9.hdrSyms fs ++ tl) (ht : TermOK (S t)) :
    Runs (extractField i d dst t tmp) S (Function.update S dst (natSyms fs[i] ++ S dst))
      (fun _ => True)
      (2 * ((fs.take i).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen fs[i] + 9) := by
  have hlen : (fs.take i).length = i := List.length_take_of_le hi.le
  have hsplit : fs = fs.take i ++ fs[i] :: fs.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i fs, List.drop_eq_getElem_cons hi]
  have hS1 : S d = W9.hdrSyms (fs.take i) ++
      (natSyms fs[i] ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl)) := by
    rw [hS]
    conv_lhs => rw [hsplit]
    rw [HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons]
    simp only [List.append_assoc, List.cons_append]
  have h1 := runs_moveFieldsTo hdt (fs.take i) _ S hS1
  rw [hlen] at h1
  have h2 := HdrAux.runs_copyBlock hdd hdm hsm (encodeNat fs[i])
    (Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl))
    (Function.update (Function.update S d (natSyms fs[i] ++ Sym.mark ::
      (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) t (movedFields (fs.take i) ++ S t))
    (TermOK.cons rfl _) (by rw [Function.update_of_ne hdt, Function.update_self]; rfl)
  have h3 := runs_moveFieldsBack (Ne.symm hdt) (fs.take i).reverse (S t)
    (Function.update (Function.update (Function.update S d (natSyms fs[i] ++ Sym.mark ::
      (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) t (movedFields (fs.take i) ++ S t)) dst
      ((encodeNat fs[i]).map Sym.bit ++ Function.update (Function.update S d
        (natSyms fs[i] ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) t
        (movedFields (fs.take i) ++ S t) dst)) ht
    (by rw [Function.update_of_ne (Ne.symm hst), Function.update_self]; rfl)
  rw [List.length_reverse, hlen] at h3
  have hc := RunsIn.seq (RunsIn.iff_runs.mpr h1)
    (RunsIn.seq (RunsIn.iff_runs.mpr h2) (RunsIn.iff_runs.mpr h3))
  refine RunsIn.iff_runs.mp (RunsIn.congr hc ?_ ?_)
  · funext k
    rw [List.reverse_reverse]
    by_cases hkd : k = d
    · simp only [hkd, Function.update_self, Function.update_of_ne hdd, Function.update_of_ne hdt]
      exact hS1.symm
    · by_cases hkt : k = t
      · simp only [hkt, Function.update_self, Function.update_of_ne (Ne.symm hdt),
          Function.update_of_ne (Ne.symm hst)]
      · by_cases hks : k = dst
        · simp only [hks, Function.update_self, Function.update_of_ne (Ne.symm hdd),
            Function.update_of_ne hst]
          rfl
        · simp only [Function.update_of_ne hks, Function.update_of_ne hkt,
            Function.update_of_ne hkd]
  · have e1 : (encodeNat fs[i]).length = bitLen fs[i] := rfl
    rw [List.map_reverse, List.sum_reverse, e1]
    omega

end Extract

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability

/-! ## The flag register -/

/-- Register of the header-test kernel: a `Bool` flag and the `NatArith` register file. -/
abbrev FReg : Type := Bool × NatArith.Reg

/-- Lens to the `NatArith` register file. -/
def lN : Lens FReg NatArith.Reg := Lens.snd _ _

/-- Lens to the work register (`SProg` library programs). -/
def lS : Lens FReg (Option Sym) := lN.comp NatArith.lW

section Flag

variable {K : Type} [DecidableEq K]

/-- An exact run (from every register value) that keeps the flag component of the register. -/
def RunsF (P : Prog K (fun _ => Sym) FReg) (S S' : K → List Sym) (T : ℕ) : Prop :=
  ∀ b : Bool, Triple [] (fun s => s.stk = S ∧ s.var.1 = b) P
    (fun s => s.stk = S' ∧ s.var.1 = b) T

theorem runsF_liftN {p : Prog K (fun _ => Sym) NatArith.Reg} {S S' : K → List Sym}
    {Q : NatArith.Reg → Prop} {T : ℕ} (h : Runs p S S' Q T) : RunsF (p.liftRegs lN) S S' T := by
  intro b
  have h2 := Triple.liftRegs lN h (fun v => v.1 = b) (fun _ _ hv => hv)
  exact Triple.conseq h2 (fun s hs => ⟨hs.1, hs.2⟩) (fun s hs => ⟨hs.1.1, hs.2⟩) le_rfl

theorem runsF_liftS {p : SProg K} {S S' : K → List Sym} {Q : Option Sym → Prop} {T : ℕ}
    (h : Runs p S S' Q T) : RunsF (p.liftRegs lS) S S' T := by
  intro b
  have h2 := Triple.liftRegs lS h (fun v => v.1 = b) (fun _ _ hv => hv)
  exact Triple.conseq h2 (fun s hs => ⟨hs.1, hs.2⟩) (fun s hs => ⟨hs.1.1, hs.2⟩) le_rfl

theorem runsF_seq {P Q : Prog K (fun _ => Sym) FReg} {S₁ S₂ S₃ : K → List Sym} {T₁ T₂ : ℕ}
    (h₁ : RunsF P S₁ S₂ T₁) (h₂ : RunsF Q S₂ S₃ T₂) : RunsF (.seq P Q) S₁ S₃ (T₁ + T₂) :=
  fun b => Triple.seq (h₁ b) (h₂ b)

theorem runsF_mono {P : Prog K (fun _ => Sym) FReg} {S S' : K → List Sym} {T T' : ℕ}
    (h : RunsF P S S' T) (hT : T ≤ T') : RunsF P S S' T' :=
  fun b => Triple.cost_mono (h b) hT

/-- A flag-keeping run is an ordinary exact run. -/
theorem runs_of_runsF {P : Prog K (fun _ => Sym) FReg} {S S' : K → List Sym} {T : ℕ}
    (h : RunsF P S S' T) : Runs P S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨s', t, e, ⟨h1, -⟩, ht⟩ := h s.var.1 s ⟨hs, rfl⟩
  exact ⟨s', t, e, ⟨h1, trivial⟩, ht⟩

/-- **Comparison with the result in the register** (`NatArith.cmpN`, lifted by `lN`): the flag
is kept, every stack is restored, the compare register holds `Lib.ordOf a b`. -/
theorem triple_cmpF {x y t1 t2 : K} (h12 : x ≠ y) (h1a : x ≠ t1) (h1b : x ≠ t2) (h2a : y ≠ t1)
    (h2b : y ≠ t2) (hab : t1 ≠ t2) (a b : ℕ) (ra rb : List Sym) (S : K → List Sym)
    (hra : TermOK ra) (hrb : TermOK rb) (hA : S x = natSyms a ++ ra)
    (hB : S y = natSyms b ++ rb) (f : Bool) :
    Triple [] (fun s => s.stk = S ∧ s.var.1 = f) ((NatArith.cmpN x y t1 t2).liftRegs lN)
      (fun s => s.stk = S ∧ s.var.1 = f ∧ s.var.2.2.2.2.2 = Lib.ordOf a b)
      (12 * min (bitLen a) (bitLen b) + 15) := by
  rintro ⟨v, S0⟩ ⟨hS0, hv⟩
  change S0 = S at hS0
  subst hS0
  have e := cmpNum_eval h12 h1a h1b h2a h2b hab v.2.2.2 (encodeNat a) (encodeNat b) ra rb S0
    hra hrb hA hB
  have e1 := e.liftRegs NatArith.lC v.2 rfl
  have e2 := e1.liftRegs lN v rfl
  refine ⟨_, _, e2, ⟨rfl, hv, ?_⟩, le_rfl⟩
  show cmpAll .eq (encodeNat a) (encodeNat b) = Lib.ordOf a b
  rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
    bitsVal_encodeNat]

end Flag

/-! ## Multiplication in place -/

section MulPow

variable {K : Type}

/-- `x ↦ x · y` in place (`z` receives the product and is restored; `A, Bs, Acc, T` are the
temporaries of `mulN`, `tmp` the temporary of the copy). -/
def mulInPlace (x y z A Bs Acc T tmp : K) : Prog K (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.mulN x y z A Bs Acc T)
    (.seq (NatArith.dropN x) (.seq (NatArith.copyN z x tmp) (NatArith.dropN z)))

/-- `x ↦ x · y ^ n` in place (`n` a compile-time constant). -/
def mulPow (n : ℕ) (x y z A Bs Acc T tmp : K) : Prog K (fun _ => Sym) NatArith.Reg :=
  forEachRange n (fun _ => mulInPlace x y z A Bs Acc T tmp)

theorem closed_mulInPlace (x y z A Bs Acc T tmp : K) :
    (mulInPlace x y z A Bs Acc T tmp).Closed :=
  ⟨NatArith.closed_mulN _ _ _ _ _ _ _, NatArith.closed_dropN _, NatArith.closed_copyN _ _ _,
    NatArith.closed_dropN _⟩

theorem closed_mulPow (n : ℕ) (x y z A Bs Acc T tmp : K) :
    (mulPow n x y z A Bs Acc T tmp).Closed :=
  closed_forEachRange n _ (fun _ _ => closed_mulInPlace _ _ _ _ _ _ _ _)

/-- Cost of one `mulInPlace` step. -/
def mulStepCost (a b : ℕ) : ℕ := NatArith.mulCost a b + 2 * bitLen a + 9 * bitLen (a * b) + 15

variable [DecidableEq K]

/-- **`mulInPlace`**, exact: `x = natSyms a ++ rx` becomes `natSyms (a * b) ++ rx`, where
`y = natSyms b ++ ry`; every other stack is unchanged (`z` must hold a number terminator). -/
theorem runs_mulInPlace {x y z A Bs Acc T tmp : K} (h : [x, y, z, A, Bs, Acc, T].Nodup)
    (hxt : x ≠ tmp) (hzt : z ≠ tmp) (a b : ℕ) (rx ry : List Sym) (S : K → List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (hz : TermOK (S z)) (hx : S x = natSyms a ++ rx)
    (hy : S y = natSyms b ++ ry) :
    Runs (mulInPlace x y z A Bs Acc T tmp) S (Function.update S x (natSyms (a * b) ++ rx))
      (fun _ => True) (mulStepCost a b) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hxy, hxz, -, -, -, -⟩, -, -, -, -, -⟩ := h'
  have r1 := NatArith.runs_mulN h a b rx ry S hrx hry hx hy
  have r2 := NatArith.runs_dropN x a rx (Function.update S z (natSyms (a * b) ++ S z)) hrx
    (by rw [Function.update_of_ne hxz, hx])
  have r3 := NatArith.runs_copyN (src := z) (dst := x) (tmp := tmp) (Ne.symm hxz) hzt hxt (a * b)
    (S z) (Function.update (Function.update S z (natSyms (a * b) ++ S z)) x rx) hz
    (by rw [Function.update_of_ne (Ne.symm hxz), Function.update_self])
  have r4 := NatArith.runs_dropN z (a * b) (S z)
    (Function.update (Function.update (Function.update S z (natSyms (a * b) ++ S z)) x rx) x
      (natSyms (a * b) ++ Function.update (Function.update S z (natSyms (a * b) ++ S z)) x rx x))
    hz (by rw [Function.update_of_ne (Ne.symm hxz), Function.update_of_ne (Ne.symm hxz),
      Function.update_self])
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [mulStepCost]
    omega

end MulPow

end SubNLogN.Machine.CCore.LeafHdrAux
