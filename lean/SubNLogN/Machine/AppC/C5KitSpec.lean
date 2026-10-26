/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5KitDefs

/-!
# Proposition A.7 kit builder, part 2 (`AppC/C5KitSpec.lean`): kernel calls and their specs

Lenses, embeddings and programs of the kit components, closedness, and the exact `Runs` specs of
the single-call components (`rowszP`, `descP`, `distP`, `mergeP`) and of one elementary stream
step and one XOR, each from the chosen leaf kernel through `runs_callInj`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus

theorem runs_callInj_le {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T T' : ℕ} (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (hT : T ≤ T') :
    Runs (callInj ι l P) B B' (fun _ => True) T' :=
  RunsIn.iff_runs.1 (RunsIn.mono (RunsIn.iff_runs.2 (runs_callInj hι l hP hout))
    (fun _ _ => trivial) hT)

section Spec

variable {q W m : ℕ} {D : NetData W m} (hL : Leaves q D) [NeZero q]

/-! ## Lenses -/

def lr : Lens (RG hL) (Option Sym) := Lens.fst _ _

def lB : Lens (RG hL) (pkB q).R := (Lens.snd _ _).comp (Lens.fst _ _)

def lS (i : SIdx D) : Lens (RG hL) (pkS hL i).R :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))).comp (piLens _ i)

def lX : Lens (RG hL) (pkX hL).R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))

def lD (ij : Fin m × Fin m) : Lens (RG hL) (pkD hL ij).R :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _))))).comp (piLens _ ij)

def lR : Lens (RG hL) (pkR hL).R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))

def lDi : Lens (RG hL) (pkDi W).R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))

def lMe : Lens (RG hL) (pkMe W D.ρ).R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))))))

/-! ## Embeddings -/

def ιB : KLoc (Fin 4) (pkB q).E → KK hL := emb hL ![.io, .tmp2, .cG, .cB] Sum.inl

def ιS (i : SIdx D) (a : Option (Fin W)) : KLoc (Fin 5) (pkS hL i).E → KK hL :=
  emb hL ![arrSlot a, .ck, .cN1, .cG, .cB] (fun e => Sum.inr (Sum.inl ⟨i, e⟩))

def ιX (t s : Fin W) : KLoc (Fin 2) (pkX hL).E → KK hL :=
  emb hL ![.role t, .role s] (fun e => Sum.inr (Sum.inr (Sum.inl e)))

def ιD (ij : Fin m × Fin m) : KLoc (Fin 4) (pkD hL ij).E → KK hL :=
  emb hL ![.ck, .cN1, .cG, .cB] (fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨ij, e⟩))))

def ιR : KLoc (Fin 5) (pkR hL).E → KK hL :=
  emb hL ![.rsz, .ck, .cN1, .cG, .cB] (fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))))

def ιDi : KLoc (Fin 2 ⊕ Fin W) (pkDi W).E → KK hL :=
  emb hL (Sum.elim ![.io, .rsz] Slot.role)
    (fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e))))))

def ιMe : KLoc (Fin 2 ⊕ Fin W) (pkMe W D.ρ).E → KK hL :=
  emb hL (Sum.elim ![.io, .rsz] Slot.role)
    (fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr e))))))

theorem ιB_inj : Function.Injective (ιB hL) :=
  emb_inj hL (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
    (fun a b h => by simpa using h)

theorem ιS_inj (i : SIdx D) (a : Option (Fin W)) : Function.Injective (ιS hL i a) :=
  emb_inj hL (by cases a <;> intro x y h <;> fin_cases x <;> fin_cases y <;> simp_all [arrSlot])
    (fun a b h => by simpa using h)

theorem ιX_inj {t s : Fin W} (hts : t ≠ s) : Function.Injective (ιX hL t s) :=
  emb_inj hL (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [eq_comm])
    (fun a b h => by simpa using h)

theorem ιD_inj (ij : Fin m × Fin m) : Function.Injective (ιD hL ij) :=
  emb_inj hL (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
    (fun a b h => by simpa using h)

theorem ιR_inj : Function.Injective (ιR hL) :=
  emb_inj hL (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
    (fun a b h => by simpa using h)

theorem elim_slot_inj : Function.Injective (Sum.elim ![.io, .rsz] Slot.role : Fin 2 ⊕ Fin W → Slot W) := by
  refine Function.Injective.sumElim (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
    (fun a b h => Slot.role.inj h) ?_
  intro a b
  fin_cases a <;> simp

theorem ιDi_inj : Function.Injective (ιDi hL) :=
  emb_inj hL elim_slot_inj (fun a b h => by simpa using h)

theorem ιMe_inj : Function.Injective (ιMe hL) :=
  emb_inj hL elim_slot_inj (fun a b h => by simpa using h)

/-! ## Programs -/

/-- Level `0`: mark `tmp2`, digit-pair swap `io → tmp2`, transfer back to `io`, pop the mark. -/
noncomputable def baseP : Prog (KK hL) (fun _ => Sym) (RG hL) :=
  .seq ((pushC (slotK hL .tmp2) Sym.mark).liftRegs (lr hL))
    (.seq (callInj (ιB hL) (lB hL) (pkB q).P)
      (.seq ((xfer (slotK hL .tmp2) (slotK hL .io) (slotK hL .tmp)).liftRegs (lr hL))
        ((popR (slotK hL .tmp2)).liftRegs (lr hL))))

/-- A stream macro on the array of `arrSlot a`: its elementary kernels in order. -/
noncomputable def streamP (o : Fin D.nOps) (a : Option (Fin W)) : Prog (KK hL) (fun _ => Sym) (RG hL) :=
  forEachProg (List.finRange (D.ops o).length)
    (fun pos => callInj (ιS hL ⟨o, pos⟩ a) (lS hL ⟨o, pos⟩) (pkS hL ⟨o, pos⟩).P)

/-- A gate: its elementary XORs in order. -/
noncomputable def gateP (g : Fin D.nG) : Prog (KK hL) (fun _ => Sym) (RG hL) :=
  forEachProg (D.gates g) (fun p => callInj (ιX hL p.1 p.2) (lX hL) (pkX hL).P)

noncomputable def descP (i j : Fin m) : Prog (KK hL) (fun _ => Sym) (RG hL) :=
  callInj (ιD hL (i, j)) (lD hL (i, j)) (pkD hL (i, j)).P

noncomputable def rowszP : Prog (KK hL) (fun _ => Sym) (RG hL) := callInj (ιR hL) (lR hL) (pkR hL).P

noncomputable def distP : Prog (KK hL) (fun _ => Sym) (RG hL) := callInj (ιDi hL) (lDi hL) (pkDi W).P

noncomputable def mergeP : Prog (KK hL) (fun _ => Sym) (RG hL) := callInj (ιMe hL) (lMe hL) (pkMe W D.ρ).P

theorem closed_baseP : (baseP hL).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, pushC, Prog.FreeBelow]),
    closed_callInj _ _ (pkB q).closed,
    WP.W9comp.closed_liftRegs _ (closed_xfer _ _ _),
    WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, popR, Prog.FreeBelow])⟩

theorem closed_streamP (o : Fin D.nOps) (a : Option (Fin W)) : (streamP hL o a).Closed :=
  freeBelow_forEachProg 0 _ _ (fun _ _ => closed_callInj _ _ (pkS hL _).closed)

theorem closed_gateP (g : Fin D.nG) : (gateP hL g).Closed :=
  freeBelow_forEachProg 0 _ _ (fun _ _ => closed_callInj _ _ (pkX hL).closed)

/-! ## Role-stack lemmas for `roleOfK` -/

theorem setRoles_noneK (F : KK hL → List Sym) (f : Fin W → List Sym) (key : KK hL)
    (h : roleOfK hL key = none) : setRoles (roleOfK hL) F f key = F key := by
  simp only [setRoles, h]

theorem setRoles_roleK (F : KK hL → List Sym) (f : Fin W → List Sym) (r : Fin W) :
    setRoles (roleOfK hL) F f (slotK hL (.role r)) = f r := rfl

/-! ## Specs of the single calls -/

theorem rowszP_spec (k N1 G B : ℕ) (S : KK hL → List Sym) (hN1 : 1 ≤ N1) (hG : 1 ≤ G)
    (hB : 1 ≤ B) (hctr : CtrOK (slotK hL) S k N1 G B) :
    Runs (rowszP hL) S (Function.update S (slotK hL .rsz)
      (natSyms (rowSize q m k N1 G B) ++ Sym.mark :: S (slotK hL .rsz))) (fun _ => True)
      ((pkR hL).C * (rowSize q m k N1 G B + 1)) := by
  obtain ⟨r1, r3, r4, r5, t1, t3, t4, t5, e1, e3, e4, e5⟩ := hctr
  refine runs_callInj_le (Q := fun _ => True) (ιR_inj hL) _ ?_ ?_ le_rfl
  · rw [show slotK hL .rsz = ιR hL (.inl 0) from rfl,
      Function.update_comp_eq_of_injective S (ιR_inj hL) (.inl 0)]
    exact (pkR hL).spec k N1 G B r1 r3 r4 r5 (S ∘ ιR hL) hN1 hG hB t1 t3 t4 t5 e1 e3 e4 e5
  · intro key hk
    exact Function.update_of_ne (fun h => hk (.inl 0) h.symm) _ _

theorem descP_spec (i j : Fin m) (k N1 G B : ℕ) (S : KK hL → List Sym) (hk : 1 ≤ k)
    (hN1 : 1 ≤ N1) (hG : 1 ≤ G) (hB : 1 ≤ B) (hctr : CtrOK (slotK hL) S k N1 G B) :
    Runs (descP hL i j) S (descPost (slotK hL) q m i j k N1 G B S) (fun _ => True)
      ((pkD hL (i, j)).C * (rowSize q m k N1 G B + 1)) := by
  obtain ⟨r1, r3, r4, r5, t1, t3, t4, t5, e1, e3, e4, e5⟩ := hctr
  have hι := ιD_inj hL (i, j)
  refine runs_callInj_le (Q := fun _ => True) hι _ ?_ ?_ le_rfl
  · simp only [descPost]
    rw [show slotK hL .cB = ιD hL (i, j) (.inl 3) from rfl,
      Function.update_comp_eq_of_injective _ hι,
      show slotK hL .cG = ιD hL (i, j) (.inl 2) from rfl,
      Function.update_comp_eq_of_injective _ hι,
      show slotK hL .cN1 = ιD hL (i, j) (.inl 1) from rfl,
      Function.update_comp_eq_of_injective _ hι,
      show slotK hL .ck = ιD hL (i, j) (.inl 0) from rfl,
      Function.update_comp_eq_of_injective _ hι]
    exact (pkD hL (i, j)).spec k N1 G B r1 r3 r4 r5 (S ∘ ιD hL (i, j)) hk hN1 hG hB t1 t3 t4 t5
      e1 e3 e4 e5
  · intro key hk'
    simp only [descPost]
    rw [Function.update_of_ne (a' := slotK hL .cB) (fun h => hk' (.inl 3) h.symm),
      Function.update_of_ne (a' := slotK hL .cG) (fun h => hk' (.inl 2) h.symm),
      Function.update_of_ne (a' := slotK hL .cN1) (fun h => hk' (.inl 1) h.symm),
      Function.update_of_ne (a' := slotK hL .ck) (fun h => hk' (.inl 0) h.symm)]

theorem distP_spec (s Rt : ℕ) (v : List (List Bool)) (rest r1 : List Sym) (S : KK hL → List Sym)
    (hv : v.length = Rt * s) (hrest : BlkTerm rest) (hr1 : TermOK r1)
    (hS : S (slotK hL .io) = arrSyms v ++ rest) (hR : S (slotK hL .rsz) = natSyms s ++ r1) :
    Runs (distP hL) S (setRoles (roleOfK hL) (Function.update S (slotK hL .io) rest)
      fun r => arrSyms (roleBlocks W r.val s v) ++ S (slotK hL (.role r))) (fun _ => True)
      ((pkDi W).C * (vol v + 1)) := by
  have hio_rsz : slotK hL .rsz ≠ slotK hL .io := fun h => by simp [slotK] at h
  refine runs_callInj_le (Q := fun _ => True) (ιDi_inj hL) _ ?_ ?_ le_rfl
  · have e : (setRoles (roleOfK hL) (Function.update S (slotK hL .io) rest)
        fun r => arrSyms (roleBlocks W r.val s v) ++ S (slotK hL (.role r))) ∘ ιDi hL =
        distBlkPost s v rest (S ∘ ιDi hL) := by
      funext x
      rcases x with (i | w) | e
      · fin_cases i
        · show setRoles (roleOfK hL) (Function.update S (slotK hL .io) rest) _ (slotK hL .io) = rest
          rw [setRoles_noneK hL _ _ _ rfl, Function.update_self]
        · show setRoles (roleOfK hL) (Function.update S (slotK hL .io) rest) _ (slotK hL .rsz) =
            S (slotK hL .rsz)
          rw [setRoles_noneK hL _ _ _ rfl, Function.update_of_ne hio_rsz]
      · rfl
      · show setRoles (roleOfK hL) (Function.update S (slotK hL .io) rest) _
            (.inr (.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))))))) = _
        rw [setRoles_noneK hL _ _ _ rfl, Function.update_of_ne (fun h => by simp [slotK] at h)]
        rfl
    rw [e]
    exact (pkDi W).spec Rt s v rest r1 (S ∘ ιDi hL) hv hrest hr1 hS hR
  · intro key hk
    rcases hr : roleOfK hL key with _ | r
    · rw [setRoles_noneK hL _ _ _ hr,
        Function.update_of_ne (a' := slotK hL .io) (fun h => hk (.inl (.inl 0)) h.symm)]
    · exact absurd (roleOfK_eq_some hL key r hr).symm (hk (.inl (.inr r)))

theorem mergeP_spec (g s : ℕ) (us : Fin W → List (List Bool)) (rests : Fin W → List Sym)
    (r1 : List Sym) (S : KK hL → List Sym) (hus : ∀ r, (us r).length = g * s)
    (hrests : ∀ r, BlkTerm (rests r)) (hr1 : TermOK r1)
    (hS : ∀ r, S (slotK hL (.role r)) = arrSyms (us r) ++ rests r)
    (hR : S (slotK hL .rsz) = natSyms s ++ r1) :
    Runs (mergeP hL) S (setRoles (roleOfK hL) (Function.update S (slotK hL .io)
      (arrSyms (mergeBlocks W D.ρ g s us) ++ S (slotK hL .io))) rests) (fun _ => True)
      ((pkMe W D.ρ).C * (∑ r, vol (us r) + 1)) := by
  have hio_rsz : slotK hL .rsz ≠ slotK hL .io := fun h => by simp [slotK] at h
  refine runs_callInj_le (Q := fun _ => True) (ιMe_inj hL) _ ?_ ?_ (le_of_eq (by rw [Fin.sum_univ_def]))
  · have e : (setRoles (roleOfK hL) (Function.update S (slotK hL .io)
        (arrSyms (mergeBlocks W D.ρ g s us) ++ S (slotK hL .io))) rests) ∘ ιMe hL =
        mergeBlkPost D.ρ g s us rests (S ∘ ιMe hL) := by
      funext x
      rcases x with (i | w) | e
      · fin_cases i
        · show setRoles (roleOfK hL) _ rests (slotK hL .io) = _
          rw [setRoles_noneK hL _ _ _ rfl, Function.update_self]
          rfl
        · show setRoles (roleOfK hL) _ rests (slotK hL .rsz) = S (slotK hL .rsz)
          rw [setRoles_noneK hL _ _ _ rfl, Function.update_of_ne hio_rsz]
      · rfl
      · show setRoles (roleOfK hL) _ rests
            (.inr (.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))))))) = _
        rw [setRoles_noneK hL _ _ _ rfl, Function.update_of_ne (fun h => by simp [slotK] at h)]
        rfl
    rw [e]
    exact (pkMe W D.ρ).spec g s us rests r1 (S ∘ ιMe hL) hus hrests hr1 hS hR
  · intro key hk
    rcases hr : roleOfK hL key with _ | r
    · rw [setRoles_noneK hL _ _ _ hr,
        Function.update_of_ne (a' := slotK hL .io) (fun h => hk (.inl (.inl 0)) h.symm)]
    · exact absurd (roleOfK_eq_some hL key r hr).symm (hk (.inl (.inr r)))

end Spec

end SubNLogN.Machine.C5
