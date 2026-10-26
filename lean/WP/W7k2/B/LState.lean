import WP.W7k2.B.Vals2

/-!
# WP.W7k2.B.LState — level states, the leaf segment and the leaf part

* `Bf S`: the initial stacks `S` with a `mark` floor on every scratch stack but `TT`
  (`marked_floor`: what `pushMarks floorSlots` produces).
* `LS S Lc p K pIn blk tr`: the state at the start of a level — `TR = tr`, the level registers
  `vL vp vK vpI` hold `Lc p K pIn`, `STG` holds the staged (reversed) pre segments `blk`.
* `FS S tr`: the state after the leaf part — `TR = tr`, `STG` back to its initial content.
* `leafPart` (= `leafSeg`, move `STG → TR`, drop the level registers): `LS … → FS …`.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- Scratch stacks carrying a `mark` floor (all but `TT`). -/
def floorSlots : List BL :=
  [vL, vp, vK, vpI, sSTG, sK1, sK2, sPW, sPC, sPS, sT1, sR, sR2, sN1, sW, sNB, sH, sTPc, sPI, sLN,
    y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10]

/-- The floored base state over the initial stacks `S`. -/
def Bf (S : BL → List Sym) : BL → List Sym := fun g =>
  if inNamed floorSlots g = true then Sym.mark :: S g else S g

theorem Bf_floor (S : BL → List Sym) (g : BL) (h : inNamed floorSlots g = true) :
    Bf S g = Sym.mark :: S g := if_pos h

theorem Bf_nofloor (S : BL → List Sym) (g : BL) (h : inNamed floorSlots g = false) :
    Bf S g = S g := by simp [Bf, h]

theorem marked_apply : ∀ (ks : List BL) (S : BL → List Sym), ks.Nodup → ∀ g,
    marked S ks g = if inNamed ks g = true then Sym.mark :: S g else S g
  | [], S, _, g => by simp [marked, inNamed]
  | k :: ks, S, hnd, g => by
    have hk : k ∉ ks := (List.nodup_cons.mp hnd).1
    have hks : ks.Nodup := (List.nodup_cons.mp hnd).2
    simp only [marked]
    rw [marked_apply ks _ hks g]
    by_cases hg : g = k
    · rw [hg]
      have h1 : inNamed ks k = false := by
        cases h : inNamed ks k
        · rfl
        · exact absurd (inNamed_iff.mp h) hk
      have h2 : inNamed (k :: ks) k = true := inNamed_iff.mpr (List.mem_cons_self ..)
      rw [h1, h2]
      simp
    · have h3 : inNamed (k :: ks) g = inNamed ks g := by
        simp [inNamed, Ne.symm hg]
      rw [h3, Function.update_of_ne hg]

theorem marked_floor (S : BL → List Sym) : marked S floorSlots = Bf S :=
  funext fun g => by rw [marked_apply _ _ (by decide) g]; rfl

/-- The state at the start of a level. -/
def LS (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) : BL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Bf S) sTR tr) vL (natSyms Lc ++ Sym.mark :: S vL))
    vp (natSyms p ++ Sym.mark :: S vp)) vK (natSyms K ++ Sym.mark :: S vK))
    vpI (natSyms pIn ++ Sym.mark :: S vpI)) sSTG (blk ++ Sym.mark :: S sSTG)

/-- The state after the leaf part. -/
def FS (S : BL → List Sym) (tr : List Sym) : BL → List Sym :=
  Function.update (Function.update (Bf S) sTR tr) sSTG (S sSTG)

/-- Drop the level registers. -/
def dropRegs (I : BI) : BP I := (bdr I vL).seq <| (bdr I vp).seq <| (bdr I vK).seq (bdr I vpI)

/-- The leaf part: the leaf segment, the staged pre segments onto `TR`, drop the registers. -/
def leafPart (I : BI) : BP I := (leafSeg I).seq <| (bmb I sSTG sTR).seq (dropRegs I)

theorem leafPart_closed (I : BI) : (leafPart I).Closed :=
  ⟨leafSeg_closed I, bmb_closed _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _⟩

/-- Cost of the leaf segment (`leafSeg_spec`). -/
def leafSegCost (C Qb Qk p K pIn : ℕ) : ℕ :=
  8 * (C * Qb) + 9 + (K * (2 ^ K * (C * Qk ^ 4 + 2 * (C * Qk) + 1) + 10 * (C * Qk) + 4 +
    2 * (C * Qb) + 1) + 2 * (C * Qb) + 1 + (1 + fieldsCost C [p, K, 2 * p + K + 8, pIn] +
    (1 + C * (bitLen (2 * p + K + 8) + 1))))

section LState

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem leafSeg_spec (hI : I.Spec Mul C) (pIn p K Qb Qk : ℕ) (B : BL → List Sym)
    (ρ : List (BP I)) (hvp : NatAt B vp p) (hvK : NatAt B vK K) (hvpI : NatAt B vpI pIn)
    (h0 : TermOK (B y0)) (h1 : TermOK (B y1)) (h2 : TermOK (B y2)) (h3 : TermOK (B y3))
    (hPS : TermOK (B sPS)) (hR : TermOK (B sR)) (hR2 : TermOK (B sR2))
    (hQb : bitLen (2 * p + K + 8) + 5 ≤ Qb) (hQk : 2 * p + 2 * K + 40 ≤ Qk) :
    HT ρ B (leafSeg I) (Function.update B sTR (leafSegC pIn p K ++ B sTR))
      (leafSegCost C Qb Qk p K pIn) := by
  have bK : bitLen K ≤ bitLen (2 * p + K + 8) := bitLen_mono (by omega)
  have e1 := leafHead_spec hI p K Qb B ρ hvp hvK h1 h2 h3 hQb
  have e2 := leafStages_spec hI (2 * p + K + 8) K Qk Qb
    (Function.update B sPS (natSyms (2 * p + K + 8) ++ B sPS)) ρ ⟨B sPS, hPS, by simp⟩
    (hvK.upd (by decide) _) (termOK_upd h0 (by decide) _) (termOK_upd h1 (by decide) _)
    (termOK_upd h2 (by decide) _) (termOK_upd hR (by decide) _) (termOK_upd hR2 (by decide) _)
    (by omega) (by omega) (by omega)
  have e3 := leafTail_spec hI p K (2 * p + K + 8) pIn
    (Function.update (Function.update B sPS (natSyms (2 * p + K + 8) ++ B sPS)) sTR
      (((List.range K).map (stageL (2 * p + K + 8))).flatten ++
        (Function.update B sPS (natSyms (2 * p + K + 8) ++ B sPS)) sTR)) ρ
    ((hvp.upd (by decide) _).upd (by decide) _) ((hvK.upd (by decide) _).upd (by decide) _)
    ((hvpI.upd (by decide) _).upd (by decide) _) (B sPS) hPS (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append])
  refine (HT.seq e1 (HT.seq e2 e3)).of_eq ?_ le_rfl
  delta stageL
  simp only [leafSegC, leafSegE]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]

theorem leafPart_spec (hI : I.Spec Mul C) (S : BL → List Sym) (Lc p K pIn : ℕ)
    (blk tr : List Sym) (Qb Qk : ℕ) (ρ : List (BP I)) (hblk : Sym.mark ∉ blk)
    (hQb : bitLen (2 * p + K + 8) + 5 ≤ Qb) (hQk : 2 * p + 2 * K + 40 ≤ Qk) :
    HT ρ (LS S Lc p K pIn blk tr) (leafPart I) (FS S (blk.reverse ++ (leafSegC pIn p K ++ tr)))
      (leafSegCost C Qb Qk p K pIn + (3 * blk.length + 2 + (C * (bitLen Lc + 1) +
        (C * (bitLen p + 1) + (C * (bitLen K + 1) + C * (bitLen pIn + 1)))))) := by
  have e1 := leafSeg_spec hI pIn p K Qb Qk (LS S Lc p K pIn blk tr) ρ
    ⟨Sym.mark :: S vp, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S vK, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S vpI, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) hQb hQk
  have e2 := bmb_spec (I := I) sSTG sTR (by decide) ρ blk (S sSTG) hblk
    (Function.update (LS S Lc p K pIn blk tr) sTR (leafSegC pIn p K ++ LS S Lc p K pIn blk tr sTR))
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor])
  refine (HT.seq e1 <| HT.seq e2 <|
    HT.seq (HT.bdr hI vL _ Lc (Sym.mark :: S vL) (termOK_mark _) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, LS, FS, Function.update_self, Function.update_of_ne,
      Bf_floor, Bf_nofloor]) only [LS, FS, upd_swap, Function.update_idem, upd_eq_self_of,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, List.append_assoc,
      List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bdr hI vp _ p (Sym.mark :: S vp) (termOK_mark _) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, LS, FS, Function.update_self, Function.update_of_ne,
      Bf_floor, Bf_nofloor]) only [LS, FS, upd_swap, Function.update_idem, upd_eq_self_of,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, List.append_assoc,
      List.cons_append, List.nil_append]) ρ) <|
    HT.seq (HT.bdr hI vK _ K (Sym.mark :: S vK) (termOK_mark _) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, LS, FS, Function.update_self, Function.update_of_ne,
      Bf_floor, Bf_nofloor]) only [LS, FS, upd_swap, Function.update_idem, upd_eq_self_of,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, List.append_assoc,
      List.cons_append, List.nil_append]) ρ) <|
    HT.bdr hI vpI _ pIn (Sym.mark :: S vpI) (termOK_mark _) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, LS, FS, Function.update_self, Function.update_of_ne,
      Bf_floor, Bf_nofloor]) only [LS, FS, upd_swap, Function.update_idem, upd_eq_self_of,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, List.append_assoc,
      List.cons_append, List.nil_append]) ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, LS, FS, Function.update_self, Function.update_of_ne,
      Bf_floor, Bf_nofloor]) only [LS, FS, upd_swap, Function.update_idem, upd_eq_self_of,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, List.append_assoc,
      List.cons_append, List.nil_append]) le_rfl

end LState

#assert_std_axioms Bf_floor Bf_nofloor marked_apply marked_floor leafPart_closed leafSeg_spec
  leafPart_spec

end WP.W7k2
