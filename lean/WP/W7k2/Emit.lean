import WP.W7k2.Ops2

/-!
# WP.W7k2.Emit — moving signed numbers, emitting header fields, moving a block

Generic host-level sub-programs used by the table builder:

| Program | Effect (top of stack first) |
|---|---|
| `moveInt X Y` | `X = intSyms z ++ rx` ↦ `X = rx`, `Y = intSyms z ++ Y` |
| `pushField X F` | `X = W7.field v ++ X` for `F = natSyms v ++ _` |
| `emitHeader X Fs` | `X = W7.header [v₁, …, vₘ] ++ X` for field stacks `Fs` |
| `moveBlock X Y` | `X = seg ++ mark :: rest` (no `mark` in `seg`) ↦ `X = rest`, `Y = seg.reverse ++ Y` |
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

variable {a b : ℕ} {σ : Type}

/-! ## Moving a signed number -/

/-- Move the signed number on top of `X` onto `Y`. -/
def moveInt (Icp : Inst 2 4 Unit) (Idr : Inst 1 4 Unit) (lS : Lens σ (Option Sym))
    (lcp : Lens σ Icp.R) (ldr : Lens σ Idr.R) (X Y dflt : Loc a b) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  ((popR' lS X).seq (.ite (fun v => decide (lS.get v = some Sym.neg))
      ((callI Icp [X, Y] dflt lcp).seq (pushS Y .neg))
      ((callI Icp [X, Y] dflt lcp).seq (pushS Y .pos)))).seq
    (callI Idr [X] dflt ldr)

theorem moveInt_closed (Icp : Inst 2 4 Unit) (Idr : Inst 1 4 Unit) (lS : Lens σ (Option Sym))
    (lcp : Lens σ Icp.R) (ldr : Lens σ Idr.R) (X Y dflt : Loc a b) :
    (moveInt Icp Idr lS lcp ldr X Y dflt).Closed :=
  ⟨⟨trivial, ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩⟩,
    callI_closed _ _ _ _⟩

theorem sgnSym_eq_pos_of_ne {z : ℤ} (h : sgnSym z ≠ .neg) : sgnSym z = .pos := by
  unfold sgnSym at h ⊢
  by_cases hz : z < 0
  · rw [if_pos hz] at h
    exact absurd rfl h
  · rw [if_neg hz]

theorem HT.moveInt {Icp : Inst 2 4 Unit} {Idr : Inst 1 4 Unit} {Cc Cd : ℕ}
    (hcp : SpecCopy Icp Cc) (hdr : SpecDrop Idr Cd) (lS : Lens σ (Option Sym))
    (lcp : Lens σ Icp.R) (ldr : Lens σ Idr.R) (X Y dflt : Loc a b) (hXY : X ≠ Y)
    (hcap : 4 + 2 ≤ a + b) (B : Loc a b → List Sym) (z : ℤ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B X = intSyms z ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (moveInt Icp Idr lS lcp ldr X Y dflt)
      (Function.update (Function.update B Y (intSyms z ++ B Y)) X rx)
      (Cc * (bitLen z.natAbs + 1) + Cd * (bitLen z.natAbs + 1) + 3) := by
  have hnd : [X, Y].Nodup := by simp [hXY]
  have hBX : B X = sgnSym z :: (natSyms z.natAbs ++ rx) := by rw [hB]; rfl
  have hcopy := HT.copyNat hcp dflt lcp X Y hnd (by omega)
    (Function.update B X (natSyms z.natAbs ++ rx)) z.natAbs rx hrx (by simp) ρ
  have hbr : ∀ s : Sym, sgnSym z = s →
      HT ρ (Function.update B X (natSyms z.natAbs ++ rx))
        ((callI Icp [X, Y] dflt lcp).seq (WP.W7k2.pushS Y s))
        (Function.update (Function.update B Y (intSyms z ++ B Y)) X (natSyms z.natAbs ++ rx))
        (Cc * (bitLen z.natAbs + 1) + 1) := by
    intro s hs
    refine (HT.seq hcopy (HT.pushS Y s _ ρ)).of_eq ?_ le_rfl
    funext g
    by_cases hgY : g = Y
    · rw [hgY]
      simp [Ne.symm hXY, intSyms, hs]
    · by_cases hgX : g = X
      · rw [hgX]
        simp [Function.update_apply, hXY]
      · simp [Function.update_apply, hgX, hgY]
  refine (HT.seq (HT.popBranch lS X B _ (sgnSym z) _ hBX
    (fun o => decide (o = some Sym.neg)) _ _ ρ
    (fun h => hbr .neg (by simpa using h))
    (fun h => hbr .pos (sgnSym_eq_pos_of_ne (by simpa using h))))
    (HT.dropNat hdr dflt ldr X (by omega) _ z.natAbs rx hrx (by simp) ρ)).of_eq
    (by rw [Function.update_idem]) (by simp only [max_self]; omega)

/-! ## Header fields -/

/-- Push `W7.field v` (`natSyms v ++ [sep]`) onto `X`, reading `v` from `F`. -/
def pushField (Icp : Inst 2 4 Unit) (lcp : Lens σ Icp.R) (X F dflt : Loc a b) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  (pushS X .sep).seq (callI Icp [F, X] dflt lcp)

theorem HT.pushField {Icp : Inst 2 4 Unit} {Cc : ℕ} (hcp : SpecCopy Icp Cc) (lcp : Lens σ Icp.R)
    (X F dflt : Loc a b) (hFX : F ≠ X) (hcap : 4 + 2 ≤ a + b) (B : Loc a b → List Sym) (v : ℕ)
    (rF : List Sym) (hrF : TermOK rF) (hB : B F = natSyms v ++ rF)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (pushField Icp lcp X F dflt) (Function.update B X (W7.field v ++ B X))
      (1 + Cc * (bitLen v + 1)) := by
  refine (HT.seq (HT.pushS X .sep B ρ) (HT.copyNat hcp dflt lcp F X (by simp [hFX]) hcap _ v rF hrF
    (by simp [hFX, hB]) ρ)).of_eq ?_ le_rfl
  simp [Function.update_idem, W7.field]

/-- Emit the fields read from `Fs` onto `X`, last field first. -/
def emitFields (Icp : Inst 2 4 Unit) (lcp : Lens σ Icp.R) (X dflt : Loc a b) :
    List (Loc a b) → Prog (Loc a b) (fun _ => Sym) σ
  | [] => .load id
  | F :: Fs => (emitFields Icp lcp X dflt Fs).seq (pushField Icp lcp X F dflt)

/-- Emit a whole header onto `X`. -/
def emitHeader (Icp : Inst 2 4 Unit) (lcp : Lens σ Icp.R) (X dflt : Loc a b) (Fs : List (Loc a b)) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  (pushS X W7.tagSub).seq (emitFields Icp lcp X dflt Fs)

theorem emitFields_closed (Icp : Inst 2 4 Unit) (lcp : Lens σ Icp.R) (X dflt : Loc a b) :
    ∀ Fs : List (Loc a b), (emitFields Icp lcp X dflt Fs).Closed
  | [] => trivial
  | _ :: Fs => ⟨emitFields_closed Icp lcp X dflt Fs, ⟨trivial, callI_closed _ _ _ _⟩⟩

theorem emitHeader_closed (Icp : Inst 2 4 Unit) (lcp : Lens σ Icp.R) (X dflt : Loc a b)
    (Fs : List (Loc a b)) : (emitHeader Icp lcp X dflt Fs).Closed :=
  ⟨trivial, emitFields_closed Icp lcp X dflt Fs⟩

/-- Cost of emitting the fields `vs`. -/
def fieldsCost (Cc : ℕ) : List ℕ → ℕ
  | [] => 1
  | v :: vs => fieldsCost Cc vs + (1 + Cc * (bitLen v + 1))

theorem HT.emitFields {Icp : Inst 2 4 Unit} {Cc : ℕ} (hcp : SpecCopy Icp Cc) (lcp : Lens σ Icp.R)
    (X dflt : Loc a b) (hcap : 4 + 2 ≤ a + b) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    ∀ (Fs : List (Loc a b)) (vs : List ℕ) (B : Loc a b → List Sym) (hl : Fs.length = vs.length),
      (∀ i (hi : i < Fs.length), Fs[i] ≠ X ∧ ∃ r, TermOK r ∧ B Fs[i] = natSyms (vs[i]'(by omega)) ++ r) →
      HT ρ B (emitFields Icp lcp X dflt Fs) (Function.update B X ((vs.map W7.field).flatten ++ B X))
        (fieldsCost Cc vs)
  | [], [], B, _, _ => by
    rintro ⟨v, S⟩ hS
    change S = B at hS
    subst hS
    refine ⟨⟨v, S⟩, 1, Eval.load ρ id v S, ?_, le_rfl⟩
    show S = Function.update S X ([] ++ S X)
    simp
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | F :: Fs, w :: vs, B, hl, hF => by
    have hl' : Fs.length = vs.length := by simpa using hl
    have h0 := hF 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨hFX, r, hr, hBF⟩ := h0
    have ih := HT.emitFields hcp lcp X dflt hcap ρ Fs vs B hl' (fun i hi => by
      have := hF (i + 1) (by simp only [List.length_cons]; omega)
      simpa using this)
    have hBF' : (Function.update B X ((vs.map W7.field).flatten ++ B X)) F = natSyms w ++ r := by
      simp [hFX, hBF]
    refine (HT.seq ih (HT.pushField hcp lcp X F dflt hFX hcap _ w r hr hBF' ρ)).of_eq ?_ le_rfl
    simp [Function.update_idem]

theorem HT.emitHeader {Icp : Inst 2 4 Unit} {Cc : ℕ} (hcp : SpecCopy Icp Cc) (lcp : Lens σ Icp.R)
    (X dflt : Loc a b) (hcap : 4 + 2 ≤ a + b) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    (Fs : List (Loc a b)) (vs : List ℕ) (B : Loc a b → List Sym) (hl : Fs.length = vs.length)
    (hF : ∀ i (hi : i < Fs.length), Fs[i] ≠ X ∧
      ∃ r, TermOK r ∧ B Fs[i] = natSyms (vs[i]'(by omega)) ++ r) :
    HT ρ B (emitHeader Icp lcp X dflt Fs) (Function.update B X (W7.header vs ++ B X))
      (1 + fieldsCost Cc vs) := by
  have hF' : ∀ i (hi : i < Fs.length), Fs[i] ≠ X ∧
      ∃ r, TermOK r ∧ (Function.update B X (W7.tagSub :: B X)) Fs[i] =
        natSyms (vs[i]'(by omega)) ++ r := fun i hi => by
    obtain ⟨hne, r, hr, he⟩ := hF i hi
    exact ⟨hne, r, hr, by simp [hne, he]⟩
  refine (HT.seq (HT.pushS X W7.tagSub B ρ)
    (HT.emitFields hcp lcp X dflt hcap ρ Fs vs _ hl hF')).of_eq ?_ le_rfl
  simp [Function.update_idem, W7.header]

/-! ## Moving a block (until `mark`) -/

/-- Pop symbols from `X` and push them onto `Y` until a `mark` is popped (the mark is dropped). -/
def moveBlock (lS : Lens σ (Option Sym)) (X Y : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (popR' lS X).seq (.loop (fun v => decide (lS.get v ≠ some Sym.mark))
    ((Prog.push Y (fun v => (lS.get v).getD .sep)).seq (popR' lS X)))

theorem moveBlock_closed (lS : Lens σ (Option Sym)) (X Y : Loc a b) :
    (moveBlock lS X Y).Closed := ⟨trivial, ⟨trivial, trivial⟩⟩

theorem moveBlock_loop (lS : Lens σ (Option Sym)) (X Y : Loc a b) (hXY : X ≠ Y)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (rest : List Sym) :
    ∀ (seg : List Sym), Sym.mark ∉ seg → ∀ (B : Loc a b → List Sym) (v : σ) (h : Sym)
      (t : List Sym), h :: t = seg ++ Sym.mark :: rest → B X = t → lS.get v = some h →
      ∃ v', Eval ρ (.loop (fun v => decide (lS.get v ≠ some Sym.mark))
        ((Prog.push Y (fun v => (lS.get v).getD .sep)).seq (popR' lS X))) ⟨v, B⟩
        ⟨v', Function.update (Function.update B X rest) Y (seg.reverse ++ B Y)⟩
        (3 * seg.length + 1)
  | [], _, B, v, h, t, hht, hBX, hv => by
    simp only [List.nil_append, List.cons.injEq] at hht
    obtain ⟨hh, ht⟩ := hht
    rw [hh] at hv
    refine ⟨v, (Eval.loop_false (by simp [hv])).of_eq ?_ rfl⟩
    have h1 : Function.update B X rest = B := by rw [← ht, ← hBX, Function.update_eq_self]
    simp [h1]
  | x :: seg', hseg, B, v, h, t, hht, hBX, hv => by
    simp only [List.cons_append, List.cons.injEq] at hht
    obtain ⟨hh, ht⟩ := hht
    rw [ht] at hBX
    rw [hh] at hv
    have hx : x ≠ Sym.mark := fun e => hseg (by simp [e])
    have hseg' : Sym.mark ∉ seg' := fun hm => hseg (List.mem_cons_of_mem _ hm)
    obtain ⟨h', t', hht'⟩ : ∃ h' t', h' :: t' = seg' ++ Sym.mark :: rest := by
      cases seg' with
      | nil => exact ⟨Sym.mark, rest, rfl⟩
      | cons y ys => exact ⟨y, ys ++ Sym.mark :: rest, rfl⟩
    have hB1X : (Function.update B Y (x :: B Y)) X = h' :: t' := by
      rw [Function.update_of_ne hXY, hBX, hht']
    have hB2X : (Function.update (Function.update B Y (x :: B Y)) X
        ((Function.update B Y (x :: B Y)) X).tail) X = t' := by
      rw [Function.update_self, hB1X]
      rfl
    obtain ⟨v', e⟩ := moveBlock_loop lS X Y hXY ρ rest seg' hseg'
      (Function.update (Function.update B Y (x :: B Y)) X ((Function.update B Y (x :: B Y)) X).tail)
      (lS.set v ((Function.update B Y (x :: B Y)) X).head?) h' t' hht' hB2X
      (by rw [lS.get_set, hB1X]; rfl)
    have epush : Eval ρ (Prog.push Y (fun v => (lS.get v).getD .sep)) ⟨v, B⟩
        ⟨v, Function.update B Y (x :: B Y)⟩ 1 := by
      refine (Eval.push ρ Y _ v B).of_eq ?_ rfl
      simp [hv]
    have epop := Eval.pop ρ X (fun v o => lS.set v o) v (Function.update B Y (x :: B Y))
    refine ⟨v', (Eval.loop_true (by simp [hv, hx]) (Eval.seq epush epop) e).of_eq ?_ ?_⟩
    · congr 1
      funext g
      by_cases hgY : g = Y
      · rw [hgY]
        simp [Function.update_apply, Ne.symm hXY]
      · by_cases hgX : g = X
        · rw [hgX]
          simp [Function.update_apply, hXY]
        · simp [Function.update_apply, hgX, hgY]
    · simp only [List.length_cons]
      omega

theorem HT.moveBlock (lS : Lens σ (Option Sym)) (X Y : Loc a b) (hXY : X ≠ Y)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (seg rest : List Sym) (hseg : Sym.mark ∉ seg)
    (B : Loc a b → List Sym) (hB : B X = seg ++ Sym.mark :: rest) :
    HT ρ B (moveBlock lS X Y)
      (Function.update (Function.update B X rest) Y (seg.reverse ++ B Y)) (3 * seg.length + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨h, t, hht⟩ : ∃ h t, h :: t = seg ++ Sym.mark :: rest := by
    cases seg with
    | nil => exact ⟨Sym.mark, rest, rfl⟩
    | cons y ys => exact ⟨y, ys ++ Sym.mark :: rest, rfl⟩
  have hSX : S X = h :: t := by rw [hB, hht]
  set S1 := Function.update S X (S X).tail with hS1
  have hS1X : S1 X = t := by rw [hS1, Function.update_self, hSX]; rfl
  obtain ⟨v', e⟩ := moveBlock_loop lS X Y hXY ρ rest seg hseg S1 (lS.set v (S X).head?) h t hht
    hS1X (by rw [lS.get_set, hSX]; rfl)
  refine ⟨⟨v', _⟩, _, Eval.seq (Eval.pop ρ X (fun v o => lS.set v o) v S) e, ?_, ?_⟩
  · show Function.update (Function.update S1 X rest) Y (seg.reverse ++ S1 Y) =
      Function.update (Function.update S X rest) Y (seg.reverse ++ S Y)
    rw [hS1, Function.update_idem, Function.update_of_ne (Ne.symm hXY)]
  · omega

#assert_std_axioms moveInt_closed HT.moveInt HT.pushField emitFields_closed emitHeader_closed
  HT.emitFields HT.emitHeader moveBlock_closed moveBlock_loop HT.moveBlock

end WP.W7k2
