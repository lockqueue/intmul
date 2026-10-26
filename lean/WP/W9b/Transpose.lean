import WP.W9b.Emit
import WP.W9b.Bridge
import Contracts.Machine.W4

/-!
# WP.W9b.Transpose — `W9_preTranspose` (PRE phase P1) from `W4_transpose .down .up`

`W0 = ⟦x⟧` (the node, `N = t1·r` entries) becomes the row-major `xRows = w9XRows t1 r x`.

**Program** (local stacks `TStk`, the W4 program `P4` as a parameter, rule 6):
1. guards on `D`, `A`, `B`; `B := log t1`, `A := log r` (header fields 4, 5 of `C0`);
2. `P4` with source `W0`, destination `D`, exponents `a = log r` (`A`) and `b = log t1` (`B`):
   `D := blk .up (transposeL (2^a) (2^b) v) ++ D`, `W0 := []`;
3. move `D → W0` up to the guard (this turns `.up` into `.down`); drop `A`, `B`; pop the guards.

**Value.** `blk .down (transposeL r t1 (x.toList.map entrySyms)) = matSyms (w9XRows t1 r x)`
(`matSyms_w9XRows`, the pure P1 bridge in `WP.W9b.Bridge`).

**Cost.** W4's `C4·(|⟦x⟧|+1)·(min a b + 1) + C4·(|a|+|b|+1)` plus `O(|⟦x⟧| + hdrLen + log t1 +
log r)`; total `≤ (C4 + 40)·preTransposeBound`.
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Program -/

/-- Local stacks of the P1 kernel; `s i` are the W4 program's scratch stacks. -/
inductive TStk
  | W0 | C0 | D | A | B | H | s (i : Fin 4)
  deriving DecidableEq

/-- Registers: the macros' symbol register and the W4 program's registers. -/
abbrev TReg (R4 : Type) := Option Sym × R4

/-- A symbol-register macro inside the P1 kernel. -/
def tS {R4 : Type} (p : SProg TStk) : Prog TStk (fun _ => Sym) (TReg R4) :=
  p.liftRegs (Lens.fst _ _)

/-- Named stacks of the W4 call: source `W0`, destination `D`, exponents `A`, `B`. -/
def tNamed : Fin 4 → TStk := fun i =>
  if i.val = 0 then .W0 else if i.val = 1 then .D else if i.val = 2 then .A else .B

/-- Scratch stacks of the W4 call. -/
def tScr {m4 : ℕ} (hm : m4 ≤ 4) : Fin m4 → TStk := fun j => .s (Fin.castLE hm j)

theorem tCall_inj {m4 : ℕ} (hm : m4 ≤ 4) : Function.Injective (embL tNamed (tScr hm)) := by
  refine embL_inj ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [tNamed]
  · intro i j h
    simp only [tScr, TStk.s.injEq] at h
    exact Fin.castLE_inj.mp h
  · intro i j
    fin_cases i <;> simp [tNamed, tScr]

/-- The W4 transpose call. -/
def tCall {m4 : ℕ} {R4 : Type} (P4 : Prog (Loc 4 m4) (fun _ => Sym) R4) (hm : m4 ≤ 4) :
    Prog TStk (fun _ => Sym) (TReg R4) :=
  (P4.mapStk (embL tNamed (tScr hm))).liftRegs (Lens.snd _ _)

/-- **The P1 kernel** (local stacks), parametrized by the W4 transpose program. -/
def tProg {m4 : ℕ} {R4 : Type} (P4 : Prog (Loc 4 m4) (fun _ => Sym) R4) (hm : m4 ≤ 4) :
    Prog TStk (fun _ => Sym) (TReg R4) :=
  .seq (tS (pushC .D .mark)) (.seq (tS (pushC .A .mark)) (.seq (tS (pushC .B .mark))
  (.seq (tS (copyField 4 .C0 .B .H)) (.seq (tS (copyField 5 .C0 .A .H))
  (.seq (tCall P4 hm)
  (.seq (tS (mvG .D .W0))
  (.seq (tS (dropBits .A)) (.seq (tS (popR .A)) (.seq (tS (dropBits .B)) (tS (popR .B)))))))))))

theorem closed_tProg {m4 : ℕ} {R4 : Type} {P4 : Prog (Loc 4 m4) (fun _ => Sym) R4}
    (hm : m4 ≤ 4) (hcl : P4.Closed) : (tProg P4 hm).Closed := by
  refine ⟨closed_liftRegs _ ?_, closed_liftRegs _ ?_, closed_liftRegs _ ?_,
    closed_liftRegs _ (closed_copyField _ _ _ _), closed_liftRegs _ (closed_copyField _ _ _ _),
    closed_liftRegs _ (closed_mapStk _ hcl), closed_liftRegs _ ?_, closed_liftRegs _ ?_,
    closed_liftRegs _ ?_, closed_liftRegs _ ?_, closed_liftRegs _ ?_⟩ <;>
  simp [Prog.Closed, Prog.FreeBelow, pushC, mvG, mvGBody, dropBits, dropBody, popR, pushR, peekR]

/-! ## The W4 call -/

/-- What `W4_transpose .down .up` promises for its program. -/
def TrSpec {m4 : ℕ} {R4 : Type} (P4 : Prog (Loc 4 m4) (fun _ => Sym) R4) (C4 : ℕ) : Prop :=
  ∀ (a b : ℕ) (v : List (List Sym)) (rest r2 r3 : List Sym) (S : Loc 4 m4 → List Sym),
    v.length = 2 ^ a * 2 ^ b → (∀ r ∈ v, RecOK r) → BlkTerm rest → TermOK r2 → TermOK r3 →
    S (.inl 0) = blk .down v ++ rest → S (.inl 2) = natSyms a ++ r2 →
    S (.inl 3) = natSyms b ++ r3 →
    Runs P4 S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (blk .up (transposeL (2 ^ a) (2 ^ b) v) ++ S (.inl 1))) (fun _ => True)
      (C4 * ((blk .down v).length + 1) * (min a b + 1) + C4 * (bitLen a + bitLen b + 1))

theorem rs_tCall {m4 : ℕ} {R4 : Type} {P4 : Prog (Loc 4 m4) (fun _ => Sym) R4} (hm : m4 ≤ 4)
    {C4 : ℕ} (hP : TrSpec P4 C4) (a b : ℕ) (v : List (List Sym)) (r2 r3 : List Sym)
    (S : TStk → List Sym) (hv : v.length = 2 ^ a * 2 ^ b) (hrec : ∀ r ∈ v, RecOK r)
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hW0 : S .W0 = blk .down v)
    (hA : S .A = natSyms a ++ r2) (hB : S .B = natSyms b ++ r3) :
    Runs (tCall P4 hm) S (Function.update (Function.update S .W0 []) .D
        (blk .up (transposeL (2 ^ a) (2 ^ b) v) ++ S .D)) (fun _ => True)
      (C4 * ((blk .down v).length + 1) * (min a b + 1) + C4 * (bitLen a + bitLen b + 1)) := by
  have h := hP a b v [] r2 r3 (fun x => S (embL tNamed (tScr hm) x)) hv hrec
    (fun _ h => by simp at h) hr2 hr3
    (show S .W0 = blk .down v ++ [] by rw [hW0, List.append_nil]) hA hB
  exact runs_lift (Lens.snd _ _) (runs_embed_upd2 (tCall_inj hm) S (.inl 0) (.inl 1) _ _ h)

/-! ## Local specification -/

theorem mem_blkUp_ne_mark (M : Array (Array (ℤ × ℤ))) :
    ∀ y ∈ (matSyms M).reverse, y ≠ Sym.mark := by
  intro y hy
  rw [List.mem_reverse] at hy
  exact mem_blkE_ne_mark _ y hy

/-- **Local specification of the P1 kernel.** -/
theorem tLocal_runs {m4 : ℕ} {R4 : Type} {P4 : Prog (Loc 4 m4) (fun _ => Sym) R4}
    (hm : m4 ≤ 4) {C4 : ℕ} (hP : TrSpec P4 C4) (S : TStk → List Sym) (h : PreHdr)
    (x : Array (ℤ × ℤ)) (r0 : List Sym) (hdims : PreDims h)
    (hC0 : S .C0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0) (hx : x.size = h.N)
    (hW0 : S .W0 = blkE x.toList) :
    Runs (tProg P4 hm) S (Function.update S .W0 (matSyms (w9XRows h.t1 h.r x))) (fun _ => True)
      (26 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length +
        3 * (matSyms (w9XRows h.t1 h.r x)).length + 3 * h.mt1 + 3 * h.mr + 40 +
        (C4 * ((blkE x.toList).length + 1) * (min h.mr h.mt1 + 1) +
          C4 * (bitLen h.mr + bitLen h.mt1 + 1))) := by
  obtain ⟨ht1, hr, h1, h12⟩ := hdims
  set v := x.toList.map entrySyms with hv
  -- guards
  have e0 := runs_lift (Lens.fst (Option Sym) R4) (rs_push TStk.D Sym.mark S)
  set Q1 := Function.update S .D (Sym.mark :: S .D) with hQ1
  have e1 := runs_lift (Lens.fst (Option Sym) R4) (rs_push TStk.A Sym.mark Q1)
  set Q2 := Function.update Q1 .A (Sym.mark :: Q1 .A) with hQ2
  have e2 := runs_lift (Lens.fst (Option Sym) R4) (rs_push TStk.B Sym.mark Q2)
  set Q3 := Function.update Q2 .B (Sym.mark :: Q2 .B) with hQ3
  -- the exponents (header fields 4 and 5 reduce to `log t1` and `log r`)
  have e3 : Runs (tS (R4 := R4) (copyField 4 .C0 .B .H)) Q3
      (Function.update Q3 .B (natSyms h.mt1 ++ Q3 .B)) (fun _ => True)
      (13 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 11) :=
    runs_lift (Lens.fst (Option Sym) R4) (rs_copyField (src := TStk.C0) (dst := TStk.B)
      (tmp := TStk.H) (by decide) (by decide) (by decide) (preTapeFields h.pSub h.m1 h.t1 h.r) 4
      (by simp [preTapeFields]) r0 Q3 (by simp [hQ3, hQ2, hQ1, hC0]))
  set Q4 := Function.update Q3 .B (natSyms h.mt1 ++ Q3 .B) with hQ4
  have e4 : Runs (tS (R4 := R4) (copyField 5 .C0 .A .H)) Q4
      (Function.update Q4 .A (natSyms h.mr ++ Q4 .A)) (fun _ => True)
      (13 * (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length + 11) :=
    runs_lift (Lens.fst (Option Sym) R4) (rs_copyField (src := TStk.C0) (dst := TStk.A)
      (tmp := TStk.H) (by decide) (by decide) (by decide) (preTapeFields h.pSub h.m1 h.t1 h.r) 5
      (by simp [preTapeFields]) r0 Q4 (by simp [hQ4, hQ3, hQ2, hQ1, hC0]))
  set Q5 := Function.update Q4 .A (natSyms h.mr ++ Q4 .A) with hQ5
  -- the W4 transpose
  have hvlen : v.length = 2 ^ h.mr * 2 ^ h.mt1 := by
    rw [hv, List.length_map, show x.toList.length = h.t1 * h.r by simp [hx, PreHdr.N], ← ht1,
      ← hr, Nat.mul_comm]
  have e5 := rs_tCall hm hP h.mr h.mt1 v (Sym.mark :: S .A) (Sym.mark :: S .B) Q5 hvlen
    (by
      intro r hr'
      rw [hv, List.mem_map] at hr'
      obtain ⟨z, -, rfl⟩ := hr'
      exact entrySyms_recOK z)
    (TermOK.cons rfl _) (TermOK.cons rfl _)
    (by simp [hQ5, hQ4, hQ3, hQ2, hQ1, hW0, blkE, hv])
    (by simp [hQ5, hQ4, hQ3, hQ2, hQ1])
    (by simp [hQ5, hQ4, hQ3, hQ2, hQ1])
  have hL : blk .up (transposeL (2 ^ h.mr) (2 ^ h.mt1) v) =
      (matSyms (w9XRows h.t1 h.r x)).reverse := by
    rw [blk_up, ← ht1, ← hr, hv, matSyms_w9XRows h.t1 h.r x ht1
      (by rw [hr]; exact Nat.two_pow_pos _) (hx.trans rfl)]
  rw [hL] at e5
  set Q6 := Function.update (Function.update Q5 .W0 []) .D
    ((matSyms (w9XRows h.t1 h.r x)).reverse ++ Q5 .D) with hQ6
  -- move back
  have e6 := runs_lift (Lens.fst (Option Sym) R4) (rs_mvG (src := TStk.D) (dst := TStk.W0)
    (by decide) (matSyms (w9XRows h.t1 h.r x)).reverse (S .D) Q6 (mem_blkUp_ne_mark _)
    (by simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1]))
  set Q7 := Function.update (Function.update Q6 .D (S .D)) .W0
    ((matSyms (w9XRows h.t1 h.r x)).reverse.reverse ++ Q6 .W0) with hQ7
  -- cleanup
  have e7 := runs_lift (Lens.fst (Option Sym) R4) (rs_dropNat TStk.A h.mr (Sym.mark :: S .A) Q7
    (TermOK.cons rfl _) (by simp [hQ7, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1]))
  set Q8 := Function.update Q7 .A (Sym.mark :: S .A) with hQ8
  have e8 := runs_lift (Lens.fst (Option Sym) R4)
    (rs_pop TStk.A Sym.mark (S .A) Q8 (by simp [hQ8]))
  set Q9 := Function.update Q8 .A (S .A) with hQ9
  have e9 := runs_lift (Lens.fst (Option Sym) R4) (rs_dropNat TStk.B h.mt1 (Sym.mark :: S .B) Q9
    (TermOK.cons rfl _) (by simp [hQ9, hQ8, hQ7, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1]))
  set Q10 := Function.update Q9 .B (Sym.mark :: S .B) with hQ10
  have e10 := runs_lift (Lens.fst (Option Sym) R4)
    (rs_pop TStk.B Sym.mark (S .B) Q10 (by simp [hQ10]))
  have hb1 := bitLen_le_self h.mr
  have hb2 := bitLen_le_self h.mt1
  refine runs_post (runs_seq e0 (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4
    (runs_seq e5 (runs_seq e6 (runs_seq e7 (runs_seq e8 (runs_seq e9 e10)))))))))) ?_ ?_
  · funext k
    cases k <;> simp [hQ10, hQ9, hQ8, hQ7, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1]
  · simp only [List.length_reverse, blkE, hv]
    omega

/-! ## The contract -/

/-- Stack map of the P1 kernel into the layout-B stacks (`8` private scratch stacks). -/
def tι : TStk → BLoc 8
  | .W0 => .inl .W0
  | .C0 => .inl .C0
  | .D => .inr ⟨0, by decide⟩
  | .A => .inr ⟨1, by decide⟩
  | .B => .inr ⟨2, by decide⟩
  | .H => .inr ⟨3, by decide⟩
  | .s i => .inr ⟨i.val + 4, by omega⟩

theorem tι_inj : Function.Injective tι := by
  intro a b h
  cases a <;> cases b <;>
    simp only [tι, Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq, reduceCtorEq] at h <;>
    first
      | rfl
      | (exact absurd h (by decide))
      | omega
      | (congr 1; exact Fin.ext (by omega))

/-- **`W9_preTranspose` holds**, given W4's transpose contract. -/
theorem W9_preTranspose_holds (h4 : W4_transpose .down .up) : W9_preTranspose := by
  obtain ⟨C4, hC4⟩ := h4
  obtain ⟨m4, R4, _, P4, hm4, hfin, hne, hcl, hspec⟩ := hC4 ()
  haveI := hfin
  obtain ⟨r4⟩ := hne
  refine ⟨C4 + 40, fun _ => ⟨8, TReg R4, (tProg P4 hm4).mapStk tι, by decide, inferInstance,
    ⟨(none, r4)⟩, closed_mapStk _ (closed_tProg hm4 hcl), ?_⟩⟩
  intro h w x σ hdims hctx hx hxw hxr hW0
  obtain ⟨⟨r0, hC0⟩, -⟩ := hctx
  have hP : TrSpec P4 C4 := hspec
  have hloc := tLocal_runs hm4 hP (fun k => σ (tι k)) h x r0 hdims hC0 hx hW0
  refine runs_mono (runs_embed_upd tι_inj σ TStk.W0 _ hloc) (fun _ _ => trivial) ?_
  -- cost
  have hb : (blkE x.toList).length ≤ h.N * eb w := by
    have := length_blkE_le w x.toList hxw
    rwa [show x.toList.length = h.N by simp [hx]] at this
  have hm : (matSyms (w9XRows h.t1 h.r x)).length ≤ h.N * eb w :=
    length_matSyms_le w h.t1 h.r _ (w9XRows_size _ _ _) (w9XRows_rows _ _ _) hxr
  have hH : (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length ≤ h.hdrLen := by
    unfold PreHdr.hdrLen
    omega
  have hb1 := bitLen_le_self h.mr
  have hb2 := bitLen_le_self h.mt1
  have hmin : min h.mr h.mt1 = min h.mt1 h.mr := Nat.min_comm _ _
  rw [hmin]
  have hX1 : C4 * ((blkE x.toList).length + 1) * (min h.mt1 h.mr + 1) ≤
      C4 * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  have hX2 : C4 * (bitLen h.mr + bitLen h.mt1 + 1) ≤ C4 * (h.mt1 + h.mr + h.hdrLen + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hX3 : h.N * eb w + 1 ≤ (h.N * eb w + 1) * (min h.mt1 h.mr + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hexp : (C4 + 40) * preTransposeBound w h =
      C4 * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) + C4 * (h.mt1 + h.mr + h.hdrLen + 1) +
        40 * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) + 40 * (h.mt1 + h.mr + h.hdrLen + 1) := by
    unfold preTransposeBound
    ring
  rw [hexp]
  omega

#assert_std_axioms tCall_inj closed_tProg rs_tCall mem_blkUp_ne_mark tLocal_runs tι_inj
  W9_preTranspose_holds

end WP.W9b
