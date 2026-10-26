import WP.W4o.RouteBody

/-!
# WP.W4o.RoutePhases — phases 2, 3 and 4 of a router node (explicit `st9` records)
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- For odd `w` the low bit of `B + w` is the complement of the low bit of `B`. -/
theorem addT_head_odd (β : Bool) (B' : List Bool) (w : ℕ) (hw : w % 2 = 1) :
    addT false (β :: B') (encodeNat w) false =
      (!β) :: (addT false (β :: B') (encodeNat w) false).tail := by
  rw [encodeNat_odd w hw]
  cases β <;> rfl

theorem length_flatten_reverse (L : List (List Sym)) :
    L.reverse.flatten.length = L.flatten.length := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    simp only [List.reverse_cons, List.flatten_append, List.length_append, ih, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    omega

/-- **Phase 2.** -/
theorem phase2_eval (β : Bool) (ρ : List (RProg L54)) (r : Reg) (B' : List Bool) (w : ℕ)
    (hw : w % 2 = 1) (r3 : List Sym) (hr3 : TermOK r3) (v1 : List (List Sym))
    (hv1 : ∀ x ∈ v1, RecOK x) (rest y k Rb a b t u : List Sym) :
    ∃ r' tm, tm ≤ 15 * (B'.length + 1) + 4 * v1.flatten.length + 15 ∧
      Eval ρ (phase2 β)
        ⟨r, st9 rest y k (natSyms w ++ r3) (B'.map Sym.bit ++ Sym.mark :: Rb) a
          (v1.flatten.reverse ++ Sym.mark :: b) t u⟩
        ⟨r', st9 (v1.flatten ++ rest) (Sym.mark :: y) k (natSyms w ++ r3)
          ((addT false (β :: B') (encodeNat w) false).tail.map Sym.bit ++ Sym.mark :: Rb) a b t u⟩
        tm := by
  have hC := addT_head_odd β B' w hw
  set C := addT false (β :: B') (encodeNat w) false with hCdef
  have e1 := eval_pushK ρ sBs (Sym.bit β) r (st9 rest y k (natSyms w ++ r3)
    (B'.map Sym.bit ++ Sym.mark :: Rb) a (v1.flatten.reverse ++ Sym.mark :: b) t u)
  simp only [upd_Bs, st9_Bs] at e1
  obtain ⟨r2, t2, ht2, e2⟩ := addTP_eval false (X := sBs) (U := sW) (T := sT) (V := sV)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ρ r (β :: B')
    (encodeNat w) (Sym.mark :: Rb) r3 (TermOK.cons rfl _) hr3 (st9 rest y k (natSyms w ++ r3)
      (Sym.bit β :: (B'.map Sym.bit ++ Sym.mark :: Rb)) a (v1.flatten.reverse ++ Sym.mark :: b)
      t u) rfl rfl
  simp only [upd_Bs] at e2
  rw [← hCdef] at e2
  have hBs : C.map Sym.bit ++ Sym.mark :: Rb =
      Sym.bit (!β) :: (C.tail.map Sym.bit ++ Sym.mark :: Rb) := by
    rw [hC]
    rfl
  have e3 := eval_dropT ρ sBs r2 (st9 rest y k (natSyms w ++ r3) (C.map Sym.bit ++ Sym.mark :: Rb)
    a (v1.flatten.reverse ++ Sym.mark :: b) t u) (Sym.bit (!β))
    (C.tail.map Sym.bit ++ Sym.mark :: Rb) hBs
  simp only [upd_Bs] at e3
  have e4 := moveAll_eval (src := sB) (dst := sX) (by decide) ρ r2 v1.flatten.reverse
    (Sym.mark :: b) (st9 rest y k (natSyms w ++ r3) (C.tail.map Sym.bit ++ Sym.mark :: Rb) a
      (v1.flatten.reverse ++ Sym.mark :: b) t u) (recSyms_rev (recSyms_flatten hv1)) rfl rfl
  simp only [upd_B, upd_X, st9_X, List.reverse_reverse] at e4
  have e5 := eval_dropT ρ sB (some Sym.mark, r2.2) (st9 (v1.flatten ++ rest) y k
    (natSyms w ++ r3) (C.tail.map Sym.bit ++ Sym.mark :: Rb) a (Sym.mark :: b) t u) Sym.mark b rfl
  simp only [upd_B] at e5
  have e6 := eval_pushK ρ sY Sym.mark (some Sym.mark, r2.2) (st9 (v1.flatten ++ rest) y k
    (natSyms w ++ r3) (C.tail.map Sym.bit ++ Sym.mark :: Rb) a b t u)
  simp only [upd_Y, st9_Y] at e6
  refine ⟨_, _, ?_, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))⟩
  simp only [List.length_reverse, List.length_cons] at ht2 ⊢
  omega

/-- **Phase 3.** -/
theorem phase3_eval (β : Bool) (ρ : List (RProg L54)) (r : Reg) (B' : List Bool) (w : ℕ)
    (hw : w % 2 = 1) (r3 : List Sym) (hr3 : TermOK r3) (x y k Rb a b t u : List Sym) :
    ∃ r' tm, tm ≤ 15 * (B'.length + 1) + 10 ∧
      Eval ρ (phase3 β)
        ⟨r, st9 x y k (natSyms w ++ r3)
          ((addT false (β :: B') (encodeNat w) false).tail.map Sym.bit ++ Sym.mark :: Rb) a b t u⟩
        ⟨r', st9 x y k (natSyms w ++ r3) ((β :: B').map Sym.bit ++ Sym.mark :: Rb) a b t u⟩ tm := by
  have hC := addT_head_odd β B' w hw
  set C := addT false (β :: B') (encodeNat w) false with hCdef
  have e1 := eval_pushK ρ sBs (Sym.bit (!β)) r (st9 x y k (natSyms w ++ r3)
    (C.tail.map Sym.bit ++ Sym.mark :: Rb) a b t u)
  simp only [upd_Bs, st9_Bs] at e1
  have hBs : Sym.bit (!β) :: (C.tail.map Sym.bit ++ Sym.mark :: Rb) =
      C.map Sym.bit ++ Sym.mark :: Rb := by
    rw [hC]
    rfl
  rw [hBs] at e1
  obtain ⟨r2, t2, ht2, e2⟩ := addTP_eval true (X := sBs) (U := sW) (T := sT) (V := sV)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ρ r C
    (encodeNat w) (Sym.mark :: Rb) r3 (TermOK.cons rfl _) hr3 (st9 x y k (natSyms w ++ r3)
      (C.map Sym.bit ++ Sym.mark :: Rb) a b t u) rfl rfl
  simp only [upd_Bs] at e2
  rw [hCdef, addT_round] at e2
  refine ⟨_, _, ?_, Eval.seq e1 e2⟩
  have hlen : C.length = B'.length + 1 := by rw [hCdef, length_addT, List.length_cons]
  rw [hlen] at ht2
  omega

/-- **Phase 4**: separate the two outputs and interleave them. -/
theorem phase4_eval (ρ : List (RProg L54)) (r : Reg) (E O : List (List Sym))
    (hEO : O.length = E.length) (hE : ∀ x ∈ E, RecOK x) (hO : ∀ x ∈ O, RecOK x)
    (x y k w bs a b t u : List Sym) :
    ∃ r' tm, tm ≤ 8 * (O.flatten.length + E.flatten.length) + 2 * O.length + 12 ∧
      Eval ρ phase4
        ⟨r, st9 x (O.flatten ++ Sym.mark :: (E.flatten ++ Sym.mark :: y)) k w bs a b t u⟩
        ⟨r', st9 x ((inter E O).flatten ++ y) k w bs a b t u⟩ tm := by
  have e1 := eval_pushK ρ sA Sym.mark r
    (st9 x (O.flatten ++ Sym.mark :: (E.flatten ++ Sym.mark :: y)) k w bs a b t u)
  simp only [upd_A, st9_A] at e1
  have e2 := moveAll_eval (src := sY) (dst := sA) (by decide) ρ r O.flatten
    (Sym.mark :: (E.flatten ++ Sym.mark :: y))
    (st9 x (O.flatten ++ Sym.mark :: (E.flatten ++ Sym.mark :: y)) k w bs (Sym.mark :: a) b t u)
    (recSyms_flatten hO) rfl rfl
  simp only [upd_A, upd_Y, st9_A] at e2
  have e3 := eval_dropT ρ sY (some Sym.mark, r.2)
    (st9 x (Sym.mark :: (E.flatten ++ Sym.mark :: y)) k w bs (O.flatten.reverse ++ Sym.mark :: a)
      b t u) Sym.mark (E.flatten ++ Sym.mark :: y) rfl
  simp only [upd_Y] at e3
  have e4 := eval_pushK ρ sB Sym.mark (some Sym.mark, r.2)
    (st9 x (E.flatten ++ Sym.mark :: y) k w bs (O.flatten.reverse ++ Sym.mark :: a) b t u)
  simp only [upd_B, st9_B] at e4
  have e5 := moveAll_eval (src := sY) (dst := sB) (by decide) ρ (some Sym.mark, r.2) E.flatten
    (Sym.mark :: y) (st9 x (E.flatten ++ Sym.mark :: y) k w bs (O.flatten.reverse ++ Sym.mark :: a)
      (Sym.mark :: b) t u) (recSyms_flatten hE) rfl rfl
  simp only [upd_B, upd_Y, st9_B] at e5
  have e6 := eval_dropT ρ sY (some Sym.mark, (some Sym.mark, r.2).2)
    (st9 x (Sym.mark :: y) k w bs (O.flatten.reverse ++ Sym.mark :: a)
      (E.flatten.reverse ++ Sym.mark :: b) t u) Sym.mark y rfl
  simp only [upd_Y] at e6
  have hO' : ∀ z ∈ O.reverse, RecOK z := fun z hz => hO z (List.mem_reverse.mp hz)
  have hE' : ∀ z ∈ E.reverse, RecOK z := fun z hz => hE z (List.mem_reverse.mp hz)
  have e7 := interL_eval (P := sA) (Q := sB) (Y := sY) (by decide) (by decide) (by decide) ρ
    (some Sym.mark, (some Sym.mark, r.2).2) (Sym.mark :: a) (Sym.mark :: b) rfl rfl O.reverse
    E.reverse (st9 x y k w bs (O.flatten.reverse ++ Sym.mark :: a)
      (E.flatten.reverse ++ Sym.mark :: b) t u) (by simp [hEO]) hO' hE'
    (by rw [st9_A, flatten_reverse_eq])
    (by rw [st9_B, flatten_reverse_eq])
  simp only [upd_A, upd_B, upd_Y, st9_Y] at e7
  rw [inter_rev O E hEO] at e7
  have e8 := eval_dropT ρ sA ((Sym.mark :: a).head?, (some Sym.mark, (some Sym.mark, r.2).2).2)
    (st9 x ((inter E O).flatten ++ y) k w bs (Sym.mark :: a) (Sym.mark :: b) t u) Sym.mark a rfl
  simp only [upd_A] at e8
  have e9 := eval_dropT ρ sB ((Sym.mark :: a).head?, (some Sym.mark, (some Sym.mark, r.2).2).2)
    (st9 x ((inter E O).flatten ++ y) k w bs a (Sym.mark :: b) t u) Sym.mark b rfl
  simp only [upd_B] at e9
  refine ⟨_, _, ?_, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 e9)))))))⟩
  simp only [length_flatten_reverse, List.length_reverse]
  omega

#assert_std_axioms addT_head_odd length_flatten_reverse phase2_eval phase3_eval phase4_eval

end TMFw.W4o
