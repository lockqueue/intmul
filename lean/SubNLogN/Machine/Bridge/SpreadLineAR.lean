/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadRunsBlk2
import SubNLogN.Machine.Bridge.SpreadMath4

/-!
# K5 spreading: the AR pieces of one line (`Bridge/SpreadLineAR.lean`)

* `linePre_eval`: build the extended line `Es = X ++ take (W-1) X` from the line's records on
  `arr` (flat moves over the product rulers `pr 0 = (W-1)·recw`, `pr 1 = t·recw`), the zero tails
  (`pr 4 = (W-1)·s` zero bits), and peek `Es`;
* `linePost_eval`: drop the tails, rotate the finalized outputs on `Q` (`pr 2 = a₀·recw`,
  `pr 3 = (t-a₀)·recw`, skip `pr 0`) onto `Out`, so that `Out` receives `lineOut` in order.

Everything is proved.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

/-- The stack symbols of a list of one-coefficient records. -/
def csym (w : ℕ) (L : List CInt) : List Sym := carrSyms w (L.map fun x => [x])

theorem csym_append (w : ℕ) (L1 L2 : List CInt) : csym w (L1 ++ L2) = csym w L1 ++ csym w L2 := by
  simp only [csym, SolveAux.carrSyms_eq_recsOf, List.map_append, SolveAux.recsOf_append]

theorem length_csym (w : ℕ) : ∀ L : List CInt, (csym w L).length = L.length * (2 * w + 1)
  | [] => by simp [csym, SolveAux.carrSyms_eq_recsOf]
  | x :: L => by
    have ih := length_csym w L
    rw [show x :: L = [x] ++ L from rfl, csym_append, List.length_append, ih]
    simp [csym, SolveAux.carrSyms_eq_recsOf, recSyms, crecBits, coefBits, K1.length_twosBits]
    ring

variable {Esu : Type} [DecidableEq Esu]

theorem notField_arr : NotField (Esu := Esu) (kW .arr) := fun _ _ => rfl
theorem notField_T2 : NotField (Esu := Esu) (sp .T2) := fun _ _ => rfl
theorem notField_T4 : NotField (Esu := Esu) (sp .T4) := fun _ _ => rfl
theorem notField_T5 : NotField (Esu := Esu) (sp .T5) := fun _ _ => rfl
theorem notField_P1 : NotField (Esu := Esu) (sp .P1) := fun _ _ => rfl
theorem notField_P2 : NotField (Esu := Esu) (sp .P2) := fun _ _ => rfl
theorem notField_Out : NotField (Esu := Esu) (sp .Out) := fun _ _ => rfl

/-- Build the extended line and the zero tails. -/
def linePre : AProg (SK Esu) :=
  .seq (copy2N (sp (.pr 0)) (sp (.X 2)) (kW .arr) (sp .T4) (sp .T5))
  (.seq (moveN (sp (.pr 0)) (sp (.X 2)) (sp .T5) (kW .arr))
  (.seq (moveN (sp (.pr 1)) (sp (.X 2)) (kW .arr) (sp .T2))
  (.seq (moveN (sp (.pr 0)) (sp (.X 2)) (sp .T4) (sp .Es))
  (.seq (moveN (sp (.pr 1)) (sp (.X 2)) (sp .T2) (sp .Es))
  (.seq (pushN (sp (.pr 4)) (sp (.X 2)) (sp .Tre) (.bit false))
  (.seq (pushN (sp (.pr 4)) (sp (.X 2)) (sp .Tim) (.bit false))
  (peekQ (sp .Es))))))))

/-- Cost bound of `linePre`. -/
def linePreCost (t W wI s : ℕ) : ℕ :=
  (11 * ((W - 1) * (2 * wI + 1)) + 4) + (10 * ((W - 1) * (2 * wI + 1)) + 4) +
    (10 * (t * (2 * wI + 1)) + 4) + (10 * ((W - 1) * (2 * wI + 1)) + 4) +
    (10 * (t * (2 * wI + 1)) + 4) + 2 * (9 * ((W - 1) * s) + 4) + 1

theorem linePre_eval (t W wI s : ℕ) (X : List CInt) (restA q : List Sym) (S0 : SK Esu → List Sym)
    (v : AReg) (hX : X.length = t) (hWt : W ≤ t + 1)
    (harr : S0 (kW .arr) = csym wI X ++ restA) (hT2 : S0 (sp .T2) = []) (hT4 : S0 (sp .T4) = [])
    (hT5 : S0 (sp .T5) = []) (hX2 : S0 (sp (.X 2)) = [])
    (hp0 : S0 (sp (.pr 0)) = List.replicate ((W - 1) * (2 * wI + 1)) .mark)
    (hp1 : S0 (sp (.pr 1)) = List.replicate (t * (2 * wI + 1)) .mark)
    (hp4 : S0 (sp (.pr 4)) = List.replicate ((W - 1) * s) .mark) :
    ∃ w c, Eval [] linePre ⟨v, bst S0 (fRest [] [] [] q)⟩
      ⟨w, bst (Function.update S0 (kW .arr) restA)
        (fRest (csym wI (X ++ X.take (W - 1))) (List.replicate ((W - 1) * s) (.bit false))
          (List.replicate ((W - 1) * s) (.bit false)) q)⟩ c ∧
      c ≤ linePreCost t W wI s ∧ w.q = (csym wI (X ++ X.take (W - 1))).head? := by
  set Lp := csym wI (X.take (W - 1)) with hLp
  set Lx := csym wI X with hLx
  set Lr := csym wI (X.drop (W - 1)) with hLr
  have hlp : Lp.length = (W - 1) * (2 * wI + 1) := by
    rw [hLp, length_csym, List.length_take, hX]; congr 1; omega
  have hlx : Lx.length = t * (2 * wI + 1) := by rw [hLx, length_csym, hX]
  have hsplit : Lx = Lp ++ Lr := by rw [hLx, hLp, hLr, ← csym_append, List.take_append_drop]
  set f0 := fRest [] [] [] q with hf0
  -- step 1: copy the prefix onto T4 and T5
  obtain ⟨v1, e1⟩ := copy2N_eval (R := sp (.pr 0)) (X := sp (.X 2)) (src := kW .arr)
    (d1 := sp .T4) (d2 := sp .T5) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) Lp (Lr ++ restA) [] (bst S0 f0)
    (by simp) (by show (S0 _).head? ≠ _; rw [hX2]; simp)
    (by show S0 _ = _; rw [hp0, hlp, List.append_nil])
    (by show S0 _ = _; rw [harr, hsplit, List.append_assoc]) v
  have h4 : bst S0 f0 (sp .T4) = [] := hT4
  have h5 : bst S0 f0 (sp .T5) = [] := hT5
  rw [h4, h5, List.append_nil, bst_upd_base notField_arr,
    bst_upd_base notField_T4, bst_upd_base notField_T5] at e1
  set S1 := Function.update (Function.update (Function.update S0 (kW .arr) (Lr ++ restA)) (sp .T4)
    Lp.reverse) (sp .T5) Lp.reverse with hS1
  -- step 2: restore the prefix on arr
  obtain ⟨v2, e2⟩ := moveN_eval (R := sp (.pr 0)) (X := sp (.X 2)) (src := sp .T5) (dst := kW .arr)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) Lp.reverse [] []
    (bst S1 f0) (by simp)
    (by show (S1 _).head? ≠ _; simp [hS1, Function.update_apply, hX2])
    (by show S1 _ = _; simp [hS1, Function.update_apply, hp0, hlp])
    (by show S1 _ = _; simp [hS1, Function.update_apply]) v1
  have ha1 : bst S1 f0 (kW .arr) = Lr ++ restA := by
    show S1 _ = _; simp [hS1, Function.update_apply]
  rw [ha1, List.reverse_reverse, ← List.append_assoc, ← hsplit, bst_upd_base notField_T5,
    bst_upd_base notField_arr] at e2
  set S2 := Function.update (Function.update S1 (sp .T5) []) (kW .arr) (Lx ++ restA) with hS2
  -- step 3: the line onto T2
  obtain ⟨v3, e3⟩ := moveN_eval (R := sp (.pr 1)) (X := sp (.X 2)) (src := kW .arr) (dst := sp .T2)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) Lx restA []
    (bst S2 f0) (by simp)
    (by show (S2 _).head? ≠ _; simp [hS2, hS1, Function.update_apply, hX2])
    (by show S2 _ = _; simp [hS2, hS1, Function.update_apply, hp1, hlx])
    (by show S2 _ = _; simp [hS2, Function.update_apply]) v2
  have ht2 : bst S2 f0 (sp .T2) = [] := by
    show S2 _ = _; simp [hS2, hS1, Function.update_apply, hT2]
  rw [ht2, List.append_nil, bst_upd_base notField_arr, bst_upd_base notField_T2] at e3
  set S3 := Function.update (Function.update S2 (kW .arr) restA) (sp .T2) Lx.reverse with hS3
  -- step 4: the prefix onto Es
  obtain ⟨v4, e4⟩ := moveN_eval (R := sp (.pr 0)) (X := sp (.X 2)) (src := sp .T4) (dst := sp .Es)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) Lp.reverse [] []
    (bst S3 f0) (by simp)
    (by show (S3 _).head? ≠ _; simp [hS3, hS2, hS1, Function.update_apply, hX2])
    (by show S3 _ = _; simp [hS3, hS2, hS1, Function.update_apply, hp0, hlp])
    (by show S3 _ = _; simp [hS3, hS2, hS1, Function.update_apply]) v3
  have hes0 : bst S3 f0 (sp .Es) = [] := rfl
  rw [hes0, List.append_nil, List.reverse_reverse, bst_upd_base notField_T4, bst_upd_es] at e4
  set S4 := Function.update S3 (sp .T4) [] with hS4
  -- step 5: the line onto Es
  obtain ⟨v5, e5⟩ := moveN_eval (R := sp (.pr 1)) (X := sp (.X 2)) (src := sp .T2) (dst := sp .Es)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) Lx.reverse [] []
    (bst S4 { f0 with es := Lp }) (by simp)
    (by show (S4 _).head? ≠ _; simp [hS4, hS3, hS2, hS1, Function.update_apply, hX2])
    (by show S4 _ = _; simp [hS4, hS3, hS2, hS1, Function.update_apply, hp1, hlx])
    (by show S4 _ = _; simp [hS4, hS3, Function.update_apply]) v4
  have hes1 : bst S4 { f0 with es := Lp } (sp .Es) = Lp := rfl
  rw [hes1, List.reverse_reverse, bst_upd_base notField_T2, bst_upd_es] at e5
  set S5 := Function.update S4 (sp .T2) [] with hS5
  have hS5' : S5 = Function.update S0 (kW .arr) restA := by
    funext k
    simp only [hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  -- steps 6, 7: zero tails
  obtain ⟨v6, e6⟩ := pushN_eval (R := sp (.pr 4)) (X := sp (.X 2)) (dst := sp .Tre) (by simp)
    (by simp) (by simp) ((W - 1) * s) (.bit false) [] (bst S5 { { f0 with es := Lp } with es := Lx ++ Lp })
    (by simp) (by show (S5 _).head? ≠ _; rw [hS5']; simp [Function.update_apply, hX2])
    (by show S5 _ = _; rw [hS5']; simp [Function.update_apply, hp4]) v5
  have htre0 : bst S5 { { f0 with es := Lp } with es := Lx ++ Lp } (sp .Tre) = [] := rfl
  rw [htre0, List.append_nil, bst_upd_tre] at e6
  obtain ⟨v7, e7⟩ := pushN_eval (R := sp (.pr 4)) (X := sp (.X 2)) (dst := sp .Tim) (by simp)
    (by simp) (by simp) ((W - 1) * s) (.bit false) []
    (bst S5 { { { f0 with es := Lp } with es := Lx ++ Lp } with
      tre := List.replicate ((W - 1) * s) (.bit false) })
    (by simp) (by show (S5 _).head? ≠ _; rw [hS5']; simp [Function.update_apply, hX2])
    (by show S5 _ = _; rw [hS5']; simp [Function.update_apply, hp4]) v6
  have htim0 : bst S5 { { { f0 with es := Lp } with es := Lx ++ Lp } with
      tre := List.replicate ((W - 1) * s) (.bit false) } (sp .Tim) = [] := rfl
  rw [htim0, List.append_nil, bst_upd_tim] at e7
  have e8 := eval_peekQ (sp .Es) v7 (bst S5 { { { { f0 with es := Lp } with es := Lx ++ Lp } with
      tre := List.replicate ((W - 1) * s) (.bit false) } with
      tim := List.replicate ((W - 1) * s) (.bit false) })
  have hEs : Lx ++ Lp = csym wI (X ++ X.take (W - 1)) := by rw [hLx, hLp, csym_append]
  refine ⟨{ v7 with q := (csym wI (X ++ X.take (W - 1))).head? }, _,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
      (Eval.seq e7 e8))))))).of_eq ?_ rfl, ?_, rfl⟩
  · rw [hS5']
    congr 1
    · show { v7 with q := (Lx ++ Lp).head? } = _
      rw [hEs]
    · show bst _ _ = bst _ (fRest (csym wI (X ++ X.take (W - 1))) _ _ q)
      rw [← hEs]
      rfl
  · simp only [List.length_reverse, hlp, hlx]
    unfold linePreCost
    omega

/-- Rotate the finalized outputs of `Q` onto `Out` and drop the tails. -/
def linePost : AProg (SK Esu) :=
  .seq (drainBits (sp .Tre)) (.seq (drainBits (sp .Tim))
  (.seq (moveN (sp (.pr 2)) (sp (.X 2)) (sp .Q) (sp .P1))
  (.seq (moveN (sp (.pr 3)) (sp (.X 2)) (sp .Q) (sp .P2))
  (.seq (dropN (sp (.pr 0)) (sp (.X 2)) (sp .Q))
  (.seq (moveN (sp (.pr 2)) (sp (.X 2)) (sp .P1) (sp .Out))
  (moveN (sp (.pr 3)) (sp (.X 2)) (sp .P2) (sp .Out)))))))

/-- Cost bound of `linePost`. -/
def linePostCost (t W wI a0 nt ni : ℕ) : ℕ :=
  (3 * nt + 2) + (3 * ni + 2) + (10 * (a0 * (2 * wI + 1)) + 4) +
    (10 * ((t - a0) * (2 * wI + 1)) + 4) + (9 * ((W - 1) * (2 * wI + 1)) + 4) +
    (10 * (a0 * (2 * wI + 1)) + 4) + (10 * ((t - a0) * (2 * wI + 1)) + 4)

theorem linePost_eval (t W wI a0 q : ℕ) (X F : List CInt) (lt li : List Bool) (O : List Sym)
    (S0 : SK Esu → List Sym) (v : AReg) (hX : X.length = t) (hF : F.length = W) (hW : 1 ≤ W)
    (hWt : W ≤ t) (ha0 : a0 ≤ t)
    (hP1 : S0 (sp .P1) = []) (hP2 : S0 (sp .P2) = []) (hOut : S0 (sp .Out) = O)
    (hX2 : S0 (sp (.X 2)) = [])
    (hp0 : S0 (sp (.pr 0)) = List.replicate ((W - 1) * (2 * wI + 1)) .mark)
    (hp2 : S0 (sp (.pr 2)) = List.replicate (a0 * (2 * wI + 1)) .mark)
    (hp3 : S0 (sp (.pr 3)) = List.replicate ((t - a0) * (2 * wI + 1)) .mark) :
    ∃ w c, Eval [] linePost ⟨v, bst S0 (fRest [] (lt.map Sym.bit) (li.map Sym.bit)
        (csym wI ((lineConv t W X F).map (roundHalfUpShiftC q))).reverse)⟩
      ⟨w, bst (Function.update S0 (sp .Out) ((csym wI (lineOut q t W a0 X F)).reverse ++ O))
        (fRest [] [] [] [])⟩ c ∧
      c ≤ linePostCost t W wI a0 lt.length li.length := by
  set Y := (lineConv t W X F).map (roundHalfUpShiftC q) with hY
  have hYl : Y.length = t + W - 1 := by rw [hY, List.length_map, length_lineConv]
  set Ya := Y.drop (W - 1 + (t - a0)) with hYa
  set Ym := (Y.drop (W - 1)).take (t - a0) with hYm
  set Yw := Y.take (W - 1) with hYw
  have hsplit : Y = Yw ++ Ym ++ Ya := by
    rw [hYw, hYm, hYa, List.append_assoc, ← List.drop_drop, List.take_append_drop,
      List.take_append_drop]
  have hla : (csym wI Ya).length = a0 * (2 * wI + 1) := by
    rw [length_csym, hYa, List.length_drop, hYl]; congr 1; omega
  have hlm : (csym wI Ym).length = (t - a0) * (2 * wI + 1) := by
    rw [length_csym, hYm, List.length_take, List.length_drop, hYl]; congr 1; omega
  have hlw : (csym wI Yw).length = (W - 1) * (2 * wI + 1) := by
    rw [length_csym, hYw, List.length_take, hYl]; congr 1; omega
  have hQ : (csym wI Y).reverse = (csym wI Ya).reverse ++ ((csym wI Ym).reverse ++
      (csym wI Yw).reverse) := by
    rw [hsplit, csym_append, csym_append, List.reverse_append, List.reverse_append]
  have hout : lineOut q t W a0 X F = Ya ++ Ym := by
    rw [lineOut_eq q t W a0 X F hX hF hW hWt ha0, List.map_append, List.map_drop, List.map_take,
      List.map_drop]
  set f0 := fRest [] (lt.map Sym.bit) (li.map Sym.bit) (csym wI Y).reverse with hf0
  -- drain the tails
  have e1 := drainBits_eval (B := sp .Tre) lt [] v (bst S0 f0) TermOK.nil (by rw [List.append_nil]; rfl)
  rw [bst_upd_tre] at e1
  have e2 := drainBits_eval (B := sp .Tim) li [] { v with q := none } (bst S0 { f0 with tre := [] })
    TermOK.nil (by rw [List.append_nil]; rfl)
  rw [bst_upd_tim] at e2
  set f2 : BF := { { f0 with tre := [] } with tim := [] } with hf2
  -- the last a₀ outputs onto P1
  obtain ⟨v3, e3⟩ := moveN_eval (R := sp (.pr 2)) (X := sp (.X 2)) (src := sp .Q) (dst := sp .P1)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (csym wI Ya).reverse
    ((csym wI Ym).reverse ++ (csym wI Yw).reverse) [] (bst S0 f2) (by simp)
    (by show (S0 _).head? ≠ _; rw [hX2]; simp)
    (by show S0 _ = _; rw [hp2, List.length_reverse, hla, List.append_nil])
    (by show (csym wI Y).reverse = _; exact hQ) { v with q := none }
  have hp10 : bst S0 f2 (sp .P1) = [] := hP1
  rw [hp10, List.append_nil, List.reverse_reverse, bst_upd_q, bst_upd_base notField_P1] at e3
  -- the next t - a₀ outputs onto P2
  obtain ⟨v4, e4⟩ := moveN_eval (R := sp (.pr 3)) (X := sp (.X 2)) (src := sp .Q) (dst := sp .P2)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (csym wI Ym).reverse
    (csym wI Yw).reverse []
    (bst (Function.update S0 (sp .P1) (csym wI Ya)) { f2 with q := (csym wI Ym).reverse ++
      (csym wI Yw).reverse }) (by simp)
    (by show (Function.update S0 (sp .P1) _ _).head? ≠ _; simp [Function.update_apply, hX2])
    (by show Function.update S0 (sp .P1) _ _ = _
        simp [Function.update_apply, hp3, hlm])
    rfl v3
  have hp20 : bst (Function.update S0 (sp .P1) (csym wI Ya)) { f2 with q := (csym wI Ym).reverse ++
      (csym wI Yw).reverse } (sp .P2) = [] := by
    show Function.update S0 (sp .P1) _ _ = _; simp [Function.update_apply, hP2]
  rw [hp20, List.append_nil, List.reverse_reverse, bst_upd_q, bst_upd_base notField_P2] at e4
  -- drop the W - 1 skipped outputs
  obtain ⟨v5, e5⟩ := dropN_eval (R := sp (.pr 0)) (X := sp (.X 2)) (src := sp .Q)
    (by simp) (by simp) (by simp) (csym wI Yw).reverse [] []
    (bst (Function.update (Function.update S0 (sp .P1) (csym wI Ya)) (sp .P2) (csym wI Ym))
      { { f2 with q := (csym wI Ym).reverse ++ (csym wI Yw).reverse } with
        q := (csym wI Yw).reverse }) (by simp)
    (by show (Function.update (Function.update S0 (sp .P1) _) (sp .P2) _ _).head? ≠ _
        simp [Function.update_apply, hX2])
    (by show Function.update (Function.update S0 (sp .P1) _) (sp .P2) _ _ = _
        simp [Function.update_apply, hp0, hlw])
    (by rw [List.append_nil]; rfl) v4
  rw [bst_upd_q] at e5
  set S5 := Function.update (Function.update S0 (sp .P1) (csym wI Ya)) (sp .P2) (csym wI Ym)
    with hS5
  set f5 : BF := { { { f2 with q := (csym wI Ym).reverse ++ (csym wI Yw).reverse } with
    q := (csym wI Yw).reverse } with q := [] } with hf5
  -- P1, then P2 onto Out
  obtain ⟨v6, e6⟩ := moveN_eval (R := sp (.pr 2)) (X := sp (.X 2)) (src := sp .P1) (dst := sp .Out)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (csym wI Ya) [] [] (bst S5 f5)
    (by simp) (by show (S5 _).head? ≠ _; simp [hS5, Function.update_apply, hX2])
    (by show S5 _ = _; simp [hS5, Function.update_apply, hp2, hla])
    (by show S5 _ = _; simp [hS5, Function.update_apply]) v5
  rw [bst_upd_base notField_P1, bst_upd_base notField_Out] at e6
  set S6 := Function.update (Function.update S5 (sp .P1) []) (sp .Out)
    ((csym wI Ya).reverse ++ bst S5 f5 (sp .Out)) with hS6
  obtain ⟨v7, e7⟩ := moveN_eval (R := sp (.pr 3)) (X := sp (.X 2)) (src := sp .P2) (dst := sp .Out)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (csym wI Ym) [] [] (bst S6 f5)
    (by simp) (by show (S6 _).head? ≠ _; simp [hS6, hS5, Function.update_apply, hX2])
    (by show S6 _ = _; simp [hS6, hS5, Function.update_apply, hp3, hlm])
    (by show S6 _ = _; simp [hS6, hS5, Function.update_apply]) v6
  rw [bst_upd_base notField_P2, bst_upd_base notField_Out] at e7
  have hO : bst S6 f5 (sp .Out) = (csym wI Ya).reverse ++ O := by
    show S6 (sp .Out) = _
    rw [hS6, Function.update_self]
    show _ ++ S5 (sp .Out) = _
    rw [hS5, Function.update_of_ne (by simp), Function.update_of_ne (by simp), hOut]
  have hV : (csym wI Ym).reverse ++ ((csym wI Ya).reverse ++ O) =
      (csym wI (lineOut q t W a0 X F)).reverse ++ O := by
    rw [hout, csym_append, List.reverse_append, List.append_assoc]
  have hbase : Function.update (Function.update S6 (sp .P2) []) (sp .Out)
      ((csym wI (lineOut q t W a0 X F)).reverse ++ O) =
      Function.update S0 (sp .Out) ((csym wI (lineOut q t W a0 X F)).reverse ++ O) := by
    funext k
    by_cases h1 : k = sp .Out
    · subst h1; rw [Function.update_self, Function.update_self]
    rw [Function.update_of_ne h1, Function.update_of_ne h1]
    by_cases h2 : k = sp .P2
    · subst h2; rw [Function.update_self, hP2]
    rw [Function.update_of_ne h2, hS6, Function.update_of_ne h1]
    by_cases h3 : k = sp .P1
    · subst h3; rw [Function.update_self, hP1]
    rw [Function.update_of_ne h3, hS5, Function.update_of_ne h2, Function.update_of_ne h3]
  rw [hO, hV, hbase] at e7
  refine ⟨v7, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    e7)))))).of_eq rfl rfl, ?_⟩
  · simp only [List.length_reverse, hla, hlm, hlw]
    unfold linePostCost
    omega

/-! ## Closedness -/

theorem closed_linePre : (linePre (Esu := Esu)).Closed := by
  simp only [Prog.Closed]
  simp [linePre, copy2N, copy1, moveN, move1, pushN, walk, walkLoop, walkStep, moveMarks, mmLoop,
    drop1, peekR, peekQ, popO, pushS, Prog.FreeBelow]

theorem closed_linePost : (linePost (Esu := Esu)).Closed := by
  simp only [Prog.Closed]
  simp [linePost, dropN, moveN, move1, walk, walkLoop, walkStep, moveMarks, mmLoop, drainBits,
    dbLoop, drop1, peekR, peekQ, popO, pushS, Prog.FreeBelow]

section ClosedBlock

variable {σ Rm : Type}

theorem closed_mulRe (lM : Lens σ Rm) {Pm : Prog MBLoc (fun _ => Sym) Rm} (hcl : Pm.Closed) :
    ∀ l : List (Fin 8), (mulRe (Esu := Esu) lM Pm l).Closed
  | [] => trivial
  | _ :: l => ⟨closed_callInj _ lM hcl, closed_mulRe lM hcl l⟩

theorem closed_mulIm (lM : Lens σ Rm) {Pm : Prog MBLoc (fun _ => Sym) Rm} (hcl : Pm.Closed) :
    ∀ l : List (Fin 8), (mulIm (Esu := Esu) lM Pm l).Closed
  | [] => trivial
  | _ :: l => ⟨closed_callInj _ lM hcl, closed_mulIm lM hcl l⟩

theorem closed_blockProg {pdp : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K}
    (hpdc : ∀ (K : Type) [DecidableEq K] (ι : PackRole → K), (pdp K ι).Closed)
    {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K}
    (hspc : ∀ (K : Type) [DecidableEq K] (ι : SlotRole → K), (prog K ι).Closed)
    (lA : Lens σ AReg) (lM : Lens σ Rm) {Pm : Prog MBLoc (fun _ => Sym) Rm} (hcl : Pm.Closed) :
    (blockProg (Esu := Esu) pdp prog lA lM Pm).Closed :=
  ⟨WP.W9comp.closed_liftRegs lA (hpdc _ _), closed_mulRe lM hcl _, closed_mulIm lM hcl _,
    WP.W9comp.closed_liftRegs lA (closed_postBlk hspc)⟩

end ClosedBlock

end SubNLogN.Machine.Bridge.SpreadAux
