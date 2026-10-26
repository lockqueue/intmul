import WP.W0m.Work

/-!
# WP.W0m.PhasesA — correctness and cost of phases A–D (library and new macros only)

Each phase lemma is stated for an arbitrary stack function `S`, constrained only on the stacks the
phase reads, and gives the exact post-state as a `Function.update` of `S`. Costs are bounded either
by the operand bit lengths (phases A, B) or by `Λ`, a common bound on the bit lengths of all small
values (phases C, D).
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts

theorem runs_post {K σ : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) σ}
    {S S1 S2 : K → List Sym} {Q : σ → Prop} {T T' : ℕ} (h : Runs P S S1 Q T) (e : S1 = S2)
    (hT : T ≤ T') : Runs P S S2 Q T' := by
  subst e
  exact runs_mono h (fun _ h => h) hT

theorem bitLen_max_le {x y Λ : ℕ} (hx : bitLen x ≤ Λ) (hy : bitLen y ≤ Λ) :
    bitLen (max x y) ≤ Λ := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    exact hy
  · rw [max_eq_left h]
    exact hx

variable {Ra Rd : Type}

/-- **Phase A** (parse): `inp = bits(b)ᴿ · sep · bits(a)ᴿ` becomes `ob = natSyms b`, `oa = natSyms a`. -/
theorem phA_runs (S : Stk → List Sym) (a b : ℕ) (hinp : S .inp = inputSyms a b)
    (hoa : S .oa = []) (hob : S .ob = []) :
    Runs (phA : WProg Ra Rd) S
      (Function.update (Function.update (Function.update S .inp []) .ob (natSyms b)) .oa
        (natSyms a))
      (fun _ => True) (3 * bitLen a + 3 * bitLen b + 4) := by
  have h1 := rs_moveBits (lS (Ra := Ra) (Rd := Rd)) (src := Stk.inp) (dst := Stk.ob) (by decide)
    (encodeNat b).reverse (Sym.sep :: (encodeNat a).reverse.map Sym.bit) S
    (TermOK.cons (by rfl) _) hinp
  set S1 := Function.update (Function.update S .inp
    (Sym.sep :: (encodeNat a).reverse.map Sym.bit).tail) .ob
    ((encodeNat b).reverse.reverse.map Sym.bit ++ S .ob) with hS1
  have h2 := rs_moveBits (lS (Ra := Ra) (Rd := Rd)) (src := Stk.inp) (dst := Stk.oa) (by decide)
    (encodeNat a).reverse [] S1 TermOK.nil (by
      rw [hS1, Function.update_of_ne (by decide), Function.update_self, List.tail_cons,
        List.append_nil])
  refine runs_post (runs_seq h1 h2) ?_ ?_
  · funext x
    simp only [hS1, Function.update_apply, List.reverse_reverse, hob, hoa, List.append_nil,
      List.tail_nil, natSyms]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, length_encodeNat_eq_bitLen]
    omega

/-- **Phase B** (bit lengths). -/
theorem phB_runs (S : Stk → List Sym) (a b : ℕ) (hoa : S .oa = natSyms a) (hob : S .ob = natSyms b)
    (hla : S .la = []) (hlb : S .lb = []) :
    Runs (phB : WProg Ra Rd) S
      (Function.update (Function.update S .la (natSyms (bitLen a))) .lb (natSyms (bitLen b)))
      (fun _ => True) (24 * bitLen a + 24 * bitLen b + 20) := by
  have h1 := rs_count0 (lS (Ra := Ra) (Rd := Rd)) (src := Stk.oa) (t := .cs) (tm := .tm) (c := .la)
    (ct := .ct) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a [] [] S
    TermOK.nil TermOK.nil (by rw [hoa, List.append_nil]) hla
  have h2 := rs_count0 (lS (Ra := Ra) (Rd := Rd)) (src := Stk.ob) (t := .cs) (tm := .tm) (c := .lb)
    (ct := .ct) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b [] []
    (Function.update S .la (natSyms (bitLen a) ++ [])) TermOK.nil TermOK.nil
    (by rw [Function.update_of_ne (by decide), hob, List.append_nil])
    (by rw [Function.update_of_ne (by decide), hlb])
  refine runs_post (runs_seq h1 h2) ?_ (by omega)
  simp only [List.append_nil]

/-- **Phase C**: `nn := max 1 (max x y)` from `la = x`, `lb = y`; `la`, `lb` are emptied. -/
theorem phC_runs (S : Stk → List Sym) (x y : ℕ) (hla : S .la = natSyms x)
    (hlb : S .lb = natSyms y) (hnn : S .nn = []) (Λ : ℕ) (hx : bitLen x ≤ Λ)
    (hy : bitLen y ≤ Λ) :
    Runs (phC : WProg Ra Rd) S
      (Function.update (Function.update (Function.update S .nn (natSyms (max 1 (max x y)))) .la [])
        .lb [])
      (fun _ => True) (40 * Λ + 50) := by
  have hm := bitLen_max_le hx hy
  have hc := rs_cmp (lC (Ra := Ra) (Rd := Rd)) (k₁ := Stk.la) (k₂ := .lb) (t₁ := .x0) (t₂ := .x1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x y [] [] S TermOK.nil
    TermOK.nil (by rw [hla, List.append_nil]) (by rw [hlb, List.append_nil])
  set S2 := Function.update S .nn (natSyms (max x y)) with hS2
  have hstep2 : Runs (.seq (cmpW .la .lb)
      (.ite isLt (sym (copyBlock .lb .nn .tm)) (sym (copyBlock .la .nn .tm))) : WProg Ra Rd) S S2
      (fun _ => True) (12 * min (bitLen x) (bitLen y) + 15 + (7 * Λ + 7 + 1)) := by
    by_cases hxy : x < y
    · have hc' := runs_mono hc (Q' := fun v => isLt v = true)
        (fun v hv => by simp only [isLt, hv, Lib.ordOf, if_pos hxy]; decide) le_rfl
      have hcp := rs_copy (lS (Ra := Ra) (Rd := Rd)) (src := Stk.lb) (dst := .nn) (tmp := .tm)
        (by decide) (by decide) (by decide) y [] S TermOK.nil (by rw [hlb, List.append_nil])
      refine runs_post (runs_ite_true hc' hcp) ?_ ?_
      · rw [hnn, List.append_nil, hS2, max_eq_right (le_of_lt hxy)]
      · omega
    · have hc' := runs_mono hc (Q' := fun v => isLt v = false)
        (fun v hv => by simp only [isLt, hv, Lib.ordOf, if_neg hxy]; split_ifs <;> decide) le_rfl
      have hcp := rs_copy (lS (Ra := Ra) (Rd := Rd)) (src := Stk.la) (dst := .nn) (tmp := .tm)
        (by decide) (by decide) (by decide) x [] S TermOK.nil (by rw [hla, List.append_nil])
      refine runs_post (runs_ite_false hc' hcp) ?_ ?_
      · rw [hnn, List.append_nil, hS2, max_eq_left (Nat.le_of_not_lt hxy)]
      · omega
  have hd1 := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.la) x [] S2 TermOK.nil
    (by rw [hS2, Function.update_of_ne (by decide), hla, List.append_nil])
  set S3 := Function.update S2 .la [] with hS3
  have hd2 := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.lb) y [] S3 TermOK.nil
    (by rw [hS3, Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide), hlb,
      List.append_nil])
  set S4 := Function.update S3 .lb [] with hS4
  have hS4nn : S4 .nn = natSyms (max x y) ++ [] := by
    rw [hS4, Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide), hS2,
      Function.update_self, List.append_nil]
  have hz := rs_zeroTest (lS (Ra := Ra) (Rd := Rd)) (k := Stk.nn) (max x y) [] S4 TermOK.nil hS4nn
  have hstep6 : Runs (.seq (sym (zeroTest .nn)) (.ite symIsBit (sym skip) (sym (inc .nn .ct))) :
      WProg Ra Rd) S4 (Function.update S4 .nn (natSyms (max 1 (max x y)))) (fun _ => True)
      (1 + (6 * Λ + 9 + 1)) := by
    by_cases h0 : max x y = 0
    · have hz' := runs_mono hz (Q' := fun v => symIsBit v = false)
        (fun v hv => by simp only [symIsBit, hv, h0]; decide) le_rfl
      have hi := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.nn) (t := .ct) (by decide) (max x y)
        [] S4 TermOK.nil hS4nn
      refine runs_post (runs_ite_false hz' hi) ?_ ?_
      · rw [h0]
        simp
      · omega
    · have hz' := runs_mono hz (Q' := fun v => symIsBit v = true)
        (fun v hv => by simp only [symIsBit, hv, h0]; decide) le_rfl
      have hs := rs_skip (lS (Ra := Ra) (Rd := Rd)) S4
      refine runs_post (runs_ite_true hz' hs) ?_ ?_
      · rw [max_eq_right (by omega : 1 ≤ max x y), ← List.append_nil (natSyms (max x y)), ← hS4nn,
          Function.update_eq_self]
      · omega
  refine runs_post (runs_seq hstep2 (runs_seq hd1 (runs_seq hd2 hstep6))) ?_ ?_
  · funext z
    simp only [hS4, hS3, hS2, Function.update_apply]
    split_ifs <;> simp_all
  · omega

/-- **Phase D**: `bb := max 1 (bitLen n − 1) = sB n`. -/
theorem phD_runs (S : Stk → List Sym) (n : ℕ) (hn : n ≠ 0) (hnn : S .nn = natSyms n)
    (hbb : S .bb = []) (Λ : ℕ) (hΛ : bitLen n ≤ Λ) :
    Runs (phD : WProg Ra Rd) S (Function.update S .bb (natSyms (sB n))) (fun _ => True)
      (40 * Λ + 30) := by
  have hpos := bitLen_pos hn
  have hb1 : bitLen (bitLen n) ≤ Λ := (bitLen_le_self _).trans hΛ
  have hb2 : bitLen (bitLen n - 1 + 1) ≤ Λ := by rw [Nat.sub_add_cancel hpos]; exact hb1
  have hb3 : bitLen (bitLen n - 1) ≤ Λ := (bitLen_mono (Nat.sub_le _ _)).trans hb1
  have hc := rs_count0 (lS (Ra := Ra) (Rd := Rd)) (src := Stk.nn) (t := .cs) (tm := .tm) (c := .bb)
    (ct := .ct) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n [] [] S
    TermOK.nil TermOK.nil (by rw [hnn, List.append_nil]) hbb
  set S1 := Function.update S .bb (natSyms (bitLen n) ++ []) with hS1
  have hd := rs_dec (lS (Ra := Ra) (Rd := Rd)) (k := Stk.bb) (t := .ct) (by decide) (bitLen n - 1)
    [] S1 TermOK.nil (by rw [hS1, Function.update_self, Nat.sub_add_cancel hpos])
  set S2 := Function.update S1 .bb (natSyms (bitLen n - 1) ++ []) with hS2
  have hS2bb : S2 .bb = natSyms (bitLen n - 1) ++ [] := by rw [hS2, Function.update_self]
  have hz := rs_zeroTest (lS (Ra := Ra) (Rd := Rd)) (k := Stk.bb) (bitLen n - 1) [] S2 TermOK.nil
    hS2bb
  have hstep : Runs (.seq (sym (zeroTest .bb)) (.ite symIsBit (sym skip) (sym (inc .bb .ct))) :
      WProg Ra Rd) S2 (Function.update S2 .bb (natSyms (max 1 (bitLen n - 1)))) (fun _ => True)
      (1 + (6 * Λ + 9 + 1)) := by
    by_cases h0 : bitLen n - 1 = 0
    · have hz' := runs_mono hz (Q' := fun v => symIsBit v = false)
        (fun v hv => by simp only [symIsBit, hv, h0]; decide) le_rfl
      have hi := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.bb) (t := .ct) (by decide)
        (bitLen n - 1) [] S2 TermOK.nil hS2bb
      refine runs_post (runs_ite_false hz' hi) ?_ ?_
      · rw [h0]
        simp
      · omega
    · have hz' := runs_mono hz (Q' := fun v => symIsBit v = true)
        (fun v hv => by simp only [symIsBit, hv, h0]; decide) le_rfl
      have hs := rs_skip (lS (Ra := Ra) (Rd := Rd)) S2
      refine runs_post (runs_ite_true hz' hs) ?_ ?_
      · rw [max_eq_right (by omega : 1 ≤ bitLen n - 1), ← List.append_nil (natSyms (bitLen n - 1)),
          ← hS2bb, Function.update_eq_self]
      · omega
  refine runs_post (runs_seq hc (runs_seq hd hstep)) ?_ ?_
  · rw [sB_eq hn, hS2, hS1, Function.update_idem, Function.update_idem]
  · omega

#assert_std_axioms runs_post bitLen_max_le phA_runs phB_runs phC_runs phD_runs

end WP.W0m
