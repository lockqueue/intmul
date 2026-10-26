import WP.W9c.WinPh
import Mathlib.Tactic.Ring

/-!
# WP.W9c.Window — `W9c_window` (one step of the buffered overlap-add)

`winProg I` (stacks `Loc 4 4`, see `WinState`; `I` an instance of the frozen `W3_addInt`):

1. guards `mark` on `sTD`, `sTW`, `sU`;
2. loop 1 (`W` iterations, driven by the window): `w_i → sTW`, `d_i → sTD` (order kept, so both
   hold their lists reversed), one unit per iteration on `sU`;
3. loop 2: `sE += w_i + d_i` from `i = W-1` down to `0`, so the emitted list has `w_0 + d_0` on
   top; the operands are dropped;
4. loop 3: the remaining digits `d_W, …` go to `sTD` symbol by symbol (reversed), one unit each
   is removed;
5. loop 4: one zero entry per remaining unit (`2W - |ds|` of them) is pushed on the window;
6. the reversed digits are moved back onto the window (`moveWhile notMark`), guards popped.

The counter stack `W` is never read: the window itself (`|ws| = W`) drives loop 1. All moves are
of digits and window entries, whose sizes are bounded by `B`; the sums are never moved.
Cost: `(2·Ca + 80)·(W·(B+1) + 1)`, `Ca` the adder's constant.
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

/-- **The window program.** -/
def winProg (I : Inst 3 4 Unit) : HP 4 4 (WR I.R) :=
  (pushS sTD .mark).seq <| (pushS sTW .mark).seq <| (pushS sU .mark).seq <|
  (whileTop (Lens.fst _ _) sWn isSign (wB1 I.R)).seq <|
  (whileTop (Lens.fst _ _) sTW isSign (wB2 I)).seq <|
  (popS sTW).seq <|
  (whileTop (Lens.fst _ _) sD isSign (wB3 I.R)).seq <|
  (whileTop (Lens.fst _ _) sU Sym.isBit (wB4 I.R)).seq <|
  (popS sU).seq <|
  (moveWhile (Lens.fst _ _) notMark sTD sWn).seq (popS sTD)

theorem winProg_closed (I : Inst 3 4 Unit) : (winProg I).Closed :=
  ⟨trivial, trivial, trivial, whileTop_closed _ _ _ (wB1_closed _),
    whileTop_closed _ _ _ (wB2_closed _), trivial, whileTop_closed _ _ _ (wB3_closed _),
    whileTop_closed _ _ _ (wB4_closed _), trivial, moveWhile_closed _ _ _ _, trivial⟩

/-- **Correctness and cost of `winProg`** on records. -/
theorem winProg_spec {I : Inst 3 4 Unit} {Ca : ℕ} (hI : SpecAddInt I Ca) (W B : ℕ)
    (ds ws : List ℤ) (rd rw e c td0 tw0 u0 x : List Sym) (hws : ws.length = W)
    (hWd : W ≤ ds.length) (hdW : ds.length ≤ 2 * W) (hbd : ∀ v ∈ ds, bitLen v.natAbs ≤ B)
    (hbw : ∀ v ∈ ws, bitLen v.natAbs ≤ B) (hrd : EndOK rd) (hrw : EndOK rw) :
    HT [] (WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw, e, c, td0, tw0, u0, x⟩) (winProg I)
      (WS.f ⟨rd, listSyms (winStep W ws ds).2 ++ rw, listSyms (winStep W ws ds).1 ++ e, c, td0,
        tw0, u0, x⟩) ((2 * Ca + 80) * (W * (B + 1) + 1)) := by
  subst hws
  -- guards
  have p1 := HT.pushS (σ := WR I.R) sTD Sym.mark
    (WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw, e, c, td0, tw0, u0, x⟩) []
  rw [f_td, upd_td] at p1
  have p2 := HT.pushS (σ := WR I.R) sTW Sym.mark
    (WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw, e, c, Sym.mark :: td0, tw0, u0, x⟩) []
  rw [f_tw, upd_tw] at p2
  have p3 := HT.pushS (σ := WR I.R) sU Sym.mark
    (WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw, e, c, Sym.mark :: td0, Sym.mark :: tw0, u0, x⟩) []
  rw [f_u, upd_u] at p3
  -- loop 1
  have l1 := ck_whileTop (ρ := []) _ _ _ _
    (win_ph1 (R := I.R) [] B rd rw e c td0 tw0 u0 x hrw ws ds [] [] 0 hWd hbw hbd)
  simp only [List.append_nil, Nat.zero_add] at l1
  -- loop 2
  have hlen2 : ws.reverse.length = (ds.take ws.length).reverse.length := by
    simp only [List.length_reverse, List.length_take]
    omega
  have l2 := ck_whileTop (ρ := []) _ _ _ _
    (win_ph2 hI [] B (listSyms (ds.drop ws.length) ++ rd) rw c td0 tw0
      (units ws.length ++ Sym.mark :: u0) x ws.reverse (ds.take ws.length).reverse e hlen2
      (fun v hv => hbw v (List.mem_reverse.mp hv))
      (fun v hv => hbd v (List.mem_of_mem_take (List.mem_reverse.mp hv))))
  obtain ⟨E2, hE2⟩ : ∃ E2, E2 = listSyms (List.zipWith (· + ·) ws.reverse
      (ds.take ws.length).reverse).reverse ++ e := ⟨_, rfl⟩
  rw [← hE2] at l2
  have p4 := HT.popS (σ := WR I.R) sTW (WS.f ⟨listSyms (ds.drop ws.length) ++ rd, rw, E2, c,
    Sym.mark :: td0, Sym.mark :: tw0, units ws.length ++ Sym.mark :: u0, x⟩) Sym.mark tw0 rfl []
  rw [upd_tw] at p4
  -- loop 3
  have l3 := ck_whileTop (ρ := []) _ _ _ _
    (win_ph3 (R := I.R) [] B rd rw E2 c td0 tw0 u0 x hrd (ds.drop ws.length) [] ws.length
      (by simp only [List.length_drop]; omega) (fun v hv => hbd v (List.mem_of_mem_drop hv)))
  simp only [List.nil_append, List.length_drop] at l3
  rw [show ws.length - (ds.length - ws.length) = 2 * ws.length - ds.length by omega] at l3
  -- loop 4
  have l4 := ck_whileTop (ρ := []) _ _ _ _
    (win_ph4 (R := I.R) [] rd E2 c ((listSyms (ds.drop ws.length)).reverse ++ Sym.mark :: td0)
      tw0 u0 x rw (2 * ws.length - ds.length) 0)
  simp only [Nat.zero_add] at l4
  have p5 := HT.popS (σ := WR I.R) sU (WS.f ⟨rd,
    listSyms (List.replicate (2 * ws.length - ds.length) 0) ++ rw, E2, c,
    (listSyms (ds.drop ws.length)).reverse ++ Sym.mark :: td0, tw0, Sym.mark :: u0, x⟩)
    Sym.mark u0 rfl []
  rw [upd_u] at p5
  -- move the remaining digits back
  have m1 := ck_moveWhile (ρ := []) (Lens.fst (Option Sym) I.R) notMark (src := sTD) (dst := sWn)
    (by decide) (Sym.mark :: td0) rfl ((listSyms (ds.drop ws.length)).reverse)
    (WS.f ⟨rd, listSyms (List.replicate (2 * ws.length - ds.length) 0) ++ rw, E2, c,
      (listSyms (ds.drop ws.length)).reverse ++ Sym.mark :: td0, tw0, u0, x⟩)
    (fun y hy => notMark_of_mem_listSyms _ y (List.mem_reverse.mp hy)) rfl
  rw [upd_td, f_w, upd_w, List.reverse_reverse] at m1
  have p6 := HT.popS (σ := WR I.R) sTD (WS.f ⟨rd, listSyms (ds.drop ws.length) ++
    (listSyms (List.replicate (2 * ws.length - ds.length) 0) ++ rw), E2, c, Sym.mark :: td0, tw0,
    u0, x⟩) Sym.mark td0 rfl []
  rw [upd_td] at p6
  -- compose
  refine HT.of_eq (p1.seq (p2.seq (p3.seq (l1.seq (l2.seq (p4.seq (l3.seq (l4.seq (p5.seq
    (m1.seq p6)))))))))) ?_ ?_
  · rw [hE2]
    simp only [winStep, listSyms_append, List.append_assoc, List.reverse_zipWith hlen2,
      List.reverse_reverse]
  · -- cost
    simp only [List.length_reverse]
    have h1 : ws.length * (16 * B + 23) ≤ 23 * (ws.length * (B + 1)) :=
      calc ws.length * (16 * B + 23) ≤ ws.length * (23 * (B + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 23 * (ws.length * (B + 1)) := by ring
    have h2 : ws.length * (Ca * (2 * B + 1) + 6 * B + 11) ≤
        2 * (Ca * (ws.length * (B + 1))) + 11 * (ws.length * (B + 1)) := by
      have hc : Ca * (2 * B + 1) ≤ Ca * (2 * (B + 1)) := Nat.mul_le_mul_left _ (by omega)
      calc ws.length * (Ca * (2 * B + 1) + 6 * B + 11) ≤
            ws.length * (Ca * (2 * (B + 1)) + 11 * (B + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (Ca * (ws.length * (B + 1))) + 11 * (ws.length * (B + 1)) := by ring
    have h3 : (ds.length - ws.length) * (4 * B + 9) ≤ 9 * (ws.length * (B + 1)) :=
      calc (ds.length - ws.length) * (4 * B + 9) ≤ ws.length * (9 * (B + 1)) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 9 * (ws.length * (B + 1)) := by ring
    have h4 : ws.length ≤ ws.length * (B + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h5 : (listSyms (ds.drop ws.length)).length ≤ 2 * (ws.length * (B + 1)) :=
      calc (listSyms (ds.drop ws.length)).length ≤ (ds.drop ws.length).length * (B + 2) :=
            length_listSyms_le _ _ (fun v hv => hbd v (List.mem_of_mem_drop hv))
        _ ≤ ws.length * (2 * (B + 1)) := Nat.mul_le_mul (by simp only [List.length_drop]; omega)
            (by omega)
        _ = 2 * (ws.length * (B + 1)) := by ring
    have hexp : (2 * Ca + 80) * (ws.length * (B + 1) + 1) =
        2 * (Ca * (ws.length * (B + 1))) + 80 * (ws.length * (B + 1)) + 2 * Ca + 80 := by ring
    omega

#assert_std_axioms winProg_closed winProg_spec

end WP.W9c.CK

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 WP.W9c.CK

/-- **`W9c_window` holds**, given the signed-addition contract `W3_addInt`. -/
theorem w9c_window_holds (hadd : W3_addInt) : W9c_window := by
  obtain ⟨Ca, hCa⟩ := exists_inst hadd
  refine ⟨2 * Ca + 80, fun _ => ?_⟩
  obtain ⟨I, hI⟩ := hCa ()
  haveI := I.fin
  haveI := I.ne
  refine ⟨4, WR I.R, fun _ => (), winProg I, by norm_num, inferInstance, inferInstance,
    winProg_closed I, ?_⟩
  intro W B ds ws rd rw rW S hws hWd hdW hbd hbw hrd hrw _ hS0 hS1 _
  have key := winProg_spec hI W B ds ws rd rw (S sE) (S sWc) (S sTD) (S sTW) (S sU) (S sX) hws hWd
    hdW hbd hbw hrd hrw
  have hpre : WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw, S sE, S sWc, S sTD, S sTW, S sU, S sX⟩
      = S := by
    rw [← hS0, ← hS1]
    exact (WS.eta S).symm
  have hpost : WS.f ⟨rd, listSyms (winStep W ws ds).2 ++ rw, listSyms (winStep W ws ds).1 ++ S sE,
      S sWc, S sTD, S sTW, S sU, S sX⟩ = Function.update (Function.update (Function.update S sD rd)
        sWn (listSyms (winStep W ws ds).2 ++ rw)) sE (listSyms (winStep W ws ds).1 ++ S sE) := by
    conv_rhs => rw [WS.eta S]
    simp only [f_e, upd_d, upd_w, upd_e]
  rw [hpre, hpost] at key
  exact HT.runs key

#assert_std_axioms w9c_window_holds

end WP.W9c
