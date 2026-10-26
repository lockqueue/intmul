import WP.W4o.TopLemmas
import WP.W4o.Fill

/-!
# WP.W4o.OddRoute — `W4_oddRoute .down .down`

`oddRouteProg` (stacks `Loc 5 4`):
1. copy `b` from `sBs` onto `sT` (above a `mark`);
2. push a `mark` and `k` zero bits onto `sBs`, then add the copy of `b` in place: `sBs` holds
   `b` padded to exactly `k` bits (`pad_spec`), above the `mark`, above the original `b`;
3. drop the copy of `b` from `sT`;
4. `route` (`WP.W4o.RouteRec`): pushes `blk .down (rt (encodeNat w) k B v)` onto `sY`, which is
   `blk .down (oddRouteL k w b v)` by `rt_eq_oddRouteL`;
5. drop the padded block and its `mark` from `sBs`.
Cost `≤ 300·(|blk|+1)·(k+1)` (`top_cost`).
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- The odd-stride router kernel (`oi = oo = .down`). -/
def oddRouteProg : RProg L54 :=
  .seq (pushK sT .mark) (.seq (copyP sBs sT sV) (.seq (pushK sBs .mark)
    (.seq (fillP false sK sBs sA sV) (.seq (addTP false sBs sT sA sV) (.seq (dropNum sT)
    (.seq route (dropNum sBs)))))))

theorem oddRouteProg_closed : oddRouteProg.Closed := by
  have h1 : Prog.FreeBelow 0 (copyP sBs sT sV) := copyP_closed sBs sT sV
  have h2 : Prog.FreeBelow 0 (fillP false sK sBs sA sV) := fillP_closed false sK sBs sA sV
  have h3 : Prog.FreeBelow 0 (addTP false sBs sT sA sV) := addTP_closed false sBs sT sA sV
  have h4 : Prog.FreeBelow 0 (dropNum sT) := dropNum_closed sT
  have h5 : Prog.FreeBelow 0 (dropNum sBs) := dropNum_closed sBs
  have h6 : Prog.FreeBelow 0 route := route_closed
  simp only [Prog.Closed, oddRouteProg, Prog.FreeBelow]
  exact ⟨trivial, h1, trivial, h2, h3, h4, h6, h5⟩

/-- **W4.oddRoute** for `.down` input and output. -/
theorem W4_oddRoute_holds : W4_oddRoute .down .down := by
  refine ⟨300, fun _ => ⟨4, Reg, fun _ => (), oddRouteProg, le_refl 4, inferInstance,
    ⟨(none, none, false)⟩, oddRouteProg_closed, ?_⟩⟩
  intro k w b v rest r2 r3 r4 S hpar hb hv hrec hrest hr2 hr3 hr4 hX hK hW hB
  have hw : w % 2 = 1 := hpar.1
  have hS := st9_eta S
  rw [hX, hK, hW, hB] at hS
  rw [hS]
  simp only [upd_X, upd_Y, st9_Y]
  refine Runs.of_eval fun r => ?_
  obtain ⟨hBkl, hBkv⟩ := pad_spec k b hb
  set Bk := addT false (List.replicate k false) (encodeNat b) false with hBk
  have e1 := eval_pushK [] sT Sym.mark r (st9 (blk .down v ++ rest) (S sY) (natSyms k ++ r2)
    (natSyms w ++ r3) (natSyms b ++ r4) (S sA) (S sB) (S sT) (S sV))
  simp only [upd_T, st9_T] at e1
  obtain ⟨q2, t2, ht2, e2⟩ := copyP_eval (src := sBs) (dst := sT) (tmp := sV) (by decide)
    (by decide) (by decide) [] r (encodeNat b) r4 (st9 (blk .down v ++ rest) (S sY)
      (natSyms k ++ r2) (natSyms w ++ r3) (natSyms b ++ r4) (S sA) (S sB) (Sym.mark :: S sT)
      (S sV)) hr4 rfl
  simp only [upd_T, st9_T] at e2
  have e3 := eval_pushK [] sBs Sym.mark q2 (st9 (blk .down v ++ rest) (S sY) (natSyms k ++ r2)
    (natSyms w ++ r3) (natSyms b ++ r4) (S sA) (S sB) ((encodeNat b).map Sym.bit ++
      Sym.mark :: S sT) (S sV))
  simp only [upd_Bs, st9_Bs] at e3
  obtain ⟨q4, t4, ht4, e4⟩ := fillP_eval (Kc := sK) (D := sBs) (C := sA) (T := sV) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) false [] q2 k r2
    (st9 (blk .down v ++ rest) (S sY) (natSyms k ++ r2) (natSyms w ++ r3)
      (Sym.mark :: (natSyms b ++ r4)) (S sA) (S sB) ((encodeNat b).map Sym.bit ++
        Sym.mark :: S sT) (S sV)) hr2 rfl
  simp only [upd_Bs, st9_Bs] at e4
  obtain ⟨q5, t5, ht5, e5⟩ := addTP_eval false (X := sBs) (U := sT) (T := sA) (V := sV)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [] q4
    (List.replicate k false) (encodeNat b) (Sym.mark :: (natSyms b ++ r4)) (Sym.mark :: S sT)
    (TermOK.cons rfl _) (TermOK.cons rfl _) (st9 (blk .down v ++ rest) (S sY) (natSyms k ++ r2)
      (natSyms w ++ r3) (List.replicate k (Sym.bit false) ++ Sym.mark :: (natSyms b ++ r4))
      (S sA) (S sB) ((encodeNat b).map Sym.bit ++ Sym.mark :: S sT) (S sV))
    (by rw [st9_Bs, List.map_replicate]) rfl
  simp only [upd_Bs] at e5
  rw [← hBk] at e5
  have e6 := dropNum_eval (k := sT) [] q5 (encodeNat b) Sym.mark (S sT)
    (st9 (blk .down v ++ rest) (S sY) (natSyms k ++ r2) (natSyms w ++ r3)
      (Bk.map Sym.bit ++ Sym.mark :: (natSyms b ++ r4)) (S sA) (S sB)
      ((encodeNat b).map Sym.bit ++ Sym.mark :: S sT) (S sV)) rfl rfl
  simp only [upd_T] at e6
  obtain ⟨q7, t7, ht7, e7⟩ := route_spec w hw r3 hr3 rest hrest k Bk v (S sY) (natSyms k ++ r2)
    (natSyms b ++ r4) (S sA) (S sB) (S sT) (S sV) (some Sym.mark, q5.2) hBkl hv hrec
  have e8 := dropNum_eval (k := sBs) [] q7 Bk Sym.mark (natSyms b ++ r4)
    (st9 rest ((rt (encodeNat w) k Bk v).flatten ++ S sY) (natSyms k ++ r2) (natSyms w ++ r3)
      (Bk.map Sym.bit ++ Sym.mark :: (natSyms b ++ r4)) (S sA) (S sB) (S sT) (S sV)) rfl rfl
  simp only [upd_Bs] at e8
  have hrt : rt (encodeNat w) k Bk v = oddRouteL k w b v := by
    rw [rt_eq_oddRouteL w hw k Bk v hBkl hv, hBkv]
  rw [← hrt]
  refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 e8)))))), trivial, ?_⟩
  have hN : 2 ^ k ≤ (blk .down v).length := by
    rw [← hv]
    exact length_le_flatten hrec
  have hbl : (encodeNat b).length ≤ (blk .down v).length := by
    have := bitLen_le_self b
    omega
  rw [hBkl]
  rw [List.length_replicate] at ht5
  have key := top_cost (N := (blk .down v).length) (bl := (encodeNat b).length)
    (X := 1 + t2 + 1 + t5 + (2 * (encodeNat b).length + 2) + (2 * k + 2)) hN (lt_two_pow' k) hbl
    ht7 ht4 (by omega)
  omega

#assert_std_axioms oddRouteProg_closed W4_oddRoute_holds

end TMFw.W4o
