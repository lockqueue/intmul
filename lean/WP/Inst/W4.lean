import WP.W4.Main
import WP.W4f.Top
import WP.W4o.OddRoute
import Mathlib.Tactic.Ring

/-!
# WP.Inst.W4 — concrete instances of the W4 routing contracts

Same convention as `WP.Inst.W3`: one namespace `WP.Inst.<c>` per contract, exporting the witnesses of
its proof as plain definitions (`m`, `R`, `r0`, `obs`, `prog`, `closed`), and `ok : <Contract>` proved
with **exactly** these definitions (the proofs are those of the packages' `_holds` theorems, with the
program replaced by the instance definition). All three contracts are hypothesis-free.

| contract | program | `m` | `R` | `r0` | `C` | proof source |
|---|---|---|---|---|---|---|
| `W4_transpose oi oo` | `TMFw.W4.transposeProg oi oo` | 4 | `CReg` | `(none, none, .eq)` | 64 | `TMFw.W4.w4_transpose_of_riff` |
| `W4_oddStrideFactor` | `WP.W4f.oddProg` | 4 | `WP.W4f.Reg` | `(none, false, false)` | 40 | `WP.W4f.W4_oddStrideFactor_holds` |
| `W4_oddRoute .down .down` | `TMFw.W4o.oddRouteProg` | 4 | `TMFw.W4o.Reg` | `(none, none, false)` | 300 | `TMFw.W4o.W4_oddRoute_holds` |
-/

namespace WP.Inst

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## `W4_transpose oi oo` -/

namespace transpose
abbrev m : ℕ := 4
abbrev R : Type := CReg
def r0 : R := (none, none, .eq)
def obs : R → Unit := fun _ => ()
def prog (oi oo : Orient) : Prog (Loc 4 m) (fun _ => Sym) R := TMFw.W4.transposeProg oi oo
theorem closed (oi oo : Orient) : (prog oi oo).Closed :=
  TMFw.W4.transposeProgP_closed TMFw.W4.riffOK.1 oi oo
end transpose

theorem transpose.ok (oi oo : Orient) : W4_transpose oi oo := by
  refine ⟨64, fun _ => ⟨transpose.m, transpose.R, transpose.obs, transpose.prog oi oo, le_rfl,
    inferInstance, ⟨transpose.r0⟩, transpose.closed oi oo, ?_⟩⟩
  intro a b v rest r2 r3 S hlen hrec hrest hr2 hr3 hS0 hS2 hS3
  have hblk : (blk oi v).length = v.flatten.length := by cases oi <;> simp [blk]
  have hNL : 2 ^ a * 2 ^ b ≤ v.flatten.length := by
    rw [← hlen]
    exact TMFw.W4.length_le_length_flatten v hrec
  rw [hblk]
  exact Triple.cost_mono (TMFw.W4.transposeProgP_spec TMFw.W4.riffOK oi oo a b v rest r2 r3 S hlen
    hrec hrest hr2 hr3 hS0 hS2 hS3) (TMFw.W4.cost_le a b _ hNL)

/-! ## `W4_oddStrideFactor` -/

namespace oddStrideFactor
abbrev m : ℕ := 4
abbrev R : Type := WP.W4f.Reg
def r0 : R := (none, false, false)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R := WP.W4f.oddProg
theorem closed : prog.Closed := WP.W4f.oddProgG_closed _ _ _ _ _ _ _
end oddStrideFactor

theorem oddStrideFactor.ok : W4_oddStrideFactor := by
  refine ⟨40, fun _ => ⟨oddStrideFactor.m, oddStrideFactor.R, oddStrideFactor.obs,
    oddStrideFactor.prog, le_refl _, inferInstance, ⟨oddStrideFactor.r0⟩, oddStrideFactor.closed,
    ?_⟩⟩
  intro k u2 r0 r1 S hr0 hr1 hK hU
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, ht, e⟩ := WP.W4f.oddProg_eval k u2 r0 r1 hr0 hr1 v S hK hU
  refine ⟨v', t, e, trivial, ?_⟩
  have hsq : (k + 1) ^ 2 = (k + 1) * (k + 1) := by ring
  rw [hsq]
  exact le_trans ht (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))

/-! ## `W4_oddRoute .down .down` -/

namespace oddRoute
abbrev m : ℕ := 4
abbrev R : Type := TMFw.W4o.Reg
def r0 : R := (none, none, false)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 5 m) (fun _ => Sym) R := TMFw.W4o.oddRouteProg
theorem closed : prog.Closed := TMFw.W4o.oddRouteProg_closed
end oddRoute

section OddRoute

open TMFw.W4o

theorem oddRoute.ok : W4_oddRoute .down .down := by
  refine ⟨300, fun _ => ⟨oddRoute.m, oddRoute.R, oddRoute.obs, oddRoute.prog, le_refl 4,
    inferInstance, ⟨oddRoute.r0⟩, oddRoute.closed, ?_⟩⟩
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
    have := TMFw.W4o.bitLen_le_self b
    omega
  rw [hBkl]
  rw [List.length_replicate] at ht5
  have key := top_cost (N := (blk .down v).length) (bl := (encodeNat b).length)
    (X := 1 + t2 + 1 + t5 + (2 * (encodeNat b).length + 2) + (2 * k + 2)) hN (lt_two_pow' k) hbl
    ht7 ht4 (by omega)
  omega

end OddRoute

#assert_std_axioms transpose.closed transpose.ok oddStrideFactor.closed oddStrideFactor.ok
  oddRoute.closed oddRoute.ok

end WP.Inst
