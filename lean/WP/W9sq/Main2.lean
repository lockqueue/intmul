import WP.W9sq.Main1

/-!
# WP.W9sq.Main2 — the stage program over the host, with the init phase as a parameter

`sqProg J initP`: push `mark` floors on `flr`; `initP` (constants `q`, `2^(q-1)`, `2^(q-1) − 1`
on `sQ, sH, sH1`, state `stI`); the entry loop; transfer `sO → S` down to `sO`'s floor; drop the
constants; pop the floors. `sq_spec` proves it from a triple for `initP` (`WP.W9sq.Init` supplies
one), with `q = qOf b K0 = rootPrecision b K0 + 2`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Floors pushed at the start (`sO`'s floor is the transfer sentinel). -/
def flr : List HL :=
  [sO, sX, sX2, sY, sY2, sP1, sP2, sP3, sP4, sD, sE, sR, sI, sQ, sH, sH1, sA, sT1]

/-- Floors popped at the end (`sO`'s was consumed by the transfer). -/
def flr' : List HL :=
  [sX, sX2, sY, sY2, sP1, sP2, sP3, sP4, sD, sE, sR, sI, sQ, sH, sH1, sA, sT1]

theorem flr_nodup : flr.Nodup := by decide
theorem flr'_nodup : flr'.Nodup := by decide

/-- The shift `q = rootPrecision b K0 + 2`. -/
def qOf (b K0 : ℕ) : ℕ := 2 * b + 2 * K0 + 8

theorem qOf_eq (b K0 : ℕ) : qOf b K0 = rootPrecision b K0 + 2 := by
  unfold qOf rootPrecision
  omega

theorem floorSt_mem (B : HL → List Sym) :
    ∀ (ks : List HL), ks.Nodup → ∀ k ∈ ks, floorSt B ks k = Sym.mark :: B k
  | [], _, k, hk => absurd hk (List.not_mem_nil)
  | j :: ks, hnd, k, hk => by
    rw [floorSt]
    by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self]
    · rw [Function.update_of_ne hkj]
      exact floorSt_mem B ks (List.nodup_cons.mp hnd).2 k
        (by rcases List.mem_cons.mp hk with h | h; exact absurd h hkj; exact h)

theorem eq_floorSt {S T : HL → List Sym} (ks : List HL) (hnd : ks.Nodup)
    (h1 : ∀ k ∈ ks, S k = Sym.mark :: T k) (h2 : ∀ k, k ∉ ks → S k = T k) : S = floorSt T ks := by
  funext k
  by_cases hk : k ∈ ks
  · rw [h1 k hk, floorSt_mem T ks hnd k hk]
  · rw [h2 k hk, floorSt_of_not_mem T ks hk]

/-- The state after the init phase. -/
def stI (B : HL → List Sym) (b K0 : ℕ) : HL → List Sym :=
  Function.update (Function.update (Function.update (floorSt B flr) sQ
    (natSyms (2 * b + 2 * K0 + 8) ++ floorSt B flr sQ)) sH
      (natSyms (2 ^ (2 * b + 2 * K0 + 7)) ++ floorSt B flr sH)) sH1
        (natSyms (2 ^ (2 * b + 2 * K0 + 7) - 1) ++ floorSt B flr sH1)

/-- Cleanup: drop the three constants, pop the floors. -/
def finP (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (callI J.dr [sQ] dfl J.lDr).seq <| (callI J.dr [sH] dfl J.lDr).seq <|
    (callI J.dr [sH1] dfl J.lDr).seq (popMarks flr')

/-- **The stage program** (host), given the init phase. -/
def sqProg (J : SqI) (initP : Prog HL (fun _ => Sym) J.Reg) : Prog HL (fun _ => Sym) J.Reg :=
  (pushMarks flr).seq <| initP.seq <| (peekLoop J.lS hS symNode (entryP J)).seq <|
    (xferLoop J.lS sO hS Sym.mark).seq (finP J)

theorem sqProg_closed (J : SqI) (initP : Prog HL (fun _ => Sym) J.Reg) (h : initP.Closed) :
    (sqProg J initP).Closed :=
  ⟨pushMarks_closed _, h, peekLoop_closed _ _ _ _ (entryP_closed J), xferLoop_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, popMarks_closed _⟩

theorem mark_not_mem_intSyms (z : ℤ) : Sym.mark ∉ intSyms z := by
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map, not_or]
  refine ⟨?_, ?_⟩
  · unfold sgnSym
    split_ifs <;> decide
  · rintro ⟨b, -, h⟩
    cases h

theorem mark_not_mem_entrySyms (e : ℤ × ℤ) : Sym.mark ∉ entrySyms e := by
  simp only [entrySyms, List.mem_append, List.mem_cons, not_or]
  refine ⟨mark_not_mem_intSyms _, by decide, mark_not_mem_intSyms _, by decide, by simp⟩

theorem stream_eq (z : Array (ℤ × ℤ)) (restS : List Sym) :
    streamSyms [z] ++ restS = (z.toList.map entrySyms).flatten ++ symNode :: symLevel :: restS := by
  simp [streamSyms, nodeSyms, blkE, blk]

#assert_std_axioms flr_nodup flr'_nodup qOf_eq floorSt_mem eq_floorSt sqProg_closed
  mark_not_mem_intSyms mark_not_mem_entrySyms stream_eq

end WP.W9sq
