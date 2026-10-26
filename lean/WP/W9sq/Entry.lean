import WP.W9sq.Entry2

/-!
# WP.W9sq.Entry — one stream entry, end to end

`entryP = parseP; mulP; dropP; rndP; emitP`. From any state with the entry `(x, y)` on top of
`S`, `TermOK` temporaries and the constants `q`, `2^(q-1)`, `2^(q-1) − 1` on `sQ, sH, sH1`, it
pops the entry and pushes `(entrySyms (sqE q (x, y))).reverse` on `sO`; every other stack is
restored. Cost `entB C Mul wR q = 4·C·Mul wR + 100·(C+1)·(wR + q + 1)`: four products at width
`wR`, everything else linear in `wR + q`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- One entry: parse, products, drop, round, emit. -/
def entryP (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (parseP J).seq <| (mulP J).seq <| (dropP J).seq <| (rndP J).seq (emitP J)

theorem entryP_closed (J : SqI) : (entryP J).Closed :=
  ⟨parseP_closed J, mulP_closed J, dropP_closed J, rndP_closed J, emitP_closed J⟩

/-- Per-entry cost bound. -/
def entB (C : ℕ) (Mul : ℕ → ℕ) (wR q : ℕ) : ℕ :=
  4 * (C * Mul wR) + 100 * (C + 1) * (wR + q + 1)

theorem mul_le_k {C y X k : ℕ} (h : y ≤ k * X) : C * y ≤ k * (C * X) :=
  calc C * y ≤ C * (k * X) := Nat.mul_le_mul_left _ h
    _ = k * (C * X) := by ring

theorem entry_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (B0 : HL → List Sym)
    (wR q : ℕ) (hq : 0 < q) (x y : ℤ) (hx : bitLen x.natAbs ≤ wR) (hy : bitLen y.natAbs ≤ wR)
    (hout : EntryW wR (sqE q (x, y))) (REST : List Sym) (hS0 : B0 hS = entrySyms (x, y) ++ REST)
    (tX : TermOK (B0 sX)) (tX2 : TermOK (B0 sX2)) (tY : TermOK (B0 sY)) (tY2 : TermOK (B0 sY2))
    (tP1 : TermOK (B0 sP1)) (tP2 : TermOK (B0 sP2)) (tP3 : TermOK (B0 sP3))
    (tP4 : TermOK (B0 sP4)) (tD : TermOK (B0 sD)) (tE : TermOK (B0 sE)) (tR : TermOK (B0 sR))
    (tI : TermOK (B0 sI)) (rQ rH rH1 : List Sym) (hrQ : TermOK rQ) (hrH : TermOK rH)
    (hrH1 : TermOK rH1) (eQ : B0 sQ = natSyms q ++ rQ) (eH : B0 sH = natSyms (2 ^ (q - 1)) ++ rH)
    (eH1 : B0 sH1 = natSyms (2 ^ (q - 1) - 1) ++ rH1) :
    HT [] B0 (entryP J)
      (Function.update (Function.update B0 hS REST) sO
        ((entrySyms (sqE q (x, y))).reverse ++ B0 sO))
      (entB C Mul wR q) := by
  have h1 := parse_spec J hJ B0 x y REST hS0 tX tY
  have h2 := mul_spec J hJ (stA B0 x y REST) wR x y hx hy (B0 sX) (B0 sX2) (B0 sY) (B0 sY2)
    tX tX2 tY tY2 (by simpa [stA] using tP1) (by simpa [stA] using tP2)
    (by simpa [stA] using tP3) (by simpa [stA] using tP4) (by simp [stA]) (by simp [stA])
    (by simp [stA]) (by simp [stA])
  have h3 := drop_spec J hJ B0 x y REST tX tX2 tY tY2 tP1 tP2 tP3 tP4
  have h4 := rnd_spec J hJ B0 REST (x * x - y * y) (x * y + y * x) q hq rQ rH rH1 hrQ hrH hrH1
    eQ eH eH1 tD tE tR tI
  have h5 := emit_spec J B0 REST (divRoundPow2 (x * x - y * y) q)
    (-divRoundPow2 (x * y + y * x) q) tR tI
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 (HT.seq h4 h5)))).of_eq rfl ?_
  -- cost
  obtain ⟨hre, him⟩ := hout
  have hre' : bitLen (divRoundPow2 (x * x - y * y) q).natAbs ≤ wR := hre
  have him' : bitLen (-divRoundPow2 (x * y + y * x) q).natAbs ≤ wR := him
  have hxx := bitLen_natAbs_mul_le hx hx
  have hyy := bitLen_natAbs_mul_le hy hy
  have hxy := bitLen_natAbs_mul_le hx hy
  have hyx := bitLen_natAbs_mul_le hy hx
  have hw1 := bitLen_natAbs_sub_le hxx hyy
  have hw2 := bitLen_natAbs_add_le hxy hyx
  have hbq := bitLen_le_self q
  obtain ⟨X, hX⟩ : ∃ X, X = wR + q + 1 := ⟨_, rfl⟩
  have f1 : C * (bitLen x.natAbs + 1) ≤ 1 * (C * X) := mul_le_k (by omega)
  have f2 : C * (bitLen y.natAbs + 1) ≤ 1 * (C * X) := mul_le_k (by omega)
  have f3 : C * (4 * wR + 1) ≤ 4 * (C * X) := mul_le_k (by omega)
  have f4 : C * (bitLen (x * x).natAbs + 1) ≤ 2 * (C * X) := mul_le_k (by omega)
  have f5 : C * (bitLen (y * y).natAbs + 1) ≤ 2 * (C * X) := mul_le_k (by omega)
  have f6 : C * (bitLen (x * y).natAbs + 1) ≤ 2 * (C * X) := mul_le_k (by omega)
  have f7 : C * (bitLen (y * x).natAbs + 1) ≤ 2 * (C * X) := mul_le_k (by omega)
  have f8 : C * (bitLen (x * x - y * y).natAbs + q + 1) ≤ 3 * (C * X) := mul_le_k (by omega)
  have f9 : C * (bitLen (x * y + y * x).natAbs + q + 1) ≤ 3 * (C * X) := mul_le_k (by omega)
  have f10 : C * (q + bitLen q + 1) ≤ 2 * (C * X) := mul_le_k (by omega)
  have f11 : C * (bitLen (x * x - y * y).natAbs + 1) ≤ 2 * (C * X) := mul_le_k (by omega)
  have f12 : C * (bitLen (x * y + y * x).natAbs + 1) ≤ 2 * (C * X) := mul_le_k (by omega)
  have f13 : C ≤ 1 * (C * X) := mul_le_k (y := 1) (by omega) |>.trans_eq' (by ring)
  have e : 100 * (C + 1) * X = 100 * (C * X) + 100 * X := by ring
  unfold entB
  rw [← hX, e]
  omega

#assert_std_axioms entryP_closed mul_le_k entry_spec

end WP.W9sq
