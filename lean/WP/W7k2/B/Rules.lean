import WP.W7k2.B.Base

/-!
# WP.W7k2.B.Rules — host rules of the builder's calls, and uniform-cost loop rules

* `HT.bcp`, `HT.bdr`, … : the `Ops.lean` / `Ops2.lean` rules specialised to `BL`, the bundle `BI`
  and its shared constant `C`;
* `HT.bcdU` (countdown loop) and `HT.bwlU` (`while x < y`): uniform per-iteration cost, bodies only
  for the iterations that run.
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-! ## Host rules -/

section Rules

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.bcp (hI : I.Spec Mul C) (x y : BL) (hxy : [x, y].Nodup) (B : BL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (BP I)) :
    HT ρ B (bcp I x y) (Function.update B y (natSyms v ++ B y)) (C * (bitLen v + 1)) :=
  HT.copyNat hI.cp d0 I.lcp x y hxy (by decide) B v r hr hB ρ

theorem HT.bdr (hI : I.Spec Mul C) (x : BL) (B : BL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (BP I)) :
    HT ρ B (bdr I x) (Function.update B x r) (C * (bitLen v + 1)) :=
  HT.dropNat hI.dr d0 I.ldr x (by decide) B v r hr hB ρ

theorem HT.bdc (hI : I.Spec Mul C) (x : BL) (B : BL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms (v + 1) ++ r) (ρ : List (BP I)) :
    HT ρ B (bdc I x) (Function.update B x (natSyms v ++ r)) (C * (bitLen (v + 1) + 1)) :=
  (HT.callI_upd I.dc [x] d0 (List.nodup_singleton _) rfl (by decide) I.ldc B (.inl 0) _
    (hI.dc v r _ hr hB) ρ).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (zerosLead_le_length _) 1))

theorem HT.bic (hI : I.Spec Mul C) (x : BL) (B : BL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (BP I)) :
    HT ρ B (bic I x) (Function.update B x (natSyms (v + 1) ++ r)) (C * (bitLen v + 1)) :=
  (HT.incNat hI.ic d0 I.lic x (by decide) B v r hr hB ρ).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (ones_le_length _) 1))

theorem HT.bad (hI : I.Spec Mul C) (x y z : BL) (hnd : [x, y, z].Nodup) (B : BL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (ρ : List (BP I)) :
    HT ρ B (bad I x y z) (Function.update B z (natSyms (u + v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.addNat hI.ad d0 I.lad x y z hnd (by decide) B u v ru rv hru hrv hx hy ρ

theorem HT.bs1 (hI : I.Spec Mul C) (x : BL) (B : BL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (BP I)) :
    HT ρ B (bs1 I x) (Function.update B x (natSyms (v * 2 ^ 1) ++ r)) (C * (1 + 1)) :=
  HT.shlConst hI.s1 d0 I.ls1 x (by decide) B v r hr hB ρ

theorem HT.br1 (hI : I.Spec Mul C) (x : BL) (B : BL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (BP I)) :
    HT ρ B (br1 I x) (Function.update B x (natSyms (v / 2 ^ 1) ++ r)) (C * (1 + 1)) :=
  HT.shrConst hI.r1 d0 I.lr1 x (by decide) B v r hr hB ρ

theorem HT.bsv (hI : I.Spec Mul C) (x c : BL) (hnd : [x, c].Nodup) (B : BL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) (ρ : List (BP I)) :
    HT ρ B (bsv I x c) (Function.update B x (natSyms (u * 2 ^ v) ++ ru))
      (C * (v + bitLen v + 1)) :=
  HT.shlVar hI.sv d0 I.lsv x c hnd (by decide) B u v ru rv hru hrv hx hc ρ

theorem HT.bcmIte (hI : I.Spec Mul C) (x y : BL) (hnd : [x, y].Nodup) (B B' : BL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (f : Ordering → Bool)
    (p q : BP I) (ρ : List (BP I)) {T₁ T₂ : ℕ} (hp : f (Lib.ordOf u v) = true → HT ρ B p B' T₁)
    (hq : f (Lib.ordOf u v) = false → HT ρ B q B' T₂) :
    HT ρ B ((bcm I x y).seq (.ite (fun s => f (I.cm.obs (I.lcm.get s))) p q)) B'
      (C * (bitLen u + bitLen v + 1) + (max T₁ T₂ + 1)) :=
  HT.cmpNat_ite hI.cm d0 I.lcm x y hnd (by decide) B B' u v ru rv hru hrv hx hy f p q ρ hp hq

theorem HT.bizIte (hI : I.Spec Mul C) (x : BL) (B B' : BL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (p q : BP I) (ρ : List (BP I)) {T₁ T₂ : ℕ}
    (hp : v = 0 → HT ρ B p B' T₁) (hq : v ≠ 0 → HT ρ B q B' T₂) :
    HT ρ B ((biz I x).seq (.ite (fun s => I.iz.obs (I.liz.get s)) p q)) B'
      (C + (max T₁ T₂ + 1)) :=
  HT.callI_test I.iz [x] d0 (List.nodup_singleton _) rfl (by decide) I.liz B B' (fun b => b)
    (decide (v = 0)) (hI.iz v r _ hr hB) p q ρ (fun h => hp (of_decide_eq_true h))
    (fun h => hq (of_decide_eq_false h))

theorem HT.bai (hI : I.Spec Mul C) (x y z : BL) (hnd : [x, y, z].Nodup) (B : BL → List Sym)
    (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) (ρ : List (BP I)) :
    HT ρ B (bai I x y z) (Function.update B z (intSyms (u + v) ++ B z))
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1)) :=
  HT.addInt hI.ai d0 I.lai x y z hnd (by decide) B u v ru rv hru hrv hx hy ρ

theorem HT.bmu (hI : I.Spec Mul C) (x y z : BL) (hnd : [x, y, z].Nodup) (B : BL → List Sym)
    (w : ℕ) (u v : ℤ) (ru rv : List Sym) (hwu : bitLen u.natAbs ≤ w) (hwv : bitLen v.natAbs ≤ w)
    (hru : TermOK ru) (hrv : TermOK rv) (hx : B x = intSyms u ++ ru)
    (hy : B y = intSyms v ++ rv) (ρ : List (BP I)) :
    HT ρ B (bmu I x y z) (Function.update B z (intSyms (u * v) ++ B z)) (C * Mul w + C) :=
  HT.mul hI.mu d0 I.lmu x y z hnd (by decide) B w u v ru rv hwu hwv hru hrv hx hy ρ

theorem HT.bdm (hI : I.Spec Mul C) (x y q r : BL) (hnd : [x, y, q, r].Nodup) (B : BL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hv : 0 < v) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (ρ : List (BP I)) :
    HT ρ B (bdm I x y q r)
      (Function.update (Function.update B q (natSyms (u / v) ++ B q)) r (natSyms (u % v) ++ B r))
      (C * (bitLen u * bitLen v + bitLen u + bitLen v + 1)) :=
  HT.divModNat hI.dm d0 I.ldm x y q r hnd (by decide) B u v ru rv hv hru hrv hx hy ρ

theorem HT.bsf (hI : I.Spec Mul C) (sq sn sd z : BL) (hnd : [sq, sn, sd, z].Nodup)
    (B : BL → List Sym) (q num den : ℕ) (r0 r1 r2 : List Sym) (hden : 0 < den) (hnum : num ≤ den)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (e0 : B sq = natSyms q ++ r0)
    (e1 : B sn = natSyms num ++ r1) (e2 : B sd = natSyms den ++ r2) (ρ : List (BP I)) :
    HT ρ B (bsf I sq sn sd z)
      (Function.update B z
        (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den false).1 ++ B z))
      (C * (q + bitLen den + 1) ^ 4) :=
  HT.stdChar hI.sf d0 I.lsf sq sn sd z hnd (by decide) B q num den r0 r1 r2 hden hnum h0 h1 h2
    e0 e1 e2 ρ

theorem HT.bst (hI : I.Spec Mul C) (sq sn sd z : BL) (hnd : [sq, sn, sd, z].Nodup)
    (B : BL → List Sym) (q num den : ℕ) (r0 r1 r2 : List Sym) (hden : 0 < den) (hnum : num ≤ den)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (e0 : B sq = natSyms q ++ r0)
    (e1 : B sn = natSyms num ++ r1) (e2 : B sd = natSyms den ++ r2) (ρ : List (BP I)) :
    HT ρ B (bst I sq sn sd z)
      (Function.update B z
        (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den true).1 ++ B z))
      (C * (q + bitLen den + 1) ^ 4) :=
  HT.stdChar hI.st d0 I.lst sq sn sd z hnd (by decide) B q num den r0 r1 r2 hden hnum h0 h1 h2
    e0 e1 e2 ρ

theorem HT.btp (hI : I.Spec Mul C) (s0 s1 s2 s3 s4 s5 s6 z : BL)
    (hnd : [s0, s1, s2, s3, s4, s5, s6, z].Nodup) (B : BL → List Sym) (p_work pSub t1 j1 s : ℕ)
    (r0 r1 r2 r3 r4 r5 r6 : List Sym) (a1 : 0 < p_work) (a2 : 0 < pSub) (a3 : 0 < t1)
    (a4 : j1 < t1) (a5 : s < 2 * pSub + 1)
    (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2) (b3 : TermOK r3) (b4 : TermOK r4)
    (b5 : TermOK r5) (b6 : TermOK r6)
    (e0 : B s0 = natSyms p_work ++ r0) (e1 : B s1 = natSyms pSub ++ r1)
    (e2 : B s2 = natSyms t1 ++ r2) (e3 : B s3 = natSyms j1 ++ r3) (e4 : B s4 = natSyms s ++ r4)
    (e5 : B s5 = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1 ++ r5)
    (e6 : B s6 = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1 ++ r6)
    (ρ : List (BP I)) :
    HT ρ B (btp I s0 s1 s2 s3 s4 s5 s6 z)
      (Function.update B z
        (intSyms (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1 ++ B z))
      (C * (p_work + pSub + bitLen t1 + 1) ^ 4) :=
  HT.tap hI.tp d0 I.ltp s0 s1 s2 s3 s4 s5 s6 z hnd (by decide) B p_work pSub t1 j1 s
    r0 r1 r2 r3 r4 r5 r6 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 e0 e1 e2 e3 e4 e5 e6 ρ

theorem HT.bcc (hI : I.Spec Mul C) (s0 s1 s2 s3 z : BL) (hnd : [s0, s1, s2, s3, z].Nodup)
    (B : BL → List Sym) (p_work pSub r u2 : ℕ) (r0 r1 r2 r3 : List Sym) (a1 : 0 < p_work)
    (a2 : 0 < r) (a3 : u2 < r) (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2)
    (b3 : TermOK r3) (e0 : B s0 = natSyms p_work ++ r0) (e1 : B s1 = natSyms pSub ++ r1)
    (e2 : B s2 = natSyms r ++ r2) (e3 : B s3 = natSyms u2 ++ r3) (ρ : List (BP I)) :
    HT ρ B (bcc I s0 s1 s2 s3 z)
      (Function.update B z
        (intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.1.1 ++
          intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.2.1 ++ B z))
      (C * (p_work + pSub + bitLen r + 1) ^ 4) :=
  HT.c0c1 hI.cc d0 I.lcc s0 s1 s2 s3 z hnd (by decide) B p_work pSub r u2 r0 r1 r2 r3 a1 a2 a3
    b0 b1 b2 b3 e0 e1 e2 e3 ρ

theorem HT.bcr (hI : I.Spec Mul C) (s0 s1 s2 s3 s4 z : BL) (hnd : [s0, s1, s2, s3, s4, z].Nodup)
    (B : BL → List Sym) (H r u2 : ℕ) (x w : ℤ) (r0 r1 r2 r3 r4 : List Sym)
    (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 x w)
    (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2) (b3 : TermOK r3) (b4 : TermOK r4)
    (e0 : B s0 = natSyms H ++ r0) (e1 : B s1 = natSyms r ++ r1) (e2 : B s2 = natSyms u2 ++ r2)
    (e3 : B s3 = intSyms x ++ r3) (e4 : B s4 = intSyms w ++ r4) (ρ : List (BP I)) :
    HT ρ B (bcr I s0 s1 s2 s3 s4 z)
      (Function.update B z (intSyms (W7.colRecip H r u2 x w) ++ B z))
      (C * ((H + 1) * (bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 x w).natAbs + 1) +
        bitLen r + bitLen u2 + bitLen x.natAbs + bitLen w.natAbs + 1)) :=
  HT.colRecip hI.cr d0 I.lcr s0 s1 s2 s3 s4 z hnd (by decide) B H r u2 x w r0 r1 r2 r3 r4 hd
    b0 b1 b2 b3 b4 e0 e1 e2 e3 e4 ρ

theorem HT.bpi (hI : I.Spec Mul C) (x z : BL) (hnd : [x, z].Nodup) (B : BL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (BP I)) :
    HT ρ B (bpi I x z)
      (Function.update B z (intSyms (IntMul.computablePiScaledWithCost v).1 ++ B z))
      (C * (v + 1) ^ 4) :=
  HT.piScaled hI.pi d0 I.lpi x z hnd (by decide) B v r hr hB ρ

theorem HT.bln (hI : I.Spec Mul C) (x z : BL) (hnd : [x, z].Nodup) (B : BL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (BP I)) :
    HT ρ B (bln I x z)
      (Function.update B z (intSyms (IntMul.computableLog2ScaledWithCost v).1 ++ B z))
      (C * (v + 1) ^ 4) :=
  HT.log2Scaled hI.ln d0 I.lln x z hnd (by decide) B v r hr hB ρ

end Rules

/-! ## Loops with uniform iteration cost -/

theorem loopCost_le_of_lt (B : ℕ → ℕ) (b : ℕ) :
    ∀ n, (∀ k < n, B k ≤ b) → loopCost B n ≤ n * (b + 1) + 1
  | 0, _ => by simp [loopCost]
  | n + 1, h => by
    have ih := loopCost_le_of_lt B b n (fun k hk => h k (by omega))
    have := h n (by omega)
    simp only [loopCost]
    rw [Nat.succ_mul]
    omega

section Loops

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

/-- **Countdown loop, uniform cost.** `St i` is the state with counter `i`; the body turns
`St (i+1)` with the counter already decremented to `i` into `St i`, for the iterations `i < n`
that run. -/
theorem HT.bcdU (hI : I.Spec Mul C) (ctr : BL) (rc : List Sym) (hrc : TermOK rc)
    (St : ℕ → BL → List Sym) (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : BP I) (n cb : ℕ)
    (ρ : List (BP I))
    (hbody : ∀ i < n, HT ρ (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) cb) :
    HT ρ (St n) (bcd I ctr body) (St 0) (n * (C * (bitLen n + 1) + cb + C + 1) + C + 1) := by
  have htest : ∀ i, Triple ρ (fun s => s.stk = St i) (callI I.iz [ctr] d0 I.liz)
      (fun s => s.stk = St i ∧ I.iz.obs (I.liz.get s.var) = decide (i = 0)) C := fun i =>
    callI_same I.iz [ctr] d0 (List.nodup_singleton _) rfl (by decide) I.liz (St i)
      (hI.iz i rc _ hrc (hSt i)) ρ
  have hloop := Triple.loop (ρ := ρ) (c := fun v => !(I.iz.obs (I.liz.get v)))
    (p := ((callI I.dc [ctr] d0 I.ldc).seq body).seq (callI I.iz [ctr] d0 I.liz))
    (I := fun k s => k ≤ n ∧ s.stk = St k ∧ I.iz.obs (I.liz.get s.var) = decide (k = 0))
    (B := fun k => C * (bitLen (k + 1) + 1) + cb + C) ?_ ?_ ?_ n
  · have hlc := loopCost_le_of_lt (fun k => C * (bitLen (k + 1) + 1) + cb + C)
      (C * (bitLen n + 1) + cb + C) n (fun k hk => by
        have h1 : bitLen (k + 1) ≤ bitLen n := bitLen_mono (by omega)
        have h2 : C * (bitLen (k + 1) + 1) ≤ C * (bitLen n + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        show C * (bitLen (k + 1) + 1) + cb + C ≤ C * (bitLen n + 1) + cb + C
        omega)
    refine (Triple.seq (htest n) (Triple.conseq hloop (fun s hs => ⟨le_rfl, hs⟩)
      (fun s hs => hs.2.1) le_rfl)).cost_mono ?_
    omega
  · intro k
    by_cases hk : k + 1 ≤ n
    · have hdec : HT ρ (St (k + 1)) (callI I.dc [ctr] d0 I.ldc)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (C * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
        HT.callI_upd I.dc [ctr] d0 (List.nodup_singleton _) rfl (by decide) I.ldc (St (k + 1))
          (.inl 0) _ (hI.dc k rc _ hrc (hSt (k + 1))) ρ
      have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
        zerosLead_le_length _
      have h1 := Triple.seq (Triple.seq hdec (hbody k (by omega))) (htest k)
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) ?_
      have : C * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤ C * (bitLen (k + 1) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      show _ ≤ C * (bitLen (k + 1) + 1) + cb + C
      omega
    · intro s hs
      exact absurd hs.1 hk
  · intro k s hs
    simp [hs.2.2]
  · intro s hs
    simp [hs.2.2]

/-- **`while x < y`, uniform cost.** `St i` is the state after `i` iterations, with `x = xv i`
and `y = yv` fixed; the loop runs exactly `n` times (`xv i < yv` for `i < n`, `yv ≤ xv n`). -/
theorem HT.bwlU (hI : I.Spec Mul C) (x y : BL) (hxy : [x, y].Nodup) (St : ℕ → BL → List Sym)
    (xv : ℕ → ℕ) (yv : ℕ) (rx : ℕ → List Sym) (ry : List Sym) (hrx : ∀ i, TermOK (rx i))
    (hry : TermOK ry) (hX : ∀ i, St i x = natSyms (xv i) ++ rx i)
    (hY : ∀ i, St i y = natSyms yv ++ ry) (n : ℕ) (hlt : ∀ i < n, xv i < yv) (hge : yv ≤ xv n)
    (body : BP I) (cb bx : ℕ) (hbx : ∀ i ≤ n, bitLen (xv i) ≤ bx) (ρ : List (BP I))
    (hbody : ∀ i < n, HT ρ (St i) body (St (i + 1)) cb) :
    HT ρ (St 0) (bwl I x y body) (St n)
      (n * (cb + C * (bx + bitLen yv + 1) + 1) + C * (bx + bitLen yv + 1) + 1) := by
  have htest : ∀ i ≤ n, Triple ρ (fun s => s.stk = St i) (bcm I x y)
      (fun s => s.stk = St i ∧ I.cm.obs (I.lcm.get s.var) = Lib.ordOf (xv i) yv)
      (C * (bx + bitLen yv + 1)) := fun i hi =>
    (callI_same I.cm [x, y] d0 hxy rfl (by decide) I.lcm (St i)
      (hI.cm (xv i) yv (rx i) ry _ (hrx i) hry (hX i) (hY i)) ρ).cost_mono
      (Nat.mul_le_mul_left _ (by have := hbx i hi; omega))
  have hloop := Triple.loop (ρ := ρ) (c := fun v => decide (I.cm.obs (I.lcm.get v) = .lt))
    (p := body.seq (bcm I x y))
    (I := fun k s => k ≤ n ∧ s.stk = St (n - k) ∧
      I.cm.obs (I.lcm.get s.var) = Lib.ordOf (xv (n - k)) yv)
    (B := fun _ => cb + C * (bx + bitLen yv + 1)) ?_ ?_ ?_ n
  · refine (Triple.seq (htest 0 (Nat.zero_le _)) (Triple.conseq hloop
      (fun s hs => ⟨le_rfl, by rw [Nat.sub_self]; exact hs.1, by rw [Nat.sub_self]; exact hs.2⟩)
      (fun s hs => by rw [← Nat.sub_zero n]; exact hs.2.1) le_rfl)).cost_mono ?_
    rw [loopCost_const]
    omega
  · intro k
    by_cases hk : k + 1 ≤ n
    · have e : n - (k + 1) + 1 = n - k := by omega
      have h1 := Triple.seq (hbody (n - (k + 1)) (by omega)) (htest (n - (k + 1) + 1) (by omega))
      rw [e] at h1
      exact Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) le_rfl
    · intro s hs
      exact absurd hs.1 hk
  · intro k s hs
    obtain ⟨hk, -, ho⟩ := hs
    simp only [ho, decide_eq_true_eq]
    unfold Lib.ordOf
    rw [if_pos (hlt _ (by omega))]
  · intro s hs
    obtain ⟨-, -, ho⟩ := hs
    rw [Nat.sub_zero] at ho
    simp only [ho, decide_eq_false_iff_not]
    unfold Lib.ordOf
    rw [if_neg (by omega)]
    split_ifs <;> simp

end Loops

/-! ## Small encoding facts -/

theorem natSyms_zero : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem intSyms_zero : intSyms 0 = [Sym.pos] := by
  simp [intSyms, sgnSym, natSyms_zero]

#assert_std_axioms HT.bcp HT.bdr HT.bdc HT.bic HT.bad HT.bs1 HT.br1 HT.bsv HT.bcmIte
  HT.bizIte HT.bai HT.bmu HT.bdm HT.bsf HT.bst HT.btp HT.bcc HT.bcr HT.bpi HT.bln
  loopCost_le_of_lt HT.bcdU HT.bwlU natSyms_zero intSyms_zero

end WP.W7k2
