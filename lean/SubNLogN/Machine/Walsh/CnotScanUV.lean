/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanUVWalk
import SubNLogN.Machine.Walsh.CnotScanMask
import SubNLogN.Machine.Walsh.CnotScanShift

/-!
# `SubNLogN.Machine.Walsh.CnotScanUV`: the `U`-vector of a CNOT batch

Paper: Lemma 5.1 (`lem:walsh-select`: `U = Sel ∖ T`, `Sel = slicePos m K j₀ D ρ`,
`T = targets pairs`) and Definition 5.6 (`def:walsh-positional`). Plan: top of
`Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** The program `uvBuild` reads the slice header (`.inl 1`) and the pair
list (`.inl 2`), both restored, and leaves on the scratch stack `uv` the bits
`uvSyms m U = ((List.finRange m).reverse.map fun p => decide (p ∈ U)).map Sym.bit`
(position `m - 1` on top), `U = slicePos m K j₀ D ρ ∖ targets pairs` (`runs_uvBuild`), every other
stack restored, within `uvCost` (`uvCost_le`). Phases: header fields in unary (`hdrUnary`),
`K - 1 - ρ` (`subRho`), the slice mask with position `0` on top (`maskBuild`), clearing every
target position (`tgtClear`), the final reversal onto `uv`.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift Computability
open SubNLogN.Math.Walsh SubNLogN.Math.Common
open WP.W9comp (runs_seq runs_mono runs_congr)

/-- The `U`-vector on a stack, position `m - 1` on top. -/
def uvSyms (m : ℕ) (U : Finset (Fin m)) : List Sym :=
  ((List.finRange m).reverse.map fun p => decide (p ∈ U)).map Sym.bit

/-! ## Header fields in unary -/

/-- Skip `k` fields of `src` onto `pk`, then put the next field in unary on `dst`. -/
def skipUnary (src pk dst bits u : SK) (k : ℕ) : SProg SK :=
  .seq (WalshCnot1.skipFields src pk k) (unaryOfTop src dst bits u)

theorem closed_skipUnary (src pk dst bits u : SK) (k : ℕ) : (skipUnary src pk dst bits u k).Closed :=
  WP.W9comp.closed_seq (WalshCnot1.closed_skipFields _ _ _) (closed_unaryOfTop _ _ _ _)

theorem runs_skipUnary {src pk dst bits u : SK} (hsp : src ≠ pk) (h1 : src ≠ dst)
    (h2 : src ≠ bits) (h3 : src ≠ u) (h4 : dst ≠ bits) (h5 : dst ≠ u) (h6 : bits ≠ u)
    (hpd : pk ≠ dst) (hpb : pk ≠ bits) (hpu : pk ≠ u) (fs : List ℕ) (n : ℕ) (rest : List Sym)
    (S : SK → List Sym) (hS : S src = hdrSyms fs ++ (natSyms n ++ Sym.mark :: rest))
    (hb : S bits = []) (hd : S dst = []) (hu : S u = []) :
    Runs (skipUnary src pk dst bits u fs.length) S
      (Function.update (Function.update (Function.update S src (natSyms n ++ Sym.mark :: rest))
        pk ((hdrSyms fs).reverse ++ S pk)) dst (List.replicate n uSym))
      (fun _ => True) (3 * (hdrSyms fs).length + 1 + (20 * n + 5)) :=
  runs_seq (runs_skipFields hsp _ fs S hS)
    (runs_unaryOfTop h1 h2 h3 h4 h5 h6 n rest _
      (by rw [Function.update_of_ne hsp, Function.update_self])
      (by rw [Function.update_of_ne hpb.symm, Function.update_of_ne h2.symm, hb])
      (by rw [Function.update_of_ne hpd.symm, Function.update_of_ne h1.symm, hd])
      (by rw [Function.update_of_ne hpu.symm, Function.update_of_ne h3.symm, hu]))

/-- Unary copies `n2 = uSym^K`, `n3 = uSym^j₀`, `n4 = uSym^D`, `n5 = uSym^nS`, `tmp = uSym^ρ`. -/
def hdrUnary : SProg SK :=
  .seq (skipUnary (.inl 1) (.inr .pk) (.inr .n2) (.inr .n1) (.inr .u) 4)
  (.seq (skipUnary (.inl 1) (.inr .pk) (.inr .n3) (.inr .n1) (.inr .u) 2)
  (.seq (skipUnary (.inl 1) (.inr .pk) (.inr .n4) (.inr .n1) (.inr .u) 1)
  (.seq (skipUnary (.inl 1) (.inr .pk) (.inr .n5) (.inr .n1) (.inr .u) 1)
  (.seq (skipUnary (.inl 1) (.inr .pk) (.inr .tmp) (.inr .n1) (.inr .u) 1)
    (drain (.inr .pk) (.inl 1))))))

theorem closed_hdrUnary : hdrUnary.Closed :=
  WP.W9comp.closed_seq (closed_skipUnary _ _ _ _ _ _) (WP.W9comp.closed_seq
    (closed_skipUnary _ _ _ _ _ _) (WP.W9comp.closed_seq (closed_skipUnary _ _ _ _ _ _)
    (WP.W9comp.closed_seq (closed_skipUnary _ _ _ _ _ _) (WP.W9comp.closed_seq
    (closed_skipUnary _ _ _ _ _ _) (closed_drain _ _)))))

/-- The cost of `hdrUnary`. -/
def hdrUnaryCost (P d r w K m j₀ D nS ρ : ℕ) : ℕ :=
  6 * (sliceHdr P d r w K m j₀ D nS ρ).length + 20 * (K + j₀ + D + nS + ρ) + 40

theorem length_hdrSyms_nil : (hdrSyms []).length = 0 := by simp [hdrSyms]

theorem runs_hdrUnary (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym) (S : SK → List Sym)
    (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hpk : S (.inr .pk) = []) (hn1 : S (.inr .n1) = []) (hu : S (.inr .u) = [])
    (hn2 : S (.inr .n2) = []) (hn3 : S (.inr .n3) = []) (hn4 : S (.inr .n4) = [])
    (hn5 : S (.inr .n5) = []) (htmp : S (.inr .tmp) = []) :
    Runs hdrUnary S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (.inr .n2) (List.replicate K uSym)) (.inr .n3) (List.replicate j₀ uSym))
        (.inr .n4) (List.replicate D uSym)) (.inr .n5) (List.replicate nS uSym))
        (.inr .tmp) (List.replicate ρ uSym))
      (fun _ => True) (hdrUnaryCost P d r w K m j₀ D nS ρ) := by
  have hH' : S (.inl 1) = hdrSyms [P, d, r, w] ++ (natSyms K ++ Sym.mark :: (natSyms m ++
      Sym.mark :: (natSyms j₀ ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms nS ++
      Sym.mark :: (natSyms ρ ++ Sym.mark :: hrest)))))) := by
    rw [hH]
    simp [sliceHdr, hdrSyms]
  have R := runs_seq (runs_skipUnary (src := (.inl 1 : SK)) (pk := .inr .pk) (dst := .inr .n2)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [P, d, r, w] K
      (natSyms m ++ Sym.mark :: (natSyms j₀ ++ Sym.mark :: (natSyms D ++ Sym.mark ::
        (natSyms nS ++ Sym.mark :: (natSyms ρ ++ Sym.mark :: hrest))))) S hH' hn1 hn2 hu)
    (runs_seq (runs_skipUnary (src := (.inl 1 : SK)) (pk := .inr .pk) (dst := .inr .n3)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [K, m] j₀
      (natSyms D ++ Sym.mark :: (natSyms nS ++ Sym.mark :: (natSyms ρ ++ Sym.mark :: hrest)))
      _ (by simp [hdrSyms]) (by simp [hn1]) (by simp [hn3]) (by simp [hu]))
    (runs_seq (runs_skipUnary (src := (.inl 1 : SK)) (pk := .inr .pk) (dst := .inr .n4)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [j₀] D
      (natSyms nS ++ Sym.mark :: (natSyms ρ ++ Sym.mark :: hrest))
      _ (by simp [hdrSyms]) (by simp [hn1]) (by simp [hn4]) (by simp [hu]))
    (runs_seq (runs_skipUnary (src := (.inl 1 : SK)) (pk := .inr .pk) (dst := .inr .n5)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [D] nS
      (natSyms ρ ++ Sym.mark :: hrest)
      _ (by simp [hdrSyms]) (by simp [hn1]) (by simp [hn5]) (by simp [hu]))
    (runs_seq (runs_skipUnary (src := (.inl 1 : SK)) (pk := .inr .pk) (dst := .inr .tmp)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [nS] ρ hrest
      _ (by simp [hdrSyms]) (by simp [hn1]) (by simp [htmp]) (by simp [hu]))
      (runs_drain (src := (.inr .pk : SK)) (dst := .inl 1) (by decide)
        ((hdrSyms [nS]).reverse ++ ((hdrSyms [D]).reverse ++ ((hdrSyms [j₀]).reverse ++
          ((hdrSyms [K, m]).reverse ++ (hdrSyms [P, d, r, w]).reverse)))) _
        (by simp [hpk]))))))
  refine runs_mono (runs_congr R ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i
      · simp
      · simp [hH, sliceHdr, hdrSyms]
      · simp
    · cases e <;> simp [hpk, hn1, hu]
  · have hL := length_sliceHdr P d r w K m j₀ D nS ρ
    simp only [hdrUnaryCost, List.length_reverse, List.length_append,
      WalshCnot1.length_hdrSyms_cons, length_hdrSyms_nil] at hL ⊢
    omega

/-! ## `K - 1 - ρ` and the slice mask -/

theorem RunsR.congr_left {K : Type} [DecidableEq K] {P : EProg K} {S1 S2 S' : K → List Sym} {A B : ER → Prop}
    {T : ℕ} (h : RunsR P S1 S' A B T) (e : S1 = S2) : RunsR P S2 S' A B T := e ▸ h

/-- `n2 := uSym^{K - 1 - ρ}` from `n2 = uSym^K`, `tmp = uSym^ρ` (restored). -/
def subRho : EProg SK :=
  .seq (popWalk (.inr .tmp) (.inr .u) (.inr .n2))
  (.seq ((drain (.inr .u) (.inr .tmp)).liftRegs lT) (popS (.inr .n2)))

theorem runsR_subRho (K ρ : ℕ) (hρ : ρ < K) (S : SK → List Sym)
    (hn2 : S (.inr .n2) = List.replicate K uSym) (htmp : S (.inr .tmp) = List.replicate ρ uSym)
    (hu : S (.inr .u) = []) :
    RunsR subRho S (Function.update S (.inr .n2) (List.replicate (K - 1 - ρ) uSym))
      (fun _ => True) (fun _ => True) (7 * ρ + 5) := by
  have hk : K - ρ - 1 = K - 1 - ρ := by omega
  have R := RunsR.seq (runsR_popWalkT (tk := (.inr .tmp : SK)) (u := .inr .u) (v := .inr .n2)
      (by decide) (by decide) (by decide) ρ (List.replicate K uSym) S (by simp; omega) htmp hn2)
    (RunsR.seq (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .tmp) (by decide)
      (List.replicate ρ uSym) _ (by simp [hu]) (fun _ => True) (fun _ _ => trivial))
      (runsR_popST (.inr .n2 : SK) (List.replicate (K - ρ) uSym) _
        (by simp [List.drop_replicate])))
  refine RunsR.mono (RunsR.congr R ?_) (fun _ h => h) (fun _ h => h)
    (by simp only [List.length_replicate]; omega)
  funext j
  rcases j with i | e
  · simp
  · cases e <;> simp [htmp, hu, List.tail_replicate, hk]

/-- One chunk (push order: `ρ` zeros, a one, `K-1-ρ` zeros); `tmp`, `n2` restored; one unit of
`n4` consumed. -/
def chunkStep : EProg SK :=
  .seq (zWalk (.inr .tmp) (.inr .u) (.inr .x2))
  (.seq ((drain (.inr .u) (.inr .tmp)).liftRegs lT)
  (.seq (pushK (.inr .x2) (.bit true))
  (.seq (zWalk (.inr .n2) (.inr .u) (.inr .x2))
  (.seq ((drain (.inr .u) (.inr .n2)).liftRegs lT)
    (popT (.inr .n4))))))

/-- The chunk-loop state: `pre` chunks pushed, `l` chunks to go. -/
def chunkSt (K ρ : ℕ) (B : SK → List Sym) (pre l : List Unit) : SK → List Sym :=
  Function.update (Function.update B (.inr .n4) (List.replicate l.length uSym).tail) (.inr .x2)
    (((List.replicate pre.length (chunkBits K ρ)).flatten).map Sym.bit ++ B (.inr .x2))

theorem runsR_chunkStep (K ρ : ℕ) (B : SK → List Sym)
    (htmp : B (.inr .tmp) = List.replicate ρ uSym)
    (hn2 : B (.inr .n2) = List.replicate (K - 1 - ρ) uSym) (hu : B (.inr .u) = [])
    (pre : List Unit) (a : Unit) (l : List Unit) :
    RunsR chunkStep (chunkSt K ρ B pre (a :: l)) (chunkSt K ρ B (pre ++ [a]) l)
      (fun _ => True) (fun r => r.t = (List.replicate l.length uSym).head?)
      (7 * ρ + 7 * (K - 1 - ρ) + 10) := by
  have R := RunsR.seq (runsR_zWalkT (tk := (.inr .tmp : SK)) (u := .inr .u) (o := .inr .x2)
      (by decide) (by decide) (by decide) ρ (chunkSt K ρ B pre (a :: l))
      (by simp [chunkSt, htmp]))
    (RunsR.seq (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .tmp) (by decide)
      (List.replicate ρ uSym) _ (by simp [chunkSt, hu]) (fun _ => True) (fun _ _ => trivial))
    (RunsR.seq (runsR_pushK (.inr .x2 : SK) (.bit true) _ (fun _ => True))
    (RunsR.seq (runsR_zWalkT (tk := (.inr .n2 : SK)) (u := .inr .u) (o := .inr .x2)
      (by decide) (by decide) (by decide) (K - 1 - ρ) _ (by simp [chunkSt, hn2]))
    (RunsR.seq (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .n2) (by decide)
      (List.replicate (K - 1 - ρ) uSym) _ (by simp [chunkSt, hu]) (fun _ => True)
      (fun _ _ => trivial))
      (runsR_popTT (.inr .n4 : SK) (List.replicate l.length uSym) _
        (by simp [chunkSt, List.replicate_succ]))))))
  refine RunsR.mono (RunsR.congr R ?_) (fun _ h => h) (fun _ h => h)
    (by simp only [List.length_replicate]; omega)
  funext j
  rcases j with i | e
  · simp [chunkSt]
  · cases e <;> simp [chunkSt, htmp, hn2, hu, List.replicate_succ, chunkBits]

/-- The slice mask on `x2` (position `0` on top) from the unary counters. -/
def maskBuild : EProg SK :=
  .seq (zWalk (.inr .n5) (.inr .u) (.inr .x2))
  (.seq ((clear (.inr .u)).liftRegs lT)
  (.seq (popT (.inr .n4))
  (.seq (.loop tSome chunkStep)
  (.seq (zWalk (.inr .n3) (.inr .u) (.inr .x2))
  (.seq ((clear (.inr .u)).liftRegs lT)
  (.seq ((clear (.inr .tmp)).liftRegs lT)
    ((clear (.inr .n2)).liftRegs lT)))))))

/-- The cost bound of `maskBuild`. -/
def maskCost (K j₀ D ρ nS : ℕ) : ℕ :=
  6 * nS + D * (7 * ρ + 7 * (K - 1 - ρ) + 10 + 1) + 6 * j₀ + 2 * ρ + 2 * (K - 1 - ρ) + 16

theorem runsR_maskBuild (K j₀ D ρ nS : ℕ) (S : SK → List Sym)
    (hn5 : S (.inr .n5) = List.replicate nS uSym) (hn4 : S (.inr .n4) = List.replicate D uSym)
    (hn3 : S (.inr .n3) = List.replicate j₀ uSym) (htmp : S (.inr .tmp) = List.replicate ρ uSym)
    (hn2 : S (.inr .n2) = List.replicate (K - 1 - ρ) uSym) (hu : S (.inr .u) = [])
    (hx2 : S (.inr .x2) = []) :
    RunsR maskBuild S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S (.inr .n5) []) (.inr .n4) []) (.inr .n3) []) (.inr .tmp) [])
        (.inr .n2) []) (.inr .x2) ((selMask K j₀ D ρ nS).map Sym.bit))
      (fun _ => True) (fun _ => True) (maskCost K j₀ D ρ nS) := by
  set B := Function.update (Function.update (Function.update (Function.update S (.inr .n5) [])
    (.inr .u) []) (.inr .x2) (List.replicate nS (Sym.bit false))) (.inr .n4)
    (List.replicate D uSym).tail with hB
  have hB0 : chunkSt K ρ B [] (List.replicate D ()) = B := by
    funext j
    rcases j with i | e
    · simp [chunkSt]
    · cases e <;> simp [chunkSt, hB]
  have hloop := runsR_loopList (chunkSt K ρ B) (fun _ => 7 * ρ + 7 * (K - 1 - ρ) + 10)
    (runsR_chunkStep K ρ B (by simp [hB, htmp]) (by simp [hB, hn2]) (by simp [hB]))
    (List.replicate D ()) []
  rw [hB0] at hloop
  have R := RunsR.seq (runsR_zWalkT (tk := (.inr .n5 : SK)) (u := .inr .u) (o := .inr .x2)
      (by decide) (by decide) (by decide) nS S hn5)
    (RunsR.seq (runsR_clearE (.inr .u : SK) (List.replicate nS uSym) _ (by simp [hu])
      (fun _ => True) (fun _ _ => trivial))
    (RunsR.seq (RunsR.congr (runsR_popTT (.inr .n4 : SK) (List.replicate D uSym) _
      (by simp [hn4])) (by funext j; rcases j with i | e
                           · simp [hB]
                           · cases e <;> simp [hB, hx2]))
    (RunsR.seq (RunsR.mono hloop (fun r h => by simpa using h) (fun _ h => h) le_rfl)
    (RunsR.seq (runsR_zWalkT (tk := (.inr .n3 : SK)) (u := .inr .u) (o := .inr .x2)
      (by decide) (by decide) (by decide) j₀ _ (by simp [chunkSt, hB, hn3]))
    (RunsR.seq (runsR_clearE (.inr .u : SK) (List.replicate j₀ uSym) _
      (by simp [chunkSt, hB]) (fun _ => True) (fun _ _ => trivial))
    (RunsR.seq (runsR_clearE (.inr .tmp : SK) (List.replicate ρ uSym) _
      (by simp [chunkSt, hB, htmp]) (fun _ => True) (fun _ _ => trivial))
      (runsR_clearE (.inr .n2 : SK) (List.replicate (K - 1 - ρ) uSym) _
        (by simp [chunkSt, hB, hn2]) (fun _ => True) (fun _ _ => trivial))))))))
  refine RunsR.mono (RunsR.congr R ?_) (fun _ h => h) (fun _ h => h) ?_
  · funext j
    rcases j with i | e
    · simp [chunkSt, hB]
    · cases e <;> simp [chunkSt, hB, selMask, hu]
  · rw [List.map_replicate, List.sum_replicate, smul_eq_mul]
    simp only [maskCost, List.length_replicate]
    omega

/-! ## Clearing the targets -/

/-- The pair fields as numbers. -/
def flatPairs {m : ℕ} (ps : List (Fin m × Fin m)) : List ℕ :=
  ps.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]

theorem flatPairs_cons {m : ℕ} (a : Fin m × Fin m) (l : List (Fin m × Fin m)) :
    flatPairs (a :: l) = (a.1 : ℕ) :: (a.2 : ℕ) :: flatPairs l := by
  simp [flatPairs]

theorem flatPairs_append {m : ℕ} (l1 l2 : List (Fin m × Fin m)) :
    flatPairs (l1 ++ l2) = flatPairs l1 ++ flatPairs l2 := by
  simp [flatPairs]

theorem flatPairs_nil {m : ℕ} : flatPairs ([] : List (Fin m × Fin m)) = [] := rfl

theorem hdrSyms_nil' : hdrSyms [] = [] := by simp [hdrSyms]

theorem hdrSyms_cons' (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append' (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

theorem length_clearTargets {m : ℕ} (pre : List (Fin m × Fin m)) (L : List Bool) :
    (clearTargets pre L).length = L.length := by
  induction pre generalizing L with
  | nil => rfl
  | cons a l ih =>
    show (clearTargets l (L.set a.2 false)).length = L.length
    rw [ih, List.length_set]

theorem clearTargets_append_single {m : ℕ} (pre : List (Fin m × Fin m)) (a : Fin m × Fin m)
    (L : List Bool) : clearTargets (pre ++ [a]) L = (clearTargets pre L).set a.2 false := by
  simp [clearTargets, List.foldl_append]

theorem set_false_map : ∀ (L : List Bool) (t : ℕ), t < L.length →
    (L.set t false).map Sym.bit =
      (L.take t).map Sym.bit ++ Sym.bit false :: ((L.drop t).map Sym.bit).tail
  | [], t, h => by simp at h
  | b :: L, 0, _ => by simp
  | b :: L, t + 1, h => by
    have ih := set_false_map L t (by simpa using h)
    simp [ih]

/-- One pair `(c, t)`: skip `c`, read `t` in unary, clear mask position `t` (position `0` on top
of `x2`), consume a unit of `n3`. -/
def tgtStep : EProg SK :=
  .seq ((WalshCnot1.skipFields (.inl 2) (.inr .pk) 1).liftRegs lT)
  (.seq ((unaryOfTop (.inl 2) (.inr .n4) (.inr .n1) (.inr .u)).liftRegs lT)
  (.seq ((WalshCnot1.skipFields (.inl 2) (.inr .pk) 1).liftRegs lT)
  (.seq (readWalk (.inr .n4) (.inr .u) (.inr .x2) (.inr .tmp))
  (.seq (popS (.inr .x2))
  (.seq (pushK (.inr .x2) (.bit false))
  (.seq (readWalk (.inr .u) (.inr .n4) (.inr .tmp) (.inr .x2))
  (.seq ((clear (.inr .n4)).liftRegs lT)
    (popT (.inr .n3)))))))))

/-- The target-loop state: pairs `pre` done, `l` to do. -/
def tgtSt {m : ℕ} (B : SK → List Sym) (L0 : List Bool) (prest : List Sym)
    (pre l : List (Fin m × Fin m)) : SK → List Sym :=
  Function.update (Function.update (Function.update (Function.update B
    (.inr .n3) (List.replicate l.length uSym).tail) (.inl 2) (hdrSyms (flatPairs l) ++ prest))
    (.inr .pk) ((hdrSyms (flatPairs pre)).reverse ++ B (.inr .pk)))
    (.inr .x2) ((clearTargets pre L0).map Sym.bit)

/-- The cost of one pair. -/
def tgtCost {m : ℕ} (a : Fin m × Fin m) : ℕ :=
  32 * (a.2 : ℕ) + 3 * (hdrSyms [(a.1 : ℕ), (a.2 : ℕ)]).length + 16

theorem runsR_tgtStep {m : ℕ} (B : SK → List Sym) (L0 : List Bool) (hL0 : L0.length = m)
    (prest : List Sym) (hn4 : B (.inr .n4) = []) (hu : B (.inr .u) = [])
    (hn1 : B (.inr .n1) = []) (htmp : B (.inr .tmp) = [])
    (pre : List (Fin m × Fin m)) (a : Fin m × Fin m) (l : List (Fin m × Fin m)) :
    RunsR tgtStep (tgtSt B L0 prest pre (a :: l)) (tgtSt B L0 prest (pre ++ [a]) l)
      (fun _ => True) (fun r => r.t = (List.replicate l.length uSym).head?) (tgtCost a) := by
  have hLm : (clearTargets pre L0).length = m := by rw [length_clearTargets, hL0]
  have ht : (a.2 : ℕ) < (clearTargets pre L0).length := by rw [hLm]; exact a.2.isLt
  have htk : ((clearTargets pre L0).take a.2).length = a.2 := by
    rw [List.length_take]; omega
  have R := RunsR.seq (runsR_of_runs (runs_skipFields (src := (.inl 2 : SK)) (pk := .inr .pk)
      (by decide) (hdrSyms ((a.2 : ℕ) :: flatPairs l) ++ prest) [(a.1 : ℕ)]
      (tgtSt B L0 prest pre (a :: l))
      (by simp [tgtSt, flatPairs_cons, hdrSyms_cons', hdrSyms_nil'])) (fun _ => True)
      (fun _ _ _ => trivial))
    (RunsR.seq (runsR_of_runs (runs_unaryOfTop (src := (.inl 2 : SK)) (dst := .inr .n4)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) a.2 (hdrSyms (flatPairs l) ++ prest) _
      (by simp [hdrSyms_cons']) (by simp [tgtSt, hn1]) (by simp [tgtSt, hn4])
      (by simp [tgtSt, hu])) (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_of_runs (runs_skipFields (src := (.inl 2 : SK)) (pk := .inr .pk)
      (by decide) (hdrSyms (flatPairs l) ++ prest) [(a.2 : ℕ)] _
      (by simp [hdrSyms_cons', hdrSyms_nil'])) (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_readWalkT (tk := (.inr .n4 : SK)) (u := .inr .u) (src := .inr .x2)
      (dst := .inr .tmp) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (((clearTargets pre L0).drop a.2).map Sym.bit)
      ((clearTargets pre L0).take a.2) _ (by rw [htk]; simp [tgtSt])
      (by rw [← List.map_append, List.take_append_drop]; simp [tgtSt]))
    (RunsR.seq (runsR_popST (.inr .x2 : SK) (((clearTargets pre L0).drop a.2).map Sym.bit) _
      (by simp))
    (RunsR.seq (runsR_pushK (.inr .x2 : SK) (Sym.bit false) _ (fun _ => True))
    (RunsR.seq (runsR_readWalkT (tk := (.inr .u : SK)) (u := .inr .n4) (src := .inr .tmp)
      (dst := .inr .x2) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) [] ((clearTargets pre L0).take a.2).reverse _ (by simp [tgtSt, hu])
      (by simp [tgtSt, htmp]))
    (RunsR.seq (runsR_clearE (.inr .n4 : SK)
      (List.replicate ((clearTargets pre L0).take a.2).reverse.length uSym) _
      (by simp [tgtSt]) (fun _ => True) (fun _ _ => trivial))
      (runsR_popTT (.inr .n3 : SK) (List.replicate l.length uSym) _
        (by simp [tgtSt, List.replicate_succ])))))))))
  refine RunsR.mono (RunsR.congr R ?_) (fun _ h => h) (fun _ h => h) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp [tgtSt]
    · cases e <;> simp [tgtSt, hn4, hu, htmp, hn1, clearTargets_append_single,
        set_false_map _ _ ht, flatPairs_append, flatPairs_cons, flatPairs_nil, hdrSyms_append',
        hdrSyms_cons', hdrSyms_nil']
  · simp only [tgtCost, List.length_reverse, List.length_replicate, htk,
      WalshCnot1.length_hdrSyms_cons, length_hdrSyms_nil]
    omega

/-- Clear every target position of the mask on `x2` (pair list restored). -/
def tgtClear : EProg SK :=
  .seq ((unaryOfTop (.inl 2) (.inr .n3) (.inr .n1) (.inr .u)).liftRegs lT)
  (.seq ((WalshCnot1.skipFields (.inl 2) (.inr .pk) 1).liftRegs lT)
  (.seq (popT (.inr .n3))
  (.seq (.loop tSome tgtStep)
    ((drain (.inr .pk) (.inl 2)).liftRegs lT))))

/-- The cost bound of `tgtClear`. -/
def tgtClearCost {m : ℕ} (pairs : List (Fin m × Fin m)) : ℕ :=
  20 * pairs.length + 6 * (pairsSyms pairs).length + (pairs.map fun a => tgtCost a + 1).sum + 12

theorem length_pairsSyms_split {m : ℕ} (pairs : List (Fin m × Fin m)) :
    (pairsSyms pairs).length =
      (hdrSyms [pairs.length]).length + (hdrSyms (flatPairs pairs)).length := by
  simp only [pairsSyms, flatPairs, WalshCnot1.length_hdrSyms_cons, length_hdrSyms_nil]

theorem runsR_tgtClear {m : ℕ} (pairs : List (Fin m × Fin m)) (prest : List Sym)
    (L0 : List Bool) (hL0 : L0.length = m) (S : SK → List Sym)
    (hQ : S (.inl 2) = pairsSyms pairs ++ prest) (hx2 : S (.inr .x2) = L0.map Sym.bit)
    (hn3 : S (.inr .n3) = []) (hn4 : S (.inr .n4) = []) (hu : S (.inr .u) = [])
    (hn1 : S (.inr .n1) = []) (htmp : S (.inr .tmp) = []) (hpk : S (.inr .pk) = []) :
    RunsR tgtClear S (Function.update S (.inr .x2) ((clearTargets pairs L0).map Sym.bit))
      (fun _ => True) (fun _ => True) (tgtClearCost pairs) := by
  have hQ' : S (.inl 2) = natSyms pairs.length ++ Sym.mark ::
      (hdrSyms (flatPairs pairs) ++ prest) := by
    rw [hQ]
    simp [pairsSyms, flatPairs, hdrSyms_cons']
  set B := Function.update (Function.update (Function.update S (.inr .n3)
    (List.replicate pairs.length uSym).tail) (.inl 2) (hdrSyms (flatPairs pairs) ++ prest))
    (.inr .pk) (hdrSyms [pairs.length]).reverse with hB
  have hB0 : tgtSt B L0 prest [] pairs = B := by
    funext j
    rcases j with i | e
    · fin_cases i <;> simp [tgtSt, hB]
    · cases e <;> simp [tgtSt, hB, hx2, clearTargets, flatPairs_nil, hdrSyms_nil']
  have hloop := runsR_loopList (tgtSt B L0 prest) tgtCost
    (runsR_tgtStep B L0 hL0 prest (by simp [hB, hn4]) (by simp [hB, hu]) (by simp [hB, hn1])
      (by simp [hB, htmp])) pairs []
  rw [hB0] at hloop
  have R := RunsR.seq (runsR_of_runs (runs_unaryOfTop (src := (.inl 2 : SK)) (dst := .inr .n3)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) pairs.length (hdrSyms (flatPairs pairs) ++ prest) S hQ' hn1 hn3 hu)
      (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_of_runs (runs_skipFields (src := (.inl 2 : SK)) (pk := .inr .pk)
      (by decide) (hdrSyms (flatPairs pairs) ++ prest) [pairs.length] _
      (by simp [hQ', hdrSyms_cons', hdrSyms_nil'])) (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (RunsR.congr (runsR_popTT (.inr .n3 : SK) (List.replicate pairs.length uSym) _
      (by simp)) (by
        funext j
        rcases j with i | e
        · fin_cases i <;> simp [hB]
        · cases e <;> simp [hB, hpk]))
    (RunsR.seq hloop
      (runsR_drainE (src := (.inr .pk : SK)) (dst := .inl 2) (by decide)
        ((hdrSyms (flatPairs pairs)).reverse ++ (hdrSyms [pairs.length]).reverse) _
        (by simp [tgtSt, hB]) (fun _ => True) (fun _ _ => trivial)))))
  refine RunsR.mono (RunsR.congr R ?_) (fun _ h => h) (fun _ h => h) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp [tgtSt, hB, hQ, pairsSyms, flatPairs, hdrSyms_cons', hdrSyms_nil']
    · cases e <;> simp [tgtSt, hB, hn3, hpk]
  · have h2 := length_pairsSyms_split pairs
    simp only [tgtClearCost, List.length_append, List.length_reverse] at h2 ⊢
    omega

/-! ## The `U`-vector builder -/

theorem uv_value {m K j₀ D ρ nS : ℕ} (pairs : List (Fin m × Fin m)) (hm : j₀ + D * K + nS = m)
    (hρ : ρ < K) :
    ((clearTargets pairs (selMask K j₀ D ρ nS)).map Sym.bit).reverse =
      uvSyms m (slicePos m K j₀ D ρ \ targets pairs) := by
  rw [selMask_eq hm hρ, clearTargets_map]
  simp [uvSyms, List.map_reverse, Finset.mem_sdiff]

/-- **The `U`-vector builder**: `uv := uvSyms m (slicePos m K j₀ D ρ ∖ targets pairs)`. -/
def uvBuild : EProg SK :=
  .seq (hdrUnary.liftRegs lT)
  (.seq subRho
  (.seq maskBuild
  (.seq tgtClear
    ((drain (.inr .x2) (.inr .uv)).liftRegs lT))))

theorem closed_tgtStep : tgtStep.Closed := by
  have h1 := WP.W9comp.closed_liftRegs lT (WalshCnot1.closed_skipFields (.inl 2 : SK) (.inr .pk) 1)
  have h2 := WP.W9comp.closed_liftRegs lT
    (closed_unaryOfTop (.inl 2 : SK) (.inr .n4) (.inr .n1) (.inr .u))
  have h3 := WP.W9comp.closed_liftRegs lT (closed_clear (.inr .n4 : SK))
  simp only [Prog.Closed] at h1 h2 h3 ⊢
  simp [Prog.FreeBelow, tgtStep, readWalk, readStep, popT, popS, pushS, pushK, h1, h2, h3]

theorem closed_uvBuild : uvBuild.Closed := by
  have hc : chunkStep.Closed := by
    have h1 := WP.W9comp.closed_liftRegs lT (closed_drain (.inr .u : SK) (.inr .tmp))
    have h2 := WP.W9comp.closed_liftRegs lT (closed_drain (.inr .u : SK) (.inr .n2))
    simp only [Prog.Closed] at h1 h2 ⊢
    simp [Prog.FreeBelow, chunkStep, zWalk, zStep, popT, pushK, h1, h2]
  have hm : maskBuild.Closed := by
    have h1 := WP.W9comp.closed_liftRegs lT (closed_clear (.inr .u : SK))
    have h2 := WP.W9comp.closed_liftRegs lT (closed_clear (.inr .tmp : SK))
    have h3 := WP.W9comp.closed_liftRegs lT (closed_clear (.inr .n2 : SK))
    simp only [Prog.Closed] at h1 h2 h3 hc ⊢
    simp [Prog.FreeBelow, maskBuild, zWalk, zStep, popT, pushK, h1, h2, h3, hc]
  have hs : subRho.Closed := by
    have h1 := WP.W9comp.closed_liftRegs lT (closed_drain (.inr .u : SK) (.inr .tmp))
    simp only [Prog.Closed] at h1 ⊢
    simp [Prog.FreeBelow, subRho, popWalk, popStep, popT, popS, pushK, h1]
  have ht : tgtClear.Closed := by
    have h1 := WP.W9comp.closed_liftRegs lT
      (closed_unaryOfTop (.inl 2 : SK) (.inr .n3) (.inr .n1) (.inr .u))
    have h2 := WP.W9comp.closed_liftRegs lT (WalshCnot1.closed_skipFields (.inl 2 : SK) (.inr .pk) 1)
    have h3 := WP.W9comp.closed_liftRegs lT (closed_drain (.inr .pk : SK) (.inl 2))
    have h4 := closed_tgtStep
    simp only [Prog.Closed] at h1 h2 h3 h4 ⊢
    simp [Prog.FreeBelow, tgtClear, popT, h1, h2, h3, h4]
  exact WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT closed_hdrUnary)
    (WP.W9comp.closed_seq hs (WP.W9comp.closed_seq hm (WP.W9comp.closed_seq ht
      (WP.W9comp.closed_liftRegs lT (closed_drain _ _)))))

/-- The cost of `uvBuild`. -/
def uvCost (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m)) : ℕ :=
  hdrUnaryCost P d r w K m j₀ D nS ρ + (7 * ρ + 5) + maskCost K j₀ D ρ nS + tgtClearCost pairs +
    (3 * m + 2)

/-- **`U`-vector builder, exact.** From a slice header (`.inl 1`) and a pair list (`.inl 2`), both
restored, and the scratch stacks `pk n1 u n2 n3 n4 n5 tmp x2 uv` empty, `uvBuild` puts
`uvSyms m (slicePos m K j₀ D ρ ∖ targets pairs)` on `uv`; every other stack is untouched. -/
theorem runs_uvBuild (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (hrest prest : List Sym) (S : SK → List Sym) (hm : j₀ + D * K + nS = m) (hρ : ρ < K)
    (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hQ : S (.inl 2) = pairsSyms pairs ++ prest)
    (hpk : S (.inr .pk) = []) (hn1 : S (.inr .n1) = []) (hu : S (.inr .u) = [])
    (hn2 : S (.inr .n2) = []) (hn3 : S (.inr .n3) = []) (hn4 : S (.inr .n4) = [])
    (hn5 : S (.inr .n5) = []) (htmp : S (.inr .tmp) = []) (hx2 : S (.inr .x2) = [])
    (huv : S (.inr .uv) = []) :
    Runs uvBuild S (Function.update S (.inr .uv) (uvSyms m (slicePos m K j₀ D ρ \ targets pairs)))
      (fun _ => True) (uvCost P d r w K m j₀ D nS ρ pairs) := by
  have hlen : (selMask K j₀ D ρ nS).length = m := by rw [selMask_eq hm hρ]; simp
  have R := RunsR.seq (runsR_of_runs (runs_hdrUnary P d r w K m j₀ D nS ρ hrest S hH hpk hn1 hu
      hn2 hn3 hn4 hn5 htmp) (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_subRho K ρ hρ _ (by simp) (by simp) (by simp [hu]))
    (RunsR.seq (runsR_maskBuild K j₀ D ρ nS _ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [hu]) (by simp [hx2]))
    (RunsR.seq (runsR_tgtClear pairs prest (selMask K j₀ D ρ nS) hlen _ (by simp [hQ]) (by simp)
      (by simp) (by simp) (by simp [hu]) (by simp [hn1]) (by simp) (by simp [hpk]))
      (runsR_drainE (src := (.inr .x2 : SK)) (dst := .inr .uv) (by decide)
        ((clearTargets pairs (selMask K j₀ D ρ nS)).map Sym.bit) _ (by simp) (fun _ => True)
        (fun _ _ => trivial)))))
  rw [← uv_value pairs hm hρ]
  refine runs_mono (runs_congr (runs_of_runsR R) ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp
    · cases e <;> simp [hpk, hn1, hu, hn2, hn3, hn4, hn5, htmp, hx2, huv]
  · simp only [uvCost, List.length_map, length_clearTargets, hlen]
    omega

/-! ## Cost bound -/

theorem sum_tgtCost_le {m : ℕ} : ∀ pairs : List (Fin m × Fin m),
    (pairs.map fun a => tgtCost a + 1).sum ≤
      32 * (m * pairs.length) + 3 * (hdrSyms (flatPairs pairs)).length + 17 * pairs.length
  | [] => by simp
  | a :: l => by
    have ih := sum_tgtCost_le l
    have ha := a.2.isLt
    simp only [List.map_cons, List.sum_cons, tgtCost, flatPairs_cons,
      WalshCnot1.length_hdrSyms_cons, length_hdrSyms_nil, List.length_cons, Nat.mul_add,
      Nat.mul_one] at ih ⊢
    omega

theorem two_mul_le_hdrSyms_flat {m : ℕ} : ∀ pairs : List (Fin m × Fin m),
    2 * pairs.length ≤ (hdrSyms (flatPairs pairs)).length
  | [] => by simp
  | a :: l => by
    have ih := two_mul_le_hdrSyms_flat l
    simp only [flatPairs_cons, WalshCnot1.length_hdrSyms_cons, List.length_cons]
    omega

/-- **Cost of the `U`-vector builder**: `O(|sliceHdr| + |pairsSyms| + K + m + m·|pairs|)`. -/
theorem uvCost_le (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (hm : j₀ + D * K + nS = m) (hρ : ρ < K) :
    uvCost P d r w K m j₀ D nS ρ pairs ≤
      100 * ((sliceHdr P d r w K m j₀ D nS ρ).length + (pairsSyms pairs).length + K + m + 1) +
        32 * (m * pairs.length) := by
  have h1 := sum_tgtCost_le pairs
  have h2 := length_pairsSyms_split pairs
  have h3 := two_mul_le_hdrSyms_flat pairs
  have hD : D ≤ D * K := Nat.le_mul_of_pos_right D (by omega)
  have h4 : D * (7 * ρ + 7 * (K - 1 - ρ) + 10 + 1) = 7 * (D * K) + 4 * D := by
    rw [show 7 * ρ + 7 * (K - 1 - ρ) + 10 + 1 = 7 * K + 4 by omega]
    ring
  simp only [uvCost, hdrUnaryCost, maskCost, tgtClearCost, h4]
  omega

end SubNLogN.Machine.WalshScanAux
