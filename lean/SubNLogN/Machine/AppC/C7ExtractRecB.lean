/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractRecA

/-!
# Lemma A.9 extraction, part 5: decoding, re-encoding and record moves (`Machine/AppC/C7ExtractRecB.lean`)

Routines of one record of the extraction kernel, generic in an arithmetic kit
`xk : XKit (XK E')`:

* `decode`: the mixed-radix coordinates of the record index on `tP` (`runs_decode`);
* `names σ`: the named chunks `x, y, z` copied from their slots (`runs_names`);
* `horner σ`: the destination rank plus `2^A`, by Horner's rule from the decoded coordinates and
  the new chunk values (`runs_horner`);
* `keyEmit`: the keyed record of an exceptional record pushed on the bank (`runs_keyEmit`);
* `goodMove`: a kept record moved to the skeleton stream (`runs_goodMove`).

Everything here is proved (no `sorry`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus
  SubNLogN.Machine.AppC.Corr SubNLogN.Machine.AppC.C7RadixAux

section Names

variable {E' : Type}

/-- The array stack. -/
abbrev sArr : XK E' := .inl (.inl 0)
/-- The parameter stacks `K, ρ, f, N1, N2, N3, R`. -/
abbrev sK : XK E' := .inl (.inl 1)
abbrev sRho : XK E' := .inl (.inl 2)
abbrev sF : XK E' := .inl (.inl 3)
abbrev sN1 : XK E' := .inl (.inl 4)
abbrev sN2 : XK E' := .inl (.inl 5)
abbrev sN3 : XK E' := .inl (.inl 6)
abbrev sR : XK E' := .inl (.inl 7)
/-- The skeleton, bank and key-width stacks. -/
abbrev sH : XK E' := .inl (.inr 0)
abbrev sB : XK E' := .inl (.inr 1)
abbrev sAc : XK E' := .inl (.inr 2)

end Names

/-- Slot stacks of the decoded chunks. -/
def slotW : Fin 3 → XW := ![.vC1, .vC2, .vC3]
/-- Name stacks (`0 = x`, `1 = y`, `2 = z`). -/
def nameW : Fin 3 → XW := ![.nX, .nY, .nZ]

theorem slotW_ne : ∀ j, slotW j ≠ .nX ∧ slotW j ≠ .nY ∧ slotW j ≠ .nZ ∧ slotW j ≠ .u1 := by
  decide

theorem nameW_ne : ∀ j, nameW j ≠ .hD ∧ nameW j ≠ .iT ∧ nameW j ≠ .u1 ∧ nameW j ≠ .u2 ∧
    nameW j ≠ .u3 := by
  decide

theorem wk_ne {E' : Type} {a b : XW} (h : a ≠ b) : (wk a : XK E') ≠ wk b := by
  simpa using h

section Rec

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

theorem dm_le (nb a b : ℕ) (ha : a ≤ nb) (hb : b ≤ nb) :
    xk.c * (a * b + a + b + 1) + 2 ≤ opCost xk nb := by
  have := c_dm_le xk nb a b ha hb
  exact le_opCost xk nb _ (by omega)

/-- Fresh floors on `q`, `r`, then `q += a / b`, `r += a % b`. -/
def dmF (x y q r : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk q .mark) (.seq (pushW xk r .mark) (xk.dm x y q r (wk .u1) (wk .u2) (wk .u3)))

theorem runs_dmF {x y q r : XK E'} (h : [x, y, q, r, wk .u1, wk .u2, wk .u3].Nodup)
    (a b nb : ℕ) (rx ry : List Sym) (S : XK E' → List Sym) (hb : 0 < b) (hrx : TermOK rx)
    (hry : TermOK ry) (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry)
    (ha' : bitLen a ≤ nb) (hb' : bitLen b ≤ nb) :
    Runs (dmF xk x y q r) S
      (Function.update (Function.update S q (natSyms (a / b) ++ Sym.mark :: S q)) r
        (natSyms (a % b) ++ Sym.mark :: S r)) (fun _ => True) (opCost xk nb) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hxy, hxq, hxr, -, -, -⟩, ⟨hyq, hyr, -, -, -⟩, ⟨hqr, -, -, -⟩, -, -, -⟩ := h'
  have X := WP.W9comp.runs_seq (runs_pushW xk q .mark S)
    (WP.W9comp.runs_seq (runs_pushW xk r .mark _)
      (xk.dm_spec h a b rx ry _ hb hrx hry (by simp [Function.update_apply, hxq, hxr, hx])
        (by simp [Function.update_apply, hyq, hyr, hy])))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have := dm_le xk nb _ _ ha' hb'
    omega

/-- **Decoding** the record index on `tP` into its mixed-radix coordinates (quotients on `q1, q2`,
coordinates on the `vA*`, `vC*` stacks, each above a fresh floor). -/
def decode : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (dmF xk (wk .tP) sN3 (wk .q1) (wk .vA3)) (.seq (dmF xk (wk .q1) (wk .c2L) (wk .q2) (wk .vC3))
  (.seq (dropFW xk (wk .q1)) (.seq (dmF xk (wk .q2) sN2 (wk .q1) (wk .vA2))
  (.seq (dropFW xk (wk .q2)) (.seq (dmF xk (wk .q1) (wk .c2L) (wk .q2) (wk .vC2))
  (.seq (dropFW xk (wk .q1)) (.seq (dmF xk (wk .q2) sN1 (wk .q1) (wk .vA1))
  (.seq (dropFW xk (wk .q2)) (.seq (dmF xk (wk .q1) (wk .c2L) (wk .vA0) (wk .vC1))
    (dropFW xk (wk .q1)))))))))))

theorem runs_decode (p N1 N2 N3 Q nb : ℕ) (S : XK E' → List Sym) (rP r1 r2 r3 rQ : List Sym)
    (hrP : TermOK rP) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3) (hrQ : TermOK rQ)
    (hP : S (wk .tP) = natSyms p ++ rP) (h1 : S sN1 = natSyms N1 ++ r1)
    (h2 : S sN2 = natSyms N2 ++ r2) (h3 : S sN3 = natSyms N3 ++ r3)
    (hQ : S (wk .c2L) = natSyms Q ++ rQ)
    (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3) (hQ0 : 0 < Q)
    (hpb : bitLen p ≤ nb) (h1b : bitLen N1 ≤ nb) (h2b : bitLen N2 ≤ nb) (h3b : bitLen N3 ≤ nb)
    (hQb : bitLen Q ≤ nb) :
    Runs (decode xk) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S
        (wk .vA3) (natSyms (p % N3) ++ Sym.mark :: S (wk .vA3)))
        (wk .vC3) (natSyms (p / N3 % Q) ++ Sym.mark :: S (wk .vC3)))
        (wk .vA2) (natSyms (p / N3 / Q % N2) ++ Sym.mark :: S (wk .vA2)))
        (wk .vC2) (natSyms (p / N3 / Q / N2 % Q) ++ Sym.mark :: S (wk .vC2)))
        (wk .vA1) (natSyms (p / N3 / Q / N2 / Q % N1) ++ Sym.mark :: S (wk .vA1)))
        (wk .vC1) (natSyms (p / N3 / Q / N2 / Q / N1 % Q) ++ Sym.mark :: S (wk .vC1)))
        (wk .vA0) (natSyms (p / N3 / Q / N2 / Q / N1 / Q) ++ Sym.mark :: S (wk .vA0)))
      (fun _ => True) (11 * opCost xk nb) := by
  have bl : ∀ x, x ≤ p → bitLen x ≤ nb := fun x hx => le_trans (TMFw.W3s.bitLen_mono hx) hpb
  have d1 : p / N3 ≤ p := Nat.div_le_self _ _
  have d2 : p / N3 / Q ≤ p := le_trans (Nat.div_le_self _ _) d1
  have d3 : p / N3 / Q / N2 ≤ p := le_trans (Nat.div_le_self _ _) d2
  have d4 : p / N3 / Q / N2 / Q ≤ p := le_trans (Nat.div_le_self _ _) d3
  have d5 : p / N3 / Q / N2 / Q / N1 ≤ p := le_trans (Nat.div_le_self _ _) d4
  have X := WP.W9comp.runs_seq (runs_dmF xk (x := wk .tP) (y := sN3) (q := wk .q1) (r := wk .vA3) (by simp) p N3 nb rP r3 S hN3 hrP hr3 hP h3 hpb h3b)
    (WP.W9comp.runs_seq (runs_dmF xk (x := wk .q1) (y := wk .c2L) (q := wk .q2) (r := wk .vC3) (by simp) (p / N3) Q nb (Sym.mark :: S (wk .q1)) rQ _ hQ0 (termOK_mark _) hrQ (by simp [Function.update_apply]) (by simp [Function.update_apply, hQ]) (bl _ d1) hQb)
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .q1) (p / N3) .mark (S (wk .q1)) _ rfl (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dmF xk (x := wk .q2) (y := sN2) (q := wk .q1) (r := wk .vA2) (by simp) (p / N3 / Q) N2 nb (Sym.mark :: S (wk .q2)) r2 _ hN2 (termOK_mark _) hr2 (by simp [Function.update_apply]) (by simp [Function.update_apply, h2]) (bl _ d2) h2b)
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .q2) (p / N3 / Q) .mark (S (wk .q2)) _ rfl (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dmF xk (x := wk .q1) (y := wk .c2L) (q := wk .q2) (r := wk .vC2) (by simp) (p / N3 / Q / N2) Q nb (Sym.mark :: S (wk .q1)) rQ _ hQ0 (termOK_mark _) hrQ (by simp [Function.update_apply]) (by simp [Function.update_apply, hQ]) (bl _ d3) hQb)
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .q1) (p / N3 / Q / N2) .mark (S (wk .q1)) _ rfl (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dmF xk (x := wk .q2) (y := sN1) (q := wk .q1) (r := wk .vA1) (by simp) (p / N3 / Q / N2 / Q) N1 nb (Sym.mark :: S (wk .q2)) r1 _ hN1 (termOK_mark _) hr1 (by simp [Function.update_apply]) (by simp [Function.update_apply, h1]) (bl _ d4) h1b)
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .q2) (p / N3 / Q / N2 / Q) .mark (S (wk .q2)) _ rfl (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dmF xk (x := wk .q1) (y := wk .c2L) (q := wk .vA0) (r := wk .vC1) (by simp) (p / N3 / Q / N2 / Q / N1) Q nb (Sym.mark :: S (wk .q1)) rQ _ hQ0 (termOK_mark _) hrQ (by simp [Function.update_apply]) (by simp [Function.update_apply, hQ]) (bl _ d5) hQb)
    (runs_dropFW xk (wk .q1) (p / N3 / Q / N2 / Q / N1) .mark (S (wk .q1)) _ rfl (by simp [Function.update_apply])))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with (k | k) | (x | e)
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · cases x <;> simp [Function.update_apply]
    · simp [Function.update_apply]
  · have c1 := small_le xk nb (bitLen (p / N3)) 0 (bl _ d1) (by omega)
    have c2 := small_le xk nb (bitLen (p / N3 / Q)) 0 (bl _ d2) (by omega)
    have c3 := small_le xk nb (bitLen (p / N3 / Q / N2)) 0 (bl _ d3) (by omega)
    have c4 := small_le xk nb (bitLen (p / N3 / Q / N2 / Q)) 0 (bl _ d4) (by omega)
    have c5 := small_le xk nb (bitLen (p / N3 / Q / N2 / Q / N1)) 0 (bl _ d5) (by omega)
    omega

/-- The named chunks `x, y, z` copied from their slots (`slot σ⁻¹ i` holds name `i`). -/
def names (σ : Equiv.Perm (Fin 3)) : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk (wk .nX) .mark) (.seq (cpT xk (wk (slotW (σ.symm 0))) (wk .nX))
  (.seq (pushW xk (wk .nY) .mark) (.seq (cpT xk (wk (slotW (σ.symm 1))) (wk .nY))
  (.seq (pushW xk (wk .nZ) .mark) (cpT xk (wk (slotW (σ.symm 2))) (wk .nZ))))))

theorem slot_ne (j : Fin 3) : (wk (slotW j) : XK E') ≠ wk .nX ∧ (wk (slotW j) : XK E') ≠ wk .nY ∧
    (wk (slotW j) : XK E') ≠ wk .nZ ∧ (wk (slotW j) : XK E') ≠ wk .u1 := by
  fin_cases j <;> simp [slotW]

theorem runs_names (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → ℕ) (nb : ℕ) (S : XK E' → List Sym)
    (r : Fin 3 → List Sym) (hr : ∀ j, TermOK (r j))
    (hS : ∀ j, S (wk (slotW j)) = natSyms (c j) ++ r j) (hb : ∀ j, bitLen (c j) ≤ nb) :
    Runs (names xk σ) S
      (Function.update (Function.update (Function.update S
        (wk .nX) (natSyms (c (σ.symm 0)) ++ Sym.mark :: S (wk .nX)))
        (wk .nY) (natSyms (c (σ.symm 1)) ++ Sym.mark :: S (wk .nY)))
        (wk .nZ) (natSyms (c (σ.symm 2)) ++ Sym.mark :: S (wk .nZ)))
      (fun _ => True) (6 * opCost xk nb) := by
  have hn := slot_ne (E' := E')
  have X := WP.W9comp.runs_seq (runs_pushW xk (wk .nX) .mark S)
    (WP.W9comp.runs_seq (runs_copyW xk (src := wk (slotW (σ.symm 0))) (dst := wk .nX) (tmp := wk .u1) (hn _).1 (hn _).2.2.2 (by simp) (c (σ.symm 0)) (r (σ.symm 0)) _ (hr _) (by simp [Function.update_apply, (hn (σ.symm 0)).1, hS]))
    (WP.W9comp.runs_seq (runs_pushW xk (wk .nY) .mark _)
    (WP.W9comp.runs_seq (runs_copyW xk (src := wk (slotW (σ.symm 1))) (dst := wk .nY) (tmp := wk .u1) (hn _).2.1 (hn _).2.2.2 (by simp) (c (σ.symm 1)) (r (σ.symm 1)) _ (hr _) (by simp [Function.update_apply, (hn (σ.symm 1)).1, (hn (σ.symm 1)).2.1, hS]))
    (WP.W9comp.runs_seq (runs_pushW xk (wk .nZ) .mark _)
    (runs_copyW xk (src := wk (slotW (σ.symm 2))) (dst := wk .nZ) (tmp := wk .u1) (hn _).2.2.1 (hn _).2.2.2 (by simp) (c (σ.symm 2)) (r (σ.symm 2)) _ (hr _) (by simp [Function.update_apply, (hn (σ.symm 2)).1, (hn (σ.symm 2)).2.1, (hn (σ.symm 2)).2.2.1, hS]))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have c0 := small_le xk nb (bitLen (c (σ.symm 0))) 0 (hb _) (by omega)
    have c1 := small_le xk nb (bitLen (c (σ.symm 1))) 0 (hb _) (by omega)
    have c2 := small_le xk nb (bitLen (c (σ.symm 2))) 0 (hb _) (by omega)
    omega


/-- **Horner's rule**: `hD := rank(a₀, c'₀, a₁, c'₁, a₂, c'₂, a₃) + 2^A` with the new chunk value
`c'_j` on the name stack of `σ j`. -/
def horner (σ : Equiv.Perm (Fin 3)) : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk (wk .hD) .mark) (.seq (cpT xk (wk .vA0) (wk .hD))
  (.seq (mulT xk (wk .hD) (wk .c2L)) (.seq (addT xk (wk .hD) (wk (nameW (σ 0))))
  (.seq (mulT xk (wk .hD) sN1) (.seq (addT xk (wk .hD) (wk .vA1))
  (.seq (mulT xk (wk .hD) (wk .c2L)) (.seq (addT xk (wk .hD) (wk (nameW (σ 1))))
  (.seq (mulT xk (wk .hD) sN2) (.seq (addT xk (wk .hD) (wk .vA2))
  (.seq (mulT xk (wk .hD) (wk .c2L)) (.seq (addT xk (wk .hD) (wk (nameW (σ 2))))
  (.seq (mulT xk (wk .hD) sN3) (.seq (addT xk (wk .hD) (wk .vA3))
    (addT xk (wk .hD) (wk .c2A)))))))))))))))

theorem hD_nodup (j : Fin 3) :
    [(wk .hD : XK E'), wk (nameW j), wk .iT, wk .u1, wk .u2, wk .u3].Nodup := by
  fin_cases j <;> simp [nameW]

theorem nm_ne (j : Fin 3) : (wk (nameW j) : XK E') ≠ wk .hD := by
  fin_cases j <;> simp [nameW]

theorem runs_horner (σ : Equiv.Perm (Fin 3)) (a0 a1 a2 a3 N1 N2 N3 Q P nb : ℕ) (d : Fin 3 → ℕ)
    (S : XK E' → List Sym) (rA0 rA1 rA2 rA3 r1 r2 r3 rQ rP : List Sym) (rN : Fin 3 → List Sym)
    (hrA0 : TermOK rA0) (hrA1 : TermOK rA1) (hrA2 : TermOK rA2) (hrA3 : TermOK rA3)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3) (hrQ : TermOK rQ) (hrP : TermOK rP)
    (hrN : ∀ j, TermOK (rN j))
    (hA0 : S (wk .vA0) = natSyms a0 ++ rA0) (hA1 : S (wk .vA1) = natSyms a1 ++ rA1)
    (hA2 : S (wk .vA2) = natSyms a2 ++ rA2) (hA3 : S (wk .vA3) = natSyms a3 ++ rA3)
    (h1 : S sN1 = natSyms N1 ++ r1) (h2 : S sN2 = natSyms N2 ++ r2)
    (h3 : S sN3 = natSyms N3 ++ r3) (hQ : S (wk .c2L) = natSyms Q ++ rQ)
    (hP : S (wk .c2A) = natSyms P ++ rP) (hN : ∀ j, S (wk (nameW j)) = natSyms (d j) ++ rN j)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) (hQ1 : 1 ≤ Q)
    (hfin : ((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q + d (σ 2)) * N3 +
      a3) + P < 2 ^ nb)
    (h1b : bitLen N1 ≤ nb) (h2b : bitLen N2 ≤ nb) (h3b : bitLen N3 ≤ nb) (hQb : bitLen Q ≤ nb) :
    Runs (horner xk σ) S
      (Function.update S (wk .hD) (natSyms (((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) *
        N2 + a2) * Q + d (σ 2)) * N3 + a3) + P) ++ Sym.mark :: S (wk .hD)))
      (fun _ => True) (15 * opCost xk nb) := by
  have bl : ∀ x, x ≤ ((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q +
      d (σ 2)) * N3 + a3) + P → bitLen x ≤ nb := fun x hx =>
    TMFw.W3s.bitLen_le_of_lt (lt_of_le_of_lt hx hfin)
  have m13 : (((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q + d (σ 2)) * N3 + a3
      ≤ ((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q + d (σ 2)) * N3 + a3) + P :=
    Nat.le_add_right _ _
  have m12 := le_trans (Nat.le_add_right _ a3) m13
  have m11 := le_trans (Nat.le_mul_of_pos_right _ hN3) m12
  have m10 := le_trans (Nat.le_add_right _ (d (σ 2))) m11
  have m9 := le_trans (Nat.le_mul_of_pos_right _ hQ1) m10
  have m8 := le_trans (Nat.le_add_right _ a2) m9
  have m7 := le_trans (Nat.le_mul_of_pos_right _ hN2) m8
  have m6 := le_trans (Nat.le_add_right _ (d (σ 1))) m7
  have m5 := le_trans (Nat.le_mul_of_pos_right _ hQ1) m6
  have m4 := le_trans (Nat.le_add_right _ a1) m5
  have m3 := le_trans (Nat.le_mul_of_pos_right _ hN1) m4
  have m2 := le_trans (Nat.le_add_right _ (d (σ 0))) m3
  have m1 := le_trans (Nat.le_mul_of_pos_right _ hQ1) m2
  have e0 := le_trans (Nat.le_add_left (d (σ 0)) _) m3
  have e1 := le_trans (Nat.le_add_left a1 _) m5
  have e2 := le_trans (Nat.le_add_left (d (σ 1)) _) m7
  have e3 := le_trans (Nat.le_add_left a2 _) m9
  have e4 := le_trans (Nat.le_add_left (d (σ 2)) _) m11
  have e5 := le_trans (Nat.le_add_left a3 _) m13
  have e6 := Nat.le_add_left P ((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q +
      d (σ 2)) * N3 + a3)
  have X := WP.W9comp.runs_seq (runs_pushW xk (wk .hD) .mark S)
    (WP.W9comp.runs_seq (runs_copyW xk (src := wk .vA0) (dst := wk .hD) (tmp := wk .u1) (by simp) (by simp) (by simp) a0 rA0 _ hrA0 (by simp [Function.update_apply, hA0]))
    (WP.W9comp.runs_seq (runs_mulBy xk (k := wk .hD) (b := wk .c2L) (t := wk .iT) (A := wk .u1) (Bs := wk .u2) (Acc := wk .u3) (T := wk .u4) (by simp) a0 Q nb (Sym.mark :: S (wk .hD)) rQ _ (termOK_mark _) hrQ (by simp [Function.update_apply]) (by simp [Function.update_apply, hQ]) (bl _ m1) hQb (bl _ m2))
    (WP.W9comp.runs_seq (runs_addTo xk (k := wk .hD) (b := wk (nameW (σ 0))) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (hD_nodup _) (a0 * Q) (d (σ 0)) nb (Sym.mark :: S (wk .hD)) (rN (σ 0)) _ (termOK_mark _) (hrN _) (by simp [Function.update_apply]) (by simp [Function.update_apply, (nm_ne _), hN]) (bl _ m2) (bl _ e0) (bl _ m3))
    (WP.W9comp.runs_seq (runs_mulBy xk (k := wk .hD) (b := sN1) (t := wk .iT) (A := wk .u1) (Bs := wk .u2) (Acc := wk .u3) (T := wk .u4) (by simp) (a0 * Q + d (σ 0)) N1 nb (Sym.mark :: S (wk .hD)) r1 _ (termOK_mark _) hr1 (by simp [Function.update_apply]) (by simp [Function.update_apply, h1]) (bl _ m3) h1b (bl _ m4))
    (WP.W9comp.runs_seq (runs_addTo xk (k := wk .hD) (b := wk .vA1) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (by simp) ((a0 * Q + d (σ 0)) * N1) a1 nb (Sym.mark :: S (wk .hD)) rA1 _ (termOK_mark _) hrA1 (by simp [Function.update_apply]) (by simp [Function.update_apply, hA1]) (bl _ m4) (bl _ e1) (bl _ m5))
    (WP.W9comp.runs_seq (runs_mulBy xk (k := wk .hD) (b := wk .c2L) (t := wk .iT) (A := wk .u1) (Bs := wk .u2) (Acc := wk .u3) (T := wk .u4) (by simp) ((a0 * Q + d (σ 0)) * N1 + a1) Q nb (Sym.mark :: S (wk .hD)) rQ _ (termOK_mark _) hrQ (by simp [Function.update_apply]) (by simp [Function.update_apply, hQ]) (bl _ m5) hQb (bl _ m6))
    (WP.W9comp.runs_seq (runs_addTo xk (k := wk .hD) (b := wk (nameW (σ 1))) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (hD_nodup _) (((a0 * Q + d (σ 0)) * N1 + a1) * Q) (d (σ 1)) nb (Sym.mark :: S (wk .hD)) (rN (σ 1)) _ (termOK_mark _) (hrN _) (by simp [Function.update_apply]) (by simp [Function.update_apply, (nm_ne _), hN]) (bl _ m6) (bl _ e2) (bl _ m7))
    (WP.W9comp.runs_seq (runs_mulBy xk (k := wk .hD) (b := sN2) (t := wk .iT) (A := wk .u1) (Bs := wk .u2) (Acc := wk .u3) (T := wk .u4) (by simp) (((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) N2 nb (Sym.mark :: S (wk .hD)) r2 _ (termOK_mark _) hr2 (by simp [Function.update_apply]) (by simp [Function.update_apply, h2]) (bl _ m7) h2b (bl _ m8))
    (WP.W9comp.runs_seq (runs_addTo xk (k := wk .hD) (b := wk .vA2) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (by simp) ((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2) a2 nb (Sym.mark :: S (wk .hD)) rA2 _ (termOK_mark _) hrA2 (by simp [Function.update_apply]) (by simp [Function.update_apply, hA2]) (bl _ m8) (bl _ e3) (bl _ m9))
    (WP.W9comp.runs_seq (runs_mulBy xk (k := wk .hD) (b := wk .c2L) (t := wk .iT) (A := wk .u1) (Bs := wk .u2) (Acc := wk .u3) (T := wk .u4) (by simp) ((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) Q nb (Sym.mark :: S (wk .hD)) rQ _ (termOK_mark _) hrQ (by simp [Function.update_apply]) (by simp [Function.update_apply, hQ]) (bl _ m9) hQb (bl _ m10))
    (WP.W9comp.runs_seq (runs_addTo xk (k := wk .hD) (b := wk (nameW (σ 2))) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (hD_nodup _) (((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q) (d (σ 2)) nb (Sym.mark :: S (wk .hD)) (rN (σ 2)) _ (termOK_mark _) (hrN _) (by simp [Function.update_apply]) (by simp [Function.update_apply, (nm_ne _), hN]) (bl _ m10) (bl _ e4) (bl _ m11))
    (WP.W9comp.runs_seq (runs_mulBy xk (k := wk .hD) (b := sN3) (t := wk .iT) (A := wk .u1) (Bs := wk .u2) (Acc := wk .u3) (T := wk .u4) (by simp) ((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q) + d (σ 2)) N3 nb (Sym.mark :: S (wk .hD)) r3 _ (termOK_mark _) hr3 (by simp [Function.update_apply]) (by simp [Function.update_apply, h3]) (bl _ m11) h3b (bl _ m12))
    (WP.W9comp.runs_seq (runs_addTo xk (k := wk .hD) (b := wk .vA3) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (by simp) ((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q + d (σ 2)) * N3) a3 nb (Sym.mark :: S (wk .hD)) rA3 _ (termOK_mark _) hrA3 (by simp [Function.update_apply]) (by simp [Function.update_apply, hA3]) (bl _ m12) (bl _ e5) (bl _ m13))
    (runs_addTo xk (k := wk .hD) (b := wk .c2A) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (by simp) ((((((a0 * Q + d (σ 0)) * N1 + a1) * Q + d (σ 1)) * N2 + a2) * Q + d (σ 2)) * N3 + a3) P nb (Sym.mark :: S (wk .hD)) rP _ (termOK_mark _) hrP (by simp [Function.update_apply]) (by simp [Function.update_apply, hP]) (bl _ m13) (bl _ e6) (bl _ le_rfl)))))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · simp only [Function.update_idem]
  · have c0 := small_le xk nb (bitLen a0) 0 (bl _ m1) (by omega)
    omega


/-- Move symbols from `src` to `dst` up to the guard `g`. -/
def passW (g : Sym) (src dst : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  (passM g src dst).liftRegs xk.lw

theorem runs_passW {g : Sym} {src dst : XK E'} (hne : src ≠ dst) (xs ts : List Sym) (hg : g ∉ xs)
    (S : XK E' → List Sym) (hS : S src = xs ++ g :: ts) :
    Runs (passW xk g src dst) S
      (Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst))
      (fun _ => True) (4 * xs.length + 2) :=
  WP.W9comp.runs_mono (WP.W0m.runs_liftRegs xk.lw (runs_passM hne xs ts hg S hS))
    (fun _ _ => trivial) le_rfl

/-- **A kept record**: from the reversed buffer `T` to the skeleton stream `H`. -/
def goodMove : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (popW xk (wk .T)) (.seq (pushW xk sH .sep) (passW xk .sep (wk .T) sH))

theorem runs_goodMove (pl : List Bool) (ts : List Sym) (S : XK E' → List Sym)
    (hT : S (wk .T) = Sym.sep :: ((pl.map Sym.bit).reverse ++ Sym.sep :: ts)) :
    Runs (goodMove xk) S
      (Function.update (Function.update S (wk .T) (Sym.sep :: ts)) sH
        (SubNLogN.Machine.recSyms pl ++ S sH)) (fun _ => True) (4 * pl.length + 4) := by
  have X := WP.W9comp.runs_seq (runs_popW_cons xk (wk .T) S Sym.sep _ hT)
    (WP.W9comp.runs_seq (runs_pushW xk sH .sep _)
    (runs_passW xk (g := .sep) (src := wk .T) (dst := sH) (by simp) ((pl.map Sym.bit).reverse) ts (by simp) _ (by simp [Function.update_apply])))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [SubNLogN.Machine.recSyms]
  · simp only [List.length_reverse, List.length_map]
    omega

/-- **An exceptional record**: its keyed record (key = the `A`-bit destination `d`, payload from the
buffer `T`) is pushed on the bank `Bk`; the key source `hD` (`natSyms (d + 2^A)` above a floor) is
consumed with its floor. -/
def keyEmit : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (popW xk (wk .T)) (.seq (pushW xk sB .sep) (.seq (passW xk .sep (wk .T) sB)
  (.seq (pushW xk sB .sep2) (.seq (pushW xk (wk .hE) .mark)
  (.seq (passW xk .mark (wk .hD) (wk .hE)) (.seq (popW xk (wk .hE))
  (.seq (passW xk .mark (wk .hE) sB) (.seq (popW xk (wk .hE)) (popW xk (wk .hD))))))))))

theorem runs_keyEmit (A d : ℕ) (hd : d < 2 ^ A) (pl : List Bool) (ts rD : List Sym)
    (S : XK E' → List Sym)
    (hT : S (wk .T) = Sym.sep :: ((pl.map Sym.bit).reverse ++ Sym.sep :: ts))
    (hD : S (wk .hD) = natSyms (d + 2 ^ A) ++ Sym.mark :: rD) :
    Runs (keyEmit xk) S
      (Function.update (Function.update (Function.update S (wk .T) (Sym.sep :: ts)) sB
        (keyedSyms (bitsLE A d, pl) ++ S sB)) (wk .hD) rD)
      (fun _ => True) (4 * pl.length + 8 * A + 30) := by
  have X := WP.W9comp.runs_seq (runs_popW_cons xk (wk .T) S Sym.sep _ hT)
    (WP.W9comp.runs_seq (runs_pushW xk sB .sep _)
    (WP.W9comp.runs_seq (runs_passW xk (g := .sep) (src := wk .T) (dst := sB) (by simp) ((pl.map Sym.bit).reverse) ts (by simp) _ (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_pushW xk sB .sep2 _)
    (WP.W9comp.runs_seq (runs_pushW xk (wk .hE) .mark _)
    (WP.W9comp.runs_seq (runs_passW xk (g := .mark) (src := wk .hD) (dst := wk .hE) (by simp) ((bitsLE A d).map Sym.bit ++ [Sym.bit true]) rD (by simp) _ (by simp [Function.update_apply, hD, natSyms_add_two_pow A d hd]))
    (WP.W9comp.runs_seq (runs_popW_cons xk (wk .hE) _ (Sym.bit true) (((bitsLE A d).map Sym.bit).reverse ++ Sym.mark :: S (wk .hE)) (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_passW xk (g := .mark) (src := wk .hE) (dst := sB) (by simp) (((bitsLE A d).map Sym.bit).reverse) (S (wk .hE)) (by simp) _ (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_popW_cons xk (wk .hE) _ Sym.mark (S (wk .hE)) (by simp [Function.update_apply]))
    (runs_popW_cons xk (wk .hD) _ Sym.mark rD (by simp [Function.update_apply]))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [keyedSyms]
  · simp only [List.length_reverse, List.length_map, List.length_append, List.length_singleton,
      bitsLE, List.length_range]
    omega

end Rec

end SubNLogN.Machine.AppC.C7ExtractAux

