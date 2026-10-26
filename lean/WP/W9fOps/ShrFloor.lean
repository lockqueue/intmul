import WP.W9fOps.Shape

/-!
# WP.W9fOps.ShrFloor — `z += a >>> |b|` (floor shift, signed)

`shrFloorProg`: pop both signs; copy `|a|` onto `z` (`w3_copyNat`); then
* `a ≥ 0` (`a = n`): shift `z` right by `|b|` (`W3_shrVar`, hypothesis), push `pos`;
* `a < 0` (`a = -(n+1)`): decrement `z` to `n` (`w3_decNat`), shift right by `|b|`, increment
  (`w3_incNat`), push `neg`: `-(n+1) >>> k = -(n / 2^k + 1)` (`shiftRight_negSucc`);
push both signs back. The number's terminator is the old content of `z` (`TermOK (S z)`).
Cost `Ccp·(|a| + 1) + (Cd + Csr + Ci)·(|a| + |b| + 1) + 6` (bit lengths only: the shift costs
`min |b|ᵥ |a| ≤ |a|`), i.e. `W9fBinOp`.
-/

namespace WP.W9fOps

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Registers: two sign slots, then copier, decrementer, shifter, incrementer registers. -/
abbrev RegF (Rcp Rd Rsr Ri : Type) : Type := Option Sym × Option Sym × Rcp × Rd × Rsr × Ri

/-- Lens onto the copier's registers. -/
def lFcp (Rcp Rd Rsr Ri : Type) : Lens (RegF Rcp Rd Rsr Ri) Rcp where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the decrementer's registers. -/
def lFd (Rcp Rd Rsr Ri : Type) : Lens (RegF Rcp Rd Rsr Ri) Rd where
  get v := v.2.2.2.1
  set v w := (v.1, v.2.1, v.2.2.1, w, v.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the shifter's registers. -/
def lFsr (Rcp Rd Rsr Ri : Type) : Lens (RegF Rcp Rd Rsr Ri) Rsr where
  get v := v.2.2.2.2.1
  set v w := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, w, v.2.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the incrementer's registers. -/
def lFi (Rcp Rd Rsr Ri : Type) : Lens (RegF Rcp Rd Rsr Ri) Ri where
  get v := v.2.2.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

section

variable {mcp md msr mi : ℕ} {Rcp Rd Rsr Ri : Type}

/-- The sign-dependent part, on `z = |a| ++ Z`. -/
def shrCore (hd : md ≤ 4) (hsr : msr ≤ 4) (hi : mi ≤ 4) (Pd : Prog (Loc 1 md) (fun _ => Sym) Rd)
    (Psr : Prog (Loc 2 msr) (fun _ => Sym) Rsr) (Pi : Prog (Loc 1 mi) (fun _ => Sym) Ri) :
    Prog (Loc 3 4) (fun _ => Sym) (RegF Rcp Rd Rsr Ri) :=
  .ite (fun v => isNegR v.1)
    (.seq (call (emb f2 hd) (lFd Rcp Rd Rsr Ri) Pd)
      (.seq (call (emb f21 hsr) (lFsr Rcp Rd Rsr Ri) Psr)
        (.seq (call (emb f2 hi) (lFi Rcp Rd Rsr Ri) Pi) (.push (.inl 2) fun _ => .neg))))
    (.seq (call (emb f21 hsr) (lFsr Rcp Rd Rsr Ri) Psr) (.push (.inl 2) fun _ => .pos))

/-- `z += a >>> |b|`. -/
def shrFloorProg (hcp : mcp ≤ 4) (hd : md ≤ 4) (hsr : msr ≤ 4) (hi : mi ≤ 4)
    (Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp) (Pd : Prog (Loc 1 md) (fun _ => Sym) Rd)
    (Psr : Prog (Loc 2 msr) (fun _ => Sym) Rsr) (Pi : Prog (Loc 1 mi) (fun _ => Sym) Ri) :
    Prog (Loc 3 4) (fun _ => Sym) (RegF Rcp Rd Rsr Ri) :=
  .seq (.pop (.inl 0) fun v o => (o, v.2))
  (.seq (.pop (.inl 1) fun v o => (v.1, o, v.2.2))
  (.seq (call (emb f02 hcp) (lFcp Rcp Rd Rsr Ri) Pcp)
  (.seq (shrCore hd hsr hi Pd Psr Pi)
  (.seq (.push (.inl 1) fun v => v.2.1.getD .pos) (.push (.inl 0) fun v => v.1.getD .pos)))))

theorem shrFloorProg_closed (hcp : mcp ≤ 4) (hd : md ≤ 4) (hsr : msr ≤ 4) (hi : mi ≤ 4)
    {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp} {Pd : Prog (Loc 1 md) (fun _ => Sym) Rd}
    {Psr : Prog (Loc 2 msr) (fun _ => Sym) Rsr} {Pi : Prog (Loc 1 mi) (fun _ => Sym) Ri}
    (h1 : Pcp.Closed) (h2 : Pd.Closed) (h3 : Psr.Closed) (h4 : Pi.Closed) :
    (shrFloorProg hcp hd hsr hi Pcp Pd Psr Pi).Closed :=
  ⟨trivial, trivial, call_closed _ _ h1, ⟨⟨call_closed _ _ h2, call_closed _ _ h3,
    call_closed _ _ h4, trivial⟩, call_closed _ _ h3, trivial⟩, trivial, trivial⟩

theorem shrCore_eval (hd : md ≤ 4) (hsr : msr ≤ 4) (hi : mi ≤ 4) {Cd Csr Ci : ℕ}
    {Pd : Prog (Loc 1 md) (fun _ => Sym) Rd} {Psr : Prog (Loc 2 msr) (fun _ => Sym) Rsr}
    {Pi : Prog (Loc 1 mi) (fun _ => Sym) Ri}
    (hD : DecSpec Cd Pd) (hSr : ShrSpec Csr Psr) (hI : IncSpec Ci Pi)
    (a b : ℤ) (Z rb : List Sym) (hZ : TermOK Z) (hrb : TermOK rb) (S : Loc 3 4 → List Sym)
    (hz : S (.inl 2) = natSyms a.natAbs ++ Z) (hy : S (.inl 1) = natSyms b.natAbs ++ rb)
    (s2 : Option Sym) (rc : Rcp) (w : Rd × Rsr × Ri) :
    ∃ w' t, Eval [] (shrCore hd hsr hi Pd Psr Pi) ⟨(some (sgnSym a), s2, rc, w), S⟩
      ⟨(some (sgnSym a), s2, rc, w'),
        Function.update S (.inl 2) (intSyms (a >>> b.natAbs) ++ Z)⟩ t ∧
      t ≤ (Cd + Csr + Ci) * (bitLen a.natAbs + bitLen b.natAbs + 1) + 2 := by
  by_cases ha : a < 0
  · -- `a = -(n+1)`: decrement, shift, increment, push `neg`
    obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero ha
    have hc : isNegR (some (sgnSym (Int.negSucc n))) = true := by
      rw [isNegR_sgnSym]
      exact decide_eq_true ha
    obtain ⟨r4, t4, e4, -, ht4⟩ := call_eval_upd (emb_injective f2_injective hd)
      (hD n Z (fun l => S (emb f2 hd l)) hZ hz) (lFd Rcp Rd Rsr Ri)
      (some (sgnSym (Int.negSucc n)), s2, rc, w)
    set S4 := Function.update S (emb f2 hd (.inl 0)) (natSyms n ++ Z) with hS4
    have hS4z : S4 (.inl 2) = natSyms n ++ Z := by simp [hS4]
    have hS4y : S4 (.inl 1) = natSyms b.natAbs ++ rb := by simp [hS4, hy]
    obtain ⟨r5, t5, e5, -, ht5⟩ := call_eval_upd (emb_injective f21_injective hsr)
      (hSr n b.natAbs Z rb (fun l => S4 (emb f21 hsr l)) hZ hrb hS4z hS4y) (lFsr Rcp Rd Rsr Ri)
      (some (sgnSym (Int.negSucc n)), s2, rc, r4, w.2)
    set S5 := Function.update S4 (emb f21 hsr (.inl 0)) (natSyms (n / 2 ^ b.natAbs) ++ Z)
      with hS5
    have hS5z : S5 (.inl 2) = natSyms (n / 2 ^ b.natAbs) ++ Z := by simp [hS5]
    obtain ⟨r6, t6, e6, -, ht6⟩ := call_eval_upd (emb_injective f2_injective hi)
      (hI (n / 2 ^ b.natAbs) Z (fun l => S5 (emb f2 hi l)) hZ hS5z) (lFi Rcp Rd Rsr Ri)
      (some (sgnSym (Int.negSucc n)), s2, rc, r4, r5, w.2.2)
    set S6 := Function.update S5 (emb f2 hi (.inl 0)) (natSyms (n / 2 ^ b.natAbs + 1) ++ Z)
      with hS6
    have e7 := eval_push_eq [] (.inl 2) (fun (_ : RegF Rcp Rd Rsr Ri) => Sym.neg)
      (some (sgnSym (Int.negSucc n)), s2, rc, r4, r5, r6) S6 .neg
      (natSyms (n / 2 ^ b.natAbs + 1) ++ Z) rfl (by simp [hS6])
    refine ⟨(r4, r5, r6), _, eval_stk (Eval.ite_true hc (Eval.seq e4 (Eval.seq e5
      (Eval.seq e6 e7)))) ?_, ?_⟩
    · have hneg : ∀ q : ℕ, -((q : ℤ) + 1) < 0 := fun q => by omega
      have habs : ∀ q : ℕ, (-((q : ℤ) + 1)).natAbs = q + 1 := fun q => by omega
      rw [shiftRight_negSucc, intSyms_append, sgnSym_of_neg (hneg _), habs]
      simp only [hS6, hS5, hS4, emb_inl, f2_zero, f21_zero, Function.update_idem]
    · show _ ≤ (Cd + Csr + Ci) * (bitLen (n + 1) + bitLen b.natAbs + 1) + 2
      have h1 : zerosLead (encodeNat (n + 1)) ≤ bitLen (n + 1) := zerosLead_le_length _
      have h2 : min b.natAbs (bitLen n) ≤ bitLen (n + 1) :=
        (min_le_right _ _).trans (bitLen_mono (Nat.le_succ n))
      have h3 : ones (encodeNat (n / 2 ^ b.natAbs)) ≤ bitLen (n + 1) :=
        (ones_le_length _).trans (bitLen_mono ((Nat.div_le_self _ _).trans (Nat.le_succ n)))
      have k1 := Nat.mul_le_mul (le_refl Cd)
        (show zerosLead (encodeNat (n + 1)) + 1 ≤ bitLen (n + 1) + bitLen b.natAbs + 1 by omega)
      have k2 := Nat.mul_le_mul (le_refl Csr)
        (show min b.natAbs (bitLen n) + bitLen b.natAbs + 1 ≤
          bitLen (n + 1) + bitLen b.natAbs + 1 by omega)
      have k3 := Nat.mul_le_mul (le_refl Ci)
        (show ones (encodeNat (n / 2 ^ b.natAbs)) + 1 ≤
          bitLen (n + 1) + bitLen b.natAbs + 1 by omega)
      simp only [Nat.add_mul]
      omega
  · -- `a = n ≥ 0`: shift, push `pos`
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ a)
    have hc : isNegR (some (sgnSym (n : ℤ))) = false := by
      rw [isNegR_sgnSym]
      exact decide_eq_false (by omega)
    obtain ⟨r5, t5, e5, -, ht5⟩ := call_eval_upd (emb_injective f21_injective hsr)
      (hSr n b.natAbs Z rb (fun l => S (emb f21 hsr l)) hZ hrb hz hy) (lFsr Rcp Rd Rsr Ri)
      (some (sgnSym (n : ℤ)), s2, rc, w)
    set S5 := Function.update S (emb f21 hsr (.inl 0)) (natSyms (n / 2 ^ b.natAbs) ++ Z)
      with hS5
    have e7 := eval_push_eq [] (.inl 2) (fun (_ : RegF Rcp Rd Rsr Ri) => Sym.pos)
      (some (sgnSym (n : ℤ)), s2, rc, w.1, r5, w.2.2) S5 .pos
      (natSyms (n / 2 ^ b.natAbs) ++ Z) rfl (by simp [hS5])
    refine ⟨(w.1, r5, w.2.2), _, eval_stk (Eval.ite_false hc (Eval.seq e5 e7)) ?_, ?_⟩
    · rw [shiftRight_ofNat, intSyms_natCast, List.cons_append]
      simp only [hS5, emb_inl, f21_zero, Function.update_idem]
    · show _ ≤ (Cd + Csr + Ci) * (bitLen n + bitLen b.natAbs + 1) + 2
      have k2 := Nat.mul_le_mul (le_refl Csr)
        (show min b.natAbs (bitLen n) + bitLen b.natAbs + 1 ≤ bitLen n + bitLen b.natAbs + 1 by
          have := min_le_right b.natAbs (bitLen n)
          omega)
      simp only [Nat.add_mul]
      omega

theorem shrFloor_runs (hcp : mcp ≤ 4) (hd : md ≤ 4) (hsr : msr ≤ 4) (hi : mi ≤ 4)
    {Ccp Cd Csr Ci : ℕ} {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp}
    {Pd : Prog (Loc 1 md) (fun _ => Sym) Rd} {Psr : Prog (Loc 2 msr) (fun _ => Sym) Rsr}
    {Pi : Prog (Loc 1 mi) (fun _ => Sym) Ri}
    (hCp : CopySpec Ccp Pcp) (hD : DecSpec Cd Pd) (hSr : ShrSpec Csr Psr) (hI : IncSpec Ci Pi)
    (a b : ℤ) (ra rb : List Sym) (S : Loc 3 4 → List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hz : TermOK (S (.inl 2))) (hx : S (.inl 0) = intSyms a ++ ra)
    (hy : S (.inl 1) = intSyms b ++ rb) :
    Runs (shrFloorProg hcp hd hsr hi Pcp Pd Psr Pi) S
      (Function.update S (.inl 2) (intSyms (a >>> b.natAbs) ++ S (.inl 2))) (fun _ => True)
      (Ccp * (bitLen a.natAbs + 1) + (Cd + Csr + Ci) * (bitLen a.natAbs + bitLen b.natAbs + 1) +
        6) := by
  refine Runs.of_eval fun v => ?_
  have e1 := eval_pop_int [] (.inl 0) (fun (v : RegF Rcp Rd Rsr Ri) o => (o, v.2)) v S a ra hx
  have hS1y : Function.update S (.inl 0) (natSyms a.natAbs ++ ra) (.inl 1) = intSyms b ++ rb := by
    simp [hy]
  have e2 := eval_pop_int [] (.inl 1) (fun (v : RegF Rcp Rd Rsr Ri) o => (v.1, o, v.2.2))
    (some (sgnSym a), v.2) (Function.update S (.inl 0) (natSyms a.natAbs ++ ra)) b rb hS1y
  set S2 := Function.update (Function.update S (.inl 0) (natSyms a.natAbs ++ ra)) (.inl 1)
    (natSyms b.natAbs ++ rb) with hS2
  have hS2x : S2 (.inl 0) = natSyms a.natAbs ++ ra := by simp [hS2]
  have hS2y : S2 (.inl 1) = natSyms b.natAbs ++ rb := by simp [hS2]
  have hS2z : S2 (.inl 2) = S (.inl 2) := by simp [hS2]
  obtain ⟨r3, t3, e3, -, ht3⟩ := call_eval_upd (emb_injective f02_injective hcp)
    (hCp a.natAbs ra (fun l => S2 (emb f02 hcp l)) hra hS2x) (lFcp Rcp Rd Rsr Ri)
    (some (sgnSym a), some (sgnSym b), v.2.2)
  set S3 := Function.update S2 (emb f02 hcp (.inl 1))
    (natSyms a.natAbs ++ (fun l => S2 (emb f02 hcp l)) (.inl 1)) with hS3
  have hS3z : S3 (.inl 2) = natSyms a.natAbs ++ S (.inl 2) := by simp [hS3, hS2z]
  have hS3y : S3 (.inl 1) = natSyms b.natAbs ++ rb := by simp [hS3, hS2y]
  obtain ⟨w', t4, e4, ht4⟩ := shrCore_eval hd hsr hi hD hSr hI a b (S (.inl 2)) rb hz hrb S3
    hS3z hS3y (some (sgnSym b)) r3 v.2.2.2
  set S4 := Function.update S3 (.inl 2) (intSyms (a >>> b.natAbs) ++ S (.inl 2)) with hS4
  have e5 := eval_push_eq [] (.inl 1) (fun (v : RegF Rcp Rd Rsr Ri) => v.2.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r3, w') S4 (sgnSym b) (natSyms b.natAbs ++ rb) rfl
    (by simp [hS4, hS3y])
  have e6 := eval_push_eq [] (.inl 0) (fun (v : RegF Rcp Rd Rsr Ri) => v.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r3, w')
    (Function.update S4 (.inl 1) (sgnSym b :: (natSyms b.natAbs ++ rb))) (sgnSym a)
    (natSyms a.natAbs ++ ra) rfl (by simp [hS4, hS3, hS2x])
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
    (Eval.seq e5 e6))))) ?_, trivial, by omega⟩
  funext k
  rcases k with ⟨_ | _ | _ | i, hk⟩ | j
  · simp [hS4, hS3, hS2, hx, intSyms_append]
  · simp [hS4, hS3, hS2, hy, intSyms_append]
  · simp [hS4, hS3, hS2]
  · omega
  · simp [hS4, hS3, hS2]

end

/-- **`a >>> |b|`** (floor shift), from `W3_shrVar` (and the proved copy / dec / inc). -/
theorem shrFloor_holds (hshr : W3_shrVar) : W9fBinOp (fun a b => a >>> b.natAbs) := by
  obtain ⟨Ccp, hcp⟩ := w3_copyNat
  obtain ⟨mcp, Rcp, _o1, Pcp, hmcp, hRcp, ⟨r1⟩, hPcp, hsp1⟩ := hcp ()
  obtain ⟨Cd, hd⟩ := w3_decNat
  obtain ⟨md, Rd, _o2, Pd, hmd, hRd, ⟨r2⟩, hPd, hsp2⟩ := hd ()
  obtain ⟨Csr, hsr⟩ := hshr
  obtain ⟨msr, Rsr, _o3, Psr, hmsr, hRsr, ⟨r3⟩, hPsr, hsp3⟩ := hsr ()
  obtain ⟨Ci, hi⟩ := w3_incNat
  obtain ⟨mi, Ri, _o4, Pi, hmi, hRi, ⟨r4⟩, hPi, hsp4⟩ := hi ()
  refine ⟨Ccp + Cd + Csr + Ci + 6, 4, RegF Rcp Rd Rsr Ri,
    shrFloorProg hmcp hmd hmsr hmi Pcp Pd Psr Pi, by decide, inferInstance,
    ⟨(none, none, r1, r2, r3, r4)⟩, shrFloorProg_closed hmcp hmd hmsr hmi hPcp hPd hPsr hPi, ?_⟩
  intro a b ra rb S hra hrb hz hx hy
  refine Triple.cost_mono (shrFloor_runs hmcp hmd hmsr hmi hsp1 hsp2 hsp3 hsp4 a b ra rb S hra
    hrb hz hx hy) ?_
  have h1 := Nat.mul_le_mul (le_refl Ccp)
    (show bitLen a.natAbs + 1 ≤ bitLen a.natAbs + bitLen b.natAbs + 1 by omega)
  simp only [Nat.add_mul]
  omega

#assert_std_axioms shrFloorProg_closed shrCore_eval shrFloor_runs shrFloor_holds

end WP.W9fOps
