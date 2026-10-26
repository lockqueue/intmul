import WP.W9fNF.Prog

/-!
# WP.W9fNF.Calls — the subroutine calls and the lifted macros in the finish layout

`callSub_eval`, `callAdd_eval`, `callShr_eval`, `callNeg_eval`: the `Kit.OK` contracts read through
`emb` (exact final stacks, any registers). `liftM_eval`: a macro run on the first register
component. `pass3_eval`: W9fM's entry mover `Z → O`.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

/-- Three distinct non-pool stacks. -/
structure Tri (a b c : FS) : Prop where
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c
  pa : NotPool a
  pb : NotPool b
  pc : NotPool c

theorem Tri.inj {a b c : FS} (h : Tri a b c) {m : ℕ} (hm : m ≤ 16) :
    Function.Injective (emb hm (tri a b c)) :=
  emb_injective hm (tri_injective h.ab h.ac h.bc) (tri_notPool h.pa h.pb h.pc)

variable {κ : Kit} {Cs Ca Cn Cf : ℕ}

theorem callSub_eval (hκ : κ.OK Cs Ca Cn Cf) {a b c : FS} (h : Tri a b c) (x y : ℤ)
    (rx ry : List Sym) (B : FS → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B a = intSyms x ++ rx) (hy : B b = intSyms y ++ ry) (v : κ.Reg) :
    ∃ w t, Eval [] (callSub κ a b c) ⟨v, B⟩ ⟨w, Function.update B c (intSyms (x - y) ++ B c)⟩ t ∧
      t ≤ Cs * (bitLen x.natAbs + bitLen y.natAbs + 1) := by
  obtain ⟨w, t, e, -, ht⟩ := call_eval_upd (h.inj κ.hms) κ.lS (B := B) (.inl 2)
    (intSyms (x - y) ++ B c) (hκ.sub x y rx ry _ hrx hry hx hy) v
  exact ⟨_, t, e, ht⟩

theorem callAdd_eval (hκ : κ.OK Cs Ca Cn Cf) {a b c : FS} (h : Tri a b c) (x y : ℤ)
    (rx ry : List Sym) (B : FS → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B a = intSyms x ++ rx) (hy : B b = intSyms y ++ ry) (v : κ.Reg) :
    ∃ w t, Eval [] (callAdd κ a b c) ⟨v, B⟩ ⟨w, Function.update B c (intSyms (x + y) ++ B c)⟩ t ∧
      t ≤ Ca * (bitLen x.natAbs + bitLen y.natAbs + 1) := by
  obtain ⟨w, t, e, -, ht⟩ := call_eval_upd (h.inj κ.hma) κ.lA (B := B) (.inl 2)
    (intSyms (x + y) ++ B c) (hκ.add x y rx ry _ hrx hry hx hy) v
  exact ⟨_, t, e, ht⟩

theorem callShr_eval (hκ : κ.OK Cs Ca Cn Cf) {a b c : FS} (h : Tri a b c) (x y : ℤ)
    (rx ry : List Sym) (B : FS → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hc : TermOK (B c)) (hx : B a = intSyms x ++ rx) (hy : B b = intSyms y ++ ry) (v : κ.Reg) :
    ∃ w t, Eval [] (callShr κ a b c) ⟨v, B⟩
      ⟨w, Function.update B c (intSyms (x >>> y.natAbs) ++ B c)⟩ t ∧
      t ≤ Cf * (bitLen x.natAbs + bitLen y.natAbs + 1) := by
  obtain ⟨w, t, e, -, ht⟩ := call_eval_upd (h.inj κ.hmf) κ.lF (B := B) (.inl 2)
    (intSyms (x >>> y.natAbs) ++ B c) (hκ.shr x y rx ry _ hrx hry hc hx hy) v
  exact ⟨_, t, e, ht⟩

theorem callNeg_eval (hκ : κ.OK Cs Ca Cn Cf) {a : FS} (ha : NotPool a) (z : ℤ) (rx : List Sym)
    (B : FS → List Sym) (hrx : TermOK rx) (hz : B a = intSyms z ++ rx) (v : κ.Reg) :
    ∃ w t, Eval [] (callNeg κ a) ⟨v, B⟩ ⟨w, Function.update B a (intSyms (-z) ++ rx)⟩ t ∧
      t ≤ Cn := by
  obtain ⟨w, t, e, -, ht⟩ := call_eval_upd (emb_injective κ.hmn (one_injective a) (fun _ => ha))
    κ.lN (B := B) (.inl 0) (intSyms (-z) ++ rx) (hκ.neg z rx _ hrx hz) v
  exact ⟨_, t, e, ht⟩

/-- A macro on the first register component. -/
theorem liftM_eval {p : SProg FS} {S S' : FS → List Sym} {r' : Option Sym} {t : ℕ}
    (h : ∀ r, Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t) (v : κ.Reg) :
    Eval [] (liftM κ p) ⟨v, S⟩ ⟨(r', v.2), S'⟩ t :=
  liftFst (h v.1) v rfl

/-- Pass 3: W9fM's mover, from `Z` (entries `xs` above a non-entry `r0`) onto `O`. -/
theorem pass3_eval (xs : List (ℤ × ℤ)) (r0 : List Sym) (hr0 : WP.W9f.NotEntry r0)
    (B : FS → List Sym) (hB : B sZ = blkE xs ++ r0) (v : κ.Reg) :
    ∃ w t, Eval [] (pass3 κ) ⟨v, B⟩
      ⟨w, Function.update (Function.update B sZ r0) sO (blkE xs.reverse ++ B sO)⟩ t ∧
      t ≤ 16 * ((blkE xs).length + 1) := by
  have h := WP.W9fM.moveEntriesProg_spec xs r0 (B ∘ ιM) hr0 hB
  have hfin : (Function.update (Function.update B sZ r0) sO (blkE xs.reverse ++ B sO)) ∘ ιM =
      Function.update (Function.update (B ∘ ιM) (.inl 0) r0) (.inl 1)
        (blkE xs.reverse ++ (B ∘ ιM) (.inl 1)) := by
    funext x
    rcases x with ⟨_ | _ | x, hx⟩ | ⟨_ | x, hx⟩
    · rfl
    · rfl
    · omega
    · rfl
    · omega
  rw [← hfin] at h
  obtain ⟨w, t, e, -, ht⟩ := call_eval ιM_injective (Lens.fst _ _) h (fun k hk => by
    rw [Function.update_of_ne (show k ≠ sO from fun e => hk (.inl 1) e.symm),
      Function.update_of_ne (show k ≠ sZ from fun e => hk (.inl 0) e.symm)]) v
  exact ⟨_, t, e, ht⟩

/-! ## The stack triples used by the program -/

theorem tri_Z_A1_X : Tri sZ sA1 sX :=
  ⟨by decide, by decide, by decide, notPool_inl _, notPool_inr _ (by decide),
    notPool_inr _ (by decide)⟩

theorem tri_Z_A2_X : Tri sZ sA2 sX :=
  ⟨by decide, by decide, by decide, notPool_inl _, notPool_inr _ (by decide),
    notPool_inr _ (by decide)⟩

theorem tri_AL_A1_X : Tri sAL sA1 sX :=
  ⟨by decide, by decide, by decide, notPool_inl _, notPool_inr _ (by decide),
    notPool_inr _ (by decide)⟩

theorem tri_AL_A2_X : Tri sAL sA2 sX :=
  ⟨by decide, by decide, by decide, notPool_inl _, notPool_inr _ (by decide),
    notPool_inr _ (by decide)⟩

theorem tri_X_KI_A (Aj : FS) (h1 : sX ≠ Aj) (h2 : sKI ≠ Aj) (hp : NotPool Aj) :
    Tri sX sKI Aj :=
  ⟨by decide, h1, h2, notPool_inr _ (by decide), notPool_inr _ (by decide), hp⟩

theorem tri_A_ONE_X (Aj : FS) (h1 : Aj ≠ sONE) (h2 : Aj ≠ sX) (hp : NotPool Aj) :
    Tri Aj sONE sX :=
  ⟨h1, h2, by decide, hp, notPool_inr _ (by decide), notPool_inr _ (by decide)⟩

theorem tri_X_ONE_A (Aj : FS) (h1 : sX ≠ Aj) (h2 : sONE ≠ Aj) (hp : NotPool Aj) :
    Tri sX sONE Aj :=
  ⟨by decide, h1, h2, notPool_inr _ (by decide), notPool_inr _ (by decide), hp⟩

theorem tri_T_A2_Z : Tri sT sA2 sZ :=
  ⟨by decide, by decide, by decide, notPool_inr _ (by decide), notPool_inr _ (by decide),
    notPool_inl _⟩

theorem tri_T_A1_Z : Tri sT sA1 sZ :=
  ⟨by decide, by decide, by decide, notPool_inr _ (by decide), notPool_inr _ (by decide),
    notPool_inl _⟩

#assert_std_axioms Tri.inj callSub_eval callAdd_eval callShr_eval callNeg_eval liftM_eval pass3_eval
  tri_Z_A1_X tri_Z_A2_X tri_AL_A1_X tri_AL_A2_X tri_X_KI_A tri_A_ONE_X tri_X_ONE_A tri_T_A2_Z
  tri_T_A1_Z

end WP.W9fNF
