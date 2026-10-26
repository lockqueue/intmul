import WP.W7k3t.Ser

set_option linter.unusedSimpArgs false

/-!
# WP.W7k3t.SerLoop — `SER`: the whole series loop

`z += (serState a0 c d (fun _ => 1) g N).2` within `(N + 1)·(160·uc U W)`.

Host `Loc 5 19`; named `0 a0`, `1 c` (signed), `2 d`, `3 N` (naturals), all restored; `4` destination.
`serProg = serSetup ⬝ tcd (counter on `.inr 5`) serBody ⬝ serFinal`:
* `serSetup` (12): the loop state `serSt S a0 0 0 d N` (`Z = 0`, `a = a0 + 0`, `s = 0`, `k = 0`,
  signed `d`, counter `N`);
* the counted loop (`cdLoop_lt_ht`, a variant of `HT.cdLoop` needing the body only for `i < N`):
  iteration `i` runs `serBody_spec` at `k = N - (i+1)`;
* `serFinal` (15): `z += s + 0`, drop the scratch values and floors.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-! ## Loop rule (body needed only below the bound) -/

theorem loopCost_le_lt (B : ℕ → ℕ) (b : ℕ) :
    ∀ n, (∀ i < n, B i ≤ b) → loopCost B n ≤ n * (b + 1) + 1
  | 0, _ => by simp [loopCost]
  | n + 1, h => by
    have ih := loopCost_le_lt B b n (fun i hi => h i (by omega))
    have hn := h n (by omega)
    simp only [loopCost]
    rw [Nat.succ_mul]
    omega

section CdLoop

variable {a b : ℕ} {σ : Type}

/-- **Counted loop rule**, body required only for counter values below the start `n`. -/
theorem cdLoop_lt_ht {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ}
    (hz : SpecIsZero Iz Cz) (hd : SpecDec Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R)
    (ctr dflt : Loc a b) (hcap : 4 + 1 ≤ a + b) (rc : List Sym) (hrc : TermOK rc)
    (St : ℕ → Loc a b → List Sym) (hSt : ∀ i, St i ctr = natSyms i ++ rc)
    (body : Prog (Loc a b) (fun _ => Sym) σ) (cb : ℕ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    (n : ℕ)
    (hbody : ∀ i < n, HT ρ (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) cb) :
    HT ρ (St n) (cdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (bitLen (i + 1) + 1) + cb + Cz) n) := by
  have htest : ∀ i, Triple ρ (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i =>
    callI_same Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i)) ρ
  refine Triple.seq (Triple.post (htest n) (fun s hs => (⟨le_rfl, hs⟩ :
    n ≤ n ∧ s.stk = St n ∧ Iz.obs (lz.get s.var) = decide (n = 0)))) ?_
  have hloop := Triple.loop (ρ := ρ) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun k s => k ≤ n ∧ s.stk = St k ∧ Iz.obs (lz.get s.var) = decide (k = 0))
    (B := fun i => Cd * (bitLen (i + 1) + 1) + cb + Cz) ?_ ?_ ?_ n
  · exact Triple.post hloop (fun s hs => hs.2.1)
  · intro k
    rintro s ⟨hk, hs, -⟩
    have hdec : HT ρ (St (k + 1)) (callI Id [ctr] dflt ld)
        (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
        (Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
      HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (k + 1)) (.inl 0) _
        (hd k rc _ hrc (hSt (k + 1))) ρ
    have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
      zerosLead_le_length _
    obtain ⟨s', t, e, ⟨hs', hobs'⟩, ht⟩ :=
      Triple.seq (Triple.seq hdec (hbody k (by omega))) (htest k) s hs
    refine ⟨s', t, e, ⟨by omega, hs', hobs'⟩, ?_⟩
    have : Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤ Cd * (bitLen (k + 1) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    show t ≤ Cd * (bitLen (k + 1) + 1) + cb + Cz
    omega
  · intro k s hs
    simp [hs.2.2]
  · intro s hs
    simp [hs.2.2]

end CdLoop

/-! ## The program -/

section Prog

variable (I : TI) (G : Prog (Loc 2 22) (fun _ => Sym) I.R) (hG : G.Closed)

/-- Set up `serSt S a0 0 0 d N`. -/
def serSetup : Prog (Loc 5 19) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (pushS (.inr 0) .pos).seq <|
  (pushS (.inr 1) .mark).seq <| (tai I (.inl 0) (.inr 0) (.inr 1)).seq <|
  (pushS (.inr 2) .mark).seq <| (pushS (.inr 2) .pos).seq <|
  (pushS (.inr 3) .mark).seq <|
  (pushS (.inr 4) .mark).seq <| (tcp I (.inl 2) (.inr 4)).seq <| (pushS (.inr 4) .pos).seq <|
  (pushS (.inr 5) .mark).seq (tcp I (.inl 3) (.inr 5))

/-- `z += s + 0`; drop the loop state. -/
def serFinal : Prog (Loc 5 19) (fun _ => Sym) I.R :=
  (tai I (.inr 2) (.inr 0) (.inl 4)).seq <| (popS (.inr 5)).seq <|
  (popS (.inr 4)).seq <| (tdr I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (tdr I (.inr 3)).seq <| (popS (.inr 3)).seq <|
  (tdrI I (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (tdrI I (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (popS (.inr 0)).seq (popS (.inr 0))

/-- **SER.** -/
def serProg : Prog (Loc 5 19) (fun _ => Sym) I.R :=
  (serSetup I).seq ((tcd I (.inr 5) (serBody I G hG)).seq (serFinal I))

theorem serProg_closed : (serProg I G hG).Closed :=
  ⟨⟨trivial, trivial, trivial, callI_closed _ _ _ _, trivial, trivial, trivial, trivial,
      callI_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _⟩,
    tcd_closed _ _ _ (serBody_closed I G hG),
    ⟨callI_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _,
      trivial, tdrI_closed _ _, trivial, tdrI_closed _ _, trivial, trivial, trivial⟩⟩

end Prog

/-! ## Specification -/

theorem ser_intSyms_zero : intSyms 0 = [Sym.pos] := by
  simp [intSyms, sgnSym, natSyms, encodeNat_zero]

theorem ser_natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem ser_av_succ (a0 c : ℤ) (d : ℕ) (g : ℕ → ℕ) (K : ℕ) :
    (serState a0 c d (fun _ => 1) g (K + 1)).1 =
      divRoundRatInt ((serState a0 c d (fun _ => 1) g K).1 * c) ((g K * d : ℕ) : ℤ) := by
  rw [serState_succ]
  show IntMul.divRoundRatInt ((serState a0 c d (fun _ => 1) g K).1 * c * ((1 : ℕ) : ℤ))
    (((g K : ℕ) : ℤ) * (d : ℤ)) = _
  rw [Nat.cast_one, mul_one, ← Nat.cast_mul]
  rfl

section Spec

variable {I : TI} {U : ℕ}

theorem serSetup_spec (hI : I.Ok U) (a0 : ℤ) (d Nn : ℕ) (r0 r2 r3 : List Sym)
    (S : Loc 5 19 → List Sym) (h0 : TermOK r0) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : S (.inl 0) = intSyms a0 ++ r0) (e2 : S (.inl 2) = natSyms d ++ r2)
    (e3 : S (.inl 3) = natSyms Nn ++ r3) {W : ℕ} (ha : bitLen a0.natAbs ≤ W)
    (hd : bitLen d ≤ W) (hN : bitLen Nn ≤ W) :
    HT [] S (serSetup I) (serSt S a0 0 0 d Nn) (12 * uc U W) := by
  have hz : bitLen (0 : ℤ).natAbs ≤ W := by simp [bitLen_zero]
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (push_ht hI (.inr 0) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (tai_ht hI (.inl 0) (.inr 0) (.inr 1) (by decide) _ a0 0 r0 (Sym.mark :: S (.inr 0))
      h0 (termOK_mark _) (by simp (disch := decide) only [Function.update_of_ne, e0])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne,
        ser_intSyms_zero, List.cons_append, List.nil_append]) ha hz []) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 2) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 3) .mark _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 4) .mark _ (W := W) []) <|
    HT.seq (tcp_ht hI (.inl 2) (.inr 4) (by decide) _ d r2 h2
      (by simp (disch := decide) only [Function.update_of_ne, e2]) hd []) <|
    HT.seq (push_ht hI (.inr 4) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 5) .mark _ (W := W) []) <|
    tcp_ht hI (.inl 3) (.inr 5) (by decide) _ Nn r3 h3
      (by simp (disch := decide) only [Function.update_of_ne, e3]) hN []).of_eq ?_
      (by by_contra hc; omega)
  unfold serSt
  simp (disch := decide) only [↓Function.update_self, ↓Function.update_of_ne]
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne, add_zero,
    ser_intSyms_zero, ser_natSyms_zero, List.cons_append, List.nil_append]

theorem serFinal_spec (hI : I.Ok U) (S : Loc 5 19 → List Sym) (av sv : ℤ) (k d : ℕ) {W : ℕ}
    (hav : bitLen av.natAbs ≤ W) (hsv : bitLen sv.natAbs ≤ W) (hk : bitLen k ≤ W)
    (hd : bitLen d ≤ W) :
    HT [] (serSt S av sv k d 0) (serFinal I)
      (Function.update S (.inl 4) (intSyms sv ++ S (.inl 4))) (15 * uc U W) := by
  have hz : bitLen (0 : ℤ).natAbs ≤ W := by simp [bitLen_zero]
  unfold serSt
  refine (HT.seq (tai_ht hI (.inr 2) (.inr 0) (.inl 4) (by decide) _ sv 0 (Sym.mark :: S (.inr 2))
      (Sym.mark :: S (.inr 0)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hsv hz []) <|
    HT.seq (pop_ht hI (.inr 5) _ .mark (S (.inr 5))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne,
        ser_natSyms_zero, List.nil_append]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 4) _ .pos (natSyms d ++ Sym.mark :: S (.inr 4))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 4) _ d (Sym.mark :: S (.inr 4)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hd []) <|
    HT.seq (pop_ht hI (.inr 4) _ .mark (S (.inr 4))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 3) _ k (Sym.mark :: S (.inr 3)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hk []) <|
    HT.seq (pop_ht hI (.inr 3) _ .mark (S (.inr 3))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 2) _ sv (Sym.mark :: S (.inr 2)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hsv []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark (S (.inr 2))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdrI_ht hI (.inr 1) _ av (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hav []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark (S (.inr 1))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 0) _ .pos (Sym.mark :: S (.inr 0))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne,
        ser_intSyms_zero, List.cons_append, List.nil_append]) (W := W) []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by omega)
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne, add_zero]

/-- **SER**: `z += (serState a0 c d (fun _ => 1) g N).2` within `(N + 1)·(160·uc U W)`. -/
theorem serProg_spec (hI : I.Ok U) {g : ℕ → ℕ}
    {G : Prog (Loc 2 22) (fun _ => Sym) I.R} (hG : G.Closed) (hGs : GSpec I U g G)
    (a0 c : ℤ) (d Nn : ℕ) (r0 r1 r2 r3 : List Sym) (S : Loc 5 19 → List Sym)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : S (.inl 0) = intSyms a0 ++ r0) (e1 : S (.inl 1) = intSyms c ++ r1)
    (e2 : S (.inl 2) = natSyms d ++ r2) (e3 : S (.inl 3) = natSyms Nn ++ r3) {W : ℕ}
    (hc : bitLen c.natAbs ≤ W) (hd : bitLen d ≤ W) (hN : bitLen Nn ≤ W)
    (ha : ∀ k ≤ Nn, bitLen (serState a0 c d (fun _ => 1) g k).1.natAbs ≤ W)
    (hs : ∀ k ≤ Nn, bitLen (serState a0 c d (fun _ => 1) g k).2.natAbs ≤ W)
    (hac : ∀ k < Nn, bitLen ((serState a0 c d (fun _ => 1) g k).1 * c).natAbs ≤ W)
    (hgd : ∀ k < Nn, bitLen (g k * d) ≤ W) (hpos : ∀ k < Nn, 0 < g k * d) :
    HT [] S (serProg I G hG)
      (Function.update S (.inl 4) (intSyms (serState a0 c d (fun _ => 1) g Nn).2 ++ S (.inl 4)))
      ((Nn + 1) * (160 * uc U W)) := by
  set St : ℕ → Loc 5 19 → List Sym := fun i =>
    serSt S (serState a0 c d (fun _ => 1) g (Nn - i)).1 (serState a0 c d (fun _ => 1) g (Nn - i)).2
      (Nn - i) d i with hStdef
  have hSt : ∀ i, St i (.inr 5) = natSyms i ++ Sym.mark :: S (.inr 5) := fun i => by
    simp only [hStdef, serSt, Function.update_self]
  have hset : HT [] S (serSetup I) (St Nn) (12 * uc U W) := by
    refine (serSetup_spec hI a0 d Nn r0 r2 r3 S h0 h2 h3 e0 e2 e3 (ha 0 (Nat.zero_le _)) hd
      hN).of_eq ?_ le_rfl
    simp only [hStdef, Nat.sub_self]
    rfl
  have hloop := cdLoop_lt_ht hI.iz hI.dc I.liz I.ldc (.inr 5) (.inl 0) (by decide)
    (Sym.mark :: S (.inr 5)) (termOK_mark _) St hSt (serBody I G hG) (125 * uc U W) [] Nn
    (fun i hi => by
      have hK : Nn - i = Nn - (i + 1) + 1 := by omega
      have hKN : Nn - (i + 1) < Nn := by omega
      have hpK := hpos _ hKN
      have hd1 : 0 < d := Nat.pos_of_ne_zero (fun h => by simp [h] at hpK)
      have hgK : bitLen (g (Nn - (i + 1))) ≤ W :=
        le_trans (bitLen_mono (Nat.le_mul_of_pos_right _ hd1)) (hgd _ hKN)
      have hkW : bitLen (Nn - (i + 1)) ≤ W := le_trans (bitLen_mono (by omega)) hN
      have hpre : Function.update (St (i + 1)) (.inr 5) (natSyms i ++ Sym.mark :: S (.inr 5)) =
          serSt S (serState a0 c d (fun _ => 1) g (Nn - (i + 1))).1
            (serState a0 c d (fun _ => 1) g (Nn - (i + 1))).2 (Nn - (i + 1)) d i := by
        simp only [hStdef, serSt, Function.update_idem]
      rw [hpre]
      refine (serBody_spec hI hG hGs c r1 h1 S e1 _ _ (Nn - (i + 1)) d i (ha _ hKN.le)
        (hs _ hKN.le) (hs (Nn - (i + 1) + 1) (by omega)) (hac _ hKN) hc hkW hgK hd (hgd _ hKN)
        hpK).of_eq ?_ le_rfl
      simp only [hStdef]
      rw [hK, ser_av_succ]
      rfl)
  have hlb : loopCost (fun i => U * (bitLen (i + 1) + 1) + 125 * uc U W + U) Nn ≤
      Nn * (127 * uc U W + 1) + 1 :=
    loopCost_le_lt _ _ Nn (fun i hi => by
      have h1 : U * (bitLen (i + 1) + 1) ≤ uc U W := uc_lin (le_trans (bitLen_mono (by omega)) hN)
      have h2 : U ≤ uc U W := uc_const
      omega)
  have hfin := serFinal_spec hI S (serState a0 c d (fun _ => 1) g Nn).1
    (serState a0 c d (fun _ => 1) g Nn).2 Nn d (ha Nn le_rfl) (hs Nn le_rfl) hN hd
  have h0 : St 0 = serSt S (serState a0 c d (fun _ => 1) g Nn).1
      (serState a0 c d (fun _ => 1) g Nn).2 Nn d 0 := by
    simp only [hStdef, Nat.sub_zero]
  rw [h0] at hloop
  refine (HT.seq hset (HT.seq hloop hfin)).mono ?_
  have hX := uc_one (U := U) (W := W) hI.one
  have hU : U ≤ uc U W := uc_const
  have e1 : (Nn + 1) * (160 * uc U W) = 160 * (Nn * uc U W) + 160 * uc U W := by ring
  have e2 : Nn * (127 * uc U W + 1) = 127 * (Nn * uc U W) + Nn := by ring
  have hNX : Nn ≤ Nn * uc U W := Nat.le_mul_of_pos_right _ hX
  omega

end Spec

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- The series loop on host stacks. -/
def tser (I : TI) (G : Prog (Loc 2 22) (fun _ => Sym) I.R) (hG : G.Closed)
    (x0 x1 x2 x3 z : Loc a b) : HP a b I :=
  tsub I (serProg I G hG) (serProg_closed I G hG) [x0, x1, x2, x3, z]

theorem tser_ht (hI : I.Ok U) {g : ℕ → ℕ} {G : Prog (Loc 2 22) (fun _ => Sym) I.R}
    (hG : G.Closed) (hGs : GSpec I U g G) (x0 x1 x2 x3 z : Loc a b)
    (hnd : [x0, x1, x2, x3, z].Nodup) (B : Loc a b → List Sym) (a0 c : ℤ) (d Nn : ℕ)
    (r0 r1 r2 r3 : List Sym) (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : B x0 = intSyms a0 ++ r0) (e1 : B x1 = intSyms c ++ r1) (e2 : B x2 = natSyms d ++ r2)
    (e3 : B x3 = natSyms Nn ++ r3) {W : ℕ}
    (hc : bitLen c.natAbs ≤ W) (hd : bitLen d ≤ W) (hN : bitLen Nn ≤ W)
    (ha : ∀ k ≤ Nn, bitLen (serState a0 c d (fun _ => 1) g k).1.natAbs ≤ W)
    (hs : ∀ k ≤ Nn, bitLen (serState a0 c d (fun _ => 1) g k).2.natAbs ≤ W)
    (hac : ∀ k < Nn, bitLen ((serState a0 c d (fun _ => 1) g k).1 * c).natAbs ≤ W)
    (hgd : ∀ k < Nn, bitLen (g k * d) ≤ W) (hpos : ∀ k < Nn, 0 < g k * d)
    (ρ : List (HP a b I)) :
    HT ρ B (tser I G hG x0 x1 x2 x3 z)
      (Function.update B z (intSyms (serState a0 c d (fun _ => 1) g Nn).2 ++ B z))
      ((Nn + 1) * (160 * uc U W)) :=
  tsub_ht (serProg I G hG) (serProg_closed I G hG) [x0, x1, x2, x3, z] hnd rfl
    (cap_le (by norm_num)) B 4 _
    (serProg_spec hI hG hGs a0 c d Nn r0 r1 r2 r3 _ h0 h1 h2 h3 e0 e1 e2 e3 hc hd hN ha hs hac
      hgd hpos) ρ

end Host

#assert_std_axioms loopCost_le_lt cdLoop_lt_ht serProg_closed ser_intSyms_zero ser_natSyms_zero
  ser_av_succ serSetup_spec serFinal_spec serProg_spec tser_ht

end WP.W7k3t
