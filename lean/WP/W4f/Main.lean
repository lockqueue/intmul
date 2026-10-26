import WP.W4f.Add

/-!
# WP.W4f.Main — the lifting loop

`mainLoop_eval`: from a residual `s` (`|s| = n`, LSB on top of `kS`, above a mark), the loop pops
`s` bit by bit, pushes the emitted bits `h` (`|h| = n`) on `kY` (so `kY` gets `h.reverse`), keeps
`u2`, `kT`, `kV` intact, and establishes the Hensel invariant `2^n ∣ (2·u2 − 1)·h + s`.
Cost `≤ 16·(n+1)²`.
-/

namespace WP.W4f

open TMFw TMFw.Lib TMFw.Contracts Computability

variable {K : Type} [DecidableEq K]

/-- The conditional addition after popping the residual's LSB `x`. -/
theorem iteAdd_eval {kS kU kV kT : K} (hSU : kS ≠ kU) (hSV : kS ≠ kV) (hST : kS ≠ kT)
    (hUV : kU ≠ kV) (hUT : kU ≠ kT) (hVT : kV ≠ kT) (u2 : ℕ) (S0 T0 V0 r1 : List Sym)
    (hr1 : TermOK r1) (x : Bool) (s : List Bool) (a c : Bool) (S : K → List Sym)
    (hS : S kS = s.map Sym.bit ++ Sym.mark :: S0) (hU : S kU = natSyms u2 ++ r1)
    (hT : S kT = Sym.mark :: T0) (hV : S kV = Sym.mark :: V0) :
    ∃ v' t, t ≤ 15 * s.length + 13 ∧
      Eval [] (.ite (fun v : Reg => optBit v.1) (addPhase kS kU kV kT) skip)
        ⟨(some (Sym.bit x), a, c), S⟩
        ⟨v', Function.update S kS
          ((bif x then addBits s (encodeNat u2) false else s).map Sym.bit ++
            Sym.mark :: S0)⟩ t := by
  cases x with
  | true =>
    obtain ⟨v', t, ht, e⟩ := addPhase_eval hSU hSV hST hUV hUT hVT s (encodeNat u2)
      (some (Sym.bit true), a, c) S S0 T0 V0 r1 hr1 hS hU hT hV
    exact ⟨v', t + 1, by omega, Eval.ite_true (by rfl) e⟩
  | false =>
    have hfin : Function.update S kS
        ((bif false then addBits s (encodeNat u2) false else s).map Sym.bit ++
          Sym.mark :: S0) = S := by
      show Function.update S kS (s.map Sym.bit ++ Sym.mark :: S0) = S
      rw [← hS, Function.update_eq_self]
    exact ⟨_, 2, by omega,
      (Eval.ite_false (by rfl) (skip_eval [] _)).of_eq (st_eq rfl hfin.symm) rfl⟩

theorem mainLoop_eval {kS kU kV kT kY : K} (hSU : kS ≠ kU) (hSV : kS ≠ kV) (hST : kS ≠ kT)
    (hSY : kS ≠ kY) (hUV : kU ≠ kV) (hUT : kU ≠ kT) (hUY : kU ≠ kY) (hVT : kV ≠ kT)
    (hVY : kV ≠ kY) (hTY : kT ≠ kY) (u2 : ℕ) (S0 T0 V0 r1 : List Sym) (hr1 : TermOK r1) :
    ∀ (n : ℕ) (s : List Bool) (a c : Bool) (S : K → List Sym), s.length = n →
      S kS = s.map Sym.bit ++ Sym.mark :: S0 → S kU = natSyms u2 ++ r1 →
      S kT = Sym.mark :: T0 → S kV = Sym.mark :: V0 →
      ∃ h v' t, h.length = n ∧
        (2 : ℤ) ^ n ∣ (2 * (u2 : ℤ) - 1) * (bitsVal h : ℤ) + (bitsVal s : ℤ) ∧
        t ≤ 16 * ((n + 1) * (n + 1)) ∧
        Eval [] (mainLoop kS kU kV kT kY) ⟨((s.map Sym.bit ++ Sym.mark :: S0).head?, a, c), S⟩
          ⟨v', Function.update (Function.update S kS (Sym.mark :: S0)) kY
            (h.reverse.map Sym.bit ++ S kY)⟩ t
  | 0, s, a, c, S, hlen, hS, _, _, _ => by
    have hs : s = [] := List.eq_nil_of_length_eq_zero hlen
    subst hs
    have hS' : S kS = Sym.mark :: S0 := hS
    have hfin : Function.update (Function.update S kS (Sym.mark :: S0)) kY
        (([] : List Bool).reverse.map Sym.bit ++ S kY) = S := by
      simp only [List.reverse_nil, List.map_nil, List.nil_append]
      rw [← hS', Function.update_eq_self, Function.update_eq_self]
    refine ⟨[], _, 1, rfl, ?_, by omega,
      (Eval.loop_false (symBit_termOK (TermOK.cons rfl S0) _)).of_eq (st_eq rfl hfin.symm) rfl⟩
    simp
  | n + 1, s, a, c, S, hlen, hS, hU, hT, hV => by
    obtain ⟨x, s', rfl⟩ : ∃ x s', s = x :: s' := by
      cases s with
      | nil => simp at hlen
      | cons x s' => exact ⟨x, s', rfl⟩
    have hlen' : s'.length = n := by simpa using hlen
    have hS' : S kS = Sym.bit x :: (s'.map Sym.bit ++ Sym.mark :: S0) := hS
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S kS (s'.map Sym.bit ++ Sym.mark :: S0) :=
      ⟨_, rfl⟩
    have e1 := (pp_eval kS (((x :: s').map Sym.bit ++ Sym.mark :: S0).head?, a, c) S _ _
      hS').of_eq (st_eq rfl hS1.symm) rfl
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 kY (Sym.bit x :: S1 kY) := ⟨_, rfl⟩
    have e2 := (pr_eval kY (Sym.bit x) (a, c) S1).of_eq (st_eq rfl hS2.symm) rfl
    have h2S : S2 kS = s'.map Sym.bit ++ Sym.mark :: S0 := by
      rw [hS2, Function.update_of_ne hSY, hS1, Function.update_self]
    have h2U : S2 kU = natSyms u2 ++ r1 := by
      rw [hS2, Function.update_of_ne hUY, hS1, Function.update_of_ne (Ne.symm hSU), hU]
    have h2T : S2 kT = Sym.mark :: T0 := by
      rw [hS2, Function.update_of_ne hTY, hS1, Function.update_of_ne (Ne.symm hST), hT]
    have h2V : S2 kV = Sym.mark :: V0 := by
      rw [hS2, Function.update_of_ne hVY, hS1, Function.update_of_ne (Ne.symm hSV), hV]
    obtain ⟨⟨o3, a3, c3⟩, t3, ht3, e3⟩ := iteAdd_eval hSU hSV hST hUV hUT hVT u2 S0 T0 V0 r1 hr1
      x s' a c S2 h2S h2U h2T h2V
    obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 kS
        ((bif x then addBits s' (encodeNat u2) false else s').map Sym.bit ++ Sym.mark :: S0) :=
      ⟨_, rfl⟩
    have e3' := e3.of_eq (st_eq rfl hS3.symm) rfl
    have h3S : S3 kS = (bif x then addBits s' (encodeNat u2) false else s').map Sym.bit ++
        Sym.mark :: S0 := by
      rw [hS3, Function.update_self]
    have h3U : S3 kU = natSyms u2 ++ r1 := by
      rw [hS3, Function.update_of_ne (Ne.symm hSU), h2U]
    have h3T : S3 kT = Sym.mark :: T0 := by
      rw [hS3, Function.update_of_ne (Ne.symm hST), h2T]
    have h3V : S3 kV = Sym.mark :: V0 := by
      rw [hS3, Function.update_of_ne (Ne.symm hSV), h2V]
    have e4 := pk_eval kS (o3, a3, c3) S3 _ h3S
    have hlen'' : (bif x then addBits s' (encodeNat u2) false else s').length = n := by
      cases x
      · exact hlen'
      · rw [← hlen']
        exact length_addBits _ _ _
    obtain ⟨h', v', t, hh', hdvd, ht, ih⟩ := mainLoop_eval hSU hSV hST hSY hUV hUT hUY hVT hVY
      hTY u2 S0 T0 V0 r1 hr1 n _ a3 c3 S3 hlen'' h3S h3U h3T h3V
    have hfin : Function.update (Function.update S3 kS (Sym.mark :: S0)) kY
        (h'.reverse.map Sym.bit ++ S3 kY) =
        Function.update (Function.update S kS (Sym.mark :: S0)) kY
          ((x :: h').reverse.map Sym.bit ++ S kY) := by
      funext j
      by_cases h1 : j = kY
      · rw [h1]
        simp only [Function.update_self, hS3, hS2, hS1, Function.update_of_ne (Ne.symm hSY),
          List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.cons_append, List.nil_append]
      by_cases h2 : j = kS
      · rw [h2]
        simp only [Function.update_self, Function.update_of_ne hSY]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2, hS3, hS2, hS1]
    refine ⟨x :: h', v', 1 + (1 + (t3 + 1)) + t + 1, by simp [hh'], ?_, ?_,
      (Eval.loop_true (by rfl) (Eval.seq e1 (Eval.seq e2 (Eval.seq e3' e4))) ih).of_eq
        (st_eq rfl hfin) rfl⟩
    · cases x
      · exact hensel_step_false u2 s' h' n hdvd
      · exact hensel_step_true u2 s' h' n hlen' hdvd
    · have hsq : (n + 1 + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + 2 * n + 3 := by ring
      rw [hsq]
      omega

#assert_std_axioms iteAdd_eval mainLoop_eval

end WP.W4f
