import WP.W4o.Basic
import Mathlib.Tactic.Ring

/-!
# WP.W4o.Fill — copy a bit block; push `k` copies of a bit (W4o piece 2)

* `copyP src dst tmp`: the seed macro `Lib.copyBlock` run on the main register `a`
  (`Prog.liftRegs (Lens.fst …)`); exact effect `dst += blk`, cost `7·|blk| + 7`.
* `fillP c Kc D C T`: `C := mark ++ copy of k`; while the top of `C` is a bit:
  push `bit c` on `D`, decrement `C` (`Lib.dec`, lifted), peek `C`; finally drop the mark.
  Cost `≤ 6k² + 19k + 12 ≤ 30·(k+1)²` (each `dec` costs `6·zerosLead + 8 ≤ 6k + 8`).

Both programs are closed. The `Eval` lemmas are generic in the environment `ρ`: the seed lemmas
are lifted with `Eval.liftRegs` at `ρ = []` and moved to any `ρ` with `Eval.env_irrel`.
Helpers live in the sub-namespace `TMFw.W4o.Fill`.
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts Computability

namespace Fill

/-- Run a seed-library program (register `Option Sym`) on the main register `a`. -/
def liftA {κ : Type} (p : SProg κ) : RProg κ :=
  p.liftRegs (Lens.fst (Option Sym) (Option Sym × Bool))

/-- `Lib.dec` on the main register. -/
def decP {κ : Type} (k t : κ) : RProg κ := liftA (Lib.dec k t)

end Fill

open Fill

/-- Copy the bit block on top of `src` onto `dst` (same order); `tmp` is scratch (restored). -/
def copyP {κ : Type} (src dst tmp : κ) : RProg κ := liftA (Lib.copyBlock src dst tmp)

/-- Push `k` copies of the bit `c` onto `D`, where `k` is the number on top of `Kc` (restored);
`C`, `T` are scratch (restored). -/
def fillP {κ : Type} (c : Bool) (Kc D C T : κ) : RProg κ :=
  .seq (pushK C .mark) <| .seq (copyP Kc C T) <| .seq (peekA C) <|
    .seq (.loop bitA (.seq (pushK D (.bit c)) (.seq (decP C T) (peekA C)))) (dropT C)

namespace Fill

/-! ## Closedness -/

theorem freeBelow_liftRegs' {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), p.FreeBelow d → (p.liftRegs l).FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => ⟨freeBelow_liftRegs' l p d h.1, freeBelow_liftRegs' l q d h.2⟩
  | .ite _ p q, d, h => ⟨freeBelow_liftRegs' l p d h.1, freeBelow_liftRegs' l q d h.2⟩
  | .loop _ p, d, h => freeBelow_liftRegs' l p d h
  | .fix b, d, h => freeBelow_liftRegs' l b (d + 1) h
  | .recur _, _, h => h

theorem copyBlock_closed' {κ : Type} (src dst tmp : κ) : (Lib.copyBlock src dst tmp).Closed :=
  ⟨trivial, ⟨⟨trivial, trivial, trivial⟩, trivial, trivial⟩, trivial, trivial, trivial, trivial⟩

theorem dec_closed' {κ : Type} (k t : κ) : (Lib.dec k t).Closed :=
  ⟨trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, trivial, trivial, trivial⟩

theorem decP_closed {κ : Type} (k t : κ) : (decP k t).Closed :=
  freeBelow_liftRegs' _ _ 0 (dec_closed' k t)

/-! ## Lifting the seed lemmas -/

/-- A closed seed program, lifted to the main register, in any environment. -/
theorem liftA_eval {κ : Type} [DecidableEq κ] {p : SProg κ} (hc : p.Closed) {v v' : Option Sym}
    {S S' : κ → List Sym} {t : ℕ} (h : Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t) (ρ : List (RProg κ))
    (r2 : Option Sym × Bool) : Eval ρ (liftA p) ⟨(v, r2), S⟩ ⟨(v', r2), S'⟩ t := by
  have h1 := Eval.liftRegs (Lens.fst (Option Sym) (Option Sym × Bool)) h (v, r2) rfl
  exact Eval.env_irrel h1 (freeBelow_liftRegs' _ p 0 hc) ρ

/-- `Lib.dec`, lifted: `natSyms (n+1) ↦ natSyms n` on `k`. -/
theorem decP_eval {κ : Type} [DecidableEq κ] {k t : κ} (hkt : k ≠ t) (ρ : List (RProg κ))
    (r : Reg) (n : ℕ) (rest : List Sym) (S : κ → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms (n + 1) ++ rest) :
    Eval ρ (decP k t) ⟨r, S⟩ ⟨(some .mark, r.2), Function.update S k (natSyms n ++ rest)⟩
      (6 * zerosLead (encodeNat (n + 1)) + 8) :=
  liftA_eval (dec_closed' k t) (Lib.dec_eval hkt [] r.1 n rest S hrest hS) ρ r.2

/-! ## Number facts -/

theorem natSyms_zero' : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

/-- The top of `natSyms n ++ rx` is a bit iff `n ≠ 0`. -/
theorem optIsBit_head_natSyms' (n : ℕ) {rx : List Sym} (hrx : TermOK rx) :
    optIsBit (natSyms n ++ rx).head? = !decide (n = 0) := by
  cases h : encodeNat n with
  | nil =>
    have hn : n = 0 := (encodeNat_eq_nil_iff n).1 h
    subst hn
    simp [natSyms, h, optIsBit_head?_of_termOK hrx]
  | cons b l =>
    have hn : n ≠ 0 := fun hn => by rw [hn, encodeNat_zero] at h; cases h
    simp [natSyms, h, hn]

theorem length_encodeNat_le_self (n : ℕ) : (encodeNat n).length ≤ n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
  · by_cases hq : q = 0
    · subst hq
      simp [encodeNat_zero]
    · have hne : encodeNat q ≠ [] := fun h => hq ((encodeNat_eq_nil_iff q).1 h)
      rw [two_mul, encodeNat_add, if_neg hne, List.length_cons]
      have := ih q (by omega)
      omega
  · rw [two_mul, encodeNat_add_add_one, List.length_cons]
    have := ih q (by omega)
    omega

/-! ## The fill loop -/

/-- From counter `j` on `C` (above `R`), the loop pushes `j` copies of `c` onto `D`. -/
theorem fill_loop {κ : Type} [DecidableEq κ] {D C T : κ} (hDC : D ≠ C) (hCT : C ≠ T)
    (c : Bool) (ρ : List (RProg κ)) (R : List Sym) (hR : TermOK R) (K : ℕ) :
    ∀ (j : ℕ) (r2 : Option Sym × Bool) (S : κ → List Sym), j ≤ K → S C = natSyms j ++ R →
      ∃ r' t, t ≤ j * (6 * K + 11) + 1 ∧
        Eval ρ (.loop bitA (.seq (pushK D (.bit c)) (.seq (decP C T) (peekA C))))
          ⟨((natSyms j ++ R).head?, r2), S⟩
          ⟨r', Function.update (Function.update S C R) D (List.replicate j (Sym.bit c) ++ S D)⟩ t
  | 0, r2, S, _, hS => by
    have hc : bitA (((natSyms 0 ++ R).head?, r2) : Reg) = false := by
      show optIsBit (natSyms 0 ++ R).head? = false
      rw [optIsBit_head_natSyms' 0 hR]
      rfl
    refine ⟨((natSyms 0 ++ R).head?, r2), 1, by omega, (Eval.loop_false hc).of_eq ?_ rfl⟩
    have hS' : S C = R := by rw [hS, natSyms_zero', List.nil_append]
    congr 1
    rw [List.replicate_zero, List.nil_append, ← hS', Function.update_eq_self,
      Function.update_eq_self]
  | j + 1, r2, S, hj, hS => by
    have hc : bitA (((natSyms (j + 1) ++ R).head?, r2) : Reg) = true := by
      show optIsBit (natSyms (j + 1) ++ R).head? = true
      rw [optIsBit_head_natSyms' (j + 1) hR]
      simp
    have e1 := eval_pushK ρ D (.bit c) ((natSyms (j + 1) ++ R).head?, r2) S
    have hSC : Function.update S D (Sym.bit c :: S D) C = natSyms (j + 1) ++ R := by
      rw [Function.update_of_ne (Ne.symm hDC)]
      exact hS
    have e2 := decP_eval hCT ρ ((natSyms (j + 1) ++ R).head?, r2) j R
      (Function.update S D (Sym.bit c :: S D)) hR hSC
    have e3 := eval_peekA ρ C (some Sym.mark, r2)
      (Function.update (Function.update S D (Sym.bit c :: S D)) C (natSyms j ++ R))
    rw [Function.update_self] at e3
    obtain ⟨r', t, ht, e4⟩ := fill_loop hDC hCT c ρ R hR K j r2
      (Function.update (Function.update S D (Sym.bit c :: S D)) C (natSyms j ++ R)) (by omega)
      (Function.update_self _ _ _)
    have hz : zerosLead (encodeNat (j + 1)) ≤ K :=
      le_trans (zerosLead_le_length _) (le_trans (length_encodeNat_le_self _) hj)
    refine ⟨r', _, ?_, (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq ?_ rfl⟩
    · have e : (j + 1) * (6 * K + 11) = j * (6 * K + 11) + (6 * K + 11) := by ring
      omega
    · congr 1
      have hD : Function.update (Function.update S D (Sym.bit c :: S D)) C (natSyms j ++ R) D =
          Sym.bit c :: S D := by
        rw [Function.update_of_ne hDC, Function.update_self]
      have hrep : List.replicate j (Sym.bit c) ++ (Sym.bit c :: S D) =
          List.replicate (j + 1) (Sym.bit c) ++ S D := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [hD, hrep, Function.update_idem, Function.update_comm hDC, Function.update_idem]

end Fill

/-! ## The passes -/

theorem copyP_closed {κ : Type} (src dst tmp : κ) : (copyP src dst tmp).Closed :=
  freeBelow_liftRegs' _ _ 0 (copyBlock_closed' src dst tmp)

theorem fillP_closed {κ : Type} (c : Bool) (Kc D C T : κ) : (fillP c Kc D C T).Closed :=
  ⟨trivial, copyP_closed Kc C T, trivial, ⟨trivial, decP_closed C T, trivial⟩, trivial⟩

theorem copyP_eval {κ : Type} [DecidableEq κ] {src dst tmp : κ} (h1 : src ≠ dst)
    (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (ρ : List (RProg κ)) (r : Reg) (l : List Bool)
    (rest : List Sym) (S : κ → List Sym) (hrest : TermOK rest) (hS : S src = l.map Sym.bit ++ rest) :
    ∃ r' t, t ≤ 8 * l.length + 8 ∧
      Eval ρ (copyP src dst tmp) ⟨r, S⟩ ⟨r', Function.update S dst (l.map Sym.bit ++ S dst)⟩ t :=
  ⟨_, _, by omega, liftA_eval (copyBlock_closed' src dst tmp)
    (Lib.copyBlock_eval h1 h2 h3 [] r.1 l rest S hrest hS) ρ r.2⟩

theorem fillP_eval {κ : Type} [DecidableEq κ] {Kc D C T : κ} (hKD : Kc ≠ D) (hKC : Kc ≠ C)
    (hKT : Kc ≠ T) (hDC : D ≠ C) (hDT : D ≠ T) (hCT : C ≠ T) (c : Bool) (ρ : List (RProg κ))
    (r : Reg) (k : ℕ) (rk : List Sym) (S : κ → List Sym) (hrk : TermOK rk)
    (hK : S Kc = natSyms k ++ rk) :
    ∃ r' t, t ≤ 30 * (k + 1) * (k + 1) ∧
      Eval ρ (fillP c Kc D C T) ⟨r, S⟩
        ⟨r', Function.update S D (List.replicate k (Sym.bit c) ++ S D)⟩ t := by
  have e1 := eval_pushK ρ C .mark r S
  obtain ⟨r2, t2, ht2, e2⟩ := copyP_eval hKC hKT hCT ρ r (encodeNat k) rk
    (Function.update S C (.mark :: S C)) hrk (by rw [Function.update_of_ne hKC]; exact hK)
  have hC2 : Function.update (Function.update S C (.mark :: S C)) C
      ((encodeNat k).map Sym.bit ++ Function.update S C (.mark :: S C) C) C =
      natSyms k ++ (.mark :: S C) := by
    rw [Function.update_self, Function.update_self]
    rfl
  have e3 := eval_peekA ρ C r2 (Function.update (Function.update S C (.mark :: S C)) C
    ((encodeNat k).map Sym.bit ++ Function.update S C (.mark :: S C) C))
  rw [hC2] at e3
  obtain ⟨r4, t4, ht4, e4⟩ := fill_loop hDC hCT c ρ (.mark :: S C) (TermOK.cons rfl _) k k r2.2
    (Function.update (Function.update S C (.mark :: S C)) C
      ((encodeNat k).map Sym.bit ++ Function.update S C (.mark :: S C) C)) le_rfl hC2
  have e5 := eval_dropT ρ C r4 (Function.update (Function.update
      (Function.update (Function.update S C (.mark :: S C)) C
        ((encodeNat k).map Sym.bit ++ Function.update S C (.mark :: S C) C)) C (.mark :: S C)) D
      (List.replicate k (Sym.bit c) ++ Function.update (Function.update S C (.mark :: S C)) C
        ((encodeNat k).map Sym.bit ++ Function.update S C (.mark :: S C) C) D))
    .mark (S C) (by rw [Function.update_of_ne (Ne.symm hDC), Function.update_self])
  refine ⟨r4, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ rfl⟩
  · have hl : (encodeNat k).length ≤ k := length_encodeNat_le_self k
    have e : 30 * (k + 1) * (k + 1) = 30 * (k * k) + 60 * k + 30 := by ring
    have e' : k * (6 * k + 11) = 6 * (k * k) + 11 * k := by ring
    omega
  · congr 1
    have hZ : Function.update (Function.update S C (.mark :: S C)) C
        ((encodeNat k).map Sym.bit ++ Function.update S C (.mark :: S C) C) D = S D := by
      rw [Function.update_of_ne hDC, Function.update_of_ne hDC]
    rw [hZ, Function.update_comm hDC, Function.update_idem, Function.update_idem,
      Function.update_idem, Function.update_eq_self]

#assert_std_axioms Fill.freeBelow_liftRegs' Fill.copyBlock_closed' Fill.dec_closed'
  Fill.decP_closed Fill.liftA_eval Fill.decP_eval Fill.natSyms_zero' Fill.optIsBit_head_natSyms'
  Fill.length_encodeNat_le_self Fill.fill_loop copyP_closed fillP_closed

#assert_std_axioms copyP_eval fillP_eval

end TMFw.W4o
