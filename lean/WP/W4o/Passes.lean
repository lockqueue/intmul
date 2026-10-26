import WP.W4o.Movers

/-!
# WP.W4o.Passes — dealing and interleaving passes of the router

* `dein_eval`: a `.down` block of an even number of records on `X` is dealt alternately onto `P`
  (even positions) and `Q` (odd positions); both receive `.up` blocks:
  `P += (sel false l).flatten.reverse`, `Q += (sel true l).flatten.reverse`.
* `interL_eval`: two `.up` blocks (top-to-bottom record lists `L1`, `L2` of equal length) are
  interleaved onto `Y` in `.down` order: `Y += (inter L1 L2).reverse.flatten`.
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts

section Proofs

variable {K : Type} [DecidableEq K]

theorem dein_loop {X P Q : K} (hXP : X ≠ P) (hXQ : X ≠ Q) (hPQ : P ≠ Q) (ρ : List (RProg K))
    (r2 : Option Sym × Bool) (R : List Sym) (hR : isRecO R.head? = false) :
    ∀ (n : ℕ) (l : List (List Sym)) (S : K → List Sym), l.length = 2 * n → (∀ r ∈ l, RecOK r) →
      S X = l.flatten ++ R →
      Eval ρ (.loop recA (deinBody X P Q)) ⟨((l.flatten ++ R).head?, r2), S⟩
        ⟨(R.head?, r2), Function.update (Function.update (Function.update S X R) P
          ((sel false l).flatten.reverse ++ S P)) Q ((sel true l).flatten.reverse ++ S Q)⟩
        (3 * l.flatten.length + l.length + 1)
  | 0, l, S, hl, _, hS => by
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hl0
    refine (Eval.loop_false hR).of_eq ?_ rfl
    have hS' : S X = R := hS
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [sel]
  | n + 1, l, S, hl, hrec, hS => by
    rcases l with _ | ⟨r1, _ | ⟨q1, l'⟩⟩
    · simp only [List.length_nil] at hl
      omega
    · simp only [List.length_cons, List.length_nil] at hl
      omega
    · have hl' : l'.length = 2 * n := by simp at hl; omega
      have hr1 : RecOK r1 := hrec r1 (by simp)
      have hq1 : RecOK q1 := hrec q1 (by simp)
      have hrec' : ∀ r ∈ l', RecOK r := fun r hr => hrec r (by simp [hr])
      have hS1 : S X = r1 ++ (q1 ++ (l'.flatten ++ R)) := by rw [hS]; simp
      have e1 := moveRecD_rec hXP ρ (((r1 :: q1 :: l').flatten ++ R).head?, r2) r1 _ S hr1 hS1
      set S1 := Function.update (Function.update S X (q1 ++ (l'.flatten ++ R))) P
        (r1.reverse ++ S P) with hS1def
      have hS1X : S1 X = q1 ++ (l'.flatten ++ R) := by
        rw [hS1def, Function.update_of_ne hXP, Function.update_self]
      have e2 := moveRecD_rec hXQ ρ (some Sym.sep, r2) q1 _ S1 hq1 hS1X
      set S2 := Function.update (Function.update S1 X (l'.flatten ++ R)) Q
        (q1.reverse ++ S1 Q) with hS2def
      have hS2X : S2 X = l'.flatten ++ R := by
        rw [hS2def, Function.update_of_ne hXQ, Function.update_self]
      have e3 := eval_peekA ρ X (some Sym.sep, r2) S2
      rw [hS2X] at e3
      have ih := dein_loop hXP hXQ hPQ ρ r2 R hR n l' S2 hl' hrec' hS2X
      have hc : recA (((r1 :: q1 :: l').flatten ++ R).head?, r2) = true := by
        show isRecO _ = true
        rw [show (r1 :: q1 :: l').flatten ++ R = r1 ++ (q1 ++ (l'.flatten ++ R)) by simp]
        exact isRecO_recOK hr1 _
      refine (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_ ?_
      · have hS2P : S2 P = r1.reverse ++ S P := by
          rw [hS2def, Function.update_of_ne hPQ, Function.update_of_ne (Ne.symm hXP), hS1def,
            Function.update_self]
        have hS2Q : S2 Q = q1.reverse ++ S Q := by
          rw [hS2def, Function.update_self, hS1def, Function.update_of_ne (Ne.symm hPQ),
            Function.update_of_ne (Ne.symm hXQ)]
        have hS2o : ∀ k, k ≠ X → k ≠ P → k ≠ Q → S2 k = S k := by
          intro k h1 h2 h3
          rw [hS2def, Function.update_of_ne h3, Function.update_of_ne h1, hS1def,
            Function.update_of_ne h2, Function.update_of_ne h1]
        rw [hS2P, hS2Q, upd3_congr hS2o]
        simp only [sel, List.flatten_cons, List.reverse_append, List.append_assoc]
      · simp only [List.flatten_cons, List.length_append, List.length_cons]
        omega

/-- **dein**: deal a `.down` block alternately onto `P` and `Q`. -/
theorem dein_eval {X P Q : K} (hXP : X ≠ P) (hXQ : X ≠ Q) (hPQ : P ≠ Q) (ρ : List (RProg K))
    (r : Reg) (R : List Sym) (hR : isRecO R.head? = false) (n : ℕ) (l : List (List Sym))
    (S : K → List Sym) (hl : l.length = 2 * n) (hrec : ∀ r ∈ l, RecOK r)
    (hS : S X = l.flatten ++ R) :
    Eval ρ (dein X P Q) ⟨r, S⟩
      ⟨(R.head?, r.2), Function.update (Function.update (Function.update S X R) P
        ((sel false l).flatten.reverse ++ S P)) Q ((sel true l).flatten.reverse ++ S Q)⟩
      (3 * l.flatten.length + l.length + 2) := by
  have h1 := eval_peekA ρ X r S
  rw [hS] at h1
  exact (Eval.seq h1 (dein_loop hXP hXQ hPQ ρ r.2 R hR n l S hl hrec hS)).of_eq rfl (by omega)

theorem inter_loop {P Q Y : K} (hPQ : P ≠ Q) (hPY : P ≠ Y) (hQY : Q ≠ Y) (ρ : List (RProg K))
    (r2 : Option Sym × Bool) (RP RQ : List Sym) (hRP : isRecO RP.head? = false)
    (hRQ : isDataR RQ.head? = false) :
    ∀ (L1 L2 : List (List Sym)) (S : K → List Sym), L1.length = L2.length →
      (∀ r ∈ L1, RecOK r) → (∀ r ∈ L2, RecOK r) →
      S P = (L1.map List.reverse).flatten ++ RP → S Q = (L2.map List.reverse).flatten ++ RQ →
      Eval ρ (.loop recA (interBody P Q Y))
        ⟨(((L1.map List.reverse).flatten ++ RP).head?, r2), S⟩
        ⟨(RP.head?, r2), Function.update (Function.update (Function.update S P RP) Q RQ) Y
          ((inter L1 L2).reverse.flatten ++ S Y)⟩
        (4 * (L1.flatten.length + L2.flatten.length) + 2 * L1.length + 1)
  | [], [], S, _, _, _, hP, hQ => by
    refine (Eval.loop_false hRP).of_eq ?_ rfl
    have hP' : S P = RP := hP
    have hQ' : S Q = RQ := hQ
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [inter]
  | [], _ :: _, _, h, _, _, _, _ => by simp at h
  | _ :: _, [], _, h, _, _, _, _ => by simp at h
  | a :: L1, b :: L2, S, hlen, h1, h2, hP, hQ => by
    have ha : RecOK a := h1 a (by simp)
    have hb : RecOK b := h2 b (by simp)
    have h1' : ∀ r ∈ L1, RecOK r := fun r hr => h1 r (by simp [hr])
    have h2' : ∀ r ∈ L2, RecOK r := fun r hr => h2 r (by simp [hr])
    have hlen' : L1.length = L2.length := by simpa using hlen
    have hRP' : isDataR RP.head? = false := isDataR_false_of_isRecO hRP
    have hP1 : S P = a.reverse ++ ((L1.map List.reverse).flatten ++ RP) := by rw [hP]; simp
    have e1 := moveRecU_rec hPY ρ ((((a :: L1).map List.reverse).flatten ++ RP).head?, r2) a _
      S ha (notData_after L1 h1' RP hRP') hP1
    set S1 := Function.update (Function.update S P ((L1.map List.reverse).flatten ++ RP)) Y
      (a ++ S Y) with hS1def
    have hS1Q : S1 Q = b.reverse ++ ((L2.map List.reverse).flatten ++ RQ) := by
      rw [hS1def, Function.update_of_ne hQY, Function.update_of_ne (Ne.symm hPQ), hQ]
      simp
    have e2 := moveRecU_rec hQY ρ (((L1.map List.reverse).flatten ++ RP).head?, r2) b _ S1 hb
      (notData_after L2 h2' RQ hRQ) hS1Q
    set S2 := Function.update (Function.update S1 Q ((L2.map List.reverse).flatten ++ RQ)) Y
      (b ++ S1 Y) with hS2def
    have hS2P : S2 P = (L1.map List.reverse).flatten ++ RP := by
      rw [hS2def, Function.update_of_ne hPY, Function.update_of_ne hPQ, hS1def,
        Function.update_of_ne hPY, Function.update_self]
    have hS2Q : S2 Q = (L2.map List.reverse).flatten ++ RQ := by
      rw [hS2def, Function.update_of_ne hQY, Function.update_self]
    have e3 := eval_peekA ρ P (((L2.map List.reverse).flatten ++ RQ).head?, r2) S2
    rw [hS2P] at e3
    have ih := inter_loop hPQ hPY hQY ρ r2 RP RQ hRP hRQ L1 L2 S2 hlen' h1' h2' hS2P hS2Q
    have hc : recA ((((a :: L1).map List.reverse).flatten ++ RP).head?, r2) = true := by
      show isRecO _ = true
      rw [show ((a :: L1).map List.reverse).flatten ++ RP =
        a.reverse ++ ((L1.map List.reverse).flatten ++ RP) by simp]
      obtain ⟨d, rfl, _⟩ := ha
      simp [List.reverse_append, isRecO, isRecSym]
    refine (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_ ?_
    · have hS2Y : S2 Y = b ++ (a ++ S Y) := by
        rw [hS2def, Function.update_self, hS1def, Function.update_self]
      have hS2o : ∀ k, k ≠ P → k ≠ Q → k ≠ Y → S2 k = S k := by
        intro k k1 k2 k3
        rw [hS2def, Function.update_of_ne k3, Function.update_of_ne k2, hS1def,
          Function.update_of_ne k3, Function.update_of_ne k1]
      rw [hS2Y, upd3_congr hS2o]
      simp only [inter, List.reverse_cons, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_assoc, List.append_nil]
    · simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

/-- **interL**: interleave two `.up` blocks onto `Y`. -/
theorem interL_eval {P Q Y : K} (hPQ : P ≠ Q) (hPY : P ≠ Y) (hQY : Q ≠ Y) (ρ : List (RProg K))
    (r : Reg) (RP RQ : List Sym) (hRP : isRecO RP.head? = false)
    (hRQ : isDataR RQ.head? = false) (L1 L2 : List (List Sym)) (S : K → List Sym)
    (hlen : L1.length = L2.length) (h1 : ∀ r ∈ L1, RecOK r) (h2 : ∀ r ∈ L2, RecOK r)
    (hP : S P = (L1.map List.reverse).flatten ++ RP)
    (hQ : S Q = (L2.map List.reverse).flatten ++ RQ) :
    Eval ρ (interL P Q Y) ⟨r, S⟩
      ⟨(RP.head?, r.2), Function.update (Function.update (Function.update S P RP) Q RQ) Y
        ((inter L1 L2).reverse.flatten ++ S Y)⟩
      (4 * (L1.flatten.length + L2.flatten.length) + 2 * L1.length + 2) := by
  have h0 := eval_peekA ρ P r S
  rw [hP] at h0
  exact (Eval.seq h0 (inter_loop hPQ hPY hQY ρ r.2 RP RQ hRP hRQ L1 L2 S hlen h1 h2 hP hQ)).of_eq
    rfl (by omega)

end Proofs

#assert_std_axioms dein_loop dein_eval inter_loop interL_eval

end TMFw.W4o
