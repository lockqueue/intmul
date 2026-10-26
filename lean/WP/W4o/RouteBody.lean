import WP.W4o.AddTProg
import WP.W4o.Passes
import WP.W4o.RouteState
import WP.W4o.RouteMath

/-!
# WP.W4o.RouteBody — the router's procedure body and its phases

`route = fix body`. With the offset block `B` (LSB on top of `sBs`, above a `mark`):
* `B = []` (one record): `base` moves it from `sX` to `sY` (twice, keeping `.down` order);
* `B = β :: B'`: `node β` =
  `phase1` (deal the block onto `sA` / `sB`, `sA` receiving the positions `≡ β`; drop `β`; move
  `sA` back to `sX`) ; `recur` (even outputs, block `B'`) ; `phase2` (restore `β`, add `w` in
  place, drop the low bit, move `sB` to `sX`) ; `recur` (odd outputs, block `(B + w).tail`) ;
  `phase3` (restore and subtract `w`, giving `B` back) ; `phase4` (separate the two outputs onto
  `sA` / `sB`, interleave them onto `sY`).
Each phase is proved here on explicit `st9` records; `WP.W4o.RouteRec` does the recursion.
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Deal so that `sA` receives the positions `≡ β (mod 2)`. -/
def deinB (β : Bool) : RProg L54 := if β then dein sX sB sA else dein sX sA sB

/-- Phase 1 of a node. -/
def phase1 (β : Bool) : RProg L54 :=
  .seq (pushK sA .mark) (.seq (pushK sB .mark) (.seq (deinB β) (.seq (dropT sBs)
    (.seq (moveAll sA sX) (.seq (dropT sA) (pushK sY .mark))))))

/-- Phase 2 of a node. -/
def phase2 (β : Bool) : RProg L54 :=
  .seq (pushK sBs (.bit β)) (.seq (addTP false sBs sW sT sV) (.seq (dropT sBs)
    (.seq (moveAll sB sX) (.seq (dropT sB) (pushK sY .mark)))))

/-- Phase 3 of a node. -/
def phase3 (β : Bool) : RProg L54 := .seq (pushK sBs (.bit (!β))) (addTP true sBs sW sT sV)

/-- Phase 4 of a node: separate the two outputs and interleave them. -/
def phase4 : RProg L54 :=
  .seq (pushK sA .mark) (.seq (moveAll sY sA) (.seq (dropT sY)
    (.seq (pushK sB .mark) (.seq (moveAll sY sB) (.seq (dropT sY)
    (.seq (interL sA sB sY) (.seq (dropT sA) (dropT sB))))))))

/-- A recursion node with offset LSB `β`. -/
def node (β : Bool) : RProg L54 :=
  .seq (phase1 β) (.seq (.recur 0) (.seq (phase2 β) (.seq (.recur 0) (.seq (phase3 β) phase4))))

/-- Base case: one record. -/
def base : RProg L54 :=
  .seq (pushK sA .mark) (.seq (moveAll sX sA) (.seq (moveAll sA sY) (dropT sA)))

/-- The procedure body. -/
def body : RProg L54 :=
  .seq (peekA sBs) (.ite bitA (.ite (fun r => optBit r.1) (node true) (node false)) base)

/-- The router procedure. -/
def route : RProg L54 := .fix body

theorem recSyms_of_recOK {r : List Sym} (h : RecOK r) : ∀ x ∈ r, isRecSym x = true := by
  obtain ⟨d, rfl, hd⟩ := h
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact isRecSym_of_data (hd x hx)
  · rw [List.mem_singleton] at hx
    subst hx
    rfl

theorem recSyms_flatten {L : List (List Sym)} (h : ∀ r ∈ L, RecOK r) :
    ∀ x ∈ L.flatten, isRecSym x = true := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hx
  exact recSyms_of_recOK (h r hr) x hxr

theorem recSyms_rev {l : List Sym} (h : ∀ x ∈ l, isRecSym x = true) :
    ∀ x ∈ l.reverse, isRecSym x = true := fun x hx => h x (List.mem_reverse.mp hx)

theorem flatten_reverse_eq (L : List (List Sym)) :
    L.flatten.reverse = (L.reverse.map List.reverse).flatten := by
  induction L with
  | nil => rfl
  | cons r L ih => simp [ih]

theorem deinB_eval (β : Bool) (ρ : List (RProg L54)) (r : Reg) (v : List (List Sym)) (m : ℕ)
    (hv : v.length = 2 * m) (hrec : ∀ x ∈ v, RecOK x) (rest : List Sym)
    (hrest : isRecO rest.head? = false) (y k w bs a b t u : List Sym) :
    Eval ρ (deinB β) ⟨r, st9 (v.flatten ++ rest) y k w bs a b t u⟩
      ⟨(rest.head?, r.2), st9 rest y k w bs ((sel β v).flatten.reverse ++ a)
        ((sel (!β) v).flatten.reverse ++ b) t u⟩ (3 * v.flatten.length + v.length + 2) := by
  cases β with
  | false =>
    have h := dein_eval (X := sX) (P := sA) (Q := sB) (by decide) (by decide) (by decide) ρ r
      rest hrest m v (st9 (v.flatten ++ rest) y k w bs a b t u) hv hrec rfl
    simp only [upd_X, upd_A, upd_B, st9_A, st9_B] at h
    exact h
  | true =>
    have h := dein_eval (X := sX) (P := sB) (Q := sA) (by decide) (by decide) (by decide) ρ r
      rest hrest m v (st9 (v.flatten ++ rest) y k w bs a b t u) hv hrec rfl
    simp only [upd_X, upd_A, upd_B, st9_A, st9_B] at h
    exact h

/-- **Phase 1.** -/
theorem phase1_eval (β : Bool) (ρ : List (RProg L54)) (r : Reg) (B' : List Bool)
    (v : List (List Sym)) (m : ℕ) (hv : v.length = 2 * m) (hrec : ∀ x ∈ v, RecOK x)
    (rest : List Sym) (hrest : isRecO rest.head? = false) (y k w Rb a b t u : List Sym) :
    ∃ r' tm, tm ≤ 3 * v.flatten.length + v.length + 4 * (sel β v).flatten.length + 9 ∧
      Eval ρ (phase1 β)
        ⟨r, st9 (v.flatten ++ rest) y k w ((β :: B').map Sym.bit ++ Sym.mark :: Rb) a b t u⟩
        ⟨r', st9 ((sel β v).flatten ++ rest) (Sym.mark :: y) k w
          (B'.map Sym.bit ++ Sym.mark :: Rb) a ((sel (!β) v).flatten.reverse ++ Sym.mark :: b)
          t u⟩ tm := by
  have hsel : ∀ x ∈ sel β v, RecOK x := fun x hx => hrec x (mem_sel β v x hx)
  have e1 := eval_pushK ρ sA Sym.mark r
    (st9 (v.flatten ++ rest) y k w ((β :: B').map Sym.bit ++ Sym.mark :: Rb) a b t u)
  simp only [upd_A, st9_A] at e1
  have e2 := eval_pushK ρ sB Sym.mark r
    (st9 (v.flatten ++ rest) y k w ((β :: B').map Sym.bit ++ Sym.mark :: Rb) (Sym.mark :: a) b
      t u)
  simp only [upd_B, st9_B] at e2
  have e3 := deinB_eval β ρ r v m hv hrec rest hrest y k w
    ((β :: B').map Sym.bit ++ Sym.mark :: Rb) (Sym.mark :: a) (Sym.mark :: b) t u
  have e4 := eval_dropT ρ sBs (rest.head?, r.2) (st9 rest y k w
    ((β :: B').map Sym.bit ++ Sym.mark :: Rb) ((sel β v).flatten.reverse ++ Sym.mark :: a)
    ((sel (!β) v).flatten.reverse ++ Sym.mark :: b) t u) (Sym.bit β)
    (B'.map Sym.bit ++ Sym.mark :: Rb) rfl
  simp only [upd_Bs] at e4
  have e5 := moveAll_eval (src := sA) (dst := sX) (by decide) ρ (rest.head?, r.2)
    (sel β v).flatten.reverse (Sym.mark :: a) (st9 rest y k w (B'.map Sym.bit ++ Sym.mark :: Rb)
      ((sel β v).flatten.reverse ++ Sym.mark :: a) ((sel (!β) v).flatten.reverse ++
        Sym.mark :: b) t u) (recSyms_rev (recSyms_flatten hsel)) rfl rfl
  simp only [upd_A, upd_X, st9_X, List.reverse_reverse] at e5
  have e6 := eval_dropT ρ sA (some Sym.mark, (rest.head?, r.2).2) (st9 ((sel β v).flatten ++ rest)
    y k w (B'.map Sym.bit ++ Sym.mark :: Rb) (Sym.mark :: a)
    ((sel (!β) v).flatten.reverse ++ Sym.mark :: b) t u) Sym.mark a rfl
  simp only [upd_A] at e6
  have e7 := eval_pushK ρ sY Sym.mark (some Sym.mark, (rest.head?, r.2).2)
    (st9 ((sel β v).flatten ++ rest) y k w (B'.map Sym.bit ++ Sym.mark :: Rb) a
      ((sel (!β) v).flatten.reverse ++ Sym.mark :: b) t u)
  simp only [upd_Y, st9_Y] at e7
  refine ⟨_, _, ?_, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 e7)))))⟩
  simp only [List.length_reverse]
  omega

/-- **Base case**: one record. -/
theorem base_eval (ρ : List (RProg L54)) (r : Reg) (r0 : List Sym) (hr0 : RecOK r0)
    (rest : List Sym) (hrest : isRecO rest.head? = false) (y k w bs a b t u : List Sym) :
    ∃ r', Eval ρ base ⟨r, st9 (r0 ++ rest) y k w bs a b t u⟩
      ⟨r', st9 rest (r0 ++ y) k w bs a b t u⟩ (8 * r0.length + 6) := by
  have e1 := eval_pushK ρ sA Sym.mark r (st9 (r0 ++ rest) y k w bs a b t u)
  simp only [upd_A, st9_A] at e1
  have e2 := moveAll_eval (src := sX) (dst := sA) (by decide) ρ r r0 rest
    (st9 (r0 ++ rest) y k w bs (Sym.mark :: a) b t u) (recSyms_of_recOK hr0) hrest rfl
  simp only [upd_A, upd_X, st9_A] at e2
  have e3 := moveAll_eval (src := sA) (dst := sY) (by decide) ρ (rest.head?, r.2) r0.reverse
    (Sym.mark :: a) (st9 rest y k w bs (r0.reverse ++ Sym.mark :: a) b t u)
    (recSyms_rev (recSyms_of_recOK hr0)) rfl rfl
  simp only [upd_A, upd_Y, st9_Y, List.reverse_reverse] at e3
  have e4 := eval_dropT ρ sA (some Sym.mark, (rest.head?, r.2).2)
    (st9 rest (r0 ++ y) k w bs (Sym.mark :: a) b t u) Sym.mark a rfl
  simp only [upd_A] at e4
  refine ⟨_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq rfl ?_⟩
  simp only [List.length_reverse]
  omega

#assert_std_axioms recSyms_of_recOK recSyms_flatten flatten_reverse_eq deinB_eval phase1_eval
  base_eval

end TMFw.W4o
