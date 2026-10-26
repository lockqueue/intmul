import WP.W5.School

/-!
# WP.W5.Spec — the procedure's specification and the recursive-call step

* `G`, `Pre`, `Post`, `μ`: ghost variables (operands and full stacks), pre/postcondition of the
  procedure `fix (bodyP U)`, and the recursion measure (the larger operand bit length).
* `call_step`: a `recur 0` whose operands sit on top of `X`, `Y` (with `TermOK` rests) pushes their
  product on `Z`, by the recursion hypothesis, at cost `F K + 2` when both operands have bit length
  `≤ K < μ g`.
* `mk11`, `tE`: clean abstract states of the Toom-3 step (parts of `|a|`, `|b|` on the scratch
  stacks, a point value on `X`, `Y`, the products so far on `Z`).
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-- Ghost variables of one call: the operands and the full stacks. -/
structure G where
  /-- first operand -/
  a : ℤ
  /-- second operand -/
  b : ℤ
  /-- all stacks at entry -/
  S : L → List Sym

/-- Precondition: the operands on top of `X`, `Y` with `TermOK` rests; everything else arbitrary. -/
def Pre {σ : Type} (g : G) (s : St L (fun _ => Sym) σ) : Prop :=
  s.stk = g.S ∧ (∃ ra, TermOK ra ∧ g.S X = intSyms g.a ++ ra) ∧
    (∃ rb, TermOK rb ∧ g.S Y = intSyms g.b ++ rb)

/-- Postcondition: the product pushed on `Z`, all other stacks restored. -/
def Post {σ : Type} (g : G) (s : St L (fun _ => Sym) σ) : Prop :=
  s.stk = Function.update g.S Z (intSyms (g.a * g.b) ++ g.S Z)

/-- Recursion measure: the larger operand bit length. -/
def μ (g : G) : ℕ := max (bitLen g.a.natAbs) (bitLen g.b.natAbs)

section Call

variable {U : Subs} {B : L → List Sym} (hB : ∀ k, bokXY k = true → TermOK (B k))

include hB in
/-- **The recursive call**, on the abstract state. -/
theorem call_step (F : ℕ → ℕ) (hF : Monotone F) (g : G)
    (IH : ∀ g' : G, μ g' < μ g → Triple [bodyP U] (Pre g') (.recur 0) (Post g') (F (μ g') + 2))
    (E : L → List Ent) (m : ℕ) (hA : AllLe E m) (p q : ℤ) (ex ey : List Ent)
    (hx : E X = .I p :: ex) (hy : E Y = .I q :: ey) (htx : tok (bokXY X) ex = true)
    (hty : tok (bokXY Y) ey = true) (K : ℕ) (hp : bitLen p.natAbs ≤ K) (hq : bitLen q.natAbs ≤ K)
    (hK : K < μ g) :
    Triple [bodyP U] (fun s => s.stk = stOf E B) (.recur 0)
      (fun s => s.stk = stOf (Function.update E Z (.I (p * q) :: E Z)) B) (F K + 2) ∧
    AllLe (Function.update E Z (.I (p * q) :: E Z)) (m + 2 * K) := by
  have hμ : μ ⟨p, q, stOf E B⟩ ≤ K := max_le hp hq
  have hFK := hF hμ
  refine ⟨(IH ⟨p, q, stOf E B⟩ (lt_of_le_of_lt hμ hK)).conseq (fun s hs => ?_) (fun s hs => ?_)
    (by omega), ?_⟩
  · exact ⟨hs, ⟨encL ex ++ B X, tok_sound (hB X) htx, stOf_head E B hx⟩,
      ⟨encL ey ++ B Y, tok_sound (hB Y) hty, stOf_head E B hy⟩⟩
  · show s.stk = _
    rw [hs, stOf_push]
    rfl
  · refine allLe_push hA (by omega) Z (.I (p * q)) ?_
    show bitLen (p * q).natAbs ≤ m + 2 * K
    have := bitLen_natAbs_mul_le p q
    omega

end Call

/-! ## Clean states of the Toom-3 step -/

/-- A stack table from 11 entry lists (`X Y Z s0 … s7`). -/
def mk11 (x y z t0 t1 t2 t3 t4 t5 t6 t7 : List Ent) : L → List Ent := fun k =>
  if k = X then x else if k = Y then y else if k = Z then z else if k = s0 then t0
  else if k = s1 then t1 else if k = s2 then t2 else if k = s3 then t3 else if k = s4 then t4
  else if k = s5 then t5 else if k = s6 then t6 else t7

/-- Toom-3 state: point values `px`, `qy` on `X`, `Y`; products `zs` on `Z`; the parts of `|a|` on
`s5, s6, s4`, of `|b|` on `s1, s2, s7`; the split position on `s0`. -/
def tE (a b : ℤ) (K : ℕ) (px qy : ℤ) (zs : List Ent) : L → List Ent :=
  mk11 [.I px, .I a] [.I qy, .I b] zs [.N K, .S] [.I (part0 b.natAbs K), .S]
    [.I (part1 b.natAbs K), .S] [.S] [.I (part2 a.natAbs K), .S] [.I (part0 a.natAbs K), .S]
    [.I (part1 a.natAbs K), .S] [.I (part2 b.natAbs K), .S]

theorem allLe_mk11 {m : ℕ} {x y z t0 t1 t2 t3 t4 t5 t6 t7 : List Ent}
    (hx : ∀ e ∈ x, e.len ≤ m) (hy : ∀ e ∈ y, e.len ≤ m) (hz : ∀ e ∈ z, e.len ≤ m)
    (h0 : ∀ e ∈ t0, e.len ≤ m) (h1 : ∀ e ∈ t1, e.len ≤ m) (h2 : ∀ e ∈ t2, e.len ≤ m)
    (h3 : ∀ e ∈ t3, e.len ≤ m) (h4 : ∀ e ∈ t4, e.len ≤ m) (h5 : ∀ e ∈ t5, e.len ≤ m)
    (h6 : ∀ e ∈ t6, e.len ≤ m) (h7 : ∀ e ∈ t7, e.len ≤ m) :
    AllLe (mk11 x y z t0 t1 t2 t3 t4 t5 t6 t7) m := by
  intro k e he
  cases k
  · exact hx e he
  · exact hy e he
  · exact hz e he
  · exact h0 e he
  · exact h1 e he
  · exact h2 e he
  · exact h3 e he
  · exact h4 e he
  · exact h5 e he
  · exact h6 e he
  · exact h7 e he

theorem allLe_one {m : ℕ} {e1 : Ent} (h1 : e1.len ≤ m) : ∀ e ∈ [e1], e.len ≤ m := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  exact h1

theorem allLe_two {m : ℕ} {e1 e2 : Ent} (h1 : e1.len ≤ m) (h2 : e2.len ≤ m) :
    ∀ e ∈ [e1, e2], e.len ≤ m := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact h1
  · exact h2

theorem allLe_tE (a b : ℤ) (K : ℕ) (px qy : ℤ) (zs : List Ent) (m : ℕ)
    (ha : bitLen a.natAbs ≤ m) (hb : bitLen b.natAbs ≤ m) (hK : bitLen K ≤ m)
    (hpx : bitLen px.natAbs ≤ m) (hqy : bitLen qy.natAbs ≤ m) (hzs : ∀ e ∈ zs, e.len ≤ m) :
    AllLe (tE a b K px qy zs) m := by
  have hpa : ∀ A : ℕ, bitLen A ≤ m → bitLen (part0 A K).natAbs ≤ m ∧
      bitLen (part1 A K).natAbs ≤ m ∧ bitLen (part2 A K).natAbs ≤ m := by
    intro A hA
    simp only [part0, part1, part2, Int.natAbs_natCast]
    exact ⟨le_trans (bitLen_mod_le _ _) hA, le_trans (bitLen_mod_le _ _)
      (le_trans (bitLen_div_le _ _) hA), le_trans (bitLen_div_le _ _)
      (le_trans (bitLen_div_le _ _) hA)⟩
  obtain ⟨ha0, ha1, ha2⟩ := hpa _ ha
  obtain ⟨hb0, hb1, hb2⟩ := hpa _ hb
  have z0 : Ent.S.len ≤ m := Nat.zero_le _
  exact allLe_mk11 (allLe_two (e1 := .I px) (e2 := .I a) hpx ha)
    (allLe_two (e1 := .I qy) (e2 := .I b) hqy hb) hzs
    (allLe_two (e1 := .N K) (e2 := .S) hK z0)
    (allLe_two (e1 := .I (part0 b.natAbs K)) (e2 := .S) hb0 z0)
    (allLe_two (e1 := .I (part1 b.natAbs K)) (e2 := .S) hb1 z0)
    (allLe_one (e1 := .S) z0)
    (allLe_two (e1 := .I (part2 a.natAbs K)) (e2 := .S) ha2 z0)
    (allLe_two (e1 := .I (part0 a.natAbs K)) (e2 := .S) ha0 z0)
    (allLe_two (e1 := .I (part1 a.natAbs K)) (e2 := .S) ha1 z0)
    (allLe_two (e1 := .I (part2 b.natAbs K)) (e2 := .S) hb2 z0)

#assert_std_axioms call_step allLe_tE

end WP.W5
