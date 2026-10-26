import WP.W4o.RoutePhases
import Mathlib.Tactic.Ring

/-!
# WP.W4o.RouteRec — the router's recursion

`body_spec`, by induction on the offset-block length `n`: from a `.down` block of `2^n` records
on `sX` (followed by a `BlkTerm` terminator) and the offset block `B` on `sBs`, the body pushes
`blk .down (rt (encodeNat w) n B v)` onto `sY`, consumes the block, and restores every other
stack, within `200·|blk|·(n+1)` steps. `route_spec` wraps it in the `fix`.
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem length_le_flatten {L : List (List Sym)} (h : ∀ r ∈ L, RecOK r) :
    L.length ≤ L.flatten.length := by
  induction L with
  | nil => simp
  | cons r L ih =>
    obtain ⟨d, rfl, _⟩ := h r (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons, List.flatten_cons, List.length_append, List.length_singleton]
    omega

theorem flatten_length_sel' (β : Bool) (v : List (List Sym)) :
    (sel β v).flatten.length + (sel (!β) v).flatten.length = v.flatten.length := by
  have := RouteMath.flatten_length_sel v
  cases β
  · exact this
  · show (sel true v).flatten.length + (sel false v).flatten.length = v.flatten.length
    omega

theorem lt_two_pow' : ∀ n : ℕ, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have := lt_two_pow' n
    rw [Nat.pow_succ]
    omega

/-- Cost arithmetic of a node. -/
theorem node_cost {N N0 N1 n X tE tO : ℕ} (hN : N0 + N1 = N) (hv : 2 ^ (n + 1) ≤ N)
    (hn : n + 1 < 2 ^ (n + 1)) (hE : tE ≤ 200 * N0 * (n + 1)) (hO : tO ≤ 200 * N1 * (n + 1))
    (hX : X ≤ 15 * N + 2 * 2 ^ (n + 1) + 30 * n + 100) :
    X + tE + tO ≤ 200 * N * (n + 1 + 1) := by
  have e1 : 200 * N * (n + 1 + 1) = 200 * (N0 * (n + 1)) + 200 * (N1 * (n + 1)) + 200 * N := by
    rw [← hN]
    ring
  have e2 : 200 * N0 * (n + 1) = 200 * (N0 * (n + 1)) := by ring
  have e3 : 200 * N1 * (n + 1) = 200 * (N1 * (n + 1)) := by ring
  rw [e1]
  rw [e2] at hE
  rw [e3] at hO
  generalize 2 ^ (n + 1) = M at *
  generalize N0 * (n + 1) = P0 at *
  generalize N1 * (n + 1) = P1 at *
  omega

/-- **A node**, given the recursion hypothesis for both children. -/
theorem node_spec (w : ℕ) (hw : w % 2 = 1) (r3 : List Sym) (hr3 : TermOK r3) (rest : List Sym)
    (hrest : BlkTerm rest) (n : ℕ)
    (ih : ∀ (B : List Bool) (v : List (List Sym)) (y k Rb a b t u : List Sym) (r : Reg),
      B.length = n → v.length = 2 ^ n → (∀ x ∈ v, RecOK x) →
      ∃ r' tm, tm ≤ 200 * v.flatten.length * (n + 1) ∧
        Eval [body] body
          ⟨r, st9 (v.flatten ++ rest) y k (natSyms w ++ r3) (B.map Sym.bit ++ Sym.mark :: Rb) a b
            t u⟩
          ⟨r', st9 rest ((rt (encodeNat w) n B v).flatten ++ y) k (natSyms w ++ r3)
            (B.map Sym.bit ++ Sym.mark :: Rb) a b t u⟩ tm)
    (β : Bool) (B' : List Bool) (v : List (List Sym)) (y k Rb a b t u : List Sym) (r : Reg)
    (hB : B'.length = n) (hv : v.length = 2 ^ (n + 1)) (hrec : ∀ x ∈ v, RecOK x) :
    ∃ r' tm, tm + 3 ≤ 200 * v.flatten.length * (n + 1 + 1) ∧
      Eval [body] (node β)
        ⟨r, st9 (v.flatten ++ rest) y k (natSyms w ++ r3)
          ((β :: B').map Sym.bit ++ Sym.mark :: Rb) a b t u⟩
        ⟨r', st9 rest ((rt (encodeNat w) (n + 1) (β :: B') v).flatten ++ y) k (natSyms w ++ r3)
          ((β :: B').map Sym.bit ++ Sym.mark :: Rb) a b t u⟩ tm := by
  have hrest' : isRecO rest.head? = false := isRecO_head?_of_blkTerm hrest
  have hv0r : ∀ x ∈ sel β v, RecOK x := fun x hx => hrec x (mem_sel β v x hx)
  have hv1r : ∀ x ∈ sel (!β) v, RecOK x := fun x hx => hrec x (mem_sel (!β) v x hx)
  have hv0l : (sel β v).length = 2 ^ n := length_sel n β v hv
  have hv1l : (sel (!β) v).length = 2 ^ n := length_sel n (!β) v hv
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hCl : (addT false (β :: B') (encodeNat w) false).tail.length = n := by
    rw [List.length_tail, length_addT, List.length_cons, hB]
    rfl
  rw [show rt (encodeNat w) (n + 1) (β :: B') v = inter (rt (encodeNat w) n B' (sel β v))
    (rt (encodeNat w) n (addT false (β :: B') (encodeNat w) false).tail (sel (!β) v)) from rfl]
  obtain ⟨r1, t1, ht1, e1⟩ := phase1_eval β [body] r B' v (2 ^ n) (by rw [hv, hpow]) hrec rest
    hrest' y k (natSyms w ++ r3) Rb a b t u
  obtain ⟨r2, t2, ht2, e2⟩ := ih B' (sel β v) (Sym.mark :: y) k Rb a
    ((sel (!β) v).flatten.reverse ++ Sym.mark :: b) t u r1 hB hv0l hv0r
  have c2 := Eval.recur (ρ := [body]) (n := 0) rfl e2
  obtain ⟨r3', t3, ht3, e3⟩ := phase2_eval β [body] r2 B' w hw r3 hr3 (sel (!β) v) hv1r rest
    ((rt (encodeNat w) n B' (sel β v)).flatten ++ Sym.mark :: y) k Rb a b t u
  obtain ⟨r4, t4, ht4, e4⟩ := ih (addT false (β :: B') (encodeNat w) false).tail (sel (!β) v)
    (Sym.mark :: ((rt (encodeNat w) n B' (sel β v)).flatten ++ Sym.mark :: y)) k Rb a b t u r3'
    hCl hv1l hv1r
  have c4 := Eval.recur (ρ := [body]) (n := 0) rfl e4
  obtain ⟨r5, t5, ht5, e5⟩ := phase3_eval β [body] r4 B' w hw r3 hr3 rest
    ((rt (encodeNat w) n (addT false (β :: B') (encodeNat w) false).tail (sel (!β) v)).flatten ++
      Sym.mark :: ((rt (encodeNat w) n B' (sel β v)).flatten ++ Sym.mark :: y)) k Rb a b t u
  have hEl := length_rt (encodeNat w) n B' (sel β v) hv0l
  have hOl := length_rt (encodeNat w) n (addT false (β :: B') (encodeNat w) false).tail
    (sel (!β) v) hv1l
  obtain ⟨r6, t6, ht6, e6⟩ := phase4_eval [body] r5 (rt (encodeNat w) n B' (sel β v))
    (rt (encodeNat w) n (addT false (β :: B') (encodeNat w) false).tail (sel (!β) v))
    (by rw [hEl, hOl]) (fun x hx => hv0r x (mem_rt _ _ _ _ x hx))
    (fun x hx => hv1r x (mem_rt _ _ _ _ x hx)) rest y k (natSyms w ++ r3)
    ((β :: B').map Sym.bit ++ Sym.mark :: Rb) a b t u
  refine ⟨r6, _, ?_, Eval.seq e1 (Eval.seq c2 (Eval.seq e3 (Eval.seq c4 (Eval.seq e5 e6))))⟩
  have hN := flatten_length_sel' β v
  have hE := flatten_length_rt (encodeNat w) n B' (sel β v)
  have hO := flatten_length_rt (encodeNat w) n (addT false (β :: B') (encodeNat w) false).tail
    (sel (!β) v)
  have hle := length_le_flatten hrec
  have hn2 := lt_two_pow' (n + 1)
  have hX : t1 + t3 + t5 + t6 + 7 ≤ 15 * v.flatten.length + 2 * 2 ^ (n + 1) + 30 * n + 100 := by
    rw [hB] at ht3 ht5
    omega
  have key := node_cost hN (by omega) hn2 ht2 ht4 hX
  omega

/-- **The body**, by induction on the offset-block length. -/
theorem body_spec (w : ℕ) (hw : w % 2 = 1) (r3 : List Sym) (hr3 : TermOK r3) (rest : List Sym)
    (hrest : BlkTerm rest) :
    ∀ (n : ℕ) (B : List Bool) (v : List (List Sym)) (y k Rb a b t u : List Sym) (r : Reg),
      B.length = n → v.length = 2 ^ n → (∀ x ∈ v, RecOK x) →
      ∃ r' tm, tm ≤ 200 * v.flatten.length * (n + 1) ∧
        Eval [body] body
          ⟨r, st9 (v.flatten ++ rest) y k (natSyms w ++ r3) (B.map Sym.bit ++ Sym.mark :: Rb) a b
            t u⟩
          ⟨r', st9 rest ((rt (encodeNat w) n B v).flatten ++ y) k (natSyms w ++ r3)
            (B.map Sym.bit ++ Sym.mark :: Rb) a b t u⟩ tm
  | 0, B, v, y, k, Rb, a, b, t, u, r, hB, hv, hrec => by
    have hB0 : B = [] := List.eq_nil_of_length_eq_zero hB
    subst hB0
    obtain ⟨r0, rfl⟩ : ∃ r0, v = [r0] := by
      match v, hv with
      | [r0], _ => exact ⟨r0, rfl⟩
    have hr0 : RecOK r0 := hrec r0 (List.mem_singleton_self _)
    have hrest' := isRecO_head?_of_blkTerm hrest
    have hx : [r0].flatten ++ rest = r0 ++ rest := by simp
    have hy : (rt (encodeNat w) 0 [] [r0]).flatten ++ y = r0 ++ y := by simp [rt]
    rw [hx, hy]
    have e1 := eval_peekA [body] sBs r (st9 (r0 ++ rest) y k (natSyms w ++ r3)
      (([] : List Bool).map Sym.bit ++ Sym.mark :: Rb) a b t u)
    obtain ⟨r', eb⟩ := base_eval [body] (some Sym.mark, r.2) r0 hr0 rest hrest' y k
      (natSyms w ++ r3) (([] : List Bool).map Sym.bit ++ Sym.mark :: Rb) a b t u
    refine ⟨r', _, ?_, Eval.seq e1 (Eval.ite_false rfl eb)⟩
    obtain ⟨d, rfl, _⟩ := hr0
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
      List.length_singleton]
    omega
  | n + 1, B, v, y, k, Rb, a, b, t, u, r, hB, hv, hrec => by
    obtain ⟨β, B', rfl⟩ : ∃ β B', B = β :: B' := by
      cases B with
      | nil => simp at hB
      | cons β B' => exact ⟨β, B', rfl⟩
    have hB' : B'.length = n := by simpa using hB
    obtain ⟨r', tm, htm, en⟩ := node_spec w hw r3 hr3 rest hrest n
      (body_spec w hw r3 hr3 rest hrest n) β B' v y k Rb a b t u (some (Sym.bit β), r.2) hB' hv
      hrec
    have e1 := eval_peekA [body] sBs r (st9 (v.flatten ++ rest) y k (natSyms w ++ r3)
      ((β :: B').map Sym.bit ++ Sym.mark :: Rb) a b t u)
    refine ⟨r', 1 + (tm + 1 + 1), by omega, ?_⟩
    cases β
    · exact Eval.seq e1 (Eval.ite_true rfl (Eval.ite_false rfl en))
    · exact Eval.seq e1 (Eval.ite_true rfl (Eval.ite_true rfl en))

/-- **The router procedure** (`fix body`). -/
theorem route_spec (w : ℕ) (hw : w % 2 = 1) (r3 : List Sym) (hr3 : TermOK r3) (rest : List Sym)
    (hrest : BlkTerm rest) (n : ℕ) (B : List Bool) (v : List (List Sym))
    (y k Rb a b t u : List Sym) (r : Reg) (hB : B.length = n) (hv : v.length = 2 ^ n)
    (hrec : ∀ x ∈ v, RecOK x) :
    ∃ r' tm, tm ≤ 200 * v.flatten.length * (n + 1) + 2 ∧
      Eval [] route
        ⟨r, st9 (v.flatten ++ rest) y k (natSyms w ++ r3) (B.map Sym.bit ++ Sym.mark :: Rb) a b
          t u⟩
        ⟨r', st9 rest ((rt (encodeNat w) n B v).flatten ++ y) k (natSyms w ++ r3)
          (B.map Sym.bit ++ Sym.mark :: Rb) a b t u⟩ tm := by
  obtain ⟨r', tm, htm, e⟩ := body_spec w hw r3 hr3 rest hrest n B v y k Rb a b t u r hB hv hrec
  exact ⟨r', tm + 2, by omega, Eval.fix e⟩

#assert_std_axioms length_le_flatten flatten_length_sel' lt_two_pow' node_cost node_spec body_spec
  route_spec

end TMFw.W4o
