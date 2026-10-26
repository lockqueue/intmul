/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedBase

/-!
# Schedule compiler, part 2 (`Machine/Walsh/PosPermSchedOps.lean`): unary arithmetic

Generic programs over unary registers (`una n` stacks, `PosPermSchedBase.lean`) and their exact
`Runs` rules: `copyU` (copy), `ifNE` (branch on a nonempty stack), `ltF` (comparison flag).
Temporaries are empty before and after every program.

**Scope (honest summary).** Definitions and proved rules only; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts

section Ops

variable {K : Type} [DecidableEq K]

/-! ## Copy -/

/-- `dst := dst + src`, `src` kept; `tmp` empty before and after. -/
def copyU (src dst tmp : K) : SProg K :=
  .seq (forDown src (.seq (incR dst) (incR tmp))) (forDown tmp (incR src))

theorem runs_copyU {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (S : K → List Sym) (a b : ℕ) (hs : S src = una a) (hd : S dst = una b) (ht : S tmp = []) :
    Runs (copyU src dst tmp) S (Function.update S dst (una (b + a))) (fun _ => True)
      (a * 10 + 6) := by
  have L1 := runs_forDown (c := src) (p := .seq (incR dst) (incR tmp))
    (fun i => Function.update (Function.update S dst (una (b + i))) tmp (una i)) 2 a
    (fun i _ => by
      have i1 := runs_incR dst (Function.update (Function.update (Function.update S dst
        (una (b + i))) tmp (una i)) src (una (a - 1 - i))) (b + i) (by
          rw [Function.update_of_ne h1.symm, Function.update_of_ne h3, Function.update_self])
      have i2 := runs_incR tmp (Function.update (Function.update (Function.update
        (Function.update S dst (una (b + i))) tmp (una i)) src (una (a - 1 - i))) dst
        (una (b + i + 1))) i (by
          rw [Function.update_of_ne h3.symm, Function.update_of_ne h2.symm, Function.update_self])
      refine runs_seq' i1 (runs_weak i2 ?_ le_rfl) le_rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all) <;> (try rfl))
  have L2 := runs_forDown (c := tmp) (p := incR src)
    (fun j => Function.update (Function.update S dst (una (b + a))) src (una j)) 1 a
    (fun j _ => by
      have i1 := runs_incR src (Function.update (Function.update (Function.update S dst
        (una (b + a))) src (una j)) tmp (una (a - 1 - j))) j (by
          rw [Function.update_of_ne h2, Function.update_self])
      refine runs_weak i1 ?_ le_rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all) <;> (try rfl))
  have e0 : Function.update (Function.update (Function.update S dst (una (b + 0))) tmp (una 0))
      src (una a) = S := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  have e1 : Function.update (Function.update (Function.update S dst (una (b + a))) tmp (una a))
      src [] = Function.update (Function.update (Function.update S dst (una (b + a))) src
      (una 0)) tmp (una a) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  have e2 : Function.update (Function.update (Function.update S dst (una (b + a))) src (una a))
      tmp [] = Function.update S dst (una (b + a)) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e0, e1] at L1
  rw [e2] at L2
  exact runs_seq' L1 L2 (by omega)

/-! ## Branch on a nonempty stack -/

/-- `if k ≠ [] then p else q`. -/
def ifNE (k : K) (p q : SProg K) : SProg K := .seq (peekR k) (.ite isSomeB p q)

theorem runs_ifNE_pos {k : K} {p q : SProg K} {S S' : K → List Sym} {T : ℕ} (hk : S k ≠ [])
    (hp : Runs p S S' (fun _ => True) T) : Runs (ifNE k p q) S S' (fun _ => True) (T + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := runs_peekR k S s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ := hp s1 hs1
  refine ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true ?_ e2), hs2, by omega⟩
  rw [hv1]
  cases h : S k with
  | nil => exact absurd h hk
  | cons a l => rfl

theorem runs_ifNE_neg {k : K} {p q : SProg K} {S S' : K → List Sym} {T : ℕ} (hk : S k = [])
    (hq : Runs q S S' (fun _ => True) T) : Runs (ifNE k p q) S S' (fun _ => True) (T + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := runs_peekR k S s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ := hq s1 hs1
  refine ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false ?_ e2), hs2, by omega⟩
  rw [hv1, hk]
  rfl

/-! ## Comparison flag -/

/-- `f := f + [x < y]`; `x`, `y` kept; `t1`, `t2`, `tmp` empty before and after. -/
def ltF (x y f t1 t2 tmp : K) : SProg K :=
  .seq (copyU x t1 tmp) (.seq (copyU y t2 tmp) (.seq (forDown t1 (popR t2))
    (.seq (ifNE t2 (incR f) skip) (clearU t2))))

theorem runs_ltF {x y f t1 t2 tmp : K} (hnd : [x, y, f, t1, t2, tmp].Nodup) (S : K → List Sym)
    (a b c : ℕ) (hx : S x = una a) (hy : S y = una b) (hf : S f = una c) (h1 : S t1 = [])
    (h2 : S t2 = []) (h3 : S tmp = []) :
    Runs (ltF x y f t1 t2 tmp) S (Function.update S f (una (c + if a < b then 1 else 0)))
      (fun _ => True) ((a + b) * 20 + 40) := by
  have hd : x ≠ y ∧ x ≠ f ∧ x ≠ t1 ∧ x ≠ t2 ∧ x ≠ tmp ∧ y ≠ f ∧ y ≠ t1 ∧ y ≠ t2 ∧ y ≠ tmp ∧
      f ≠ t1 ∧ f ≠ t2 ∧ f ≠ tmp ∧ t1 ≠ t2 ∧ t1 ≠ tmp ∧ t2 ≠ tmp := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨hxy, hxf, hx1, hx2, hxt, hyf, hy1, hy2, hyt, hf1, hf2, hft, h12, h1t, h2t⟩ := hd
  have c1 := runs_copyU hx1 hxt h1t S a 0 hx h1 h3
  have c2 := runs_copyU hy2 hyt h2t (Function.update S t1 (una (0 + a))) b 0
    (by rw [Function.update_of_ne hy1, hy]) (by rw [Function.update_of_ne h12.symm, h2]; rfl)
    (by rw [Function.update_of_ne h1t.symm, h3])
  have c3 := runs_forDown (c := t1) (p := popR t2) (fun i => Function.update S t2 (una (b - i)))
    1 a (fun i _ => by
      have hp := runs_popR t2
        (Function.update (Function.update S t2 (una (b - i))) t1 (una (a - 1 - i)))
      simp only [Function.update_of_ne h12.symm, Function.update_self, tail_una] at hp
      refine runs_weak (runs_true hp) ?_ le_rfl
      have e : b - i - 1 = b - (i + 1) := by omega
      rw [e]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e3 : Function.update (Function.update S t2 (una (b - 0))) t1 (una a) =
      Function.update (Function.update S t1 (una (0 + a))) t2 (una (0 + b)) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e3] at c3
  by_cases hab : a < b
  · rw [if_pos hab]
    have hne : Function.update (Function.update S t2 (una (b - a))) t1 [] t2 ≠ [] := by
      rw [Function.update_of_ne h12.symm, Function.update_self]
      exact una_ne_nil (by omega)
    have c4 := runs_ifNE_pos (q := skip) hne (runs_incR f _ c (by
      rw [Function.update_of_ne hf1, Function.update_of_ne hf2, hf]))
    have c5 := runs_clearU t2 (Function.update (Function.update (Function.update S t2
      (una (b - a))) t1 []) f (una (c + 1))) (b - a) (by
        rw [Function.update_of_ne hf2.symm, Function.update_of_ne h12.symm, Function.update_self])
    refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_weak c5 ?_ le_rfl)
      le_rfl) le_rfl) le_rfl) ?_
    · funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all)
    · omega
  · rw [if_neg hab]
    have hba : b - a = 0 := by omega
    have hne : Function.update (Function.update S t2 (una (b - a))) t1 [] t2 = [] := by
      rw [Function.update_of_ne h12.symm, Function.update_self, hba, una_zero]
    have c4 := runs_ifNE_neg (p := incR f) hne (runs_skip _)
    have c5 := runs_clearU t2 (Function.update (Function.update S t2 (una (b - a))) t1 []) (b - a)
      (by rw [Function.update_of_ne h12.symm, Function.update_self])
    refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_weak c5 ?_ le_rfl)
      le_rfl) le_rfl) le_rfl) ?_
    · funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all)
    · omega

/-! ## Equality flag -/

/-- `f := f + [x = y]`; `x`, `y` kept; `t1 t2 t3 tmp` empty before and after. -/
def eqF (x y f t1 t2 t3 tmp : K) : SProg K :=
  .seq (ltF x y t3 t1 t2 tmp) (.seq (ltF y x t3 t1 t2 tmp)
    (.seq (ifNE t3 skip (incR f)) (clearU t3)))

theorem runs_eqF {x y f t1 t2 t3 tmp : K} (hnd : [x, y, f, t3, t1, t2, tmp].Nodup)
    (S : K → List Sym) (a b c : ℕ) (hx : S x = una a) (hy : S y = una b) (hf : S f = una c)
    (h1 : S t1 = []) (h2 : S t2 = []) (h3 : S t3 = []) (h4 : S tmp = []) :
    Runs (eqF x y f t1 t2 t3 tmp) S (Function.update S f (una (c + if a = b then 1 else 0)))
      (fun _ => True) ((a + b) * 50 + 100) := by
  have n1 : [x, y, t3, t1, t2, tmp].Nodup :=
    hnd.sublist (.cons_cons _ (.cons_cons _ (.cons _ (List.Sublist.refl _))))
  have n2 : [y, x, t3, t1, t2, tmp].Nodup := (List.Perm.swap x y _).nodup_iff.mpr n1
  have hd : x ≠ y ∧ x ≠ f ∧ x ≠ t3 ∧ x ≠ t1 ∧ x ≠ t2 ∧ x ≠ tmp ∧ y ≠ f ∧ y ≠ t3 ∧ y ≠ t1 ∧
      y ≠ t2 ∧ y ≠ tmp ∧ f ≠ t3 ∧ f ≠ t1 ∧ f ≠ t2 ∧ f ≠ tmp ∧ t3 ≠ t1 ∧ t3 ≠ t2 ∧ t3 ≠ tmp ∧
      t1 ≠ t2 ∧ t1 ≠ tmp ∧ t2 ≠ tmp := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨hxy, hxf, hx3, hx1, hx2, hxt, hyf, hy3, hy1, hy2, hyt, hf3, hf1, hf2, hft, h31, h32,
    h3t, h12, h1t, h2t⟩ := hd
  have h13 : t1 ≠ t3 := h31.symm
  have h23 : t2 ≠ t3 := h32.symm
  have c1 := runs_ltF n1 S a b 0 hx hy h3 h1 h2 h4
  set u := (0 + if a < b then 1 else 0) with hu
  have c2 := runs_ltF n2 (Function.update S t3 (una u)) b a u
    (by rw [Function.update_of_ne hy3, hy]) (by rw [Function.update_of_ne hx3, hx])
    (by rw [Function.update_self]) (by rw [Function.update_of_ne h13, h1])
    (by rw [Function.update_of_ne h23, h2]) (by rw [Function.update_of_ne h3t.symm, h4])
  set w := (u + if b < a then 1 else 0) with hw
  by_cases hab : a = b
  · rw [if_pos hab]
    have hw0 : w = 0 := by rw [hw, hu]; split_ifs <;> omega
    have hne : Function.update (Function.update S t3 (una u)) t3 (una w) t3 = [] := by
      rw [Function.update_self, hw0, una_zero]
    have c3 := runs_ifNE_neg (p := skip) hne (runs_incR f _ c (by
      rw [Function.update_of_ne hf3, Function.update_of_ne hf3, hf]))
    have c4 := runs_clearU t3 (Function.update (Function.update (Function.update S t3 (una u))
      t3 (una w)) f (una (c + 1))) w (by rw [Function.update_of_ne hf3.symm, Function.update_self])
    refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_weak c4 ?_ le_rfl) le_rfl) le_rfl) ?_
    · funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all)
    · rw [hw0]
      have hu1 : u ≤ 1 := by rw [hu]; split_ifs <;> omega
      omega
  · rw [if_neg hab]
    have hw1 : w ≠ 0 := by rw [hw, hu]; split_ifs <;> omega
    have hne : Function.update (Function.update S t3 (una u)) t3 (una w) t3 ≠ [] := by
      rw [Function.update_self]
      exact una_ne_nil hw1
    have c3 := runs_ifNE_pos (q := incR f) hne (runs_skip _)
    have c4 := runs_clearU t3 (Function.update (Function.update S t3 (una u)) t3 (una w)) w
      (by rw [Function.update_self])
    refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_weak c4 ?_ le_rfl) le_rfl) le_rfl) ?_
    · funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all)
    · have hw2 : w ≤ 2 := by rw [hw, hu]; split_ifs <;> omega
      omega

/-! ## Truncated subtraction, product, minimum -/

/-- `dst := dst + (x - y)`; `x`, `y` kept; `t1 t2 tmp` empty before and after. -/
def subU (x y dst t1 t2 tmp : K) : SProg K :=
  .seq (copyU x t1 tmp) (.seq (copyU y t2 tmp) (.seq (forDown t2 (popR t1)) (moveU t1 dst)))

theorem runs_subU {x y dst t1 t2 tmp : K} (hnd : [x, y, dst, t1, t2, tmp].Nodup)
    (S : K → List Sym) (a b c : ℕ) (hx : S x = una a) (hy : S y = una b) (hd : S dst = una c)
    (h1 : S t1 = []) (h2 : S t2 = []) (h3 : S tmp = []) :
    Runs (subU x y dst t1 t2 tmp) S (Function.update S dst (una (c + (a - b))))
      (fun _ => True) ((a + b) * 20 + 20) := by
  have hd' : x ≠ y ∧ x ≠ dst ∧ x ≠ t1 ∧ x ≠ t2 ∧ x ≠ tmp ∧ y ≠ dst ∧ y ≠ t1 ∧ y ≠ t2 ∧
      y ≠ tmp ∧ dst ≠ t1 ∧ dst ≠ t2 ∧ dst ≠ tmp ∧ t1 ≠ t2 ∧ t1 ≠ tmp ∧ t2 ≠ tmp := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨hxy, hxd, hx1, hx2, hxt, hyd, hy1, hy2, hyt, hd1, hd2, hdt, h12, h1t, h2t⟩ := hd'
  have c1 := runs_copyU hx1 hxt h1t S a 0 hx h1 h3
  have c2 := runs_copyU hy2 hyt h2t (Function.update S t1 (una (0 + a))) b 0
    (by rw [Function.update_of_ne hy1, hy]) (by rw [Function.update_of_ne h12.symm, h2]; rfl)
    (by rw [Function.update_of_ne h1t.symm, h3])
  have c3 := runs_forDown (c := t2) (p := popR t1)
    (fun i => Function.update S t1 (una (a - i))) 1 b (fun i _ => by
      have hp := runs_popR t1
        (Function.update (Function.update S t1 (una (a - i))) t2 (una (b - 1 - i)))
      simp only [Function.update_of_ne h12, Function.update_self, tail_una] at hp
      refine runs_weak (runs_true hp) ?_ le_rfl
      have e : a - i - 1 = a - (i + 1) := by omega
      rw [e]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e3 : Function.update (Function.update S t1 (una (a - 0))) t2 (una b) =
      Function.update (Function.update S t1 (una (0 + a))) t2 (una (0 + b)) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e3] at c3
  have c4 := runs_moveU hd1.symm (Function.update (Function.update S t1 (una (a - b))) t2 [])
    (a - b) c (by rw [Function.update_of_ne h12, Function.update_self])
    (by rw [Function.update_of_ne hd2, Function.update_of_ne hd1, hd])
  refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_weak c4 ?_ le_rfl) le_rfl) le_rfl) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · omega

/-- `dst := dst + x * y`; `x`, `y` kept; `t1 tmp` empty before and after. -/
def mulU (x y dst t1 tmp : K) : SProg K :=
  .seq (copyU y t1 tmp) (forDown t1 (copyU x dst tmp))

theorem runs_mulU {x y dst t1 tmp : K} (hnd : [x, y, dst, t1, tmp].Nodup)
    (S : K → List Sym) (a b c : ℕ) (hx : S x = una a) (hy : S y = una b) (hd : S dst = una c)
    (h1 : S t1 = []) (h3 : S tmp = []) :
    Runs (mulU x y dst t1 tmp) S (Function.update S dst (una (c + a * b)))
      (fun _ => True) ((a + 1) * (b + 1) * 20 + 20) := by
  have hd' : x ≠ y ∧ x ≠ dst ∧ x ≠ t1 ∧ x ≠ tmp ∧ y ≠ dst ∧ y ≠ t1 ∧ y ≠ tmp ∧ dst ≠ t1 ∧
      dst ≠ tmp ∧ t1 ≠ tmp := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨hxy, hxd, hx1, hxt, hyd, hy1, hyt, hd1, hdt, h1t⟩ := hd'
  have c1 := runs_copyU hy1 hyt h1t S b 0 hy h1 h3
  have c2 := runs_forDown (c := t1) (p := copyU x dst tmp)
    (fun i => Function.update S dst (una (c + i * a))) (a * 10 + 6) b (fun i _ => by
      have hc := runs_copyU hxd hxt hdt
        (Function.update (Function.update S dst (una (c + i * a))) t1 (una (b - 1 - i))) a
        (c + i * a) (by rw [Function.update_of_ne hx1, Function.update_of_ne hxd, hx])
        (by rw [Function.update_of_ne hd1, Function.update_self])
        (by rw [Function.update_of_ne h1t.symm, Function.update_of_ne hdt.symm, h3])
      refine runs_weak hc ?_ le_rfl
      have e : c + i * a + a = c + (i + 1) * a := by ring
      rw [← e]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e2 : Function.update (Function.update S dst (una (c + 0 * a))) t1 (una b) =
      Function.update S t1 (una (0 + b)) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e2] at c2
  refine runs_seq' c1 (runs_weak c2 ?_ le_rfl) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
    all_goals (rw [Nat.mul_comm])
  · have e1 : (a + 1) * (b + 1) * 20 + 20 = a * b * 20 + a * 20 + b * 20 + 40 := by ring
    have e2 : b * (a * 10 + 6 + 3) = a * b * 10 + b * 9 := by ring
    omega

/-! ## Division with remainder -/

theorem succ_mod_div (i b : ℕ) (hb : 0 < b) :
    (i + 1) % b = (if i % b + 1 = b then 0 else i % b + 1) ∧
      (i + 1) / b = i / b + (if i % b + 1 = b then 1 else 0) := by
  have h1 := Nat.div_add_mod i b
  have h2 := Nat.mod_lt i hb
  split_ifs with h
  · have e : i + 1 = b * (i / b + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    constructor
    · rw [e, Nat.mul_mod_right]
    · rw [e, Nat.mul_div_cancel_left _ hb]
  · have e : i + 1 = b * (i / b) + (i % b + 1) := by omega
    have hlt : i % b + 1 < b := by omega
    constructor
    · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    · rw [e, Nat.mul_add_div hb, Nat.div_eq_of_lt hlt, Nat.add_zero]

/-- `q := q + x / y`, `r := r + x % y` (`r = 0` before, `y ≥ 1`); `x`, `y` kept;
`cnt f t1 t2 t3 tmp` empty before and after. -/
def divmodU (x y q r cnt f t1 t2 t3 tmp : K) : SProg K :=
  .seq (copyU x cnt tmp) (forDown cnt (.seq (incR r) (.seq (eqF r y f t1 t2 t3 tmp)
    (.seq (ifNE f (.seq (clearU r) (incR q)) skip) (clearU f)))))

theorem runs_divmodU {x y q r cnt f t1 t2 t3 tmp : K}
    (hnd : [x, y, q, r, cnt, f, t3, t1, t2, tmp].Nodup) (S : K → List Sym) (a b c : ℕ)
    (hb : 0 < b) (hx : S x = una a) (hy : S y = una b) (hq : S q = una c) (hr : S r = [])
    (hcnt : S cnt = []) (hf : S f = []) (h1 : S t1 = []) (h2 : S t2 = []) (h3 : S t3 = [])
    (h4 : S tmp = []) :
    Runs (divmodU x y q r cnt f t1 t2 t3 tmp) S
      (Function.update (Function.update S q (una (c + a / b))) r (una (a % b)))
      (fun _ => True) ((a + 1) * (b + 1) * 200) := by
  have hd : x ≠ y ∧ x ≠ q ∧ x ≠ r ∧ x ≠ cnt ∧ x ≠ f ∧ x ≠ t3 ∧ x ≠ t1 ∧ x ≠ t2 ∧ x ≠ tmp ∧
      y ≠ q ∧ y ≠ r ∧ y ≠ cnt ∧ y ≠ f ∧ y ≠ t3 ∧ y ≠ t1 ∧ y ≠ t2 ∧ y ≠ tmp ∧
      q ≠ r ∧ q ≠ cnt ∧ q ≠ f ∧ q ≠ t3 ∧ q ≠ t1 ∧ q ≠ t2 ∧ q ≠ tmp ∧
      r ≠ cnt ∧ r ≠ f ∧ r ≠ t3 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ tmp ∧
      cnt ≠ f ∧ cnt ≠ t3 ∧ cnt ≠ t1 ∧ cnt ≠ t2 ∧ cnt ≠ tmp ∧
      f ≠ t3 ∧ f ≠ t1 ∧ f ≠ t2 ∧ f ≠ tmp ∧ t3 ≠ t1 ∧ t3 ≠ t2 ∧ t3 ≠ tmp ∧
      t1 ≠ t2 ∧ t1 ≠ tmp ∧ t2 ≠ tmp := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨hxy, hxq, hxr, hxc, hxf, hx3, hx1, hx2, hxt, hyq, hyr, hyc, hyf, hy3, hy1, hy2, hyt,
    hqr, hqc, hqf, hq3, hq1, hq2, hqt, hrc, hrf, hr3, hr1, hr2, hrt, hcf, hc3, hc1, hc2, hct,
    hf3, hf1, hf2, hft, h31, h32, h3t, h12, h1t, h2t⟩ := hd
  have n0 : [y, r, f, t3, t1, t2, tmp].Nodup :=
    hnd.sublist (.cons _ (.cons_cons _ (.cons _ (.cons_cons _ (.cons _ (List.Sublist.refl _))))))
  have nE : [r, y, f, t3, t1, t2, tmp].Nodup := (List.Perm.swap y r _).nodup_iff.mpr n0
  have c1 := runs_copyU hxc hxt hct S a 0 hx hcnt h4
  have L := runs_forDown (c := cnt)
    (p := .seq (incR r) (.seq (eqF r y f t1 t2 t3 tmp)
      (.seq (ifNE f (.seq (clearU r) (incR q)) skip) (clearU f))))
    (fun i => Function.update (Function.update S q (una (c + i / b))) r (una (i % b)))
    (b * 110 + 130) a (fun i hi => by
      obtain ⟨hm, hd⟩ := succ_mod_div i b hb
      have hib := Nat.mod_lt i hb
      set S0 := Function.update (Function.update (Function.update S q (una (c + i / b))) r
        (una (i % b))) cnt (una (a - 1 - i)) with hS0
      have s1 := runs_incR r S0 (i % b) (by rw [hS0, Function.update_of_ne hrc,
        Function.update_self])
      have s2 := runs_eqF nE (Function.update S0 r (una (i % b + 1))) (i % b + 1) b 0
        (by rw [Function.update_self]) (by rw [Function.update_of_ne hyr, hS0,
          Function.update_of_ne hyc, Function.update_of_ne hyr, Function.update_of_ne hyq, hy])
        (by rw [Function.update_of_ne hrf.symm, hS0, Function.update_of_ne hcf.symm,
          Function.update_of_ne hrf.symm, Function.update_of_ne hqf.symm, hf]; rfl)
        (by rw [Function.update_of_ne hr1.symm, hS0, Function.update_of_ne hc1.symm,
          Function.update_of_ne hr1.symm, Function.update_of_ne hq1.symm, h1])
        (by rw [Function.update_of_ne hr2.symm, hS0, Function.update_of_ne hc2.symm,
          Function.update_of_ne hr2.symm, Function.update_of_ne hq2.symm, h2])
        (by rw [Function.update_of_ne hr3.symm, hS0, Function.update_of_ne hc3.symm,
          Function.update_of_ne hr3.symm, Function.update_of_ne hq3.symm, h3])
        (by rw [Function.update_of_ne hrt.symm, hS0, Function.update_of_ne hct.symm,
          Function.update_of_ne hrt.symm, Function.update_of_ne hqt.symm, h4])
      by_cases he : i % b + 1 = b
      · rw [if_pos he] at s2 hm hd
        have hfne : Function.update (Function.update S0 r (una (i % b + 1))) f (una (0 + 1)) f ≠
            [] := by rw [Function.update_self]; exact una_ne_nil (by omega)
        have s3a := runs_clearU r (Function.update (Function.update S0 r (una (i % b + 1))) f
          (una (0 + 1))) (i % b + 1) (by rw [Function.update_of_ne hrf, Function.update_self])
        have s3b := runs_incR q (Function.update (Function.update (Function.update S0 r
          (una (i % b + 1))) f (una (0 + 1))) r []) (c + i / b) (by
            rw [Function.update_of_ne hqr, Function.update_of_ne hqf, Function.update_of_ne hqr,
              hS0, Function.update_of_ne hqc, Function.update_of_ne hqr, Function.update_self])
        have s3 := runs_ifNE_pos (q := skip) hfne (runs_seq' s3a s3b le_rfl)
        have s4 := runs_clearU f (Function.update (Function.update (Function.update
          (Function.update S0 r (una (i % b + 1))) f (una (0 + 1))) r []) q
          (una (c + i / b + 1))) (0 + 1) (by
            rw [Function.update_of_ne hqf.symm, Function.update_of_ne hrf.symm,
              Function.update_self])
        refine runs_seq' s1 (runs_seq' s2 (runs_seq' s3 (runs_weak s4 ?_ le_rfl) le_rfl)
          le_rfl) (by omega)
        rw [hm, hd, hS0]
        funext k
        simp only [Function.update_apply]
        split_ifs <;> (try subst_vars) <;> (try simp_all) <;> rfl
      · rw [if_neg he] at s2 hm hd
        have hfe : Function.update (Function.update S0 r (una (i % b + 1))) f (una (0 + 0)) f =
            [] := by rw [Function.update_self]; rfl
        have s3 := runs_ifNE_neg (p := .seq (clearU r) (incR q)) hfe (runs_skip _)
        have s4 := runs_clearU f (Function.update (Function.update S0 r (una (i % b + 1))) f
          (una (0 + 0))) (0 + 0) (by rw [Function.update_self])
        refine runs_seq' s1 (runs_seq' s2 (runs_seq' s3 (runs_weak s4 ?_ le_rfl) le_rfl)
          le_rfl) (by omega)
        rw [hm, hd, hS0]
        funext k
        simp only [Function.update_apply]
        split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e0 : Function.update (Function.update (Function.update S q (una (c + 0 / b))) r
      (una (0 % b))) cnt (una a) = Function.update S cnt (una (0 + a)) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e0] at L
  refine runs_seq' c1 (runs_weak L ?_ le_rfl) ?_
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have e1 : (a + 1) * (b + 1) * 200 = a * b * 200 + a * 200 + b * 200 + 200 := by ring
    have e2 : a * (b * 110 + 130 + 3) = a * b * 110 + a * 133 := by ring
    omega

end Ops

end SubNLogN.Machine.Walsh.PosPermSchedAux
