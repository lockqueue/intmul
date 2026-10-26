/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitMath

/-!
# Schedule compiler emitter, part 2 (`Machine/Walsh/PosPermSchedEmitSt.lean`): the emitter's states

The emitter's states `st S₀ v acc bt`:
* every register outside the scratch set holds `una (v q)`; the scratch registers
  `xc kc kk idx lc t1 t2 t3 tmp Ix q1 q6` of the generic programs are empty;
* the accumulator `ACC` holds `acc` and the batch buffer `BT` holds `bt`;
* every other stack is as in `S₀`.

The file gives the exact update rules of such states and restates the rules of the generic programs
(`PosPermSchedOps/Tbl/IO`) on them, each within the uniform cost `opW V` when the values read are
`≤ V`.

**Scope (honest summary).** Definitions and proved rules only; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- The scratch registers of the generic programs (empty between programs). -/
def isScr : RegN → Bool
  | .xc | .kc | .kk | .idx | .lc | .t1 | .t2 | .t3 | .tmp | .Ix | .q1 | .q6 => true
  | _ => false

/-- The emitter's state. -/
def st (S₀ : Stk → List Sym) (v : RegN → ℕ) (acc bt : List Sym) : Stk → List Sym
  | .inr (.inr q) => if isScr q then [] else una (v q)
  | .inr (.inl .ACC) => acc
  | .inr (.inl .BT) => bt
  | k => S₀ k

section States

variable (S₀ : Stk → List Sym) (v : RegN → ℕ) (acc bt : List Sym)

theorem st_rg (q : RegN) (hq : isScr q = false) : st S₀ v acc bt (rg q) = una (v q) := by
  simp [st, hq]

theorem st_scr (q : RegN) (hq : isScr q = true) : st S₀ v acc bt (rg q) = [] := by
  simp [st, hq]

@[simp] theorem st_acc : st S₀ v acc bt (rs .ACC) = acc := rfl
@[simp] theorem st_bt : st S₀ v acc bt (rs .BT) = bt := rfl

theorem st_raw (w : RawN) (h1 : w ≠ .ACC) (h2 : w ≠ .BT) : st S₀ v acc bt (rs w) = S₀ (rs w) := by
  cases w <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

theorem st_inl (i : Fin 3) : st S₀ v acc bt (.inl i) = S₀ (.inl i) := rfl

theorem rg_inj : Function.Injective rg := fun _ _ h => Sum.inr.inj (Sum.inr.inj h)

theorem st_upd_rg (q : RegN) (n : ℕ) (hq : isScr q = false) :
    Function.update (st S₀ v acc bt) (rg q) (una n) = st S₀ (Function.update v q n) acc bt := by
  funext k
  rcases k with i | w | q'
  · rw [Function.update_of_ne (by simp)]
    rfl
  · rw [Function.update_of_ne (by simp)]
    cases w <;> rfl
  · by_cases h : q' = q
    · subst h
      rw [Function.update_self]
      show una n = if isScr q' then [] else una (Function.update v q' n q')
      rw [hq, Function.update_self]
      rfl
    · rw [Function.update_of_ne (rg_inj.ne h)]
      show (if isScr q' then [] else una (v q')) =
        (if isScr q' then [] else una (Function.update v q n q'))
      rw [Function.update_of_ne h]

theorem st_upd_rg0 (q : RegN) (hq : isScr q = false) :
    Function.update (st S₀ v acc bt) (rg q) [] = st S₀ (Function.update v q 0) acc bt :=
  st_upd_rg S₀ v acc bt q 0 hq

theorem st_upd_acc (a' : List Sym) :
    Function.update (st S₀ v acc bt) (rs .ACC) a' = st S₀ v a' bt := by
  funext k
  rcases k with i | w | q'
  · rw [Function.update_of_ne (by simp)]
    rfl
  · by_cases h : w = .ACC
    · subst h
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by simpa using h)]
      cases w <;> first | rfl | exact absurd rfl h
  · rw [Function.update_of_ne (by simp)]
    rfl

theorem st_upd_bt (b' : List Sym) :
    Function.update (st S₀ v acc bt) (rs .BT) b' = st S₀ v acc b' := by
  funext k
  rcases k with i | w | q'
  · rw [Function.update_of_ne (by simp)]
    rfl
  · by_cases h : w = .BT
    · subst h
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by simpa using h)]
      cases w <;> first | rfl | exact absurd rfl h
  · rw [Function.update_of_ne (by simp)]
    rfl

theorem st_upd_raw (w : RawN) (h1 : w ≠ .ACC) (h2 : w ≠ .BT) (L : List Sym) (hL : S₀ (rs w) = L) :
    Function.update (st S₀ v acc bt) (rs w) L = st S₀ v acc bt := by
  rw [← hL, ← st_raw S₀ v acc bt w h1 h2, Function.update_eq_self]

end States

/-! ## The uniform cost unit -/

/-- The cost unit of one generic program on values `≤ V`. -/
def opW (V : ℕ) : ℕ := 1000 * (V + 1) ^ 2

theorem one_le_opW (V : ℕ) : 1 ≤ opW V := by
  unfold opW
  have : 1 ≤ (V + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem le_opW_lin {a b V : ℕ} (ha : a ≤ V) (hb : b ≤ V) : (a + b) * 50 + 100 ≤ opW V := by
  unfold opW
  have h : V + 1 ≤ (V + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

theorem le_opW_mul {a b V : ℕ} (ha : a ≤ V) (hb : b ≤ V) : (a + 1) * (b + 1) * 200 ≤ opW V := by
  unfold opW
  have h : (a + 1) * (b + 1) ≤ (V + 1) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  omega

theorem le_opW_sq {n V : ℕ} (hn : n ≤ V) : 7 * (n + 1) ^ 2 ≤ opW V := by
  unfold opW
  have : (n + 1) ^ 2 ≤ (V + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

/-! ## Program abbreviations (the scratch registers are fixed) -/

def copyR (a b : RegN) : SProg Stk := copyU (rg a) (rg b) (rg .tmp)
def ltR (a b f : RegN) : SProg Stk := ltF (rg a) (rg b) (rg f) (rg .t1) (rg .t2) (rg .tmp)
def eqR (a b f : RegN) : SProg Stk := eqF (rg a) (rg b) (rg f) (rg .t1) (rg .t2) (rg .t3) (rg .tmp)
def subR (a b c : RegN) : SProg Stk := subU (rg a) (rg b) (rg c) (rg .t1) (rg .t2) (rg .tmp)
def mulR (a b c : RegN) : SProg Stk := mulU (rg a) (rg b) (rg c) (rg .t1) (rg .tmp)
def dmR (a b q r : RegN) : SProg Stk :=
  divmodU (rg a) (rg b) (rg q) (rg r) (rg .kc) (rg .kk) (rg .t1) (rg .t2) (rg .t3) (rg .tmp)
def lookR (IT : RawN) (i o : RegN) : SProg Stk :=
  lookup (rs IT) (rs .U) (rg i) (rg o) (rg .lc) (rg .tmp)
def emitA (a : RegN) : SProg Stk := PSIO.emitField (rg a) (rg .idx) (rs .B1) (rs .ACC)
def emitB (a : RegN) : SProg Stk := PSIO.emitField (rg a) (rg .idx) (rs .B1) (rs .BT)
def pushA (s : Sym) : SProg Stk := pushC (rs .ACC) s
def clr (q : RegN) : SProg Stk := clearU (rg q)
def inc (q : RegN) : SProg Stk := incR (rg q)
def dec (q : RegN) : SProg Stk := decR (rg q)
def ifR (q : RegN) (p r : SProg Stk) : SProg Stk := ifNE (rg q) p r
def loopR (q : RegN) (p : SProg Stk) : SProg Stk := forDown (rg q) p
def xferBT : SProg Stk := .seq (PSIO.moveAll (rs .BT) (rs .U)) (PSIO.moveAll (rs .U) (rs .ACC))

/-! ## Rules on emitter states, each within `opW V` -/

section Rules

variable (S₀ : Stk → List Sym) (v : RegN → ℕ) (acc bt : List Sym) {V : ℕ}

theorem runs_copyR (a b : RegN) (hV : v a ≤ V) (h1 : a ≠ b := by decide)
    (h2 : a ≠ .tmp := by decide) (h3 : b ≠ .tmp := by decide) (ha : isScr a = false := by decide)
    (hb : isScr b = false := by decide) :
    Runs (copyR a b) (st S₀ v acc bt) (st S₀ (Function.update v b (v b + v a)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_copyU (rg_inj.ne h1) (rg_inj.ne h2) (rg_inj.ne h3) (st S₀ v acc bt) (v a) (v b)
    (st_rg S₀ v acc bt a ha) (st_rg S₀ v acc bt b hb) (st_scr S₀ v acc bt .tmp rfl)
  rw [st_upd_rg S₀ v acc bt b _ hb] at h
  exact runs_weak h rfl (by have := le_opW_lin (b := 0) hV (Nat.zero_le V); omega)

theorem runs_ltR (a b f : RegN) (ha : v a ≤ V) (hb : v b ≤ V)
    (hnd : [a, b, f, .t1, .t2, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sf : isScr f = false := by decide) :
    Runs (ltR a b f) (st S₀ v acc bt)
      (st S₀ (Function.update v f (v f + if v a < v b then 1 else 0)) acc bt) (fun _ => True)
      (opW V) := by
  have h := runs_ltF (List.Nodup.map rg_inj hnd) (st S₀ v acc bt) (v a) (v b) (v f)
    (st_rg S₀ v acc bt a sa) (st_rg S₀ v acc bt b sb) (st_rg S₀ v acc bt f sf)
    (st_scr S₀ v acc bt .t1 rfl) (st_scr S₀ v acc bt .t2 rfl) (st_scr S₀ v acc bt .tmp rfl)
  rw [st_upd_rg S₀ v acc bt f _ sf] at h
  exact runs_weak h rfl (by have := le_opW_lin ha hb; omega)

theorem runs_eqR (a b f : RegN) (ha : v a ≤ V) (hb : v b ≤ V)
    (hnd : [a, b, f, .t3, .t1, .t2, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sf : isScr f = false := by decide) :
    Runs (eqR a b f) (st S₀ v acc bt)
      (st S₀ (Function.update v f (v f + if v a = v b then 1 else 0)) acc bt) (fun _ => True)
      (opW V) := by
  have h := runs_eqF (List.Nodup.map rg_inj hnd) (st S₀ v acc bt) (v a) (v b) (v f)
    (st_rg S₀ v acc bt a sa) (st_rg S₀ v acc bt b sb) (st_rg S₀ v acc bt f sf)
    (st_scr S₀ v acc bt .t1 rfl) (st_scr S₀ v acc bt .t2 rfl) (st_scr S₀ v acc bt .t3 rfl)
    (st_scr S₀ v acc bt .tmp rfl)
  rw [st_upd_rg S₀ v acc bt f _ sf] at h
  exact runs_weak h rfl (le_opW_lin ha hb)

theorem runs_subR (a b c : RegN) (ha : v a ≤ V) (hb : v b ≤ V)
    (hnd : [a, b, c, .t1, .t2, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sc : isScr c = false := by decide) :
    Runs (subR a b c) (st S₀ v acc bt)
      (st S₀ (Function.update v c (v c + (v a - v b))) acc bt) (fun _ => True) (opW V) := by
  have h := runs_subU (List.Nodup.map rg_inj hnd) (st S₀ v acc bt) (v a) (v b) (v c)
    (st_rg S₀ v acc bt a sa) (st_rg S₀ v acc bt b sb) (st_rg S₀ v acc bt c sc)
    (st_scr S₀ v acc bt .t1 rfl) (st_scr S₀ v acc bt .t2 rfl) (st_scr S₀ v acc bt .tmp rfl)
  rw [st_upd_rg S₀ v acc bt c _ sc] at h
  exact runs_weak h rfl (by have := le_opW_lin ha hb; omega)

theorem runs_mulR (a b c : RegN) (ha : v a ≤ V) (hb : v b ≤ V)
    (hnd : [a, b, c, .t1, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sc : isScr c = false := by decide) :
    Runs (mulR a b c) (st S₀ v acc bt)
      (st S₀ (Function.update v c (v c + v a * v b)) acc bt) (fun _ => True) (opW V) := by
  have h := runs_mulU (List.Nodup.map rg_inj hnd) (st S₀ v acc bt) (v a) (v b) (v c)
    (st_rg S₀ v acc bt a sa) (st_rg S₀ v acc bt b sb) (st_rg S₀ v acc bt c sc)
    (st_scr S₀ v acc bt .t1 rfl) (st_scr S₀ v acc bt .tmp rfl)
  rw [st_upd_rg S₀ v acc bt c _ sc] at h
  refine runs_weak h rfl ?_
  have h1 := le_opW_mul ha hb
  have h2 : 0 < (v a + 1) * (v b + 1) := Nat.mul_pos (by omega) (by omega)
  omega

theorem runs_dmR (a b q r : RegN) (ha : v a ≤ V) (hb : v b ≤ V) (hb0 : 0 < v b) (hr : v r = 0)
    (hnd : [a, b, q, r, .kc, .kk, .t3, .t1, .t2, .tmp].Nodup := by decide)
    (sa : isScr a = false := by decide) (sb : isScr b = false := by decide)
    (sq : isScr q = false := by decide) (sr : isScr r = false := by decide) :
    Runs (dmR a b q r) (st S₀ v acc bt)
      (st S₀ (Function.update (Function.update v q (v q + v a / v b)) r (v a % v b)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_divmodU (List.Nodup.map rg_inj hnd) (st S₀ v acc bt) (v a) (v b) (v q) hb0
    (st_rg S₀ v acc bt a sa) (st_rg S₀ v acc bt b sb) (st_rg S₀ v acc bt q sq)
    (by rw [st_rg S₀ v acc bt r sr, hr]; rfl) (st_scr S₀ v acc bt .kc rfl)
    (st_scr S₀ v acc bt .kk rfl) (st_scr S₀ v acc bt .t1 rfl) (st_scr S₀ v acc bt .t2 rfl)
    (st_scr S₀ v acc bt .t3 rfl) (st_scr S₀ v acc bt .tmp rfl)
  rw [st_upd_rg S₀ v acc bt q _ sq, st_upd_rg S₀ _ acc bt r _ sr] at h
  exact runs_weak h rfl (le_opW_mul ha hb)

theorem runs_lookR (IT : RawN) (hIT : IT = .I0T ∨ IT = .I1T) (i o : RegN) (l : List ℕ)
    (hT : S₀ (rs IT) = utab l) (hU : S₀ (rs .U) = []) (hj : v i < l.length) (hi : v i ≤ V)
    (hL : (utab l).length ≤ V) (hnd : [i, o, .lc, .tmp].Nodup := by decide)
    (si : isScr i = false := by decide) (so : isScr o = false := by decide) :
    Runs (lookR IT i o) (st S₀ v acc bt) (st S₀ (Function.update v o (v o + l[v i])) acc bt)
      (fun _ => True) (opW V) := by
  have hIU : IT ≠ .U := by rcases hIT with rfl | rfl <;> decide
  have hIA : IT ≠ .ACC := by rcases hIT with rfl | rfl <;> decide
  have hIB : IT ≠ .BT := by rcases hIT with rfl | rfl <;> decide
  have hnd' : [rs IT, rs .U, rg i, rg o, rg .lc, rg .tmp].Nodup := by
    have h2 : [rg i, rg o, rg .lc, rg .tmp].Nodup := List.Nodup.map rg_inj hnd
    refine List.Nodup.cons ?_ (List.Nodup.cons ?_ h2)
    · simp [hIU]
    · simp
  have h := runs_lookup hnd' (st S₀ v acc bt) l (v i) (v o) hj
    (by rw [st_raw S₀ v acc bt IT hIA hIB]; exact hT) (st_rg S₀ v acc bt i si)
    (st_rg S₀ v acc bt o so) (by rw [st_raw S₀ v acc bt .U (by decide) (by decide)]; exact hU)
    (st_scr S₀ v acc bt .lc rfl) (st_scr S₀ v acc bt .tmp rfl)
  rw [st_upd_rg S₀ v acc bt o _ so] at h
  refine runs_weak h rfl ?_
  have := le_opW_mul hi hL
  have h3 : (v i + 1) * ((utab l).length + 1) * 30 ≤ (v i + 1) * ((utab l).length + 1) * 200 :=
    Nat.mul_le_mul_left _ (by norm_num)
  omega

theorem runs_emitA (a : RegN) (hB1 : S₀ (rs .B1) = []) (hV : v a ≤ V)
    (ha : a ≠ .idx := by decide) (sa : isScr a = false := by decide) :
    Runs (emitA a) (st S₀ v acc bt)
      (st S₀ (Function.update v a 0) (natSyms (v a) ++ Sym.mark :: acc) bt) (fun _ => True)
      (opW V) := by
  have h := PSIO.runs_emitField (x := rg a) (q := rg .idx) (tmp := rs .B1) (acc := rs .ACC)
    (rg_inj.ne ha) (by simp) (by simp) (by simp) (by simp) (by simp)
    (st S₀ v acc bt) (v a) (st_rg S₀ v acc bt a sa) (st_scr S₀ v acc bt .idx rfl)
    (by rw [st_raw S₀ v acc bt .B1 (by decide) (by decide)]; exact hB1)
  rw [st_upd_rg0 S₀ v acc bt a sa, st_upd_acc] at h
  exact runs_weak h rfl (le_opW_sq hV)

theorem runs_emitB (a : RegN) (hB1 : S₀ (rs .B1) = []) (hV : v a ≤ V)
    (ha : a ≠ .idx := by decide) (sa : isScr a = false := by decide) :
    Runs (emitB a) (st S₀ v acc bt)
      (st S₀ (Function.update v a 0) acc (natSyms (v a) ++ Sym.mark :: bt)) (fun _ => True)
      (opW V) := by
  have h := PSIO.runs_emitField (x := rg a) (q := rg .idx) (tmp := rs .B1) (acc := rs .BT)
    (rg_inj.ne ha) (by simp) (by simp) (by simp) (by simp) (by simp)
    (st S₀ v acc bt) (v a) (st_rg S₀ v acc bt a sa) (st_scr S₀ v acc bt .idx rfl)
    (by rw [st_raw S₀ v acc bt .B1 (by decide) (by decide)]; exact hB1)
  rw [st_upd_rg0 S₀ v acc bt a sa, st_upd_bt] at h
  exact runs_weak h rfl (le_opW_sq hV)

theorem runs_pushA (s : Sym) :
    Runs (pushA s) (st S₀ v acc bt) (st S₀ v (s :: acc) bt) (fun _ => True) (opW V) := by
  have h := runs_pushC (rs .ACC) s (st S₀ v acc bt)
  rw [st_upd_acc] at h
  exact runs_weak h rfl (one_le_opW V)

theorem runs_clr (q : RegN) (hV : v q ≤ V) (sq : isScr q = false := by decide) :
    Runs (clr q) (st S₀ v acc bt) (st S₀ (Function.update v q 0) acc bt) (fun _ => True)
      (opW V) := by
  have h := runs_clearU (rg q) (st S₀ v acc bt) (v q) (st_rg S₀ v acc bt q sq)
  rw [st_upd_rg0 S₀ v acc bt q sq] at h
  exact runs_weak h rfl (by have := le_opW_lin (b := 0) hV (Nat.zero_le V); omega)

theorem runs_inc (q : RegN) (sq : isScr q = false := by decide) :
    Runs (inc q) (st S₀ v acc bt) (st S₀ (Function.update v q (v q + 1)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_incR (rg q) (st S₀ v acc bt) (v q) (st_rg S₀ v acc bt q sq)
  rw [st_upd_rg S₀ v acc bt q _ sq] at h
  exact runs_weak h rfl (one_le_opW V)

theorem runs_dec (q : RegN) (sq : isScr q = false := by decide) :
    Runs (dec q) (st S₀ v acc bt) (st S₀ (Function.update v q (v q - 1)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_decR (rg q) (st S₀ v acc bt) (v q) (st_rg S₀ v acc bt q sq)
  rw [st_upd_rg S₀ v acc bt q _ sq] at h
  exact runs_weak h rfl (one_le_opW V)

theorem runs_skip_st : Runs (skip : SProg Stk) (st S₀ v acc bt) (st S₀ v acc bt) (fun _ => True)
    (opW V) :=
  runs_weak (runs_skip _) rfl (one_le_opW V)

theorem runs_xfer (hU : S₀ (rs .U) = []) (hV : bt.length ≤ V) :
    Runs xferBT (st S₀ v acc bt) (st S₀ v (bt ++ acc) []) (fun _ => True) (opW V) := by
  have h1 := PSIO.runs_moveAll (src := rs .BT) (dst := rs .U) (by simp) (st S₀ v acc bt)
  rw [st_upd_bt, st_bt, st_raw S₀ v acc bt .U (by decide) (by decide), hU, List.append_nil] at h1
  have h2 := PSIO.runs_moveAll (src := rs .U) (dst := rs .ACC) (by simp)
    (Function.update (st S₀ v acc []) (rs .U) bt.reverse)
  have e1 : Function.update (Function.update (st S₀ v acc []) (rs .U) bt.reverse) (rs .U) [] =
      st S₀ v acc [] := by
    rw [Function.update_idem]
    exact st_upd_raw S₀ v acc [] .U (by decide) (by decide) [] hU
  rw [e1, Function.update_self, Function.update_of_ne (by simp), st_acc, st_upd_acc,
    List.reverse_reverse, List.length_reverse] at h2
  refine runs_weak (runs_seq' h1 h2 le_rfl) rfl ?_
  have := le_opW_lin hV hV
  omega

theorem runs_ifR_pos {q : RegN} {p r : SProg Stk} {S' : Stk → List Sym} {T : ℕ}
    (h : v q ≠ 0) (hp : Runs p (st S₀ v acc bt) S' (fun _ => True) T)
    (sq : isScr q = false := by decide) :
    Runs (ifR q p r) (st S₀ v acc bt) S' (fun _ => True) (T + 2) :=
  runs_ifNE_pos (by rw [st_rg S₀ v acc bt q sq]; exact una_ne_nil h) hp

theorem runs_ifR_neg {q : RegN} {p r : SProg Stk} {S' : Stk → List Sym} {T : ℕ}
    (h : v q = 0) (hr : Runs r (st S₀ v acc bt) S' (fun _ => True) T)
    (sq : isScr q = false := by decide) :
    Runs (ifR q p r) (st S₀ v acc bt) S' (fun _ => True) (T + 2) :=
  runs_ifNE_neg (by rw [st_rg S₀ v acc bt q sq, h]; rfl) hr

end Rules

/-- **Counted loop on an emitter register.** -/
theorem runs_loopR (S₀ : Stk → List Sym) (q : RegN) (hq : isScr q = false) {p : SProg Stk}
    (E : ℕ → RegN → ℕ) (A B : ℕ → List Sym) (Tb n : ℕ)
    (hstep : ∀ i < n, Runs p (st S₀ (Function.update (E i) q (n - 1 - i)) (A i) (B i))
      (st S₀ (Function.update (E (i + 1)) q (n - 1 - i)) (A (i + 1)) (B (i + 1)))
      (fun _ => True) Tb) :
    Runs (loopR q p) (st S₀ (Function.update (E 0) q n) (A 0) (B 0))
      (st S₀ (Function.update (E n) q 0) (A n) (B n)) (fun _ => True) (n * (Tb + 3) + 2) := by
  have h := runs_forDown (c := rg q) (p := p) (fun i => st S₀ (E i) (A i) (B i)) Tb n
    (fun i hi => by
      have h1 := hstep i hi
      rw [← st_upd_rg S₀ (E i) (A i) (B i) q _ hq,
        ← st_upd_rg S₀ (E (i + 1)) (A (i + 1)) (B (i + 1)) q _ hq] at h1
      exact h1)
  have h' : Runs (forDown (rg q) p) (Function.update (st S₀ (E 0) (A 0) (B 0)) (rg q) (una n))
      (Function.update (st S₀ (E n) (A n) (B n)) (rg q) []) (fun _ => True)
      (n * (Tb + 3) + 2) := h
  rw [st_upd_rg S₀ (E 0) (A 0) (B 0) q _ hq, st_upd_rg0 S₀ (E n) (A n) (B n) q hq] at h'
  exact h'

/-- Equal valuations give equal states. -/
theorem st_congr {S₀ : Stk → List Sym} {w₁ w₂ : RegN → ℕ} {acc bt : List Sym}
    (h : ∀ r, w₁ r = w₂ r) : st S₀ w₁ acc bt = st S₀ w₂ acc bt := by
  rw [funext h]

/-- The stage pair of a candidate at position `xr` with `y = I xr`: `c := y, t := xr` (stage A)
or `c := xr, t := y` (stage B). -/
def ctSet (stA : Bool) (xr : RegN) : SProg Stk :=
  if stA then .seq (copyR .y .c) (copyR xr .t) else .seq (copyR xr .c) (copyR .y .t)

/-! ## Rules with a zero destination -/

section Zero

variable (S₀ : Stk → List Sym) (v : RegN → ℕ) (acc bt : List Sym) {V : ℕ}

theorem runs_copyR0 (a b : RegN) (hV : v a ≤ V) (h0 : v b = 0) (h1 : a ≠ b := by decide)
    (h2 : a ≠ .tmp := by decide) (h3 : b ≠ .tmp := by decide) (ha : isScr a = false := by decide)
    (hb : isScr b = false := by decide) :
    Runs (copyR a b) (st S₀ v acc bt) (st S₀ (Function.update v b (v a)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_copyR S₀ v acc bt a b hV h1 h2 h3 ha hb
  rwa [h0, Nat.zero_add] at h

theorem runs_ltR0 (a b f : RegN) (ha : v a ≤ V) (hb : v b ≤ V) (h0 : v f = 0)
    (hnd : [a, b, f, .t1, .t2, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sf : isScr f = false := by decide) :
    Runs (ltR a b f) (st S₀ v acc bt)
      (st S₀ (Function.update v f (if v a < v b then 1 else 0)) acc bt) (fun _ => True)
      (opW V) := by
  have h := runs_ltR S₀ v acc bt a b f ha hb hnd sa sb sf
  rwa [h0, Nat.zero_add] at h

theorem runs_eqR0 (a b f : RegN) (ha : v a ≤ V) (hb : v b ≤ V) (h0 : v f = 0)
    (hnd : [a, b, f, .t3, .t1, .t2, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sf : isScr f = false := by decide) :
    Runs (eqR a b f) (st S₀ v acc bt)
      (st S₀ (Function.update v f (if v a = v b then 1 else 0)) acc bt) (fun _ => True)
      (opW V) := by
  have h := runs_eqR S₀ v acc bt a b f ha hb hnd sa sb sf
  rwa [h0, Nat.zero_add] at h

theorem runs_subR0 (a b c : RegN) (ha : v a ≤ V) (hb : v b ≤ V) (h0 : v c = 0)
    (hnd : [a, b, c, .t1, .t2, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sc : isScr c = false := by decide) :
    Runs (subR a b c) (st S₀ v acc bt) (st S₀ (Function.update v c (v a - v b)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_subR S₀ v acc bt a b c ha hb hnd sa sb sc
  rwa [h0, Nat.zero_add] at h

theorem runs_mulR0 (a b c : RegN) (ha : v a ≤ V) (hb : v b ≤ V) (h0 : v c = 0)
    (hnd : [a, b, c, .t1, .tmp].Nodup := by decide) (sa : isScr a = false := by decide)
    (sb : isScr b = false := by decide) (sc : isScr c = false := by decide) :
    Runs (mulR a b c) (st S₀ v acc bt) (st S₀ (Function.update v c (v a * v b)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_mulR S₀ v acc bt a b c ha hb hnd sa sb sc
  rwa [h0, Nat.zero_add] at h

theorem runs_dmR0 (a b q r : RegN) (ha : v a ≤ V) (hb : v b ≤ V) (hb0 : 0 < v b)
    (hq0 : v q = 0) (hr : v r = 0)
    (hnd : [a, b, q, r, .kc, .kk, .t3, .t1, .t2, .tmp].Nodup := by decide)
    (sa : isScr a = false := by decide) (sb : isScr b = false := by decide)
    (sq : isScr q = false := by decide) (sr : isScr r = false := by decide) :
    Runs (dmR a b q r) (st S₀ v acc bt)
      (st S₀ (Function.update (Function.update v q (v a / v b)) r (v a % v b)) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_dmR S₀ v acc bt a b q r ha hb hb0 hr hnd sa sb sq sr
  rwa [hq0, Nat.zero_add] at h

theorem runs_lookR0 (IT : RawN) (hIT : IT = .I0T ∨ IT = .I1T) (i o : RegN) (l : List ℕ)
    (hT : S₀ (rs IT) = utab l) (hU : S₀ (rs .U) = []) (hj : v i < l.length) (hi : v i ≤ V)
    (hL : (utab l).length ≤ V) (h0 : v o = 0) (hnd : [i, o, .lc, .tmp].Nodup := by decide)
    (si : isScr i = false := by decide) (so : isScr o = false := by decide) :
    Runs (lookR IT i o) (st S₀ v acc bt) (st S₀ (Function.update v o l[v i]) acc bt)
      (fun _ => True) (opW V) := by
  have h := runs_lookR S₀ v acc bt IT hIT i o l hT hU hj hi hL hnd si so
  rwa [h0, Nat.zero_add] at h

end Zero

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
