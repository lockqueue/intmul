import WP.W7k3.Helpers
import WP.W7k3.SerMath

/-!
# WP.W7k3.SerDefs — the series sub-kernel's program and host states

Host `SL = Loc 5 12`: named `0 a0, 1 c` (signed), `2 d, 3 n` (unsigned), `4` destination; every
scratch stack gets a `mark` floor first (so every value on it is `TermOK`-terminated) and is restored
at the end.

| stack | role | stack | role |
|---|---|---|---|
| `.inr 0` | loop counter (`n - k`) | `.inr 6` | `d` as a signed number |
| `.inr 1` | `a_k` | `.inr 7` | `a_k·c`, later `s_k + a_k` |
| `.inr 2` | `s_k` | `.inr 8` | `a_k·c·f k` |
| `.inr 3` | `f k` | `.inr 9` | `g k` |
| `.inr 4` | `gγ·k + gδ` | `.inr 10` | `g k·d` |
| `.inr 5` | `gε·k + gζ` | `.inr 11` | `a_(k+1)` |

One step (`serBody`, 24 calls): `T1 := a·c`, `T2 := T1·f`, `T3 := G1·G2`, `T4 := T3·d`,
`T5 := divRound T2 T4`, `T1 := s + a`, then `A := T5`, `Sacc := T1`, and `f`, `G1`, `G2` advance by
`fα`, `gγ`, `gε` (increments).
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

/-- The series sub-kernel's host stacks. -/
abbrev SL := Loc 5 12

section Prog

variable (I : KI)

/-- Setup: marks; `ctr := n`, `A := a0`, `Sacc := 0`, `F := f 0`, `G1 := gδ`, `G2 := gζ`,
`Dz := d` (signed). -/
def serSetup (κ : SK) : KP 5 12 I :=
  (pushS (.inr 0) .mark).seq <|
  (pushS (.inr 1) .mark).seq <|
  (pushS (.inr 2) .mark).seq <|
  (pushS (.inr 3) .mark).seq <|
  (pushS (.inr 4) .mark).seq <|
  (pushS (.inr 5) .mark).seq <|
  (pushS (.inr 6) .mark).seq <|
  (pushS (.inr 7) .mark).seq <|
  (pushS (.inr 8) .mark).seq <|
  (pushS (.inr 9) .mark).seq <|
  (pushS (.inr 10) .mark).seq <|
  (pushS (.inr 11) .mark).seq <|
  (kcp I (.inl 3) (.inr 0)).seq <|
  (kcpI I (.inl 0) (.inr 1)).seq <|
  (pushS (.inr 2) .pos).seq <|
  (pushNat (.inr 3) κ.fβ).seq <|
  (pushNat (.inr 4) κ.gδ).seq <|
  (pushNat (.inr 5) κ.gζ).seq <|
  (kcp I (.inl 2) (.inr 6)).seq (pushS (.inr 6) .pos)

/-- One series step. -/
def serBody (κ : SK) : KP 5 12 I :=
  (pushS (.inr 3) .pos).seq <|
  (kmu I (.inr 1) (.inl 1) (.inr 7)).seq <|
  (kmu I (.inr 7) (.inr 3) (.inr 8)).seq <|
  (popS (.inr 3)).seq <|
  (kdrI I (.inr 7)).seq <|
  (pushS (.inr 4) .pos).seq <|
  (pushS (.inr 5) .pos).seq <|
  (kmu I (.inr 4) (.inr 5) (.inr 9)).seq <|
  (popS (.inr 4)).seq <|
  (popS (.inr 5)).seq <|
  (kmu I (.inr 9) (.inr 6) (.inr 10)).seq <|
  (kdrI I (.inr 9)).seq <|
  (popS (.inr 10)).seq <|
  (kdv I (.inr 8) (.inr 10) (.inr 11)).seq <|
  (kdrI I (.inr 8)).seq <|
  (kdr I (.inr 10)).seq <|
  (kai I (.inr 2) (.inr 1) (.inr 7)).seq <|
  (kdrI I (.inr 1)).seq <|
  (kmvI I (.inr 11) (.inr 1)).seq <|
  (kdrI I (.inr 2)).seq <|
  (kmvI I (.inr 7) (.inr 2)).seq <|
  (kincN I (.inr 3) κ.fα).seq <|
  (kincN I (.inr 4) κ.gγ).seq (kincN I (.inr 5) κ.gε)

/-- Cleanup: drop the values, pop the marks. -/
def serClean : KP 5 12 I :=
  (kdrI I (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (kdrI I (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (kdr I (.inr 3)).seq <| (popS (.inr 3)).seq <|
  (kdr I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (kdr I (.inr 5)).seq <| (popS (.inr 5)).seq <|
  (kdrI I (.inr 6)).seq <| (popS (.inr 6)).seq <|
  (popS (.inr 0)).seq <| (popS (.inr 7)).seq <| (popS (.inr 8)).seq <| (popS (.inr 9)).seq <|
  (popS (.inr 10)).seq (popS (.inr 11))

/-- **The series sub-kernel.** -/
def serProg (κ : SK) : KP 5 12 I :=
  (serSetup I κ).seq <| (kloop I (.inr 0) (serBody I κ)).seq <|
  (kcpI I (.inr 2) (.inl 4)).seq (serClean I)

theorem serProg_closed (κ : SK) : (serProg I κ).Closed := by
  have hb : (serBody I κ).Closed := by
    unfold serBody
    repeat' first
      | exact callI_closed _ _ _ _ | exact kdrI_closed _ _ | exact kmvI_closed _ _ _
      | exact kcpI_closed _ _ _ | exact kincN_closed _ _ _ | exact pushBits_closed _ _
      | exact trivial | refine ⟨?_, ?_⟩
  unfold serProg serSetup serClean
  refine ⟨?_, kloop_closed _ _ _ hb, ?_⟩
  all_goals repeat' first
    | exact callI_closed _ _ _ _ | exact kdrI_closed _ _ | exact kmvI_closed _ _ _
    | exact kcpI_closed _ _ _ | exact kincN_closed _ _ _ | exact pushBits_closed _ _
    | exact trivial | refine ⟨?_, ?_⟩

end Prog

/-! ## Host states -/

/-- The series host state: scratch contents `t0 … t11`, destination content `vd`, the rest as `S`. -/
def sSt (S : SL → List Sym) (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd : List Sym) : SL → List Sym
  | .inl i => if i = 4 then vd else S (.inl i)
  | .inr j =>
    if j = 0 then t0 else if j = 1 then t1 else if j = 2 then t2 else if j = 3 then t3 else
    if j = 4 then t4 else if j = 5 then t5 else if j = 6 then t6 else if j = 7 then t7 else
    if j = 8 then t8 else if j = 9 then t9 else if j = 10 then t10 else if j = 11 then t11 else S (.inr j)

section sSt

variable (S : SL → List Sym) (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd w : List Sym)

@[simp] theorem sSt_0 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 0) = t0 := rfl
@[simp] theorem sSt_1 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 1) = t1 := rfl
@[simp] theorem sSt_2 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 2) = t2 := rfl
@[simp] theorem sSt_3 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 3) = t3 := rfl
@[simp] theorem sSt_4 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 4) = t4 := rfl
@[simp] theorem sSt_5 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 5) = t5 := rfl
@[simp] theorem sSt_6 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 6) = t6 := rfl
@[simp] theorem sSt_7 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 7) = t7 := rfl
@[simp] theorem sSt_8 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 8) = t8 := rfl
@[simp] theorem sSt_9 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 9) = t9 := rfl
@[simp] theorem sSt_10 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 10) = t10 := rfl
@[simp] theorem sSt_11 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inr 11) = t11 := rfl
@[simp] theorem sSt_d : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inl 4) = vd := rfl
@[simp] theorem sSt_in0 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inl 0) = S (.inl 0) := rfl
@[simp] theorem sSt_in1 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inl 1) = S (.inl 1) := rfl
@[simp] theorem sSt_in2 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inl 2) = S (.inl 2) := rfl
@[simp] theorem sSt_in3 : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inl 3) = S (.inl 3) := rfl
theorem sSt_in (i : Fin 5) (hi : i ≠ 4) : sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd (.inl i) = S (.inl i) := by
  simp [sSt, hi]

theorem sSt_upd0 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 0) w = sSt S w t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 0
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd1 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 1) w = sSt S t0 w t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 1
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd2 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 2) w = sSt S t0 t1 w t3 t4 t5 t6 t7 t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 2
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd3 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 3) w = sSt S t0 t1 t2 w t4 t5 t6 t7 t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 3
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd4 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 4) w = sSt S t0 t1 t2 t3 w t5 t6 t7 t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 4
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd5 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 5) w = sSt S t0 t1 t2 t3 t4 w t6 t7 t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 5
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd6 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 6) w = sSt S t0 t1 t2 t3 t4 t5 w t7 t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 6
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd7 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 7) w = sSt S t0 t1 t2 t3 t4 t5 t6 w t8 t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 7
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd8 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 8) w = sSt S t0 t1 t2 t3 t4 t5 t6 t7 w t9 t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 8
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd9 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 9) w = sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 w t10 t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 9
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd10 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 10) w = sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 w t11 vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 10
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_upd11 :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inr 11) w = sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 w vd := by
  funext x
  rcases x with i | k
  · simp [sSt]
  · by_cases h : k = 11
    · subst h
      simp [sSt]
    · simp [sSt, h]

theorem sSt_updd :
    Function.update (sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 vd) (.inl 4) w = sSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 w := by
  funext x
  rcases x with i | k
  · by_cases h : i = 4
    · subst h
      simp [sSt]
    · simp [sSt, h]
  · simp [sSt]

theorem sSt_self : sSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inr 6)) (S (.inr 7)) (S (.inr 8)) (S (.inr 9)) (S (.inr 10)) (S (.inr 11)) (S (.inl 4)) = S := by
  funext x
  rcases x with i | k
  · fin_cases i <;> rfl
  · fin_cases k <;> rfl

theorem sSt_final : sSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inr 6)) (S (.inr 7)) (S (.inr 8)) (S (.inr 9)) (S (.inr 10)) (S (.inr 11)) w = Function.update S (.inl 4) w := by
  rw [← sSt_updd, sSt_self]

end sSt

theorem sSt_init (S : SL → List Sym) (w : List Sym) :
    Function.update S (.inr 0) w = sSt S w (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inr 6)) (S (.inr 7)) (S (.inr 8)) (S (.inr 9)) (S (.inr 10)) (S (.inr 11)) (S (.inl 4)) := by
  conv_lhs => rw [← sSt_self S]
  rw [sSt_upd0]

#assert_std_axioms serProg_closed sSt_in0 sSt_in1 sSt_in2 sSt_in3 sSt_in sSt_upd0 sSt_upd1 sSt_upd2 sSt_upd3 sSt_upd4 sSt_upd5 sSt_upd6 sSt_upd7 sSt_upd8 sSt_upd9 sSt_upd10 sSt_upd11 sSt_updd sSt_self sSt_final sSt_init

end WP.W7k3
