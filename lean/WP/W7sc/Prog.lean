import WP.W7k3.SerCall
import WP.W7k3.Helpers

/-!
# WP.W7sc.Prog — the `stdChar` kernel's program and host states

Host `HL = Loc 4 16`: named `0 q`, `1 num`, `2 den` (restored), `3` destination; 16 scratch
stacks, each with a `mark` floor first (so every value on it is `TermOK`-terminated), restored at
the end. Values (`WP.W7sc.Math`; `P` = the natural `π·2^(q+6)`, `Bint = q+2+2(q+2+25)+22`):

| stack | role | stack | role |
|---|---|---|---|
| `.inr 0` | `q+2+4` | `.inr 8` | `denTheta²` |
| `.inr 1` | `π`, `2π`, later `im` | `.inr 9` | `N = q+2+25` |
| `.inr 2` | `num`, later `numTheta·2^Bint` | `.inr 10` | `B = q+2` |
| `.inr 3` | `numTheta` | `.inr 11` | `Bint` |
| `.inr 4` | copy, later `sinA0` | `.inr 12` | `2^Bint` |
| `.inr 5` | `-numTheta²` | `.inr 13` | `cos·2^B` |
| `.inr 6` | `denTheta` | `.inr 14` | `re` |
| `.inr 7` | copy, later `sin·2^B` | `.inr 15` | temporary |

Phases: `phM` marks; `phA` `B`, `B_pi`, `π`, `numTheta`; `phB` the squares and `denTheta`;
`phC` `N`, `Bint`, `2^Bint`; `phD` cosine series and `re`; `phE` sine series, `im`, sign;
`phF` the record onto the destination and the drops; `phZ` the marks.
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

/-- The kernel's host stacks. -/
abbrev HL := Loc 4 16

section Prog

variable (I : KI)

/-- Marks on all scratch stacks. -/
def phM : KP 4 16 I :=
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
  (pushS (.inr 12) .mark).seq <|
  (pushS (.inr 13) .mark).seq <|
  (pushS (.inr 14) .mark).seq <|
  (pushS (.inr 15) .mark)

/-- `B`, `B_pi`, `π`, `numTheta = 2·π·num`. -/
def phA : KP 4 16 I :=
  (kcp I (.inl 0) (.inr 10)).seq <|
  (kincN I (.inr 10) 2).seq <|
  (kcp I (.inr 10) (.inr 0)).seq <|
  (kincN I (.inr 0) 4).seq <|
  (kpi I (.inr 0) (.inr 1)).seq <|
  (popS (.inr 1)).seq <|
  (ks1 I (.inr 1)).seq <|
  (pushS (.inr 1) .pos).seq <|
  (kcp I (.inl 1) (.inr 2)).seq <|
  (pushS (.inr 2) .pos).seq <|
  (kmu I (.inr 1) (.inr 2) (.inr 3)).seq <|
  (kdrI I (.inr 1)).seq (kdrI I (.inr 2))

/-- `-numTheta²`, `denTheta`, `denTheta²`. -/
def phB : KP 4 16 I :=
  (kcpI I (.inr 3) (.inr 4)).seq <|
  (kmu I (.inr 3) (.inr 4) (.inr 5)).seq <|
  (kdrI I (.inr 4)).seq <|
  (kng I (.inr 5)).seq <|
  (kcp I (.inl 2) (.inr 6)).seq <|
  (ksv I (.inr 6) (.inr 0)).seq <|
  (kdr I (.inr 0)).seq <|
  (pushS (.inr 6) .pos).seq <|
  (kcpI I (.inr 6) (.inr 7)).seq <|
  (kmu I (.inr 6) (.inr 7) (.inr 8)).seq <|
  (kdrI I (.inr 7)).seq <|
  (popS (.inr 8)).seq (popS (.inr 6))

/-- `N`, `Bint`, `2^Bint` (signed). -/
def phC : KP 4 16 I :=
  (kcp I (.inr 10) (.inr 9)).seq <|
  (kincN I (.inr 9) 25).seq <|
  (kcp I (.inr 9) (.inr 15)).seq <|
  (kad I (.inr 9) (.inr 15) (.inr 12)).seq <|
  (kdr I (.inr 15)).seq <|
  (kad I (.inr 10) (.inr 12) (.inr 11)).seq <|
  (kdr I (.inr 12)).seq <|
  (kincN I (.inr 11) 22).seq <|
  (pushNat (.inr 12) 1).seq <|
  (ksv I (.inr 12) (.inr 11)).seq (pushS (.inr 12) .pos)

/-- The cosine series and `re`. -/
def phD : KP 4 16 I :=
  (ksc I (.inr 12) (.inr 5) (.inr 8) (.inr 9) (.inr 13)).seq <|
  (popS (.inr 12)).seq <|
  (kshlI I (.inr 13) (.inr 10)).seq <|
  (kdv I (.inr 13) (.inr 12) (.inr 14)).seq (kdrI I (.inr 13))

/-- `sinA0`, the sine series and `im` before the sign. -/
def phE0 : KP 4 16 I :=
  (kcpI I (.inr 3) (.inr 2)).seq <|
  (kdrI I (.inr 3)).seq <|
  (kshlI I (.inr 2) (.inr 11)).seq <|
  (kdv I (.inr 2) (.inr 6) (.inr 4)).seq <|
  (kdrI I (.inr 2)).seq <|
  (kss I (.inr 4) (.inr 5) (.inr 8) (.inr 9) (.inr 7)).seq <|
  (kshlI I (.inr 7) (.inr 10)).seq (kdv I (.inr 7) (.inr 12) (.inr 1))

/-- The compile-time sign of `im`. -/
def negStep (neg : Bool) : KP 4 16 I := bif neg then kng I (.inr 1) else .load id

/-- The record onto the destination, then the drops. -/
def phF : KP 4 16 I :=
  (pushS (.inl 3) .sep).seq <|
  (kmvI I (.inr 1) (.inl 3)).seq <|
  (kmvI I (.inr 14) (.inl 3)).seq <|
  (kdrI I (.inr 4)).seq <|
  (kdrI I (.inr 5)).seq <|
  (kdr I (.inr 6)).seq <|
  (kdrI I (.inr 7)).seq <|
  (kdr I (.inr 8)).seq <|
  (kdr I (.inr 9)).seq <|
  (kdr I (.inr 10)).seq <|
  (kdr I (.inr 11)).seq (kdr I (.inr 12))

/-- Pop the marks. -/
def phZ : KP 4 16 I :=
  (popS (.inr 0)).seq <|
  (popS (.inr 1)).seq <|
  (popS (.inr 2)).seq <|
  (popS (.inr 3)).seq <|
  (popS (.inr 4)).seq <|
  (popS (.inr 5)).seq <|
  (popS (.inr 6)).seq <|
  (popS (.inr 7)).seq <|
  (popS (.inr 8)).seq <|
  (popS (.inr 9)).seq <|
  (popS (.inr 10)).seq <|
  (popS (.inr 11)).seq <|
  (popS (.inr 12)).seq <|
  (popS (.inr 13)).seq <|
  (popS (.inr 14)).seq <|
  (popS (.inr 15))

/-- **The `stdChar` kernel** (compile-time sign `neg`). -/
def scProg (neg : Bool) : KP 4 16 I :=
  (phM I).seq <| (phA I).seq <| (phB I).seq <| (phC I).seq <| (phD I).seq <| (phE0 I).seq <|
  (negStep I neg).seq <| (phF I).seq (phZ I)

theorem scProg_closed (neg : Bool) : (scProg I neg).Closed := by
  have hn : (negStep I neg).Closed := by
    cases neg
    · exact trivial
    · exact callI_closed _ _ _ _
  unfold scProg phM phA phB phC phD phE0 phF phZ
  repeat' first
    | exact hn
    | exact callI_closed _ _ _ _ | exact kdrI_closed _ _ | exact kmvI_closed _ _ _
    | exact kcpI_closed _ _ _ | exact kshlI_closed _ _ _ | exact kincN_closed _ _ _
    | exact pushBits_closed _ _ | exact trivial | refine ⟨?_, ?_⟩

end Prog

/-! ## Host states -/

/-- The kernel's host state: scratch contents `t0 … t15`, destination `vd`, the rest as `S`. -/
def cSt (S : HL → List Sym) (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd : List Sym) : HL → List Sym
  | .inl i => if i = 3 then vd else S (.inl i)
  | .inr j =>
    if j = 0 then t0 else if j = 1 then t1 else if j = 2 then t2 else if j = 3 then t3 else
    if j = 4 then t4 else if j = 5 then t5 else if j = 6 then t6 else if j = 7 then t7 else
    if j = 8 then t8 else if j = 9 then t9 else if j = 10 then t10 else if j = 11 then t11 else
    if j = 12 then t12 else if j = 13 then t13 else if j = 14 then t14 else
    if j = 15 then t15 else S (.inr j)

section cSt

variable (S : HL → List Sym) (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd w : List Sym)

@[simp] theorem cSt_0 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 0) = t0 := rfl
@[simp] theorem cSt_1 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 1) = t1 := rfl
@[simp] theorem cSt_2 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 2) = t2 := rfl
@[simp] theorem cSt_3 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 3) = t3 := rfl
@[simp] theorem cSt_4 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 4) = t4 := rfl
@[simp] theorem cSt_5 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 5) = t5 := rfl
@[simp] theorem cSt_6 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 6) = t6 := rfl
@[simp] theorem cSt_7 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 7) = t7 := rfl
@[simp] theorem cSt_8 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 8) = t8 := rfl
@[simp] theorem cSt_9 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 9) = t9 := rfl
@[simp] theorem cSt_10 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 10) = t10 := rfl
@[simp] theorem cSt_11 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 11) = t11 := rfl
@[simp] theorem cSt_12 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 12) = t12 := rfl
@[simp] theorem cSt_13 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 13) = t13 := rfl
@[simp] theorem cSt_14 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 14) = t14 := rfl
@[simp] theorem cSt_15 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inr 15) = t15 := rfl
@[simp] theorem cSt_d : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inl 3) = vd := rfl
@[simp] theorem cSt_in0 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inl 0) = S (.inl 0) := rfl
@[simp] theorem cSt_in1 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inl 1) = S (.inl 1) := rfl
@[simp] theorem cSt_in2 : cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd (.inl 2) = S (.inl 2) := rfl

theorem cSt_upd0 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 0) w = cSt S w t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 0
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd1 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 1) w = cSt S t0 w t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 1
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd2 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 2) w = cSt S t0 t1 w t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 2
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd3 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 3) w = cSt S t0 t1 t2 w t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 3
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd4 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 4) w = cSt S t0 t1 t2 t3 w t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 4
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd5 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 5) w = cSt S t0 t1 t2 t3 t4 w t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 5
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd6 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 6) w = cSt S t0 t1 t2 t3 t4 t5 w t7 t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 6
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd7 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 7) w = cSt S t0 t1 t2 t3 t4 t5 t6 w t8 t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 7
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd8 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 8) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 w t9 t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 8
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd9 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 9) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 w t10 t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 9
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd10 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 10) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 w t11 t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 10
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd11 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 11) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 w t12 t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 11
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd12 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 12) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 w t13 t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 12
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd13 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 13) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 w t14 t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 13
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd14 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 14) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 w t15 vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 14
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_upd15 :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inr 15) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 w vd := by
  funext x
  rcases x with i | k
  · simp [cSt]
  · by_cases h : k = 15
    · subst h
      simp [cSt]
    · simp [cSt, h]

theorem cSt_updd :
    Function.update (cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 vd) (.inl 3) w = cSt S t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 w := by
  funext x
  rcases x with i | k
  · by_cases h : i = 3
    · subst h
      simp [cSt]
    · simp [cSt, h]
  · simp [cSt]

theorem cSt_self : cSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inr 6)) (S (.inr 7)) (S (.inr 8)) (S (.inr 9)) (S (.inr 10)) (S (.inr 11)) (S (.inr 12)) (S (.inr 13)) (S (.inr 14)) (S (.inr 15)) (S (.inl 3)) = S := by
  funext x
  rcases x with i | k
  · fin_cases i <;> rfl
  · fin_cases k <;> rfl

theorem cSt_final : cSt S (S (.inr 0)) (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inr 6)) (S (.inr 7)) (S (.inr 8)) (S (.inr 9)) (S (.inr 10)) (S (.inr 11)) (S (.inr 12)) (S (.inr 13)) (S (.inr 14)) (S (.inr 15)) w = Function.update S (.inl 3) w := by
  rw [← cSt_updd, cSt_self]

end cSt


theorem cSt_init (S : HL → List Sym) (w : List Sym) :
    Function.update S (.inr 0) w = cSt S w (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (S (.inr 6)) (S (.inr 7)) (S (.inr 8)) (S (.inr 9)) (S (.inr 10)) (S (.inr 11)) (S (.inr 12)) (S (.inr 13)) (S (.inr 14)) (S (.inr 15)) (S (.inl 3)) := by
  conv_lhs => rw [← cSt_self S]
  rw [cSt_upd0]

/-- `.load id` (the `neg = false` sign step). -/
theorem HT.skipL {a b : ℕ} {σ : Type} (B : Loc a b → List Sym) :
    HT (σ := σ) [] B (.load id) B 1 := by
  rintro ⟨w, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨⟨w, S⟩, 1, Eval.load [] id w S, rfl, le_rfl⟩

#assert_std_axioms scProg_closed cSt_upd0 cSt_upd1 cSt_upd2 cSt_upd3 cSt_upd4 cSt_upd5 cSt_upd6 cSt_upd7 cSt_upd8 cSt_upd9 cSt_upd10 cSt_upd11 cSt_upd12 cSt_upd13 cSt_upd14 cSt_upd15 cSt_updd cSt_self cSt_final cSt_init HT.skipL

end WP.W7sc
