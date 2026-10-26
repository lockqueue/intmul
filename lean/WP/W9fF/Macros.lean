import WP.W9fF.HostL
import Contracts.W9.Common

/-!
# WP.W9fF.Macros — entry and variable-stack macros (generic in the host stacks)

Raw macros (`SProg K`, exact `Eval` lemmas, any initial register):
| macro | effect | cost |
|---|---|---|
| `popInt src v tmp` | `src = intSyms y ++ d :: rest` (`d` non-bit) ⇒ `v := intSyms y ++ R`, `src := rest` | `9|y| + 2|e| + 23` |
| `popEntry src v1 v2 tmp` | `src = entrySyms y ++ rest` ⇒ `v1, v2 := y`, `src := rest` | `9|y1| + 9|y2| + 2|e1| + 2|e2| + 46` |
| `pushIntD v d dst tmp` | `dst := intSyms e ++ d :: dst` | `7|e| + 13` |
| `pushEntry v1 v2 dst tmp` | `dst := entrySyms (e1, e2) ++ dst` | `7|e1| + 7|e2| + 26` |
| `loadNat src v tmp` | `src = natSyms n ++ rs` ⇒ `v := intSyms n ++ R` | `2|e| + 7|n| + 13` |
| `loadInt src v tmp` | `src = intSyms z ++ rs` ⇒ `v := intSyms z ++ R` | `2|e| + 7|z| + 17` |
| `initVars L vs` | every `varLoc v` (`v ∈ vs`) gets `pos :: mark ::` on top (`intSyms 0`, guard) | `2|vs| + 1` |
| `dropVars L vs` | drops each variable value and its guard | `Σ (2|env v| + 6) + 1` |

Host forms (`Lay.hst`): `Lay.popEntry_runs`, `Lay.pushEntry_runs`, `Lay.loadNat_runs`,
`Lay.loadInt_runs`, `Lay.initVars_runs`, `Lay.dropVars_runs`.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL Computability

section Raw

variable {K : Type} [DecidableEq K]

theorem popR_eval' (ρ : List (SProg K)) (k : K) (v : Option Sym) (S : K → List Sym) (x : Sym)
    (L : List Sym) (hS : S k = x :: L) :
    Eval ρ (popR k) ⟨v, S⟩ ⟨some x, Function.update S k L⟩ 1 :=
  (Eval.pop ρ k (fun _ o => o) v S).of_eq (by simp only [hS, List.head?_cons, List.tail_cons]) rfl

theorem pushC_eval' (ρ : List (SProg K)) (k : K) (x : Sym) (v : Option Sym) (S : K → List Sym) :
    Eval ρ (pushC k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 :=
  (Eval.push (Γ := fun _ => Sym) ρ k (fun _ => x) v S).of_eq rfl rfl

/-- Pop the signed number on top of `src` into the variable stack `v` (old value dropped), then
pop the delimiter that follows it. -/
def popInt (src v tmp : K) : SProg K :=
  .seq (dropInt v) (.seq (copyInt src v tmp) (.seq (dropInt src) (popR src)))

theorem popInt_eval {src v tmp : K} (h1 : src ≠ v) (h3 : src ≠ tmp) (h5 : v ≠ tmp) (y e : ℤ)
    (d : Sym) (hd : d.isBit = false) (R rest : List Sym) (S : K → List Sym) (hR : TermOK R)
    (hs : S src = intSyms y ++ d :: rest) (hv : S v = intSyms e ++ R) (r : Option Sym) :
    Eval [] (popInt src v tmp) ⟨r, S⟩
      ⟨some d, Function.update (Function.update S src rest) v (intSyms y ++ R)⟩
      (9 * bitLen y.natAbs + 2 * bitLen e.natAbs + 23) := by
  have hT : TermOK (d :: rest) := TermOK.cons hd _
  have e1 := dropInt_eval [] v r e R S hR hv
  set S1 := Function.update S v R with hS1
  have e2 := copyInt_eval h1 h3 h5 [] R.head? y (d :: rest) S1 hT
    (by rw [hS1, Function.update_of_ne h1, hs])
  set S2 := Function.update S1 v (intSyms y ++ S1 v) with hS2
  have e3 := dropInt_eval [] src (some (sgnSym y)) y (d :: rest) S2 hT
    (by rw [hS2, Function.update_of_ne h1, hS1, Function.update_of_ne h1, hs])
  set S3 := Function.update S2 src (d :: rest) with hS3
  have e4 := popR_eval' [] src (d :: rest).head? S3 d rest (by rw [hS3, Function.update_self])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [hS3, hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all

/-- Pop the entry on top of `src` into the variable stacks `v1`, `v2`. -/
def popEntry (src v1 v2 tmp : K) : SProg K := .seq (popInt src v1 tmp) (popInt src v2 tmp)

theorem popEntry_eval {src v1 v2 tmp : K} (h1 : src ≠ v1) (h2 : src ≠ v2) (h3 : src ≠ tmp)
    (h4 : v1 ≠ v2) (h5 : v1 ≠ tmp) (h6 : v2 ≠ tmp) (y : ℤ × ℤ) (e1 e2 : ℤ)
    (R1 R2 rest : List Sym) (S : K → List Sym) (hR1 : TermOK R1) (hR2 : TermOK R2)
    (hs : S src = entrySyms y ++ rest) (hv1 : S v1 = intSyms e1 ++ R1)
    (hv2 : S v2 = intSyms e2 ++ R2) (r : Option Sym) :
    Eval [] (popEntry src v1 v2 tmp) ⟨r, S⟩
      ⟨some .sep, Function.update (Function.update (Function.update S src rest) v1
        (intSyms y.1 ++ R1)) v2 (intSyms y.2 ++ R2)⟩
      (9 * bitLen y.1.natAbs + 9 * bitLen y.2.natAbs + 2 * bitLen e1.natAbs +
        2 * bitLen e2.natAbs + 46) := by
  have hs' : S src = intSyms y.1 ++ Sym.sep2 :: (intSyms y.2 ++ Sym.sep :: rest) := by
    rw [hs]
    simp [entrySyms]
  have ea := popInt_eval h1 h3 h5 y.1 e1 .sep2 rfl R1 (intSyms y.2 ++ Sym.sep :: rest) S hR1 hs'
    hv1 r
  set S1 := Function.update (Function.update S src (intSyms y.2 ++ Sym.sep :: rest)) v1
    (intSyms y.1 ++ R1) with hS1
  have eb := popInt_eval h2 h3 h6 y.2 e2 .sep rfl R2 rest S1 hR2
    (by rw [hS1, Function.update_of_ne h1, Function.update_self])
    (by rw [hS1, Function.update_of_ne (Ne.symm h4), Function.update_of_ne (Ne.symm h2), hv2])
    (some .sep2)
  refine (Eval.seq ea eb).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [hS1, Function.update_apply]
  split_ifs <;> simp_all

/-- Push delimiter `d`, then a copy of the signed number on `v`, onto `dst`. -/
def pushIntD (v : K) (d : Sym) (dst tmp : K) : SProg K := .seq (pushC dst d) (copyInt v dst tmp)

theorem pushIntD_eval {v dst tmp : K} (h1 : v ≠ dst) (h3 : v ≠ tmp) (h5 : dst ≠ tmp) (d : Sym)
    (e : ℤ) (R : List Sym) (S : K → List Sym) (hR : TermOK R) (hv : S v = intSyms e ++ R)
    (r : Option Sym) :
    Eval [] (pushIntD v d dst tmp) ⟨r, S⟩
      ⟨some (sgnSym e), Function.update S dst (intSyms e ++ d :: S dst)⟩
      (7 * bitLen e.natAbs + 13) := by
  have e1 := pushC_eval' [] dst d r S
  have e2 := copyInt_eval h1 h3 h5 [] r e R (Function.update S dst (d :: S dst)) hR
    (by rw [Function.update_of_ne h1, hv])
  refine (Eval.seq e1 e2).of_eq ?_ (by omega)
  rw [Function.update_idem, Function.update_self]

/-- Push the entry `(env v1, env v2)` onto `dst`. -/
def pushEntry (v1 v2 dst tmp : K) : SProg K := .seq (pushIntD v2 .sep dst tmp) (pushIntD v1 .sep2 dst tmp)

theorem pushEntry_eval {v1 v2 dst tmp : K} (h1 : v1 ≠ dst) (h2 : v2 ≠ dst) (h3 : v1 ≠ tmp)
    (h4 : v2 ≠ tmp) (h5 : dst ≠ tmp) (e1 e2 : ℤ) (R1 R2 : List Sym) (S : K → List Sym)
    (hR1 : TermOK R1) (hR2 : TermOK R2) (hv1 : S v1 = intSyms e1 ++ R1)
    (hv2 : S v2 = intSyms e2 ++ R2) (r : Option Sym) :
    Eval [] (pushEntry v1 v2 dst tmp) ⟨r, S⟩
      ⟨some (sgnSym e1), Function.update S dst (entrySyms (e1, e2) ++ S dst)⟩
      (7 * bitLen e1.natAbs + 7 * bitLen e2.natAbs + 26) := by
  have ea := pushIntD_eval h2 h4 h5 .sep e2 R2 S hR2 hv2 r
  have eb := pushIntD_eval h1 h3 h5 .sep2 e1 R1
    (Function.update S dst (intSyms e2 ++ Sym.sep :: S dst)) hR1
    (by rw [Function.update_of_ne h1, hv1]) (some (sgnSym e2))
  refine (Eval.seq ea eb).of_eq ?_ (by omega)
  rw [Function.update_idem, Function.update_self]
  simp [entrySyms]

/-- Replace the value of the variable stack `v` by the natural on `src`. -/
def loadNat (src v tmp : K) : SProg K :=
  .seq (dropInt v) (.seq (copyBlock src v tmp) (pushC v .pos))

theorem loadNat_eval {src v tmp : K} (h1 : src ≠ v) (h3 : src ≠ tmp) (h5 : v ≠ tmp) (n : ℕ)
    (e : ℤ) (R rs : List Sym) (S : K → List Sym) (hR : TermOK R) (hrs : TermOK rs)
    (hs : S src = natSyms n ++ rs) (hv : S v = intSyms e ++ R) (r : Option Sym) :
    Eval [] (loadNat src v tmp) ⟨r, S⟩
      ⟨some .mark, Function.update S v (intSyms (n : ℤ) ++ R)⟩
      (2 * bitLen e.natAbs + 7 * bitLen n + 13) := by
  have e1 := dropInt_eval [] v r e R S hR hv
  have e2 := copyBlock_eval h1 h3 h5 [] R.head? (encodeNat n) rs (Function.update S v R) hrs
    (by rw [Function.update_of_ne h1, hs]; rfl)
  have e3 := pushC_eval' [] v .pos (some .mark)
    (Function.update (Function.update S v R) v ((encodeNat n).map Sym.bit ++
      Function.update S v R v))
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ (by simp only [bitLen]; omega)
  rw [Function.update_idem, Function.update_idem, Function.update_self, Function.update_self,
    intSyms_natCast]
  rfl

/-- Replace the value of the variable stack `v` by the signed number on `src`. -/
def loadInt (src v tmp : K) : SProg K := .seq (dropInt v) (copyInt src v tmp)

theorem loadInt_eval {src v tmp : K} (h1 : src ≠ v) (h3 : src ≠ tmp) (h5 : v ≠ tmp) (z e : ℤ)
    (R rs : List Sym) (S : K → List Sym) (hR : TermOK R) (hrs : TermOK rs)
    (hs : S src = intSyms z ++ rs) (hv : S v = intSyms e ++ R) (r : Option Sym) :
    Eval [] (loadInt src v tmp) ⟨r, S⟩
      ⟨some (sgnSym z), Function.update S v (intSyms z ++ R)⟩
      (2 * bitLen e.natAbs + 7 * bitLen z.natAbs + 17) := by
  have e1 := dropInt_eval [] v r e R S hR hv
  have e2 := copyInt_eval h1 h3 h5 [] R.head? z rs (Function.update S v R) hrs
    (by rw [Function.update_of_ne h1, hs])
  refine (Eval.seq e1 e2).of_eq ?_ (by omega)
  rw [Function.update_idem, Function.update_self]

end Raw

#assert_std_axioms popR_eval' pushC_eval' popInt_eval popEntry_eval pushIntD_eval pushEntry_eval
  loadNat_eval loadInt_eval

end WP.W9fF
