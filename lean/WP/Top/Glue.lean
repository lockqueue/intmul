import WP.Top.States
import IntMulTM.Framework.Lib.Basic

/-!
# WP.Top.Glue — the root parameters for W9: `c 0 := hdrSyms [hB n, hK0 n, hK n, hK n]`

W0m leaves the schedule parameters as separate `natSyms` blocks on `pb`, `pk`, `pK0`. `W9_multiply`
reads the root parameters `b, K0, k1, k2` (with `k1 = k2 = k`) from `C0`, as `hdrSyms`: each number
followed by `mark`, `b` on top.

`glueProg` builds the header bottom-up on the empty `c 0`:
* push `mark`, copy `pk`;
* push `mark`, copy `pk`;
* push `mark`, copy `pK0`;
* push `mark`, copy `pb`.

Each `copyBlock` uses the spare `xs 0` as its temporary and restores it. The sources are unchanged.
**`glue_eval`**: exact, only `c 0` changes, cost `glueCost n = 14·|k| + 7·|K0| + 7·|b| + 32`.
-/

namespace WP.Top

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts

/-- **The parameter glue.** -/
def glueProg : SProg GW :=
  .seq (pushC (.c 0) .mark) (.seq (copyBlock .pk (.c 0) (.xs 0))
    (.seq (pushC (.c 0) .mark) (.seq (copyBlock .pk (.c 0) (.xs 0))
      (.seq (pushC (.c 0) .mark) (.seq (copyBlock .pK0 (.c 0) (.xs 0))
        (.seq (pushC (.c 0) .mark) (copyBlock .pb (.c 0) (.xs 0))))))))

/-- Cost of the glue. -/
def glueCost (n : ℕ) : ℕ :=
  14 * bitLen (W8.hK n) + 7 * bitLen (W8.hK0 n) + 7 * bitLen (W8.hB n) + 32

theorem push_c0 (S0 : GW → List Sym) (Y : List Sym) (v : Option Sym) :
    Eval [] (pushC (GW.c 0) Sym.mark) ⟨v, Function.update S0 (GW.c 0) Y⟩
      ⟨v, Function.update S0 (GW.c 0) (Sym.mark :: Y)⟩ 1 := by
  refine (Eval.push [] (GW.c 0) (fun _ => Sym.mark) v (Function.update S0 (GW.c 0) Y)).of_eq ?_
    rfl
  show (⟨v, Function.update (Function.update S0 (GW.c 0) Y) (GW.c 0)
    (Sym.mark :: Function.update S0 (GW.c 0) Y (GW.c 0))⟩ : SSt GW) = _
  rw [Function.update_self, Function.update_idem]

theorem copy_c0 (S0 : GW → List Sym) (Y : List Sym) (v : Option Sym) {src : GW}
    (hsrc : src ≠ GW.c 0) (hsx : src ≠ GW.xs 0) (val : ℕ) (hS : S0 src = natSyms val) :
    Eval [] (copyBlock src (GW.c 0) (GW.xs 0)) ⟨v, Function.update S0 (GW.c 0) Y⟩
      ⟨some Sym.mark, Function.update S0 (GW.c 0) (natSyms val ++ Y)⟩ (7 * bitLen val + 7) := by
  have h := copyBlock_eval hsrc hsx (by decide : GW.c 0 ≠ GW.xs 0) [] v (encodeNat val) []
    (Function.update S0 (GW.c 0) Y) TermOK.nil
    (by rw [Function.update_of_ne hsrc, hS, List.append_nil]; rfl)
  refine h.of_eq ?_ rfl
  rw [Function.update_self, Function.update_idem]
  rfl

theorem hdr4 (b K0 k : ℕ) :
    hdrSyms [b, K0, k, k] =
      natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: (natSyms k ++ Sym.mark ::
        (natSyms k ++ [Sym.mark]))) := by
  simp [hdrSyms]

/-- **The glue, exact.** -/
theorem glue_eval (S : GW → List Sym) (n : ℕ) (hb : S .pb = natSyms (W8.hB n))
    (hk : S .pk = natSyms (W8.hK n)) (hK0 : S .pK0 = natSyms (W8.hK0 n)) (hc : S (.c 0) = [])
    (v : Option Sym) :
    Eval [] glueProg ⟨v, S⟩ ⟨some .mark, Function.update S (.c 0) (rootHdr n)⟩ (glueCost n) := by
  have hS : S = Function.update S (GW.c 0) [] := by
    rw [← hc, Function.update_eq_self]
  have e1 := push_c0 S [] v
  have e2 := copy_c0 S [Sym.mark] v (src := .pk) (by decide) (by decide) _ hk
  have e3 := push_c0 S (natSyms (W8.hK n) ++ [Sym.mark]) (some .mark)
  have e4 := copy_c0 S (Sym.mark :: (natSyms (W8.hK n) ++ [Sym.mark])) (some .mark) (src := .pk)
    (by decide) (by decide) _ hk
  have e5 := push_c0 S (natSyms (W8.hK n) ++ Sym.mark :: (natSyms (W8.hK n) ++ [Sym.mark]))
    (some .mark)
  have e6 := copy_c0 S (Sym.mark :: (natSyms (W8.hK n) ++ Sym.mark :: (natSyms (W8.hK n) ++
    [Sym.mark]))) (some .mark) (src := .pK0) (by decide) (by decide) _ hK0
  have e7 := push_c0 S (natSyms (W8.hK0 n) ++ Sym.mark :: (natSyms (W8.hK n) ++ Sym.mark ::
    (natSyms (W8.hK n) ++ [Sym.mark]))) (some .mark)
  have e8 := copy_c0 S (Sym.mark :: (natSyms (W8.hK0 n) ++ Sym.mark :: (natSyms (W8.hK n) ++
    Sym.mark :: (natSyms (W8.hK n) ++ [Sym.mark])))) (some .mark) (src := .pb) (by decide)
    (by decide) _ hb
  have e := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 e8))))))
  rw [← hS] at e
  refine e.of_eq ?_ ?_
  · rw [rootHdr, hdr4]
  · unfold glueCost
    omega

#assert_std_axioms push_c0 copy_c0 hdr4 glue_eval

end WP.Top
