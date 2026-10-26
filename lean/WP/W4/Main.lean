import WP.W4.Contract
import WP.W4.Riff

/-!
# WP.W4.Main — `W4_transpose oi oo` for all orientations

The program is `transposeProg oi oo = transposeProgP (riffPass X Y Z U) oi oo`:
* `cmpNum a b`; if `a > b`: `b` perfect-unshuffle passes, else `a` perfect-riffle passes;
* each pass is linear in `|blk|`; the pass counter is a binary copy of `min a b`;
* input/output transfers convert between `oi`/`oo` and the passes' `.down` block on `X`.

Cost constant `64`; scratch stacks `4`; registers `CReg`.
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts

/-- The transpose program. -/
def transposeProg (oi oo : Orient) : Prog L44 (fun _ => Sym) CReg :=
  transposeProgP (riffPass (.inr 0) (.inr 1) (.inr 2) (.inr 3)) oi oo

theorem riffOK : RiffOK (riffPass (.inr 0 : L44) (.inr 1) (.inr 2) (.inr 3)) := by
  refine ⟨riffPass_closed _ _ _ _, fun N L hN l S X0 hl hs hX => ?_⟩
  obtain ⟨⟨Y0, hY⟩, ⟨Z0, hZ⟩, ⟨U0, hU⟩⟩ := hs
  exact riffPass_spec (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [] N
    L l hl hN S X0 Y0 Z0 U0 hX hY hZ hU

/-- **W4.transpose, all orientations.** -/
theorem W4_transpose_holds : ∀ oi oo : Orient, W4_transpose oi oo :=
  fun oi oo => w4_transpose_of_riff riffOK oi oo

/-- Used by W9b. -/
theorem W4_transpose_down_up : W4_transpose .down .up := W4_transpose_holds _ _

/-- Used by W9e. -/
theorem W4_transpose_down_down : W4_transpose .down .down := W4_transpose_holds _ _

#assert_std_axioms riffOK W4_transpose_holds W4_transpose_down_up W4_transpose_down_down

end TMFw.W4
