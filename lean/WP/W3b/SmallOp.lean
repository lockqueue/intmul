import WP.W3b.Small
import WP.W3b.Mul3
import WP.W3b.Div3

/-!
# WP.W3b.SmallOp — `W3_smallOpInt` (`×2`, `×3`, exact `÷2`, exact `÷3`)

One cost constant `C = 20` for all four compile-time operations:

| op | program | scratch | proved cost |
|---|---|---|---|
| `mul2` | `mul2Prog` | 0 | `5` |
| `div2` | `div2Prog` | 0 | `5` |
| `mul3` | `mul3Prog` | 1 | `6·|z| + 19` |
| `div3` | `div3Prog` | 1 | `7·|z| + 9` |
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem W3_smallOpInt_holds : W3_smallOpInt := by
  refine ⟨20, fun op => ?_⟩
  cases op with
  | mul2 =>
    refine ⟨0, Reg2, fun _ => (), mul2Prog, Nat.zero_le _, inferInstance, ⟨(none, none)⟩,
      mul2Prog_closed, ?_⟩
    intro z rx S hrx _ hx
    exact Triple.cost_mono (mul2_runs z rx hrx S hx) (by omega)
  | mul3 =>
    refine ⟨1, M3R, fun _ => (), mul3Prog, by decide, inferInstance, ⟨(none, none, 0)⟩,
      mul3Prog_closed, ?_⟩
    intro z rx S hrx _ hx
    exact Triple.cost_mono (mul3_runs z rx hrx S hx) (by omega)
  | div2 =>
    refine ⟨0, Reg2, fun _ => (), div2Prog, Nat.zero_le _, inferInstance, ⟨(none, none)⟩,
      div2Prog_closed, ?_⟩
    intro z rx S hrx hok hx
    exact Triple.cost_mono (div2_runs z hok rx hrx S hx) (by omega)
  | div3 =>
    refine ⟨1, D3R, fun _ => (), div3Prog, by decide, inferInstance, ⟨(none, none, 0, false)⟩,
      div3Prog_closed, ?_⟩
    intro z rx S hrx hok hx
    exact Triple.cost_mono (div3_runs z hok rx hrx S hx) (by omega)

#assert_std_axioms W3_smallOpInt_holds

end TMFw.W3b
