import WP.W9a.Pipeline
import WP.W9a.Sweep
import WP.W9a.Level
import WP.W9a.Ret

/-!
# WP.W9a.Final — the W9a results with the proved combinators discharged

`W9_sweep`, `W9_level`, `W9_retFlip` (this package) and `W9_retMark` (`Contracts.W9.Ret`, `w9_retMark`)
are proved. So the level programs and the pipeline depend only on the three node kernels, at one
shared `Mul`.
-/

namespace WP.W9a

open TMFw TMFw.Contracts TMFw.Contracts.W9

theorem W9_preLevelProg_of_kernel (Mul : ℕ → ℕ) (hK : W9_preNode Mul) : W9_preLevelProg Mul :=
  W9_preLevelProg_holds Mul W9_sweep_holds w9_retMark hK

theorem W9_leafLevelProg_of_kernel (Mul : ℕ → ℕ) (hK : W9_leafFFT Mul) : W9_leafLevelProg Mul :=
  W9_leafLevelProg_holds Mul W9_sweep_holds hK

theorem W9_postLevelProg_of_kernel (Mul : ℕ → ℕ) (hK : W9_postNode Mul) : W9_postLevelProg Mul :=
  W9_postLevelProg_holds Mul W9_sweep_holds W9_retFlip_holds hK

/-- **The pipeline from the three node kernels** (one shared `Mul`). -/
theorem W9_pipeline_of_kernels (Mul : ℕ → ℕ) (hPre : W9_preNode Mul) (hLeaf : W9_leafFFT Mul)
    (hPost : W9_postNode Mul) : W9_pipeline Mul :=
  W9_pipeline_of_levels_holds Mul W9_level_holds (W9_preLevelProg_of_kernel Mul hPre)
    (W9_leafLevelProg_of_kernel Mul hLeaf) (W9_postLevelProg_of_kernel Mul hPost)

#assert_std_axioms W9_preLevelProg_of_kernel W9_leafLevelProg_of_kernel W9_postLevelProg_of_kernel
  W9_pipeline_of_kernels

end WP.W9a
