import WP.F9.MulLeafRun

/-!
# Evidence run: the W9 multiplier `WP.F9.Top.P9C` (v3) on `3 · 5`

`WP.F9.MulLeafRun.rowM b K0 k A B` runs the multiplier on the leaf-only chain of size `2^K0` with the indexed
runner and returns `(every stack = W9_multiply's post-state, snapshot value = A·B, steps)`. The smoke module
runs `13 · 11` (2-point transform); this run is the 4-point transform `3 · 5` (`b = K0 = k = 2`). It takes about
two minutes in the interpreter, so it is a separate target.
-/

#eval WP.F9.MulLeafRun.rowM 2 2 2 3 5
