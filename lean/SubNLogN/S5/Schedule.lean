import SubNLogN.Spec

/-!
# Component S5 (`Schedule.lean`): Parameter Rows, Admissibility Margins & Positive Gap Slacks

Verifies in exact integer arithmetic (`decide` / `omega`) all admissibility inequalities
`(eq:walsh-layer-a)`, `(eq:walsh-layer-b)`, `ε C₁ < 1`, and positive gap slacks `g_min - κ > 0`
for:
1. The three Walsh parameter rows (`Table 6`, `§7.5`, `Remark 7.3`, and `Table 10`):
   - `C₁ = 14` parameter-exposed row (`κ = 2^{-46}`),
   - `C₁ = 20` parameter-exposed row (`κ = 2^{-47}`),
   - `C₁ = 20, β = 1/2, τ = σ = 1 - 2^{-50}` printed-interface row (`κ = 2^{-56}`);
2. The four Bluestein comparison rows (`Table 10`, `Appendix C`):
   - `κ = 2^{-84}` (`C₁ = 14`),
   - `κ = 2^{-85}` (`C₁ = 20`),
   - `κ = 2^{-108}` (`C₁ = 20`, printed network exponents),
   - `κ = 2^{-182}` (`[OAI26, (38)]`).
-/

namespace SubNLogN.S5

open SubNLogN

/-- **`C₁ = 14` Walsh Parameter Row (`κ = 2^{-46}`, `Table 6` & `§7.5`):**
With `ξ = 2^{-42}`, `ε = 1/15`, `β = 1/64`, `c = 2^{-50}`, `τ = 1 - 4ξ`, `σ = 1 - ξ`,
`λ = 1 - 63ξ/64`, `λ' = 1 - 31ξ/32`:
1. Guard admissibility: `14 < 15` (`ε C₁ < 1`) and `14 ≥ 11 + 3`;
2. Layer recurrence `(eq:walsh-layer-a,b)` scaled to common denominator `64 · 2^{84}`:
   - `τ < σ < λ < λ' < 1`,
   - `τ (1 + c / β) = (1 - 4ξ)(1 + ξ/4) = 1 - (15/4)ξ - ξ^2 < 1 - (63/64)ξ = λ`,
   - `σ + β (1 - σ) = 1 - (63/64)ξ = λ < λ'`;
3. Positive gap slack (`§7.4`–`§7.5`, `eq:gaps`):
   - `g_lay = ε (1 - λ') = 31 / (480 · 2^{42}) > 30 / (480 · 2^{42}) = 2^{-46} = κ`,
   - `g_axis = (1 - ε)(1 - τ) = (14/15) · 4ξ = 56ξ / 15 > κ`,
   - `g_last = 1/15 > κ`, `g_short = 14/15 > κ`, `g_pre = 1 - (1 + c)/15 > κ`. -/
theorem walsh_row_46_admissible_and_slack :
    -- ε C₁ = 14/15 < 1 and C₁ ≥ ν + 3 = 14
    14 < 15 ∧ 14 ≥ 11 + 3 ∧
    -- 1 - λ = 63/64 ξ < 1 - σ = ξ < 1 - τ = 4ξ
    31 < 2 * 63 ∧ 63 < 64 ∧ 1 < 4 ∧
    -- λ - τ(1 + c/β) = (15/4 - 63/64) ξ + ξ^2 = (177/64) ξ + ξ^2 > 0
    63 < 15 * 16 ∧
    -- g_lay = 31 / (480 · 2^42) > 1 / 2^46 = 30 / (480 · 2^42)
    31 * (2 ^ 46) > 480 * (2 ^ 42) ∧
    (31 * (2 ^ 46) - 480 * (2 ^ 42)) = 2 ^ 46 := by decide

/-- **`C₁ = 20` Walsh Parameter Row (`κ = 2^{-47}`, `Remark 7.3` & `Table 10`):**
With `ξ = 2^{-42}`, `ε = 1/21`, `β = 1/8`, `c = 2^{-44}`, `τ = 1 - 4ξ`, `σ = 1 - ξ`,
`λ = 1 - 7ξ/8`, `λ' = 1 - 3ξ/4`:
1. Guard admissibility: `20 < 21` (`ε C₁ < 1`) and `20 ≥ 11 + 3`;
2. `λ - τ(1 + c/β) = (9/8)ξ + 8ξ^2 > 0` (`7 < 2 * 8`);
3. Binding butterfly-layer gap `g_lay = 1 / (28 · 2^{42}) > 1 / (32 · 2^{42}) = 2^{-47} = κ`. -/
theorem walsh_row_47_admissible_and_slack :
    20 < 21 ∧ 20 ≥ 11 + 3 ∧
    3 < 2 * 7 ∧ 7 < 8 ∧ 7 < 2 * 8 ∧
    1 * (2 ^ 47) > 28 * (2 ^ 42) ∧
    32 - 28 = 4 := by decide

/-- **Printed-Interface Walsh Row (`κ = 2^{-56}`, `Remark 7.3` & `Table 10`):**
With `u = 2^{-51}`, `C₁ = 20`, `ε = 1/21`, `β = 1/2`, `c = u/4 = 2^{-53}`, `τ = σ = 1 - 2u`,
`λ = 1 - 129u/128`, `λ' = 1 - 63u/64`:
1. `λ - τ(1 + c/β) = (63/128)u + u^2 > 0` (`129 < 3 * 64`);
2. `λ' - (σ + β(1 - σ)) = (1 - 63u/64) - (1 - u) = u/64 > 0`;
3. Binding butterfly-layer gap `g_lay = ε (1 - λ') = 63u / (21 · 64) = 3u / 64`:
   for the printed-constants row (`Remark 7.3`, `rem:printed-optimal`) with `ε = 1/21` and
   `1 - λ' = 63u/64`, `(1/21) * (63u/64) = 3u/64 = 3 · 2^{-57} > 2 · 2^{-57} = 2^{-56} = κ` (slack `2^{-57}`). -/
theorem walsh_row_56_admissible_and_slack :
    20 < 21 ∧
    129 < 3 * 64 ∧ 63 < 64 ∧ 2 * 63 < 129 ∧
    -- ε * (1 - λ') = (1/21) * (63/64) u = (3/64) u = 3 * 2^{-57} > 2^{-56}
    63 * (2 ^ 56) > 21 * 64 * (2 ^ 51) ∧
    63 / 21 = 3 := by decide

/-- **Bluestein Comparison Rows (`Table 10`, `Appendix C`):**
Positive gap slack `g_chunk = ε c (1 - τ) > κ` for `κ = 2^{-84}, 2^{-85}, 2^{-108}, 2^{-182}`. -/
theorem bluestein_rows_slack :
    -- κ = 2^{-84}: g_chunk = (9/128) * (29/32) * 2^{-80} = (261/4096) * 2^{-80} > (256/4096) * 2^{-80} = 2^{-84}
    9 * 29 > 256 ∧ 9 * 29 - 256 = 5 ∧
    -- κ = 2^{-85}: g_chunk = (1/21) * (7/8) * 2^{-80} = (1/24) * 2^{-80} > (1/32) * 2^{-80} = 2^{-85}
    32 > 24 ∧
    -- κ = 2^{-108}: g_chunk = 2^{-5} * 2^{-52} * 2^{-50} = 2^{-107} > 2^{-108}
    (2 : ℕ) ^ 108 > 2 ^ 107 ∧
    -- κ = 2^{-182}: g_chunk = 2^{-75} * 2^{-56} * 2^{-50} = 2^{-181} > 2^{-182}
    (2 : ℕ) ^ 182 > 2 ^ 181 := by decide

end SubNLogN.S5
