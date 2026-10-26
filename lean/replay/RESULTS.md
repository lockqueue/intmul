# Results of the `comparator` runs

All runs use `configs/positive.json` or the corresponding file in `configs/controls/`, i.e. the same `theorem_names`, `permitted_axioms` and `enable_nanoda: true`; only the challenge or the solution module differs. "Output" is the decisive line printed by `comparator`; the exit status of the `systemd-run` unit equals that of `comparator`. Wall time and peak memory are those reported by systemd for the whole unit (`lake build`, `lean4export`, `comparator`, `nanoda`).

| Run | Challenge module | Solution module | Expected | Output | Exit | Wall | Peak memory |
|---|---|---|---|---|---|---|---|
| positive run | `Replay.Challenge` | `SubNLogN.Assembly.ChallengeHeadline` | accepted | `Nanoda kernel accepts the solution` / `Lean default kernel accepts the solution` / `Your solution is okay!` | 0 | 25min 44.550s | 17.5G |
| S0 (positive control: byte-identical copy of `Challenge.lean` under another module name) | `Replay.Controls.S0_IdenticalCopy` | `SubNLogN.Assembly.ChallengeHeadline` | accepted | `Nanoda kernel accepts the solution` / `Lean default kernel accepts the solution` / `Your solution is okay!` | 0 | 24min 6.705s | 17.4G |
| S1: `2 ^ 46` → `2 ^ 45` | `Replay.Controls.S1_Exp45` | `SubNLogN.Assembly.ChallengeHeadline` | rejected: statement comparison | `Const does not match between challenge and target 'SubNLogN.Challenge.IntMulSubNLogN'` | 1 | 3min 48.152s | 10.8G |
| S2: conjunct `(∀ k, Finite (M.tm.Γ k))` deleted | `Replay.Controls.S2_NoFinite` | `SubNLogN.Assembly.ChallengeHeadline` | rejected: statement comparison | `Const does not match between challenge and target 'SubNLogN.Challenge.IntMulSubNLogN'` | 1 | 3min 42.930s | 10.8G |
| S3: `≤` → `<` | `Replay.Controls.S3_StrictLt` | `SubNLogN.Assembly.ChallengeHeadline` | rejected: statement comparison | `Const does not match between challenge and target 'SubNLogN.Challenge.IntMulSubNLogN'` | 1 | 3min 48.213s | 10.8G |
| P1: proof `sorry` | `Replay.Challenge` | `Replay.Controls.P1_Sorry` | rejected: permitted-axiom check | `Illegal axiom detected: 'sorryAx'` | 1 | 10.995s | 673.5M |
| P2: proof by an added axiom | `Replay.Challenge` | `Replay.Controls.P2_AddedAxiom` | rejected: permitted-axiom check | `Illegal axiom detected: 'Replay.Controls.P2.intMul_challenge_axiom'` | 1 | 10.077s | 568M |
| P3: genuine proof plus a `native_decide` step | `Replay.Challenge` | `Replay.Controls.P3_NativeDecide` | rejected: permitted-axiom check | `Illegal axiom detected: 'SubNLogN.Assembly.intMul_challenge._native.native_decide.ax_1_1'` | 1 | 3min 40.870s | 11.2G |
| P4: extra axiom `False` used through a lemma | `Replay.Challenge` | `Replay.Controls.P4_ExtraAxiomTransitive` | rejected: permitted-axiom check | `Illegal axiom detected: 'Replay.Controls.P4.oracle'` | 1 | 10.018s | 567.4M |
| P5 (additional): statement constant re-declared as `True` in the solution | `Replay.Challenge` | `Replay.Controls.P5_DefinitionSwap` | rejected: statement comparison | `Const does not match between challenge and target 'SubNLogN.Challenge.IntMulSubNLogN'` | 1 | 9.516s | 556.1M |

Order of the checks inside `comparator`: statement comparison, then permitted-axiom check, then `nanoda`, then the Lean kernel; a run stops at the first failing check, so each rejected control has exactly one cause. The three altered statements and `P5` fail the statement comparison with a message naming the statement constant `SubNLogN.Challenge.IntMulSubNLogN` itself (its definition differs; every other constant of the copied file matches). The four altered proofs are accepted by the Lean kernel (and would pass `leanchecker`); they fail the permitted-axiom check. The positive control `S0` is accepted exactly like the positive run, so the three statement rejections are due to the edits and not to re-elaborating the statement file.

## `leanchecker` replay of every module (summary)

| Prefix | Modules replayed | Exit status | Wall time | Peak RSS | Workers |
|---|---|---|---|---|---|
| `AxiomCheck` | 1 / 1 | 0 | 0:21.30 | 3.7 GB | 5 |
| `LevelSync` | 5 / 5 | 0 | 0:29.66 | 10.7 GB | 5 |
| `Contracts` | 29 / 29 | 0 | 0:51.75 | 16.9 GB | 5 |
| `IntMulTM` | 51 / 51 | 0 | 1:11.06 | 19.6 GB | 5 |
| `IntMul` | 30 / 30 | 0 | 1:05.97 | 19.5 GB | 5 |
| `WP` | 833 / 833 | 0 | 14:18.23 | 21.1 GB | 5 |
| `SubNLogN` | 1,062 / 1,062 | 0 | 46:03.42 | 30.1 GB | 3 |
| total | 2,011 / 2,011 | | | | |

`--fresh` runs: `SubNLogN.Assembly.ChallengeHeadline` (874,850 constants of 12,755 modules) exit 0, 51:12, 15.4 GB; `IntMulTM.Headline` (555,268 constants of 6,695 modules) exit 0, 16:03, 4.9 GB.
