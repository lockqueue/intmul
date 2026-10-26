# Kernel replay and independent checking of the headline theorems

This directory records how the compiled development was re-checked by tools other than the elaborator
that produced it, and how to repeat those checks. We ran three kinds of checks on the compiled
(`lake build`) tree:

1. **Declaration replay with `leanchecker`.** `leanchecker` is part of the Lean toolchain since v4.28
   (it is the former stand-alone `lean4checker`). It re-reads the compiled `.olean` files and re-submits every
   declaration to the Lean kernel, independently of the elaborator, so it detects any environment manipulation
   that bypassed the kernel. With `--fresh` it rebuilds the complete environment of a module, including all of
   Mathlib the module imports, from an empty kernel environment.
2. **Statement comparison, axiom check and kernel replay with `comparator`.** `comparator` exports the proof
   of the headline theorem with `lean4export`, checks that the exported theorem has exactly the type stated in
   the frozen statement file `SubNLogN/Challenge.lean` (including the definitions of every constant the
   statement depends on), checks that the proof depends on no axiom other than `propext`, `Quot.sound` and
   `Classical.choice`, and replays the exported proof in the Lean kernel.
3. **Replay in an independent kernel.** `comparator` hands the same export to `nanoda`, a type checker for
   Lean 4 written in Rust that shares no code with Lean. We also ran `nanoda` by itself on the same export file.

`leanchecker` is not an axiom check: axioms, including `sorryAx`, are replayed as axioms. Which axioms a
theorem actually uses is shown by `#print axioms` (`PrintAxioms.lean`) and enforced by `comparator`'s
`permitted_axioms` check. Negative controls (altered statements and altered proofs) were run through the
same `comparator` pipeline to confirm that it rejects what it must reject (`RESULTS.md`).

## Versions

| Tool | Source | Version used |
|---|---|---|
| Lean, `lake`, `leanchecker` | `lean-toolchain`: `leanprover/lean4:v4.33.1` | Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Mathlib | pinned in `lake-manifest.json` | commit `0df444a360eaa60ab8c11dca51a86af692955474` |
| `comparator` | https://github.com/leanprover/comparator | tag `v4.33.0`, commit `3927ad383f208ae977c340a91c48ac9b497d2097`, built with Lean 4.33.1 (see below) |
| `lean4export` | https://github.com/leanprover/lean4export | tag `v4.33.0`, commit `15f6055e299ad5b89345e533cc2192f4cc00f659` (the revision pinned by `comparator`), built with Lean 4.33.1; export format 3.1.0 |
| `landrun` (the sandbox `comparator` runs `lake` and `lean4export` in) | https://github.com/Zouuup/landrun | commit `ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a`, `landrun version 0.1.18`, built with Go 1.26.8; Linux 7.1 with Landlock |
| `nanoda` | https://github.com/ammkrn/nanoda_lib | commit `37cb87b7e6cd6862ef2bd121faa9f4604f59fe96`, crate version 0.4.29, built with `cargo build --release` (rustc 1.99.1) |

Machine used for the timings below: 64-thread AMD EPYC 7B13, 118 GB RAM, Linux 7.1.

### Building the tools

* `comparator` and `lean4export`: clone `comparator` at tag `v4.33.0`, replace the content of its
  `lean-toolchain` by `leanprover/lean4:v4.33.1` (so that the `lean4export` it builds reads this project's
  `.olean` files), and run `lake build lean4export comparator` inside the clone. The binaries are
  `.lake/build/bin/comparator` and `.lake/packages/lean4export/.lake/build/bin/lean4export`.
  `comparator`'s own test suite (`lean --run runtests.lean`, 14 tests) passes with this build and the real
  `landrun` (`logs/comparator_selftests.txt`).
* `landrun`: `go build -o landrun cmd/landrun/main.go` inside a clone of the repository.
* `nanoda`: `cargo build --release` inside a clone of the repository; the binary is `target/release/nanoda_bin`.

All commands below are run from the project root after `lake exe cache get && lake build` (see the top-level
`README.md`). The `Replay` library (this directory's `Replay/` folder, declared by the five lines of
`lakefile_addition.toml` appended to `lakefile.toml`) only contains the challenge module and the controls; it
is not imported by anything in the development.

## 1. Declaration replay with `leanchecker`

### 1.1 Every module against its imports

`leanchecker <prefix>…` replays, for every module whose name starts with one of the prefixes, the module's
own declarations into the environment formed by its imports (one task per module; the number of concurrent
tasks is bounded by `LEAN_NUM_THREADS`, and each task needs about 6 GB of memory because it imports a
Mathlib-sized environment). The seven libraries of the project were covered by prefix; `-v` prints
`replaying <module>` for every module checked.

```
LEAN_NUM_THREADS=5 lake env leanchecker -v AxiomCheck
LEAN_NUM_THREADS=5 lake env leanchecker -v LevelSync
LEAN_NUM_THREADS=5 lake env leanchecker -v Contracts
LEAN_NUM_THREADS=5 lake env leanchecker -v IntMulTM
LEAN_NUM_THREADS=5 lake env leanchecker -v IntMul
LEAN_NUM_THREADS=5 lake env leanchecker -v WP
LEAN_NUM_THREADS=3 lake env leanchecker -v SubNLogN
```

| Prefix | Modules | Exit status | Wall time | Peak RSS |
|---|---|---|---|---|
| `AxiomCheck` | 1 | 0 | 0:21 | 3.8 GB |
| `LevelSync` | 5 | 0 | 0:30 | 11.0 GB |
| `Contracts` | 29 | 0 | 0:52 | 17.3 GB |
| `IntMulTM` | 51 | 0 | 1:11 | 20.1 GB |
| `IntMul` | 30 | 0 | 1:06 | 19.9 GB |
| `WP` | 833 | 0 | 14:18 | 21.7 GB |
| `SubNLogN` | 1,062 | 0 | 46:03 | 31.5 GB |

(2,011 modules in total; `logs/R1c_<prefix>.txt` lists every module replayed.) A rejected declaration would be
reported as `leanchecker found a problem in <module>` followed by the kernel error, with a non-zero exit
status; no such line occurs.

### 1.2 The complete environment of each headline module, from an empty kernel

`--fresh` imports the module and replays every constant of the resulting environment — all imported modules
included — into an empty kernel environment. It is single-threaded and accepts one module per invocation.

```
lake env leanchecker --fresh -v SubNLogN.Assembly.ChallengeHeadline
lake env leanchecker --fresh -v IntMulTM.Headline
```

| Module | Imported modules | Constants replayed | Exit status | Wall time | Peak RSS |
|---|---|---|---|---|---|
| `SubNLogN.Assembly.ChallengeHeadline` | 12,755 (of which Mathlib 8,312, SubNLogN 1,017, WP 642) | 874,850 (590,131 theorems, 253,569 definitions, 7,625 inductive types, …) | 0 | 51:12 | 15.4 GB |
| `IntMulTM.Headline` | 6,695 (of which Mathlib 3,385, WP 638) | 555,268 (349,155 theorems, 183,174 definitions, 5,339 inductive types, …) | 0 | 16:03 | 4.9 GB |

The only output of a successful run is `replaying <module> with --fresh`. The module and constant counts come
from `lake env lean --run replay/EnvStats.lean SubNLogN.Assembly.ChallengeHeadline IntMulTM.Headline`
(`logs/env_stats.txt`); `Lean.Environment.replay` skips `unsafe` and `partial` constants (774 + 4,878 and
739 + 4,243 respectively) and checks constructors and recursors against the ones the kernel generates.

### 1.3 Axioms

```
lake env lean replay/PrintAxioms.lean
```

prints `'SubNLogN.Assembly.intMul_challenge' depends on axioms: [propext, Classical.choice, Quot.sound]` and
`'IntMulTM.intMul_TM2_nlogn' depends on axioms: [propext, Classical.choice, Quot.sound]` (`logs/print_axioms.txt`).

## 2. `comparator`: statement comparison, axiom check, replay in two kernels

`comparator` needs a *challenge* module that states the theorem with its proof left open. Ours is
`Replay/Challenge.lean`; it imports the frozen statement file unchanged and adds one declaration:

```lean
import SubNLogN.Challenge

theorem SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN := sorry
```

The *solution* module is the shipped `SubNLogN.Assembly.ChallengeHeadline`. Configuration
(`configs/positive.json`):

```json
{
    "challenge_module": "Replay.Challenge",
    "solution_module": "SubNLogN.Assembly.ChallengeHeadline",
    "theorem_names": ["SubNLogN.Assembly.intMul_challenge"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": true
}
```

Invocation, as prescribed by the `comparator` README (`systemd-run` with `RestrictAddressFamilies=~AF_UNIX`;
we used `--wait --pipe` rather than `--pty` because the run was not interactive):

```
systemd-run --user --wait --pipe \
  --property=RestrictAddressFamilies=~AF_UNIX --property=LimitSTACK=16G \
  -E PATH="$PATH" -E HOME="$HOME" \
  -E COMPARATOR_LANDRUN=<path to landrun> \
  -E COMPARATOR_LEAN4EXPORT=<path to lean4export> \
  -E COMPARATOR_NANODA=<path to nanoda_bin> \
  --working-directory "$PWD" -- \
  /bin/bash -c 'lake env <path to comparator> replay/configs/positive.json'
```

**Stack limit.** `nanoda` type-checks serially on its main thread, and `comparator` v4.33.0 generates
`nanoda`'s configuration itself (no thread option). With the default 8 MB stack, `nanoda` aborts on this
export with `thread 'main' has overflowed its stack` / `fatal runtime error: stack overflow, aborting`, which
`comparator` reports as `Nanoda kernel rejected the solution` and a non-zero exit status, although the Lean
kernel step still succeeds (`logs/R2_positive_attempt1_default8MBstack.txt`). The `LimitSTACK=16G` property
(equivalently `ulimit -s 16777216` in the shell that runs `comparator`) raises the limit; we did not search for
the smallest sufficient value.

What `comparator` does: it builds the challenge module with `lake build` inside a `landrun` sandbox (read-only
file system, write access only to `.lake`); exports from it with `lean4export` the theorem, the permitted
axioms, the kernel-primitive constants (`Nat.add`, …, `String.ofList`, `Char.ofNat`, `List`, `eagerReduce`)
and, because `nanoda` is enabled, `Nat`, `String`, `String.mk`, `Char`, `Quot`, `Quot.mk`, `Quot.lift`,
`Quot.ind`; repeats build and export for the solution module; checks that the theorem's name, universe
parameters and type coincide in both exports and that every constant reachable from the statement has an
identical definition in both; checks that the solution's proof reaches no axiom outside `permitted_axioms`;
pipes the solution export to `nanoda` (permitted axioms as above, `unpermitted_axiom_hard_error: true`, `Nat`
and `String` kernel extensions); and finally replays the whole solution export into a fresh Lean kernel
environment. Both `lake build` steps are no-ops on a built tree.

Expected output of a successful run (`logs/R2_positive.txt`), in this order:

```
Building Replay.Challenge
Build completed successfully (1227 jobs).
Exporting #[Nat, String, …, SubNLogN.Assembly.intMul_challenge, propext, Quot.sound, Classical.choice, …] from Replay.Challenge
Building SubNLogN.Assembly.ChallengeHeadline
Build completed successfully (10447 jobs).
Exporting #[…] from SubNLogN.Assembly.ChallengeHeadline
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

exit status 0; wall time 25:45 (about 4 min export, 9 min `nanoda`, 12 min Lean kernel replay), peak memory
17.5 GB. Any statement mismatch (`Challenge and solution theorem statement do not match: '…'` or
`Const does not match between challenge and target '<constant>'`), any non-permitted axiom
(`Illegal axiom detected: '<axiom>'`) or any kernel rejection stops the run with a non-zero exit status before
`Your solution is okay!`.

### The export file, and `nanoda` on its own

The export that both kernels check can be written to a file with exactly the constant list `comparator` uses:

```
lake env <path to lean4export> SubNLogN.Assembly.ChallengeHeadline -- \
  Nat String String.mk Char Quot Quot.mk Quot.lift Quot.ind SubNLogN.Assembly.intMul_challenge \
  propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq \
  Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce \
  > intMul_challenge.ndjson
```

The file is 1,961,472,978 bytes (36,388,950 lines; SHA-256
`13546e52adb30ab15ef67f81a7cbb2fc798218b379c7fa20990cab3f075a6dd9`); its first line records the exporter
(`lean4export 3.1.0`), the format version (3.1.0) and Lean's version and commit. Then, from the directory
containing the file,

```
ulimit -s 16777216 && <path to nanoda_bin> replay/configs/nanoda_intMul_challenge.json
```

prints `Checked 124418 declarations with no typechecker errors` and exits with status 0 (9:04 wall time,
7.4 GB peak RSS; `logs/nanoda_standalone.txt`). The dependency closure of `intMul_challenge` therefore
consists of 124,418 declarations, all accepted by `nanoda`. (The trailing `1 pretty printer errors: ["Unable
to print axioms"]` refers only to the optional pretty-printer output, for which no declaration was requested,
and does not affect the exit status.)

## 3. Controls

Seven negative controls and one positive control were run through the pipeline of Section 2 with the same
configuration, changing only the challenge or the solution module (`configs/controls/*.json`,
`Replay/Controls/*.lean`). Each negative control is rejected with the message below, exit status 1;
`RESULTS.md` has the full table with wall times.

**Altered statements** (the altered file is the challenge, the shipped proof is the solution). Each is a
verbatim copy of `SubNLogN/Challenge.lean` — same namespace, same constant names, so the altered statement
constant is still called `SubNLogN.Challenge.IntMulSubNLogN` — with one edit in `def IntMulSubNLogN`, plus the
one-line theorem of `Replay/Challenge.lean`:

| Module | Edit | Output |
|---|---|---|
| `S1_Exp45` | `2 ^ 46` replaced by `2 ^ 45` in the time bound (all three occurrences) | `Const does not match between challenge and target 'SubNLogN.Challenge.IntMulSubNLogN'` |
| `S2_NoFinite` | the conjunct `(∀ k, Finite (M.tm.Γ k)) ∧` deleted | same |
| `S3_StrictLt` | `≤` replaced by `<` in the time bound | same |

The message names the statement constant: the rejection comes from comparing the *definition* of
`IntMulSubNLogN` (all other constants of the copied file match), not from a different name. The positive
control `S0_IdenticalCopy`, a byte-identical copy of `SubNLogN/Challenge.lean` under another module name plus
the same theorem line, is accepted (exit status 0, 24:07, peak memory 17.4 GB; `logs/R3_S0_IdenticalCopy.txt`), which shows that the three rejections are caused by
the edits and not by re-elaborating the file.

**Altered proofs** (challenge `Replay/Challenge.lean`, the altered module is the solution):

| Module | Proof | Output |
|---|---|---|
| `P1_Sorry` | `sorry` | `Illegal axiom detected: 'sorryAx'` |
| `P2_AddedAxiom` | an axiom asserting the statement | `Illegal axiom detected: 'Replay.Controls.P2.intMul_challenge_axiom'` |
| `P3_NativeDecide` | the genuine proof term preceded by `have h : (2 : ℕ) ^ 46 = 70368744177664 := by native_decide` | `Illegal axiom detected: 'SubNLogN.Assembly.intMul_challenge._native.native_decide.ax_1_1'` |
| `P4_ExtraAxiomTransitive` | `axiom oracle : False`, used through an intermediate lemma | `Illegal axiom detected: 'Replay.Controls.P4.oracle'` |

(In Lean 4.33, `native_decide` introduces a per-use axiom named `<declaration>._native.native_decide.ax_<n>`.)
All four modules are accepted by the Lean kernel and hence by `leanchecker`; the rejection comes from the
`permitted_axioms` check. An additional control, `P5_DefinitionSwap` — a solution that does not import
`SubNLogN/Challenge.lean`, re-declares `SubNLogN.Challenge.IntMulSubNLogN := True` and proves it by
`trivial` — is rejected by the statement comparison (`Const does not match between challenge and target
'SubNLogN.Challenge.IntMulSubNLogN'`), although the theorem's type is syntactically the same constant name as
in the challenge.

## Logs

`logs/` contains, for every run above, the exact command line, the tool versions, start and end times, the
output (complete for the `leanchecker` runs, which list every replayed module; the final lines for the
`comparator` runs, whose output is otherwise dominated by the cached build diagnostics that `lake build`
re-prints for an up-to-date tree) and the GNU `time -v` summary with the exit status, wall time and peak RSS.
`SHA256SUMS` lists every file of this directory.
