# Raw Benchmark Logs (`bench/logs/`)

This directory contains the complete, unfiltered raw benchmark logs from the
2026-10-24 measurement summarized in [`../BENCHMARK.md`](../BENCHMARK.md),
recorded on the 64-vCPU AMD EPYC 7B13 (Zen 3) Linux x86-64 machine documented in
[`../MACHINE.txt`](../MACHINE.txt).

## Committed Files

* `cgmp_build.log` — compiler stdout/stderr from the measured build
  `gcc -O2 -march=native -fopenmp -DNDEBUG intmul_fastdft.c -o intmul_fastdft -l:libmpfr.so.6 -l:libgmp.so.10 -lm`
  (equivalent to the public `make` build `-lmpfr -lgmp -lm`; see
  [`../MACHINE.txt`](../MACHINE.txt); 0 bytes: zero warnings).
* `selftest_1T.log` — full stdout+stderr of
  `OMP_NUM_THREADS=1 ./intmul_fastdft selftest` (`SELFTEST: ALL PASSED`).
* `RUNS.tsv` — tab-separated run manifest recording ISO-8601 start time,
  `nbits`, `algo`, `threads`, exit status (`0` for all 7 runs), and system
  `uptime` / load average before and after each run.
* `mul_10000000_sinc_1T.log` — $10^7$-bit `sinc` (`algo=1`), 1 thread (`e2e`
  `9.92 s` vs. GMP `0.0478 s`, `207×`, RSS `584620 kB` = `0.56 GiB`,
  `EXACT MATCH`).
* `mul_100000000_sinc_1T.log` — $10^8$-bit `sinc` (`algo=1`), 1 thread (`e2e`
  `92.51 s` vs. GMP `0.6059 s`, `153×`, RSS `4578528 kB` = `4.4 GiB`,
  `EXACT MATCH`).
* `mul_100000000_sinc_64T.log` — $10^8$-bit `sinc` (`algo=1`), 64 threads (`e2e`
  `6.31 s` vs. GMP `0.6056 s`, `10.4×`, `3528%` CPU, RSS `4638848 kB` =
  `4.4 GiB`, `EXACT MATCH`).
* `mul_500000000_sinc_1T.log` — $5\cdot 10^8$-bit `sinc` (`algo=1`), 1 thread
  (`e2e` `805.37 s` vs. GMP `3.4417 s`, `234×`, RSS `35450496 kB` = `33.8 GiB`,
  `EXACT MATCH`).
* `mul_1000000000_sinc_1T.log` — $10^9$-bit `sinc` (`algo=1`), 1 thread (`e2e`
  `2612.65 s` vs. GMP `8.0969 s`, `323×`, 2 recursion levels
  `2^27 → 2^14 → 128 base`, RSS `70614344 kB` = `67.3 GiB`, `EXACT MATCH`).
* `mul_10000000_gauss_1T.log` — $10^7$-bit `gauss` (`algo=0`), 1 thread (`e2e`
  `18.52 s` vs. GMP `0.0470 s`, `394×`, RSS `2131944 kB` = `2.0 GiB`,
  `EXACT MATCH`).
* `mul_100000000_gauss_1T.log` — $10^8$-bit `gauss` (`algo=0`), 1 thread (`e2e`
  `163.46 s` vs. GMP `0.5960 s`, `274×`, RSS `10926124 kB` = `10.4 GiB`,
  `EXACT MATCH`).

## Re-Running the Benchmark Suite

On a Linux x86-64 machine with `gcc` (OpenMP), `libgmp-dev`, `libmpfr-dev`, GNU
`/usr/bin/time`, and at least `70 GiB` of RAM (required by the $10^9$-bit run):

```bash
# From the repository root:
./scripts/selftest.sh
./scripts/bench.sh      # builds intmul_fastdft, runs selftest_1T.log, and invokes ./bench/run_bench.sh
```
