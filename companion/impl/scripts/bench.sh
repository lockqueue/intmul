#!/usr/bin/env bash
# Builds a fresh OpenMP intmul_fastdft binary, records single-thread selftest
# output in bench/logs/selftest_1T.log, and runs ./bench/run_bench.sh to
# regenerate bench/logs/mul_*.log and bench/logs/RUNS.tsv.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

CC_BIN="${CC:-gcc}"
CFLAGS_VAL="${CFLAGS:--O2 -march=native}"
CPPFLAGS_VAL="${CPPFLAGS:--DNDEBUG}"
LDLIBS_VAL="${LDLIBS:--lmpfr -lgmp -lm}"

mkdir -p bench/logs

echo "[bench] Building fresh OpenMP binary intmul_fastdft (logging compiler output to bench/logs/cgmp_build.log)..."
make clean > /dev/null
make all CC="$CC_BIN" CFLAGS="$CFLAGS_VAL" CPPFLAGS="$CPPFLAGS_VAL" LDLIBS="$LDLIBS_VAL" > bench/logs/cgmp_build.log 2>&1

echo "[bench] Running single-thread selftest (bench/logs/selftest_1T.log)..."
OMP_NUM_THREADS=1 ./intmul_fastdft selftest > bench/logs/selftest_1T.log 2>&1

echo "[bench] Running sequential benchmark suite (./bench/run_bench.sh)..."
exec ./bench/run_bench.sh
