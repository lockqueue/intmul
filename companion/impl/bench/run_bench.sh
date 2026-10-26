#!/bin/bash
# Sequential benchmark runner for intmul_fastdft (build it first with `make`; see README.md).
# Every run: `OMP_NUM_THREADS=<T> /usr/bin/time -v ./intmul_fastdft mul <nbits> 0 7 <algo>`
# Full stdout+stderr of each run goes to bench/logs/mul_<nbits>_<algo>_<T>T.log; a one-line
# status per run goes to bench/logs/RUNS.tsv. Nothing is filtered.
set -u
B=$(cd "$(dirname "$0")" && pwd)          # bench/ directory containing this script
ROOT=$(cd "$B/.." && pwd)                 # repository root
L="$B/logs"
mkdir -p "$L"

if [ -x "$ROOT/intmul_fastdft" ]; then
  cd "$ROOT" || exit 9
elif [ -x "$B/intmul_fastdft" ]; then
  cd "$B" || exit 9
else
  echo "Error: ./intmul_fastdft not found; build it first with 'make' in $ROOT." >&2
  exit 1
fi
BIN=./intmul_fastdft

echo -e "start_iso\tnbits\talgo\tthreads\texit\tuptime_before\tuptime_after" > "$L/RUNS.tsv"
any_fail=0

run() {  # nbits algo threads
  local n=$1 a=$2 t=$3 name
  if [ "$a" = "1" ]; then name=sinc; else name=gauss; fi
  local log="$L/mul_${n}_${name}_${t}T.log"
  local ub ua st
  ub=$(uptime)
  st=$(date -Is)
  {
    echo "### cmd: OMP_NUM_THREADS=$t /usr/bin/time -v $BIN mul $n 0 7 $a"
    echo "### start: $st"
    echo "### uptime before: $ub"
  } > "$log"
  OMP_NUM_THREADS=$t /usr/bin/time -v $BIN mul $n 0 7 $a >> "$log" 2>&1
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    any_fail=1
  fi
  ua=$(uptime)
  {
    echo "### end: $(date -Is)"
    echo "### uptime after: $ua"
    echo "### exit=$rc"
  } >> "$log"
  echo -e "$st\t$n\t$name\t$t\t$rc\t$ub\t$ua" >> "$L/RUNS.tsv"
}

run 10000000   1 1
run 100000000  1 1
run 100000000  1 64
run 10000000   0 1
run 100000000  0 1
run 500000000  1 1
run 1000000000 1 1
echo "ALL RUNS DONE $(date -Is)" >> "$L/RUNS.tsv"
exit $any_fail
