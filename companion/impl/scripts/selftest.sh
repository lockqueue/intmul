#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [[ ! -x ./intmul_fastdft || intmul_fastdft.c -nt ./intmul_fastdft ]]; then
  echo "[selftest] Building intmul_fastdft..."
  make all
fi

echo "[selftest] Running ./intmul_fastdft selftest..."
./intmul_fastdft selftest
