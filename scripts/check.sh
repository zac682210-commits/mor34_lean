#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p logs
lean --version | tee logs/lean_version.txt
lake build 2>&1 | tee logs/build.log
lake env lean Check.lean 2>&1 | tee logs/axioms.log
python3 scripts/audit_axioms.py logs/axioms.log
echo 'Arithmetic modules checked; Targets.lean contains OPEN proposition definitions.'
echo 'This is not a formal proof of MOR34 or its FPT running time.'
