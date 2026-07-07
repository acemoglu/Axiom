#!/usr/bin/env bash
# Compare Axiom (in-process Swift) vs Lean on the same machine.
# Usage: ./Scripts/benchmark-compare.sh [release|debug]
# Skip slow subprocess row: SKIP_SUBPROCESS=1 ./Scripts/benchmark-compare.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CONFIG="${1:-release}"
N=5000

echo "=== Axiom vs Lean benchmark ==="
echo "Machine: $(uname -m) $(uname -s)"
echo "Swift config: $CONFIG"
echo "Iterations per workload: $N"
echo ""
echo "Workload: identity  λ (x : Type₀), x"
echo ""

cd "$ROOT"

echo "Building Axiom ($CONFIG)…"
swift build -c "$CONFIG" >/dev/null
swift test -c "$CONFIG" --filter BenchmarkTests 2>&1 | grep '^BENCHMARK' || true

echo ""

if command -v lean >/dev/null 2>&1; then
  echo "Lean: $(lean --version | head -1)"
  lean --run "$ROOT/Scripts/lean-bench/Main.lean" "$N" all
  lean --run "$ROOT/Scripts/lean-bench/DeepApp.lean" 500 200

  echo ""
  if [[ "${SKIP_SUBPROCESS:-0}" == "1" ]]; then
    echo "Subprocess benchmark skipped (SKIP_SUBPROCESS=1)."
  else
  echo "Subprocess path (full elaboration per lean invocation, n=5)…"
  SUB_N=5
  T0=$(python3 -c 'import time; print(time.time())')
  for _ in $(seq 1 "$SUB_N"); do
    lean "$ROOT/Scripts/lean-bench/Subprocess.lean" >/dev/null 2>&1
  done
  T1=$(python3 -c 'import time; print(time.time())')
  ELAPSED=$(python3 -c "print($T1 - $T0)")
  OPS=$(python3 -c "print(round($SUB_N / ($T1 - $T0), 2))")
  echo "BENCHMARK lean subprocess elaborate: ${OPS} ops/sec (n=${SUB_N}, ${ELAPSED}s total)"
  fi
else
  echo "Lean not found (install via elan). Skipping Lean benchmarks."
fi

echo ""
echo "=== How to read this ==="
echo ""
echo "Fair kernel rows (compare Axiom ↔ Lean on the same line):"
echo "  • shared term  — same AST every iteration (Lean kernel caches the type; Axiom re-walks)"
echo "  • fresh term   — rebuild λ each iteration on both sides"
echo ""
echo "Context rows (do not compare across tools):"
echo "  • inferType    — Lean elaborator layer, not the trusted kernel"
echo "  • subprocess   — spawn lean + elaborate + exit per obligation"
echo "  • nat match    — Axiom-only workload today"
echo "  • parallel     — Axiom multi-core scaling demo"
echo ""
echo "Headline: library embed (import Axiom) vs subprocess embed (lean File.lean)."
