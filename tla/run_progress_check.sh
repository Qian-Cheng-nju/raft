#!/bin/bash
# Run TLC model checker on etcdraft_progress.tla with sensible defaults.

set -euo pipefail

SPEC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPEC_FILE="etcdraft_progress.tla"
CFG_FILE="etcdraft_progress.cfg"

cd "$SPEC_DIR"

echo "========================================="
echo "TLC Model Checker for etcdraft_progress"
echo "========================================="
echo ""
echo "Spec: $SPEC_FILE"
echo "Config: $CFG_FILE"
echo ""

# Locate TLC: prefer system tlc, fall back to bundled tla2tools.jar
ROOT_DIR="$(cd "$SPEC_DIR/../../../../" && pwd)"
TLA_JAR="$ROOT_DIR/lib/tla2tools.jar"

if command -v tlc &> /dev/null; then
    TLC_CMD=(tlc)
    echo "Using tlc from PATH"
elif [ -f "$TLA_JAR" ]; then
    # Add throughput-optimized GC to silence JVM warning and improve performance
    TLC_CMD=(java -XX:+UseParallelGC -cp "$TLA_JAR" tlc2.TLC)
    echo "Using bundled tla2tools.jar at $TLA_JAR"
else
    echo "ERROR: tlc command not found and $TLA_JAR missing"
    echo "Please install TLA+ Toolbox or place tla2tools.jar under lib/"
    exit 1
fi

# Optional: limit search depth via environment (e.g., TLC_DEPTH=100)
DEPTH_ARGS=()
if [[ -n "${TLC_DEPTH:-}" ]]; then
    DEPTH_ARGS=(-depth "$TLC_DEPTH")
fi

echo "Running TLC model checker..."
echo ""

# Run TLC and capture its exit status (not tee's)
set +e
"${TLC_CMD[@]}" \
    -workers auto \
    -coverage 5 \
    -deadlock \
    -nowarning \
    "${DEPTH_ARGS[@]}" \
    "$SPEC_FILE" \
    -config "$CFG_FILE" \
    2>&1 | tee tlc_progress_output.log
TLC_STATUS=${PIPESTATUS[0]}
set -e

echo ""
echo "========================================="
echo "Check complete. Output saved to tlc_progress_output.log"
echo "Exit status: $TLC_STATUS"
echo "========================================="

exit "$TLC_STATUS"
